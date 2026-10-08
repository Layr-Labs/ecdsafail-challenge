//! SKY-COF park/modmul component (research module; INERT unless called).
//!
//! Three exact-construction families for the SKY-COF walk and its multiply legs, over
//! p = 2^n - c (secp256k1: n = 256, c = 2^32 + 977; small (n, c) pairs for the selftests):
//!
//! 1. POST-PARK DOUBLING. After the walk's relabel doubling the cofactor field is the
//!    (n+1)-wire value X = 2s (X[0] == 0). [`park_fold`] applies, controlled on the park
//!    flag `fl`, the fold X -> X - p if X >= 2^n (= low n bits + c, the top wire cleared);
//!    [`park_unfold`] is its exact inverse (reverse tick). 1 + (w-1) Toffoli, w = fold window.
//!    [`odo_inc`] / [`odo_dec`] keep the park odometer (ob wires, ob-1 Toffoli each) and
//!    [`odo_nonzero_xor`] gives the reverse decoder its post-park predicate (ob-1 Toffoli).
//!    Recommended tick schedule (verified end-to-end by the selftest with a stand-in flag):
//!      forward t:  rail/cofactor tick; F = [u_post == 0] (rails); odo_inc(F); park_fold(X, F); uncompute F (rails)
//!      reverse t:  F = [u_post == 0] (rails); odo_dec(F); P = [odo != 0] (= post-park, i.e. t > park);
//!                  park_unfold(X, F); decode with P; uncompute P (odometer, unchanged); un-tick; uncompute F (rails)
//!    The odometer counts the F ticks (park tick included), max R - park (7 wires for R <= 404).
//!
//! 2. HORNER MODMUL, garbage-free and out of place: out = a * b * 2^-k * (-1)^neg (mod p), with
//!    a, b quantum and unchanged. k = 0: MSB-first doubling Horner; k >= n: LSB-first halving
//!    Horner (2^-n for free) plus k - n halvings (the 2^-R correction: k = R); 0 < k < n: the
//!    cheaper of the two plus doublings/halvings. Per bit: one controlled add (2n+1 Toffoli),
//!    one fold of the add's carry (w-1), one measured erase of that carry by a W-bit compare
//!    (W/2 expected), one doubling/halving fold (w-1). [`mul_inv`] is the exact inverse
//!    (uncomputation, phase-debt payment).
//!
//! 3. LOW ROOM. Every adder/compare here takes a `room` (clean scratch wires it may use) and
//!    splits its carry chain into chunks whose boundary carries are erased afterwards by
//!    measurement plus a conditional compare (half the chunk width in expectation). The last
//!    chunk is the widest, so the premium is (L - k_last - chunks + 1)/2 Toffoli per chain.
//!
//! Arithmetic semantics are LAZY (values are n-bit strings, congruent mod p; a value in
//! [p, 2^n) is not reduced). With `fold_w = n` and `cmp_w = n` every step is exact on every
//! canonical input; with windows (fold_w = cbits + G, cmp_w = W) a fold carry leaving the window
//! (~2^-G per fold) or a compare tie (~2^-W per erase) is the only approximation. The bit-exact
//! classical model is `model.rs`; `selftest.rs` checks the circuit against it.
use super::Builder;
use crate::circuit::{QubitId, NO_BIT};

pub mod model;
pub mod selftest;

type Q = QubitId;

/// p = 2^n - c, c odd, 0 < c < 2^(n-1), c < 2^127.
#[derive(Clone, Copy, Debug)]
pub struct Field {
    pub n: usize,
    pub c: u128,
}

impl Field {
    pub fn secp() -> Self {
        Field {
            n: 256,
            c: (1u128 << 32) + 977,
        }
    }
    pub fn cbits(&self) -> usize {
        128 - self.c.leading_zeros() as usize
    }
}

/// `fold_w`: low bits a fold's constant add spans (cbits..=n; n = exact). `cmp_w`: top bits a
/// carry-erasing compare reads (1..=n; n = exact). `room`: clean scratch the call may use.
#[derive(Clone, Copy, Debug)]
pub struct Cfg {
    pub fold_w: usize,
    pub cmp_w: usize,
    pub room: usize,
}

impl Cfg {
    /// Windows priced like the tree's FOLD_GUARD / ERASE_COMPARE.
    pub fn windowed(f: Field, guard: usize, cmp_w: usize, room: usize) -> Self {
        Cfg {
            fold_w: (f.cbits() + guard).min(f.n),
            cmp_w: cmp_w.min(f.n),
            room,
        }
    }
    pub fn exact(f: Field, room: usize) -> Self {
        Cfg {
            fold_w: f.n,
            cmp_w: f.n,
            room,
        }
    }
}

// ─── carry-chain engine ──────────────────────────────────────────────────────────────────────

/// One addend bit: constant 0, constant 1, or a wire (a shared control wire is fine: every
/// step restores the addend wire immediately).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Ad {
    Zero,
    One,
    W(Q),
}

/// What happens to y at a position once its carry is erased.
#[derive(Clone, Copy, Debug)]
pub enum Fin {
    /// y ^= ad ^ carry_in (y += ad).
    Sum,
    /// y ^= e & (ad ^ carry_in) with UNCONTROLLED carries (y += e * ad).
    CtlSum(Q),
    /// y left unchanged (compares).
    Restore,
}

#[derive(Clone, Copy)]
enum Top {
    None,
    Keep,
    Xor(Q),
}

/// Action on the carry-out of y + ad + bin: a phase (optionally controlled by e) or an XOR
/// into a target (optionally ANDed with e).
#[derive(Clone, Copy)]
pub enum Act {
    Phase(Option<Q>),
    Xor(Q, Option<Q>),
}

fn hmr_cz(b: &mut Builder, t: Q, u: Q, v: Q) {
    let m = b.alloc_bit();
    b.hmr(t, m);
    b.cz_if(u, v, m);
    b.free_bit(m);
}

fn z(b: &mut Builder, q: Q) {
    b.z_if(q, NO_BIT);
}

/// Compute the carry out of position i into a fresh wire (MAJ(y, ad, ci)). Leaves y ^= ci for
/// a wire addend with a carry-in; restores everything else.
fn fwd_step(b: &mut Builder, y: Q, ad: Ad, ci: Option<Q>) -> Option<Q> {
    match (ad, ci) {
        (Ad::Zero, None) => None,
        (Ad::Zero, Some(c)) => {
            let t = b.alloc_qubit();
            b.ccx(y, c, t);
            Some(t)
        }
        (Ad::One, None) => {
            let t = b.alloc_qubit();
            b.cx(y, t);
            Some(t)
        }
        (Ad::One, Some(c)) => {
            let t = b.alloc_qubit();
            b.x(y);
            b.x(c);
            b.ccx(y, c, t);
            b.x(y);
            b.x(c);
            b.x(t);
            Some(t)
        }
        (Ad::W(a), None) => {
            let t = b.alloc_qubit();
            b.ccx(a, y, t);
            Some(t)
        }
        (Ad::W(a), Some(c)) => {
            let t = b.alloc_qubit();
            b.cx(c, y);
            b.cx(c, a);
            b.ccx(a, y, t);
            b.cx(c, a);
            b.cx(c, t);
            Some(t)
        }
    }
}

/// Erase the carry wire `t` computed by [`fwd_step`] (y still in its post-fwd state). 0 Toffoli.
fn erase_step(b: &mut Builder, y: Q, ad: Ad, ci: Option<Q>, t: Q) {
    match (ad, ci) {
        (Ad::Zero, None) => unreachable!("dead carry has no wire"),
        (Ad::Zero, Some(c)) => hmr_cz(b, t, y, c),
        (Ad::One, None) => b.cx(y, t),
        (Ad::One, Some(c)) => {
            b.x(t);
            b.x(y);
            b.x(c);
            hmr_cz(b, t, y, c);
            b.x(y);
            b.x(c);
        }
        (Ad::W(a), None) => hmr_cz(b, t, a, y),
        (Ad::W(a), Some(c)) => {
            b.cx(c, t);
            b.cx(c, a);
            hmr_cz(b, t, a, y);
            b.cx(c, a);
        }
    }
    b.release_clean(t);
}

fn finalize(b: &mut Builder, y: Q, ad: Ad, ci: Option<Q>, modified: bool, fin: Fin) {
    if modified {
        b.cx(ci.expect("modified implies carry-in"), y);
    }
    match fin {
        Fin::Restore => {}
        Fin::Sum => {
            match ad {
                Ad::Zero => {}
                Ad::One => b.x(y),
                Ad::W(a) => b.cx(a, y),
            }
            if let Some(c) = ci {
                b.cx(c, y);
            }
        }
        Fin::CtlSum(e) => match (ad, ci) {
            (Ad::Zero, None) => {}
            (Ad::Zero, Some(c)) => b.ccx(e, c, y),
            (Ad::One, None) => b.cx(e, y),
            (Ad::One, Some(c)) => {
                b.cx(e, y);
                b.ccx(e, c, y);
            }
            (Ad::W(a), None) => b.ccx(e, a, y),
            (Ad::W(a), Some(c)) => {
                b.cx(c, a);
                b.ccx(e, a, y);
                b.cx(c, a);
            }
        },
    }
}

fn modified(ad: Ad, ci: Option<Q>) -> bool {
    matches!(ad, Ad::W(_)) && ci.is_some()
}

/// One chunk: carries forward, top handling, backward erase + finalize. Returns the kept top
/// carry for `Top::Keep`.
fn add_chunk(b: &mut Builder, y: &[Q], ad: &[Ad], cin: Option<Q>, top: Top, fin: Fin) -> Option<Q> {
    let l = y.len();
    let m = if matches!(top, Top::None) { l - 1 } else { l };
    let mut c: Vec<Option<Q>> = Vec::with_capacity(m + 1);
    c.push(cin);
    for i in 0..m {
        let t = fwd_step(b, y[i], ad[i], c[i]);
        c.push(t);
    }
    let mut kept = None;
    match top {
        Top::None => finalize(b, y[l - 1], ad[l - 1], c[l - 1], false, fin),
        Top::Keep => kept = c[l],
        Top::Xor(tg) => {
            if let Some(t) = c[l] {
                match fin {
                    Fin::CtlSum(e) => b.ccx(e, t, tg),
                    _ => b.cx(t, tg),
                }
            }
        }
    }
    for i in (0..m).rev() {
        let keep_this = matches!(top, Top::Keep) && i == l - 1;
        if !keep_this {
            if let Some(t) = c[i + 1] {
                erase_step(b, y[i], ad[i], c[i], t);
            }
        }
        finalize(b, y[i], ad[i], c[i], modified(ad[i], c[i]), fin);
    }
    kept
}

/// Chunk sizes for an `l`-position chain in `room` wires: a non-last chunk j (0-based) holds j
/// earlier boundaries plus its k_j carries; the last holds J-1 boundaries, k-1 carries and
/// `last_extra` (a computed top carry). Fewest chunks, widest last chunk.
pub fn plan(l: usize, room: usize, last_extra: usize) -> Vec<usize> {
    for jn in 1..=l {
        let Some(cap_last) = (room + 1).checked_sub(last_extra + (jn - 1)) else {
            break;
        };
        if cap_last == 0 {
            break;
        }
        if (0..jn - 1).any(|j| room <= j) {
            break;
        }
        let caps: Vec<usize> = (0..jn - 1).map(|j| room - j).collect();
        let total: usize = caps.iter().sum::<usize>() + cap_last;
        if total >= l {
            let k_last = cap_last.min(l - (jn - 1));
            let mut rem = l - k_last;
            let mut ks = Vec::with_capacity(jn);
            for (j, &cap) in caps.iter().enumerate() {
                let left = jn - 2 - j;
                let k = cap.min(rem - left);
                ks.push(k);
                rem -= k;
            }
            assert_eq!(rem, 0);
            ks.push(k_last);
            return ks;
        }
    }
    panic!("skycof_mm: room {room} too small for a {l}-position chain");
}

/// y += ad (`Fin::Sum`) or y += e*ad (`Fin::CtlSum(e)`) mod 2^len(y); `cout` ^= the carry out
/// (times e). Chunked to `room` clean wires.
pub fn add_gen(b: &mut Builder, y: &[Q], ad: &[Ad], fin: Fin, cout: Option<Q>, room: usize) {
    let l = y.len();
    assert_eq!(ad.len(), l);
    assert!(l >= 1);
    let ks = plan(l, room, cout.is_some() as usize);
    let mut bounds: Vec<(usize, usize, Option<Q>)> = Vec::new();
    let (mut lo, mut cin) = (0usize, None);
    for (j, &k) in ks.iter().enumerate() {
        let hi = lo + k;
        let last = j + 1 == ks.len();
        let top = if !last {
            Top::Keep
        } else if let Some(co) = cout {
            Top::Xor(co)
        } else {
            Top::None
        };
        let kept = add_chunk(b, &y[lo..hi], &ad[lo..hi], cin, top, fin);
        if !last {
            bounds.push((lo, hi, kept));
            cin = kept;
        }
        lo = hi;
    }
    for j in (0..bounds.len()).rev() {
        let (lo, hi, bj) = bounds[j];
        let Some(bj) = bj else { continue };
        let bprev = if j == 0 { None } else { bounds[j - 1].2 };
        let m = b.alloc_bit();
        b.hmr(bj, m);
        b.release_clean(bj);
        b.push_condition(m);
        let yy = &y[lo..hi];
        // B_j = [z < ad + B_{j-1}], z = y' (Sum) or e ? y' : ~y' (CtlSum, uncontrolled carries).
        let conj = |b: &mut Builder| {
            if let Fin::CtlSum(e) = fin {
                b.x(e);
                for &q in yy {
                    b.cx(e, q);
                }
                b.x(e);
            }
        };
        conj(b);
        b.x_all(yy);
        carry_act(b, yy, &ad[lo..hi], bprev, Act::Phase(None), room - j);
        b.x_all(yy);
        conj(b);
        b.pop_condition();
        b.free_bit(m);
    }
}

fn maj_phase(b: &mut Builder, y: Q, ad: Ad, ci: Option<Q>) {
    match (ad, ci) {
        (Ad::Zero, None) => {}
        (Ad::Zero, Some(c)) => b.cz(y, c),
        (Ad::One, None) => z(b, y),
        (Ad::One, Some(c)) => {
            z(b, y);
            z(b, c);
            b.cz(y, c);
        }
        (Ad::W(a), None) => b.cz(a, y),
        (Ad::W(a), Some(c)) => {
            b.cz(y, a);
            b.cz(a, c);
            b.cz(y, c);
        }
    }
}

fn last_chunk_act(b: &mut Builder, y: &[Q], ad: &[Ad], cin: Option<Q>, act: Act) {
    let l = y.len();
    let mut c: Vec<Option<Q>> = vec![cin];
    for i in 0..l - 1 {
        let t = fwd_step(b, y[i], ad[i], c[i]);
        c.push(t);
    }
    let (yt, at, ct) = (y[l - 1], ad[l - 1], c[l - 1]);
    match act {
        Act::Phase(None) => maj_phase(b, yt, at, ct),
        Act::Phase(Some(_)) | Act::Xor(..) => {
            if let Some(t) = fwd_step(b, yt, at, ct) {
                match act {
                    Act::Phase(Some(e)) => b.cz(e, t),
                    Act::Xor(tg, Some(e)) => b.ccx(e, t, tg),
                    Act::Xor(tg, None) => b.cx(t, tg),
                    Act::Phase(None) => unreachable!(),
                }
                erase_step(b, yt, at, ct, t);
                finalize(b, yt, at, ct, modified(at, ct), Fin::Restore);
            }
        }
    }
    for i in (0..l - 1).rev() {
        if let Some(t) = c[i + 1] {
            erase_step(b, y[i], ad[i], c[i], t);
        }
        finalize(b, y[i], ad[i], c[i], modified(ad[i], c[i]), Fin::Restore);
    }
}

/// Act on carry_out(y + ad + bin) (y, ad, bin unchanged). Chunked to `room`.
pub fn carry_act(b: &mut Builder, y: &[Q], ad: &[Ad], bin: Option<Q>, act: Act, room: usize) {
    let l = y.len();
    assert_eq!(ad.len(), l);
    let extra = if matches!(act, Act::Phase(None)) {
        0
    } else {
        1
    };
    let ks = plan(l, room, extra);
    let mut bounds: Vec<(usize, usize, Option<Q>)> = Vec::new();
    let (mut lo, mut cin) = (0usize, bin);
    for (j, &k) in ks.iter().enumerate() {
        let hi = lo + k;
        if j + 1 < ks.len() {
            let kept = add_chunk(b, &y[lo..hi], &ad[lo..hi], cin, Top::Keep, Fin::Restore);
            bounds.push((lo, hi, kept));
            cin = kept;
        } else {
            last_chunk_act(b, &y[lo..hi], &ad[lo..hi], cin, act);
        }
        lo = hi;
    }
    for j in (0..bounds.len()).rev() {
        let (lo, hi, bj) = bounds[j];
        let Some(bj) = bj else { continue };
        let bprev = if j == 0 { bin } else { bounds[j - 1].2 };
        let m = b.alloc_bit();
        b.hmr(bj, m);
        b.release_clean(bj);
        b.push_condition(m);
        carry_act(
            b,
            &y[lo..hi],
            &ad[lo..hi],
            bprev,
            Act::Phase(None),
            room - j,
        );
        b.pop_condition();
        b.free_bit(m);
    }
}

/// Act on [z < ad + bin] (z unchanged).
pub fn lt(b: &mut Builder, z: &[Q], ad: &[Ad], bin: Option<Q>, act: Act, room: usize) {
    b.x_all(z);
    carry_act(b, z, ad, bin, act, room);
    b.x_all(z);
}

pub fn wires(a: &[Q]) -> Vec<Ad> {
    a.iter().map(|&q| Ad::W(q)).collect()
}

/// Bits 0..w of the constant k, each a constant (g None) or the control wire g (g Some).
pub fn const_ad(k: u128, w: usize, g: Option<Q>) -> Vec<Ad> {
    (0..w)
        .map(|i| {
            if i < 128 && (k >> i) & 1 == 1 {
                g.map_or(Ad::One, Ad::W)
            } else {
                Ad::Zero
            }
        })
        .collect()
}

/// y += g*k (mod 2^len(y)).
pub fn cadd_k(b: &mut Builder, y: &[Q], k: u128, g: Q, room: usize) {
    add_gen(b, y, &const_ad(k, y.len(), Some(g)), Fin::Sum, None, room);
}

/// y -= g*k (mod 2^len(y)).
pub fn csub_k(b: &mut Builder, y: &[Q], k: u128, g: Q, room: usize) {
    b.x_all(y);
    cadd_k(b, y, k, g, room);
    b.x_all(y);
}

// ─── modular steps (lazy fold semantics, see model.rs) ─────────────────────────────────────

/// out <- fold(2*out): relabel (fresh LSB, top wire t out), out[0..w] += t*c, t cleared by out[0].
pub fn dbl(b: &mut Builder, f: Field, cfg: Cfg, out: &mut Vec<Q>, room: usize) {
    let t = out.pop().expect("register");
    let zq = b.alloc_qubit();
    out.insert(0, zq);
    cadd_k(b, &out[..cfg.fold_w], f.c, t, room - 1);
    b.cx(out[0], t);
    b.release_clean(t);
}

/// Inverse of [`dbl`]: out <- (out + out[0]*p) / 2 (lazy).
pub fn hlv(b: &mut Builder, f: Field, cfg: Cfg, out: &mut Vec<Q>, room: usize) {
    let t = b.alloc_qubit();
    b.cx(out[0], t);
    csub_k(b, &out[..cfg.fold_w], f.c, t, room - 1);
    let zq = out.remove(0);
    b.release_clean(zq);
    out.push(t);
}

/// Exact composition of four shipped finite-window halves, not an ideal
/// field-division substitution. Stable q controls are outside every target.
fn hlv4_eligible(f: Field, cfg: Cfg) -> bool {
    f.c % 16 == 1 && cfg.fold_w >= 4 && cfg.fold_w <= f.n.saturating_sub(4)
}

pub fn hlv4(b: &mut Builder, f: Field, cfg: Cfg, out: &mut Vec<Q>, room: usize) {
    assert!(hlv4_eligible(f, cfg));
    let span = cfg.fold_w - 4;
    let d = (f.c - 1) / 16;
    // LSB-first wire vector: integer right-rotate is Vec left-rotate.
    out.rotate_left(4);
    let q = out[f.n - 4..].to_vec();
    for i in 0..4 { csub_k(b, &out[i..i + span], d, q[i], room); }
}

/// Literal inverse of hlv4, equal to four shipped finite-window doubles.
pub fn dbl4(b: &mut Builder, f: Field, cfg: Cfg, out: &mut Vec<Q>, room: usize) {
    assert!(hlv4_eligible(f, cfg));
    let span = cfg.fold_w - 4;
    let d = (f.c - 1) / 16;
    let q = out[f.n - 4..].to_vec();
    for i in (0..4).rev() { cadd_k(b, &out[i..i + span], d, q[i], room); }
    out.rotate_right(4);
}

/// out <- out + e*a (mod p): controlled add with carry t2, fold t2, measured erase of t2 by
/// t2 == e*[out < a] on the top cmp_w bits.
pub fn madd(b: &mut Builder, f: Field, cfg: Cfg, out: &[Q], a: &[Q], e: Q, room: usize) {
    let n = f.n;
    let ad = wires(a);
    let t2 = b.alloc_qubit();
    add_gen(b, out, &ad, Fin::CtlSum(e), Some(t2), room - 1);
    cadd_k(b, &out[..cfg.fold_w], f.c, t2, room - 1);
    let m = b.alloc_bit();
    b.hmr(t2, m);
    b.release_clean(t2);
    b.push_condition(m);
    lt(
        b,
        &out[n - cfg.cmp_w..],
        &ad[n - cfg.cmp_w..],
        None,
        Act::Phase(Some(e)),
        room,
    );
    b.pop_condition();
    b.free_bit(m);
}

/// Fused `madd` followed by `hlv`. If `u` is the carry of `out + e*a` and
/// `r` its raw low bit, the two pseudo-Mersenne corrections combine to
/// `(u-(u xor r))*c`. Complementing the target under `!u` lets one controlled
/// constant add implement either sign. The corrected low bit is zero and
/// `u xor r` is the high bit introduced by the half.
pub fn madd_hlv(b: &mut Builder, f: Field, cfg: Cfg, out: &mut Vec<Q>, a: &[Q], e: Q, room: usize) {
    let n = f.n;
    assert_eq!(out.len(), n);
    assert!(cfg.cmp_w < n && room >= 8);
    let ad = wires(a);
    let u = b.alloc_qubit();
    add_gen(b, out, &ad, Fin::CtlSum(e), Some(u), room - 2);
    let parity = b.alloc_qubit();
    b.cx(out[0], parity);
    b.x(u);
    b.cx_all(u, &out[..cfg.fold_w]);
    b.x(u);
    cadd_k(b, &out[..cfg.fold_w], f.c, parity, room - 2);
    b.x(u);
    b.cx_all(u, &out[..cfg.fold_w]);
    b.x(u);
    b.cx(u, parity);
    let low = out.remove(0);
    b.release_clean(low);
    out.push(parity);
    let m = b.alloc_bit();
    b.hmr(u, m);
    b.release_clean(u);
    b.push_condition(m);
    // In the established finite-window contract the top bits of the value
    // before halving are this public one-position view of the result.
    lt(
        b,
        &out[n - cfg.cmp_w - 1..n - 1],
        &ad[n - cfg.cmp_w..],
        None,
        Act::Phase(Some(e)),
        room,
    );
    b.pop_condition();
    b.free_bit(m);
}

/// Independent inverse of [`madd_hlv`] for disjoint low-fold and top-compare
/// windows. The final rotated top window reconstructs the original full-add
/// carry `u`; after rotating the word back, `u` and the stored high bit recover
/// the raw low sum bit. One controlled subtraction then undoes the fused
/// pseudo-Mersenne correction before the original multiplicand add is
/// reversed. The disjoint-window promise is essential: when the low fold
/// overlaps the rotated comparison window its discarded carry changes the
/// predicate (the rejected small-width prototype hit exactly that case).
pub fn madd_hlv_inv(
    b: &mut Builder,
    f: Field,
    cfg: Cfg,
    out: &mut Vec<Q>,
    a: &[Q],
    e: Q,
    room: usize,
) {
    let n = f.n;
    assert_eq!(out.len(), n);
    assert!(cfg.fold_w + cfg.cmp_w + 1 <= n && room >= 8);
    let ad = wires(a);
    let u = b.alloc_qubit();
    lt(
        b,
        &out[n - cfg.cmp_w - 1..n - 1],
        &ad[n - cfg.cmp_w..],
        None,
        Act::Xor(u, Some(e)),
        room - 1,
    );

    let parity = out.pop().expect("register");
    let low = b.alloc_qubit();
    out.insert(0, low);
    b.cx(u, parity); // stored u xor r -> raw low bit r

    b.x(u);
    b.cx_all(u, &out[..cfg.fold_w]);
    b.x(u);
    csub_k(b, &out[..cfg.fold_w], f.c, parity, room - 2);
    b.x(u);
    b.cx_all(u, &out[..cfg.fold_w]);
    b.x(u);
    b.cx(out[0], parity);
    b.release_clean(parity);

    b.x_all(out);
    add_gen(b, out, &ad, Fin::CtlSum(e), Some(u), room - 1);
    b.x_all(out);
    b.release_clean(u);
}

/// Fused `dbl` followed by `madd` for the MSB-first Horner path.
///
/// Let `t` be the old top bit and `u` the carry from adding `e*a` to the
/// shifted low word.  Before reduction the quotient by `2^n` is `q=t+u`.
/// The two separate `+t*c` and `+u*c` corrections used by `dbl; madd` can
/// therefore be replaced by one addition selected from `{0,c,2c}`.  The
/// selector is represented by `r=t xor u` and `v=t&u`; the constants are
/// public, so their possibly-overlapping one bits need only the Clifford
/// combination `r xor v`.
pub fn dbl_madd(b: &mut Builder, f: Field, cfg: Cfg, out: &mut Vec<Q>, a: &[Q], e: Q, room: usize) {
    let n = f.n;
    assert_eq!(out.len(), n);
    assert_eq!(a.len(), n);
    assert!(cfg.fold_w + cfg.cmp_w <= n && room >= 8);

    let t = out.pop().expect("register");
    let low = b.alloc_qubit();
    out.insert(0, low);
    let u = b.alloc_qubit();
    let aad = wires(a);
    add_gen(b, out, &aad, Fin::CtlSum(e), Some(u), room - 2);

    let v = b.alloc_qubit();
    b.ccx(t, u, v);
    b.cx(u, t); // t now holds r = old_t xor u.
    let w = b.alloc_qubit();
    b.cx(t, w);
    b.cx(v, w); // w = r xor v, for bit positions shared by c and 2c.
    let c2 = f.c << 1;
    let qad: Vec<Ad> = (0..cfg.fold_w)
        .map(|i| {
            let cb = i < 128 && ((f.c >> i) & 1) != 0;
            let db = i < 128 && ((c2 >> i) & 1) != 0;
            match (cb, db) {
                (false, false) => Ad::Zero,
                (true, false) => Ad::W(t),
                (false, true) => Ad::W(v),
                (true, true) => Ad::W(w),
            }
        })
        .collect();
    add_gen(b, &out[..cfg.fold_w], &qad, Fin::Sum, None, room - 4);
    b.cx(v, w);
    b.cx(t, w);
    b.release_clean(w);
    b.cx(u, t); // restore old_t.
    // v=t&u was only a control; both inputs are restored here.
    hmr_cz(b, v, t, u);
    b.release_clean(v);

    // c is odd, so result[0] = e*a[0] xor old_t xor u.
    b.ccx(e, a[0], t);
    b.cx(u, t);
    b.cx(out[0], t);
    b.release_clean(t);

    let m = b.alloc_bit();
    b.hmr(u, m);
    b.release_clean(u);
    b.push_condition(m);
    lt(
        b,
        &out[n - cfg.cmp_w..],
        &aad[n - cfg.cmp_w..],
        None,
        Act::Phase(Some(e)),
        room,
    );
    b.pop_condition();
    b.free_bit(m);
}

/// Literal inverse of [`dbl_madd`].  The top-window comparison recovers `u`.
/// The odd correction constant then exposes `t` in the low result bit, after
/// which the selected `q*c` correction and the controlled add are reversed.
pub fn dbl_madd_inv(
    b: &mut Builder,
    f: Field,
    cfg: Cfg,
    out: &mut Vec<Q>,
    a: &[Q],
    e: Q,
    room: usize,
) {
    let n = f.n;
    assert_eq!(out.len(), n);
    assert_eq!(a.len(), n);
    assert!(cfg.fold_w + cfg.cmp_w <= n && room >= 8);
    let aad = wires(a);

    let u = b.alloc_qubit();
    lt(
        b,
        &out[n - cfg.cmp_w..],
        &aad[n - cfg.cmp_w..],
        None,
        Act::Xor(u, Some(e)),
        room - 1,
    );
    let t = b.alloc_qubit();
    b.cx(out[0], t);
    b.ccx(e, a[0], t);
    b.cx(u, t);

    let v = b.alloc_qubit();
    b.ccx(t, u, v);
    b.cx(u, t);
    let w = b.alloc_qubit();
    b.cx(t, w);
    b.cx(v, w);
    let c2 = f.c << 1;
    let qad: Vec<Ad> = (0..cfg.fold_w)
        .map(|i| {
            let cb = i < 128 && ((f.c >> i) & 1) != 0;
            let db = i < 128 && ((c2 >> i) & 1) != 0;
            match (cb, db) {
                (false, false) => Ad::Zero,
                (true, false) => Ad::W(t),
                (false, true) => Ad::W(v),
                (true, true) => Ad::W(w),
            }
        })
        .collect();
    b.x_all(&out[..cfg.fold_w]);
    add_gen(b, &out[..cfg.fold_w], &qad, Fin::Sum, None, room - 4);
    b.x_all(&out[..cfg.fold_w]);
    b.cx(v, w);
    b.cx(t, w);
    b.release_clean(w);
    b.cx(u, t);
    // Same temporary-AND cleanup in the literal inverse.
    hmr_cz(b, v, t, u);
    b.release_clean(v);

    b.x_all(out);
    add_gen(b, out, &aad, Fin::CtlSum(e), Some(u), room - 2);
    b.x_all(out);
    b.free(u);

    let low = out.remove(0);
    b.release_clean(low);
    out.push(t);
}

/// Inverse of [`madd`].
pub fn msub(b: &mut Builder, f: Field, cfg: Cfg, out: &[Q], a: &[Q], e: Q, room: usize) {
    let n = f.n;
    let ad = wires(a);
    let t2 = b.alloc_qubit();
    lt(
        b,
        &out[n - cfg.cmp_w..],
        &ad[n - cfg.cmp_w..],
        None,
        Act::Xor(t2, Some(e)),
        room - 1,
    );
    csub_k(b, &out[..cfg.fold_w], f.c, t2, room - 1);
    b.x_all(out);
    add_gen(b, out, &ad, Fin::CtlSum(e), Some(t2), room - 1);
    b.x_all(out);
    b.free(t2);
}

/// out <- -out (mod p) under s: complement, then subtract (c-1) in the fold window. Self-inverse.
pub fn cneg(b: &mut Builder, f: Field, cfg: Cfg, out: &[Q], s: Q, room: usize) {
    for &q in out {
        b.cx(s, q);
    }
    csub_k(b, &out[..cfg.fold_w], f.c - 1, s, room);
}

/// (lsb_first, extra halvings, extra doublings) for a * b * 2^-k.
pub fn schedule(n: usize, k: usize) -> (bool, usize, usize) {
    if k == 0 {
        (false, 0, 0)
    } else if k >= n {
        (true, k - n, 0)
    } else if k <= n / 2 {
        (false, k, 0)
    } else {
        (true, 0, n - k)
    }
}

/// out = a * bb * 2^-k * (-1)^neg (mod p, lazy), out freshly allocated (returned). a, bb, neg
/// unchanged. Scratch <= cfg.room beyond a, bb, neg and out.
pub fn mul_fwd(
    b: &mut Builder,
    f: Field,
    cfg: Cfg,
    a: &[Q],
    bb: &[Q],
    k: usize,
    neg: Option<Q>,
) -> Vec<Q> {
    let n = f.n;
    assert_eq!(a.len(), n);
    assert_eq!(bb.len(), n);
    let room = cfg.room;
    let mut out = b.alloc_qubits(n);
    let (lsb, xh, xd) = schedule(n, k);
    if lsb {
        for i in 0..n {
            b.ccx(bb[0], a[i], out[i]);
        }
        hlv(b, f, cfg, &mut out, room);
        for i in 1..n {
            if cfg.cmp_w < n && room >= 8 {
                madd_hlv(b, f, cfg, &mut out, a, bb[i], room);
            } else {
                madd(b, f, cfg, &out, a, bb[i], room);
                hlv(b, f, cfg, &mut out, room);
            }
        }
    } else {
        for i in 0..n {
            b.ccx(bb[n - 1], a[i], out[i]);
        }
        for i in (0..n - 1).rev() {
            if n >= 64 && cfg.fold_w + cfg.cmp_w <= n && room >= 8 {
                dbl_madd(b, f, cfg, &mut out, a, bb[i], room);
            } else {
                dbl(b, f, cfg, &mut out, room);
                madd(b, f, cfg, &out, a, bb[i], room);
            }
        }
    }
    if hlv4_eligible(f, cfg) {
        for _ in 0..xh / 4 { hlv4(b, f, cfg, &mut out, room); }
        for _ in 0..xh % 4 { hlv(b, f, cfg, &mut out, room); }
    } else {
        for _ in 0..xh { hlv(b, f, cfg, &mut out, room); }
    }
    for _ in 0..xd {
        dbl(b, f, cfg, &mut out, room);
    }
    if let Some(s) = neg {
        cneg(b, f, cfg, &out, s, room);
    }
    out
}

/// Exact inverse of [`mul_fwd`]: returns the n wires of `out`, back at |0> (still allocated;
/// the caller frees or reuses them).
pub fn mul_inv(
    b: &mut Builder,
    f: Field,
    cfg: Cfg,
    a: &[Q],
    bb: &[Q],
    k: usize,
    neg: Option<Q>,
    mut out: Vec<Q>,
) -> Vec<Q> {
    let n = f.n;
    let room = cfg.room;
    let (lsb, xh, xd) = schedule(n, k);
    if let Some(s) = neg {
        cneg(b, f, cfg, &out, s, room);
    }
    for _ in 0..xd {
        hlv(b, f, cfg, &mut out, room);
    }
    if hlv4_eligible(f, cfg) {
        for _ in 0..xh % 4 { dbl(b, f, cfg, &mut out, room); }
        for _ in 0..xh / 4 { dbl4(b, f, cfg, &mut out, room); }
    } else {
        for _ in 0..xh { dbl(b, f, cfg, &mut out, room); }
    }
    if lsb {
        for i in (1..n).rev() {
            if n >= 64 && cfg.fold_w + cfg.cmp_w + 1 <= n && room >= 8 {
                madd_hlv_inv(b, f, cfg, &mut out, a, bb[i], room);
            } else {
                dbl(b, f, cfg, &mut out, room);
                msub(b, f, cfg, &out, a, bb[i], room);
            }
        }
        dbl(b, f, cfg, &mut out, room);
        for i in 0..n {
            b.ccx(bb[0], a[i], out[i]);
        }
    } else {
        for i in 0..n - 1 {
            if n >= 64 && cfg.fold_w + cfg.cmp_w <= n && room >= 8 {
                dbl_madd_inv(b, f, cfg, &mut out, a, bb[i], room);
            } else {
                msub(b, f, cfg, &out, a, bb[i], room);
                hlv(b, f, cfg, &mut out, room);
            }
        }
        for i in 0..n {
            b.ccx(bb[n - 1], a[i], out[i]);
        }
    }
    out
}

// ─── park doubling and odometer ─────────────────────────────────────────────────────────────

/// Under `fl`: X <- X - p if X >= 2^n (X = x[0..=n], requires x[0] == 0 when fl = 1); the top
/// wire x[n] ends at 0. 1 + (w-1) Toffoli.
pub fn park_fold(b: &mut Builder, f: Field, cfg: Cfg, x: &[Q], fl: Q, room: usize) {
    let n = f.n;
    assert_eq!(x.len(), n + 1);
    let g = b.alloc_qubit();
    b.ccx(fl, x[n], g);
    cadd_k(b, &x[..cfg.fold_w], f.c, g, room - 1);
    b.cx(g, x[n]);
    // g == fl & x[0] now.
    hmr_cz(b, g, fl, x[0]);
    b.release_clean(g);
}

/// Exact inverse of [`park_fold`]: under `fl`, X <- X + p if X odd (x[n] must be 0 when fl = 1).
pub fn park_unfold(b: &mut Builder, f: Field, cfg: Cfg, x: &[Q], fl: Q, room: usize) {
    let n = f.n;
    assert_eq!(x.len(), n + 1);
    let g = b.alloc_qubit();
    b.ccx(fl, x[0], g);
    b.cx(g, x[n]);
    csub_k(b, &x[..cfg.fold_w], f.c, g, room - 1);
    // g == fl & x[n] now.
    hmr_cz(b, g, fl, x[n]);
    b.release_clean(g);
}

/// odo += ctl (mod 2^len). len-1 Toffoli.
pub fn odo_inc(b: &mut Builder, odo: &[Q], ctl: Q, room: usize) {
    if odo.len() == 1 {
        b.cx(ctl, odo[0]);
        return;
    }
    let mut ad = vec![Ad::Zero; odo.len()];
    ad[0] = Ad::W(ctl);
    add_gen(b, odo, &ad, Fin::Sum, None, room);
}

/// odo -= ctl (mod 2^len).
pub fn odo_dec(b: &mut Builder, odo: &[Q], ctl: Q, room: usize) {
    b.x_all(odo);
    odo_inc(b, odo, ctl, room);
    b.x_all(odo);
}

/// target ^= [odo != 0] (carry of odo + 2^len - 1). len-1 Toffoli.
pub fn odo_nonzero_xor(b: &mut Builder, odo: &[Q], target: Q, room: usize) {
    if odo.len() == 1 {
        b.cx(odo[0], target);
        return;
    }
    let ad = vec![Ad::One; odo.len()];
    carry_act(b, odo, &ad, None, Act::Xor(target, None), room);
}
