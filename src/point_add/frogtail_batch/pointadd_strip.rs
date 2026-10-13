//! frogstrip point addition: frogtail's shell with the frogstrip walk (+-1 digits, rot4 strip barrel, ~300 ticks) as
//! the inversion core: 1/dx = (-1)^S C' 2^-H0 with H0 a classical bound on a walk's halvings. Outer structure as frogdrop's (two
//! divisions, measurement-based erasure of dy and lambda after Luo et al. / gnuchev):
//!
//!   dx = x - ox, dy = y - oy
//!   division 1:  walk on dx' (dx made odd: dx or p - dx) -> C with 1/dx = (-1)^S C 2^-T;  lambda = (-1)^S C dy 2^-T;
//!                measure dy away;  inverse walk -> dx;  recompute dy = lambda * dx, fix its phase, uncompute
//!   x:  dx' = lambda^2 - dx - 3 ox;   y:  ndy = -lambda * dx';  measure lambda away
//!   division 2:  walk on dx' -> C';  recompute lambda = -ndy (-1)^S' C' 2^-T, fix its phase, uncompute;
//!                inverse walk -> dx'
//!   x3 = dx' + ox,  y3 = ndy - oy

use super::builder::{B, G};
use super::frogstrip::{e0, unabsorb, SWalk, JS, SHB};
use super::frogtail::{Scr, QB};
use super::strip_model::{SSched, EB};
use super::modp_frogdrop::load_bits;
use super::modp_ft::{
    ctrl_neg, mod_double_n, modadd, modsub, product_inv_sum_transport, product_sum_transport,
    product_tail_neg_s_sum_transport, product_tail_neg_s_uncompute_sum_transport, product_tail_neg_stream, Ms,
};
use crate::circuit::{BitId, QubitId};

const FIELD_C: u128 = (1u128 << 32) + 977;
const FIELD_C_BITS: usize = 35;
fn c_zero(b: &mut B, bits: &[BitId]) {
    for &x in bits { b.bit_store0(x); }
}
fn c_copy(b: &mut B, dst: &[BitId], src: &[BitId]) {
    for (&d, &s) in dst.iter().zip(src) { b.bit_copy(d, s); }
}
fn c_add_into(b: &mut B, acc: &[BitId], addend: &[BitId]) {
    let carry = b.fresh_bits(1)[0];
    let newcarry = b.fresh_bits(1)[0];
    b.bit_store0(carry);
    for (i, &a0) in acc.iter().enumerate() {
        b.bit_store0(newcarry);
        if let Some(&x) = addend.get(i) {
            b.bit_and_xor_into(newcarry, a0, x);
            b.bit_and_xor_into(newcarry, a0, carry);
            b.bit_and_xor_into(newcarry, x, carry);
            b.bit_xor_into(a0, x);
        } else {
            b.bit_and_xor_into(newcarry, a0, carry);
        }
        b.bit_xor_into(a0, carry);
        b.bit_copy(carry, newcarry);
    }
    b.bit_store0(newcarry);
    b.bit_store0(carry);
}
fn c_add_const(b: &mut B, acc: &[BitId], k: u128) {
    let w = (128 - k.leading_zeros() as usize).min(acc.len());
    let addend = b.fresh_bits(w);
    for (i, &x) in addend.iter().enumerate() {
        if (k >> i) & 1 == 1 { b.bit_store1(x); } else { b.bit_store0(x); }
    }
    c_add_into(b, acc, &addend);
    c_zero(b, &addend);
}
fn c_or_const_if(b: &mut B, dst: &[BitId], k: u128, gate: BitId) {
    for (i, &x) in dst.iter().enumerate() {
        if (k >> i) & 1 == 1 {
            b.push_bit_condition(gate);
            b.bit_store1(x);
            b.pop_bit_condition();
        }
    }
}
fn c_times3_mod_p(b: &mut B, coord: &[BitId]) -> Vec<BitId> {
    assert_eq!(coord.len(), 256);
    let s = b.fresh_bits(258);
    c_zero(b, &s);
    for _ in 0..3 { c_add_into(b, &s, coord); }
    let av = b.fresh_bits(FIELD_C_BITS);
    c_zero(b, &av);
    c_or_const_if(b, &av, FIELD_C, s[256]);
    c_or_const_if(b, &av, 2 * FIELD_C, s[257]);
    let r = b.fresh_bits(257);
    c_copy(b, &r[..256], &s[..256]);
    b.bit_store0(r[256]);
    c_add_into(b, &r, &av);
    let tmp = b.fresh_bits(257);
    c_copy(b, &tmp, &r);
    c_add_const(b, &tmp, FIELD_C);
    let out = b.fresh_bits(256);
    for i in 0..256 {
        b.bit_xor_into(tmp[i], r[i]);
        b.bit_copy(out[i], r[i]);
        b.bit_and_xor_into(out[i], tmp[256], tmp[i]);
    }
    for reg in [&tmp, &r, &av, &s] { c_zero(b, reg); }
    out
}

pub const SCHED_STRIP: &str = include_str!("sched_strip.txt");
pub const LSC_STRIP: &str = include_str!("lsc_strip.txt");

/// classical bound on a walk's halvings up to its absorption (the tails' exponent)
pub const H0: usize = 564;
/// lanes of C' = C 2^(H0 - halvings)
pub const RLEN_S: usize = 328;
/// lambda is measured as lambda 2^LHAT (LHAT = H0 - 256), so division 2's recompute needs only the tail's own
/// halvings.
const LHAT: usize = H0 - 256;
/// lambda fix uncompute: tail steps below this run as the inverse of their hybrid-ladder recording
const TAIL_K0: usize = 48;

/// Circuit peak (the inverse walk needs 936); the modular routines take every qubit below it as a carry pool. 949
/// gives the inverse walk's cofactor adds enough pool for a chunk plan on every tick (best score of the sweep).
pub const PEAK0: u64 = 975;
pub fn peak() -> u64 {
    std::env::var("STRIP_PEAK").ok().and_then(|v| v.parse().ok()).unwrap_or(PEAK0)
}

pub fn sched() -> SSched {
    SSched::from_text(SCHED_STRIP, Some(LSC_STRIP))
}

thread_local! {
    /// (name, op index) at every checkpoint, for the per-phase average profile in the tests.
    pub(crate) static CKS: std::cell::RefCell<Vec<(String, usize)>> = const { std::cell::RefCell::new(Vec::new()) };
}

pub(crate) fn ck(b: &B, name: &str) {
    CKS.with(|c| c.borrow_mut().push((name.to_string(), b.ops.len())));
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!(
            "ck {:24} live {} peak {} peak_op {} ops {} tof {} cond_tof {} expected_tof {:.1}",
            name,
            b.live,
            b.peak,
            b.peak_op,
            b.ops.len(),
            b.tof,
            b.tof_cond,
            b.tof as f64 - b.tof_cond as f64 / 2.0,
        );
    }
}

/// A division's state between its forward and inverse walk.
pub(crate) struct Div {
    pub(crate) w: SWalk,
    pub(crate) sch: SSched,
    /// [dx was even] (dx' = p - dx)
    n0: QubitId,
    /// S = s ^ parity ^ 1 ^ n0: 1/dx = (-1)^S C_T 2^-T
    pub(crate) key: QubitId,
    rc: Vec<G>,
    /// C_T's lanes (B's cofactor lanes and RLEN - |B.c| lanes of A, rebuilt by `unabsorb`)
    pub(crate) inv: Vec<QubitId>,
    /// m = ticks since the absorption (kept between the walks)
    mr: Vec<QubitId>,
    /// unabsorb's temps (|0> between the walks)
    tm: Vec<QubitId>,
    /// qubits |0> between the walks (A but C's lanes, B.v's low lane, j - 3)
    parked: Vec<QubitId>,
    /// the forward walk's digit measurements
    m: super::frogstrip::WalkTape,
}

/// Forward walk on dx (in `xq`, value in [1, p)); `dirty` (>= 32 lanes) is borrowed.
pub(crate) fn div_forward(b: &mut B, xq: &[QubitId], dirty: &[QubitId]) -> Div {
    let sch = sched();
    let n0 = b.alloc();
    b.cx(xq[0], n0);
    b.x(n0);
    {
        let ms = Ms::alloc_room(b, peak());
        ctrl_neg(b, &ms, xq, Some(n0));
        ms.release(b);
    }
    let mut bb = xq.to_vec();
    bb.extend(b.alloc_n(sch.w - xq.len()));
    let w = SWalk {
        a: b.alloc_n(sch.w),
        bb,
        q: vec![],
        j: b.alloc_n(JS),
        par: b.alloc(),
        ec: b.alloc_n(EB),
        e0p: e0(&sch, H0) & 1 == 1,
    };
    let room = peak().saturating_sub(b.live + 12) as usize;
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!("forward walk live {} room {room}", b.live + 12);
    }
    let sc = Scr::alloc_fwd(b, dirty, room);
    let m = super::frogstrip::walk_forward_paired(b, &w, &sch, &sc, e0(&sch, H0));
    sc.release(b);
    ck(b, "walk forward end");
    let mr = b.alloc_n(SHB);
    let tm = b.alloc_n(SHB);
    let (inv, key, rc) = unabsorb(b, &w, &sch, RLEN_S, &mr, &tm, dirty);
    b.free_n(&tm);
    // B.v = -2s: lanes 2.. copy lane 1 (s)
    let cz = sch.c[sch.t + 1];
    for l in 2..cz {
        b.cx(w.bf(1), w.bf(l));
    }
    b.cx(w.par, key);
    b.cx(n0, key);
    b.x(key);
    // absorbed shots hold h = 1 (j = 3)
    b.x(w.j[0]);
    let mut parked: Vec<QubitId> = w.a.iter().cloned().filter(|q| !inv.contains(q)).collect();
    parked.push(w.bf(0));
    parked.extend((2..cz).map(|l| w.bf(l)));
    parked.extend(&w.j);
    b.free_n(&parked);
    Div {
        w,
        sch,
        n0,
        key,
        rc,
        inv,
        mr,
        tm,
        parked,
        m,
    }
}

/// Exact inverse of div_forward: dx back in `xq` (= w.bb[0..256)), everything else freed.
pub(crate) fn div_inverse(b: &mut B, dv: Div, xq: &[QubitId], dirty: &[QubitId]) {
    let Div {
        mut w,
        sch,
        n0,
        key,
        rc,
        mr,
        tm,
        parked,
        m,
        ..
    } = dv;
    for &q in parked.iter().chain(&tm) {
        b.acquire(q);
    }
    b.x(w.j[0]);
    b.x(key);
    b.cx(n0, key);
    b.cx(w.par, key);
    for l in 2..sch.c[sch.t + 1] {
        b.cx(w.bf(1), w.bf(l));
    }
    b.play(&rc, true);
    b.free_n(&tm);
    b.free_n(&mr);
    w.q = b.alloc_n(QB);
    let mut sc = Scr::alloc(b, dirty);
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!("inverse walk live before pool {}", b.live);
    }
    sc.pool = b.alloc_n(peak().saturating_sub(b.live) as usize);
    super::frogstrip::walk_inverse_paired(b, &w, &sch, &sc, m, e0(&sch, H0));
    ck(b, "walk inverse end");
    sc.release(b);
    b.free_n(&w.q);
    b.free_n(&w.a);
    b.free_n(&w.bb[xq.len()..]);
    b.free_n(&w.j);
    b.free(w.par);
    b.free_n(&w.ec);
    {
        let ms = Ms::alloc_room(b, peak());
        ctrl_neg(b, &ms, xq, Some(n0));
        ms.release(b);
    }
    b.x(n0);
    b.cx(xq[0], n0);
    b.free(n0);
}

/// C' (`inv`, RLEN_S lanes) <-> lo' = C' mod p on its low 256 lanes (hi kept): the tails then run 256 steps.
/// lo' = lo + hi c mod 2^256 with c = 2^32 + 977.  Materialize
/// hi*977 in a temporary word, add it once to lo, then uncompute it.  This
/// trades classical construction objects and 82 temporary quantum lanes for
/// two fewer full sign-extended adders while staying under the 975Q cap.
fn reduce_ct(b: &mut B, inv: &[QubitId], undo: bool) {
    use super::modp_ft::reduce_hi;
    let tq = b.alloc_n(inv.len() - 256 + 10);
    let ms = Ms::alloc_room(b, peak());
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!("reduce_ct live {} pool {}", b.live, ms.r.len());
    }
    b.begin();
    reduce_hi(b, inv, &tq, &ms.r);
    let r = b.end();
    b.play(&r, undo);
    ms.release(b);
    b.free_n(&tq);
}

/// z = y C 2^-tt (mod p), negated iff neg.0 ^ neg.1 (when given), recorded. (product_tail_neg gives -y C 2^-tt;
/// its negation folds into the sign's.)
fn rec_product_tail_s(
    b: &mut B,
    ms: &Ms,
    z: &[QubitId],
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
    neg: Option<(QubitId, bool)>,
) -> Vec<G> {
    b.begin();
    let mut zz = z.to_vec();
    // Transport both semantic carry boundaries for the whole Horner product.
    // The suffix is consumed by forward inverse arithmetic; the recorded
    // prefix is consumed at per-step seams exposed by its literal inverse.
    product_tail_neg_s_sum_transport(b, ms, &mut zz, c, y, tt, c.len() != 256, 0);
    let neg = neg.map(|(q, f)| (q, !f));
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if let Some((c, flip)) = neg {
        if flip {
            b.x(c);
        }
        ctrl_neg(b, ms, z, Some(c));
        if flip {
            b.x(c);
        }
    }
    b.end()
}

/// Uncompute of rec_product_tail_s's result in z (same arguments): its negation and lane reorder undone, then
/// product_tail_neg_s_uncompute (steps below k0 by the hybrid-ladder recording's inverse).
#[allow(clippy::too_many_arguments)]
fn uncompute_product_tail_s(
    b: &mut B,
    ms: &Ms,
    z: &[QubitId],
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
    neg: Option<(QubitId, bool)>,
    k0: usize,
) {
    let neg = neg.map(|(q, f)| (q, !f));
    if let Some((cq, flip)) = neg {
        if flip {
            b.x(cq);
        }
        ctrl_neg(b, ms, z, Some(cq));
        if flip {
            b.x(cq);
        }
    }
    // the compute's lane reorder (vector after tt halvings: z rotated left by tt), undone
    let mut zz: Vec<QubitId> = z.to_vec();
    zz.rotate_left(tt % 256);
    let mut pos = zz.clone();
    let mut sw = vec![];
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            sw.push((pos[i], pos[j]));
            pos.swap(i, j);
        }
    }
    for &(a, d) in sw.iter().rev() {
        b.swap(a, d);
    }
    product_tail_neg_s_uncompute_sum_transport(b, ms, &mut zz, c, y, tt, c.len() != 256, k0);
    assert_eq!(zz, z);
}

/// z = a * y (mod p) recorded, so the caller can uncompute it.
fn rec_product(
    b: &mut B,
    ms: &Ms,
    z: &[QubitId],
    a: &[QubitId],
    y: &[QubitId],
    negate: bool,
) -> Vec<G> {
    b.begin();
    let mut zz = z.to_vec();
    product_sum_transport(b, ms, &mut zz, a, y);
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if negate {
        ctrl_neg(b, ms, z, None);
    }
    b.end()
}

pub fn point_add(b: &mut B) -> (Vec<QubitId>, Vec<QubitId>) {
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    b.declare_qubits(0, &x);
    b.declare_qubits(1, &y);
    let ox: Vec<BitId> = b.declare_bits(2, 256);
    let oy: Vec<BitId> = b.declare_bits(3, 256);

    // dx, dy
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        load_bits(b, &t, &ox);
        modsub(b, &ms, &x, &t, y[0]);
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t, x[0]);
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }

    // ---------------- division 1
    ck(b, "-- division 1");
    let dv = div_forward(b, &x, &y);
    let sq = (dv.key, false);
    let m1 = b.fresh_bits(256);
    reduce_ct(b, &dv.inv, false);
    {
        // lambda = -dy C' 2^-H0 (negated by the key): dy supplies the digits and is X-measured bit by bit as the
        // tail consumes it (its phase is fixed by the dy recompute), the measured lanes joining the carry pool
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        let mut zz = z.clone();
        product_tail_neg_stream(b, &ms, &mut zz, &y, &dv.inv[..256], H0, &m1);
        let mut pos: Vec<QubitId> = zz.clone();
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        let (kq, flip) = (sq.0, !sq.1);
        if flip {
            b.x(kq);
        }
        ctrl_neg(b, &ms, &z, Some(kq));
        if flip {
            b.x(kq);
        }
        ms.release(b);
        ck(b, "lambda = inv * dy");
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }
    reduce_ct(b, &dv.inv, true);
    div_inverse(b, dv, &x, &y);
    ck(b, "walk inverse 1 end");
    // dy = lambda * dx: recompute, fix the phase of the dy measurement, uncompute
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        let r = rec_product(b, &ms, &z, &y, &x, false);
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m1[i]);
        }
        let mut zz = z.clone();
        product_inv_sum_transport(b, &ms, &mut zz, &y, &x);
        b.free_n(&z);
        ms.release(b);
    }

    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    ck(b, "-- x: dx' = lambda^2 - ");
    {
        // sub_square(x,y), followed by negation, gives y²-x. The imported
        // square owns its complete scratch lifetime and sees only 512 data
        // lanes; no modular pool may co-reside with its retained certificate.
        b.native_square(&x, &y);
        let ms = Ms::alloc_room(b, peak());
        ctrl_neg(b, &ms, &x, None);
        ms.release(b);
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        let ox3 = c_times3_mod_p(b, &ox);
        load_bits(b, &t, &ox3);
        modsub(b, &ms, &x, &t, y[0]);
        load_bits(b, &t, &ox3);
        c_zero(b, &ox3);
        b.free_n(&t);
        ms.release(b);
    }
    // ---------------- ndy = -lambda * dx', measure lambda away
    ck(b, "-- ndy = -lambda * dx',");
    let m2 = b.fresh_bits(256);
    {
        // lambda' = lambda 2^(H0 - 256) is what gets measured (its recompute is then a tail without the H0 - 256
        // trailing halvings): double first, then ndy = -lambda' dx' 2^-(H0 - 256) as a halving tail whose digits
        // come from lambda', each bit X-measured right after its last use (the measured lanes join the carry pool)
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        let mut yy = y.clone();
        mod_double_n(b, &ms, &mut yy, LHAT);
        let mut zz = z.clone();
        product_tail_neg_stream(b, &ms, &mut zz, &yy, &x, LHAT, &m2);
        let mut pos: Vec<QubitId> = zz.clone();
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        ms.release(b);
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }

    // ---------------- division 2: recompute lambda = -ndy / dx' to fix its phase
    ck(b, "-- division 2: recomput");
    let dv = div_forward(b, &x, &y);
    let (sqq, sqf) = (dv.key, false);
    reduce_ct(b, &dv.inv, false);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        let tt = H0 - LHAT;
        let r = rec_product_tail_s(b, &ms, &z, &dv.inv[..256], &y, tt, Some((sqq, !sqf)));
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m2[i]);
        }
        // uncompute: forward operations above step TAIL_K0, the hybrid-ladder recording's inverse below it
        uncompute_product_tail_s(b, &ms, &z, &dv.inv[..256], &y, tt, Some((sqq, !sqf)), TAIL_K0);
        b.free_n(&z);
        ms.release(b);
    }
    reduce_ct(b, &dv.inv, true);
    ck(b, "lambda fix (+ unreduce)");
    div_inverse(b, dv, &x, &y);

    // ---------------- x3 = dx' + ox, y3 = ndy - oy
    ck(b, "-- x3 = dx' + ox, y3 = ");
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        load_bits(b, &t, &ox);
        modadd(b, &ms, &x, &t, y[0]);
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t, x[0]);
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }
    // Fiat-Shamir nonce: one X X pair (identity) on qubit NONCE; fixed op count, so a nonce scan re-hashes only
    // the tail
    b.x(QubitId(super::NONCE as u64));
    b.x(QubitId(super::NONCE as u64));
    ck(b, "end");
    (x, y)
}
