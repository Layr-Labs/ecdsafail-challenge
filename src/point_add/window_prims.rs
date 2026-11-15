//! window_prims: gate-level primitives for a low Bezout window (G765 PRIMS, port of invent/INV4 `invent/inv4/`).
//!
//! Every routine emits through `B::g` (so it can sit inside a recording and be played inverted) and takes its lanes
//! as slices: the caller chooses the layout. `pool` lanes are DIRTY (any content, restored); clean lanes are used only
//! where the INV4 Python construction uses them (K0's W lanes, invp's optional clean limbs) or where the caller passes
//! them in `Cfg::clean` for the optimised adders (Gidney adders with measured-uncompute ANDs). Nothing here
//! allocates a qubit, and nothing depends on the greedy walk.
//!
//! Conventions: registers are little endian; arithmetic is mod 2^len; constants are given by their low 64 bits
//! (`p` = p mod 2^64, enough for every register below 64 lanes). Python names (rev.py / k.py / k2.py) are kept.
//! With `Cfg::PY` (no clean lane, `fast` off) the gate lists are the Python ones gate for gate, so the CCX counts
//! equal INV4's tables.

use super::prims_builder::{B, G};
use crate::circuit::QubitId;

type Q = QubitId;

/// Optimisation switches. `PY` reproduces INV4's gate lists exactly.
#[derive(Clone, Copy)]
pub struct Cfg<'a> {
    /// lanes known |0> on entry, returned |0>: Gidney adders (n - 1 Toffoli, measured uncompute) and AND-measure
    /// controls where enough of them are given; otherwise the zero-clean TTK forms are used.
    pub clean: &'a [Q],
    /// dirty-only improvements (carry toggle as a carry-only chain + one dirty CCCX: 2n + 3 instead of 4n).
    pub fast: bool,
}
impl Cfg<'static> {
    pub const PY: Cfg<'static> = Cfg { clean: &[], fast: false };
    pub const FAST: Cfg<'static> = Cfg { clean: &[], fast: true };
}

/// p mod 2^64 for secp256k1's field prime p = 2^256 - 2^32 - 977.
pub const P256_LO: u64 = 0xFFFF_FFFE_FFFF_FC2F;

fn mask(n: usize) -> u128 { if n >= 128 { u128::MAX } else { (1u128 << n) - 1 } }

/// Inverse of an odd a mod 2^n (n <= 64).
pub fn inv2k(a: u64, n: usize) -> u64 {
    assert!(a & 1 == 1);
    let mut x: u64 = 1;
    for _ in 0..7 { x = x.wrapping_mul(2u64.wrapping_sub(a.wrapping_mul(x))); }
    (x as u128 & mask(n)) as u64
}

// ------------------------------------------------------------------ recording helpers
/// Gates of `f` without emitting them.
pub fn rec(b: &mut B, f: impl FnOnce(&mut B)) -> Vec<G> {
    b.begin();
    f(b);
    b.end()
}
/// Emit the exact inverse of `f` (AndC / AndU swap, so measured uncomputes stay measured).
pub fn undo(b: &mut B, f: impl FnOnce(&mut B)) {
    let r = rec(b, f);
    b.play(&r, true);
}
/// out ^= c0 & c1 & c2 with one borrowed lane v (any state, restored): 4 CCX (Barenco 7.2).
pub fn cccx_dirty(b: &mut B, c0: Q, c1: Q, c2: Q, out: Q, v: Q) {
    for _ in 0..2 {
        b.ccx(c2, v, out);
        b.ccx(c0, c1, v);
    }
}
/// out ^= c0 & c1 & c2 with a clean lane w (|0> in and out): 2 CCX (AND compute, measured uncompute).
pub fn cccx_clean(b: &mut B, c0: Q, c1: Q, c2: Q, out: Q, w: Q) {
    b.and_c(c0, c1, w);
    b.ccx(w, c2, out);
    b.and_u(c0, c1, w);
}

// ------------------------------------------------------------------ adders
/// t += a mod 2^n; z ^= carry-out if given. TTK (Takahashi-Tani-Kunihiro), no ancilla: 2n - 2 CCX (+1 with z).
pub fn add_ttk(b: &mut B, a: &[Q], t: &[Q], z: Option<Q>) {
    let n = a.len();
    assert_eq!(t.len(), n);
    if n == 0 { return; }
    for i in 1..n { b.cx(a[i], t[i]); }
    if let Some(z) = z { if n >= 2 { b.cx(a[n - 1], z); } }
    for i in (1..n - 1).rev() { b.cx(a[i], a[i + 1]); }
    for i in 0..n - 1 { b.ccx(a[i], t[i], a[i + 1]); }
    if let Some(z) = z { b.ccx(a[n - 1], t[n - 1], z); }
    for i in (1..n).rev() {
        b.cx(a[i], t[i]);
        b.ccx(a[i - 1], t[i - 1], a[i]);
    }
    for i in 1..n.saturating_sub(1) { b.cx(a[i], a[i + 1]); }
    for i in 0..n { b.cx(a[i], t[i]); }
}

/// t += a mod 2^n (z ^= carry-out), Gidney 2018: carries in n - 1 clean lanes, n - 1 AND computes (+1 CCX with z),
/// measured uncompute (0 Toffoli; the inverse, a subtractor, computes where this measures: also n - 1).
pub fn add_gidney(b: &mut B, a: &[Q], t: &[Q], z: Option<Q>, cl: &[Q]) {
    let n = a.len();
    assert_eq!(t.len(), n);
    if n == 0 { return; }
    assert!(cl.len() >= n - 1);
    // c_i (i = 1..n-1) on cl[i-1]; forward: a_i, t_i -> a_i ^ c_i, t_i ^ c_i for i >= 1
    for i in 0..n - 1 {
        if i == 0 {
            b.and_c(a[0], t[0], cl[0]);
        } else {
            let c = cl[i - 1];
            b.cx(c, a[i]);
            b.cx(c, t[i]);
            b.and_c(a[i], t[i], cl[i]);
            b.cx(c, cl[i]);
        }
    }
    let top = n - 1;
    if let Some(z) = z {
        if top >= 1 {
            let c = cl[top - 1];
            b.cx(c, a[top]);
            b.cx(c, t[top]);
            b.ccx(a[top], t[top], z);
            b.cx(c, z);
            b.cx(c, a[top]);
            b.cx(c, t[top]);
        } else {
            b.ccx(a[0], t[0], z);
        }
    }
    b.cx(a[top], t[top]);
    if top >= 1 { b.cx(cl[top - 1], t[top]); }
    for i in (0..n - 1).rev() {
        if i == 0 {
            b.and_u(a[0], t[0], cl[0]);
            b.cx(a[0], t[0]);
        } else {
            let c = cl[i - 1];
            b.cx(c, cl[i]);
            b.and_u(a[i], t[i], cl[i]);
            b.cx(c, a[i]);
            b.cx(a[i], t[i]);
        }
    }
}

/// t += a (z ^= carry-out): Gidney if `cf.clean` holds n - 1 lanes, else TTK.
pub fn add(b: &mut B, cf: Cfg, a: &[Q], t: &[Q], z: Option<Q>) {
    let n = a.len();
    if n >= 2 && cf.clean.len() >= n - 1 { add_gidney(b, a, t, z, cf.clean) } else { add_ttk(b, a, t, z) }
}

/// t += ctrl * a mod 2^n, TTK controlled adder, no ancilla: 3n - 2 CCX.
pub fn cadd_ttk(b: &mut B, ctrl: Q, a: &[Q], t: &[Q]) {
    let n = a.len();
    assert_eq!(t.len(), n);
    if n == 0 { return; }
    for i in 1..n { b.cx(a[i], t[i]); }
    for i in (1..n - 1).rev() { b.cx(a[i], a[i + 1]); }
    for i in 0..n - 1 { b.ccx(a[i], t[i], a[i + 1]); }
    for i in (1..n).rev() {
        b.ccx(ctrl, a[i], t[i]);
        b.ccx(a[i - 1], t[i - 1], a[i]);
    }
    for i in 1..n.saturating_sub(1) { b.cx(a[i], a[i + 1]); }
    for i in 1..n { b.cx(a[i], t[i]); }
    b.ccx(ctrl, a[0], t[0]);
}

/// t += ctrl * a mod 2^n with n - 1 clean lanes: the carries of a + t (uncontrolled; ctrl * carry is the carry of
/// ctrl * a + t) by n - 1 AND computes, the control applied only to the sum bits (n CCX), measured uncompute:
/// 2n - 1 Toffoli.
pub fn cadd_gidney(b: &mut B, ctrl: Q, a: &[Q], t: &[Q], cl: &[Q]) {
    let n = a.len();
    assert_eq!(t.len(), n);
    if n == 0 { return; }
    assert!(cl.len() >= n - 1);
    for i in 0..n - 1 {
        if i == 0 {
            b.and_c(a[0], t[0], cl[0]);
        } else {
            let c = cl[i - 1];
            b.cx(c, a[i]);
            b.cx(c, t[i]);
            b.and_c(a[i], t[i], cl[i]);
            b.cx(c, cl[i]);
        }
    }
    let top = n - 1;
    if top >= 1 {
        let c = cl[top - 1];
        b.cx(c, a[top]);
        b.ccx(ctrl, a[top], t[top]);
        b.cx(c, a[top]);
    } else {
        b.ccx(ctrl, a[0], t[0]);
    }
    for i in (0..n - 1).rev() {
        if i == 0 {
            b.and_u(a[0], t[0], cl[0]);
            b.ccx(ctrl, a[0], t[0]);
        } else {
            let c = cl[i - 1];
            b.cx(c, cl[i]);
            b.and_u(a[i], t[i], cl[i]);
            b.cx(c, t[i]);
            b.ccx(ctrl, a[i], t[i]); // a lane holds a_i ^ c_i
            b.cx(c, a[i]);
        }
    }
}

/// t += ctrl * a: controlled Gidney (2n - 1 Toffoli) if `cf.clean` holds n - 1 lanes, else TTK (3n - 2).
pub fn cadd(b: &mut B, cf: Cfg, ctrl: Q, a: &[Q], t: &[Q]) {
    let n = a.len();
    if n >= 2 && cf.clean.len() >= n - 1 { cadd_gidney(b, ctrl, a, t, cf.clean) } else { cadd_ttk(b, ctrl, a, t) }
}

/// t += a with len(a) <= len(t): the missing high addend bits are a DIRTY pad (added, then subtracted).
pub fn add_p(b: &mut B, cf: Cfg, a: &[Q], t: &[Q], pool: &[Q], z: Option<Q>) {
    let a = &a[..a.len().min(t.len())];
    let (w, ww) = (a.len(), t.len());
    if w == 0 { return; }
    if w == ww { return add(b, cf, a, t, z); }
    let pad = &pool[..ww - w];
    let mut ap = a.to_vec();
    ap.extend_from_slice(pad);
    add(b, cf, &ap, t, z);
    undo(b, |b| add(b, cf, pad, &t[w..], z));
}

/// t += ctrl * a with len(a) <= len(t) (dirty pad as in `add_p`).
pub fn cadd_p(b: &mut B, cf: Cfg, ctrl: Q, a: &[Q], t: &[Q], pool: &[Q]) {
    let a = &a[..a.len().min(t.len())];
    let (w, ww) = (a.len(), t.len());
    if w == 0 { return; }
    if w == ww { return cadd(b, cf, ctrl, a, t); }
    let pad = &pool[..ww - w];
    let mut ap = a.to_vec();
    ap.extend_from_slice(pad);
    cadd(b, cf, ctrl, &ap, t);
    undo(b, |b| cadd(b, cf, ctrl, pad, &t[w..]));
}

/// t += (c0 & c1) * a (len(a) <= len(t)). Clean lane: AND-measure into it (1 Toffoli + the adder). Dirty only: the
/// complement trick on a borrowed lane v (pool[0]): CX(v -> t); t += v a; v ^= c0 c1; t -= v a; v ^= c0 c1;
/// CX(v -> t) leaves t - (c0 c1) a for either v, and its inverse is played (2 adders + 2 CCX).
pub fn cc_add_p(b: &mut B, cf: Cfg, c0: Q, c1: Q, a: &[Q], t: &[Q], pool: &[Q]) {
    if a.is_empty() || t.is_empty() { return; }
    if let Some((&w, rest)) = cf.clean.split_first() {
        let cf2 = Cfg { clean: rest, fast: cf.fast };
        b.and_c(c0, c1, w);
        cadd_p(b, cf2, w, a, t, pool);
        b.and_u(c0, c1, w);
        return;
    }
    let (v, pool2) = (pool[0], &pool[1..]);
    undo(b, |b| {
        for &q in t { b.cx(v, q); }
        cadd_p(b, cf, v, a, t, pool2);
        b.ccx(c0, c1, v);
        undo(b, |b| cadd_p(b, cf, v, a, t, pool2));
        b.ccx(c0, c1, v);
        for &q in t { b.cx(v, q); }
    });
}

// ------------------------------------------------------------------ multiplies
/// R *= x mod 2^n in place (x odd, explicit, unchanged; x[0] is not read). `skip`: the low `skip` lanes of R are
/// known |0> (their adders are skipped). Top-down controlled adds, 1.5 n^2 CCX.
pub fn imul(b: &mut B, cf: Cfg, r: &[Q], x: &[Q], pool: &[Q], skip: usize) {
    let n = r.len();
    if n < 2 { return; }
    for i in (skip..=n - 2).rev() {
        let hi = (n - i).min(x.len());
        let xs = if hi > 1 { &x[1..hi] } else { &x[0..0] };
        cadd_p(b, cf, r[i], xs, &r[i + 1..], pool);
    }
}
/// R /= x mod 2^n (inverse of `imul`).
pub fn idiv(b: &mut B, cf: Cfg, r: &[Q], x: &[Q], pool: &[Q]) { undo(b, |b| imul(b, cf, r, x, pool, 0)); }

/// R *= x^ctrl in place (controlled multiply): every adder is controlled by ctrl & R_i (`cc_add_p`).
pub fn cimul(b: &mut B, cf: Cfg, ctrl: Q, r: &[Q], x: &[Q], pool: &[Q]) {
    let n = r.len();
    if n < 2 { return; }
    for i in (0..=n - 2).rev() {
        let hi = (n - i).min(x.len());
        let xs = if hi > 1 { &x[1..hi] } else { &x[0..0] };
        cc_add_p(b, cf, ctrl, r[i], xs, &r[i + 1..], pool);
    }
}
/// R /= x^ctrl in place.
pub fn cidiv(b: &mut B, cf: Cfg, ctrl: Q, r: &[Q], x: &[Q], pool: &[Q]) { undo(b, |b| cimul(b, cf, ctrl, r, x, pool)); }

/// R += a * y mod 2^n (multiply-accumulate; a, y explicit and unchanged).
pub fn mac(b: &mut B, cf: Cfg, r: &[Q], a: &[Q], y: &[Q], pool: &[Q]) {
    let n = r.len();
    for i in 0..n.min(a.len()) {
        let ys = &y[..(n - i).min(y.len())];
        cadd_p(b, cf, a[i], ys, &r[i..], pool);
    }
}

// ------------------------------------------------------------------ increments and constants
/// R += 1 with a dirty register d = pool[..n]: R -= d; d = ~d; R -= d; d = ~d. With n - 2 clean lanes in `cf`, an
/// AND chain (n - 2 Toffoli, measured uncompute) instead.
pub fn inc(b: &mut B, cf: Cfg, r: &[Q], pool: &[Q]) {
    let n = r.len();
    if n == 0 { return; }
    if n == 1 { b.x(r[0]); return; }
    if n == 2 && (cf.fast || !cf.clean.is_empty()) { b.cx(r[0], r[1]); b.x(r[0]); return; }
    if n >= 3 && cf.clean.len() >= n - 2 {
        // k_i = AND(r[0..i]) for i = 1..n-1: k_1 = r[0], k_i on cl[i-2]
        let cl = cf.clean;
        let k = |i: usize| if i == 1 { r[0] } else { cl[i - 2] };
        for i in 2..n { b.and_c(k(i - 1), r[i - 1], cl[i - 2]); }
        for i in (1..n).rev() {
            b.cx(k(i), r[i]);
            if i >= 2 { b.and_u(k(i - 1), r[i - 1], cl[i - 2]); }
        }
        b.x(r[0]);
        return;
    }
    let d = &pool[..n];
    let cfa = Cfg { clean: &[], fast: cf.fast };
    for _ in 0..2 {
        undo(b, |b| add(b, cfa, d, r, None));
        for &q in d { b.x(q); }
    }
}

/// Signed binary digits (position, +-1) of K mod 2^n (Python `naf`).
pub fn naf(k: u128, n: usize) -> Vec<(usize, i8)> {
    let mut k = k & mask(n);
    let mut ds = vec![];
    let mut j = 0;
    while k != 0 && j < n {
        if k & 1 == 1 {
            let d: i8 = if j == n - 1 || k & 3 == 1 { 1 } else { -1 };
            ds.push((j, d));
            if d > 0 { k -= 1 } else { k += 1 }
        }
        k >>= 1;
        j += 1;
    }
    ds
}

/// R += K (classical) mod 2^n: one dirty increment per signed digit.
pub fn const_add(b: &mut B, cf: Cfg, r: &[Q], k: u64, pool: &[Q]) {
    for (j, d) in naf(k as u128, r.len()) {
        if d > 0 { inc(b, cf, &r[j..], pool) } else { undo(b, |b| inc(b, cf, &r[j..], pool)) }
    }
}

/// R += ctrl * K mod 2^n.
pub fn c_const_add(b: &mut B, cf: Cfg, ctrl: Q, r: &[Q], k: u64, pool: &[Q]) {
    for (j, d) in naf(k as u128, r.len()) {
        if d > 0 { add_p(b, cf, &[ctrl], &r[j..], pool, None) } else { undo(b, |b| add_p(b, cf, &[ctrl], &r[j..], pool, None)) }
    }
}

/// R *= K in place for an odd classical K (top-down controlled constant adds).
pub fn constmul(b: &mut B, cf: Cfg, r: &[Q], k: u64, pool: &[Q]) {
    let n = r.len();
    if n < 2 { return; }
    for i in (0..=n - 2).rev() { c_const_add(b, cf, r[i], &r[i + 1..], k >> 1, pool); }
}

/// R = -R mod 2^n.
pub fn neg(b: &mut B, cf: Cfg, r: &[Q], pool: &[Q]) {
    for &q in r { b.x(q); }
    inc(b, cf, r, pool);
}

/// R *= (1 + 2^j) in place: add the ORIGINAL j-bit chunks top-down, each with carry to the top.
pub fn mul1p(b: &mut B, cf: Cfg, r: &[Q], j: usize, pool: &[Q]) {
    let m = r.len();
    if j == 0 || j >= m { return; }
    let mut c = (m - 1) / j;
    while c >= 1 {
        let lo = (c - 1) * j;
        let w = j.min(m - c * j);
        add_p(b, cf, &r[lo..lo + w], &r[c * j..], pool, None);
        c -= 1;
    }
}

/// R *= K in place for a classical K = 1 mod 4, as a product of (1 + 2^j) factors (j >= 2).
pub fn constmul14(b: &mut B, cf: Cfg, r: &[Q], k: u64, pool: &[Q]) {
    let m = r.len();
    let mk = mask(m) as u64;
    let mut k = k & mk;
    assert!(m < 2 || k % 4 == 1, "constmul14 needs K = 1 mod 4");
    for j in 2..m {
        if (k >> j) & 1 == 1 {
            mul1p(b, cf, r, j, pool);
            let f = inv2k(1u64.wrapping_add(1u64 << j), m);
            k = (((k as u128) * (f as u128)) as u64) & mk;
        }
    }
}

// ------------------------------------------------------------------ in-place p / x
/// x -> p / x mod 2^n in place (x odd), dirty lanes only (INV4 section 4, seed S1 with p folded in). `limbs`: clean
/// lanes handed to the recursion (a clean d limb at the first level it fits, as INV4's g). Pool needs about
/// 1.5 n + 2 lanes disjoint from x.
pub fn invp(b: &mut B, cf: Cfg, x: &[Q], pool: &[Q], p: u64, limbs: &[Q]) {
    let n = x.len();
    if n <= 1 { return; }
    if n == 2 {
        if (p >> 1) & 1 == 1 { b.x(x[1]); }
        return;
    }
    let l = (n + 1) / 2;
    let m = n - l;
    let (lo, hi) = x.split_at(l);
    let (d, rest, skip, g2, pool2): (&[Q], &[Q], usize, &[Q], &[Q]) = if limbs.len() >= l {
        (&limbs[..l], &limbs[l..], l, &pool[..m], &pool[m..])
    } else {
        (&pool[..l], limbs, 0, &pool[l..l + m], &pool[l + m..])
    };
    let mut rr = d.to_vec();
    rr.extend_from_slice(hi);
    let mut xt = lo.to_vec();
    xt.extend_from_slice(g2);
    let kc;
    if m >= 2 && (p >> 1) & 1 == 1 {
        undo(b, |b| add(b, cf, g2, hi, None)); // hi = x_hi - g2, constant -p = 1 mod 4
        kc = p.wrapping_neg();
    } else {
        for &q in g2 { b.x(q); }
        add(b, cf, g2, hi, None);
        for &q in g2 { b.x(q); }
        for &q in hi { b.x(q); } // hi = g2 - x_hi (complement trick), constant p
        kc = p;
    }
    idiv(b, cf, hi, &lo[..m], pool2);
    idiv(b, cf, hi, &lo[..m], pool2);
    constmul14(b, cf, hi, kc, pool2);
    imul(b, cf, &rr, &xt, pool2, skip);
    const_add(b, cf, &rr, p, pool2);
    idiv(b, cf, &rr, &xt, pool2); // R += p / xt: d += y_lo, hi = y_hi + carry(d + y_lo)
    invp(b, cf, lo, pool, p, rest); // x_lo -> y_lo (d, g2 restored dirty space)
    undo(b, |b| add_p(b, cf, lo, &rr, pool2, None)); // R -= y_lo: restores d, cancels the carry
}

// ------------------------------------------------------------------ carry toggle
/// t ^= ctrl * carry(W + s), W on lanes `wl` (D lanes), s = s[..D-k] shifted by k (k > 0: s is the VIEW 2^k tB, pass
/// the tB lanes). `borrow`: t ^= ctrl * [W < s] instead (remainder rows). u: a dirty lane (Python form) - also the
/// borrowed lane of the fast form.
pub fn carry_toggle(b: &mut B, cf: Cfg, wl: &[Q], s: &[Q], k: usize, ctrl: Q, t: Q, u: Q, borrow: bool) {
    let d = wl.len();
    let n = d.saturating_sub(k);
    let (sa, wb) = (&s[..n], &wl[k..]);
    if cf.fast || !cf.clean.is_empty() {
        // carry-only TTK prefix (n - 1 CCX), the top cell targets t directly, prefix undone
        if n == 0 { return; }
        if borrow { for &q in wb { b.x(q); } } // [W < s] = carry(s + ~W)
        if n >= 2 { b.ccx(ctrl, sa[n - 1], t); }
        let pre = rec(b, |b| {
            for i in 1..n { b.cx(sa[i], wb[i]); }
            for i in (1..n - 1).rev() { b.cx(sa[i], sa[i + 1]); }
            for i in 0..n - 1 { b.ccx(sa[i], wb[i], sa[i + 1]); }
        });
        b.play(&pre, false);
        match cf.clean.first() {
            Some(&w) => cccx_clean(b, ctrl, sa[n - 1], wb[n - 1], t, w),
            None => cccx_dirty(b, ctrl, sa[n - 1], wb[n - 1], t, u),
        }
        b.play(&pre, true);
        if borrow { for &q in wb { b.x(q); } }
        return;
    }
    let a = rec(b, |b| add(b, cf, sa, wb, Some(u)));
    b.ccx(ctrl, u, t);
    b.play(&a, borrow);
    b.ccx(ctrl, u, t);
    b.play(&a, !borrow);
}

// ------------------------------------------------------------------ carriers and the carry constructions
/// Words of the page, D low lanes each: a = A_low, bw = B_low (odd), tb = tB_low. W = (p - A tB) / B mod 2^D.
#[derive(Clone, Copy)]
pub struct Page<'a> { pub a: &'a [Q], pub bw: &'a [Q], pub tb: &'a [Q] }

/// K1A carrier forward (needs tB odd): A lanes -> W = (p - A tB) / B. Inverse with `undo`.
pub fn k1a_fwd(b: &mut B, cf: Cfg, pg: Page, pool: &[Q], p: u64) {
    imul(b, cf, pg.a, pg.tb, pool, 0);
    for &q in pg.a { b.x(q); }
    const_add(b, cf, pg.a, p.wrapping_add(1), pool);
    idiv(b, cf, pg.a, pg.bw, pool);
}
/// K2 carrier forward (any parities): A -> a = A / B, B -> p / B (invp), B -= a tB: B lanes hold W. `limbs`: clean
/// limbs for invp (INV4's g; usually empty). This is also the in-place format switch (A, B) -> (A / B, W).
pub fn k2_fwd(b: &mut B, cf: Cfg, pg: Page, pool: &[Q], p: u64, limbs: &[Q]) {
    idiv(b, cf, pg.a, pg.bw, pool);
    invp(b, cf, pg.bw, pool, p, limbs);
    undo(b, |b| mac(b, cf, pg.bw, pg.a, pg.tb, pool));
}

/// K1A: t ^= ctrl * carry(W + s) (or the borrow [W < s]); s = s[..D-k] << k (view: s = tb). Zero clean lanes; tB odd.
pub fn k1a(b: &mut B, cf: Cfg, pg: Page, s: &[Q], k: usize, ctrl: Q, t: Q, pool: &[Q], p: u64, borrow: bool) {
    let f = rec(b, |b| k1a_fwd(b, cf, pg, pool, p));
    b.play(&f, false);
    carry_toggle(b, cf, pg.a, s, k, ctrl, t, pool[0], borrow);
    b.play(&f, true);
}
/// K1T: carrier tB (needs A odd; s on its own lanes, not a view of tB).
pub fn k1t(b: &mut B, cf: Cfg, pg: Page, s: &[Q], ctrl: Q, t: Q, pool: &[Q], p: u64, borrow: bool) {
    let f = rec(b, |b| {
        imul(b, cf, pg.tb, pg.a, pool, 0);
        for &q in pg.tb { b.x(q); }
        const_add(b, cf, pg.tb, p.wrapping_add(1), pool);
        idiv(b, cf, pg.tb, pg.bw, pool);
    });
    b.play(&f, false);
    carry_toggle(b, cf, pg.tb, s, 0, ctrl, t, pool[0], borrow);
    b.play(&f, true);
}
/// K2: universal carry (any parities of A, tB), zero clean lanes.
pub fn k2(b: &mut B, cf: Cfg, pg: Page, s: &[Q], k: usize, ctrl: Q, t: Q, pool: &[Q], p: u64, borrow: bool, limbs: &[Q]) {
    let f = rec(b, |b| k2_fwd(b, cf, pg, pool, p, limbs));
    b.play(&f, false);
    carry_toggle(b, cf, pg.bw, s, k, ctrl, t, pool[0], borrow);
    b.play(&f, true);
}
/// K0 baseline: materialise W in D CLEAN lanes `wc` (|0> in and out).
pub fn k0(b: &mut B, cf: Cfg, pg: Page, s: &[Q], k: usize, ctrl: Q, t: Q, wc: &[Q], pool: &[Q], p: u64, borrow: bool) {
    let f = rec(b, |b| {
        for (i, &q) in wc.iter().enumerate() { if (p >> i) & 1 == 1 { b.x(q); } }
        undo(b, |b| mac(b, cf, wc, pg.a, pg.tb, pool));
        idiv(b, cf, wc, pg.bw, pool);
    });
    b.play(&f, false);
    carry_toggle(b, cf, wc, s, k, ctrl, t, pool[0], borrow);
    b.play(&f, true);
}

/// Words with bit D (D + 1 lanes each) for K1V / K4: a1, b1 (odd), t1 = tB; h = bit D of tA (lowest stored lane).
#[derive(Clone, Copy)]
pub struct Page1<'a> { pub a1: &'a [Q], pub b1: &'a [Q], pub t1: &'a [Q], pub h: Q }

/// K1V: s = the VIEW 2^k tB_low. Carrier = the tB lanes: Z -> (p - (A -+ 2^k B) Z) / B mod 2^(D+1) on (tB_low, u).
/// Needs A - 2^k B odd. `borrow`: t ^= ctrl * [W < 2^k tB] (shear A += 2^k B; same parity condition).
pub fn k1v(b: &mut B, cf: Cfg, pg: Page1, k: usize, ctrl: Q, t: Q, pool: &[Q], p: u64, borrow: bool) {
    let (a1, b1, t1) = (pg.a1, pg.b1, pg.t1);
    let d = a1.len() - 1;
    let (u, v, pool) = (pool[0], pool[1], &pool[2..]);
    b.ccx(ctrl, u, t);
    b.ccx(ctrl, pg.h, t);
    cccx_dirty(b, ctrl, a1[0], t1[d], t, v);
    if k >= 1 { b.ccx(ctrl, t1[d - k], t); }
    let shear = rec(b, |b| add(b, cf, &b1[..d + 1 - k], &a1[k..], None)); // A += 2^k B
    b.play(&shear, !borrow); // carry: A -= 2^k B (the partner V row's low word)
    let mut r = t1[..d].to_vec();
    r.push(u);
    let f = rec(b, |b| {
        imul(b, cf, &r, a1, pool, 0);
        for &q in &r { b.x(q); }
        const_add(b, cf, &r, p.wrapping_add(1), pool);
        idiv(b, cf, &r, b1, pool);
    });
    b.play(&f, false);
    b.ccx(ctrl, u, t);
    b.play(&f, true);
    b.play(&shear, borrow);
}

/// K4 (literal reading: s on its own D lanes): (s, u) += (p - A tB) / B mod 2^(D+1); top lane = u ^ h ^ carry.
pub fn k4(b: &mut B, cf: Cfg, pg: Page1, s: &[Q], ctrl: Q, t: Q, pool: &[Q], p: u64) {
    let (u, pool) = (pool[0], &pool[1..]);
    let mut r = s.to_vec();
    r.push(u);
    b.ccx(ctrl, u, t);
    b.ccx(ctrl, pg.h, t);
    let cj = rec(b, |b| {
        imul(b, cf, &r, pg.b1, pool, 0);
        const_add(b, cf, &r, p, pool);
        undo(b, |b| mac(b, cf, &r, pg.a1, pg.t1, pool));
        idiv(b, cf, &r, pg.b1, pool);
    });
    b.play(&cj, false);
    b.ccx(ctrl, u, t);
    b.play(&cj, true);
}

/// Which carrier holds W while it is used.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Carrier { K1A, K2 }

/// E += +-(ctrl *) 2^j W (W implicit, zero-extended into E[j..]) through a carrier: the carrier's lanes hold W for the
/// add and are restored. E must be disjoint from the page and the pool (E is not an input of W). ctrl = None: always.
pub fn add_implicit(b: &mut B, cf: Cfg, car: Carrier, pg: Page, e: &[Q], j: usize, ctrl: Option<Q>, sub: bool,
                    pool: &[Q], p: u64) {
    let f = rec(b, |b| match car {
        Carrier::K1A => k1a_fwd(b, cf, pg, pool, p),
        Carrier::K2 => k2_fwd(b, cf, pg, pool, p, &[]),
    });
    let wl = if car == Carrier::K1A { pg.a } else { pg.bw };
    b.play(&f, false);
    if j < e.len() {
        let g = rec(b, |b| match ctrl {
            Some(c) => cadd_p(b, cf, c, wl, &e[j..], pool),
            None => add_p(b, cf, wl, &e[j..], pool, None),
        });
        b.play(&g, sub);
    }
    b.play(&f, true);
}

/// Affine format switch Z -> (p - X Z) / Y mod 2^n in place (X, Y odd, explicit, unchanged); its inverse is the same
/// switch with X and Y exchanged. With the page relation a tb + b ta = p (mod 2^D), INV2 section 3:
/// same-kind  ta implicit -> tb implicit: Z = tb, X = a, Y = b (lanes then hold ta); b -> a: Z = a, X = tb, Y = ta;
/// cross-kind ta implicit -> a implicit: Z = a, X = tb, Y = b (lanes then hold ta); tb -> b: Z = b, X = ta, Y = a, ...
pub fn aff_switch(b: &mut B, cf: Cfg, z: &[Q], x: &[Q], y: &[Q], pool: &[Q], p: u64) {
    imul(b, cf, z, x, pool, 0);
    for &q in z { b.x(q); }
    const_add(b, cf, z, p.wrapping_add(1), pool);
    idiv(b, cf, z, y, pool);
}

#[cfg(test)]
#[path = "window_prims_tests.rs"]
mod tests;
