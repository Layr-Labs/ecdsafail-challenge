//! H4.A18: split extended-Euclid in-place modular multiplier and divider,
//! after Khattar et al., "Verifiable quantum advantage via optimized DQI
//! circuits" (arXiv:2510.10967), as used for point addition by
//! Schrottenloher, "Optimized Point Addition Circuits for Elliptic Curve
//! Discrete Logarithms" (arXiv:2606.02235).
//!
//! GCD construction on (u, v) = (q, x), per step: b0 = v mod 2,
//! b1 = [u > v]; record h0 = b0 and h1 = b0 ∧ b1; if h1 swap u, v; if h0
//! v −= u; v /= 2. After enough steps (u, v) = (1, 0) and the history encodes
//! x. Replaying the history in reverse on (r, s) with s ← 2s, s += h0·r,
//! swap if h1 maps (y, 0) to (0, y·x mod q) exactly (the doublings cancel the
//! halvings, so no 2^k factor remains; checked in moonshots/eea_check.py). The
//! inverse replay maps (0, z) to (z/x, 0). Running the GCD backward then
//! rebuilds x from the history, so (x, y) ↦ (x, y·x) or (x, y/x) in place.
//!
//! The (u, v) multiset evolves exactly as in canonical Kaliski, so the
//! tail-fitted widths (`kaliski_widths`) and the policy-B iteration counts
//! apply unchanged. v is x's own register; during the replay x's qubits are
//! |0⟩ and are lent (reserved) to step-local scratch only.

use super::kaliski_fused::{lazy_resize, min_width, uv_width, with_gt_oriented};
use super::*;

pub(super) struct EeaHist {
    h0: Vec<QubitId>,
    h1: Vec<QubitId>,
    /// H4.A19: packed[t] = steps 3t..3t+2 are stored in 5 qubits (h1[3t+2]'s
    /// qubit is freed while packed).
    packed: Vec<bool>,
}

/// H4.A19: history compression (as in Schrottenloher 2026: 3 steps → 5 bits).
/// Each step's (h0, h1) has h1 ⇒ h0, so 3 states; three steps (27 states) fit in
/// 5 bits. This gate list maps (a1,c1,a2,c2,a3,c3) to 5 bits with c3 → 0, using
/// 6 ancillas that all return to 0; its inverse is the reversed list (every gate
/// is self-inverse). 18 Toffoli-class gates. Checked exhaustively on all 27
/// inputs (experiments/moonshots/tri.py).
const TRI: &[(u8, u8, u8, u8)] = {
    // (kind, a, b, t): kind 0 = X(t), 1 = CX(a→t), 2 = CCX(a,b→t), 3 = CSWAP(a; b,t)
    const A1: u8 = 0; const C1: u8 = 1; const A2: u8 = 2; const C2: u8 = 3; const A3: u8 = 4; const C3: u8 = 5;
    const G: u8 = 6; const T: u8 = 7; const M2: u8 = 8; const T2: u8 = 9; const H: u8 = 10; const T3: u8 = 11;
    &[(2, C3, C1, G), (3, G, A1, A2), (3, G, C1, C2), (1, G, 0, A2),
      (0, 0, 0, A2), (2, A2, C2, T), (0, 0, 0, A2), (2, C3, T, G), (0, 0, 0, A2), (2, A2, C2, T), (0, 0, 0, A2),
      (0, 0, 0, A2), (2, A2, C2, M2), (0, 0, 0, A2),
      (0, 0, 0, C1), (0, 0, 0, M2), (2, C1, M2, T2), (0, 0, 0, M2), (0, 0, 0, C1),
      (2, C3, T2, H),
      (0, 0, 0, C1), (0, 0, 0, M2), (2, C1, M2, T2), (0, 0, 0, M2), (0, 0, 0, C1),
      (0, 0, 0, A2), (2, A2, C2, M2), (0, 0, 0, A2),
      (2, H, A1, A3), (0, 0, 0, A3), (2, H, A3, A1), (0, 0, 0, A3), (1, H, 0, C1),
      (0, 0, 0, A1), (2, A1, C1, T3), (0, 0, 0, A1), (2, C3, T3, H), (0, 0, 0, A1), (2, A1, C1, T3), (0, 0, 0, A1),
      (0, 0, 0, A1), (2, A1, C1, C3), (0, 0, 0, A1), (0, 0, 0, A2), (2, A2, C2, C3), (0, 0, 0, A2)]
};

fn tri_apply(b: &mut B, bits: [QubitId; 6], decode: bool) {
    let anc = b.alloc_qubits(6);
    let q = |i: u8| if (i as usize) < 6 { bits[i as usize] } else { anc[i as usize - 6] };
    let mut run = |g: &(u8, u8, u8, u8), b: &mut B| match g.0 {
        0 => b.x(q(g.3)),
        1 => b.cx(q(g.1), q(g.3)),
        2 => b.ccx(q(g.1), q(g.2), q(g.3)),
        _ => cswap(b, q(g.1), q(g.2), q(g.3)),
    };
    if decode {
        for g in TRI.iter().rev() {
            run(g, b);
        }
    } else {
        for g in TRI.iter() {
            run(g, b);
        }
    }
    b.free_vec(&anc);
}

impl EeaHist {
    fn tri_bits(&self, t: usize) -> [QubitId; 6] {
        let i = 3 * t;
        [self.h0[i], self.h1[i], self.h0[i + 1], self.h1[i + 1], self.h0[i + 2], self.h1[i + 2]]
    }
    /// Pack triple t (its three steps' bits must be plain).
    fn pack(&mut self, b: &mut B, t: usize) {
        if !H4_HIST_PACK {
            return;
        }
        tri_apply(b, self.tri_bits(t), false);
        b.free(self.h1[3 * t + 2]);
        self.packed[t] = true;
    }
    /// Unpack triple t if it is packed.
    fn unpack(&mut self, b: &mut B, t: usize) {
        if t >= self.packed.len() || !self.packed[t] {
            return;
        }
        self.h1[3 * t + 2] = b.alloc_qubit_unreserved();
        tri_apply(b, self.tri_bits(t), true);
        self.packed[t] = false;
    }
}

/// H4.A22: the GCD's comparison [u > v] looks only at the top CMP_BITS bits of
/// the step's fitted window (MSB comparison, after Schrottenloher 2026). It is
/// wrong only if u > v while u and v agree on all of those bits; census
/// (experiments/moonshots/prefix.py, 30k inputs): P(common prefix ≥ 88) =
/// 3.4e-7, falling ≈ 0.6× per bit, so ≈ 5e-16 per comparison at 128 bits
/// (≈ 1.5e-13 per point addition). Forward and backward use the same predicate.
const CMP_BITS: usize = 128;

fn cmp_lo(w: usize) -> usize {
    if H4_MSB_CMP && w > CMP_BITS { w - CMP_BITS } else { 0 }
}

/// GCD construction. x (n qubits, value in [1, q)) is consumed: on return its
/// qubits are |0⟩ and freed into the reserved set.
fn gcd_forward(b: &mut B, x: &[QubitId], iters: usize, p: U256) -> EeaHist {
    let n = x.len();
    let mut u = b.alloc_qubits(n);
    for j in 0..n {
        if bit(p, j) {
            b.x(u[j]);
        }
    }
    let mut hist = EeaHist { h0: Vec::with_capacity(iters), h1: Vec::with_capacity(iters), packed: vec![false; iters / 3] };
    for i in 0..iters {
        let w = uv_width(n, i);
        let mw = min_width(n, i);
        lazy_resize(b, &mut u, w);
        let h0 = b.alloc_qubit();
        b.cx(x[0], h0);
        let h1 = b.alloc_qubit();
        let lgt = b.alloc_qubit();
        let lo = cmp_lo(w);
        with_gt_oriented(b, &u[lo..w], &x[lo..w], None, lgt, |b| b.ccx(h0, lgt, h1));
        b.free(lgt);
        for j in 0..w {
            cswap(b, h1, u[j], x[j]);
        }
        // v −= h0·u; after the swap u = min(u, v) whenever h0 = 1.
        let tmp = b.alloc_qubits(w);
        for j in 0..mw {
            b.ccx(h0, u[j], tmp[j]);
        }
        sub_nbit_qq_fast(b, &tmp, &x[..w]);
        for j in 0..mw {
            let m = b.alloc_bit();
            b.hmr(tmp[j], m);
            b.cz_if(h0, u[j], m);
        }
        b.free_vec(&tmp);
        // v /= 2 (v is even here): relabel.
        for j in 0..w - 1 {
            b.swap(x[j], x[j + 1]);
        }
        hist.h0.push(h0);
        hist.h1.push(h1);
        if i % 3 == 2 {
            hist.pack(b, i / 3);
        }
    }
    // (u, v) = (1, 0).
    b.x(u[0]);
    b.free_vec(&u);
    for &q in x.iter().rev() {
        b.free_reserved(q);
    }
    hist
}

/// Inverse of `gcd_forward`: re-acquires x's exact qubits, rebuilds x from the
/// history and frees the history.
fn gcd_backward(b: &mut B, x: &[QubitId], mut hist: EeaHist, iters: usize, p: U256) {
    let n = x.len();
    for &q in x.iter() {
        b.alloc_specific(q);
    }
    let mut u = b.alloc_qubits(uv_width(n, iters));
    b.x(u[0]);
    for i in (0..iters).rev() {
        let w = uv_width(n, i);
        let mw = min_width(n, i);
        lazy_resize(b, &mut u, w);
        if i % 3 == 2 {
            hist.unpack(b, i / 3);
        }
        let h0 = hist.h0.pop().expect("history");
        let h1 = hist.h1.pop().expect("history");
        for j in (0..w - 1).rev() {
            b.swap(x[j], x[j + 1]);
        }
        let tmp = b.alloc_qubits(w);
        for j in 0..mw {
            b.ccx(h0, u[j], tmp[j]);
        }
        add_nbit_qq_fast(b, &tmp, &x[..w]);
        for j in 0..mw {
            let m = b.alloc_bit();
            b.hmr(tmp[j], m);
            b.cz_if(h0, u[j], m);
        }
        b.free_vec(&tmp);
        for j in 0..w {
            cswap(b, h1, u[j], x[j]);
        }
        // h1 = h0 ∧ [u > v]: X-measure it; the phase (−1)^{h1} is fixed only
        // when the outcome is 1 (half the shots), with one comparator.
        let c1 = b.alloc_bit();
        b.hmr(h1, c1);
        b.free(h1);
        b.push_condition(c1);
        let lgt = b.alloc_qubit();
        let lo = cmp_lo(w);
        with_gt_oriented(b, &u[lo..w], &x[lo..w], None, lgt, |b| b.cz(h0, lgt));
        b.free(lgt);
        b.pop_condition();
        b.cx(x[0], h0);
        b.free(h0);
    }
    lazy_resize(b, &mut u, n);
    for j in 0..n {
        if bit(p, j) {
            b.x(u[j]);
        }
    }
    b.free_vec(&u);
}

/// s ±= h0·r mod q (s, r < q), with the masked operand in step-local scratch.
///
/// Add: t = s + h0·r as a 257-bit sum whose carry-out f is the reduction flag;
/// if f, the low 256 bits get +c (q = 2^256 − c); then f = [s_new < h0·r] is
/// uncomputed with one comparator. Sub is the exact mirror: f = [s < h0·r], if f
/// the low part gets −c, then the 257-bit subtraction clears f as its top bit.
/// The ±c is applied to the low WINDOW bits only (see WINDOW).
/// Both are wrong in the band s + r ∈ [q, 2^256). In the replay that band is
/// hit exactly once, at the step where x's GCD first swaps (step index =
/// trailing zeros of x; `moonshots/band.py`), so steps below EXACT_STEPS use
/// the exact modular add/sub (`exact`); elsewhere the band has probability
/// ≈ 2^-224 per step. EXACT_STEPS = 48 fails only if x has ≥ 48 trailing zeros
/// (probability 2^-48 per inversion). (A ±c
/// truncated to the low 128 bits was tried and is wrong: the replay produces
/// small values systematically, e.g. s − c with s < c.)
pub(super) fn cmod_add(b: &mut B, s: &[QubitId], r: &[QubitId], h0: QubitId, p: U256, sub: bool, exact: bool) {
    let n = s.len();
    let c = U256::MAX.wrapping_sub(p).wrapping_add(U256::from(1));
    let tmp = b.alloc_qubits(n);
    for j in 0..n {
        b.ccx(h0, r[j], tmp[j]);
    }
    if exact {
        if sub {
            mod_sub_qq_fast(b, s, &tmp, p);
        } else {
            mod_add_qq_fast(b, s, &tmp, p);
        }
        for j in 0..n {
            let m = b.alloc_bit();
            b.hmr(tmp[j], m);
            b.cz_if(h0, r[j], m);
        }
        b.free_vec(&tmp);
        return;
    }
    let f = b.alloc_qubit();
    let pad = b.alloc_qubit();
    let mut t_ext = tmp.clone();
    t_ext.push(pad);
    let mut s_ext = s.to_vec();
    s_ext.push(f);
    if !sub {
        add_nbit_qq_fast(b, &t_ext, &s_ext);
        add_c_low(b, &s[..WINDOW], c, f, &tmp, true);
        // f = [s_new < h0·r]: X-measure f; fix (−1)^f only when the outcome is 1.
        let cf = b.alloc_bit();
        b.hmr(f, cf);
        b.push_condition(cf);
        phase_lt(b, s, &tmp);
        b.pop_condition();
    } else {
        cmp_lt_into_fast(b, s, &tmp, f);
        add_c_low(b, &s[..WINDOW], c, f, &tmp, false);
        sub_nbit_qq_fast(b, &t_ext, &s_ext);
    }
    b.free(pad);
    b.free(f);
    for j in 0..n {
        let m = b.alloc_bit();
        b.hmr(tmp[j], m);
        b.cz_if(h0, r[j], m);
    }
    b.free_vec(&tmp);
}

/// Applies the phase (−1)^{[u < v]}. With room under the cap: the
/// measurement-uncomputed carry comparator (n Toffolis); otherwise (H4.A21) the
/// carry-free MAJ comparator (2n Toffolis, no carry qubits), with the carry-out
/// left in u's top bit for a CZ against a |1⟩ ancilla.
fn phase_lt(b: &mut B, u: &[QubitId], v: &[QubitId]) {
    let n = u.len();
    let one = b.alloc_qubit();
    b.x(one);
    if fits_cap(b, n + 2) {
        let lt = b.alloc_qubit();
        with_lt(b, u, v, lt, |b| b.cz(lt, one));
        b.free(lt);
    } else {
        let c_in = b.alloc_qubit();
        for i in 0..n {
            b.x(u[i]);
        }
        maj(b, c_in, v[0], u[0]);
        for i in 1..n {
            maj(b, u[i - 1], v[i], u[i]);
        }
        b.cz(u[n - 1], one);
        for i in (1..n).rev() {
            inv_maj(b, u[i - 1], v[i], u[i]);
        }
        inv_maj(b, c_in, v[0], u[0]);
        for i in 0..n {
            b.x(u[i]);
        }
        b.free(c_in);
    }
    b.x(one);
    b.free(one);
}

/// lo ±= ctrl·c (mod 2^|lo|), loading only c's 33 bits and padding with live
/// qubits `dirty` (unchanged).
pub(super) fn add_c_low(b: &mut B, lo: &[QubitId], c: U256, ctrl: QubitId, dirty: &[QubitId], add: bool) {
    if fits_cap(b, lo.len() + 2) {
        // Room for a zero-padded operand; the (cap-aware) adder trades any
        // carries that do not fit for 2-Toffoli bits, which is cheaper than a
        // second, dirty-pad subtraction.
        let op = b.alloc_qubits(lo.len());
        for j in 0..33 {
            if bit(c, j) {
                b.cx(ctrl, op[j]);
            }
        }
        if add {
            add_nbit_qq_fast(b, &op, lo);
        } else {
            sub_nbit_qq_fast(b, &op, lo);
        }
        for j in 0..33 {
            if bit(c, j) {
                b.cx(ctrl, op[j]);
            }
        }
        b.free_vec(&op);
        return;
    }
    let k = 33;
    let op = b.alloc_qubits(k);
    for j in 0..k {
        if bit(c, j) {
            b.cx(ctrl, op[j]);
        }
    }
    addsub_dirty_padded(b, &op, dirty, lo, add);
    for j in 0..k {
        if bit(c, j) {
            b.cx(ctrl, op[j]);
        }
    }
    b.free_vec(&op);
}

/// Steps (by GCD step index) that use the exact modular add/sub; see `cmod_add`.
const EXACT_STEPS: usize = 48;

/// H4.A20: outside the exact steps every ±c correction (reduction, modular
/// double, modular halve) acts on the low WINDOW bits only. A carry/borrow
/// leaves the window only if the operand's bits 33..WINDOW−1 are all ones/zeros:
/// measured tail P(chain reaches bit 33+k) ≈ 2^-(k+1) over 140,590 corrections
/// (max bit 51; experiments/moonshots/chains.py), so ≈ 2^-127 per correction.
const WINDOW: usize = 160;

/// v (WINDOW bits) ±= ctrl·c mod 2^WINDOW: c's 33 bits loaded under ctrl, the
/// operand zero-padded when the cap allows, else padded with live qubits `dirty`.
fn cadd_window(b: &mut B, v: &[QubitId], c: U256, ctrl: QubitId, dirty: &[QubitId], add: bool) {
    add_c_low(b, v, c, ctrl, dirty, add);
}

/// s ← 2s mod q with the ±c correction on the low WINDOW bits.
fn mod_double_window(b: &mut B, v: &[QubitId], p: U256, dirty: &[QubitId]) {
    mod_double_w(b, v, p, dirty, WINDOW);
}

/// s ← 2s mod q with the +c correction on the low `w` bits (w = n: exact).
fn mod_double_w(b: &mut B, v: &[QubitId], p: U256, dirty: &[QubitId], w: usize) {
    let n = v.len();
    let c = U256::MAX.wrapping_sub(p).wrapping_add(U256::from(1));
    let ovf = b.alloc_qubit();
    b.swap(v[n - 1], ovf);
    for i in (0..n - 1).rev() {
        b.swap(v[i], v[i + 1]);
    }
    cadd_window(b, &v[..w], c, ovf, dirty, true);
    b.cx(v[0], ovf); // result parity = old top bit
    b.free(ovf);
}

/// v ← v/2 mod q with the −c correction on the low WINDOW bits.
fn mod_halve_window(b: &mut B, v: &[QubitId], p: U256, dirty: &[QubitId]) {
    mod_halve_w(b, v, p, dirty, WINDOW);
}

/// v ← v/2 mod q with the −c correction on the low `w` bits (w = n: exact).
fn mod_halve_w(b: &mut B, v: &[QubitId], p: U256, dirty: &[QubitId], w: usize) {
    let n = v.len();
    let c = U256::MAX.wrapping_sub(p).wrapping_add(U256::from(1));
    let ovf = b.alloc_qubit();
    b.cx(v[0], ovf);
    cadd_window(b, &v[..w], c, ovf, dirty, false);
    for i in 0..n - 1 {
        b.swap(v[i], v[i + 1]);
    }
    b.swap(v[n - 1], ovf);
    b.free(ovf);
}

/// lo (window) ±= k·c with k = o + 2e ∈ {0, 1, 2} (o, e never both 1): the
/// operand is c's bits under o and 2c's bits under e.
fn add_kc_window(b: &mut B, lo: &[QubitId], c: U256, o: QubitId, e: QubitId, dirty: &[QubitId], add: bool) {
    let c2 = c << 1usize;
    let load = |b: &mut B, op: &[QubitId]| {
        for j in 0..34 {
            if bit(c, j) {
                b.cx(o, op[j]);
            }
            if bit(c2, j) {
                b.cx(e, op[j]);
            }
        }
    };
    if fits_cap(b, lo.len() + 2) {
        let op = b.alloc_qubits(lo.len());
        load(b, &op);
        if add {
            add_nbit_qq_fast(b, &op, lo);
        } else {
            sub_nbit_qq_fast(b, &op, lo);
        }
        load(b, &op);
        b.free_vec(&op);
    } else {
        let op = b.alloc_qubits(34);
        load(b, &op);
        addsub_dirty_padded(b, &op, dirty, lo, add);
        load(b, &op);
        b.free_vec(&op);
    }
}

/// Phase (−1)^{[u < v] ∧ ¬ctrl}, cap-aware like `phase_lt`.
fn phase_lt_not(b: &mut B, u: &[QubitId], v: &[QubitId], ctrl: QubitId) {
    let n = u.len();
    b.x(ctrl);
    if fits_cap(b, n + 2) {
        let lt = b.alloc_qubit();
        with_lt(b, u, v, lt, |b| b.cz(lt, ctrl));
        b.free(lt);
    } else {
        let c_in = b.alloc_qubit();
        for i in 0..n {
            b.x(u[i]);
        }
        maj(b, c_in, v[0], u[0]);
        for i in 1..n {
            maj(b, u[i - 1], v[i], u[i]);
        }
        b.cz(u[n - 1], ctrl);
        for i in (1..n).rev() {
            inv_maj(b, u[i - 1], v[i], u[i]);
        }
        inv_maj(b, c_in, v[0], u[0]);
        for i in 0..n {
            b.x(u[i]);
        }
        b.free(c_in);
    }
    b.x(ctrl);
}

/// H4.A23 fast replay step, multiply direction: s ← 2s + h0·r mod q with one ±c.
/// V = 2s + h0·r (258 bits: shift s with its top bit to o, then add the masked
/// r with a fresh e on top), k = V >> 256 = o + 2e, s_new = (V mod 2^256) + k·c.
/// o is cleared from parity (s_new[0] ⊕ (h0·r)[0]); e = ¬o ∧ [s_new < h0·r] is
/// X-measured and its phase fixed in half the shots (moonshots/merged.py).
fn dbl_add_fast(b: &mut B, s: &[QubitId], r: &[QubitId], h0: QubitId, p: U256) {
    let n = s.len();
    let c = U256::MAX.wrapping_sub(p).wrapping_add(U256::from(1));
    let o = b.alloc_qubit();
    b.swap(s[n - 1], o);
    for i in (0..n - 1).rev() {
        b.swap(s[i], s[i + 1]);
    }
    let tmp = b.alloc_qubits(n);
    for j in 0..n {
        b.ccx(h0, r[j], tmp[j]);
    }
    let e = b.alloc_qubit();
    let pads = b.alloc_qubits(2);
    let mut t_ext = tmp.clone();
    t_ext.extend_from_slice(&pads);
    let mut s_ext = s.to_vec();
    s_ext.push(o);
    s_ext.push(e);
    add_nbit_qq_fast(b, &t_ext, &s_ext);
    b.free_vec(&pads);
    add_kc_window(b, &s[..WINDOW], c, o, e, &tmp, true);
    let ce = b.alloc_bit();
    b.hmr(e, ce);
    b.free(e);
    b.push_condition(ce);
    phase_lt_not(b, s, &tmp, o);
    b.pop_condition();
    b.cx(s[0], o);
    b.cx(tmp[0], o);
    b.free(o);
    for j in 0..n {
        let m = b.alloc_bit();
        b.hmr(tmp[j], m);
        b.cz_if(h0, r[j], m);
    }
    b.free_vec(&tmp);
}

/// Inverse of `dbl_add_fast` (divide direction): s ← (s − h0·r)/2 mod q.
fn sub_halve_fast(b: &mut B, s: &[QubitId], r: &[QubitId], h0: QubitId, p: U256) {
    let n = s.len();
    let c = U256::MAX.wrapping_sub(p).wrapping_add(U256::from(1));
    let tmp = b.alloc_qubits(n);
    for j in 0..n {
        b.ccx(h0, r[j], tmp[j]);
    }
    let o = b.alloc_qubit();
    b.cx(s[0], o);
    b.cx(tmp[0], o);
    let e = b.alloc_qubit();
    let lt = b.alloc_qubit();
    b.x(o);
    with_lt(b, s, &tmp, lt, |b| b.ccx(o, lt, e));
    b.x(o);
    b.free(lt);
    add_kc_window(b, &s[..WINDOW], c, o, e, &tmp, false);
    let pads = b.alloc_qubits(2);
    let mut t_ext = tmp.clone();
    t_ext.extend_from_slice(&pads);
    let mut s_ext = s.to_vec();
    s_ext.push(o);
    s_ext.push(e);
    sub_nbit_qq_fast(b, &t_ext, &s_ext);
    b.free_vec(&pads);
    b.free(e);
    for i in 0..n - 1 {
        b.swap(s[i], s[i + 1]);
    }
    b.swap(s[n - 1], o);
    b.free(o);
    for j in 0..n {
        let m = b.alloc_bit();
        b.hmr(tmp[j], m);
        b.cz_if(h0, r[j], m);
    }
    b.free_vec(&tmp);
}

/// y ← y·x mod q, in place (x unchanged). x, y in [1, q) and [0, q).
pub(super) fn mul_inplace(b: &mut B, x: &[QubitId], y: &[QubitId], iters: usize, p: U256) {
    let n = y.len();
    b.set_phase("eea_gcd_fwd");
    let mut hist = b.prof("gcd_forward", |b| gcd_forward(b, x, iters, p));
    b.set_phase("eea_replay");
    let s = b.alloc_qubits(n);
    b.prof("replay_mul", |b| {
        for i in (0..iters).rev() {
            if i % 3 == 2 {
                hist.unpack(b, i / 3);
            }
            b.allow_reserved += 1;
            if i < EXACT_STEPS {
                mod_double_w(b, &s, p, y, n);
                cmod_add(b, &s, y, hist.h0[i], p, false, true);
            } else if H4_MERGED_STEP {
                dbl_add_fast(b, &s, y, hist.h0[i], p);
            } else {
                mod_double_window(b, &s, p, y);
                cmod_add(b, &s, y, hist.h0[i], p, false, false);
            }
            b.allow_reserved -= 1;
            for j in 0..n {
                cswap(b, hist.h1[i], y[j], s[j]);
            }
            if i % 3 == 0 && i / 3 < hist.packed.len() {
                hist.pack(b, i / 3);
            }
        }
    });
    // (y, s) = (0, y·x): move the product into y's qubits.
    for j in 0..n {
        b.swap(y[j], s[j]);
    }
    b.free_vec(&s);
    b.set_phase("eea_gcd_bwd");
    b.prof("gcd_backward", |b| gcd_backward(b, x, hist, iters, p));
}

/// y ← y / x mod q, in place (x unchanged, x in [1, q)).
/// Inherits `mod_halve_inplace_fast`'s precondition (exact unless the halved
/// value is odd and below c = 2^32 + 977; probability ≈ 2^-224 per step for
/// the random values a point addition produces).
pub(super) fn div_inplace(b: &mut B, x: &[QubitId], y: &[QubitId], iters: usize, p: U256) {
    let n = y.len();
    b.set_phase("eea_gcd_fwd");
    let mut hist = b.prof("gcd_forward", |b| gcd_forward(b, x, iters, p));
    b.set_phase("eea_replay");
    let r = b.alloc_qubits(n);
    b.prof("replay_div", |b| {
        for i in 0..iters {
            if i % 3 == 0 {
                hist.unpack(b, i / 3);
            }
            for j in 0..n {
                cswap(b, hist.h1[i], r[j], y[j]);
            }
            b.allow_reserved += 1;
            if i < EXACT_STEPS {
                cmod_add(b, y, &r, hist.h0[i], p, true, true);
                mod_halve_w(b, y, p, &r, n);
            } else if H4_MERGED_STEP {
                sub_halve_fast(b, y, &r, hist.h0[i], p);
            } else {
                cmod_add(b, y, &r, hist.h0[i], p, true, false);
                mod_halve_window(b, y, p, &r);
            }
            b.allow_reserved -= 1;
            if i % 3 == 2 {
                hist.pack(b, i / 3);
            }
        }
    });
    // (r, y) = (y/x, 0): move the quotient into y's qubits.
    for j in 0..n {
        b.swap(r[j], y[j]);
    }
    b.free_vec(&r);
    b.set_phase("eea_gcd_bwd");
    b.prof("gcd_backward", |b| gcd_backward(b, x, hist, iters, p));
}

