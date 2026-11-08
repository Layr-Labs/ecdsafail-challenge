//! H4.A2: in-place multiplication by 2^±k mod p in k-bit chunks
//! (Montgomery-style), replacing chains of single-bit halvings/doublings.
//!
//! p = 2^n − c with c = 2^32 + 2^10 − 2^6 + 2^4 + 1 (secp256k1), C = c^-1 mod 2^k.
//!
//! Right shift R_k: y ↦ v = y·2^-k mod p, for y < p.
//!   M = y·C mod 2^k makes y + M·p ≡ 0 (mod 2^k) because p ≡ −c. With
//!   Z = y + M·2^n − M·c (n+k bits), Z's low k bits are exactly 0 and
//!   v = Z/2^k = (y + M·p)/2^k < p (M < 2^k). A SWAP network moves Z down by k.
//!   Garbage: M = h + flag(v), with h = top k bits of v and
//!   flag(v) = [l·2^k + h·c ≥ p] (l = low n−k bits of v), because
//!   v·2^k = y + (h + flag)·p in the forward direction. M −= h leaves the single
//!   bit flag(v), which is X-measured; its phase (−1)^flag(v) is fixed up inside
//!   a block conditioned on the measured bit.
//! Left shift L_k is the exact inverse: compute M = h + flag(v), shift up by
//! SWAPs, add M·c, subtract M from the top k bits (they become 0), then clear
//! M = y·C mod 2^k with the constant multiply.
//!
//! flag(v) = [T_hi > ¬v[0..34]] ∧ [v[34..n−k] all ones], T = (h+1)·c, because
//! l·2^k + (h+1)·c ≥ 2^n needs a carry out of the low k+34 bits (a 34-bit
//! comparison of T>>k against v's low 34 bits) and all-ones bits above it.

use super::*;

/// Signed shifts of c = 2^32 + 2^10 − 2^6 + 2^4 + 2^0: (position, is_add).
const C_TERMS: [(usize, bool); 5] = [(0, true), (4, true), (6, false), (10, true), (32, true)];

fn c_inverse_mod_2k(k: usize) -> u128 {
    let c: u128 = (1u128 << 32) + 977;
    let mut x: u128 = 1;
    for _ in 0..8 {
        x = x.wrapping_mul(2u128.wrapping_sub(c.wrapping_mul(x)));
    }
    if k >= 128 {
        x
    } else {
        x & ((1u128 << k) - 1)
    }
}

/// z[pos..] ±= m (mod 2^(len z − pos)), zero-padding or truncating m.
fn add_shifted(b: &mut B, m: &[QubitId], z: &[QubitId], pos: usize, add: bool) {
    let w = z.len() - pos;
    let mut op: Vec<QubitId> = m.iter().take(w).copied().collect();
    let pad = b.alloc_qubits(w - op.len());
    op.extend_from_slice(&pad);
    if add {
        add_nbit_qq_fast(b, &op, &z[pos..]);
    } else {
        sub_nbit_qq_fast(b, &op, &z[pos..]);
    }
    b.free_vec(&pad);
}

/// dst (k bits) ±= (src_lo · cc) mod 2^k, using shifted adds of src's low bits.
fn mul_const_mod2k(b: &mut B, src: &[QubitId], dst: &[QubitId], cc: u128, add: bool) {
    let k = dst.len();
    for j in 0..k {
        if (cc >> j) & 1 == 1 {
            let a: Vec<QubitId> = src[0..k - j].to_vec();
            if add {
                add_nbit_qq_fast(b, &a, &dst[j..k]);
            } else {
                sub_nbit_qq_fast(b, &a, &dst[j..k]);
            }
        }
    }
}

/// Runs `body(b, l, z)` with qubits l, z such that l ∧ z = flag(v) (both are
/// uncomputed afterwards; the body must leave them unchanged).
fn with_flag<F: FnOnce(&mut B, QubitId, QubitId)>(b: &mut B, v: &[QubitId], k: usize, body: F) {
    let n = v.len();
    assert!(n > k + 34);
    let h: Vec<QubitId> = v[n - k..n].to_vec();
    // H1 = h + 1 (k+1 bits).
    let h1 = b.alloc_qubits(k + 1);
    for i in 0..k {
        b.cx(h[i], h1[i]);
    }
    add_nbit_const_fast(b, &h1, U256::from(1u64));
    // T = H1 · c (k+34 bits).
    let t = b.alloc_qubits(k + 34);
    for &(pos, add) in C_TERMS.iter() {
        add_shifted(b, &h1, &t, pos, add);
    }
    // l = [T_hi > ¬v[0..34]], z = [v[34..n−k] all ones].
    let low: Vec<QubitId> = v[0..34].to_vec();
    let mid: Vec<QubitId> = v[34..n - k].to_vec();
    for &q in &low {
        b.x(q);
    }
    let l = b.alloc_qubit();
    with_gt(b, &t[k..k + 34], &low, l, |b| {
        for &q in &mid {
            b.x(q);
        }
        let z = b.alloc_qubit();
        with_eq_zero_fast(b, &mid, z, |b| body(b, l, z));
        b.free(z);
        for &q in &mid {
            b.x(q);
        }
    });
    b.free(l);
    for &q in &low {
        b.x(q);
    }
    // Uncompute T and H1.
    for &(pos, add) in C_TERMS.iter().rev() {
        add_shifted(b, &h1, &t, pos, !add);
    }
    b.free_vec(&t);
    sub_nbit_const_fast(b, &h1, U256::from(1u64));
    for i in 0..k {
        b.cx(h[i], h1[i]);
    }
    b.free_vec(&h1);
}

/// y ← y·2^-k mod p (in place, register identity kept).
fn shift_right_chunk(b: &mut B, y: &[QubitId], k: usize) {
    let n = y.len();
    let cc = c_inverse_mod_2k(k);
    let m = b.alloc_qubits(k);
    let e = b.alloc_qubits(k);
    mul_const_mod2k(b, y, &m, cc, true);
    for i in 0..k {
        b.cx(m[i], e[i]);
    }
    let mut z: Vec<QubitId> = y.to_vec();
    z.extend_from_slice(&e);
    for &(pos, add) in C_TERMS.iter() {
        add_shifted(b, &m, &z, pos, !add); // Z −= M·c
    }
    // Z ≡ 0 (mod 2^k): move it down by k bits.
    for i in 0..n {
        b.swap(z[i], z[i + k]);
    }
    b.free_vec(&e);
    // M = h + flag(v) → flag(v).
    sub_nbit_qq_fast(b, &y[n - k..n], &m);
    b.free_vec(&m[1..k]);
    let s = b.alloc_bit();
    b.hmr(m[0], s);
    b.free(m[0]);
    b.push_condition(s);
    with_flag(b, y, k, |b, l, zq| b.cz(l, zq));
    b.pop_condition();
}

/// v ← v·2^k mod p (in place, register identity kept).
fn shift_left_chunk(b: &mut B, v: &[QubitId], k: usize) {
    let n = v.len();
    let cc = c_inverse_mod_2k(k);
    // M = h + flag(v).
    let m = b.alloc_qubits(k);
    for i in 0..k {
        b.cx(v[n - k + i], m[i]);
    }
    let f = b.alloc_qubit();
    with_flag(b, v, k, |b, l, zq| {
        b.ccx(l, zq, f);
        add_shifted(b, &[f], &m, 0, true);
        b.ccx(l, zq, f);
    });
    b.free(f);
    // Z = v·2^k.
    let e = b.alloc_qubits(k);
    let mut z: Vec<QubitId> = v.to_vec();
    z.extend_from_slice(&e);
    for i in (0..n).rev() {
        b.swap(z[i], z[i + k]);
    }
    for &(pos, add) in C_TERMS.iter() {
        add_shifted(b, &m, &z, pos, add); // Z += M·c
    }
    sub_nbit_qq_fast(b, &m, &z[n..n + k]); // top −= M → 0
    b.free_vec(&e);
    // M = y·C mod 2^k → 0.
    mul_const_mod2k(b, v, &m, cc, false);
    b.free_vec(&m);
}

pub(super) const CHUNK: usize = 64;

/// y ← y·2^-bits mod p.
pub(super) fn shift_right_mod_p(b: &mut B, y: &[QubitId], bits: usize) {
    let mut left = bits;
    while left > 0 {
        let k = left.min(CHUNK);
        shift_right_chunk(b, y, k);
        left -= k;
    }
}

/// v ← v·2^bits mod p.
pub(super) fn shift_left_mod_p(b: &mut B, v: &[QubitId], bits: usize) {
    let mut left = bits;
    while left > 0 {
        let k = left.min(CHUNK);
        shift_left_chunk(b, v, k);
        left -= k;
    }
}

/// H4.A6: acc ±= hi·c mod p (hi any n-bit value, acc < p) via an exact integer
/// product W = hi·c (n+34 bits), one fold of W's top 34 bits (2^n ≡ c), a
/// single modular add/sub, and full reversal. Replaces the double/halve ladder.
pub(super) fn acc_addsub_hi_times_c(b: &mut B, acc: &[QubitId], hi: &[QubitId], p: U256, add: bool) {
    let n = hi.len();
    let w = b.alloc_qubits(n + 34);
    for &(pos, a) in C_TERMS.iter() {
        add_shifted(b, hi, &w, pos, a); // W = hi·c (< 2^(n+33))
    }
    let g = b.alloc_qubits(34);
    for i in 0..34 {
        b.cx(w[n + i], g[i]);
        b.cx(g[i], w[n + i]); // move W's top into G
    }
    for &(pos, a) in C_TERMS.iter() {
        add_shifted(b, &g, &w[0..n + 2], pos, a); // W_lo += G·c (< 2^(n+1))
    }
    // Second, 1-bit fold: if bit n is set, the low part is < 2^67, so adding c
    // cannot overflow. Afterwards W[0..n] = hi·c mod 2^n-folded, exactly < 2^n.
    let c_const = U256::from((1u64 << 32) + 977);
    let h1 = b.alloc_qubit();
    b.cx(w[n], h1);
    b.cx(h1, w[n]);
    cadd_nbit_const_fast(b, &w[0..n], c_const, h1);
    if add {
        mod_add_qq_fast(b, acc, &w[0..n], p);
    } else {
        mod_sub_qq_fast(b, acc, &w[0..n], p);
    }
    csub_nbit_const_fast(b, &w[0..n], c_const, h1);
    b.cx(h1, w[n]);
    b.cx(w[n], h1);
    b.free(h1);
    for &(pos, a) in C_TERMS.iter().rev() {
        add_shifted(b, &g, &w[0..n + 2], pos, !a);
    }
    for i in (0..34).rev() {
        b.cx(g[i], w[n + i]);
        b.cx(w[n + i], g[i]);
    }
    b.free_vec(&g);
    for &(pos, a) in C_TERMS.iter().rev() {
        add_shifted(b, hi, &w, pos, !a);
    }
    b.free_vec(&w);
}

/// H4.A9: acc ±= P mod p for a 2n-bit product P held in `prod` (lo | hi),
/// folding in place inside `prod` instead of materialising hi·c:
///   lo|G += hi·c        (G: 34 fresh qubits; lo + hi·c < 2^(n+34))
///   lo|h1 += G·c        (h1: 1 fresh qubit; result < 2^(n+1))
///   if h1: lo += c      (then lo < 2^67, so no overflow)
///   acc ±= lo mod p     (lo ≡ P mod p, lo < 2^n)
/// then the three folds are undone, leaving `prod` = P and G = h1 = 0.
/// `from_zero`: acc is known to be 0 (add only).
/// Precondition (shared with the ladder and with `acc_addsub_hi_times_c`,
/// whose first step mod-adds an arbitrary 256-bit lo): the folded lo < p,
/// which fails with probability ≈ c/2^256 for a uniformly distributed product.
pub(super) fn acc_addsub_product_inplace(b: &mut B, acc: &[QubitId], prod: &[QubitId], p: U256, add: bool, from_zero: bool) {
    let n = acc.len();
    debug_assert_eq!(prod.len(), 2 * n);
    let lo: Vec<QubitId> = prod[0..n].to_vec();
    let hi: Vec<QubitId> = prod[n..2 * n].to_vec();
    let g = b.alloc_qubits(34);
    let mut lg = lo.clone();
    lg.extend_from_slice(&g);
    for &(pos, a) in C_TERMS.iter() {
        add_shifted_dirty(b, &hi, &lg, pos, a, acc);
    }
    let h1 = b.alloc_qubit();
    let mut lh = lo.clone();
    lh.push(h1);
    fold_g(b, &g, &hi, acc, &lh, true);
    let c_const = U256::from((1u64 << 32) + 977);
    cadd_c_folded(b, &lo, h1, &hi, c_const, true);
    if from_zero {
        debug_assert!(add);
        mod_add_qq_fast_from_zero(b, acc, &lo, p);
    } else if add {
        mod_add_qq_fast(b, acc, &lo, p);
    } else {
        mod_sub_qq_fast(b, acc, &lo, p);
    }
    cadd_c_folded(b, &lo, h1, &hi, c_const, false);
    fold_g(b, &g, &hi, acc, &lh, false);
    b.free(h1);
    for &(pos, a) in C_TERMS.iter().rev() {
        add_shifted_dirty(b, &hi, &lg, pos, !a, acc);
    }
    b.free_vec(&g);
}

/// lh ±= G·c (G: 34 bits). With H4_TIGHT_SCRATCH, W2 = G·c (< 2^67) is built
/// in 67 fresh qubits and added once, padded with live qubits from `dirty`
/// (unchanged), instead of five zero-padded 257-bit adds.
fn fold_g(b: &mut B, g: &[QubitId], dirty: &[QubitId], dirty2: &[QubitId], lh: &[QubitId], add: bool) {
    if !H4_TIGHT_SCRATCH {
        if add {
            for &(pos, a) in C_TERMS.iter() {
                add_shifted(b, g, lh, pos, a);
            }
        } else {
            for &(pos, a) in C_TERMS.iter().rev() {
                add_shifted(b, g, lh, pos, !a);
            }
        }
        return;
    }
    let w2 = b.alloc_qubits(67);
    for &(pos, a) in C_TERMS.iter() {
        add_shifted_dirty(b, g, &w2, pos, a, dirty2);
    }
    addsub_dirty_padded(b, &w2, dirty, lh, add);
    for &(pos, a) in C_TERMS.iter().rev() {
        add_shifted_dirty(b, g, &w2, pos, !a, dirty2);
    }
    b.free_vec(&w2);
}

/// lo ±= h1·c. With H4_TIGHT_SCRATCH only c's 33 bits are loaded (under h1)
/// and the add is padded with live qubits from `dirty` (unchanged), instead of
/// loading a full 256-qubit constant register.
fn cadd_c_folded(b: &mut B, lo: &[QubitId], h1: QubitId, dirty: &[QubitId], c: U256, add: bool) {
    if !H4_TIGHT_SCRATCH {
        if add {
            cadd_nbit_const_fast(b, lo, c, h1);
        } else {
            csub_nbit_const_fast(b, lo, c, h1);
        }
        return;
    }
    let k = 33;
    let op = b.alloc_qubits(k);
    for j in 0..k {
        if c.bit(j) {
            b.cx(h1, op[j]);
        }
    }
    addsub_dirty_padded(b, &op, dirty, lo, add);
    for j in 0..k {
        if c.bit(j) {
            b.cx(h1, op[j]);
        }
    }
    b.free_vec(&op);
}

/// `add_shifted` with the operand padded by live qubits `dirty` (unchanged)
/// instead of zero pads, under H4_TIGHT_SCRATCH.
fn add_shifted_dirty(b: &mut B, m: &[QubitId], z: &[QubitId], pos: usize, add: bool, dirty: &[QubitId]) {
    let w = z.len() - pos;
    if !H4_TIGHT_SCRATCH || m.len() >= w {
        add_shifted(b, m, z, pos, add);
        return;
    }
    addsub_dirty_padded(b, m, dirty, &z[pos..], add);
}
