use super::*;

// ─── Static bit-width bounds for the mixed point-add multiply path ────────────
//
// Every classical operand and intermediate in the qprod/round84 path carries a
// STATIC upper bound: a compile-time `usize` derived from the operand
// constants (e.g. the secp256k1 modulus-derived c = 0x3D1 and shift list
// {4, 5, 10, 32}) and the operand bit-widths (q is at most 33 bits, the
// quotient accumulator is at most 33 bits, etc.). These bounds let the
// multiplier emitter narrow its row width: it elides the leading-zero limbs of
// each addend and truncates the row target beyond the static bound, so
// neither the carry/borrow chain nor the temp allocation has to be paid for
// over the full n-bit width. The bit-count is small per row (one fewer bit
// per omitted position, one fewer carry per omitted chain link), but the row
// count is in the thousands per round and the bound is the same every call,
// so the saving compounds to a real reduction in the qubit×toffoli product.

/// Returns the index of the highest set bit in `c` (0 if `c == 0`).
/// This is the minimum number of low bits the operand occupies.
#[inline]
pub(crate) const fn nbit_classical_operand_top_bit(c: U256) -> usize {
    let limbs = c.as_limbs();
    let mut hi_limb: usize = 0;
    let mut i = 0;
    while i < 4 {
        if limbs[i] != 0 {
            hi_limb = i;
        }
        i += 1;
    }
    if limbs[hi_limb] == 0 {
        return 0;
    }
    let mut v = limbs[hi_limb];
    let mut bit: usize = 0;
    while v > 1 {
        v >>= 1;
        bit += 1;
    }
    bit + 64 * hi_limb
}

/// Returns the number of bits needed to represent `c` (0 if `c == 0`).
#[inline]
pub(crate) const fn nbit_classical_operand_width(c: U256) -> usize {
    let t = nbit_classical_operand_top_bit(c);
    if t == 0 && c == U256::ZERO {
        0
    } else {
        t + 1
    }
}

/// Upper bound on the number of bits of `a + b` where `a` and `b` are
/// each bounded by their respective widths. One carry bit past the wider
/// operand is the tightest pre-prove bound.
#[inline]
pub(crate) const fn nbit_addsum_width(a_width: usize, b_width: usize) -> usize {
    if a_width >= b_width {
        a_width + 1
    } else {
        b_width + 1
    }
}

/// Upper bound on the number of bits of `a * b` where `a` and `b` are each
/// bounded by their respective widths. The classic bound: `a_w + b_w`.
#[inline]
pub(crate) const fn nbit_product_width(a_width: usize, b_width: usize) -> usize {
    a_width + b_width
}

/// Upper bound on the number of bits of `a * b` plus a constant `k` (signed
/// shift in NAF style). Same as product width, since the k-shift dominates
/// the carry/borrow only when the shift is bigger than the product width.
#[inline]
pub(crate) const fn nbit_shifted_product_width(
    a_width: usize,
    b_width: usize,
    shift: usize,
) -> usize {
    a_width + b_width + shift
}

/// Width of a target register needed to receive `add_short_to_long(q, target)`
/// at offset `shift`, where `q` is bounded by `q_width` and the static product
/// bound is `q_width + c_width`. The result must hold bits up to
/// `shift + q_width + c_width` (capped by `total_width`).
#[inline]
pub(crate) const fn nbit_qprod_target_width(
    shift: usize,
    q_width: usize,
    c_width: usize,
    total_width: usize,
) -> usize {
    let hi = shift + q_width + c_width;
    if hi < total_width { hi } else { total_width }
}

/// secp256k1 modulus-derived qprod constant: `2^32 + 2^10 - 2^5 - 2^4 =
/// 0x1_0000_03D1`. The NAF form used by `round84_compute_quotient_c_product`
/// is `+q<<10, +q<<32, -q<<5, -q<<4` (sum = 0x3D1 + 0x400 = 0x3D1 +
/// (1<<10) − (1<<5) − (1<<4) at the shifted positions). The top bit of `0x3D1`
/// sits at position 9, so the per-row static c-width is 10.
pub(crate) const SECP256K1_QPROD_C: U256 = U256::from_limbs([0x3D1, 0, 0, 0]);
pub(crate) const SECP256K1_QPROD_C_WIDTH: usize = 10;
pub(crate) const ROUND84_QUOTIENT_BITS: usize = 33;
/// Static upper bound for the round84 product: `q * c` with q < 2^33 and
/// c < 2^32 → product < 2^65 → 65 bits needed. The existing emitter
/// over-allocates 66 qubits; the narrowed row fits in 65.
pub(crate) const ROUND84_QPROD_TOTAL_WIDTH: usize = 65;
/// The five shift values used by `round84_fold_hi_into_lo_aggregate` for
/// the Solinas fold. Each one is a CLASSICAL operand with a known width.
pub(crate) const ROUND84_FOLD_SHIFTS: [usize; 5] = [0, 4, 5, 10, 32];
/// The four NAF (shift, add) pairs used by `round84_compute_quotient_c_product`.
pub(crate) const ROUND84_QPROD_NAF: [(usize, bool); 4] =
    [(10, true), (32, true), (5, false), (4, false)];

/// Static width bound for the round84 qprod target row at shift `s`.
/// `min(shift + q_width + c_width, total_width)`. The addend `q` is `q_width`
/// bits; the c-bit-width `c_width` adds `c_width` low-order bits to the
/// product beyond `q`; the shift `s` positions the result at bit `s + k`.
pub(crate) const fn round84_qprod_row_width(s: usize) -> usize {
    let s_shift = s + ROUND84_QUOTIENT_BITS + SECP256K1_QPROD_C_WIDTH;
    if s_shift < ROUND84_QPROD_TOTAL_WIDTH {
        s_shift
    } else {
        ROUND84_QPROD_TOTAL_WIDTH
    }
}

/// Number of low bits of `q` that can affect the target row at shift `s`:
/// the row width minus the shift. The high bits of `q` are leading-zero
/// relative to this row and may be elided.
pub(crate) const fn round84_qprod_row_q_len(s: usize) -> usize {
    let row = round84_qprod_row_width(s);
    if row > s {
        row - s
    } else {
        0
    }
}

pub(crate) fn add_nbit_qq_fast(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_add_fast(b, a, acc, c_in);
    b.free(c_in);
}

pub(crate) fn sub_nbit_qq_fast(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_sub_fast(b, a, acc, c_in);
    b.free(c_in);
}

pub(crate) fn add_nbit_qq_fast_borrowed_carries(
    b: &mut B,
    a: &[QubitId],
    acc: &[QubitId],
    carries: &[QubitId],
) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_add_fast_borrowed_carries(b, a, acc, c_in, carries);
    b.free(c_in);
}

pub(crate) fn sub_nbit_qq_fast_borrowed_carries(
    b: &mut B,
    a: &[QubitId],
    acc: &[QubitId],
    carries: &[QubitId],
) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_sub_fast_borrowed_carries(b, a, acc, c_in, carries);
    b.free(c_in);
}

#[inline]
fn maj3_into_clean_2ccx(b: &mut B, x: QubitId, y: QubitId, z: QubitId, target: QubitId) {
    debug_assert!(x != y && x != z && x != target && y != z && y != target && z != target);
    b.ccx(x, z, target);
    b.cx(x, z);
    b.ccx(y, z, target);
    b.cx(x, z);
}

pub(crate) fn add_short_to_long_qq_fast_no_cin(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    let m = a.len();
    let n = acc.len();
    assert!(m > 0);
    assert!(m <= n);
    if n == 1 {
        b.cx(a[0], acc[0]);
        return;
    }

    let carries = b.alloc_qubits(n - 1);
    for i in 0..n - 1 {
        if i < m {
            if i == 0 {
                b.ccx(acc[i], a[i], carries[i]);
            } else {
                maj3_into_clean_2ccx(b, acc[i], a[i], carries[i - 1], carries[i]);
            }
        } else {
            b.ccx(acc[i], carries[i - 1], carries[i]);
        }
    }

    for i in 0..n {
        if i < m {
            b.cx(a[i], acc[i]);
        }
        if i > 0 {
            b.cx(carries[i - 1], acc[i]);
        }
    }

    for i in (0..n - 1).rev() {
        let bit = b.alloc_bit();
        b.hmr(carries[i], bit);
        if i < m {
            b.x(acc[i]);
            b.cz_if(acc[i], a[i], bit);
            if i > 0 {
                b.cz_if(acc[i], carries[i - 1], bit);
                b.x(acc[i]);
                b.cz_if(a[i], carries[i - 1], bit);
            } else {
                b.x(acc[i]);
            }
        } else {
            b.x(acc[i]);
            b.cz_if(acc[i], carries[i - 1], bit);
            b.x(acc[i]);
        }
    }
    b.free_vec(&carries);
}

pub(crate) fn sub_short_to_long_qq_fast_no_cin(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    let m = a.len();
    let n = acc.len();
    assert!(m > 0);
    assert!(m <= n);
    if n == 1 {
        b.cx(a[0], acc[0]);
        return;
    }

    let borrows = b.alloc_qubits(n - 1);
    for i in 0..n - 1 {
        if i < m {
            b.x(acc[i]);
            if i == 0 {
                b.ccx(acc[i], a[i], borrows[i]);
            } else {
                maj3_into_clean_2ccx(b, acc[i], a[i], borrows[i - 1], borrows[i]);
            }
            b.x(acc[i]);
        } else {
            b.x(acc[i]);
            b.ccx(acc[i], borrows[i - 1], borrows[i]);
            b.x(acc[i]);
        }
    }

    for i in 0..n {
        if i < m {
            b.cx(a[i], acc[i]);
        }
        if i > 0 {
            b.cx(borrows[i - 1], acc[i]);
        }
    }

    for i in (0..n - 1).rev() {
        let bit = b.alloc_bit();
        b.hmr(borrows[i], bit);
        if i < m {
            b.cz_if(acc[i], a[i], bit);
            if i > 0 {
                b.cz_if(acc[i], borrows[i - 1], bit);
                b.cz_if(a[i], borrows[i - 1], bit);
            }
        } else {
            b.cz_if(acc[i], borrows[i - 1], bit);
        }
    }
    b.free_vec(&borrows);
}

/// Bounded variant of `add_short_to_long_qq_fast_no_cin`. The full-length
/// variant requires `a.len() <= acc.len()` and adds every bit of `a` into
/// `acc`. In the qprod row emitter the addend is a static-width register
/// (`q` is bounded by `ROUND84_QUOTIENT_BITS` bits) but the target is
/// narrowed to a static upper bound `acc_width` (which is at most
/// `q_width + c_width + shift`); the high bits of `q` are provably
/// leading-zero relative to the truncated target. This function elides them,
/// allocating only the carries needed to span the visible part of the row.
pub(crate) fn add_short_to_long_qq_fast_no_cin_bounded(
    b: &mut B,
    a: &[QubitId],
    acc: &[QubitId],
) {
    let m_full = a.len();
    let n_full = acc.len();
    debug_assert!(m_full > 0);
    debug_assert!(n_full > 0);

    let m = m_full.min(n_full);
    let a_window: &[QubitId] = &a[..m];
    let acc_window: &[QubitId] = &acc[..m];
    if m == 1 {
        b.cx(a_window[0], acc_window[0]);
        return;
    }

    let carries = b.alloc_qubits(m - 1);
    b.ccx(acc_window[0], a_window[0], carries[0]);
    for i in 1..m - 1 {
        maj3_into_clean_2ccx(b, acc_window[i], a_window[i], carries[i - 1], carries[i]);
    }

    for i in 0..m {
        if i > 0 {
            b.cx(carries[i - 1], acc_window[i]);
        }
    }
    for i in 0..m {
        b.cx(a_window[i], acc_window[i]);
    }

    for i in (0..m - 1).rev() {
        let bit = b.alloc_bit();
        b.hmr(carries[i], bit);
        if i < m {
            b.x(acc_window[i]);
            b.cz_if(acc_window[i], a_window[i], bit);
            if i > 0 {
                b.cz_if(acc_window[i], carries[i - 1], bit);
                b.x(acc_window[i]);
                b.cz_if(a_window[i], carries[i - 1], bit);
            } else {
                b.x(acc_window[i]);
            }
        } else {
            b.x(acc_window[i]);
            b.cz_if(acc_window[i], carries[i - 1], bit);
            b.x(acc_window[i]);
        }
    }
    b.free_vec(&carries);
}

/// Bounded variant of `sub_short_to_long_qq_fast_no_cin`. Same elision
/// contract as the bounded add: only the first `min(a.len(), acc.len())`
/// bits participate.
pub(crate) fn sub_short_to_long_qq_fast_no_cin_bounded(
    b: &mut B,
    a: &[QubitId],
    acc: &[QubitId],
) {
    let m_full = a.len();
    let n_full = acc.len();
    debug_assert!(m_full > 0);
    debug_assert!(n_full > 0);

    let m = m_full.min(n_full);
    let a_window: &[QubitId] = &a[..m];
    let acc_window: &[QubitId] = &acc[..m];
    if m == 1 {
        b.cx(a_window[0], acc_window[0]);
        return;
    }

    let borrows = b.alloc_qubits(m - 1);
    b.x(acc_window[0]);
    b.ccx(acc_window[0], a_window[0], borrows[0]);
    b.x(acc_window[0]);
    for i in 1..m - 1 {
        b.x(acc_window[i]);
        maj3_into_clean_2ccx(b, acc_window[i], a_window[i], borrows[i - 1], borrows[i]);
        b.x(acc_window[i]);
    }

    for i in 0..m {
        if i > 0 {
            b.cx(borrows[i - 1], acc_window[i]);
        }
    }
    for i in 0..m {
        b.cx(a_window[i], acc_window[i]);
    }

    for i in (0..m - 1).rev() {
        let bit = b.alloc_bit();
        b.hmr(borrows[i], bit);
        if i < m {
            b.cz_if(acc_window[i], a_window[i], bit);
            if i > 0 {
                b.cz_if(acc_window[i], borrows[i - 1], bit);
                b.cz_if(a_window[i], borrows[i - 1], bit);
            }
        } else {
            b.cz_if(acc_window[i], borrows[i - 1], bit);
        }
    }
    b.free_vec(&borrows);
}

pub(crate) fn add_nbit_qq(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_add(b, a, acc, c_in);
    b.free(c_in);
}

pub(crate) fn sub_nbit_qq(b: &mut B, a: &[QubitId], acc: &[QubitId]) {
    assert_eq!(a.len(), acc.len());
    let c_in = b.alloc_qubit();
    cuccaro_sub(b, a, acc, c_in);
    b.free(c_in);
}

pub(crate) fn add_nbit_const(b: &mut B, acc: &[QubitId], c: U256) {
    let n = acc.len();
    let a = load_const(b, n, c);
    add_nbit_qq(b, &a, acc);
    unload_const(b, &a, c);
}

pub(crate) fn sub_nbit_const(b: &mut B, acc: &[QubitId], c: U256) {
    let n = acc.len();
    let a = load_const(b, n, c);
    sub_nbit_qq(b, &a, acc);
    unload_const(b, &a, c);
}
