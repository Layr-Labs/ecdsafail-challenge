//! Karatsuba modular square-subtract: `out -= y^2 (mod p)` on secp256k1.
//!
//! Called once per point addition, as the `square` phase, where `y` holds
//! the chord slope and `out` the running x-coordinate. `y` comes back
//! bit-exact and every scratch qubit is returned to |0>, because this runs
//! inside a larger reversible computation that is later run backwards.
//!
//! `y = a + b*2^128` gives `y^2 = A + (C - A - B)*2^128 + B*2^256` with
//! `A = a^2`, `B = b^2`, `C = (a+b)^2`, so three squares suffice rather than
//! four. Each is built by the same split one level down, in `tri_square_k2r`,
//! and folded into `out` with integer weights -- which is what lets each be
//! materialised, folded and uncomputed before the next is built.
//!
//! The sign of every fold is settled while the circuit is built, so it travels
//! as a `bool` and never as a wire: `negate` turns an add into the
//! complement-add-complement subtraction.

use super::modular::{add_wide, addsub_full, addsub_wide, mod_addsub, sub_wide};
use super::{fold_guard, Builder, N};
use crate::circuit::QubitId;

/// `f = 2^256 - p` in non-adjacent form: the value is `sum (-1)^neg * 2^shift`,
/// i.e. `1 + 2^4 - 2^6 + 2^10 + 2^32`. Five terms against the constant's six set
/// bits, and every fold of `f` in this file is driven off it.
const F_NAF: [(usize, bool); 5] = [(0, false), (4, false), (6, true), (10, false), (32, false)];

// This file's three approximations -- the `+f` add and the erasure comparator
// inside `mod_addsub`, and `window_add`'s headroom below -- all read the
// tree-wide `FOLD_GUARD` / `ERASE_COMPARE`. None of them is the
// square's own: a fold is a fold wherever it sits, and the balance rule prices
// them all the same.

/// One triangular row: `acc -+= operand`, conditioned on `ctrl` being *clear*.
/// The carry-out CX leads on the way in and trails on the way out.
fn row_addsub(
    circ: &mut Builder,
    ctrl: QubitId,
    operand: &[QubitId],
    acc: &[QubitId],
    inverse: bool,
) {
    let k = operand.len();
    assert_eq!(acc.len(), k + 1);
    circ.x(ctrl);
    if inverse {
        circ.cx(ctrl, acc[k]);
    }
    circ.cx_all(ctrl, &acc[..k]);
    addsub_wide(circ, operand, acc, inverse);
    circ.cx_all(ctrl, &acc[..k]);
    if !inverse {
        circ.cx(ctrl, acc[k]);
    }
    circ.x(ctrl);
}

fn tri_square(circ: &mut Builder, x: &[QubitId], product: &[QubitId], inverse: bool) {
    let m = x.len();
    assert_eq!(product.len(), 2 * m);
    assert_ne!(m, 0);
    if inverse {
        tri_corr(circ, x, product, true);
    }
    // Forward walks the rows low-to-high; the inverse undoes them high-to-low.
    // Row `i` lands `x[i+1..]` at offset `2i+1`, so it spans up to bit `i+m+1`.
    for r in 0..m - 1 {
        let i = if inverse { m - 2 - r } else { r };
        let row = &product[2 * i + 1..i + m + 1];
        row_addsub(circ, x[i], &x[i + 1..], row, inverse);
    }
    if !inverse {
        tri_corr(circ, x, product, false);
    }
}

/// The diagonal correction: two full-width terms of opposite sign. The inverse
/// runs them in the opposite order with both signs flipped.
fn tri_corr(circ: &mut Builder, x: &[QubitId], product: &[QubitId], inverse: bool) {
    if inverse {
        diag_correction(circ, x, product, false);
        diag_spread(circ, x, product, true);
    } else {
        diag_spread(circ, x, product, false);
        diag_correction(circ, x, product, true);
    }
}

/// x interleaved with fresh zeros, i.e. the bits of x at odd positions.
///
/// The addend's bit 0 is one of those zeros, so the whole term is even and the
/// ripple can start at position 1: `product[1..] -+= spread(x) >> 1` is the
/// same computation over one bit less, and bit 0 cannot receive a carry or a
/// borrow from it. That drops the leading Toffoli and one pad per call.
fn diag_spread(circ: &mut Builder, x: &[QubitId], product: &[QubitId], inverse: bool) {
    let m = x.len();
    let pads = circ.alloc_qubits(m - 1);
    let mut value = Vec::with_capacity(2 * m - 1);
    value.push(x[0]);
    for i in 1..m {
        value.push(pads[i - 1]);
        value.push(x[i]);
    }
    addsub_full(circ, &value, &product[1..], inverse);
    circ.free_vec(&pads);
}

/// `x + ~(x mod 2^(m-1)) << m`. The two halves occupy disjoint bit ranges, so
/// they concatenate into one full-width term; building the complemented high
/// half is Clifford, which saves an (m-1)-Toffoli carry ladder per correction.
fn diag_correction(circ: &mut Builder, x: &[QubitId], product: &[QubitId], inverse: bool) {
    let m = x.len();
    let pads = circ.alloc_qubits(m);
    for i in 0..m - 1 {
        circ.cx(x[i], pads[i]);
        circ.x(pads[i]);
    }
    let mut value = x.to_vec();
    value.extend_from_slice(&pads);
    addsub_full(circ, &value, product, inverse);
    for i in 0..m - 1 {
        circ.x(pads[i]);
        circ.cx(x[i], pads[i]);
    }
    circ.free_vec(&pads);
}

/// Truncated fold of `value` at `shift`: carries past [`fold_guard`] bits of
/// headroom above the operand are discarded. Same knob and same meaning as the
/// headroom [`super::modular::f_slice`] leaves above `f`; this one just sits
/// above a register rather than a constant.
fn window_add(circ: &mut Builder, negate: bool, value: &[QubitId], out: &[QubitId], shift: usize) {
    let top = shift + value.len() + fold_guard();
    assert!(top <= out.len());
    addsub_wide(circ, value, &out[shift..top], negate);
}

/// Fold a value whose high limb has wrapped past `2^N`. Since `2^N = f (mod
/// p)`, that limb contributes `f * high`: rotating it into the vacated low
/// positions folds its unit term into the main modular add, and the remaining
/// NAF terms carry the `(f - 1) * high` that is left.
fn fold_rotated(
    circ: &mut Builder,
    negate: bool,
    low: &[QubitId],
    high: &[QubitId],
    out: &[QubitId],
) {
    let wrapped = N - low.len();
    assert!(high.len() >= wrapped);
    let mut rotated = Vec::with_capacity(N);
    rotated.extend_from_slice(&high[..wrapped]);
    rotated.extend_from_slice(low);
    mod_addsub(circ, negate, &rotated, out);
    // The unit term of `f * high` rode in on the rotate; the rest of the NAF
    // carries the `(f - 1) * high` that is left.
    for (shift, neg) in F_NAF.into_iter().skip(1) {
        window_add(circ, negate ^ neg, high, out, shift);
    }
}

/// `out -+= value * 2^shift (mod p)` for a full-width value.
fn fold_shifted(
    circ: &mut Builder,
    negate: bool,
    value: &[QubitId],
    out: &[QubitId],
    shift: usize,
) {
    assert_eq!(value.len(), N);
    assert!(shift < N);
    if shift == 0 {
        mod_addsub(circ, negate, value, out);
    } else {
        fold_rotated(circ, negate, &value[..N - shift], &value[N - shift..], out);
    }
}

/// `out -+= product * f`, i.e. `product * 2^256 (mod p)`.
fn fold_times_f(circ: &mut Builder, negate: bool, product: &[QubitId], out: &[QubitId]) {
    assert_eq!(product.len(), out.len());
    for (shift, neg) in F_NAF {
        fold_shifted(circ, negate ^ neg, product, out, shift);
    }
}

/// Scratch held from a forward split to its matching inverse: `t = a + b`, and
/// a register that holds `t^2` at both ends and `2ab` in between.
type K2Retained = (Vec<QubitId>, Vec<QubitId>);

/// Triangular square of `x` into the materialised `product` via the in-place
/// Karatsuba split: `a^2` and `b^2` are built by `tri_square` directly into the
/// two DISJOINT halves of the zeroed product register, and the cross term
/// `2ab = t^2 - a^2 - b^2` is built in the returned scratch and rippled in at
/// shift `lo` with one full-width exact add. That scratch stays live across the
/// consumer's folds, so the inverse never recomputes a sub-square.
///
/// Every primitive here is an exact full-width add or subtract, so this adds no
/// truncated comparison, windowed fold or measured chunk boundary — the
/// per-shot failure site count is unchanged in both channels by construction.
fn tri_square_k2r(circ: &mut Builder, x: &[QubitId], product: &[QubitId]) -> K2Retained {
    let m = x.len();
    assert_eq!(product.len(), 2 * m);
    let lo = m / 2;
    let (a, bs) = x.split_at(lo);
    let (a2, b2) = product.split_at(2 * lo);
    // a^2 and b^2 straight into the disjoint halves of the zeroed product.
    tri_square(circ, a, a2, false);
    tri_square(circ, bs, b2, false);
    // t = a + b, one bit wider than b.
    let t = circ.alloc_qubits(bs.len() + 1);
    circ.cx_pairs(a, &t[..lo]);
    add_wide(circ, bs, &t);
    // p_t = t^2, then subtract the still-pure halves to leave 2ab. Both
    // intermediates are nonnegative (t^2 - a^2 = 2ab + b^2 >= 0), so the
    // two's-complement frame never wraps at this width.
    let p_t = circ.alloc_qubits(2 * t.len());
    tri_square(circ, &t, &p_t, false);
    sub_wide(circ, a2, &p_t);
    sub_wide(circ, b2, &p_t);
    // product += 2ab << lo, exact full ripple to the top (x^2 < 2^(2m), so the
    // top never overflows).
    add_wide(circ, &p_t, &product[lo..]);
    (t, p_t)
}

/// Inverse of `tri_square_k2r`, consuming its retained scratch. Requires
/// `product` to hold exactly `x^2` (i.e. every consumer fold undone).
fn tri_square_k2r_inv(
    circ: &mut Builder,
    x: &[QubitId],
    product: &[QubitId],
    retained: K2Retained,
) {
    let m = x.len();
    assert_eq!(product.len(), 2 * m);
    let (t, p_t) = retained;
    let lo = m / 2;
    let (a, bs) = x.split_at(lo);
    let (a2, b2) = product.split_at(2 * lo);
    // product -= 2ab << lo: the halves are pure a^2 / b^2 again.
    sub_wide(circ, &p_t, &product[lo..]);
    // p_t: 2ab -> t^2, then clear it with the inverse triangular square.
    add_wide(circ, b2, &p_t);
    add_wide(circ, a2, &p_t);
    tri_square(circ, &t, &p_t, true);
    circ.free_vec(&p_t);
    // Uncompute t = a + b.
    sub_wide(circ, bs, &t);
    circ.cx_pairs(a, &t[..lo]);
    circ.free_vec(&t);
    // Clear the pure halves.
    tri_square(circ, bs, b2, true);
    tri_square(circ, a, a2, true);
}

/// Materialise `x^2` in a fresh register, run `folds` against it, then uncompute
/// and release it.
///
/// The shape the whole file is built around: a sub-square is live only for the
/// folds that consume it, and `tri_square_k2r`'s retained scratch makes the
/// uncompute exact rather than a second square. Having the three uses go through
/// here means a fold cannot be added without its inverse, or a register leaked.
fn with_square(circ: &mut Builder, x: &[QubitId], folds: impl FnOnce(&mut Builder, &[QubitId])) {
    let product = circ.alloc_qubits(2 * x.len());
    let retained = tri_square_k2r(circ, x, &product);
    folds(circ, &product);
    tri_square_k2r_inv(circ, x, &product, retained);
    circ.free_vec(&product);
}

pub fn sub_square(circ: &mut Builder, out: &[QubitId], y: &[QubitId]) {
    assert_eq!(y.len(), N);
    assert_eq!(out.len(), N);
    let h = N / 2;
    let (y_lo, y_hi) = y.split_at(h);

    // y = a + b*2^h, so y^2 = A + (C - A - B)*2^h + B*2^256 with A = a^2,
    // B = b^2, C = (a+b)^2. Five folds, and this routine subtracts, so every
    // sign below is the negation of that expansion.
    with_square(circ, y_lo, |circ, a2| {
        mod_addsub(circ, true, a2, out);
        fold_shifted(circ, false, a2, out, h);
    });

    with_square(circ, y_hi, |circ, b2| {
        fold_shifted(circ, false, b2, out, h);
        fold_times_f(circ, true, b2, out);
    });

    // a+b lives in the caller's own high half plus one borrowed carry wire, and
    // is restored right after the cross-term square. That keeps the Karatsuba
    // identity exact without standing up a separate 129-qubit register.
    let sum_carry = circ.alloc_qubit();
    let mut sum = y_hi.to_vec();
    sum.push(sum_carry);
    add_wide(circ, y_lo, &sum);

    // C is 258 bits, so its high limb overhangs the rotate by two bits; those
    // ride in on a separate window add at the same shift.
    with_square(circ, &sum, |circ, c2| {
        fold_rotated(circ, true, &c2[..h], &c2[h..], out);
        window_add(circ, true, &c2[2 * h..], out, h);
    });

    sub_wide(circ, y_lo, &sum);
    circ.free(sum_carry);
}
