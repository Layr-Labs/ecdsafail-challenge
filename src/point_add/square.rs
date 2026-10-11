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

use super::modular::{
    add_wide, addsub_full, addsub_full_low, addsub_wide, addsub_wide_low, mod_addsub, sub_wide,
    Carry0, Carry1,
};
use super::{fold_guard, pinned_env, Builder, N};
use crate::circuit::{BitId, QubitId};
use alloy_primitives::U256;
fn cut_sqident() -> bool {
    super::env_flag("PP_CUT_SQIDENT")
}
/// SQ_ROW0_COPY: every SQ_CIN_SPREAD leaf stores `x^2 - 2` (row 0 becomes a
/// Clifford copy), each node's product and cross carry known constant offsets,
/// and the square's total offset is pre-added classically in `coord_add3x`.
fn row0_copy() -> bool {
    super::env_flag("SQ_ROW0_COPY") && super::env_flag("SQ_CIN_SPREAD")
}
/// The low-diagonal preload ([`diag_preload`]). Off by default: with this clear
/// the file emits exactly the stream it did before the lever existed.
fn diag_preload_on() -> bool {
    super::env_flag("SQ_DIAG_PRELOAD")
}

/// How many of the diagonal's bits ride in for free.
///
/// `diag_spread` adds `2*spread(x)`, whose bit `j` sits at product position
/// `2j+1`. The row ladder leaves exactly `2^m - 1` of headroom below every
/// row window's top (the rows sum to at most `2^(i+m+1) - 2^m` after row `i`,
/// and the window reaches bit `i+m`), so any value under `2^m` may be sitting
/// in the product BEFORE the first row without any row's truncated window
/// losing a carry. The diagonal bits with `2j+1 < m` are exactly that value --
/// their sum is under `2^(2*ceil((m-1)/2)) <= 2^m` -- so they are copied in
/// with a CX apiece and the add that used to carry them shrinks from the full
/// `2m-1` positions to the `2m-2j0-1` above them.
///
/// `j0 = ceil((m-1)/2) = m/2` in integer division. Zero when the knob is off,
/// which is what makes every routine below fall back to its old shape.
fn diag_split(m: usize) -> usize {
    if diag_preload_on() {
        m / 2
    } else {
        0
    }
}

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
    first_copies_operand: bool,
    borrowed: Option<&[QubitId]>,
) {
    let k = operand.len();
    assert_eq!(acc.len(), k + 1);
    circ.x(ctrl);
    if inverse {
        circ.cx(ctrl, acc[k]);
    }
    circ.cx_all(ctrl, &acc[..k]);
    if let Some(qs) = borrowed {
        let c0 = if first_copies_operand {
            Carry0::IsAddend0
        } else {
            Carry0::Full
        };
        let top = (inverse && super::env_flag("SQ_ROW_ALL_MEASURE_TOP")).then_some(false);
        super::modular::addsub_wide_borrowed(
            circ,
            operand,
            acc,
            inverse,
            c0,
            Carry1::Full,
            top,
            qs,
        );
    } else if inverse && super::env_flag("SQ_ROW_ALL_MEASURE_TOP") {
        // Before row i, previous rows touched only through product[m+i-1]
        // and preload lies below m. Thus row i's top product[m+i] was zero.
        // On inverse, after its leading top CX, the inner subtraction must
        // restore that zero; the lower complement frame never touches it.
        let c0 = if first_copies_operand {
            Carry0::IsAddend0
        } else {
            Carry0::Full
        };
        super::modular::addsub_wide_known_top(circ, operand, acc, true, c0, Carry1::Full, false);
    } else if first_copies_operand {
        addsub_wide_low(circ, operand, acc, inverse, Carry0::IsAddend0, Carry1::Full);
    } else {
        addsub_wide(circ, operand, acc, inverse);
    }
    circ.cx_all(ctrl, &acc[..k]);
    if !inverse {
        circ.cx(ctrl, acc[k]);
    }
    circ.x(ctrl);
}

/// SQ_CIN_SPREAD: triangular row with the diagonal spread bit riding in on the
/// ripple's carry-in. The complement frame is driven by X gates plus CX from
/// `xi` (instead of X on `xi` itself), so the wire `xi` stays intact and can be
/// the carry-in. The row then computes `acc += (2 xi - 1)(v + xi)
/// = (2 xi - 1) v + xi`, i.e. it also adds `xi * 2^(2i+1)`, which is the spread
/// bit of `xi`. A carry-in costs no Toffoli.
fn row_addsub_cin(
    circ: &mut Builder,
    xi: QubitId,
    operand: &[QubitId],
    acc: &[QubitId],
    inverse: bool,
    first_copies_operand: bool,
    known_output: Option<&[(bool, Vec<QubitId>)]>,
    borrowed: Option<&[QubitId]>,
) {
    let k = operand.len();
    assert_eq!(acc.len(), k + 1);
    if inverse {
        circ.x(acc[k]);
        circ.cx(xi, acc[k]);
    }
    circ.x_all(&acc[..k]);
    circ.cx_all(xi, &acc[..k]);
    if inverse {
        circ.x_all(acc);
    }
    let c0 = if first_copies_operand {
        Carry0::IsAddend0
    } else {
        Carry0::Full
    };
    // Inverse rows restore a state that never reached bit i+m (see
    // SQ_ROW_ALL_MEASURE_TOP); in the subtraction frame that top reads 1.
    let top = (known_output.is_none() && inverse && super::env_flag("SQ_ROW_ALL_MEASURE_TOP"))
        .then_some(true);
    if let Some(out) = known_output.filter(|_| super::env_flag("SQ_ROW1_STREAM")) {
        super::stream_wide::add(circ, operand, acc, Some(xi), out);
    } else {
        super::modular::ripple_add_proved(
            circ,
            operand,
            acc,
            Some(xi),
            None,
            c0,
            Carry1::Full,
            None,
            known_output,
            top,
            borrowed,
        );
    }
    if inverse {
        circ.x_all(acc);
    }
    circ.x_all(&acc[..k]);
    circ.cx_all(xi, &acc[..k]);
    if !inverse {
        circ.x(acc[k]);
        circ.cx(xi, acc[k]);
    }
}

/// SQ_CIN_SPREAD inverse correction: add `x + ~x_low << m` back. The rows alone
/// never reach product[2m-1], and the lone spread CX on that bit has already
/// been undone, so the result's top bit is zero: measured terminal.
fn diag_correction_known_top(circ: &mut Builder, x: &[QubitId], product: &[QubitId]) {
    let m = x.len();
    let pads = circ.alloc_qubits(m);
    for i in 0..m - 1 {
        circ.cx(x[i], pads[i]);
        circ.x(pads[i]);
    }
    let mut value = x.to_vec();
    value.extend_from_slice(&pads);
    let c0 = if cut_sqident() {
        Carry0::IsAddend0
    } else {
        Carry0::Full
    };
    super::modular::addsub_wide_known_top(circ, &value, product, false, c0, Carry1::Full, false);
    for i in 0..m - 1 {
        circ.x(pads[i]);
        circ.cx(x[i], pads[i]);
    }
    circ.free_vec(&pads);
}

/// SQ_CIN_SPREAD leaf: rows carry the whole diagonal spread through their
/// carry-in, the top spread bit x[m-1]*2^(2m-1) is one CX onto a still-zero
/// wire, and only the correction subtract remains. No preload, no spread add.
fn tri_square_cin(circ: &mut Builder, x: &[QubitId], product: &[QubitId], inverse: bool) {
    let m = x.len();
    assert_eq!(product.len(), 2 * m);
    assert!(m >= 3);
    if inverse {
        circ.cx(x[m - 1], product[2 * m - 1]);
        diag_correction_known_top(circ, x, product);
    }
    for r in 0..m - 1 {
        let i = if inverse { m - 2 - r } else { r };
        let row = &product[2 * i + 1..i + m + 1];
        let borrowed =
            super::env_flag("SQ_BORROW_ROW_CARRIES").then(|| &product[m + i + 1..2 * m - 1]);
        if i == 0 && row0_copy() {
            // SQ_ROW0_COPY: row 0 on the zero window would leave
            // F = x0 ? v+1 : 2^k - v. Store F - 1 = x0 ? v : ~v instead (top bit
            // zero), which is Clifford and self-inverse. The leaf then holds
            // x^2 - 2; see [`sub_square_offset`] for where the 2 goes.
            for j in 0..m - 1 {
                circ.cx(x[j + 1], row[j]);
                circ.x(row[j]);
                circ.cx(x[0], row[j]);
            }
            continue;
        }
        if inverse && i == 1 && row0_copy() && super::env_flag("SQ_ROW1_INVERSE_CARRIES") {
            let out = row1_known_output(x);
            if super::env_flag("I48_TRACE") {
                eprintln!("I48_ROW1 {} {}", m, circ.active_qubits());
            }
            row_addsub_cin(circ, x[1], &x[2..], row, true, false, Some(&out), borrowed);
            continue;
        }
        if inverse && i == 0 && super::env_flag("SQ_ROW0_INVERSE_CARRIES") {
            // Before row 0 the product is all zero, so every framed output bit
            // is known: x0 on the k low bits, 1 on the top.
            let k = m - 1;
            let mut out = vec![(false, vec![x[0]]); k];
            out.push((true, Vec::new()));
            row_addsub_cin(circ, x[0], &x[1..], row, true, false, Some(&out), borrowed);
            continue;
        }
        // Forward row 0 sees a zero window: framed acc[0] = NOT x0 = NOT carry_in,
        // so its first carry is x[1].
        let first = super::env_flag("SQ_ROW0_CARRY") && !inverse && i == 0;
        row_addsub_cin(circ, x[i], &x[i + 1..], row, inverse, first, None, borrowed);
    }
    if !inverse {
        circ.cx(x[m - 1], product[2 * m - 1]);
        diag_correction(circ, x, product, true);
    }
}

fn tri_square(circ: &mut Builder, x: &[QubitId], product: &[QubitId], inverse: bool) {
    if super::env_flag("SQ_CIN_SPREAD") {
        tri_square_cin(circ, x, product, inverse);
        return;
    }
    let m = x.len();
    assert_eq!(product.len(), 2 * m);
    assert_ne!(m, 0);
    if inverse {
        tri_corr(circ, x, product, true);
    } else {
        // Into the still-zeroed product, so this is a copy and not an add.
        diag_preload(circ, x, product);
    }
    // Forward walks the rows low-to-high; the inverse undoes them high-to-low.
    // Row `i` lands `x[i+1..]` at offset `2i+1`, so it spans up to bit `i+m+1`.
    for r in 0..m - 1 {
        let i = if inverse { m - 2 - r } else { r };
        let row = &product[2 * i + 1..i + m + 1];
        // Before forward row i, higher product bits have never been touched.
        // Before inverse row i, the higher rows are already undone. Preload
        // occupies only bits below m. There are m-i-1 clean bits above the
        // row, enough for all m-i-2 owned ripple carries. Return them to zero
        // without releasing the product's ownership or extending its lifetime.
        let borrowed =
            super::env_flag("SQ_BORROW_ROW_CARRIES").then(|| &product[m + i + 1..2 * m - 1]);
        if inverse
            && i == 0
            && diag_split(m) > 0
            && m >= 4
            && super::env_flag("SQ_ROW0_INVERSE_CARRIES")
        {
            row0_inverse_known(circ, x, row, borrowed);
            continue;
        }
        // With diagonal preload, row0 starts at product[1]=x[0]. The
        // controlled complement therefore makes the forward low acc bit 1,
        // so its first carry is x[1]. On reversal the row output low bit is
        // x[0]^x[1]; the two complement frames make the adder's bit x[1],
        // again giving carry x[1]&x[1]=x[1]. Keep the usual measured unwind:
        // only the first carry's computation changes from CCX to CX.
        let copy_first =
            super::env_flag("SQ_ROW0_CARRY") && i == 0 && diag_split(m) > 0 && row.len() >= 4;
        row_addsub(circ, x[i], &x[i + 1..], row, inverse, copy_first, borrowed);
    }
    if !inverse {
        tri_corr(circ, x, product, false);
    } else {
        diag_preload(circ, x, product);
    }
}

/// The diagonal bits that fit under the row ladder's headroom, copied straight
/// into the product. Self-inverse, and free -- a CX apiece, no Toffoli.
///
/// It must run while the product is still |0...0>, i.e. before the first row
/// forward and after the last one on the way back. See [`diag_split`] for why
/// the rows' truncated windows stay exact with it sitting there.
fn diag_preload(circ: &mut Builder, x: &[QubitId], product: &[QubitId]) {
    for j in 0..diag_split(x.len()) {
        circ.cx(x[j], product[2 * j + 1]);
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
    // Bits below `j0` are already in the product -- [`diag_preload`] put them
    // there for free. With the knob off `j0` is 0 and this is the whole term.
    let j0 = diag_split(m);
    let k = m - j0;
    if super::env_flag("SQ_SPARSE_SPREAD") {
        let map: Vec<Vec<QubitId>> = (0..2 * k - 1)
            .map(|i| {
                if i % 2 == 0 {
                    vec![x[j0 + i / 2]]
                } else {
                    Vec::new()
                }
            })
            .collect();
        sparse_diag_add(circ, &map, &product[2 * j0 + 1..], inverse, false);
        return;
    }
    let pads = circ.alloc_qubits(k - 1);
    let mut value = Vec::with_capacity(2 * k - 1);
    value.push(x[j0]);
    for i in 1..k {
        value.push(pads[i - 1]);
        value.push(x[j0 + i]);
    }
    if inverse && super::env_flag("SQ_ZERO_TOP_SPREAD") {
        // After removing the diagonal corrections only row outputs remain;
        // no triangular row ever reached product[2m-1].
        super::modular::addsub_wide_known_top(
            circ,
            &value,
            &product[2 * j0 + 1..],
            true,
            Carry0::Full,
            Carry1::Full,
            false,
        );
    } else {
        addsub_full(circ, &value, &product[2 * j0 + 1..], inverse);
    }
    circ.free_vec(&pads);
}

/// `x + ~(x mod 2^(m-1)) << m`. The two halves occupy disjoint bit ranges, so
/// they concatenate into one full-width term; building the complemented high
/// half is Clifford, which saves an (m-1)-Toffoli carry ladder per correction.
fn diag_correction(circ: &mut Builder, x: &[QubitId], product: &[QubitId], inverse: bool) {
    let m = x.len();
    if super::env_flag("SQ_SPARSE_CORRECTION") {
        let one = circ.alloc_qubit();
        circ.x(one);
        let mut map: Vec<Vec<QubitId>> = x.iter().map(|&q| vec![q]).collect();
        for &q in x.iter().take(m - 1) {
            map.push(vec![q, one]);
        }
        map.push(Vec::new());
        sparse_diag_add(circ, &map, product, inverse, cut_sqident() && 2 * m >= 4);
        circ.x(one);
        circ.free(one);
        return;
    }
    let pads = circ.alloc_qubits(m);
    for i in 0..m - 1 {
        circ.cx(x[i], pads[i]);
        circ.x(pads[i]);
    }
    let mut value = x.to_vec();
    value.extend_from_slice(&pads);
    if cut_sqident() && 2 * m >= 4 {
        addsub_full_low(
            circ,
            &value,
            product,
            inverse,
            Carry0::IsAddend0,
            Carry1::Full,
        );
    } else {
        addsub_full(circ, &value, product, inverse);
    }
    for i in 0..m - 1 {
        circ.x(pads[i]);
        circ.cx(x[i], pads[i]);
    }
    circ.free_vec(&pads);
}

/// Undo the first row after all subsequent rows have been removed. Its output
/// is the affine diagonal preload. Inside the subtraction/complement frame,
/// output[j] = preload[j+1] XOR original_x0 for j<m-1, and output[m-1]=1.
/// Those expressions recover every owned arithmetic carry without an AND.
/// Keep the generic terminal CCX and measured carry unwind; scratch is unchanged.
fn row0_inverse_known(
    circ: &mut Builder,
    x: &[QubitId],
    row: &[QubitId],
    borrowed: Option<&[QubitId]>,
) {
    let m = x.len();
    let k = m - 1;
    assert_eq!(row.len(), m);
    circ.x(x[0]); // the ordinary row's complemented control
    circ.cx(x[0], row[k]);
    circ.cx_all(x[0], &row[..k]);
    circ.x_all(row); // addsub_wide's subtraction frame
    let mut output = Vec::with_capacity(m);
    for j in 0..m {
        // The preload's lowest bit is original_x0, hence this framed output
        // bit is zero. x[0] itself is currently complemented.
        if j == 0 {
            output.push((false, Vec::new()));
            continue;
        }
        let mut sources = Vec::new();
        if j < k {
            sources.push(x[0]);
            if j % 2 == 0 && j / 2 < diag_split(m) {
                sources.push(x[j / 2]);
            }
        }
        output.push((true, sources));
    }
    super::modular::add_wide_known_output(circ, &x[1..], row, &output, borrowed);
    circ.x_all(row);
    circ.cx_all(x[0], &row[..k]);
    circ.x(x[0]);
}

/// Exact full-width addition of the diagonal's XOR expressions, without an
/// interleaved zero register or a copied complemented high half. The first
/// carry stays separate from aliased source bits throughout the mapped add.
fn sparse_diag_add(
    circ: &mut Builder,
    map: &[Vec<QubitId>],
    acc: &[QubitId],
    inverse: bool,
    first_copies_source: bool,
) {
    assert_eq!(map.len(), acc.len());
    assert!(!acc.is_empty());
    assert_eq!(map[0].len(), 1);
    if acc.len() == 1 {
        circ.cx(map[0][0], acc[0]);
        return;
    }
    if inverse {
        circ.x_all(acc);
    }
    let source0 = map[0][0];
    let first = circ.alloc_qubit();
    if first_copies_source {
        circ.cx(source0, first);
    } else {
        circ.ccx(source0, acc[0], first);
    }
    circ.cx(source0, acc[0]);
    let n = acc.len() - 1;
    let room = super::pingpong::walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
    let plan = (room..=n.max(room))
        .find_map(|r| super::width_composition::direct_plan(n, r))
        .unwrap();
    super::width_composition::direct_add(circ, &map[1..], &acc[1..], first, &plan);
    if first_copies_source {
        circ.cx(source0, first);
    } else {
        circ.cx(source0, acc[0]);
        let bit = circ.alloc_bit();
        circ.hmr(first, bit);
        circ.cz_if(source0, acc[0], bit);
        circ.free_bit(bit);
        circ.cx(source0, acc[0]);
    }
    circ.free(first);
    if inverse {
        circ.x_all(acc);
    }
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
    if super::j_fuse::j_wcin() {
        fold_rotated_wcin(circ, negate, &rotated, high, out);
        return;
    }
    mod_addsub(circ, negate, &rotated, out);
    // The unit term of `f * high` rode in on the rotate; the rest of the NAF
    // carries the `(f - 1) * high` that is left.
    for (shift, neg) in F_NAF.into_iter().skip(1) {
        window_add(circ, negate ^ neg, high, out, shift);
    }
}

/// PP_J_WCIN: [`fold_rotated`] with the ripple's carry folded through the NAF
/// windows' carry-ins plus a narrow unit-term increment (see `j_fuse`).
fn fold_rotated_wcin(
    circ: &mut Builder,
    negate: bool,
    rotated: &[QubitId],
    high: &[QubitId],
    out: &[QubitId],
) {
    let c = wcin_ripple(circ, negate, rotated, out);
    wcin_windows(circ, negate, high, out, c);
    wcin_finish(circ, negate, rotated, out, c);
}

fn wcin_ripple(circ: &mut Builder, negate: bool, rotated: &[QubitId], out: &[QubitId]) -> QubitId {
    assert_eq!(rotated.len(), N);
    if negate {
        circ.x_all(out);
    }
    // CLASSIFIER adapt (HEO builds only): route the vented ripple through HEO's room-fitted path.
    let c = if super::heo::fit_adds() {
        super::modular::heo_vented_ripple(circ, rotated, out)
    } else {
        let c = circ.alloc_qubit();
        super::modular::peak_fitted_add(circ, rotated, out, c);
        c
    };
    if negate {
        circ.x_all(out);
    }
    // out now holds D (mod 2^256); the value is D + s*c*f, s = -1 when negate.
    c
}

fn wcin_windows(circ: &mut Builder, negate: bool, high: &[QubitId], out: &[QubitId], c: QubitId) {
    let k = super::j_fuse::x_erase_width();
    for (shift, neg) in F_NAF.into_iter().skip(1) {
        let top = shift + high.len() + fold_guard();
        assert!(top <= N - k, "WCIN window reaches the erase compare");
        let win = &out[shift..top];
        let inv = negate ^ neg;
        if inv {
            circ.x_all(win);
        }
        let owned = win.len() - 2;
        let room = super::pingpong::walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
        // CLASSIFIER adapt: under HEO, ripple_add_proved's HEO block chunks the window to the room.
        if room >= owned || super::heo::fit_adds() {
            super::modular::ripple_add(circ, high, win, Some(c), None);
        } else {
            // One wire short: the carry-in hosts position 0's carry in place
            // (a Cuccaro MAJ/UMA pair), one extra Toffoli for one fewer wire.
            assert!(
                room + 1 >= owned,
                "WCIN window more than one wire over the peak: room {room} owned {owned}"
            );
            let (v0, a0) = (high[0], win[0]);
            circ.cx(c, v0);
            circ.cx(c, a0);
            circ.ccx(v0, a0, c);
            super::modular::ripple_add(circ, &high[1..], &win[1..], Some(c), None);
            circ.ccx(v0, a0, c);
            circ.cx(c, v0);
            circ.cx(c, a0);
            circ.cx(v0, a0);
            circ.cx(c, a0);
        }
        if inv {
            circ.x_all(win);
        }
    }
}

fn wcin_finish(circ: &mut Builder, negate: bool, rotated: &[QubitId], out: &[QubitId], c: QubitId) {
    let k = super::j_fuse::x_erase_width();
    let w = super::j_fuse::wcin_w();
    assert!(w <= N - k);
    let unit = &out[..w];
    if negate {
        circ.x_all(unit);
    }
    super::const_arith::cadd_const_trunc(circ, unit, U256::from(1), c, false);
    if negate {
        circ.x_all(unit);
    }
    let top = &out[N - k..];
    if negate {
        circ.x_all(top);
    }
    super::compare::erase_with_compare(circ, c, top, &rotated[N - k..], None);
    if negate {
        circ.x_all(top);
    }
    circ.free(c);
}

fn rotate_by(value: &[QubitId], shift: usize) -> Vec<QubitId> {
    assert_eq!(value.len(), N);
    let mut rotated = Vec::with_capacity(N);
    rotated.extend_from_slice(&value[N - shift..]);
    rotated.extend_from_slice(&value[..N - shift]);
    rotated
}

/// PP_J_BMERGE: `out -= b2 * (2^4 - 2^6 + 2^10 + 2^32) (mod p)` with one window
/// set.  Every fold's `(f-1) * high_s` window term has sign `-` except the
/// 2^6 one, so together they are `-(f-1) * R` with
/// `R = high32 + high10 - high6 + high4` (the highs are b2's top s bits;
/// high10 >= high6, so 0 <= R < 2^33).  The 2^32 fold runs last and its carry
/// rides the merged windows exactly as in [`fold_rotated_wcin`].
fn b_merged_folds(circ: &mut Builder, b2: &[QubitId], out: &[QubitId]) {
    assert_eq!(b2.len(), N);
    for (shift, neg) in F_NAF.into_iter().skip(1).take(3) {
        mod_addsub(circ, true ^ neg, &rotate_by(b2, shift), out);
    }
    let (s32, n32) = F_NAF[4];
    assert!(s32 == 32 && !n32);
    let rot32 = rotate_by(b2, 32);
    let c = wcin_ripple(circ, true, &rot32, out);
    let skywalk_mode = std::env::var("SKYWALK_MERGED_HIGH_STREAM")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(0);
    if skywalk_mode == 1 || skywalk_mode == 3 {
        skywalk_merged_high_stream(circ, &b2[N - 32..], |circ, r| {
            if skywalk_mode == 3 {
                super::modular::shared_exact_split_scope(circ, |circ| {
                    wcin_windows(circ, true, r, out, c)
                });
            } else {
                wcin_windows(circ, true, r, out, c);
            }
        });
        wcin_finish(circ, true, &rot32, out, c);
        return;
    }
    let hi = |s: usize| &b2[N - s..];
    let small = circ.alloc_qubits(if skywalk_mode == 2 { 10 } else { 11 });
    for i in 0..10 {
        circ.cx(hi(10)[i], small[i]);
    }
    let keep: usize = std::env::var("SHARED_BMERGE_CARRIES")
        .ok()
        .map(|v| v.parse().unwrap())
        .unwrap_or(0);
    let census = std::env::var_os("SHARED_CARRY_TRACE").is_some();
    let before = circ.report_totals().map(|x| x.1).unwrap_or(0.0);
    if census {
        eprintln!(
            "SHARED_BMERGE entry mask={} live={} peak={}",
            keep,
            circ.active_qubits(),
            circ.peak_total()
        );
    }
    let c6 = if keep & 1 != 0 {
        Some(super::modular::shared_carry_forward(
            circ,
            hi(6),
            &small,
            true,
        ))
    } else {
        addsub_wide(circ, hi(6), &small, true);
        None
    };
    if census {
        eprintln!(
            "SHARED_BMERGE after6 live={} peak={} T={}",
            circ.active_qubits(),
            circ.peak_total(),
            circ.report_totals().unwrap().1 - before
        );
    }
    let c4 = if keep & 2 != 0 {
        Some(super::modular::shared_carry_forward(
            circ,
            hi(4),
            &small,
            false,
        ))
    } else {
        addsub_wide(circ, hi(4), &small, false);
        None
    };
    let r = circ.alloc_qubits(33);
    for i in 0..32 {
        circ.cx(hi(32)[i], r[i]);
    }
    let loan = keep == 7 && super::env_flag("SHARED_BMERGE_SOURCE_LOAN");
    if loan {
        for i in 0..32 {
            circ.cx(r[i], hi(32)[i]);
        }
        circ.free_vec(hi(32));
        if census {
            eprintln!(
                "SHARED_BMERGE source_loan live={} peak={}",
                circ.active_qubits(),
                circ.peak_total()
            );
        }
    }
    let cr = if keep & 4 != 0 {
        Some(super::modular::shared_carry_forward(
            circ, &small, &r, false,
        ))
    } else {
        addsub_wide(circ, &small, &r, false);
        None
    };
    if census {
        eprintln!(
            "SHARED_BMERGE callback_entry live={} peak={} T={}",
            circ.active_qubits(),
            circ.peak_total(),
            circ.report_totals().unwrap().1 - before
        );
    }
    if loan {
        super::modular::shared_exact_split_scope(circ, |circ| wcin_windows(circ, true, &r, out, c));
    } else {
        wcin_windows(circ, true, &r, out, c);
    }
    if census {
        eprintln!(
            "SHARED_BMERGE callback_exit live={} peak={} T={}",
            circ.active_qubits(),
            circ.peak_total(),
            circ.report_totals().unwrap().1 - before
        );
    }
    if let Some(cs) = cr {
        super::modular::shared_carry_inverse(circ, &small, &r, false, cs);
    } else {
        addsub_wide(circ, &small, &r, true);
    }
    if loan {
        for &q in hi(32) {
            circ.reacquire(q);
        }
        for i in 0..32 {
            circ.cx(r[i], hi(32)[i]);
        }
        if census {
            eprintln!(
                "SHARED_BMERGE source_restore live={} peak={}",
                circ.active_qubits(),
                circ.peak_total()
            );
        }
    }
    for i in 0..32 {
        circ.cx(hi(32)[i], r[i]);
    }
    circ.free_vec(&r);
    if let Some(cs) = c4 {
        super::modular::shared_carry_inverse(circ, hi(4), &small, false, cs);
    } else {
        addsub_wide(circ, hi(4), &small, true);
    }
    if let Some(cs) = c6 {
        super::modular::shared_carry_inverse(circ, hi(6), &small, true, cs);
    } else {
        addsub_wide(circ, hi(6), &small, false);
    }
    if census {
        eprintln!(
            "SHARED_BMERGE restore live={} peak={} T={}",
            circ.active_qubits(),
            circ.peak_total(),
            circ.report_totals().unwrap().1 - before
        );
    }
    for i in 0..10 {
        circ.cx(hi(10)[i], small[i]);
    }
    circ.free_vec(&small);
    wcin_finish(circ, true, &rot32, out, c);
}

/// PP_J_SFUSE: `fold_rotated(true, ..)` whose modular subtract keeps its
/// borrow; the borrow's fold moves into the multiply walk's round-0 lift, run
/// here while the subtrahend is still live for the borrow's top-bit compare.
/// `overhang` is an extra window at shift `low.len()` added before the lift.
fn fold_rotated_sub_r0(
    circ: &mut Builder,
    low: &[QubitId],
    high: &[QubitId],
    out: &[QubitId],
    overhang: Option<&[QubitId]>,
) {
    let wrapped = N - low.len();
    assert!(high.len() >= wrapped);
    let mut rotated = Vec::with_capacity(N);
    rotated.extend_from_slice(&high[..wrapped]);
    rotated.extend_from_slice(low);
    let c = super::j_fuse::sub_keep_borrow_q(circ, &rotated, out);
    for (shift, neg) in F_NAF.into_iter().skip(1) {
        window_add(circ, true ^ neg, high, out, shift);
    }
    if let Some(o) = overhang {
        window_add(circ, true, o, out, low.len());
    }
    let k = super::j_fuse::x_erase_width();
    super::pingpong::j_pre_round0(circ, out, c, &rotated[N - k..]);
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

/// Scratch held from a forward split to its matching inverse.
///
/// The sum `t = a + b` is not a register of its own: it lives in the input's
/// high half `b` plus this one borrowed carry wire, exactly as the top-level
/// [`sub_square`] does with the caller's `y_hi`. `b` is restored in the inverse
/// before `b^2` is cleared. `cross` holds `t^2` at both ends and `2ab` in
/// between. `low` / `sum` carry the retained scratch of a child split when a
/// half was itself split rather than squared directly.
struct K2Retained {
    carry: QubitId,
    flat_sum_carries: Vec<QubitId>,
    xkept: Vec<QubitId>,
    cross: Vec<QubitId>,
    low: Option<Box<K2Retained>>,
    sum: Option<Box<K2Retained>>,
    /// The high half's own retained scratch, when [`sq_split_b_min`] split it.
    high: Option<Box<K2Retained>>,
    cross_phase: Option<(super::width_composition::Plan, Vec<(usize, BitId)>)>,
    /// SQ_HOLD_BOUNDARY: live boundary carries of the fitted assembly, cleared
    /// by the inverse assembly's high-to-low chunk ripple.
    held: Vec<QubitId>,
}

/// Recursion policy: a sum half of at least this many bits is split again
/// instead of squared triangularly. `B(m) = m(m-1)/2 + 4m - 3` for the base
/// case against `K(m) = B(a) + B(b) + B(b+1) + a + 7b + 1` for one split puts
/// the break-even near 60 bits; the tree-wide peak, not the count, is what
/// bounds how deep this may go, so it is a pinned knob rather than a constant.
pinned_env!(sq_split_sum_min, "SQ_SPLIT_SUM_MIN");
/// Same policy for the low half `a`, whose split leaves `a` itself modified
/// until the inverse -- so `a` must be consumed (into `t = a + b`) before its
/// split is built. Disabled by pinning it above any half width (>= 129).
pinned_env!(sq_split_low_min, "SQ_SPLIT_LOW_MIN");
/// Same policy for the HIGH half `b`, and the one that needs a restore.
///
/// `b` has to be pristine one line below its own square, where `t = a + b` is
/// formed in its wires -- and a split leaves its input holding that same
/// in-place sum until its inverse. So a split `b` is undone at once with one
/// subtract and re-formed just before its own inverse: two adds of `|b|/2 + 1`
/// bits against the level's saving. That restore is one subtract only while the
/// split does not recurse, because a recursive split leaves two more in-place
/// sums under it -- hence [`tri_square_k2r_flat`]. Unset means never, which is
/// the shipped head.
fn sq_split_b_min() -> usize {
    static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| super::optional_env("SQ_SPLIT_B_MIN").unwrap_or(usize::MAX))
}

// Public build-time policy context, restored by with_square. It changes only
// exact integer producer trees; each inverse follows its retained tree.
thread_local! { static OUTER_SQUARE_POLICY: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) }; }
fn policy_min(bit: usize, default: usize) -> usize {
    OUTER_SQUARE_POLICY.with(|p| match p.get() {
        None => default,
        Some(mask) => {
            if mask & (1 << bit) != 0 {
                if bit == 1 {
                    65
                } else {
                    64
                }
            } else {
                usize::MAX
            }
        }
    })
}

fn square_half(
    circ: &mut Builder,
    x: &[QubitId],
    product: &[QubitId],
    min: usize,
) -> Option<Box<K2Retained>> {
    if x.len() >= min {
        Some(Box::new(tri_square_k2r(circ, x, product)))
    } else {
        tri_square(circ, x, product, false);
        None
    }
}

/// `b^2` into the high half of the product, from the pristine `b`, restoring
/// `b` before returning. See [`sq_split_b_min`] for why the restore is here and
/// not in the inverse, and why the split underneath it does not recurse.
fn square_b(circ: &mut Builder, bs: &[QubitId], b2: &[QubitId]) -> Option<Box<K2Retained>> {
    if bs.len() < policy_min(2, sq_split_b_min()) {
        tri_square(circ, bs, b2, false);
        return None;
    }
    let mut r = tri_square_k2r_flat(circ, bs, b2);
    high_early_trace(circ, bs, &r, "producer_end");
    high_early_pair(circ, bs, &r, false);
    let (a, inner) = bs.split_at(bs.len() / 2);
    let mut t = inner.to_vec();
    t.push(r.carry);
    if r.flat_sum_carries.is_empty() {
        restore_square_sum(circ, a, &t);
    } else {
        sum_bank_inverse(circ, a, &t, std::mem::take(&mut r.flat_sum_carries));
    }
    high_early_trace(circ, bs, &r, "source_restored");
    // SQ_HIGH_CARRY_LOAN: t - a = b < 2^|b| left r.carry at exactly |0>, and
    // nothing reads it until square_b_inv re-forms the in-place sum.
    if super::env_flag("SQ_HIGH_CARRY_LOAN") {
        circ.release_clean(r.carry);
    }
    Some(Box::new(r))
}

/// Inverse of [`square_b`]: put the in-place sum back, then run the split's own
/// inverse, which is the ordinary one -- a flat node's `low`/`sum` are `None`,
/// so it reduces to two triangular inverses.
fn square_b_inv(
    circ: &mut Builder,
    bs: &[QubitId],
    b2: &[QubitId],
    retained: Option<Box<K2Retained>>,
) {
    match retained {
        None => tri_square(circ, bs, b2, true),
        Some(mut r) => {
            if super::env_flag("SQ_HIGH_CARRY_LOAN") {
                circ.reacquire(r.carry);
            }
            let (a, inner) = bs.split_at(bs.len() / 2);
            let mut t = inner.to_vec();
            t.push(r.carry);
            let keep = go_keep_sum() || super::env_flag("SQ_FLAT_SHARED_CARRIES");
            if keep {
                high_early_reserve(circ, &r);
                // Shift the already-paid cross[1] reconstruction into pristine a,b frame.
                if go_keep_sum() && go_b2() {
                    if high_early_mode() & 1 != 0 {
                        circ.ccx(a[0], inner[0], r.cross[1]);
                    }
                    super::modular::go_given_c0(r.cross[1]);
                }
                r.flat_sum_carries = sum_bank_forward(circ, a, &t);
            } else {
                add_wide(circ, a, &t);
            }
            high_early_trace(circ, bs, &r, "inverse_sum_ready");
            high_early_pair_reserved_skip(circ, bs, &r, true, keep, go_keep_sum() && go_b2());
            high_early_trace(circ, bs, &r, "inverse_cross_ready");
            tri_square_k2r_inv(circ, bs, b2, *r);
        }
    }
}

fn square_half_inv(
    circ: &mut Builder,
    x: &[QubitId],
    product: &[QubitId],
    retained: Option<Box<K2Retained>>,
) {
    match retained {
        Some(r) => tri_square_k2r_inv(circ, x, product, *r),
        None => tri_square(circ, x, product, true),
    }
}

/// Triangular square of `x` into the materialised `product` via the in-place
/// Karatsuba split: `a^2` and `b^2` are built into the two DISJOINT halves of
/// the zeroed product register, and the cross term `2ab = t^2 - a^2 - b^2` is
/// built in the returned scratch and rippled in at shift `lo` with one
/// full-width exact add. That scratch stays live across the consumer's folds,
/// so the inverse never recomputes a sub-square.
///
/// Order matters for the in-place sum: `b^2` is built from the pristine `b`,
/// then `b` becomes `t = a + b` (with the pristine `a`), and only then may `a`
/// be split -- a split leaves its input modified until the inverse.
///
/// Every primitive here is an exact full-width add or subtract, so this adds no
/// truncated comparison, windowed fold or measured chunk boundary — the
/// per-shot failure site count is unchanged in both channels by construction.
fn tri_square_k2r(circ: &mut Builder, x: &[QubitId], product: &[QubitId]) -> K2Retained {
    tri_square_k2r_inner(circ, x, product, false)
}

/// The same node with no recursion under it: `a`, `t` and `b` are all squared
/// triangularly. [`square_b`] builds on this, because its restore is one
/// subtract only while nothing below it has left an in-place sum of its own.
fn tri_square_k2r_flat(circ: &mut Builder, x: &[QubitId], product: &[QubitId]) -> K2Retained {
    tri_square_k2r_inner(circ, x, product, true)
}

/// The exact 2ab cross term has bit0=0. If its wide assembly ladder binds,
/// reuse that zero source bit as the incoming carry to an exact chunk plan.
/// Retain all internal boundary carries and pay their full phase cleanup.
/// No fold/comparison truncation window is changed by this helper.
fn add_cross(
    circ: &mut Builder,
    cross: &[QubitId],
    acc: &[QubitId],
    inverse: bool,
    recover: Option<(super::width_composition::Plan, Vec<(usize, BitId)>)>,
    held: &mut Vec<QubitId>,
    keep: usize,
    xkept: &mut Vec<QubitId>,
) -> Option<(super::width_composition::Plan, Vec<(usize, BitId)>)> {
    // SQ_ASM_TAIL=E: ripple the carry only E bits past the cross word. The
    // bits above hold b^2 and are random, so a carry reaches E bits in with
    // probability about 2^-E. An approximate cut, priced as a sell.
    let full = acc;
    let acc = match super::optional_env::<usize>("SQ_ASM_TAIL") {
        Some(e) => &full[..full.len().min(cross.len() + e)],
        None => full,
    };
    let mut room = super::pingpong::walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
    if inverse && !xkept.is_empty() && recover.is_none() {
        assert!(held.is_empty());
        super::modular::sub_low_kept(circ, cross, acc, std::mem::take(xkept));
        return None;
    }
    if recover.is_some() || (super::env_flag("SQ_FIT_CROSS") && acc.len().saturating_sub(2) > room)
    {
        // SQ_OWN_TOP_ZEROS: this node's own top cross bits are zero for every
        // input (2ab < 2^(lo+hi+1)); add them as zero addend bits and lend them.
        let tops = if super::env_flag("SQ_OWN_TOP_ZEROS") {
            own_top_zero_bits(cross, full)
        } else {
            Vec::new()
        };
        for &q in &tops {
            circ.release_clean(q);
        }
        room += tops.len();
        if inverse {
            circ.x_all(acc);
        }
        let n = acc.len() - 1;
        let proom = if keep > 0 {
            room.saturating_sub(keep)
        } else {
            room
        };
        let (plan, fixes) = recover.unwrap_or_else(|| {
            (
                (proom..=proom.max(n))
                    .find_map(|r| super::width_composition::direct_plan(n, r))
                    .unwrap(),
                Vec::new(),
            )
        });
        if keep > 0 || !xkept.is_empty() {
            eprintln!(
                "BM2_CROSS inverse={} n={} live={} room={} kept={} plan={:?} held={:?} low={:?}",
                inverse,
                acc.len(),
                circ.active_qubits(),
                room,
                keep,
                plan.sizes,
                held.iter().map(|q| q.0).collect::<Vec<_>>(),
                xkept.iter().map(|q| q.0).collect::<Vec<_>>()
            );
        }
        let map: Vec<Vec<QubitId>> = (1..acc.len())
            .map(|i| {
                cross
                    .get(i)
                    .copied()
                    .filter(|q| !tops.contains(q))
                    .into_iter()
                    .collect()
            })
            .collect();
        // SQ_HOLD_BOUNDARY: keep the chunk carry-outs live instead of measuring
        // them. The inverse (forced onto this plan) recreates the same carries
        // and XORs each back to zero, so no boundary phase ever needs repair.
        if !inverse
            && super::env_flag("SQ_HOLD_BOUNDARY")
            && keep > 0
            && plan.sizes.len() >= 2
            && plan.sizes[0] >= 2
        {
            let (h, kk) = super::width_composition::direct_add_hold_keep(
                circ,
                &map,
                &acc[1..],
                cross[0],
                &plan,
                keep.min(plan.sizes[0] - 1),
            );
            *held = h;
            *xkept = kk;
            let hn = held.len();
            held.extend(std::mem::take(xkept));
            rehome_held(circ, held, &tops);
            *xkept = held.split_off(hn);
            return Some((plan, Vec::new()));
        }
        if inverse && !xkept.is_empty() {
            super::width_composition::direct_add_unhold_keep(
                circ,
                &map,
                &acc[1..],
                cross[0],
                &plan,
                std::mem::take(held),
                std::mem::take(xkept),
            );
            circ.x_all(acc);
            for &q in &tops {
                circ.reacquire(q);
            }
            return None;
        }
        if !inverse && super::env_flag("SQ_HOLD_BOUNDARY") {
            *held =
                super::width_composition::direct_add_hold(circ, &map, &acc[1..], cross[0], &plan);
            rehome_held(circ, held, &tops);
            return Some((plan, Vec::new()));
        }
        if inverse && !held.is_empty() {
            super::width_composition::direct_add_unhold(
                circ,
                &map,
                &acc[1..],
                cross[0],
                &plan,
                std::mem::take(held),
            );
            circ.x_all(acc);
            for &q in &tops {
                circ.reacquire(q);
            }
            return None;
        }
        // bit0 of the source is zero, so acc[0] and the first carry stay put.
        let defer = !inverse && super::env_flag("SQ_DEFER_CROSS_PHASE");
        let pending = super::width_composition::direct_add_phase_transport(
            circ,
            &map,
            &acc[1..],
            cross[0],
            &plan,
            defer,
            &fixes,
        );
        if inverse {
            circ.x_all(acc);
        }
        for &q in &tops {
            circ.reacquire(q);
        }
        if super::env_flag("SQ_FIT_CROSS_TRACE") {
            eprintln!(
                "FIT_CROSS {} {} {} {} {}",
                acc.len(),
                room,
                plan.peak,
                plan.extra2,
                inverse as u8
            );
        }
        if defer {
            return Some((plan, pending));
        }
    } else if cut_sqident() {
        if !inverse && keep > 0 {
            *xkept = super::modular::add_low_keep(circ, cross, acc, keep);
        } else {
            addsub_wide_low(circ, cross, acc, inverse, Carry0::Zero, Carry1::Full);
        }
    } else {
        addsub_wide(circ, cross, acc, inverse);
    }
    None
}

/// SQ_OWN_TOP_ZEROS: a node's retained cross holds 2ab in 2*(hi+1) bits, and
/// 2ab < 2^(lo+hi+1): its top bit, and the one below when lo < hi, are zero.
/// `acc` is product[lo..], of length 2m - lo = lo + 2hi.
fn own_top_zero_bits(cross: &[QubitId], acc: &[QubitId]) -> Vec<QubitId> {
    let n = cross.len();
    let hi = n / 2 - 1;
    let lo = acc.len() - 2 * hi;
    assert!(
        n % 2 == 0 && lo <= hi && hi <= lo + 1,
        "own_top_zero_bits: unexpected node shape"
    );
    if lo < hi {
        vec![cross[n - 1], cross[n - 2]]
    } else {
        vec![cross[n - 1]]
    }
}

/// SQ_HOLD_BOUNDARY: a held carry may have been allocated on a wire that is
/// currently lent (assembly loans, own top zeros). Reacquire every other lent
/// wire, then move each such carry to a fresh wire (2 CX) so the lent wire is
/// |0> and live again in its own role. No Toffoli, no measurement.
fn rehome_held(circ: &mut Builder, held: &mut [QubitId], lent: &[QubitId]) {
    for &q in lent {
        if !held.contains(&q) {
            circ.reacquire(q);
        }
    }
    for h in held.iter_mut() {
        if lent.contains(h) {
            let f = circ.alloc_qubit();
            circ.cx(*h, f);
            circ.cx(f, *h);
            *h = f;
        }
    }
}
fn assembly_repay_held(
    circ: &mut Builder,
    x: &[QubitId],
    product: &[QubitId],
    qs: Vec<QubitId>,
    held: &mut [QubitId],
) {
    if held.is_empty() {
        assembly_repay(circ, x, product, qs);
        return;
    }
    if qs.is_empty() {
        return;
    }
    rehome_held(circ, held, &qs);
    circ.cx(x[0], product[0]);
    if row0_copy() {
        circ.x(product[1]);
    }
}

/// The full sum is exactly a+b; removing a restores b and clears its extra
/// top carry for every bitstring, independent of upstream field errors.
fn restore_square_sum(circ: &mut Builder, a: &[QubitId], t: &[QubitId]) {
    if super::env_flag("SQ_ZERO_TOP_SUM") {
        super::modular::addsub_wide_known_top(circ, a, t, true, Carry0::Full, Carry1::Full, false);
    } else {
        sub_wide(circ, a, t);
    }
}

/// Parent cross assembly does not read any child's retained cross scratch,
/// or product bits below the assembly offset. Child low/top bits are zero;
/// product[1] is zero for any square, and product[0] copies the stable x[0].
/// Return the same identities before any child inverse or product consumer.
fn assembly_loans(
    circ: &mut Builder,
    x: &[QubitId],
    product: &[QubitId],
    low: Option<&K2Retained>,
    sum: Option<&K2Retained>,
    high: Option<&K2Retained>,
) -> Vec<QubitId> {
    if !super::env_flag("SQ_LEND_ASSEMBLY_ZEROS") || x.len() / 2 < 2 {
        return Vec::new();
    }
    let lo = x.len() / 2;
    let hi = x.len() - lo;
    let mut qs = vec![product[0], product[1]];
    if let Some(r) = low {
        retained_zero_bits(r, lo, &mut qs);
    }
    if let Some(r) = sum {
        retained_zero_bits(r, hi + 1, &mut qs);
    }
    if let Some(r) = high {
        retained_zero_bits(r, hi, &mut qs);
    }
    circ.cx(x[0], product[0]);
    // SQ_ROW0_COPY: the low half holds a^2 + Na with Na = 2 (mod 4), so
    // product[1] is one rather than zero here.
    if row0_copy() {
        circ.x(product[1]);
    }
    for &q in &qs {
        circ.release_clean(q);
    }
    qs
}
fn assembly_repay(circ: &mut Builder, x: &[QubitId], product: &[QubitId], qs: Vec<QubitId>) {
    if qs.is_empty() {
        return;
    }
    for q in qs {
        circ.reacquire(q);
    }
    circ.cx(x[0], product[0]);
    if row0_copy() {
        circ.x(product[1]);
    }
}

fn tri_square_k2r_inner(
    circ: &mut Builder,
    x: &[QubitId],
    product: &[QubitId],
    flat: bool,
) -> K2Retained {
    let m = x.len();
    assert_eq!(product.len(), 2 * m);
    let lo = m / 2;
    let (a, bs) = x.split_at(lo);
    let (a2, b2) = product.split_at(2 * lo);
    // b^2 straight into the high half of the zeroed product, from the pristine b.
    let high = if flat {
        tri_square(circ, bs, b2, false);
        None
    } else {
        square_b(circ, bs, b2)
    };
    // t = a + b, in place: b's own wires plus one carry.
    let carry = circ.alloc_qubit();
    let mut t = bs.to_vec();
    t.push(carry);
    let k0 = if !flat && go_b1() {
        let q = circ.alloc_qubit();
        super::modular::go_copy_c0(q);
        Some(q)
    } else {
        None
    };
    let flat_sum_carries = if flat && (go_keep_sum() || super::env_flag("SQ_FLAT_SHARED_CARRIES")) {
        sum_bank_forward(circ, a, &t)
    } else {
        add_wide(circ, a, &t);
        Vec::new()
    };
    assert!(super::modular::go_c0_clear());
    // a^2 into the low half; a may now be split since nothing reads it again
    // before the inverse.
    let low = if flat {
        tri_square(circ, a, a2, false);
        None
    } else {
        square_half(circ, a, a2, policy_min(0, sq_split_low_min()))
    };
    // cross = t^2, then subtract the still-pure halves to leave 2ab. Both
    // intermediates are nonnegative (t^2 - a^2 = 2ab + b^2 >= 0), so the
    // two's-complement frame never wraps at this width.
    let cross = circ.alloc_qubits(2 * t.len());
    let sum = if flat {
        tri_square(circ, &t, &cross, false);
        None
    } else {
        square_half(circ, &t, &cross, policy_min(1, sq_split_sum_min()))
    };
    // SQ_ODD_NODE_TOPS: with lo = hi-1, t^2 - a^2 = b(2a+b) < 2^(2hi+1), so the
    // top of the 2(hi+1)-bit cross word is zero after this subtraction.
    let first = if !flat_sum_carries.is_empty() && (go_b2() || super::env_flag("SQ_FLAT_SHARE_C0"))
    {
        assert!(row0_copy());
        Carry0::Known(flat_sum_carries[0])
    } else if let Some(q) = k0 {
        assert!(row0_copy());
        Carry0::Known(q)
    } else {
        Carry0::Full
    };
    let odd_tops = lo < m - lo && super::env_flag("SQ_ODD_NODE_TOPS");
    if odd_tops {
        let c1 = if cut_sqident() {
            Carry1::CopiesCarry0
        } else {
            Carry1::Full
        };
        super::modular::addsub_wide_known_top(circ, a2, &cross, true, first, c1, false);
    } else if cut_sqident() {
        addsub_wide_low(circ, a2, &cross, true, first, Carry1::CopiesCarry0);
    } else {
        addsub_wide_low(circ, a2, &cross, true, first, Carry1::Full);
    }
    // SQ_ROW0_COPY: b2 holds b^2 + Nb with Nb = 2 (mod 4), so its bit 1 is
    // always set. Clearing it subtracts b2 - 2, which keeps the bit-1 carry
    // identity below and adds 2 to this node's cross offset.
    if row0_copy() {
        circ.x(b2[1]);
    }
    if super::env_flag("SQ_ZERO_TOP_CROSS") {
        // 2ab < 2^(lo+hi+1), while cross has 2*(hi+1) bits: its top is zero.
        let (c0, c1) = if cut_sqident() {
            (Carry0::Zero, Carry1::CopiesCarry0)
        } else {
            (Carry0::Full, Carry1::Full)
        };
        super::modular::addsub_wide_known_top(circ, b2, &cross, true, c0, c1, false);
    } else if cut_sqident() {
        addsub_wide_low(circ, b2, &cross, true, Carry0::Zero, Carry1::CopiesCarry0);
    } else {
        sub_wide(circ, b2, &cross);
    }
    if row0_copy() {
        circ.x(b2[1]);
    }
    if let Some(q) = k0 {
        circ.cx(cross[1], q);
        circ.release_clean(q);
    }
    // product += 2ab << lo, exact full ripple to the top (x^2 < 2^(2m), so the
    // top never overflows).
    let loans = assembly_loans(
        circ,
        x,
        product,
        low.as_deref(),
        sum.as_deref(),
        high.as_deref(),
    );
    let mut held = Vec::new();
    let b3 = GO_B3.with(|g| g.get());
    let keep = if b3.0 == m { b3.1 } else { 0 };
    let mut xkept = Vec::new();
    let cross_phase = add_cross(
        circ,
        &cross,
        &product[lo..],
        false,
        None,
        &mut held,
        keep,
        &mut xkept,
    );
    let hn = held.len();
    held.extend(xkept);
    assembly_repay_held(circ, x, product, loans, &mut held);
    let xkept = held.split_off(hn);
    K2Retained {
        carry,
        flat_sum_carries,
        xkept,
        cross,
        low,
        sum,
        high,
        cross_phase,
        held,
    }
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
    let K2Retained {
        carry,
        flat_sum_carries,
        mut xkept,
        cross,
        low,
        sum,
        high,
        cross_phase,
        mut held,
    } = retained;
    let first = if go_b2() {
        assert!(row0_copy());
        Carry0::Known(cross[1])
    } else if !flat_sum_carries.is_empty() && super::env_flag("SQ_FLAT_SHARE_C0") {
        assert!(row0_copy());
        Carry0::Known(flat_sum_carries[0])
    } else {
        Carry0::Full
    };
    let lo = m / 2;
    let (a, bs) = x.split_at(lo);
    let (a2, b2) = product.split_at(2 * lo);
    let mut t = bs.to_vec();
    t.push(carry);
    // product -= 2ab << lo: the halves are pure a^2 / b^2 again.
    let loans = assembly_loans(
        circ,
        x,
        product,
        low.as_deref(),
        sum.as_deref(),
        high.as_deref(),
    );
    assert!(add_cross(
        circ,
        &cross,
        &product[lo..],
        true,
        cross_phase,
        &mut held,
        0,
        &mut xkept
    )
    .is_none());
    assert!(
        held.is_empty(),
        "SQ_HOLD_BOUNDARY: held carries not cleared"
    );
    assembly_repay(circ, x, product, loans);
    let k1 = if flat_sum_carries.is_empty() && go_b1() {
        let q = circ.alloc_qubit();
        circ.cx(cross[1], q);
        Some(q)
    } else {
        None
    };
    // cross: 2ab -> t^2, then clear it with the inverse square (which also
    // restores t if its own split modified it).
    if lo < m - lo && super::env_flag("SQ_ODD_NODE_TOPS") {
        // 2ab + b^2 = b(2a+b) < 2^(2hi+1) when lo = hi-1: zero top after the re-add.
        let (c0, c1) = if cut_sqident() {
            (Carry0::Zero, Carry1::CopiesCarry0)
        } else {
            (Carry0::Full, Carry1::Full)
        };
        if row0_copy() {
            circ.x(b2[1]);
        }
        super::modular::addsub_wide_known_top(circ, b2, &cross, false, c0, c1, false);
        if row0_copy() {
            circ.x(b2[1]);
        }
        if cut_sqident() {
            addsub_wide_low(circ, a2, &cross, false, first, Carry1::CopiesCarry0);
        } else {
            addsub_wide_low(circ, a2, &cross, false, first, Carry1::Full);
        }
    } else if cut_sqident() {
        if row0_copy() {
            circ.x(b2[1]);
        }
        addsub_wide_low(circ, b2, &cross, false, Carry0::Zero, Carry1::CopiesCarry0);
        if row0_copy() {
            circ.x(b2[1]);
        }
        addsub_wide_low(circ, a2, &cross, false, first, Carry1::CopiesCarry0);
    } else {
        if row0_copy() {
            circ.x(b2[1]);
        }
        add_wide(circ, b2, &cross);
        if row0_copy() {
            circ.x(b2[1]);
        }
        addsub_wide_low(circ, a2, &cross, false, first, Carry1::Full);
    }
    square_half_inv(circ, &t, &cross, sum);
    circ.free_vec(&cross);
    // Clear a^2, restoring a first if it was split, then uncompute t = a + b:
    // t - a = b < 2^|b|, so the carry wire returns to |0>.
    square_half_inv(circ, a, a2, low);
    if flat_sum_carries.is_empty() {
        if let Some(q) = k1 {
            super::modular::go_given_c0(q);
            super::modular::go_copy_c0(q);
        }
        restore_square_sum(circ, a, &t);
        if let Some(q) = k1 {
            assert!(super::modular::go_c0_clear());
            circ.release_clean(q);
        }
    } else {
        sum_bank_inverse(circ, a, &t, flat_sum_carries);
    }
    circ.free(carry);
    square_b_inv(circ, bs, b2, high);
}

/// Retained cross terms are exactly 2ab. Their low bit and unused high bit(s)
/// are zero for every input. These wires are not product/consumer operands.
fn retained_zero_bits(r: &K2Retained, m: usize, out: &mut Vec<QubitId>) {
    let lo = m / 2;
    let hi = m - lo;
    let n = r.cross.len();
    out.push(r.cross[0]);
    out.push(r.cross[n - 1]);
    if lo < hi {
        out.push(r.cross[n - 2]);
    }
    if let Some(q) = r.low.as_ref() {
        retained_zero_bits(q, lo, out);
    }
    if let Some(q) = r.sum.as_ref() {
        retained_zero_bits(q, hi + 1, out);
    }
    if let Some(q) = r.high.as_ref() {
        retained_zero_bits(q, hi, out);
    }
}

/// For a node retaining t=a+b in its high input half, bit1 of 2ab is
/// a0*b0 = a0 AND NOT t0. Low/sum children retain this same source frame.
/// A high child was restored and overwritten by its parent's sum; skip it.
fn retained_and_bits(r: &K2Retained, x: &[QubitId], out: &mut Vec<(QubitId, QubitId, QubitId)>) {
    let lo = x.len() / 2;
    out.push((r.cross[1], x[0], x[lo]));
    if let Some(q) = r.low.as_ref() {
        retained_and_bits(q, &x[..lo], out);
    }
    if let Some(q) = r.sum.as_ref() {
        let mut t = x[lo..].to_vec();
        t.push(r.carry);
        retained_and_bits(q, &t, out);
    }
}

/// Consumer-only W61 loan. No high edge: square_b restores that child's
/// source frame, which its parent subsequently overwrites with a sum.
#[derive(Clone, Copy, Debug)]
struct Cross2Loan {
    q: QubitId,
    a0: QubitId,
    a1: QubitId,
    t0: QubitId,
    t1: QubitId,
}
fn retained_cross2_bits(r: &K2Retained, x: &[QubitId], out: &mut Vec<Cross2Loan>) {
    assert!(
        matches!(x.len(), 64 | 65 | 66 | 128 | 129),
        "W61 only proves the production-sized retained frames"
    );
    let lo = x.len() / 2;
    // These allowed shapes and their actual retained children never modify
    // either input half's first two bits. Recurse only through proved frames.
    out.push(Cross2Loan {
        q: r.cross[2],
        a0: x[0],
        a1: x[1],
        t0: x[lo],
        t1: x[lo + 1],
    });
    if let Some(q) = r.low.as_ref() {
        retained_cross2_bits(q, &x[..lo], out);
    }
    if let Some(q) = r.sum.as_ref() {
        let mut t = x[lo..].to_vec();
        t.push(r.carry);
        retained_cross2_bits(q, &t, out);
    }
}
fn cross2_erase(circ: &mut Builder, l: Cross2Loan) {
    // cross[2] = a0*t1 ^ a1*t0 ^ a0*t0 ^ a0, for t=a+b.
    // SQ_ROW0_COPY: bit 2 is flipped (see cross2_restore); unflip it first so
    // the phase repair below stays exact rather than off by (-1)^m.
    if row0_copy() {
        circ.x(l.q);
    }
    let m = circ.alloc_bit();
    circ.hmr(l.q, m);
    circ.cz_if(l.a0, l.t1, m);
    circ.cz_if(l.a1, l.t0, m);
    circ.cz_if(l.a0, l.t0, m);
    circ.z_if(l.a0, m);
    circ.free_bit(m);
}
fn cross2_restore(circ: &mut Builder, l: Cross2Loan) {
    // Two products after an exactly restored Clifford source-frame change.
    circ.cx(l.t0, l.t1);
    circ.x(l.t1);
    circ.ccx(l.a0, l.t1, l.q);
    circ.x(l.t1);
    circ.cx(l.t0, l.t1);
    circ.ccx(l.a1, l.t0, l.q);
    // SQ_ROW0_COPY: every node's cross offset is 4 (mod 8), which flips bit 2
    // and leaves bits 0 and 1 alone. The erase only changes by a global phase.
    if row0_copy() {
        circ.x(l.q);
    }
}

/// Materialise `x^2` in a fresh register, run `folds` against it, then uncompute
/// and release it.
///
/// The shape the whole file is built around: a sub-square is live only for the
/// folds that consume it, and `tri_square_k2r`'s retained scratch makes the
/// uncompute exact rather than a second square. Having the three uses go through
/// here means a fold cannot be added without its inverse, or a register leaked.
fn with_square(
    circ: &mut Builder,
    x: &[QubitId],
    policy_name: &str,
    folds: impl FnOnce(&mut Builder, &[QubitId]),
) {
    let price_branches = super::env_flag("SQ_MODEL_BRANCHES");
    if price_branches {
        circ.set_phase(match policy_name {
            "SQ_A_POLICY" => "square_a",
            "SQ_B_POLICY" => "square_b",
            "SQ_C_POLICY" => "square_c",
            _ => "square_test",
        });
    }
    let old_policy =
        OUTER_SQUARE_POLICY.with(|p| p.replace(super::optional_env::<usize>(policy_name)));
    let product = circ.alloc_qubits(2 * x.len());
    let k = super::optional_env::<usize>(match policy_name {
        "SQ_A_POLICY" => "GO_B3_A",
        "SQ_B_POLICY" => "GO_B3_B",
        "SQ_C_POLICY" => "GO_B3_C",
        _ => "GO_B3_X",
    })
    .unwrap_or(0);
    let old = GO_B3.with(|g| g.replace((x.len(), k)));
    let retained = tri_square_k2r(circ, x, &product);
    GO_B3.with(|g| g.set(old));
    let mut loans = Vec::new();
    if super::env_flag("SQ_LEND_RETAINED_ZEROS") {
        retained_zero_bits(&retained, x.len(), &mut loans);
    }
    let branch = match policy_name {
        "SQ_A_POLICY" => 1,
        "SQ_B_POLICY" => 2,
        "SQ_C_POLICY" => 4,
        _ => 7,
    };
    let and_mask = super::optional_env::<usize>("SQ_LEND_RETAINED_ANDS").unwrap_or(0);
    let mut and_loans = Vec::new();
    if and_mask & branch != 0 {
        retained_and_bits(&retained, x, &mut and_loans);
    }
    let cross2_mask = super::optional_env::<usize>("SQ_LEND_RETAINED_CROSS2").unwrap_or(0);
    assert!(cross2_mask <= 7, "W61 branch mask must be in 0..=7");
    let mut cross2_loans = Vec::new();
    if cross2_mask & branch != 0 {
        retained_cross2_bits(&retained, x, &mut cross2_loans);
    }
    for &(q, a, t) in &and_loans {
        let m = circ.alloc_bit();
        circ.hmr(q, m);
        circ.x(t);
        circ.cz_if(a, t, m);
        circ.x(t);
        circ.free_bit(m);
        loans.push(q);
    }
    // x[0] is unchanged by the in-place Karatsuba sums. Product bit0 equals
    // that bit, so the consumer may read it directly through a source alias.
    let alias = super::env_flag("SQ_ALIAS_PRODUCT_LSB");
    let mut consumer_product = product.clone();
    if alias {
        circ.cx(x[0], product[0]);
        loans.push(product[0]);
        consumer_product[0] = x[0];
    }
    for &l in &cross2_loans {
        cross2_erase(circ, l);
        loans.push(l.q);
    }
    if !cross2_loans.is_empty() {
        let ids: std::collections::HashSet<_> = loans.iter().map(|q| q.0).collect();
        assert_eq!(ids.len(), loans.len(), "W61 duplicate loan target");
        for l in &cross2_loans {
            for q in [l.a0, l.a1, l.t0, l.t1] {
                assert!(!ids.contains(&q.0), "W61 control is being loaned");
            }
        }
    }
    for &q in &loans {
        circ.release_clean(q);
    }
    if super::j_fuse::j_sfuse() || super::j_fuse::j_sfuse_b() || super::native_sfuse_b::mode() > 0 {
        SQ_LOANS.with(|l| *l.borrow_mut() = loans.clone());
    }
    folds(circ, &consumer_product);
    if super::j_fuse::j_sfuse() || super::j_fuse::j_sfuse_b() || super::native_sfuse_b::mode() > 0 {
        SQ_LOANS.with(|l| l.borrow_mut().clear());
    }
    // Every consumer restores its temporary work and source. Reclaim the same
    // physical wire identities before the retained inverse consumes them.
    for &q in &loans {
        circ.reacquire(q);
    }
    for &(q, a, t) in &and_loans {
        circ.x(t);
        circ.ccx(a, t, q);
        circ.x(t);
    }
    for &l in &cross2_loans {
        cross2_restore(circ, l);
    }
    if alias {
        circ.cx(x[0], product[0]);
    }
    tri_square_k2r_inv(circ, x, &product, retained);
    circ.free_vec(&product);
    OUTER_SQUARE_POLICY.with(|p| p.set(old_policy));
    if price_branches {
        circ.set_phase("square_between");
    }
}

/// SQ_ROW0_COPY offsets, mod p, mirroring the split decisions of
/// [`tri_square_k2r_inner`]. A leaf stores `x^2 - 2`. A node stores
/// `x^2 + Na + c 2^lo + Nb 2^(2 lo)`, where its cross holds `2ab + c` with
/// `c = Nt - Na - Nb + 2` (the 2 is the cleared bit 1 of b2).
fn k2r_offset(m: usize, flat: bool) -> U256 {
    let p = super::SECP256K1_P;
    let leaf = p - U256::from(2);
    let lo = m / 2;
    let hi = m - lo;
    let child = |len: usize, min: usize, flat_child: bool| {
        if !flat && len >= min {
            k2r_offset(len, flat_child)
        } else {
            leaf
        }
    };
    let nb = child(hi, policy_min(2, sq_split_b_min()), true);
    let na = child(lo, policy_min(0, sq_split_low_min()), false);
    let nt = child(hi + 1, policy_min(1, sq_split_sum_min()), false);
    let neg = |v: U256| if v.is_zero() { v } else { p - v };
    let c = nt
        .add_mod(neg(na), p)
        .add_mod(neg(nb), p)
        .add_mod(U256::from(2), p);
    let pow = |k: usize| (U256::from(1) << k).reduce_mod(p);
    na.add_mod(c.mul_mod(pow(lo), p), p)
        .add_mod(nb.mul_mod(pow(2 * lo), p), p)
}

fn square_offset(len: usize, policy_name: &str) -> U256 {
    let old = OUTER_SQUARE_POLICY.with(|p| p.replace(super::optional_env::<usize>(policy_name)));
    let n = k2r_offset(len, false);
    OUTER_SQUARE_POLICY.with(|p| p.set(old));
    n
}

/// What [`sub_square`] leaves `out` short by under SQ_ROW0_COPY, mod p: each
/// branch's product offset times that branch's fold weight. The caller adds
/// it back classically. Zero with the knob off.
pub(super) fn sub_square_offset() -> U256 {
    if !row0_copy() {
        return U256::ZERO;
    }
    let p = super::SECP256K1_P;
    let h = N / 2;
    let pow = |k: usize| (U256::from(1) << k).reduce_mod(p);
    let two_n = super::modular::f();
    let na = square_offset(h, "SQ_A_POLICY");
    let nb = square_offset(h, "SQ_B_POLICY");
    let nc = square_offset(h + 1, "SQ_C_POLICY");
    // out -= A (1 - 2^h) + B (2^N - 2^h) + C 2^h.
    let wa = U256::from(1).add_mod(p - pow(h), p);
    let wb = two_n.add_mod(p - pow(h), p);
    na.mul_mod(wa, p)
        .add_mod(nb.mul_mod(wb, p), p)
        .add_mod(nc.mul_mod(pow(h), p), p)
}

thread_local! {
    /// PP_J_SFUSE: the wires `with_square` lent its folds; they come back.
    pub(super) static SQ_LOANS: std::cell::RefCell<Vec<QubitId>> = std::cell::RefCell::new(Vec::new());
}

pub fn sub_square(circ: &mut Builder, out: &[QubitId], y: &[QubitId]) {
    assert_eq!(y.len(), N);
    assert_eq!(out.len(), N);
    let h = N / 2;
    let (y_lo, y_hi) = y.split_at(h);

    // y = a + b*2^h, so y^2 = A + (C - A - B)*2^h + B*2^256 with A = a^2,
    // B = b^2, C = (a+b)^2. Five folds, and this routine subtracts, so every
    // sign below is the negation of that expansion.
    with_square(circ, y_lo, "SQ_A_POLICY", |circ, a2| {
        mod_addsub(circ, true, a2, out);
        fold_shifted(circ, false, a2, out, h);
    });

    if super::j_fuse::j_sfuse_b() || super::native_sfuse_b::mode() > 0 {
        // PP_J_SFUSE_B: C before B, and B's last fold (the 2^32 NAF term, a
        // subtract) fused into the multiply's round-0 lift. B's inverse has
        // room for the four wires the early round 0 leaves standing.
        let sum_carry = circ.alloc_qubit();
        let mut sum = y_hi.to_vec();
        sum.push(sum_carry);
        add_wide(circ, y_lo, &sum);
        with_square(circ, &sum, "SQ_C_POLICY", |circ, c2| {
            fold_rotated(circ, true, &c2[..h], &c2[h..], out);
            window_add(circ, true, &c2[2 * h..], out, h);
        });
        restore_square_sum(circ, y_lo, &sum);
        circ.free(sum_carry);
        with_square(circ, y_hi, "SQ_B_POLICY", |circ, b2| {
            fold_shifted(circ, false, b2, out, h);
            if super::j_fuse::j_wcin_b0last() || super::native_sfuse_b::mode() > 0 {
                if super::j_fuse::j_bmerge() || super::native_sfuse_b::mode() > 0 {
                    b_merged_folds(circ, b2, out);
                } else {
                    for (shift, neg) in F_NAF.into_iter().skip(1) {
                        fold_shifted(circ, true ^ neg, b2, out, shift);
                    }
                }
                if super::native_sfuse_b::mode() > 0 {
                    if super::native_sfuse_b::mode() == 1 {
                        mod_addsub(circ, true, b2, out);
                    } else {
                        super::native_sfuse_b::prepare_native(circ, out, b2);
                    }
                    return;
                }
                let c = super::j_fuse::sub_keep_borrow_q(circ, b2, out);
                let k = super::j_fuse::x_erase_width();
                super::pingpong::j_pre_round0(circ, out, c, &b2[N - k..]);
                return;
            }
            let last = F_NAF.len() - 1;
            for (shift, neg) in F_NAF.into_iter().take(last) {
                fold_shifted(circ, true ^ neg, b2, out, shift);
            }
            let (shift, neg) = F_NAF[last];
            assert!(!neg && shift > 0);
            fold_rotated_sub_r0(circ, &b2[..N - shift], &b2[N - shift..], out, None);
        });
        return;
    }

    with_square(circ, y_hi, "SQ_B_POLICY", |circ, b2| {
        fold_shifted(circ, false, b2, out, h);
        if super::heo::research_on() && std::env::var("CLS_BMERGE_LITE").is_ok_and(|v| v == "1") {
            // CLASSIFIER adapt: PP_J_BMERGE's merged NAF windows without the round-0 fusion; the shift-0
            // subtract stays a plain modular subtract (F_NAF[0] = (0, false), negate = true).
            b_merged_folds(circ, b2, out);
            mod_addsub(circ, true, b2, out);
        } else {
            fold_times_f(circ, true, b2, out);
        }
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
    with_square(circ, &sum, "SQ_C_POLICY", |circ, c2| {
        if super::j_fuse::j_sfuse() {
            fold_rotated_sub_r0(circ, &c2[..h], &c2[h..], out, Some(&c2[2 * h..]));
        } else {
            fold_rotated(circ, true, &c2[..h], &c2[h..], out);
            window_add(circ, true, &c2[2 * h..], out, h);
        }
    });

    restore_square_sum(circ, y_lo, &sum);
    circ.free(sum_carry);
}

// Before row1, only row0 ran. Physical product[j]=x[j]^1^x0 for1<=j<m,
// and all higher bits are zero. In the inverse adder frame, low outputs
// additionally XOR x1 and the top output is1.
fn row1_known_output(x: &[QubitId]) -> Vec<(bool, Vec<QubitId>)> {
    let m = x.len();
    assert!(m >= 3);
    let k = m - 2;
    let mut out: Vec<_> = (0..k)
        .map(|j| {
            if j + 3 < m {
                (true, vec![x[j + 3], x[0], x[1]])
            } else {
                (false, vec![x[1]])
            }
        })
        .collect();
    out.push((true, Vec::new()));
    out
}
pub(super) fn i48_row_fixture(c: &mut Builder, x: &[QubitId], product: &[QubitId]) {
    let m = x.len();
    let row = &product[3..m + 2];
    let out = row1_known_output(x);
    row_addsub_cin(c, x[1], &x[2..], row, true, false, Some(&out), None);
}
pub(super) fn i48_leaf_fixture(c: &mut Builder, x: &[QubitId], product: &[QubitId], inverse: bool) {
    tri_square_cin(c, x, product, inverse);
}

include!("square_high_probe.rs");

fn go_keep_sum() -> bool {
    super::env_flag("GO_KEEP_SUM")
}
fn go_b1() -> bool {
    super::env_flag("GO_B1")
}
fn go_b2() -> bool {
    super::env_flag("GO_B2")
}
thread_local! {static GO_B3:std::cell::Cell<(usize,usize)>=const{std::cell::Cell::new((0,0))};}
fn sum_bank_forward(c: &mut Builder, a: &[QubitId], t: &[QubitId]) -> Vec<QubitId> {
    if go_keep_sum() {
        super::modular::add_wide_keep(c, a, t)
    } else {
        super::modular::shared_carry_forward(c, a, t, false)
    }
}
fn sum_bank_inverse(c: &mut Builder, a: &[QubitId], t: &[QubitId], bank: Vec<QubitId>) {
    if go_keep_sum() {
        super::modular::sub_wide_kept(c, a, t, bank)
    } else {
        super::modular::shared_carry_inverse(c, a, t, false, bank)
    }
}

// Native port of upstream454ff5a. high10=16u+v implies correction<=975.
fn skywalk_merged_high_stream(
    circ: &mut Builder,
    high: &[QubitId],
    consume: impl FnOnce(&mut Builder, &[QubitId]),
) {
    assert_eq!(high.len(), 32);
    let hi = |n: usize| &high[32 - n..];
    let small = circ.alloc_qubits(10);
    for i in 0..10 {
        circ.cx(hi(10)[i], small[i]);
    }
    addsub_wide(circ, hi(6), &small, true);
    let c4 = if std::env::var_os("SKYWALK_MERGED_HIGH_RETAIN4").is_some() {
        Some(super::modular::shared_carry_forward(
            circ,
            hi(4),
            &small,
            false,
        ))
    } else {
        addsub_wide(circ, hi(4), &small, false);
        None
    };
    let r = circ.alloc_qubits(33);
    for i in 0..32 {
        circ.cx(high[i], r[i]);
    }
    addsub_wide(circ, &small, &r, false);
    consume(circ, &r);
    let mut restored: Vec<_> = high.iter().map(|&q| (true, vec![q])).collect();
    restored.push((true, Vec::new()));
    circ.x_all(&r);
    super::stream_wide::add(circ, &small, &r, None, &restored);
    circ.x_all(&r);
    for i in 0..32 {
        circ.cx(high[i], r[i]);
    }
    circ.free_vec(&r);
    if let Some(cs) = c4 {
        super::modular::shared_carry_inverse(circ, hi(4), &small, false, cs);
    } else {
        addsub_wide(circ, hi(4), &small, true);
    }
    let restored_small: Vec<_> = hi(10).iter().map(|&q| (false, vec![q])).collect();
    super::stream_wide::add(circ, hi(6), &small, None, &restored_small);
    for i in 0..10 {
        circ.cx(hi(10)[i], small[i]);
    }
    circ.free_vec(&small);
}
