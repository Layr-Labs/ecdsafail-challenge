//! Dormant product-register Karatsuba square port.
//!
//! The source construction accumulates three half-width triangular squares in
//! plain product registers, then reduces five times.  This target translation
//! deliberately reuses the legacy builder's clean add, fold, comparator, and
//! measurement-based erasure primitives.

use super::super::{arith, comparator, B, BExt};
use crate::circuit::{OperationType, QubitId, QubitOrBit};

const N: usize = 256;
const LSBS: usize = 56;
const MSBS: usize = 24;
const GUARD: usize = 24;
const F_NAF: [(usize, bool); 5] = [
    (0, false),
    (4, false),
    (6, true),
    (10, false),
    (32, false),
];

/// The Karatsuba sum now lives in the input high half instead of a separate
/// 129-qubit register. The resulting liveness margin lets every square add use
/// its exact full-width ladder below the replay peak.
const SQUARE_CHUNK_MIN: usize = usize::MAX;
/// Retain the current public frontier's ladder budget when an explicit
/// environment override requests the chunked diagnostic path.
const SQUARE_LADDER: usize = 243;
fn add_full(circ: &mut B, addend: &[QubitId], acc: &[QubitId]) {
    assert_eq!(addend.len(), acc.len());
    let chunk_min = std::env::var("SUB4_SQUARE_CHUNK_MIN")
        .ok()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(SQUARE_CHUNK_MIN);
    if acc.len() >= chunk_min {
        // The square's own footprint sits ~160 qubits below the replay peak, so
        // it can afford a much wider carry ladder than the replay can - and a
        // wider ladder means fewer chunks, i.e. fewer measured boundary
        // repairs.  Budget it explicitly instead of inheriting the replay's
        // chunk width.
        let budget = std::env::var("SUB4_SQUARE_LADDER")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(SQUARE_LADDER);
        if budget == 0 {
            crate::point_add::pingpong_div::add_chunked_measured(circ, addend, acc, None);
        } else {
            crate::point_add::pingpong_div::add_chunked_measured_budgeted(
                circ, addend, acc, None, budget,
            );
        }
        return;
    }
    arith::hybrid_add_adaptive(circ, acc, addend, usize::MAX);
}

fn sub_full(circ: &mut B, addend: &[QubitId], acc: &[QubitId]) {
    for &q in acc {
        circ.x(q);
    }
    add_full(circ, addend, acc);
    for &q in acc {
        circ.x(q);
    }
}

fn row_addsub(
    circ: &mut B,
    ctrl: QubitId,
    operand: &[QubitId],
    acc: &[QubitId],
    inverse: bool,
) {
    let k = operand.len();
    assert_eq!(acc.len(), k + 1);
    let pad = circ.alloc_qubit();
    let mut operand_wide = operand.to_vec();
    operand_wide.push(pad);
    if inverse {
        circ.cx(ctrl, acc[k]);
        for &q in &acc[..k] {
            circ.cx(ctrl, q);
        }
        sub_full(circ, &operand_wide, acc);
        for &q in &acc[..k] {
            circ.cx(ctrl, q);
        }
    } else {
        for &q in &acc[..k] {
            circ.cx(ctrl, q);
        }
        add_full(circ, &operand_wide, acc);
        for &q in &acc[..k] {
            circ.cx(ctrl, q);
        }
        circ.cx(ctrl, acc[k]);
    }
    circ.zero_and_free(pad);
}

fn tri_square(circ: &mut B, x: &[QubitId], product: &[QubitId], inverse: bool) {
    let m = x.len();
    assert_eq!(product.len(), 2 * m);
    if m == 0 {
        return;
    }
    if inverse {
        tri_corr(circ, x, product, true);
        for i in (0..m.saturating_sub(1)).rev() {
            let k = m - 1 - i;
            circ.x(x[i]);
            row_addsub(
                circ,
                x[i],
                &x[i + 1..],
                &product[2 * i + 1..2 * i + 2 + k],
                true,
            );
            circ.x(x[i]);
        }
    } else {
        for i in 0..m.saturating_sub(1) {
            let k = m - 1 - i;
            circ.x(x[i]);
            row_addsub(
                circ,
                x[i],
                &x[i + 1..],
                &product[2 * i + 1..2 * i + 2 + k],
                false,
            );
            circ.x(x[i]);
        }
        tri_corr(circ, x, product, false);
    }
}

fn tri_corr(circ: &mut B, x: &[QubitId], product: &[QubitId], inverse: bool) {
    let m = x.len();
    let spread = |circ: &mut B| {
        let pads = circ.alloc_qubits(m);
        let mut value = Vec::with_capacity(2 * m);
        for i in 0..m {
            value.push(pads[i]);
            value.push(x[i]);
        }
        (value, pads)
    };
    let correction = |circ: &mut B| {
        // The prior form subtracted x across the full product and then
        // subtracted ~(x mod 2^(m-1)) from the high half. Those operands occupy
        // disjoint bit ranges, so concatenate them and use one full-width
        // subtraction. Copying and complementing the high half is Clifford;
        // this removes one (m-1)-Toffoli carry ladder per correction.
        let pads = circ.alloc_qubits(m);
        for i in 0..m - 1 {
            circ.cx(x[i], pads[i]);
            circ.x(pads[i]);
        }
        let mut value = x.to_vec();
        value.extend_from_slice(&pads);
        (value, pads)
    };
    let clear_correction = |circ: &mut B, pads: &[QubitId]| {
        for i in 0..m - 1 {
            circ.x(pads[i]);
            circ.cx(x[i], pads[i]);
        }
    };

    if !inverse {
        let (value, pads) = spread(circ);
        add_full(circ, &value, product);
        circ.free_vec(&pads);
        let (value, pads) = correction(circ);
        sub_full(circ, &value, product);
        clear_correction(circ, &pads);
        circ.free_vec(&pads);
    } else {
        let (value, pads) = correction(circ);
        add_full(circ, &value, product);
        clear_correction(circ, &pads);
        circ.free_vec(&pads);
        let (value, pads) = spread(circ);
        sub_full(circ, &value, product);
        circ.free_vec(&pads);
    }
}

fn clear_overflow_phase(circ: &mut B, overflow: QubitId, acc: &[QubitId], addend: &[QubitId]) {
    let bit = circ.alloc_bit();
    circ.hmr(overflow, bit);
    circ.push_condition(bit);
    let c_in = circ.alloc_qubit();
    comparator::compare_geq_cin_middle(
        circ,
        &acc[acc.len() - MSBS..],
        &addend[addend.len() - MSBS..],
        &c_in,
        |c, a, b, carry_in| {
            // The omitted final carry is carry_in ^ (a & b) in this frame.
            // Correct the phase of its complement directly with Cliffords.
            c.neg();
            c.z(*carry_in);
            c.cz(*a, *b);
        },
    );
    circ.zero_and_free(c_in);
    circ.pop_condition();
}

fn mod_add_top(
    circ: &mut B,
    sign: QubitId,
    value: &[QubitId],
    out: &[QubitId],
    overflow: QubitId,
    shift: usize,
) {
    assert_eq!(shift + value.len(), out.len());
    for &q in out {
        circ.cx(sign, q);
    }
    let pad = circ.alloc_qubit();
    let mut value_wide = value.to_vec();
    value_wide.push(pad);
    let mut acc_wide = out[shift..].to_vec();
    acc_wide.push(overflow);
    add_full(circ, &value_wide, &acc_wide);
    circ.zero_and_free(pad);

    let f = arith::F_SECP256K1.to_le_bytes();
    arith::add_f_window_pub(circ, &overflow, out, LSBS, &f, Some(LSBS));
    clear_overflow_phase(circ, overflow, out, value);
    for &q in out {
        circ.cx(sign, q);
    }
}

fn window_add(circ: &mut B, sign: QubitId, value: &[QubitId], out: &[QubitId], shift: usize) {
    let top = shift + value.len() + GUARD;
    assert!(top <= out.len());
    let acc = &out[shift..top];
    let pads = circ.alloc_qubits(GUARD);
    let mut value_wide = value.to_vec();
    value_wide.extend_from_slice(&pads);
    for &q in acc {
        circ.cx(sign, q);
    }
    add_full(circ, &value_wide, acc);
    for &q in acc {
        circ.cx(sign, q);
    }
    circ.free_vec(&pads);
}

fn apply_f(circ: &mut B, sign: QubitId, value: &[QubitId], out: &[QubitId]) {
    for (shift, negate) in F_NAF {
        if negate {
            circ.x(sign);
        }
        window_add(circ, sign, value, out, shift);
        if negate {
            circ.x(sign);
        }
    }
}

fn apply_f_without_unit(
    circ: &mut B,
    sign: QubitId,
    value: &[QubitId],
    out: &[QubitId],
) {
    for (shift, negate) in F_NAF.into_iter().skip(1) {
        if negate {
            circ.x(sign);
        }
        window_add(circ, sign, value, out, shift);
        if negate {
            circ.x(sign);
        }
    }
}

/// Add `value * 2^shift (mod p)` for a full-width value. Since
/// `2^N = f (mod p)`, the wrapped high limb contributes `f * high`.
/// Rotating that limb into the vacated low positions folds its unit term into
/// the main modular add. The remaining NAF terms contribute `(f - 1) * high`.
fn apply_shifted_full_term(
    circ: &mut B,
    sign: QubitId,
    value: &[QubitId],
    out: &[QubitId],
    overflow: QubitId,
    shift: usize,
) {
    assert_eq!(value.len(), N);
    assert!(shift < N);
    if shift == 0 {
        mod_add_top(circ, sign, value, out, overflow, 0);
        return;
    }

    let split = N - shift;
    let high = &value[split..];
    let mut rotated = Vec::with_capacity(N);
    rotated.extend_from_slice(high);
    rotated.extend_from_slice(&value[..split]);
    mod_add_top(circ, sign, &rotated, out, overflow, 0);
    apply_f_without_unit(circ, sign, high, out);
}

fn apply_shift_half(
    circ: &mut B,
    sign: QubitId,
    product: &[QubitId],
    out: &[QubitId],
    overflow: QubitId,
) {
    let h = out.len() / 2;
    if product.len() == out.len() {
        apply_shifted_full_term(circ, sign, product, out, overflow, h);
    } else if product.len() == out.len() + 2 {
        // The Karatsuba cross-square has two extra high bits. Rotate the low
        // half of its high limb into the full-width add, then add the two
        // overlapping bits separately. This keeps the same carry lengths and
        // removes the 128 sign-copy pairs from the unit fold.
        let high = &product[h..];
        let mut rotated = Vec::with_capacity(N);
        rotated.extend_from_slice(&high[..h]);
        rotated.extend_from_slice(&product[..h]);
        mod_add_top(circ, sign, &rotated, out, overflow, 0);
        apply_f_without_unit(circ, sign, high, out);
        window_add(circ, sign, &high[h..], out, h);
    } else {
        mod_add_top(circ, sign, &product[..h], out, overflow, h);
        if product.len() > h {
            apply_f(circ, sign, &product[h..], out);
        }
    }
}

fn apply_shift_full(
    circ: &mut B,
    sign: QubitId,
    product: &[QubitId],
    out: &[QubitId],
    overflow: QubitId,
) {
    assert_eq!(product.len(), out.len());
    for (shift, negate) in F_NAF {
        if negate {
            circ.x(sign);
        }
        apply_shifted_full_term(circ, sign, product, out, overflow, shift);
        if negate {
            circ.x(sign);
        }
    }
}

pub(super) fn square_sub(circ: &mut B, y: &[QubitId], out: &[QubitId]) {
    assert_eq!(y.len(), N);
    assert_eq!(out.len(), N);
    let h = N / 2;
    let sign = circ.alloc_qubit();
    let overflow = circ.alloc_qubit();
    circ.x(sign);

    let product_a = circ.alloc_qubits(2 * h);
    tri_square(circ, &y[..h], &product_a, false);
    mod_add_top(circ, sign, &product_a, out, overflow, 0);
    circ.x(sign);
    apply_shift_half(circ, sign, &product_a, out, overflow);
    circ.x(sign);
    tri_square(circ, &y[..h], &product_a, true);
    circ.free_vec(&product_a);

    let product_b = circ.alloc_qubits(2 * h);
    tri_square(circ, &y[h..], &product_b, false);
    circ.x(sign);
    apply_shift_half(circ, sign, &product_b, out, overflow);
    circ.x(sign);
    apply_shift_full(circ, sign, &product_b, out, overflow);
    tri_square(circ, &y[h..], &product_b, true);
    circ.free_vec(&product_b);

    // Hold a+b in the input's high half plus one carry wire. The original high
    // half is restored immediately after the cross-term square. This removes a
    // separate 129-qubit live register while preserving the exact Karatsuba
    // identity and the caller's input register.
    let sum_carry = circ.alloc_qubit();
    let mut sum = y[h..].to_vec();
    sum.push(sum_carry);
    let pad = circ.alloc_qubit();
    let mut lo_wide = y[..h].to_vec();
    lo_wide.push(pad);
    add_full(circ, &lo_wide, &sum);
    circ.zero_and_free(pad);

    let product_c = circ.alloc_qubits(2 * (h + 1));
    tri_square(circ, &sum, &product_c, false);
    apply_shift_half(circ, sign, &product_c, out, overflow);
    tri_square(circ, &sum, &product_c, true);
    circ.free_vec(&product_c);

    let pad = circ.alloc_qubit();
    let mut lo_wide = y[..h].to_vec();
    lo_wide.push(pad);
    sub_full(circ, &lo_wide, &sum);
    circ.zero_and_free(pad);
    circ.zero_and_free(sum_carry);
    circ.x(sign);
    circ.zero_and_free(sign);
    circ.zero_and_free(overflow);
}

pub(super) fn selfcheck() {
    use crate::point_add::SECP256K1_P;
    use crate::sim::Simulator;
    use alloy_primitives::U256;
    use sha3::{
        digest::{ExtendableOutput, Update, XofReader},
        Shake256,
    };

    let mut circ = B::new();
    let source = circ.alloc_qubits(N);
    let accumulator = circ.alloc_qubits(N);
    square_sub(&mut circ, &source, &accumulator);
    let num_qubits = circ.next_qubit as usize;
    let num_bits = circ.next_bit as usize;
    let peak_qubits = circ.peak_qubits;
    let ops = circ.take_ops();

    let mut input_seed = Shake256::default();
    input_seed.update(b"product-register-square-inputs");
    let mut input_reader = input_seed.finalize_xof();
    let mut sources = [U256::ZERO; 64];
    let mut accumulators = [U256::ZERO; 64];
    let mut expected = [U256::ZERO; 64];
    let mut bytes = [0u8; 32];
    for shot in 0..64 {
        input_reader.read(&mut bytes);
        sources[shot] = U256::from_le_bytes(bytes) % SECP256K1_P;
        input_reader.read(&mut bytes);
        accumulators[shot] = U256::from_le_bytes(bytes) % SECP256K1_P;
        let square = sources[shot].mul_mod(sources[shot], SECP256K1_P);
        expected[shot] = if accumulators[shot] >= square {
            accumulators[shot] - square
        } else {
            SECP256K1_P - (square - accumulators[shot])
        };
    }

    let mut sim_seed = Shake256::default();
    sim_seed.update(b"product-register-square-simulator");
    let mut sim_reader = sim_seed.finalize_xof();
    let mut sim = Simulator::new(num_qubits, num_bits, &mut sim_reader);
    let source_reg: Vec<QubitOrBit> = source.iter().copied().map(QubitOrBit::Qubit).collect();
    let accumulator_reg: Vec<QubitOrBit> = accumulator
        .iter()
        .copied()
        .map(QubitOrBit::Qubit)
        .collect();
    for shot in 0..64 {
        sim.set_register(&source_reg, sources[shot], shot);
        sim.set_register(&accumulator_reg, accumulators[shot], shot);
    }
    sim.apply_iter(ops.iter());

    for shot in 0..64 {
        assert_eq!(sim.get_register(&source_reg, shot), sources[shot]);
        assert_eq!(sim.get_register(&accumulator_reg, shot), expected[shot]);
    }
    assert_eq!(sim.phase, 0, "phase garbage in product-register square");
    for q in 0..num_qubits as u64 {
        let q = QubitId(q);
        if source.contains(&q) || accumulator.contains(&q) {
            continue;
        }
        assert_eq!(sim.qubit(q), 0, "dirty product-square ancilla {q:?}");
    }

    let emitted = ops
        .iter()
        .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
        .count();
    let executed = sim.stats.toffoli_gates as f64 / 64.0;
    eprintln!(
        "product-register square: {emitted} emitted / {executed:.3} executed Toffoli, {peak_qubits} peak qubits"
    );
}
