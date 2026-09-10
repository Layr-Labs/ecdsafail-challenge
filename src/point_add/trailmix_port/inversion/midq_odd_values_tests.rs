//! Exhaustive small-width differential channel tests. Intentionally not run by
//! this change. Dirty signed-resize resets are compared, not assumed clean.

use super::super::{
    midq_loan_odd_low_bits, midq_restore_odd_low_bits, midq_signed_resize,
    midq_value_round_backward, midq_value_round_forward, midq_value_round_forward_with_sign,
    midq_value_vents, MIDQ_TAIL_VALUE_WIDTH,
};
use super::*;
use crate::circuit::{analyze_ops, Op, OperationType as K, QubitId, NO_BIT};
use crate::sim::Simulator;
use sha3::digest::XofReader;

fn ids(reg: &[QReg]) -> Vec<QubitId> {
    reg.iter().map(|q| QubitId(q.id().into())).collect()
}

fn simulator_capacity(c: &Circuit) -> (usize, usize) {
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    // Untouched inputs/spectators need storage too. Allocator high-water marks
    // cover every initial, intermediate, and final ID, including freed IDs.
    (
        (nq as usize).max(c.b.next_qubit as usize),
        (nb as usize).max(c.b.next_bit as usize),
    )
}

fn signed(value: i128, width: usize) -> i128 {
    assert!((1..128).contains(&width));
    (value << (128 - width)) >> (128 - width)
}

// Separate full-width reference with an explicit vent budget. The production
// reference mode below additionally exercises the actual unmodified parent.
fn full_forward(
    c: &mut Circuit,
    source: &mut Vec<QReg>,
    target: &mut Vec<QReg>,
    sign: &QReg,
    next: usize,
    vents: usize,
    supplied: bool,
) {
    if !supplied {
        c.cx(&target[1], sign);
        c.cx(&source[1], sign);
    }
    for q in target.iter() {
        c.cx(sign, q);
    }
    hybrid_add_refs(
        c,
        &target.iter().collect::<Vec<_>>(),
        &source.iter().collect::<Vec<_>>(),
        vents,
    );
    for q in target.iter() {
        c.cx(sign, q);
    }
    let low = target.remove(0);
    c.zero_and_free(low);
    midq_signed_resize(c, target, next, "reference.target");
    midq_signed_resize(c, source, next, "reference.source");
}

fn full_backward(
    c: &mut Circuit,
    source: &mut Vec<QReg>,
    target: &mut Vec<QReg>,
    sign: QReg,
    old: usize,
    vents: usize,
) {
    midq_signed_resize(c, source, old, "reference.source");
    midq_signed_resize(c, target, old - 1, "reference.target");
    target.insert(0, c.alloc_qreg("reference.low"));
    c.x(&sign);
    for q in target.iter() {
        c.cx(&sign, q);
    }
    hybrid_add_refs(
        c,
        &target.iter().collect::<Vec<_>>(),
        &source.iter().collect::<Vec<_>>(),
        vents,
    );
    for q in target.iter() {
        c.cx(&sign, q);
    }
    c.x(&sign);
    c.cx(&source[1], &sign);
    c.cx(&target[1], &sign);
    c.zero_and_free(sign);
}

#[derive(Clone, Copy)]
enum Mode {
    Roundtrip,
    Supplied,
    BackwardOnly,
}

struct Stage {
    start: usize,
    end: usize,
    inverse: bool,
    target: usize,
    width: usize,
    output_width: usize,
    // Indices of just the signed-shrink resets, in semantic execution order.
    resets: Vec<usize>,
    rows: [Vec<QubitId>; 2],
    tape: Vec<QubitId>,
}

struct Built {
    ops: Vec<Op>,
    initial: [Vec<QubitId>; 2],
    initial_sign: Option<QubitId>,
    odd: bool,
    stages: Vec<Stage>,
    peak: u64,
    nq: usize,
    nb: usize,
}

fn build(widths: &[usize], odd: bool, vents: usize, production: bool, mode: Mode) -> Built {
    assert!(widths.len() >= 2 && widths.iter().all(|&w| (3..128).contains(&w)));
    assert!(!production || !odd);
    if matches!(mode, Mode::BackwardOnly | Mode::Supplied) {
        assert_eq!(widths.len(), 2);
    }
    let mut c = Circuit::new();
    let mut a = c.alloc_qreg_bits("a", widths[0] - usize::from(odd));
    let mut b = c.alloc_qreg_bits("b", widths[0] - usize::from(odd));
    let initial = [ids(&a), ids(&b)];
    let mut tape = Vec::new();
    let initial_sign = if matches!(mode, Mode::Supplied | Mode::BackwardOnly) {
        let sign = c.alloc_qreg("input.sign");
        let id = QubitId(sign.id().into());
        tape.push(sign);
        Some(id)
    } else {
        None
    };
    let mut plan = Vec::new();
    if matches!(mode, Mode::BackwardOnly) {
        plan.push((true, 1, widths[0], widths[1]));
    } else {
        for r in 0..widths.len() - 1 {
            plan.push((false, 1 - r % 2, widths[r], widths[r + 1]));
        }
        for r in (0..widths.len() - 1).rev() {
            plan.push((true, 1 - r % 2, widths[r + 1], widths[r]));
        }
    }
    let mut stages = Vec::new();
    let mut last_forward_width = [None; 2];
    for (inverse, target_index, width, output_width) in plan {
        let (source, target) = if target_index == 1 {
            (&mut a, &mut b)
        } else {
            (&mut b, &mut a)
        };
        let start = c.b.ops.len();
        if inverse {
            let sign = tape.pop().unwrap();
            if odd {
                if padding_enabled() && width == output_width {
                    prepare_backward_target(&mut c, target, output_width);
                }
                backward(&mut c, source, target, sign, output_width, vents);
            } else if production {
                midq_value_round_backward(&mut c, source, target, sign, output_width);
            } else {
                full_backward(&mut c, source, target, sign, output_width, vents);
            }
        } else {
            let supplied = matches!(mode, Mode::Supplied);
            let sign = if supplied {
                tape.pop().unwrap()
            } else {
                c.alloc_qreg("sign")
            };
            if odd {
                if supplied {
                    forward_with_sign(&mut c, source, target, &sign, output_width, vents);
                } else {
                    forward(&mut c, source, target, &sign, output_width, vents);
                }
            } else if production {
                if supplied {
                    midq_value_round_forward_with_sign(&mut c, source, target, &sign, output_width);
                } else {
                    midq_value_round_forward(&mut c, source, target, &sign, output_width);
                }
            } else {
                full_forward(&mut c, source, target, &sign, output_width, vents, supplied);
            }
            if odd && padding_enabled() {
                with_forward_padding(&mut c, source, target, width, output_width,
                    last_forward_width[1 - target_index], |_| {});
            }
            last_forward_width[target_index] = Some(width);
            tape.push(sign);
        }
        let end = c.b.ops.len();
        let count = if inverse {
            width.saturating_sub(output_width) + width.saturating_sub(output_width - 1)
        } else {
            width.saturating_sub(output_width) + (width - 1).saturating_sub(output_width)
        };
        let all_resets: Vec<usize> = (start..end).filter(|&i| c.b.ops[i].kind == K::R).collect();
        assert!(all_resets.len() >= count);
        // Backward shrinks before its adder; forward shrinks after its adder
        // and low-bit discharge. This excludes all clean vent and low resets.
        let resets = if inverse {
            all_resets[..count].to_vec()
        } else {
            all_resets[all_resets.len() - count..].to_vec()
        };
        for &i in &resets {
            assert_eq!(c.b.ops[i - 1].kind, K::CX);
            assert_eq!(c.b.ops[i - 1].q_target, c.b.ops[i].q_target);
        }
        let add_width = (if inverse { output_width } else { width }) - usize::from(odd);
        let actual_t = c.b.ops[start..end]
            .iter()
            .filter(|op| matches!(op.kind, K::CCX | K::CCZ))
            .count();
        assert_eq!(actual_t, 2 * (add_width - 1) - vents.min(add_width - 1));
        stages.push(Stage {
            start,
            end,
            inverse,
            target: target_index,
            width,
            output_width,
            resets,
            rows: [ids(&a), ids(&b)],
            tape: ids(&tape),
        });
    }
    let (nq, nb) = simulator_capacity(&c);
    Built {
        initial,
        initial_sign,
        odd,
        stages,
        peak: c.b.peak_qubits as u64,
        nq,
        nb,
        ops: c.b.ops.clone(),
    }
}

fn resize_model(value: i128, from: usize, to: usize, resets: &mut Vec<bool>) -> i128 {
    for high in (to..from).rev() {
        resets.push(((value >> high) ^ (value >> (high - 1))) & 1 != 0);
    }
    signed(value, to)
}

#[derive(Clone)]
struct Case {
    pair: [i128; 2],
    tape: Vec<bool>,
}

fn step_model(case: &mut Case, stage: &Stage, supplied: bool) -> Vec<bool> {
    let mut resets = Vec::new();
    let t = stage.target;
    let s = 1 - t;
    let w = stage.width;
    let n = stage.output_width;
    if stage.inverse {
        let sign = case.tape.pop().unwrap();
        case.pair[s] = resize_model(case.pair[s], w, n, &mut resets);
        case.pair[t] = resize_model(case.pair[t], w, n - 1, &mut resets);
        case.pair[t] = signed(
            2 * case.pair[t] + if sign { case.pair[s] } else { -case.pair[s] },
            n,
        );
        assert_eq!(((case.pair[s] ^ case.pair[t]) >> 1) & 1 != 0, sign);
    } else {
        let sign = ((case.pair[s] ^ case.pair[t]) >> 1) & 1 != 0;
        if supplied {
            assert_eq!(case.tape.last().copied(), Some(sign));
        } else {
            case.tape.push(sign);
        }
        let sum = case.pair[t] + if sign { -case.pair[s] } else { case.pair[s] };
        let half = signed(sum, w) >> 1;
        case.pair[t] = resize_model(half, w - 1, n, &mut resets);
        case.pair[s] = resize_model(case.pair[s], w, n, &mut resets);
    }
    assert!(case.pair.iter().all(|v| v & 1 == 1));
    resets
}

struct Word(u64);
impl XofReader for Word {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8);
        out.copy_from_slice(&self.0.to_le_bytes());
    }
}

fn measurement(mode: usize, index: usize) -> u64 {
    match mode {
        0 => 0,
        1 => u64::MAX,
        2 => 0x55aa_33cc_f00f_9696u64.rotate_left(index as u32),
        _ => {
            let mut x = (index as u64).wrapping_add(0x9e37_79b9_7f4a_7c15);
            x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            x ^ (x >> 31)
        }
    }
}

fn write(sim: &mut Simulator<Word>, reg: &[QubitId], lane: usize, value: i128) {
    for (bit, &q) in reg.iter().enumerate() {
        *sim.qubit_mut(q) |= (((value >> bit) & 1) as u64) << lane;
    }
}

fn read(sim: &Simulator<Word>, reg: &[QubitId], lane: usize) -> i128 {
    reg.iter().enumerate().fold(0, |v, (i, &q)| {
        v | (((sim.qubit(q) >> lane) & 1) as i128) << i
    })
}

// R outcomes are keyed by semantic discarded-bit index, NOT physical ID or
// PRNG position. HMR outcomes can differ completely: their fixups must cancel.
fn check(built: &Built, inputs: &[Case], mode: usize, hmr_tape: Option<usize>) -> usize {
    let mut dirty = 0;
    for batch in inputs.chunks(64) {
        let mask = u64::MAX >> (64 - batch.len());
        let mut word = Word(0);
        let mut sim = Simulator::new(built.nq, built.nb, &mut word);
        let mut cases = batch.to_vec();
        let mut phase = 0xc391_275a_0fe6_b84d & mask;
        sim.phase = phase;
        for (lane, case) in cases.iter().enumerate() {
            for row in 0..2 {
                write(
                    &mut sim,
                    &built.initial[row],
                    lane,
                    if built.odd {
                        case.pair[row] >> 1
                    } else {
                        case.pair[row]
                    },
                );
            }
            if let Some(q) = built.initial_sign {
                write(&mut sim, &[q], lane, i128::from(case.tape[0]));
            }
        }
        let mut reset_index = 0;
        let mut hmr_index = 0;
        let mut dirty_support = 0u64;
        for (stage_index, stage) in built.stages.iter().enumerate() {
            let supplied = stage_index == 0 && built.initial_sign.is_some() && !stage.inverse;
            let deltas: Vec<Vec<bool>> = cases
                .iter_mut()
                .map(|case| step_model(case, stage, supplied))
                .collect();
            assert!(deltas.iter().all(|d| d.len() == stage.resets.len()));
            for i in stage.start..stage.end {
                let op = &built.ops[i];
                op.validate();
                assert!(!matches!(op.kind, K::PushCondition | K::PopCondition));
                if op.kind == K::R {
                    assert_eq!(op.c_condition, NO_BIT);
                    if let Some(j) = stage.resets.iter().position(|&r| r == i) {
                        let expected = deltas
                            .iter()
                            .enumerate()
                            .fold(0, |v, (lane, d)| v | (u64::from(d[j]) << lane));
                        assert_eq!(
                            sim.qubit(op.q_target) & mask,
                            expected,
                            "pre-reset delta stage={stage_index} op={i} odd={}",
                            built.odd
                        );
                        dirty += expected.count_ones() as usize;
                        dirty_support |= expected;
                        sim.xof.0 = measurement(mode, reset_index);
                        reset_index += 1;
                        phase ^= expected & sim.xof.0;
                    } else {
                        assert_eq!(
                            sim.qubit(op.q_target) & mask,
                            0,
                            "new dirty reset stage={stage_index} op={i} odd={}",
                            built.odd
                        );
                        sim.xof.0 = measurement(mode, i + 1000);
                    }
                } else if op.kind == K::Hmr {
                    sim.xof.0 = if let Some(tape) = hmr_tape {
                        assert!(hmr_index < usize::BITS as usize);
                        if (tape >> hmr_index) & 1 == 1 {
                            u64::MAX
                        } else {
                            0
                        }
                    } else {
                        measurement(mode, hmr_index + 100_000)
                    };
                    hmr_index += 1;
                }
                sim.apply_iter(std::iter::once(op));
            }
            assert_eq!(
                sim.phase & mask,
                phase & mask,
                "phase at stage {stage_index}"
            );
            for (lane, case) in cases.iter().enumerate() {
                for row in 0..2 {
                    let raw = read(&sim, &stage.rows[row], lane);
                    let value = if built.odd { 2 * raw + 1 } else { raw };
                    assert_eq!(
                        signed(value, stage.output_width),
                        case.pair[row],
                        "value stage={stage_index} row={row} lane={lane} odd={}",
                        built.odd
                    );
                }
                assert_eq!(stage.tape.len(), case.tape.len());
                for (&q, &expected) in stage.tape.iter().zip(&case.tape) {
                    assert_eq!(sim.qubit(q) >> lane & 1, u64::from(expected));
                }
            }
            for (q, &value) in sim.qubits.iter().enumerate() {
                let id = QubitId(q as u64);
                if !stage.rows.iter().any(|r| r.contains(&id)) && !stage.tape.contains(&id) {
                    assert_eq!(value & mask, 0, "scratch at stage={stage_index} wire={q}");
                }
            }
        }
        if built.stages.len() > 1 {
            for (lane, (before, after)) in batch.iter().zip(&cases).enumerate() {
                if dirty_support >> lane & 1 == 0 {
                    assert_eq!(after.pair, before.pair, "clean-support roundtrip");
                    assert!(after.tape.is_empty());
                }
            }
        }
    }
    dirty
}

fn all_pairs(width: usize, mode: Mode) -> Vec<Case> {
    let mut cases = Vec::new();
    for a in (1..1usize << width).step_by(2) {
        for b in (1..1usize << width).step_by(2) {
            let pair = [signed(a as i128, width), signed(b as i128, width)];
            match mode {
                Mode::Roundtrip => cases.push(Case { pair, tape: vec![] }),
                Mode::Supplied => cases.push(Case {
                    pair,
                    tape: vec![((a ^ b) >> 1) & 1 != 0],
                }),
                Mode::BackwardOnly => {
                    for sign in [false, true] {
                        cases.push(Case {
                            pair,
                            tape: vec![sign],
                        });
                    }
                }
            }
        }
    }
    cases
}

#[cfg_attr(test, test)]
fn exhaustive_basis_phase_and_pre_reset() {
    let mut dirty = 0;
    for width in 3..=7 {
        for next in 3..=width + 1 {
            for mode in [Mode::Roundtrip, Mode::Supplied, Mode::BackwardOnly] {
                let cases = all_pairs(width, mode);
                for vents in [0, 1, usize::MAX] {
                    for odd in [false, true] {
                        let built = build(&[width, next], odd, vents, false, mode);
                        for stream in 0..4 {
                            dirty += check(&built, &cases, stream, None);
                        }
                    }
                }
            }
        }
    }
    assert!(
        dirty > 0,
        "must exercise invalid width reductions, not just clean inputs"
    );
}

#[cfg_attr(test, test)]
fn actual_parent_and_every_small_vent_transcript() {
    for mode in [Mode::Roundtrip, Mode::Supplied, Mode::BackwardOnly] {
        for widths in [[4, 3], [4, 4], [4, 5]] {
            let cases = all_pairs(widths[0], mode);
            let vents = midq_value_vents();
            let full = build(&widths, false, vents, true, mode);
            let odd = build(&widths, true, vents, false, mode);
            for stream in 0..4 {
                check(&full, &cases, stream, None);
                check(&odd, &cases, stream, None);
            }
        }
    }
    for odd in [false, true] {
        let built = build(&[3, 3], odd, usize::MAX, false, Mode::Roundtrip);
        let hmr = built.ops.iter().filter(|op| op.kind == K::Hmr).count();
        assert!(hmr <= 4);
        for tape in 0..1 << hmr {
            check(&built, &all_pairs(3, Mode::Roundtrip), 3, Some(tape));
        }
    }
}

#[cfg_attr(test, test)]
fn ping_pong_schedule_and_static_cost() {
    assert_eq!(MIDQ_TAIL_VALUE_WIDTH.len(), 225);
    assert!(MIDQ_TAIL_VALUE_WIDTH.iter().all(|&w| w >= 4));
    assert!(MIDQ_TAIL_VALUE_WIDTH.windows(2).all(|w| w[1] <= w[0]));
    // Exhaustive projection retains the entire 224-round ordering, plateau
    // behavior and the late reductions. Other drops are covered above.
    let small: Vec<usize> = MIDQ_TAIL_VALUE_WIDTH
        .iter()
        .map(|&w| usize::from(w).min(6))
        .collect();
    for odd in [false, true] {
        let built = build(&small, odd, 1, false, Mode::Roundtrip);
        for stream in 0..4 {
            check(&built, &all_pairs(6, Mode::Roundtrip), stream, None);
        }
    }
    // Actual 85..4 schedule, including extreme signed/overflowing inputs.
    // This checks the value walk, not normalization/coefficient/endpoint code.
    let widths: Vec<usize> = MIDQ_TAIL_VALUE_WIDTH
        .iter()
        .map(|&w| usize::from(w))
        .collect();
    let edge = (1i128 << (widths[0] - 1)) - 1;
    let values = [-edge, -edge + 2, -7, -3, -1, 1, 3, 7, edge - 2, edge];
    let cases: Vec<Case> = values
        .iter()
        .flat_map(|&a| {
            values.iter().map(move |&b| Case {
                pair: [a, b],
                tape: vec![],
            })
        })
        .collect();
    for odd in [false, true] {
        // The actual reference reads its configured budget. Never mutate the
        // process environment in a test: other selftests can run concurrently.
        let built = build(
            &widths,
            odd,
            1,
            !odd && midq_value_vents() == 1,
            Mode::Roundtrip,
        );
        for stream in 0..4 {
            check(&built, &cases, stream, None);
        }
    }
    for width in 3..=12 {
        for vents in [0, 1, usize::MAX] {
            let full = build(&[width, width], false, vents, false, Mode::Roundtrip);
            let odd = build(&[width, width], true, vents, false, Mode::Roundtrip);
            assert_eq!(full.peak - odd.peak, 2 + u64::from(vents >= width - 1));
        }
    }
}

#[cfg_attr(test, test)]
fn conversion_reuses_freed_ids_without_reacquiring_them() {
    let mut c = Circuit::new();
    let mut a = c.alloc_qreg_bits("a", 4);
    let mut b = c.alloc_qreg_bits("b", 4);
    let initial = [ids(&a), ids(&b)];
    compress(&mut c, &mut a);
    compress(&mut c, &mut b);
    assert_eq!(c.b.active_qubits, 6);
    let occupied = c.alloc_qreg_bits("occupied.lows", 2);
    let occupied_ids = ids(&occupied);
    assert!(occupied_ids.contains(&initial[0][0]) && occupied_ids.contains(&initial[1][0]));
    for q in &occupied {
        c.x(q);
    }
    let middle = c.b.ops.len();
    expand(&mut c, &mut a);
    expand(&mut c, &mut b);
    let final_rows = [ids(&a), ids(&b)];
    assert!(!occupied_ids.contains(&final_rows[0][0]) && !occupied_ids.contains(&final_rows[1][0]));
    for q in occupied {
        c.x(&q);
        c.zero_and_free(q);
    }
    let (nq, nb) = simulator_capacity(&c);
    for stream in 0..4 {
        let mut word = Word(0);
        let mut sim = Simulator::new(nq, nb, &mut word);
        for lane in 0..64 {
            write(&mut sim, &initial[0], lane, ((lane & 7) * 2 + 1) as i128);
            write(&mut sim, &initial[1], lane, ((lane >> 3) * 2 + 1) as i128);
        }
        sim.phase = 0x1234_5678_9abc_def0;
        for (i, op) in c.b.ops.iter().enumerate() {
            if op.kind == K::R {
                assert_eq!(sim.qubit(op.q_target), 0, "conversion pre-reset");
            }
            sim.xof.0 = measurement(stream, i);
            sim.apply_iter(std::iter::once(op));
            if i + 1 == middle {
                assert!(occupied_ids.iter().all(|&q| sim.qubit(q) == u64::MAX));
            }
        }
        assert_eq!(sim.phase, 0x1234_5678_9abc_def0);
        for lane in 0..64 {
            assert_eq!(
                read(&sim, &final_rows[0], lane),
                ((lane & 7) * 2 + 1) as i128
            );
            assert_eq!(
                read(&sim, &final_rows[1], lane),
                ((lane >> 3) * 2 + 1) as i128
            );
        }
        for (q, &value) in sim.qubits.iter().enumerate() {
            if !final_rows.iter().any(|r| r.contains(&QubitId(q as u64))) {
                assert_eq!(value, 0);
            }
        }
    }
}

#[cfg_attr(test, test)]
fn preceding_loan_establishes_oddness_without_erasing_old_error_phases() {
    let mut c = Circuit::new();
    let mut a = c.alloc_qreg_bits("a", 4);
    let mut b = c.alloc_qreg_bits("b", 4);
    let initial = [ids(&a), ids(&b)];
    let lows = midq_loan_odd_low_bits(&mut c, &a, &b);
    let inherited: Vec<usize> = (0..c.b.ops.len())
        .filter(|&i| c.b.ops[i].kind == K::R)
        .collect();
    assert_eq!(inherited.len(), 2);
    midq_restore_odd_low_bits(&mut c, &a, &b, lows);
    compress(&mut c, &mut a);
    compress(&mut c, &mut b);
    let output = [ids(&a), ids(&b)];
    let (nq, nb) = simulator_capacity(&c);
    for stream in 0..4 {
        for first in (0..256).step_by(64) {
            let mut word = Word(0);
            let mut sim = Simulator::new(nq, nb, &mut word);
            for lane in 0..64 {
                write(&mut sim, &initial[0], lane, ((first + lane) & 15) as i128);
                write(&mut sim, &initial[1], lane, ((first + lane) >> 4) as i128);
            }
            let mut phase = 0;
            for (i, op) in c.b.ops.iter().enumerate() {
                sim.xof.0 = measurement(stream, i);
                if op.kind == K::R {
                    let expected = if let Some(row) = inherited.iter().position(|&r| r == i) {
                        (0..64).fold(0, |mask, lane| {
                            mask | (((((first + lane) >> (4 * row)) & 1) ^ 1) as u64) << lane
                        })
                    } else {
                        0
                    };
                    assert_eq!(sim.qubit(op.q_target), expected);
                    phase ^= expected & sim.xof.0;
                }
                sim.apply_iter(std::iter::once(op));
            }
            assert_eq!(sim.phase, phase);
            for lane in 0..64 {
                assert_eq!(
                    read(&sim, &output[0], lane),
                    (((first + lane) & 15) >> 1) as i128
                );
                assert_eq!(read(&sim, &output[1], lane), ((first + lane) >> 5) as i128);
            }
            for (q, &value) in sim.qubits.iter().enumerate() {
                if !output.iter().any(|r| r.contains(&QubitId(q as u64))) {
                    assert_eq!(value, 0);
                }
            }
        }
    }
}

#[cfg_attr(test, test)]
fn simulator_capacity_includes_untouched_registers() {
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("input.a", 4);
    let b = c.alloc_qreg_bits("input.b", 4);
    let carry = c.alloc_qreg_bits("untouched.carry", 1);
    let sign = c.alloc_qreg_bits("untouched.sign", 1);
    let _unused_bit = c.alloc_bit();
    c.x(&a[0]);
    c.x(&b[0]);
    let declared = [ids(&a), ids(&b), ids(&carry), ids(&sign)];
    let (op_nq, op_nb, _, _) = analyze_ops(c.b.ops.iter());
    assert_eq!((op_nq, op_nb), (5, 0));
    let (nq, nb) = simulator_capacity(&c);
    assert_eq!((nq, nb), (10, 1));
    assert!(declared.iter().flatten().all(|q| (q.0 as usize) < nq));
    let mut word = Word(0);
    let mut sim = Simulator::new(nq, nb, &mut word);
    for (reg, value) in declared.iter().zip([15, 15, 1, 1]) {
        write(&mut sim, reg, 0, value);
    }
    sim.bits[nb - 1] = 1;
    sim.apply_iter(c.b.ops.iter());
    for (reg, expected) in declared.iter().zip([14, 14, 1, 1]) {
        assert_eq!(read(&sim, reg, 0), expected);
    }
    assert_eq!(sim.bits[nb - 1], 1);
    assert_eq!(sim.phase, 0);
}

#[cfg_attr(test, test)]
fn wrap_and_domain_counterexamples() {
    // Odd 7+7 at W=4 wraps to -2 BEFORE halving, so output is -1, not 7.
    assert_eq!(signed(7 + 7, 4) >> 1, -1);
    // A wrong supplied sign makes the output even: it cannot be compressed.
    assert_eq!(signed(1 - 1, 4) >> 1, 0);
    // Do not silently turn an even normalized input into an odd input.
    assert_ne!(((2i128 >> 1) << 1) | 1, 2);
    // Signed-unit convergence is not assumed by the constant-width map.
    let mut case = Case {
        pair: [3, 3],
        tape: vec![],
    };
    let built = build(&[4, 4, 4, 4, 4], true, 0, false, Mode::Roundtrip);
    for stage in &built.stages[..4] {
        step_model(&mut case, stage, false);
    }
    assert!(case.pair.iter().any(|v| v.abs() == 3));
}

pub(super) fn run() {
    simulator_capacity_includes_untouched_registers();
    exhaustive_basis_phase_and_pre_reset();
    actual_parent_and_every_small_vent_transcript();
    ping_pong_schedule_and_static_cost();
    conversion_reuses_freed_ids_without_reacquiring_them();
    preceding_loan_establishes_oddness_without_erasing_old_error_phases();
    wrap_and_domain_counterexamples();
    eprintln!("MIDQ_ODD_VALUES PASS: exhaustive odd basis, wrap, inverse including invalid resizes, semantic R/phase coupling, pre-reset/scratch, vents, ownership, 225-boundary schedule");
}
