use super::super::{midq_value_round_backward, midq_value_round_forward};
use super::*;
use crate::circuit::{analyze_ops, Op, OperationType, QubitId};
use crate::sim::Simulator;
use alloy_primitives::U256;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

fn ids(reg: &[QReg]) -> Vec<QubitId> {
    reg.iter().map(|q| QubitId(q.id().into())).collect()
}

fn read<R: XofReader>(sim: &Simulator<R>, reg: &[QubitId], lane: usize) -> U256 {
    reg.iter().enumerate().fold(U256::ZERO, |value, (bit, &q)| {
        if sim.qubit(q) >> lane & 1 != 0 {
            value | (U256::from(1) << bit)
        } else {
            value
        }
    })
}

fn write<R: XofReader>(sim: &mut Simulator<R>, reg: &[QubitId], lane: usize, value: U256) {
    for (bit, &q) in reg.iter().enumerate() {
        if bit < 256 && value.bit(bit) {
            *sim.qubit_mut(q) |= 1 << lane;
        }
    }
}

fn check_scratch<R: XofReader>(sim: &Simulator<R>, live: &[&[QubitId]]) {
    for (index, &bits) in sim.qubits.iter().enumerate() {
        if !live.iter().any(|reg| reg.contains(&QubitId(index as u64))) {
            assert_eq!(bits, 0, "dirty scratch wire {index}");
        }
    }
}

#[cfg_attr(test, test)]
pub(super) fn checkpoint_lookup_exhaustive_values_signs_and_phase() {
    let mut c = Circuit::new();
    let a = c.alloc_qreg_bits("a", WIDTH);
    let b = c.alloc_qreg_bits("b", WIDTH);
    let outputs = c.alloc_qreg_bits("lookup.outputs", functions().len());
    for (output, target) in outputs.iter().enumerate() {
        lookup(&mut c, &a, &b, target, output);
    }
    let midpoint = c.b.ops.len();
    for (output, target) in outputs.iter().enumerate().rev() {
        lookup(&mut c, &a, &b, target, output);
    }
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let mut seed = Shake256::default();
    seed.update(b"checkpoint-lookups-v1");
    let mut rng = seed.finalize_xof();
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut rng);
    let (a_ids, b_ids, output_ids) = (ids(&a), ids(&b), ids(&outputs));
    for input in 0..STATES {
        write(&mut sim, &a_ids, input, U256::from((input & 7) * 2 + 1));
        write(&mut sim, &b_ids, input, U256::from((input >> 3) * 2 + 1));
    }
    sim.apply_iter(c.b.ops[..midpoint].iter());
    assert_eq!(sim.phase, 0);
    for input in 0..STATES {
        let (signs, pair) = trajectory(input);
        let tape: usize = signs
            .iter()
            .enumerate()
            .map(|(i, &s)| (s as usize) << i)
            .sum();
        let expected = tape
            | ((pair[0] as usize & 15) << ROUNDS)
            | ((pair[1] as usize & 15) << (ROUNDS + WIDTH));
        assert_eq!(read(&sim, &output_ids, input), U256::from(expected));
    }
    check_scratch(&sim, &[&a_ids, &b_ids, &output_ids]);
    sim.apply_iter(c.b.ops[midpoint..].iter());
    assert_eq!(sim.phase, 0);
    check_scratch(&sim, &[&a_ids, &b_ids]);
    for input in 0..STATES {
        assert_eq!(read(&sim, &a_ids, input), U256::from((input & 7) * 2 + 1));
        assert_eq!(read(&sim, &b_ids, input), U256::from((input >> 3) * 2 + 1));
    }
    eprintln!("CHECKPOINT_LOOKUP PASS: 64 odd pairs, all 4 signs and 8 terminal bits, phase/scratch/roundtrip");
}

#[cfg_attr(test, test)]
pub(super) fn checkpoint_value_model_matches_emitted_overflow_behavior() {
    let mut c = Circuit::new();
    let mut a = c.alloc_qreg_bits("a", WIDTH);
    let mut b = c.alloc_qreg_bits("b", WIDTH);
    let initial = [ids(&a), ids(&b)];
    let mut tape = Vec::new();
    let mut boundaries = Vec::new();
    for round in START..MIDQ_TAIL_ROUNDS {
        let sign = c.alloc_qreg("sign");
        if round % 2 == 0 {
            midq_value_round_forward(&mut c, &mut a, &mut b, &sign, WIDTH);
        } else {
            midq_value_round_forward(&mut c, &mut b, &mut a, &sign, WIDTH);
        }
        tape.push(sign);
        boundaries.push((c.b.ops.len(), [ids(&a), ids(&b)], ids(&tape)));
    }
    let midpoint = c.b.ops.len();
    for round in (START..MIDQ_TAIL_ROUNDS).rev() {
        let sign = tape.pop().unwrap();
        if round % 2 == 0 {
            midq_value_round_backward(&mut c, &mut a, &mut b, sign, WIDTH);
        } else {
            midq_value_round_backward(&mut c, &mut b, &mut a, sign, WIDTH);
        }
    }
    let final_ids = [ids(&a), ids(&b)];
    let (nq, nb, _, _) = analyze_ops(c.b.ops.iter());
    let mut seed = Shake256::default();
    seed.update(b"checkpoint-overflow-v1");
    let mut rng = seed.finalize_xof();
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut rng);
    let mut model = [[0i16; 2]; STATES];
    for (input, pair) in model.iter_mut().enumerate() {
        pair[0] = signed(((input & 7) * 2 + 1) as i16, WIDTH);
        pair[1] = signed(((input >> 3) * 2 + 1) as i16, WIDTH);
        write(
            &mut sim,
            &initial[0],
            input,
            U256::from(pair[0] as u16 & 15),
        );
        write(
            &mut sim,
            &initial[1],
            input,
            U256::from(pair[1] as u16 & 15),
        );
    }
    let mut begin = 0;
    let mut overflow = 0;
    for (offset, (end, regs, signs)) in boundaries.iter().enumerate() {
        sim.apply_iter(c.b.ops[begin..*end].iter());
        assert_eq!(sim.phase, 0, "value round {offset}");
        for (input, pair) in model.iter_mut().enumerate() {
            let sign = (pair[0] ^ pair[1]) >> 1 & 1;
            let target = if (START + offset) % 2 == 0 { 1 } else { 0 };
            let sum = pair[target]
                + if sign == 0 {
                    pair[1 - target]
                } else {
                    -pair[1 - target]
                };
            overflow += usize::from(!(-8..8).contains(&sum));
            pair[target] = signed(sum, WIDTH) >> 1;
            assert_eq!((sim.qubit(signs[offset]) >> input) & 1, sign as u64);
            for reg in 0..2 {
                assert_eq!(
                    read(&sim, &regs[reg], input),
                    U256::from(pair[reg] as u16 & 15)
                );
            }
        }
        check_scratch(&sim, &[&regs[0], &regs[1], signs]);
        begin = *end;
    }
    assert!(overflow > 0);
    assert!(model.iter().any(|pair| pair[0].abs() == 3));
    sim.apply_iter(c.b.ops[midpoint..].iter());
    assert_eq!(sim.phase, 0);
    for input in 0..STATES {
        assert_eq!(
            read(&sim, &final_ids[0], input),
            U256::from((input & 7) * 2 + 1)
        );
        assert_eq!(
            read(&sim, &final_ids[1], input),
            U256::from((input >> 3) * 2 + 1)
        );
    }
    check_scratch(&sim, &[&final_ids[0], &final_ids[1]]);
    eprintln!("CHECKPOINT_VALUES PASS: 64 pairs x 4 emitted rounds, {overflow} overflowing sums, non-unit endpoints, inverse/phase/scratch");
}

struct Component {
    ops: Vec<Op>,
    midpoint: usize,
    initial: [Vec<QubitId>; 4],
    terminal: [Vec<QubitId>; 4],
    final_ids: [Vec<QubitId>; 4],
    terminal_tape: Vec<QubitId>,
}

fn component(checkpoint: bool) -> Component {
    let mut c = Circuit::new();
    let mut a = c.alloc_qreg_bits("a", WIDTH);
    let mut b = c.alloc_qreg_bits("b", WIDTH);
    let ca = c.alloc_qreg_bits("ca", 257);
    let cb = c.alloc_qreg_bits("cb", 257);
    let initial = [ids(&a), ids(&b), ids(&ca), ids(&cb)];
    let mut tape = Vec::new();
    if checkpoint {
        forward(&mut c, &a, &b, &ca, &cb);
    } else {
        for round in START..MIDQ_TAIL_ROUNDS {
            let sign = c.alloc_qreg("sign");
            if round % 2 == 0 {
                midq_value_round_forward(&mut c, &mut a, &mut b, &sign, WIDTH);
            } else {
                midq_value_round_forward(&mut c, &mut b, &mut a, &sign, WIDTH);
            }
            let lows = midq_loan_odd_low_bits(&mut c, &a, &b);
            let (target, source) = if round % 2 == 0 {
                (&cb, &ca)
            } else {
                (&ca, &cb)
            };
            midq_mod_signed_add_halve(&mut c, target, source, &sign, false);
            midq_restore_odd_low_bits(&mut c, &a, &b, lows);
            tape.push(sign);
        }
    }
    let midpoint = c.b.ops.len();
    let terminal = [ids(&a), ids(&b), ids(&ca), ids(&cb)];
    let terminal_tape = ids(&tape);
    if checkpoint {
        backward(&mut c, &a, &b, &ca, &cb);
    } else {
        for round in (START..MIDQ_TAIL_ROUNDS).rev() {
            let sign = tape.pop().unwrap();
            let lows = midq_loan_odd_low_bits(&mut c, &a, &b);
            let (target, source) = if round % 2 == 0 {
                (&cb, &ca)
            } else {
                (&ca, &cb)
            };
            midq_mod_signed_add_halve(&mut c, target, source, &sign, true);
            midq_restore_odd_low_bits(&mut c, &a, &b, lows);
            if round % 2 == 0 {
                midq_value_round_backward(&mut c, &mut a, &mut b, sign, WIDTH);
            } else {
                midq_value_round_backward(&mut c, &mut b, &mut a, sign, WIDTH);
            }
        }
    }
    let final_ids = [ids(&a), ids(&b), ids(&ca), ids(&cb)];
    Component {
        ops: c.b.ops,
        midpoint,
        initial,
        terminal,
        final_ids,
        terminal_tape,
    }
}

#[cfg_attr(test, test)]
pub(super) fn checkpoint_full_width_coefficients_match_reference() {
    let cases = [component(false), component(true)];
    let p = U256::MAX - U256::from(0x1000003d0u64);
    let mut observations = Vec::new();
    for (checkpoint, case) in cases.iter().enumerate() {
        let (nq, nb, _, _) = analyze_ops(case.ops.iter());
        let mut seed = Shake256::default();
        seed.update(b"checkpoint-coefficients-v1");
        let mut rng = seed.finalize_xof();
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut rng);
        let mut observed = Vec::new();
        for batch in 0..8 {
            sim.clear_for_shot();
            let mut inputs = Vec::new();
            for input in 0..STATES {
                let u = U256::from((input + 1 + batch * 73) as u64);
                // The inherited fast modular cells have their own exceptional
                // zero/cancellation boundary. Use nondegenerate full-width
                // canonical coefficients, independently of the 64 value pairs.
                let coeffs = [(u << 192) + (u << 65) + u, p - (u << 128) - u];
                let values = [
                    U256::from((input & 7) * 2 + 1),
                    U256::from((input >> 3) * 2 + 1),
                    coeffs[0],
                    coeffs[1],
                ];
                for reg in 0..4 {
                    write(&mut sim, &case.initial[reg], input, values[reg]);
                }
                inputs.push(values);
            }
            sim.apply_iter(case.ops[..case.midpoint].iter());
            assert_eq!(
                sim.phase, 0,
                "forward phase checkpoint={checkpoint} batch={batch}"
            );
            assert_eq!(sim.qubit(case.terminal[2][256]), 0, "ca overflow bit");
            assert_eq!(sim.qubit(case.terminal[3][256]), 0, "cb overflow bit");
            for input in 0..STATES {
                let pair = trajectory(input).1;
                for reg in 0..2 {
                    let sign_bit = if checkpoint == 1 { 0 } else { WIDTH - 1 };
                    assert_eq!(
                        sim.qubit(case.terminal[reg][sign_bit]) >> input & 1,
                        u64::from(pair[reg] < 0)
                    );
                }
                observed.push([
                    read(&sim, &case.terminal[2], input),
                    read(&sim, &case.terminal[3], input),
                ]);
            }
            check_scratch(
                &sim,
                &[
                    &case.terminal[0],
                    &case.terminal[1],
                    &case.terminal[2],
                    &case.terminal[3],
                    &case.terminal_tape,
                ],
            );
            sim.apply_iter(case.ops[case.midpoint..].iter());
            assert_eq!(
                sim.phase, 0,
                "reverse phase checkpoint={checkpoint} batch={batch}"
            );
            assert_eq!(
                sim.qubit(case.final_ids[2][256]),
                0,
                "restored ca overflow bit"
            );
            assert_eq!(
                sim.qubit(case.final_ids[3][256]),
                0,
                "restored cb overflow bit"
            );
            for (input, expected) in inputs.iter().enumerate() {
                for reg in 0..4 {
                    assert_eq!(
                        read(&sim, &case.final_ids[reg], input),
                        expected[reg],
                        "restoration checkpoint={checkpoint} batch={batch} lane={input} reg={reg}"
                    );
                }
            }
            check_scratch(
                &sim,
                &[
                    &case.final_ids[0],
                    &case.final_ids[1],
                    &case.final_ids[2],
                    &case.final_ids[3],
                ],
            );
        }
        observations.push(observed);
        let tof = case
            .ops
            .iter()
            .filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ))
            .count();
        eprintln!(
            "CHECKPOINT_COMPONENT checkpoint={checkpoint} Q={nq} emitted_T={tof} ops={}",
            case.ops.len()
        );
    }
    assert_eq!(observations[0], observations[1]);
    eprintln!("CHECKPOINT_COEFFICIENTS PASS: 512 inputs per circuit, 257-bit coefficients, all four forward/backward updates, selectors/phase/scratch");
}

#[cfg_attr(test, test)]
pub(super) fn checkpoint_schedule_storage_accounting() {
    assert_eq!(MIDQ_TAIL_VALUE_WIDTH.len(), 225);
    assert_eq!(MIDQ_TAIL_VALUE_WIDTH[219], 5);
    assert!(MIDQ_TAIL_VALUE_WIDTH[220..].iter().all(|&w| w == 4));
    let raw_endpoint = MIDQ_TAIL_ROUNDS + 2 * WIDTH;
    let best_copied = (0..MIDQ_TAIL_ROUNDS)
        .map(|r| r + 4 * MIDQ_TAIL_VALUE_WIDTH[r] as usize - 2)
        .min()
        .unwrap();
    assert_eq!(raw_endpoint, 232);
    assert_eq!(best_copied, 234);
    for r in [0, 32, 92, 100, 140, 160, 180, 198, 202, 211, 220] {
        let w = MIDQ_TAIL_VALUE_WIDTH[r] as usize;
        eprintln!("CHECKPOINT_BOUNDARY r={r} w={w} suffix={} checkpoint_odd={} prefix_checkpoint_current={} optimistic_oracle_state={}",
            MIDQ_TAIL_ROUNDS-r, 2*w-2, r+4*w-2, r+2*w-2);
    }
    eprintln!("CHECKPOINT_STORAGE raw_endpoint={raw_endpoint} best_duplicate_before_scratch={best_copied}; encoded_suffix=6 checkpoint + 2 selectors + at most 1 lookup scratch; coefficient pair=514 unchanged");
}
