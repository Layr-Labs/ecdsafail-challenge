use super::*;
use crate::circuit::{OperationType as K, QubitId, RegisterId};
use crate::sim::Simulator;
use sha3::digest::XofReader;

fn gate(kind: K, qs: &[u64]) -> Op {
    let mut op = Op::empty();
    op.kind = kind;
    if !qs.is_empty() {
        op.q_target = QubitId(qs[0]);
    }
    if qs.len() > 1 {
        op.q_control1 = QubitId(qs[1]);
    }
    if qs.len() > 2 {
        op.q_control2 = QubitId(qs[2]);
    }
    op
}
fn conditioned(mut op: Op, bit: u64) -> Op {
    op.c_condition = BitId(bit);
    op
}
fn bit_gate(kind: K, bit: u64) -> Op {
    let mut op = gate(kind, &[]);
    op.c_target = BitId(bit);
    op
}
fn hmr(q: u64, bit: u64) -> Op {
    let mut op = gate(K::Hmr, &[q]);
    op.c_target = BitId(bit);
    op
}
fn declarations(dirty: bool) -> Vec<Op> {
    let mut ops = Vec::new();
    for (reg, qs) in [(0, vec![0, 1, 2]), (1, vec![4, 5, 6])] {
        for q in qs
            .into_iter()
            .chain(if dirty && reg == 0 { Some(3) } else { None })
        {
            let mut op = gate(K::AppendToRegister, &[q]);
            op.r_target = RegisterId(reg);
            ops.push(op);
        }
    }
    for (reg, bit) in [(2, 0), (3, 1)] {
        let mut op = bit_gate(K::AppendToRegister, bit);
        op.r_target = RegisterId(reg);
        ops.push(op);
    }
    ops
}
fn circuit(body: &[Op], dirty: bool, late: bool) -> Vec<Op> {
    let mut ops = if late {
        Vec::new()
    } else {
        declarations(dirty)
    };
    ops.extend_from_slice(body);
    if late {
        ops.extend(declarations(dirty));
    }
    ops
}

struct Tape<'a> {
    words: &'a [u64],
    cursor: usize,
}
impl XofReader for Tape<'_> {
    fn read(&mut self, bytes: &mut [u8]) {
        assert_eq!(bytes.len(), 8);
        bytes.copy_from_slice(&self.words[self.cursor].to_le_bytes());
        self.cursor += 1;
    }
}
#[derive(Debug, PartialEq, Eq)]
struct State {
    q: Vec<u64>,
    c: Vec<u64>,
    phase: u64,
    t: u64,
}
fn native(ops: &[Op], q: &[u64], c: &[u64], tape: &[u64]) -> State {
    let mut rng = Tape {
        words: tape,
        cursor: 0,
    };
    let mut sim = Simulator::new(q.len(), c.len(), &mut rng);
    sim.qubits.clone_from_slice(q);
    sim.bits.clone_from_slice(c);
    sim.phase = 0xa55a_c33c_9669_f00f;
    // Always replay the complete prefix: apply_iter owns its condition stack.
    // Repeated one-op apply_iter calls would incorrectly drop nested guards.
    sim.apply_iter(ops.iter());
    let state = State {
        q: sim.qubits,
        c: sim.bits,
        phase: sim.phase,
        t: sim.stats.toffoli_gates,
    };
    assert_eq!(rng.cursor, tape.len());
    state
}
fn random(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

fn check(body: &[Op], dirty: bool) -> Stats { check_mode(body, dirty, false) }
fn check_mode(body: &[Op], dirty: bool, residual: bool) -> Stats {
    let mut last = None;
    for late in [false, true] {
        let source = circuit(body, dirty, late);
        let abi = AbiInputs::from_ops(&source);
        let mut segments = Vec::new();
        let (output, stats) = transform_mode(source.clone(), |_, replacement| {
            segments.push(replacement.len())
        }, residual);
        assert_eq!(stats.source_ops, source.len());
        // Independent direct stepping fingerprints the same outgoing proof state.
        // Any accidental stepping of emitted HMR/lowered records changes this.
        let mut direct = proof_engine::Proof::new(abi.nq, abi.nb, &abi.qinputs, &abi.cinputs);
        direct.affine_allowed = residual;
        for op in &source {
            direct.step(op);
        }
        assert_eq!(stats.proof_fingerprint, direct.diagnostic_fingerprint());
        let (_, output_nb, _, _) = analyze_ops(output.iter());
        let mut fresh_ids = Vec::new();
        let mut cursor = 0;
        for (index, op) in source.iter().enumerate() {
            let end = cursor + segments[index];
            let replacement = &output[cursor..end];
            if op.kind != K::CCX {
                assert_eq!(replacement, std::slice::from_ref(op));
            }
            if op.kind == K::CCX && replacement.first().map(|o| o.kind) == Some(K::Hmr) {
                assert_eq!(replacement[0].kind, K::Hmr);
                assert_eq!(replacement[1].kind, K::CZ);
                assert!(replacement[0].c_target.0 >= abi.nb as u64);
                assert_eq!(replacement[1].c_condition, replacement[0].c_target);
                fresh_ids.push(replacement[0].c_target.0);
            }
            for op in replacement {
                op.validate();
            }
            cursor = end;
        }
        assert!(fresh_ids.windows(2).all(|pair| pair[1] == pair[0] + 1));
        assert_eq!(fresh_ids.len() as u64, stats.measured_ands + stats.residual_wires + stats.residual_ones);
        let variables = abi.qinputs.len() + abi.cinputs.len();
        for base in (0..(1usize << variables)).step_by(64) {
            let mut q = vec![0; abi.nq];
            let mut c = vec![0; output_nb as usize];
            for lane in 0..64 {
                for (j, &wire) in abi.qinputs.iter().enumerate() {
                    q[wire] |= (((base + lane) >> j) as u64 & 1) << lane;
                }
                for (j, &wire) in abi.cinputs.iter().enumerate() {
                    c[wire] |= (((base + lane) >> (j + abi.qinputs.len())) as u64 & 1) << lane;
                }
            }
            // Four independent source/new outcome constants plus mixed masks.
            // Source outcomes keep their original identity after inserted HMRs.
            for mode in 0..5 {
                let mut old_tape = Vec::new();
                let mut new_tape = Vec::new();
                let mut rng = 0x217e_a8d9_7345_cf61u64;
                let mut cursor = 0;
                for (index, op) in source.iter().enumerate() {
                    let end = cursor + segments[index];
                    let original_outcome = if mode == 4 {
                        random(&mut rng)
                    } else if mode & 1 == 0 {
                        0
                    } else {
                        u64::MAX
                    };
                    let added_outcome = if mode == 4 {
                        random(&mut rng)
                    } else if mode & 2 == 0 {
                        0
                    } else {
                        u64::MAX
                    };
                    if matches!(op.kind, K::R | K::Hmr) {
                        old_tape.push(original_outcome);
                    }
                    for replacement in &output[cursor..end] {
                        if matches!(replacement.kind, K::R | K::Hmr) {
                            new_tape.push(
                                if replacement.kind == K::Hmr
                                    && replacement.c_target.0 >= abi.nb as u64
                                {
                                    added_outcome
                                } else {
                                    original_outcome
                                },
                            );
                        }
                    }
                    // This checks every wire (including scratch), every original
                    // classical bit, and phase before any later R can hide dirt.
                    let old = native(&source[..=index], &q, &c, &old_tape);
                    let new = native(&output[..end], &q, &c, &new_tape);
                    assert_eq!(old.q, new.q, "quantum prefix {index}: {op:?}");
                    assert_eq!(old.c[..abi.nb], new.c[..abi.nb], "classical prefix {index}");
                    assert_eq!(old.phase, new.phase, "phase prefix {index}: {op:?}");
                    if index + 1 == source.len() {
                        assert_eq!(
                            old.t - new.t,
                            64 * (stats.measured_ands + stats.residual_wires + stats.residual_ones
                                + stats.support_dead
                                + stats.support_x
                                + stats.support_cx)
                        );
                    }
                    cursor = end;
                }
            }
        }
        last = Some(stats);
    }
    last.unwrap()
}

#[test]
fn nonlinear_and_conditional_restored_controls_are_recovered() {
    let compute = gate(K::CCX, &[3, 1, 2]);
    for mutation in [
        gate(K::CCX, &[1, 5, 6]),
        conditioned(gate(K::CCX, &[1, 5, 6]), 0),
    ] {
        let body = [
            compute,
            mutation,
            mutation,
            gate(K::CX, &[4, 3]),
            gate(K::CZ, &[3, 6]),
            compute,
        ];
        assert_eq!(check(&body, false).measured_ands, 1);
        assert_eq!(check(&body, true).measured_ands, 0);
        let changed = [compute, mutation, gate(K::CX, &[4, 3]), compute];
        assert_eq!(check(&changed, false).measured_ands, 0);
    }
}

#[test]
fn actual_incumbent_pass_composition_preserves_the_new_opportunity() {
    let compute = gate(K::CCX, &[3, 1, 2]);
    let mutate = conditioned(gate(K::CCX, &[1, 5, 6]), 0);
    let original = circuit(
        &[compute, mutate, mutate, gate(K::CX, &[4, 3]), compute],
        false,
        true,
    );
    let incumbent = super::super::exact_boolean::simplify(original);
    let (_, stats) = transform(incumbent, |_, _| {});
    assert_eq!(stats.measured_ands, 1);
}

#[test]
fn source_measurements_keep_their_tape_and_new_ids_are_fresh() {
    let compute = gate(K::CCX, &[3, 1, 2]);
    let body = [
        compute,
        compute,
        hmr(7, 37),
        conditioned(gate(K::X, &[4]), 37),
        compute,
        gate(K::CX, &[7, 3]),
        hmr(7, 37),
        conditioned(gate(K::CZ, &[3, 1]), 37),
        compute,
    ];
    assert_eq!(check(&body, false).measured_ands, 2);
    assert_eq!(check(&body, false).fresh_classical_bits, 2);
    check(
        &[compute, gate(K::R, &[3]), compute, gate(K::Z, &[3])],
        false,
    );
}

#[test]
fn symbolic_classical_conditions_and_saved_stack_values() {
    let compute = gate(K::CCX, &[3, 1, 2]);
    let push0 = conditioned(gate(K::PushCondition, &[]), 0);
    let pop = gate(K::PopCondition, &[]);
    assert_eq!(
        check(&[compute, conditioned(compute, 0)], false).measured_ands,
        0
    );
    let restore = conditioned(gate(K::X, &[1]), 0);
    assert_eq!(
        check(&[compute, restore, restore, compute], false).measured_ands,
        1
    );
    // The source bit is changed inside the scope; the outer mask is a snapshot.
    check(
        &[
            compute,
            push0,
            bit_gate(K::BitInvert, 0),
            conditioned(compute, 0),
            pop,
            compute,
        ],
        false,
    );
    // A syntactically conditional source may be globally enabled by proven
    // classical state. The original engine admits cleanup only when cond==1.
    assert_eq!(
        check(
            &[
                compute,
                bit_gate(K::BitStore1, 37),
                conditioned(compute, 37)
            ],
            false
        )
        .measured_ands,
        1
    );
}

#[test]
fn only_support_lowering_and_clean_zero_residual_are_admitted() {
    assert_eq!(check(&[gate(K::CCX, &[3, 1, 7])], true).support_dead, 1);
    let set1 = [gate(K::R, &[1]), gate(K::X, &[1])];
    let mut body = set1.to_vec();
    body.push(gate(K::CCX, &[3, 1, 2]));
    assert_eq!(check(&body, true).support_cx, 1);
    let mut body = set1.to_vec();
    body.extend([gate(K::R, &[2]), gate(K::X, &[2]), gate(K::CCX, &[3, 1, 2])]);
    assert_eq!(check(&body, true).support_x, 1);
    for complement in [false, true] {
        let mut body = vec![gate(K::CX, &[7, 1])];
        if complement {
            body.push(gate(K::X, &[7]));
        }
        body.push(gate(K::CCX, &[3, 1, 7]));
        let stats = check(&body, true);
        assert_eq!(stats.support_dead, u64::from(complement));
        assert_eq!(stats.support_cx, u64::from(!complement));
    }
    // This target has an affine residual after cleanup. It must NOT trigger
    // the copied engine's optional residual/affine replacement machinery.
    let compute = gate(K::CCX, &[3, 1, 2]);
    let body = [compute, gate(K::CX, &[3, 4]), compute];
    let source = circuit(&body, false, false);
    let (output, stats) = transform(source, |_, _| {});
    assert_eq!(stats.measured_ands, 0);
    assert_eq!(output.last(), Some(&compute));
    check(&body, false);
}

#[test]
fn q0_exclusions_and_late_abi_inputs_are_preserved() {
    let involving_q0 = gate(K::CCX, &[3, 0, 1]);
    let stats = check(&[involving_q0, involving_q0], false);
    assert_eq!(stats.measured_ands, 0);
    assert_eq!(stats.support_dead + stats.support_x + stats.support_cx, 0);
    // Dirty registered q3, and both classical ABI inputs, are unknown even when
    // every declaration appears after the arithmetic source operations.
    let compute = gate(K::CCX, &[3, 1, 2]);
    assert_eq!(check(&[compute, compute], true).measured_ands, 0);
    assert_eq!(
        check(&[compute, conditioned(gate(K::X, &[3]), 1), compute], false).measured_ands,
        0
    );
}

#[test]
#[should_panic(expected = "four ABI registers")]
fn missing_abi_is_rejected_before_proofs() {
    transform(vec![gate(K::CCX, &[3, 1, 2])], |_, _| {});
}

#[test]
fn bounded_mixed_native_prefix_regression() {
    let gates = [
        gate(K::X, &[1]),
        gate(K::CX, &[3, 1]),
        gate(K::CX, &[7, 2]),
        gate(K::CCX, &[3, 1, 2]),
        gate(K::CCX, &[1, 5, 6]),
        gate(K::CZ, &[3, 7]),
        gate(K::CCZ, &[3, 1, 4]),
        gate(K::R, &[3]),
        hmr(7, 0),
        bit_gate(K::BitInvert, 1),
        conditioned(gate(K::CCX, &[3, 1, 2]), 1),
        gate(K::Swap, &[1, 2]),
    ];
    let mut seed = 0x8ad3_f702_1356_9be1;
    for _ in 0..32 {
        let body: Vec<_> = (0..24)
            .map(|_| gates[random(&mut seed) as usize % gates.len()])
            .collect();
        check(&body, false);
    }
}

#[test]
fn residual_native_one_and_live_wire_preserve_every_prefix() {
    let compute = gate(K::CCX, &[3, 1, 2]);
    for parity in [false, true] {
        let mut body = vec![compute, gate(K::CX, &[3, 4])];
        if parity { body.push(gate(K::X, &[3])); }
        body.push(compute);
        let stats = check_mode(&body, false, true);
        assert_eq!(stats.residual_wires, 1);
        assert_eq!(stats.residual_ones, 0);
        assert_eq!(check_mode(&body, true, true).residual_wires, 0);
    }
    let stats = check_mode(&[compute, gate(K::X, &[3]), compute], false, true);
    assert_eq!(stats.residual_ones, 1);
    assert_eq!(stats.residual_wires, 0);
}

#[test]
fn residual_phase_witness_change_and_condition_fallback() {
    let compute = gate(K::CCX, &[3, 1, 2]);
    let body = [compute, gate(K::CX, &[3, 4]), gate(K::X, &[4]), compute];
    assert_eq!(check_mode(&body, false, true).residual_wires, 1);
    let changed = [compute, gate(K::CX, &[3, 4]), gate(K::CX, &[4, 5]), compute];
    assert_eq!(check_mode(&changed, false, true).residual_wires, 0);
    let conditional = [compute, gate(K::CX, &[3, 4]), conditioned(compute, 0)];
    assert_eq!(check_mode(&conditional, false, true).residual_wires, 0);
    let mut push = gate(K::PushCondition, &[]); push.c_condition = BitId(0);
    let nested = [compute, gate(K::CX, &[3, 4]), push, compute, gate(K::PopCondition, &[])];
    assert_eq!(check_mode(&nested, false, true).residual_wires, 0);
}
