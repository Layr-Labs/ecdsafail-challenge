use super::*;
use crate::circuit::{BitId, RegisterId};
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

fn gate(kind: K, q: &[u64]) -> Op {
    let mut op = Op::empty();
    op.kind = kind;
    match kind {
        K::X | K::Z | K::R | K::Hmr => op.q_target = QubitId(q[0]),
        K::CX | K::CZ | K::Swap => {
            op.q_control1 = QubitId(q[0]);
            op.q_target = QubitId(q[1]);
        }
        K::CCX | K::CCZ => {
            op.q_control2 = QubitId(q[0]);
            op.q_control1 = QubitId(q[1]);
            op.q_target = QubitId(q[2]);
        }
        _ => {}
    }
    op
}
fn bit_op(kind: K, bit: u64) -> Op {
    let mut op = gate(kind, &[]);
    op.c_target = BitId(bit);
    op
}
fn push(bit: u64) -> Op {
    let mut op = gate(K::PushCondition, &[]);
    op.c_condition = BitId(bit);
    op
}
fn measured(q: u64, bit: u64) -> Op {
    let mut op = gate(K::Hmr, &[q]);
    op.c_target = BitId(bit);
    op
}
struct Outcomes(Option<u8>, sha3::Shake256Reader);
impl Outcomes {
    fn new(mode: usize) -> Self {
        let mut h = Shake256::default();
        h.update(b"q834-overlapping-commutation-20260910");
        h.update(&(mode as u64).to_le_bytes());
        Self(
            [Some(0), Some(255), Some(0x55), None][mode],
            h.finalize_xof(),
        )
    }
}
impl XofReader for Outcomes {
    fn read(&mut self, out: &mut [u8]) {
        if let Some(v) = self.0 {
            out.fill(v)
        } else {
            self.1.read(out)
        }
    }
}
fn equivalent(before: &[Op], after: &[Op]) {
    for op in before.iter().chain(after) {
        op.validate();
    }
    for mode in 0..4 {
        for classical in 0..4 {
            let mut ra = Outcomes::new(mode);
            let mut rb = Outcomes::new(mode);
            let mut a = Simulator::new(6, 4, &mut ra);
            let mut b = Simulator::new(6, 4, &mut rb);
            // All six-qubit computational basis states occupy the64 native lanes.
            // The incoming phase is deliberately nonzero, and all work bits are compared.
            for q in 0..6 {
                a.qubits[q] =
                    (0..64).fold(0u64, |m, lane| m | ((((lane >> q) & 1) as u64) << lane));
            }
            a.bits[0] = if classical & 1 != 0 { u64::MAX } else { 0 };
            a.bits[1] = if classical & 2 != 0 { u64::MAX } else { 0 };
            a.bits[2] = 0x935a_7601_d4ef_a871;
            a.bits[3] = 0x679b_ac3d_052e_f841;
            a.phase = 0x59a6_f120_8b3d_7ce4;
            b.qubits = a.qubits.clone();
            b.bits = a.bits.clone();
            b.phase = a.phase;
            a.apply_iter(before.iter());
            b.apply_iter(after.iter());
            assert_eq!(
                a.qubits, b.qubits,
                "quantum data/ancilla state mode={mode},classical={classical}"
            );
            assert_eq!(
                a.bits, b.bits,
                "measurement/classical state mode={mode},classical={classical}"
            );
            assert_eq!(a.phase, b.phase, "phase mode={mode},classical={classical}");
            assert!(b.stats.toffoli_gates <= a.stats.toffoli_gates);
            assert!(b.stats.clifford_gates <= a.stats.clifford_gates);
            drop(a);
            drop(b);
            let mut next_a = [0u8; 32];
            let mut next_b = [0u8; 32];
            ra.read(&mut next_a);
            rb.read(&mut next_b);
            assert_eq!(next_a, next_b, "unchanged R/HMR consumption order");
        }
    }
}
fn transformed(before: &[Op]) -> (Vec<Op>, Stats) {
    let mut after = before.to_vec();
    let original_ptr = after.as_ptr();
    let original_capacity = after.capacity();
    let stats = cancel(&mut after);
    assert_eq!(
        after.as_ptr(),
        original_ptr,
        "Op storage must be compacted in place"
    );
    assert_eq!(
        after.capacity(),
        original_capacity,
        "no Op shrink/reallocation"
    );
    equivalent(before, &after);
    (after, stats)
}

#[test]
fn overlapping_xfamily_and_diagonal_pairs() {
    let triples = [
        (gate(K::CCX, &[0, 1, 2]), gate(K::X, &[2])),
        (gate(K::CCX, &[0, 1, 2]), gate(K::CX, &[3, 2])),
        (gate(K::CCX, &[0, 1, 2]), gate(K::CX, &[0, 3])),
        (gate(K::CCX, &[0, 1, 2]), gate(K::Z, &[0])),
        (gate(K::CX, &[0, 1]), gate(K::X, &[1])),
        (gate(K::Z, &[0]), gate(K::CZ, &[0, 1])),
        (gate(K::CZ, &[0, 1]), gate(K::CCZ, &[0, 2, 3])),
        (gate(K::CCZ, &[0, 1, 2]), gate(K::CZ, &[1, 3])),
        (gate(K::X, &[0]), gate(K::X, &[1])),
    ];
    for (pair, middle) in triples {
        let (after, stats) = transformed(&[pair, middle, pair]);
        assert_eq!(after, vec![middle]);
        assert_eq!(stats.removed_ops, 2);
        assert_eq!(stats.toffoli_pairs_conditioned, 0);
        assert_eq!(
            stats.toffoli_pairs_unconditional,
            usize::from(matches!(pair.kind, K::CCX | K::CCZ))
        );
    }
}
#[test]
fn noncommuting_writes_reads_phases_and_swaps_block() {
    let triples = [
        (gate(K::CCX, &[0, 1, 2]), gate(K::X, &[0])),
        (gate(K::CCX, &[0, 1, 2]), gate(K::CX, &[2, 3])),
        (gate(K::CCX, &[0, 1, 2]), gate(K::Z, &[2])),
        (gate(K::CCX, &[0, 1, 2]), gate(K::CZ, &[2, 3])),
        (gate(K::CCX, &[0, 1, 2]), gate(K::Swap, &[0, 3])),
        (gate(K::CCX, &[0, 1, 2]), gate(K::Swap, &[2, 3])),
        (gate(K::Z, &[0]), gate(K::X, &[0])),
        (gate(K::CZ, &[0, 1]), gate(K::CX, &[2, 1])),
        (gate(K::CCZ, &[0, 1, 2]), gate(K::CCX, &[3, 4, 2])),
    ];
    for (pair, middle) in triples {
        let before = [pair, middle, pair];
        let (after, stats) = transformed(&before);
        assert_eq!(after, before);
        assert_eq!(stats.removed_ops, 0);
    }
}
#[test]
fn all_global_barriers_survive_and_clear_keys() {
    let pair = gate(K::CCX, &[0, 1, 2]);
    let mut register = gate(K::Register, &[]);
    register.r_target = RegisterId(0);
    let mut append = gate(K::AppendToRegister, &[]);
    append.r_target = RegisterId(0);
    append.q_target = QubitId(5);
    let mut conditional = gate(K::X, &[5]);
    conditional.c_condition = BitId(0);
    let barriers = [
        gate(K::Neg, &[]),
        register,
        append,
        bit_op(K::BitInvert, 0),
        bit_op(K::BitStore0, 0),
        bit_op(K::BitStore1, 0),
        gate(K::R, &[5]),
        measured(5, 2),
        gate(K::DebugPrint, &[]),
        conditional,
    ];
    for middle in barriers {
        let before = [pair, middle, pair];
        let (after, stats) = transformed(&before);
        assert_eq!(after, before);
        assert_eq!(stats.removed_ops, 0);
        assert_eq!(stats.max_keys, 1);
    }
    let before = [
        pair,
        push(0),
        gate(K::X, &[5]),
        gate(K::PopCondition, &[]),
        pair,
    ];
    let (after, stats) = transformed(&before);
    assert_eq!(after, before);
    assert_eq!(stats.removed_ops, 0);
}
#[test]
fn enclosing_conditions_allow_only_internal_pairs() {
    let pair = gate(K::CCX, &[0, 1, 2]);
    let middle = gate(K::X, &[2]);
    let before = [
        push(0),
        push(1),
        pair,
        middle,
        pair,
        gate(K::PopCondition, &[]),
        gate(K::PopCondition, &[]),
    ];
    let (after, stats) = transformed(&before);
    assert_eq!(after, [before[0], before[1], middle, before[5], before[6]]);
    assert_eq!(stats.toffoli_pairs_unconditional, 0);
    assert_eq!(stats.toffoli_pairs_conditioned, 1);
    assert_eq!(stats.max_condition_depth, 2);
    // Directly conditioned quantum gates remain complete barriers, even when
    // the same condition is named. Do not reuse the older q834 tuple shortcut.
    let mut direct = pair;
    direct.c_condition = BitId(0);
    let before = [direct, middle, direct];
    let (after, stats) = transformed(&before);
    assert_eq!(after, before);
    assert_eq!(stats.removed_ops, 0);
    // A classical write inside an enclosing condition also breaks matching.
    let before = [
        push(0),
        pair,
        bit_op(K::BitInvert, 1),
        pair,
        gate(K::PopCondition, &[]),
    ];
    let (after, stats) = transformed(&before);
    assert_eq!(after, before);
    assert_eq!(stats.removed_ops, 0);
}
#[test]
fn post_outer_elimination_q0_is_ordinary_data() {
    let pair = gate(K::CCX, &[1, 2, 3]);
    let mut ops = vec![
        gate(K::X, &[0]),
        pair,
        gate(K::X, &[3]),
        pair,
        gate(K::X, &[0]),
    ];
    super::super::eliminate_constant_outer_control(&mut ops, QubitId(0));
    assert_eq!(
        ops,
        [
            gate(K::CCX, &[0, 1, 2]),
            gate(K::X, &[2]),
            gate(K::CCX, &[0, 1, 2])
        ]
    );
    let (after, stats) = transformed(&ops);
    assert_eq!(after, [gate(K::X, &[2])]);
    assert_eq!(stats.toffoli_pairs_unconditional, 1);
}
#[test]
fn packed_mask_boundaries_and_no_stale_map_growth() {
    let pair = gate(K::CCX, &[0, 1, 2]);
    for padding in [0usize, 62, 63, 64, 65, 127, 128] {
        let mut before = vec![gate(K::Neg, &[]); padding];
        before.extend([pair, gate(K::X, &[2]), pair]);
        let (after, stats) = transformed(&before);
        assert_eq!(after.len(), padding + 1);
        assert_eq!(after[padding], gate(K::X, &[2]));
        assert_eq!(stats.deletion_words, before.len().div_ceil(64));
        assert_eq!(stats.deletion_bytes, 8 * before.len().div_ceil(64));
    }
    // Each key dies at its barrier. Peak map size is one rather than the
    // number of distinct gate signatures encountered in the whole stream.
    let mut before = Vec::new();
    for a in 0..6 {
        for b in 0..6 {
            if a != b {
                before.push(gate(K::CX, &[a, b]));
                before.push(bit_op(K::BitStore0, 0));
            }
        }
    }
    let (after, stats) = transformed(&before);
    assert_eq!(after, before);
    assert_eq!(stats.max_keys, 1);
    assert!(stats.max_key_capacity < 16);
}
fn next(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state
}
fn random_gate(state: &mut u64) -> Op {
    let mut wires = [0u64, 1, 2, 3, 4, 5];
    for i in (1..6).rev() {
        let j = (next(state) >> 32) as usize % (i + 1);
        wires.swap(i, j);
    }
    match next(state) % 12 {
        0 => gate(K::X, &wires[..1]),
        1 => gate(K::Z, &wires[..1]),
        2 => gate(K::CX, &wires[..2]),
        3 => gate(K::CZ, &wires[..2]),
        4 => gate(K::CCX, &wires[..3]),
        5 => gate(K::CCZ, &wires[..3]),
        6 => gate(K::Swap, &wires[..2]),
        7 => gate(K::R, &wires[..1]),
        8 => measured(wires[0], 2 + next(state) % 2),
        9 => bit_op(K::BitInvert, next(state) % 2),
        10 => {
            let mut op = gate(K::CCX, &wires[..3]);
            op.c_condition = BitId(next(state) % 4);
            op
        }
        _ => gate(K::Neg, &[]),
    }
}
#[test]
fn deterministic_mixed_programs_preserve_the_native_instrument() {
    let mut seed = 0x932c_581a_b74e_02dfu64;
    for _ in 0..40 {
        let pair = gate(K::CCX, &[0, 1, 2]);
        let mut before = vec![pair, gate(K::X, &[2]), pair];
        for block in 0..24 {
            if block % 3 == 0 {
                before.push(push(next(&mut seed) % 4));
                for _ in 0..5 {
                    before.push(random_gate(&mut seed));
                }
                before.push(gate(K::PopCondition, &[]));
            } else {
                for _ in 0..5 {
                    before.push(random_gate(&mut seed));
                }
            }
        }
        let (_, stats) = transformed(&before);
        assert!(stats.removed_ops >= 2);
    }
}
