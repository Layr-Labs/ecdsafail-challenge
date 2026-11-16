//! Fixed differential test for the pristine and mechanically moved simulators.
//! Defined here only; source preparation does not execute it.
use super::c162_audit::{c162_validate_shape, C162Audit, C162Relation, Simulator as Audited};
use crate::circuit::{BitId, Op, OperationType as K, QubitId, RegisterId};
use crate::sim::Simulator as Pristine;
use sha3::{digest::XofReader, Digest, Keccak256};

const CASES: usize = 128;
const WIDTH: usize = 8;
const BITS: usize = 8;
const SEED: u64 = 0x49534f4c41544526;
fn next(x: &mut u64) -> u64 { *x ^= *x << 13; *x ^= *x >> 7; *x ^= *x << 17; *x }
#[derive(Clone)]
struct Bytes { state: u64, reads: usize, bytes: usize }
impl XofReader for Bytes {
    fn read(&mut self, out: &mut [u8]) {
        self.reads += 1; self.bytes += out.len();
        for byte in out { *byte = next(&mut self.state) as u8; }
    }
}
#[derive(Clone)]
struct Input { qubits: Vec<u64>, bits: Vec<u64>, phase: u64, seed: u64, valid: u64 }
#[derive(Debug, PartialEq, Eq)]
struct State {
    qubits: Vec<u64>, bits: Vec<u64>, phase: u64, stats: (u64, u64),
    random: (u64, usize, usize),
}
fn input(case: usize) -> Input {
    let mut seed = SEED ^ ((case as u64 + 1) << 32);
    let mut qubits: Vec<_> = (0..WIDTH).map(|_| next(&mut seed)).collect();
    let mut bits: Vec<_> = (0..BITS).map(|_| next(&mut seed)).collect();
    qubits[4] = 0; bits[0] = 0;
    let masks = [0, u64::MAX, 0xaaaaaaaaaaaaaaaa, 0x5555555555555555];
    bits[1] = masks[case & 3]; bits[2] = masks[(case >> 2) & 3]; bits[3] = masks[(case >> 4) & 3];
    Input { qubits, bits, phase: next(&mut seed), seed: next(&mut seed),
        valid: if case < 64 { u64::MAX } else { 0xaaaaaaaaaaaaaaaa } }
}
fn stream() -> (Vec<Op>, Vec<C162Audit>) {
    let q = QubitId; let c = BitId;
    let mut ops = vec![
        Op { kind: K::Register, r_target: RegisterId(0), ..Op::empty() },
        Op { kind: K::AppendToRegister, r_target: RegisterId(0), q_target: q(7), ..Op::empty() },
        Op { kind: K::AppendToRegister, r_target: RegisterId(0), c_target: c(7), ..Op::empty() },
        Op { kind: K::DebugPrint, ..Op::empty() },
        Op { kind: K::PushCondition, c_condition: c(1), ..Op::empty() },
        Op { kind: K::X, q_target: q(0), c_condition: c(3), ..Op::empty() },
        Op { kind: K::CX, q_control1: q(0), q_target: q(1), c_condition: c(3), ..Op::empty() },
        Op { kind: K::CCX, q_control1: q(0), q_control2: q(1), q_target: q(2), ..Op::empty() },
        Op { kind: K::Z, q_target: q(2), c_condition: c(3), ..Op::empty() },
        Op { kind: K::CZ, q_control1: q(0), q_target: q(1), ..Op::empty() },
        Op { kind: K::CCZ, q_control1: q(0), q_control2: q(1), q_target: q(2), c_condition: c(3), ..Op::empty() },
        Op { kind: K::Swap, q_control1: q(2), q_target: q(3), c_condition: c(3), ..Op::empty() },
        Op { kind: K::Neg, c_condition: c(3), ..Op::empty() },
        Op { kind: K::BitInvert, c_target: c(4), c_condition: c(3), ..Op::empty() },
        Op { kind: K::BitStore0, c_target: c(5), c_condition: c(3), ..Op::empty() },
        Op { kind: K::BitStore1, c_target: c(6), c_condition: c(3), ..Op::empty() },
        Op { kind: K::PushCondition, c_condition: c(2), ..Op::empty() },
    ];
    let compute = Op { kind: K::CCX, q_control1: q(0), q_control2: q(1), q_target: q(4), c_condition: c(3), ..Op::empty() };
    let hmr = Op { kind: K::Hmr, q_target: q(4), c_target: c(0), c_condition: c(3), ..Op::empty() };
    let correction = Op { kind: K::CZ, q_control1: q(0), q_target: q(1), c_condition: c(0), ..Op::empty() };
    let audits = vec![
        C162Audit { at: ops.len(), family: "isolation_compute", operation: compute, relation: C162Relation::Clean, correction: vec![] },
        C162Audit { at: ops.len()+1, family: "isolation_erase", operation: hmr, relation: C162Relation::Product(q(0), q(1)), correction: vec![correction] },
    ];
    ops.extend([compute, hmr, correction,
        Op { kind: K::R, q_target: q(5), c_condition: c(3), ..Op::empty() },
        Op { kind: K::PopCondition, ..Op::empty() },
        Op { kind: K::X, q_target: q(6), ..Op::empty() },
        Op { kind: K::PopCondition, ..Op::empty() },
        Op { kind: K::BitInvert, c_target: c(7), ..Op::empty() },
    ]);
    assert_eq!(ops.len(), 25);
    let mut kinds = 0u32;
    for op in &ops { op.validate(); kinds |= 1 << (op.kind as u32); }
    assert_eq!(kinds, (1 << 18)-1, "every official operation family is present");
    c162_validate_shape(&ops, &audits).unwrap(); (ops, audits)
}
fn pure(ops: &[Op], w: &Input) -> State {
    let mut rng = Bytes { state: w.seed, reads: 0, bytes: 0 };
    let mut sim = Pristine::new(WIDTH, BITS, &mut rng);
    sim.qubits.clone_from_slice(&w.qubits); sim.bits.clone_from_slice(&w.bits); sim.phase = w.phase;
    sim.apply_iter(ops.iter());
    State { qubits: sim.qubits, bits: sim.bits, phase: sim.phase,
        stats: (sim.stats.clifford_gates, sim.stats.toffoli_gates),
        random: (sim.xof.state, sim.xof.reads, sim.xof.bytes) }
}
fn audited(ops: &[Op], entries: &[C162Audit], w: &Input) -> (State, usize, usize, u64, usize) {
    let mut rng = Bytes { state: w.seed, reads: 0, bytes: 0 };
    let mut sim = Audited::new(WIDTH, BITS, &mut rng);
    sim.qubits.clone_from_slice(&w.qubits); sim.bits.clone_from_slice(&w.bits); sim.phase = w.phase;
    sim.c162_audit = entries.to_vec(); sim.c162_valid_mask = w.valid;
    sim.apply_iter(ops.iter());
    let checked = sim.c162_checked;
    let bad = sim.c162_counts.values().map(|x| x.bad_operations).sum();
    let mask = sim.c162_counts.values().fold(0, |m,x| m | x.bad_lane_mask);
    let unchecked = sim.c162_counts.values().map(|x| x.unchecked_operations).sum();
    let state = State { qubits: sim.qubits, bits: sim.bits, phase: sim.phase,
        stats: (sim.stats.clifford_gates, sim.stats.toffoli_gates),
        random: (sim.xof.state, sim.xof.reads, sim.xof.bytes) };
    (state, checked, bad, mask, unchecked)
}
fn op_hash(ops: &[Op]) -> String {
    let mut h = Keccak256::new();
    for o in ops {
        h.update((o.kind as u32).to_le_bytes());
        for x in [o.q_control2.0, o.q_control1.0, o.q_target.0, o.c_target.0, o.c_condition.0, o.r_target.0] { h.update(x.to_le_bytes()); }
    }
    format!("{:x}", h.finalize())
}

#[test]
fn pristine_audited_differential() {
    let (ops, entries) = stream(); let mut inputs = Keccak256::new(); let mut plays = 0;
    for case in 0..CASES {
        let w = input(case);
        for x in w.qubits.iter().chain(&w.bits).copied().chain([w.phase,w.seed,w.valid]) { inputs.update(x.to_le_bytes()); }
        let reference = pure(&ops, &w); plays += 1;
        let (without, checked, bad, mask, unchecked) = audited(&ops, &[], &w); plays += 1;
        assert_eq!((checked,bad,mask,unchecked),(0,0,0,0)); assert_eq!(reference, without);
        let (with, checked, bad, mask, unchecked) = audited(&ops, &entries, &w); plays += 1;
        assert_eq!((checked,bad,mask,unchecked),(2,0,0,0)); assert_eq!(reference, with);
        assert_eq!((reference.random.1,reference.random.2),(2,16));
    }
    // A real invalid compute/erase image must be diagnosed without changing
    // the native word, classical, phase, gate-statistic or RNG behavior.
    let mut bad_input = input(0); bad_input.qubits[4] = u64::MAX;
    bad_input.bits[1] = u64::MAX; bad_input.bits[2] = u64::MAX; bad_input.bits[3] = u64::MAX;
    let reference = pure(&ops, &bad_input); plays += 1;
    let (bad_state, checked, bad, mask, unchecked) = audited(&ops, &entries, &bad_input); plays += 1;
    assert_eq!(reference,bad_state); assert_eq!((checked,bad,mask,unchecked),(2,2,u64::MAX,0));
    let mut wrong_shape = entries.clone(); wrong_shape[1].correction.clear();
    assert!(c162_validate_shape(&ops,&wrong_shape).is_err());
    // Independent comparator falsifiers: phase-only and unused-wire-only.
    let mut phase_ops = ops.clone(); phase_ops.push(Op { kind: K::Neg, ..Op::empty() });
    let phase_bad = pure(&phase_ops, &bad_input); plays += 1;
    assert_eq!(phase_bad.qubits,reference.qubits); assert_eq!(phase_bad.bits,reference.bits);
    assert_eq!(phase_bad.stats,reference.stats); assert_eq!(phase_bad.random,reference.random);
    assert_eq!(phase_bad.phase,reference.phase ^ u64::MAX);
    let mut donor_ops = ops.clone(); donor_ops.push(Op { kind: K::X, q_target: QubitId(7), ..Op::empty() });
    let donor_bad = pure(&donor_ops, &bad_input); plays += 1;
    assert_eq!(donor_bad.phase,reference.phase); assert_eq!(donor_bad.bits,reference.bits);
    assert_eq!(donor_bad.stats,reference.stats); assert_eq!(donor_bad.random,reference.random);
    for q in 0..WIDTH { assert_eq!(donor_bad.qubits[q],reference.qubits[q] ^ if q==7 {u64::MAX} else {0}); }
    assert_eq!(plays,388);
    println!("HARNESS_ISOLATION_COMPLETE tests=1 fixed_packed_cases=128 fixture_lanes=8192 physical_qubits=8 classical_bits=8 operation_families=18 normal_comparisons=256 controls=4 simulator_plays={plays} replayed_lanes={} normal_ops=25 normal_rng_reads=2 normal_rng_bytes=16 operation_hash={} input_hash={:x} whole_stream_identity=false submit=CLOSED",plays*64,op_hash(&ops),inputs.finalize());
}
