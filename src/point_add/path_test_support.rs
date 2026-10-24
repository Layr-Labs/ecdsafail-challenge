//! Exercise local circuits with all inputs packed into simulator lanes.
use crate::circuit::{analyze_ops, BitId, Op, OperationType, QubitId, NO_BIT};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};
use sha3::Shake256;
use std::sync::{Mutex, MutexGuard};

pub fn lock() -> MutexGuard<'static, ()> {
    static LOCK: Mutex<()> = Mutex::new(());
    LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

pub fn ccx_count(ops: &[Op]) -> usize {
    ops.iter().filter(|op| op.kind == OperationType::CCX).count()
}

pub fn run(
    ops: &[Op],
    rows: &[Vec<u64>],
    inputs: &[Vec<QubitId>],
    expected: impl Fn(&[u64]) -> Vec<u64>,
    outputs: &[Vec<QubitId>],
) {
    let (nq, nb, _, _) = analyze_ops(ops.iter());
    for seed in [0u8, 91] {
        for batch in rows.chunks(64) {
            let mut shake = Shake256::default();
            shake.update(&[seed]);
            let mut reader = shake.finalize_xof();
            let mut simulator = Simulator::new(nq as usize, nb as usize + 1, &mut reader);
            for (lane, row) in batch.iter().enumerate() {
                for (register, value) in inputs.iter().zip(row) {
                    for (bit, q) in register.iter().enumerate() {
                        *simulator.qubit_mut(*q) |= ((value >> bit) & 1) << lane;
                    }
                }
            }
            let mask = if batch.len() == 64 { u64::MAX } else { (1 << batch.len()) - 1 };
            let mut condition = u64::MAX;
            let mut stack = Vec::new();
            for (i, op) in ops.iter().enumerate() {
                if op.kind == OperationType::PushCondition {
                    stack.push(condition);
                    condition &= simulator.bit(op.c_condition);
                    continue;
                }
                if op.kind == OperationType::PopCondition {
                    condition = stack.pop().expect("balanced condition stack");
                    continue;
                }
                let enabled = condition & if op.c_condition == NO_BIT {u64::MAX} else {simulator.bit(op.c_condition)};
                if op.kind == OperationType::R {
                    assert_eq!(simulator.qubit(op.q_target) & mask & enabled, 0, "dirty reset at op {i}");
                }
                let mut guarded = op.clone();
                guarded.c_condition = BitId(nb);
                *simulator.bit_mut(BitId(nb)) = enabled;
                simulator.apply_iter(std::iter::once(&guarded));
            }
            assert_eq!(simulator.phase & mask, 0, "phase seed={seed}");
            for (lane, row) in batch.iter().enumerate() {
                for (register, want) in outputs.iter().zip(expected(row)) {
                    let got = register.iter().enumerate().fold(0, |value, (bit, q)|
                        value | (((simulator.qubit(*q) >> lane) & 1) << bit));
                    assert_eq!(got, want, "input={row:?}; seed={seed}");
                }
            }
            for (q, value) in simulator.qubits.iter().enumerate() {
                if !outputs.iter().flatten().any(|wire| wire.0 == q as u64) {
                    assert_eq!(value & mask, 0, "dirty scratch q{q}");
                }
            }
        }
    }
}
