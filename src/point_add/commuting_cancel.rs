//! Exact deletion of identical gates across overlapping commuting operations.
//! Port of submit-q1010-n599's X-family/diagonal pass, with a packed deletion
//! mask and barrier-local key map. No gate, measurement or classical write is
//! moved or synthesized. Classical and nonunitary barriers are unchanged.
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
use std::collections::HashMap;

const NONE: usize = usize::MAX;
type Key = (u8, u64, u64, u64);

#[derive(Default, Debug)]
pub(super) struct Stats {
    pub input_ops: usize,
    pub output_ops: usize,
    pub removed_ops: usize,
    pub toffoli_pairs_unconditional: usize,
    pub toffoli_pairs_conditioned: usize,
    pub other_pairs: usize,
    pub barriers: usize,
    pub max_condition_depth: usize,
    pub max_keys: usize,
    pub max_key_capacity: usize,
    pub deletion_words: usize,
    pub deletion_bytes: usize,
    pub tracker_bytes: usize,
}
struct Deleted(Vec<u64>);
impl Deleted {
    fn new(n: usize) -> Self {
        Self(vec![0; n.div_ceil(64)])
    }
    fn get(&self, index: usize) -> bool {
        (self.0[index / 64] >> (index % 64)) & 1 != 0
    }
    fn mark(&mut self, index: usize) {
        self.0[index / 64] |= 1u64 << (index % 64);
    }
}
fn barrier(op: &Op) -> bool {
    op.c_condition != NO_BIT
        || matches!(
            op.kind,
            K::Neg
                | K::Register
                | K::AppendToRegister
                | K::BitInvert
                | K::BitStore0
                | K::BitStore1
                | K::R
                | K::Hmr
                | K::PushCondition
                | K::PopCondition
                | K::DebugPrint
        )
}
fn qubits(op: &Op) -> [QubitId; 3] {
    [op.q_control2, op.q_control1, op.q_target]
}
fn key(op: &Op) -> Key {
    (
        op.kind as u8,
        op.q_control2.0,
        op.q_control1.0,
        op.q_target.0,
    )
}

pub(super) fn cancel(ops: &mut Vec<Op>) -> Stats {
    let nq = ops
        .iter()
        .flat_map(qubits)
        .filter(|&q| q != NO_QUBIT)
        .map(|q| usize::try_from(q.0).expect("qubit index fits usize"))
        .max()
        .map_or(0, |q| q.checked_add(1).expect("qubit extent overflow"));
    let mut last_write = vec![NONE; nq];
    let mut last_control_read = vec![NONE; nq];
    let mut last_phase_touch = vec![NONE; nq];
    let mut last_swap = vec![NONE; nq];
    let mut last_same = HashMap::<Key, usize>::new();
    let mut deleted = Deleted::new(ops.len());
    let mut stats = Stats {
        input_ops: ops.len(),
        deletion_words: deleted.0.len(),
        deletion_bytes: deleted.0.len() * std::mem::size_of::<u64>(),
        tracker_bytes: 4 * nq * std::mem::size_of::<usize>(),
        ..Stats::default()
    };
    let mut depth = 0usize;
    for read in 0..ops.len() {
        let op = ops[read];
        match op.kind {
            K::PushCondition => {
                depth += 1;
                stats.max_condition_depth = stats.max_condition_depth.max(depth);
            }
            K::PopCondition => {
                depth = depth.checked_sub(1).expect("unbalanced condition pop");
            }
            _ => {}
        }
        if barrier(&op) {
            // No previous key can cross this barrier. Keeping stale entries
            // would only grow memory without adding any legal matches.
            last_same.clear();
            stats.barriers += 1;
            continue;
        }
        let controls: Option<&[QubitId]> = match op.kind {
            K::X => Some(&[]),
            K::CX => Some(std::slice::from_ref(&op.q_control1)),
            K::CCX => Some(&[op.q_control2, op.q_control1]),
            _ => None,
        };
        let diagonal: Option<&[QubitId]> = match op.kind {
            K::Z => Some(std::slice::from_ref(&op.q_target)),
            K::CZ => Some(&[op.q_control1, op.q_target]),
            K::CCZ => Some(&[op.q_control2, op.q_control1, op.q_target]),
            _ => None,
        };
        if controls.is_some() || diagonal.is_some() {
            let gate_key = key(&op);
            if let Some(&previous) = last_same.get(&gate_key) {
                debug_assert!(!deleted.get(previous));
                let blocker = if let Some(controls) = controls {
                    controls
                        .iter()
                        .copied()
                        .map(|q| last_write[q.0 as usize])
                        .chain(std::iter::once(last_control_read[op.q_target.0 as usize]))
                        .chain(std::iter::once(last_phase_touch[op.q_target.0 as usize]))
                        .chain(
                            qubits(&op)
                                .into_iter()
                                .filter(|&q| q != NO_QUBIT)
                                .map(|q| last_swap[q.0 as usize]),
                        )
                        .filter(|&i| i != NONE)
                        .max()
                } else {
                    diagonal
                        .expect("selected commuting family")
                        .iter()
                        .copied()
                        .flat_map(|q| [last_write[q.0 as usize], last_swap[q.0 as usize]])
                        .filter(|&i| i != NONE)
                        .max()
                };
                if blocker.is_none_or(|i| i < previous) {
                    deleted.mark(previous);
                    deleted.mark(read);
                    last_same.remove(&gate_key);
                    stats.removed_ops += 2;
                    if matches!(op.kind, K::CCX | K::CCZ) {
                        if depth == 0 {
                            stats.toffoli_pairs_unconditional += 1;
                        } else {
                            stats.toffoli_pairs_conditioned += 1;
                        }
                    } else {
                        stats.other_pairs += 1;
                    }
                    // Histories of the deleted first member may remain. They
                    // can conservatively block a later match, never create one.
                    continue;
                }
            }
            last_same.insert(gate_key, read);
            stats.max_keys = stats.max_keys.max(last_same.len());
            stats.max_key_capacity = stats.max_key_capacity.max(last_same.capacity());
        }
        match op.kind {
            K::X => last_write[op.q_target.0 as usize] = read,
            K::CX => {
                last_write[op.q_target.0 as usize] = read;
                last_control_read[op.q_control1.0 as usize] = read;
            }
            K::CCX => {
                last_write[op.q_target.0 as usize] = read;
                last_control_read[op.q_control1.0 as usize] = read;
                last_control_read[op.q_control2.0 as usize] = read;
            }
            K::Z => last_phase_touch[op.q_target.0 as usize] = read,
            K::CZ => {
                last_phase_touch[op.q_target.0 as usize] = read;
                last_phase_touch[op.q_control1.0 as usize] = read;
            }
            K::CCZ => {
                last_phase_touch[op.q_target.0 as usize] = read;
                last_phase_touch[op.q_control1.0 as usize] = read;
                last_phase_touch[op.q_control2.0 as usize] = read;
            }
            K::Swap => {
                for q in [op.q_control1, op.q_target] {
                    last_write[q.0 as usize] = read;
                    last_swap[q.0 as usize] = read;
                }
            }
            _ => {}
        }
    }
    assert_eq!(depth, 0, "unbalanced condition stack at end");
    let mut read = 0;
    // Stable in-place compaction. Never clone, rebuild or shrink the Op vector.
    ops.retain(|_| {
        let keep = !deleted.get(read);
        read += 1;
        keep
    });
    stats.output_ops = ops.len();
    assert_eq!(stats.output_ops + stats.removed_ops, stats.input_ops);
    assert_eq!(
        stats.removed_ops,
        2 * (stats.toffoli_pairs_unconditional
            + stats.toffoli_pairs_conditioned
            + stats.other_pairs)
    );
    stats
}

#[cfg(test)]
#[path = "commuting_cancel_tests.rs"]
mod tests;
