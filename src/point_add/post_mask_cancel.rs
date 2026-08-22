//! Post-build exact commuting self-inverse gate cancellation.
//!
//! Finds `U ... U` pairs where U in {X, Z, CX, CZ, Swap, CCX, CCZ, BitInvert}
//! whose intervening window contains no PushCondition/PopCondition and no
//! operation touching the support wires of U, and removes both gates.
//! Because U^2 = I and disjoint gates commute, this rewrite is a strict
//! mathematical identity on the entire Hilbert state.

use crate::circuit::{Op, OperationType, NO_BIT, NO_QUBIT};
use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Key {
    X { t: u64, cond: u64 },
    Z { t: u64, cond: u64 },
    BitInvert { t: u64, cond: u64 },
    CX { c: u64, t: u64, cond: u64 },
    CZ { q1: u64, q2: u64, cond: u64 },
    Swap { q1: u64, q2: u64, cond: u64 },
    CCX { c1: u64, c2: u64, t: u64, cond: u64 },
    CCZ { q1: u64, q2: u64, q3: u64, cond: u64 },
}

fn op_key(op: &Op) -> Option<Key> {
    let cond = op.c_condition.0;
    match op.kind {
        OperationType::X if op.q_target != NO_QUBIT => Some(Key::X {
            t: op.q_target.0,
            cond,
        }),
        OperationType::Z if op.q_target != NO_QUBIT => Some(Key::Z {
            t: op.q_target.0,
            cond,
        }),
        OperationType::BitInvert if op.c_target != NO_BIT => Some(Key::BitInvert {
            t: op.c_target.0,
            cond,
        }),
        OperationType::CX if op.q_control1 != NO_QUBIT && op.q_target != NO_QUBIT => {
            Some(Key::CX {
                c: op.q_control1.0,
                t: op.q_target.0,
                cond,
            })
        }
        OperationType::CZ if op.q_control1 != NO_QUBIT && op.q_target != NO_QUBIT => {
            let (q1, q2) = if op.q_control1.0 <= op.q_target.0 {
                (op.q_control1.0, op.q_target.0)
            } else {
                (op.q_target.0, op.q_control1.0)
            };
            Some(Key::CZ { q1, q2, cond })
        }
        OperationType::Swap if op.q_control1 != NO_QUBIT && op.q_target != NO_QUBIT => {
            let (q1, q2) = if op.q_control1.0 <= op.q_target.0 {
                (op.q_control1.0, op.q_target.0)
            } else {
                (op.q_target.0, op.q_control1.0)
            };
            Some(Key::Swap { q1, q2, cond })
        }
        OperationType::CCX
            if op.q_control1 != NO_QUBIT
                && op.q_control2 != NO_QUBIT
                && op.q_target != NO_QUBIT =>
        {
            let (c1, c2) = if op.q_control1.0 <= op.q_control2.0 {
                (op.q_control1.0, op.q_control2.0)
            } else {
                (op.q_control2.0, op.q_control1.0)
            };
            Some(Key::CCX {
                c1,
                c2,
                t: op.q_target.0,
                cond,
            })
        }
        OperationType::CCZ
            if op.q_control1 != NO_QUBIT
                && op.q_control2 != NO_QUBIT
                && op.q_target != NO_QUBIT =>
        {
            let mut qs = [op.q_control1.0, op.q_control2.0, op.q_target.0];
            qs.sort_unstable();
            Some(Key::CCZ {
                q1: qs[0],
                q2: qs[1],
                q3: qs[2],
                cond,
            })
        }
        _ => None,
    }
}

fn touches(op: &Op, key: &Key) -> bool {
    let qc2 = op.q_control2.0;
    let qc1 = op.q_control1.0;
    let qt = op.q_target.0;
    let ct = op.c_target.0;
    let ccond = op.c_condition.0;

    let touches_qubit = |q: u64| q == qc2 || q == qc1 || q == qt;
    let touches_bit = |b: u64| b == ct || b == ccond;
    let no_bit = NO_BIT.0;

    match *key {
        Key::X { t, cond } | Key::Z { t, cond } => touches_qubit(t) || (cond != no_bit && touches_bit(cond)),
        Key::BitInvert { t, cond } => touches_bit(t) || (cond != no_bit && touches_bit(cond)),
        Key::CX { c, t, cond } => touches_qubit(c) || touches_qubit(t) || (cond != no_bit && touches_bit(cond)),
        Key::CZ { q1, q2, cond } | Key::Swap { q1, q2, cond } => {
            touches_qubit(q1) || touches_qubit(q2) || (cond != no_bit && touches_bit(cond))
        }
        Key::CCX { c1, c2, t, cond } => {
            touches_qubit(c1) || touches_qubit(c2) || touches_qubit(t) || (cond != no_bit && touches_bit(cond))
        }
        Key::CCZ { q1, q2, q3, cond } => {
            touches_qubit(q1) || touches_qubit(q2) || touches_qubit(q3) || (cond != no_bit && touches_bit(cond))
        }
    }
}

pub(crate) fn apply_post_mask_cancel(ops: Vec<Op>) -> Vec<Op> {
    let n = ops.len();
    if n <= 96 {
        return ops;
    }
    let scan_len = n - 96;
    let mut cancelled = vec![false; n];
    let mut pending: HashMap<Key, usize> = HashMap::new();

    for i in 0..scan_len {
        let op = &ops[i];
        match op.kind {
            OperationType::PushCondition | OperationType::PopCondition => {
                pending.clear();
            }
            _ => {
                let mut inserted: Option<Key> = None;
                if let Some(k) = op_key(op) {
                    if let Some(first) = pending.remove(&k) {
                        cancelled[first] = true;
                        cancelled[i] = true;
                    } else {
                        inserted = Some(k);
                        pending.insert(k, i);
                    }
                }
                if pending.is_empty() {
                    continue;
                }
                let touched_keys: Vec<Key> = pending
                    .keys()
                    .copied()
                    .filter(|k| Some(*k) != inserted && touches(op, k))
                    .collect();
                for k in touched_keys {
                    pending.remove(&k);
                }
            }
        }
    }

    let removed = cancelled.iter().filter(|c| **c).count();
    if removed == 0 {
        return ops;
    }
    let out: Vec<Op> = ops
        .into_iter()
        .zip(cancelled)
        .filter(|(_, dead)| !dead)
        .map(|(op, _)| op)
        .collect();
    eprintln!(
        "[post-cancel] cancelled {} commutative gate pairs, removed {} ops ({} -> {})",
        removed / 2,
        removed,
        n,
        out.len()
    );
    out
}
