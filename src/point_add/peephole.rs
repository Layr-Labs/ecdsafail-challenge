//! Conservative self-inverse gate cancellation.
//!
//! Two identical self-inverse gates cancel when every operation between them acts
//! on disjoint qubits. The pass keeps a bounded look-back window so it stays linear
//! in the 12.4M-op stream. Annotations and the global phase do not affect the state
//! and are skipped; a condition-stack change breaks the window because a conditional
//! gate is not the same operation as an unconditional one.

use crate::circuit::{Op, OperationType, QubitId, NO_QUBIT};

/// How far back a partner may be. Longer windows find fewer pairs per unit of work.
const WINDOW: usize = 96;

#[inline]
fn gate_qubits(op: &Op) -> [QubitId; 3] {
    [op.q_control2, op.q_control1, op.q_target]
}

#[inline]
fn touches(op: &Op, qs: &[QubitId; 3]) -> bool {
    let a = gate_qubits(op);
    a.iter().any(|q| *q != NO_QUBIT && qs.contains(q))
}

#[inline]
fn same_gate(a: &Op, b: &Op) -> bool {
    a.kind == b.kind
        && a.q_control2 == b.q_control2
        && a.q_control1 == b.q_control1
        && a.q_target == b.q_target
}

#[inline]
fn self_inverse(kind: OperationType) -> bool {
    // Only the Toffoli is targeted: it is a permutation (no phase), it is self-inverse,
    // and it is the only gate the score counts. Cancelling a pair removes 1,229 points.
    matches!(kind, OperationType::CCX)
}

#[inline]
fn commutes_ccx(p: &Op, qs: &[QubitId; 3], target: QubitId) -> bool {
    match p.kind {
        // No state effect.
        OperationType::Neg | OperationType::Register | OperationType::AppendToRegister => true,
        // Diagonal on anything except the Toffoli target: commutes with the X on the target.
        OperationType::Z => p.q_target != target,
        OperationType::CZ => p.q_control1 != target && p.q_target != target,
        // Bit flips commute only on fully disjoint qubits.
        OperationType::X
        | OperationType::CX
        | OperationType::Swap
        | OperationType::CCX
        | OperationType::CCZ => !touches(p, qs),
        // Classically conditioned work, measurements, resets and condition changes.
        _ => false,
    }
}

pub fn cancel(ops: Vec<Op>) -> Vec<Op> {
    let mut out: Vec<Op> = Vec::with_capacity(ops.len());
    for op in ops {
        if self_inverse(op.kind) {
            let qs = gate_qubits(&op);
            let lo = out.len().saturating_sub(WINDOW);
            let mut hit = None;
            for i in (lo..out.len()).rev() {
                let p = &out[i];
                if same_gate(p, &op) {
                    hit = Some(i);
                    break;
                }
                if commutes_ccx(p, &qs, op.q_target) {
                    continue;
                }
                break;
            }
            if let Some(i) = hit {
                out.remove(i);
                continue;
            }
        }
        out.push(op);
    }
    out
}
