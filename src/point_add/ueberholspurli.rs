//! Exact local Toffoli merges whose intervening operations are wire-disjoint.

use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};

const MAX_GAP: usize = 512;

fn operands(op: &Op) -> [QubitId; 3] {
    [op.q_control1, op.q_control2, op.q_target]
}

fn uses_any(op: &Op, wires: &[QubitId]) -> bool {
    operands(op)
        .iter()
        .any(|q| *q != NO_QUBIT && wires.contains(q))
}

#[derive(Clone, Copy)]
enum Middle {
    X(QubitId),
    Cx {
        control: QubitId,
        target: QubitId,
    },
}

fn middle(op: &Op, a: QubitId, b: QubitId, t: QubitId) -> Option<Middle> {
    if op.c_condition != NO_BIT {
        return None;
    }
    match op.kind {
        K::X if op.q_target == a || op.q_target == b => Some(Middle::X(op.q_target)),
        K::CX if op.q_target == a || op.q_target == b => {
            let d = op.q_control1;
            let other = if op.q_target == a { b } else { a };
            if d != NO_QUBIT && d != a && d != b && d != t && d != other {
                Some(Middle::Cx {
                    control: d,
                    target: op.q_target,
                })
            } else {
                None
            }
        }
        _ => None,
    }
}

fn sandwich(op: &[Op], i: usize, max_gap: usize) -> Option<(usize, Vec<Op>)> {
    let first = op[i];
    if first.kind != K::CCX || first.c_condition != NO_BIT {
        return None;
    }
    let (a, b, t) = (first.q_control1, first.q_control2, first.q_target);
    let wires = [a, b, t];
    let mut found_middle: Option<Middle> = None;
    let end = (i + max_gap).min(op.len().saturating_sub(1));
    for j in i + 1..=end {
        let here = op[j];
        if here == first {
            let m = found_middle?;
            let mut replacement = op[i + 1..j].to_vec();
            match m {
                Middle::X(target) => {
                    let other = if target == a { b } else { a };
                    replacement.push(Op {
                        kind: K::CX,
                        q_control1: other,
                        q_target: t,
                        ..Op::empty()
                    });
                }
                Middle::Cx { control, target } => {
                    let other = if target == a { b } else { a };
                    replacement.push(Op {
                        kind: K::CCX,
                        q_control1: control,
                        q_control2: other,
                        q_target: t,
                        ..Op::empty()
                    });
                }
            }
            return Some((j, replacement));
        }
        if here.c_condition != NO_BIT {
            break;
        }
        if let Some(m) = middle(&here, a, b, t) {
            if found_middle.is_some() {
                break;
            }
            found_middle = Some(m);
        } else if uses_any(&here, &wires) {
            break;
        }
    }
    None
}

fn pairmerge(op: &[Op], i: usize, max_gap: usize) -> Option<(usize, Vec<Op>)> {
    let first = op[i];
    if first.kind != K::CCX || first.c_condition != NO_BIT {
        return None;
    }
    let a = first.q_control1;
    let b = first.q_control2;
    let t = first.q_target;
    let end = (i + max_gap).min(op.len().saturating_sub(1));
    for j in i + 1..=end {
        let second = op[j];
        if second.kind != K::CCX || second.c_condition != NO_BIT || second.q_target != t {
            continue;
        }
        let (common, other) = if second.q_control1 == a {
            (a, second.q_control2)
        } else if second.q_control2 == a {
            (a, second.q_control1)
        } else if second.q_control1 == b {
            (b, second.q_control2)
        } else if second.q_control2 == b {
            (b, second.q_control1)
        } else {
            continue;
        };
        let real_other = if common == a { b } else { a };
        let boundary = [a, b, t, other];
        if other == real_other
            || other == t
            || !op[i + 1..j]
                .iter()
                .all(|m| m.c_condition == NO_BIT && !uses_any(m, &boundary))
        {
            continue;
        }
        let mut replacement = op[i + 1..j].to_vec();
        replacement.push(Op {
            kind: K::CX,
            q_control1: other,
            q_target: real_other,
            ..Op::empty()
        });
        replacement.push(first);
        replacement.push(Op {
            kind: K::CX,
            q_control1: other,
            q_target: real_other,
            ..Op::empty()
        });
        return Some((j, replacement));
    }
    None
}

pub(crate) fn apply(mut ops: Vec<Op>) -> Vec<Op> {
    let mut total_sandwich = 0usize;
    let mut total_pair = 0usize;
    for pass in 1..=8 {
        let mut out = Vec::with_capacity(ops.len());
        let mut sandwich_count = 0usize;
        let mut pair_count = 0usize;
        let mut i = 0usize;
        while i < ops.len() {
            if let Some((end, replacement)) = sandwich(&ops, i, MAX_GAP) {
                out.extend(replacement);
                i = end + 1;
                sandwich_count += 1;
            } else if let Some((end, replacement)) = pairmerge(&ops, i, MAX_GAP) {
                out.extend(replacement);
                i = end + 1;
                pair_count += 1;
            } else {
                out.push(ops[i]);
                i += 1;
            }
        }
        eprintln!(
            "UEBERHOL pass={pass} sandwich={sandwich_count} pairmerge={pair_count} ops {} -> {}",
            ops.len(),
            out.len()
        );
        total_sandwich += sandwich_count;
        total_pair += pair_count;
        let changed = sandwich_count + pair_count > 0;
        ops = out;
        if !changed {
            break;
        }
    }
    eprintln!(
        "UEBERHOL_TOTAL sandwich={total_sandwich} pairmerge={total_pair}"
    );
    ops
}
