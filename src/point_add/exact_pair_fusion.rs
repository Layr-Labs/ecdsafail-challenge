//! Exact, zero-ancilla factoring of adjacent Toffoli pairs.
//!
//! This is a research-only final-stream pass. It makes no assumptions about
//! zero ancillas, immutable wire IDs, bounded Boolean support, or input data.
//! Each accepted pair is a complete identity on arbitrary computational-basis
//! states, hence on arbitrary coherent states by linearity. There are no
//! measurements or phase gates in a replacement.
//!
//! First identity: a, b, t, u all distinct. Second: a, b, c, t all distinct.
//!   CCX(a,b;t); CCX(a,b;u) = CX(t;u); CCX(a,b;t); CX(t;u)
//!   CCX(a,b;t); CCX(a,c;t) = CX(b;c); CCX(a,c;t); CX(b;c)
//! Equal pairs cancel. Every replacement gate has the original classical
//! condition. The condition cannot change inside an adjacent pair. We reject
//! every pair inside a condition stack, even though these identities also hold
//! for a fixed outer condition. No operation is commuted across another one.

use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT, NO_REG};

/// Explicit source-level research switch, enabled here for remote evaluation.
/// Set false to reproduce the inherited stream without this candidate pass.
/// The pinned builder clears inherited environment and the benchmark may use
/// sudo, so an environment flag would not be a reliable isolated opt-in.
pub(super) const ENABLED: bool = true;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Counts {
    fanout_pairs: usize,
    shared_target_pairs: usize,
    cancelled_pairs: usize,
    invalid_scope: bool,
}

impl Counts {
    fn ccx_removed(self) -> usize {
        self.fanout_pairs + self.shared_target_pairs + 2 * self.cancelled_pairs
    }

    fn cx_added(self) -> usize {
        2 * (self.fanout_pairs + self.shared_target_pairs)
    }
}

/// Only ordinary well-formed CCX gates, not future extensions or annotations.
fn controls(op: &Op) -> Option<[QubitId; 2]> {
    if op.kind != K::CCX
        || op.c_target != NO_BIT
        || op.r_target != NO_REG
        || op.q_target == NO_QUBIT
        || op.q_control1 == NO_QUBIT
        || op.q_control2 == NO_QUBIT
        || op.q_control1 == op.q_control2
        || op.q_target == op.q_control1
        || op.q_target == op.q_control2
    {
        return None;
    }
    let mut result = [op.q_control1, op.q_control2];
    result.sort_unstable();
    Some(result)
}

fn cx(control: QubitId, target: QubitId, original: &Op) -> Op {
    let mut result = Op::empty();
    result.kind = K::CX;
    result.q_control1 = control;
    result.q_target = target;
    result.c_condition = original.c_condition;
    result
}

/// A successful match emits a complete replacement, never a partial edit.
fn pair(first: Op, second: Op, out: &mut Vec<Op>, counts: &mut Counts) -> bool {
    let (Some(a), Some(b)) = (controls(&first), controls(&second)) else {
        return false;
    };
    if first.c_condition != second.c_condition {
        return false;
    }
    if a == b {
        if first.q_target == second.q_target {
            counts.cancelled_pairs += 1;
        } else {
            // (t,u) -> (t XOR ab, u XOR ab), even if both targets are dirty.
            let helper = cx(first.q_target, second.q_target, &first);
            out.extend([helper, first, helper]);
            counts.fanout_pairs += 1;
        }
        return true;
    }
    if first.q_target == second.q_target {
        // Different two-element control sets may share exactly one control.
        if let Some(&shared) = a.iter().find(|q| b.contains(q)) {
            let left = *a.iter().find(|&&q| q != shared).unwrap();
            let right = *b.iter().find(|&&q| q != shared).unwrap();
            // Conjugating by CX(left;right) factors a*b XOR a*c.
            let helper = cx(left, right, &first);
            out.extend([helper, second, helper]);
            counts.shared_target_pairs += 1;
            return true;
        }
    }
    false
}

fn rewrite(ops: Vec<Op>) -> (Vec<Op>, Counts) {
    let mut out = Vec::with_capacity(ops.len());
    let mut counts = Counts::default();
    let mut depth = 0usize;
    let mut i = 0;
    while i < ops.len() {
        let op = ops[i];
        match op.kind {
            K::PushCondition => depth += 1,
            K::PopCondition => {
                let Some(parent) = depth.checked_sub(1) else {
                    // Do not reinterpret an ill-formed scope, even partly.
                    return (ops, Counts { invalid_scope: true, ..Counts::default() });
                };
                depth = parent;
            }
            K::CCX if depth == 0 && i + 1 < ops.len() => {
                if pair(op, ops[i + 1], &mut out, &mut counts) {
                    i += 2;
                    continue;
                }
            }
            _ => {}
        }
        out.push(op);
        i += 1;
    }
    if depth != 0 {
        return (ops, Counts { invalid_scope: true, ..Counts::default() });
    }
    (out, counts)
}

pub(super) fn run(ops: Vec<Op>) -> Vec<Op> {
    let (out, counts) = rewrite(ops);
    eprintln!(
        "EXACT_PAIR_FUSION fanout_pairs={} shared_target_pairs={} cancelled_pairs={} ccx_removed={} cx_added={} quantum_scratch_added=0 invalid_scope={}",
        counts.fanout_pairs,
        counts.shared_target_pairs,
        counts.cancelled_pairs,
        counts.ccx_removed(),
        counts.cx_added(),
        counts.invalid_scope,
    );
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{BitId, RegisterId};

    fn ccx(a: u64, b: u64, target: u64, condition: Option<u64>) -> Op {
        let mut op = Op::empty();
        op.kind = K::CCX;
        op.q_control1 = QubitId(a);
        op.q_control2 = QubitId(b);
        op.q_target = QubitId(target);
        op.c_condition = condition.map_or(NO_BIT, BitId);
        op
    }

    fn apply(ops: &[Op], mut state: u64, condition: bool) -> u64 {
        for op in ops {
            op.validate();
            if op.c_condition != NO_BIT && !condition {
                continue;
            }
            let bit = |q: QubitId| (state >> q.0) & 1;
            let toggle = match op.kind {
                K::CX => bit(op.q_control1),
                K::CCX => bit(op.q_control1) & bit(op.q_control2),
                _ => panic!("unexpected gate in Boolean test"),
            };
            state ^= toggle << op.q_target.0;
        }
        state
    }

    fn assert_equivalent(input: Vec<Op>, expected: Counts) {
        let (output, counts) = rewrite(input.clone());
        assert_eq!(counts, expected);
        for state in 0..16 {
            for condition in [false, true] {
                assert_eq!(apply(&input, state, condition), apply(&output, state, condition));
            }
        }
        assert_eq!(
            input.iter().filter(|op| op.kind == K::CCX).count()
                - output.iter().filter(|op| op.kind == K::CCX).count(),
            counts.ccx_removed(),
        );
        assert_eq!(output.iter().filter(|op| op.kind == K::CX).count(), counts.cx_added());
    }

    #[test]
    fn both_identities_all_wire_permutations_and_conditions() {
        for a in 0..4 {
            for b in 0..4 {
                for t in 0..4 {
                    for u in 0..4 {
                        let mut ids = [a, b, t, u];
                        ids.sort_unstable();
                        if ids != [0, 1, 2, 3] { continue; }
                        for condition in [None, Some(0)] {
                            for reverse_first in [false, true] {
                                for reverse_second in [false, true] {
                                    let first = if reverse_first { ccx(b, a, t, condition) } else { ccx(a, b, t, condition) };
                                    let fanout = if reverse_second { ccx(b, a, u, condition) } else { ccx(a, b, u, condition) };
                                    assert_equivalent(vec![first, fanout], Counts { fanout_pairs: 1, ..Counts::default() });
                                    let factored = if reverse_second { ccx(u, a, t, condition) } else { ccx(a, u, t, condition) };
                                    assert_equivalent(vec![first, factored], Counts { shared_target_pairs: 1, ..Counts::default() });
                                    let same = if reverse_second { ccx(b, a, t, condition) } else { ccx(a, b, t, condition) };
                                    assert_equivalent(vec![first, same], Counts { cancelled_pairs: 1, ..Counts::default() });
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn refuses_different_conditions_or_no_common_factor() {
        for input in [
            vec![ccx(0, 1, 2, None), ccx(0, 1, 3, Some(0))],
            vec![ccx(0, 1, 2, Some(0)), ccx(0, 1, 3, Some(1))],
            vec![ccx(0, 1, 4, None), ccx(2, 3, 4, None)],
            vec![ccx(0, 1, 2, None), ccx(0, 2, 3, None)],
        ] {
            assert_eq!(rewrite(input.clone()), (input, Counts::default()));
        }
    }

    #[test]
    fn every_non_ccx_operation_is_a_boundary() {
        for kind in [K::Neg, K::Register, K::AppendToRegister, K::BitInvert,
            K::BitStore0, K::BitStore1, K::X, K::Z, K::CX, K::CZ,
            K::Swap, K::R, K::Hmr, K::CCZ, K::DebugPrint] {
            let mut boundary = Op::empty();
            boundary.kind = kind;
            let input = vec![ccx(0, 1, 2, None), boundary, ccx(0, 1, 3, None)];
            assert_eq!(rewrite(input.clone()), (input, Counts::default()));
        }
    }

    #[test]
    fn condition_scopes_and_malformed_scopes_are_not_rewritten() {
        let mut push = Op::empty();
        push.kind = K::PushCondition;
        push.c_condition = BitId(0);
        let mut pop = Op::empty();
        pop.kind = K::PopCondition;
        let a = ccx(0, 1, 2, None);
        let b = ccx(0, 1, 3, None);
        for input in [vec![push, a, b, pop], vec![push, push, a, b, pop, pop], vec![a, push, pop, b]] {
            assert_eq!(rewrite(input.clone()), (input, Counts::default()));
        }
        for input in [vec![a, b, pop], vec![a, b, push], vec![pop, a, b]] {
            assert_eq!(rewrite(input.clone()), (input, Counts { invalid_scope: true, ..Counts::default() }));
        }
        // Rewriting can resume after a complete scope without crossing it.
        let (output, counts) = rewrite(vec![push, pop, a, b]);
        assert_eq!(&output[..2], &[push, pop]);
        assert_eq!(counts.fanout_pairs, 1);
    }

    #[test]
    fn malformed_or_aliased_operands_are_not_rewritten() {
        let valid = ccx(0, 1, 2, None);
        let mut invalid = [valid; 8];
        invalid[0].q_control1 = NO_QUBIT;
        invalid[1].q_control2 = NO_QUBIT;
        invalid[2].q_target = NO_QUBIT;
        invalid[3].q_control2 = invalid[3].q_control1;
        invalid[4].q_target = invalid[4].q_control1;
        invalid[5].q_target = invalid[5].q_control2;
        invalid[6].c_target = BitId(0);
        invalid[7].r_target = RegisterId(0);
        for bad in invalid {
            for input in [vec![bad, valid], vec![valid, bad]] {
                assert_eq!(rewrite(input.clone()), (input, Counts::default()));
            }
        }
    }

    #[test]
    fn empty_single_and_greedy_sequences() {
        for input in [vec![], vec![ccx(0, 1, 2, None)]] {
            assert_eq!(rewrite(input.clone()), (input, Counts::default()));
        }
        let gate = ccx(0, 1, 2, None);
        assert_equivalent(vec![gate; 3], Counts { cancelled_pairs: 1, ..Counts::default() });
        assert_equivalent(vec![gate; 4], Counts { cancelled_pairs: 2, ..Counts::default() });
    }
}
