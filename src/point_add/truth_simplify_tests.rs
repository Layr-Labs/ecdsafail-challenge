use super::simplify;
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use crate::sim::Simulator;
use sha3::digest::XofReader;
use std::collections::BTreeSet;

fn op(
    k: OperationType,
    qt: Option<u64>,
    q1: Option<u64>,
    q2: Option<u64>,
    bt: Option<u64>,
    bc: Option<u64>,
) -> Op {
    let mut o = Op::empty();
    o.kind = k;
    if let Some(v) = qt {
        o.q_target = QubitId(v)
    }
    if let Some(v) = q1 {
        o.q_control1 = QubitId(v)
    }
    if let Some(v) = q2 {
        o.q_control2 = QubitId(v)
    }
    if let Some(v) = bt {
        o.c_target = BitId(v)
    }
    if let Some(v) = bc {
        o.c_condition = BitId(v)
    }
    o.validate();
    o
}
fn x(t: u64) -> Op {
    op(OperationType::X, Some(t), None, None, None, None)
}
fn cx(a: u64, t: u64) -> Op {
    op(OperationType::CX, Some(t), Some(a), None, None, None)
}
fn cc(a: u64, b: u64, t: u64) -> Op {
    op(OperationType::CCX, Some(t), Some(a), Some(b), None, None)
}
fn h(t: u64, c: u64, guard: Option<u64>) -> Op {
    op(OperationType::Hmr, Some(t), None, None, Some(c), guard)
}
fn reset(t: u64, g: Option<u64>) -> Op {
    op(OperationType::R, Some(t), None, None, None, g)
}
fn push(c: u64) -> Op {
    op(
        OperationType::PushCondition,
        None,
        None,
        None,
        None,
        Some(c),
    )
}
fn pop() -> Op {
    op(OperationType::PopCondition, None, None, None, None, None)
}
struct Fixture {
    name: &'static str,
    ops: Vec<Op>,
    qi: Vec<usize>,
    bi: Vec<usize>,
}
struct Words {
    words: Vec<u64>,
    pos: usize,
}
impl XofReader for Words {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8);
        out.copy_from_slice(&self.words[self.pos].to_le_bytes());
        self.pos += 1;
    }
}
fn run(
    ops: &[Op],
    qi: &[usize],
    bi: &[usize],
    input: usize,
    random: usize,
    nrandom: usize,
) -> (Vec<u64>, Vec<u64>, u64, usize) {
    let mut rng = Words {
        words: (0..nrandom)
            .map(|i| if random >> i & 1 != 0 { u64::MAX } else { 0 })
            .collect(),
        pos: 0,
    };
    let state = {
        let mut s = Simulator::new(40, 4, &mut rng);
        for (k, &q) in qi.iter().enumerate() {
            s.qubits[q] = if input >> k & 1 != 0 { u64::MAX } else { 0 };
        }
        for (k, &b) in bi.iter().enumerate() {
            s.bits[b] = if input >> (k + qi.len()) & 1 != 0 {
                u64::MAX
            } else {
                0
            };
        }
        s.apply_iter(ops.iter());
        (s.qubits, s.bits, s.phase)
    };
    (state.0, state.1, state.2, rng.pos)
}

fn with_abi(f: &Fixture) -> Vec<Op> {
    let mut ops = Vec::new();
    let mut register = Op::empty();
    register.kind = OperationType::Register;
    register.r_target = RegisterId(0);
    ops.push(register);
    for &q in &f.qi {
        let mut o = Op::empty();
        o.kind = OperationType::AppendToRegister;
        o.r_target = RegisterId(0);
        o.q_target = QubitId(q as u64);
        ops.push(o);
    }
    for &b in &f.bi {
        let mut o = Op::empty();
        o.kind = OperationType::AppendToRegister;
        o.r_target = RegisterId(0);
        o.c_target = BitId(b as u64);
        ops.push(o);
    }
    ops.extend(f.ops.iter().copied());
    ops
}

// Recognize only an ordered sequence of CCX keep/drop/CX/X edits. Every
// non-CCX must match verbatim; branching handles identical adjacent gates.
fn legal_ccx_edits(original: &[Op], rewritten: &[Op]) -> bool {
    fn visit(a: &[Op], b: &[Op], i: usize, j: usize, seen: &mut BTreeSet<(usize, usize)>) -> bool {
        if !seen.insert((i, j)) {
            return false;
        }
        if i == a.len() {
            return j == b.len();
        }
        if j < b.len() && a[i] == b[j] && visit(a, b, i + 1, j + 1, seen) {
            return true;
        }
        if a[i].kind != OperationType::CCX {
            return false;
        }
        if visit(a, b, i + 1, j, seen) {
            return true;
        }
        if j == b.len() {
            return false;
        }
        let mut replacement = Op::empty();
        replacement.q_target = a[i].q_target;
        replacement.c_condition = a[i].c_condition;
        replacement.kind = OperationType::X;
        if b[j] == replacement && visit(a, b, i + 1, j + 1, seen) {
            return true;
        }
        replacement.kind = OperationType::CX;
        for control in [a[i].q_control1, a[i].q_control2] {
            replacement.q_control1 = control;
            if b[j] == replacement && visit(a, b, i + 1, j + 1, seen) {
                return true;
            }
        }
        false
    }
    visit(original, rewritten, 0, 0, &mut BTreeSet::new())
}

fn compare(
    f: &Fixture,
    original: &[Op],
    rewritten: &[Op],
    inputs: impl Iterator<Item = usize>,
) -> (usize, usize) {
    let nr = original
        .iter()
        .filter(|o| matches!(o.kind, OperationType::R | OperationType::Hmr))
        .count();
    let (mut cases, mut failed) = (0, 0);
    for input in inputs {
        for random in 0..1usize << nr {
            cases += 1;
            if run(original, &f.qi, &f.bi, input, random, nr)
                != run(rewritten, &f.qi, &f.bi, input, random, nr)
            {
                failed += 1;
            }
        }
    }
    (cases, failed)
}

#[test]
fn cubic_association_adds_a_truth_proof() {
    let f = Fixture {
        name: "cubic-association",
        ops: vec![
            cc(0, 1, 3),
            cc(1, 2, 4),
            cc(3, 2, 5),
            cc(0, 4, 6),
            cc(5, 6, 7),
            h(7, 0, None),
        ],
        qi: vec![0, 1, 2],
        bi: vec![],
    };
    let original = with_abi(&f);
    let rewritten = simplify(original.clone());
    assert!(legal_ccx_edits(&original, &rewritten));
    assert_eq!(compare(&f, &original, &rewritten, 0..8), (16, 0));
    assert_eq!(
        rewritten[rewritten.len() - 2],
        cx(5, 7),
        "missing supported cubic equality rewrite"
    );
    let old = super::super::quadratic_simplify::simplify(original);
    assert_eq!(
        old[old.len() - 2],
        cc(5, 6, 7),
        "fixture must distinguish existing union"
    );
}

// Exercise the same public union with the unchanged inherited semantic suite.
#[path = "affine_simplify_tests.rs"]
mod inherited_union;

fn truth_only(ops: Vec<Op>) -> Vec<Op> {
    let mut support = super::Support::new(&ops);
    let mut result = Vec::new();
    for op in ops {
        support.step(&op).emit(op, &mut result);
    }
    result
}

fn check_native(f: &Fixture) -> usize {
    let original = with_abi(f);
    let inputs = 1usize << (f.qi.len() + f.bi.len());
    let union = simplify(original.clone());
    let truth = truth_only(original.clone());
    for rewritten in [&union, &truth] {
        assert!(
            legal_ccx_edits(&original, rewritten),
            "{} changed another opcode",
            f.name
        );
        let (_, mismatches) = compare(f, &original, rewritten, 0..inputs);
        assert_eq!(mismatches, 0, "{} full state/phase/draw mismatch", f.name);
    }
    let (cases, _) = compare(f, &original, &union, 0..inputs);
    cases
}

#[test]
fn captured_guards_hmr_abi_and_supported_products_preserve_all_state() {
    use OperationType::*;
    let common = |name, ops, _required: Vec<&'static str>| Fixture {
        name,
        ops,
        qi: vec![0, 1],
        bi: vec![0, 1],
    };
    let fs = vec![
        common(
            "constant-controls",
            vec![
                x(2),
                cc(2, 3, 4),
                cc(2, 0, 4),
                cc(0, 2, 4),
                x(3),
                cc(2, 3, 4),
                op(CZ, Some(4), Some(0), None, None, None),
                reset(4, None),
            ],
            vec!["ZeroControl", "Control1One", "Control2One", "BothOne"],
        ),
        common(
            "equal-complement-phase",
            vec![
                cx(0, 2),
                cc(0, 2, 3),
                x(2),
                cc(0, 2, 3),
                h(3, 2, None),
                op(Z, Some(0), None, None, None, Some(2)),
                reset(2, None),
            ],
            vec!["EqualControls", "ComplementControls"],
        ),
        common(
            "opaque-nonlinear",
            vec![
                cc(0, 1, 2),
                cx(2, 3),
                cc(2, 3, 4),
                cc(0, 1, 5),
                cc(2, 5, 4),
                x(2),
                cx(3, 2),
                cc(2, 0, 4),
            ],
            vec!["EqualControls", "Control1One"],
        ),
        Fixture {
            name: "cap-loss",
            ops: vec![
                cx(0, 3),
                cx(1, 3),
                cx(2, 3),
                cx(3, 4),
                cc(3, 4, 5),
                reset(3, None),
                cc(3, 4, 6),
            ],
            qi: vec![0, 1, 2],
            bi: vec![],
        },
        common(
            "classical-ABI",
            vec![
                x(2),
                op(X, Some(3), None, None, None, Some(0)),
                cc(2, 3, 4),
                h(4, 2, None),
            ],
            vec!["Control1One"],
        ),
        common(
            "unknown-guards-reset",
            vec![
                x(2),
                op(X, Some(3), None, None, None, Some(0)),
                cc(2, 3, 4),
                h(0, 0, Some(1)),
                op(BitInvert, None, None, None, Some(0), Some(1)),
                op(X, Some(5), None, None, None, Some(0)),
                cc(2, 5, 4),
                reset(0, Some(1)),
                cc(0, 2, 4),
            ],
            vec!["Control1One", "Control2One"],
        ),
        common(
            "false-guards",
            vec![
                x(2),
                op(BitStore0, None, None, None, Some(2), None),
                op(CCX, Some(3), Some(0), Some(1), None, Some(2)),
                push(2),
                h(0, 0, None),
                reset(1, None),
                x(4),
                cc(0, 1, 3),
                pop(),
                cc(1, 2, 3),
            ],
            vec!["FalseGuard", "Control2One"],
        ),
        common(
            "nested-snapshots",
            vec![
                push(0),
                op(BitInvert, None, None, None, Some(0), None),
                x(2),
                push(1),
                op(BitStore0, None, None, None, Some(1), None),
                x(3),
                pop(),
                x(4),
                pop(),
                cc(2, 4, 6),
                h(6, 3, None),
                cc(2, 3, 6),
            ],
            vec!["EqualControls"],
        ),
        common(
            "Hmr-classical-reuse",
            vec![
                h(0, 0, None),
                push(0),
                h(1, 0, None),
                x(2),
                pop(),
                op(X, Some(3), None, None, None, Some(0)),
                cc(2, 3, 4),
                h(4, 2, None),
                op(BitStore1, None, None, None, Some(0), None),
                op(CCX, Some(5), Some(2), Some(3), None, Some(0)),
            ],
            vec![],
        ),
        common(
            "conditional-swap",
            vec![
                cx(0, 2),
                op(Swap, Some(2), Some(1), None, None, Some(0)),
                cx(2, 3),
                cc(2, 3, 4),
                op(CCZ, Some(4), Some(0), Some(1), None, Some(1)),
                reset(4, None),
            ],
            vec!["EqualControls"],
        ),
    ];

    let mut total = 0;
    for f in &fs {
        total += check_native(f);
    }
    let cubic = Fixture {
        name: "cubic-association-exact",
        ops: vec![
            cc(0, 1, 3),
            cc(1, 2, 4),
            cc(3, 2, 5),
            cc(0, 4, 6),
            cc(5, 6, 7),
            op(CCZ, Some(7), Some(1), Some(2), None, None),
            h(7, 0, None),
        ],
        qi: vec![0, 1, 2],
        bi: vec![],
    };
    let cancel = Fixture {
        name: "cubic-cancellation-exact",
        ops: vec![
            cc(0, 1, 3),
            cc(3, 2, 4),
            cc(1, 2, 5),
            cc(0, 5, 4),
            cc(0, 4, 6),
            h(6, 0, None),
        ],
        qi: vec![0, 1, 2],
        bi: vec![],
    };
    let guard = Fixture {
        name: "cubic-guard-Hmr-overwrite",
        ops: vec![
            push(0),
            push(1),
            push(2),
            h(0, 0, None),
            op(BitInvert, None, None, None, Some(1), None),
            x(3),
            reset(1, Some(1)),
            pop(),
            x(4),
            pop(),
            x(5),
            pop(),
            cx(3, 6),
            cc(3, 6, 7),
            op(CCZ, Some(7), Some(4), Some(5), None, Some(0)),
            h(7, 3, Some(0)),
        ],
        qi: vec![0, 1, 2],
        bi: vec![0, 1, 2],
    };
    let mut capops = vec![];
    for i in 0..7 {
        capops.push(cx(i, 7));
    }
    capops.push(x(8));
    for i in 0..7 {
        capops.push(cx(i, 8));
    }
    capops.extend([
        cc(7, 8, 9),
        op(CZ, Some(9), Some(0), None, None, None),
        h(9, 0, None),
        cc(7, 0, 10),
        h(10, 1, None),
    ]);
    let cap = Fixture {
        name: "seven-atom-distinct-forgetting",
        ops: capops,
        qi: (0..7).collect(),
        bi: vec![],
    };
    let table = Fixture {
        name: "table-variable-order",
        ops: vec![
            cx(0, 3),
            cc(0, 1, 3),
            cc(3, 0, 4),
            cc(4, 0, 5),
            h(5, 0, None),
        ],
        qi: vec![0, 1],
        bi: vec![],
    };

    for f in [&cubic, &cancel, &guard, &cap, &table] {
        total += check_native(f);
    }
    println!(
        "truth native fixtures: {total} exhaustive assignments, each checked union and truth-only"
    );
}

#[test]
fn six_atom_copy_and_complement_remain_exact() {
    use OperationType::*;
    let mut ops = Vec::new();
    for i in 0..6 {
        ops.push(cx(i, 6));
        ops.push(cx(i, 7));
    }
    ops.extend([
        cc(6, 7, 8),
        x(7),
        cc(6, 7, 9),
        op(CCZ, Some(8), Some(0), Some(2), None, None),
        h(8, 0, None),
        h(9, 1, None),
    ]);
    let f = Fixture {
        name: "six-atom-copy-complement",
        ops,
        qi: (0..6).collect(),
        bi: vec![],
    };
    assert_eq!(check_native(&f), 256);
}

#[test]
fn union_preserves_existing_proofs_after_truth_support_overflow() {
    // Two separately evaluated eight-input parities exceed six support atoms;
    // truth forgets them independently, while both old domains retain equality.
    let mut ops = Vec::new();
    for i in 0..8 {
        ops.push(cx(i, 8));
        ops.push(cx(i, 9));
    }
    ops.push(cc(8, 9, 10));
    let f = Fixture {
        name: "old-proof-after-truth-cap",
        ops,
        qi: (0..8).collect(),
        bi: vec![],
    };
    let original = with_abi(&f);
    let truth = truth_only(original.clone());
    assert_eq!(truth.last(), original.last());
    let old = super::super::quadratic_simplify::simplify(original.clone());
    assert_eq!(old.last(), Some(&cx(8, 10)));
    assert_eq!(simplify(original), old);
    assert_eq!(check_native(&f), 256);
}

fn table_value(value: &super::Truth, input: usize) -> bool {
    let row = value
        .atoms
        .iter()
        .enumerate()
        .fold(0, |r, (j, &id)| r | (((input >> id) & 1) << j));
    value.table >> row & 1 != 0
}

#[test]
fn canonical_support_matches_independent_essential_cofactors() {
    use super::Truth;
    fn check(ids: Vec<u64>, table: u64) {
        // Determine all essential coordinates from the original table at once.
        let keep: Vec<usize> = (0..ids.len())
            .filter(|&j| {
                (0..1usize << ids.len())
                    .any(|r| ((table >> r) ^ (table >> (r ^ (1 << j)))) & 1 != 0)
            })
            .collect();
        let mut expected = 0;
        for r in 0..1usize << keep.len() {
            let old = keep
                .iter()
                .enumerate()
                .fold(0, |a, (k, &j)| a | (((r >> k) & 1) << j));
            expected |= ((table >> old) & 1) << r;
        }
        let actual = Truth::canonical(ids.clone(), table);
        assert_eq!(
            actual.atoms,
            keep.iter().map(|&j| ids[j]).collect::<Vec<_>>()
        );
        assert_eq!(actual.table, expected);
    }
    for n in 0..=4 {
        for t in 0..=Truth::row_mask(n) {
            check((0..n as u64).collect(), t)
        }
    }
    for subset in 0u32..64 {
        if subset.count_ones() > 3 {
            continue;
        }
        let used: Vec<usize> = (0..6).filter(|&j| subset >> j & 1 != 0).collect();
        for t in 0..=Truth::row_mask(used.len()) {
            let table = (0..64).fold(0u64, |acc, r| {
                let small = used
                    .iter()
                    .enumerate()
                    .fold(0, |a, (k, &j)| a | (((r >> j) & 1) << k));
                acc | (((t >> small) & 1) << r)
            });
            check(vec![3, 7, 12, 44, 71, 100], table);
        }
    }
    for t in [
        1u64 << 63,
        !(1u64 << 63),
        0x9669699669969669,
        0xfedcba9876543210,
    ] {
        check(vec![1, 3, 5, 7, 9, 11], t)
    }
    let atom = Truth::canonical(vec![17], 2);
    let padded = Truth::canonical(vec![3, 17, 100], 0b11001100);
    assert_eq!(atom, padded);
    assert!(atom.complements(&padded.complement()));
    assert_ne!(atom, Truth::canonical(vec![18], 2));
}

#[test]
fn all_three_atom_products_and_xors_preserve_bit_indexing() {
    use super::{Support, Truth};
    let mut support = Support::new(&[]);
    let mut checks = 0;
    for (left, right, width) in [
        (vec![0, 1, 2], vec![0, 1, 2], 3),
        (vec![0, 2, 4], vec![1, 3, 5], 6),
        (vec![0, 1, 3], vec![1, 2, 3], 4),
    ] {
        for lt in 0..256 {
            let a = Truth::canonical(left.clone(), lt);
            for rt in 0..256 {
                let b = Truth::canonical(right.clone(), rt);
                let xor = support.xor(&a, &b);
                let and = support.and(&a, &b);
                for row in 0..1usize << width {
                    assert_eq!(
                        table_value(&xor, row),
                        table_value(&a, row) ^ table_value(&b, row)
                    );
                    assert_eq!(
                        table_value(&and, row),
                        table_value(&a, row) & table_value(&b, row)
                    );
                    checks += 1;
                }
            }
        }
    }
    assert_eq!(support.next_atom, 0, "supported operations must not forget");
    assert_eq!(checks, 5767168);
}

#[test]
fn support_overflow_forgets_the_whole_result_with_distinct_atoms() {
    use super::{Support, Truth};
    let mut support = Support::new(&[]);
    let inputs: Vec<_> = (0..7).map(|_| support.fresh()).collect();
    let mut six = Truth::constant(true);
    for input in &inputs[..6] {
        six = support.xor(&six, input)
    }
    assert_eq!(six.atoms.len(), 6);
    assert_eq!(support.next_atom, 7);
    let a = support.xor(&six, &inputs[6]);
    let b = support.and(&six, &inputs[6]);
    let c = support.xor(&six.complement(), &inputs[6]);
    assert_eq!(
        (a.atoms.clone(), b.atoms.clone(), c.atoms.clone()),
        (vec![7], vec![8], vec![9])
    );
    assert_eq!((a.table, b.table, c.table), (2, 2, 2));
    assert_eq!(support.next_atom, 10);
    assert!(support.xor(&a, &a).is_zero());
    assert!(support.and(&b, &b.complement()).is_zero());
}
