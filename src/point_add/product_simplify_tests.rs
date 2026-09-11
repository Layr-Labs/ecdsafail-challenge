use super::super::simplify_products as simplify;
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use crate::sim::Simulator;
use sha3::digest::XofReader;

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
    expected: Vec<(usize, bool)>,
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

fn compare_all(f: &Fixture, original: &[Op], rewritten: &[Op]) -> usize {
    let nr = original
        .iter()
        .filter(|o| matches!(o.kind, OperationType::R | OperationType::Hmr))
        .count();
    let mut cases = 0;
    for input in 0..1usize << (f.qi.len() + f.bi.len()) {
        for random in 0..1usize << nr {
            assert_eq!(
                run(original, &f.qi, &f.bi, input, random, nr),
                run(rewritten, &f.qi, &f.bi, input, random, nr),
                "{} input={input} random={random}",
                f.name
            );
            cases += 1;
        }
    }
    cases
}

#[test]
fn repeated_product_uses_current_distinct_physical_witness() {
    let f = Fixture {
        name: "repeated-product",
        qi: vec![0, 1],
        bi: vec![],
        ops: vec![cc(0, 1, 2), cc(0, 1, 3), h(3, 0, None)],
        expected: vec![(1, false)],
    };
    let original = with_abi(&f);
    let rewritten = simplify(original.clone());
    assert_eq!(compare_all(&f, &original, &rewritten), 8);
    assert_eq!(rewritten[rewritten.len() - 2], cx(2, 3));
}

// Independent current-slot enumeration checks the maintained index at each query.
fn product_only(original: &[Op]) -> (Vec<Op>, Vec<(usize, bool)>) {
    let mut state = super::Support::new(original);
    let mut index = super::Index::new(&state, original);
    let mut output = Vec::new();
    let mut hits = Vec::new();
    for (i, op) in original.iter().enumerate() {
        let next = state.next_atom;
        let hit = index.before(&state, op);
        assert_eq!(state.next_atom, next, "query must not allocate");
        if op.kind == OperationType::CCX {
            let product = super::exact_product(
                &state.qubits[op.q_control1.0 as usize],
                &state.qubits[op.q_control2.0 as usize],
            );
            let mut expected = None;
            if let Some(p) = product {
                'search: for complement in [false, true] {
                    for q in 0..state.qubits.len() {
                        if index.permitted(q, op)
                            && state.qubits[q]
                                == if complement {
                                    p.complement()
                                } else {
                                    p.clone()
                                }
                        {
                            expected = Some(super::Hit {
                                witness: QubitId(q as u64),
                                complement,
                                zero_product: p.is_zero(),
                            });
                            break 'search;
                        }
                    }
                }
            }
            assert_eq!(hit, expected, "index mismatch at {i}");
        }
        state.step(op); // ORIGINAL, even when emitted operation differs.
        index.after(&state, op);
        let mut expected_index = std::collections::HashMap::new();
        for (q, value) in state.qubits.iter().enumerate() {
            if index.eligible[q] {
                expected_index
                    .entry(value.clone())
                    .or_insert_with(std::collections::BTreeSet::new)
                    .insert(q);
            }
        }
        assert_eq!(
            index.values, expected_index,
            "post-op index mismatch at {i}"
        );
        if let Some(hit) = hit {
            hits.push((i, hit.complement));
            hit.emit(*op, &mut output);
        } else {
            output.push(*op);
        }
    }
    (output, hits)
}

fn product_fixtures() -> Vec<Fixture> {
    use OperationType::*;
    let mut cases = vec![
        Fixture {
            name: "mutable-exact-complement",
            qi: vec![0, 1, 2],
            bi: vec![],
            ops: vec![
                cc(0, 1, 3),
                cc(0, 1, 2),
                x(3),
                cc(0, 1, 2),
                cx(0, 3),
                cc(0, 1, 2),
                h(2, 0, None),
                op(Z, Some(1), None, None, None, Some(0)),
                reset(3, None),
            ],
            expected: vec![(1, false), (3, true)],
        },
        Fixture {
            name: "target-exclusion",
            qi: vec![0, 1],
            bi: vec![],
            ops: vec![cc(0, 1, 2), cc(0, 1, 2), h(2, 0, None)],
            expected: vec![],
        },
        Fixture {
            name: "original-control-exclusion",
            qi: vec![0],
            bi: vec![],
            ops: vec![x(1), cc(0, 1, 2), h(2, 0, None)],
            expected: vec![],
        },
        Fixture {
            name: "captured-direct-nested-guards",
            qi: vec![0, 1, 2],
            bi: vec![0, 1],
            ops: vec![
                cc(0, 1, 3),
                push(0),
                op(BitInvert, None, None, None, Some(0), None),
                push(1),
                op(CCX, Some(2), Some(0), Some(1), None, Some(1)),
                pop(),
                h(0, 0, None),
                pop(),
                op(CCZ, Some(2), Some(1), Some(3), None, Some(0)),
                reset(3, Some(1)),
            ],
            expected: vec![(4, false)],
        },
        Fixture {
            name: "unknown-classical",
            qi: vec![1, 2],
            bi: vec![0],
            ops: vec![
                x(4),
                x(4),
                op(X, Some(3), None, None, None, Some(0)),
                cc(3, 1, 2),
                h(2, 1, None),
            ],
            expected: vec![],
        },
        Fixture {
            name: "conditional-reset",
            qi: vec![0, 1, 2],
            bi: vec![0],
            ops: vec![
                x(4),
                x(4),
                cc(0, 1, 3),
                reset(0, Some(0)),
                op(Z, Some(0), None, None, None, None),
                cc(0, 1, 2),
                h(2, 1, None),
            ],
            expected: vec![],
        },
        Fixture {
            name: "fresh-Hmr-output",
            qi: vec![0, 1, 2],
            bi: vec![],
            ops: vec![
                h(0, 0, None),
                op(X, Some(3), None, None, None, Some(0)),
                cc(3, 1, 2),
                h(2, 1, None),
            ],
            expected: vec![],
        },
        Fixture {
            name: "reset-witness-touch",
            qi: vec![0, 1, 2],
            bi: vec![0],
            ops: vec![
                cc(0, 1, 3),
                reset(3, Some(0)),
                op(Z, Some(3), None, None, None, None),
                cc(0, 1, 2),
                h(2, 1, None),
            ],
            expected: vec![],
        },
        Fixture {
            name: "guarded-complement",
            qi: vec![0, 1, 2],
            bi: vec![0],
            ops: vec![
                x(3),
                cc(0, 1, 3),
                op(CCX, Some(2), Some(0), Some(1), None, Some(0)),
                h(2, 1, None),
            ],
            expected: vec![(2, true)],
        },
    ];
    let mut fallback = (0..7).map(|q| cx(q, 8)).collect::<Vec<_>>();
    fallback.extend([cc(8, 0, 10), cx(8, 9), cc(9, 0, 12)]);
    fallback.extend((1..8).map(|q| cx(q, 11)));
    fallback.extend([
        cc(11, 0, 13),
        h(13, 0, None),
        op(CZ, Some(12), Some(10), None, None, None),
    ]);
    cases.push(Fixture {
        name: "correlated-fresh-fallback",
        qi: (0..8).collect(),
        bi: vec![],
        ops: fallback,
        expected: vec![(9, false)],
    });
    let mut unsupported = (0..6).map(|q| cx(q, 8)).collect::<Vec<_>>();
    unsupported.extend([cc(8, 6, 10), cc(8, 6, 11), h(11, 0, None)]);
    cases.push(Fixture {
        name: "query-cap-does-not-allocate",
        qi: (0..7).collect(),
        bi: vec![],
        ops: unsupported,
        expected: vec![],
    });

    cases.push(Fixture {
        name: "swap-moves-product",
        qi: vec![0, 1, 2, 4],
        bi: vec![0],
        expected: vec![(2, false)],
        ops: vec![
            cc(0, 1, 3),
            op(Swap, Some(4), Some(3), None, None, None),
            cc(0, 1, 2),
            op(Swap, Some(3), Some(4), None, None, Some(0)),
            cc(0, 1, 2),
            h(2, 1, None),
        ],
    });
    cases.push(Fixture {
        name: "zero-product-needs-witness",
        qi: vec![0, 1, 4],
        bi: vec![],
        expected: vec![(6, false)],
        ops: vec![
            cc(0, 1, 2),
            x(1),
            cc(0, 1, 3),
            x(1),
            cc(2, 3, 4),
            op(Z, Some(5), None, None, None, None),
            cc(2, 3, 4),
            h(4, 0, None),
        ],
    });
    cases.push(Fixture {
        name: "reset-zero-eligibility",
        qi: vec![0, 1, 4],
        bi: vec![],
        expected: vec![(9, false)],
        ops: vec![
            cc(0, 1, 2),
            x(1),
            cc(0, 1, 3),
            x(1),
            cc(2, 3, 4),
            reset(5, None),
            cc(2, 3, 4),
            op(Z, Some(5), None, None, None, None),
            reset(6, None),
            cc(2, 3, 4),
        ],
    });
    let mut overcap = (0..6).map(|q| cx(q, 8)).collect::<Vec<_>>();
    overcap.extend([
        op(Z, Some(12), None, None, None, None),
        cc(8, 6, 10),
        h(10, 0, None),
    ]);
    cases.push(Fixture {
        name: "overcap-query-with-eligible-zero",
        qi: (0..7).collect(),
        bi: vec![],
        expected: vec![],
        ops: overcap,
    });
    cases
}

#[test]
fn original_stream_product_union_preserves_native_state_phase_and_draws() {
    let mut total = 0;
    for f in product_fixtures() {
        let original = with_abi(&f);
        let abi_len = original.len() - f.ops.len();
        let (only, hits) = product_only(&original);
        let relative: Vec<_> = hits.iter().map(|&(i, c)| (i - abi_len, c)).collect();
        for wanted in &f.expected {
            assert!(
                relative.contains(wanted),
                "{} missing {wanted:?}: {relative:?}",
                f.name
            );
        }
        if [
            "target-exclusion",
            "original-control-exclusion",
            "query-cap-does-not-allocate",
        ]
        .contains(&f.name)
        {
            assert!(relative.is_empty());
        }
        if f.name == "mutable-exact-complement" {
            assert!(!relative.iter().any(|x| x.0 == 5));
        }
        if f.name == "zero-product-needs-witness" || f.name == "reset-zero-eligibility" {
            assert!(!relative.iter().any(|x| x.0 == 4));
        }
        if f.name == "reset-zero-eligibility" {
            assert!(!relative.iter().any(|x| x.0 == 6));
        }
        let union = simplify(original.clone());
        let n = compare_all(&f, &original, &union);
        assert_eq!(compare_all(&f, &original, &only), n);
        total += n;
        println!(
            "product fixture={} cases={n} query_hits={relative:?} union_and_product_only=PASS",
            f.name
        );
    }
    println!("product native total={total}, each checked union and product-only");
}

#[test]
fn zero_without_witness_is_not_a_new_rewrite() {
    let f = Fixture {
        name: "no-free-zero-rule",
        qi: vec![0, 1, 4],
        bi: vec![],
        expected: vec![],
        ops: vec![cc(0, 1, 2), x(1), cc(0, 1, 3), x(1), cc(2, 3, 4)],
    };
    let original = with_abi(&f);
    let candidate = simplify(original.clone());
    assert_eq!(candidate.last(), original.last());
    let mut witnessed = original.clone();
    witnessed.insert(
        witnessed.len() - 1,
        op(OperationType::Z, Some(5), None, None, None, None),
    );
    let candidate = simplify(witnessed.clone());
    assert_eq!(candidate.len(), witnessed.len() - 1);
    compare_all(&f, &witnessed, &candidate);
}

#[test]
fn pure_product_cap_and_correlated_atoms_are_conservative() {
    use super::{exact_product, Support, Truth};
    let mut state = Support::new(&[]);
    let values: Vec<_> = (0..7).map(|_| state.fresh()).collect();
    let mut six = Truth::constant(false);
    for v in &values[..6] {
        six = state.xor(&six, v);
    }
    let next = state.next_atom;
    assert!(exact_product(&six, &values[6]).is_none());
    assert_eq!(state.next_atom, next);
    assert_eq!(exact_product(&six, &six), Some(six.clone()));
    assert_eq!(
        exact_product(&six, &six.complement()),
        Some(Truth::constant(false))
    );
    let opaque_a = state.and(&six, &values[6]);
    let opaque_b = state.and(&six, &values[6]);
    assert_ne!(opaque_a, opaque_b);
    assert_ne!(exact_product(&opaque_a, &opaque_b), Some(opaque_a.clone()));
    // Exact query vs separate scalar evaluator under disjoint/interleaved IDs.
    let eval = |e: &Truth, input: usize| {
        let row = e
            .atoms
            .iter()
            .enumerate()
            .fold(0, |a, (j, &id)| a | (((input >> id) & 1) << j));
        (e.table >> row) & 1
    };
    let mut checked = 0;
    for left in 0..256 {
        let a = Truth::canonical(vec![0, 2, 4], left);
        for right in 0..256 {
            let b = Truth::canonical(vec![1, 3, 5], right);
            let p = exact_product(&a, &b).unwrap();
            for row in 0..64 {
                assert_eq!(eval(&p, row), eval(&a, row) & eval(&b, row));
                checked += 1;
            }
        }
    }
    assert_eq!(checked, 4194304);
}

#[test]
fn union_preserves_old_priority_after_truth_forgetting() {
    let mut ops = Vec::new();
    for q in 0..8 {
        ops.extend([cx(q, 8), cx(q, 9)]);
    }
    ops.extend([cc(8, 9, 10), cc(8, 9, 11)]);
    let f = Fixture {
        name: "old-priority",
        ops,
        qi: (0..8).collect(),
        bi: vec![],
        expected: vec![],
    };
    let original = with_abi(&f);
    let old = super::super::simplify(original.clone());
    let new = simplify(original.clone());
    assert_eq!(new, old);
    assert_eq!(new.last(), Some(&cx(8, 11)));
    compare_all(&f, &original, &new);
}

// Native-only path ensures broken production logic is exposed independently of
// the test's index-equality assertions, including phase and random draw count.
#[test]
fn native_witness_regressions() {
    for f in product_fixtures() {
        let original = with_abi(&f);
        let rewritten = simplify(original.clone());
        compare_all(&f, &original, &rewritten);
    }
}
