//! Synthetic canonical LOCAL algebraic cases near W97/W109 margin bounds.
//! These fixtures do not establish reachable PZ states or profile membership.
use super::*;
type Wide = ruint::Uint<512, 8>;

#[derive(Clone)]
struct Case {
    width: usize,
    family: String,
    a: U256,
    b: U256,
    sign: bool,
    y: U256,
    forward_carry: bool,
    forward_lhs: U256,
    inverse_carry: bool,
    inverse_lhs: U256,
    wrong_forward: bool,
    wrong_inverse: bool,
}
fn wide(x: U256) -> Wide {
    let b = x.as_limbs();
    Wide::from_limbs([b[0], b[1], b[2], b[3], 0, 0, 0, 0])
}
fn narrow(x: Wide) -> U256 {
    let b = x.as_limbs();
    assert!(b[4..].iter().all(|&x| x == 0));
    U256::from_limbs([b[0], b[1], b[2], b[3]])
}
fn required_drop(width: usize) -> usize {
    match width {
        97 => 125,
        109 => 113,
        _ => panic!("unsupported near-margin fixture width"),
    }
}

fn cases() -> Vec<Case> {
    let rows: Vec<_> = include_str!("hybrid_margin_near_cases.txt")
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .map(|line| {
            let f: Vec<_> = line.split_whitespace().collect();
            assert_eq!(f.len(), 13);
            let word = |i: usize| U256::from_str_radix(f[i], 16).unwrap();
            Case {
                width: f[0].parse().unwrap(),
                family: f[1].into(),
                a: word(3),
                b: word(4),
                sign: f[5] == "1",
                y: word(6),
                forward_carry: f[7] == "1",
                forward_lhs: word(8),
                inverse_carry: f[9] == "1",
                inverse_lhs: word(10),
                wrong_forward: f[11] == "1",
                wrong_inverse: f[12] == "1",
            }
        })
        .collect();
    assert_eq!(rows.len(), 128);
    let one = Wide::from(1);
    let f = (one << 32) + Wide::from(977);
    let p = (one << 256) - f;
    for row in &rows {
        let (a, b, y) = (wide(row.a), wide(row.b), wide(row.y));
        assert!(a > Wide::ZERO && a < p && b > Wide::ZERO && b < p && y > Wide::ZERO && y < p);
        // Expected arithmetic is independent modular integer add/sub and
        // divide-by-two, not the production rotate/selected-offset algorithm.
        let z = if row.sign {
            (a + p - b) % p
        } else {
            (a + b) % p
        };
        let expected = (z + (z & one) * p) >> 1usize;
        assert_eq!(y, expected);
        let doubled = (Wide::from(2) * y) % p;
        let old = if row.sign {
            (Wide::from(2) * y + b) % p
        } else {
            (Wide::from(2) * y + p - b) % p
        };
        assert_eq!(old, a);
        let d = Wide::from(2) * ((one << 32) + one) * (one << row.width);
        let vmin = p / d + one;
        for value in [a, b, y, doubled] {
            assert!(
                value.min(p - value) >= vmin,
                "local residue bound family={}",
                row.family
            );
        }
        let framed = if row.sign { !row.a } else { row.a };
        assert_eq!(framed.overflowing_add(row.b).1, row.forward_carry);
        let rotated = (row.y << 1usize) | (row.y >> 255usize);
        assert_eq!(if row.sign { !rotated } else { rotated }, row.forward_lhs);
        let decoded = rotated.wrapping_add(if row.y.bit(255) {
            narrow(f - one)
        } else {
            U256::ZERO
        });
        assert_eq!(
            decoded,
            narrow(doubled),
            "literal old doubling equals independent field arithmetic"
        );
        let inverse_framed = if !row.sign { !decoded } else { decoded };
        let (sum, carry) = inverse_framed.overflowing_add(row.b);
        let folded = sum.wrapping_add(if carry { narrow(f) } else { U256::ZERO });
        assert_eq!((carry, folded), (row.inverse_carry, row.inverse_lhs));
        assert_eq!(if !row.sign { !folded } else { folded }, row.a);
        let drop = required_drop(row.width);
        for (lhs, carry, bad) in [
            (row.forward_lhs, row.forward_carry, row.wrong_forward),
            (row.inverse_lhs, row.inverse_carry, row.wrong_inverse),
        ] {
            assert_eq!(lhs < row.b, carry);
            assert_eq!((lhs >> drop) < (row.b >> drop), carry);
            assert_eq!(((lhs >> 136usize) < (row.b >> 136usize)) != carry, bad);
            let gap = if lhs < row.b {
                row.b - lhs
            } else {
                lhs - row.b
            };
            assert!(gap > (U256::from(1) << drop));
        }
    }
    for width in [97, 109] {
        let group: Vec<_> = rows.iter().filter(|r| r.width == width).collect();
        assert_eq!(group.len(), 64);
        assert_eq!(group.iter().filter(|r| r.wrong_forward).count(), 24);
        assert_eq!(group.iter().filter(|r| r.wrong_inverse).count(), 16);
    }
    rows
}

pub(super) fn selected_cells() -> Vec<(U256, U256, bool, U256)> {
    let selected = super::super::super::super::MIDQ_TAIL_VALUE_WIDTH[0] as usize;
    let rows = cases();
    let selected_rows: Vec<_> = rows
        .into_iter()
        .filter(|r| r.width == selected)
        .map(|r| (r.a, r.b, r.sign, r.y))
        .collect();
    if [97, 109].contains(&selected) {
        assert_eq!(selected_rows.len(), 64);
    } else {
        assert!(selected_rows.is_empty());
    }
    eprintln!("HYBRID_MARGIN_NEAR_SELECTED width={selected} local_cases={} expected_drop={:?} not_PZ_membership=true",selected_rows.len(),[97,109].contains(&selected).then(||required_drop(selected)));
    selected_rows
}

fn oracle(inverse: bool, drop: usize) -> B {
    let mut c = Circuit::new();
    let target = c.alloc_qreg_bits("near.oracle.target", 256);
    let source = c.alloc_qreg_bits("near.oracle.source", 256);
    let sign = c.alloc_qreg("near.oracle.sign");
    let overflow = c.alloc_qreg("near.oracle.overflow");
    if !inverse {
        for q in &target {
            c.cx(&sign, q);
        }
    }
    let lhs: Vec<_> = if inverse {
        target.iter().collect()
    } else {
        std::iter::once(&target[255])
            .chain(&target[..255])
            .collect()
    };
    let rhs: Vec<_> = source.iter().collect();
    super::super::super::super::clear_borrow_compare_refs(
        &mut c,
        &lhs[drop..],
        &rhs[drop..],
        &overflow,
    );
    if !inverse {
        for q in &target {
            c.cx(&sign, q);
        }
    }
    c.flush_pending_frees();
    c.into_builder()
}

pub(super) fn run_oracles() {
    let rows = cases();
    let mut checked = 0;
    for width in [97, 109] {
        let group: Vec<_> = rows.iter().filter(|r| r.width == width).collect();
        let drop = required_drop(width);
        for inverse in [false, true] {
            let full = oracle(inverse, 0);
            let selected = oracle(inverse, drop);
            let stale_legacy = oracle(inverse, 136); // intentional mutation witness
            let mut input = vec![0u64; 514];
            let mut defect = 0u64;
            for (lane, row) in group.iter().enumerate() {
                let target = if inverse { row.inverse_lhs } else { row.y };
                for bit in 0..256 {
                    input[bit] |= u64::from(target.bit(bit)) << lane;
                    input[256 + bit] |= u64::from(row.b.bit(bit)) << lane;
                }
                input[512] |= u64::from(row.sign) << lane;
                input[513] |= u64::from(if inverse {
                    row.inverse_carry
                } else {
                    row.forward_carry
                }) << lane;
                defect |= u64::from(if inverse {
                    row.wrong_inverse
                } else {
                    row.wrong_forward
                }) << lane;
            }
            let mut expected = input.clone();
            expected[513] = 0;
            assert_ne!(defect, 0, "old136 must be detected for both directions");
            for mode in 0..3 {
                let measurement = [0, u64::MAX, 0xa55a_c33c_9669_5aa5][mode as usize];
                for (which, built) in [&full, &selected, &stale_legacy].into_iter().enumerate() {
                    let (value, phase, _) = super::super::super::selftest::run_ops(
                        built,
                        &input,
                        mode,
                        None,
                        Some((513, measurement)),
                    );
                    assert_eq!(value, expected);
                    assert_eq!(
                        phase,
                        if which == 2 { defect & measurement } else { 0 },
                        "near boundary width={width} inverse={inverse} implementation={which}"
                    );
                    checked += 64;
                }
            }
            eprintln!("HYBRID_MARGIN_NEAR_ORACLE width={width} inverse={inverse} drop={drop} local_cases=64 old136_defects={} coherent_phase_mutation_detected=true",defect.count_ones());
        }
    }
    eprintln!("HYBRID_MARGIN_NEAR_ORACLES PASS cases={checked};bothW97W109,bothdirections,full/new/stale136,coupledHMRoutcomes,allresets;LOCAL_ALGEBRA_NOT_PZ_REACHABILITY");
}

#[cfg(test)]
#[test]
fn hybrid_margin_near_exact_fixture_arithmetic() {
    assert_eq!(cases().len(), 128);
}
