use std::cell::RefCell;
use std::collections::BTreeMap;

use alloy_primitives::U256;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

use super::{build_point_add, SECP256K1_P};
use crate::circuit::{analyze_ops, OperationType, QubitId, NO_BIT};
use crate::sim::Simulator;
use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;

thread_local! {
    static PHASES: RefCell<Vec<(usize, &'static str)>> = const { RefCell::new(Vec::new()) };
    static RESETS: RefCell<Vec<(usize, &'static str, u32)>> = const { RefCell::new(Vec::new()) };
    static RELEASES: RefCell<Vec<(usize, QubitId, &'static str, u32)>> = const { RefCell::new(Vec::new()) };
    static WALK: RefCell<Vec<(usize, &'static str, usize, usize)>> = const { RefCell::new(Vec::new()) };
}

pub(super) fn record_phase(index: usize, name: &'static str) {
    PHASES.with(|phases| phases.borrow_mut().push((index, name)));
}

pub(super) fn record_reset(index: usize, file: &'static str, line: u32) {
    RESETS.with(|resets| resets.borrow_mut().push((index, file, line)));
}

pub(super) fn record_release(index: usize, q: QubitId, file: &'static str, line: u32) {
    RELEASES.with(|releases| releases.borrow_mut().push((index, q, file, line)));
}

pub(super) fn record_walk(index: usize, phase: &'static str, round: usize, width: usize) {
    WALK.with(|walk| walk.borrow_mut().push((index, phase, round, width)));
}

fn curve() -> WeierstrassEllipticCurve {
    WeierstrassEllipticCurve {
        modulus: SECP256K1_P,
        a: U256::ZERO,
        b: U256::from(7),
        gx: U256::from_str_radix(
            "79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798",
            16,
        )
        .unwrap(),
        gy: U256::from_str_radix(
            "483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8",
            16,
        )
        .unwrap(),
        order: U256::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141",
            16,
        )
        .unwrap(),
    }
}

#[test]
#[ignore = "build-only resource diagnostic"]
fn circuit_resource_profile() {
    let ops = build_point_add();
    let width = analyze_ops(ops.iter()).0;
    assert!(width <= super::pingpong::walk_max_qubits() as u64);
    assert!(
        width < 1250,
        "must improve the original 1250-qubit baseline"
    );
    eprintln!("resource profile: qubits={width}");
}

#[test]
#[ignore = "8192 independent inputs plus 64 measurements of the regression point"]
fn independent_point_addition_precision() {
    check_precision(false, false);
}

#[test]
#[ignore = "diagnose the input and measurement seed in the current ops.bin"]
fn current_benchmark_precision() {
    check_precision(true, false);
}

#[test]
#[ignore = "64-shot regression for the retained failing curve-point pair"]
fn regression_point_precision() {
    check_precision(false, true);
}

fn benchmark_seed() -> sha3::Shake256Reader {
    use std::io::Read;

    let mut file = std::fs::File::open("ops.bin").expect("run ecdsafail run first");
    let mut header = [0u8; 16];
    file.read_exact(&mut header).unwrap();
    assert_eq!(&header[..8], b"QECCOPSZ");
    let count = u64::from_le_bytes(header[8..].try_into().unwrap());
    let mut hash = Shake256::default();
    hash.update(b"quantum_ecc-fiat-shamir-v2");
    hash.update(&count.to_le_bytes());
    let mut decoder = zstd::stream::read::Decoder::new(file).unwrap();
    let mut record = [0u8; 56];
    for _ in 0..count {
        decoder.read_exact(&mut record).unwrap();
        assert!(u32::from_le_bytes(record[..4].try_into().unwrap()) <= 17);
        hash.update(&record[..1]);
        hash.update(&record[8..]);
    }
    hash.finalize_xof()
}

fn check_precision(benchmark: bool, regressions_only: bool) {
    PHASES.with(|phases| phases.borrow_mut().clear());
    RESETS.with(|resets| resets.borrow_mut().clear());
    RELEASES.with(|releases| releases.borrow_mut().clear());
    WALK.with(|walk| walk.borrow_mut().clear());
    let ops = build_point_add();
    let phases = PHASES.with(|phases| phases.take());
    let reset_sites = RESETS.with(|resets| resets.take());
    let release_sites = RELEASES.with(|releases| releases.take());
    let walk_sites = WALK.with(|walk| walk.take());
    let mut next_release = 0usize;
    let (nq, nb, _, registers) = analyze_ops(ops.iter());
    assert_eq!(registers.len(), 4);
    let mut checkpoints = Vec::new();
    for (i, &(start, _)) in phases.iter().enumerate() {
        let end = phases.get(i + 1).map_or(ops.len(), |&(at, _)| at);
        let mut depth = 0usize;
        let mut resets = Vec::new();
        for (at, op) in ops.iter().enumerate().take(end).skip(start) {
            while release_sites
                .get(next_release)
                .is_some_and(|site| site.0 == at)
            {
                let (_, q, file, line) = release_sites[next_release];
                if depth == 0 {
                    resets.push((at, q, Some((file, line))));
                }
                next_release += 1;
            }
            match op.kind {
                OperationType::PushCondition => depth += 1,
                OperationType::PopCondition => depth -= 1,
                OperationType::R if depth == 0 && op.c_condition == NO_BIT => {
                    resets.push((at, op.q_target, None));
                }
                _ => {}
            }
        }
        assert_eq!(depth, 0, "phase boundary inside a classical condition");
        checkpoints.push((start, end, resets));
    }

    let curve = curve();
    let mut input_hash = Shake256::default();
    input_hash.update(b"ecdsafail-resource-reduction-independent-inputs-v1");
    let mut inputs = if benchmark {
        benchmark_seed()
    } else {
        input_hash.finalize_xof()
    };
    let shots = if benchmark {
        9024
    } else if regressions_only {
        0
    } else {
        8192
    };
    let mut points = Vec::with_capacity(shots);
    for _ in 0..shots {
        let mut scalars = [[0u8; 32]; 2];
        inputs.read(&mut scalars[0]);
        inputs.read(&mut scalars[1]);
        let target = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(scalars[0]));
        let offset = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(scalars[1]));
        assert_ne!(target.0, offset.0);
        assert_ne!(target, (U256::ZERO, U256::ZERO));
        assert_ne!(offset, (U256::ZERO, U256::ZERO));
        points.push((
            target,
            offset,
            curve.add(target.0, target.1, offset.0, offset.1),
        ));
    }
    if !benchmark {
        let hex = |s| U256::from_str_radix(s, 16).unwrap();
        let target = (
            hex("0ca07ea8e7f9e7799b120158ff33e4be0ecd9601a0385090fa67bfa334fe1110"),
            hex("f73406628539fc668fdd1f59b7a7812c4fd2b2f8c667fda1276aa96527de150b"),
        );
        let offset = (
            hex("dcb4d71b47632a37fc1f9be7fb92025c9afe6c784c77a597a827104f20472de8"),
            hex("246f243102d1a28af64d11717c95a77e541b7c8dc03f666ea5abfa1a00332217"),
        );
        assert!(curve.is_on_curve(target.0, target.1));
        assert!(curve.is_on_curve(offset.0, offset.1));
        let expected = curve.add(target.0, target.1, offset.0, offset.1);
        points.extend(std::iter::repeat_n((target, offset, expected), 64));
    }
    let shots = points.len();
    let mut measurement_hash = Shake256::default();
    measurement_hash.update(b"ecdsafail-resource-reduction-independent-measurements-v1");
    let mut measurements = if benchmark {
        inputs
    } else {
        measurement_hash.finalize_xof()
    };
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut measurements);
    let mut dirty_counts = vec![0usize; phases.len()];
    let mut first_dirty = vec![None; phases.len()];
    let mut classical_failures = 0usize;
    let mut phase_failures = 0usize;
    let mut ancilla_failures = 0usize;
    let mut dirty_sites = BTreeMap::new();

    for batch in 0..shots / 64 {
        sim.clear_for_shot();
        let batch_points = &points[batch * 64..(batch + 1) * 64];
        for (shot, &(target, offset, _)) in batch_points.iter().enumerate() {
            sim.set_register(&registers[0], target.0, shot);
            sim.set_register(&registers[1], target.1, shot);
            sim.set_register(&registers[2], offset.0, shot);
            sim.set_register(&registers[3], offset.1, shot);
        }
        for (i, (start, end, resets)) in checkpoints.iter().enumerate() {
            let mut from = *start;
            let mut dirty = 0u64;
            for &(at, q, release_site) in resets {
                sim.apply_iter(ops[from..at].iter());
                let value = sim.qubit(q);
                if value != 0 {
                    let (file, line) = release_site.unwrap_or_else(|| {
                        let site = reset_sites
                            .binary_search_by_key(&at, |&(index, _, _)| index)
                            .expect("every reset has a builder call site");
                        let (_, file, line) = reset_sites[site];
                        (file, line)
                    });
                    *dirty_sites.entry((file, line)).or_insert(0usize) +=
                        value.count_ones() as usize;
                }
                if value != 0 && first_dirty[i].is_none() {
                    first_dirty[i] = Some((batch * 64 + value.trailing_zeros() as usize, at));
                }
                dirty |= value;
                from = at;
            }
            sim.apply_iter(ops[from..*end].iter());
            dirty_counts[i] += dirty.count_ones() as usize;
        }
        for (shot, &(target, offset, point)) in batch_points.iter().enumerate() {
            let actual = (
                sim.get_register(&registers[0], shot),
                sim.get_register(&registers[1], shot),
            );
            if actual != point {
                classical_failures += 1;
                if classical_failures <= 4 {
                    eprintln!(
                        "regression input: shot={}, target=({:x},{:x}), offset=({:x},{:x})",
                        batch * 64 + shot,
                        target.0,
                        target.1,
                        offset.0,
                        offset.1
                    );
                }
            }
        }
        phase_failures += sim.phase.count_ones() as usize;
        ancilla_failures += sim.qubits[512..]
            .iter()
            .fold(0u64, |mask, &value| mask | value)
            .count_ones() as usize;
    }
    for ((file, line), count) in dirty_sites {
        eprintln!("dirty reset site: {file}:{line}, events={count}");
    }
    for (i, &count) in dirty_counts.iter().enumerate() {
        if count != 0 {
            let walk = first_dirty[i].and_then(|(_, at)| {
                walk_sites
                    .partition_point(|&(start, _, _, _)| start <= at)
                    .checked_sub(1)
                    .map(|index| walk_sites[index])
            });
            eprintln!(
                "dirty resets: phase={}, shots={count}, first={:?}, last_walk={walk:?}",
                phases[i].1, first_dirty[i],
            );
        }
    }
    eprintln!(
        "precision {shots} shots (benchmark={benchmark}): classical={classical_failures}, phase={phase_failures}, \
         ancilla={ancilla_failures}, qubits={nq}"
    );
    assert_eq!(classical_failures, 0);
    assert_eq!(phase_failures, 0);
    assert_eq!(ancilla_failures, 0);
    assert!(dirty_counts.iter().all(|&count| count == 0));
}
