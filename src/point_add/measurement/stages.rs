//! Locate the first failing affine stage on independent, reproducible inputs.

use super::*;
use crate::weierstrass_elliptic_curve::sub_mod;

fn diagnostic_xof(ops: &[Op]) -> Shake256Reader {
    match std::env::var("MEASURE_DIAGNOSTIC_OPS") {
        Ok(path) => {
            assert!(
                std::env::var_os("MEASURE_DIAGNOSTIC_STREAM").is_none(),
                "choose either a saved input stream or the current Fiat-Shamir stream"
            );
            println!("DIAGNOSTIC_STREAM saved operations opened read-only: {path}");
            return artifact_xof(File::open(path).expect("open saved diagnostic operations"));
        }
        Err(std::env::VarError::NotPresent) => {}
        Err(std::env::VarError::NotUnicode(_)) => panic!("MEASURE_DIAGNOSTIC_OPS is not Unicode"),
    }
    match std::env::var("MEASURE_DIAGNOSTIC_STREAM") {
        Err(std::env::VarError::NotPresent) => independent_xof(&fresh_seed()),
        Ok(value) if value == "fiat-shamir" => {
            println!("DIAGNOSTIC_STREAM unchanged circuit Fiat-Shamir stream; no nonce search");
            let mut hash = super::nonce_grinder::hash_header(ops.len());
            for op in ops {
                super::nonce_grinder::hash_op(&mut hash, op);
            }
            hash.finalize_xof()
        }
        _ => panic!("MEASURE_DIAGNOSTIC_STREAM must be absent or fiat-shamir"),
    }
}

fn artifact_xof(mut reader: impl Read) -> Shake256Reader {
    let mut header = [0u8; 16];
    reader
        .read_exact(&mut header)
        .expect("read saved operation header");
    assert_eq!(&header[..8], b"QECCOPSZ");
    let count = u64::from_le_bytes(header[8..].try_into().unwrap());
    assert!(
        count <= 4_000_000_000,
        "saved operation count exceeds harness limit"
    );
    let mut hash = super::nonce_grinder::hash_header(usize::try_from(count).unwrap());
    let mut decoder = zstd::stream::read::Decoder::new(BufReader::new(reader)).unwrap();
    decoder.window_log_max(27).unwrap();
    let mut record = [0u8; 56];
    for _ in 0..count {
        decoder
            .read_exact(&mut record)
            .expect("read saved operation record");
        assert!(
            u32::from_le_bytes(record[..4].try_into().unwrap()) <= OperationType::DebugPrint as u32
        );
        hash.update(&record[..1]);
        hash.update(&record[8..]);
    }
    assert_eq!(
        decoder.read(&mut [0u8; 1]).unwrap(),
        0,
        "trailing saved operation data"
    );
    hash.finalize_xof()
}

#[test]
fn saved_artifact_inputs_match_the_literal_operation_hash() {
    let mut first = Op::empty();
    first.kind = OperationType::X;
    first.q_target = QubitId(0);
    let mut second = Op::empty();
    second.kind = OperationType::CX;
    second.q_control1 = QubitId(0);
    second.q_target = QubitId(1);
    let ops = [first, second];
    let mut artifact = b"QECCOPSZ".to_vec();
    artifact.extend_from_slice(&(ops.len() as u64).to_le_bytes());
    let records: Vec<_> = ops.iter().flat_map(op_bytes).collect();
    artifact.extend(zstd::stream::encode_all(&records[..], 3).unwrap());
    let mut actual = artifact_xof(&artifact[..]);
    let mut hash = super::nonce_grinder::hash_header(ops.len());
    for op in &ops {
        super::nonce_grinder::hash_op(&mut hash, op);
    }
    let mut expected = hash.finalize_xof();
    let (mut actual_bytes, mut expected_bytes) = ([0; 64], [0; 64]);
    XofReader::read(&mut actual, &mut actual_bytes);
    XofReader::read(&mut expected, &mut expected_bytes);
    assert_eq!(actual_bytes, expected_bytes);
}

fn expected_stages(shot: &Shot) -> [(U256, U256); 6] {
    let p = super::super::SECP256K1_P;
    let dx = sub_mod(shot.target.0, shot.offset.0, p);
    let dy = sub_mod(shot.target.1, shot.offset.1, p);
    let slope = dy.mul_mod(dx.inv_mod(p).expect("nondegenerate point pair"), p);
    let adjusted = dx.add_mod(shot.offset.0.mul_mod(U256::from(3), p), p);
    let product_x = sub_mod(adjusted, slope.mul_mod(slope, p), p);
    let product_y = slope.mul_mod(product_x, p);
    [
        (dx, dy),
        (dx, slope),
        (adjusted, slope),
        (product_x, slope),
        (product_x, product_y),
        (
            sub_mod(shot.offset.0, product_x, p),
            sub_mod(product_y, shot.offset.1, p),
        ),
    ]
}

#[test]
#[ignore = "selected-case replay diagnostic; does not search or alter input seeds"]
fn diagnose_division_rounds() {
    let attempts: usize = std::env::var("MEASURE_SHOTS")
        .map(|value| value.parse().expect("numeric MEASURE_SHOTS"))
        .unwrap_or(9024);
    let selected: std::collections::BTreeSet<usize> = std::env::var("MEASURE_DIAGNOSTIC_CASES")
        .expect("set MEASURE_DIAGNOSTIC_CASES to comma-separated zero-based shot indices")
        .split(',')
        .map(|value| value.parse().expect("numeric diagnostic shot index"))
        .collect();
    assert!(!selected.is_empty());
    let (ops, census) = build_measured();
    let steps = census.replay.division_steps();
    assert!(!steps.is_empty());
    assert!(steps
        .iter()
        .enumerate()
        .all(|(index, step)| step.round == index));
    let (coefficient, numerator) = census.replay.division_words();
    let coefficient: Vec<_> = coefficient.iter().copied().map(QubitOrBit::Qubit).collect();
    let numerator: Vec<_> = numerator.iter().copied().map(QubitOrBit::Qubit).collect();
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let p = super::super::SECP256K1_P;
    let inverse_two = (p >> 1) + U256::from(1);
    let mut xof = diagnostic_xof(&ops);
    let shots = sample_points(&mut xof, attempts);
    assert!(selected.last().is_some_and(|&index| index < shots.len()));
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
    for (batch, chunk) in shots.chunks(64).enumerate() {
        sim.clear_for_shot();
        for (lane, shot) in chunk.iter().enumerate() {
            for (reg, value) in
                regs.iter()
                    .zip([shot.target.0, shot.target.1, shot.offset.0, shot.offset.1])
            {
                sim.set_register(reg, value, lane);
            }
        }
        let cases: Vec<_> = (0..chunk.len())
            .filter(|lane| selected.contains(&(64 * batch + lane)))
            .collect();
        if cases.is_empty() {
            sim.apply_iter(ops.iter());
            continue;
        }
        let mut expected: Vec<_> = cases
            .iter()
            .map(|&lane| {
                [
                    U256::ZERO,
                    sub_mod(chunk[lane].target.1, chunk[lane].offset.1, p),
                ]
            })
            .collect();
        let mut seen = vec![false; cases.len()];
        let mut previous = 0;
        for step in &steps {
            sim.apply_iter(ops[previous..step.ops.start].iter());
            let signs = sim.qubits[step.sign.0 as usize];
            for (case, &lane) in cases.iter().enumerate() {
                let target = if step.round % 2 == 0 { 1 } else { 0 };
                let source = 1 - target;
                let sum = if step.round > 0 && (signs >> lane) & 1 != 0 {
                    sub_mod(expected[case][target], expected[case][source], p)
                } else {
                    expected[case][target].add_mod(expected[case][source], p)
                };
                expected[case][target] = sum.mul_mod(inverse_two, p);
            }
            sim.apply_iter(ops[step.ops.clone()].iter());
            previous = step.ops.end;
            for (case, &lane) in cases.iter().enumerate() {
                let actual = [
                    sim.get_register(&coefficient, lane),
                    sim.get_register(&numerator, lane),
                ];
                if actual != expected[case] && !seen[case] {
                    println!(
                        "REPLAY_FIRST shot={} round={} path={} sign={} phase={} \
                         coefficient={:#x} expected_coefficient={:#x} \
                         numerator={:#x} expected_numerator={:#x}",
                        64 * batch + lane,
                        step.round,
                        step.path,
                        (signs >> lane) & 1,
                        (sim.phase >> lane) & 1,
                        actual[0],
                        expected[case][0],
                        actual[1],
                        expected[case][1],
                    );
                    seen[case] = true;
                }
            }
        }
        sim.apply_iter(ops[previous..].iter());
        for (case, &lane) in cases.iter().enumerate() {
            println!(
                "REPLAY_FINAL shot={} replay_mismatch={} classical_mismatch={}",
                64 * batch + lane,
                seen[case],
                (
                    sim.get_register(&regs[0], lane),
                    sim.get_register(&regs[1], lane)
                ) != chunk[lane].expected,
            );
        }
    }
}

#[test]
fn affine_stage_reference_agrees_with_curve_addition() {
    let curve = curve();
    for (a, b) in [(3, 5), (10, 17), (23, 41)] {
        let target = curve.mul(curve.gx, curve.gy, U256::from(a));
        let offset = curve.mul(curve.gx, curve.gy, U256::from(b));
        let expected = curve.add(target.0, target.1, offset.0, offset.1);
        let shot = Shot {
            target,
            offset,
            expected,
        };
        assert_eq!(expected_stages(&shot)[5], expected);
    }
}

#[test]
#[ignore = "full independent-input stage diagnostic; reports errors, not acceptance"]
fn diagnose_point_stages() {
    let attempts: usize = std::env::var("MEASURE_SHOTS")
        .map(|value| value.parse().expect("numeric MEASURE_SHOTS"))
        .unwrap_or(9024);
    assert!(attempts > 0);
    let (ops, census) = build_measured();
    let coordinates: Vec<_> = census
        .spans
        .iter()
        .filter(|span| span.phase == Phase::Coordinates)
        .collect();
    let squares: Vec<_> = census
        .spans
        .iter()
        .filter(|span| span.phase == Phase::Square)
        .collect();
    assert_eq!(coordinates.len(), 3);
    assert_eq!(squares.len(), 1);
    // These are existing, condition-balanced census span boundaries.
    let boundaries = [
        ("coordinate-deltas", coordinates[0].ops.end),
        ("divide", coordinates[1].ops.start),
        ("add3x", coordinates[1].ops.end),
        ("square", squares[0].ops.end),
        ("multiply", coordinates[2].ops.start),
        ("final", coordinates[2].ops.end),
    ];
    assert!(boundaries.windows(2).all(|pair| pair[0].1 <= pair[1].1));
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    assert_eq!(regs.len(), 4);
    let mut outputs = vec![false; nq as usize];
    for register in &regs[..2] {
        for wire in register {
            let QubitOrBit::Qubit(q) = wire else {
                panic!("quantum output expected");
            };
            outputs[q.0 as usize] = true;
        }
    }
    let mut xof = diagnostic_xof(&ops);
    let shots = sample_points(&mut xof, attempts);
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
    let mut first_failures = [[0usize; 3]; 6];
    let mut final_failures = Failures::default();
    let mut printed = 0;
    let mut toffoli = 0u64;
    let mut full_shots = 0usize;
    let (walk_widths, multiply_rounds) = super::super::pingpong::measurement_walk_widths();
    let exact_from =
        super::super::pingpong::measurement_exact_tail_start().unwrap_or(walk_widths.len());
    for (batch, chunk) in shots.chunks(64).enumerate() {
        sim.clear_for_shot();
        let before = sim.stats.toffoli_gates;
        let expected: Vec<_> = chunk.iter().map(expected_stages).collect();
        for (lane, shot) in chunk.iter().enumerate() {
            for (reg, value) in
                regs.iter()
                    .zip([shot.target.0, shot.target.1, shot.offset.0, shot.offset.1])
            {
                sim.set_register(reg, value, lane);
            }
        }
        let mut previous = 0;
        let mut seen = [0u64; 3];
        let mask = live_mask(chunk.len());
        for (stage, &(name, end)) in boundaries.iter().enumerate() {
            sim.apply_iter(ops[previous..end].iter());
            previous = end;
            let mut classical = 0u64;
            for (lane, expected) in expected.iter().enumerate() {
                if sim.get_register(&regs[0], lane) != expected[stage].0
                    || sim.get_register(&regs[1], lane) != expected[stage].1
                {
                    classical |= 1 << lane;
                }
            }
            let ancilla = sim
                .qubits
                .iter()
                .zip(&outputs)
                .filter(|(_, output)| !**output)
                .fold(0, |value, (&qubit, _)| value | qubit)
                & mask;
            let current = [classical, sim.phase & mask, ancilla];
            let mut newly_bad = 0;
            for channel in 0..3 {
                let first = current[channel] & !seen[channel];
                first_failures[stage][channel] += first.count_ones() as usize;
                newly_bad |= first;
                seen[channel] |= current[channel];
            }
            for (lane, expected) in expected.iter().enumerate() {
                if printed < 16 && newly_bad & (1 << lane) != 0 {
                    println!(
                        "STAGE_FIRST shot={} stage={name} classical={} phase={} ancilla={} \
                         got_x={:#x} expected_x={:#x} got_y={:#x} expected_y={:#x}",
                        batch * 64 + lane,
                        (current[0] >> lane) & 1,
                        (current[1] >> lane) & 1,
                        (current[2] >> lane) & 1,
                        sim.get_register(&regs[0], lane),
                        expected[stage].0,
                        sim.get_register(&regs[1], lane),
                        expected[stage].1,
                    );
                    let p = super::super::SECP256K1_P;
                    let shot = &chunk[lane];
                    println!(
                        "STAGE_WALK shot={} divide={:?} multiply={:?}",
                        batch * 64 + lane,
                        super::walk::model(
                            sub_mod(shot.target.0, shot.offset.0, p),
                            &walk_widths,
                            walk_widths.len(),
                            exact_from
                        ),
                        super::walk::model(
                            sub_mod(shot.offset.0, shot.expected.0, p),
                            &walk_widths,
                            multiply_rounds,
                            exact_from
                        ),
                    );
                    printed += 1;
                }
            }
        }
        sim.apply_iter(ops[previous..].iter());
        check_batch(&sim, &regs, chunk, &outputs, &mut final_failures);
        if chunk.len() == 64 {
            toffoli += sim.stats.toffoli_gates - before;
            full_shots += 64;
        }
    }
    for ((name, _), counts) in boundaries.iter().zip(first_failures) {
        println!(
            "STAGE_COUNTS {name} classical={} phase={} ancilla={}",
            counts[0], counts[1], counts[2]
        );
    }
    println!(
        "STAGE_FINAL shots={} classical={} phase={} ancilla={} any={}",
        shots.len(),
        final_failures.classical,
        final_failures.phase,
        final_failures.ancilla,
        final_failures.any,
    );
    census.print(None);
    if full_shots > 0 {
        println!(
            "EXECUTED full_batch_shots={full_shots} mean_toffoli={:.3}",
            toffoli as f64 / full_shots as f64
        );
    }
    println!("DIAGNOSTIC_ONLY: observations are not a scored acceptance result");
}
