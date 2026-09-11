//! Env-gated profiler for the ping-pong point-add.  `PP_PROFILE=1` simulates
//! 64 valid lanes with the harness simulator and reports executed Toffoli per
//! phase, emitted CCX/CCZ per phase, and the allocator peak.  Emits no ops.
use super::*;

pub(crate) fn enabled() -> bool {
    std::env::var_os("PP_PROFILE").is_some()
}

pub(crate) fn report(
    ops: &[Op],
    phases: &[(usize, &'static str)],
    peak_qubits: u32,
    peak_ops_idx: usize,
    peak_phase: &str,
    timeline: &[(usize, u32)],
) {
    use sha3::{
        digest::{ExtendableOutput, Update, XofReader},
        Shake256,
    };
    let (num_qubits, num_bits, _nr, registers) = analyze_ops(ops.iter());
    let curve = WeierstrassEllipticCurve {
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
    };
    let seed_tag = std::env::var("PP_PROFILE_SEED").unwrap_or_else(|_| "0".into());
    let mut input_seed = Shake256::default();
    input_seed.update(b"pp_profile inputs ");
    input_seed.update(seed_tag.as_bytes());
    let mut input_reader = input_seed.finalize_xof();
    let mut targets = Vec::new();
    let mut offsets = Vec::new();
    let mut expected = Vec::new();
    while targets.len() < 64 {
        let mut sb = [[0u8; 32]; 2];
        XofReader::read(&mut input_reader, &mut sb[0]);
        XofReader::read(&mut input_reader, &mut sb[1]);
        let t = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(sb[0]));
        let o = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(sb[1]));
        if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) {
            continue;
        }
        expected.push(curve.add(t.0, t.1, o.0, o.1));
        targets.push(t);
        offsets.push(o);
    }
    let mut sim_seed = Shake256::default();
    sim_seed.update(b"pp_profile sim ");
    sim_seed.update(seed_tag.as_bytes());
    let mut sim_reader = sim_seed.finalize_xof();
    let mut sim = Simulator::new(num_qubits as usize, num_bits as usize, &mut sim_reader);
    for shot in 0..64 {
        sim.set_register(&registers[0], targets[shot].0, shot);
        sim.set_register(&registers[1], targets[shot].1, shot);
        sim.set_register(&registers[2], offsets[shot].0, shot);
        sim.set_register(&registers[3], offsets[shot].1, shot);
    }

    // phase ranges
    let mut bounds: Vec<(usize, usize, &str)> = Vec::new();
    for (i, &(start, name)) in phases.iter().enumerate() {
        let end = if i + 1 < phases.len() { phases[i + 1].0 } else { ops.len() };
        if end > start {
            bounds.push((start, end, name));
        }
    }
    if bounds.is_empty() || bounds[0].0 > 0 {
        let end = bounds.first().map(|b| b.0).unwrap_or(ops.len());
        bounds.insert(0, (0, end, "init"));
    }

    eprintln!("PP_PROFILE peak_qubits={peak_qubits} peak_ops_idx={peak_ops_idx} peak_phase={peak_phase} num_qubits={num_qubits} ops={}", ops.len());
    eprintln!("{:<24} {:>10} {:>10} {:>10} {:>12} {:>12} {:>8}", "phase", "ops", "ccx", "ccz", "exec_tof", "exec_cliff", "peak");
    let mut total_exec = 0.0;
    let mut rows = Vec::new();
    for &(start, end, name) in &bounds {
        let before = sim.stats;
        sim.apply_iter(ops[start..end].iter());
        let after = sim.stats;
        let exec_tof = (after.toffoli_gates - before.toffoli_gates) as f64 / 64.0;
        let exec_cliff = (after.clifford_gates - before.clifford_gates) as f64 / 64.0;
        let ccx = ops[start..end].iter().filter(|o| o.kind == OperationType::CCX).count();
        let ccz = ops[start..end].iter().filter(|o| o.kind == OperationType::CCZ).count();
        let peak = timeline
            .iter()
            .filter(|(i, _)| *i >= start && *i < end)
            .map(|(_, a)| *a)
            .max()
            .unwrap_or(0);
        total_exec += exec_tof;
        rows.push((name, end - start, ccx, ccz, exec_tof, exec_cliff, peak));
        eprintln!("{:<24} {:>10} {:>10} {:>10} {:>12.2} {:>12.1} {:>8}", name, end - start, ccx, ccz, exec_tof, exec_cliff, peak);
    }
    eprintln!("{:<24} {:>10} {:>10} {:>10} {:>12.2}", "TOTAL", ops.len(), rows.iter().map(|r| r.2).sum::<usize>(), rows.iter().map(|r| r.3).sum::<usize>(), total_exec);

    let mut cls = 0;
    for shot in 0..64 {
        if sim.get_register(&registers[0], shot) != expected[shot].0
            || sim.get_register(&registers[1], shot) != expected[shot].1
        {
            cls += 1;
        }
    }
    let mut dirty = 0;
    for register in &registers {
        for wire in register {
            if let QubitOrBit::Qubit(q) = *wire {
                *sim.qubit_mut(q) = 0;
            }
        }
    }
    for q in 0..num_qubits {
        if sim.qubit(QubitId(q)) != 0 {
            dirty += 1;
        }
    }
    eprintln!("PP_PROFILE lanes=64 classical_mismatch={cls} phase={:#x} dirty_qubits={dirty}", sim.phase);
}
