use alloy_primitives::U256;
use crate::circuit::{analyze_ops, Op, OperationType, QubitId, QubitOrBit};
use crate::sim::Simulator;
use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

fn secp256k1() -> WeierstrassEllipticCurve {
    WeierstrassEllipticCurve {
        modulus: U256::from_str_radix(
            "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F",
            16,
        )
        .unwrap(),
        a: U256::from(0),
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

pub fn run_parallel_nonce_grind(mut ops: Vec<Op>, start_nonce: u64, max_trials: u64) -> Option<u64> {
    let mut x = Op::empty();
    x.kind = OperationType::X;
    x.q_target = QubitId(0);
    ops.extend(std::iter::repeat_n(x, 96));

    let (total_qubits, num_bits, _num_registers, layout_regs) = analyze_ops(ops.iter());
    let op_len = ops.len();
    assert!(op_len >= 96);

    let mut base_hasher = Shake256::default();
    base_hasher.update(b"quantum_ecc-fiat-shamir-v2");
    base_hasher.update(&(op_len as u64).to_le_bytes());
    for op in &ops[..op_len - 96] {
        base_hasher.update(&[op.kind as u8]);
        base_hasher.update(&op.q_control2.0.to_le_bytes());
        base_hasher.update(&op.q_control1.0.to_le_bytes());
        base_hasher.update(&op.q_target.0.to_le_bytes());
        base_hasher.update(&op.c_target.0.to_le_bytes());
        base_hasher.update(&op.c_condition.0.to_le_bytes());
        base_hasher.update(&op.r_target.0.to_le_bytes());
    }

    let num_threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8)
        .min(10);

    eprintln!(
        "Starting parallel nonce grind: {} threads, qubits={}, start_nonce={}",
        num_threads, total_qubits, start_nonce
    );

    let found = Arc::new(AtomicBool::new(false));
    let winning_nonce = Arc::new(AtomicU64::new(0));
    let tested_count = Arc::new(AtomicU64::new(0));
    let ops_arc = Arc::new(ops);
    let layout_regs_arc = Arc::new(layout_regs);

    let start_time = Instant::now();
    let mut handles = Vec::new();

    for t_idx in 0..num_threads {
        let found = Arc::clone(&found);
        let winning_nonce = Arc::clone(&winning_nonce);
        let tested_count = Arc::clone(&tested_count);
        let ops = Arc::clone(&ops_arc);
        let layout_regs = Arc::clone(&layout_regs_arc);
        let base_hasher = base_hasher.clone();

        let handle = std::thread::spawn(move || {
            let curve = secp256k1();
            let mut local_ops = (*ops).clone();
            let tail_start = local_ops.len() - 96;

            let mut nonce = start_nonce + t_idx as u64;
            let step = num_threads as u64;

            while !found.load(Ordering::Relaxed) && (nonce - start_nonce) < max_trials {
                for b in 0..48 {
                    let target_q = if (nonce >> b) & 1 == 1 {
                        QubitId(1)
                    } else {
                        QubitId(0)
                    };
                    local_ops[tail_start + 2 * b].q_target = target_q;
                    local_ops[tail_start + 2 * b + 1].q_target = target_q;
                }

                let mut hasher = base_hasher.clone();
                for op in &local_ops[tail_start..] {
                    hasher.update(&[op.kind as u8]);
                    hasher.update(&op.q_control2.0.to_le_bytes());
                    hasher.update(&op.q_control1.0.to_le_bytes());
                    hasher.update(&op.q_target.0.to_le_bytes());
                    hasher.update(&op.c_target.0.to_le_bytes());
                    hasher.update(&op.c_condition.0.to_le_bytes());
                    hasher.update(&op.r_target.0.to_le_bytes());
                }
                let mut xof = hasher.finalize_xof();

                let mut targets = Vec::with_capacity(9024);
                let mut offsets = Vec::with_capacity(9024);
                let mut expected = Vec::with_capacity(9024);
                while targets.len() < 9024 {
                    let mut rb = [[0u8; 32]; 2];
                    XofReader::read(&mut xof, &mut rb[0]);
                    XofReader::read(&mut xof, &mut rb[1]);
                    let k1 = U256::from_le_bytes(rb[0]);
                    let k2 = U256::from_le_bytes(rb[1]);
                    let t = curve.mul(curve.gx, curve.gy, k1);
                    let o = curve.mul(curve.gx, curve.gy, k2);
                    if t.0 == o.0
                        || (t.0.is_zero() && t.1.is_zero())
                        || (o.0.is_zero() && o.1.is_zero())
                    {
                        continue;
                    }
                    let e = curve.add(t.0, t.1, o.0, o.1);
                    targets.push(t);
                    offsets.push(o);
                    expected.push(e);
                }

                let mut sim = Simulator::new(total_qubits as usize, num_bits as usize, &mut xof);
                let mut ok = true;
                const BATCH: usize = 64;
                let num_batches = (9024 + BATCH - 1) / BATCH;

                for batch in 0..num_batches {
                    let bs = BATCH.min(9024 - batch * BATCH);
                    let cond_mask: u64 = if bs == 64 { u64::MAX } else { (1u64 << bs) - 1 };

                    sim.clear_for_shot();
                    for shot in 0..bs {
                        let i = batch * BATCH + shot;
                        sim.set_register(&layout_regs[0], targets[i].0, shot);
                        sim.set_register(&layout_regs[1], targets[i].1, shot);
                        sim.set_register(&layout_regs[2], offsets[i].0, shot);
                        sim.set_register(&layout_regs[3], offsets[i].1, shot);
                    }

                    sim.apply_iter(local_ops.iter());

                    for shot in 0..bs {
                        let i = batch * BATCH + shot;
                        let gx = sim.get_register(&layout_regs[0], shot);
                        let gy = sim.get_register(&layout_regs[1], shot);
                        if gx != expected[i].0 || gy != expected[i].1 {
                            ok = false;
                            break;
                        }
                    }
                    if !ok {
                        break;
                    }

                    let phase = sim.phase & cond_mask;
                    if phase != 0 {
                        ok = false;
                        break;
                    }

                    for register in layout_regs.iter() {
                        for qb in register {
                            if let QubitOrBit::Qubit(q) = *qb {
                                *sim.qubit_mut(q) = 0;
                            }
                        }
                    }

                    for q in 0..total_qubits {
                        let v = sim.qubit(QubitId(q)) & cond_mask;
                        if v != 0 {
                            ok = false;
                            break;
                        }
                    }
                    if !ok {
                        break;
                    }
                }

                let cnt = tested_count.fetch_add(1, Ordering::Relaxed) + 1;
                if cnt % 500 == 0 {
                    let elapsed = start_time.elapsed().as_secs_f64();
                    let rate = cnt as f64 / elapsed.max(0.001);
                    eprintln!("Tested {} nonces ({:.1} nonces/sec)...", cnt, rate);
                }

                if ok {
                    winning_nonce.store(nonce, Ordering::SeqCst);
                    found.store(true, Ordering::SeqCst);
                    eprintln!(">>> SUCCESS! Found clean nonce: {} <<<", nonce);
                    break;
                }

                nonce += step;
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        let _ = handle.join();
    }

    if found.load(Ordering::SeqCst) {
        Some(winning_nonce.load(Ordering::SeqCst))
    } else {
        None
    }
}
