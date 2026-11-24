//! Trusted 2-pass streaming & parallel evaluator for `ops.bin`.
//!
//! - Pass 1 (`pass1_validate_and_hash`): stream-decompresses `ops.bin`, validates
//!   every op, runs `OpsAnalyzer`, counts `Hmr`/`R` ops, hashes the op stream
//!   with SHAKE256 on a pipelined hasher thread (with buffer recycling), and
//!   records the SHA3-256 digest of the raw `ops.bin` bytes (`0..EOF`).
//! - `compute_wave_plan`: bounds simulator memory with checked arithmetic and
//!   a dynamic wave budget `clamp(n * 56, 2 GiB, 32 GiB)`, rejecting any single
//!   simulator exceeding 32 GiB before curve point generation.
//! - `generate_test_points`: draws all Fiat-Shamir scalar bytes sequentially
//!   from the single `Shake256Reader`, then computes secp256k1 points in parallel
//!   and filters in original index order.
//! - Pass 2 (`run_tests_streaming`): rewinds the exact `File` fd from Pass 1,
//!   streams chunks with `validate = true` + explicit qubit/bit bounds checks
//!   across parallel worker slices using per-worker `mpsc::sync_channel(2)` and
//!   a 4-slot `Arc<Vec<Op>>` ring pool, verifies every wave's SHA3-256 matches
//!   Pass 1, and checks every batch in deterministic order.

use crate::circuit::{Op, OperationType, OpsAnalyzer, QubitId, QubitOrBit, NO_BIT, NO_QUBIT};
use crate::ops_io::{OpsReader, OP_BYTES};
use crate::sim::{SimExecState, Simulator};
use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
use alloy_primitives::U256;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256, Shake256Reader,
};
use std::fs::File;
use std::path::Path;
use std::sync::{mpsc, Arc};

pub const NUM_TESTS: usize = 9024;
pub const CHUNK_OPS: usize = 65_536;
pub const MIN_SIM_STATE_BYTES: usize = 2 * 1024 * 1024 * 1024;
pub const MAX_SIM_STATE_BYTES: usize = 32 * 1024 * 1024 * 1024;

const BATCH_SIZE: usize = 64;
const FS_RECORD_BYTES: usize = 49;

pub struct Pass1Summary {
    pub ops_len: u64,
    pub total_qubits: u64,
    pub num_bits: u64,
    pub regs: Vec<Vec<QubitOrBit>>,
    pub rng_ops: u64,
    pub file_digest: [u8; 32],
}

pub struct TestPoints {
    pub targets: Vec<(U256, U256)>,
    pub offsets: Vec<(U256, U256)>,
    pub expected: Vec<(U256, U256)>,
}

#[derive(Debug)]
pub struct SeedReport {
    pub ok: bool,
    pub avg_cliff: f64,
    pub avg_tof: f64,
    pub tot_tof: u64,
    pub tot_cliff: u64,
    pub n_shots: usize,
    pub classical_failures: usize,
    pub phase_garbage_batches: usize,
    pub ancilla_garbage_batches: usize,
    pub fail_reason: Option<String>,
}

pub fn secp256k1() -> WeierstrassEllipticCurve {
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

pub fn pass1_validate_and_hash(
    path: &Path,
) -> Result<(Pass1Summary, Shake256Reader, File), String> {
    let mut reader = OpsReader::open(path)?;
    let ops_len = reader.total_ops();

    let (prod_res, hasher_res) = std::thread::scope(|s| {
        let (data_tx, data_rx) = mpsc::sync_channel::<Vec<Op>>(2);
        let (free_tx, free_rx) = mpsc::sync_channel::<Vec<Op>>(3);

        let hasher_handle = s.spawn(move || {
            let mut hasher = Shake256::default();
            hasher.update(b"quantum_ecc-fiat-shamir-v2");
            hasher.update(&ops_len.to_le_bytes());

            let mut pack_buf: Vec<u8> = Vec::with_capacity(CHUNK_OPS * FS_RECORD_BYTES);
            while let Ok(mut chunk) = data_rx.recv() {
                pack_buf.clear();
                pack_buf.reserve(chunk.len() * FS_RECORD_BYTES);
                for op in &chunk {
                    pack_buf.push(op.kind as u8);
                    pack_buf.extend_from_slice(&op.q_control2.0.to_le_bytes());
                    pack_buf.extend_from_slice(&op.q_control1.0.to_le_bytes());
                    pack_buf.extend_from_slice(&op.q_target.0.to_le_bytes());
                    pack_buf.extend_from_slice(&op.c_target.0.to_le_bytes());
                    pack_buf.extend_from_slice(&op.c_condition.0.to_le_bytes());
                    pack_buf.extend_from_slice(&op.r_target.0.to_le_bytes());
                }
                hasher.update(&pack_buf);
                chunk.clear();
                // Non-blocking return so the hasher can never block if producer exits early.
                let _ = free_tx.try_send(chunk);
            }
            hasher.finalize_xof()
        });

        let prod_res: Result<(OpsAnalyzer, u64, File, [u8; 32]), String> = (|| {
            let mut analyzer = OpsAnalyzer::new();
            let mut rng_ops = 0u64;
            loop {
                let mut buf = free_rx
                    .try_recv()
                    .unwrap_or_else(|_| Vec::with_capacity(CHUNK_OPS));
                let got = reader.read_chunk(&mut buf, CHUNK_OPS, true)?;
                if got == 0 {
                    break;
                }
                for op in &buf {
                    analyzer.observe(op)?;
                    if matches!(op.kind, OperationType::Hmr | OperationType::R) {
                        rng_ops += 1;
                    }
                }
                data_tx
                    .send(buf)
                    .map_err(|_| "hasher thread terminated unexpectedly".to_string())?;
            }
            let (file, file_digest) = reader.into_file_and_digest()?;
            Ok((analyzer, rng_ops, file, file_digest))
        })();

        // Always close the channel before joining so the hasher exits on any error.
        drop(data_tx);

        let hasher_res = hasher_handle
            .join()
            .map_err(|_| "Pass 1 hasher thread panicked".to_string());
        (prod_res, hasher_res)
    });

    let (analyzer, rng_ops, file, file_digest) = prod_res?;
    let xof = hasher_res?;
    let (total_qubits, num_bits, _num_regs, regs) = analyzer.finish();

    Ok((
        Pass1Summary {
            ops_len,
            total_qubits,
            num_bits,
            regs,
            rng_ops,
            file_digest,
        },
        xof,
        file,
    ))
}

pub fn validate_registers(regs: &[Vec<QubitOrBit>]) -> Result<(), String> {
    if regs.len() != 4 {
        return Err(format!("expected 4 registers, got {}", regs.len()));
    }
    for (i, r) in regs.iter().enumerate() {
        if r.len() != 256 {
            return Err(format!("register {i} should be 256 wide, got {}", r.len()));
        }
    }
    for q in &regs[0] {
        if !matches!(q, QubitOrBit::Qubit(_)) {
            return Err("register 0 must be qubits".to_string());
        }
    }
    for q in &regs[1] {
        if !matches!(q, QubitOrBit::Qubit(_)) {
            return Err("register 1 must be qubits".to_string());
        }
    }
    for q in &regs[2] {
        if !matches!(q, QubitOrBit::Bit(_)) {
            return Err("register 2 must be bits".to_string());
        }
    }
    for q in &regs[3] {
        if !matches!(q, QubitOrBit::Bit(_)) {
            return Err("register 3 must be bits".to_string());
        }
    }
    Ok(())
}

pub fn compute_wave_plan(
    ops_len: u64,
    total_qubits: u64,
    num_bits: u64,
    max_batches: usize,
    min_budget_bytes: usize,
    max_budget_bytes: usize,
) -> Result<usize, String> {
    let total_lanes: usize = total_qubits
        .checked_add(num_bits)
        .and_then(|v| usize::try_from(v).ok())
        .ok_or_else(|| "qubit + bit count overflows usize".to_string())?;
    let per_sim_bytes: usize = total_lanes
        .checked_mul(8)
        .ok_or_else(|| "simulator state size overflows usize".to_string())?;
    if per_sim_bytes > max_budget_bytes {
        return Err(format!(
            "single simulator requires {per_sim_bytes} bytes, exceeding limit {max_budget_bytes}"
        ));
    }

    let stream_bytes: usize = ops_len
        .saturating_mul(OP_BYTES as u64)
        .min(usize::MAX as u64) as usize;
    let floor = min_budget_bytes.min(max_budget_bytes);
    let wave_budget: usize = stream_bytes.clamp(floor, max_budget_bytes);
    let max_b = max_batches.max(1);
    let wave_size = if per_sim_bytes == 0 {
        max_b
    } else {
        (wave_budget / per_sim_bytes).clamp(1, max_b)
    };
    Ok(wave_size)
}

pub fn generate_test_points(
    xof: &mut Shake256Reader,
    target_shots: usize,
    threads: usize,
) -> TestPoints {
    let mut raw_pairs = Vec::with_capacity(target_shots);
    for _ in 0..target_shots {
        let mut rb = [[0u8; 32]; 2];
        XofReader::read(xof, &mut rb[0]);
        XofReader::read(xof, &mut rb[1]);
        raw_pairs.push(rb);
    }

    let worker_count = threads.clamp(1, target_shots.max(1));
    let slice_len = target_shots.max(1).div_ceil(worker_count);
    let mut results: Vec<Option<((U256, U256), (U256, U256), (U256, U256))>> =
        vec![None; target_shots];

    std::thread::scope(|s| {
        for (pair_chunk, out_chunk) in raw_pairs
            .chunks(slice_len)
            .zip(results.chunks_mut(slice_len))
        {
            s.spawn(move || {
                let curve = secp256k1();
                for (rb, slot) in pair_chunk.iter().zip(out_chunk.iter_mut()) {
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
                    *slot = Some((t, o, e));
                }
            });
        }
    });

    let mut targets = Vec::with_capacity(target_shots);
    let mut offsets = Vec::with_capacity(target_shots);
    let mut expected = Vec::with_capacity(target_shots);
    for entry in results.into_iter().flatten() {
        targets.push(entry.0);
        offsets.push(entry.1);
        expected.push(entry.2);
    }

    TestPoints {
        targets,
        offsets,
        expected,
    }
}

pub fn check_chunk_bounds(ops: &[Op], total_qubits: u64, num_bits: u64) -> Result<(), String> {
    for op in ops {
        if op.q_control2 != NO_QUBIT && op.q_control2.0 >= total_qubits {
            return Err(format!(
                "q_control2 {} out of bounds (total_qubits={total_qubits})",
                op.q_control2.0
            ));
        }
        if op.q_control1 != NO_QUBIT && op.q_control1.0 >= total_qubits {
            return Err(format!(
                "q_control1 {} out of bounds (total_qubits={total_qubits})",
                op.q_control1.0
            ));
        }
        if op.q_target != NO_QUBIT && op.q_target.0 >= total_qubits {
            return Err(format!(
                "q_target {} out of bounds (total_qubits={total_qubits})",
                op.q_target.0
            ));
        }
        if op.c_target != NO_BIT && op.c_target.0 >= num_bits {
            return Err(format!(
                "c_target {} out of bounds (num_bits={num_bits})",
                op.c_target.0
            ));
        }
        if op.c_condition != NO_BIT && op.c_condition.0 >= num_bits {
            return Err(format!(
                "c_condition {} out of bounds (num_bits={num_bits})",
                op.c_condition.0
            ));
        }
    }
    Ok(())
}

/// Fan out chunks from `produce` to scoped worker threads owning disjoint slices
/// of `items`, using one bounded `sync_channel(2)` per actually-spawned slice
/// and a 4-slot `Arc<Vec<Op>>` ring pool for zero steady-state allocations.
pub fn fanout_chunks<W, P, F>(
    items: &mut [W],
    num_workers: usize,
    chunk_ops: usize,
    mut produce: P,
    worker_fn: F,
) -> Result<(), String>
where
    W: Send,
    P: FnMut(&mut Vec<Op>) -> Result<usize, String>,
    F: Fn(&mut [W], &[Op]) + Sync,
{
    if items.is_empty() {
        return Ok(());
    }
    let worker_count = num_workers.clamp(1, items.len());
    let slice_len = items.len().div_ceil(worker_count);
    let worker_fn_ref = &worker_fn;

    std::thread::scope(|s| {
        let mut txs = Vec::new();
        let mut handles = Vec::new();

        // Create one channel per actual slice so txs.len() == spawned workers by construction.
        for slice in items.chunks_mut(slice_len) {
            let (tx, rx) = mpsc::sync_channel::<Arc<Vec<Op>>>(2);
            txs.push(tx);
            let h = s.spawn(move || {
                while let Ok(chunk) = rx.recv() {
                    worker_fn_ref(slice, &chunk);
                }
            });
            handles.push(h);
        }

        let prod_res: Result<(), String> = (|| {
            let mut pool: [Arc<Vec<Op>>; 4] =
                std::array::from_fn(|_| Arc::new(Vec::with_capacity(chunk_ops)));
            let mut chunk_idx = 0usize;
            loop {
                let slot = &mut pool[chunk_idx % 4];
                if Arc::get_mut(slot).is_none() {
                    *slot = Arc::new(Vec::with_capacity(chunk_ops));
                }
                let buf = Arc::get_mut(slot).unwrap();
                buf.clear();
                let got = produce(buf)?;
                if got == 0 {
                    break;
                }
                for tx in &txs {
                    tx.send(Arc::clone(slot))
                        .map_err(|_| "worker thread terminated unexpectedly".to_string())?;
                }
                chunk_idx += 1;
            }
            Ok(())
        })();

        // Always drop all senders before joining so every surviving worker observes RecvError.
        drop(txs);

        let mut worker_err: Option<String> = None;
        for h in handles {
            if h.join().is_err() && worker_err.is_none() {
                worker_err = Some("Pass 2 worker thread panicked".to_string());
            }
        }

        if let Some(err) = worker_err {
            return Err(err);
        }
        prod_res
    })
}

fn advance_xof(xof: &mut Shake256Reader, mut bytes: u64) {
    let mut scratch = [0u8; 65_536];
    while bytes > 0 {
        let step = (bytes as usize).min(scratch.len());
        XofReader::read(xof, &mut scratch[..step]);
        bytes -= step as u64;
    }
}

struct BatchRunner<'a> {
    sim: Simulator<'a, Shake256Reader>,
    exec_state: SimExecState,
    batch_idx: usize,
    bs: usize,
    cond_mask: u64,
}

struct BatchVerifyAcc {
    ok: bool,
    fail_reason: Option<String>,
    classical_failures: usize,
    phase_garbage_batches: usize,
    ancilla_garbage_batches: usize,
    tot_tof: u64,
    tot_cliff: u64,
}

fn verify_batch(
    runner: &mut BatchRunner<'_>,
    summary: &Pass1Summary,
    points: &TestPoints,
    acc: &mut BatchVerifyAcc,
) {
    let batch = runner.batch_idx;
    let bs = runner.bs;
    let cond_mask = runner.cond_mask;

    acc.tot_tof += runner.sim.stats.toffoli_gates;
    acc.tot_cliff += runner.sim.stats.clifford_gates;

    for shot in 0..bs {
        let i = batch * BATCH_SIZE + shot;
        let gx = runner.sim.get_register(&summary.regs[0], shot);
        let gy = runner.sim.get_register(&summary.regs[1], shot);
        if gx != points.expected[i].0 || gy != points.expected[i].1 {
            acc.classical_failures += 1;
            if acc.fail_reason.is_none() {
                acc.fail_reason = Some(format!(
                    "CLASSICAL MISMATCH shot {i}: got ({:#x},{:#x}) exp ({:#x},{:#x})",
                    gx, gy, points.expected[i].0, points.expected[i].1
                ));
            }
            acc.ok = false;
        }
    }

    let phase = runner.sim.phase & cond_mask;
    if phase != 0 {
        acc.phase_garbage_batches += 1;
        if acc.fail_reason.is_none() {
            acc.fail_reason = Some(format!(
                "PHASE GARBAGE: global_phase = {:#018x} across {} live shots (must be 0)",
                phase, bs
            ));
        }
        acc.ok = false;
    }

    for register in &summary.regs {
        for qb in register {
            if let QubitOrBit::Qubit(q) = *qb {
                *runner.sim.qubit_mut(q) = 0;
            }
        }
    }
    let mut garbage_q: Option<u64> = None;
    for q in 0..summary.total_qubits {
        let v = runner.sim.qubit(QubitId(q)) & cond_mask;
        if v != 0 {
            garbage_q = Some(q);
            break;
        }
    }
    if let Some(q) = garbage_q {
        acc.ancilla_garbage_batches += 1;
        let v = runner.sim.qubit(QubitId(q)) & cond_mask;
        if acc.fail_reason.is_none() {
            acc.fail_reason = Some(format!(
                "ANCILLA GARBAGE: qubit {} = {:#018x} (live shots) at end of forward; \
                 every non-register qubit must be |0⟩ on every live shot",
                q, v
            ));
        }
        acc.ok = false;
    }
}

pub fn run_tests_streaming(
    mut file: File,
    summary: &Pass1Summary,
    points: &TestPoints,
    xof: &mut Shake256Reader,
    chunk_ops: usize,
    wave_size: usize,
    num_workers: usize,
) -> Result<SeedReport, String> {
    let n = points.targets.len();
    let num_batches = n.div_ceil(BATCH_SIZE);
    let effective_wave = wave_size.clamp(1, num_batches.max(1));
    let rng_bytes_per_batch = summary
        .rng_ops
        .checked_mul(8)
        .ok_or_else(|| "rng_ops * 8 overflows u64".to_string())?;

    let mut acc = BatchVerifyAcc {
        ok: true,
        fail_reason: None,
        classical_failures: 0,
        phase_garbage_batches: 0,
        ancilla_garbage_batches: 0,
        tot_tof: 0,
        tot_cliff: 0,
    };

    let total_qubits = summary.total_qubits as usize;
    let num_bits = summary.num_bits as usize;

    for wave_start in (0..num_batches).step_by(effective_wave) {
        let wave_end = (wave_start + effective_wave).min(num_batches);
        let wave_len = wave_end - wave_start;

        let mut wave_xofs = Vec::with_capacity(wave_len);
        for _ in 0..wave_len {
            wave_xofs.push(xof.clone());
            advance_xof(xof, rng_bytes_per_batch);
        }

        let mut runners: Vec<BatchRunner<'_>> = Vec::with_capacity(wave_len);
        for (offset, batch_xof) in wave_xofs.iter_mut().enumerate() {
            let batch_idx = wave_start + offset;
            let bs = BATCH_SIZE.min(n - batch_idx * BATCH_SIZE);
            let cond_mask: u64 = if bs == 64 { u64::MAX } else { (1u64 << bs) - 1 };

            let mut sim = Simulator::new(total_qubits, num_bits, batch_xof);
            for shot in 0..bs {
                let i = batch_idx * BATCH_SIZE + shot;
                sim.set_register(&summary.regs[0], points.targets[i].0, shot);
                sim.set_register(&summary.regs[1], points.targets[i].1, shot);
                sim.set_register(&summary.regs[2], points.offsets[i].0, shot);
                sim.set_register(&summary.regs[3], points.offsets[i].1, shot);
            }
            runners.push(BatchRunner {
                sim,
                exec_state: SimExecState::new(),
                batch_idx,
                bs,
                cond_mask,
            });
        }

        let mut reader = OpsReader::from_file(file)?;
        if reader.total_ops() != summary.ops_len {
            return Err(format!(
                "ops.bin op count changed between Pass 1 ({}) and Pass 2 ({})",
                summary.ops_len,
                reader.total_ops()
            ));
        }

        fanout_chunks(
            &mut runners,
            num_workers,
            chunk_ops.max(1),
            |buf| {
                let got = reader.read_chunk(buf, chunk_ops.max(1), true)?;
                if got > 0 {
                    check_chunk_bounds(buf, summary.total_qubits, summary.num_bits)?;
                }
                Ok(got)
            },
            |slice, chunk| {
                for r in slice.iter_mut() {
                    r.sim.apply_chunk(&mut r.exec_state, chunk.iter());
                }
            },
        )?;

        let (next_file, wave_digest) = reader.into_file_and_digest()?;
        if wave_digest != summary.file_digest {
            return Err("ops.bin contents changed between Pass 1 and Pass 2".to_string());
        }
        file = next_file;

        for runner in &mut runners {
            verify_batch(runner, summary, points, &mut acc);
        }
    }

    let denom = n.max(1) as f64;
    Ok(SeedReport {
        ok: acc.ok,
        avg_cliff: acc.tot_cliff as f64 / denom,
        avg_tof: acc.tot_tof as f64 / denom,
        tot_tof: acc.tot_tof,
        tot_cliff: acc.tot_cliff,
        n_shots: n,
        classical_failures: acc.classical_failures,
        phase_garbage_batches: acc.phase_garbage_batches,
        ancilla_garbage_batches: acc.ancilla_garbage_batches,
        fail_reason: acc.fail_reason,
    })
}
