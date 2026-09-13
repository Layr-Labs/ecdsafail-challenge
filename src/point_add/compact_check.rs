//! Developer validation of the exact expanded primitive stream with shared RAM blocks.
//! Official Vec loader and canonical remote benchmark are separate requirements.
use alloy_primitives::U256;
use crate::circuit::{analyze_ops, Op, QubitId, QubitOrBit};
use crate::sim::Simulator;
use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
use sha3::{digest::{ExtendableOutput,Update,XofReader},Shake256};
use std::sync::Arc;
struct Program { blocks: Vec<Arc<Vec<Op>>>, len: usize }
impl Program {
    fn len(&self)->usize { self.len }
    fn iter(&self)->impl Iterator<Item=&Op> { self.blocks.iter().flat_map(|block|block.iter()) }
}
// Copied trusted evaluator SHA256: b35314bc47a5f8eecbf60459e6c76c9b43aa034eeb9b7ec3421655d74f9e890b
pub(super) fn secp256k1() -> WeierstrassEllipticCurve {
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

// ─── Fiat-Shamir seed ──────────────────────────────────────────────────────
//
// SHAKE256 over the op stream. Determines test inputs, simulator RNG for
// R/Hmr phase randomization, etc.

fn fiat_shamir_seed(ops: &Program) -> sha3::Shake256Reader {
    let mut hasher = Shake256::default();
    hasher.update(b"quantum_ecc-fiat-shamir-v2");
    hasher.update(&(ops.len() as u64).to_le_bytes());
    for op in ops.iter() {
        hasher.update(&[op.kind as u8]);
        hasher.update(&op.q_control2.0.to_le_bytes());
        hasher.update(&op.q_control1.0.to_le_bytes());
        hasher.update(&op.q_target.0.to_le_bytes());
        hasher.update(&op.c_target.0.to_le_bytes());
        hasher.update(&op.c_condition.0.to_le_bytes());
        hasher.update(&op.r_target.0.to_le_bytes());
    }
    hasher.finalize_xof()
}

// ─── Test runner ──────────────────────────────────────────────────────────

struct SeedReport {
    ok: bool,
    avg_cliff: f64,
    avg_tof: f64,
    tot_tof: u64,
    tot_cliff: u64,
    n_shots: usize,
    classical_failures: usize,
    phase_garbage_batches: usize,
    ancilla_garbage_batches: usize,
    fail_reason: Option<String>,
}

fn run_tests(
    ops: &Program,
    layout_regs: &[Vec<QubitOrBit>],
    total_qubits: u64,
    num_bits: u64,
    mut xof: sha3::Shake256Reader,
    target_shots: usize,
) -> SeedReport {
    let curve = secp256k1();

    let mut targets = Vec::with_capacity(target_shots);
    let mut offsets = Vec::with_capacity(target_shots);
    let mut expected = Vec::with_capacity(target_shots);
    for _ in 0..target_shots {
        let mut rb = [[0u8; 32]; 2];
        // Disambiguate from std::io::Read (in scope for the zstd loader).
        XofReader::read(&mut xof, &mut rb[0]);
        XofReader::read(&mut xof, &mut rb[1]);
        let k1 = U256::from_le_bytes(rb[0]);
        let k2 = U256::from_le_bytes(rb[1]);
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        if t.0 == o.0 {
            continue;
        }
        if t.0.is_zero() && t.1.is_zero() {
            continue;
        }
        if o.0.is_zero() && o.1.is_zero() {
            continue;
        }
        let e = curve.add(t.0, t.1, o.0, o.1);
        targets.push(t);
        offsets.push(o);
        expected.push(e);
    }
    let n = targets.len();

    let mut sim = Simulator::new(total_qubits as usize, num_bits as usize, &mut xof);
    let mut ok = true;
    let mut fail_reason: Option<String> = None;
    let mut classical_failures = 0usize;
    let mut phase_garbage_batches = 0usize;
    let mut ancilla_garbage_batches = 0usize;

    const BATCH: usize = 64;
    let num_batches = (n + BATCH - 1) / BATCH;
    for batch in 0..num_batches {
        let bs = BATCH.min(n - batch * BATCH);
        let cond_mask: u64 = if bs == 64 { u64::MAX } else { (1u64 << bs) - 1 };

        sim.clear_for_shot();
        for shot in 0..bs {
            let i = batch * BATCH + shot;
            sim.set_register(&layout_regs[0], targets[i].0, shot);
            sim.set_register(&layout_regs[1], targets[i].1, shot);
            sim.set_register(&layout_regs[2], offsets[i].0, shot);
            sim.set_register(&layout_regs[3], offsets[i].1, shot);
        }

        sim.apply_iter(ops.iter());

        for shot in 0..bs {
            let i = batch * BATCH + shot;
            let gx = sim.get_register(&layout_regs[0], shot);
            let gy = sim.get_register(&layout_regs[1], shot);
            if gx != expected[i].0 || gy != expected[i].1 {
                classical_failures += 1;
                if fail_reason.is_none() {
                    fail_reason = Some(format!(
                        "CLASSICAL MISMATCH shot {i}: got ({:#x},{:#x}) exp ({:#x},{:#x})",
                        gx, gy, expected[i].0, expected[i].1
                    ));
                }
                ok = false;
            }
        }

        let phase = sim.phase & cond_mask;
        if phase != 0 {
            phase_garbage_batches += 1;
            let msg = format!(
                "PHASE GARBAGE: global_phase = {:#018x} across {} live shots (must be 0)",
                phase, bs
            );
            if fail_reason.is_none() {
                fail_reason = Some(msg);
            }
            ok = false;
        }

        for register in layout_regs {
            for qb in register {
                if let QubitOrBit::Qubit(q) = *qb {
                    *sim.qubit_mut(q) = 0;
                }
            }
        }
        let mut garbage_q: Option<u64> = None;
        for q in 0..total_qubits {
            let v = sim.qubit(QubitId(q)) & cond_mask;
            if v != 0 {
                garbage_q = Some(q);
                break;
            }
        }
        if let Some(q) = garbage_q {
            ancilla_garbage_batches += 1;
            let v = sim.qubit(QubitId(q)) & cond_mask;
            let msg = format!(
                "ANCILLA GARBAGE: qubit {} = {:#018x} (live shots) at end of forward; \
                 every non-register qubit must be |0⟩ on every live shot",
                q, v
            );
            if fail_reason.is_none() {
                fail_reason = Some(msg);
            }
            ok = false;
        }
        eprintln!("COMPACT_BATCH {}/{} shots={} ok={} reason={:?}", batch+1,num_batches,(batch*BATCH+bs),ok,fail_reason);
    }

    let _ = num_bits;
    let denom = n.max(1) as f64;
    SeedReport {
        ok,
        avg_cliff: sim.stats.clifford_gates as f64 / denom,
        avg_tof: sim.stats.toffoli_gates as f64 / denom,
        tot_tof: sim.stats.toffoli_gates,
        tot_cliff: sim.stats.clifford_gates,
        n_shots: n,
        classical_failures,
        phase_garbage_batches,
        ancilla_garbage_batches,
        fail_reason,
    }
}


pub(super) fn run() {
    assert!(super::trailmix_port::inversion::paper2607_eea::optimized_shared_configuration());
    assert!(std::env::var_os("POINT_ADD_COUNT_ONLY").is_none());
    let started=std::time::Instant::now();
    let mut b=super::trailmix_port::build_builder();
    assert!(!b.count_only);b.flush_compact_block();
    let program=Program { blocks:b.compact_blocks.take().unwrap(),len:b.counted_ops };
    assert_eq!(program.blocks.iter().map(|x|x.len()).sum::<usize>(),program.len());
    let mut unique=std::collections::HashSet::new();let mut stored=0usize;
    for block in &program.blocks {
        if unique.insert(Arc::as_ptr(block)) {
            for op in block.iter() {op.validate();}
            stored+=block.len();
        }
    }
    eprintln!("COMPACT_BUILT expanded_ops={} blocks={} unique_blocks={} stored_ops={} stored_bytes={} elapsed={:?}",
        program.len(),program.blocks.len(),unique.len(),stored,stored*std::mem::size_of::<Op>(),started.elapsed());
    let (nq,nb,nr,regs)=analyze_ops(program.iter());
    assert_eq!(nq,if super::trailmix_port::inversion::rank5_lifecycle::enabled(){799}else{802});assert_eq!(nr,4);assert_eq!(regs.len(),4);
    for (i,reg) in regs.iter().enumerate() {
        assert_eq!(reg.len(),256);
        for wire in reg {assert_eq!(matches!(wire,QubitOrBit::Qubit(_)),i<2);}
    }
    eprintln!("COMPACT_LAYOUT qubits={nq} bits={nb} elapsed={:?}; hashing actual expanded circuit",started.elapsed());
    let xof=fiat_shamir_seed(&program);
    eprintln!("COMPACT_HASH_DONE elapsed={:?}; starting unchanged 9024-shot test algorithm",started.elapsed());
    let r=run_tests(&program,&regs,nq,nb,xof,9024);
    eprintln!("COMPACT_WHOLE_RESULT ok={} shots={} qubits={} expanded_ops={} avg_T={} avg_cliff={} total_T={} total_cliff={} classical_failures={} phase_batches={} ancilla_batches={} reason={:?} elapsed={:?}; DEVELOPMENT VERIFICATION, NOT OFFICIAL SCORE",
        r.ok,r.n_shots,nq,program.len(),r.avg_tof,r.avg_cliff,r.tot_tof,r.tot_cliff,r.classical_failures,r.phase_garbage_batches,r.ancilla_garbage_batches,r.fail_reason,started.elapsed());
    assert!(r.ok,"whole point addition failed: {:?}",r.fail_reason);
}
