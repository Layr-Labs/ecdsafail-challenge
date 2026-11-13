//! Differential and negative-control gates for the approved Lilypad-G layers.

use super::builder::B;
use super::frogdrop_sched::{p, N};
use super::modp_ft::{
    fix_pair_begin_repay, fix_pair_begin_save, fix_pair_end_repay, fix_pair_end_save,
    fix_pair_test_no_repay, fix_pair_test_reset, offset_test_disabled, product, product_inv,
    product_tail_neg_s, product_tail_neg_s_offset, product_tail_neg_s_offset_uncompute,
    product_tail_neg_s_uncompute, Ms,
};
use super::tests_frogdrop::Rng;
use super::tests_strip::put;
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

fn get_n(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut value = N::ZERO;
    for (i, q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 {
            value |= N::from(1u64) << i;
        }
    }
    value
}

struct PairCircuit {
    b: B,
    a: Vec<QubitId>,
    y: Vec<QubitId>,
    z: Vec<QubitId>,
    z_mid: Vec<QubitId>,
    pool: Vec<QubitId>,
    flag: QubitId,
    mid: usize,
}

fn paired_circuit(tail: bool, pool_len: usize, no_repay: bool) -> PairCircuit {
    fix_pair_test_reset();
    fix_pair_test_no_repay(no_repay);
    let mut b = B::new();
    let (a, y) = (b.alloc_n(256), b.alloc_n(256));
    let flag = b.alloc();
    let pool = b.alloc_n(pool_len);
    let one = b.alloc();
    b.x(one);
    let ms = Ms { k: flag, r: pool.clone(), one };
    let z = b.alloc_n(256);
    let mut zz = z.clone();
    fix_pair_begin_save(if tail { 48 } else { 0 });
    if tail {
        product_tail_neg_s(&mut b, &ms, &mut zz, &a, &y, 256, false);
    } else {
        product(&mut b, &ms, &mut zz, &a, &y);
    }
    fix_pair_end_save();
    let mid = b.ops.len();
    let z_mid = zz.clone();
    fix_pair_begin_repay();
    if tail {
        product_tail_neg_s_uncompute(&mut b, &ms, &mut zz, &a, &y, 256, false, 48);
    } else {
        product_inv(&mut b, &ms, &mut zz, &a, &y);
    }
    fix_pair_end_repay();
    fix_pair_test_no_repay(false);
    PairCircuit { b, a, y, z, z_mid, pool, flag, mid }
}

fn check_pair_batches(tail: bool, pool_len: usize, batches: usize, no_repay: bool) -> (usize, u64, u64) {
    let pc = paired_circuit(tail, pool_len, no_repay);
    let (nq, nb, _, _) = analyze_ops(pc.b.ops.iter());
    let pm = p();
    let inv2_256 = N::from(2u64).pow_mod(pm - N::from(2u64), pm).pow_mod(N::from(256u64), pm);
    let mut bad = 0usize;
    let mut phase = 0u64;
    let mut dirty = 0u64;
    let mut rng = Rng::new(0x4c31_2026 ^ pool_len as u64 ^ u64::from(tail));
    for batch in 0..batches {
        let av: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
        let yv: Vec<N> = (0..64).map(|_| {
            let v = rng.below(256) % pm;
            if v <= N::from(1u64) { N::from(3u64) } else { v }
        }).collect();
        let mut h = sha3::Shake256::default();
        h.update(b"lilypad-l1-paired-fixes");
        h.update(&(batch as u64).to_le_bytes());
        h.update(&(pool_len as u64).to_le_bytes());
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new((nq as usize).max(pc.b.width() as usize), (nb as usize).max(1), &mut xof);
        for shot in 0..64 {
            put(&mut sim.qubits, &pc.a, shot, av[shot]);
            put(&mut sim.qubits, &pc.y, shot, yv[shot]);
        }
        sim.apply_iter(pc.b.ops[..pc.mid].iter());
        for shot in 0..64 {
            let want = if tail {
                (pm - av[shot].mul_mod(yv[shot], pm).mul_mod(inv2_256, pm)) % pm
            } else {
                av[shot].mul_mod(yv[shot], pm)
            };
            bad += usize::from(get_n(&sim.qubits, &pc.z_mid, shot) % pm != want);
        }
        sim.apply_iter(pc.b.ops[pc.mid..].iter());
        phase |= sim.phase;
        for q in pc.z.iter().chain(&pc.pool).chain([&pc.flag]) {
            dirty |= sim.qubits[q.0 as usize];
        }
        for shot in 0..64 {
            bad += usize::from(get_n(&sim.qubits, &pc.a, shot) != av[shot]);
            bad += usize::from(get_n(&sim.qubits, &pc.y, shot) != yv[shot]);
        }
    }
    (bad, phase, dirty)
}

#[test]
#[ignore]
fn lilypad_l1_paired_fixes_10k() {
    for (tail, pool) in [(false, 122usize), (true, 75usize)] {
        let (bad, phase, dirty) = check_pair_batches(tail, pool, 160, false);
        eprintln!("L1 paired tail={tail} pool={pool}: 10240 shots bad={bad} phase={} dirty={}", phase.count_ones(), dirty.count_ones());
        assert_eq!((bad, phase, dirty), (0, 0, 0));
    }
}

#[test]
#[ignore]
fn lilypad_l1_negative_controls() {
    let (bad, phase, dirty) = check_pair_batches(false, 122, 1, true);
    eprintln!("L1 no-repay control: bad={bad} phase={} dirty={}", phase.count_ones(), dirty.count_ones());
    assert!(phase.count_ones() >= 16, "no-repay control did not create the expected relative-phase debt");

    fix_pair_test_reset();
    let mismatch = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut b = B::new();
        let (a, y, z) = (b.alloc_n(256), b.alloc_n(256), b.alloc_n(256));
        let ms1 = Ms::alloc_room(&mut b, 893);
        let mut zz = z.clone();
        fix_pair_begin_save(0);
        product(&mut b, &ms1, &mut zz, &a, &y);
        fix_pair_end_save();
        let ms2 = Ms::alloc_room(&mut b, 886);
        fix_pair_begin_repay();
        product_inv(&mut b, &ms2, &mut zz, &a, &y);
    }));
    fix_pair_test_reset();
    assert!(mismatch.is_err(), "pool/shape mismatch did not trip the keyed debt assertion");
}

fn offset_circuit(disable_offset: bool) -> PairCircuit {
    fix_pair_test_reset();
    offset_test_disabled(disable_offset);
    let mut b = B::new();
    let (a, y) = (b.alloc_n(256), b.alloc_n(256));
    let flag = b.alloc();
    let pool = b.alloc_n(75);
    let one = b.alloc();
    b.x(one);
    let ms = Ms { k: flag, r: pool.clone(), one };
    let z = b.alloc_n(256);
    let mut zz = z.clone();
    fix_pair_begin_save(0);
    product_tail_neg_s_offset(&mut b, &ms, &mut zz, &a, &y, 256);
    fix_pair_end_save();
    let mid = b.ops.len();
    let z_mid = zz.clone();
    fix_pair_begin_repay();
    product_tail_neg_s_offset_uncompute(&mut b, &ms, &mut zz, &a, &y, 256);
    fix_pair_end_repay();
    offset_test_disabled(false);
    PairCircuit { b, a, y, z, z_mid, pool, flag, mid }
}

fn check_offset_batches(batches: usize, disable_offset: bool) -> (usize, u64, u64) {
    let pc = offset_circuit(disable_offset);
    let (nq, nb, _, _) = analyze_ops(pc.b.ops.iter());
    let pm = p();
    let inv2_256 = N::from(2u64).pow_mod(pm - N::from(2u64), pm).pow_mod(N::from(256u64), pm);
    let mut bad = 0usize;
    let mut phase = 0u64;
    let mut dirty = 0u64;
    let mut rng = Rng::new(0x4c33_2026 ^ u64::from(disable_offset));
    for batch in 0..batches {
        let av: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
        let yv: Vec<N> = (0..64).map(|_| {
            let v = rng.below(256) % pm;
            if v <= N::from(1u64) { N::from(3u64) } else { v }
        }).collect();
        let mut h = sha3::Shake256::default();
        h.update(b"lilypad-l3-offset-tail");
        h.update(&(batch as u64).to_le_bytes());
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new((nq as usize).max(pc.b.width() as usize), (nb as usize).max(1), &mut xof);
        for shot in 0..64 {
            put(&mut sim.qubits, &pc.a, shot, av[shot]);
            put(&mut sim.qubits, &pc.y, shot, yv[shot]);
        }
        sim.apply_iter(pc.b.ops[..pc.mid].iter());
        for shot in 0..64 {
            let want = (pm - av[shot].mul_mod(yv[shot], pm).mul_mod(inv2_256, pm)) % pm;
            bad += usize::from(get_n(&sim.qubits, &pc.z_mid, shot) % pm != want);
        }
        sim.apply_iter(pc.b.ops[pc.mid..].iter());
        phase |= sim.phase;
        for q in pc.z.iter().chain(&pc.pool).chain([&pc.flag]) {
            dirty |= sim.qubits[q.0 as usize];
        }
        for shot in 0..64 {
            bad += usize::from(get_n(&sim.qubits, &pc.a, shot) != av[shot]);
            bad += usize::from(get_n(&sim.qubits, &pc.y, shot) != yv[shot]);
        }
    }
    (bad, phase, dirty)
}

#[test]
#[ignore]
fn lilypad_l3_offset_tail_10k() {
    let (bad, phase, dirty) = check_offset_batches(160, false);
    eprintln!("L3 offset tail: 10240 shots bad={bad} phase={} dirty={}", phase.count_ones(), dirty.count_ones());
    assert_eq!((bad, phase, dirty), (0, 0, 0));
}

#[test]
#[ignore]
fn lilypad_l3_negative_control() {
    let (bad, phase, dirty) = check_offset_batches(4, true);
    eprintln!("L3 no-offset control: 256 shots bad={bad} phase={} dirty={}", phase.count_ones(), dirty.count_ones());
    assert!(bad > 0 || phase != 0 || dirty != 0, "no-offset control did not fire");
}
