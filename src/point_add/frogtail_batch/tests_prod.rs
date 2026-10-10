//! Shell-product prototypes: signed-digit modular adds and products against integer references.

use super::builder::B;
use super::frogdrop_sched::{p, N};
use super::modp_ft::*;
use super::tests_frogdrop::Rng;
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

fn put(w: &mut [u64], qs: &[QubitId], shot: usize, v: N) {
    for (i, q) in qs.iter().enumerate() {
        if v.bit(i) {
            w[q.0 as usize] |= 1 << shot;
        }
    }
}
fn get(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}
fn run(b: &B, init: &dyn Fn(&mut [u64], usize)) -> (Vec<u64>, u64, u64) {
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"ftprod");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
    for k in 0..64 {
        init(&mut s.qubits, k);
    }
    s.apply_iter(b.ops.iter());
    (s.qubits.clone(), s.phase, s.stats.toffoli_gates)
}

#[test]
fn ftprod_signed_modadd() {
    let pm = p();
    let mut rng = Rng::new(77);
    for &pool in &[64usize, 76, 147, 255, 256] {
        let mut b = B::new();
        let (z, y, sq) = (b.alloc_n(256), b.alloc_n(256), b.alloc());
        let k = b.alloc();
        let r = b.alloc_n(pool);
        let one = b.alloc();
        b.x(one);
        let ms = Ms { k, r, one };
        let t0 = b.tof;
        b.x(sq);
        signed_modadd(&mut b, &ms, &z, &y, Some(sq));
        b.x(sq);
        let tt = b.tof - t0;
        let zs: Vec<N> = (0..64)
            .map(|i| match i {
                1 | 2 | 4 => N::from(i as u64 - 1),
                _ => rng.below(256) % pm,
            })
            .collect();
        let ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
        let ss: Vec<bool> = (0..64).map(|i| i % 3 == 0).collect();
        let (q, ph, _) = run(&b, &|w, k| {
            put(w, &z, k, zs[k]);
            put(w, &y, k, ys[k]);
            if ss[k] {
                w[sq.0 as usize] |= 1 << k;
            }
        });
        let mut bad = 0;
        for k in 0..64 {
            // subtract where sq = 0
            let want = if ss[k] { (zs[k] + ys[k]) % pm } else { (zs[k] + pm - ys[k]) % pm };
            let got = get(&q, &z, k);
            let pk = (ph >> k) & 1;
            let kk = (q[ms.k.0 as usize] >> k) & 1;
            if got != want || pk != 0 || kk != 0 {
                bad += 1;
                eprintln!("pool {pool} shot {k} sub {} ok {} phase {pk} k {kk}", !ss[k], got == want);
            }
        }
        eprintln!("signed_modadd pool {pool}: {tt} T emitted, bad {bad}");
        assert_eq!(bad, 0);
    }
}

#[test]
fn ftprod_reduce_hi() {
    let pm = p();
    let mut rng = Rng::new(91);
    let mut b = B::new();
    let r = b.alloc_n(318);
    let tq = b.alloc_n(72);
    let pool = b.alloc_n(255);
    b.begin();
    reduce_hi(&mut b, &r, &tq, &pool);
    let rec = b.end();
    let t0 = b.tof;
    b.play(&rec, false);
    let tf = b.tof - t0;
    let split = b.ops.len();
    b.play(&rec, true);
    let m318 = (N::from(1u64) << 318) - N::from(1u64);
    // C_T values: random widths up to 318 lanes, both signs, some with trailing zeros
    let cs: Vec<N> = (0..64)
        .map(|k| {
            let w = 200 + (k * 7) % 117;
            let v = rng.below(w) << (k % 9);
            if k % 2 == 1 { (m318 + N::from(1u64) - v) & m318 } else { v & m318 }
        })
        .collect();
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"ftprod-red");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
    for k in 0..64 {
        put(&mut s.qubits, &r, k, cs[k]);
    }
    let init = s.qubits.clone();
    s.apply_iter(b.ops[..split].iter());
    assert_eq!(s.phase, 0);
    for k in 0..64 {
        let c = cs[k];
        let cm = if c.bit(317) { pm - (((m318 + N::from(1u64)) - c) % pm) } else { c % pm };
        let lo = get(&s.qubits, &r[..256], k);
        assert_eq!(lo % pm, cm % pm, "shot {k}");
        assert_eq!(get(&s.qubits, &r[256..], k), c >> 256, "hi kept {k}");
        for q in tq.iter().chain(&pool) {
            assert_eq!((s.qubits[q.0 as usize] >> k) & 1, 0, "scratch clean");
        }
    }
    s.apply_iter(b.ops[split..].iter());
    assert_eq!(s.qubits, init, "undo restores");
    assert_eq!(s.phase, 0);
    eprintln!("reduce_hi: {tf} T each way");
}

fn roundtrip(tail: bool, pool: usize) -> (u64, usize, u64, u64) {
    let pm = p();
    let mut rng = Rng::new(5 + pool as u64);
    let mut b = B::new();
    let (a, y) = (b.alloc_n(256), b.alloc_n(256));
    let k = b.alloc();
    let r = b.alloc_n(pool);
    let one = b.alloc();
    b.x(one);
    let ms = Ms { k, r, one };
    let z = b.alloc_n(256);
    let mut zz = z.clone();
    let t0 = b.tof;
    assert!(!tail, "tails are uncomputed by their exact reverse (see pointadd_frogtail)");
    product(&mut b, &ms, &mut zz, &a, &y);
    let tf = b.tof - t0;
    let mid = b.ops.len();
    let zmid = zz.clone();
    product_inv(&mut b, &ms, &mut zz, &a, &y);
    let avs: Vec<N> = (0..64).map(|i| if i < 4 { N::from(i as u64) << (i * 3) } else { rng.below(256) % pm }).collect();
    let ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"ftprod-rt");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
    for k in 0..64 {
        put(&mut s.qubits, &a, k, avs[k]);
        put(&mut s.qubits, &y, k, ys[k]);
    }
    s.apply_iter(b.ops[..mid].iter());
    let inv2 = N::from(2u64).pow_mod(pm - N::from(2u64), pm);
    let mut badv = 0;
    for k in 0..64 {
        let want = if tail {
            (pm - avs[k].mul_mod(ys[k], pm).mul_mod(inv2.pow_mod(N::from(556u64), pm), pm)) % pm
        } else {
            avs[k].mul_mod(ys[k], pm)
        };
        if get(&s.qubits, &zmid, k) != want {
            badv += 1;
        }
    }
    let ph1 = s.phase;
    s.apply_iter(b.ops[mid..].iter());
    let mut dirty = 0u64;
    for q in z.iter().chain(&ms.r).chain([&ms.k]) {
        dirty |= s.qubits[q.0 as usize];
    }
    (tf, badv, ph1 | s.phase, dirty)
}

#[test]
fn ftprod_roundtrips() {
    for tail in [false] {
        for pool in [76usize, 147, 256] {
            let (tf, badv, ph, dirty) = roundtrip(tail, pool);
            eprintln!("tail {tail} pool {pool}: fwd {tf} T, bad values {badv}, phase {ph:#x}, dirty {dirty:#x}");
            assert_eq!((badv, ph, dirty), (0, 0, 0));
        }
    }
}

/// Average executed Toffoli per shell phase on 64 random point additions.
#[test]
#[ignore]
fn ftprod_phase_profile() {
    use super::pointadd_frogtail::CKS;
    let mut b = B::new();
    let (_x, _y) = super::pointadd_frogtail::point_add(&mut b);
    let ops = std::mem::take(&mut b.ops);
    let cks = CKS.with(|c| c.borrow().clone());
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let mut rng = Rng::new(31);
    let pm = p();
    let mut h = sha3::Shake256::default();
    h.update(b"ftprod-prof");
    let mut xof = h.finalize_xof();
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
    for k in 0..64 {
        for r in 0..4 {
            let v = rng.below(256) % pm;
            let u = ruint::aliases::U256::from_limbs(v.as_limbs()[0..4].try_into().unwrap());
            sim.set_register(&regs[r], u, k);
        }
    }
    let mut last = 0usize;
    let mut lt = 0u64;
    let mut prev = "start".to_string();
    for (name, at) in cks.iter().cloned().chain([("END".to_string(), ops.len())]) {
        sim.apply_iter(ops[last..at].iter());
        let t = sim.stats.toffoli_gates;
        eprintln!("{:28} avg T {:>9}", prev, (t - lt) / 64);
        lt = t;
        last = at;
        prev = name;
    }
    eprintln!("total avg T {}", lt / 64);
}

#[test]
fn ftprod_signed_roundtrip() {
    let pm = p();
    for &(pool, s1) in &[(147usize, false), (147, true), (76, false), (76, true), (256, false), (256, true)] {
        let mut rng = Rng::new(3 + pool as u64);
        let mut b = B::new();
        let (z, y) = (b.alloc_n(256), b.alloc_n(256));
        let k = b.alloc();
        let r = b.alloc_n(pool);
        let one = b.alloc();
        b.x(one);
        let ms = Ms { k, r, one };
        // first op: subtract if s1, then the inverse op
        signed_modadd(&mut b, &ms, &z, &y, if s1 { Some(ms.one) } else { None });
        let mid = b.ops.len();
        signed_modadd(&mut b, &ms, &z, &y, if s1 { None } else { Some(ms.one) });
        let zs: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
        let ys: Vec<N> = (0..64).map(|_| rng.below(256) % pm).collect();
        let (aq, nb, _, _) = analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"ftprod-srt");
        let mut xof = h.finalize_xof();
        let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
        for k in 0..64 {
            put(&mut s.qubits, &z, k, zs[k]);
            put(&mut s.qubits, &y, k, ys[k]);
        }
        s.apply_iter(b.ops[..mid].iter());
        let p1 = s.phase;
        s.apply_iter(b.ops[mid..].iter());
        let mut bad = 0;
        for k in 0..64 {
            if get(&s.qubits, &z, k) != zs[k] {
                bad += 1;
            }
        }
        eprintln!("pool {pool} sub-first {s1}: phase after 1st {p1:#x}, after 2nd {:#x}, bad {bad}", s.phase);
    }
}

