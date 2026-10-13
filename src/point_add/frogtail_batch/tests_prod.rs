//! Shell-product prototypes: signed-digit modular adds and products against integer references.

use super::builder::B;
use super::frogdrop_sched::{p, N};
use super::modp_ft::*;
use super::tests_frogdrop::Rng;
use crate::circuit::{analyze_ops, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};
use sha3::digest::XofReader;

/// Deterministic HMR masks: all-zero, all-one, alternating, and a distinct
/// splitmix mask for every measurement.  The last mode prevents accidentally
/// relying on correlations between retained receipts and the unchanged local
/// inverse oracles.
struct ForcedHmr { mode: u8, state: u64 }
impl XofReader for ForcedHmr {
    fn read(&mut self, out: &mut [u8]) {
        assert_eq!(out.len(), 8);
        let v = match self.mode {
            0 => 0,
            1 => u64::MAX,
            2 => { self.state = self.state.rotate_left(1); self.state },
            3 => {
                self.state = self.state.wrapping_add(0x9e3779b97f4a7c15);
                let mut z = self.state;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
                z ^ (z >> 31)
            },
            _ => unreachable!(),
        };
        out.copy_from_slice(&v.to_le_bytes());
    }
}

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

fn assert_transport_clean(
    b: &B,
    data: &[QubitId],
    zero: &[QubitId],
    one: QubitId,
    spectator: QubitId,
    init_data: &[N],
    spectator_mask: u64,
    tag: &str,
) {
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    for mode in 0..=3 {
        let mut xof = ForcedHmr { mode, state: 0x0123_4567_89ab_cdef };
        let mut sim = Simulator::new((nq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
        for (word, qs) in init_data.iter().zip(data.chunks_exact(256)) {
            for shot in 0..64 { put(&mut sim.qubits, qs, shot, *word); }
        }
        sim.qubits[spectator.0 as usize] = spectator_mask;
        sim.apply_iter(b.ops.iter());
        assert_eq!(sim.phase, 0, "{tag} forced-HMR mode {mode}: phase");
        for (word, qs) in init_data.iter().zip(data.chunks_exact(256)) {
            for shot in 0..64 { assert_eq!(get(&sim.qubits, qs, shot), *word, "{tag} mode {mode}: data"); }
        }
        assert_eq!(sim.qubits[spectator.0 as usize], spectator_mask, "{tag} mode {mode}: spectator");
        assert_eq!(sim.qubits[one.0 as usize], u64::MAX, "{tag} mode {mode}: one");
        for &q in zero { assert_eq!(sim.qubits[q.0 as usize], 0, "{tag} mode {mode}: dirty q{}", q.0); }
    }
}

/// Native dy transport: fixed [67,189] producer plan, all 255 receipts,
/// unchanged inverse add/halve oracles, arbitrary spectator restored.
#[test]
fn sum_carry_dy_transport_forced_hmr() {
    let mut b = B::new();
    let a = b.alloc_n(256); let y = b.alloc_n(256); let z = b.alloc_n(256);
    let spectator = b.alloc(); let k = b.alloc(); let r = b.alloc_n(190); let one = b.alloc(); b.x(one);
    let ms = Ms { k, r, one };
    let mut zz = z.clone();
    b.begin(); product_sum_transport(&mut b, &ms, &mut zz, &a, &y); let rec = b.end();
    b.play(&rec, false);
    product_inv_sum_transport(&mut b, &ms, &mut zz, &a, &y);
    assert_eq!(zz, z);
    let av = N::from_str_radix("9b18f2d77c8d31a4bb2d57e079f1641c0a4d6623b992e52d81f5e1d07ab43915", 16).unwrap();
    let yv = N::from_str_radix("56d3c2a1938354bdf60896cc90112ddae901e7f7d8fe7b4b5a311be35cb12731", 16).unwrap();
    let mut data = a.clone(); data.extend_from_slice(&y);
    let mut zero = z.clone(); zero.push(ms.k); zero.extend_from_slice(&ms.r);
    assert_transport_clean(&b, &data, &zero, ms.one, spectator, &[av, yv], 0xa55a_f00f_9696_3cc3, "dy");
}

/// Native full-tail transport: two receipts for every semantic step.  The
/// suffix uses forward inverse arithmetic and the prefix uses segmented
/// literal-inverse seams.
#[test]
fn sum_carry_tail_full_forced_hmr() {
    let mut b = B::new();
    let c = b.alloc_n(256); let y = b.alloc_n(256); let z = b.alloc_n(256);
    let spectator = b.alloc(); let k = b.alloc(); let r = b.alloc_n(117); let one = b.alloc(); b.x(one);
    let ms = Ms { k, r, one };
    let mut zz = z.clone();
    b.begin();
    product_tail_neg_s_sum_transport(&mut b, &ms, &mut zz, &c, &y, 256, false, 0);
    let rec = b.end();
    b.play(&rec, false);
    product_tail_neg_s_uncompute_sum_transport(&mut b, &ms, &mut zz, &c, &y, 256, false, 48);
    assert_eq!(zz, z);
    let cv = N::from_str_radix("dfe97760c6230c98fdd39520fdc79d17b1f9130f1053b8f646925e7fe1aa049d", 16).unwrap();
    let yv = N::from_str_radix("318a421c05bb621be9d5dc766af085304764a9c7e46165ea1cc68d9c24bba6f3", 16).unwrap();
    let mut data = c.clone(); data.extend_from_slice(&y);
    let mut zero = z.clone(); zero.push(ms.k); zero.extend_from_slice(&ms.r);
    assert_transport_clean(&b, &data, &zero, ms.one, spectator, &[cv, yv], 0x6996_c33c_5aa5_0ff0, "tail");
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
