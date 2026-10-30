//! R4-SHELL checks for the two fold trims (R4S1 halve-in-place, R4S2 inline table bits).
//! 1. r4s_table_exhaustive: add_table_inline and the inherited add_table against t + val(a) mod 2^w on every t and every
//!    control assignment, small widths, full and short (recycling) pools.
//! 2. r4s_step_vs_base: the 256-bit fused steps with the trims on vs off on identical inputs (random and edge values),
//!    at the pool sizes the shell meets; outputs, flag, pool and phase must agree shot for shot.
//! 3. r4s_paired_exactness (ignored): the full point add, base vs candidate vs negative controls, identical inputs.
use super::builder::{B, ONE};
use super::frogdrop_sched::{p, N};
use super::modp_ft::{self, Ms};
use super::pointadd_lilypad;
use super::tests_frogdrop::Rng;
use crate::circuit::{analyze_ops, Op, QubitId};
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
fn sim(b: &B, tag: &str, init: &dyn Fn(&mut [u64], usize)) -> (Vec<u64>, u64) {
    let (aq, nb, _, _) = analyze_ops(b.ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(tag.as_bytes());
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new((aq as usize).max(b.width() as usize), (nb as usize).max(1), &mut xof);
    for k in 0..64 {
        init(&mut s.qubits, k);
    }
    s.apply_iter(b.ops.iter());
    (s.qubits.clone(), s.phase)
}

#[test]
fn r4s_table_exhaustive() {
    let mut rng = Rng::new(0x4b5_2027);
    let mut configs = 0;
    for &w in &[5usize, 7, 9] {
        for nv in 1..=3usize {
            for trial in 0..4 {
                let na = 1usize << nv;
                let mask = (1u128 << w) - 1;
                let tab: Vec<u128> = (0..na).map(|a| if a == 0 { 0 } else { (rng.next() as u128) & mask }).collect();
                // pools: generous, then short enough to recycle carries in both forms (each keeps > loan lanes)
                for &pool in &[w + 12, w + 3, w - 1, (w + 1) / 2 + 3] {
                    for inline in [false, true] {
                        let val = |a: usize| tab[a];
                        let mut b = B::new();
                        let t = b.alloc_n(w);
                        let vars = b.alloc_n(nv);
                        let pl = b.alloc_n(pool);
                        let ok = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            modp_ft::test_add_table(&mut b, &pl, &t, &vars, &val, inline);
                        }));
                        if ok.is_err() {
                            // the inherited form may refuse a pool its bridge rule rejects; the inline form must not
                            // be asked for less than it can do either: skip only when both refuse
                            continue;
                        }
                        configs += 1;
                        let total = (1usize << w) * na;
                        for base in (0..total).step_by(64) {
                            let (q, ph) = sim(&b, "r4s-tab", &|st, k| {
                                let idx = base + k;
                                if idx < total {
                                    put(st, &t, k, N::from((idx >> nv) as u64));
                                    put(st, &vars, k, N::from((idx & (na - 1)) as u64));
                                }
                            });
                            for k in 0..64.min(total - base) {
                                let idx = base + k;
                                let (tv, a) = (idx >> nv, idx & (na - 1));
                                let want = ((tv as u128 + tab[a]) & mask) as u64;
                                let got = get(&q, &t, k).as_limbs()[0];
                                assert_eq!(got, want, "w {w} nv {nv} trial {trial} pool {pool} inline {inline} t {tv} a {a}");
                                assert_eq!(get(&q, &vars, k).as_limbs()[0] as usize, a);
                                assert_eq!(get(&q, &pl, k), N::ZERO, "pool dirty");
                                assert_eq!((ph >> k) & 1, 0, "phase w {w} nv {nv} pool {pool} inline {inline} t {tv} a {a}");
                            }
                        }
                    }
                }
            }
        }
    }
    eprintln!("r4s_table_exhaustive: {configs} circuits, every (t, a) checked");
    assert!(configs >= 60);
}

/// One fused step on fresh registers; returns (builder, z logical order after the step, y, s lane, ms).
fn one_step(mode: i8, pool: usize, halve: bool, sk: u8) -> (B, Vec<QubitId>, Vec<QubitId>, QubitId, Ms) {
    modp_ft::test_r4(Some(mode));
    let mut b = B::new();
    let mut z = b.alloc_n(256);
    let y = b.alloc_n(256);
    let sq = b.alloc();
    let k = b.alloc();
    let r = b.alloc_n(pool);
    let ms = Ms { k, r, one: ONE };
    let s = match sk {
        0 => None,
        1 => Some(ONE),
        _ => Some(sq),
    };
    if halve {
        modp_ft::signed_modadd_halve(&mut b, &ms, &mut z, &y, s);
    } else {
        modp_ft::signed_modadd_double(&mut b, &ms, &mut z, &y, s);
    }
    modp_ft::test_r4(None);
    (b, z, y, sq, ms)
}

#[test]
fn r4s_step_vs_base() {
    let pm = p();
    let mut rng = Rng::new(0x4b5_1027);
    let edge = [N::ZERO, N::from(1u64), N::from(2u64), pm - N::from(1u64), pm - N::from(2u64), N::from(1u64) << 255,
        (N::from(1u64) << 255) - N::from(1u64), N::from((1u64 << 32) + 977), pm >> 1];
    let mut shots = 0usize;
    let (mut ok_shots, mut approx, mut approx_cand_garbage) = (0usize, 0usize, 0usize);
    let mut tof = [[0u64; 2]; 2];
    for &halve in &[true, false] {
        for &pool in &[47usize, 55, 60, 61, 64, 65, 70, 73, 74, 90, 106, 107, 150, 256] {
            for sk in 0..3u8 {
                let cand_mode = if halve { 19 } else { 2 };
                let (bo, zo, y, sq, mso) = one_step(0, pool, halve, sk);
                let (bn, zn, yn, sqn, msn) = one_step(cand_mode, pool, halve, sk);
                assert_eq!(y, yn);
                assert_eq!(sq, sqn);
                if pool == 106 && sk == 2 {
                    tof[halve as usize] = [bo.tof, bn.tof];
                }
                for batch in 0..6 {
                    let mut zs = vec![];
                    let mut ys = vec![];
                    for i in 0..64 {
                        let j = batch * 64 + i;
                        zs.push(if j < edge.len() * edge.len() { edge[j % edge.len()] } else { rng.below(256) % pm });
                        ys.push(if j < edge.len() * edge.len() { edge[j / edge.len()] } else { rng.below(256) % pm });
                    }
                    let ss: Vec<bool> = (0..64).map(|i| (i * 7 + batch) % 3 != 0).collect();
                    let init = |st: &mut [u64], k: usize| {
                        put(st, &(0..256).map(|i| QubitId(i as u64)).collect::<Vec<_>>(), k, zs[k]);
                        put(st, &y, k, ys[k]);
                        if ss[k] {
                            st[sq.0 as usize] |= 1 << k;
                        }
                    };
                    let (qo, po) = sim(&bo, "r4s-step", &init);
                    let (qn, pn) = sim(&bn, "r4s-step", &init);
                    // garbage masks over 24 measurement seeds on the edge batches, 4 on random ones
                    let gmask = |b: &B, ms: &Ms| -> u64 {
                        let mut g = 0u64;
                        for t in 0..(if batch < 2 { 24 } else { 4 }) {
                            let (q, ph) = sim(b, &format!("r4s-step-{t}"), &init);
                            g |= ph | q[ms.k.0 as usize];
                            for &l in &ms.r { g |= q[l.0 as usize]; }
                        }
                        g
                    };
                    let (go, gn) = (gmask(&bo, &mso), gmask(&bn, &msn));
                    for k in 0..64 {
                        let (vo, vn) = (get(&qo, &zo, k), get(&qn, &zn, k));
                        assert_eq!(vo, vn, "halve {halve} pool {pool} sk {sk} shot {k} z {:?} y {:?}", zs[k], ys[k]);
                        assert_eq!(get(&qn, &yn, k), ys[k]);
                        let sub = sk == 1 || (sk == 2 && ss[k]);
                        let u = if sub { (zs[k] + pm - ys[k]) % pm } else { (zs[k] + ys[k]) % pm };
                        let want = if halve { u.mul_mod((pm + N::from(1u64)) >> 1, pm) } else { u.mul_mod(N::from(2u64), pm) };
                        let clean = |q: &[u64], ms: &Ms, ph: u64| (ph >> k) & 1 == 0 && (q[ms.k.0 as usize] >> k) & 1 == 0 && get(q, &ms.r, k) == N::ZERO;
                        let (co, cn) = (clean(&qo, &mso, po) && (go >> k) & 1 == 0, clean(&qn, &msn, pn) && (gn >> k) & 1 == 0);
                        if vo == want && co {
                            // a correct, clean base shot must be correct and clean on the candidate
                            assert!(cn, "candidate garbage on a clean base shot: halve {halve} pool {pool} sk {sk} shot {k}");
                            ok_shots += 1;
                        } else {
                            // inherited approximation class (values within 2^-32 p of p): same value, garbage may differ
                            approx += 1;
                            if !cn { approx_cand_garbage += 1; }
                        }
                    }
                    shots += 64;
                }
            }
        }
    }
    eprintln!("r4s_step_vs_base: {shots} shots, values identical; {ok_shots} correct+clean on both; {approx} inherited approximation shots ({approx_cand_garbage} with candidate garbage); emitted T at pool 106 (halve old/new, double old/new): {:?} {:?}",
        tof[1], tof[0]);
}

// ---------------------------------------------------------------- full point add, paired
type U = ruint::aliases::U256;

fn curve() -> crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
    let hx = |h: &str| U::from_str_radix(h, 16).unwrap();
    crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U::ZERO,
        b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    }
}

struct Built { ops: Vec<Op>, nq: u64, nb: u64, regs: Vec<Vec<crate::circuit::QubitOrBit>>, data: std::collections::HashSet<u64> }

fn build(mode: i8) -> Built {
    modp_ft::test_r4(Some(mode));
    let mut b = B::new();
    let (xq, yq) = pointadd_lilypad::point_add(&mut b);
    modp_ft::test_r4(None);
    let ops = std::mem::take(&mut b.ops);
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let data = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    eprintln!("R4S mode {mode}: ops {} peak {} nq {nq} expected_t {:.1}", ops.len(), b.peak, super::tests_chunked::expected_t(&ops));
    Built { ops, nq, nb, regs, data }
}

fn run(c: &Built, cases: &[((U, U), (U, U), (U, U))], tag: &str) -> (u64, u64) {
    let mut h = sha3::Shake256::default();
    h.update(tag.as_bytes());
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(c.nq as usize, c.nb as usize, &mut xof);
    for (k, (t, o, _)) in cases.iter().enumerate() {
        s.set_register(&c.regs[0], t.0, k);
        s.set_register(&c.regs[1], t.1, k);
        s.set_register(&c.regs[2], o.0, k);
        s.set_register(&c.regs[3], o.1, k);
    }
    s.apply_iter(c.ops.iter());
    let mut bad = s.phase;
    for (k, (_, _, e)) in cases.iter().enumerate() {
        if s.get_register(&c.regs[0], k) != e.0 || s.get_register(&c.regs[1], k) != e.1 { bad |= 1 << k; }
    }
    for q in 0..c.nq {
        if !c.data.contains(&q) { bad |= s.qubits[q as usize]; }
    }
    let n = cases.len();
    let mask = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
    (bad & mask, s.stats.toffoli_gates)
}

/// R4S_MODES (default "0,19,23,27,51"): 0 = base (trims off), 19 = candidate (R4S1+S2+S3), 23 / 27 / 51 = negative
/// controls (R4S1's parity term wrong / one inline carry lane left uncorrected / R4S3's X left out). R4S_BATCHES x 64 shots, R4S_SEED, 3 threads.
#[test]
#[ignore]
fn r4s_paired_exactness() {
    let batches: usize = std::env::var("R4S_BATCHES").ok().map(|v| v.parse().unwrap()).unwrap_or(160);
    let seed: u64 = std::env::var("R4S_SEED").ok().map(|v| v.parse().unwrap()).unwrap_or(0x2026_1027);
    let modes: Vec<i8> = std::env::var("R4S_MODES").unwrap_or_else(|_| "0,19,23,27,51".into()).split(',').map(|v| v.parse().unwrap()).collect();
    let cs: Vec<Built> = modes.iter().map(|&m| build(m)).collect();
    let cv = curve();
    let to_u = |v: &N| -> U { U::from_limbs(v.as_limbs()[0..4].try_into().unwrap()) };
    let mut rng = Rng::new(seed);
    let mut all = vec![];
    for _ in 0..batches {
        let mut cases = vec![];
        while cases.len() < 64 {
            let k1 = to_u(&(rng.below(250) + N::from(1u64)));
            let k2 = to_u(&(rng.below(250) + N::from(1u64)));
            let t = cv.mul(cv.gx, cv.gy, k1);
            let o = cv.mul(cv.gx, cv.gy, k2);
            if t.0 == o.0 { continue; }
            let e = cv.add(t.0, t.1, o.0, o.1);
            cases.push((t, o, e));
        }
        all.push(cases);
    }
    let next = std::sync::atomic::AtomicUsize::new(0);
    let res = std::sync::Mutex::new(vec![vec![(0u64, 0u64); batches]; cs.len()]);
    std::thread::scope(|sc| {
        for _ in 0..3 {
            sc.spawn(|| loop {
                let i = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                if i >= batches { break; }
                for (j, c) in cs.iter().enumerate() {
                    let r = run(c, &all[i], &format!("r4s-{seed}-{i}"));
                    res.lock().unwrap()[j][i] = r;
                }
            });
        }
    });
    let res = res.into_inner().unwrap();
    let shots = (batches * 64) as f64;
    for (j, m) in modes.iter().enumerate() {
        let fails: u32 = res[j].iter().map(|r| r.0.count_ones()).sum();
        let tof: u64 = res[j].iter().map(|r| r.1).sum();
        eprintln!("R4S_RESULT mode {m}: shots {} failing {fails} ({:.2} per 9024) mean executed T {:.1}",
            batches * 64, fails as f64 * 9024.0 / shots, tof as f64 / shots);
    }
    if let Some(a) = modes.iter().position(|&m| m == 0) {
        for (j, m) in modes.iter().enumerate() {
            if j == a { continue; }
            let diff: u32 = (0..batches).map(|i| (res[a][i].0 ^ res[j][i].0).count_ones()).sum();
            let only: u32 = (0..batches).map(|i| (res[j][i].0 & !res[a][i].0).count_ones()).sum();
            eprintln!("R4S_PAIRED base-vs-mode-{m}: disagreements {diff}, failing only in mode {m}: {only}");
        }
    }
}

#[test]
#[ignore]
fn r4s_debug_pool() {
    let pm = p();
    let pool: usize = std::env::var("R4S_POOL").ok().map(|v| v.parse().unwrap()).unwrap_or(47);
    let mut rng = Rng::new(5);
    for mode in [0i8, 1, 2, 3, 19] {
        for halve in [true, false] {
            let (b, z, y, _sq, ms) = one_step(mode, pool, halve, 0);
            let zs: Vec<N> = (0..64).map(|i| if i == 0 { pm - N::from(1u64) } else { rng.below(256) % pm }).collect();
            let ys: Vec<N> = (0..64).map(|i| if i == 0 { pm - N::from(1u64) } else { rng.below(256) % pm }).collect();
            let (q, ph) = sim(&b, "dbg", &|st, k| { put(st, &(0..256).map(|i| QubitId(i as u64)).collect::<Vec<_>>(), k, zs[k]); put(st, &y, k, ys[k]); });
            let mut bad = 0; let mut badv = 0;
            for k in 0..64 {
                let want = if halve { ((zs[k] + pm - ys[k]) % pm).mul_mod((pm + N::from(1u64)) >> 1, pm) } else { ((zs[k] + pm - ys[k]) % pm).mul_mod(N::from(2u64), pm) };
                if get(&q, &z, k) != want { badv += 1; }
                if (ph >> k) & 1 == 1 || get(&q, &ms.r, k) != N::ZERO || (q[ms.k.0 as usize] >> k) & 1 == 1 { bad += 1; }
            }
            eprintln!("pool {pool} mode {mode} halve {halve}: value-bad {badv} garbage {bad} tof {}", b.tof);
        }
    }
}

#[test]
#[ignore]
fn r4s_debug_edge() {
    let pm = p();
    let pool: usize = std::env::var("R4S_POOL").ok().map(|v| v.parse().unwrap()).unwrap_or(47);
    let zv = pm - N::from(std::env::var("R4S_ZOFF").ok().map(|v| v.parse().unwrap()).unwrap_or(2u64));
    for halve in [true, false] {
    for mode in [0i8, 1, 2, 3, 19] {
        let (b, _z, y, _sq, ms) = one_step(mode, pool, halve, 0);
        let (mut ph_n, mut k_n, mut p_n) = (0, 0, 0);
        for t in 0..16 {
            let (q, ph) = sim(&b, &format!("e{t}"), &|st, k| { put(st, &(0..256).map(|i| QubitId(i as u64)).collect::<Vec<_>>(), k, zv); put(st, &y, k, zv); });
            ph_n += (ph & 1) as u32; k_n += (q[ms.k.0 as usize] & 1) as u32; p_n += (get(&q, &ms.r, 0) != N::ZERO) as u32;
        }
        eprintln!("halve {halve} pool {pool} mode {mode}: of 16 seeds phase {ph_n} k {k_n} pool {p_n}");
    }}
}
