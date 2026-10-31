//! R2-LANES paired exactness check: the full point add built with the odd-tick Q lend in mode 0 (off, = b2e876),
//! 1 (production: odd ticks) and 2 (negative control: every tick) is simulated on identical random point pairs.
//! Per shot: x3/y3 value, phase and every non-output qubit clean. Reports failures per mode and 0-vs-1 disagreements.
//! R2L_BATCHES (default 160) x 64 shots, R2L_SEED, 3 threads.
use super::builder::B;
use super::frogdrop_sched::N;
use super::lilypad_g::r2l_test_mode;
use super::pointadd_lilypad;
use super::tests_frogdrop::Rng;
use crate::circuit::{analyze_ops, Op};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

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

fn build(mode: u8) -> Built {
    r2l_test_mode(Some(mode));
    let mut b = B::new();
    let (xq, yq) = pointadd_lilypad::point_add(&mut b);
    r2l_test_mode(None);
    let ops = std::mem::take(&mut b.ops);
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let data = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    eprintln!("R2L mode {mode}: ops {} peak {} nq {nq} expected_t {:.1}", ops.len(), b.peak, super::tests_chunked::expected_t(&ops));
    Built { ops, nq, nb, regs, data }
}

/// Returns (fail mask, total executed Toffoli over the 64 shots).
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

#[test]
#[ignore]
fn r2l_paired_exactness() {
    let batches: usize = std::env::var("R2L_BATCHES").ok().map(|v| v.parse().unwrap()).unwrap_or(160);
    let seed: u64 = std::env::var("R2L_SEED").ok().map(|v| v.parse().unwrap()).unwrap_or(0x2026_1026);
    let modes: Vec<u8> = std::env::var("R2L_MODES").unwrap_or_else(|_| "0,1,2".into()).split(',').map(|v| v.parse().unwrap()).collect();
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
                    let r = run(c, &all[i], &format!("r2l-{seed}-{i}"));
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
        eprintln!("R2L_RESULT mode {m}: shots {} failing {fails} ({:.2} per 9024) mean executed T {:.1}",
            batches * 64, fails as f64 * 9024.0 / shots, tof as f64 / shots);
    }
    if let (Some(a), Some(b)) = (modes.iter().position(|&m| m == 0), modes.iter().position(|&m| m == 1)) {
        let diff: u32 = (0..batches).map(|i| (res[a][i].0 ^ res[b][i].0).count_ones()).sum();
        let only1: u32 = (0..batches).map(|i| (res[b][i].0 & !res[a][i].0).count_ones()).sum();
        eprintln!("R2L_PAIRED off-vs-odd disagreements {diff} (odd-only failures {only1})");
    }
    if let (Some(a), Some(c)) = (modes.iter().position(|&m| m == 0), modes.iter().position(|&m| m == 2)) {
        let only2: u32 = (0..batches).map(|i| (res[c][i].0 & !res[a][i].0).count_ones()).sum();
        eprintln!("R2L_NEGCTL every-tick-only failures {only2}");
    }
}
