//! R4-ERASE tests. (1) r4e_sdm_kernel_exhaustive: the signed-digit eraser multiply against the integer oracle
//! q (1 + 2 e a) mod 2^n on every input with e = 0 or q[0] = 0, n = 3..=8, carry banks from 1 lane to full, four forced
//! measurement tapes each way; operands and e restored, bank clean and phase 0 after the forward play, the inverse
//! play restores the start state. Negative control: dropping the merged row 0 (closing subtract) must fail.
//! (2) r4e_paired_exactness: the full point add in modes 0 = SDM off (R2-LANES tree), 1 = on, 2/3 = negative controls
//! (no D up-rotation / unskipped mask lane) on identical random point pairs; x3, y3, phase and every other qubit.
//! R4E_BATCHES (default 160) x 64 shots, R4E_SEED, R4E_MODES (default 0,1,2), 3 threads.
use super::builder::B;
use super::frogdrop_sched::N;
use super::lilypad::{r4e_hold_override, r4e_neg_set, r4e_sdm_mul, r4e_sdm_override, r4e_trim_override};
use super::pointadd_lilypad;
use super::tests_frogdrop::Rng;
use crate::circuit::{analyze_ops, Op, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update, XofReader};

struct Fixed(u8);
impl XofReader for Fixed {
    fn read(&mut self, out: &mut [u8]) { out.fill(self.0); }
}
fn put(sim: &mut Simulator<Fixed>, qs: &[QubitId], lane: usize, v: u64) {
    for (i, q) in qs.iter().enumerate() { if v >> i & 1 != 0 { sim.qubits[q.0 as usize] |= 1 << lane; } }
}
fn get(sim: &Simulator<Fixed>, qs: &[QubitId], lane: usize) -> u64 {
    qs.iter().enumerate().map(|(i, q)| ((sim.qubits[q.0 as usize] >> lane) & 1) << i).sum()
}

/// Returns the number of checked (input, tape) cases; panics on any mismatch unless `expect_fail`, in which case it
/// returns 0 as soon as one mismatch is seen.
fn kernel(n: usize, room: usize, expect_fail: bool) -> usize {
    let mut b = B::new();
    let q = b.alloc_n(n);
    let a = b.alloc_n(n - 1);
    let e = b.alloc();
    let pool = b.alloc_n(room);
    b.begin();
    r4e_sdm_mul(&mut b, &a, &q, e, &pool);
    let r = b.end();
    b.play(&r, false);
    let split = b.ops.len();
    b.play(&r, true);
    let (nq, nb, _, _) = analyze_ops(b.ops.iter());
    let mask = (1u64 << n) - 1;
    let cases: Vec<(u64, u64, u64)> = (0..1u64 << n)
        .flat_map(|qv| (0..1u64 << (n - 1)).flat_map(move |av| [0u64, 1].into_iter().map(move |ev| (qv, av, ev))))
        .filter(|&(qv, _, ev)| ev == 0 || qv & 1 == 0)
        .collect();
    let mut checked = 0;
    for fb in [0u8, 255, 170, 85] {
        for ib in [0u8, 255, 170, 85] {
            for batch in cases.chunks(64) {
                let mut tape = Fixed(fb);
                let mut sim = Simulator::new((nq as usize).max(b.width() as usize), nb as usize, &mut tape);
                for (i, &(qv, av, ev)) in batch.iter().enumerate() {
                    put(&mut sim, &q, i, qv);
                    put(&mut sim, &a, i, av);
                    put(&mut sim, &[e], i, ev);
                }
                let init = sim.qubits.clone();
                sim.apply_iter(b.ops[..split].iter());
                let mut bad = sim.phase;
                for (i, &(qv, av, ev)) in batch.iter().enumerate() {
                    let want = qv.wrapping_mul(1 + 2 * ev * av) & mask;
                    if get(&sim, &q, i) != want || get(&sim, &a, i) != av || get(&sim, &[e], i) != ev { bad |= 1 << i; }
                }
                for p in &pool { bad |= sim.qubits[p.0 as usize]; }
                let lanes = if batch.len() == 64 { u64::MAX } else { (1u64 << batch.len()) - 1 };
                if bad & lanes != 0 {
                    if expect_fail { return 0; }
                    panic!("SDM n{n} room{room} tape{fb}/{ib}: mismatch mask {:x}", bad & lanes);
                }
                sim.xof.0 = ib;
                sim.apply_iter(b.ops[split..].iter());
                let mut bad = sim.phase;
                for (x, y) in sim.qubits.iter().zip(&init) { bad |= x ^ y; }
                if bad & lanes != 0 {
                    if expect_fail { return 0; }
                    panic!("SDM n{n} room{room} tape{fb}/{ib}: inverse not restoring, mask {:x}", bad & lanes);
                }
                checked += batch.len();
            }
        }
    }
    checked
}

#[test]
fn r4e_sdm_kernel_exhaustive() {
    let mut checked = 0;
    for n in 3..=8 {
        for room in [2, 3, 4, n] {
            checked += kernel(n, room, false);
        }
    }
    eprintln!("R4E_SDM_KERNEL exhaustive cases {checked}");
    r4e_neg_set(3);
    let neg = kernel(6, 6, true);
    r4e_neg_set(0);
    assert_eq!(neg, 0, "negative control (no merged row 0) passed");
    eprintln!("R4E_SDM_KERNEL negative control (no merged row 0) fails as required");
}

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
    // mode 0 = every R4-ERASE switch off (the R2-LANES tree); 1 = all on; 2.. = all on plus negative control mode-1.
    r4e_sdm_override(Some(mode != 0));
    r4e_trim_override(Some(mode != 0));
    r4e_hold_override(if mode == 0 { Some(8) } else { None });
    r4e_neg_set(if mode >= 2 { mode - 1 } else { 0 });
    let mut b = B::new();
    let (xq, yq) = pointadd_lilypad::point_add(&mut b);
    r4e_sdm_override(None);
    r4e_trim_override(None);
    r4e_hold_override(None);
    r4e_neg_set(0);
    let ops = std::mem::take(&mut b.ops);
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let data = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    eprintln!("R4E mode {mode}: ops {} peak {} nq {nq} expected_t {:.1}", ops.len(), b.peak, super::tests_chunked::expected_t(&ops));
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

#[test]
#[ignore]
fn r4e_paired_exactness() {
    let batches: usize = std::env::var("R4E_BATCHES").ok().map(|v| v.parse().unwrap()).unwrap_or(160);
    let seed: u64 = std::env::var("R4E_SEED").ok().map(|v| v.parse().unwrap()).unwrap_or(0x2026_1027);
    let modes: Vec<u8> = std::env::var("R4E_MODES").unwrap_or_else(|_| "0,1,2".into()).split(',').map(|v| v.parse().unwrap()).collect();
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
                    let r = run(c, &all[i], &format!("r4e-{seed}-{i}"));
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
        eprintln!("R4E_RESULT mode {m}: shots {} failing {fails} ({:.2} per 9024) mean executed T {:.1}",
            batches * 64, fails as f64 * 9024.0 / shots, tof as f64 / shots);
    }
    let base = modes.iter().position(|&m| m == 0);
    for (j, m) in modes.iter().enumerate() {
        if let (Some(a), true) = (base, *m != 0) {
            let diff: u32 = (0..batches).map(|i| (res[a][i].0 ^ res[j][i].0).count_ones()).sum();
            let only: u32 = (0..batches).map(|i| (res[j][i].0 & !res[a][i].0).count_ones()).sum();
            eprintln!("R4E_PAIRED off-vs-mode{m} disagreements {diff} (mode{m}-only failures {only})");
        }
    }
}
