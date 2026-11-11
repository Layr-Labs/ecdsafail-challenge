//! FD pane micro-benchmarks: Toffoli price of the product building blocks.
use super::builder::B;
use super::modp_frogdrop::Ms;

fn tof_of(f: impl FnOnce(&mut B)) -> u64 {
    let mut b = B::new();
    let t0 = b.tof;
    f(&mut b);
    b.flush_dependency();
    b.tof - t0
}

#[test]
fn fd_price_blocks() {
    let ctrl_modadd = tof_of(|b| {
        let ms = Ms::alloc(b); let z = b.alloc_n(256); let y = b.alloc_n(256); let c = b.alloc(); let d = b.alloc();
        super::modp_frogdrop::ctrl_modadd(b, &ms, &z, &y, c, d);
    });
    let ctrl_modadd255 = tof_of(|b| {
        let ms = Ms::alloc(b); let z = b.alloc_n(256); let a = b.alloc_n(255); let c = b.alloc(); let d = b.alloc_n(2);
        super::pointadd_frogdrop::ctrl_modadd255(b, &ms, &z, &a, c, d[0], d[1]);
    });
    let ttk_add_c = tof_of(|b| {
        let ms = Ms::alloc(b); let z = b.alloc_n(256); let y = b.alloc_n(256); let c = b.alloc(); let d = b.alloc();
        super::arith::ttk_add(b, &y, &z, Some(c), Some((ms.k, d)));
    });
    let add_small = tof_of(|b| {
        let ms = Ms::alloc(b); let z = b.alloc_n(256); let y = b.alloc_n(256);
        super::modp_frogdrop::add_small(b, &ms, &z, 0, Some(ms.k), super::modp_frogdrop::C, &y);
    });
    let mod_double = tof_of(|b| {
        let ms = Ms::alloc(b); let mut z = b.alloc_n(256); let y = b.alloc_n(256);
        super::modp_frogdrop::mod_double(b, &ms, &mut z, &y);
    });
    let activate = tof_of(|b| {
        let z = b.alloc_n(256); let f = b.alloc(); let a = b.alloc_n(255);
        super::joint_seed::activate_bits(b, &z, f, 1365, &a, 11);
    });
    eprintln!("FDPRICE ctrl_modadd {ctrl_modadd} ctrl_modadd255 {ctrl_modadd255} ttk_add_ctl {ttk_add_c} add_small {add_small} mod_double {mod_double} activate {activate}");
}

/// FD: walk failure channels over FD_V random traversal inputs (uniform in [1, p)), FD_T threads.
/// Parameters from env (defaults = the built machine). lambda = 2 * 9024 * rate (two divisions per shot).
#[test]
#[ignore = "tool"]
fn fd_walk_lambda() {
    use super::frogdrop_sched::*;
    use super::pointadd_frogdrop as pf;
    let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|s| s.parse().ok()).unwrap_or(d);
    let v = env("FD_V", 200000);
    let th = env("FD_T", 8);
    let (k, kp, qb, tot, nq, emax, nring) = (env("FD_K", pf::K), env("FD_KP", pf::KP), env("FD_QB", pf::QB),
        env("FD_TOT", pf::TOT), env("FD_NQ", pf::NQ), env("FD_EMAX", pf::EMAX), env("FD_NRING", pf::N));
    let seed = env("FD_SEED", 1) as u64;
    let sc = std::sync::Arc::new(from_text(pf::SCHED_FROGDROP));
    let hs: Vec<_> = (0..th).map(|t| {
        let sc = sc.clone();
        std::thread::spawn(move || {
            let mut h = std::collections::BTreeMap::<&'static str, usize>::new();
            for x in sample(v / th, seed * 1000 + t as u64) {
                if let Some(w) = predict_n(x, &sc, k, kp, qb, tot, nq, emax, nring) { *h.entry(w).or_default() += 1; }
            }
            h
        })
    }).collect();
    let mut all = std::collections::BTreeMap::<&'static str, usize>::new();
    for h in hs { for (k2, c) in h.join().unwrap() { *all.entry(k2).or_default() += c; } }
    let n = (v / th) * th;
    let nf: usize = all.values().sum();
    eprintln!("FDLAMBDA K {k} KP {kp} QB {qb} TOT {tot} NQ {nq} EMAX {emax} NRING {nring}: {nf} fails / {n} -> lambda {:.3} per 9024 shots; {:?}",
              2.0 * 9024.0 * nf as f64 / n as f64, all);
}

#[test]
#[ignore = "tool"]
fn fd_cnt_hist() {
    use super::frogdrop_sched::*;
    let mut h = std::collections::BTreeMap::<usize, usize>::new();
    let v = 400000;
    for x in sample(v, 7) { *h.entry(shot(x, L0).recs.len()).or_default() += 1; }
    eprintln!("FDCNT {:?}", h);
}

type NN = super::frogdrop_sched::N;
fn fput(w: &mut [u64], qs: &[crate::circuit::QubitId], shot: usize, v: &NN) {
    for (i, &q) in qs.iter().enumerate() {
        if v.bit(i) { w[q.0 as usize] |= 1 << shot } else { w[q.0 as usize] &= !(1 << shot) }
    }
}
fn fget(w: &[u64], qs: &[crate::circuit::QubitId], shot: usize) -> NN {
    let mut v = NN::ZERO;
    for (i, &q) in qs.iter().enumerate() { if (w[q.0 as usize] >> shot) & 1 == 1 { v |= NN::from(1u64) << i; } }
    v
}

/// seed_fwd (measured activation) gives j*a mod p; seed_inv + pay_debts return the input with zero phase.
#[test]
fn fd_seed_meas_roundtrip() {
    use super::frogdrop_sched::p;
    let w = 4usize;
    let mut b = B::new();
    let z = b.alloc_n(256);
    let a = b.alloc_n(255);
    let y = b.alloc_n(256);
    let flag = b.alloc();
    let k = b.alloc();
    let mut dirty = a.clone();
    dirty.extend_from_slice(&y);
    let (zz, aa, yy) = (z.clone(), a.clone(), y.clone());
    let debts = super::fd_seed::seed_fwd(&mut b, &z, flag, k, w, &dirty, &mut |b: &mut B| {
        super::pointadd_frogdrop::ctrl_modadd255(b, &Ms { k }, &zz, &aa, flag, yy[0], yy[1]);
    });
    b.flush_dependency();
    let mid = b.ops.len();
    b.begin();
    super::pointadd_frogdrop::ctrl_modadd255(&mut b, &Ms { k }, &z, &a, flag, y[0], y[1]);
    let rec = b.end();
    super::fd_seed::seed_inv(&mut b, &z, flag, k, w, &dirty, &rec);
    super::fd_seed::pay_debts(&mut b, &z[256 - w..], &debts, k, &y);
    b.flush_dependency();
    let ops = std::mem::take(&mut b.ops);
    let pp = p();
    let mut rng = super::tests_frogdrop::Rng::new(11);
    let mut js = vec![]; let mut as_ = vec![];
    for _ in 0..64 { js.push(rng.next() as usize % (1 << w)); let mut v = rng.below(255); if v.is_zero() { v = NN::from(1u64); } as_.push(v); }
    let ys: Vec<NN> = (0..64).map(|_| rng.below(256)).collect();
    let init = |q: &mut Vec<u64>| {
        for s in 0..64 {
            fput(q, &z, s, &(NN::from(js[s] as u64) << (256 - w)));
            fput(q, &a, s, &as_[s]);
            fput(q, &y, s, &ys[s]);
        }
    };
    let half = super::tests_frogdrop::run(&ops[..mid], 0, &init);
    for s in 0..64 {
        let want = (NN::from(js[s] as u64) * as_[s]) % pp;
        assert_eq!(fget(&half.q, &z, s), want, "shot {s} j {}", js[s]);
        assert_eq!((half.q[flag.0 as usize] >> s) & 1, 0);
        assert_eq!((half.q[k.0 as usize] >> s) & 1, 0);
    }
    let full = super::tests_frogdrop::run(&ops, 0, &init);
    for s in 0..64 {
        assert_eq!(fget(&full.q, &z, s), NN::from(js[s] as u64) << (256 - w));
        assert_eq!(fget(&full.q, &a, s), as_[s]);
        assert_eq!(fget(&full.q, &y, s), ys[s]);
    }
    assert_eq!(full.phase, 0, "phase garbage {:x}", full.phase);
    eprintln!("FDSEED ok: fwd tof {} total tof {}", half.tof, full.tof);
}
