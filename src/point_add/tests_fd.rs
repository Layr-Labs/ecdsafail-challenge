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

/// FD: where (column index, phase, quotient size) the estimate channel fails.
#[test]
#[ignore = "tool"]
fn fd_estimate_where() {
    use super::frogdrop_sched::*;
    use super::pointadd_frogdrop as pf;
    let env = |k: &str, d: usize| std::env::var(k).ok().and_then(|s| s.parse().ok()).unwrap_or(d);
    let v = env("FD_V", 2000000); let th = 8;
    let kp = env("FD_KP", pf::KP);
    let hs: Vec<_> = (0..th).map(|t| std::thread::spawn(move || {
        let pp = p(); let one = NN::from(1u64);
        let mut out = vec![];
        for xr in sample(v / th, 5000 + t as u64) {
            let s = shot(xr, L0);
            let (mut r, mut tt) = (vec![pp, xr], vec![NN::ZERO, one]);
            while !r[r.len() - 1].is_zero() { let n = r.len(); let q = r[n-2] / r[n-1]; let rn = r[n-2] - q * r[n-1]; let tn = tt[n-2] + q * tt[n-1]; r.push(rn); tt.push(tn); }
            let nn = r.len() - 1;
            let (mut j, mut col) = (1usize, 0usize);
            let mut cols = vec![];
            for rec in &s.recs { match rec.kind { Kind::Hr => { cols.push((0u8, j, col)); j += 1; } Kind::Ht => { cols.push((1, j, col)); j += 1; } _ => {} } col += 1; }
            cols.push((1, nn - 1, col));
            for &(ph, j, col) in &cols {
                let q = r[j - 1] / r[j];
                let (z, x, y) = if ph == 0 { (r[j], tt[j - 1], tt[j]) } else { (tt[j], r[j + 1], r[j]) };
                let (sz, sy) = (z.bit_len(), y.bit_len());
                let k = pf::K;
                let zh = (z >> (sz - k)) | one;
                let (yh, xh) = if sy >= kp { (y >> (sy - kp), x >> (sy - kp)) } else { (y << (kp - sy), x << (kp - sy)) };
                let e = 256 + k + kp - sz - sy;
                if e > pf::TOT { continue; }
                let fh = ((one << e) - one) / zh;
                let (q0, rho) = (fh / yh, fh % yh);
                if q0 >= (one << pf::QB) { continue; }
                let b = if rho < xh { one } else { NN::ZERO };
                if q0 - b != q { out.push((col, ph, sy, q.bit_len(), (q0 - b) > q)); }
            }
        }
        out
    })).collect();
    let mut all = vec![];
    for h in hs { all.extend(h.join().unwrap()); }
    all.sort();
    eprintln!("FDEST KP {kp} n {} : {:?}", all.len(), all);
}

/// P1 shape: measured seed (w) + lazy Ms rounds with HMR of each multiplier bit -> z = a * y mod p.
#[test]
fn fd_p1_rounds_value() {
    use super::frogdrop_sched::p;
    use super::modp_frogdrop::mod_double;
    let w: usize = std::env::var("FD_W").ok().and_then(|v| v.parse().ok()).unwrap_or(4); let nl = 256 - w;
    let mut b = B::new();
    let zlow = b.alloc_n(nl); let a = b.alloc_n(255); let y = b.alloc_n(256); let flag = b.alloc(); let k = b.alloc();
    let mut z = zlow.clone(); z.extend_from_slice(&y[nl..]);
    let mut zz = z.clone();
    let (zc, ac, y0, y1) = (zz.clone(), a.clone(), y[0], y[1]);
    let m = b.fresh_bits(nl);
    let _debts = super::fd_seed::seed_fwd(&mut b, &zz, flag, k, w, &a, &mut |b: &mut B| {
        super::pointadd_frogdrop::ctrl_modadd255(b, &Ms { k }, &zc, &ac, flag, y0, y1);
    });
    let ms = Ms { k };
    let rounds: usize = std::env::var("FD_R").ok().and_then(|v| v.parse().ok()).unwrap_or(nl);
    let dbl_only = std::env::var("FD_DBL").is_ok();
    for i in (nl - rounds..nl).rev() {
        if std::env::var("FD_CANON").is_ok() { super::early_product_fifth::round(&mut b, &mut zz, &a, &y[..nl], i, flag, m[i]); continue; }
        mod_double(&mut b, &ms, &mut zz, &a);
        if !dbl_only { super::pointadd_frogdrop::ctrl_modadd255(&mut b, &ms, &zz, &a, y[i], y[(i + 1) % nl], y[(i + 2) % nl]); }
        if std::env::var("FD_NOHMR").is_err() { b.hmr_to(y[i], m[i]); }
    }
    b.flush_dependency();
    let ops = std::mem::take(&mut b.ops);
    let pp = p();
    let mut rng = super::tests_frogdrop::Rng::new(3);
    let as_: Vec<NN> = (0..64).map(|_| { let v = rng.below(255); if v.is_zero() { NN::from(1u64) } else { v } }).collect();
    let ys: Vec<NN> = (0..64).map(|_| rng.below(256) % pp).collect();
    let init = |q: &mut Vec<u64>| { for s in 0..64 { fput(q, &a, s, &as_[s]); fput(q, &y, s, &ys[s]); } };
    let r = super::tests_frogdrop::run(&ops, 0, &init);
    let mut bad = 0;
    for s in 0..64 {
        let lo = nl - rounds;
        let mult = if dbl_only { (ys[s] >> nl) << rounds } else { ys[s] >> lo };
        let got = fget(&r.q, &zz, s); let mask = (NN::from(1u64) << 128) - NN::from(1u64); let hi = ((as_[s] * (mult >> 128)) % pp) << 128; let want = ((hi % pp) + (as_[s] * (mult & mask)) % pp) % pp;
        if got != want { eprintln!("FDBAD shot {s} got {got:#x} want {want:#x} got%p==want {}", got % pp == want); bad += 1; }
        assert_eq!(fget(&r.q, &a, s), as_[s]);
    }
    eprintln!("FDK k-nonzero shots {}", r.q[k.0 as usize].count_ones());
    assert_eq!(bad, 0);
    eprintln!("FDP1 ok tof/shot {}", r.tof / 64);
}

fn modmul(a: &NN, m: &NN) -> NN {
    let pp = super::frogdrop_sched::p();
    let mask = (NN::from(1u64) << 128) - NN::from(1u64);
    let hi = ((*a * (*m >> 128)) % pp) << 128;
    ((hi % pp) + (*a * (*m & mask)) % pp) % pp
}

/// Signed-digit Horner (fd_shell) after a measured seed: z = (j 2^m + L) a mod p, for 255- and 256-lane addends.
#[test]
fn fd_signed_rounds() {
    for alen in [255usize, 256] {
        let w = 4usize; let m = 40usize;
        let mut b = B::new();
        let zlow = b.alloc_n(256 - w); let a = b.alloc_n(alen); let y = b.alloc_n(256); let flag = b.alloc(); let k = b.alloc();
        let mut z = zlow.clone(); z.extend_from_slice(&y[256 - w..]);
        let mut zz = z.clone();
        let (zc, ac, y0, y1) = (zz.clone(), a.clone(), y[0], y[1]);
        let mut dirty = a.clone(); dirty.extend_from_slice(&y[..200]);
        let _ = super::fd_seed::seed_fwd(&mut b, &zz, flag, k, w, &dirty, &mut |b: &mut B| {
            if alen == 255 { super::pointadd_frogdrop::ctrl_modadd255(b, &Ms { k }, &zc, &ac, flag, y0, y1); }
            else { super::modp_frogdrop::ctrl_modadd(b, &Ms { k }, &zc, &ac, flag, y0); }
        });
        let ms = Ms { k };
        b.begin();
        super::fd_shell::pre(&mut b, &ms, &mut zz, &a, y[0]);
        for i in (256 - w - m..256 - w).rev() { super::fd_shell::sround(&mut b, &ms, &mut zz, &a, y[i], y[(i + 1) % 200]); }
        super::fd_shell::post(&mut b, &ms, &mut zz, &a, y[0]);
        let rec = b.end();
        b.play(&rec, false);
        b.flush_dependency();
        let ops = std::mem::take(&mut b.ops);
        let pp = super::frogdrop_sched::p();
        let mut rng = super::tests_frogdrop::Rng::new(9 + alen as u64);
        let as_: Vec<NN> = (0..64).map(|_| { let v = rng.below(alen) % pp; if v.is_zero() { NN::from(1u64) } else { v } }).collect();
        let ys: Vec<NN> = (0..64).map(|_| rng.below(256) % pp).collect();
        let init = |q: &mut Vec<u64>| { for s in 0..64 { fput(q, &a, s, &as_[s]); fput(q, &y, s, &ys[s]); } };
        let r = super::tests_frogdrop::run(&ops, 0, &init);
        for s in 0..64 {
            let mult = ys[s] >> (256 - w - m);
            assert_eq!(fget(&r.q, &zz, s), modmul(&as_[s], &mult), "alen {alen} shot {s}");
            assert_eq!(fget(&r.q, &y[..256 - w], s), ys[s] & ((NN::from(1u64) << (256 - w)) - NN::from(1u64)));
            assert_eq!((r.q[k.0 as usize] >> s) & 1, 0);
        }
        eprintln!("FDSIGNED ok alen {alen} tof/shot {}", r.tof / 64);
    }
}

/// sq_horner: x <- lam^2 - x mod p.
#[test]
fn fd_sq_horner() {
    let mut b = B::new();
    let x = b.alloc_n(256); let lam = b.alloc_n(256); let d = b.alloc();
    super::pointadd_frogdrop::sq_horner(&mut b, &x, &lam, d);
    b.flush_dependency();
    let ops = std::mem::take(&mut b.ops);
    let pp = super::frogdrop_sched::p();
    let mut rng = super::tests_frogdrop::Rng::new(77);
    let xs: Vec<NN> = (0..64).map(|_| { let v = rng.below(256) % pp; if v.is_zero() { NN::from(1u64) } else { v } }).collect();
    let ls: Vec<NN> = (0..64).map(|_| rng.below(256) % pp).collect();
    let init = |q: &mut Vec<u64>| { for s in 0..64 { fput(q, &x, s, &xs[s]); fput(q, &lam, s, &ls[s]); } };
    let r = super::tests_frogdrop::run(&ops, 0, &init);
    for s in 0..64 {
        let want = (modmul(&ls[s], &ls[s]) + pp - xs[s]) % pp;
        assert_eq!(fget(&r.q, &x, s), want, "shot {s}");
        assert_eq!(fget(&r.q, &lam, s), ls[s]);
    }
    eprintln!("FDSQ ok tof/shot {}", r.tof / 64);
}

/// FD diagnostic: Fiat-Shamir draw of an ops.bin file (FD_OPS) and the classical walk predictor on both divisions of
/// every shot (parent walk constants and schedule only). Prints the failing shot indices (post-skip numbering).
#[test]
#[ignore = "tool"]
fn fd_predict_file() {
    use crate::circuit::{BitId, Op, OperationType as K, QubitId, RegisterId};
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    use sha3::digest::{ExtendableOutput, Update, XofReader};
    use std::io::Read;
    use super::pointadd_frogdrop::*;
    type U = ruint::aliases::U256;
    let path = std::env::var("FD_OPS").unwrap();
    let mut f = std::fs::File::open(&path).unwrap();
    let mut h = [0u8; 16];
    f.read_exact(&mut h).unwrap();
    let n = u64::from_le_bytes(h[8..].try_into().unwrap());
    let mut dec = zstd::stream::read::Decoder::new(std::io::BufReader::with_capacity(1 << 20, f)).unwrap();
    dec.window_log_max(27).unwrap();
    let mut dec = std::io::BufReader::with_capacity(1 << 22, dec);
    let mut hs = sha3::Shake256::default();
    hs.update(b"quantum_ecc-fiat-shamir-v2");
    hs.update(&n.to_le_bytes());
    let kinds = [K::Neg, K::Register, K::AppendToRegister, K::BitInvert, K::BitStore0, K::BitStore1, K::X, K::Z, K::CX,
                 K::CZ, K::Swap, K::R, K::Hmr, K::CCX, K::CCZ, K::PushCondition, K::PopCondition, K::DebugPrint];
    let mut r = [0u8; 56];
    for _ in 0..n {
        dec.read_exact(&mut r).unwrap();
        let u = |o: usize| u64::from_le_bytes(r[o..o + 8].try_into().unwrap());
        let mut op = Op::empty();
        op.kind = kinds[u32::from_le_bytes(r[0..4].try_into().unwrap()) as usize];
        op.q_control2 = QubitId(u(8)); op.q_control1 = QubitId(u(16)); op.q_target = QubitId(u(24));
        op.c_target = BitId(u(32)); op.c_condition = BitId(u(40)); op.r_target = RegisterId(u(48));
        hs.update(&[op.kind as u8]);
        for v in [op.q_control2.0, op.q_control1.0, op.q_target.0, op.c_target.0, op.c_condition.0, op.r_target.0] { hs.update(&v.to_le_bytes()); }
    }
    let mut xof = hs.finalize_xof();
    let hx = |s: &str| U::from_str_radix(s, 16).unwrap();
    let curve = WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"), a: U::ZERO, b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    };
    let sched = super::frogdrop_sched::from_text(SCHED_FROGDROP);
    let pp = super::frogdrop_sched::p();
    let to_n = |u: U| -> NN { let mut v = NN::ZERO; for (i, &w) in u.as_limbs().iter().enumerate() { v |= NN::from(w) << (64 * i); } v };
    let mut idx = 0usize;
    let mut fails = vec![];
    for _ in 0..9024 {
        let mut rb = [[0u8; 32]; 2];
        XofReader::read(&mut xof, &mut rb[0]); XofReader::read(&mut xof, &mut rb[1]);
        let t = curve.mul(curve.gx, curve.gy, U::from_le_bytes(rb[0]));
        let o = curve.mul(curve.gx, curve.gy, U::from_le_bytes(rb[1]));
        if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) { continue; }
        let e = curve.add(t.0, t.1, o.0, o.1);
        let (x1, x2, x3) = (to_n(t.0), to_n(o.0), to_n(e.0));
        let d1 = if x1 >= x2 { x1 - x2 } else { x1 + pp - x2 };
        let d2 = if x3 >= x2 { x3 - x2 } else { x3 + pp - x2 };
        if std::env::var("FD_SHOT").ok().and_then(|v| v.parse::<usize>().ok()) == Some(idx) {
            for (dv, d) in [(1, d1), (2, d2)] {
                let r: Vec<_> = (25..=31).map(|kp| (kp, super::frogdrop_sched::predict(d, &sched, K, kp, QB, TOT, NQ, EMAX))).collect();
                let rq: Vec<_> = (24..=27).map(|qb| (qb, super::frogdrop_sched::predict(d, &sched, K, 29, qb, TOT, NQ, EMAX))).collect();
                eprintln!("FDSHOT {idx} div {dv} d {d:#x} kp-scan {:?} qb-scan(kp29) {:?}", r, rq);
            }
        }
        for (dv, d) in [(1, d1), (2, d2)] {
            if let Some(w) = super::frogdrop_sched::predict(d, &sched, K, KP, QB, TOT, NQ, EMAX) { fails.push((idx, dv, w)); }
        }
        idx += 1;
    }
    eprintln!("FDPRED {path}: {idx} shots, predicted walk failures {:?}", fails);
}

#[test]
#[ignore = "tool"]
fn fd_shot_len() {
    use super::frogdrop_sched::*;
    for h in std::env::var("FD_DS").unwrap().split(',') {
        let d = NN::from_str_radix(h.trim_start_matches("0x"), 16).unwrap();
        let s = shot(d, L0);
        let kinds: Vec<_> = s.recs.iter().map(|r| match r.kind { Kind::Hr => 'R', Kind::Ht => 'T', Kind::Sw => 'S', Kind::Idle => 'I' }).collect();
        let qmax = s.recs.iter().map(|r| r.qn).max().unwrap();
        eprintln!("FDLEN {h}: {} stepping columns, qn max {qmax}, br {} ; {}", s.recs.len(), s.br, kinds.iter().collect::<String>());
    }
}

#[test]
#[ignore = "tool"]
fn fd_len_tail() {
    use super::frogdrop_sched::*;
    let v: usize = std::env::var("FD_V").ok().and_then(|s| s.parse().ok()).unwrap_or(8_000_000);
    let th = 8;
    let hs: Vec<_> = (0..th).map(|t| std::thread::spawn(move || {
        let mut h = std::collections::BTreeMap::<usize, usize>::new();
        for x in sample(v / th, 31337 + t as u64) { let l = shot(x, L0).recs.len(); if l >= 190 { *h.entry(l).or_default() += 1; } }
        h
    })).collect();
    let mut all = std::collections::BTreeMap::<usize, usize>::new();
    for h in hs { for (k, c) in h.join().unwrap() { *all.entry(k).or_default() += c; } }
    eprintln!("FDTAIL n {} lengths>=190 {:?}", v, all);
}
