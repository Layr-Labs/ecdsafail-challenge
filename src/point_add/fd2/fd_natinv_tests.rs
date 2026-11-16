//! KT13 tests of the native inverses: value, phase, lanes returned clean, exact uncompute, and a sabotaged inverse
//! that must fail. Run on the G4: `bash kt13test.sh natinv`.
use super::*;
use crate::point_add::fd2::tests_frogdrop::{run, Rng};
type U = [u64; 4];
const P: U = [0xFFFF_FFFE_FFFF_FC2F, u64::MAX, u64::MAX, u64::MAX];
fn add(a: &U, b: &U) -> (U, bool) {
    let mut r = [0u64; 4]; let mut c = 0u128;
    for i in 0..4 { let t = a[i] as u128 + b[i] as u128 + c; r[i] = t as u64; c = t >> 64; }
    (r, c == 1)
}
fn sub(a: &U, b: &U) -> (U, bool) {
    let mut r = [0u64; 4]; let mut br = 0i128;
    for i in 0..4 { let t = a[i] as i128 - b[i] as i128 - br; r[i] = t as u64; br = if t < 0 { 1 } else { 0 }; }
    (r, br == 1)
}
fn ge(a: &U, b: &U) -> bool { for i in (0..4).rev() { if a[i] != b[i] { return a[i] > b[i]; } } true }
fn red(a: &U) -> U { if ge(a, &P) { sub(a, &P).0 } else { *a } }
fn addm(a: &U, b: &U) -> U { let (s, c) = add(&red(a), &red(b)); if c || ge(&s, &P) { sub(&s, &P).0 } else { s } }
fn mulm(a: &U, b: &U) -> U {
    let (a, b) = (red(a), red(b)); let mut r = [0u64; 4];
    for i in (0..256).rev() { r = addm(&r, &r); if (b[i / 64] >> (i % 64)) & 1 == 1 { r = addm(&r, &a); } }
    r
}
fn put(w: &mut Vec<u64>, qs: &[QubitId], shot: usize, v: &U) {
    for (i, q) in qs.iter().enumerate() { if (v[i / 64] >> (i % 64)) & 1 == 1 { w[q.0 as usize] |= 1 << shot; } }
}
fn get(w: &[u64], qs: &[QubitId], shot: usize) -> U {
    let mut v = [0u64; 4];
    for (i, q) in qs.iter().enumerate() { if (w[q.0 as usize] >> shot) & 1 == 1 { v[i / 64] |= 1 << (i % 64); } }
    v
}
fn rnd(r: &mut Rng) -> U { [r.next(), r.next(), r.next(), r.next()] }

/// add_fwd alone (value = lazy z + y, phase, flag and pool clean, y restored) or add_fwd then add_inv (identity),
/// with `ncl` clean lanes in the pool: 1 = the parent's increments for the fold, 2 = the adder.
fn add_case(ncl: usize, roundtrip: bool, sabotage: bool) -> bool {
    let mut rng = Rng::new(51 + ncl as u64);
    SABOTAGE.with(|s| s.set(sabotage));
    let mut b = B::new();
    let ms = Ms::alloc(&mut b);
    let z = b.alloc_n(256); let y = b.alloc_n(256); let cl = b.alloc_n(ncl);
    b.gpool = cl.clone();
    add_fwd(&mut b, &ms, &z, &y);
    if roundtrip { add_inv(&mut b, &ms, &z, &y); }
    b.gpool.clear();
    b.flush_dependency();
    SABOTAGE.with(|s| s.set(false));
    let nq = b.width() as usize;
    let zs: Vec<U> = (0..64).map(|_| rnd(&mut rng)).collect();
    let ys: Vec<U> = (0..64).map(|_| rnd(&mut rng)).collect();
    let sim = run(&b.ops, nq, &|w: &mut Vec<u64>| { for s in 0..64 { put(w, &z, s, &zs[s]); put(w, &y, s, &ys[s]); } });
    let mut ok = sim.phase == 0 && sim.q[ms.k.0 as usize] == 0 && cl.iter().all(|q| sim.q[q.0 as usize] == 0);
    let mut carries = 0;
    for s in 0..64 {
        ok &= get(&sim.q, &y, s) == ys[s];
        let (sum, c) = add(&zs[s], &ys[s]);
        if c { carries += 1; }
        let want = if roundtrip { zs[s] } else if c { add(&sum, &[C, 0, 0, 0]).0 } else { sum };
        ok &= get(&sim.q, &z, s) == want;
    }
    assert!(carries > 10 && carries < 54, "carry cases {carries}");
    eprintln!("NATINV add ncl={ncl} roundtrip={roundtrip} sabotage={sabotage}: ok {ok}, emitted tof {}", b.tof);
    ok
}

#[test]
fn natinv_add_value_and_inverse() {
    for ncl in [1usize, 2] {
        assert!(add_case(ncl, false, false), "forward add, {ncl} clean lanes");
        assert!(add_case(ncl, true, false), "add then inverse, {ncl} clean lanes");
        assert!(!add_case(ncl, true, true), "sabotaged inverse not caught, {ncl} clean lanes");
    }
}

/// double alone (value = 2z mod p) or double then halve (identity, lane order restored); pool of `ncl` lanes
/// (0 = the parent's increments, 1 = the adder on that lane and the idle flag k).
fn dh_case(ncl: usize, roundtrip: bool) -> bool {
    let mut rng = Rng::new(61 + ncl as u64);
    let mut b = B::new();
    let ms = Ms::alloc(&mut b);
    let z = b.alloc_n(256); let y = b.alloc_n(256); let cl = b.alloc_n(ncl);
    b.gpool = cl.clone();
    let mut zz = z.clone();
    double(&mut b, &ms, &mut zz, &y);
    if roundtrip {
        halve(&mut b, &ms, &mut zz, &y);
        assert_eq!(zz, z, "lane order after double + halve");
    }
    b.gpool.clear();
    b.flush_dependency();
    let nq = b.width() as usize;
    let zs: Vec<U> = (0..64).map(|_| rnd(&mut rng)).collect();
    let ys: Vec<U> = (0..64).map(|_| rnd(&mut rng)).collect();
    let sim = run(&b.ops, nq, &|w: &mut Vec<u64>| { for s in 0..64 { put(w, &z, s, &zs[s]); put(w, &y, s, &ys[s]); } });
    let mut ok = sim.phase == 0 && sim.q[ms.k.0 as usize] == 0 && cl.iter().all(|q| sim.q[q.0 as usize] == 0);
    for s in 0..64 {
        ok &= get(&sim.q, &y, s) == ys[s];
        let got = get(&sim.q, &zz, s);
        if roundtrip { ok &= got == zs[s]; } else { ok &= red(&got) == addm(&zs[s], &zs[s]); }
    }
    eprintln!("NATINV double/halve ncl={ncl} roundtrip={roundtrip}: ok {ok}, emitted tof {}", b.tof);
    ok
}

#[test]
fn natinv_double_and_halve() {
    for ncl in [0usize, 1] {
        assert!(dh_case(ncl, false), "double, pool {ncl}");
        assert!(dh_case(ncl, true), "double then halve, pool {ncl}");
    }
}

/// rounds_fwd on z = 0 computes alow * y mod p (negated under the sign control); with `roundtrip` the uncompute pass
/// must return z to exactly zero with every flag and clean lane zero and no phase. NB multiplier bits.
fn rounds_case(nx: usize, with_neg: bool, roundtrip: bool, sabotage: bool) -> bool {
    const NB: usize = 20;
    let mut rng = Rng::new(71 + nx as u64 + 2 * (with_neg as u64));
    SABOTAGE.with(|s| s.set(sabotage));
    let mut b = B::new();
    let ms = Ms::alloc(&mut b);
    let z = b.alloc_n(256); let y = b.alloc_n(256); let alow = b.alloc_n(NB);
    let flag = b.alloc(); let c = b.alloc();
    let neg = if with_neg { Some((c, false)) } else { None };
    let (nat, r) = rounds_fwd(&mut b, &ms, &z, &alow, &y, neg, flag, nx);
    assert!(r.is_empty() && nat.on);
    let tof_fwd = b.tof;
    if roundtrip { nat.inverse(&mut b, &ms); }
    b.flush_dependency();
    SABOTAGE.with(|s| s.set(false));
    let nq = b.width() as usize;
    let ys: Vec<U> = (0..64).map(|_| { let mut v = rnd(&mut rng); v[0] |= 1; red(&v) }).collect();
    let ls: Vec<u64> = (0..64).map(|_| (rng.next() & ((1u64 << NB) - 1)) | 1).collect();
    let cw = rng.next();
    let sim = run(&b.ops, nq, &|w: &mut Vec<u64>| {
        for s in 0..64 { put(w, &y, s, &ys[s]); put(w, &alow, s, &[ls[s], 0, 0, 0]); }
        w[c.0 as usize] = cw;
    });
    let mut ok = sim.phase == 0 && sim.q[ms.k.0 as usize] == 0 && sim.q[flag.0 as usize] == 0 && sim.q[c.0 as usize] == cw;
    for q in (c.0 as usize + 1)..nq { ok &= sim.q[q] == 0; }
    for s in 0..64 {
        ok &= get(&sim.q, &y, s) == ys[s];
        ok &= get(&sim.q, &alow, s)[0] == ls[s];
        let got = get(&sim.q, &z, s);
        if roundtrip {
            ok &= got == [0u64; 4];
        } else {
            let prod = mulm(&ys[s], &[ls[s], 0, 0, 0]);
            let want = if with_neg && (cw >> s) & 1 == 1 { sub(&P, &prod).0 } else { prod };
            ok &= red(&got) == want;
        }
    }
    eprintln!("NATINV rounds nx={nx} neg={with_neg} roundtrip={roundtrip} sabotage={sabotage}: ok {ok}, forward tof {tof_fwd}, total tof {} ({} round units)",
              b.tof, NB + 2);
    ok
}

#[test]
fn natinv_rounds_compute_the_product() {
    for nx in [0usize, 1] {
        for neg in [false, true] {
            assert!(rounds_case(nx, neg, false, false), "product, nx {nx}, neg {neg}");
        }
    }
}

#[test]
fn natinv_rounds_uncompute_exactly() {
    for nx in [0usize, 1] {
        for neg in [false, true] {
            assert!(rounds_case(nx, neg, true, false), "uncompute, nx {nx}, neg {neg}");
        }
    }
}

#[test]
fn natinv_sabotaged_uncompute_is_caught() {
    assert!(!rounds_case(1, false, true, true));
    assert!(!rounds_case(0, false, true, true));
}

/// r765b P3NAT_SEED (v1) end to end at a small multiplier width: five-bit measured seed, `stream_fwd` (the streamed
/// bit measured away, native rounds on [flag, bit]), then `Nat::inverse`, `Nat::seed_inv` (six-bit inverse seed with
/// zero test ZW_STREAM, swap, Z repair) and the five-bit seed debts. Returns (forward half holds +-(S 2^NB + alow) y
/// with flag, k and the bit lane |0>; every lane restored at the end; zero phase at the end). `omit_phase` leaves out
/// the bit's Z repair (negative control: lanes still restored, phase garbage).
fn stream_case(with_neg: bool, omit_phase: bool) -> (bool, bool, bool) {
    use crate::point_add::fd2::fd_seed::{pay_debts, seed_fwd, seed_inv_zw};
    use crate::point_add::fd2::modp_frogdrop::ctrl_modadd;
    const NB: usize = 12;
    const W: usize = 5;
    let mut rng = Rng::new(91 + 2 * (with_neg as u64) + (omit_phase as u64));
    let mut b = B::new();
    let ms = Ms::alloc(&mut b);
    let k = ms.k;
    let z = b.alloc_n(256); let y = b.alloc_n(256); let alow = b.alloc_n(NB);
    let flag = b.alloc(); let c = b.alloc();
    let bit = alow[NB - 1];
    let mut dirty = alow.clone();
    dirty.extend_from_slice(&y);
    let (zc, yc, d) = (z.clone(), y.clone(), alow[0]);
    let debts = seed_fwd(&mut b, &z, flag, k, W, &dirty, &mut |b: &mut B| {
        ctrl_modadd(b, &Ms { k }, &zc, &yc, flag, d);
    });
    b.begin();
    ctrl_modadd(&mut b, &Ms { k }, &z, &y, flag, d);
    let addrec = b.end();
    let neg = if with_neg { Some((c, false)) } else { None };
    let (nat, r) = stream_fwd(&mut b, &ms, &z, &alow, &y, neg, flag);
    assert!(r.is_empty() && nat.on);
    b.finish_fold();
    let mid = b.ops.len();
    nat.inverse(&mut b, &ms);
    if omit_phase {
        let dd: Vec<QubitId> = dirty.iter().copied().filter(|&q| q != bit).collect();
        seed_inv_zw(&mut b, &z, flag, k, W + 1, &dd, &addrec, ZW_STREAM, None, None);
        b.swap(z[256 - (W + 1)], bit);
    } else {
        nat.seed_inv(&mut b, &z, flag, k, W, &dirty, &addrec, &y, d);
    }
    pay_debts(&mut b, &z[256 - W..], &debts, k, &y);
    b.finish_fold();
    let nq = b.width() as usize;
    let ops = std::mem::take(&mut b.ops);
    let ys: Vec<U> = (0..64).map(|_| { let mut v = rnd(&mut rng); v[0] |= 1; red(&v) }).collect();
    let ls: Vec<u64> = (0..64).map(|_| (rng.next() & ((1u64 << NB) - 1)) | 1).collect();
    let ss: Vec<u64> = (0..64).map(|_| rng.next() % (1u64 << W)).collect();
    let cw = rng.next();
    let init = |w: &mut Vec<u64>| {
        for s in 0..64 {
            put(w, &y, s, &ys[s]);
            put(w, &alow, s, &[ls[s], 0, 0, 0]);
            put(w, &z, s, &[0, 0, 0, ss[s] << (64 - W)]);
        }
        w[c.0 as usize] = cw;
    };
    let half = run(&ops[..mid], nq, &init);
    let mut half_ok = half.q[k.0 as usize] == 0 && half.q[flag.0 as usize] == 0 && half.q[bit.0 as usize] == 0
        && half.q[c.0 as usize] == cw;
    for s in 0..64 {
        half_ok &= get(&half.q, &y, s) == ys[s];
        half_ok &= get(&half.q, &alow[..NB - 1], s)[0] == ls[s] & ((1u64 << (NB - 1)) - 1);
        let prod = mulm(&ys[s], &[(ss[s] << NB) | ls[s], 0, 0, 0]);
        let want = if with_neg && (cw >> s) & 1 == 1 { sub(&P, &prod).0 } else { prod };
        half_ok &= red(&get(&half.q, &z, s)) == want;
    }
    let full = run(&ops, nq, &init);
    let mut lanes_ok = full.q[k.0 as usize] == 0 && full.q[flag.0 as usize] == 0 && full.q[c.0 as usize] == cw;
    for s in 0..64 {
        lanes_ok &= get(&full.q, &y, s) == ys[s];
        lanes_ok &= get(&full.q, &alow, s)[0] == ls[s];
        lanes_ok &= get(&full.q, &z, s) == [0, 0, 0, ss[s] << (64 - W)];
    }
    let phase_ok = full.phase == 0;
    eprintln!("NATINV stream neg={with_neg} omit_phase={omit_phase}: half {half_ok} lanes {lanes_ok} phase {phase_ok}, fwd tof {}, total tof {}",
              half.tof, full.tof);
    (half_ok, lanes_ok, phase_ok)
}

#[test]
fn natinv_stream_seed_roundtrip() {
    for neg in [false, true] {
        assert_eq!(stream_case(neg, false), (true, true, true), "streamed seed, neg {neg}");
    }
}

#[test]
fn natinv_stream_seed_phase_repair_is_needed() {
    assert_eq!(stream_case(false, true), (true, true, false));
}

/// Saatgutzuegle: `stream_case` with the hybrid seed at both ends. W-bit hybrid forward seed (split hyb_s(W)),
/// `stream_fwd`, `Nat::inverse`, `Nat::seed_inv_hyb` ((W + 1)-bit hybrid inverse, window ZW_STREAM, swap, Z repair), the
/// W-bit seed debts. W = FD_W (default 9). Forced shots: (J, bit) = (0, 0), (0, 1), (2^W - 1, 1), (2^W - 1, 0); rest random.
fn stream_case_hyb(with_neg: bool) -> (bool, bool, bool) {
    use crate::point_add::fd2::fd_seed::{hyb_s, hyb_s_zw, pay_debts, seed_fwd_hyb};
    use crate::point_add::fd2::modp_frogdrop::ctrl_modadd_top;
    const NB: usize = 12;
    let w: usize = std::env::var("FD_W").ok().and_then(|v| v.parse().ok()).unwrap_or(9);
    assert!(crate::point_add::fd2::fd_seed::hyb());
    let (hs, hi) = (crate::point_add::fd2::fd_seed::fwd_split(w), hyb_s_zw(w + 1, ZW_STREAM)); // Saatgutzuegle 2: forward split
    if stream_seed() { assert_eq!(hi, inv_split(w)); }
    let mut rng = Rng::new(191 + 2 * (with_neg as u64) + 7 * w as u64);
    let mut b = B::new();
    let ms = Ms::alloc(&mut b);
    let k = ms.k;
    let z = b.alloc_n(256); let y = b.alloc_n(256); let alow = b.alloc_n(NB);
    let flag = b.alloc(); let c = b.alloc();
    let bit = alow[NB - 1];
    let mut dirty = alow.clone();
    dirty.extend_from_slice(&y);
    let (zc, yc, d) = (z.clone(), y.clone(), alow[0]);
    let debts = seed_fwd_hyb(&mut b, &z, flag, k, w, &dirty, &y, d, hs, &mut |b: &mut B| {
        ctrl_modadd_top(b, &Ms { k }, &zc, &yc, flag, d, hs);
    });
    b.begin();
    ctrl_modadd_top(&mut b, &Ms { k }, &z, &y, flag, d, hi);
    let addrec = b.end();
    let neg = if with_neg { Some((c, false)) } else { None };
    let (nat, r) = stream_fwd(&mut b, &ms, &z, &alow, &y, neg, flag);
    assert!(r.is_empty() && nat.on);
    b.finish_fold();
    let mid = b.ops.len();
    let t0 = b.tof; nat.inverse(&mut b, &ms);
    let t1 = b.tof; nat.seed_inv_hyb(&mut b, &z, flag, k, w, &dirty, &addrec, &y, d, hi);
    let t2 = b.tof; pay_debts(&mut b, &z[256 - w..], &debts, k, &y);
    eprintln!("SECTIONS w={w}: natinv={} seedinv={} paydebts={}", t1 - t0, t2 - t1, b.tof - t2);
    b.finish_fold();
    let nq = b.width() as usize;
    let ops = std::mem::take(&mut b.ops);
    let pin_y = std::env::var("FD_PIN_Y").map(|v| v.trim() == "1").unwrap_or(false);
    let pin_l = std::env::var("FD_PIN_L").map(|v| v.trim() == "1").unwrap_or(false);
    let pin_j = std::env::var("FD_PIN_J").map(|v| v.trim() == "1").unwrap_or(false);
    let pin_yk = std::env::var("FD_PIN_YK").ok().and_then(|v| v.trim().parse::<usize>().ok()).filter(|&k| k < 256);
    let ys: Vec<U> = (0..64).map(|s| {
        if let Some(k) = pin_yk { if s == 6 || s == 7 { let mut v = [0u64; 4]; v[k / 64] = 1u64 << (k % 64); return red(&v); } }
        if pin_y && (s == 6 || s == 7) { return red(&[1, 0, 0, 0]); }
        let mut v = rnd(&mut rng); v[0] |= 1; red(&v)
    }).collect();
    let top = 1u64 << (NB - 1);
    let ls: Vec<u64> = (0..64).map(|s| {
        let r = (rng.next() & ((1u64 << NB) - 1)) | 1;
        match s { 0 | 3 => r & !top, 1 | 2 => r | top, 6 | 7 if pin_l => if s == 6 { 1 } else { 1 | top }, _ => r }
    }).collect();
    let ss: Vec<u64> = (0..64).map(|s| match s { 0 | 1 => 0, 2 | 3 => (1u64 << w) - 1, 4 => 1, 5 => 2, 6 | 7 if pin_j => 1, _ => rng.next() % (1u64 << w) }).collect(); // Saatgutzuegle 2: + j = 1, 2
    let cw = rng.next();
    let init = |q: &mut Vec<u64>| {
        for s in 0..64 {
            put(q, &y, s, &ys[s]);
            put(q, &alow, s, &[ls[s], 0, 0, 0]);
            put(q, &z, s, &[0, 0, 0, ss[s] << (64 - w)]);
        }
        q[c.0 as usize] = cw;
    };
    let half = run(&ops[..mid], nq, &init);
    let mut half_ok = half.q[k.0 as usize] == 0 && half.q[flag.0 as usize] == 0 && half.q[bit.0 as usize] == 0
        && half.q[c.0 as usize] == cw;
    for s in 0..64 {
        half_ok &= get(&half.q, &y, s) == ys[s];
        half_ok &= get(&half.q, &alow[..NB - 1], s)[0] == ls[s] & ((1u64 << (NB - 1)) - 1);
        let prod = mulm(&ys[s], &[(ss[s] << NB) | ls[s], 0, 0, 0]);
        let want = if with_neg && (cw >> s) & 1 == 1 { sub(&P, &prod).0 } else { prod };
        half_ok &= red(&get(&half.q, &z, s)) == want;
    }
    let full = run(&ops, nq, &init);
    let mut lanes_ok = full.q[k.0 as usize] == 0 && full.q[flag.0 as usize] == 0 && full.q[c.0 as usize] == cw;
    for s in 0..64 {
        lanes_ok &= get(&full.q, &y, s) == ys[s];
        lanes_ok &= get(&full.q, &alow, s)[0] == ls[s];
        lanes_ok &= get(&full.q, &z, s) == [0, 0, 0, ss[s] << (64 - w)];
    }
    let phase_ok = full.phase == 0;
    for s in 0..64 {
        let zg = get(&full.q, &z, s); let z0 = zg == [0, 0, 0, ss[s] << (64 - w)];
        let y0 = get(&full.q, &y, s) == ys[s]; let l0 = get(&full.q, &alow, s)[0] == ls[s];
        if !z0 || !y0 || !l0 { eprintln!("  SHOT {s} J={} z_ok={z0} y_ok={y0} l_ok={l0} z={:016x?} alow={:x} y0={:x}", ss[s], zg, get(&full.q, &alow, s)[0], ys[s][0]); }
    }
    eprintln!("NATINV stream HYB w={w} hs={hs} hi={hi} neg={with_neg}: half {half_ok} lanes {lanes_ok} phase {phase_ok}, fwd tof {}, total tof {}",
              half.tof, full.tof);
    (half_ok, lanes_ok, phase_ok)
}

#[test]
fn natinv_stream_seed_hyb_roundtrip() {
    for neg in [false, true] {
        assert_eq!(stream_case_hyb(neg), (true, true, true), "hybrid streamed seed, neg {neg}");
    }
}

/// Saatgutzuegle 2, Bitbhaltis (B), site-shaped as P2a / P3 with the switch on: W-bit hybrid forward seed at the forward
/// split (fwd_split), `rounds_fwd` over all of alow with no extra lane (pool [flag] only), `Nat::inverse`,
/// `Nat::seed_inv_hyb` (W-bit hybrid inverse, window ZW, split hyb_s(W)), then the W-bit debts (pay_debts2 with flag as
/// the second clean lane under FD_S2DEBT=1, else pay_debts). W = FD_W (default 9). Forced shots: J = 0, 1, 2, 2^W - 1.
fn nostream_case_hyb(with_neg: bool) -> (bool, bool, bool) {
    use crate::point_add::fd2::fd_seed::{fwd_split, hyb_s, pay_debts, pay_debts2, s2_debt, seed_fwd_hyb};
    use crate::point_add::fd2::modp_frogdrop::ctrl_modadd_top;
    const NB: usize = 12;
    let w: usize = std::env::var("FD_W").ok().and_then(|v| v.parse().ok()).unwrap_or(9);
    assert!(crate::point_add::fd2::fd_seed::hyb() && on());
    let (hs, hi) = (fwd_split(w), hyb_s(w));
    let mut rng = Rng::new(291 + 2 * (with_neg as u64) + 7 * w as u64);
    let mut b = B::new();
    let ms = Ms::alloc(&mut b);
    let k = ms.k;
    let z = b.alloc_n(256); let y = b.alloc_n(256); let alow = b.alloc_n(NB);
    let flag = b.alloc(); let c = b.alloc();
    let mut dirty = alow.clone();
    dirty.extend_from_slice(&y);
    let (zc, yc, d) = (z.clone(), y.clone(), alow[0]);
    let debts = seed_fwd_hyb(&mut b, &z, flag, k, w, &dirty, &y, d, hs, &mut |b: &mut B| {
        ctrl_modadd_top(b, &Ms { k }, &zc, &yc, flag, d, hs);
    });
    b.begin();
    ctrl_modadd_top(&mut b, &Ms { k }, &z, &y, flag, d, hi);
    let addrec = b.end();
    let neg = if with_neg { Some((c, false)) } else { None };
    let w0 = b.width();
    let (nat, r) = rounds_fwd(&mut b, &ms, &z, &alow, &y, neg, flag, 0);
    assert!(r.is_empty() && nat.on && b.width() == w0, "Bitbhaltis must not allocate");
    b.finish_fold();
    let mid = b.ops.len();
    let tmid = b.tof;
    nat.inverse(&mut b, &ms);
    let minv = crate::point_add::fd2::fd_seed::s2_minv();
    if minv {
        // Rueckwaertsmessli: measured inverse, its debts merged into the forward debts
        let di = crate::point_add::fd2::fd_seed::seed_inv_hyb_m(&mut b, &z, flag, k, w, &dirty, &mut |b: &mut B| {
            crate::point_add::fd2::modp_frogdrop::ctrl_modsub_top_m(b, &Ms { k }, &zc, &yc, flag, d, hi);
        }, &y, d, hi);
        // negative control: S2_SABOTAGE=1 drops the merge (phase must then fail)
        if std::env::var("S2_SABOTAGE").is_err() { crate::point_add::fd2::fd_seed::merge_debts(&mut b, &debts, &di); }
    } else {
    nat.seed_inv_hyb(&mut b, &z, flag, k, w, &dirty, &addrec, &y, d, hi);
    }
    if s2_debt() { pay_debts2(&mut b, &z[256 - w..], &debts, k, flag, &y); } else { pay_debts(&mut b, &z[256 - w..], &debts, k, &y); }
    b.finish_fold();
    let _ = tmid;
    let nq = b.width() as usize;
    let ops = std::mem::take(&mut b.ops);
    let ys: Vec<U> = (0..64).map(|s| {
        let mut v = rnd(&mut rng); v[0] |= 1;
        red(&v)
    }).collect();
    let ls: Vec<u64> = (0..64).map(|s| {
        let r = rng.next() & ((1u64 << NB) - 1);
        match s { 0 => 1, 1 => (1u64 << NB) - 1, _ => r }
    }).collect();
    let ss: Vec<u64> = (0..64).map(|s| match s { 0 | 4 => 0, 1 | 5 => (1u64 << w) - 1, 2 => 1, 3 => 2, _ => rng.next() % (1u64 << w) }).collect();
    let cw = rng.next();
    let init = |q: &mut Vec<u64>| {
        for s in 0..64 {
            put(q, &y, s, &ys[s]);
            put(q, &alow, s, &[ls[s], 0, 0, 0]);
            put(q, &z, s, &[0, 0, 0, ss[s] << (64 - w)]);
        }
        q[c.0 as usize] = cw;
    };
    let half = run(&ops[..mid], nq, &init);
    let mut half_ok = half.q[k.0 as usize] == 0 && half.q[flag.0 as usize] == 0 && half.q[c.0 as usize] == cw;
    for s in 0..64 {
        half_ok &= get(&half.q, &y, s) == ys[s];
        half_ok &= get(&half.q, &alow, s)[0] == ls[s];
        let prod = mulm(&ys[s], &[(ss[s] << NB) | ls[s], 0, 0, 0]);
        let want = if with_neg && (cw >> s) & 1 == 1 && prod != [0; 4] { sub(&P, &prod).0 } else { prod };
        half_ok &= red(&get(&half.q, &z, s)) == red(&want);
    }
    let full = run(&ops, nq, &init);
    let mut lanes_ok = full.q[k.0 as usize] == 0 && full.q[flag.0 as usize] == 0 && full.q[c.0 as usize] == cw;
    for s in 0..64 {
        lanes_ok &= get(&full.q, &y, s) == ys[s];
        lanes_ok &= get(&full.q, &alow, s)[0] == ls[s];
        lanes_ok &= get(&full.q, &z, s) == [0, 0, 0, ss[s] << (64 - w)];
    }
    let phase_ok = full.phase == 0;
    for s in 0..64 {
        if get(&full.q, &z, s) != [0, 0, 0, ss[s] << (64 - w)] || get(&full.q, &alow, s)[0] != ls[s] { eprintln!("  nostream bad shot {s}"); }
    }
    eprintln!("NATINV nostream HYB w={w} hs={hs} hi={hi} neg={with_neg} debt2={} minv={minv}: half {half_ok} lanes {lanes_ok} phase {phase_ok}, fwd tof {}, total tof {}",
              s2_debt(), half.tof, full.tof);
    (half_ok, lanes_ok, phase_ok)
}

#[test]
fn natinv_nostream_seed_hyb_roundtrip() {
    for neg in [false, true] {
        assert_eq!(nostream_case_hyb(neg), (true, true, true), "Bitbhaltis seed, neg {neg}");
    }
}
