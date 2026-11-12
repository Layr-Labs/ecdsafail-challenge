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
