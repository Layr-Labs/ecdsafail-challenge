//! TRACK1 tests: value, phase, lanes returned clean, and a sabotaged control that must fail.
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

#[test]
fn xclean_const_add_ctl() {
    let mut rng = Rng::new(11);
    for &(k, neg) in &[(C, false), (C, true), (C - 1, false), (C - 1, true)] {
        let mut b = B::new();
        let t = b.alloc_n(FW); let ctl = b.alloc(); let bank = b.alloc_n(FW);
        const_add_ctl(&mut b, &t, k, ctl, neg, &bank);
        b.flush_dependency();
        let nq = b.width() as usize;
        let vals: Vec<U> = (0..64).map(|_| { let mut v = rnd(&mut rng); v[1] &= 7; v[2] = 0; v[3] = 0; v }).collect();
        let cw = rng.next();
        let sim = run(&b.ops, nq, &|w: &mut Vec<u64>| { for s in 0..64 { put(w, &t, s, &vals[s]); } w[ctl.0 as usize] = cw; });
        assert_eq!(sim.phase, 0);
        for q in &bank { assert_eq!(sim.q[q.0 as usize], 0, "bank dirty"); }
        assert_eq!(sim.q[ctl.0 as usize], cw);
        for s in 0..64 {
            let v = (vals[s][0] as u128) | ((vals[s][1] as u128) << 64);
            let on = (cw >> s) & 1 == 1; let m = (1u128 << FW) - 1;
            let want = if !on { v } else if neg { v.wrapping_sub(k as u128) & m } else { (v + k as u128) & m };
            let g = get(&sim.q, &t, s);
            assert_eq!((g[0] as u128) | ((g[1] as u128) << 64), want, "k={k} neg={neg} shot {s}");
        }
    }
}

fn modadd_case(sabotage: bool) -> bool {
    let mut rng = Rng::new(21);
    SABOTAGE.with(|s| s.set(sabotage));
    let mut b = B::new();
    let z = b.alloc_n(256); let y = b.alloc_n(256); let flag = b.alloc(); let bank = b.alloc_n(BANK);
    modadd_c(&mut b, &z, &y, flag, &bank);
    b.flush_dependency();
    let nq = b.width() as usize;
    let zs: Vec<U> = (0..64).map(|_| rnd(&mut rng)).collect();
    let ys: Vec<U> = (0..64).map(|_| rnd(&mut rng)).collect();
    let sim = run(&b.ops, nq, &|w: &mut Vec<u64>| { for s in 0..64 { put(w, &z, s, &zs[s]); put(w, &y, s, &ys[s]); } });
    SABOTAGE.with(|s| s.set(false));
    let mut ok = sim.phase == 0 && sim.q[flag.0 as usize] == 0 && bank.iter().all(|q| sim.q[q.0 as usize] == 0);
    let mut carries = 0;
    for s in 0..64 {
        ok &= get(&sim.q, &y, s) == ys[s];
        let (sum, c) = add(&zs[s], &ys[s]);
        if c { carries += 1; }
        let want = if c { add(&sum, &[C, 0, 0, 0]).0 } else { sum };
        ok &= get(&sim.q, &z, s) == want;
    }
    if !sabotage { assert!(carries > 10 && carries < 54, "carry cases {carries}"); }
    ok
}
#[test]
fn xclean_modadd_value_phase_clean() { assert!(modadd_case(false)); }
#[test]
fn xclean_modadd_sabotage_is_caught() { assert!(!modadd_case(true)); }

#[test]
fn xclean_sq_horner_matches_reference() {
    let mut rng = Rng::new(31);
    let mut b = B::new();
    let x = b.alloc_n(256); let lam = b.alloc_n(256);
    sq_horner_c(&mut b, &x, &lam);
    b.flush_dependency();
    let nq = b.width() as usize;
    let mk = |r: &mut Rng| { let mut v = rnd(r); v[3] &= 0x7FFF_FFFF_FFFF_FFFF; v[0] |= 1; v };
    let xs: Vec<U> = (0..64).map(|_| mk(&mut rng)).collect();
    let ls: Vec<U> = (0..64).map(|_| mk(&mut rng)).collect();
    let sim = run(&b.ops, nq, &|w: &mut Vec<u64>| { for s in 0..64 { put(w, &x, s, &xs[s]); put(w, &lam, s, &ls[s]); } });
    assert_eq!(sim.phase, 0, "phase garbage");
    for q in 512..nq { assert_eq!(sim.q[q], 0, "lane {q} dirty"); }
    for s in 0..64 {
        let l2 = mulm(&ls[s], &ls[s]);
        let want = { let (d, br) = sub(&l2, &red(&xs[s])); if br { add(&d, &P).0 } else { d } };
        assert_eq!(red(&get(&sim.q, &x, s)), want, "shot {s}");
        assert_eq!(get(&sim.q, &lam, s), ls[s]);
    }
    eprintln!("XCLEAN_SQ_PASS tof {}", b.tof);
}

/// STEP 2: the four straight-line adds with the measured flag erase: value, phase, flag clean, borrowed lanes restored.
fn merase_case(which: usize, sabotage: bool) -> bool {
    use crate::point_add::fd2::{fd_shell, modp_frogdrop, pointadd_frogdrop};
    let mut rng = Rng::new(41 + which as u64);
    let mut b = B::new();
    let ms = Ms::alloc(&mut b);
    let z = b.alloc_n(256); let y = b.alloc_n(256);
    let (ctl, d, d2) = (b.alloc(), b.alloc(), b.alloc());
    let a255 = which == 1 || which == 3;
    let ya = if a255 { &y[..255] } else { &y[..] };
    match which {
        0 => fd_shell::modadd_unc(&mut b, &ms, &z, &y),
        1 => fd_shell::modadd255_unc(&mut b, &ms, &z, ya, d),
        2 => modp_frogdrop::ctrl_modadd(&mut b, &ms, &z, &y, ctl, d),
        _ => pointadd_frogdrop::ctrl_modadd255(&mut b, &ms, &z, ya, ctl, d, d2),
    }
    if sabotage { b.x(z[3]); }
    b.flush_dependency();
    let nq = b.width() as usize;
    let zs: Vec<U> = (0..64).map(|_| rnd(&mut rng)).collect();
    let ys: Vec<U> = (0..64).map(|_| { let mut v = rnd(&mut rng); if a255 { v[3] &= 0x7FFF_FFFF_FFFF_FFFF; } v }).collect();
    let (cw, dw, d2w) = (rng.next(), rng.next(), rng.next());
    let sim = run(&b.ops, nq, &|w: &mut Vec<u64>| {
        for s in 0..64 { put(w, &z, s, &zs[s]); put(w, &y, s, &ys[s]); }
        w[ctl.0 as usize] = cw; w[d.0 as usize] = dw; w[d2.0 as usize] = d2w;
    });
    let mut ok = sim.phase == 0 && sim.q[ms.k.0 as usize] == 0 && sim.q[d.0 as usize] == dw && sim.q[d2.0 as usize] == d2w;
    let mut carries = 0;
    for s in 0..64 {
        ok &= get(&sim.q, &y, s) == ys[s];
        let on = which < 2 || (cw >> s) & 1 == 1;
        let (sum, c) = add(&zs[s], &ys[s]);
        if c && on { carries += 1; }
        let want = if !on { zs[s] } else if c { add(&sum, &[C, 0, 0, 0]).0 } else { sum };
        ok &= get(&sim.q, &z, s) == want;
    }
    if !sabotage { assert!(carries >= 2, "carry cases {carries}"); }
    ok
}
#[test]
fn xclean_measured_erase_four_adds() {
    let mut bad = vec![];
    for w in 0..4 { let a = merase_case(w, false); let c = !merase_case(w, true); eprintln!("MERASE variant {w}: exact {a}, sabotage caught {c}"); if !a || !c { bad.push(w); } }
    assert!(bad.is_empty(), "failing variants {:?}", bad);
}
