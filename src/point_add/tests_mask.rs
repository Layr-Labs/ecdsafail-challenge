//! Masked-ladder tests (mask.rs).

use super::builder::B;
use super::mask::*;
use super::frogdrop_sched::N;
use super::tests_frogdrop::{run, Rng};
use crate::circuit::QubitId;

fn put(words: &mut [u64], qs: &[QubitId], shot: usize, val: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if val.bit(i) { words[q.0 as usize] |= 1 << shot } else { words[q.0 as usize] &= !(1 << shot) }
    }
}
fn get(words: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (words[q.0 as usize] >> shot) & 1 == 1 { v |= N::from(1u64) << i; }
    }
    v
}
fn getb(words: &[u64], q: QubitId, shot: usize) -> u64 { (words[q.0 as usize] >> shot) & 1 }
fn field(x: &N, lo: usize, hi_incl: usize) -> N {
    if hi_incl < lo { return N::ZERO; }
    (*x >> lo) & ((N::from(1u64) << (hi_incl - lo + 1)) - N::from(1u64))
}

struct Case { t: N, s: N, v2: usize, v: usize, g: u64 }

/// Layout: L = 40 lanes, own = [v2 <= lane <= v]: wrap source toggles at lane v2 (window [0,9)),
/// band source toggles at lane v+1 (window [24,40)).
fn setup(b: &mut B) -> (Vec<QubitId>, Vec<QubitId>, QubitId, Vec<QubitId>, Vec<QubitId>, Mscr, QubitId, Vec<Src>) {
    let t = b.alloc_n(40);
    let s = b.alloc_n(40);
    let c0 = b.alloc();
    let v2 = b.alloc_n(4);
    let v = b.alloc_n(6);
    let pre = b.alloc_n(5);
    let sc = Mscr { f: b.alloc(), t: b.alloc(), gf: b.alloc(), chain: pre.clone(), dirty: vec![] };
    let g = b.alloc();
    let wins = vec![
        Src { lo: 0, hi: 9, v: v2.clone(), a: 0, d: 1, pre: pre[..3].to_vec(), late: false },
        Src { lo: 24, hi: 40, v: v.clone(), a: -1, d: 1, pre: pre.clone(), late: false },
    ];
    (t, s, c0, v2, v, sc, g, wins)
}

fn cases(seed: u64, coef: bool) -> Vec<Case> {
    let mut rng = Rng::new(seed);
    (0..64).map(|_| {
        let v2 = (rng.next() % 9) as usize;
        let v = 23 + (rng.next() % 17) as usize;
        let mut t = rng.below(40);
        let mut s = rng.below(40);
        if coef {
            // own fields: make t_own < s_own (COEF precondition when beta = 0), sometimes add
            let so = (field(&s, v2, v) >> 1) | N::from(1u64); // top own bit 0: T_own + S_own fits
            let to = field(&t, v2, v) % so;
            let mask = ((N::from(1u64) << (v - v2 + 1)) - N::from(1u64)) << v2;
            t = (t & !mask) | (to << v2);
            s = (s & !mask) | (so << v2);
        } else if rng.next() % 3 == 0 {
            // equal own fields sometimes
            let mask = ((N::from(1u64) << (v - v2 + 1)) - N::from(1u64)) << v2;
            s = (s & !mask) | (t & mask);
        }
        Case { t, s, v2, v, g: rng.next() & 1 }
    }).collect()
}

#[test]
fn masked_compare_and_cond_sub() {
    let mut b = B::new();
    let (t, s, c0, v2, v, sc, g, wins) = setup(&mut b);
    let x = b.alloc();
    let ld = Lad { t: &t, s: &s, c0, srcs: &wins, f0: false, cmpl: true, sc: &sc, keep_f: false };
    let ru = mup(&mut b, &ld);
    let rd = mdown(&mut b, &ld, Some(x));
    b.play(&ru, false);
    let ct = top_carry(&ld);
    b.x(ct);
    b.and_c(g, ct, x); // x = g & [T_own >= S_own]
    b.x(ct);
    b.play(&rd, false);
    let cs = cases(11, false);
    let r = run(&b.ops, 0, &|w| {
        for (k, c) in cs.iter().enumerate() {
            put(w, &t, k, &c.t); put(w, &s, k, &c.s);
            put(w, &v2, k, &N::from(c.v2 as u64)); put(w, &v, k, &N::from(c.v as u64));
            if c.g == 1 { w[g.0 as usize] |= 1 << k; }
        }
    });
    assert_eq!(r.phase, 0);
    for (k, c) in cs.iter().enumerate() {
        let to = field(&c.t, c.v2, c.v);
        let so = field(&c.s, c.v2, c.v);
        let xe = c.g == 1 && to >= so;
        assert_eq!(getb(&r.q, x, k) == 1, xe, "x k={k}");
        let mask = ((N::from(1u64) << (c.v - c.v2 + 1)) - N::from(1u64)) << c.v2;
        let te = if xe { (c.t & !mask) | ((to - so) << c.v2) } else { c.t };
        assert_eq!(get(&r.q, &t, k), te, "t k={k} v2={} v={}", c.v2, c.v);
        assert_eq!(get(&r.q, &s, k), c.s, "s k={k}");
        for &q in [sc.f, sc.t, sc.gf, c0].iter().chain(sc.chain.iter()) { assert_eq!(getb(&r.q, q, k), 0, "scratch"); }
    }
    eprintln!("masked compare+cond-sub: {} Toffoli for 40 lanes (24 masked)", b.tof);
}

#[test]
fn masked_coef_inverse() {
    // U^-1: (T_own, beta) -> (T_own + beta S_own, 0) when T_own < S_own; erase beta mid-ladder with enable ep
    let mut b = B::new();
    let (t, s, c0, v2, v, sc, g, wins) = setup(&mut b);
    let ep = b.alloc();
    let ld = Lad { t: &t, s: &s, c0, srcs: &wins, f0: false, cmpl: true, sc: &sc, keep_f: false };
    let ru = mup(&mut b, &ld);
    let rd = mdown(&mut b, &ld, Some(g));
    b.play(&rd, true);
    let ct = top_carry(&ld);
    b.x(ct);
    b.ccx(ep, ct, g);
    b.x(ct);
    b.play(&ru, true);
    let cs = cases(12, true);
    let r = run(&b.ops, 0, &|w| {
        for (k, c) in cs.iter().enumerate() {
            put(w, &t, k, &c.t); put(w, &s, k, &c.s);
            put(w, &v2, k, &N::from(c.v2 as u64)); put(w, &v, k, &N::from(c.v as u64));
            if c.g == 1 { w[g.0 as usize] |= 1 << k; }
            w[ep.0 as usize] |= 1 << k;
        }
    });
    assert_eq!(r.phase, 0);
    for (k, c) in cs.iter().enumerate() {
        let to = field(&c.t, c.v2, c.v);
        let so = field(&c.s, c.v2, c.v);
        let mask = ((N::from(1u64) << (c.v - c.v2 + 1)) - N::from(1u64)) << c.v2;
        let te = if c.g == 1 { (c.t & !mask) | ((to + so) << c.v2) } else { c.t };
        assert_eq!(get(&r.q, &t, k), te, "t k={k}");
        assert_eq!(getb(&r.q, g, k), 0, "beta erased k={k}");
        assert_eq!(get(&r.q, &s, k), c.s);
    }
}

#[test]
fn masked_reversed_window() {
    // physical lanes 0..40, value LSB at phys 39 going down; own = phys >= v (v in [0, 23]).
    // ladder order l = 0 -> phys 39 ... l = 39 -> phys 0; window ladder [16, 40) = phys [0, 24), dir -1, base 39.
    let mut b = B::new();
    let tp = b.alloc_n(40);
    let sp = b.alloc_n(40);
    let c0 = b.alloc();
    let v = b.alloc_n(5);
    let pre = b.alloc_n(4);
    let sc = Mscr { f: b.alloc(), t: b.alloc(), gf: b.alloc(), chain: pre.clone(), dirty: vec![] };
    let g = b.alloc();
    let x = b.alloc();
    let tl: Vec<QubitId> = (0..40).map(|l| tp[39 - l]).collect();
    let sl: Vec<QubitId> = (0..40).map(|l| sp[39 - l]).collect();
    let wins = vec![Src { lo: 16, hi: 40, v: v.clone(), a: 40, d: -1, pre: pre.clone(), late: false }];
    let ld = Lad { t: &tl, s: &sl, c0, srcs: &wins, f0: true, cmpl: true, sc: &sc, keep_f: false };
    let ru = mup(&mut b, &ld);
    let rd = mdown(&mut b, &ld, Some(x));
    b.play(&ru, false);
    let ct = top_carry(&ld);
    b.x(ct);
    b.and_c(g, ct, x);
    b.x(ct);
    b.play(&rd, false);
    let mut rng = Rng::new(77);
    let cs: Vec<(N, N, usize, u64)> = (0..64).map(|_| (rng.below(40), rng.below(40), (rng.next() % 24) as usize, rng.next() & 1)).collect();
    let own = |x: &N, vv: usize| -> N { let mut r = N::ZERO; for p in vv..40 { if x.bit(p) { r |= N::from(1u64) << (39 - p); } } r };
    let r = run(&b.ops, 0, &|w| {
        for (k, c) in cs.iter().enumerate() {
            put(w, &tp, k, &c.0); put(w, &sp, k, &c.1); put(w, &v, k, &N::from(c.2 as u64));
            if c.3 == 1 { w[g.0 as usize] |= 1 << k; }
        }
    });
    assert_eq!(r.phase, 0);
    for (k, c) in cs.iter().enumerate() {
        let (to, so) = (own(&c.0, c.2), own(&c.1, c.2));
        let xe = c.3 == 1 && to >= so;
        assert_eq!(getb(&r.q, x, k) == 1, xe, "x k={k}");
        let got = get(&r.q, &tp, k);
        let rest_ok = (0..c.2).all(|p| got.bit(p) == c.0.bit(p));
        assert!(rest_ok, "foreign lanes changed k={k}");
        let want = if xe { to - so } else { to };
        assert_eq!(own(&got, c.2), want, "own field k={k}");
        assert_eq!(get(&r.q, &sp, k), c.1);
    }
}

#[test]
fn masked_overlapping_windows() {
    // own = [v2 <= lane <= v], wrap toggles at v2 in [0,30), band toggles at v+1 in [10,40): windows overlap.
    let mut b = B::new();
    let t = b.alloc_n(40);
    let s = b.alloc_n(40);
    let c0 = b.alloc();
    let v2 = b.alloc_n(5);
    let v = b.alloc_n(6);
    let pa = b.alloc_n(4);
    let pb = b.alloc_n(5);
    let sc = Mscr { f: b.alloc(), t: b.alloc(), gf: b.alloc(), chain: pb.clone(), dirty: vec![] };
    let x = b.alloc();
    let g = b.alloc();
    let srcs = vec![
        Src { lo: 0, hi: 30, v: v2.clone(), a: 0, d: 1, pre: pa.clone(), late: false },
        Src { lo: 10, hi: 40, v: v.clone(), a: -1, d: 1, pre: pb.clone(), late: false },
    ];
    let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: false, cmpl: true, sc: &sc, keep_f: false };
    let ru = mup(&mut b, &ld);
    let rd = mdown(&mut b, &ld, Some(x));
    b.play(&ru, false);
    let ct = top_carry(&ld);
    b.x(ct);
    b.and_c(g, ct, x);
    b.x(ct);
    b.play(&rd, false);
    let mut rng = Rng::new(31);
    let cs: Vec<(N, N, usize, usize, u64)> = (0..64).map(|_| {
        let a = (rng.next() % 30) as usize;
        let hi = (a.max(10)).max(9) + (rng.next() % (39 - a.max(9) as u64 + 0).max(1)) as usize;
        let vv = hi.min(39).max(9).max(a.saturating_sub(1));
        (rng.below(40), rng.below(40), a, vv, rng.next() & 1)
    }).collect();
    let r = run(&b.ops, 0, &|w| {
        for (k, c) in cs.iter().enumerate() {
            put(w, &t, k, &c.0); put(w, &s, k, &c.1);
            put(w, &v2, k, &N::from(c.2 as u64)); put(w, &v, k, &N::from(c.3 as u64));
            if c.4 == 1 { w[g.0 as usize] |= 1 << k; }
        }
    });
    assert_eq!(r.phase, 0);
    for (k, c) in cs.iter().enumerate() {
        let (to, so) = (field(&c.0, c.2, c.3), field(&c.1, c.2, c.3));
        let xe = c.4 == 1 && to >= so;
        assert_eq!(getb(&r.q, x, k) == 1, xe, "x k={k} v2={} v={}", c.2, c.3);
        let w = if c.3 + 1 >= c.2 { c.3 + 1 - c.2 } else { 0 };
        let mask = if w > 0 { ((N::from(1u64) << w) - N::from(1u64)) << c.2 } else { N::ZERO };
        let te = if xe { (c.0 & !mask) | ((to - so) << c.2) } else { c.0 };
        assert_eq!(get(&r.q, &t, k), te, "t k={k}");
        assert_eq!(get(&r.q, &s, k), c.1);
        for &q in [sc.f, sc.t, sc.gf, c0].iter().chain(pa.iter()).chain(pb.iter()) { assert_eq!(getb(&r.q, q, k), 0); }
    }
}
