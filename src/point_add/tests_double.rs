//! froghop-double tests: masked ladders, then the slot against refmodel_double.

use super::builder::B;
use super::mask::*;
use super::refmodel_double::N;
use crate::circuit::{analyze_ops, Op, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};

pub struct Sim {
    pub q: Vec<u64>,
    pub phase: u64,
    pub tof: u64,
}

/// Run ops on 64 shots starting from `init` qubit words; returns final words, phase word, Toffoli count.
pub fn run(ops: &[Op], nq: usize, init: &dyn Fn(&mut Vec<u64>)) -> Sim {
    let (aq, nb, _, _) = analyze_ops(ops.iter());
    let nq = nq.max(aq as usize);
    let mut h = sha3::Shake256::default();
    h.update(b"froghop-test");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(nq, (nb as usize).max(1), &mut xof);
    init(&mut s.qubits);
    s.apply_iter(ops.iter());
    Sim { q: s.qubits.clone(), phase: s.phase, tof: s.stats.toffoli_gates }
}

pub struct Rng(u64);
impl Rng {
    pub fn new(s: u64) -> Rng {
        Rng(s ^ 0x9E3779B97F4A7C15)
    }
    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    pub fn below(&mut self, bits: usize) -> N {
        let mut v = N::ZERO;
        for i in 0..6 {
            v |= N::from(self.next()) << (64 * i);
        }
        if bits < 384 { v & ((N::from(1u64) << bits) - N::from(1u64)) } else { v }
    }
}


fn put(words: &mut [u64], qs: &[QubitId], shot: usize, val: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if val.bit(i) { words[q.0 as usize] |= 1 << shot } else { words[q.0 as usize] &= !(1 << shot) }
    }
}
pub(super) fn get(words: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (words[q.0 as usize] >> shot) & 1 == 1 { v |= N::from(1u64) << i; }
    }
    v
}
pub(super) fn getb(words: &[u64], q: QubitId, shot: usize) -> u64 { (words[q.0 as usize] >> shot) & 1 }
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
        Src { lo: 0, hi: 9, v: v2.clone(), a: 0, d: 1, pre: pre[..3].to_vec(), late: false, hk: None },
        Src { lo: 24, hi: 40, v: v.clone(), a: -1, d: 1, pre: pre.clone(), late: false, hk: None },
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
    let wins = vec![Src { lo: 16, hi: 40, v: v.clone(), a: 40, d: -1, pre: pre.clone(), late: false, hk: None }];
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
        Src { lo: 0, hi: 30, v: v2.clone(), a: 0, d: 1, pre: pa.clone(), late: false, hk: None },
        Src { lo: 10, hi: 40, v: v.clone(), a: -1, d: 1, pre: pb.clone(), late: false, hk: None },
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

use super::froghop_double::{BB, FhDouble, LayDouble, WD, WD_D};
use super::refmodel_double::{self as rmd, Ph};

pub fn lay_double() -> LayDouble {
    LayDouble::from_text(include_str!("sched_double.txt"), 24)
}

pub fn expect_lanes(m: &rmd::St) -> (Vec<u8>, Vec<u8>) {
    let w = WD;
    let wd = WD_D;
    let mut d = vec![0u8; wd];
    let mut v = vec![0u8; w];
    for j in 0..wd {
        if j < 300 && m.r.bit(j) { d[j] |= 1; }
        if m.cd.bit(wd - 1 - j) { d[j] |= 1; }
    }
    if m.ph == rmd::Ph::Dn {
        // DONE counter XORed into D lanes WD_D-256.. (p's top bits)
        for j in 0..8 { d[wd - 256 + j] ^= ((m.cnt >> j) & 1) as u8; }
    }
    let mut vf = vec![0u8; w]; // V frame
    for u in 0..w {
        if m.rv.bit(u) { vf[u] = 1; }
        if m.cv.bit(w - 1 - u) { vf[u] = 1; }
    }
    // stored quotient bits stk[1..] (stk[0] = c_k is never stored) at V-frame lanes b + j
    for (j, &bit) in m.stk.iter().enumerate().skip(1) {
        vf[m.b as usize + j] ^= bit;
    }
    for u in 0..w {
        let p = ((u as i64 + m.pi as i64).rem_euclid(w as i64)) as usize;
        v[p] = vf[u];
    }
    (d, v)
}

/// lane FHD-LEFT (PARV): where the swap parity lives at a slot boundary: (in D?, physical lane)
pub fn par_lane(m: &rmd::St) -> (bool, usize) {
    let w = WD as i64;
    let wd = WD_D as i64;
    let (b, pi, dep) = (m.b as i64, m.pi as i64, m.stk.len() as i64);
    let vf = |u: i64| ((u + pi).rem_euclid(w)) as usize;
    match m.ph {
        Ph::Al | Ph::Dn => (false, vf(b)),
        Ph::Dv => (false, vf(b + (pi + dep).max(1))),
        Ph::Co => {
            // lane FHD-787: k >= 2 shots host at D[b + k - 1] (the M2's bq + depth scan); the k <= 1 shots keep
            // the parity at the V-frame b + max(k, 1) (the marker's t[0] cell - no hosting, the S6 reads it there)
            let k = pi + dep - 1;
            if k >= 2 {
                (true, (b + k - 1 - super::froghop_double::c787_on() as i64) as usize)
            } else {
                if super::froghop_double::c787_on() { (false, vf(b)) } else { (false, ((b + 1 + pi).rem_euclid(w)) as usize) }
            }
        }
        Ph::Rt => (false, vf(b)),
    }
}

/// lane FHD-LEFT (PARV): the circuit flips the parity at the CO -> RT marker, the model at the RT0 swap
pub fn par_bit(m: &rmd::St, init: u8) -> u8 {
    init ^ m.par ^ (m.ph == Ph::Rt) as u8
}

#[test]
fn double_traversal_matches_model() {
    let lay = lay_double();
    let w = WD;
    let wd = WD_D;
    let mut b = B::new();
    let d = b.alloc_n(wd);
    let v = b.alloc_n(w);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
    let mut rng = Rng::new(std::env::var("DSEED").ok().and_then(|s| s.parse().ok()).unwrap_or(4242));
    let pp = rmd::p();
    let mut models: Vec<rmd::St> = (0..64).map(|_| {
        let mut x = rng.below(256) % pp;
        if x == N::ZERO { x = N::from(1u64); }
        rmd::St::new(x)
    }).collect();
    // lane FHD-789: shots with a >= 24-bit Euclid quotient (pi reaches 24) collide in the joint (h, depth) code and
    // are expected to leave the model (the row's error trade); every other shot is checked as before
    let skip: Vec<bool> = models.iter().map(|m| super::tests_789::max_q_bits(&(if m.refl == 1 { pp - m.rv } else { m.rv })) >= super::froghop_double::QBAD).collect();
    let skipmask: u64 = (0..64).filter(|&k| skip[k]).fold(0, |a, k| a | (1u64 << k));
    if skipmask != 0 { eprintln!("L19: shots with a >= QBAD-bit quotient (not checked): {:?}", (0..64).filter(|&k| skip[k]).collect::<Vec<_>>()); }
    let vl: Vec<QubitId> = f.v[1..257].to_vec();
    f.init(&mut b, &lay);
    let nq = b.width() as usize;
    let mods = models.clone();
    let dq = dirty.clone();
    // lane FHD-LEFT (PARV): a random initial parity per shot in V's top lane (the first AL's V-frame b = 256)
    let mut parinit: Vec<u8> = (0..64).map(|k| ((rng.next() >> (k % 7)) & 1) as u8).collect();
    if let Ok(v) = std::env::var("C787_PARFLIP") { for t in v.split(',') { let k: usize = t.parse().unwrap(); parinit[k] ^= 1; } }
    let vtop = f.v[w - 1];
    let parv = f.parv;
    let pin = parinit.clone();
    let mut words = run(&b.ops, nq, &|wd| {
        for k in 0..64 { put(wd, &vl, k, &mods[k].rv); }
        if parv { for k in 0..64 { if pin[k] == 1 { wd[vtop.0 as usize] |= 1 << k; } } }
        for (i, &q) in dq.iter().enumerate() { wd[q.0 as usize] = 0x9E3779B97F4A7C15u64.wrapping_mul(i as u64 + 7) ^ 0x5bd1e995; }
    }).q;
    let dirty0: Vec<u64> = dirty.iter().map(|q| words[q.0 as usize]).collect();
    let mut tof = 0u64;
    let pool = f.pool.clone();
    let mut prev: Vec<rmd::St> = models.clone();
    for sigma in 0..lay.s {
        for k in 0..64 {
            if skip[k] { continue; }
            let m = &models[k];
            {
                let (mut ed, _) = expect_lanes(m);
                if parv { let (ind, l) = par_lane(m); if ind { ed[l] ^= par_bit(m, parinit[k]); } }
                let bad: Vec<usize> = (0..wd).filter(|&j| getb(&words, f.d[j], k) as u8 != ed[j]).collect();
                if !bad.is_empty() {
                    let p = &prev[k];
                    eprintln!("slot {sigma} shot {k}: D mismatch lanes {:?}; prev {:?} pi {} stk {:?} b {} R {} rv {} cd {} cv {}; now {:?} pi {} R {}",
                        &bad[..bad.len().min(8)], p.ph, p.pi, p.stk, p.b, p.r.bit_len(), p.rv.bit_len(), p.cd.bit_len(), p.cv.bit_len(),
                        m.ph, m.pi, m.r);
                    eprintln!("   row prev {:?}", lay.rows[sigma.saturating_sub(1)]);
                }
            }
            if let Ok(v) = std::env::var("C787_MDUMP") {
                let v: Vec<usize> = v.split(':').map(|x| x.parse().unwrap()).collect();
                if v[0] == sigma && v[1] == k {
                    eprintln!("MDUMP slot {sigma} shot {k}: ph {:?} pi {} stk {:?} b {} | BL r {} cd {} rv {} cv {} | cd {:x} cv {:x} par {}", m.ph, m.pi, m.stk, m.b, m.r.bit_len(), m.cd.bit_len(), m.rv.bit_len(), m.cv.bit_len(), m.cd, m.cv, par_bit(m, parinit[k]));
                }
            }
            let (mut ed, mut ev) = expect_lanes(m);
            let rtdep = parv && m.ph == Ph::Rt && super::froghop_double::c787_rtdep();
            if parv && !rtdep {
                let (ind, l) = par_lane(m);
                let pb = par_bit(m, parinit[k]);
                if ind { ed[l] ^= pb; } else { ev[l] ^= pb; }
            }
            if std::env::var_os("FHD_DBG").is_some() {
                let bd: Vec<usize> = (0..wd).filter(|&j| getb(&words, f.d[j], k) as u8 != ed[j]).collect();
                let bv: Vec<usize> = (0..w).filter(|&j| getb(&words, f.v[j], k) as u8 != ev[j]).collect();
                if !bd.is_empty() || !bv.is_empty() {
                    let p = &prev[k];
                    eprintln!("DBG slot {sigma} shot {k}: D bad {:?} V bad {:?}; now {:?} pi {} dep {} b {} par_lane {:?} bit {}; prev {:?} pi {} dep {} b {} par_lane {:?}", bd, bv, m.ph, m.pi, m.stk.len(), m.b, par_lane(m), par_bit(m, parinit[k]), p.ph, p.pi, p.stk.len(), p.b, par_lane(p));
                    let code = [f.p0, f.p1, f.p2].iter().map(|&q| getb(&words, q, k)).collect::<Vec<_>>();
                    eprintln!("DBG   circuit: code {:?} pi lanes {} dep lanes {} bq {} (want {:?} bq {})", code, get(&words, &f.pi, k), get(&words, &f.dep, k), get(&words, &f.bq, k),
                        super::froghop_double::l19_encode((m.pi >> 1) as u64, m.stk.len() as u64), ((m.b as i64 - 1 - lay.base[sigma] as i64).rem_euclid(1 << BB)));
                }
            }
            for j in 0..wd {
                assert_eq!(getb(&words, f.d[j], k) as u8, ed[j], "slot {sigma} shot {k} D lane {j} ph {:?}", m.ph);
            }
            for j in 0..w {
                assert_eq!(getb(&words, f.v[j], k) as u8, ev[j], "slot {sigma} shot {k} V lane {j} ph {:?} pi {}", m.ph, m.pi);
            }
            let (epi, mut edep) = super::froghop_double::l19_encode((m.pi >> 1) as u64, m.stk.len() as u64);
            if rtdep { edep ^= (par_bit(m, parinit[k]) as u64) << 2; }
            assert_eq!(get(&words, &f.pi, k), N::from(epi), "slot {sigma} shot {k} pi >> 1 (L19 code)");
            assert_eq!(m.pi & 1, if sigma % 2 == 0 { 1 } else { 0 }, "slot {sigma} shot {k} pi parity");
            let code = [f.p0, f.p1, f.p2].iter().map(|&q| getb(&words, q, k)).collect::<Vec<_>>();
            let want = match m.ph { Ph::Al => [1, 0, 0], Ph::Dv => [0, 1, 0], Ph::Co => [1, 1, 0], Ph::Rt => [0, 0, 0], Ph::Dn => [0, 0, 1] };
            assert_eq!(code, want.to_vec(), "slot {sigma} shot {k} phase {:?} pi {} dep {} b {}; prev {:?} pi {} dep {} b {}", m.ph, m.pi, m.stk.len(), m.b, prev[k].ph, prev[k].pi, prev[k].stk.len(), prev[k].b);
            assert_eq!(get(&words, &f.bq, k), N::from(((m.b as i64 - 1 - lay.base[sigma] as i64).rem_euclid(1 << BB)) as u64), "slot {sigma} shot {k} b");
            assert_eq!(get(&words, &f.dep, k), N::from(edep), "slot {sigma} shot {k} dep (L19 code)");
            if !parv {
                assert_eq!(getb(&words, f.par, k) as u8, m.par, "par");
            }
        }
        let start = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        let ops = b.ops[start..].to_vec();
        if let Ok(tr) = std::env::var("FHD_TRACE") {
            let v: Vec<usize> = tr.split(':').map(|x| x.parse().unwrap()).collect();
            if v[0] == sigma {
                let k = v[1];
                let marks: Vec<(&str, usize)> = f.marks.iter().filter(|m| m.1 >= start).map(|m| (m.0, m.1 - start)).chain([("end", ops.len())]).collect();
                for &(nm, mk) in marks.iter() {
                    let wd = words.clone();
                    let rr = run(&ops[..mk], nq, &move |x| x.copy_from_slice(&wd));
                    let code = [f.p0, f.p1, f.p2].iter().map(|&q| getb(&rr.q, q, k)).collect::<Vec<_>>();
                    let vs: String = std::env::var("C787_TLO").map(|_| (0..8).collect::<Vec<usize>>()).unwrap_or((250..258).collect()).iter().map(|&j| format!("{}", getb(&rr.q, f.v[j], k))).collect();
                    let ds: String = std::env::var("C787_TLO").map(|_| (0..8).collect::<Vec<usize>>()).unwrap_or((250..257).collect()).iter().map(|&j| format!("{}", getb(&rr.q, f.d[j], k))).collect();
                    eprintln!("TRACE slot {sigma} shot {k} at {nm} (op {mk}): code {:?} pi {} dep {} bq {} V250.. {vs} D250.. {ds}", code, get(&rr.q, &f.pi, k), get(&rr.q, &f.dep, k), get(&rr.q, &f.bq, k));
                }
            }
        }
        let wd = words.clone();
        let r0 = words.clone();
        let r = run(&ops, nq, &move |x| x.copy_from_slice(&wd));
        if r.phase != 0 {
            let marks: Vec<(&str, usize)> = f.marks.iter().filter(|m| m.1 >= start).map(|m| (m.0, m.1 - start)).chain([("end", ops.len())]).collect();
            for &(nm, mk) in marks.iter() {
                let wd = r0.clone();
                let rr = run(&ops[..mk], nq, &move |x| x.copy_from_slice(&wd));
                eprintln!("  phase at mark {nm} (op {mk}): {:#x}", rr.phase);
            }
            if let Ok(_) = std::env::var("OPBIS") {
                let s8 = marks.iter().find(|m| m.0 == "S8").map(|m| m.1).unwrap_or(0);
                let top = marks.iter().find(|m| m.0 == "S8 top").map(|m| m.1).unwrap_or(ops.len());
                for i in s8..top {
                    let wd = r0.clone();
                    let rr = run(&ops[..i + 1], nq, &move |x| x.copy_from_slice(&wd));
                    if rr.phase != 0 {
                        eprintln!("first phase at op {} : {:?}", i, ops[i]);
                        for j in i.saturating_sub(6)..=i { eprintln!("   op {}: {:?}", j, ops[j]); }
                        break;
                    }
                }
            }
            for k in 0..64 {
                if (r.phase >> k) & 1 == 1 {
                    let m = &models[k];
                    let mut m2 = m.clone(); m2.fwd(sigma);
                    eprintln!("phase shot {k}: pre {:?} pi {} stk {:?} b {} | post {:?} pi {} stk {:?}", m.ph, m.pi, m.stk, m.b, m2.ph, m2.pi, m2.stk);
                }
            }
        }
        assert_eq!(r.phase & !skipmask, 0, "phase after slot {sigma}");
        tof += r.tof;
        words = r.q;
        for (i, q) in dirty.iter().enumerate() { assert_eq!(words[q.0 as usize] & !skipmask, dirty0[i] & !skipmask, "dirty qubit {i} not restored after slot {sigma}"); }
        for &q in &pool {
            if words[q.0 as usize] & !skipmask != 0 {
                for k in 0..64 {
                    if (words[q.0 as usize] >> k) & 1 == 1 {
                        let m = &models[k];
                        let mut m2 = m.clone(); m2.fwd(sigma);
                        eprintln!("shot {k}: pre {:?} pi {} stk {:?} b {} | post {:?} pi {} | bits cv {} cd {} rv {} R {}",
                            m.ph, m.pi, m.stk, m.b, m2.ph, m2.pi, m2.cv.bit_len(), m2.cd.bit_len(), m2.rv.bit_len(), m2.r.bit_len());
                    }
                }
                let marks: Vec<(&str, usize)> = f.marks.iter().filter(|m| m.1 >= start).map(|m| (m.0, m.1 - start)).chain([("end", ops.len())]).collect();
                for &(nm, mk) in marks.iter() {
                    let wd = r0.clone();
                    let rr = run(&ops[..mk], nq, &move |x| x.copy_from_slice(&wd));
                    for k in 0..64 {
                        if (words[q.0 as usize] >> k) & 1 == 1 {
                            eprintln!("  mark {nm} (op {mk}) shot {k}: q {} bq {} pi {}", getb(&rr.q, q, k), get(&rr.q, &f.bq, k), get(&rr.q, &f.pi, k));
                        }
                    }
                }
                panic!("scratch q{} dirty after slot {sigma} row {:?}", q.0, lay.rows[sigma]);
            }
        }
        prev = models.clone();
        for m in models.iter_mut() { m.fwd(sigma); }
    }
    for (k, m) in models.iter().enumerate() { if skip[k] { continue; } assert!(m.ph == Ph::Dn); let _ = m.result(); }
    eprintln!("v2 traversal: {} slots, avg Toffoli/shot {} ({} per slot), qubits {}", lay.s, tof / 64, tof / 64 / lay.s as u64, b.width());
}

#[test]
fn double_forward_inverse_identity() {
    let lay = lay_double();
    let w = WD;
    for seed in 0..4u64 {
        let mut b = B::new();
        let d = b.alloc_n(w);
        let v = b.alloc_n(w);
        let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
        let vl: Vec<QubitId> = f.v[1..257].to_vec();
        let v0 = f.v.clone();
        let mut rng = Rng::new(900 + seed);
        let pp = rmd::p();
        let xs: Vec<N> = (0..64).map(|_| { let x = rng.below(256) % pp; if x == N::ZERO { N::from(1u64) } else { x } }).collect();
        let ms: Vec<rmd::St> = xs.iter().map(|&x| rmd::St::new(x)).collect();
        f.init(&mut b, &lay);
        let maps = f.forward(&mut b, &lay);
        f.inverse(&mut b, &lay, &maps);
        f.init(&mut b, &lay);
        assert_eq!(f.v, v0);
        let nq = b.width() as usize;
        let r = run(&b.ops, nq, &|wd| { for k in 0..64 { put(wd, &vl, k, &ms[k].rv); } });
        // lane FHD-789: shots with a >= 24-bit quotient are this row's expected failures (not checked)
        let skipmask: u64 = (0..64).filter(|&k| super::tests_789::max_q_bits(&xs[k]) >= super::froghop_double::QBAD).fold(0, |a, k| a | (1u64 << k));
        if skipmask != 0 { eprintln!("v2 seed {seed}: L19 collision shots (>= QBAD-bit quotient) mask {skipmask:#x}, phase {:#x}", r.phase); }
        assert_eq!(r.phase & !skipmask, 0, "phase");
        for q in 0..nq {
            if vl.iter().any(|x| x.0 as usize == q) { continue; }
            assert_eq!(r.q[q] & !skipmask, 0, "qubit {q} not restored (seed {seed})");
        }
        for k in 0..64 { if (skipmask >> k) & 1 == 1 { continue; } assert_eq!(get(&r.q, &vl, k), ms[k].rv); }
        eprintln!("v2 seed {seed}: forward+inverse identity ok, tof/shot {}", r.tof / 64);
    }
}

#[test]
fn double_slot_inverse_bisect() {
    let lay = lay_double();
    let w = WD;
    // per-slot: run forward up to slot s-1, then slot s and its inverse; check phase and state restored
    let mut b = B::new();
    let d = b.alloc_n(w);
    let v = b.alloc_n(w);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
    let vl: Vec<QubitId> = f.v[1..257].to_vec();
    let mut rng = Rng::new(std::env::var("DSEED").ok().and_then(|s| s.parse().ok()).unwrap_or(901));
    let pp = rmd::p();
    let xs: Vec<N> = (0..64).map(|_| rng.below(256) % pp).collect();
    let ms: Vec<rmd::St> = xs.iter().map(|&x| rmd::St::new(x)).collect();
    f.init(&mut b, &lay);
    let nq = b.width() as usize;
    let mut words = run(&b.ops, nq, &|wd| { for k in 0..64 { put(wd, &vl, k, &ms[k].rv); } }).q;
    for sigma in 0..lay.s {
        let vmap = f.v.clone();
        let start = b.ops.len();
        b.begin();
        f.slot(&mut b, &lay, sigma);
        let rec = b.end();
        let vafter = f.v.clone();
        b.play(&rec, false);
        b.play(&rec, true);
        let ops = b.ops[start..].to_vec();
        let wd = words.clone();
        let r = run(&ops, nq, &move |x| x.copy_from_slice(&wd));
        if r.phase != 0 || r.q != words {
            let diff: Vec<usize> = (0..nq).filter(|&q| r.q[q] != words[q]).collect();
            panic!("slot {sigma}: fwd+inv not identity: phase {:#x}, changed qubits {:?}", r.phase, &diff[..diff.len().min(10)]);
        }
        // advance forward
        b.ops.truncate(start);
        f.v = vmap;
        let s2 = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        assert_eq!(f.v, vafter);
        let ops = b.ops[s2..].to_vec();
        let wd = words.clone();
        words = run(&ops, nq, &move |x| x.copy_from_slice(&wd)).q;
    }
}

#[test]
fn double_profile() {
    use crate::circuit::OperationType as OT;
    use std::collections::BTreeMap;
    let lay = lay_double();
    let mut b = B::new();
    let d = b.alloc_n(WD_D);
    let v = b.alloc_n(WD);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
    f.init(&mut b, &lay);
    let mut tot: BTreeMap<&'static str, u64> = BTreeMap::new();
    for sigma in 0..lay.s {
        f.marks.clear();
        let start = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        let mut mk = vec![("pre", start)];
        mk.extend(f.marks.iter().cloned());
        mk.push(("end", b.ops.len()));
        for i in 0..mk.len() - 1 {
            let c = b.ops[mk[i].1..mk[i + 1].1].iter().filter(|o| matches!(o.kind, OT::CCX | OT::CCZ)).count() as u64;
            *tot.entry(mk[i].0).or_default() += c;
        }
    }
    let all: u64 = tot.values().sum();
    for (k, v) in &tot {
        eprintln!("{:10} {:>9} ({:5.1}%) {:7.1}/slot", k, v, 100.0 * *v as f64 / all as f64, *v as f64 / lay.s as f64);
    }
    eprintln!("total {} ({:.1}/slot)", all, all as f64 / lay.s as f64);
    eprintln!("scratch peaks per step: {:?}", f.peaks);
}

#[test]
fn double_point_add_end_to_end() {
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    let lay = lay_double();
    let mut b = B::new();
    let (xq, yq) = super::pointadd_double::point_add(&mut b, &lay);
    let ops = b.ops.clone();
    let (nq, _, _, regs) = crate::circuit::analyze_ops(ops.iter());
    eprintln!("ops {} qubits {} peak {} emitted tof {}", ops.len(), nq, b.peak, b.tof);
    // curve
    let pp = super::refmodel_double::p();
    let to_u = |v: &N| -> ruint::aliases::U256 { ruint::aliases::U256::from_limbs(v.as_limbs()[0..4].try_into().unwrap()) };
    type U = ruint::aliases::U256;
    let hx = |h: &str| U::from_str_radix(h, 16).unwrap();
    let curve = WeierstrassEllipticCurve {
        modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
        a: U::ZERO,
        b: U::from(7u64),
        gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
        gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
        order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
    };
    let _ = &pp;
    let mut rng = Rng::new(2024);
    let mut cases = vec![];
    for _ in 0..64 {
        let k1 = to_u(&(rng.below(250) + N::from(1u64)));
        let k2 = to_u(&(rng.below(250) + N::from(1u64)));
        let t = curve.mul(curve.gx, curve.gy, k1);
        let o = curve.mul(curve.gx, curve.gy, k2);
        let e = curve.add(t.0, t.1, o.0, o.1);
        cases.push((t, o, e));
    }
    use sha3::digest::{ExtendableOutput, Update};
    let mut h = sha3::Shake256::default();
    h.update(b"froghop-e2e");
    let mut xof = h.finalize_xof();
    let (_, nb, _, _) = crate::circuit::analyze_ops(ops.iter());
    let mut sim = crate::sim::Simulator::new(nq as usize, nb as usize, &mut xof);
    for (k, (t, o, _)) in cases.iter().enumerate() {
        sim.set_register(&regs[0], t.0, k);
        sim.set_register(&regs[1], t.1, k);
        sim.set_register(&regs[2], o.0, k);
        sim.set_register(&regs[3], o.1, k);
    }
    sim.apply_iter(ops.iter());
    let mut bad = 0;
    for (k, (_, _, e)) in cases.iter().enumerate() {
        let gx = sim.get_register(&regs[0], k);
        let gy = sim.get_register(&regs[1], k);
        if gx != e.0 || gy != e.1 { bad += 1; }
    }
    assert_eq!(sim.phase, 0, "phase garbage");
    let regq: std::collections::HashSet<u64> = xq.iter().chain(yq.iter()).map(|q| q.0).collect();
    for q in 0..nq {
        if !regq.contains(&q) { assert_eq!(sim.qubits[q as usize], 0, "ancilla garbage q{q}"); }
    }
    assert_eq!(bad, 0, "classical mismatches");
    eprintln!("v2 end-to-end OK: avg Toffoli {}", sim.stats.toffoli_gates / 64);
}


#[test]
fn modp_double_fold_dirty_carry() {
    use super::modp_double::{add_small, Ms, C};
    for &(lo, k) in &[(4usize, C - 1)] {
        let mut b = B::new();
        let t = b.alloc_n(256);
        let g = b.alloc_n(256);
        let ctl = b.alloc();
        let ms = Ms::alloc(&mut b);
        add_small(&mut b, &ms, &t, lo, Some(ctl), k, &g);
        let mut rng = Rng::new(lo as u64 + 77);
        let mut tv: Vec<N> = vec![];
        let mut gv: Vec<N> = vec![];
        for s in 0..64 {
            let mut x = rng.below(256);
            // force long carry runs into both borrowed increments, but keep bits 41 and 63 clear (no truncation)
            if s % 2 == 0 { for j in 0..41 { x |= N::from(1u64) << j; } }
            if s % 4 == 0 { for j in 32..63 { x |= N::from(1u64) << j; } }
            let c41: N = N::from(1u64) << 41;
            let c63: N = N::from(1u64) << 63;
            x &= !c41;
            x &= !c63;
            tv.push(x);
            gv.push(rng.below(256));
        }
        let (tv2, gv2, t2, g2) = (tv.clone(), gv.clone(), t.clone(), g.clone());
        let r = run(&b.ops, 0, &move |w| {
            for s in 0..64 {
                put(w, &t2, s, &tv2[s]);
                put(w, &g2, s, &gv2[s]);
                if s % 3 != 2 { w[ctl.0 as usize] |= 1 << s; }
            }
        });
        let m256 = (N::from(1u64) << 256) - N::from(1u64);
        for s in 0..64 {
            let c = s % 3 != 2;
            let want = (tv[s] + if c { N::from(k) } else { N::ZERO }) & m256;
            assert_eq!(get(&r.q, &t, s), want, "fold lo {lo} shot {s}");
            assert_eq!(get(&r.q, &g, s), gv[s], "dirty restored");
            assert_eq!(getb(&r.q, ctl, s), c as u64, "ctrl restored");
        }
        assert_eq!(r.phase, 0);
        for &q in ms.s.iter().chain([ms.c0, ms.k, ms.c1].iter()) { for s in 0..64 { assert_eq!(getb(&r.q, q, s), 0); } }
        eprintln!("fold lo {lo}: ok ({} T)", b.tof);
    }
}

/// ds-q787 debug: per-op state hash of slot 1, shot 1 (V lanes + phase + pi + dep + bq + par + phase word).
/// Run with Q787_TRACE=1 --nocapture. Diff t/ vs parent output: first differing T line = first divergent op.
#[test]
fn q787_trace_slot1() {
    if std::env::var_os("Q787_TRACE").is_none() { return; }
    let lay = lay_double();
    let w = WD;
    let wd = WD_D;
    let mut b = B::new();
    let d = b.alloc_n(wd);
    let v = b.alloc_n(w);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
    let mut rng = Rng::new(std::env::var("DSEED").ok().and_then(|s| s.parse().ok()).unwrap_or(4242));
    let pp = rmd::p();
    let mut models: Vec<rmd::St> = (0..64).map(|_| {
        let mut x = rng.below(256) % pp;
        if x == N::ZERO { x = N::from(1u64); }
        rmd::St::new(x)
    }).collect();
    let _skip: Vec<bool> = models.iter().map(|m| super::tests_789::max_q_bits(&(if m.refl == 1 { pp - m.rv } else { m.rv })) >= super::froghop_double::QBAD).collect();
    let vl: Vec<QubitId> = f.v[1..257].to_vec();
    f.init(&mut b, &lay);
    let nq = b.width() as usize;
    let mods = models.clone();
    let dq = dirty.clone();
    let parinit: Vec<u8> = (0..64).map(|k| ((rng.next() >> (k % 7)) & 1) as u8).collect();
    let vtop = f.v[w - 1];
    let parv = f.parv;
    let pin = parinit.clone();
    let words0 = run(&b.ops, nq, &|wd| {
        for k in 0..64 { put(wd, &vl, k, &mods[k].rv); }
        if parv { for k in 0..64 { if pin[k] == 1 { wd[vtop.0 as usize] |= 1 << k; } } }
        for (i, &q) in dq.iter().enumerate() { wd[q.0 as usize] = 0x9E3779B97F4A7C15u64.wrapping_mul(i as u64 + 7) ^ 0x5bd1e995; }
    }).q;
    let s0start = b.ops.len();
    // capture the slot-0 physical ids before the rotation (S9) reassigns self.v
    let id_v255_0: u64 = f.v[255].0; let id_v256_0: u64 = f.v[256].0; let id_v257_0: u64 = f.v[257].0;
    let id_d255_0: u64 = f.d[255].0; let id_d256_0: u64 = f.d[256].0; let id_f_0: u64 = f.p0.0; let id_bq_0: Vec<u64> = f.bq.iter().map(|q| q.0).collect();
    f.slot(&mut b, &lay, 0);
    let ops0: Vec<Op> = b.ops[s0start..].to_vec();
    let words1 = run(&ops0, nq, &|x| x.copy_from_slice(&words0)).q;
    let start = b.ops.len();
    // capture the slot-1 physical ids before slot 1's rotation reassigns self.v
    let id_v255_1: u64 = f.v[255].0; let id_v256_1: u64 = f.v[256].0; let id_v257_1: u64 = f.v[257].0;
    let id_d255_1: u64 = f.d[255].0; let id_d256_1: u64 = f.d[256].0; let id_f_1: u64 = f.p0.0;
    f.slot(&mut b, &lay, 1);
    let ops1: Vec<Op> = b.ops[start..].to_vec();
    let marks1: Vec<(&str, usize)> = f.marks.iter().filter(|m| m.1 >= start).map(|m| (m.0, m.1 - start)).collect();
    let (aq, nb, _, _) = analyze_ops(ops1.iter());
    let nq2 = nq.max(aq as usize);
    let mut h = sha3::Shake256::default();
    h.update(b"froghop-test");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(nq2, (nb as usize).max(1), &mut xof);
    for i in 0..words1.len() { s.qubits[i] = words1[i]; }
    let mut hash = |q: &[u64], shot: usize| -> u64 {
        let mut hsh: u64 = 0x9E3779B97F4A7C15;
        let mut mix = |hsh: &mut u64, bit: u64| {
            *hsh = hsh.rotate_left(7) ^ (bit.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(*hsh));
        };
        for &wq in q.iter() { mix(&mut hsh, (wq >> shot) & 1); }
        hsh
    };
    let vtracked: Vec<QubitId> = f.v.iter().cloned().chain([f.par].iter().cloned()).collect();
    let qshot: usize = std::env::var("Q787_SHOT").ok().and_then(|x| x.parse().ok()).unwrap_or(1);
    let hhv = |qubits: &[u64]| -> u64 {
        let mut hsh: u64 = 0x9E3779B97F4A7C15;
        for &q in vtracked.iter() {
            let bit = (qubits[q.0 as usize] >> qshot) & 1;
            hsh = hsh.rotate_left(7) ^ (bit.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(hsh));
        }
        hsh
    };
    let ctracked: Vec<QubitId> = [f.p0, f.p1, f.p2].iter().cloned()
        .chain(f.pi.iter().cloned())
        .chain(f.dep.iter().cloned())
        .chain(f.bq.iter().cloned())
        .collect();
    let hhc = |qubits: &[u64], phase: u64| -> u64 {
        let mut hsh: u64 = 0x9E3779B97F4A7C15;
        for &q in ctracked.iter() {
            let bit = (qubits[q.0 as usize] >> qshot) & 1;
            hsh = hsh.rotate_left(7) ^ (bit.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(hsh));
        }
        hsh = hsh.rotate_left(7) ^ ((phase >> qshot) & 1).wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(hsh);
        hsh
    };
    let _ = &mut hash;
    eprintln!("T -1 V={:016x} C={:016x} (entry)", hhv(&s.qubits), hhc(&s.qubits, s.phase));
    if let Ok(_) = std::env::var("Q787_ODUMP") {
        let (aq0, nb0, _, _) = analyze_ops(ops0.iter());
        let mut h0 = sha3::Shake256::default();
        h0.update(b"froghop-test");
        let mut xof0 = h0.finalize_xof();
        let mut s0 = Simulator::new(nq.max(aq0 as usize), (nb0 as usize).max(1), &mut xof0);
        for i in 0..words0.len() { s0.qubits[i] = words0[i]; }
        eprintln!("ODUMP ids: s0start {} slot1start {} v255 {} v256 {} v257 {} d255 {} d256 {} f {} bq {:?}",
            s0start, start, id_v255_0, id_v256_0, id_v257_0, id_d255_0, id_d256_0, id_f_0, id_bq_0);
        for (i, op) in ops0.iter().enumerate() {
            s0.apply_iter(std::iter::once(op));
            eprintln!("ODUMP {i} {:?} c2 {} c1 {} t {} | v255 {} v256 {} v257 {} d255 {} d256 {} f {} dep3 {} p2 {}",
                op.kind, op.q_control2.0, op.q_control1.0, op.q_target.0,
                getb(&s0.qubits, QubitId(id_v255_0), qshot), getb(&s0.qubits, QubitId(id_v256_0), qshot), getb(&s0.qubits, QubitId(id_v257_0), qshot),
                getb(&s0.qubits, QubitId(id_d255_0), qshot), getb(&s0.qubits, QubitId(id_d256_0), qshot), getb(&s0.qubits, QubitId(id_f_0), qshot),
                getb(&s0.qubits, f.dep[2], qshot), getb(&s0.qubits, f.p2, qshot));
        }
    }
    for (i, op) in ops1.iter().enumerate() {
        s.apply_iter(std::iter::once(op));
        let ms = marks1.iter().find(|m| m.1 == i).map(|m| format!("  [{}]", m.0)).unwrap_or_default();
        eprintln!("T {i} V={:016x} C={:016x}  {:?} {:?} {:?} {:?}{}", hhv(&s.qubits), hhc(&s.qubits, s.phase), op.kind, op.q_control2.0, op.q_control1.0, op.q_target.0, ms);
        if let Ok(_) = std::env::var("Q787_ODUMP") {
            eprintln!("ODUMP1 {i} {:?} c2 {} c1 {} t {} | v255 {} v256 {} v257 {} d255 {} d256 {} f {} dep3 {} p2 {} p1 {}",
                op.kind, op.q_control2.0, op.q_control1.0, op.q_target.0,
                getb(&s.qubits, QubitId(id_v255_1), qshot), getb(&s.qubits, QubitId(id_v256_1), qshot), getb(&s.qubits, QubitId(id_v257_1), qshot),
                getb(&s.qubits, QubitId(id_d255_1), qshot), getb(&s.qubits, QubitId(id_d256_1), qshot), getb(&s.qubits, QubitId(id_f_1), qshot),
                getb(&s.qubits, f.dep[2], qshot), getb(&s.qubits, f.p2, qshot), getb(&s.qubits, f.p1, qshot));
        }
        if let Ok(di) = std::env::var("Q787_DUMP") {
            if i == di.parse().unwrap() {
                for k in 0..64 {
                    let code: Vec<u64> = [f.p0, f.p1, f.p2].iter().map(|&q| getb(&s.qubits, q, k)).collect();
                    let m0 = &models[k];
                    let mut m = m0.clone();
                    m.fwd(0);
                    eprintln!("DUMP shot {k}: code {:?} pi {:?} dep {:?} bq {:?} d255 {} d256 {} u {} v256 {} v0 {} v255 {} | slot1 {:?} pi {} b {} cd {} rvbl {} cvbl {} stk {} rv255 {} rv254 {} rv253 {}", code,
                        get(&s.qubits, &f.pi, k), get(&s.qubits, &f.dep, k), get(&s.qubits, &f.bq, k),
                        getb(&s.qubits, f.d[255], k), getb(&s.qubits, f.d[256], k), getb(&s.qubits, f.dirty[0], k), getb(&s.qubits, f.v[256], k), getb(&s.qubits, f.v[0], k), getb(&s.qubits, f.v[255], k),
                        m.ph, m.pi, m.b, m.cd, m.rv.bit_len(), m.cv.bit_len(), m.stk.len(), m.rv.bit(255), m.rv.bit(254), m.rv.bit(253));
                }
            }
        }
    }
}

/// ds-q787 debug: per-op state dump of slot 3, one shot (Q787_SHOT): the slot-3 physical ids (captured before
/// slot 3's rotation) of v255/v256/v257, d253/d254/d255/d256, f=p0, dep3, p2, p1, plus pi and bq registers.
#[test]
fn q787_trace_slot3() {
    if std::env::var_os("Q787_TRACE").is_none() { return; }
    let lay = lay_double();
    let w = WD;
    let wd = WD_D;
    let mut b = B::new();
    let d = b.alloc_n(wd);
    let v = b.alloc_n(w);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
    let mut rng = Rng::new(std::env::var("DSEED").ok().and_then(|s| s.parse().ok()).unwrap_or(4242));
    let pp = rmd::p();
    let mut models: Vec<rmd::St> = (0..64).map(|_| {
        let mut x = rng.below(256) % pp;
        if x == N::ZERO { x = N::from(1u64); }
        rmd::St::new(x)
    }).collect();
    let vl: Vec<QubitId> = f.v[1..257].to_vec();
    f.init(&mut b, &lay);
    let nq = b.width() as usize;
    let mods = models.clone();
    let dq = dirty.clone();
    let parinit: Vec<u8> = (0..64).map(|k| ((rng.next() >> (k % 7)) & 1) as u8).collect();
    let vtop = f.v[w - 1];
    let parv = f.parv;
    let pin = parinit.clone();
    let mut words0 = run(&b.ops, nq, &|wd| {
        for k in 0..64 { put(wd, &vl, k, &mods[k].rv); }
        if parv { for k in 0..64 { if pin[k] == 1 { wd[vtop.0 as usize] |= 1 << k; } } }
        for (i, &q) in dq.iter().enumerate() { wd[q.0 as usize] = 0x9E3779B97F4A7C15u64.wrapping_mul(i as u64 + 7) ^ 0x5bd1e995; }
    }).q;
    // per-slot build and per-slot state evolution (mimic the traversal exactly)
    let mut words3 = words0.clone();
    let mut s3start = 0usize;
    for sigma in 0..3 {
        let s0 = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        let ops: Vec<Op> = b.ops[s0..].to_vec();
        let wd = words3.clone();
        words3 = run(&ops, nq, &move |x| x.copy_from_slice(&wd)).q;
        s3start = b.ops.len();
    }
    // capture slot-3 physical ids before slot 3 runs (the S9 rotation reassigns self.v at the END of each slot)
    let id_v255_3: u64 = f.v[255].0; let id_v256_3: u64 = f.v[256].0; let id_v257_3: u64 = f.v[257].0;
    let id_d253_3: u64 = f.d[253].0; let id_d254_3: u64 = f.d[254].0; let id_d255_3: u64 = f.d[255].0; let id_d256_3: u64 = f.d[256].0;
    let id_f_3: u64 = f.p0.0;
    let id_z_3: u64 = f.dirty[f.dirty.len() - 1].0;
    let id_dirty3_3: u64 = f.dirty[3].0;
    let start = b.ops.len();
    f.slot(&mut b, &lay, 3);
    let ops3: Vec<Op> = b.ops[start..].to_vec();
    {
        let qshot3: usize = std::env::var("Q787_SHOT").ok().and_then(|x| x.parse().ok()).unwrap_or(2);
        eprintln!("S3DEBUG words0 len {} words3 len {} bq {} pi {} p2 {} p1 {} p0 {} | words0: bq {} pi {} p0 {} | d0 {} d256 {}", words0.len(), words3.len(),
            get(&words3, &f.bq, qshot3), get(&words3, &f.pi, qshot3), getb(&words3, f.p2, qshot3), getb(&words3, f.p1, qshot3), getb(&words3, f.p0, qshot3),
            get(&words0, &f.bq, qshot3), get(&words0, &f.pi, qshot3), getb(&words0, f.p0, qshot3),
            getb(&words0, f.d[0], qshot3), getb(&words0, f.d[256], qshot3));
    }
    let (aq, nb, _, _) = analyze_ops(ops3.iter());
    let nq2 = nq.max(aq as usize);
    let mut h = sha3::Shake256::default();
    h.update(b"froghop-test");
    let mut xof = h.finalize_xof();
    let mut s = Simulator::new(nq2, (nb as usize).max(1), &mut xof);
    for i in 0..words3.len() { s.qubits[i] = words3[i]; }
    let qshot: usize = std::env::var("Q787_SHOT").ok().and_then(|x| x.parse().ok()).unwrap_or(2);
    {
        let mut m = models[qshot].clone();
        for sgm in 0..3 { m.fwd(sgm); }
        eprintln!("S3MODEL shot {qshot}: pre {:?} pi {} b {} cdbl {} rvbl {} cvbl {} stk {:?}", m.ph, m.pi, m.b, m.cd.bit_len(), m.rv.bit_len(), m.cv.bit_len(), m.stk);
        m.fwd(3);
        eprintln!("S3MODEL shot {qshot}: post {:?} pi {} b {} cdbl {} rvbl {} cvbl {} stk {:?}", m.ph, m.pi, m.b, m.cd.bit_len(), m.rv.bit_len(), m.cv.bit_len(), m.stk);
    }
    eprintln!("ODUMP3 ids: v255 {} v256 {} v257 {} d253 {} d254 {} d255 {} d256 {} f {} dep3 {} p2 {} p1 {} pi {:?} bq {:?} z {}",
        id_v255_3, id_v256_3, id_v257_3, id_d253_3, id_d254_3, id_d255_3, id_d256_3, id_f_3,
        f.dep[2].0, f.p2.0, f.p1.0, f.pi.iter().map(|q| q.0).collect::<Vec<_>>(), f.bq.iter().map(|q| q.0).collect::<Vec<_>>(), id_z_3);
    for (i, op) in ops3.iter().enumerate() {
        s.apply_iter(std::iter::once(op));
        if let Ok(_) = std::env::var("Q787_ODUMP") {
            eprintln!("ODUMP3 {i} {:?} c2 {} c1 {} t {} | v255 {} v256 {} v257 {} d253 {} d254 {} d255 {} d256 {} f {} dep3 {} p2 {} p1 {} pi {} bq {} z {} dq3 {}",
                op.kind, op.q_control2.0, op.q_control1.0, op.q_target.0,
                getb(&s.qubits, QubitId(id_v255_3), qshot), getb(&s.qubits, QubitId(id_v256_3), qshot), getb(&s.qubits, QubitId(id_v257_3), qshot),
                getb(&s.qubits, QubitId(id_d253_3), qshot), getb(&s.qubits, QubitId(id_d254_3), qshot), getb(&s.qubits, QubitId(id_d255_3), qshot), getb(&s.qubits, QubitId(id_d256_3), qshot),
                getb(&s.qubits, QubitId(id_f_3), qshot),
                getb(&s.qubits, f.dep[2], qshot), getb(&s.qubits, f.p2, qshot), getb(&s.qubits, f.p1, qshot),
                get(&s.qubits, &f.pi, qshot), get(&s.qubits, &f.bq, qshot),
                getb(&s.qubits, QubitId(id_z_3), qshot), getb(&s.qubits, QubitId(id_dirty3_3), qshot));
        }
    }
}

/// c787 census: model-resynced per slot (every register written from the model at slot start), then the slot's
/// ops run up to each mark; for the just-converted CO shots (prev Dv pi 0 -> Co) record D[b], D[b-1] and
/// (k >= 2) D[b+k-1] at every mark. Run with C787_CENSUS=1 --nocapture.
#[test]
fn c787_census() {
    if std::env::var_os("C787_CENSUS").is_none() { return; }
    let lay = lay_double();
    let w = WD;
    let wd = WD_D;
    let mut b = B::new();
    let d = b.alloc_n(wd);
    let v = b.alloc_n(w);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
    let mut rng = Rng::new(std::env::var("DSEED").ok().and_then(|s| s.parse().ok()).unwrap_or(4242));
    let pp = rmd::p();
    let mut models: Vec<rmd::St> = (0..64).map(|_| {
        let mut x = rng.below(256) % pp;
        if x == N::ZERO { x = N::from(1u64); }
        rmd::St::new(x)
    }).collect();
    let skip: Vec<bool> = models.iter().map(|m| super::tests_789::max_q_bits(&(if m.refl == 1 { pp - m.rv } else { m.rv })) >= super::froghop_double::QBAD).collect();
    let vl: Vec<QubitId> = f.v[1..257].to_vec();
    f.init(&mut b, &lay);
    let nq = b.width() as usize;
    let mods = models.clone();
    let dq = dirty.clone();
    let parinit: Vec<u8> = (0..64).map(|k| ((rng.next() >> (k % 7)) & 1) as u8).collect();
    let vtop = f.v[w - 1];
    let parv = f.parv;
    let pin = parinit.clone();
    let words = run(&b.ops, nq, &|wd| {
        for k in 0..64 { put(wd, &vl, k, &mods[k].rv); }
        if parv { for k in 0..64 { if pin[k] == 1 { wd[vtop.0 as usize] |= 1 << k; } } }
        for (i, &q) in dq.iter().enumerate() { wd[q.0 as usize] = 0x9E3779B97F4A7C15u64.wrapping_mul(i as u64 + 7) ^ 0x5bd1e995; }
    }).q;
    let dirty0: Vec<u64> = dirty.iter().map(|q| words[q.0 as usize]).collect();
    let setb = |wds: &mut Vec<u64>, q: QubitId, k: usize, x: u8| { if x == 1 { wds[q.0 as usize] |= 1 << k } else { wds[q.0 as usize] &= !(1u64 << k) } };
    use std::collections::BTreeMap;
    // (mark, cls) -> [n, d[b]=1, d[b-1]=1, both, d[b]==model]
    let mut tab: BTreeMap<(String, String), [u64; 5]> = BTreeMap::new();
    let mut nslots = 0;
    for sigma in 0..lay.s {
        // resync every register from the model
        let mut wds = words.clone();
        for k in 0..64 {
            let m = &models[k];
            let (mut ed, mut ev) = expect_lanes(m);
            if parv { let (ind, l) = par_lane(m); let pb = par_bit(m, parinit[k]); if ind { ed[l] ^= pb } else { ev[l] ^= pb } }
            for j in 0..wd { setb(&mut wds, f.d[j], k, ed[j]); }
            for j in 0..w { setb(&mut wds, f.v[j], k, ev[j]); }
            let (epi, edep) = super::froghop_double::l19_encode((m.pi >> 1) as u64, m.stk.len() as u64);
            put(&mut wds, &f.pi.clone(), k, &N::from(epi));
            put(&mut wds, &f.dep.clone(), k, &N::from(edep));
            put(&mut wds, &f.bq.clone(), k, &N::from(((m.b as i64 - 1 - lay.base[sigma] as i64).rem_euclid(1 << BB)) as u64));
            let want = match m.ph { Ph::Al => [1, 0, 0], Ph::Dv => [0, 1, 0], Ph::Co => [1, 1, 0], Ph::Rt => [0, 0, 0], Ph::Dn => [0, 0, 1] };
            for (q, x) in [f.p0, f.p1, f.p2].iter().zip(want.iter()) { setb(&mut wds, *q, k, *x as u8); }
        }
        for (i, q) in dirty.iter().enumerate() { wds[q.0 as usize] = dirty0[i]; }
        let prev = models.clone();
        for m in models.iter_mut() { m.fwd(sigma); }
        let start = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        let ops = b.ops[start..].to_vec();
        let tgt: Vec<usize> = (0..64).filter(|&k| !skip[k] && prev[k].ph == Ph::Dv && prev[k].pi == 0 && models[k].ph == Ph::Co).collect();
        if tgt.is_empty() { continue; }
        nslots += 1;
        let marks: Vec<(&str, usize)> = f.marks.iter().filter(|m| m.1 >= start).map(|m| (m.0, m.1 - start)).chain([("end", ops.len())]).collect();
        for (mi, &(nm, mk)) in marks.iter().enumerate() {
            let w0 = wds.clone();
            let rr = run(&ops[..mk], nq, &move |x| x.copy_from_slice(&w0));
            if nm == "M2" {
                let mut disc: Vec<u8> = vec![3; rr.q.len()];
                let mut cls = [0u32; 2];
                for &k in tgt.iter() {
                    let m = &models[k];
                    let kk = m.pi as i64 + m.stk.len() as i64 - 1;
                    if kk > 1 { continue; }
                    let g1 = m.r.bit(m.b as usize - 1) as u64;
                    cls[g1 as usize] += 1;
                    let vb = getb(&rr.q, f.v[m.b as usize], k); let vb1 = getb(&rr.q, f.v[m.b as usize + 1], k); let vbm = getb(&rr.q, f.v[m.b as usize - 1], k);
                    let _ = (vb, vb1, vbm);
                    let (_, evp) = expect_lanes(&prev[k]);
                    let (_, evn) = expect_lanes(m);
                    let bb = m.b as usize;
                    let ph: String = (bb - 3..bb + 4).map(|j| format!("{}", getb(&rr.q, f.v[j % 258], k))).collect();
                    let ep: String = (bb - 3..bb + 4).map(|j| format!("{}", evp[j % 258])).collect();
                    let en: String = (bb - 3..bb + 4).map(|j| format!("{}", evn[(j + 1) % 258])).collect();
                    eprintln!("C787 VLANE slot {sigma} k {kk} g1 {g1} b {bb} par {} | V[b-3..b+3] now {ph} prev-model {ep} post-model(shifted -1) {en}", par_bit(&prev[k], parinit[k]));
                    for q in 0..rr.q.len().min(disc.len()) {
                        let x = (rr.q[q] >> k) & 1;
                        if x != g1 { disc[q] &= !1; }
                        if x == g1 { disc[q] &= !2; }
                    }
                }
                if cls[0] > 0 && cls[1] > 0 {
                    let dl: Vec<String> = (0..nq).filter(|&q| disc[q] != 0).map(|q| {
                        let nmq = if let Some(j) = f.d.iter().position(|x| x.0 as usize == q) { format!("D{j}") } else if let Some(j) = f.v.iter().position(|x| x.0 as usize == q) { format!("V{j}") } else { format!("q{q}") };
                        format!("{nmq}:{}", disc[q]) }).collect();
                    eprintln!("C787 DISC slot {sigma} G1 {} else {} -> {:?}", cls[1], cls[0], dl);
                }
            }
            for &k in tgt.iter() {
                let m = &models[k];
                let kk = m.pi as i64 + m.stk.len() as i64 - 1;
                let bb = m.b as usize;
                let (ed, _) = expect_lanes(m);
                let cls = if kk <= 1 { if m.r.bit(bb - 1) { "k<=1 G1" } else { "k<=1 else" } } else { "k>=2" };
                let (x1, x0) = if kk <= 1 { (getb(&rr.q, f.d[bb], k), getb(&rr.q, f.d[bb - 1], k)) } else { (getb(&rr.q, f.d[(bb as i64 + kk - 1) as usize], k), 0) };
                let e = tab.entry((format!("{:02} {}", mi, nm), cls.to_string())).or_insert([0; 5]);
                e[0] += 1; e[1] += x1; e[2] += x0; e[3] += x1 & x0; e[4] += (x1 as u8 == ed[bb.min(wd - 1)]) as u64;
            }
        }
    }
    eprintln!("C787 slots with conversions: {nslots}");
    // discriminator search: per (slot-relative) M2 state, which physical qubit equals G1 (or !G1) on every k<=1 target
    for ((nm, cls), e) in tab.iter() {
        eprintln!("C787 mark {:>12} {:>10}: n {:5} d[b]=1 {:5} d[b-1]=1 {:5} both {:5} d[b]==model {:5}", nm, cls, e[0], e[1], e[2], e[3], e[4]);
    }
}

/// c787: model-only count of on-model AL / DV slot-start states whose 257-lane D holds a cd bit inside the S2 P1
/// window [pi, b + [DV] pi] (lanes <= 255; lane 256 is the ds-tree's aliased top cell). Parent layout for comparison.
#[test]
fn c787_p1_collide() {
    if std::env::var_os("C787_CENSUS").is_none() { return; }
    let lay = lay_double();
    let mut rng = Rng::new(std::env::var("DSEED").ok().and_then(|s| s.parse().ok()).unwrap_or(4242));
    let pp = rmd::p();
    let nsh: usize = std::env::var("C787_NSH").ok().and_then(|s| s.parse().ok()).unwrap_or(64);
    let mut models: Vec<rmd::St> = (0..nsh).map(|_| {
        let mut x = rng.below(256) % pp;
        if x == N::ZERO { x = N::from(1u64); }
        rmd::St::new(x)
    }).collect();
    let skip: Vec<bool> = models.iter().map(|m| super::tests_789::max_q_bits(&(if m.refl == 1 { pp - m.rv } else { m.rv })) >= super::froghop_double::QBAD).collect();
    let (mut tot, mut cand, mut par, mut cand_b, mut shots_hit) = ([0u64; 2], [0u64; 2], [0u64; 2], [0u64; 2], vec![false; nsh]);
    let (mut ovl, mut dvtop) = ([0u64; 2], [0u64; 2]);
    let mut c1 = [0u64; 2];
    let mut turn = [0u64; 4];
    let mut dlc = [0u64; 3];
    let mut park = [0u64; 9];
    let mut park2 = [0u64; 5];
    let mut s3e = [0u64; 3];
    let mut mk = [[0u64; 9]; 2];
    let mut hist: std::collections::BTreeMap<(u8, u8, u8, u8), u64> = Default::default();
    for sigma in 0..lay.s {
        for (k, m) in models.iter().enumerate() {
            if skip[k] { continue; }
            let ix = match m.ph { Ph::Al => 0, Ph::Dv => 1, _ => continue };
            let b = m.b as usize;
            if b >= 256 { continue; }
            let pi = m.pi.max(0) as usize;
            let hi = (b + if ix == 1 { pi } else { 0 }).min(255);
            tot[ix] += 1;
            let c = (pi..=hi).any(|j| j <= 256 && m.cd.bit(256 - j));
            let p = (pi..=hi).any(|j| j <= 257 && m.cd.bit(257 - j));
            if c { cand[ix] += 1; shots_hit[k] = true; }
            if p { par[ix] += 1; }
            if m.cd.bit(256 - b) { cand_b[ix] += 1; }
            // overlap: a lane holding both an r bit and a cd bit in the 257 layout (unrepresentable), and the DV top lane
            if (0..257).any(|j| m.r.bit(j) && m.cd.bit(256 - j)) { ovl[ix] += 1; }
            if ix == 1 { let jt = b + pi; if jt <= 256 && m.cd.bit(256 - jt) { if m.r.bit(jt) { dvtop[1] += 1 } else { dvtop[0] += 1 } } }
            if ix == 1 && m.stk.is_empty() { let x = m.rv.clone() << pi; if m.r >= x { c1[1] += 1 } else { c1[0] += 1 } }
            if ix == 1 { let jt = b + pi; if jt <= 256 { let key = (m.cd.bit(256 - jt) as u8, m.r.bit(jt) as u8, m.stk.len().min(3) as u8, (m.pi as usize).min(3) as u8); *hist.entry(key).or_insert(0u64) += 1; } }
        }
        for (k, m) in models.iter_mut().enumerate() {
            let pre = m.clone();
            m.fwd(sigma);
            if skip[k] { continue; }
            if pre.ph == Ph::Co && pre.pi == 1 && pre.stk.len() <= 1 && m.ph == Ph::Rt {
                // marker slot of a k <= 1 shot: occupancy of candidate lanes (model, no parity)
                let kk = pre.stk.len();
                let bb = pre.b as usize;
                let dbit = |j: usize| -> bool { (j < 300 && pre.r.bit(j)) || (j <= 256 && pre.cd.bit(256 - j)) };
                let vfr = |u: usize| -> bool { pre.rv.bit(u) || pre.cv.bit(257 - u) || (u > bb && u - bb < pre.stk.len()) };
                let lanes: Vec<bool> = vec![dbit(bb - 2), dbit(bb - 1), dbit(bb), dbit(bb + 1), vfr(bb - 1), vfr(bb), vfr(bb + 1), vfr(bb + 2)];
                for (i, &x) in lanes.iter().enumerate() { if x { mk[kk][i] += 1; } }
                mk[kk][8] += 1;
            }
            if pre.ph == Ph::Dv && pre.stk.is_empty() {
                // first DV step: carry of (r' + X1) out of lanes [pi, b+pi-1] vs dl (b_A = BL(r) = b + pi + dl)
                let pi1 = pre.pi as usize; let bq1 = pre.b as usize;
                let dl = (pre.r.bit_len() as usize) - (bq1 + pi1);
                let x1 = pre.rv.clone() << pi1;
                let r1 = m.r.clone();
                let n = bq1 + pi1;
                let mask = (N::from(1u64) << n) - N::from(1u64);
                let sum = (r1.clone() & mask.clone()) + (x1 & mask.clone());
                let carry = sum.bit(n) as usize;
                let cdwin = (pi1..n).any(|j| j <= 256 && pre.cd.bit(256 - j));
                dlc[(dl == carry) as usize] += 1; if cdwin { dlc[2] += 1; }
            }
            if pre.ph == Ph::Al && m.ph == Ph::Dv {
                // turn: b_A = pre.b = BL(r); dl = 1 iff b' = b_A - pi_A + 1 - 1
                let ba = pre.b as usize;
                let dl = (pre.b as i64 - pre.pi as i64 + 1 - m.b as i64) as usize;
                let full = ba <= 256 && pre.cd.bit(256 - ba);
                turn[dl.min(1) * 2 + full as usize] += 1;
                {
                    // S3 in-place erase identity: dl == [rv << (pi_A - 1) > r mod 2^(b' + pi_A - 1)]
                    let n = m.b as usize + pre.pi as usize - 1;
                    let x1 = pre.rv.clone() << (pre.pi as usize - 1);
                    let mask = (N::from(1u64) << n) - N::from(1u64);
                    let rl = pre.r.clone() & mask;
                    let ok = ((x1 > rl) as usize) == dl;
                    let cdw = (0..n).any(|j| j <= 256 && pre.cd.bit(256 - j));
                    s3e[ok as usize] += 1; if cdw { s3e[2] += 1; }
                }
                // park-lane census on the post-turn model (V-frame u = rv bit u | cv bit 257-u | stk bits at b+j)
                let k = pre.pi as i64 - 1;
                let bb = m.b as usize;
                let vfr = |u: usize| -> bool { m.rv.bit(u) || m.cv.bit(257 - u) || (u > bb && u - bb < m.stk.len()) };
                let u1 = bb + 1; let u2 = bb + 2;
                let pl = (bb as i64 + k.max(1)) as usize;
                park[(k >= 2) as usize * 4 + (vfr(u1) as usize) * 2 + vfr(u2) as usize] += 1;
                if (k >= 2 && u1 == pl) || (k < 2 && u2 == pl) { park[8] += 1; }
                if k < 2 { for (i, du) in [0i64, 2, 3, 4].iter().enumerate() { let u = (bb as i64 + du) as usize; if u < 258 && vfr(u) { park2[i] += 1; } } park2[4] += 1; }
            }
        }
    }
    eprintln!("C787P1 dl-erase check (first DV step): carry==dl {} / != {} | cd bit inside [pi, b+pi-1]: {}", dlc[1], dlc[0], dlc[2]);
    eprintln!("C787P1 park census [k<=1: (vb+1,vb+2) 00 01 10 11 | k>=2: 00 01 10 11 | park==parity lane]: {:?}", park);
    eprintln!("C787P1 k<=1 turns: occupied V-frame b' {} b'+2 {} b'+3 {} b'+4 {} of {}", park2[0], park2[1], park2[2], park2[3], park2[4]);
    eprintln!("C787P1 S3 in-place erase identity: ok {} bad {} | cd bit in [0, n): {}", s3e[1], s3e[0], s3e[2]);
    for kk in 0..2 { eprintln!("C787P1 marker-slot k={kk} occupied [D b-2, D b-1, D b, D b+1, V b-1, V b, V b+1, V b+2] of n: {:?}", mk[kk]); }
    eprintln!("C787P1 turns: dl0 notfull {} dl0 FULL {} dl1 notfull {} dl1 FULL {}", turn[0], turn[1], turn[2], turn[3]);
    eprintln!("C787P1 shots {nsh} states AL {} DV {} | cd bit in window: cand AL {} DV {} | parent AL {} DV {} | cand lane b only AL {} DV {} | shots ever hit {}",
        tot[0], tot[1], cand[0], cand[1], par[0], par[1], cand_b[0], cand_b[1], shots_hit.iter().filter(|&&x| x).count());
    eprintln!("C787P1 r&cd same-lane overlap states AL {} DV {} | DV top lane b+pi holds cd bit: r bit 0 there {} / r bit 1 there {}", ovl[0], ovl[1], dvtop[0], dvtop[1]);
    eprintln!("C787P1 DV dep-0 states: c=[r >= rv<<pi] = 1: {} / c = 0: {}", c1[1], c1[0]);
    for (k, v) in hist.iter() { eprintln!("C787P1 DVTOP cdbit {} rbit {} dep(min3) {} pi(min3) {}: {}", k.0, k.1, k.2, k.3, v); }
}
