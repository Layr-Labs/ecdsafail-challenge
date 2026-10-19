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

use super::froghop_double::{BB, FhDouble, LayDouble, WD};
use super::refmodel_double::{self as rmd, Ph};

pub fn lay_double() -> LayDouble {
    LayDouble::from_text(include_str!("sched_double.txt"), 24)
}

fn expect_lanes(m: &rmd::St) -> (Vec<u8>, Vec<u8>) {
    let w = WD;
    let mut d = vec![0u8; w];
    let mut v = vec![0u8; w];
    for j in 0..w {
        if j < 300 && m.r.bit(j) { d[j] |= 1; }
        if m.cd.bit(w - 1 - j) { d[j] |= 1; }
    }
    if m.ph == rmd::Ph::Dn {
        // DONE counter XORed into D lanes W-256.. (p's top bits)
        for j in 0..8 { d[w - 256 + j] ^= ((m.cnt >> j) & 1) as u8; }
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

#[test]
fn double_traversal_matches_model() {
    let lay = lay_double();
    let w = WD;
    let mut b = B::new();
    let d = b.alloc_n(w);
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
    let mut words = run(&b.ops, nq, &|wd| {
        for k in 0..64 { put(wd, &vl, k, &mods[k].rv); }
        for (i, &q) in dq.iter().enumerate() { wd[q.0 as usize] = 0x9E3779B97F4A7C15u64.wrapping_mul(i as u64 + 7) ^ 0x5bd1e995; }
    }).q;
    let dirty0: Vec<u64> = dirty.iter().map(|q| words[q.0 as usize]).collect();
    let mut tof = 0u64;
    let pool = f.pool.clone();
    let mut prev: Vec<rmd::St> = models.clone();
    for sigma in 0..lay.s {
        for k in 0..64 {
            let m = &models[k];
            {
                let (ed, _) = expect_lanes(m);
                let bad: Vec<usize> = (0..w).filter(|&j| getb(&words, f.d[j], k) as u8 != ed[j]).collect();
                if !bad.is_empty() {
                    let p = &prev[k];
                    eprintln!("slot {sigma} shot {k}: D mismatch lanes {:?}; prev {:?} pi {} stk {:?} b {} R {} rv {} cd {} cv {}; now {:?} pi {} R {}",
                        &bad[..bad.len().min(8)], p.ph, p.pi, p.stk, p.b, p.r.bit_len(), p.rv.bit_len(), p.cd.bit_len(), p.cv.bit_len(),
                        m.ph, m.pi, m.r);
                    eprintln!("   row prev {:?}", lay.rows[sigma.saturating_sub(1)]);
                }
            }
            let (ed, ev) = expect_lanes(m);
            for j in 0..w {
                assert_eq!(getb(&words, f.d[j], k) as u8, ed[j], "slot {sigma} shot {k} D lane {j} ph {:?}", m.ph);
                assert_eq!(getb(&words, f.v[j], k) as u8, ev[j], "slot {sigma} shot {k} V lane {j} ph {:?} pi {}", m.ph, m.pi);
            }
            assert_eq!(get(&words, &f.pi, k), N::from(m.pi as u64), "slot {sigma} shot {k} pi");
            let code = [f.p0, f.p1, f.p2].iter().map(|&q| getb(&words, q, k)).collect::<Vec<_>>();
            let want = match m.ph { Ph::Al => [1, 0, 0], Ph::Dv => [0, 1, 0], Ph::Co => [1, 1, 0], Ph::Rt => [0, 0, 0], Ph::Dn => [0, 0, 1] };
            assert_eq!(code, want.to_vec(), "slot {sigma} shot {k} phase {:?}", m.ph);
            assert_eq!(get(&words, &f.bq, k), N::from(((m.b as i64 - 1 - lay.base[sigma] as i64).rem_euclid(1 << BB)) as u64), "slot {sigma} shot {k} b");
            assert_eq!(get(&words, &f.dep, k), N::from(m.stk.len() as u64), "slot {sigma} shot {k} dep");
            assert_eq!(getb(&words, f.par, k) as u8, m.par, "par");
        }
        let start = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        let ops = b.ops[start..].to_vec();
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
        assert_eq!(r.phase, 0, "phase after slot {sigma}");
        tof += r.tof;
        words = r.q;
        for (i, q) in dirty.iter().enumerate() { assert_eq!(words[q.0 as usize], dirty0[i], "dirty qubit {i} not restored after slot {sigma}"); }
        for &q in &pool {
            if words[q.0 as usize] != 0 {
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
    for m in &models { assert!(m.ph == Ph::Dn); let _ = m.result(); }
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
        assert_eq!(r.phase, 0, "phase");
        for q in 0..nq {
            if vl.iter().any(|x| x.0 as usize == q) { continue; }
            assert_eq!(r.q[q], 0, "qubit {q} not restored (seed {seed})");
        }
        for k in 0..64 { assert_eq!(get(&r.q, &vl, k), ms[k].rv); }
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
    let d = b.alloc_n(WD);
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
    for &(lo, k) in &[(0usize, C), (4usize, C - 1)] {
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
