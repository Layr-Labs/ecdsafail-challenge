//! froghop-one tests: integer model, envelope generator (FH1_GEN), and later the gate-level slot.

use super::refmodel_one::{self as rm, bl, Ph, St, N};

struct Rng(u64);
impl Rng {
    fn new(s: u64) -> Rng {
        Rng(s ^ 0x9E3779B97F4A7C15)
    }
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below_p(&mut self) -> N {
        let pp = rm::p();
        loop {
            let mut v = N::ZERO;
            for i in 0..4 {
                v |= N::from(self.next()) << (64 * i);
            }
            if v < pp && v != N::ZERO {
                return v;
            }
        }
    }
}

#[test]
fn one_model_result() {
    let pp = rm::p();
    let mut rng = Rng::new(7);
    let mut maxs = 0;
    for _ in 0..300 {
        let x = rng.below_p();
        let mut st = St::new(x);
        let mut s = 0;
        while st.ph != Ph::Dn {
            st.fwd_at(s);
            s += 1;
            assert!(s < 2000);
        }
        maxs = maxs.max(s);
        let inv = st.result();
        assert_eq!(inv.mul_mod(x, pp), N::from(1u64), "inverse");
    }
    eprintln!("one model OK, max slots {maxs}");
}

/// Per-slot envelopes for the window schedule. FH1_GEN=<shots> FH1_SEED=<seed> FH1_OUT=<file>.
/// Columns per slot: running, B1 min, B1 max, pi max, align b0 min/max, align (b + pi - 1 after) min/max,
/// step-end b min/max, first-step-end b min/max.
#[test]
fn one_envelope() {
    let Ok(n) = std::env::var("FH1_GEN") else { return };
    let n: usize = n.parse().unwrap();
    let seed: u64 = std::env::var("FH1_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
    let out = std::env::var("FH1_OUT").unwrap_or("fh1_env.txt".into());
    const S: usize = 1000;
    let big = u32::MAX;
    let mut run = vec![0u64; S];
    let mut b1 = vec![(big, 0u32); S];
    let mut pim = vec![0u32; S];
    let mut al0 = vec![(big, 0u32); S];
    let mut al1 = vec![(big, 0u32); S];
    let mut se = vec![(big, 0u32); S];
    let mut fse = vec![(big, 0u32); S];
    let mut lens = vec![0u32; S + 2];
    let mut maxk = 0;
    let mut maxdep = 0;
    let mut rng = Rng::new(seed);
    let mm = |a: &mut (u32, u32), v: u32| {
        a.0 = a.0.min(v);
        a.1 = a.1.max(v);
    };
    for _ in 0..n {
        let x = rng.below_p();
        let mut st = St::new(x);
        let mut fin = S + 1;
        for s in 0..S {
            if st.ph == Ph::Dn {
                fin = s;
                break;
            }
            run[s] += 1;
            mm(&mut b1[s], st.b1());
            pim[s] = pim[s].max(st.pi);
            maxdep = maxdep.max(st.stk.len());
            let ev = st.fwd_at(s);
            maxk = maxk.max(st.k);
            if let Some((b0, bv, pi)) = ev.align {
                mm(&mut al0[s], b0);
                mm(&mut al1[s], bv + pi - 1);
            }
            if let Some(b) = ev.step_end {
                mm(&mut se[s], b);
                if ev.first_step_end {
                    mm(&mut fse[s], b);
                }
            }
        }
        lens[fin.min(S + 1)] += 1;
    }
    let mut txt = String::new();
    for s in 0..S {
        let z = |a: (u32, u32)| if a.0 == big { (0, 0) } else { a };
        let (b1s, al0s, al1s, ses, fses) = (z(b1[s]), z(al0[s]), z(al1[s]), z(se[s]), z(fse[s]));
        txt += &format!("{} {} {} {} {} {} {} {} {} {} {} {} {}
", s, run[s], b1s.0, b1s.1, pim[s], al0s.0, al0s.1,
                        al1s.0, al1s.1, ses.0, ses.1, fses.0, fses.1);
    }
    std::fs::write(&out, txt).unwrap();
    let mut acc = 0u64;
    let mut last = 0;
    for (s, &c) in lens.iter().enumerate() {
        if c > 0 {
            last = s;
        }
        acc += c as u64;
    }
    let _ = acc;
    eprintln!("envelope: {n} shots, last finishing slot {last}, max k {maxk}, max stack {maxdep}; written {out}");
    let _ = bl;
}

/// Window schedule for froghop-one from the integer model. FH1_SCHED=<out file> FH1_N=<shots> FH1_SEED=<seed>
/// FH1_M=<lane margin> FH1_T=<slot shift> FH1_BM=<offset-register margin>. Columns: lv jw p1lo lc p2hi pb0 pb1 pe0 pe1
/// fin 0 termon base q0 q1 u0 u1; header "W S f1w".
/// Layout: b is the dividend's length through OUT and converts at the turn; quotient bits sit in V's gap during DIV
/// (V frame lanes b + 1 .. b + d) and in D's gap during OUT (lanes b + 1 .. b + d).
#[test]
fn one_schedule() {
    let Ok(out) = std::env::var("FH1_SCHED") else { return };
    let n: usize = std::env::var("FH1_N").ok().and_then(|v| v.parse().ok()).unwrap_or(1_000_000);
    let seed: u64 = std::env::var("FH1_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(2026);
    let m: i64 = std::env::var("FH1_M").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    let tsh: usize = std::env::var("FH1_T").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    let w = super::froghop_one::W1 as i64;
    const S: usize = 1000;
    let big = i64::MAX;
    let mut b1p = vec![(big, -1i64); S]; // P1 boundary B1 (shots whose P1 result is used)
    let mut b1m = vec![(big, -1i64); S]; // P2/P3 boundary B1 + d (shots whose P2/P3 result is used)
    let mut pim = vec![0i64; S];
    let mut vpr = vec![(big, -1i64); S]; // turn: V probe lane (phys)
    let mut dpr = vec![(big, -1i64); S]; // turn: D probe lane
    let mut pop = vec![(big, -1i64); S];
    let mut push = vec![(big, -1i64); S];
    let mut term = vec![false; S];
    let mut fin = vec![false; S];
    let mut last = 0usize;
    let mut f1last = 0usize;
    let mut maxdep = 0usize;
    let mut rng = Rng::new(seed);
    let mm = |a: &mut (i64, i64), v: i64| {
        a.0 = a.0.min(v);
        a.1 = a.1.max(v);
    };
    for _ in 0..n {
        let x = rng.below_p();
        let mut st = St::new(x);
        for s in 0..S {
            if st.ph == Ph::Dn {
                break;
            }
            let s0 = st.clone();
            let pi0 = s0.pi as i64;
            pim[s] = pim[s].max(pi0);
            if s0.ph == Ph::Out && s0.k == 0 && s0.b == 1 {
                fin[s] = true;
            }
            let blr0 = bl(&s0.r) as i64;
            let d0 = s0.stk.len() as i64;
            let nb0 = if s0.ph == Ph::Out { blr0 } else { s0.b as i64 };
            let al0 = s0.k != 0 || s0.b == 1;
            if !(s0.ph == Ph::Out && s0.k != 0) {
                mm(&mut b1p[s], nb0 + if al0 { pi0 } else { 0 });
            }
            if s0.ph == Ph::Out && d0 > 0 {
                mm(&mut pop[s], blr0 + d0);
            }
            let ev = st.fwd_at(s);
            let s1 = &st;
            maxdep = maxdep.max(s1.stk.len());
            let (rel, mv) = match (s0.ph, s1.ph) {
                (Ph::Out, Ph::Out) => {
                    let al1 = s1.k != 0 || s1.b == 1;
                    (true, blr0 + s1.stk.len() as i64 + if al1 { pi0 } else { 0 })
                }
                (Ph::Out, Ph::Ret) => (true, s1.b as i64 + pi0),
                (Ph::Out, Ph::Dn) => (true, 1 + pi0),
                (Ph::Ret, _) | (Ph::Div, _) => {
                    if ev.step_end.is_some() {
                        (true, s1.b as i64 + s1.stk.len() as i64)
                    } else {
                        (s0.ph == Ph::Ret, s0.b as i64 + pi0)
                    }
                }
                _ => (false, 0),
            };
            if rel {
                mm(&mut b1m[s], mv);
            }
            if s1.ph == Ph::Div && ev.step_end.is_none() {
                let d1 = s1.stk.len() as i64;
                if s0.ph == Ph::Div || d1 > d0 {
                    mm(&mut push[s], s1.b as i64 + d1 + pi0);
                }
            }
            if s0.ph == Ph::Out && s1.ph == Ph::Ret {
                let k = s1.k as i64;
                mm(&mut vpr[s], blr0 - k + pi0);
                mm(&mut dpr[s], s1.b as i64 + k - 1);
            }
            if st.ph == Ph::Dn && st.cnt == 0 {
                term[s] = true;
            }
            if ev.first_step_end {
                f1last = f1last.max(s);
            }
            last = last.max(s);
        }
    }
    let s_slots = last + 1 + 10;
    let f1w = f1last + 1 + 10;
    let env = |v: &Vec<(i64, i64)>, s: usize| -> (i64, i64) {
        let lo = s.saturating_sub(tsh);
        let hi = (s + tsh).min(S - 1);
        let mut r = (big, -1i64);
        for t in lo..=hi {
            if v[t].1 >= 0 {
                r.0 = r.0.min(v[t].0);
                r.1 = r.1.max(v[t].1);
            }
        }
        r
    };
    let mut txt = format!("{} {} {}\n", w, s_slots, f1w);
    // offset-register base: every value the slot decodes must lie in [base, base + 2^BB - 1] (margin where possible);
    // 193 in the first-step slots (values up to 256 there), 0 where [b == 1] is tested
    let bb = super::froghop_one::BB as i64;
    let top = (1i64 << bb) - 1;
    let mg: i64 = std::env::var("FH1_BM").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    let mut base_prev = 193i64;
    let mut bases = vec![0i64; s_slots];
    let mut worst_slack = i64::MAX;
    for s in 0..s_slots {
        let mut lo = big;
        let mut hi = -1i64;
        // decoded values (bq units): B1 - 1, B1 + d - 1, V probe lane - 1, D probe lane, pop lane - 1, push lane - 1
        for (v, sh) in [(&b1p, -1i64), (&b1m, -1), (&vpr, -1), (&dpr, 0), (&pop, -1), (&push, -1)] {
            let (a, z) = env(v, s);
            if z >= 0 {
                lo = lo.min(a + sh);
                hi = hi.max(z + sh);
            }
        }
        let fi = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).any(|t| fin[t]);
        let tm = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).any(|t| term[t]);
        let base = if s < f1w {
            193
        } else if fi || tm || hi < 0 {
            0
        } else if base_prev <= lo - mg && base_prev + top >= hi + mg {
            base_prev
        } else {
            let mut m2 = mg;
            while m2 > 0 && (hi + m2 - top).max(0) > lo - m2 {
                m2 -= 1;
            }
            let lb = (hi + m2 - top).max(0);
            let ub = lo - m2;
            assert!(lb <= ub, "slot {s}: values [{lo}, {hi}] do not fit {bb} bits");
            (lb + ub) / 2
        };
        if hi >= 0 {
            let up = if base + top >= 256 { 99 } else { base + top - hi };
            let dn = if base == 0 { 99 } else { lo - base };
            if dn.min(up) < mg {
                eprintln!("base slack {} at slot {s}: base {base} values [{lo}, {hi}]", dn.min(up));
            }
            worst_slack = worst_slack.min(dn.min(up));
            assert!(dn >= 0 && up >= 0, "slot {s}: base {base} does not cover [{lo}, {hi}]");
            if s < f1w {
                assert!(lo - base >= mg, "slot {s}: first-step base 193 too close to [{lo}, {hi}]");
            }
        }
        bases[s] = base;
        base_prev = base;
    }
    assert_eq!(bases[s_slots - 1], 0);
    eprintln!("offset base: {} changes, worst slack {worst_slack}; max stack {maxdep}",
              bases.windows(2).filter(|p| p[0] != p[1]).count());
    let ev_ = |k: &str, d: i64| -> i64 { std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d) };
    let (mpb, mpe, mq, mu, mlv, mp2) = (ev_("FH1_MPB", m), ev_("FH1_MPE", m), ev_("FH1_MQ", m), ev_("FH1_MU", m),
                                        ev_("FH1_MLV", m), ev_("FH1_MP2", m));
    let win = |v: &Vec<(i64, i64)>, s: usize, mm: i64| -> (i64, i64) {
        let (a, z) = env(v, s);
        if z < 0 { (0, 0) } else { ((a - mm).max(0), (z + 1 + mm).min(w)) }
    };
    for s in 0..s_slots {
        let (l1, h1) = env(&b1p, s);
        let (l2, h2) = env(&b1m, s);
        let pmax = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).map(|t| pim[t]).max().unwrap();
        let (lv, jw, p1lo) = if h1 < 0 {
            (0, 0, 0)
        } else {
            let lv = (h1 + 2 + mlv).min(w);
            let jw = (pmax + 1 + m).min(lv);
            let p1lo = (l1 + 1 - m).max(0).min(lv);
            (lv, jw, p1lo)
        };
        let (lc, p2hi) = if h2 < 0 { (w, w) } else { ((l2 + 1 - m).max(0), (h2 + 1 + mp2).min(w)) };
        let (pb0, pb1) = win(&vpr, s, mpb);
        let (pe0, pe1) = win(&dpr, s, mpe);
        let (q0, q1) = win(&pop, s, mq);
        let (u0, u1) = win(&push, s, mu);
        let tm = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).any(|t| term[t]) as i64;
        let fi = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).any(|t| fin[t]) as i64;
        txt += &format!("{lv} {jw} {p1lo} {lc} {p2hi} {pb0} {pb1} {pe0} {pe1} {fi} 0 {tm} {} {q0} {q1} {u0} {u1}\n", bases[s]);
    }
    std::fs::write(&out, txt).unwrap();
    eprintln!("schedule: {n} shots, slots {s_slots} (last finishing {last}), f1w {f1w}, margin {m}, shift {tsh}; {out}");
}

// ---------------------------------------------------------------- gate-level slot against the model
use super::builder::B;
use super::froghop_one::{FhOne, LayOne, W1};
use super::tests_double::run;
use crate::circuit::QubitId;

pub fn lay_one() -> LayOne {
    LayOne::from_text(include_str!("sched_one.txt"), 24)
}

fn putv(words: &mut [u64], qs: &[QubitId], shot: usize, val: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if val.bit(i) {
            words[q.0 as usize] |= 1 << shot;
        } else {
            words[q.0 as usize] &= !(1 << shot);
        }
    }
}
fn getv(words: &[u64], qs: &[QubitId], shot: usize) -> u64 {
    let mut v = 0u64;
    for (i, &q) in qs.iter().enumerate() {
        v |= ((words[q.0 as usize] >> shot) & 1) << i;
    }
    v
}
fn gb(words: &[u64], q: QubitId, shot: usize) -> u64 {
    (words[q.0 as usize] >> shot) & 1
}

fn expect_lanes_one(m: &St) -> (Vec<u8>, Vec<u8>) {
    let w = W1;
    let mut d = vec![0u8; w];
    let mut v = vec![0u8; w];
    for j in 0..w {
        if j < 300 && m.r.bit(j) {
            d[j] |= 1;
        }
        if m.cd.bit(w - 1 - j) {
            d[j] |= 1;
        }
    }
    for u in 0..w {
        let mut bit = 0u8;
        if m.rv.bit(u) {
            bit = 1;
        }
        if m.cv.bit(w - 1 - u) {
            bit = 1;
        }
        let p = ((u as i64 + m.pi as i64).rem_euclid(w as i64)) as usize;
        v[p] = bit;
    }
    // quotient bits: D's gap during OUT (lanes bl(r) + 1 ..), V's gap during DIV (V frame lanes b + 1 ..)
    for (i, &bit) in m.stk.iter().enumerate() {
        match m.ph {
            Ph::Out => {
                let j = bl(&m.r) as usize + 1 + i;
                assert_eq!(d[j], 0, "stack lane {j} of D not free");
                d[j] = bit;
            }
            Ph::Div | Ph::Ret => {
                let u = m.b as usize + 1 + i;
                let p = ((u as i64 + m.pi as i64).rem_euclid(w as i64)) as usize;
                assert_eq!(v[p], 0, "stack lane {u} of V not free");
                v[p] = bit;
            }
            Ph::Dn => panic!("DONE with a stack"),
        }
    }
    (d, v)
}

fn check_state(words: &[u64], f: &FhOne, lay: &LayOne, sigma: usize, k: usize, m: &St) {
    let w = W1;
    let (ed, ev) = expect_lanes_one(m);
    for j in 0..w {
        assert_eq!(gb(words, f.d[j], k) as u8, ed[j], "slot {sigma} shot {k} D lane {j} ph {:?} pi {}", m.ph, m.pi);
        assert_eq!(gb(words, f.v[j], k) as u8, ev[j], "slot {sigma} shot {k} V lane {j} ph {:?} pi {}", m.ph, m.pi);
    }
    assert_eq!(getv(words, &f.pi, k), m.pi as u64, "slot {sigma} shot {k} pi");
    if m.ph != Ph::Dn {
        assert_eq!(getv(words, &f.k, k), m.k as u64, "slot {sigma} shot {k} k");
    }
    let bb = super::froghop_one::BB;
    let bs = lay.base[sigma.saturating_sub(1)]; // the slot shifts the offset at its start
    let bl_ = if m.ph == Ph::Out && m.k > 0 { bl(&m.r) } else { m.b }; // b converts at the turn
    let u = (bl_ as i64 - 1 - bs as i64).rem_euclid(1 << bb) as u64;
    assert_eq!(getv(words, &f.bq, k), u, "slot {sigma} shot {k} b");
    let f1on = sigma < lay.f1w;
    let (fo, fd, fnn) = (gb(words, f.fo, k), gb(words, f.fd, k), gb(words, f.fnn, k));
    let done = if f1on { 0 } else { fnn };
    let want = match m.ph {
        Ph::Out => (1, 0, 0),
        Ph::Ret => (0, 0, 0),
        Ph::Div => (0, 1, 0),
        Ph::Dn => (0, 0, 1),
    };
    assert_eq!((fo, fd, done), want, "slot {sigma} shot {k} phase {:?}", m.ph);
    if f1on {
        assert_eq!(fnn as u8, m.f1, "slot {sigma} shot {k} f1");
    }
    if m.ph != Ph::Dn {
        assert_eq!(getv(words, &f.dep, k), m.stk.len() as u64, "slot {sigma} shot {k} dep");
    } else {
        assert_eq!(getv(words, &f.cnt(), k), m.cnt as u64, "slot {sigma} shot {k} cnt");
        assert_eq!(getv(words, &f.dep[super::froghop_one::CNTB - super::froghop_one::KB..], k), 0, "slot {sigma} shot {k} dep top");
    }
    assert_eq!(gb(words, f.par, k) as u8, m.par, "slot {sigma} shot {k} par");
}

#[test]
fn one_traversal_matches_model() {
    let lay = lay_one();
    let w = W1;
    let gpool: usize = std::env::var("FH1_GP").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let mut b = B::new();
    let d = b.alloc_n(w);
    let v = b.alloc_n(w);
    let par = b.alloc();
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, vec![], gpool);
    let seed: u64 = std::env::var("DSEED").ok().and_then(|s| s.parse().ok()).unwrap_or(4242);
    let mut rng = Rng::new(seed);
    let mut models: Vec<St> = (0..64).map(|_| St::new(rng.below_p())).collect();
    let vl: Vec<QubitId> = f.v[1..257].to_vec();
    f.init(&mut b, &lay);
    let nq = b.width() as usize;
    let mods = models.clone();
    let mut words = run(&b.ops, nq, &|wd| {
        for k in 0..64 {
            putv(wd, &vl, k, &mods[k].rv);
        }
    })
    .q;
    let mut tof = 0u64;
    let pool = f.pool.clone();
    for sigma in 0..lay.s {
        for k in 0..64 {
            check_state(&words, &f, &lay, sigma, k, &models[k]);
        }
        let start = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        let ops = b.ops[start..].to_vec();
        let wd = words.clone();
        let r = run(&ops, nq, &move |x| x.copy_from_slice(&wd));
        assert_eq!(r.phase, 0, "phase after slot {sigma}");
        tof += r.tof;
        words = r.q;
        for &q in pool.iter().chain(f.gp.iter()) {
            assert_eq!(words[q.0 as usize], 0, "scratch q{} dirty after slot {sigma} row {:?}", q.0, lay.rows[sigma]);
        }
        for m in models.iter_mut() {
            m.fwd_at(sigma);
        }
    }
    for m in &models {
        assert!(m.ph == Ph::Dn);
        let _ = m.result();
    }
    eprintln!("one traversal: {} slots, avg Toffoli/shot {} ({:.1} per slot), qubits {}, scratch high water {}",
              lay.s, tof / 64, tof as f64 / 64.0 / lay.s as f64, b.width(), f.hw);
}

#[test]
fn one_profile() {
    use crate::circuit::OperationType as OT;
    use std::collections::BTreeMap;
    let lay = lay_one();
    let gpool: usize = std::env::var("FH1_GP").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let mut b = B::new();
    let d = b.alloc_n(W1);
    let v = b.alloc_n(W1);
    let par = b.alloc();
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, vec![], gpool);
    f.init(&mut b, &lay);
    let mut tot: BTreeMap<&'static str, u64> = BTreeMap::new();
    let (mut odd_t, mut even_t) = (0u64, 0u64);
    for sigma in 0..lay.s {
        f.marks.clear();
        let start = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        let mut mk = vec![("pre", start)];
        mk.extend(f.marks.iter().cloned());
        mk.push(("end", b.ops.len()));
        let mut st = 0u64;
        for i in 0..mk.len() - 1 {
            let c = b.ops[mk[i].1..mk[i + 1].1].iter().filter(|o| matches!(o.kind, OT::CCX | OT::CCZ)).count() as u64;
            *tot.entry(mk[i].0).or_default() += c;
            st += c;
        }
        if sigma % 2 == 1 { odd_t += st } else { even_t += st }
    }
    let all: u64 = tot.values().sum();
    for (k, v) in &tot {
        eprintln!("{:6} {:>9} ({:5.1}%) {:7.1}/slot", k, v, 100.0 * *v as f64 / all as f64, *v as f64 / lay.s as f64);
    }
    eprintln!("total {} ({:.1}/slot; odd slots {:.1}, even {:.1}); scratch high water {} at {}", all, all as f64 / lay.s as f64,
              odd_t as f64 / (lay.s / 2) as f64, even_t as f64 / ((lay.s + 1) / 2) as f64, f.hw, f.hw_at);
    eprintln!("scratch peaks by step: {:?}", f.peaks);
}

fn getn(words: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (words[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}

impl Rng {
    fn below_bits(&mut self, bits: usize) -> N {
        let mut v = N::ZERO;
        for i in 0..6 {
            v |= N::from(self.next()) << (64 * i);
        }
        v & ((N::from(1u64) << bits) - N::from(1u64))
    }
}

#[test]
fn one_forward_inverse_identity() {
    let lay = lay_one();
    let w = W1;
    for seed in 0..4u64 {
        let mut b = B::new();
        let d = b.alloc_n(w);
        let v = b.alloc_n(w);
        let par = b.alloc();
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, vec![], 0);
        let vl: Vec<QubitId> = f.v[1..257].to_vec();
        let v0 = f.v.clone();
        let mut rng = Rng::new(900 + seed);
        let pp = rm::p();
        let xs: Vec<N> = (0..64).map(|_| { let x = rng.below_p() % pp; if x == N::ZERO { N::from(1u64) } else { x } }).collect();
        let ms: Vec<St> = xs.iter().map(|&x| St::new(x)).collect();
        f.init(&mut b, &lay);
        let maps = f.forward(&mut b, &lay);
        f.inverse(&mut b, &lay, &maps);
        f.init(&mut b, &lay);
        assert_eq!(f.v, v0);
        let nq = b.width() as usize;
        let r = run(&b.ops, nq, &|wd| { for k in 0..64 { putv(wd, &vl, k, &ms[k].rv); } });
        assert_eq!(r.phase, 0, "phase");
        for q in 0..nq {
            if vl.iter().any(|x| x.0 as usize == q) { continue; }
            assert_eq!(r.q[q], 0, "qubit {q} not restored (seed {seed})");
        }
        for k in 0..64 { assert_eq!(getn(&r.q, &vl, k), ms[k].rv); }
        eprintln!("one seed {seed}: forward+inverse identity ok, tof/shot {}", r.tof / 64);
    }
}

#[test]
fn one_point_add_end_to_end() {
    use crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve;
    let lay = lay_one();
    let mut b = B::new();
    let (xq, yq) = super::pointadd_one::point_add(&mut b, &lay);
    let ops = b.ops.clone();
    let (nq, _, _, regs) = crate::circuit::analyze_ops(ops.iter());
    eprintln!("ops {} qubits {} peak {} emitted tof {}", ops.len(), nq, b.peak, b.tof);
    // curve
    let pp = rm::p();
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
        let k1 = to_u(&(rng.below_bits(250) + N::from(1u64)));
        let k2 = to_u(&(rng.below_bits(250) + N::from(1u64)));
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
    eprintln!("one end-to-end OK: avg Toffoli {}", sim.stats.toffoli_gates / 64);
}



/// Window check of given inputs (FH1_LX = comma-separated hex) against sched_one.txt: per window the
/// minimum slack over the trajectory (negative = outside), plus base-range coverage, finishing slot and stack depth.
#[test]
fn one_check_lean() {
    let Ok(xs) = std::env::var("FH1_LX") else { return };
    let txt = include_str!("sched_one.txt");
    let mut lines = txt.lines();
    let hdr: Vec<i64> = lines.next().unwrap().split_whitespace().map(|v| v.parse().unwrap()).collect();
    let (w, s_n, f1w) = (hdr[0], hdr[1] as usize, hdr[2] as usize);
    let rows: Vec<Vec<i64>> = lines.map(|l| l.split_whitespace().map(|v| v.parse().unwrap()).collect()).collect();
    let names = ["lv", "p1lo", "jw", "lc", "p2hi", "pb", "pe", "pop", "push", "base", "fin", "term"];
    for xh in xs.split(',') {
        let x = N::from_str_radix(xh.trim(), 16).unwrap();
        let mut st = St::new(x);
        let mut sl = vec![(i64::MAX, 0usize); names.len()];
        let mut upd = |i: usize, v: i64, s: usize| {
            if v < sl[i].0 {
                sl[i] = (v, s);
            }
        };
        let mut fin_slot = usize::MAX;
        let mut maxdep = 0usize;
        let mut maxk = 0u32;
        for s in 0..s_n {
            if st.ph == Ph::Dn {
                fin_slot = fin_slot.min(s);
                break;
            }
            let r = &rows[s];
            let base = r[12];
            let s0 = st.clone();
            let pi0 = s0.pi as i64;
            let blr0 = bl(&s0.r) as i64;
            let d0 = s0.stk.len() as i64;
            let nb0 = if s0.ph == Ph::Out { blr0 } else { s0.b as i64 };
            let al0 = s0.k != 0 || s0.b == 1;
            let mut vals: Vec<i64> = vec![];
            if s0.ph == Ph::Out && s0.k == 0 && s0.b == 1 {
                upd(10, if r[9] != 0 { 99 } else { -99 }, s);
            }
            if !(s0.ph == Ph::Out && s0.k != 0) {
                let b1 = nb0 + if al0 { pi0 } else { 0 };
                upd(0, r[0] - (b1 + 2), s);
                upd(1, (b1 + 1) - r[2], s);
                upd(2, r[1] - (pi0 + 1), s);
                vals.push(b1 - 1);
            }
            if s0.ph == Ph::Out && d0 > 0 {
                let j = blr0 + d0;
                upd(7, (j - r[13]).min(r[14] - 1 - j), s);
                vals.push(j - 1);
            }
            let ev = st.fwd_at(s);
            let s1 = &st;
            maxdep = maxdep.max(s1.stk.len());
            maxk = maxk.max(s1.k);
            let (rel, mv) = match (s0.ph, s1.ph) {
                (Ph::Out, Ph::Out) => {
                    let al1 = s1.k != 0 || s1.b == 1;
                    (true, blr0 + s1.stk.len() as i64 + if al1 { pi0 } else { 0 })
                }
                (Ph::Out, Ph::Ret) => (true, s1.b as i64 + pi0),
                (Ph::Out, Ph::Dn) => (true, 1 + pi0),
                (Ph::Ret, _) | (Ph::Div, _) => {
                    if ev.step_end.is_some() {
                        (true, s1.b as i64 + s1.stk.len() as i64)
                    } else {
                        (s0.ph == Ph::Ret, s0.b as i64 + pi0)
                    }
                }
                _ => (false, 0),
            };
            if rel {
                upd(3, (mv + 1) - r[3], s);
                upd(4, r[4] - (mv + 1), s);
                vals.push(mv - 1);
            }
            if s1.ph == Ph::Div && ev.step_end.is_none() {
                let d1 = s1.stk.len() as i64;
                if s0.ph == Ph::Div || d1 > d0 {
                    let j = s1.b as i64 + d1 + pi0;
                    upd(8, (j - r[15]).min(r[16] - 1 - j), s);
                    vals.push(j - 1);
                }
            }
            if s0.ph == Ph::Out && s1.ph == Ph::Ret {
                let k = s1.k as i64;
                let jv = blr0 - k + pi0;
                let jd = s1.b as i64 + k - 1;
                upd(5, (jv - r[5]).min(r[6] - 1 - jv), s);
                upd(6, (jd - r[7]).min(r[8] - 1 - jd), s);
                vals.push(jv - 1);
                vals.push(jd);
            }
            for v in vals {
                upd(9, (v - base).min(base + 63 - v), s);
            }
            if st.ph == Ph::Dn && st.cnt == 0 {
                upd(11, if r[11] != 0 { 99 } else { -99 }, s);
            }
        }
        let mut msg = format!("x {xh}: finish {fin_slot} (S {s_n}, f1w {f1w}), max stack {maxdep}, max k {maxk};");
        for (i, nm) in names.iter().enumerate() {
            if sl[i].0 != i64::MAX {
                msg += &format!(" {nm} {}@{}", sl[i].0, sl[i].1);
            }
        }
        let _ = w;
        eprintln!("{msg}");
    }
}

