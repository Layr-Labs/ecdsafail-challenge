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
/// FH1_M=<lane margin> FH1_T=<slot shift>. Columns: lv jw p1lo lc p2hi pb0 pb1 pe0 pe1 fb0 fb1 termon; header
/// "W S f1w".
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
    let mut b1p = vec![(big, -1i64); S]; // P1 boundary (pre-slot)
    let mut b1m = vec![(big, -1i64); S]; // P2/P3 boundary (after alignment / step end of the slot)
    let mut pim = vec![0i64; S];
    let mut pb = vec![(big, -1i64); S];
    let mut pe = vec![(big, -1i64); S];
    let mut term = vec![false; S];
    let mut fin = vec![false; S];
    let mut bpre = vec![(big, -1i64); S]; // b - 1 pre-slot (held, never decoded: not part of the base range)
    let mut last = 0usize;
    let mut f1last = 0usize;
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
            mm(&mut b1p[s], st.b1() as i64);
            mm(&mut bpre[s], st.b as i64 - 1);
            pim[s] = pim[s].max(st.pi as i64);
            if st.ph == Ph::Out && st.k == 0 && st.b == 1 {
                fin[s] = true;
            }
            let ev = st.fwd_at(s);
            // P2/P3 run after the alignment conversion and the step end, before the pi update: mid-slot boundary
            let mid = match (ev.align, ev.step_end) {
                (Some((_, bv, pi)), _) => (bv + pi) as i64,
                (None, Some(b)) => b as i64,
                _ => {
                    if st.ph == Ph::Dn {
                        -1
                    } else {
                        // pi already moved by +-1: recover the pre-update pi from the phase transition
                        -2
                    }
                }
            };
            let _ = mid;
            if let Some((b0, bv, pi)) = ev.align {
                mm(&mut pb[s], b0 as i64);
                mm(&mut pe[s], (bv + pi - 1) as i64);
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
    // the mid-slot boundary equals the pre-slot one except at alignment (b_V + pi) and step ends (b): recompute it
    // exactly in a second pass over the same shots
    let mut rng = Rng::new(seed);
    for _ in 0..n {
        let x = rng.below_p();
        let mut st = St::new(x);
        for s in 0..S {
            if st.ph == Ph::Dn {
                break;
            }
            let pre_pi = st.pi;
            let pre_b1 = st.b1() as i64;
            let ev = st.fwd_at(s);
            let mid = if let Some((_, bv, pi)) = ev.align {
                (bv + pi) as i64
            } else if let Some(b) = ev.step_end {
                b as i64
            } else {
                let _ = pre_pi;
                pre_b1
            };
            mm(&mut b1m[s], mid);
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
    // offset-register base: every value the slot decodes (b - 1, B1 - 1 before and mid slot, the probe values) must lie
    // in [base + mg, base + 2^BB - 1 - mg]; 192 in the first-step slots, 0 where [b == 1] is tested
    let bb = super::froghop_one::BB as i64;
    let top = (1i64 << bb) - 1;
    let mg: i64 = std::env::var("FH1_BM").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    let mut base_prev = 192i64;
    let mut bases = vec![0i64; s_slots];
    let mut worst_slack = i64::MAX;
    for s in 0..s_slots {
        let mut lo = big;
        let mut hi = -1i64;
        for (v, sh) in [(&b1p, -1i64), (&b1m, -1), (&pb, -1), (&pe, 0)] {
            let (a, z) = env(v, s);
            if z >= 0 {
                lo = lo.min(a + sh);
                // a D-probe value of 256 (first step, dl = 0: D lane 256 is 0) is skipped by the scan
                hi = hi.max((z + sh).min(255));
            }
        }
        let fi = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).any(|t| fin[t]);
        let tm = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).any(|t| term[t]);
        let base = if s < f1w {
            192
        } else if fi || tm || hi < 0 {
            0
        } else if base_prev <= lo - mg && base_prev + top >= hi + mg {
            base_prev
        } else {
            // widest margin that fits (mg, then less), centred
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
            // b - 1 <= 255 always (and B1 - 1 = 256 only at a first-step alignment, where cd = 0 and f1 make P2/P3
            // irrelevant): no margin is needed above 255
            let up = if base + top >= 255 { 99 } else { base + top - hi };
            let dn = if base == 0 { 99 } else { lo - base }; // b - 1 >= 0 always
            if dn.min(up) < mg {
                eprintln!("base slack {} at slot {s}: base {base} values [{lo}, {hi}]", dn.min(up));
            }
            worst_slack = worst_slack.min(dn.min(up));
            assert!(lo - base >= 0 && up >= 0, "slot {s}: base {base} does not cover [{lo}, {hi}]");
            if s < f1w {
                assert!(lo - base >= mg, "slot {s}: first-step base 192 too close to [{lo}, {hi}]");
            }
        }
        bases[s] = base;
        base_prev = base;
    }
    assert_eq!(bases[s_slots - 1], 0);
    eprintln!("offset base: {} changes, worst slack {worst_slack}", bases.windows(2).filter(|p| p[0] != p[1]).count());
    for s in 0..s_slots {
        let (l1, h1) = env(&b1p, s);
        let (l2, h2) = env(&b1m, s);
        let (pbl, pbh) = env(&pb, s);
        let (pel, peh) = env(&pe, s);
        let pmax = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).map(|t| pim[t]).max().unwrap();
        let (lv, jw, p1lo, lc, p2hi) = if h1 < 0 {
            (0, 0, 0, w, w)
        } else {
            let lv = (h1 + 2 + m).min(w);
            let jw = (pmax + 1 + m).min(lv);
            let p1lo = (l1 + 1 - m).max(0).min(lv);
            let lc = (l2 + 1 - m).max(0);
            let p2hi = (h2 + 1 + m).min(w);
            (lv, jw, p1lo, lc, p2hi)
        };
        let (pb0, pb1) = if pbh < 0 { (0, 0) } else { ((pbl - m).max(0), (pbh + 1 + m).min(w)) };
        let (pe0, pe1) = if peh < 0 { (0, 0) } else { ((pel - m).max(0), (peh + 1 + m).min(w)) };
        let tm = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).any(|t| term[t]) as i64;
        let fi = (s.saturating_sub(tsh)..=(s + tsh).min(S - 1)).any(|t| fin[t]) as i64;
        txt += &format!("{lv} {jw} {p1lo} {lc} {p2hi} {pb0} {pb1} {pe0} {pe1} {fi} 0 {tm} {}\n", bases[s]);
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
    assert_eq!(getv(words, &f.k, k), m.k as u64, "slot {sigma} shot {k} k");
    let bb = super::froghop_one::BB;
    let bs = lay.base[sigma.saturating_sub(1)]; // the slot shifts the offset at its start
    let u = (m.b as i64 - 1 - bs as i64).rem_euclid(1 << bb) as u64;
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
    assert_eq!(getv(words, &f.dep, k), m.stk.len() as u64, "slot {sigma} shot {k} dep");
    for (i, bit) in m.stk.iter().rev().enumerate() {
        assert_eq!(gb(words, f.stk[i], k) as u8, *bit, "slot {sigma} shot {k} stk {i}");
    }
    if m.ph == Ph::Dn {
        assert_eq!(getv(words, f.cnt(), k), m.cnt as u64, "slot {sigma} shot {k} cnt");
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

/// R9-C5 diagnostic: exact emitted T by slot stage for the paired ghost legs.
/// The builder's mark positions follow the enclosing recording during inverse construction.
#[test]
fn one_r9_c5_stage_attribution() {
    use super::builder::G;
    use super::froghop_one::SlotMode;
    use crate::circuit::OperationType as OT;
    use std::collections::BTreeMap;
    let lay = lay_one();
    let mut b = B::new();
    let d = b.alloc_n(W1);
    let v = b.alloc_n(W1);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, dirty, 0);
    assert_eq!(b.peak, 843);
    f.init(&mut b, &lay);
    let receipts = b.fresh_bits(lay.s);
    let dl_receipts = b.fresh_bits(lay.s);
    let mut maps = Vec::with_capacity(lay.s);
    let mut fw = BTreeMap::<&'static str, u64>::new();
    for (sigma, (&receipt, &dl_receipt)) in receipts.iter().zip(dl_receipts.iter()).enumerate() {
        maps.push(f.v.clone());
        f.marks.clear();
        let start = b.ops.len();
        let t0 = b.tof;
        f.slot_mode(&mut b, &lay, sigma, SlotMode::ForwardGhost { receipt, dl_receipt: Some(dl_receipt), extras: None });
        let mut marks = vec![("pre", start)];
        marks.extend(f.marks.iter().copied());
        marks.push(("end", b.ops.len()));
        let mut st = 0;
        for pair in marks.windows(2) {
            let c = b.ops[pair[0].1..pair[1].1].iter()
                .filter(|op| matches!(op.kind, OT::CCX | OT::CCZ)).count() as u64;
            *fw.entry(pair[0].0).or_default() += c;
            st += c;
        }
        assert_eq!(st, b.tof - t0, "forward stage accounting slot {sigma}");
    }
    let fw_pool = f.peaks.clone();
    f.peaks.clear();
    let mut rv = BTreeMap::<&'static str, u64>::new();
    for sigma in (0..lay.s).rev() {
        f.v = maps[sigma].clone();
        f.marks.clear();
        b.begin();
        f.slot_mode(&mut b, &lay, sigma,
            SlotMode::RecordInverseWithRepair { receipt: receipts[sigma], dl_receipt: Some(dl_receipts[sigma]), extras: None });
        let rec = b.end();
        let mut marks = vec![("pre", 0)];
        marks.extend(f.marks.iter().copied());
        marks.push(("end", rec.len()));
        let mut st = 0;
        for pair in marks.windows(2) {
            let c = rec[pair[0].1..pair[1].1].iter()
                .filter(|g| matches!(g, G::Ccx(..) | G::AndU(..))).count() as u64;
            *rv.entry(pair[0].0).or_default() += c;
            st += c;
        }
        let t0 = b.tof;
        b.play(&rec, true);
        assert_eq!(st, b.tof - t0, "inverse stage accounting slot {sigma}");
        f.v = maps[sigma].clone();
    }
    let fw_sum: u64 = fw.values().sum();
    let rv_sum: u64 = rv.values().sum();
    assert_eq!((fw_sum, rv_sum), (2_210_389, 2_847_080));
    eprintln!("R9-C5 forward T {fw_sum} by stage {fw:?}");
    eprintln!("R9-C5 inverse T {rv_sum} by stage {rv:?}");
    eprintln!("R9-C5 forward pool max-used {fw_pool:?}");
    eprintln!("R9-C5 inverse pool max-used {:?}", f.peaks);
}

/// R9-C5 sampled all-wire zero census, observing D/V after every emitted op.
/// The scratch ownership census comes from Pl.peaks in the stage attribution test.
#[test]
fn one_r9_c5_sampled_free_lanes() {
    use super::froghop_one::SlotMode;
    use crate::circuit::{Op, OperationType as OT};
    use sha3::digest::{ExtendableOutput, Update};
    use std::collections::BTreeMap;
    #[derive(Clone, Copy, Debug)]
    struct Span { d: usize, v: usize, both: usize, ops: u64 }
    impl Span {
        fn new() -> Self { Span { d: usize::MAX, v: usize::MAX, both: usize::MAX, ops: 0 } }
        fn see(&mut self, d: usize, v: usize) {
            self.d = self.d.min(d);
            self.v = self.v.min(v);
            self.both = self.both.min(d + v);
        }
    }
    fn apply<R: sha3::digest::XofReader>(ops: &[Op], sim: &mut crate::sim::Simulator<'_, R>, kind: &[u8], zeros: &mut [usize; 3], span: &mut Span) {
        span.see(zeros[1], zeros[2]);
        for op in ops {
            let a = op.q_target.0 as usize;
            let b = op.q_control1.0 as usize;
            let sw = op.kind == OT::Swap && b != a;
            let old_a = a < kind.len() && kind[a] != 0 && sim.qubits[a] == 0;
            let old_b = sw && b < kind.len() && kind[b] != 0 && sim.qubits[b] == 0;
            sim.apply_iter(std::iter::once(op));
            if a < kind.len() && kind[a] != 0 {
                zeros[kind[a] as usize] = (zeros[kind[a] as usize] as isize
                    + usize::from(sim.qubits[a] == 0) as isize - usize::from(old_a) as isize) as usize;
            }
            if sw && b < kind.len() && kind[b] != 0 {
                zeros[kind[b] as usize] = (zeros[kind[b] as usize] as isize
                    + usize::from(sim.qubits[b] == 0) as isize - usize::from(old_b) as isize) as usize;
            }
            span.see(zeros[1], zeros[2]);
            span.ops += 1;
        }
    }
    let lay = lay_one();
    let mut b = B::new();
    let d = b.alloc_n(W1);
    let v = b.alloc_n(W1);
    let par = b.alloc();
    let foreign = b.alloc_n(256);
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, foreign.clone(), 0);
    let vl = f.v[1..257].to_vec();
    let mut rng = Rng::new(4242);
    let xs: Vec<N> = (0..64).map(|_| St::new(rng.below_p()).rv).collect();
    f.init(&mut b, &lay);
    let receipts = b.fresh_bits(lay.s);
    let mut h = sha3::Shake256::default();
    h.update(b"R9-C5-free-lanes");
    let mut xof = h.finalize_xof();
    let mut sim = crate::sim::Simulator::new(b.width() as usize, receipts.last().unwrap().0 as usize + 1, &mut xof);
    for k in 0..64 { putv(&mut sim.qubits, &vl, k, &xs[k]); }
    for &q in &foreign { sim.qubits[q.0 as usize] = rng.next(); }
    sim.apply_iter(b.ops.iter());
    b.ops.clear();
    let mut kind = vec![0u8; b.width() as usize];
    for &q in &f.d { kind[q.0 as usize] = 1; }
    for &q in &f.v { kind[q.0 as usize] = 2; }
    let mut zeros = [0, 0, 0];
    for (i, &k) in kind.iter().enumerate() {
        if k != 0 && sim.qubits[i] == 0 { zeros[k as usize] += 1; }
    }
    let mut maps = Vec::with_capacity(lay.s);
    let mut fw = BTreeMap::<&'static str, Span>::new();
    for (sigma, &receipt) in receipts.iter().enumerate() {
        maps.push(f.v.clone());
        f.marks.clear();
        f.slot_mode(&mut b, &lay, sigma, SlotMode::ForwardGhost { receipt, dl_receipt: None, extras: None });
        let mut marks = vec![("pre", 0)];
        marks.extend(f.marks.iter().copied());
        marks.push(("end", b.ops.len()));
        for pair in marks.windows(2) {
            apply(&b.ops[pair[0].1..pair[1].1], &mut sim, &kind, &mut zeros,
                fw.entry(pair[0].0).or_insert_with(Span::new));
        }
        b.ops.clear();
    }
    let mut rv = BTreeMap::<&'static str, Span>::new();
    for sigma in (0..lay.s).rev() {
        f.v = maps[sigma].clone();
        f.marks.clear();
        b.begin();
        f.slot_mode(&mut b, &lay, sigma,
            SlotMode::RecordInverseWithRepair { receipt: receipts[sigma], dl_receipt: None, extras: None });
        let rec = b.end();
        let mut marks = vec![("pre", 0)];
        marks.extend(f.marks.iter().copied());
        marks.push(("end", rec.len()));
        for pair in marks.windows(2).rev() {
            b.play(&rec[pair[0].1..pair[1].1], true);
            apply(&b.ops, &mut sim, &kind, &mut zeros,
                rv.entry(pair[0].0).or_insert_with(Span::new));
            b.ops.clear();
        }
        f.v = maps[sigma].clone();
    }
    eprintln!("R9-C5 sampled D/V zero minima over every op of 903 forward slots, 64 deterministic words: {fw:?}");
    eprintln!("R9-C5 sampled D/V zero minima over every op of 903 inverse slots, 64 deterministic words: {rv:?}");
    assert_eq!(sim.phase, 0, "sampled paired phase");
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

/// Independent Plain oracle at every boundary, with the actual pre-HMR TT
/// word and its actual measurement outcome accounting for forward phase debt.
#[test]
fn one_ghost_forward_data_and_debt() {
    use super::froghop_one::SlotMode;
    use crate::circuit::OperationType as OT;
    use sha3::digest::{ExtendableOutput, Update};
    let lay = lay_one();
    let setup = |b: &mut B| {
        let d = b.alloc_n(W1);
        let v = b.alloc_n(W1);
        let par = b.alloc();
        let foreign = b.alloc_n(256);
        let mut f = FhOne::alloc(b, d, v, &lay, par, foreign.clone(), 0);
        f.init(b, &lay);
        (f, foreign)
    };
    let (mut plain_b, mut ghost_b) = (B::new(), B::new());
    let (mut plain, foreign) = setup(&mut plain_b);
    let (mut ghost, ghost_foreign) = setup(&mut ghost_b);
    assert_eq!(foreign, ghost_foreign);
    let vl = plain.v[1..257].to_vec();
    let receipts = ghost_b.fresh_bits(lay.s);
    let nb = receipts.last().unwrap().0 as usize + 1;
    let nq = plain_b.width() as usize;
    assert_eq!(nq, 843);
    let mut hash = sha3::Shake256::default();
    hash.update(b"froghop-ghost-debt-r2");
    let mut plain_xof = hash.clone().finalize_xof();
    let mut ghost_xof = hash.finalize_xof();
    let mut ps = crate::sim::Simulator::new(nq, nb, &mut plain_xof);
    let mut gs = crate::sim::Simulator::new(nq, nb, &mut ghost_xof);
    let mut rng = Rng::new(4242);
    let mut models: Vec<St> = (0..64).map(|_| St::new(rng.below_p())).collect();
    for k in 0..64 { putv(&mut ps.qubits, &vl, k, &models[k].rv); }
    for &q in &foreign { ps.qubits[q.0 as usize] = rng.next(); }
    gs.qubits.copy_from_slice(&ps.qubits);
    let foreign_words: Vec<u64> = foreign.iter().map(|q| ps.qubits[q.0 as usize]).collect();
    ps.apply_iter(plain_b.ops.iter());
    gs.apply_iter(ghost_b.ops.iter());
    let mut debt = 0;
    let mut tt_one = 0u64;
    let mut tt_zero = 0u64;
    let mut turn_post_fo_zero = 0u64;
    let mut no_lanes = 0;
    for sigma in 0..lay.s {
        for k in 0..64 { check_state(&gs.qubits, &ghost, &lay, sigma, k, &models[k]); }
        plain_b.ops.clear();
        ghost_b.ops.clear();
        plain.slot(&mut plain_b, &lay, sigma);
        ghost.slot_mode(&mut ghost_b, &lay, sigma, SlotMode::ForwardGhost { receipt: receipts[sigma], dl_receipt: None, extras: None });
        ps.apply_iter(plain_b.ops.iter());
        let mut discharges = 0;
        for op in &ghost_b.ops {
            if op.kind == OT::Hmr && op.c_target == receipts[sigma] {
                let tt = gs.qubits[op.q_target.0 as usize];
                tt_one += tt.count_ones() as u64;
                tt_zero += (!tt).count_ones() as u64;
                turn_post_fo_zero += (tt & !gs.qubits[ghost.fo.0 as usize]).count_ones() as u64;
                gs.apply_iter(std::iter::once(op));
                debt ^= tt & gs.bits[receipts[sigma].0 as usize];
                discharges += 1;
            } else {
                gs.apply_iter(std::iter::once(op));
            }
        }
        assert_eq!(discharges, 1, "ghost slot {sigma}");
        assert_eq!(ps.phase, 0, "Plain phase slot {sigma}");
        assert_eq!(gs.phase, debt, "forward debt slot {sigma}");
        assert_eq!(gs.qubits, ps.qubits, "forward data/foreign payload slot {sigma}");
        assert_eq!(ghost.v, plain.v, "lane descriptors slot {sigma}");
        for &q in ghost.pool.iter().chain(ghost.gp.iter()) {
            assert_eq!(gs.qubits[q.0 as usize], 0, "ghost scratch slot {sigma}");
        }
        for (i, &q) in foreign.iter().enumerate() { assert_eq!(gs.qubits[q.0 as usize], foreign_words[i]); }
        no_lanes += usize::from(lay.rows[sigma][3] >= W1);
        for m in &mut models { m.fwd_at(sigma); }
    }
    assert!(tt_one > 0 && tt_zero > 0 && turn_post_fo_zero > 0 && no_lanes > 0);
    assert_eq!(plain_b.tof - ghost_b.tof, 521_891);
    assert_eq!(ghost_b.peak, 843);
    eprintln!("ghost forward: 903 boundaries/data/debt/foreign words pass; tt1 {tt_one} tt0 {tt_zero}, tt1/postfo0 {turn_post_fo_zero}, no-lane slots {no_lanes}; saving {} T, debt {debt:016x}, Q{}", plain_b.tof - ghost_b.tof, ghost_b.peak);
}

/// Old/plain versus six-HMR forward kernel on every slot boundary.
#[test]
fn one_r9_c5_extra_forward_boundary() {
    use super::froghop_one::SlotMode;
    use crate::circuit::OperationType as OT;
    use sha3::digest::{ExtendableOutput, Update};
    let lay = lay_one();
    let setup = |b: &mut B| {
        let d = b.alloc_n(W1);
        let v = b.alloc_n(W1);
        let par = b.alloc();
        let foreign = b.alloc_n(256);
        let mut f = FhOne::alloc(b, d, v, &lay, par, foreign.clone(), 0);
        f.init(b, &lay);
        (f, foreign)
    };
    let (mut old_b, mut new_b) = (B::new(), B::new());
    let (mut old, foreign) = setup(&mut old_b);
    let (mut new, new_foreign) = setup(&mut new_b);
    assert_eq!(foreign, new_foreign);
    let vl = old.v[1..257].to_vec();
    let tt_receipts = new_b.fresh_bits(lay.s);
    let dl_receipts = new_b.fresh_bits(lay.s);
    let extra_flat = new_b.fresh_bits(4 * lay.s);
    let extra_receipts: Vec<[crate::circuit::BitId; 4]> = extra_flat.chunks_exact(4)
        .map(|chunk| chunk.try_into().unwrap()).collect();
    let nb = extra_flat.last().unwrap().0 as usize + 1;
    let nq = old_b.width() as usize;
    assert_eq!(nq, 843);
    let mut h = sha3::Shake256::default();
    h.update(b"R9-C5-dl-boundary");
    let mut old_xof = h.clone().finalize_xof();
    let mut new_xof = h.finalize_xof();
    let mut os = crate::sim::Simulator::new(nq, nb, &mut old_xof);
    let mut ns = crate::sim::Simulator::new(nq, nb, &mut new_xof);
    let mut rng = Rng::new(4242);
    let mut models: Vec<St> = (0..64).map(|_| St::new(rng.below_p())).collect();
    for k in 0..64 { putv(&mut os.qubits, &vl, k, &models[k].rv); }
    for &q in &foreign { os.qubits[q.0 as usize] = rng.next(); }
    ns.qubits.copy_from_slice(&os.qubits);
    let foreign_words: Vec<u64> = foreign.iter().map(|q| os.qubits[q.0 as usize]).collect();
    os.apply_iter(old_b.ops.iter());
    ns.apply_iter(new_b.ops.iter());
    let mut debt = 0u64;
    let mut dl_one = 0u64;
    let mut dl_zero = 0u64;
    for sigma in 0..lay.s {
        for k in 0..64 { check_state(&ns.qubits, &new, &lay, sigma, k, &models[k]); }
        old_b.ops.clear();
        new_b.ops.clear();
        old.slot(&mut old_b, &lay, sigma);
        new.slot_mode(&mut new_b, &lay, sigma, SlotMode::ForwardGhost {
            receipt: tt_receipts[sigma], dl_receipt: Some(dl_receipts[sigma]),
            extras: Some(extra_receipts[sigma]) });
        os.apply_iter(old_b.ops.iter());
        let mut tt_hits = 0;
        let mut dl_hits = 0;
        let mut extra_hits = [0usize; 4];
        for op in &new_b.ops {
            let is_tt = op.kind == OT::Hmr && op.c_target == tt_receipts[sigma];
            let is_dl = op.kind == OT::Hmr && op.c_target == dl_receipts[sigma];
            let extra = extra_receipts[sigma].iter().position(|&id| op.kind == OT::Hmr && op.c_target == id);
            let val = if is_tt || is_dl || extra.is_some() { ns.qubits[op.q_target.0 as usize] } else { 0 };
            ns.apply_iter(std::iter::once(op));
            if is_tt || is_dl || extra.is_some() { debt ^= val & ns.bits[op.c_target.0 as usize]; }
            if is_tt { tt_hits += 1; }
            if is_dl { dl_hits += 1; dl_one += val.count_ones() as u64; dl_zero += (!val).count_ones() as u64; }
            if let Some(j) = extra { extra_hits[j] += 1; }
        }
        assert_eq!((tt_hits, dl_hits, extra_hits), (1, 1, [1; 4]), "receipts slot {sigma}");
        assert_eq!(os.phase, 0, "old phase slot {sigma}");
        assert_eq!(ns.phase, debt, "new phase debt slot {sigma}");
        assert_eq!(os.qubits, ns.qubits, "old/new all-wire data slot {sigma}");
        assert_eq!(old.v, new.v, "lane descriptor slot {sigma}");
        for &q in new.pool.iter().chain(new.gp.iter()) {
            assert_eq!(ns.qubits[q.0 as usize], 0, "scratch slot {sigma}");
        }
        for (i, &q) in foreign.iter().enumerate() {
            assert_eq!(ns.qubits[q.0 as usize], foreign_words[i], "foreign slot {sigma}");
        }
        for m in &mut models { m.fwd_at(sigma); }
    }
    assert!(dl_one > 0 && dl_zero > 0, "dl measurement sampled both values");
    eprintln!("R9-C5 six-debt old/new all 903 slots OK; forward saving {} T; dl one/zero {dl_one}/{dl_zero}", old_b.tof - new_b.tof);
}

#[test]
fn one_r9_c5_adjacent_pair_kernel() {
    let mut b = B::new();
    let qs = b.alloc_n(259);
    b.ccx(qs[0], qs[1], qs[2]);
    b.ccx(qs[0], qs[1], qs[2]);
    let old = b.ops.clone();
    let mut new = old.clone();
    assert_eq!(super::cancel_adjacent_ccx(&mut new), 2);
    assert!(new.is_empty());
    let mut rng = Rng::new(8435);
    let input: Vec<u64> = (0..259).map(|_| rng.next()).collect();
    let init = |words: &mut Vec<u64>| words.copy_from_slice(&input);
    let before = run(&old, 259, &init);
    let after = run(&new, 259, &init);
    assert_eq!(before.q, input);
    assert_eq!(after.q, input);
    assert_eq!((before.phase, after.phase), (0, 0));
    assert_eq!((before.tof, after.tof), (128, 0));
    eprintln!("R9-C5 adjacent CCX pair: all 259 wires/64 words, dirty passengers, zero phase");
}

#[test]
fn one_r9_c5_decoder_pivot_kernel() {
    use super::mask::{onehot_scan, onehot_scan_old};
    let build = |fast: bool, undo: bool| {
        let mut b = B::new();
        let v = b.alloc_n(9);
        let pre = b.alloc_n(8);
        let out = b.alloc_n(512);
        let dirty = b.alloc_n(256);
        b.begin();
        if fast {
            onehot_scan(&mut b, &v, &pre, 0, 512, 0, |b, j, o| b.cx(o, out[j]));
        } else {
            onehot_scan_old(&mut b, &v, &pre, 0, 512, 0, |b, j, o| b.cx(o, out[j]));
        }
        let rec = b.end();
        b.play(&rec, false);
        if undo { b.play(&rec, true); }
        (b, v, pre, out, dirty)
    };
    let mut rng = Rng::new(8436);
    let data: Vec<u64> = (0..9 + 512 + 256).map(|_| rng.next()).collect();
    let eval = |fast: bool, undo: bool| {
        let (b, v, pre, out, dirty) = build(fast, undo);
        let r = run(&b.ops, b.width() as usize, &|wd| {
            for (i, &q) in v.iter().chain(out.iter()).chain(dirty.iter()).enumerate() {
                wd[q.0 as usize] = data[i];
            }
        });
        for q in pre { assert_eq!(r.q[q.0 as usize], 0, "decoder scratch"); }
        (r, b.tof)
    };
    let (old, old_t) = eval(false, false);
    let (new, new_t) = eval(true, false);
    assert_eq!(new.q, old.q, "forward all-wire mismatch");
    assert_eq!((old.phase, new.phase), (0, 0));
    let (old_inv, _) = eval(false, true);
    let (new_inv, _) = eval(true, true);
    assert_eq!(old_inv.q, new_inv.q, "inverse all-wire mismatch");
    assert_eq!((old_inv.phase, new_inv.phase), (0, 0));
    assert_eq!(new_inv.q[0..9], data[0..9]);
    eprintln!("R9-C5 decoder pivot all-wire forward/inverse, 256 dirty passengers, zero phase; old {old_t} T, new {new_t} T");
    assert!(new_t < old_t);
}

#[test]
fn one_r9_c5_masked_down_shared_and_kernel() {
    let build = |shared: bool, undo: bool| {
        let mut b = B::new();
        let q = b.alloc_n(7 + 256);
        let (f, t, s, x, g, tmp, gf) = (q[0], q[1], q[2], q[3], q[4], q[5], q[6]);
        b.begin();
        if shared {
            b.and_c(f, s, tmp);
            b.ccx(tmp, t, x);
            b.ccx(tmp, g, t);
            b.and_u(f, s, tmp);
        } else {
            b.and_c(t, s, tmp);
            b.ccx(f, tmp, x);
            b.and_u(t, s, tmp);
            b.and_c(g, f, gf);
            b.ccx(gf, s, t);
            b.and_u(g, f, gf);
        }
        b.cx(x, t);
        b.cx(x, s);
        let rec = b.end();
        b.play(&rec, false);
        if undo { b.play(&rec, true); }
        (b, q)
    };
    let mut rng = Rng::new(8437);
    let mut input = vec![0u64; 7 + 256];
    for bit in 0..5 {
        for shot in 0..64 { if ((shot >> bit) & 1) != 0 { input[bit] |= 1u64 << shot; } }
    }
    for q in &mut input[7..] { *q = rng.next(); }
    let eval = |shared: bool, undo: bool| {
        let (b, q) = build(shared, undo);
        let r = run(&b.ops, b.width() as usize, &|wd| wd.copy_from_slice(&input));
        assert_eq!(r.q[q[5].0 as usize], 0, "temporary AND target");
        assert_eq!(r.q[q[6].0 as usize], 0, "old second AND target");
        (r, b.tof)
    };
    let (old, old_t) = eval(false, false);
    let (new, new_t) = eval(true, false);
    assert_eq!(old.q, new.q, "forward all-wire mismatch");
    assert_eq!((old.phase, new.phase), (0, 0));
    let (old_inv, _) = eval(false, true);
    let (new_inv, _) = eval(true, true);
    assert_eq!(old_inv.q, input, "old inverse identity");
    assert_eq!(new_inv.q, input, "new inverse identity");
    assert_eq!((old_inv.phase, new_inv.phase), (0, 0));
    assert_eq!((old_t, new_t), (4, 3));
    eprintln!("R9-C5 shared-AND masked cell: all 263 wires, 32 control states, dirty passengers, inverse, zero phase");
}

#[test]
fn one_r9_c5_ladder_midpoint_kernel() {
    use super::mask::{mdown, mdown_mid, mup, mup_mid, Lad, Mscr, Src};
    let build = |mid: bool, undo: bool| {
        let mut b = B::new();
        let t = b.alloc_n(8);
        let s = b.alloc_n(8);
        let v = b.alloc_n(3);
        let pre = b.alloc_n(2);
        let c0 = b.alloc();
        let f = b.alloc();
        let temp = b.alloc();
        let gf = b.alloc();
        let chain = b.alloc_n(3);
        let g = b.alloc();
        let dirty = b.alloc_n(256);
        let srcs = vec![Src { lo: 0, hi: 8, v: v.clone(), a: 0, d: 1, pre: pre.clone(), late: false }];
        let sc = Mscr { f, t: temp, gf, chain: chain.clone() };
        let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: false, cmpl: true, sc: &sc, g: &[] };
        b.begin();
        let up = if mid { mup_mid(&mut b, &ld) } else { mup(&mut b, &ld) };
        let down = if mid { mdown_mid(&mut b, &ld, Some(g)) } else { mdown(&mut b, &ld, Some(g)) };
        b.play(&up, false);
        b.play(&down, false);
        let rec = b.end();
        b.play(&rec, false);
        if undo { b.play(&rec, true); }
        (b, t, s, v, pre, c0, f, temp, gf, chain, g, dirty)
    };
    let mut rng = Rng::new(8438);
    let mut input = vec![0u64; 8 + 8 + 3 + 2 + 1 + 1 + 1 + 1 + 3 + 1 + 256];
    for x in &mut input[0..19] { *x = rng.next(); }
    input[28] = rng.next(); // g; all scratch lanes remain zero
    for x in &mut input[29..] { *x = rng.next(); }
    let eval = |mid: bool, undo: bool| {
        let (b, _, _, _, _, _, _, _, _, _, _, _) = build(mid, undo);
        let r = run(&b.ops, b.width() as usize, &|wd| wd.copy_from_slice(&input));
        (r, b.tof)
    };
    let (old, old_t) = eval(false, false);
    let (new, new_t) = eval(true, false);
    assert_eq!(old.q, new.q, "forward all-wire midpoint mismatch");
    assert_eq!((old.phase, new.phase), (0, 0));
    let (old_inv, _) = eval(false, true);
    let (new_inv, _) = eval(true, true);
    assert_eq!(old_inv.q, input, "old inverse identity");
    assert_eq!(new_inv.q, input, "new inverse identity");
    assert_eq!((old_inv.phase, new_inv.phase), (0, 0));
    assert!(new_t < old_t);
    eprintln!("R9-C5 ladder midpoint all-wire old/new and inverse with dirty passengers: {old_t} -> {new_t} emitted T");
}

#[test]
fn one_ghost_paired_identity() {
    let lay = lay_one();
    for seed in 0..4u64 {
        let mut b = B::new();
        let d = b.alloc_n(W1);
        let v = b.alloc_n(W1);
        let par = b.alloc();
        let foreign = b.alloc_n(256);
        let mut f = FhOne::alloc(&mut b, d, v, &lay, par, foreign.clone(), 0);
        let vl = f.v[1..257].to_vec();
        let v0 = f.v.clone();
        let mut rng = Rng::new(900 + seed);
        // Match the existing traversal/Div entry promise, not the raw field
        // draw: the caller reflects x before entering the packed machine.
        let xs: Vec<N> = (0..64).map(|_| St::new(rng.below_p()).rv).collect();
        assert!(xs.iter().all(|&x| x > N::ZERO && x < rm::p() / N::from(2u64)));
        let foreign_words: Vec<u64> = foreign.iter().map(|_| rng.next()).collect();
        f.init(&mut b, &lay);
        let trace = f.forward_ghost(&mut b, &lay);
        f.inverse_ghost(&mut b, &lay, trace);
        f.init(&mut b, &lay);
        assert_eq!(f.v, v0);
        assert_eq!(b.peak, 843);
        let r = run(&b.ops, b.width() as usize, &|wd| {
            for k in 0..64 { putv(wd, &vl, k, &xs[k]); }
            for (i, &q) in foreign.iter().enumerate() { wd[q.0 as usize] = foreign_words[i]; }
        });
        assert_eq!(r.phase, 0, "paired ghost phase seed {seed}");
        for q in 0..b.width() as usize {
            if vl.iter().chain(foreign.iter()).any(|x| x.0 as usize == q) { continue; }
            assert_eq!(r.q[q], 0, "paired ghost ancilla q{q} seed {seed}");
        }
        for k in 0..64 { assert_eq!(getn(&r.q, &vl, k), xs[k]); }
        for (i, &q) in foreign.iter().enumerate() { assert_eq!(r.q[q.0 as usize], foreign_words[i]); }
        eprintln!("paired ghost seed {seed}: value/phase/foreign/scratch/channel OK, T{}, Q{}", r.tof / 64, b.peak);
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



/// Minimum slack of every sched_one.txt window over the trajectory of input x (slack >= margin 2 for every shot inside
/// the 1M-division envelope). Returns (slacks with slot, finishing slot, first step end slot, b + k there, max stack).
fn one_slacks(x: N, w: i64, s_n: usize, rows: &[Vec<i64>]) -> (Vec<(i64, usize)>, usize, usize, u32, usize) {
    let mut st = St::new(x);
    let mut sl = vec![(i64::MAX, 0usize); 13];
    let mut upd = |i: usize, v: i64, s: usize| {
        if v < sl[i].0 {
            sl[i] = (v, s);
        }
    };
    let mut fin_slot = usize::MAX;
    let mut fse = (0usize, 0u32);
    let mut maxdep = 0;
    for s in 0..s_n {
        if st.ph == Ph::Dn {
            fin_slot = fin_slot.min(s);
        }
        let r = &rows[s];
        let running = st.ph != Ph::Dn;
        if running {
            let b1 = st.b1() as i64;
            upd(0, r[0] - (b1 + 2), s);
            upd(1, r[1] - (st.pi as i64 + 1), s);
            upd(2, (b1 + 1) - r[2], s);
            if st.ph == Ph::Out && st.k == 0 && st.b == 1 {
                upd(9, if r[9] != 0 { 99 } else { -99 }, s);
            }
            upd(11, w - (bl(&st.r) as i64 + bl(&st.cd) as i64), s);
            upd(12, w - (bl(&st.rv) as i64 + bl(&st.cv) as i64), s);
        }
        let pre_b1 = st.b1() as i64;
        let bk = st.b + st.k;
        let ev = st.fwd_at(s);
        maxdep = maxdep.max(st.stk.len());
        if running {
            let mid = if let Some((_, bv, pi)) = ev.align {
                (bv + pi) as i64
            } else if let Some(b) = ev.step_end {
                b as i64
            } else {
                pre_b1
            };
            upd(3, (mid + 1) - r[3], s);
            upd(4, r[4] - (mid + 1), s);
        }
        if let Some((b0, bv, pi)) = ev.align {
            upd(5, b0 as i64 - r[5], s);
            upd(6, r[6] - 1 - b0 as i64, s);
            let e = (bv + pi - 1) as i64;
            upd(7, e - r[7], s);
            upd(8, r[8] - 1 - e, s);
        }
        if ev.first_step_end {
            fse = (s, bk);
        }
        if st.ph == Ph::Dn && st.cnt == 0 {
            upd(10, if r[11] != 0 { 99 } else { -99 }, s);
        }
    }
    if st.ph == Ph::Dn {
        fin_slot = fin_slot.min(s_n);
    }
    (sl, fin_slot, fse.0, fse.1, maxdep)
}

fn one_sched_rows() -> (i64, usize, usize, Vec<Vec<i64>>) {
    let txt = include_str!("sched_one.txt");
    let mut lines = txt.lines();
    let hdr: Vec<i64> = lines.next().unwrap().split_whitespace().map(|v| v.parse().unwrap()).collect();
    let rows: Vec<Vec<i64>> = lines.map(|l| l.split_whitespace().map(|v| v.parse().unwrap()).collect()).collect();
    (hdr[0], hdr[1] as usize, hdr[2] as usize, rows)
}

const SLACK_NAMES: [&str; 13] = ["lv", "jw", "p1lo", "lc", "p2hi", "pb0", "pb1", "pe0", "pe1", "fin", "term", "dlane",
                                 "vlane"];

/// Check given inputs (FH1_X = comma-separated hex) against sched_one.txt.
#[test]
fn one_check_inputs() {
    let Ok(xs) = std::env::var("FH1_X") else { return };
    let (w, s_n, f1w, rows) = one_sched_rows();
    for xh in xs.split(',') {
        let x = N::from_str_radix(xh.trim(), 16).unwrap();
        let (sl, fin_slot, fs, bk, maxdep) = one_slacks(x, w, s_n, &rows);
        let mut msg = format!("x {xh}: finish {fin_slot} (S {s_n}), first step end slot {fs} (f1w {f1w}) b+k {bk}, max stack {maxdep};");
        for (i, n) in SLACK_NAMES.iter().enumerate() {
            if sl[i].0 != i64::MAX {
                msg += &format!(" {n} {}@{}", sl[i].0, sl[i].1);
            }
        }
        eprintln!("{msg}");
    }
}

/// Window tail on fresh inputs: FH1_TAIL=<divisions> FH1_SEED=<seed>. Counts divisions whose minimum window slack is
/// < 0, < 1, < 2, or that finish late / overflow the stack.
#[test]
fn one_tail() {
    let Ok(n) = std::env::var("FH1_TAIL") else { return };
    let n: usize = n.parse().unwrap();
    let seed: u64 = std::env::var("FH1_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(77);
    let (w, s_n, f1w, rows) = one_sched_rows();
    let mut rng = Rng::new(seed);
    let (mut c0, mut c1, mut c2, mut late, mut any) = (0usize, 0usize, 0usize, 0usize, 0usize);
    let mut by = vec![0usize; 13];
    for _ in 0..n {
        let x = rng.below_p();
        let (sl, fin_slot, fs, _bk, maxdep) = one_slacks(x, w, s_n, &rows);
        let m = sl.iter().map(|v| v.0).min().unwrap();
        let lt = fin_slot >= s_n || fs >= f1w || maxdep > 24;
        if lt {
            late += 1;
        }
        if lt || m < 0 {
            any += 1;
        }
        if m < 0 {
            c0 += 1;
            for (i, v) in sl.iter().enumerate() {
                if v.0 < 0 {
                    by[i] += 1;
                }
            }
        }
        if m < 1 {
            c1 += 1;
        }
        if m < 2 {
            c2 += 1;
        }
    }
    let mut msg = format!("tail: {n} divisions seed {seed}: slack<0 {c0}, <1 {c1}, <2 {c2}, late/stack {late}, either {any}; slack<0 by window:");
    for (i, nm) in SLACK_NAMES.iter().enumerate() {
        if by[i] > 0 {
            msg += &format!(" {nm} {}", by[i]);
        }
    }
    eprintln!("{msg}");
}
