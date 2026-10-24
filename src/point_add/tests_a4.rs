//! Lane A4 census: which bookkeeping lanes are |0> on every shot of a phase class at the step entries that bind
//! at pool 1 (S2, S3, S6, S8). Gate-level replay against refmodel_double, 64 shots per seed.

use super::builder::B;
use super::froghop_double::{FhDouble, DEPB, PIB, BB, WD};
use super::refmodel_double::{self as rmd, Ph, N};
use super::tests_double::{lay_double, run, Rng};
use crate::circuit::QubitId;

fn putv(words: &mut [u64], qs: &[QubitId], shot: usize, val: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if val.bit(i) { words[q.0 as usize] |= 1 << shot } else { words[q.0 as usize] &= !(1 << shot) }
    }
}

#[test]
fn a4_census() {
    let lay = lay_double();
    let w = WD;
    let seeds: Vec<u64> = std::env::var("A4SEEDS").ok().map(|s| s.split(',').map(|x| x.parse().unwrap()).collect())
        .unwrap_or(vec![11, 22, 33, 44]);
    let names = ["p2", "p1", "dep0", "dep1", "dep2", "dep3", "dep4", "h3", "bq5"];
    let marks = ["S2", "S3", "S6", "S8"];
    let classes = ["AL", "DV", "CO", "RT", "DN"];
    // nz[mark][class][cand] = number of (slot, seed) pairs where the candidate is nonzero on some shot of the class
    let mut nz = vec![vec![vec![0u64; names.len()]; classes.len()]; marks.len()];
    let mut seen = vec![vec![0u64; classes.len()]; marks.len()];
    let mut maxdep = [0usize; 5];
    let mut maxpi = [0i32; 5];
    for &seed in &seeds {
        let mut b = B::new();
        let d = b.alloc_n(w);
        let v = b.alloc_n(w);
        let par = b.alloc();
        let dirty = b.alloc_n(256);
        let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
        let mut rng = Rng::new(seed);
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
            for k in 0..64 { putv(wd, &vl, k, &mods[k].rv); }
            for (i, &q) in dq.iter().enumerate() { wd[q.0 as usize] = 0x9E3779B97F4A7C15u64.wrapping_mul(i as u64 + 7) ^ 0x5bd1e995; }
        }).q;
        let cand: Vec<QubitId> = vec![f.p2, f.p1, f.dep[0], f.dep[1], f.dep[2], f.dep[3], f.dep[4], f.pi[PIB - 1], f.bq[BB - 1]];
        assert_eq!(f.dep.len(), DEPB);
        for sigma in 0..lay.s {
            let cls: Vec<usize> = models.iter().map(|m| match m.ph { Ph::Al => 0, Ph::Dv => 1, Ph::Co => 2, Ph::Rt => 3, Ph::Dn => 4 }).collect();
            for (k, m) in models.iter().enumerate() {
                maxdep[cls[k]] = maxdep[cls[k]].max(m.stk.len());
                maxpi[cls[k]] = maxpi[cls[k]].max(m.pi);
            }
            let start = b.ops.len();
            f.marks.clear();
            f.slot(&mut b, &lay, sigma);
            let ops = b.ops[start..].to_vec();
            let mut pos = 0usize;
            let mut cur = words.clone();
            let mk: Vec<(&str, usize)> = f.marks.iter().map(|m| (m.0, m.1 - start)).collect();
            for (nm, at) in mk {
                if at > pos {
                    let wd = cur.clone();
                    cur = run(&ops[pos..at], nq, &move |x| x.copy_from_slice(&wd)).q;
                    pos = at;
                }
                if let Some(mi) = marks.iter().position(|x| *x == nm) {
                    for c in 0..classes.len() {
                        let mask: u64 = (0..64).filter(|&k| cls[k] == c).fold(0, |a, k| a | (1u64 << k));
                        if mask == 0 { continue; }
                        seen[mi][c] += 1;
                        for (ci, q) in cand.iter().enumerate() {
                            if cur[q.0 as usize] & mask != 0 { nz[mi][c][ci] += 1; }
                        }
                    }
                }
            }
            let wd = words.clone();
            words = run(&ops, nq, &move |x| x.copy_from_slice(&wd)).q;
            for m in models.iter_mut() { m.fwd(sigma); }
        }
    }
    eprintln!("A4 census, seeds {:?} (64 shots each): nonzero (slot,seed) count / slots with the class present", seeds);
    for (mi, mn) in marks.iter().enumerate() {
        for (c, cn) in classes.iter().enumerate() {
            if seen[mi][c] == 0 { continue; }
            let row: Vec<String> = names.iter().enumerate().map(|(ci, n)| format!("{}={}", n, nz[mi][c][ci])).collect();
            eprintln!("  {:3} entry {:2} (n={:5}): {}", mn, cn, seen[mi][c], row.join(" "));
        }
    }
    eprintln!("  max depth per class {:?}, max pi per class {:?}", maxdep, maxpi);
}

// ---------------------------------------------------------------------------------------------- TTK vs Cuccaro
use super::mask::*;
use super::builder::G;
use crate::circuit::NO_QUBIT;

fn getv(words: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (words[q.0 as usize] >> shot) & 1 == 1 { v |= N::from(1u64) << i; }
    }
    v
}

struct Cfg { f0: bool, late: bool, temp: bool, two: bool }

/// Builds the layout: 40 lanes t, s; sources; scratch. Returns (t, s, srcs, sc, regs to randomize)
fn lay40(b: &mut B, cfg: &Cfg) -> (Vec<QubitId>, Vec<QubitId>, Vec<Src>, Mscr, Vec<(Vec<QubitId>, usize)>) {
    let t = b.alloc_n(40);
    let s = b.alloc_n(40);
    let v2 = b.alloc_n(4);
    let v = b.alloc_n(6);
    let pre = b.alloc_n(5);
    let dirty = b.alloc_n(8);
    let f = b.alloc();
    let tq = if cfg.temp { b.alloc() } else { NO_QUBIT };
    let sc = Mscr { f, t: tq, gf: tq, chain: pre.clone(), dirty: dirty.clone() };
    let mut srcs = vec![];
    if cfg.two {
        srcs.push(Src { lo: 0, hi: 9, v: v2.clone(), a: 0, d: 1, pre: pre[..3].to_vec(), late: false, hk: None });
    }
    srcs.push(Src { lo: 24, hi: 40, v: v.clone(), a: -1, d: 1, pre: pre.clone(), late: cfg.late, hk: None });
    (t, s, srcs, sc, vec![(v2, 9), (v, 40), (dirty, 0)])
}

fn rnd_init(cfg_seed: u64, t: &[QubitId], s: &[QubitId], regs: &[(Vec<QubitId>, usize)], extra: &[QubitId]) -> impl Fn(&mut Vec<u64>) {
    let t = t.to_vec(); let s = s.to_vec(); let regs = regs.to_vec(); let extra = extra.to_vec();
    move |w: &mut Vec<u64>| {
        let mut rng = Rng::new(cfg_seed);
        for k in 0..64 {
            let mut tv = rng.below(40);
            let sv = rng.below(40);
            if rng.next() % 3 == 0 { let m: N = ((N::from(1u64) << 40) - N::from(1u64)) ^ ((N::from(1u64) << (rng.next() % 30) as usize) - N::from(1u64)); tv = (tv & !m) | (sv & m); }
            putv(w, &t, k, &tv); putv(w, &s, k, &sv);
            for (r, range) in &regs {
                let val = if *range > 0 { N::from(rng.next() % (*range as u64 + 4)) } else { rng.below(r.len()) };
                putv(w, r, k, &(val & ((N::from(1u64) << r.len()) - N::from(1u64))));
            }
            for &q in &extra { if rng.next() & 1 == 1 { w[q.0 as usize] |= 1 << k; } }
        }
    }
}

#[test]
fn a4_ttk_matches_cuccaro() {
    for seed in 0..6u64 {
        for &(f0, late, temp, two) in &[(false, false, false, true), (false, false, true, true), (true, false, false, false),
                                         (true, false, true, false), (true, true, false, false), (true, true, true, false)] {
            let cfg = Cfg { f0, late, temp, two };
            // ---- compare + conditional subtract (P1 pattern; no late sources) / compare only (late)
            for mode in 0..2 {
                if late && mode == 0 { continue; }
                let mut bc = B::new();
                let (t, s, srcs, sc, regs) = lay40(&mut bc, &cfg);
                let c0 = bc.alloc();
                let g = bc.alloc();
                let x = bc.alloc();
                let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0, cmpl: true, sc: &sc, keep_f: true };
                // Cuccaro: mode 0: up, x ^= g & !ct, down(x); mode 1 (compare / COEF form): x ^= g & ct, up^-1 after
                let ru = mup(&mut bc, &ld);
                let rd = mdown(&mut bc, &ld, if mode == 0 { Some(x) } else { None });
                bc.play(&ru, false);
                let ct = top_carry(&ld);
                if mode == 0 { bc.x(ct); bc.ccx(g, ct, x); bc.x(ct); bc.play(&rd, false); }
                else { bc.ccx(g, ct, x); bc.play(&ru, true); }
                // TTK on an identical allocation
                let mut bt = B::new();
                let (t2, s2, srcs2, sc2, _) = lay40(&mut bt, &cfg);
                let _c0 = bt.alloc();
                let g2 = bt.alloc();
                let x2 = bt.alloc();
                assert_eq!((t2[0], g2, x2), (t[0], g, x));
                let ld2 = Lad { t: &t2, s: &s2, c0: NO_QUBIT, srcs: &srcs2, f0, cmpl: true, sc: &sc2, keep_f: true };
                let dirty2 = sc2.dirty.clone();
                if mode == 0 {
                    // x = g & !ct = g ^ g&A ^ g&T
                    if let Some(a) = top_a(&ld2) { bt.ccx(g2, a, x2); }
                    let topf = |b: &mut B, terms: &[Vec<(QubitId, bool)>]| {
                        for tm in terms { let mut l = vec![(g2, false)]; l.extend(tm.iter().cloned()); mc_xor(b, &l, x2, &[], &dirty2); }
                    };
                    let ru2 = mup_t(&mut bt, &ld2, Some(&topf));
                    let rd2 = mdown_t(&mut bt, &ld2, Some(x2));
                    bt.play(&ru2, false);
                    bt.cx(g2, x2);
                    bt.play(&rd2, false);
                } else {
                    let topf = |b: &mut B, terms: &[Vec<(QubitId, bool)>]| {
                        for tm in terms { let mut l = vec![(g2, false)]; l.extend(tm.iter().cloned()); mc_xor(b, &l, x2, &[], &dirty2); }
                    };
                    let ruw = mup_t(&mut bt, &ld2, Some(&topf));
                    let run_ = mup_t(&mut bt, &ld2, None);
                    bt.play(&ruw, false);
                    bt.play(&run_, true);
                    if let Some(a) = top_a(&ld2) { bt.ccx(g2, a, x2); }
                }
                let nq = bc.width().max(bt.width()) as usize;
                let init = rnd_init(1000 * seed + mode as u64 + 7 * (f0 as u64) + 13 * (late as u64), &t, &s, &regs, &[g]);
                let rc = run(&bc.ops, nq, &init);
                let rt = run(&bt.ops, nq, &init);
                assert_eq!(rt.phase, 0, "ttk phase seed {seed} f0 {f0} late {late} temp {temp} mode {mode}");
                assert_eq!(rc.phase, 0, "cuccaro phase");
                for q in 0..nq { assert_eq!(rt.q[q], rc.q[q], "qubit {q} differs seed {seed} f0 {f0} late {late} temp {temp} two {two} mode {mode}"); }
                let _ = getv(&rt.q, &t, 0);
            }
            if late { continue; }
            // ---- COEF form (P2 pattern): (T, beta) -> (T + beta S, 0) with the erase beta ^= ep & !ct at the top
            let mut bc = B::new();
            let (t, s, srcs, sc, regs) = lay40(&mut bc, &cfg);
            let c0 = bc.alloc();
            let g = bc.alloc();
            let ep = bc.alloc();
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0, cmpl: true, sc: &sc, keep_f: true };
            let ru = mup(&mut bc, &ld);
            let rd = mdown(&mut bc, &ld, Some(g));
            bc.play(&rd, true);
            let ct = top_carry(&ld);
            bc.x(ct); bc.ccx(ep, ct, g); bc.x(ct);
            bc.play(&ru, true);
            let mut bt = B::new();
            let (t2, s2, srcs2, sc2, _) = lay40(&mut bt, &cfg);
            let _c0 = bt.alloc();
            let g2 = bt.alloc();
            let ep2 = bt.alloc();
            let ld2 = Lad { t: &t2, s: &s2, c0: NO_QUBIT, srcs: &srcs2, f0, cmpl: true, sc: &sc2, keep_f: true };
            let dirty2 = sc2.dirty.clone();
            let topf = |b: &mut B, terms: &[Vec<(QubitId, bool)>]| {
                for tm in terms { let mut l = vec![(ep2, false)]; l.extend(tm.iter().cloned()); mc_xor(b, &l, g2, &[], &dirty2); }
            };
            let ruw = mup_t(&mut bt, &ld2, Some(&topf));
            let rd2 = mdown_t(&mut bt, &ld2, Some(g2));
            bt.play(&rd2, true);
            bt.play(&ruw, true);
            if let Some(a) = top_a(&ld2) { bt.ccx(ep2, a, g2); }
            bt.cx(ep2, g2);
            let nq = bc.width().max(bt.width()) as usize;
            let init = rnd_init(5000 + seed * 31 + 3 * (f0 as u64), &t, &s, &regs, &[g, ep]);
            let rc = run(&bc.ops, nq, &init);
            let rt = run(&bt.ops, nq, &init);
            assert_eq!(rt.phase, rc.phase, "coef phase seed {seed} f0 {f0} temp {temp}");
            for q in 0..nq { assert_eq!(rt.q[q], rc.q[q], "coef qubit {q} differs seed {seed} f0 {f0} temp {temp} two {two}"); }
            let _: Vec<G> = vec![];
        }
    }
    eprintln!("TTK masked ladders match Cuccaro masked ladders bit for bit (6 seeds x 6 configs x 3 forms)");
}
