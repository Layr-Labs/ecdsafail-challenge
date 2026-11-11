//! Gnueggredt (lane T1c): the signed-batch high part cut at lane k + CAP in both the forward nu increment and the
//! inverse explicit tails. Checks on random shots (64 per run, several runs):
//!   1. forward then inverse (deferred modes 1 and 2) restores v exactly, every scratch lane returns to 0 and the
//!      phase word is 0, for CAP = 0 (the tree) and for small CAPs (the cut pair must stay an exact inverse);
//!   2. forward only: the cut value differs from the exact one only on lanes >= k + CAP, and only on shots whose exact
//!      carry/borrow out of lane k travels CAP lanes or more (counted, with the lane-k carry rate).

use super::builder::B;
use super::signed_batch::{forward_walk, inverse_walk, Shape, GNUEGG_TEST};
use super::tests_frogdrop::{run, Rng};
use crate::circuit::QubitId;

struct Lay { s: Shape, e: QubitId, all_scratch: Vec<QubitId>, dirty: Vec<QubitId> }

fn layout(b: &mut B, top: usize, m: usize, lo: usize, hi: usize, nbank: usize, nhigh: usize, chunk: usize, inv: bool) -> Lay {
    let v = b.alloc_n(top);
    let source = b.alloc_n(m);
    let bank = b.alloc_n(nbank);
    let c0 = b.alloc(); let h = b.alloc(); let nu = b.alloc(); let sig = b.alloc(); let e = b.alloc();
    let dirty = b.alloc_n(128);
    let k = hi + m + 1;
    assert!(k < top);
    let s = Shape { v, source, enables: vec![e; hi - lo + 1], bank: bank.clone(), high_bank: bank[..nhigh].to_vec(),
                    dirty: dirty.clone(), c0, h, nu, sig, lo, hi, k, inverse: inv, chunks: vec![chunk; hi - lo + 1] };
    let mut all_scratch = bank; all_scratch.extend([c0, h, nu, sig]);
    Lay { s, e, all_scratch, dirty }
}

fn build(cap: usize, round_trip: bool, top: usize, m: usize, lo: usize, hi: usize, nbank: usize, nhigh: usize, chunk: usize)
    -> (B, Lay) { build2(cap, round_trip, top, m, lo, hi, nbank, nhigh, chunk, false, false) }

/// inv: the batch's direction flag (true = the divide, i.e. the multiply's recorded rows played inverted in the
/// forward walk); e_rand: the enable lane is a random per-shot input (rows of a shot all off or all on) instead of 1.
fn build2(cap: usize, round_trip: bool, top: usize, m: usize, lo: usize, hi: usize, nbank: usize, nhigh: usize, chunk: usize,
          inv: bool, e_rand: bool) -> (B, Lay) {
    GNUEGG_TEST.with(|c| c.set(Some((cap, 0, usize::MAX))));
    let mut b = B::new();
    let l = layout(&mut b, top, m, lo, hi, nbank, nhigh, chunk, inv);
    if !e_rand { b.x(l.e); }
    b.deferred_forward();
    let masks = forward_walk(&mut b, &l.s, |_, _| {});
    b.flush_dependency();
    if round_trip {
        b.deferred_inverse();
        inverse_walk(&mut b, &l.s, masks, |_, _| {});
        b.flush_dependency();
        b.deferred_finish();
    }
    if !e_rand { b.x(l.e); }
    b.flush_dependency();
    GNUEGG_TEST.with(|c| c.set(None));
    (b, l)
}

fn words(l: &Lay, seed: u64) -> Vec<(QubitId, u64)> {
    let mut r = Rng::new(seed);
    let mut w = vec![];
    for &q in l.s.v.iter().chain(&l.s.source).chain(&l.dirty) { w.push((q, r.next())); }
    w
}
fn words_e(l: &Lay, seed: u64) -> Vec<(QubitId, u64)> {
    let mut w = words(l, seed);
    w.push((l.e, Rng::new(seed ^ 0xe).next()));
    w
}

fn sim(b: &B, init: &[(QubitId, u64)]) -> super::tests_frogdrop::Sim {
    run(&b.ops, b.width() as usize, &|w: &mut Vec<u64>| { for &(q, x) in init { w[q.0 as usize] = x; } })
}

#[test]
fn gnuegg_round_trip_and_cut_value() {
    // geometry: top 120, m 20, batch rows 30..=41 (k = 62, top - k = 58); bank 20 (chunk 4: 5 flags, 15 work lanes),
    // high bank 8: exercises the clean prefix, the conditional increment and the dirty suffix.
    let (top, m, lo, hi, nbank, nhigh, chunk) = (120usize, 20usize, 30usize, 41usize, 20usize, 8usize, 4usize);
    let mut tof = vec![];
    for &cap in &[0usize, 4, 8, 12, 40, 58, 80] {
        let (b, l) = build(cap, true, top, m, lo, hi, nbank, nhigh, chunk);
        tof.push((cap, b.tof));
        for seed in 0..8u64 {
            let init = words(&l, 1000 * cap as u64 + seed);
            let r = sim(&b, &init);
            assert_eq!(r.phase, 0, "phase cap={cap} seed={seed}");
            for &(q, x) in &init { assert_eq!(r.q[q.0 as usize], x, "value/passenger not restored cap={cap} seed={seed}"); }
            for &q in &l.all_scratch { assert_eq!(r.q[q.0 as usize], 0, "scratch not clean cap={cap} seed={seed}"); }
        }
    }
    eprintln!("GNUEGG_ROUNDTRIP_PASS tof(cap)={:?}", tof);
    // forward only: cut value vs exact value
    let (be, le) = build(0, false, top, m, lo, hi, nbank, nhigh, chunk);
    let k = le.s.k;
    for &cap in &[4usize, 8, 12] {
        let (bc, lc) = build(cap, false, top, m, lo, hi, nbank, nhigh, chunk);
        let (mut shots, mut diff, mut carry_k, mut long) = (0u64, 0u64, 0u64, 0u64);
        for seed in 0..64u64 {
            let init = words(&le, 77 + seed);
            let init_c: Vec<(QubitId, u64)> = init.iter().map(|&(q, x)| (q, x)).collect();
            let re = sim(&be, &init);
            let rc = sim(&bc, &init_c);
            for shot in 0..64 {
                shots += 1;
                let bit = |w: &Vec<u64>, q: QubitId| (w[q.0 as usize] >> shot) & 1;
                let mut d = false;
                for (j, (&qe, &qc)) in le.s.v.iter().zip(&lc.s.v).enumerate() {
                    let (x, y) = (bit(&re.q, qe), bit(&rc.q, qc));
                    if x != y { d = true; assert!(j >= (k + cap).min(top), "cut changed lane {j} < k+cap (cap={cap})"); }
                }
                // exact high-part change: did lanes [k, top) change, and how far did the change reach
                let mut hi_changed = 0usize;
                for j in k..top {
                    let q = le.s.v[j];
                    let x0 = (init.iter().find(|p| p.0 == q).unwrap().1 >> shot) & 1;
                    if bit(&re.q, q) != x0 { hi_changed = j - k + 1; }
                }
                if hi_changed > 0 { carry_k += 1; }
                if hi_changed > cap { long += 1; }
                if d { diff += 1; }
            }
        }
        eprintln!("GNUEGG_CUT cap={cap}: shots {shots} carry-at-k {carry_k} exact-chain>cap {long} cut-value-differs {diff}");
        assert_eq!(diff, long, "cut value must differ exactly on the shots whose exact high change reaches past k+cap");
    }
    eprintln!("GNUEGG_CUT_PASS");
}

#[test]
fn gnuegg_divide_direction_and_enables() {
    // same checks for the divide direction (Shape.inverse = true) and a random per-shot enable lane, two geometries
    // (the second with a short top - k = 41 so a CAP 40 cut removes one lane, and a bank too small for clean tails).
    for &(top, m, lo, hi, nbank, nhigh, chunk) in &[(120usize, 20usize, 30usize, 41usize, 20usize, 8usize, 4usize),
                                                    (100, 24, 20, 34, 22, 4, 6)] {
        for &inv in &[false, true] {
            for &cap in &[0usize, 3, 8, 40] {
                let (b, l) = build2(cap, true, top, m, lo, hi, nbank, nhigh, chunk, inv, true);
                for seed in 0..6u64 {
                    let init = words_e(&l, 31 * cap as u64 + seed + if inv { 500 } else { 0 });
                    let r = sim(&b, &init);
                    assert_eq!(r.phase, 0, "phase top={top} inv={inv} cap={cap} seed={seed}");
                    for &(q, x) in &init { assert_eq!(r.q[q.0 as usize], x, "not restored top={top} inv={inv} cap={cap}"); }
                    for &q in &l.all_scratch { assert_eq!(r.q[q.0 as usize], 0, "scratch top={top} inv={inv} cap={cap}"); }
                }
            }
            let (be, le) = build2(0, false, top, m, lo, hi, nbank, nhigh, chunk, inv, true);
            let k = le.s.k;
            for &cap in &[3usize, 8] {
                let (bc, _) = build2(cap, false, top, m, lo, hi, nbank, nhigh, chunk, inv, true);
                let (mut diff, mut long, mut carry_k) = (0u64, 0u64, 0u64);
                for seed in 0..16u64 {
                    let init = words_e(&le, 900 + seed);
                    let (re, rc) = (sim(&be, &init), sim(&bc, &init));
                    for shot in 0..64 {
                        let bit = |w: &Vec<u64>, q: QubitId| (w[q.0 as usize] >> shot) & 1;
                        let mut d = false;
                        for (j, &q) in le.s.v.iter().enumerate() {
                            if bit(&re.q, q) != bit(&rc.q, q) { d = true; assert!(j >= (k + cap).min(top), "lane {j} < k+cap"); }
                        }
                        let mut reach = 0usize;
                        for j in k..top { let q = le.s.v[j]; let x0 = (init.iter().find(|p| p.0 == q).unwrap().1 >> shot) & 1;
                                          if bit(&re.q, q) != x0 { reach = j - k + 1; } }
                        if reach > 0 { carry_k += 1; }
                        if reach > cap { long += 1; }
                        if d { diff += 1; }
                    }
                }
                eprintln!("GNUEGG_DIV top={top} inv={inv} cap={cap}: shots 1024 carry-at-k {carry_k} chain>cap {long} differs {diff}");
                assert_eq!(diff, long);
            }
        }
    }
    eprintln!("GNUEGG_DIV_PASS");
}

#[test]
fn gnuegg_planted_long_chains() {
    // worst structural case: the high part [k, top) planted as a sign-extension run (all ones, or all zeros) on every
    // shot, so any carry (resp. borrow) out of lane k runs to the top. At CAP 40 (top - k = 58) every such shot must give
    // a cut value that differs exactly on lanes >= k + 40, the round trip must stay exact, and nothing else may change.
    let (top, m, lo, hi, nbank, nhigh, chunk) = (120usize, 20usize, 30usize, 41usize, 20usize, 8usize, 4usize);
    let cap = 40usize;
    for &inv in &[false, true] {
        for &ones in &[true, false] {
            let (be, le) = build2(0, false, top, m, lo, hi, nbank, nhigh, chunk, inv, true);
            let (bc, _) = build2(cap, false, top, m, lo, hi, nbank, nhigh, chunk, inv, true);
            let (brt, lrt) = build2(cap, true, top, m, lo, hi, nbank, nhigh, chunk, inv, true);
            let k = le.s.k;
            let (mut carry_k, mut long, mut diff) = (0u64, 0u64, 0u64);
            for seed in 0..16u64 {
                let mut init = words_e(&le, 4242 + seed + if inv { 100 } else { 0 } + if ones { 0 } else { 50 });
                for p in init.iter_mut() { if le.s.v[k..].contains(&p.0) { p.1 = if ones { u64::MAX } else { 0 }; } }
                let (re, rc) = (sim(&be, &init), sim(&bc, &init));
                let rr = sim(&brt, &init);
                assert_eq!(rr.phase, 0, "planted round trip phase inv={inv} ones={ones}");
                for &(q, x) in &init { assert_eq!(rr.q[q.0 as usize], x, "planted round trip value inv={inv} ones={ones}"); }
                for &q in &lrt.all_scratch { assert_eq!(rr.q[q.0 as usize], 0, "planted round trip scratch"); }
                for shot in 0..64 {
                    let bit = |w: &Vec<u64>, q: QubitId| (w[q.0 as usize] >> shot) & 1;
                    let mut d = false;
                    for (j, &q) in le.s.v.iter().enumerate() {
                        if bit(&re.q, q) != bit(&rc.q, q) { d = true; assert!(j >= k + cap, "planted: lane {j} < k+cap"); }
                    }
                    let mut reach = 0usize;
                    for j in k..top { let q = le.s.v[j]; let x0 = (init.iter().find(|p| p.0 == q).unwrap().1 >> shot) & 1;
                                      if bit(&re.q, q) != x0 { reach = j - k + 1; } }
                    if reach > 0 { carry_k += 1; }
                    if reach > cap { long += 1; }
                    if d { diff += 1; }
                }
            }
            eprintln!("GNUEGG_PLANT inv={inv} high={}: shots 1024 change-at-k {carry_k} chain>40 {long} cut-differs {diff}",
                      if ones { "ones" } else { "zeros" });
            assert_eq!(diff, long, "cut must differ exactly on the planted long chains");
        }
    }
    eprintln!("GNUEGG_PLANT_PASS");
}
