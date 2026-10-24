//! Lane A1b: scratch-pool census of the froghop-one traversal (forward ghost + paired inverse recording).
//! `A1B_THR=<n>` (default POOL_1) records, for every scratch hand-out that brings the pool use to >= n, the stage, the
//! slot class tag and the source lines that hold every live scratch lane.

use super::builder::B;
use super::froghop_one::{FhOne, LayOne, SlotMode, CENSUS, CENSUS_THR, POOL_1, W1};

fn lay_one() -> LayOne {
    super::layout_one()
}

#[test]
fn a1b_pool_census() {
    let thr: usize = std::env::var("A1B_THR").ok().and_then(|v| v.parse().ok()).unwrap_or(POOL_1);
    CENSUS_THR.with(|c| c.set(thr));
    let lay = lay_one();
    let mut b = B::new();
    let d = b.alloc_n(W1);
    let v = b.alloc_n(W1);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhOne::alloc(&mut b, d, v, &lay, par, dirty, 0);
    f.init(&mut b, &lay);
    let receipts = b.fresh_bits(lay.s);
    let dl_receipts = b.fresh_bits(lay.s);
    let extra_flat = b.fresh_bits(16 * lay.s);
    let extra_receipts: Vec<[crate::circuit::BitId; 16]> = extra_flat.chunks_exact(16)
        .map(|chunk| chunk.try_into().unwrap()).collect();
    let mut maps = Vec::with_capacity(lay.s);
    let mut s5saved = Vec::new();
    for sigma in 0..lay.s {
        maps.push(f.v.clone());
        f.s5_carry_bits.clear();
        f.slot_mode(&mut b, &lay, sigma, SlotMode::ForwardGhost {
            receipt: receipts[sigma], dl_receipt: Some(dl_receipts[sigma]), extras: Some(extra_receipts[sigma]) });
        s5saved.push(f.s5_carry_bits.clone());
        b.ops.clear();
    }
    for sigma in (0..lay.s).rev() {
        f.v = maps[sigma].clone();
        f.s5_carry_bits = s5saved[sigma].clone();
        b.begin();
        f.slot_mode(&mut b, &lay, sigma, SlotMode::RecordInverseWithRepair {
            receipt: receipts[sigma], dl_receipt: Some(dl_receipts[sigma]), extras: Some(extra_receipts[sigma]) });
        let _ = b.end();
        f.v = maps[sigma].clone();
    }
    // plain slots too (the slot-level tests and the unpaired forward/inverse)
    for sigma in 0..lay.s {
        f.slot(&mut b, &lay, sigma);
        b.ops.clear();
    }
    CENSUS.with(|c| {
        for (k, n) in c.borrow().iter() {
            eprintln!("{n:6}  {k}");
        }
    });
    eprintln!("census threshold {thr}, high water {} at {}", f.hw, f.hw_at);
}

/// gadd_top1 against the integer sum and against modp_double::gadd: n = 2..=7, every Some/None addend pattern below
/// the (absent) top bit, every (t, a) input, 64 random dirty passengers. Checks the sum, addend and passengers
/// restored, carries back to 0, zero phase, and the Toffoli count equal to gadd's (one carry lane fewer).
#[test]
fn a1b_gadd_top1_exhaustive() {
    use super::froghop_one::gadd_top1;
    use super::modp_double::gadd;
    use super::tests_double::{run, Rng};
    use crate::circuit::QubitId;
    let mut rng = Rng::new(0xa1b);
    let mut cases = 0u64;
    for n in 2..=7usize {
        for pat in 0..(1usize << (n - 1)) {
            let make = |ng: usize| {
                let mut b = B::new();
                let t = b.alloc_n(n);
                let a = b.alloc_n(n - 1);
                let g = b.alloc_n(ng);
                let dirty = b.alloc_n(64);
                (b, t, a, g, dirty)
            };
            let (mut nb, nt, na, ng, nd) = make(n - 2);
            let (mut ob, ot, oa, og, od) = make(n - 1);
            let opt = |a: &[QubitId]| -> Vec<Option<QubitId>> {
                (0..n).map(|i| if i + 1 < n && (pat >> i) & 1 == 1 { Some(a[i]) } else { None }).collect()
            };
            gadd_top1(&mut nb, &nt, &opt(&na), &ng);
            gadd(&mut ob, &ot, &opt(&oa), &og);
            assert_eq!(nb.tof, ob.tof, "Toffoli n {n} pat {pat:b}");
            let dirty: Vec<u64> = (0..64).map(|_| rng.next()).collect();
            let total = 1usize << (2 * n - 1);
            for batch in 0..total.div_ceil(64) {
                let init = |wd: &mut Vec<u64>, t: &[QubitId], a: &[QubitId], d: &[QubitId]| {
                    for lane in 0..64 {
                        let x = (batch * 64 + lane) % total;
                        for (j, &q) in t.iter().enumerate() {
                            if (x >> j) & 1 != 0 { wd[q.0 as usize] |= 1u64 << lane; }
                        }
                        for (j, &q) in a.iter().enumerate() {
                            if (x >> (n + j)) & 1 != 0 { wd[q.0 as usize] |= 1u64 << lane; }
                        }
                    }
                    for (i, &q) in d.iter().enumerate() { wd[q.0 as usize] = dirty[i]; }
                };
                let r = run(&nb.ops, nb.width() as usize, &|wd| init(wd, &nt, &na, &nd));
                assert_eq!(r.phase, 0, "phase n {n} pat {pat:b} batch {batch}");
                for lane in 0..64 {
                    let x = (batch * 64 + lane) % total;
                    let tv = x & ((1 << n) - 1);
                    let av = (x >> n) & pat;
                    let want = (tv + av) & ((1 << n) - 1);
                    let got = (0..n).fold(0, |v, j| v | (((r.q[nt[j].0 as usize] >> lane) & 1) as usize) << j);
                    assert_eq!(got, want, "sum n {n} pat {pat:b} t {tv} a {av}");
                    let ga = (0..n - 1).fold(0, |v, j| v | (((r.q[na[j].0 as usize] >> lane) & 1) as usize) << j);
                    assert_eq!(ga, (x >> n) & ((1 << (n - 1)) - 1), "addend restored");
                    cases += 1;
                }
                for &q in &ng { assert_eq!(r.q[q.0 as usize], 0, "carry lane clean n {n} pat {pat:b}"); }
                for (i, &q) in nd.iter().enumerate() { assert_eq!(r.q[q.0 as usize], dirty[i], "passenger {i}"); }
            }
            let _ = (ot, oa, og, od);
        }
    }
    eprintln!("gadd_top1: {cases} cases, n = 2..=7, all addend patterns, Toffoli equal to gadd");
}
