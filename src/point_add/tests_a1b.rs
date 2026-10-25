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

/// gadd_top1_jit against the integer sum and gadd_top1's Toffoli count + one AND per AND bit (+1 below lane n-2):
/// n = 2..=6 (the traversal uses n = 6), every No / Q / And pattern below the top bit (And bits read two input wires x_i, y_i), every input.
#[test]
fn a1b_gadd_top1_jit_exhaustive() {
    use super::froghop_one::{gadd_top1_jit, Ad};
    use super::tests_double::{run, Rng};
    use crate::circuit::QubitId;
    let mut rng = Rng::new(0xa1b2);
    let mut cases = 0u64;
    for n in 2..=6usize {
        let m = n - 1; // addend bits below the top
        for pat in 0..3usize.pow(m as u32) {
            let kinds: Vec<usize> = (0..m).map(|i| (pat / 3usize.pow(i as u32)) % 3).collect();
            let mut b = B::new();
            let t = b.alloc_n(n);
            let x = b.alloc_n(m);
            let y = b.alloc_n(m);
            let g = b.alloc_n(n - 2);
            let tmp = b.alloc();
            let dirty = b.alloc_n(32);
            let mut a: Vec<Ad> = (0..m).map(|i| match kinds[i] { 0 => Ad::No, 1 => Ad::Q(x[i]), _ => Ad::And(x[i], y[i]) })
                .collect();
            a.push(Ad::No);
            gadd_top1_jit(&mut b, &t, &a, &g, tmp);
            let nq = kinds.iter().filter(|&&k| k != 0).count();
            let nand = kinds.iter().filter(|&&k| k == 2).count();
            let nand_low = kinds[..m - 1].iter().filter(|&&k| k == 2).count();
            // Toffoli: one per non-trivial carry lane / top toggle (as gadd_top1) plus the JIT ANDs
            let carries = {
                let mut c = false;
                let mut cnt = 0;
                for i in 0..m {
                    let has = kinds[i] != 0;
                    if has || c { cnt += 1; c = true; }
                }
                cnt
            };
            assert_eq!(b.tof as usize, carries + nand + nand_low, "Toffoli n {n} kinds {kinds:?}");
            let _ = nq;
            let dv: Vec<u64> = (0..32).map(|_| rng.next()).collect();
            let bits = n + 2 * m;
            let total = 1usize << bits;
            for batch in 0..total.div_ceil(64) {
                let init = |wd: &mut Vec<u64>| {
                    for lane in 0..64 {
                        let v = (batch * 64 + lane) % total;
                        for (j, &q) in t.iter().chain(x.iter()).chain(y.iter()).enumerate() {
                            if (v >> j) & 1 != 0 { wd[q.0 as usize] |= 1u64 << lane; }
                        }
                    }
                    for (i, &q) in dirty.iter().enumerate() { wd[q.0 as usize] = dv[i]; }
                };
                let r = run(&b.ops, b.width() as usize, &init);
                assert_eq!(r.phase, 0, "phase n {n} kinds {kinds:?}");
                for lane in 0..64 {
                    let v = (batch * 64 + lane) % total;
                    let tv = v & ((1 << n) - 1);
                    let xv = (v >> n) & ((1 << m) - 1);
                    let yv = (v >> (n + m)) & ((1 << m) - 1);
                    let mut av = 0usize;
                    for i in 0..m {
                        let bit = match kinds[i] { 0 => 0, 1 => (xv >> i) & 1, _ => (xv >> i) & (yv >> i) & 1 };
                        av |= bit << i;
                    }
                    let want = (tv + av) & ((1 << n) - 1);
                    let getq = |qs: &[QubitId]| (0..qs.len()).fold(0usize, |acc, j| acc | (((r.q[qs[j].0 as usize] >> lane) & 1) as usize) << j);
                    assert_eq!(getq(&t), want, "sum n {n} kinds {kinds:?} t {tv} a {av}");
                    assert_eq!(getq(&x), xv, "x restored");
                    assert_eq!(getq(&y), yv, "y restored");
                    cases += 1;
                }
                for &q in g.iter().chain(std::iter::once(&tmp)) { assert_eq!(r.q[q.0 as usize], 0, "scratch clean n {n}"); }
                for (i, &q) in dirty.iter().enumerate() { assert_eq!(r.q[q.0 as usize], dv[i], "passenger {i}"); }
            }
        }
    }
    eprintln!("gadd_top1_jit: {cases} cases, n = 2..=6, all No/Q/And patterns");
}

/// Short retained decoder (mask::short_pre) against the ordinary retained decoder in the traversal's ladder shapes,
/// all wires compared: (a) S2 form: pi-parity source (xor_into prefix) + bq source d = +1, mid up pass, gated down
/// pass, inverse; (b) S5 / S7 form: one bq source d = -1, forward path rd^-1 ru^-1 from a held decoder start
/// (mup_mid_from) then clear_onehot_dec, as the paired inverse records it; (c) the same with an ordinary start.
/// 6-bit sources over windows that cover only part of the value range, random values (so most shots are outside the
/// window), random targets / sources / gates, 256 dirty passengers.
#[test]
fn a1b_short_decoder_ladder() {
    use super::mask::{clear_onehot_dec, mdown_mid, mup_mid, mup_mid_from, short_pre, Lad, Mscr, Src};
    use super::tests_double::{run, Rng};
    let l_n = 24usize;
    for form in 0..3usize {
        for seed in 0..12u64 {
            let build = |short: bool| {
                let mut b = B::new();
                let t = b.alloc_n(l_n);
                let s = b.alloc_n(l_n);
                let bq = b.alloc_n(6);
                let pi = b.alloc_n(4);
                let pre = b.alloc_n(5);
                let pa = b.alloc_n(1);
                let c0 = b.alloc();
                let mf = b.alloc_n(2);
                let g = b.alloc();
                let dirty = b.alloc_n(256);
                let own = if short { pre[..4].to_vec() } else { pre.clone() };
                let spre = if short { short_pre(&own) } else { own.clone() };
                let (lo, hi, a, d) = match form { 0 => (3usize, l_n, 2isize, 1isize), _ => (2usize, 20usize, 40isize, -1isize) };
                let mut srcs = vec![];
                if form == 0 {
                    srcs.push(Src { lo: 0, hi: 11, v: pi.clone(), a: 1, d: 0, pre: vec![pa[0], mf[1]], late: false });
                }
                srcs.push(Src { lo, hi, v: bq.clone(), a, d, pre: spre.clone(), late: false });
                let ms = Mscr { f: mf[0], t: mf[1], gf: mf[1], chain: own.clone() };
                let f0 = form != 0;
                let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0, cmpl: true, sc: &ms, g: &[] };
                b.begin();
                if form == 0 {
                    let ru = mup_mid(&mut b, &ld);
                    let rd = mdown_mid(&mut b, &ld, Some(g));
                    b.play(&ru, false);
                    b.play(&rd, false);
                } else {
                    let start = (lo..hi).find_map(|l| {
                        let j = a + d * l as isize;
                        (j >= 0 && j < 64).then_some(j as usize)
                    }).unwrap();
                    let ru = if form == 1 { mup_mid_from(&mut b, &ld, start) } else { mup_mid(&mut b, &ld) };
                    let rd = mdown_mid(&mut b, &ld, Some(g));
                    b.play(&rd, true);
                    b.play(&ru, true);
                    if form == 1 { clear_onehot_dec(&mut b, &bq, &spre, start); }
                }
                let rec = b.end();
                b.play(&rec, false);
                (b, rec, t, s, bq, pi, g, dirty)
            };
            let (ob, orec, t, s, bq, pi, g, dirty) = build(false);
            let (nb, nrec, _, _, _, _, _, _) = build(true);
            let mut rng = Rng::new(0x5a0 + 97 * seed + form as u64);
            let mut input = vec![0u64; ob.width().max(nb.width()) as usize];
            for &q in t.iter().chain(s.iter()).chain(bq.iter()).chain(pi.iter()).chain(std::iter::once(&g))
                .chain(dirty.iter()) {
                input[q.0 as usize] = rng.next();
            }
            if seed % 3 == 0 {
                // concentrate bq inside the window on half the shots: high bits 0
                for &q in &bq[4..] { input[q.0 as usize] &= rng.next(); }
            }
            let o = run(&ob.ops, input.len(), &|wd| wd.copy_from_slice(&input));
            let n = run(&nb.ops, input.len(), &|wd| wd.copy_from_slice(&input));
            assert_eq!((o.phase, n.phase), (0, 0), "phase form {form} seed {seed}");
            assert_eq!(o.q, n.q, "all wires form {form} seed {seed}");
            if form == 0 {
                // the inverse returns every wire
                let mut bi = B::new();
                let _ = bi.alloc_n(input.len());
                bi.play(&nrec, false);
                bi.play(&nrec, true);
                let r = run(&bi.ops, input.len(), &|wd| wd.copy_from_slice(&input));
                assert_eq!(r.q, input, "short inverse identity seed {seed}");
                assert_eq!(r.phase, 0);
            }
            let _ = orec;
            if seed == 0 {
                eprintln!("short decoder form {form}: retained {} T, short {} T", ob.tof, nb.tof);
            }
        }
    }
}

/// ctrl_neg (z <- ctl ? p - z : z, i.e. complement then subtract c - 1 at lane 4) on short carry pools: the
/// uncontrolled form's constant has bit 28 set (lane 32), so from pool 28 down add_small_head adds the high bit apart
/// (lane A1b). Pools GLOW..=33, ctl None / random, 64 inputs per batch (edges + random z in [1, p)), dirty passengers
/// restored, carry pool and c0 / k clean, zero phase, integer model exact.
#[test]
fn a1b_ctrl_neg_short_pools() {
    use super::modp_double::{ctrl_neg, Ms, GLOW};
    use super::refmodel_one::{p, N};
    use super::tests_double::{run, Rng};
    let pp = p();
    let mut rng = Rng::new(0xa1b3);
    let mut checked = 0usize;
    for pool in GLOW..=33usize {
        for controlled in [false, true] {
            for batch in 0..4 {
                let mut b = B::new();
                let z = b.alloc_n(256);
                let dirty = b.alloc_n(256);
                let c = b.alloc();
                let ms = Ms::alloc_pool(&mut b, pool);
                ctrl_neg(&mut b, &ms, &z, controlled.then_some(c), &dirty);
                let mut zv = vec![N::ZERO; 64];
                for (i, v) in zv.iter_mut().enumerate() {
                    *v = match (batch, i) {
                        (0, 0) => N::from(1u64),
                        (0, 1) => pp - N::from(1u64),
                        (0, 2) => N::from((1u64 << 32) + 976),
                        (0, 3) => pp - N::from((1u64 << 32) + 977),
                        _ => loop {
                            let mut x = N::ZERO;
                            for l in 0..4 { x |= N::from(rng.next()) << (64 * l); }
                            let x = x % pp;
                            if x != N::ZERO { break x; }
                        },
                    };
                }
                let cw = rng.next();
                let dv: Vec<u64> = (0..256).map(|_| rng.next()).collect();
                let init = |wd: &mut Vec<u64>| {
                    for (j, &q) in z.iter().enumerate() {
                        let mut w = 0u64;
                        for s in 0..64 { if zv[s].bit(j) { w |= 1u64 << s; } }
                        wd[q.0 as usize] = w;
                    }
                    for (i, &q) in dirty.iter().enumerate() { wd[q.0 as usize] = dv[i]; }
                    wd[c.0 as usize] = cw;
                };
                let r = run(&b.ops, b.width() as usize, &init);
                assert_eq!(r.phase, 0, "phase pool {pool}");
                for s in 0..64 {
                    let on = !controlled || (cw >> s) & 1 == 1;
                    let want = if on { pp - zv[s] } else { zv[s] };
                    let mut got = N::ZERO;
                    for (j, &q) in z.iter().enumerate() {
                        if (r.q[q.0 as usize] >> s) & 1 == 1 { got |= N::from(1u64) << j; }
                    }
                    assert_eq!(got, want, "pool {pool} controlled {controlled} shot {s}");
                    checked += 1;
                }
                for (i, &q) in dirty.iter().enumerate() { assert_eq!(r.q[q.0 as usize], dv[i], "passenger {i} pool {pool}"); }
                assert_eq!(r.q[c.0 as usize], cw, "control");
                for &q in ms.g.iter().chain([ms.c0, ms.k].iter()) { assert_eq!(r.q[q.0 as usize], 0, "scratch pool {pool}"); }
            }
        }
    }
    eprintln!("ctrl_neg short pools {GLOW}..=33: {checked} shots exact");
}
