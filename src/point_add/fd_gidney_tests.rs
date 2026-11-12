//! TRACK2 tests of the Gidney constant adder: value, phase, lanes returned clean, Toffoli count, sabotaged control.
use super::*;
use crate::point_add::tests_frogdrop::{run, Rng};

struct Out { ok: bool, phase: u64, tof: u64 }

/// one adder circuit on n lanes, constant kwin, control mode `cm` (0: none, 1: ctl); 64 shots.
/// x: per-shot target values (< 2^n, n <= 64); returns whether every shot is exactly right.
fn case(n: usize, kwin: u128, cm: usize, xs: &[u128; 64], cw: u64, rng: &mut Rng, sabotage: bool) -> Out {
    SABOTAGE.with(|s| s.set(sabotage));
    let mut b = B::new();
    let t = b.alloc_n(n);
    let c = b.alloc();
    let cl = b.alloc_n(2);
    let d = b.alloc_n(n - 2);
    gidney_add(&mut b, &t, kwin, if cm == 1 { Some(c) } else { None }, [cl[0], cl[1]], &d);
    b.flush_dependency();
    let tof = b.tof;
    let nq = b.width() as usize;
    let dw: Vec<u64> = (0..n - 2).map(|_| rng.next()).collect();
    let sim = run(&b.ops, nq, &|w: &mut Vec<u64>| {
        for s in 0..64 { for i in 0..n { if (xs[s] >> i) & 1 == 1 { w[t[i].0 as usize] |= 1u64 << s; } } }
        w[c.0 as usize] = cw;
        for j in 0..n - 2 { w[d[j].0 as usize] = dw[j]; }
    });
    SABOTAGE.with(|s| s.set(false));
    let mask: u128 = (1u128 << n) - 1;
    let mut ok = sim.q[cl[0].0 as usize] == 0 && sim.q[cl[1].0 as usize] == 0 && sim.q[c.0 as usize] == cw;
    for j in 0..n - 2 { ok &= sim.q[d[j].0 as usize] == dw[j]; }
    for s in 0..64 {
        let mut v = 0u128;
        for i in 0..n { if (sim.q[t[i].0 as usize] >> s) & 1 == 1 { v |= 1u128 << i; } }
        let on = cm == 0 || (cw >> s) & 1 == 1;
        let want = if on { (xs[s] + kwin) & mask } else { xs[s] };
        ok &= v == want;
    }
    Out { ok, phase: sim.phase, tof }
}

#[test]
fn gidney_exhaustive_small() {
    let mut rng = Rng::new(7);
    let mut cases = 0;
    for n in 3..=6usize {
        for kwin in 0..(1u128 << n) {
            for cm in 0..2 {
                let mut xs = [0u128; 64];
                for s in 0..64 { xs[s] = (s as u128) % (1 << n); }
                let cw = if n < 6 { let mut w = 0u64; for s in 0..64 { if (s >> n) & 1 == 1 { w |= 1 << s; } } if n == 5 { w = rng.next(); } w } else { rng.next() };
                let o = case(n, kwin, cm, &xs, cw, &mut rng, false);
                assert!(o.ok && o.phase == 0, "n={n} K={kwin} cm={cm} ok={} phase={:#x}", o.ok, o.phase);
                cases += 1;
            }
        }
    }
    eprintln!("GIDNEY_EXHAUSTIVE_PASS cases {cases}");
}

#[test]
fn gidney_random_wide_and_counts() {
    let mut rng = Rng::new(17);
    let mut seen = std::collections::BTreeMap::new();
    for &(n, kwin) in &[(67usize, (1u128 << 32) | 977), (63usize, ((1u128 << 32) | 976) >> 4), (21, 0x1_2345u128), (40, 0xdead_beefu128), (64, u64::MAX as u128), (90, (1u128 << 89) | 12345)] {
        for cm in 0..2 {
            let mask: u128 = (1u128 << n) - 1;
            let mut xs = [0u128; 64];
            for s in 0..64 { xs[s] = (((rng.next() as u128) << 64) | rng.next() as u128) & mask; }
            // force carry chains: a few shots with long runs of ones
            xs[1] = mask; xs[2] = mask ^ 1; xs[3] = ((mask >> 1) << 1) | 1; xs[4] = 0;
            xs[5] = mask - (kwin & mask) + 1; xs[6] = mask - (kwin & mask); xs[7] = (mask - (kwin & mask)) & !1;
            let cw = rng.next();
            let o = case(n, kwin & mask, cm, &xs, cw, &mut rng, false);
            assert!(o.ok && o.phase == 0, "n={n} cm={cm} ok={} phase={:#x}", o.ok, o.phase);
            seen.insert((n, cm), o.tof);
        }
    }
    eprintln!("GIDNEY_WIDE_PASS tof {:?}", seen);
}

/// the fold windows of the tree: C (67 lanes) and C - 1 >> 4 (63 lanes) under a control: 3n - 6 Toffoli each
#[test]
fn gidney_fold_window_toffoli() {
    for &(n, kwin, want) in &[(67usize, (1u128 << 32) + 977, 195u64), (63, ((1u128 << 32) + 976) >> 4, 183)] {
        let mut b = B::new();
        let t = b.alloc_n(n); let c = b.alloc(); let cl = b.alloc_n(2); let d = b.alloc_n(n - 2);
        gidney_add(&mut b, &t, kwin, Some(c), [cl[0], cl[1]], &d);
        b.flush_dependency();
        eprintln!("GIDNEY_FOLD n={n}: {} Toffoli (3n-6 = {})", b.tof, 3 * n - 6);
        assert_eq!(b.tof, want);
    }
}

#[test]
fn gidney_sabotage_is_caught() {
    let mut rng = Rng::new(29);
    let n = 6usize;
    let mut caught = 0;
    for kwin in [13u128, 45, 63, 22] {
        let mut xs = [0u128; 64];
        for s in 0..64 { xs[s] = s as u128; }
        let o = case(n, kwin, 1, &xs, rng.next(), &mut rng, true);
        if !o.ok || o.phase != 0 { caught += 1; }
    }
    assert_eq!(caught, 4, "sabotage (second Z layer dropped) must be detected for every constant");
}

// ---------------------------------------------------------------------------------------------------------------------
// the hook: Horner rounds (pre, sround x NB, post) with the pool on (Gidney folds / AND-cell folds) against the same rounds
// with the pool off (the parent's NAF increments): same z, same lanes returned, phase clean.
// ---------------------------------------------------------------------------------------------------------------------
use crate::point_add::modp_frogdrop::Ms;
use crate::point_add::fd_shell;

const NB: usize = 12;

struct Rounds { z: Vec<[u64; 4]>, phase: u64, clean_ok: bool, tof: u64 }

fn rounds(a255: bool, pool_n: usize, seed: u64, sabotage: bool) -> Rounds {
    SABOTAGE.with(|s| s.set(sabotage));
    let mut rng = Rng::new(seed);
    let mut b = B::new();
    let ms = Ms::alloc(&mut b);
    let z = b.alloc_n(256);
    let a = b.alloc_n(if a255 { 255 } else { 256 });
    let bits = b.alloc_n(NB);
    let pool = b.alloc_n(pool_n);
    // the addend lanes double as the dirty lanes of the folds (as in the tree)
    if pool_n > 0 { b.gpool = pool.clone(); }
    let mut zz = z.clone();
    fd_shell::pre(&mut b, &ms, &mut zz, &a, bits[0]);
    for i in (0..NB).rev() {
        fd_shell::sround(&mut b, &ms, &mut zz, &a, bits[i], bits[(i + 1) % NB]);
    }
    fd_shell::post(&mut b, &ms, &mut zz, &a, bits[0]);
    b.gpool.clear();
    b.flush_dependency();
    let tof = b.tof;
    let nq = b.width() as usize;
    let mut zs = vec![[0u64; 4]; 64];
    let mut as_ = vec![[0u64; 4]; 64];
    for s in 0..64 {
        for i in 0..4 { zs[s][i] = rng.next(); as_[s][i] = rng.next(); }
        if a255 { as_[s][3] &= 0x7FFF_FFFF_FFFF_FFFF; }
    }
    // shots 0..3: edge cases around the fold (z near 2^256, a all ones)
    zs[0] = [u64::MAX; 4]; as_[0] = [u64::MAX, u64::MAX, u64::MAX, if a255 { 0x7FFF_FFFF_FFFF_FFFF } else { u64::MAX }];
    zs[1] = [0; 4]; zs[2] = [u64::MAX, u64::MAX, u64::MAX, u64::MAX - 1];
    let bw: Vec<u64> = (0..NB).map(|_| rng.next()).collect();
    let sim = run(&b.ops, nq, &|w: &mut Vec<u64>| {
        for s in 0..64 {
            for i in 0..256 { if (zs[s][i / 64] >> (i % 64)) & 1 == 1 { w[z[i].0 as usize] |= 1u64 << s; } }
            for i in 0..a.len() { if (as_[s][i / 64] >> (i % 64)) & 1 == 1 { w[a[i].0 as usize] |= 1u64 << s; } }
        }
        for i in 0..NB { w[bits[i].0 as usize] = bw[i]; }
    });
    SABOTAGE.with(|s| s.set(false));
    let mut clean_ok = sim.q[ms.k.0 as usize] == 0;
    for q in &pool { clean_ok &= sim.q[q.0 as usize] == 0; }
    for i in 0..NB { clean_ok &= sim.q[bits[i].0 as usize] == bw[i]; }
    let mut out = vec![[0u64; 4]; 64];
    for s in 0..64 {
        for i in 0..256 { if (sim.q[zz[i].0 as usize] >> s) & 1 == 1 { out[s][i / 64] |= 1u64 << (i % 64); } }
        for i in 0..a.len() { let bit = (sim.q[a[i].0 as usize] >> s) & 1; clean_ok &= bit == ((as_[s][i / 64] >> (i % 64)) & 1); }
    }
    Rounds { z: out, phase: sim.phase, clean_ok, tof }
}

#[test]
fn pool_rounds_match_parent_folds() {
    for &a255 in &[false, true] {
        let base = rounds(a255, 0, 5, false);
        assert!(base.clean_ok && base.phase == 0);
        for &pool_n in &[1usize, 2, 3, 70] {
            let r = rounds(a255, pool_n, 5, false);
            assert!(r.clean_ok, "a255={a255} pool={pool_n}: lanes not restored");
            assert_eq!(r.phase, 0, "a255={a255} pool={pool_n}: phase garbage");
            assert_eq!(r.z, base.z, "a255={a255} pool={pool_n}: value differs from the parent folds");
            eprintln!("POOL_ROUNDS a255={a255} pool={pool_n}: tof {} (parent folds {})", r.tof, base.tof);
        }
    }
}

#[test]
fn pool_rounds_sabotage_is_caught() {
    let r = rounds(false, 2, 5, true);
    let base = rounds(false, 0, 5, false);
    assert!(r.phase != 0 || r.z != base.z || !r.clean_ok, "sabotaged Gidney fold not detected");
}
