//! Scheme G unit tests (midg.rs).

use super::builder::B;
use super::frogdrop_sched::N;
use super::midg::*;
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
fn pval() -> N {
    (N::from(1u64) << 256) - (N::from(1u64) << 32) - N::from(977u64)
}
fn bl(v: &N) -> usize { v.bit_len() }

/// model: over(W) = [(W >> u) > (F >> u)], F = floor((2^(256-s) - 1) / Zh), Zh = (Z >> s) | 1, s = sz - K
fn over_model(w: &N, z: &N, k: usize) -> bool {
    let sz = bl(z);
    let s = sz - k;
    let zh = (*z >> s) | N::from(1u64);
    let f = ((N::from(1u64) << (256 - s)) - N::from(1u64)) / zh;
    assert_eq!(bl(&f), 257 - sz);
    let u = (257 - sz).saturating_sub(TC);
    (*w >> u) > (f >> u)
}

/// stage1_test on 64 shots per seed: Z with bl(Z) in [szlo, szhi], W near F (ties, +-1, +-small) or random below
/// 2^(258 - sz); lanes past W's position 0 hold junk that must survive.
fn run_stage1(seed: u64, szlo: usize, szhi: usize) {
    let k = 23usize;
    let mut b = B::new();
    let zh = b.alloc_n(k);
    let win = b.alloc_n(TC + 1);
    let sz = b.alloc_n(9);
    let s = S1 { r: b.alloc_n(k + 1), f: b.alloc(), zero: b.alloc(), sgn: b.alloc(), gt: b.alloc_n(3), anc: vec![], andc: b.alloc_n(10),
                 chain: b.alloc_n(9), dirty: b.alloc_n(48) };
    let t = b.alloc();
    let ctl = b.alloc();
    let temps = b.alloc_n(2);
    let fwd = stage1_fwd(&mut b, &zh, &win, &sz, (szlo, szhi), &s);
    stage1_test(&mut b, &fwd, &s, t, &[(ctl, false)], &temps, true);
    let mut rng = Rng::new(seed);
    struct Sh { z: N, w: N, sz: usize, junk: N, ctl: u64, d: N }
    let mut shots = vec![];
    for i in 0..64 {
        let szv = szlo + (rng.next() as usize) % (szhi - szlo + 1);
        let z = (rng.below(szv - 1)) | (N::from(1u64) << (szv - 1));
        let ss = szv - k;
        let zhv = (z >> ss) | N::from(1u64);
        let f = ((N::from(1u64) << (256 - ss)) - N::from(1u64)) / zhv;
        let u = (257 - szv).saturating_sub(TC);
        let mode = rng.next() % 6;
        let w = match mode {
            0 => f,
            1 => f + N::from(1u64),
            2 => if f > N::ZERO { f - N::from(1u64) } else { f },
            3 => ((f >> u) << u) + (rng.below(u.max(1)) % (N::from(1u64) << u)),
            4 => (((f >> u) + N::from(1u64)) << u) + (rng.below(u.max(1)) % (N::from(1u64) << u)),
            _ => rng.below(258 - szv),
        };
        let w = w % (N::from(1u64) << (258 - szv));
        shots.push(Sh { z, w, sz: szv, junk: rng.below(TC + 1), ctl: rng.next() & 1, d: rng.below(48) });
        let _ = i;
    }
    let sim = run(&b.ops, b.width() as usize, &|wd| {
        for (si, sh) in shots.iter().enumerate() {
            let ss = sh.sz - k;
            put(wd, &zh, si, &(sh.z >> ss));
            // window: index 0 = position 257 - sz, index 1 + j = position 256 - sz - j; below position 0: junk
            let mut wv = N::ZERO;
            for i in 0..=TC {
                let pos = 257isize - sh.sz as isize - i as isize;
                let bit = if pos >= 0 { sh.w.bit(pos as usize) } else { sh.junk.bit(i) };
                if bit { wv |= N::from(1u64) << i; }
            }
            put(wd, &win, si, &wv);
            put(wd, &sz, si, &N::from(sh.sz as u64));
            put(wd, &s.dirty, si, &sh.d);
            if sh.ctl == 1 { wd[ctl.0 as usize] |= 1 << si; }
        }
    });
    assert_eq!(sim.phase, 0, "phase garbage");
    let mut nover = 0;
    for (si, sh) in shots.iter().enumerate() {
        let want = sh.ctl == 1 && over_model(&sh.w, &sh.z, k);
        if want { nover += 1; }
        assert_eq!((sim.q[t.0 as usize] >> si) & 1 == 1, want, "shot {si}: t (sz {}, ctl {})", sh.sz, sh.ctl);
        assert_eq!(get(&sim.q, &zh, si), sh.z >> (sh.sz - k), "shot {si}: zh");
        assert_eq!(get(&sim.q, &s.dirty, si), sh.d, "shot {si}: dirty");
        assert_eq!(get(&sim.q, &sz, si), N::from(sh.sz as u64), "shot {si}: sz");
        let mut wv = N::ZERO;
        for i in 0..=TC {
            let pos = 257isize - sh.sz as isize - i as isize;
            let bit = if pos >= 0 { sh.w.bit(pos as usize) } else { sh.junk.bit(i) };
            if bit { wv |= N::from(1u64) << i; }
        }
        assert_eq!(get(&sim.q, &win, si), wv, "shot {si}: window");
        for &q in s.r.iter().chain([s.f, s.zero, s.sgn].iter()).chain(s.gt.iter()).chain(s.chain.iter()).chain(temps.iter()) {
            assert_eq!((sim.q[q.0 as usize] >> si) & 1, 0, "shot {si}: scratch q{}", q.0);
        }
    }
    eprintln!("stage1 seed {seed} sz [{szlo},{szhi}]: ok, {nover} over, {} T, {} ops", sim.tof, b.ops.len());
}

#[test]
fn midg_stage1_mid() {
    for seed in 1..4 { run_stage1(seed, 128, 200); }
}

#[test]
fn midg_stage1_early() {
    for seed in 11..14 { run_stage1(seed, 220, 256); }
}

#[test]
fn midg_stage1_p() {
    // the real dividend: p >> s must be all ones for s >= 33
    let p = pval();
    for s in 33..240usize { assert_eq!(p >> s, (N::from(1u64) << (256 - s)) - N::from(1u64)); }
}

