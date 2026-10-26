//! Lane A4b census: the joint code of the bookkeeping lanes (p0 p1 p2 dep0..4) per phase class at the step entries
//! whose re-encodings the 791 build relies on. Gate-level replay against refmodel_double, 64 shots per seed.

use super::builder::B;
use super::froghop_double::{FhDouble, WD};
use super::refmodel_double::{self as rmd, Ph, N};
use super::tests_double::{lay_double, run, Rng};
use crate::circuit::QubitId;
use std::collections::BTreeMap;

fn putv(words: &mut [u64], qs: &[QubitId], shot: usize, val: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if val.bit(i) { words[q.0 as usize] |= 1 << shot } else { words[q.0 as usize] &= !(1 << shot) }
    }
}

fn bit(words: &[u64], q: QubitId, k: usize) -> u32 {
    ((words[q.0 as usize] >> k) & 1) as u32
}

/// code string "p0p1p2:depth"
fn code_str(c: u32) -> String {
    format!("{}{}{}:{:2}{}", c & 1, (c >> 1) & 1, (c >> 2) & 1, (c >> 3) & 31, if (c >> 8) & 1 == 1 { " z0" } else { "" })
}

#[test]
fn a4b_census() {
    let lay = lay_double();
    let w = WD;
    let seeds: Vec<u64> = std::env::var("A4SEEDS").ok().map(|s| s.split(',').map(|x| x.parse().unwrap()).collect())
        .unwrap_or(vec![11, 22, 33, 44]);
    let marks = ["S2", "S3", "S4 aldv", "SC", "S5", "S6 lad", "S7", "S8", "S9"];
    let classes = ["AL", "DV", "CO", "RT", "DN"];
    // seen[mark][(class, code)] = count of (slot, shot)
    let mut seen: Vec<BTreeMap<(usize, u32), u64>> = vec![BTreeMap::new(); marks.len()];
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
        for sigma in 0..lay.s {
            let cls: Vec<usize> = models.iter().map(|m| match m.ph { Ph::Al => 0, Ph::Dv => 1, Ph::Co => 2, Ph::Rt => 3, Ph::Dn => 4 }).collect();
            let start = b.ops.len();
            f.marks.clear();
            f.slot(&mut b, &lay, sigma);
            let ops = b.ops[start..].to_vec();
            let mut pos = 0usize;
            let mut cur = words.clone();
            let mk: Vec<(&str, usize)> = f.marks.iter().map(|m| (m.0, m.1 - start)).collect();
            let lanes: Vec<QubitId> = [f.p0, f.p1, f.p2].iter().copied().chain(f.dep.iter().copied()).collect();
            let hq = f.pi.clone();
            for (nm, at) in mk {
                if at > pos {
                    let wd = cur.clone();
                    cur = run(&ops[pos..at], nq, &move |x| x.copy_from_slice(&wd)).q;
                    pos = at;
                }
                if let Some(mi) = marks.iter().position(|x| *x == nm) {
                    for k in 0..64 {
                        let mut c = 0u32;
                        for (i, &q) in lanes.iter().enumerate() { c |= bit(&cur, q, k) << i; }
                        // [pi == 0]: odd slots, h == 0
                        let z0 = sigma % 2 == 1 && hq.iter().all(|&q| bit(&cur, q, k) == 0);
                        if z0 { c |= 1 << 8; }
                        *seen[mi].entry((cls[k], c)).or_insert(0) += 1;
                    }
                }
            }
            let wd = words.clone();
            words = run(&ops, nq, &move |x| x.copy_from_slice(&wd)).q;
            for m in models.iter_mut() { m.fwd(sigma); }
        }
    }
    eprintln!("A4b census, seeds {:?} (64 shots each): joint code p0p1p2:depth [z0] per pre-slot class", seeds);
    for (mi, mn) in marks.iter().enumerate() {
        eprintln!("== {}", mn);
        for c in 0..classes.len() {
            let row: Vec<String> = seen[mi].iter().filter(|((cc, _), _)| *cc == c).map(|((_, code), n)| format!("{}x{}", code_str(*code), n)).collect();
            if !row.is_empty() { eprintln!("  {}: {}", classes[c], row.join("  ")); }
        }
    }
}

/// Bit length of the largest Euclid quotient of (p, x') (x' = min(x, p - x), the traversal's start)
fn max_q_bits(x: &N) -> u32 {
    let pp = rmd::p();
    let mut a = pp;
    let mut bb = if *x > pp - *x { pp - *x } else { *x };
    let mut m = 0;
    while bb != N::ZERO {
        let q = a / bb;
        m = m.max(q.bit_len() as u32);
        let r = a - q * bb;
        a = bb;
        bb = r;
    }
    m
}

/// Directed inputs with large Euclid quotients (depth and pi far above the census range: quotients of 16..QMAX bits,
/// first-step and mid-run), checked register by register at every slot boundary against the integer model. Records
/// per shot the first slot it leaves the model, so a POOL_D = 0 / POOL_D = 1 pair can be compared shot by shot.
#[test]
fn a4b_large_quotients() {
    use super::froghop_double::{BB, POOL_D};
    use super::tests_double::{expect_lanes, get, getb, par_bit, par_lane};
    let lay = lay_double();
    let w = WD;
    let seed: u64 = std::env::var("DSEED").ok().and_then(|s| s.parse().ok()).unwrap_or(5150);
    let mut rng = Rng::new(seed);
    let pp = rmd::p();
    // quotients up to QMAX bits (default 24): wider first-step quotients leave the model on the 792 parent too (the
    // early slots' h window is 26 lanes); A4B_QMAX=28 with A4B_ALLOW_BAD=1 lists them for a POOL_D A/B
    let qmax: u32 = std::env::var("A4B_QMAX").ok().and_then(|s| s.parse().ok()).unwrap_or(24);
    let mut xs: Vec<N> = vec![];
    // first-step large quotient q0 of k bits: x = p / (q0 + u), u a random 120-bit fraction (x = p >> k would give
    // a ~200-bit second quotient, since p is close to 2^256); keep inputs whose every quotient fits 28 bits
    for k in (16..=qmax).cycle().take(13) {
        loop {
            let q0 = (rng.below(k as usize - 1)) | (N::from(1u64) << (k as usize - 1));
            // a 120-bit fraction: with a short one p / x sits too close to a small-denominator rational and a later
            // quotient is ~2^100 (p << 120 fits the 384-bit model integer)
            let u = rng.below(120);
            let x = (pp << 120) / ((q0 << 120) + u);
            if max_q_bits(&x) <= qmax && x > N::ZERO {
                xs.push(x);
                break;
            }
        }
    }
    // mid-run large quotients by rejection sampling: max quotient of 16..28 bits
    let mut tries = 0u64;
    while xs.len() < 64 {
        tries += 1;
        let x = rng.below(256) % pp;
        if x == N::ZERO { continue; }
        let m = max_q_bits(&x);
        if (16..=qmax).contains(&m) { xs.push(x); }
    }
    let mut b = B::new();
    let d = b.alloc_n(w);
    let v = b.alloc_n(w);
    let par = b.alloc();
    let dirty = b.alloc_n(256);
    let mut f = FhDouble::alloc(&mut b, d, v, &lay, par, dirty.clone());
    let mut models: Vec<rmd::St> = xs.iter().map(|&x| rmd::St::new(x)).collect();
    let vl: Vec<QubitId> = f.v[1..257].to_vec();
    f.init(&mut b, &lay);
    let nq = b.width() as usize;
    let mods = models.clone();
    let dq = dirty.clone();
    // lane FHD-LEFT (PARV): random initial parity in V's top lane
    let parv = f.parv;
    let parinit: Vec<u8> = (0..64).map(|k| ((rng.next() >> (k % 5)) & 1) as u8).collect();
    let vtop = f.v[w - 1];
    let pin = parinit.clone();
    let mut words = run(&b.ops, nq, &|wd| {
        for k in 0..64 { putv(wd, &vl, k, &mods[k].rv); }
        if parv { for k in 0..64 { if pin[k] == 1 { wd[vtop.0 as usize] |= 1 << k; } } }
        for (i, &q) in dq.iter().enumerate() { wd[q.0 as usize] = 0x9E3779B97F4A7C15u64.wrapping_mul(i as u64 + 7) ^ 0x5bd1e995; }
    }).q;
    let dirty0: Vec<u64> = dirty.iter().map(|q| words[q.0 as usize]).collect();
    let mut first_bad: Vec<Option<(usize, &'static str)>> = vec![None; 64];
    let mut maxdep = 0usize;
    let mut maxpi = 0i32;
    for sigma in 0..lay.s {
        for k in 0..64 {
            if first_bad[k].is_some() { continue; }
            let m = &models[k];
            maxdep = maxdep.max(m.stk.len());
            maxpi = maxpi.max(m.pi);
            let (mut ed, mut ev) = expect_lanes(m);
            if parv {
                let (ind, l) = par_lane(m);
                let pb = par_bit(m, parinit[k]);
                if ind { ed[l] ^= pb; } else { ev[l] ^= pb; }
            }
            let mut why: Option<&'static str> = None;
            if (0..w).any(|j| getb(&words, f.d[j], k) as u8 != ed[j]) { why = Some("D"); }
            else if (0..w).any(|j| getb(&words, f.v[j], k) as u8 != ev[j]) { why = Some("V"); }
            else if get(&words, &f.pi, k) != N::from((m.pi >> 1) as u64) { why = Some("pi"); }
            else if get(&words, &f.dep, k) != N::from(m.stk.len() as u64) { why = Some("dep"); }
            else if get(&words, &f.bq, k) != N::from(((m.b as i64 - 1 - lay.base[sigma] as i64).rem_euclid(1 << BB)) as u64) { why = Some("b"); }
            else {
                let code = [f.p0, f.p1, f.p2].iter().map(|&q| getb(&words, q, k)).collect::<Vec<_>>();
                let want = match m.ph { Ph::Al => [1, 0, 0], Ph::Dv => [0, 1, 0], Ph::Co => [1, 1, 0], Ph::Rt => [0, 0, 0], Ph::Dn => [0, 0, 1] };
                if code != want.to_vec() { why = Some("phase"); }
                else if !parv && getb(&words, f.par, k) as u8 != m.par { why = Some("par"); }
            }
            if let Some(wy) = why { first_bad[k] = Some((sigma, wy)); }
        }
        let start = b.ops.len();
        f.slot(&mut b, &lay, sigma);
        let ops = b.ops[start..].to_vec();
        let wd = words.clone();
        let r = run(&ops, nq, &move |x| x.copy_from_slice(&wd));
        for k in 0..64 {
            if (r.phase >> k) & 1 == 1 && first_bad[k].is_none() { first_bad[k] = Some((sigma, "phase-word")); }
        }
        words = r.q;
        for (i, q) in dirty.iter().enumerate() {
            let diff = words[q.0 as usize] ^ dirty0[i];
            for k in 0..64 { if (diff >> k) & 1 == 1 && first_bad[k].is_none() { first_bad[k] = Some((sigma, "dirty")); } }
        }
        for m in models.iter_mut() { m.fwd(sigma); }
    }
    for (k, m) in models.iter().enumerate() {
        if first_bad[k].is_none() && m.ph != Ph::Dn { first_bad[k] = Some((lay.s, "not done")); }
    }
    let bad: Vec<(usize, (usize, &str), u32)> = first_bad.iter().enumerate().filter_map(|(k, x)| x.map(|y| (k, y, max_q_bits(&xs[k])))).collect();
    eprintln!("A4b large quotients (POOL_D {}, seed {}, {} rejection tries): max depth {} max pi {}; off-model shots {}: {:?}",
              POOL_D, seed, tries, maxdep, maxpi, bad.len(), bad);
    if std::env::var_os("A4B_ALLOW_BAD").is_none() {
        assert!(bad.is_empty(), "shots left the model");
    }
}
