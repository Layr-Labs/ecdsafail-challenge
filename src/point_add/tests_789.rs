//! Lane FHD-789: tests for the 789 row (L1-8 joint (h, depth) code, split ctrl_modadd fold).
//! - `t789_ctrl_modadd`: the split fold on random field elements plus forced carry-drop inputs (the one new error mode).
//! - `t789_tails`: integer-model census of the L1-8 collision set (per walk; a graded shot runs two walks).
//! - `t789_encode`: the stored code is injective on the on-model (h, depth) pairs.

use super::refmodel_double::{self as rmd, Ph, N};
use super::tests_double::Rng;

fn walk(rng: &mut Rng, pp: &N) -> rmd::St {
    let mut x = rng.below(256) % *pp;
    if x == N::ZERO {
        x = N::from(1u64);
    }
    rmd::St::new(x)
}

/// L1-8 collision predicate for a state (h, d): not representable / colliding with another on-model code
pub(super) fn l18_bad(h: i32, d: usize) -> bool {
    (d <= 15 && h >= 12) || (d >= 16 && h >= 4) || d >= 24
}

#[test]
fn t789_encode() {
    use super::froghop_double::l18_encode;
    let mut seen = std::collections::HashMap::new();
    for h in 0..16u64 {
        for d in 0..32u64 {
            if l18_bad(h as i32, d as usize) {
                continue;
            }
            let c = l18_encode(h, d);
            assert!(c.0 < 16 && c.1 < 16);
            if let Some(prev) = seen.insert(c, (h, d)) {
                panic!("code {:?} for both {:?} and {:?}", c, prev, (h, d));
            }
        }
    }
    eprintln!("L1-8 code injective on {} on-model (h, depth) pairs", seen.len());
}

#[test]
fn t789_tails() {
    let shots: usize = std::env::var("SC_SHOTS").ok().and_then(|s| s.parse().ok()).unwrap_or(200000);
    let seed: u64 = std::env::var("SC_SEED").ok().and_then(|s| s.parse().ok()).unwrap_or(78901);
    let lay = super::layout_double();
    let pp = rmd::p();
    let mut rng = Rng::new(seed);
    let (mut bad, mut pi24, mut unfinished) = (0u64, 0u64, 0u64);
    for _ in 0..shots {
        let mut m = walk(&mut rng, &pp);
        let (mut fl, mut fp) = (false, false);
        for sigma in 0..lay.s {
            let h = m.pi >> 1;
            let d = m.stk.len();
            fl |= l18_bad(h, d);
            fp |= m.pi >= 24;
            m.fwd(sigma);
            // mid-slot: depth moves at S4 / S6 before pi moves at S9
            fl |= l18_bad(h, m.stk.len());
        }
        if m.ph != Ph::Dn {
            unfinished += 1;
        }
        bad += fl as u64;
        pi24 += fp as u64;
    }
    let lam = |c: u64| {
        let p1 = c as f64 / shots as f64;
        9024.0 * (1.0 - (1.0 - p1) * (1.0 - p1))
    };
    eprintln!("T789 tails seed {seed}: {shots} walks; L1-8 collisions {bad} (lambda {:.3}); walks with pi >= 24 {pi24} (lambda {:.3}); unfinished {unfinished}",
              lam(bad), lam(pi24));
}

fn put_n(words: &mut [u64], qs: &[crate::circuit::QubitId], shot: usize, val: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if val.bit(i) {
            words[q.0 as usize] |= 1 << shot
        } else {
            words[q.0 as usize] &= !(1 << shot)
        }
    }
}

/// ctrl_modadd (split fold): Toffoli per call, Ms width, correctness on random field elements. Shot 0 of the first 8
/// batches is forced onto the carry-drop input (k = 1 and the 256-bit sum's low 32 bits all ones).
#[test]
fn t789_ctrl_modadd() {
    use super::builder::B;
    use super::modp_double::{ctrl_modadd, Ms};
    use super::tests_double::{get, getb, run};
    let pp = rmd::p();
    let mut rng = Rng::new(4242);
    let (mut bad, mut forced_bad, mut tot) = (0, 0, 0);
    let mut tof_call = 0;
    let mut msw = 0;
    for rep in 0..16 {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let y = b.alloc_n(256);
        let ctl = b.alloc();
        let ms = Ms::alloc(&mut b);
        msw = 3 + ms.s.len();
        let t0 = b.tof;
        ctrl_modadd(&mut b, &ms, &z, &y, ctl);
        tof_call = b.tof - t0;
        let mut zv = vec![];
        let mut yv = vec![];
        let mut cv = vec![];
        for s in 0..64 {
            let yy = rng.below(256) % pp;
            let mut zz = rng.below(256) % pp;
            if s == 0 && rep < 8 {
                let m = rng.below(200);
                let tgt = (N::from(1u64) << 256) + (N::from(1u64) << 32) - N::from(1u64) + (m << 32);
                if tgt > yy && tgt - yy < pp {
                    zz = tgt - yy;
                }
            }
            zv.push(zz);
            yv.push(yy);
            cv.push(s % 5 != 3 || (s == 0 && rep < 8));
        }
        let (z2, y2, zv2, yv2, cv2) = (z.clone(), y.clone(), zv.clone(), yv.clone(), cv.clone());
        let r = run(&b.ops, 0, &move |w| {
            for s in 0..64 {
                put_n(w, &z2, s, &zv2[s]);
                put_n(w, &y2, s, &yv2[s]);
                if cv2[s] {
                    w[ctl.0 as usize] |= 1 << s;
                }
            }
        });
        assert_eq!(r.phase, 0);
        for s in 0..64 {
            let want = if cv[s] { (zv[s] + yv[s]) % pp } else { zv[s] };
            let ok = get(&r.q, &z, s) == want
                && get(&r.q, &y, s) == yv[s]
                && getb(&r.q, ctl, s) == cv[s] as u64
                && ms.s.iter().chain([ms.c0, ms.k, ms.c1].iter()).all(|&q| getb(&r.q, q, s) == 0);
            tot += 1;
            if !ok {
                if s == 0 && rep < 8 {
                    forced_bad += 1;
                } else {
                    bad += 1;
                }
            }
        }
    }
    eprintln!("T789 ctrl_modadd: Ms width {msw}; Toffoli per call {tof_call}; random shots bad {bad} of {}; forced carry-drop shots bad {forced_bad} of 8", tot - 8);
    // lane FHD-SHIFT: the 790 fold (no split): Ms 13, and the 789 split's carry-drop inputs are handled
    assert_eq!(msw, 13);
    assert_eq!(bad, 0);
    assert_eq!(forced_bad, 0, "the unsplit fold has no carry drop on the split's forced inputs");
}

/// Bit length of the largest Euclid quotient of (p, x') (x' = min(x, p - x))
pub(super) fn max_q_bits(x: &N) -> u32 {
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

/// The 64 model-test inputs of DSEED (the draw of double_traversal_matches_model / the identity tests): which have a
/// quotient of >= 24 bits (this row's collision set)
#[test]
fn t789_seed_qbits() {
    let seed: u64 = std::env::var("DSEED").ok().and_then(|s| s.parse().ok()).unwrap_or(4242);
    let mut rng = Rng::new(seed);
    let pp = rmd::p();
    let v: Vec<(usize, u32)> = (0..64).map(|k| {
        let mut x = rng.below(256) % pp;
        if x == N::ZERO { x = N::from(1u64); }
        (k, max_q_bits(&x))
    }).filter(|&(_, q)| q >= 24).collect();
    eprintln!("T789 seed {seed}: shots with a >= 24-bit quotient: {:?}", v);
}
