//! Schoggistängeli (lane T1b): one consume-seed transposition split into its parts and counted, and the seeds and
//! consume products with the cheaper transposition checked against the tree's on random shots (64 per run).

use super::builder::B;
use super::frogdrop_sched::N;
use super::modp_frogdrop::Ms;
use super::pointadd_frogdrop as pf;
use super::tests_frogdrop::{run, Rng};
use crate::circuit::QubitId;

fn put(w: &mut [u64], qs: &[QubitId], shot: usize, v: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if v.bit(i) { w[q.0 as usize] |= 1 << shot } else { w[q.0 as usize] &= !(1 << shot) }
    }
}
fn get(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, &q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 {
            v |= N::from(1u64) << i;
        }
    }
    v
}
fn getb(w: &[u64], q: QubitId, shot: usize) -> u64 {
    (w[q.0 as usize] >> shot) & 1
}

/// Parts of one transposition (emitted T): P1 form (255-lane addend, ctrl_modadd255) and P5 form (256-lane addend,
/// ctrl_modadd), the tree's and Schoggistängeli's, at w = 11.
#[test]
fn schoggi_transposition_split() {
    use super::arith::{ttk_add, ttk_carry};
    use super::modp_frogdrop::{add_small, C, CMPT};
    let w = 11;
    let j = 1365; // a mid pattern (6 set bits); the count does not depend on j
    for &sg in &[None, Some((pf::SCHOGGI_ZT, pf::SCHOGGI_H))] {
        for &p1 in &[true, false] {
            let mut b = B::new();
            let z = b.alloc_n(256);
            let a = b.alloc_n(if p1 { 255 } else { 256 });
            let ylow = b.alloc_n(2);
            let flag = b.alloc();
            let ms = Ms::alloc(&mut b);
            let mut parts: Vec<(&str, u64)> = vec![];
            let mut t0 = b.tof;
            let mut mark = |b: &B, name: &'static str, parts: &mut Vec<(&str, u64)>| {
                parts.push((name, b.tof - t0));
                t0 = b.tof;
            };
            match sg {
                None => super::joint_seed::activate_bits(&mut b, &z, flag, j, &a, w),
                Some((zt, _)) => pf::sg_activate(&mut b, &z, flag, j, &a, w, zt),
            }
            mark(&b, "activation (zero test)", &mut parts);
            let k = ms.k;
            if p1 {
                ttk_add(&mut b, &a, &z[..255], Some(flag), Some((k, ylow[0])));
                mark(&b, "ripple add 255 + carry", &mut parts);
                b.cx(k, z[255]);
                let at = &a[255 - CMPT..255];
                let rt = &z[255 - CMPT..255];
                pf::dctl_lt(&mut b, at, rt, flag, z[255], k, ylow[0], ylow[1]);
                mark(&b, "carry fold + top compare", &mut parts);
                match sg {
                    None => add_small(&mut b, &ms, &z, 0, Some(k), C, &a),
                    Some((_, h)) => pf::sg_add_small(&mut b, &z, 0, k, C, &a, h),
                }
                mark(&b, "+c fold", &mut parts);
                b.x(z[255]);
                pf::dctl_lt(&mut b, at, rt, flag, z[255], k, ylow[0], ylow[1]);
                b.x(z[255]);
                mark(&b, "flag erase (top compare)", &mut parts);
            } else {
                ttk_add(&mut b, &a, &z, Some(flag), Some((k, ylow[0])));
                mark(&b, "ripple add 256 + carry", &mut parts);
                match sg {
                    None => add_small(&mut b, &ms, &z, 0, Some(k), C, &a),
                    Some((_, h)) => pf::sg_add_small(&mut b, &z, 0, k, C, &a, h),
                }
                mark(&b, "+c fold", &mut parts);
                let zt = &z[256 - CMPT..];
                let yt = &a[256 - CMPT..];
                for &q in zt { b.x(q); }
                ttk_carry(&mut b, yt, zt, flag, k, ylow[0]);
                for &q in zt { b.x(q); }
                mark(&b, "flag erase (top compare)", &mut parts);
            }
            let tot: u64 = parts.iter().map(|p| p.1).sum();
            // the whole transposition through the production functions must count the same
            let mut b2 = B::new();
            let z2 = b2.alloc_n(256);
            let a2 = b2.alloc_n(if p1 { 255 } else { 256 });
            let y2 = b2.alloc_n(2);
            let f2 = b2.alloc();
            let ms2 = Ms::alloc(&mut b2);
            match (sg, p1) {
                (None, true) => {
                    super::joint_seed::activate_bits(&mut b2, &z2, f2, j, &a2, w);
                    pf::ctrl_modadd255(&mut b2, &ms2, &z2, &a2, f2, y2[0], y2[1]);
                }
                (None, false) => {
                    super::joint_seed::activate_bits(&mut b2, &z2, f2, j, &a2, w);
                    super::modp_frogdrop::ctrl_modadd(&mut b2, &ms2, &z2, &a2, f2, y2[0]);
                }
                (Some((zt, h)), true) => {
                    pf::sg_activate(&mut b2, &z2, f2, j, &a2, w, zt);
                    pf::sg_ctrl_modadd255(&mut b2, &ms2, &z2, &a2, f2, y2[0], y2[1], h);
                }
                (Some((zt, h)), false) => {
                    pf::sg_activate(&mut b2, &z2, f2, j, &a2, w, zt);
                    pf::sg_ctrl_modadd(&mut b2, &ms2, &z2, &a2, f2, y2[0], h);
                }
            }
            b2.flush_dependency();
            eprintln!("SPLIT {} {}: total {} (production fn {})",
                      if sg.is_some() { "schoggi" } else { "tree   " }, if p1 { "P1 (255)" } else { "P5 (256)" },
                      tot, b2.tof);
            for (n, t) in &parts {
                eprintln!("SPLIT    {:28} {:5}", n, t);
            }
        }
    }
}

fn seed_case(sg: Option<(usize, usize)>, w: usize, seed: u64) -> u64 {
    let pp = super::frogdrop_sched::p();
    let mut b = B::new();
    let zlow = b.alloc_n(256 - w);
    let jt = b.alloc_n(w);
    let mut z = zlow.clone();
    z.extend_from_slice(&jt);
    let a = b.alloc_n(255);
    let ylow = b.alloc_n(4);
    let flag = b.alloc();
    let ms = Ms::alloc(&mut b);
    pf::seed_ms255_mode(&mut b, &ms, &z, &a, &ylow, flag, w, sg);
    b.flush_dependency();
    let mut rng = Rng::new(seed);
    let (mut jv, mut av, mut yv) = (vec![], vec![], vec![]);
    for s in 0..64 {
        let j = match s { 0 => 0, 1 => 1, 2 => (1 << w) - 1, 3 => (1 << w) - 2, _ => (rng.next() as usize) & ((1 << w) - 1) };
        let mut x = rng.below(255);
        if s == 4 { x = N::from(1u64); }
        // (no all-ones multiplicand: it is adversarial to the 32-lane carry headroom that both versions share)
        if s == 5 { x = (N::from(1u64) << 254) + N::from(1u64); }
        if x == N::ZERO { x = N::from(3u64); }
        jv.push(N::from(j as u64));
        av.push(x);
        yv.push(rng.below(4));
    }
    let (jv2, av2, yv2, jt2, a2, y2) = (jv.clone(), av.clone(), yv.clone(), jt.clone(), a.clone(), ylow.clone());
    let width = b.width() as usize;
    let r = run(&b.ops, width, &move |q| {
        for s in 0..64 {
            put(q, &jt2, s, &jv2[s]);
            put(q, &a2, s, &av2[s]);
            put(q, &y2, s, &yv2[s]);
        }
    });
    for s in 0..64 {
        assert_eq!(get(&r.q, &z, s) % pp, (jv[s] * av[s]) % pp, "seed value shot {s} j {} a {:#x} mode {:?} w {w}", jv[s], av[s], sg);
        assert_eq!(get(&r.q, &a, s), av[s], "a restored");
        assert_eq!(get(&r.q, &ylow, s), yv[s], "dirty restored");
        assert_eq!(getb(&r.q, flag, s), 0, "flag clean");
        assert_eq!(getb(&r.q, ms.k, s), 0, "k clean");
    }
    assert_eq!(r.phase, 0, "phase");
    b.tof
}

/// P1's seed (seed_ms255), tree and Schoggistängeli, values on 64 shots per seed; prints T per transposition.
#[test]
fn schoggi_seed_ms255_values() {
    for &w in &[3usize, 11] {
        let t_tree = seed_case(None, w, 11 + w as u64);
        let t_sg = seed_case(Some((pf::SCHOGGI_ZT, pf::SCHOGGI_H)), w, 11 + w as u64);
        let t_sg2 = seed_case(Some((pf::SCHOGGI_ZT, pf::SCHOGGI_H)), w, 99 + w as u64);
        assert_eq!(t_sg, t_sg2);
        let n = ((1u64 << w) - 1) as f64;
        eprintln!("SEED P1 w {w}: tree {t_tree} T ({:.1} per transposition), schoggi {t_sg} T ({:.1}), delta {}",
                  t_tree as f64 / n, t_sg as f64 / n, t_tree as i64 - t_sg as i64);
    }
}

fn consume_case(sg: Option<(usize, usize)>, w: usize, seed: u64, wide: bool) -> u64 {
    // z = a * y mod p (a's top w bits in z's top lanes), recorded and played forward
    let pp = super::frogdrop_sched::p();
    let mut b = B::new();
    let zlow = b.alloc_n(256 - w);
    let atop = b.alloc_n(w);
    let mut z = zlow.clone();
    z.extend_from_slice(&atop);
    let nlow = if wide { 256 - w } else { 255 - w };
    let alow = b.alloc_n(nlow);
    let y = b.alloc_n(256);
    let flag = b.alloc();
    let ms = Ms::alloc(&mut b);
    let r = if wide {
        pf::rec_product_consume_ms_mode(&mut b, &ms, &z, &alow, &y, flag, false, sg)
    } else {
        pf::rec_product_consume_ms_w_mode(&mut b, &ms, &z, &alow, &y, flag, w, None, sg)
    };
    // forward only: playing r and its inverse back to back would cancel in the builder's peephole index (in the row
    // the phase fixes sit between them); the inverse is the exact reversed gate list of r
    b.play(&r, false);
    b.flush_dependency();
    let tof = b.tof;
    let mut rng = Rng::new(seed);
    let (mut lv, mut tv, mut yv) = (vec![], vec![], vec![]);
    for s in 0..64 {
        let mut t = N::from((rng.next() as usize & ((1 << w) - 1)) as u64);
        if s == 0 { t = N::ZERO; }
        if s == 1 { t = N::from(((1u64 << w) - 1) as u64); }
        let l = rng.below(nlow);
        let mut yy = rng.below(256) % pp;
        if yy == N::ZERO { yy = N::from(5u64); }
        lv.push(l);
        tv.push(t);
        yv.push(yy);
    }
    let (lv2, tv2, yv2, al2, at2, y2) = (lv.clone(), tv.clone(), yv.clone(), alow.clone(), atop.clone(), y.clone());
    let init = move |q: &mut Vec<u64>| {
        for s in 0..64 {
            put(q, &al2, s, &lv2[s]);
            put(q, &at2, s, &tv2[s]);
            put(q, &y2, s, &yv2[s]);
        }
    };
    let width = b.width() as usize;
    let fwd = run(&b.ops, width, &init);
    for s in 0..64 {
        let a = lv[s] + (tv[s] << nlow);
        assert_eq!(get(&fwd.q, &z, s) % pp, (a % pp).mul_mod(yv[s], pp), "product shot {s} mode {:?} w {w}", sg);
        assert_eq!(get(&fwd.q, &y, s), yv[s]);
        assert_eq!(get(&fwd.q, &alow, s), lv[s]);
        assert_eq!(getb(&fwd.q, flag, s), 0);
        assert_eq!(getb(&fwd.q, ms.k, s), 0);
    }
    assert_eq!(fwd.phase, 0);
    tof
}

/// P5's product (rec_product_consume_ms_w, w = 11, 244 + 11 multiplier bits) and the P2/P4 product
/// (rec_product_consume_ms, w = 5): value on the forward recording, tree and Schoggistängeli.
#[test]
fn schoggi_consume_products() {
    let sgm = Some((pf::SCHOGGI_ZT, pf::SCHOGGI_H));
    let t0 = consume_case(None, 11, 5, false);
    let t1 = consume_case(sgm, 11, 5, false);
    let _ = consume_case(sgm, 11, 6, false);
    eprintln!("CONSUME P5 w 11: tree {t0} T, schoggi {t1} T per execution, delta {} ({:.1} per transposition)",
              t0 as i64 - t1 as i64, (t0 as f64 - t1 as f64) / 2047.0);
    let u0 = consume_case(None, 5, 7, true);
    let u1 = consume_case(sgm, 5, 7, true);
    eprintln!("CONSUME P2/P4 w 5: tree {u0} T, schoggi {u1} T per execution, delta {}", u0 as i64 - u1 as i64);
}


/// The Schoggistängeli fold against exact (t + ctl k) mod 2^256: carry-heavy and borrow-heavy low parts (runs of ones
/// below lane 41, tiny values that make the -2^6 digit borrow through the whole low span, all-zero low lanes), with
/// lane 41 clear (no carry leaves the shared 42-lane end) and lane 63 clear (the tree's own 2^32 headroom).
#[test]
fn schoggi_fold_values() {
    use super::modp_frogdrop::C;
    for &(lo, k) in &[(0usize, C), (4usize, C - 1)] {
        let mut b = B::new();
        let t = b.alloc_n(256);
        let g = b.alloc_n(256);
        let ctl = b.alloc();
        pf::sg_add_small(&mut b, &t, lo, ctl, k, &g, pf::SCHOGGI_H);
        b.flush_dependency();
        let tof = b.tof;
        for seed in 0..4u64 {
            let mut rng = Rng::new(seed * 7 + lo as u64);
            let mut tv: Vec<N> = vec![];
            let mut gv: Vec<N> = vec![];
            for s in 0..64 {
                let mut x = rng.below(256);
                match s % 6 {
                    0 => { for j in 0..41 { x |= N::from(1u64) << j; } }
                    1 => { let m64: N = (N::from(1u64) << 64) - N::from(1u64); x &= !m64; x |= N::from((s as u64) & 31); }
                    2 => { let m64: N = (N::from(1u64) << 64) - N::from(1u64); x &= !m64; }
                    3 => { for j in 32..63 { x |= N::from(1u64) << j; } }
                    4 => { x = N::from((s as u64) % 47); }
                    _ => {}
                }
                let b41: N = N::from(1u64) << 41;
                let b63: N = N::from(1u64) << 63;
                x &= !b41;
                x &= !b63;
                tv.push(x);
                gv.push(rng.below(256));
            }
            let (tv2, gv2, t2, g2) = (tv.clone(), gv.clone(), t.clone(), g.clone());
            let width = b.width() as usize;
            let r = run(&b.ops, width, &move |w| {
                for s in 0..64 {
                    put(w, &t2, s, &tv2[s]);
                    put(w, &g2, s, &gv2[s]);
                    if s % 3 != 2 { w[ctl.0 as usize] |= 1 << s; }
                }
            });
            let m256 = (N::from(1u64) << 256) - N::from(1u64);
            for s in 0..64 {
                let c = s % 3 != 2;
                let want = (tv[s] + if c { N::from(k) } else { N::ZERO }) & m256;
                assert_eq!(get(&r.q, &t, s), want, "sg fold lo {lo} shot {s} t {:#x}", tv[s]);
                assert_eq!(get(&r.q, &g, s), gv[s], "dirty restored");
                assert_eq!(getb(&r.q, ctl, s), c as u64, "ctrl restored");
            }
            assert_eq!(r.phase, 0);
        }
        eprintln!("SGFOLD lo {lo}: ok ({tof} T)");
    }
}

/// More random shots of the two w = 11 seed forms (P1 seed and P5 product) with Schoggistängeli on.
#[test]
fn schoggi_more_shots() {
    let sgm = Some((pf::SCHOGGI_ZT, pf::SCHOGGI_H));
    for seed in 0..6u64 {
        seed_case(sgm, 11, 1000 + seed);
        consume_case(sgm, 11, 2000 + seed, false);
    }
    eprintln!("SGMORE: 6 x 64 shots of each form ok");
}
