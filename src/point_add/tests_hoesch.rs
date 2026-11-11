//! Hoesch (lane T1d): head_product_care::head_product at the tree's width (H = 51) and at the smaller head windows
//! the Q765_HOESCH_H knob uses. Checks, on 64 random shots per width: the 2H-lane target ends as the expected
//! product (low half B times A with A's lsb forced to 1, "implied odd"; high half initially 0), the multiplier lanes
//! a, the dirty lanes and the clean banks are restored, phase 0. Reports the Toffoli count per width.
use super::builder::B;
use super::frogdrop_sched::N;
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
        if (w[q.0 as usize] >> shot) & 1 == 1 { v |= N::from(1u64) << i; }
    }
    v
}

fn case(h: usize, nandc: usize, seed: u64) -> u64 {
    let mut b = B::new();
    let t = b.alloc_n(2 * h);
    let a = b.alloc_n(h);
    let c0 = b.alloc();
    let hh = b.alloc();
    let anc = b.alloc_n(1);
    let andc = b.alloc_n(nandc);
    let dirty = b.alloc_n(128);
    super::head_product_care::head_product(&mut b, &t, &a, c0, hh, &anc, &andc, &dirty);
    b.flush_dependency();
    let mut rng = Rng::new(seed);
    let bv: Vec<N> = (0..64).map(|s| match s { 0 => N::ZERO, 1 => (N::from(1u64) << h) - N::from(1u64), _ => rng.below(h) }).collect();
    let av: Vec<N> = (0..64).map(|s| match s { 0 | 1 => (N::from(1u64) << h) - N::from(1u64), 2 => N::ZERO, _ => rng.below(h) }).collect();
    let dv: Vec<N> = (0..64).map(|_| rng.below(128)).collect();
    let (bv2, av2, dv2, t2, a2, d2) = (bv.clone(), av.clone(), dv.clone(), t.clone(), a.clone(), dirty.clone());
    let r = run(&b.ops, b.width() as usize, &move |q| {
        for s in 0..64 { put(q, &t2[..h], s, &bv2[s]); put(q, &a2, s, &av2[s]); put(q, &d2, s, &dv2[s]); }
    });
    let m = (N::from(1u64) << (2 * h)) - N::from(1u64);
    for s in 0..64 {
        let want = (bv[s] * (av[s] | N::from(1u64))) & m;
        assert_eq!(get(&r.q, &t, s), want, "H {h} shot {s}: product");
        assert_eq!(get(&r.q, &a, s), av[s], "a restored");
        assert_eq!(get(&r.q, &dirty, s), dv[s], "dirty restored");
        let mut clean = vec![c0, hh]; clean.extend(&anc); clean.extend(&andc);
        assert_eq!(get(&r.q, &clean, s), N::ZERO, "banks clean");
    }
    assert_eq!(r.phase, 0, "phase");
    b.tof
}

#[test]
fn hoesch_head_product_widths() {
    for &h in &[51usize, 44, 40, 36, 32, 28] {
        for &nandc in &[2usize, 9, 20] {
            let t0 = case(h, nandc, 11 + h as u64);
            let t1 = case(h, nandc, 97 + h as u64);
            assert_eq!(t0, t1);
            eprintln!("HOESCH_HP H {h} andc {nandc}: head product {t0} T");
        }
    }
    eprintln!("HOESCH_HP_PASS");
}
