//! agent_lowq_quot: the K-lane remainder V form on the 694 frame (R = ring[0..20) + sx[1..5), the window top ring[19]
//! shared as in the virtual zero; sx[5] is a dirty passenger) against the K24 reference reciprocal model.
use super::builder::{B, G};
use super::frogdrop_col::{rec, ColPar};
use super::frogdrop_sched::N;
use super::midg::{stage1_v, S1, TC};
use super::tests_frogdrop::{run, Rng};
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT};

fn put(q: &mut [u64], reg: &[QubitId], lane: usize, v: N) {
    for (i, p) in reg.iter().enumerate() {
        q[p.0 as usize] = (q[p.0 as usize] & !(1u64 << lane)) | (u64::from(v.bit(i)) << lane);
    }
}
fn get(q: &[u64], reg: &[QubitId], lane: usize) -> N {
    reg.iter().enumerate().fold(N::ZERO, |v, (i, p)| v | (N::from((q[p.0 as usize] >> lane) & 1) << i))
}
struct Frame { ring: Vec<QubitId>, sx: Vec<QubitId>, sz: Vec<QubitId>, bank: Vec<QubitId>, dirty: Vec<QubitId>,
               act: QubitId }
fn frame(b: &mut B, cp: &ColPar) -> Frame {
    assert_eq!((cp.n, cp.nq, cp.k, cp.h), (277, 128, 18, 20));
    let ring = b.alloc_n(277);
    let q = b.alloc_n(128);
    let _sy = b.alloc_n(8);
    let sx = b.alloc_n(8);
    let _ph = b.alloc();
    let pool = b.alloc_n(13);
    let dirty = b.alloc_n(259);
    assert_eq!(b.width(), 694);
    let mut sz = pool[..8].to_vec();
    if cp.sz.1 > 255 { sz.push(pool[8]); }
    let mt = (cp.n - (cp.sz.0 + cp.h) + 1).min(cp.nq.max(cp.xw) + 1);
    let kmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0).min(super::mid2::QF).min(mt);
    let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
    let end = cp.nq - if cp.dn { super::pointadd_frogdrop::CNTB } else { 0 };
    let start = lsb.max(cp.sy.1.min(cp.nq) + kmax);
    let bank = if start < end { q[start..end].to_vec() } else { vec![] };
    Frame { ring, sx, sz, bank, dirty, act: pool[12] }
}
fn r_lanes(f: &Frame, klane: bool) -> Vec<QubitId> {
    let mut r = f.ring[..20].to_vec();
    r.extend(f.sx[1..if klane { 5 } else { 6 }].iter().copied());
    r
}
fn layout(f: &Frame, klane: bool) -> S1 {
    let bank = f.bank.clone();
    S1 { r: r_lanes(f, klane), f: f.sx[0], zero: f.ring[19], sgn: f.sx[0], gt: vec![f.sx[0]],
         anc: bank.iter().skip(1).copied().collect(), andc: bank.clone(), chain: bank, dirty: f.dirty.clone() }
}
fn vform(b: &mut B, f: &Frame, cp: &ColPar, klane: bool) -> Vec<G> {
    let s = layout(f, klane);
    let fv = stage1_v(b, &f.ring[253..277], &f.ring[19..20 + TC], &f.sz, cp.sz, &s, f.act, true);
    let fr = stage1_v(b, &f.ring[253..277], &f.ring[19..20 + TC], &f.sz, cp.sz, &s, f.act, false);
    rec(b, |b| { b.play(&fv, false); b.play(&fr, true); })
}
fn emitted(b: &mut B, r: &[G], inverse: bool) -> Vec<Op> {
    assert!(b.ops.is_empty());
    b.play(r, inverse);
    std::mem::take(&mut b.ops)
}
fn symbolic(ops: &[Op], mut q: Vec<u64>) -> Vec<u64> {
    let mut measured = std::collections::BTreeMap::new();
    let mut phases = Vec::<u64>::new();
    let mut constant = 0u64;
    for op in ops {
        let t = op.q_target.0 as usize;
        let a = op.q_control1.0 as usize;
        let c = op.q_control2.0 as usize;
        match op.kind {
            K::X => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= u64::MAX; }
            K::CX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a]; }
            K::CCX => { assert_eq!(op.c_condition, NO_BIT); q[t] ^= q[a] & q[c]; }
            K::Swap => { assert_eq!(op.c_condition, NO_BIT); q.swap(a, t); }
            K::Hmr => { measured.insert(op.c_target, phases.len()); phases.push(q[t]); q[t] = 0; }
            K::CZ => {
                if op.c_condition == NO_BIT { constant ^= q[a] & q[t]; }
                else { phases[measured[&op.c_condition]] ^= q[a] & q[t]; }
            }
            other => panic!("unexpected op {other:?}"),
        }
    }
    assert_eq!(constant, 0, "constant phase");
    assert!(phases.iter().all(|&v| v == 0), "independent HMR coefficient");
    q
}
fn apply(ops: &[Op], input: &[u64]) -> Vec<u64> {
    let q = symbolic(ops, input.to_vec());
    let actual = run(ops, input.len(), &|w| *w = input.to_vec());
    assert_eq!(actual.phase, 0, "native phase");
    assert_eq!(actual.q, q, "native vs symbolic");
    q
}
fn input(f: &Frame, cp: &ColPar, mode: usize, seed: u64) -> Vec<u64> {
    let mut rng = Rng::new(seed);
    let mut q: Vec<_> = (0..694).map(|_| rng.next()).collect();
    let act = [0, u64::MAX, 0x00ff_0f0f_3333_5555, 0xa55a_c33c_0ff0_f00f][mode];
    q[f.act.0 as usize] = act;
    // K-lane R (incl. the shared window top ring[19]) is clean on the act shots; sx[5] stays an arbitrary passenger
    for &p in r_lanes(f, true).iter() { q[p.0 as usize] &= !act; }
    q[f.ring[276].0 as usize] |= act;
    q[f.sx[0].0 as usize] = 0;
    for &p in &f.bank { q[p.0 as usize] = 0; }
    let sizes = [57usize, 128, 133, 230, 231, 232, 233, 234, 255, 256];
    let tt = N::from_str_radix("11884e93b469ce87829ca3198b81d79443", 16).unwrap();
    for lane in 0..64 {
        let sz = sizes[lane % sizes.len()].max(cp.sz.0).min(cp.sz.1);
        put(&mut q, &f.sz, lane, N::from(sz as u64));
        if ((act >> lane) & 1) == 0 { continue; }
        let zh = match lane % 5 {
            0 => N::from(1u64) << 23,
            1 => (N::from(1u64) << 24) - N::from(1u64),
            2 => tt >> (133 - 24),
            _ => rng.below(23) | (N::from(1u64) << 23),
        };
        put(&mut q, &f.ring[253..277], lane, zh);
        let ss = sz - 24;
        let divisor = zh | N::from(1u64);
        let reciprocal = ((N::from(1u64) << (256 - ss)) - N::from(1u64)) / divisor;
        let u = (257 - sz).saturating_sub(TC);
        let t = N::from(1u64) << (257 - sz);
        let tie = (reciprocal >> u) << u;
        let w = match lane % 4 {
            0 => tie, 1 => tie + N::from(1u64),
            2 => tie.saturating_sub(N::from(1u64)), _ => rng.below(257 - sz),
        } & (t - N::from(1u64));
        for i in 0..=TC {
            let pos = 257isize - sz as isize - i as isize;
            if pos >= 0 {
                let p = f.ring[19 + i];
                q[p.0 as usize] = (q[p.0 as usize] & !(1 << lane)) | (u64::from(w.bit(pos as usize)) << lane);
            }
        }
    }
    q
}
fn expected(f: &Frame, input: &[u64]) -> Vec<u64> {
    let mut q = input.to_vec();
    for lane in 0..64 {
        if ((input[f.act.0 as usize] >> lane) & 1) == 0 { continue; }
        let sz = get(input, &f.sz, lane).as_limbs()[0] as usize;
        let divisor = get(input, &f.ring[253..277], lane) | N::from(1u64);
        let u = (257 - sz).saturating_sub(TC);
        let reciprocal = ((N::from(1u64) << (256 - (sz - 24))) - N::from(1u64)) / divisor;
        let t = N::from(1u64) << (257 - sz);
        let delta = t - (((reciprocal >> u) + N::from(1u64)) << u);
        let mut w = N::ZERO;
        for i in 0..=TC {
            let pos = 257isize - sz as isize - i as isize;
            if pos >= 0 && ((input[f.ring[19 + i].0 as usize] >> lane) & 1) != 0 { w |= N::from(1u64) << pos as usize; }
        }
        let w = (w + delta) & (t - N::from(1u64));
        for i in 1..=TC {
            let pos = 257isize - sz as isize - i as isize;
            if pos >= 0 {
                let p = f.ring[19 + i];
                q[p.0 as usize] = (q[p.0 as usize] & !(1 << lane)) | (u64::from(w.bit(pos as usize)) << lane);
            }
        }
    }
    q
}

#[test]
fn quot_klane_vform_matches_k24_reference() {
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    for &ci in &[10usize, 60, 70, 85, 140] {
        let cp = &cols[ci];
        if !(cp.hr || cp.ht) { continue; }
        let mut tof = [0u64; 2];
        for (which, klane) in [(0usize, false), (1usize, true)] {
            let mut b = B::new();
            let f = frame(&mut b, cp);
            let t0 = b.tof;
            let r = vform(&mut b, &f, cp, klane);
            let forward = emitted(&mut b, &r, false);
            let inverse = emitted(&mut b, &r, true);
            tof[which] = forward.iter().filter(|o| matches!(o.kind, K::CCX)).count() as u64;
            let _ = t0;
            if !klane { continue; }
            for mode in 0..4 {
                let inp = input(&f, cp, mode, 0x9_0a7_000 + 31 * ci as u64 + mode as u64);
                let want = expected(&f, &inp);
                let got = apply(&forward, &inp);
                assert_eq!(got, want, "col {ci} mode {mode}: K-lane V form vs K24 reference (sx[5] untouched)");
                assert_eq!(apply(&inverse, &got), inp, "col {ci} mode {mode}: inverse");
            }
        }
        eprintln!("QUOT_KLANE col {ci} sz {:?}: vform CCX reference {} k-lane {}", cp.sz, tof[0], tof[1]);
    }
}

// ------------------------------------------------------------------------------------------------ the map at N270
fn putn(w: &mut [u64], qs: &[QubitId], shot: usize, v: &N) {
    for (i, q) in qs.iter().enumerate() {
        let bit = if i < 256 { v.bit(i) } else { false };
        let x = &mut w[q.0 as usize];
        *x = (*x & !(1u64 << shot)) | ((bit as u64) << shot);
    }
}
fn getn(w: &[u64], qs: &[QubitId], shot: usize) -> N {
    let mut v = N::ZERO;
    for (i, q) in qs.iter().enumerate() {
        if (w[q.0 as usize] >> shot) & 1 == 1 { assert!(i < 256, "value beyond 256 bits"); v |= N::from(1u64) << i; }
    }
    v
}
fn rev_put(w: &mut [u64], lanes: &[QubitId], shot: usize, v: &N) {
    let r: Vec<QubitId> = lanes.iter().rev().copied().collect();
    putn(w, &r, shot, v);
}
fn rev_getn(w: &[u64], lanes: &[QubitId], shot: usize) -> N {
    let r: Vec<QubitId> = lanes.iter().rev().copied().collect();
    getn(w, &r, shot)
}
fn bl(x: &N) -> usize { x.bit_len() }
fn pv() -> N { super::frogdrop_sched::p() }
fn modinv(a: &N, m: &N) -> N {
    // a^-1 mod m by extended Euclid on (m, a mod m), signed via (value, negative) pairs
    let (mut r0, mut r1) = (*m, *a % *m);
    let (mut t0, mut t1): ((N, bool), (N, bool)) = ((N::ZERO, false), (N::from(1u64), false));
    while !r1.is_zero() {
        let q = r0 / r1;
        let r2 = r0 - q * r1;
        // t2 = t0 - q t1 (signed)
        let qt = q * t1.0;
        let t2 = if t0.1 == t1.1 {
            if t0.0 >= qt { (t0.0 - qt, t0.1) } else { (qt - t0.0, !t0.1) }
        } else { (t0.0 + qt, t0.1) };
        r0 = r1; r1 = r2; t0 = t1; t1 = t2;
    }
    assert_eq!(r0, N::from(1u64), "not coprime");
    if t0.1 { *m - (t0.0 % *m) } else { t0.0 % *m }
}
fn gcd(a: &N, b: &N) -> N { let (mut x, mut y) = (*a, *b); while !y.is_zero() { let r = x % y; x = y; y = r; } x }

/// One map case Z X + y Y = p with X = 2^e Xo or Y = 2^f Yo (large v2), bl(Y) <= bl(X) <= bx.
fn map_case(rng: &mut Rng, bx: usize, ex: usize, ey: usize) -> (N, N, N, N) {
    let p = pv();
    loop {
        let bxo = bx - ex;
        let xo = (rng.below(bxo - 1) | (N::from(1u64) << (bxo - 1))) | N::from(1u64);
        let x = xo << ex;
        let by = (bx - 8 + (rng.next() as usize % 9)).min(bx);
        let byo = by - ey;
        let yo = (rng.below(byo - 1) | (N::from(1u64) << (byo - 1))) | N::from(1u64);
        let y = yo << ey;
        if gcd(&x, &y) != N::from(1u64) { continue; }
        let yv = (p % x) * modinv(&(y % x), &x) % x;
        if yv * y >= p { continue; }
        let z = (p - yv * y) / x;
        if z.is_zero() { continue; }
        assert_eq!(z * x + yv * y, p);
        return (z, x, y, yv);
    }
}

fn map_test(n: usize, label: &str) { map_test_sw(n, label, false) }
fn map_test_sw(n: usize, label: &str, sw: bool) { map_test_gen(n, label, sw, 100, 29) }
fn map_test_gen(n: usize, label: &str, sw: bool, blo: usize, bspan: usize) {
    use super::frogdrop_col::{map_stage, ColScr, Fd};
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let mut rng = Rng::new(0x9_0a7_2700 + n as u64);
    let mut cases = vec![];
    for shot in 0..64 {
        let bx = blo + rng.next() as usize % bspan;
        let e = [0, 23, 22, 20, 17, 13, 9, 5, 1, 0, 0, 0, 3, 7, 11, super::pointadd_frogdrop::EMAX][shot % 16].min(super::pointadd_frogdrop::EMAX);
        let (ex, ey) = if shot % 2 == 0 { (e, 0) } else { (0, e.min(bx - 10)) };
        cases.push(map_case(&mut rng, bx, ex, ey));
    }
    let mx = |c: &(N, N, N, N)| bl(&c.1).max(bl(&c.2));
    let mut cp = cols[60].clone();
    cp.n = n; cp.h = n - 257; cp.sw = sw; cp.dn = false; cp.fin = false; cp.nomap = false; cp.emax = super::pointadd_frogdrop::EMAX;
    cp.cntw = 0;
    cp.m = cases.iter().map(|c| mx(c)).max().unwrap();
    cp.smax = (cases.iter().map(|c| mx(c)).min().unwrap(), cp.m);
    cp.sy = (cases.iter().map(|c| bl(&c.2)).min().unwrap(), cases.iter().map(|c| bl(&c.2)).max().unwrap());
    cp.sz = (cases.iter().map(|c| bl(&c.0)).min().unwrap(), cases.iter().map(|c| bl(&c.0)).max().unwrap());
    for (s, c) in cases.iter().enumerate() {
        let need = (bl(&c.0) + c.1.trailing_zeros()).max(bl(&c.3) + c.2.trailing_zeros()) + mx(c);
        assert!(super::frogdrop_col::map_tz() || need <= 280, "shot {s}: frame need {need}");
    }
    let mut b = B::new();
    let ring = b.alloc_n(n);
    let payload = b.alloc_n(259);
    let q = b.alloc_n(128);
    let sy = b.alloc_n(8);
    let sx = b.alloc_n(8);
    let ph = b.alloc();
    let pool = b.alloc_n(13);
    let width = b.width() as usize;
    assert_eq!(width, n + 417);
    let fd = Fd { ring: ring.clone(), q: q.clone(), sy: sy.clone(), sx: sx.clone(), ph, cnt: q[121..].to_vec() };
    let sc = ColScr::carve_col(&pool, &fd.sx, &payload, cp.kp, cp.qb, cp.tail, false);
    let t0 = b.tof;
    let record = map_stage(&mut b, &fd, &cp, &sc);
    b.play(&record, false);
    let tof = b.tof - t0;
    let forward = b.ops.len();
    b.play(&record, true);
    let mut input = vec![0u64; width];
    for &lane in &payload { input[lane.0 as usize] = rng.next(); }
    input[ph.0 as usize] = 0;
    for (s, (z, x, y, _)) in cases.iter().enumerate() {
        let cut = n - mx(&cases[s]);
        putn(&mut input, &ring[..cut], s, z);
        rev_put(&mut input, &ring[cut..], s, y);
        putn(&mut input, &q, s, x);
        putn(&mut input, &sy, s, &N::from(bl(y) as u64));
    }
    let f = run(&b.ops[..forward], width, &|w| *w = input.clone());
    assert_eq!(f.phase, 0, "{label} forward phase");
    for (s, (_, x, y, yv)) in cases.iter().enumerate() {
        let cut = n - mx(&cases[s]);
        assert_eq!(getn(&f.q, &ring[..cut], s), *yv, "{label} map bottom shot {s}");
        assert_eq!(rev_getn(&f.q, &ring[cut..], s), *x, "{label} map top shot {s}");
        assert_eq!(getn(&f.q, &q, s), *y, "{label} map Q shot {s}");
    }
    let both = run(&b.ops, width, &|w| *w = input.clone());
    assert_eq!(both.phase, 0, "{label} round-trip phase");
    assert_eq!(both.q, input, "{label} forward/inverse restores scratch and dirty passengers");
    eprintln!("QUOT_MAP {label} n={n} width={width} map_T={tof} ops={forward} m={} smax={:?}", cp.m, cp.smax);
}

#[test]
fn quot_map_n278_large_v2() { map_test(278, "n278"); }

#[test]
fn quot_map_n270_syfree_ext10_large_v2() { map_test(270, "n270"); }

#[test]
fn quot_map_columns_n270_budget() {
    let (cols, b0, last) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let n = 270;
    let mut worst = 0;
    for (i, cp) in cols.iter().enumerate() {
        if cp.nomap { continue; }
        let extra = if cp.sw { (2 * cp.nq + cp.emax).saturating_sub(n) } else { (257 + cp.emax).saturating_sub(n) };
        let ctop = cp.nq - super::pointadd_frogdrop::CNTB;
        let lean_park = cp.dn && cp.m > ctop;
        let nc = if lean_park { cp.cntw.min(super::pointadd_frogdrop::CNTB) } else { 0 };
        let need = extra + nc;
        worst = worst.max(need);
        if lean_park || cp.sw || need > 9 {
            eprintln!("QUOT_MAPCOL {i}: sw {} dn {} hr {} m {} cntw {} lean_park {lean_park} extra {extra} park {nc} need {need}",
                      cp.sw, cp.dn, cp.hr, cp.m, cp.cntw);
        }
    }
    eprintln!("QUOT_MAPCOL worst extension+park {worst} (sy-free budget: bq + 9 lean lanes = 10); b0 {:?} last {:?}",
              b0.map(|c| (c.m, c.dn, c.cntw)), (last.m, last.dn, last.nomap));
}

#[test]
fn quot_map_n270_switch_column() { map_test_sw(270, "n270sw", true); }

#[test]
fn quot_map_n270_b0_controlled() { b0_controlled(270); }
/// agent_lowq_quot QUOT_MAP_TZ=1 (run with it set): the controlled B0 map on the trailing-zero room
#[test]
#[ignore]
fn quot_map_tz_b0_n267() { b0_controlled(267); }
#[test]
#[ignore]
fn quot_map_tz_b0_n266() { b0_controlled(266); }
fn b0_controlled(n: usize) {
    use super::frogdrop_col::{map_stage, ColScr, Fd};
    let (_, b0, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let mut cp = b0.expect("B0 column");
    cp.n = n; cp.h = n - 257; cp.emax = super::pointadd_frogdrop::EMAX;
    let mut b = B::new();
    let ring = b.alloc_n(n);
    let payload = b.alloc_n(259);
    let q = b.alloc_n(128);
    let sy = b.alloc_n(8);
    let sx = b.alloc_n(8);
    let ph = b.alloc();
    let pool = b.alloc_n(13);
    let width = b.width() as usize;
    let fd = Fd { ring: ring.clone(), q: q.clone(), sy: sy.clone(), sx, ph, cnt: q[121..].to_vec() };
    let sc = ColScr::carve_col(&pool, &fd.sx, &payload, cp.kp, cp.qb, cp.tail, false);
    b.allow_booth = false;
    let record = map_stage(&mut b, &fd, &cp, &sc);
    // (B0_UNCTRL=1: the record played on every shot, the active mask all ones)
    let unctrl = std::env::var_os("B0_UNCTRL").is_some();
    if unctrl { b.play(&record, false); } else { b.play_ctrl(&record, sc.sw, sc.g); }
    let forward = b.ops.len();
    let inverse = super::frogdrop_col::rec(&mut b, |b| b.play(&record, true));
    if unctrl { b.play(&inverse, false); } else { b.play_ctrl(&inverse, sc.sw, sc.g); }
    let mut input = vec![0u64; width];
    let mut rng = Rng::new(0xd3_b0_000 + n as u64);
    let active = if unctrl { u64::MAX } else { 0x55aa_33cc_f00f_0ff0u64 };
    input[sc.sw.0 as usize] = active;
    input[ph.0 as usize] = u64::MAX;
    for &lane in &payload { input[lane.0 as usize] = rng.next(); }
    let p = pv();
    let mut cases = Vec::new();
    for lane in 0..64 {
        // R even with large v2 on some lanes (X = R, Y = 1): Z = p - R t
        let e = [0usize, 1, 5, 13, 20, super::pointadd_frogdrop::EMAX.min(25)][lane % 6];
        let rb = 26 - e;
        let odd: u64 = (rng.next() % (1u64 << (rb - 1))) | 1;
        let r: N = N::from(odd) << e;
        let y = N::from(1u64);
        let k = rng.below(200) | N::from(1u64);
        let z = (p - k) / r;
        let x = r;
        let cut = n - bl(&x).max(bl(&y));
        assert!(super::frogdrop_col::map_tz() || bl(&z) + x.trailing_zeros() + bl(&x).max(bl(&y)) <= 280);
        putn(&mut input, &ring[..cut], lane, &z);
        rev_put(&mut input, &ring[cut..], lane, &y);
        putn(&mut input, &q, lane, &x);
        putn(&mut input, &sy, lane, &N::from(bl(&y) as u64));
        cases.push((lane, cut, x, y, (p - z * x) / y));
    }
    let out = run(&b.ops[..forward], width, &|w| *w = input.clone());
    assert_eq!(out.phase, 0);
    for (lane, cut, x, y, want) in cases.iter() {
        if (active >> lane) & 1 == 1 {
            assert_eq!(getn(&out.q, &ring[..*cut], *lane), *want, "active B0 bottom {lane}");
            assert_eq!(rev_getn(&out.q, &ring[*cut..], *lane), *x, "active B0 top {lane}");
            assert_eq!(getn(&out.q, &q, *lane), *y, "active B0 Q {lane}");
        }
    }
    let both = run(&b.ops, width, &|w| *w = input.clone());
    assert_eq!(both.phase, 0);
    assert_eq!(both.q, input, "controlled B0 forward/inverse cleanup");
    eprintln!("QUOT_MAP B0 n{n} cases={} forward_ops={forward}", cases.len());
}

#[test]
fn quot_map_n270_wide_sizes() { map_test_gen(270, "n270wide", false, 34, 95); }

#[test]
fn quot_map_n278_wide_sizes() { map_test_gen(278, "n278wide", false, 34, 95); }

/// A late lean-park column (done shots with an idle counter in Q[121..], big stepping shots, small stepping shots)
/// at ring n: map exact, counter restored, everything else restored by the inverse.
fn map_test_done(n: usize, ci: usize, label: &str) {
    use super::frogdrop_col::{map_stage, ColScr, Fd};
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let p = pv();
    let mut cp = cols[ci].clone();
    cp.emax = super::pointadd_frogdrop::EMAX;
    assert!(cp.dn && cp.m > 121, "lean-park column");
    let cntw = cp.cntw;
    let mut rng = Rng::new(0x9_d0e_0000 + 1000 * n as u64 + ci as u64);
    // (z, x, y, yv, cnt, kind)
    let mut cases: Vec<(N, N, N, N, u64, u8)> = vec![];
    for shot in 0..64 {
        match shot % 4 {
            0 | 1 => {
                // done: {X, Y} = {R, 1}, R < 2^26 with v2 up to 23
                let e = [0usize, 3, 9, 17, 23, 1, 0, 12][(shot / 4) % 8].min(if cols[ci].sw { 22 } else { 23 });
                let rb = 26 - e;
                let odd: u64 = (rng.next() % (1u64 << (rb - 1))) | 1 | (1u64 << (rb - 1)) >> 1;
                let r: N = (N::from(odd) | N::from(1u64)) << e;
                let r = if r == N::from(1u64) { N::from(3u64) } else { r };
                let cnt = 1 + rng.next() % ((1u64 << cntw) - 1);
                if shot % 4 == 0 {
                    // X = R (Q), Y = 1: y = p - Z R
                    let z = (p - (rng.below(64) | N::from(1u64))) / r;
                    cases.push((z, r, N::from(1u64), p - z * r, cnt, 0));
                } else {
                    // X = 1 (Q), Y = R: Z = p - y R
                    let yv = (p / r) - rng.below(64);
                    cases.push((p - yv * r, N::from(1u64), r, yv, cnt, 0));
                }
            }
            2 => {
                // big stepping shot (Q value >= 2^64 so the done test is false)
                let bx = 100 + rng.next() as usize % 29;
                let e = [0usize, 23, 20, 13, 5, 0, 0, 7][(shot / 4) % 8].min(if cols[ci].sw { 22 } else { 23 });
                let (ex, ey) = if (shot / 4) % 2 == 0 { (e, 0) } else { (0, e) };
                let c = map_case(&mut rng, bx, ex, ey);
                cases.push((c.0, c.1, c.2, c.3, 0, 1));
            }
            _ => {
                // small stepping shot below 2^64: the done test's Q part is true, counter zero
                let bsmall = 40 + rng.next() as usize % 20;
                let c = map_case(&mut rng, bsmall, 0, 0);
                cases.push((c.0, c.1, c.2, c.3, 0, 2));
            }
        }
    }
    let mx = |c: &(N, N, N, N, u64, u8)| bl(&c.1).max(bl(&c.2));
    cp.n = n; cp.h = n - 257;
    cp.smax = (cases.iter().map(|c| mx(c)).min().unwrap(), cases.iter().map(|c| mx(c)).max().unwrap());
    cp.m = cp.m.max(cp.smax.1);
    cp.sy = (cases.iter().map(|c| bl(&c.2)).min().unwrap(), cases.iter().map(|c| bl(&c.2)).max().unwrap());
    cp.sz = (cases.iter().map(|c| bl(&c.0)).min().unwrap(), cases.iter().map(|c| bl(&c.0)).max().unwrap());
    let frame = if cp.sw { 2 * cp.nq + cp.emax } else { 257 + cp.emax };
    for (s, c) in cases.iter().enumerate() {
        let need = (bl(&c.0) + c.1.trailing_zeros()).max(bl(&c.3) + c.2.trailing_zeros()) + mx(c);
        assert!(need <= frame.max(n), "shot {s}: frame need {need}");
    }
    let mut b = B::new();
    let ring = b.alloc_n(n);
    let payload = b.alloc_n(259);
    let q = b.alloc_n(128);
    let sy = b.alloc_n(8);
    let sx = b.alloc_n(8);
    let ph = b.alloc();
    let pool = b.alloc_n(13);
    let width = b.width() as usize;
    let fd = Fd { ring: ring.clone(), q: q.clone(), sy: sy.clone(), sx: sx.clone(), ph, cnt: q[121..].to_vec() };
    let sc = ColScr::carve_col(&pool, &fd.sx, &payload, cp.kp, cp.qb, cp.tail, false);
    let t0 = b.tof;
    let record = map_stage(&mut b, &fd, &cp, &sc);
    b.play(&record, false);
    let tof = b.tof - t0;
    let forward = b.ops.len();
    b.play(&record, true);
    let mut input = vec![0u64; width];
    for &lane in &payload { input[lane.0 as usize] = rng.next(); }
    // every shot of an HR-free column is HT or done (ph = 1); otherwise mark the big shots HR at random
    input[ph.0 as usize] = u64::MAX;
    if cp.hr { for (s, c) in cases.iter().enumerate() { if c.5 == 1 && rng.next() & 1 == 0 { input[ph.0 as usize] &= !(1u64 << s); } } }
    for (s, c) in cases.iter().enumerate() {
        let cut = n - mx(c);
        putn(&mut input, &ring[..cut], s, &c.0);
        rev_put(&mut input, &ring[cut..], s, &c.2);
        putn(&mut input, &q, s, &c.1);
        if c.5 == 0 { putn(&mut input, &q[121..], s, &N::from(c.4)); }
        putn(&mut input, &sy, s, &N::from(bl(&c.2) as u64));
    }
    let f = run(&b.ops[..forward], width, &|w| *w = input.clone());
    assert_eq!(f.phase, 0, "{label} forward phase");
    for (s, c) in cases.iter().enumerate() {
        let cut = n - mx(c);
        assert_eq!(getn(&f.q, &ring[..cut], s), c.3, "{label} map bottom shot {s} kind {}", c.5);
        assert_eq!(rev_getn(&f.q, &ring[cut..], s), c.1, "{label} map top shot {s} kind {}", c.5);
        let want_q = if c.5 == 0 { c.2 | (N::from(c.4) << 121) } else { c.2 };
        assert_eq!(getn(&f.q, &q, s), want_q, "{label} map Q (+counter) shot {s} kind {}", c.5);
    }
    let both = run(&b.ops, width, &|w| *w = input.clone());
    assert_eq!(both.phase, 0, "{label} round-trip phase");
    assert_eq!(both.q, input, "{label} forward/inverse restores everything");
    eprintln!("QUOT_MAPDONE {label} n={n} col={ci} sw={} hr={} cntw={cntw} width={width} map_T={tof}", cp.sw, cp.hr);
}

#[test]
fn quot_map_done_n278_col115() { map_test_done(278, 115, "n278c115"); }
#[test]
fn quot_map_done_n273_col115() { map_test_done(273, 115, "n273c115"); }
#[test]
fn quot_map_done_n274_col112() { map_test_done(274, 112, "n274c112"); }
#[test]
fn quot_map_done_n273_col112() { map_test_done(273, 112, "n273c112"); }
#[test]
fn quot_map_done_n273_col113() { map_test_done(273, 113, "n273c113"); }
#[test]
fn quot_map_done_n273_col104() { map_test_done(273, 104, "n273c104"); }
#[test]
fn quot_map_done_n273_col100() { map_test_done(273, 100, "n273c100"); }
#[test]
fn quot_map_done_n273_col119() { map_test_done(273, 119, "n273c119"); }
/// agent_lowq_quot QUOT_MAP_TZ=1 (run with it set): the trailing-zero-room map, no extension lanes
#[test]
#[ignore]
fn quot_map_tz_n267() { map_test(267, "tz267"); }
#[test]
#[ignore]
fn quot_map_tz_n260() { map_test(260, "tz260"); }
#[test]
#[ignore]
fn quot_map_tz_n257() { map_test(257, "tz257"); }
#[test]
#[ignore]
fn quot_map_tz_n267_switch() { map_test_sw(267, "tz267sw", true); }
#[test]
#[ignore]
fn quot_map_tz_n267_wide() { map_test_gen(267, "tz267wide", false, 34, 95); }
#[test]
#[ignore]
fn quot_map_tz_n266() { map_test(266, "tz266"); map_test_sw(266, "tz266sw", true); map_test_gen(266, "tz266wide", false, 34, 95); }
#[test]
#[ignore]
fn quot_map_tz_done_n266_cols() {
    for ci in [100, 104, 112, 113, 115, 119] { map_test_done(266, ci, &format!("tz266c{ci}")); }
}
#[test]
#[ignore]
fn quot_map_tz_done_n267_cols() {
    for ci in [100, 104, 112, 113, 115, 119] { map_test_done(267, ci, &format!("tz267c{ci}")); }
}
#[test]
#[ignore]
fn quot_map_tz_done_n262_cols() {
    for ci in [100, 112, 115, 119] { map_test_done(262, ci, &format!("tz262c{ci}")); }
}

#[test]
fn quot_map_done_n272_col115_expect_short() {
    let r = std::panic::catch_unwind(|| map_test_done(272, 115, "n272c115"));
    assert!(r.is_err(), "272 should exceed the budget at column 115 without F1/F2");
}

/// Classical failure census (predict_n) on random traversal inputs: 694 geometry (N277 / EMAX22) vs the
/// K-lane + sy-free map geometry (N276 / EMAX23). QUOT_PRED_N inputs (default 200k), split over 3 threads.
#[test]
#[ignore]
fn quot_predict_lambda() {
    super::bake_pred_knobs();
    use super::frogdrop_sched::{from_text, predict_n, sample};
    use super::pointadd_frogdrop::*;
    let total: usize = std::env::var("QUOT_PRED_N").ok().and_then(|s| s.parse().ok()).unwrap_or(200_000);
    let sched = std::sync::Arc::new(from_text(SCHED_FROGDROP));
    // QUOT_PRED_RINGS=271,273: the rings (EMAX 23) to census
    let configs: Vec<(usize, usize)> = std::env::var("QUOT_PRED_RINGS").map(|v| v.split(',').map(|x| (x.parse().unwrap(), super::pointadd_frogdrop::EMAX))
        .collect()).unwrap_or(vec![(273, 23), (276, 23), (272, 23)]);
    let nc = configs.len();
    let configs = std::sync::Arc::new(configs);
    let mut handles = vec![];
    for t in 0..3u64 {
        let sched = sched.clone();
        let configs = configs.clone();
        handles.push(std::thread::spawn(move || {
            let mut counts: Vec<std::collections::BTreeMap<&'static str, usize>> = vec![Default::default(); nc];
            let per = total / 3;
            let mut done = 0;
            let mut seed = 0x9_1a3b_0000 + t * 1_000_000;
            while done < per {
                let xs = sample(64, seed);
                seed += 1;
                for x in xs.iter() {
                    if done >= per { break; }
                    done += 1;
                    for (ci, &(nring, emax)) in configs.iter().enumerate() {
                        // (QUOT_PRED_PREC: the reciprocal precision, default 24)
                        let prec: usize = std::env::var("QUOT_PRED_PREC").ok().and_then(|v| v.parse().ok()).unwrap_or(24);
                        if let Some(k) = predict_n(*x, &sched, prec, KP, QB, TOT, NQ, emax, nring) {
                            *counts[ci].entry(k).or_insert(0) += 1;
                        }
                    }
                }
            }
            counts
        }));
    }
    let mut agg: Vec<std::collections::BTreeMap<&'static str, usize>> = vec![Default::default(); nc];
    for h in handles { for (ci, c) in h.join().unwrap().into_iter().enumerate() { for (k, v) in c { *agg[ci].entry(k).or_insert(0) += v; } } }
    let n = (total / 3) * 3;
    for (ci, &(nring, emax)) in configs.iter().enumerate() {
        let f: usize = agg[ci].values().sum();
        eprintln!("QUOT_PRED nring {nring} emax {emax}: inputs {n} fails {f} lambda(18048 walks) {:.3} by kind {:?}",
                  f as f64 / n as f64 * 18048.0, agg[ci]);
    }
}

#[test]
fn quot_column_kinds() {
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let (mut hr, mut ht, mut both, mut dl) = (0, 0, 0, 0);
    let mut kmaxes = std::collections::BTreeMap::new();
    for cp in cols.iter() {
        if cp.hr { hr += 1; } if cp.ht { ht += 1; } if cp.hr && cp.ht { both += 1; } if cp.dl || cp.dq { dl += 1; }
        let mt = (cp.n - (cp.sz.0 + cp.h) + 1).min(cp.nq.max(cp.xw) + 1);
        let kmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0).min(super::mid2::QF).min(mt);
        *kmaxes.entry(kmax).or_insert(0) += 1;
    }
    eprintln!("QUOT_KINDS cols {} hr {hr} ht {ht} both {both} dl/dq {dl} kmax histogram {:?}", cols.len(), kmaxes);
}

/// agent_lowq_quot: packed 203-column replay (64 varied payloads) of QUOT_X (hex), with the 24-bit predictor's verdict.
#[test]
#[ignore]
fn quot_replay_x() {
    super::bake_knobs();
    use super::frogdrop_sched::{from_text, predict_n, N};
    use super::pointadd_frogdrop::*;
    let x = N::from_str_radix(&std::env::var("QUOT_X").expect("QUOT_X"), 16).unwrap();
    let dy = N::from_str_radix("564b1a76853d2295410e7ccd2aa128c52f84c1e577ab7011b206b43d4e9a70cb", 16).unwrap();
    eprintln!("QUOT_X {:x}: predict_n(K24, nring {}) = {:?}", x, super::pointadd_frogdrop::N,
              predict_n(x, &from_text(SCHED_FROGDROP), 24, KP, QB, TOT, NQ, EMAX, super::pointadd_frogdrop::N));
    super::tests_frogdrop::frogdrop_col_trace_impl(x, dy, true);
}

/// agent_lowq_quot: columns whose one-session park fits a RES-lane reserve (sy.1 + kmax - 1 < 129 + RES), by kind.
#[test]
#[ignore]
fn quot_single_fit() {
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    for res in [2usize, 3, 4] {
        let (mut hr_fit, mut ht_fit, mut hr, mut ht) = (0, 0, 0, 0);
        for cp in cols.iter() {
            let mt = (cp.n - (cp.sz.0 + cp.h) + 1).min(cp.nq.max(cp.xw) + 1);
            let kmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0).min(super::mid2::QF).min(mt);
            let fit = cp.sy.1.min(128) + kmax < 130 + res;
            if cp.hr { hr += 1; if fit { hr_fit += 1; } }
            if cp.ht { ht += 1; if fit { ht_fit += 1; } }
        }
        eprintln!("QUOT_SINGLE_FIT res {res}: hr {hr_fit}/{hr} ht {ht_fit}/{ht}");
    }
    for (i, cp) in cols.iter().enumerate() {
        if cp.hr || cp.ht { eprint!("{i}:{}{}{}:{}-{} ", if cp.hr { "R" } else { "" }, if cp.ht { "T" } else { "" },
                                    if cp.dl || cp.dq { "d" } else { "" }, cp.sy.0, cp.sy.1); }
    }
    eprintln!();
}

/// agent_lowq_quot: inputs that the EMAX 23 geometry fails only by v2 (a map operand with v2 in 24..=EMAX) and the
/// current geometry predicts clean (QUOT_PICK_N inputs, default 4M; up to 6)
#[test]
#[ignore]
fn quot_pick_v2() {
    use super::frogdrop_sched::{from_text, predict_n, sample};
    use super::pointadd_frogdrop::*;
    let total: usize = std::env::var("QUOT_PICK_N").ok().and_then(|s| s.parse().ok()).unwrap_or(4_000_000);
    let sched = std::sync::Arc::new(from_text(SCHED_FROGDROP));
    let hs: Vec<_> = (0..3u64).map(|t| {
        let sched = sched.clone();
        std::thread::spawn(move || {
            let mut got = vec![];
            let mut seed = 0x0e_2a_0000 + t * 1_000_000;
            let mut done = 0;
            while done < total / 3 && got.len() < 2 {
                for x in sample(256, seed) {
                    done += 1;
                    if predict_n(x, &sched, 24, KP, QB, TOT, NQ, 23, N) == Some("v2")
                        && predict_n(x, &sched, 24, KP, QB, TOT, NQ, EMAX, N).is_none() {
                        got.push(format!("{:x}", x));
                    }
                }
                seed += 1;
            }
            got
        })
    }).collect();
    let all: Vec<String> = hs.into_iter().flat_map(|h| h.join().unwrap()).collect();
    eprintln!("PICK_V2 {:?}", all);
}

/// agent_lowq_quot: inputs whose crossing step (bl(r_j) <= L0 < bl(r_{j-1})) is parked in a wide column (sz envelope
/// >= 128 lanes, the N-chunk cuts there) with bl(q) >= QUOT_PICK_QB (default 12), split by form (HT / delayed HR),
/// model-clean under predict_n at this ring. QUOT_PICK_N inputs scanned (default 200k).
#[test]
#[ignore]
fn quot_pick_cross_wide() {
    use super::frogdrop_sched::{from_text, predict_n, sample, shot, Kind, L0};
    use super::pointadd_frogdrop::*;
    let sched = from_text(SCHED_FROGDROP);
    let total: usize = std::env::var("QUOT_PICK_N").ok().and_then(|s| s.parse().ok()).unwrap_or(200_000);
    let qbmin: usize = std::env::var("QUOT_PICK_QB").ok().and_then(|s| s.parse().ok()).unwrap_or(12);
    let p = super::frogdrop_sched::p();
    let (mut ht, mut dl) = (vec![], vec![]);
    let mut seed = 0x5eed_0000u64;
    let mut done = 0;
    while done < total && (ht.len() < 4 || dl.len() < 4) {
        for x in sample(64, seed) {
            done += 1;
            let sh = shot(x, L0);
            let (mut r, mut t) = (vec![p, x], vec![N::ZERO, N::from(1u64)]);
            while !r[r.len() - 1].is_zero() {
                let n = r.len();
                let q = r[n - 2] / r[n - 1];
                let rn = r[n - 2] - q * r[n - 1];
                let tn = t[n - 2] + q * t[n - 1];
                r.push(rn);
                t.push(tn);
            }
            let mut j = 1usize;
            for (c, rec) in sh.recs.iter().enumerate() {
                let (step, form_dl) = match rec.kind {
                    Kind::Hr | Kind::Ht => (Some(j), false),
                    Kind::Dl => (Some(j), true),
                    _ => (None, false),
                };
                if let Some(jj) = step {
                    if jj >= 1 && jj + 1 < r.len() && r[jj].bit_len() <= L0 && r[jj - 1].bit_len() > L0 {
                        let qb = (r[jj - 1] / r[jj]).bit_len();
                        let e = &sched.cols[c];
                        let wide = e.sz.1.min(255) - e.sz.0.min(255) >= 128;
                        let want_wide = std::env::var_os("QUOT_PICK_NARROW").is_none();
                        let mincol: usize = std::env::var("QUOT_PICK_MINCOL").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
                        if wide == want_wide && qb >= qbmin && c >= mincol && predict_n(x, &sched, 24, KP, QB, TOT, NQ, EMAX, N).is_none() {
                            let v = if form_dl { &mut dl } else { &mut ht };
                            if v.len() < 4 { v.push((format!("{:x}", x), c, qb)); }
                        }
                    }
                }
                match rec.kind { Kind::Hr | Kind::Ht | Kind::Dq => j += 1, _ => {} }
            }
        }
        seed += 1;
    }
    eprintln!("PICK scanned {done}: HT-form {:?}", ht);
    eprintln!("PICK delayed-HR-form {:?}", dl);
}

/// agent_lowq_quot: inputs the predictor (with QUOT_PRED_DLCHK=1 set by the caller) fails only by "dlhalf"
#[test]
#[ignore]
fn quot_pick_dlhalf() {
    use super::frogdrop_sched::{from_text, predict_n, sample};
    use super::pointadd_frogdrop::*;
    let sched = from_text(SCHED_FROGDROP);
    let mut found = vec![];
    let mut seed = 0x0d1a_0000u64;
    let mut n = 0;
    while found.len() < 4 && n < 2_000_000 {
        for x in sample(64, seed) {
            n += 1;
            if predict_n(x, &sched, 24, KP, QB, TOT, NQ, EMAX, N) == Some("dlhalf") { found.push(format!("{:x}", x)); }
        }
        seed += 1;
    }
    eprintln!("DLHALF scanned {n}: {:?}", found);
}
