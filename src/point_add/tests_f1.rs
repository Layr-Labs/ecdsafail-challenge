//! F1 counter-park differential on the real 695-wire geometry.
use super::builder::{B, G};
use super::frogdrop_col::f1_lean_counter_swaps;
use super::mask::mc_xor;
use super::tests_frogdrop::{run, Rng};
use crate::circuit::{Op, OperationType, QubitId};

struct Frame {
    q: Vec<QubitId>, ph: QubitId, park: Vec<QubitId>, flag: QubitId,
    dirty: Vec<QubitId>,
}
fn frame(b: &mut B, n: usize) -> Frame {
    let _ring = b.alloc_n(278);
    let _payload = b.alloc_n(259);
    let q = b.alloc_n(128);
    let _sy = b.alloc_n(8);
    let _sx = b.alloc_n(8);
    let ph = b.alloc();
    let pool = b.alloc_n(13);
    assert_eq!(b.width(), 695);
    Frame { q, ph, park: pool[..n].to_vec(), flag: pool[7], dirty: _payload }
}
fn recipe(b: &mut B, f: &Frame, inverse: bool, shared: bool) -> Vec<G> {
    let predicate: Vec<(QubitId, bool)> = std::iter::once((f.ph, false))
        .chain((64..121).map(|i| (f.q[i], true))).collect();
    b.begin();
    if shared {
        f1_lean_counter_swaps(b, &predicate, &f.q[121..121 + f.park.len()],
                              &f.park, f.flag, &f.dirty, inverse);
    } else {
        let indices: Vec<usize> = if inverse { (0..f.park.len()).rev().collect() }
                                  else { (0..f.park.len()).collect() };
        for i in indices {
            let x = f.park[i];
            let mut l1 = predicate.clone(); l1.push((f.q[121 + i], false));
            let mut l2 = predicate.clone(); l2.push((x, false));
            if inverse {
                mc_xor(b, &l2, f.q[121 + i], &[], &f.dirty);
                mc_xor(b, &l1, x, &[], &f.dirty);
            } else {
                mc_xor(b, &l1, x, &[], &f.dirty);
                mc_xor(b, &l2, f.q[121 + i], &[], &f.dirty);
            }
        }
    }
    b.end()
}
fn emission(n: usize, inverse: bool, shared: bool) -> (Vec<Op>, u64) {
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    let mut b = B::new();
    let f = frame(&mut b, n);
    let r = recipe(&mut b, &f, inverse, shared);
    b.play(&r, false);
    (b.ops, b.tof)
}
fn input(n: usize, seed: u64) -> Vec<u64> {
    let mut b = B::new();
    let f = frame(&mut b, n);
    let mut rng = Rng::new(seed);
    let mut q: Vec<u64> = (0..695).map(|_| rng.next()).collect();
    for &x in f.park.iter().chain(std::iter::once(&f.flag)) { q[x.0 as usize] = 0; }
    // Include both A=1 and A=0 with arbitrary counter, ring, payload and
    // dirty passenger values. The prefix is never changed by the recipe.
    q[f.ph.0 as usize] = 0xaaaa_aaaa_ffff_ffff;
    for &x in &f.q[64..121] { q[x.0 as usize] &= !0x0000_0000_0000_ffff; }
    q
}
fn apply(ops: &[Op], input: &[u64]) -> Vec<u64> {
    let sim = run(ops, 695, &|q| *q = input.to_vec());
    assert_eq!(sim.phase, 0);
    sim.q
}

#[test]
fn f1_counter_park_shared_predicate_exact697() {
    for n in [1, 4, 7] {
        let (of, oft) = emission(n, false, false);
        let (oi, oit) = emission(n, true, false);
        let (nf, nft) = emission(n, false, true);
        let (ni, nit) = emission(n, true, true);
        for seed in 0..4 {
            let q = input(n, 0xf1_697_000 + seed);
            let a = apply(&of, &q);
            assert_eq!(apply(&nf, &q), a, "forward n={n} seed={seed}");
            let ai = apply(&oi, &q);
            assert_eq!(apply(&ni, &q), ai, "inverse n={n} seed={seed}");
            assert_eq!(apply(&oi, &a), q, "original FI");
            assert_eq!(apply(&ni, &a), q, "shared FI");
            assert_eq!(apply(&of, &ai), q, "original IF");
            assert_eq!(apply(&nf, &ai), q, "shared IF");
        }
        eprintln!("F1_COUNTER_PARK_DIFF_PASS n={n} packs=4 lanes=256 width=695 old_F_T={oft} old_I_T={oit} new_F_T={nft} new_I_T={nit} phase=0 all_wires=true");
        assert_eq!(oft, oit);
        assert_eq!(nft, nit);
        assert!(nft < oft);
    }
}

#[test]
fn f1_fetch_selector_screen_exact697() {
    use super::frogdrop::rot_by_range_care;
    use super::frogdrop_col::rec;
    use super::payload::read_lane;
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    for ci in [0usize, 10, 85, 145, 202] {
        let cp = &cols[ci];
        for kb in [0usize, 11, 22] {
            if kb >= (258usize.saturating_sub(cp.sz.0 + cp.sy.0)).min(23) { continue; }
            let mut b = B::new();
            let ring = b.alloc_n(278); let _payload = b.alloc_n(259); let _q = b.alloc_n(128);
            let _sy = b.alloc_n(8); let sx = b.alloc_n(8); let _ph = b.alloc(); let pool = b.alloc_n(13);
            assert_eq!(b.width(), 695);
            let sz = if cp.sz.1 > 255 { pool[..9].to_vec() } else { pool[..8].to_vec() };
            let act = pool[12]; let c = sx[7];
            let dest = std::collections::BTreeSet::from([kb]);
            let old = rec(&mut b, |b| {
                let rot = rec(b, |b| rot_by_range_care(b, &ring, &sz, cp.sz.0, cp.sz.1, true, &_payload, &dest));
                b.play(&rot, false);
                b.cx(c, ring[kb]);
                mc_xor(b, &[(act, false), (ring[kb], false)], c, &[], &_payload);
                b.cx(c, ring[kb]);
                b.play(&rot, true);
            });
            let new = rec(&mut b, |b| {
                let lane = |sv: usize| ring.get(kb + sv).copied();
                read_lane(b, &sz, cp.sz.0, cp.sz.1, &lane, false,
                          &[(act, false)], c, &sx[..7], &[], &_payload);
            });
            let swap = rec(&mut b, |b| {
                let lane = |sv: usize| ring.get(kb + sv).copied();
                super::mid2::dec_swap(b, &sz, cp.sz.0, cp.sz.1, &lane, c,
                    &[(act, false)], &sx[..7], &[], &_payload);
            });
            let old_f = emission_record(&old, false);
            let new_f = emission_record(&new, false);
            let swap_f = emission_record(&swap, false);
            eprintln!("F1_FETCH_SCREEN col={ci} kb={kb} old_T={} copy_T={} swap_T={}", old_f.1, new_f.1, swap_f.1);
        }
    }
}
fn emission_record(rec: &[G], inverse: bool) -> (Vec<Op>, u64) {
    let mut b = B::new(); b.alloc_n(695); b.play(rec, inverse); (b.ops, b.tof)
}

#[test]
fn f1_map_clean_carry_loan_exact697() {
    use super::frogdrop::{mapf, Cut, MapPar};
    use super::frogdrop_col::{ColPar, ColScr};
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let selected: Vec<_> = cols.iter().enumerate()
        .filter(|(_, cp)| (!cp.sw || cp.emax <= 26) && cp.m <= 128)
        .take(2).collect();
    assert_eq!(selected.len(), 2);
    for (ci, cp) in selected {
        let (old_f, old_t) = map_emission(cp, false, 0);
        let (old_i, _) = map_emission(cp, false, 1);
        let (new_f, new_t) = map_emission(cp, true, 0);
        let (new_i, _) = map_emission(cp, true, 1);
        let (old_fi, _) = map_emission(cp, false, 2);
        let (new_fi, _) = map_emission(cp, true, 2);
        let (old_if, _) = map_emission(cp, false, 3);
        let (new_if, _) = map_emission(cp, true, 3);
        for seed in 0..2 {
            let q = map_input(cp, 0xf1_697_400 + ci as u64 * 13 + seed);
            let f = apply(&old_f, &q);
            assert_eq!(apply(&new_f, &q), f, "map forward col={ci}");
            let i = apply(&old_i, &q);
            assert_eq!(apply(&new_i, &q), i, "map inverse col={ci}");
            assert_eq!(apply(&old_fi, &q), q, "map old FI col={ci}");
            assert_eq!(apply(&new_fi, &q), q, "map new FI col={ci}");
            assert_eq!(apply(&old_if, &q), q, "map old IF col={ci}");
            assert_eq!(apply(&new_if, &q), q, "map new IF col={ci}");
        }
        eprintln!("F1_MAP_LOAN_DIFF_PASS col={ci} width=695 packs=2 old_F_T={old_t} new_F_T={new_t} phase=0 all_wires=true");
        assert!(new_t <= old_t);
    }

    fn map_frame(b: &mut B, cp: &ColPar) -> (Vec<QubitId>, Vec<QubitId>, Vec<QubitId>, ColScr) {
        let ring = b.alloc_n(278); let p = b.alloc_n(259); let q = b.alloc_n(128);
        let _sy = b.alloc_n(8); let sx = b.alloc_n(8); let _ph = b.alloc(); let pool = b.alloc_n(13);
        assert_eq!(b.width(), 695);
        let sc = ColScr::carve_col(&pool, &sx, &p, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255);
        (ring, q, sx, sc)
    }
    fn map_emission(cp: &ColPar, extra: bool, order: usize) -> (Vec<Op>, u64) {
        let mut b = B::new();
        let (ring, q, sx, sc) = map_frame(&mut b, cp);
        let mut ms = sc.ms.clone();
        if extra { ms.andc.push(sc.bq); if !cp.sw && !sc.sz.contains(&sc.sw) { ms.andc.push(sc.sw); } }
        let cut = Cut { v: sx, a: 278, neg: true };
        let par = MapPar { clo: 278 - cp.smax.1, chi: 278 - cp.smax.0,
                           m: cp.m, tail: cp.tail, emax: cp.emax };
        b.begin(); mapf(&mut b, &ring, &q, &cut, &par, &ms); let r = b.end();
        match order { 0 => b.play(&r, false), 1 => b.play(&r, true),
                      2 => { b.play(&r, false); b.play(&r, true); },
                      3 => { b.play(&r, true); b.play(&r, false); }, _ => unreachable!() }
        (b.ops, b.tof)
    }
    fn map_input(cp: &ColPar, seed: u64) -> Vec<u64> {
        let mut b = B::new(); let (_ring, q, sx, sc) = map_frame(&mut b, cp);
        let mut rng = Rng::new(seed);
        let mut v: Vec<u64> = (0..695).map(|_| rng.next()).collect();
        for &p in &q[cp.m..] { v[p.0 as usize] = 0; }
        v[q[0].0 as usize] |= u64::MAX;
        for &p in sc.ms.ez.iter().chain(std::iter::once(&sc.bq))
            .chain(if cp.sw || sc.sz.contains(&sc.sw) { None } else { Some(&sc.sw) })
            .chain([&sc.ms.c0, &sc.ms.e, &sc.ms.g, &sc.ms.f, &sc.ms.anc[0]].into_iter()) {
            v[p.0 as usize] = 0;
        }
        for &p in &sx { v[p.0 as usize] = 0; }
        for lane in 0..64 {
            let s = if lane % 2 == 0 { cp.smax.0 } else { cp.smax.1 };
            for (i, &p) in sx.iter().enumerate() {
                v[p.0 as usize] |= (((s >> i) & 1) as u64) << lane;
            }
        }
        v
    }
}

#[test]
fn f1_fetch_copy_refuted_by_real_add() {
    use super::frogdrop::rot_by_range_care;
    use super::frogdrop_col::{rec, ring_cadd2_loan};
    use super::payload::read_lane;
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    for ci in [0usize] {
        let cp = &cols[ci];
        let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
        let end = 128 - if cp.dn { 7 } else { 0 };
        let mt = (278 - (cp.sz.0 + cp.h) + 1).min(128usize.max(cp.xw) + 1);
        let kmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0).min(cp.qb).min(mt);
        if kmax == 0 { continue; }
        for kb in [0usize].into_iter().filter(|&k| k < kmax) {
            for sub in [false] {
                let (old, old_t) = composed_fetch(cp, kb, sub, false);
                let (new, new_t) = composed_fetch(cp, kb, sub, true);
                for seed in 0..1 {
                    let input = composed_input(cp, lsb, end, 0xf1_697_700 + 31 * ci as u64 + seed);
                    let a = apply(&old, &input); let b = apply(&new, &input);
                    let first = a.iter().zip(&b).position(|(x, y)| x != y).expect("expected copy counterexample");
                    eprintln!("F1_FETCH_COPY_REFUTED col={ci} kb={kb} sub={sub} seed={seed} first_wire={first} old_word={} new_word={}", a[first], b[first]);
                }
                eprintln!("F1_FETCH_COPY_PRICE old_T={old_t} new_T={new_t}");
            }
        }
    }

    fn composed_frame(b: &mut B) -> (Vec<QubitId>, Vec<QubitId>, Vec<QubitId>, Vec<QubitId>, Vec<QubitId>) {
        let ring = b.alloc_n(278); let p = b.alloc_n(259); let q = b.alloc_n(128);
        let _sy = b.alloc_n(8); let sx = b.alloc_n(8); let _ph = b.alloc(); let pool = b.alloc_n(13);
        assert_eq!(b.width(), 695); (ring, p, q, sx, pool)
    }
    fn composed_fetch(cp: &super::frogdrop_col::ColPar, kb: usize, sub: bool, copy: bool) -> (Vec<Op>, u64) {
        let mut b = B::new(); let (ring, dirty, q, sx, pool) = composed_frame(&mut b);
        let mut sz = pool[..8].to_vec(); if cp.sz.1 > 255 { sz.push(pool[8]); }
        let (act, c, c0, x128, pzero) = (pool[12], sx[7], pool[11], pool[9], pool[10]);
        let mt = (278 - (cp.sz.0 + cp.h) + 1).min(128usize.max(cp.xw) + 1);
        let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
        let end = 128 - if cp.dn { 7 } else { 0 };
        let step = rec(&mut b, |b| {
            if copy {
                let lane = |sv: usize| Some(ring[kb + sv]);
                read_lane(b, &sz, cp.sz.0, cp.sz.1, &lane, false,
                    &[(act, false)], c, &sx[..7], &[], &dirty);
            } else {
                let dest = std::collections::BTreeSet::from([kb]);
                let rot = rec(b, |b| rot_by_range_care(b, &ring, &sz, cp.sz.0, cp.sz.1, true, &dirty, &dest));
                b.play(&rot, false);
                b.cx(c, ring[kb]);
                mc_xor(b, &[(act, false), (ring[kb], false)], c, &[], &dirty);
                b.cx(c, ring[kb]);
                b.play(&rot, true);
            }
        });
        b.play(&step, false);
        ring_cadd2_loan(&mut b, &ring, &q, kb, mt-kb, c, sub, &[pzero], c0, x128,
                        &dirty, lsb, end, x128);
        b.play(&step, false);
        (b.ops, b.tof)
    }
    fn composed_input(cp: &super::frogdrop_col::ColPar, lsb: usize, end: usize, seed: u64) -> Vec<u64> {
        let mut b = B::new(); let (_ring, _dirty, q, sx, pool) = composed_frame(&mut b);
        let mut rng = Rng::new(seed); let mut v: Vec<u64> = (0..695).map(|_| rng.next()).collect();
        for &x in &q[lsb..end] { v[x.0 as usize] = 0; }
        for &x in &sx { v[x.0 as usize] = 0; }
        for &x in &[pool[9], pool[10], pool[11]] { v[x.0 as usize] = 0; }
        if cp.sz.1 > 255 { v[pool[8].0 as usize] = 0; }
        v[pool[12].0 as usize] = 0xaaaa_ffff_5555_ffff;
        for &x in &pool[..8] { v[x.0 as usize] = 0; }
        for lane in 0..64 {
            let sz = if lane % 2 == 0 { cp.sz.0 } else { cp.sz.1 };
            for bit in 0..8 { v[pool[bit].0 as usize] |= (((sz >> bit) & 1) as u64) << lane; }
            if cp.sz.1 > 255 { v[pool[8].0 as usize] |= (((sz >> 8) & 1) as u64) << lane; }
        }
        v
    }
}

#[test]
fn f1_record_pair_cancellation_exact697_map() {
    use super::frogdrop::{mapf, Cut, MapPar};
    use super::frogdrop_col::ColScr;
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let cp = &cols[0];
    let mut rng = Rng::new(0xf1_697_900);
    let mut input: Vec<u64> = (0..695).map(|_| rng.next()).collect();
    // q is odd and fits the public map source bound; all borrowed helpers
    // are clean, while the ring and payload passengers remain arbitrary.
    let mut g = B::new(); let ring = g.alloc_n(278); let p = g.alloc_n(259);
    let q = g.alloc_n(128); let _sy = g.alloc_n(8); let sx = g.alloc_n(8);
    let _ph = g.alloc(); let pool = g.alloc_n(13);
    let sc = ColScr::carve_col(&pool, &sx, &p, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255);
    for &x in &q[cp.m..] { input[x.0 as usize] = 0; }
    input[q[0].0 as usize] |= u64::MAX;
    for &x in &pool[..8] { input[x.0 as usize] = 0; }
    for &x in &sc.ms.ez { input[x.0 as usize] = 0; }
    for &x in &[sc.ms.c0, sc.ms.e, sc.ms.g, sc.ms.f, sc.ms.anc[0]] { input[x.0 as usize] = 0; }
    for &x in &sx { input[x.0 as usize] = 0; }
    for lane in 0..64 {
        let value = if lane % 2 == 0 { cp.smax.0 } else { cp.smax.1 };
        for (bit, &x) in sx.iter().enumerate() {
            input[x.0 as usize] |= (((value >> bit) & 1) as u64) << lane;
        }
    }
    let build = |cancel: bool, order: usize| {
        let mut b = B::new(); b.cancel_simple_pairs = cancel; b.cancel_commuting_pairs = cancel;
        let ring = b.alloc_n(278); let p = b.alloc_n(259); let q = b.alloc_n(128);
        let _sy = b.alloc_n(8); let sx = b.alloc_n(8); let _ph = b.alloc(); let pool = b.alloc_n(13);
        let sc = ColScr::carve_col(&pool, &sx, &p, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255);
        let cut = Cut { v: sx, a: 278, neg: true };
        let par = MapPar { clo: 278-cp.smax.1, chi: 278-cp.smax.0,
                           m: cp.m, tail: cp.tail, emax: cp.emax };
        b.begin(); mapf(&mut b, &ring, &q, &cut, &par, &sc.ms); let r = b.end();
        match order { 0 => b.play(&r, false), 1 => b.play(&r, true),
                      2 => { b.play(&r, false); b.play(&r, true); },
                      3 => { b.play(&r, true); b.play(&r, false); }, _ => unreachable!() }
        (b.ops, b.tof)
    };
    for order in 0..4 {
        let (old, ot) = build(false, order);
        let (new, nt) = build(true, order);
        let a = apply(&old, &input);
        assert_eq!(apply(&new, &input), a, "pair cancellation order={order}");
        if order >= 2 { assert_eq!(a, input, "map cancellation order={order}"); }
        eprintln!("F1_PAIR_MAP_DIFF_PASS order={order} width=695 old_T={ot} new_T={nt} phase=0 all_wires=true");
    }
    let _ = ring;
}

#[test]
fn f1_record_pair_cancellation_exact697_field_rounds() {
    use super::modp_frogdrop::{ctrl_modadd, mod_double, mod_halve, Ms};
    for kind in 0..3 {
        let build = |cancel: bool, order: usize| {
            let mut b = B::new(); b.cancel_simple_pairs = cancel; b.cancel_commuting_pairs = cancel;
            let z = b.alloc_n(256); let y = b.alloc_n(256);
            let ctl = b.alloc(); let d = b.alloc(); let k = b.alloc();
            let _passengers = b.alloc_n(695 - b.width() as usize);
            assert_eq!(b.width(), 695);
            let ms = Ms { k };
            let mut zv = z.clone();
            b.begin();
            match kind {
                0 => ctrl_modadd(&mut b, &ms, &z, &y, ctl, d),
                1 => mod_double(&mut b, &ms, &mut zv, &y),
                2 => mod_halve(&mut b, &ms, &mut zv, &y),
                _ => unreachable!(),
            }
            let r = b.end();
            match order { 0 => b.play(&r, false), 1 => b.play(&r, true),
                          2 => { b.play(&r, false); b.play(&r, true); },
                          3 => { b.play(&r, true); b.play(&r, false); }, _ => unreachable!() }
            (b.ops, b.tof)
        };
        let mut rng = Rng::new(0xf1_697_a00 + kind as u64);
        let mut input: Vec<u64> = (0..695).map(|_| rng.next()).collect();
        input[514] = 0; // k clean; z, y, d and passengers arbitrary.
        for order in 0..4 {
            let (old, ot) = build(false, order);
            let (new, nt) = build(true, order);
            let a = apply(&old, &input);
            assert_eq!(apply(&new, &input), a, "field kind={kind} order={order}");
            if order >= 2 { assert_eq!(a, input, "field FI/IF kind={kind}"); }
            eprintln!("F1_PAIR_FIELD_DIFF_PASS kind={kind} order={order} width=695 old_T={ot} new_T={nt} phase=0 all_wires=true");
        }
    }
}

#[test]
fn d2_f1_record_pair_cancellation_actual697_column0() {
    use super::frogdrop_col::{column_upto, ColScr, Fd};
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let cp = &cols[0];
    let build = |cancel: bool, order: usize| {
        let mut b = B::new(); b.cancel_simple_pairs = cancel; b.cancel_commuting_pairs = cancel;
        let ring = b.alloc_n(278); let dirty = b.alloc_n(259); let q = b.alloc_n(128);
        let sy = b.alloc_n(8); let sx = b.alloc_n(8); let ph = b.alloc(); let pool = b.alloc_n(13);
        let cnt = q[121..].to_vec();
        let mut fd = Fd { ring, q, sy, sx, ph, cnt };
        let sc = ColScr::carve_col(&pool, &fd.sx, &dirty, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255);
        assert_eq!(b.width(), 695);
        b.begin(); column_upto(&mut b, &mut fd, cp, &sc, 99, None); let r = b.end();
        match order { 0 => b.play(&r, false), 1 => b.play(&r, true),
                      2 => { b.play(&r, false); b.play(&r, true); },
                      3 => { b.play(&r, true); b.play(&r, false); }, _ => unreachable!() }
        (b.ops, b.tof)
    };
    let mut rng = Rng::new(0xf1_697_c00);
    let mut input: Vec<u64> = (0..695).map(|_| rng.next()).collect();
    for i in 256..278 { input[i] = 0; }
    input[255] = 0;
    input[254] = u64::MAX;
    input[278] = u64::MAX; // t1 = 1 at traversal entry
    for i in 278 + 259..695 { input[i] = 0; }
    input[278 + 259 + 128] = u64::MAX; // sy = 1
    let (old_forward, _) = build(false, 0);
    let forward_state = apply(&old_forward, &input);
    for order in 0..4 {
        let (old, ot) = build(false, order);
        let (new, nt) = build(true, order);
        let entry = if order == 1 || order == 3 { &forward_state } else { &input };
        let a = apply(&old, entry);
        assert_eq!(apply(&new, entry), a, "column0 order={order}");
        if order == 1 || order == 2 { assert_eq!(a, input, "column0 cleanup order={order}"); }
        if order == 3 { assert_eq!(a, forward_state, "column0 IF"); }
        eprintln!("F1_PAIR_COLUMN_DIFF_PASS col=0 order={order} width=695 old_T={ot} new_T={nt} phase=0 all_wires=true");
    }
}
