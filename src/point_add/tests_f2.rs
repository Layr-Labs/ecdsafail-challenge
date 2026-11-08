use super::builder::B;
use super::frogdrop_col::{column_upto, ColScr, Fd};
use super::tests_frogdrop::{run, Rng};
use crate::circuit::Op;

#[test]
fn f2_cancel_window_screen_exact698_columns() {
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    assert_eq!(cols.len(), 203);
    for ci in [0usize, 85, 202] {
        let cp = &cols[ci];
        let mut counts = vec![];
        for (window, global) in [(128usize, false), (4096, false), (128, true), (4096, true)] {
            let mut b = B::new(); b.cancel_window = window; b.global_cancel = global;
            let ring = b.alloc_n(278); let dirty = b.alloc_n(259); let q = b.alloc_n(128);
            let sy = b.alloc_n(8); let sx = b.alloc_n(8); let ph = b.alloc(); let pool = b.alloc_n(13);
            let cnt = q[121..].to_vec();
            let mut fd = Fd { ring, q, sy, sx, ph, cnt };
            let sc = ColScr::carve_col(&pool, &fd.sx, &dirty, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255);
            assert_eq!(b.width(), 695);
            b.begin(); column_upto(&mut b, &mut fd, cp, &sc, 99, None); let rec = b.end();
            b.play(&rec, false);
            b.flush_global();
            counts.push(b.tof);
        }
        eprintln!("F2_CANCEL_SCREEN col={ci} record128={} record4096={} global128={} global4096={}",
            counts[0], counts[1], counts[2], counts[3]);
    }
}

#[test]
fn f2_wide_cancellation_actual698_column_four_orders() {
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let cp = &cols[0];
    let build = |wide: bool, order: usize| -> (Vec<Op>, u64) {
        let mut b = B::new();
        b.cancel_window = if wide { 4096 } else { 128 };
        b.global_cancel = wide;
        let ring = b.alloc_n(278); let dirty = b.alloc_n(259); let q = b.alloc_n(128);
        let sy = b.alloc_n(8); let sx = b.alloc_n(8); let ph = b.alloc(); let pool = b.alloc_n(13);
        let cnt = q[121..].to_vec();
        let mut fd = Fd { ring, q, sy, sx, ph, cnt };
        let sc = ColScr::carve_col(&pool, &fd.sx, &dirty, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255);
        assert_eq!(b.width(), 695);
        b.begin(); column_upto(&mut b, &mut fd, cp, &sc, 99, None); let rec = b.end();
        match order { 0 => b.play(&rec, false), 1 => b.play(&rec, true),
                      2 => { b.play(&rec, false); b.play(&rec, true); },
                      3 => { b.play(&rec, true); b.play(&rec, false); }, _ => unreachable!() }
        b.flush_global();
        (b.ops, b.tof)
    };
    let apply = |ops: &[Op], input: &[u64]| {
        let sim = run(ops, 695, &|q| *q = input.to_vec());
        assert_eq!(sim.phase, 0);
        sim.q
    };
    for seed in 0..2 {
        let mut rng = Rng::new(0xf2_698_100 + seed);
        let mut input: Vec<u64> = (0..695).map(|_| rng.next()).collect();
        for x in &mut input[256..278] { *x = 0; }
        input[255] = 0;
        input[254] = u64::MAX;
        input[278] = u64::MAX;
        for x in &mut input[278 + 259..695] { *x = 0; }
        input[278 + 259 + 128] = u64::MAX;
        let forward = apply(&build(false, 0).0, &input);
        for order in 0..4 {
            let (old, ot) = build(false, order);
            let (new, nt) = build(true, order);
            let entry = if order == 1 || order == 3 { &forward } else { &input };
            let expected = apply(&old, entry);
            assert_eq!(apply(&new, entry), expected, "order={order} seed={seed}");
            if order == 1 || order == 2 { assert_eq!(expected, input); }
            if order == 3 { assert_eq!(expected, forward); }
            eprintln!("F2_WIDE_DIFF_PASS seed={seed} order={order} old_T={ot} new_T={nt} width=698 all_wires=true phase=0");
        }
    }
}

#[test]
fn f2_global_forward_actual698_column_four_orders() {
    let (cols, _, _) = super::pointadd_frogdrop::col_pars(
        &super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let cp = &cols[0];
    let build = |global: bool, order: usize| -> (Vec<Op>, u64) {
        let mut b = B::new(); b.cancel_window = 4096; b.global_cancel = global;
        let ring = b.alloc_n(278); let dirty = b.alloc_n(259); let q = b.alloc_n(128);
        let sy = b.alloc_n(8); let sx = b.alloc_n(8); let ph = b.alloc(); let pool = b.alloc_n(13);
        let cnt = q[121..].to_vec();
        let mut fd = Fd { ring, q, sy, sx, ph, cnt };
        let sc = ColScr::carve_col(&pool, &fd.sx, &dirty, cp.kp, cp.qb, cp.tail, cp.sz.1 > 255);
        assert_eq!(b.width(), 695);
        let mut recorded = Fd { ring: fd.ring.clone(), q: fd.q.clone(), sy: fd.sy.clone(),
                                sx: fd.sx.clone(), ph: fd.ph, cnt: fd.cnt.clone() };
        b.begin(); column_upto(&mut b, &mut recorded, cp, &sc, 99, None); let inverse = b.end();
        match order {
            0 => column_upto(&mut b, &mut fd, cp, &sc, 99, None),
            1 => b.play(&inverse, true),
            2 => { column_upto(&mut b, &mut fd, cp, &sc, 99, None); b.play(&inverse, true); },
            3 => { b.play(&inverse, true); column_upto(&mut b, &mut fd, cp, &sc, 99, None); },
            _ => unreachable!(),
        }
        b.flush_global();
        (b.ops, b.tof)
    };
    let apply = |ops: &[Op], input: &[u64]| {
        let sim = run(ops, 695, &|q| *q = input.to_vec());
        assert_eq!(sim.phase, 0);
        sim.q
    };
    for seed in 0..2 {
        let mut rng = Rng::new(0xf2_698_300 + seed);
        let mut input: Vec<u64> = (0..695).map(|_| rng.next()).collect();
        for x in &mut input[256..278] { *x = 0; }
        input[255] = 0; input[254] = u64::MAX; input[278] = u64::MAX;
        for x in &mut input[278 + 259..695] { *x = 0; }
        input[278 + 259 + 128] = u64::MAX;
        let forward = apply(&build(false, 0).0, &input);
        for order in 0..4 {
            let (old, ot) = build(false, order);
            let (new, nt) = build(true, order);
            let entry = if order == 1 || order == 3 { &forward } else { &input };
            let expected = apply(&old, entry);
            assert_eq!(apply(&new, entry), expected, "global order={order} seed={seed}");
            if order == 1 || order == 2 { assert_eq!(expected, input); }
            if order == 3 { assert_eq!(expected, forward); }
            eprintln!("F2_GLOBAL_DIFF_PASS seed={seed} order={order} old_T={ot} new_T={nt} width=698 all_wires=true phase=0");
        }
    }
}
