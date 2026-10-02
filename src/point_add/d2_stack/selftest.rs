//! Gate-level selftests of the D2 stacks and park skip: `D2_STACK_SELFTEST=1 build_circuit`.
//!
//! Every test emits the blocks into a fresh [`Builder`], runs the op stream on the harness [`Simulator`]
//! (64 basis-state lanes per pass, random measurement outcomes), checks the post-state against a classical
//! model, then runs the exact inverse (or the block again, for the self-inverse detector) and checks that
//! every wire is back, every temporary is clean and the phase is zero.
//!   A  primitives: increment/decrement, <=, ==, in{a,b} compares, unary iteration -- exhaustive.
//!   B  push / pop / tick-pop / fixup at A = 8 -- exhaustive over N, stack contents, typ, s, preg.
//!   C  park detector at small widths -- exhaustive over N, the rail value, sig and preg, random stack bits in
//!      the masked window, every pebble budget.
//!   E  walk context at A = 288: real FD-seed walks (R = 395 ticks) with a classical stand-in for the rail
//!      tick, the production schedule, forward then walk back.
//!   F  Toffoli and scratch per call at the design's widths.
//! Knobs: D2_SELFTEST_ONLY=ABCEF (subset), D2_SELFTEST_WALKS (E lanes, default 256),
//! D2_SELFTEST_TABLE (model window table for E/F), D2_SELFTEST_PEBBLES (detector budget, default 6),
//! D2_SELFTEST_MARGIN (window margin, default 3).
use super::gl::{emit, Gl, W};
use super::prim::*;
use super::sched::D2Sched;
use super::*;
use crate::circuit::{Op, OperationType, QubitId};
use crate::sim::Simulator;
use sha3::{digest::{ExtendableOutput, Update}, Shake256};

fn xof(tag: &[u8]) -> sha3::Shake256Reader {
    let mut h = Shake256::default();
    h.update(b"d2-stack-selftest-v1");
    h.update(tag);
    h.finalize_xof()
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn bit(&mut self) -> bool {
        self.next() & 1 == 1
    }
}

fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d)
}

fn tcount(ops: &[Op]) -> usize {
    ops.iter().filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ)).count()
}

/// Run `segments` in order on `n` lanes.  `set(lane)` gives the initial 1-bits; after each segment
/// `check(seg, lane, bit, phase)` is called for every lane.
fn batch(
    segments: &[&[Op]],
    nq: usize,
    nb: usize,
    n: usize,
    tag: &[u8],
    set: &dyn Fn(usize) -> Vec<QubitId>,
    check: &mut dyn FnMut(usize, usize, &dyn Fn(QubitId) -> bool, bool),
) {
    let mut x = xof(tag);
    let mut sim = Simulator::new(nq, nb, &mut x);
    let mut first = 0;
    while first < n {
        let cnt = 64.min(n - first);
        sim.clear_for_shot();
        for sh in 0..cnt {
            for q in set(first + sh) {
                *sim.qubit_mut(q) |= 1u64 << sh;
            }
        }
        for (si, seg) in segments.iter().enumerate() {
            sim.apply_iter(seg.iter());
            for sh in 0..cnt {
                let get = |q: QubitId| (sim.qubit(q) >> sh) & 1 == 1;
                check(si, first + sh, &get, (sim.phase >> sh) & 1 == 1);
            }
        }
        first += cnt;
    }
}

fn all_zero_except(nq: usize, get: &dyn Fn(QubitId) -> bool, keep: &dyn Fn(QubitId) -> bool) -> bool {
    (0..nq as u64).all(|i| keep(QubitId(i)) || !get(QubitId(i)))
}

fn reg_val(get: &dyn Fn(QubitId) -> bool, r: &[QubitId]) -> u64 {
    r.iter().enumerate().map(|(i, &q)| (get(q) as u64) << i).sum()
}

fn set_reg(out: &mut Vec<QubitId>, r: &[QubitId], v: u64) {
    for (i, &q) in r.iter().enumerate() {
        if (v >> i) & 1 == 1 {
            out.push(q);
        }
    }
}

fn wv(r: &[QubitId]) -> Vec<W> {
    r.iter().map(|&q| W::Q(q)).collect()
}

// ─── A: primitives ────────────────────────────────────────────────────────────────────────────────────────

fn test_primitives() {
    let mut cases = 0usize;
    // A1 increment / decrement, controlled and not, k = 8
    for &dec in &[false, true] {
        for &ctl in &[false, true] {
            let mut c = Builder::new();
            let r = c.alloc_qubits(8);
            let cw = c.alloc_qubit();
            let mut g = Gl::new();
            if dec {
                decrement(&mut g, &wv(&r), ctl.then_some(W::Q(cw)));
            } else {
                increment(&mut g, &wv(&r), ctl.then_some(W::Q(cw)));
            }
            emit(&mut c, &g, false);
            let mid = c.op_count();
            emit(&mut c, &g, true);
            let ops = c.take_ops();
            let (nq, nb) = c.i13_dims();
            let keep = |q: QubitId| r.contains(&q) || q == cw;
            batch(&[&ops[..mid], &ops[mid..]], nq, nb + 1, 512, b"inc", &|l| {
                let mut v = Vec::new();
                set_reg(&mut v, &r, (l % 256) as u64);
                if l >= 256 {
                    v.push(cw);
                }
                v
            }, &mut |seg, l, get, ph| {
                let x = (l % 256) as u64;
                let on = !ctl || l >= 256;
                let exp = if seg == 1 { x } else if !on { x } else if dec { x.wrapping_sub(1) & 255 } else { (x + 1) & 255 };
                assert_eq!(reg_val(get, &r), exp, "inc/dec dec={dec} ctl={ctl} x={x} seg={seg}");
                assert!(!ph, "inc/dec phase");
                assert!(all_zero_except(nq, get, &keep) && get(cw) == (l >= 256), "inc/dec garbage");
                cases += 1;
            });
            eprintln!("  A1 {} ctl={ctl}: {} T fwd", if dec { "decrement" } else { "increment" }, g.t_fwd());
        }
    }
    // A2/A3 compares on 7 bits: <= K, == K, in {a, b}; controlled and not; out preset 0/1
    for kind in 0..3 {
        for k in 0..128u64 {
            for &ctl in &[false, true] {
                let other = (k * 37 + 11) % 128;
                if kind == 2 && other == k {
                    continue;
                }
                let mut c = Builder::new();
                let r = c.alloc_qubits(7);
                let cw = c.alloc_qubit();
                let out = c.alloc_qubit();
                let mut g = Gl::new();
                let cc = ctl.then_some(W::Q(cw));
                match kind {
                    0 => le_const_into(&mut g, &wv(&r), k, cc, W::Q(out)),
                    1 => eq_const_into(&mut g, &wv(&r), k, cc, W::Q(out)),
                    _ => memb2_into(&mut g, &wv(&r), k, other, cc, W::Q(out)),
                }
                emit(&mut c, &g, false);
                let mid = c.op_count();
                emit(&mut c, &g, true);
                let ops = c.take_ops();
                let (nq, nb) = c.i13_dims();
                let keep = |q: QubitId| r.contains(&q) || q == cw || q == out;
                batch(&[&ops[..mid], &ops[mid..]], nq, nb + 1, 512, b"cmp", &|l| {
                    let mut v = Vec::new();
                    set_reg(&mut v, &r, (l % 128) as u64);
                    if (l / 128) & 1 == 1 {
                        v.push(cw);
                    }
                    if l / 256 == 1 {
                        v.push(out);
                    }
                    v
                }, &mut |seg, l, get, ph| {
                    let x = (l % 128) as u64;
                    let on = !ctl || (l / 128) & 1 == 1;
                    let pred = match kind { 0 => x <= k, 1 => x == k, _ => x == k || x == other };
                    let o0 = l / 256 == 1;
                    let exp = if seg == 0 { o0 ^ (on && pred) } else { o0 };
                    assert_eq!(get(out), exp, "cmp kind={kind} k={k} x={x} ctl={ctl} seg={seg}");
                    assert_eq!(reg_val(get, &r), x);
                    assert!(!ph, "cmp phase kind={kind}");
                    assert!(all_zero_except(nq, get, &keep), "cmp garbage");
                    cases += 1;
                });
            }
        }
    }
    // A4 unary iteration: k = 6, promise and live ranges, controlled and not
    let mut rng = Rng(77);
    for trial in 0..60 {
        let k = 6usize;
        let a0 = rng.next() % 64;
        let a1 = rng.next() % 64;
        let (lo, hi) = (a0.min(a1), a0.max(a1));
        let b0 = lo + rng.next() % (hi - lo + 1);
        let b1 = lo + rng.next() % (hi - lo + 1);
        let live = (b0.min(b1), b0.max(b1));
        let desc = trial % 2 == 0;
        let ctl = trial % 3 != 0;
        let mut c = Builder::new();
        let r = c.alloc_qubits(k);
        let cw = c.alloc_qubit();
        let outs = c.alloc_qubits(64);
        let mut g = Gl::new();
        let mut order = Vec::new();
        unary(&mut g, ctl.then_some(W::Q(cw)), &wv(&r), lo, hi, live, desc, &mut |g, v, leaf| {
            order.push(v);
            cx_o(g, leaf, W::Q(outs[v as usize]));
        });
        let mut sorted = order.clone();
        sorted.sort();
        if desc {
            sorted.reverse();
        }
        assert_eq!(order, sorted, "unary leaf order");
        assert_eq!(order.len() as u64, live.1 - live.0 + 1, "unary leaf count");
        emit(&mut c, &g, false);
        let mid = c.op_count();
        emit(&mut c, &g, true);
        let ops = c.take_ops();
        let (nq, nb) = c.i13_dims();
        let keep = |q: QubitId| r.contains(&q) || q == cw || outs.contains(&q);
        batch(&[&ops[..mid], &ops[mid..]], nq, nb + 1, 128, b"unary", &|l| {
            let mut v = Vec::new();
            set_reg(&mut v, &r, (l % 64) as u64);
            if l >= 64 {
                v.push(cw);
            }
            v
        }, &mut |seg, l, get, ph| {
            let x = (l % 64) as u64;
            let on = !ctl || l >= 64;
            assert!(!ph, "unary phase");
            assert!(all_zero_except(nq, get, &keep), "unary garbage");
            assert_eq!(reg_val(get, &r), x);
            if seg == 0 && x >= lo && x <= hi {
                for v in live.0..=live.1 {
                    assert_eq!(get(outs[v as usize]), on && v == x, "unary leaf v={v} x={x} lo={lo} hi={hi} live={live:?}");
                }
            }
            if seg == 1 {
                assert!(outs.iter().all(|&q| !get(q)), "unary reverse");
            }
            cases += 1;
        });
    }
    eprintln!("D2 SELFTEST A PASS: primitives, {cases} lane checks (inc/dec 8-bit all values; <=, ==, in{{a,b}} on 7 bits for every constant; 60 unary iterations, every register value), zero phase, no garbage, exact inverse");
}

// ─── B: push / pop / tick-pop / fixup ────────────────────────────────────────────────────────────────────

fn small_layout(c: &mut Builder, a: usize, pbits: usize) -> D2Layout {
    D2Layout::alloc(c, a, pbits)
}

fn layout_wires(l: &D2Layout) -> Vec<QubitId> {
    let mut v = Vec::new();
    v.extend(&l.p[0]);
    v.extend(&l.p[1]);
    v.extend(&l.sig);
    v.extend(&l.nreg);
    v.extend(&l.preg);
    v.push(l.s);
    v
}

fn test_stack() {
    let a = 8usize;
    let t = 2usize; // typ wire p[0][1]
    let nmax = 12u64; // entries 0..11 occupy p[*][7..2]
    let mut cases = 0usize;
    // B1 push: every N in [0, nmax - 1], every stack content, typ, s; promise = full and a narrow window
    for &(wlo, whi) in &[(0u64, nmax - 1), (3, 8)] {
        let mut c = Builder::new();
        let l = small_layout(&mut c, a, 5);
        let g = push_gl(&l, t, (wlo, whi));
        emit(&mut c, &g, false);
        let mid = c.op_count();
        emit(&mut c, &g, true);
        let ops = c.take_ops();
        let (nq, nb) = c.i13_dims();
        let lw = layout_wires(&l);
        // lane enumeration: N, content (2^N), typ, s
        let mut lanes: Vec<(u64, u64, bool, bool, u64)> = Vec::new();
        let mut rng = Rng(5);
        for n in wlo..=whi {
            for content in 0..(1u64 << n) {
                for typ in [false, true] {
                    for s in [false, true] {
                        lanes.push((n, content, typ, s, rng.next()));
                    }
                }
            }
        }
        let typw = l.typ_wire(t);
        let fill = |lane: &(u64, u64, bool, bool, u64)| -> Vec<QubitId> {
            let (n, content, typ, s, sp) = *lane;
            let mut v = Vec::new();
            set_reg(&mut v, &l.nreg, n + 1);
            for j in 0..n as usize {
                if (content >> j) & 1 == 1 {
                    v.push(l.stack_wire(j));
                }
            }
            // spectators: typ wires below position 2 random (except the tested typ wire), sig random
            for (i, &q) in [l.p[0][0], l.p[1][0], l.p[1][1], l.sig[0], l.sig[1]].iter().enumerate() {
                if (sp >> i) & 1 == 1 {
                    v.push(q);
                }
            }
            if typ {
                v.push(typw);
            }
            if s {
                v.push(l.s);
            }
            v
        };
        let lanes_ref = &lanes;
        batch(&[&ops[..mid], &ops[mid..]], nq, nb + 1, lanes.len(), b"push", &|i| fill(&lanes_ref[i]), &mut |seg, i, get, ph| {
            let (n, content, typ, s, _) = lanes_ref[i];
            assert!(!ph, "push phase");
            let fires = seg == 0 && !typ;
            let mut exp: std::collections::BTreeSet<QubitId> = fill(&lanes_ref[i]).into_iter().collect();
            if fires {
                // N + 1 and s moved to entry N
                for (b, &q) in l.nreg.iter().enumerate() {
                    exp.remove(&q);
                    if ((n + 2) >> b) & 1 == 1 {
                        exp.insert(q);
                    }
                }
                exp.remove(&l.s);
                if s {
                    exp.insert(l.stack_wire(n as usize));
                }
            }
            for &q in &lw {
                assert_eq!(get(q), exp.contains(&q), "push n={n} content={content:b} typ={typ} s={s} seg={seg} wire {}", q.0);
            }
            assert!(all_zero_except(nq, get, &|q| lw.contains(&q)), "push garbage");
            cases += 1;
        });
        eprintln!("  B1 push window [{wlo},{whi}]: {} T, {} temps, {} lanes", g.t_fwd(), g.peak, lanes.len());
    }
    // B2 pop_into under a control wire: every N in [1, nmax], every content, ctrl
    for &(wlo, whi) in &[(1u64, nmax), (4, 9)] {
        let mut c = Builder::new();
        let l = small_layout(&mut c, a, 5);
        let ctrl = c.alloc_qubit();
        let target = l.typ_wire(t);
        let mut g = Gl::new();
        pop_into(&mut g, &l, W::Q(target), W::Q(ctrl), (wlo, whi));
        emit(&mut c, &g, false);
        let mid = c.op_count();
        emit(&mut c, &g, true);
        let ops = c.take_ops();
        let (nq, nb) = c.i13_dims();
        let mut lw = layout_wires(&l);
        lw.push(ctrl);
        let mut lanes = Vec::new();
        for n in wlo..=whi {
            for content in 0..(1u64 << n) {
                for ct in [false, true] {
                    lanes.push((n, content, ct));
                }
            }
        }
        let fill = |&(n, content, ct): &(u64, u64, bool)| -> Vec<QubitId> {
            let mut v = Vec::new();
            set_reg(&mut v, &l.nreg, n + 1);
            for j in 0..n as usize {
                if (content >> j) & 1 == 1 {
                    v.push(l.stack_wire(j));
                }
            }
            if ct {
                v.push(ctrl);
            }
            v
        };
        let lanes_ref = &lanes;
        batch(&[&ops[..mid], &ops[mid..]], nq, nb + 1, lanes.len(), b"pop", &|i| fill(&lanes_ref[i]), &mut |seg, i, get, ph| {
            let (n, content, ct) = lanes_ref[i];
            assert!(!ph, "pop phase");
            let mut exp: std::collections::BTreeSet<QubitId> = fill(&lanes_ref[i]).into_iter().collect();
            if seg == 0 && ct {
                for (b, &q) in l.nreg.iter().enumerate() {
                    exp.remove(&q);
                    if (n >> b) & 1 == 1 {
                        exp.insert(q);
                    }
                }
                let top = l.stack_wire(n as usize - 1);
                if exp.remove(&top) {
                    exp.insert(target);
                }
            }
            for &q in &lw {
                assert_eq!(get(q), exp.contains(&q), "pop n={n} content={content:b} ctrl={ct} seg={seg} wire {}", q.0);
            }
            assert!(all_zero_except(nq, get, &|q| lw.contains(&q)), "pop garbage");
            cases += 1;
        });
        eprintln!("  B2 pop window [{wlo},{whi}]: {} T, {} temps, {} lanes", g.t_fwd(), g.peak, lanes.len());
    }
    // B3 tick_pop at tick t = 5, k = 2 / 4 bits, k = 9 / 7 bits: every preg value, typ wire, N in [1, 8], random contents
    for &(pbits, k) in &[(4usize, 2u64), (7, 9)] {
        let tt = 5usize;
        let mut c = Builder::new();
        let l = small_layout(&mut c, a, pbits);
        let g = tick_pop_gl(&l, tt, k, (1, 8));
        emit(&mut c, &g, false);
        let mid = c.op_count();
        emit(&mut c, &g, true);
        let ops = c.take_ops();
        let (nq, nb) = c.i13_dims();
        let lw = layout_wires(&l);
        let w = l.typ_wire(tt);
        let mut lanes = Vec::new();
        let mut rng = Rng(9);
        for pv in 0..(1u64 << pbits) {
            for n in 1..=8u64 {
                for wbit in [false, true] {
                    let parked = pv <= k;
                    if parked && !wbit {
                        continue; // valid states: a detected walk's typ wire holds 1
                    }
                    for _ in 0..4 {
                        lanes.push((pv, n, wbit, rng.next() & ((1 << n) - 1)));
                    }
                }
            }
        }
        let fill = |&(pv, n, wbit, content): &(u64, u64, bool, u64)| -> Vec<QubitId> {
            let mut v = Vec::new();
            set_reg(&mut v, &l.preg, pv);
            set_reg(&mut v, &l.nreg, n + 1);
            for j in 0..n as usize {
                if (content >> j) & 1 == 1 {
                    v.push(l.stack_wire(j));
                }
            }
            if wbit {
                v.push(w);
            }
            v
        };
        let lanes_ref = &lanes;
        batch(&[&ops[..mid], &ops[mid..]], nq, nb + 1, lanes.len(), b"tickpop", &|i| fill(&lanes_ref[i]), &mut |seg, i, get, ph| {
            let (pv, n, _wbit, _) = lanes_ref[i];
            assert!(!ph, "tick_pop phase");
            let mut exp: std::collections::BTreeSet<QubitId> = fill(&lanes_ref[i]).into_iter().collect();
            if seg == 0 && pv <= k {
                exp.remove(&w);
                for (b, &q) in l.nreg.iter().enumerate() {
                    exp.remove(&q);
                    if (n >> b) & 1 == 1 {
                        exp.insert(q);
                    }
                }
                if exp.remove(&l.stack_wire(n as usize - 1)) {
                    exp.insert(w);
                }
            }
            for &q in &lw {
                assert_eq!(get(q), exp.contains(&q), "tick_pop p={pv} n={n} seg={seg}");
            }
            assert!(all_zero_except(nq, get, &|q| lw.contains(&q)), "tick_pop garbage");
            cases += 1;
        });
        eprintln!("  B3 tick_pop ({pbits}-bit preg): {} T, {} temps, {} lanes", g.t_fwd(), g.peak, lanes.len());
    }
    // B4 fixup at tick 6: every preg value x typ wires t-1, t (5-bit preg, every k)
    for k in 0..31u64 {
        let tt = 6usize;
        let mut c = Builder::new();
        let l = small_layout(&mut c, a, 5);
        let g = fixup_gl(&l, tt, k);
        emit(&mut c, &g, false);
        let mid = c.op_count();
        emit(&mut c, &g, true);
        let ops = c.take_ops();
        let (nq, nb) = c.i13_dims();
        let lw = layout_wires(&l);
        let (wp, wc) = (l.typ_wire(tt - 1), l.typ_wire(tt));
        let lanes: Vec<(u64, bool, bool)> = (0..32u64).flat_map(|pv| [(pv, false, false), (pv, false, true), (pv, true, false), (pv, true, true)]).collect();
        let fill = |&(pv, a0, a1): &(u64, bool, bool)| -> Vec<QubitId> {
            let mut v = Vec::new();
            set_reg(&mut v, &l.preg, pv);
            if a0 {
                v.push(wp);
            }
            if a1 {
                v.push(wc);
            }
            v
        };
        let lanes_ref = &lanes;
        batch(&[&ops[..mid], &ops[mid..]], nq, nb + 1, lanes.len(), b"fixup", &|i| fill(&lanes_ref[i]), &mut |seg, i, get, ph| {
            let (pv, a0, a1) = lanes_ref[i];
            assert!(!ph);
            let flip = seg == 0 && pv <= k && !a0;
            assert_eq!(get(wc), a1 ^ flip, "fixup p={pv}");
            assert_eq!(get(wp), a0);
            assert_eq!(reg_val(get, &l.preg), pv);
            assert!(all_zero_except(nq, get, &|q| lw.contains(&q)), "fixup garbage");
            cases += 1;
        });
        if k == 30 {
            eprintln!("  B4 fixup: {} T, {} temps (k = 0..30)", g.t_fwd(), g.peak);
        }
    }
    // B5 peek: every N in [depth + 1, nmax], every content, ctrl, out preset; depths 0..3
    for depth in 0..4usize {
        let (wlo, whi) = (depth as u64 + 1, nmax);
        let mut c = Builder::new();
        let l = small_layout(&mut c, a, 5);
        let ctrl = c.alloc_qubit();
        let out = c.alloc_qubit();
        let g = peek_gl(&l, depth, Some(W::Q(ctrl)), W::Q(out), (wlo, whi));
        emit(&mut c, &g, false);
        let mid = c.op_count();
        emit(&mut c, &g, true);
        let ops = c.take_ops();
        let (nq, nb) = c.i13_dims();
        let mut lw = layout_wires(&l);
        lw.push(ctrl);
        lw.push(out);
        let mut lanes = Vec::new();
        for n in wlo..=whi {
            for content in 0..(1u64 << n) {
                for ct in [false, true] {
                    lanes.push((n, content, ct, (content ^ n) & 1 == 1));
                }
            }
        }
        let fill = |&(n, content, ct, o): &(u64, u64, bool, bool)| -> Vec<QubitId> {
            let mut v = Vec::new();
            set_reg(&mut v, &l.nreg, n + 1);
            for j in 0..n as usize {
                if (content >> j) & 1 == 1 {
                    v.push(l.stack_wire(j));
                }
            }
            if ct {
                v.push(ctrl);
            }
            if o {
                v.push(out);
            }
            v
        };
        let lanes_ref = &lanes;
        batch(&[&ops[..mid], &ops[mid..]], nq, nb + 1, lanes.len(), b"peek", &|i| fill(&lanes_ref[i]), &mut |seg, i, get, ph| {
            let (n, content, ct, o) = lanes_ref[i];
            assert!(!ph, "peek phase");
            let bitv = (content >> (n as usize - 1 - depth)) & 1 == 1;
            let exp_o = if seg == 0 { o ^ (ct && bitv) } else { o };
            assert_eq!(get(out), exp_o, "peek depth={depth} n={n} content={content:b} ctrl={ct}");
            let exp: std::collections::BTreeSet<QubitId> = fill(&lanes_ref[i]).into_iter().collect();
            for &q in &lw {
                if q != out {
                    assert_eq!(get(q), exp.contains(&q), "peek disturbed wire {}", q.0);
                }
            }
            assert!(all_zero_except(nq, get, &|q| lw.contains(&q)), "peek garbage");
            cases += 1;
        });
        if depth == 0 {
            eprintln!("  B5 peek window [{wlo},{whi}]: {} T, {} temps", g.t_fwd(), g.peak);
        }
    }
    // B6 typ_read: every preg value x typ wire x out preset, k = 0..30
    for k in 0..31u64 {
        let tp = 4usize;
        let mut c = Builder::new();
        let l = small_layout(&mut c, a, 5);
        let out = c.alloc_qubit();
        let g = typ_read_gl(&l, tp, Some(k), W::Q(out));
        emit(&mut c, &g, false);
        let mid = c.op_count();
        emit(&mut c, &g, true);
        let ops = c.take_ops();
        let (nq, nb) = c.i13_dims();
        let w = l.typ_wire(tp);
        let mut lw = layout_wires(&l);
        lw.push(out);
        let lanes: Vec<(u64, bool, bool)> = (0..32u64).flat_map(|pv| [(pv, false, false), (pv, false, true), (pv, true, false), (pv, true, true)]).collect();
        let lanes_ref = &lanes;
        batch(&[&ops[..mid], &ops[mid..]], nq, nb + 1, lanes.len(), b"typread", &|i| {
            let (pv, wb, o) = lanes_ref[i];
            let mut v = Vec::new();
            set_reg(&mut v, &l.preg, pv);
            if wb {
                v.push(w);
            }
            if o {
                v.push(out);
            }
            v
        }, &mut |seg, i, get, ph| {
            let (pv, wb, o) = lanes_ref[i];
            assert!(!ph);
            let typ = if pv <= k { true } else { wb };
            assert_eq!(get(out), if seg == 0 { o ^ typ } else { o }, "typ_read p={pv} k={k}");
            assert_eq!(get(w), wb);
            assert!(all_zero_except(nq, get, &|q| lw.contains(&q)), "typ_read garbage");
            cases += 1;
        });
        if k == 30 {
            eprintln!("  B6 typ_read: {} T, {} temps", g.t_fwd(), g.peak);
        }
    }
    eprintln!("D2 SELFTEST B PASS: push/pop/tick-pop/fixup/peek/typ-read, {cases} lane checks (A = 8, every N in window, every stack content, typ, s, preg), zero phase, no garbage, exact inverse");
}

// ─── C: park detector ─────────────────────────────────────────────────────────────────────────────────────

fn test_detect() {
    let mut cases = 0usize;
    let mut rng = Rng(31);
    // (A, t, top, preg bits, index): small layouts where the masked window is wide relative to the rail
    for &(a, t, top, pbits, index) in &[(12usize, 6usize, 6usize, 5usize, 3u64), (12, 7, 6, 4, 0), (14, 9, 7, 5, 30), (10, 4, 5, 3, 6)] {
        let o0 = (t + 1) / 2;
        let ox = t / 2 + 1;
        let x = t % 2;
        for pebbles in 1..=top + 1 {
            if super::pebble::visit_cost(top, pebbles).is_none() {
                continue;
            }
            // N range: every N whose region Ladd(M) >= 0 (plus two beyond)
            let nmax = 2 * (a - o0) as u64;
            let m_hi = ((nmax + 1) / 2).min(((a - o0 - 1) as u64).saturating_sub(0));
            let mut c = Builder::new();
            let l = D2Layout::alloc(&mut c, a, pbits);
            let m_lo = if pebbles % 2 == 0 { 0 } else { 1 };
            let dp = DetParams {
                index,
                top,
                m_lo,
                m_hi,
                pebbles,
                late_memb: env_usize("D2_SELFTEST_LATE_MEMB", 0) == 1,
                dirty_lv: env_usize("D2_SELFTEST_DIRTY_LV", 0),
            };
            let g = detect_gl(&l, t, dp);
            emit(&mut c, &g, false);
            let mid = c.op_count();
            emit(&mut c, &g, false);
            let ops = c.take_ops();
            let (nq, nb) = c.i13_dims();
            let lw = layout_wires(&l);
            let mark = index;
            let all1 = l.undetected();
            // lanes: N, rail n (all values of bit length <= min(top, Ladd(M))), sig, preg in {all ones, index, other}
            let mut lanes: Vec<(u64, u64, bool, u64, u64)> = Vec::new();
            for n in 0..=nmax {
                let m = (n + 1) / 2;
                let ladd = a as i64 - o0 as i64 - 1 - m as i64;
                let lim = ladd.clamp(0, top as i64) as u32;
                for rail in 0..(1u64 << lim) {
                    for sig in [false, true] {
                        for &pv in &[all1, mark, rng.next() % (all1 + 1)] {
                            lanes.push((n, rail, sig, pv, rng.next()));
                        }
                    }
                }
            }
            let fill = |&(n, rail, sig, pv, junk): &(u64, u64, bool, u64, u64)| -> Vec<QubitId> {
                let mut v = Vec::new();
                set_reg(&mut v, &l.nreg, n + 1);
                set_reg(&mut v, &l.preg, pv);
                if sig {
                    v.push(l.sig[x]);
                }
                for i in 0..(a - ox) {
                    let bitv = if i < 64 && (rail >> i) & 1 == 1 { true } else {
                        // above the rail: random junk only at positions >= Ladd(M) (gap/stack, masked)
                        let m = (n + 1) / 2;
                        let ladd = a as i64 - o0 as i64 - 1 - m as i64;
                        (i as i64) >= ladd.max(0) && (junk >> (i % 64)) & 1 == 1
                    };
                    if bitv {
                        v.push(l.p[x][ox + i]);
                    }
                }
                // the other array and the X typ wires: random spectators
                for i in 0..a {
                    if (junk >> ((i + 7) % 64)) & 1 == 1 {
                        v.push(l.p[1 - x][i]);
                    }
                }
                for i in 0..ox {
                    if (junk >> ((i + 31) % 64)) & 1 == 1 {
                        v.push(l.p[x][i]);
                    }
                }
                v
            };
            let lanes_ref = &lanes;
            batch(&[&ops[..mid], &ops[mid..]], nq, nb + 64, lanes.len(), b"detect", &|i| fill(&lanes_ref[i]), &mut |seg, i, get, ph| {
                let (n, rail, sig, pv, _) = lanes_ref[i];
                let m = (n + 1) / 2;
                let z = rail == 0 && !sig && m <= m_hi && m >= m_lo;
                let fire = seg == 0 && z && (pv == all1 || pv == mark);
                let exp_p = if fire { pv ^ all1 ^ mark } else { pv };
                assert!(!ph, "detect phase (A={a} t={t} pebbles={pebbles} n={n} rail={rail} sig={sig})");
                assert_eq!(reg_val(get, &l.preg), exp_p, "detect preg A={a} t={t} pebbles={pebbles} n={n} rail={rail} sig={sig} p={pv} seg={seg}");
                let exp: std::collections::BTreeSet<QubitId> = fill(&lanes_ref[i]).into_iter().collect();
                for &q in &lw {
                    if !l.preg.contains(&q) {
                        assert_eq!(get(q), exp.contains(&q), "detect disturbed wire {} (A={a} t={t})", q.0);
                    }
                }
                assert!(all_zero_except(nq, get, &|q| lw.contains(&q)), "detect garbage");
                cases += 1;
            });
            if pebbles == top + 1 || pebbles == 2 {
                eprintln!("  C detect A={a} t={t} top={top} pebbles={pebbles}: {} T, {} temps, {} lanes", g.t_fwd(), g.peak, lanes.len());
            }
        }
    }
    eprintln!("D2 SELFTEST C PASS: park detector, {cases} lane checks (every N, every rail value within the region, sig, preg in {{all ones, index, other}}, random bits in the masked window, every pebble budget), zero phase, no garbage, self-inverse");
}

fn set_reg_set(out: &mut std::collections::BTreeSet<QubitId>, r: &[QubitId], v: u64) {
    for (i, &q) in r.iter().enumerate() {
        if (v >> i) & 1 == 1 {
            out.insert(q);
        }
    }
}

// ─── E: walk context at full width ────────────────────────────────────────────────────────────────────────

mod big {
    pub const NL: usize = 5;
    pub type U = [u64; NL];
    pub const P: U = [0xFFFFFFFEFFFFFC2F, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0];
    pub const ONE: U = [1, 0, 0, 0, 0];
    pub fn zero() -> U { [0; NL] }
    pub fn is_zero(a: &U) -> bool { a.iter().all(|&x| x == 0) }
    pub fn add(a: &U, b: &U) -> U { let mut o = zero(); let mut c = 0u128;
        for i in 0..NL { let t = a[i] as u128 + b[i] as u128 + c; o[i] = t as u64; c = t >> 64; } o }
    pub fn sub(a: &U, b: &U) -> U { let mut o = zero(); let mut br = 0i128;
        for i in 0..NL { let t = a[i] as i128 - b[i] as i128 - br; o[i] = t as u64; br = if t < 0 { 1 } else { 0 }; } o }
    pub fn sar1(a: &U) -> U { let mut o = zero(); for i in 0..NL { o[i] = (a[i] >> 1) | if i + 1 < NL { a[i + 1] << 63 } else { 0 }; }
        if (a[NL - 1] as i64) < 0 { o[NL - 1] |= 1 << 63; } o }
    pub fn bits(a: &U) -> usize { for i in (0..NL).rev() { if a[i] != 0 { return 64 * i + 64 - a[i].leading_zeros() as usize; } } 0 }
    pub fn neg(a: &U) -> bool { (a[NL - 1] as i64) < 0 }
    pub fn not(a: &U) -> U { let mut o = *a; for x in o.iter_mut() { *x = !*x; } o }
    pub fn nrm(a: &U) -> U { if neg(a) { not(a) } else { *a } }
    pub fn bl(a: &U) -> usize { bits(&nrm(a)) }
    pub fn absv(a: &U) -> U { if neg(a) { add(&not(a), &ONE) } else { *a } }
    pub fn ltu(a: &U, b: &U) -> bool { for i in (0..NL).rev() { if a[i] != b[i] { return a[i] < b[i]; } } false }
    pub fn is01(a: &U, b: &U) -> bool { let (x, y) = (absv(a), absv(b)); (is_zero(&x) && y == ONE) || (is_zero(&y) && x == ONE) }
    pub fn bit(a: &U, i: usize) -> bool { i < 64 * NL && (a[i / 64] >> (i % 64)) & 1 == 1 }
    pub fn from_nrm(n: &U, s: bool) -> U { if s { not(n) } else { *n } }
}
use big::U;

/// One classical lane: the D2 walk under this module's exact discipline, and every wire it implies.
#[derive(Clone)]
struct Lane {
    v: [U; 2],
    /// typ wire contents and stack (entries 0..N) per array position, as the circuit holds them.
    arr: [Vec<bool>; 2],
    n: u64,
    p_reg: u64,
    typ_init: bool,
    park: i64,
    valid: bool,
    why: &'static str,
}

/// The classical rail tick (alternating relabel) on a lane's values.  Returns (c, s, H, O').
fn rail_tick(v: &mut [U; 2], t: usize) -> (bool, bool) {
    let x = t % 2;
    let y = 1 - x;
    let c = v[x][0] & 1 == 1;
    if c {
        v.swap(0, 1);
    }
    let h = big::sar1(&v[x]);
    let o = v[y];
    let agr = big::neg(&h) == big::neg(&o);
    let op = if agr { big::sub(&o, &h) } else { big::add(&o, &h) };
    let s = agr ^ (big::neg(&h) == big::neg(&op));
    v[x] = h;
    v[y] = op;
    (c, s)
}

fn fd_seed(d: &U) -> [U; 2] {
    let b = d[0] & 1;
    let x0 = if b == 1 { big::sar1(&big::sub(d, &big::P)) } else { big::sar1(d) };
    let y0 = if b == 1 { big::add(d, &x0) } else { big::add(&big::sub(d, &big::P), &x0) };
    [x0, y0]
}

fn test_walks() {
    let a = 288usize;
    let ticks = 395usize;
    let nwalks = env_usize("D2_SELFTEST_WALKS", 256);
    let pebbles = env_usize("D2_SELFTEST_PEBBLES", 6);
    let margin = env_usize("D2_SELFTEST_MARGIN", 3) as u64;
    let text = model_table();
    let cks = super::sched::default_checkpoints();
    let sch = D2Sched::from_model_table(&text, a, &cks, margin, pebbles);
    let sch = if env_usize("D2_SELFTEST_AFTER_PUSH", 0) == 1 { sch.with_detect_after_push() } else { sch };
    eprintln!("  E walks: detect_after_push={}", sch.detect_after_push);
    // circuit
    let mut c = Builder::new();
    let l = D2Layout::alloc(&mut c, a, sch.pbits());
    let mut fwd_segs: Vec<(usize, usize)> = Vec::new();
    let mut blocks = Vec::new();
    for t in 0..ticks {
        let b = tick_blocks(&l, &sch, t);
        let s0 = c.op_count();
        after_tick_fwd(&mut c, &b);
        after_cell_fwd(&mut c, &b);
        fwd_segs.push((s0, c.op_count()));
        blocks.push(b);
    }
    let mut rev_segs: Vec<(usize, usize)> = vec![(0, 0); ticks];
    for t in (0..ticks).rev() {
        let s0 = c.op_count();
        before_cell_rev(&mut c, &blocks[t]);
        after_cell_rev(&mut c, &blocks[t]);
        rev_segs[t] = (s0, c.op_count());
    }
    let ops = c.take_ops();
    let (nq, nb) = c.i13_dims();
    let t_fwd: usize = fwd_segs.iter().map(|&(s, e)| tcount(&ops[s..e])).sum();
    let t_rev: usize = rev_segs.iter().map(|&(s, e)| tcount(&ops[s..e])).sum();
    eprintln!("  E circuit: {} ops, {nq} qubits ({} persistent), forward {t_fwd} T, walk back {t_rev} T, checkpoints {}", ops.len(), l.persistent_wires(), cks.len());

    // classical lanes
    let mut rng = Rng(2027);
    let mut lanes: Vec<Lane> = Vec::new();
    for _ in 0..nwalks {
        let d = loop {
            let mut d = big::zero();
            for i in 0..4 {
                d[i] = rng.next();
            }
            if !big::is_zero(&d) && big::ltu(&d, &big::P) {
                break d;
            }
        };
        let v = fd_seed(&d);
        let typ_init = big::ltu(&big::absv(&v[0]), &big::absv(&v[1]));
        lanes.push(Lane { v, arr: [vec![false; a], vec![false; a]], n: 0, p_reg: l.undetected(), typ_init, park: -1, valid: true, why: "" });
    }
    let init_lanes = lanes.clone();
    // wire image of a lane: rails normalized in [o_k, A - S_k), typ wires and stack from `arr`
    let image = |ln: &Lane, t: usize| -> Vec<QubitId> {
        // t = number of ticks done
        let o = [(t + 1) / 2, t / 2];
        let s = [((ln.n + 1) / 2) as usize, (ln.n / 2) as usize];
        let mut out = Vec::new();
        for k in 0..2 {
            for i in 0..a {
                let b = if i < o[k] || i >= a - s[k] { ln.arr[k][i] } else { big::bit(&big::nrm(&ln.v[k]), i - o[k]) };
                if b {
                    out.push(l.p[k][i]);
                }
            }
            if big::neg(&ln.v[k]) {
                out.push(l.sig[k]);
            }
        }
        set_reg(&mut out, &l.nreg, ln.n + 1);
        set_reg(&mut out, &l.preg, ln.p_reg);
        out
    };
    // classical reference of the whole forward walk under the circuit's discipline
    let all1 = l.undetected();
    let mut refs: Vec<Vec<Lane>> = vec![lanes.clone()]; // state after each tick's blocks
    for t in 0..ticks {
        let mut next = refs[t].clone();
        for ln in next.iter_mut() {
            if !ln.valid {
                continue;
            }
            let x = t % 2;
            let o = [(t + 1) / 2, t / 2];
            let npre = ln.n;
            let m = (npre + 1) / 2;
            let ladd = a as i64 - o[0] as i64 - 1 - m as i64;
            // typ wire value the tick writes (blind formula) and the fixup
            let prev_w = if t > 0 { ln.arr[(t - 1) % 2][(t - 1) / 2] } else { false };
            let (c_, s_) = rail_tick(&mut ln.v, t);
            let mut typ_w = if t > 0 { c_ ^ prev_w ^ true } else { c_ ^ ln.typ_init };
            if t >= 1 && sch.last_ck_index(t - 1).is_some_and(|k| ln.p_reg <= k) && !prev_w {
                typ_w ^= true;
            }
            let typ_true = big::ltu(&big::absv(&ln.v[x]), &big::absv(&ln.v[1 - x]));
            if typ_w != typ_true {
                ln.valid = false;
                ln.why = "typ mismatch (model)";
                continue;
            }
            if ln.park < 0 && big::is01(&ln.v[0], &ln.v[1]) {
                ln.park = t as i64;
            }
            // the tick's promise: both rails within [0, Ladd) of their post-tick origins
            if (big::bl(&ln.v[0]) as i64) > ladd || (big::bl(&ln.v[1]) as i64) > ladd {
                ln.valid = false;
                ln.why = "rail beyond Ladd (tick promise)";
                continue;
            }
            ln.arr[x][t / 2] = typ_w;
            // detect
            if let Some(dp) = sch.det[t] {
                if m > dp.m_hi || m < dp.m_lo || big::bl(&ln.v[x]) > dp.top {
                    ln.valid = false;
                    ln.why = "detector window";
                    continue;
                }
                let z = big::is_zero(&ln.v[x]);
                if z && ln.p_reg == all1 {
                    ln.p_reg = dp.index;
                    if !(ln.park >= 0 && ln.park < t as i64) {
                        ln.valid = false;
                        ln.why = "detection without a park (model)";
                        continue;
                    }
                }
            }
            // push
            if !typ_w {
                let w = sch.push_win[t];
                if w.is_none_or(|w| npre < w.0 || npre > w.1) {
                    ln.valid = false;
                    ln.why = "push window";
                    continue;
                }
                let j = ln.n as usize;
                ln.arr[j & 1][a - 1 - (j >> 1)] = s_;
                ln.n += 1;
            } else if s_ {
                ln.valid = false;
                ln.why = "A letter with s = 1";
                continue;
            }
            // tick pop
            if sch.last_ck_index(t).is_some_and(|k| ln.p_reg <= k) {
                let w = sch.pop_win[t].unwrap();
                if ln.n < w.0 || ln.n > w.1 {
                    ln.valid = false;
                    ln.why = "pop window";
                    continue;
                }
                let j = ln.n as usize - 1;
                let pos = (j & 1, a - 1 - (j >> 1));
                ln.arr[x][t / 2] = ln.arr[pos.0][pos.1];
                ln.arr[pos.0][pos.1] = false;
                ln.n -= 1;
            }
            // storage after the tick: rails below the stacks
            let o2 = [(t + 2) / 2, (t + 1) / 2];
            let s2 = [((ln.n + 1) / 2) as usize, (ln.n / 2) as usize];
            for k in 0..2 {
                if o2[k] + big::bl(&ln.v[k]) + s2[k] > a {
                    ln.valid = false;
                    ln.why = "storage overflow";
                }
            }
        }
        refs.push(next);
    }
    let final_ref = &refs[ticks];
    let nvalid = final_ref.iter().filter(|x| x.valid).count();
    let unparked = final_ref.iter().filter(|x| x.valid && x.park < 0).count();
    for ln in final_ref.iter().filter(|x| !x.valid) {
        eprintln!("  E lane excluded: {}", ln.why);
    }

    // simulation with the classical tick stand-in between op segments
    let mut xr = xof(b"walks");
    let mut sim = Simulator::new(nq, nb + 64, &mut xr);
    let lw = layout_wires(&l);
    let mut checked = 0usize;
    let mut first = 0usize;
    while first < nwalks {
        let cnt = 64.min(nwalks - first);
        sim.clear_for_shot();
        for sh in 0..cnt {
            for q in image(&init_lanes[first + sh], 0) {
                *sim.qubit_mut(q) |= 1u64 << sh;
            }
        }
        // per lane, per tick: N at the tick and the stand-in's touched wires (pre / post values, packed)
        let touched_of = |t: usize, n: u64| -> Vec<QubitId> {
            let o = [(t + 1) / 2, t / 2];
            let s = [((n + 1) / 2) as usize, (n / 2) as usize];
            let mut v = Vec::new();
            for k in 0..2 {
                for i in o[k]..a - s[k] {
                    v.push(l.p[k][i]);
                }
                v.push(l.sig[k]);
            }
            v.push(l.s);
            v
        };
        let pack = |bits: &[bool]| -> Vec<u64> {
            let mut out = vec![0u64; bits.len().div_ceil(64)];
            for (i, &b) in bits.iter().enumerate() {
                if b {
                    out[i / 64] |= 1 << (i % 64);
                }
            }
            out
        };
        let mut snaps: Vec<Vec<(u64, Vec<u64>, Vec<u64>)>> = vec![Vec::new(); cnt];
        for t in 0..ticks {
            for sh in 0..cnt {
                let li = first + sh;
                if !final_ref[li].valid {
                    continue;
                }
                let get = |q: QubitId| (sim.qubit(q) >> sh) & 1 == 1;
                // read the lane from the wires
                let n = reg_val(&get, &l.nreg) - 1;
                let o = [(t + 1) / 2, t / 2];
                let s = [((n + 1) / 2) as usize, (n / 2) as usize];
                let mut v = [big::zero(); 2];
                for k in 0..2 {
                    let mut nn = big::zero();
                    for i in o[k]..a - s[k] {
                        if get(l.p[k][i]) {
                            nn[(i - o[k]) / 64] |= 1u64 << ((i - o[k]) % 64);
                        }
                    }
                    v[k] = big::from_nrm(&nn, get(l.sig[k]));
                }
                let prev_w = if t > 0 { get(l.typ_wire(t - 1)) } else { false };
                let (c_, s_) = rail_tick(&mut v, t);
                let typ_w = if t > 0 { c_ ^ prev_w ^ true } else { c_ ^ init_lanes[li].typ_init };
                // touched wires: arrays from o_k up to the stack bottom, sigs, s
                let mut postv: Vec<bool> = Vec::new();
                let x = t % 2;
                for k in 0..2 {
                    for i in o[k]..a - s[k] {
                        let nb_ = if k == x {
                            if i == o[k] { typ_w } else { big::bit(&big::nrm(&v[k]), i - o[k] - 1) }
                        } else {
                            big::bit(&big::nrm(&v[k]), i - o[k])
                        };
                        postv.push(nb_);
                    }
                    postv.push(big::neg(&v[k]));
                }
                postv.push(s_);
                let tw = touched_of(t, n);
                let prev: Vec<bool> = tw.iter().map(|&q| get(q)).collect();
                for (&q, &b) in tw.iter().zip(postv.iter()) {
                    let w = sim.qubit_mut(q);
                    *w = (*w & !(1u64 << sh)) | ((b as u64) << sh);
                }
                snaps[sh].push((n, pack(&prev), pack(&postv)));
            }
            let (s0, e0) = fwd_segs[t];
            sim.apply_iter(ops[s0..e0].iter());
        }
        // forward end: compare with the classical reference
        for sh in 0..cnt {
            let li = first + sh;
            let r = &final_ref[li];
            if !r.valid {
                continue;
            }
            let get = |q: QubitId| (sim.qubit(q) >> sh) & 1 == 1;
            let exp: std::collections::BTreeSet<QubitId> = image(r, ticks).into_iter().collect();
            for &q in &lw {
                if q == l.s {
                    continue;
                }
                assert_eq!(get(q), exp.contains(&q), "walk lane {li}: wire {} after the forward walk (park {})", q.0, r.park);
            }
            assert!(!get(l.s));
            assert!((sim.phase >> sh) & 1 == 0, "walk lane {li}: phase after the forward walk");
            assert!(all_zero_except(nq, &get, &|q| lw.contains(&q)), "walk lane {li}: garbage after the forward walk");
        }
        // walk back
        for t in (0..ticks).rev() {
            let (s0, e0) = rev_segs[t];
            sim.apply_iter(ops[s0..e0].iter());
            for sh in 0..cnt {
                let li = first + sh;
                if !final_ref[li].valid {
                    continue;
                }
                let (n, ref prev, ref postv) = snaps[sh][t];
                let tw = touched_of(t, n);
                for (i, &q) in tw.iter().enumerate() {
                    let b = (postv[i / 64] >> (i % 64)) & 1 == 1;
                    assert_eq!((sim.qubit(q) >> sh) & 1 == 1, b, "walk lane {li}: tick {t} state not restored by the walk back (wire {})", q.0);
                }
                for (i, &q) in tw.iter().enumerate() {
                    let b = (prev[i / 64] >> (i % 64)) & 1 == 1;
                    let w = sim.qubit_mut(q);
                    *w = (*w & !(1u64 << sh)) | ((b as u64) << sh);
                }
            }
        }
        for sh in 0..cnt {
            let li = first + sh;
            if !final_ref[li].valid {
                continue;
            }
            let get = |q: QubitId| (sim.qubit(q) >> sh) & 1 == 1;
            let exp: std::collections::BTreeSet<QubitId> = image(&init_lanes[li], 0).into_iter().collect();
            for q in 0..nq as u64 {
                assert_eq!(get(QubitId(q)), exp.contains(&QubitId(q)), "walk lane {li}: wire {q} after the walk back");
            }
            assert!((sim.phase >> sh) & 1 == 0, "walk lane {li}: phase after the walk back");
            checked += 1;
        }
        first += cnt;
    }
    let parks: Vec<i64> = final_ref.iter().filter(|x| x.valid).map(|x| x.park).collect();
    let pmin = parks.iter().copied().filter(|&p| p >= 0).min().unwrap_or(-1);
    let pmax = parks.iter().copied().max().unwrap_or(-1);
    eprintln!("D2 SELFTEST E PASS: {checked}/{nwalks} real walks (A = {a}, R = {ticks}, {} checkpoints {}..{}, pebbles {pebbles}, margin {margin}; parks {pmin}..{pmax}, {unparked} unparked, {} excluded) forward: every array wire, N, preg equal the classical discipline; walk back: every wire restored, zero phase, no garbage", cks.len(), cks[0], cks[cks.len() - 1], nwalks - nvalid);
}

// ─── F: costs at the design's widths ──────────────────────────────────────────────────────────────────────

fn model_table() -> String {
    let table = std::env::var("D2_SELFTEST_TABLE").unwrap_or_else(|_| {
        concat!(env!("CARGO_MANIFEST_DIR"), "/src/point_add/d2_stack/tools/out/sched_A288_d2_win.tsv").to_string()
    });
    std::fs::read_to_string(&table).unwrap_or_else(|e| panic!("D2 selftest: window table {table}: {e}"))
}

fn report_costs() {
    let a = 288usize;
    let ticks = 395usize;
    let margin = env_usize("D2_SELFTEST_MARGIN", 3) as u64;
    let text = model_table();
    let dflt = super::sched::default_checkpoints();
    let every350: Vec<usize> = (350..395).collect();
    let configs: Vec<(&str, Vec<usize>, usize)> = vec![
        ("default (350..375 /3, 376..394 /1)", dflt.clone(), 6),
        ("default", dflt.clone(), 8),
        ("default", dflt.clone(), 7),
        ("default", dflt.clone(), 10),
        ("default", dflt.clone(), 99),
        ("every tick 350..394", every350, 8),
    ];
    for (ci, (name, cks, pebbles)) in configs.into_iter().enumerate() {
        let sch = D2Sched::from_model_table(&text, a, &cks, margin, pebbles);
        let mut c = Builder::new();
        let l = D2Layout::alloc(&mut c, a, sch.pbits());
        let mut tot = [(0usize, 0usize); 4];
        let mut peak = [0u32; 4];
        let mut rows = Vec::new();
        for t in 0..ticks {
            let b = tick_blocks(&l, &sch, t);
            let cs = b.costs();
            for i in 0..4 {
                tot[i].0 += cs[i].0;
                tot[i].1 += cs[i].1;
                peak[i] = peak[i].max(cs[i].2);
            }
            if t % 50 == 0 || (t >= 340 && t % 5 == 0) || t == 394 {
                let pw = sch.push_win[t].map_or(0, |w| w.1 - w.0 + 1);
                let ow = sch.pop_win[t].map_or(0, |w| w.1 - w.0 + 1);
                rows.push(format!("    t={t:3}  fixup {:3}  detect {:4} (top {:2})  push {:4} ({pw:3} N)  tick_pop {:4} ({ow:3} N)   peak temps {:?}",
                    cs[0].0, cs[1].0, sch.det[t].map_or(0, |d| d.top), cs[2].0, cs[3].0, [cs[0].2, cs[1].2, cs[2].2, cs[3].2]));
            }
        }
        let names = ["fixup", "detect", "push", "tick_pop"];
        let fwd: usize = tot.iter().map(|x| x.0).sum();
        let rev: usize = tot.iter().map(|x| x.1).sum();
        eprintln!("  F {name}: {} checkpoints, {}-bit preg, pebbles {pebbles}, margin {margin}: per traversal {fwd} T forward, {rev} T walk back; park part (fixup+detect+tick_pop) {} T",
            cks.len(), sch.pbits(), tot[0].0 + tot[1].0 + tot[3].0);
        for i in 0..4 {
            eprintln!("    {:9} fwd {:7}  back {:7}  peak temporaries {}", names[i], tot[i].0, tot[i].1, peak[i]);
        }
        if ci == 0 {
            for r in rows {
                eprintln!("{r}");
            }
        }
    }
}

pub fn run() {
    let only = std::env::var("D2_SELFTEST_ONLY").unwrap_or_else(|_| "ABCEF".to_string());
    let t0 = std::time::Instant::now();
    if only.contains('A') {
        test_primitives();
    }
    if only.contains('B') {
        test_stack();
    }
    if only.contains('C') {
        test_detect();
    }
    if only.contains('E') {
        test_walks();
    }
    if only.contains('F') {
        report_costs();
    }
    eprintln!("D2_STACK_SELFTEST PASS ({only}) in {:.1}s", t0.elapsed().as_secs_f64());
}
