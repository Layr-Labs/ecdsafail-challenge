//! C59E actual-prefix differential fixture. Each column is built and simulated
//! before its ops are dropped, keeping peak host memory below a whole traversal.
use super::builder::B;
use super::frogdrop_col::{self, ColScr, Fd, MARKS};
use super::frogdrop_sched::{from_text, shot, Kind, L0, N};
use super::pointadd_frogdrop::{self, CNTB, KP, NQ, QB, SW, TAIL, SCHED_FROGDROP};
use super::payload::NP;
use super::tests_frogdrop::Rng;
use crate::circuit::{analyze_ops, Op, QubitId};
use crate::sim::Simulator;
use sha3::digest::{ExtendableOutput, Update};
use std::collections::BTreeMap;

#[cfg(test)]
thread_local! {
    pub(crate) static C63_AK_LANES: std::cell::RefCell<Option<(usize, usize)>> = const { std::cell::RefCell::new(None) };
    static C63B_PLAY: std::cell::RefCell<Vec<(usize, usize, QubitId, QubitId, QubitId)>> = const { std::cell::RefCell::new(Vec::new()) };
    static C63B_ANDZ: std::cell::RefCell<Vec<(usize, QubitId, QubitId, QubitId, bool)>> = const { std::cell::RefCell::new(Vec::new()) };
    static C63B_ANDZ_EXEMPT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(crate) fn c63b_play_boundary(at: usize, mark: usize, ak: QubitId, c: QubitId, sx0: QubitId) {
    C63B_PLAY.with(|v| v.borrow_mut().push((at, mark, ak, c, sx0)));
}

pub(crate) fn c63b_andz_event(at: usize, a: QubitId, b: QubitId, t: QubitId, compute: bool) {
    if std::env::var("C63B_ANDZ").as_deref() == Ok("1") {
        C63B_ANDZ.with(|v| v.borrow_mut().push((at, a, b, t, compute)));
    }
}

pub(crate) fn c63b_andz_exempt() {
    if std::env::var("C63B_ANDZ").as_deref() == Ok("1") {
        C63B_ANDZ_EXEMPT.with(|v| v.set(v.get() + 1));
    }
}

fn apply_andz_segment<R: sha3::digest::XofReader>(
    sim: &mut Simulator<'_, R>, ops: &[Op], events: &[(usize, QubitId, QubitId, QubitId, bool)],
    event_idx: &mut usize, pos: &mut usize, end: usize, col: usize, mark: usize,
    checks: &mut usize, violations: &mut usize, active_violations: &mut usize,
) {
    let start = *pos;
    sim.apply_iter_checked(ops[start..end].iter(), |offset, state, active| {
        let at = start + offset;
        while *event_idx < events.len() && events[*event_idx].0 == at {
            let (_, a, b, t, compute) = events[*event_idx];
            let actual = state.qubit(t);
            let expected = if compute { 0 } else { state.qubit(a) & state.qubit(b) };
            let bad = actual ^ expected;
            *checks += 1;
            if bad != 0 {
                *violations += 1;
                if bad & active != 0 { *active_violations += 1; }
                if *violations <= 12 {
                    eprintln!("C63B_ANDZ_VIOLATION col={col} mark={mark} op={at} kind={} lane={} a={} b={} shot_mask={bad:#018x} active_mask={active:#018x} actual={actual:#018x} expected={expected:#018x}",
                        if compute { "AndC" } else { "AndU" }, t.0, a.0, b.0);
                }
            }
            *event_idx += 1;
        }
    });
    *pos = end;
}

fn put(w: &mut [u64], qs: &[QubitId], shot: usize, v: &N) {
    for (i, &q) in qs.iter().enumerate() {
        if v.bit(i) { w[q.0 as usize] |= 1u64 << shot; }
    }
}

type Snap = (usize, usize, Vec<u64>, u64);
type SzSnap = (usize, usize, [u64; 6]);

struct TraceData {
    marks: Vec<Snap>,
    ak_lanes: Vec<(usize, usize, usize)>,
    sz: Vec<SzSnap>,
    ends: Vec<Snap>,
    costs: Vec<(usize, u64)>,
    final_q: Vec<u64>,
    final_phase: u64,
    andz_checks: usize,
    andz_violations: usize,
    andz_active_violations: usize,
    andz_exempt: usize,
}

fn session_mark(st: usize) -> bool {
    (4001..=4404).contains(&st) || (5100..=5322).contains(&st) || (6100..=6299).contains(&st)
}

fn vg_mark(st: usize) -> bool {
    (5200..=5209).contains(&st) || (6100..=6109).contains(&st) || (6140..=6149).contains(&st)
}

fn log_vg_words(control: &[SzSnap], candidate: &[SzSnap], mode: &str, fixture: &str) {
    assert_eq!(control.len(), candidate.len(), "C63_D5 mark count {fixture} {mode}");
    for (a, b) in control.iter().zip(candidate) {
        assert_eq!((a.0, a.1), (b.0, b.1), "C63_D5 mark identity {fixture} {mode}");
        eprintln!("C63_D5 fixture={fixture} mode={mode} col={} mark={} control_sz0_5={:x?} candidate_sz0_5={:x?} equal={}",
            a.0, a.1, a.2, b.2, a.2 == b.2);
        assert_eq!(a.2, b.2, "C63_D5 vg_s mismatch fixture={fixture} mode={mode} col={} mark={}", a.0, a.1);
    }
}

fn trace(g3: bool, pl_mode: bool, stop: usize) -> TraceData {
    let xs: [N; 2] = [
        N::from_str_radix("24da2b3aa967419120e4517f75ac5c7100b64a5fb8020834706ca618d1ae8d28", 16).unwrap(),
        N::from_str_radix("337e0487c47c5a313bc0905119b944dfa74de639c9d5d2aae3684738ba378171", 16).unwrap(),
    ];
    for &(col, kind) in &[(26, Kind::Hr), (32, Kind::Hr), (76, Kind::Hr), (121, Kind::Ht), (138, Kind::Ht)] {
        let x = if col == 76 || col == 138 { xs[1] } else { xs[0] };
        assert_eq!(shot(x, L0).rec(col).kind, kind, "C59E classical fixture type col={col}");
    }
    let mut targets = vec![26, 32, 76, 121, 138];
    if std::env::var("C63B_Q666_RESERVE").as_deref() == Ok("1") { targets.extend([0, 1]); }
    trace_with(g3, pl_mode, stop, &xs, &targets, false)
}

fn trace_with(g3: bool, pl_mode: bool, stop: usize, xs: &[N], targets: &[usize], full: bool) -> TraceData {
    assert!((2..=64).contains(&xs.len()), "C63 input count 2..64");
    let c63c_strict = std::env::var("C63C_STRICT_PREFIX").as_deref() == Ok("1");
    if g3 { std::env::set_var("C59E_G3", std::env::var("C59E_TRIAL").unwrap_or_else(|_| "1".into())); }
    else { std::env::remove_var("C59E_G3"); }
    std::env::set_var("FD_MARK", "1");
    super::bake_knobs();
    let audit = stop >= 27 && std::env::var("C59E_TRIAL").ok().as_deref() == Some("3")
        && std::env::var_os("C62B_ANDZ_ONLY").is_none();
    if audit {
        if g3 { super::g3p_audit::begin_candidate(); }
        else { super::g3p_audit::begin_control(); }
        super::g3p_audit::set_pl_mode(pl_mode);
    }
    let (cols, _, _) = pointadd_frogdrop::col_pars(&from_text(SCHED_FROGDROP));
    assert!(stop <= cols.len());
    let mut b = B::new();
    let xq = b.alloc_n(256);
    let pl = b.alloc_n(NP);
    let cargo = b.alloc_n(12);
    let mut ring = xq.clone(); ring.extend(b.alloc_n(pointadd_frogdrop::N - 256));
    let q = b.alloc_n(NQ);
    let cnt = q[NQ - CNTB..].to_vec();
    let mut fd = Fd { ring, q, sy: b.alloc_n(SW), sx: b.alloc_n(SW), ph: b.alloc(), cnt };
    let pool = b.alloc_n(frogdrop_col::pool_size(KP, QB, SW));
    let plc = pointadd_frogdrop::pl_col(&pl, &fd, &pool);
    let mut h = sha3::Shake256::default(); h.update(b"c59e-actual-prefix");
    let mut xof = h.finalize_xof();
    let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
    let mut rng = Rng::new(0xc59e_0064);
    for s in 0..64 {
        put(&mut sim.qubits, &xq, s, &xs[if full { s } else { s % 2 }]);
        if pl_mode {
            let dy = rng.below(256) % super::frogdrop_sched::p();
            put(&mut sim.qubits, &pl[..256], s, &dy);
        } else {
            for &lane in &pl[3..] { sim.qubits[lane.0 as usize] |= (rng.next() & 1) << s; }
        }
    }
    for &lane in &cargo { sim.qubits[lane.0 as usize] = rng.next(); }
    sim.qubits[fd.ring[pointadd_frogdrop::N - 1].0 as usize] = u64::MAX;
    sim.qubits[fd.sy[0].0 as usize] = u64::MAX;
    let cargo_before: Vec<u64> = cargo.iter().map(|q| sim.qubits[q.0 as usize]).collect();
    let payload_before: Vec<u64> = pl.iter().map(|q| sim.qubits[q.0 as usize]).collect();
    let mut snaps = Vec::new();
    let mut ak_lanes = Vec::new();
    let mut sz_snaps = Vec::new();
    let mut ends = Vec::new();
    let mut costs = Vec::new();
    let mut andz_checks = 0usize;
    let mut andz_violations = 0usize;
    let mut andz_active_violations = 0usize;
    let mut andz_exempt = 0usize;
    for (c, cp) in cols[..stop].iter().enumerate() {
        if audit { super::g3p_audit::set_column(c); }
        let target = targets.contains(&c);
        let inverse_before = if g3 && (target || c63c_strict) && std::env::var_os("C59E_SKIP_INVERSE").is_none() { Some((sim.qubits.clone(), sim.phase,
            Fd { ring: fd.ring.clone(), q: fd.q.clone(), sy: fd.sy.clone(), sx: fd.sx.clone(),
                 ph: fd.ph, cnt: fd.cnt.clone() })) } else { None };
        assert!(b.ops.is_empty() && b.pending_count() == 0);
        MARKS.with(|m| m.borrow_mut().clear());
        C63_AK_LANES.with(|m| *m.borrow_mut() = None);
        C63B_PLAY.with(|v| v.borrow_mut().clear());
        C63B_ANDZ.with(|v| v.borrow_mut().clear());
        C63B_ANDZ_EXEMPT.with(|v| v.set(0));
        let before_t = b.tof;
        let sc = ColScr::carve_col(&pool, &fd.sx, &pl, KP, QB, TAIL, cp.sz.1 > 255);
        frogdrop_col::column_pl(&mut b, &mut fd, cp, &sc, if pl_mode { Some(&plc) } else { None });
        if target && full {
            if let Some((sx3, sx6)) = C63_AK_LANES.with(|m| *m.borrow()) {
                ak_lanes.push((c, sx3, sx6));
            }
        }
        b.flush_global();
        let marks = MARKS.with(|m| m.borrow().clone());
        let play_boundaries = C63B_PLAY.with(|v| v.borrow().clone());
        let andz_events = C63B_ANDZ.with(|v| v.borrow().clone());
        andz_exempt += C63B_ANDZ_EXEMPT.with(|v| v.get());
        let (aq, nb, _, _) = analyze_ops(b.ops.iter());
        if aq as usize > sim.num_qubits { sim.qubits.resize(aq as usize, 0); sim.num_qubits = aq as usize; }
        if nb as usize > sim.num_bits { sim.bits.resize(nb as usize, 0); sim.num_bits = nb as usize; }
        let mut pos = 0;
        let mut event_idx = 0usize;
        let mut prior_mark = 0usize;
        for &(at, st) in &marks {
            assert!(at >= pos && at <= b.ops.len(), "C59E mark order col={c} mark={st}");
            apply_andz_segment(&mut sim, &b.ops, &andz_events, &mut event_idx, &mut pos, at,
                c, prior_mark, &mut andz_checks, &mut andz_violations, &mut andz_active_violations);
            prior_mark = st;
            if g3 && std::env::var("C63B_D7").as_deref() == Ok("1")
                && std::env::var_os("C62B_ANDZ_ONLY").is_none() && (7300..=7403).contains(&st) {
                let &(_, _, ak, carry, sx0) = play_boundaries.iter()
                    .find(|&&(where_at, mark, _, _, _)| where_at == at && mark == st)
                    .expect("D7 boundary registration");
                // In the Q666 HT frame c=sx7 also hosts w across the form.
                // w is returned by toggle_ht_w after mark 7402.
                let w_held = super::frogdrop_col::c66_direct() && (7401..=7402).contains(&st);
                for (name, q) in [("ak", ak), ("c", carry), ("sx0", sx0)] {
                    if w_held && name == "c" { continue; }
                    let word = sim.qubit(q);
                    assert_eq!(word, 0, "C63B_D7_BOUNDARY col={c} mark={st} op={at} lane={name}:{} mask={word:#x}", q.0);
                }
            }
            if (target || full) && vg_mark(st) {
                sz_snaps.push((c, st, std::array::from_fn(|i| sim.qubits[sc.sz[i].0 as usize])));
            }
            let early_mark = stop < 26 && c < 2 && std::env::var("C63B_Q666_RESERVE").as_deref() == Ok("1");
            if target && (session_mark(st) || (full && (1000..=1022).contains(&st)) || early_mark) {
                if !early_mark { assert_eq!(sim.phase, 0, "C59E phase-zero col={c} mark={st} mode={} g3={g3}",
                    if pl_mode { "PL" } else { "NONE" });
                for (i, &lane) in cargo.iter().enumerate() {
                    assert_eq!(sim.qubits[lane.0 as usize], cargo_before[i], "C59E cargo col={c} mark={st} lane={i}");
                }
                if !pl_mode { for (i, &lane) in pl.iter().enumerate() {
                    assert_eq!(sim.qubits[lane.0 as usize], payload_before[i], "C59E NONE passenger col={c} mark={st} lane={i}");
                } } }
                snaps.push((c, st, sim.qubits.clone(), sim.phase));
            }
        }
        apply_andz_segment(&mut sim, &b.ops, &andz_events, &mut event_idx, &mut pos, b.ops.len(),
            c, prior_mark, &mut andz_checks, &mut andz_violations, &mut andz_active_violations);
        assert_eq!(event_idx, andz_events.len(), "G-ANDZ event coverage col={c}");
        if c63c_strict {
            assert_eq!(sim.phase, 0, "C63C column-end phase col={c}");
            for (i, &lane) in cargo.iter().enumerate() {
                assert_eq!(sim.qubits[lane.0 as usize], cargo_before[i], "C63C cargo col={c} lane={i}");
            }
            if !pl_mode { for (i, &lane) in pl.iter().enumerate() {
                assert_eq!(sim.qubits[lane.0 as usize], payload_before[i], "C63C dirty NONE passenger col={c} lane={i}");
            } }
        }
        if target || full { costs.push((c, b.tof - before_t)); }
        if full { ends.push((c, usize::MAX, sim.qubits.clone(), sim.phase)); }
        if let Some((before_q, before_phase, mut inv_fd)) = inverse_before {
            if audit { super::g3p_audit::pause(); }
            let mut ib = B::new();
            ib.alloc_n(b.width() as usize);
            let isc = ColScr::carve_col(&pool, &inv_fd.sx, &pl, KP, QB, TAIL, cp.sz.1 > 255);
            let part = frogdrop_col::rec(&mut ib, |ib| frogdrop_col::column_pl(ib, &mut inv_fd, cp, &isc,
                if pl_mode { Some(&plc) } else { None }));
            ib.play(&part, true);
            ib.flush_global();
            let (iq, inb, _, _) = analyze_ops(ib.ops.iter());
            let mut ih = sha3::Shake256::default(); ih.update(b"c59e-inverse");
            let mut ixof = ih.finalize_xof();
            let mut inv = Simulator::new(sim.num_qubits.max(iq as usize), sim.num_bits.max(inb as usize), &mut ixof);
            inv.qubits[..sim.qubits.len()].copy_from_slice(&sim.qubits);
            inv.bits[..sim.bits.len()].copy_from_slice(&sim.bits);
            inv.phase = sim.phase;
            inv.apply_iter(ib.ops.iter());
            assert_eq!(inv.phase, before_phase, "C59E inverse phase col={c}");
            assert_eq!(&inv.qubits[..before_q.len()], &before_q, "C59E inverse all-wire col={c}");
            assert!(inv.qubits[before_q.len()..].iter().all(|&word| word == 0), "C59E inverse extra wires col={c}");
            eprintln!("C59E_INVERSE_PASS col={c} mode={} shots=64 all_wire=true phase=true",
                if pl_mode { "PL" } else { "NONE" });
            if audit { super::g3p_audit::resume(); }
        }
        b.ops.clear();
    }
    if audit { super::g3p_audit::finish(); }
    if std::env::var("C63B_ANDZ").as_deref() == Ok("1") {
        eprintln!("C63B_ANDZ_REPORT mode={} g3={g3} columns={stop} checks={andz_checks} violations={andz_violations} active_violations={andz_active_violations} deccc_exempt={andz_exempt}",
            if pl_mode { "PL" } else { "NONE" });
    }
    TraceData { marks: snaps, ak_lanes, sz: sz_snaps, ends, costs, final_q: sim.qubits.clone(), final_phase: sim.phase,
        andz_checks, andz_violations, andz_active_violations, andz_exempt }
}

#[test]
#[ignore = "C63C fixed-P1 Q666 strict prefix against identical-byte knob-off control"]
fn c63c_fixed_p1_prefix() {
    assert_eq!(std::env::var("C59E_TRIAL").ok().as_deref(), Some("3"));
    let stop = std::env::var("C63C_PFX_STOP").ok().and_then(|s| s.parse::<usize>().ok()).unwrap_or(141);
    let pl_mode = std::env::var("C59E_MODE").unwrap_or_else(|_| "PL".into()) == "PL";
    let xs = f3_inputs();
    let targets = [24, 25, 139, 140];
    std::env::set_var("C63C_STRICT_PREFIX", "1");
    std::env::set_var("C63B_ANDZ", "1");
    std::env::set_var("C63B_Q666_RESERVE", "0");
    let control = trace_with(true, pl_mode, stop, &xs, &targets, true);
    std::env::set_var("C63B_Q666_RESERVE", "1");
    let candidate = trace_with(true, pl_mode, stop, &xs, &targets, true);
    assert_eq!(control.ends.len(), stop);
    assert_eq!(candidate.ends.len(), stop);
    for (a, b) in control.ends.iter().zip(&candidate.ends) {
        assert_eq!(a.0, b.0, "C63C column identity");
        assert_eq!(a.2, b.2, "C63C column-end all wires col={}", a.0);
        assert_eq!(a.3, b.3, "C63C column-end phase col={}", a.0);
    }
    assert_eq!(control.andz_active_violations, 0, "C63C control active-shot G-ANDZ");
    assert_eq!(candidate.andz_active_violations, 0, "C63C candidate active-shot G-ANDZ");
    eprintln!("C63C_PFX_PASS mode={} columns={stop} shots=64 cargo=12 all_wire=true per_column_inverse=true dirty_none=true control_andz_raw={} candidate_andz_raw={} control_andz_active={} candidate_andz_active={}",
        if pl_mode { "PL" } else { "NONE" }, control.andz_violations, candidate.andz_violations,
        control.andz_active_violations, candidate.andz_active_violations);
}

#[test]
#[ignore = "C62B direct-five active-shot G-ANDZ prefix"]
fn c62b_andz_prefix() {
    assert_eq!(std::env::var("C59E_TRIAL").ok().as_deref(), Some("3"));
    let stop = std::env::var("C62B_ANDZ_STOP").ok().and_then(|s| s.parse::<usize>().ok()).unwrap_or(115);
    let pl_mode = std::env::var("C59E_MODE").unwrap_or_else(|_| "PL".into()) == "PL";
    std::env::set_var("C63B_ANDZ", "1");
    std::env::set_var("C62B_ANDZ_ONLY", "1");
    let xs = f3_inputs();
    let candidate = trace_with(true, pl_mode, stop, &xs, &[], true);
    eprintln!("C62B_ANDZ_RESULT mode={} columns={stop} checks={} raw={} active={} exempt={}",
        if pl_mode { "PL" } else { "NONE" }, candidate.andz_checks,
        candidate.andz_violations, candidate.andz_active_violations, candidate.andz_exempt);
    assert_eq!(candidate.andz_active_violations, 0, "C62B direct-five active-shot G-ANDZ");
}

#[test]
#[ignore = "C63B D7 play-boundary and differential fixture"]
fn c63b_d7_plays() {
    assert_eq!(std::env::var("C59E_TRIAL").ok().as_deref(), Some("3"));
    let pl_mode = std::env::var("C59E_MODE").unwrap_or_else(|_| "PL".into()) == "PL";
    let xs = f3_inputs();
    let targets = [37, 72, 76, 104, 113];
    std::env::remove_var("C63B_D7");
    let control = trace_with(true, pl_mode, 114, &xs, &targets, true);
    std::env::set_var("C63B_D7", "1");
    let candidate = trace_with(true, pl_mode, 114, &xs, &targets, true);
    assert_eq!(control.marks.len(), candidate.marks.len(), "D7 mark count");
    for (a, b) in control.marks.iter().zip(&candidate.marks) {
        assert_eq!((a.0, a.1), (b.0, b.1), "D7 mark identity");
        if a.2 != b.2 || a.3 != b.3 {
            let first = a.2.iter().zip(&b.2).enumerate().find(|(_, (x,y))| x != y)
                .map(|(i,(x,y))| (i,*x,*y));
            panic!("C63B_D7_DIFF col={} mark={} first={first:?} phases={:#x}/{:#x}", a.0, a.1, a.3, b.3);
        }
    }
    for (a, b) in control.ends.iter().zip(&candidate.ends) {
        assert_eq!(a.2, b.2, "D7 column-end wires col={}", a.0);
        assert_eq!(a.3, b.3, "D7 column-end phase col={}", a.0);
    }
    for ((col, old), (_, new)) in control.costs.iter().zip(&candidate.costs) {
        eprintln!("C63B_D7_COST mode={} col={col} frozen_T={old} candidate_T={new} delta={}",
            if pl_mode { "PL" } else { "NONE" }, *new as i64 - *old as i64);
    }
    eprintln!("C63B_D7_PASS mode={} columns={targets:?} boundary=ak,c,sx0_zero shots=64",
        if pl_mode { "PL" } else { "NONE" });
}

#[test]
#[ignore = "C62C Q666 direct D7 boundary and G3 session fixture"]
fn c62c_d7_direct() {
    assert_eq!(std::env::var("C59E_TRIAL").as_deref(), Ok("3"));
    assert_eq!(std::env::var("C63B_D7").as_deref(), Ok("1"));
    let pl_mode = std::env::var("C59E_MODE").unwrap_or_else(|_| "PL".into()) == "PL";
    let xs = f3_inputs();
    let targets = [37, 72, 76, 104, 113];
    let candidate = trace_with(true, pl_mode, 114, &xs, &targets, true);
    assert_eq!(candidate.ends.len(), 114);
    eprintln!("C62C_D7_DIRECT_PASS mode={} columns=114 targets={targets:?} shots=64",
        if pl_mode { "PL" } else { "NONE" });
}

#[test]
#[ignore = "C59E actual-prefix 64-shot differential fixture"]
fn c59e_g3_actual_prefix_stage_diff() {
    let stop = std::env::var("C59E_STOP").ok().and_then(|s| s.parse::<usize>().ok()).unwrap_or(139);
    let pl_mode = std::env::var("C59E_MODE").unwrap_or_else(|_| "PL".into()) == "PL";
    let a = trace(false, pl_mode, stop);
    let b = trace(true, pl_mode, stop);
    let (control, tc, qc, pc) = (&a.marks, &a.costs, &a.final_q, a.final_phase);
    let (candidate, tg, qg, pg) = (&b.marks, &b.costs, &b.final_q, b.final_phase);
    eprintln!("C59E_COST mode={} columns={stop} control_builder_T={tc:?} candidate_builder_T={tg:?}",
        if pl_mode { "PL" } else { "NONE" });
    if stop < 26 {
        assert_eq!(control.len(), candidate.len(), "C63B early mark count");
        for (a, b) in control.iter().zip(candidate) {
            assert_eq!((a.0, a.1), (b.0, b.1), "C63B early mark identity");
            // Q666 deliberately remaps fixed-R scratch during these marks.
            // Compare identities here and all wires at the cleaned boundary.
            if std::env::var("C63B_Q666_RESERVE").as_deref() != Ok("1") && (a.2 != b.2 || a.3 != b.3) {
                let first = a.2.iter().zip(&b.2).enumerate().find(|(_, (x, y))| x != y)
                    .map(|(i, (x, y))| (i, *x, *y));
                panic!("C63B_EARLY_MARK_DIFF col={} mark={} first={first:?} phases={:#x}/{:#x}",
                    a.0, a.1, a.3, b.3);
            }
        }
        if qc != qg {
            let first = qc.iter().zip(qg).enumerate().find(|(_, (x, y))| x != y)
                .map(|(i, (x, y))| (i, *x, *y));
            panic!("C63B_EARLY_DIFF last_col={} first={first:?} phases={pc:#x}/{pg:#x}", stop-1);
        }
        assert_eq!(pc, pg, "C63B early prefix phase");
        eprintln!("C63B_EARLY_PREFIX_PASS mode={} columns={stop} shots=64",
            if pl_mode { "PL" } else { "NONE" });
        return;
    }
    assert!(!control.is_empty(), "C59E no target marks");
    assert_eq!(control.len(), candidate.len(), "C59E mark count");
    if stop > 138 { assert_eq!(control.len(), 552, "C59E full F2 mark count"); }
    for &col in &[26, 32, 76, 121, 138] {
        if col >= stop { continue; }
        assert!(candidate.iter().any(|x| x.0 == col), "C59E missing target marks col={col}");
    }
    if stop > 138 { for &col in &[121, 138] {
        for (lo, hi) in [(6140, 6149), (6220, 6232), (6280, 6284)] {
            assert!(candidate.iter().any(|x| x.0 == col && (lo..=hi).contains(&x.1)),
                "C59E missing q0-in-ph loop col={col} marks={lo}..{hi}");
        }
    } }
    for (a, b) in control.iter().zip(candidate) {
        assert_eq!((a.0, a.1), (b.0, b.1), "C59E mark identity");
        if a.2 != b.2 || a.3 != b.3 {
            let first = a.2.iter().zip(&b.2).enumerate().find(|(_, (x, y))| x != y)
                .map(|(i, (x, y))| (i, *x, *y));
            panic!("C59E_STAGE_DIFF col={} mark={} first={first:?} phase_control={:#x} phase_g3={:#x} mode={}",
                a.0, a.1, a.3, b.3, if pl_mode { "PL" } else { "NONE" });
        }
    }
    log_vg_words(&a.sz, &b.sz, if pl_mode { "PL" } else { "NONE" }, "F2");
    assert_eq!(qc, qg, "C59E final prefix wires");
    assert_eq!(pc, pg, "C59E final prefix phase");
    eprintln!("C59E_PFX_PASS mode={} columns={stop} shots=64 marks={} cargo=12 dirty_passengers=true control_T={tc:?} g3_T={tg:?}",
        if pl_mode { "PL" } else { "NONE" }, control.len());
}

const F3_TARGETS: [usize; 12] = [26, 32, 37, 72, 76, 85, 88, 104, 112, 113, 121, 138];

fn f3_t1(sy: usize) -> usize {
    match sy { 1..=120 => 5, 121..=123 => 4, 124..=127 => 2, 128 => 1, _ => panic!("F3 sy={sy}") }
}
fn f3_t2(sy: usize) -> usize {
    match sy { 1..=118 => 13, 119..=120 => 11, 121 => 10, 122..=123 => 8,
        124..=128 => 5, _ => panic!("F3 sy={sy}") }
}

fn f3_profile(sz: usize, sy: usize) -> (usize, usize, usize, usize, usize) {
    let tb = 257usize.saturating_sub(sz + sy).min(22);
    let (t1, t2) = (f3_t1(sy), f3_t2(sy));
    (t1, t2, t1.min(tb + 1), (tb + 1).saturating_sub(t1).min(t2 - t1),
        (tb + 1).saturating_sub(t2))
}

fn f3_inputs() -> Vec<N> {
    let named: [(&str, &str, Option<(usize, Kind, usize, usize)>); 12] = [
        ("x0", "24da2b3aa967419120e4517f75ac5c7100b64a5fb8020834706ca618d1ae8d28", None),
        ("x1", "337e0487c47c5a313bc0905119b944dfa74de639c9d5d2aae3684738ba378171", None),
        ("B26", "44c0bba21c9bbb8286fca90342b407e1b6c666b27e493caf12a8f43583f62010", Some((26, Kind::Hr, 206, 37))),
        ("B32", "e548a354b0956d89c967a1fab4e8482c4ad007d6ae71d6df9ee5a0599f988efa", Some((32, Kind::Hr, 203, 41))),
        ("B121", "46f160750be42389f6ec81fa9eb4d4865b538a767d3540655a0926f1276aaaa8", Some((121, Kind::Ht, 181, 60))),
        ("B138", "9bacca6d5c4ef5148baae4e71a74a654be9afb9aefaacf73967c759f186d4556", Some((138, Kind::Ht, 235, 9))),
        ("M121", "35d9eafd5685cfa4b57f3a8a3194d2119db9257c6f3faa75b97a4ca341675c6e", Some((121, Kind::Ht, 231, 20))),
        ("M138", "0913bf9acfae7e93c54c5c9242b25c42ef71a3c0a05244832b35d19c7ad45781", Some((138, Kind::Ht, 225, 25))),
        ("W3", "8bdedcc9d66b3fb9b49af95355b11673d6b3ddd66cc0e97ea68ce039b95ec60c", Some((26, Kind::Hr, 210, 33))),
        ("W5", "9957ce5ef387f34e22ef7c51f4e416bc95bd9eb3a0d3e9c6591878ffb5216969", Some((138, Kind::Ht, 245, 7))),
        ("W1p", "bfd5248a40fdb9c89b50e31796d8129096fa447f7287eb80aec7e926c5236d07", Some((85, Kind::Hr, 129, 126))),
        ("W8", "59d9028ed4415b4a73b4af684f66c8f964e1c0f093bbd60caadd33b1a326f84d", Some((72, Kind::Hr, 131, 119))),
    ];
    let sched = from_text(SCHED_FROGDROP);
    let mut xs = Vec::with_capacity(64);
    for (idx, &(name, hex, expected)) in named.iter().enumerate() {
        let mut x = N::from_str_radix(hex, 16).unwrap();
        let mut s = shot(x, L0);
        if let Some((col, kind, sz, sy)) = expected {
            if (s.rec(col).kind, s.rec(col).sz, s.rec(col).sy) != (kind, sz, sy) {
                let want_profile = f3_profile(sz, sy);
                let seed = 0xc63_6300_0000u64 ^ idx as u64;
                let found = super::frogdrop_sched::sample(50_000, seed).into_iter().find(|&candidate| {
                    let candidate_shot = shot(candidate, L0);
                    if super::frogdrop_sched::check(&candidate_shot, &sched).is_some() { return false; }
                    let r = candidate_shot.rec(col);
                    r.kind == kind && f3_profile(r.sz, r.sy) == want_profile
                        && candidate_shot.recs.iter().filter(|r| matches!(r.kind, Kind::Hr | Kind::Ht))
                            .all(|r| 257usize.saturating_sub(r.sz + r.sy) <= 25)
                }).unwrap_or_else(|| panic!("C63 no seeded replacement name={name} col={col} profile={want_profile:?}"));
                eprintln!("C63_WITNESS_REPLACED name={name} col={col} original={x:?} replacement={found:?} original_rec={:?} replacement_rec={:?} seed={seed:#x}",
                    s.rec(col), shot(found, L0).rec(col));
                x = found;
                s = shot(x, L0);
                assert_eq!(s.rec(col).kind, kind, "C63 replacement kind {name}");
                assert_eq!(f3_profile(s.rec(col).sz, s.rec(col).sy), want_profile, "C63 replacement band {name}");
            }
        }
        assert_eq!(super::frogdrop_sched::check(&s, &sched), None, "C63 named envelope {name}");
        assert!(s.recs.iter().filter(|r| matches!(r.kind, Kind::Hr | Kind::Ht))
            .all(|r| 257usize.saturating_sub(r.sz + r.sy) <= 25), "C63 named g_max {name}");
        eprintln!("C63_WITNESS name={name} designated={expected:?} records={}", s.recs.len());
        xs.push(x);
    }
    for x in super::frogdrop_sched::sample(1024, 0xc63_0000_0052) {
        if xs.len() == 64 { break; }
        let s = shot(x, L0);
        if super::frogdrop_sched::check(&s, &sched).is_some() { continue; }
        if s.recs.iter().filter(|r| matches!(r.kind, Kind::Hr | Kind::Ht))
            .any(|r| 257usize.saturating_sub(r.sz + r.sy) > 25) { continue; }
        xs.push(x);
    }
    assert_eq!(xs.len(), 64, "C63 seeded fill exhausted");
    eprintln!("C63_WITNESS_FILL accepted=52 seed=0xc6300000052 scanned_max=1024");
    xs
}

fn f3_coverage(xs: &[N]) {
    let sched = from_text(SCHED_FROGDROP);
    let mut cov = BTreeMap::<&'static str, usize>::new();
    let mut by_col = BTreeMap::<(usize, &'static str), usize>::new();
    let mut hit = |col, key| {
        *cov.entry(key).or_default() += 1;
        *by_col.entry((col, key)).or_default() += 1;
    };
    for &x in xs {
        let s = shot(x, L0);
        for &c in &F3_TARGETS {
            let r = s.rec(c);
            let cp = &sched.cols[c];
            match r.kind {
                Kind::Hr | Kind::Ht => {
                    if !(1..=128).contains(&r.sy) {
                        hit(c, "out_of_support_sy");
                        continue;
                    }
                    let g = 257usize.saturating_sub(r.sz + r.sy);
                    let tb = g.min(22);
                    let t1 = f3_t1(r.sy);
                    let t2 = f3_t2(r.sy);
                    let mid = (tb + 1).saturating_sub(t1).min(t2 - t1);
                    let bot = (tb + 1).saturating_sub(t2);
                    if r.kind == Kind::Hr {
                        hit(c, "hr_top");
                        if mid > 0 { hit(c, "hr_middle"); }
                        if bot > 0 { hit(c, "hr_bottom"); }
                        if cp.ht { hit(c, "hr_in_ht_session"); }
                    } else {
                        if mid > 0 { hit(c, "ht_middle"); }
                        if mid >= 2 { hit(c, "ht_middle_ge2"); }
                        if bot > 0 { hit(c, "ht_bottom"); }
                        if cp.hr { hit(c, "ht_in_hr_session"); }
                    }
                }
                Kind::Idle => if c == 138 { hit(c, "done_138"); },
                Kind::Sw => hit(c, "kind_sw"),
                Kind::Dq => hit(c, "kind_dq"),
                Kind::Dl => hit(c, "kind_dl"),
            }
        }
    }
    for &c in &F3_TARGETS {
        let cp = &sched.cols[c];
        if cp.sw { hit(c, "switch_column"); }
        if cp.dl { hit(c, "dl_column"); }
        if cp.dq { hit(c, "dq_column"); }
        if cp.dn { hit(c, "dn_column"); }
    }
    for (&(col, key), &count) in &by_col {
        eprintln!("C63_COVERAGE_COL col={col} key={key} count={count}");
    }
    for (&key, &count) in &cov { eprintln!("C63_COVERAGE key={key} count={count}"); }
    for key in ["hr_top", "hr_middle", "hr_bottom", "ht_middle", "ht_middle_ge2", "ht_bottom",
        "hr_in_ht_session", "ht_in_hr_session", "done_138", "kind_sw", "kind_dq", "kind_dl",
        "switch_column", "dl_column", "dq_column", "dn_column"] {
        assert!(cov.get(key).copied().unwrap_or(0) > 0, "C63 coverage gap {key}");
    }
    for &(col, key) in &[(26, "hr_bottom"), (32, "hr_bottom"), (121, "ht_middle_ge2"),
        (138, "ht_middle_ge2"), (121, "ht_bottom"), (138, "ht_bottom"), (138, "done_138")] {
        assert!(by_col.get(&(col, key)).copied().unwrap_or(0) > 0,
            "C63 per-column coverage gap col={col} key={key}");
    }
}

#[test]
fn c63_g3p_witness_coverage() {
    let xs = f3_inputs();
    f3_coverage(&xs);
    eprintln!("C63_WITNESS_COVERAGE_PASS inputs={}", xs.len());
}

#[test]
#[ignore = "C63 all-column 64-witness actual-prefix differential fixture"]
fn c63_g3p_all_column_witness_diff() {
    assert_eq!(std::env::var("C59E_TRIAL").ok().as_deref(), Some("3"));
    let pl_mode = std::env::var("C59E_MODE").unwrap_or_else(|_| "PL".into()) == "PL";
    let xs = f3_inputs();
    f3_coverage(&xs);
    let total = from_text(SCHED_FROGDROP).cols.len();
    let stop = std::env::var("C63_F3_STOP").ok().map(|v| v.parse::<usize>().expect("C63_F3_STOP integer"))
        .unwrap_or(total);
    assert!(stop <= total);
    let a = trace_with(false, pl_mode, stop, &xs, &F3_TARGETS, true);
    let b = trace_with(true, pl_mode, stop, &xs, &F3_TARGETS, true);
    assert_eq!(a.marks.len(), b.marks.len(), "C63 mark count");
    assert_eq!(a.ak_lanes, b.ak_lanes, "C63 transient ak physical lanes");
    let mut role_marks = 0usize;
    for (x, y) in a.marks.iter().zip(&b.marks) {
        assert_eq!((x.0, x.1), (y.0, y.1), "C63 mark identity");
        assert_eq!(x.2.len(), y.2.len(), "C63 mark wire count");
        let pair = if (1000..=1022).contains(&x.1) {
            role_marks += 1;
            Some(*a.ak_lanes.iter().find(|v| v.0 == x.0).expect("C63 target ak lanes"))
        } else { None };
        let first = (0..x.2.len()).find_map(|i| {
            let j = match pair {
                Some((_, sx3, sx6)) if i == sx3 => sx6,
                Some((_, sx3, sx6)) if i == sx6 => sx3,
                _ => i,
            };
            (x.2[i] != y.2[j]).then_some((i, j, x.2[i], y.2[j]))
        });
        if first.is_some() || x.3 != y.3 {
            panic!("C63_STAGE_DIFF col={} mark={} lanes={first:?} ak_pair={pair:?} phase_control={:#x} phase_g3p={:#x} mode={}",
                x.0, x.1, x.3, y.3, if pl_mode { "PL" } else { "NONE" });
        }
    }
    eprintln!("C63_AK_ROLE_PASS mode={} transient_marks={} raw_session_marks={}",
        if pl_mode { "PL" } else { "NONE" }, role_marks, a.marks.len() - role_marks);
    log_vg_words(&a.sz, &b.sz, if pl_mode { "PL" } else { "NONE" }, "F3");
    assert_eq!(a.ends.len(), stop);
    assert_eq!(a.ends.len(), b.ends.len());
    for (x, y) in a.ends.iter().zip(&b.ends) {
        assert_eq!(x.0, y.0);
        assert_eq!(x.2, y.2, "C63 column-end all-wire col={}", x.0);
        assert_eq!(x.3, y.3, "C63 column-end phase col={}", x.0);
    }
    assert_eq!(a.final_q, b.final_q, "C63 final wires");
    assert_eq!(a.final_phase, b.final_phase, "C63 final phase");
    for ((ca, ta), (cb, tb)) in a.costs.iter().zip(&b.costs) {
        assert_eq!(ca, cb);
        eprintln!("C63_COST mode={} col={ca} control_builder_T={ta} candidate_builder_T={tb} delta={}",
            if pl_mode { "PL" } else { "NONE" }, *tb as i64 - *ta as i64);
    }
    if stop == total {
        eprintln!("C63_F3_PASS mode={} columns={stop} shots=64 marks={} inverse={} cargo=12 dirty_passengers=true",
            if pl_mode { "PL" } else { "NONE" }, a.marks.len(), F3_TARGETS.len());
    } else {
        eprintln!("C63_F3_DEV_STOP mode={} columns={stop} shots=64 marks={}",
            if pl_mode { "PL" } else { "NONE" }, a.marks.len());
    }
}
