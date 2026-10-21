//! G3' emitted-gate audit. The builder calls `on_g` after the conditional
//! clean-target conversion, and only replayed gates are counted. A control
//! trace calibrates outside-session-lane AND targets before the candidate.
use super::builder::{B, G};
use crate::circuit::QubitId;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};

type CalKey = (&'static str, &'static str, u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Mode { Off, Control, Candidate }

#[derive(Clone, Debug)]
struct Scope {
    name: &'static str,
    sx: Vec<QubitId>,
    sz: Vec<QubitId>,
    ph: QubitId,
    excluded: usize,
    gate_nat: usize,
    checked: u64,
    omitted: u64,
}

struct Audit {
    mode: Mode,
    paused: Option<Mode>,
    pl_mode: Option<bool>,
    col: usize,
    scope: Option<Scope>,
    calibrated: BTreeSet<CalKey>,
    counts: BTreeMap<(usize, &'static str), (u64, u64)>,
    and_targets: BTreeMap<(usize, &'static str, &'static str, u64), u64>,
}

impl Default for Audit {
    fn default() -> Self {
        Self { mode: Mode::Off, paused: None, pl_mode: None, col: usize::MAX, scope: None,
            calibrated: BTreeSet::new(), counts: BTreeMap::new(), and_targets: BTreeMap::new() }
    }
}

thread_local! { static AUDIT: RefCell<Audit> = RefCell::new(Audit::default()); }

pub(super) fn begin_control() {
    AUDIT.with(|a| {
        let mut a = a.borrow_mut();
        assert!(a.scope.is_none(), "G3P_AUDIT live scope on reset");
        *a = Audit::default();
        a.mode = Mode::Control;
    });
}

pub(super) fn begin_candidate() {
    AUDIT.with(|a| {
        let mut a = a.borrow_mut();
        assert!(a.scope.is_none(), "G3P_AUDIT live scope on reset");
        assert_eq!(a.mode, Mode::Off, "G3P_AUDIT finish control first");
        // An empty set is valid when the unchanged 669 emits no outside-S
        // AND target in the selected prefix. Candidate targets are still
        // checked against this exact set.
        a.mode = Mode::Candidate;
        a.counts.clear();
        a.and_targets.clear();
    });
}

pub(super) fn set_column(col: usize) {
    AUDIT.with(|a| {
        let mut a = a.borrow_mut();
        assert!(a.scope.is_none(), "G3P_AUDIT column changed in session");
        a.col = col;
    });
}

pub(super) fn set_pl_mode(pl_mode: bool) {
    AUDIT.with(|a| {
        let mut a = a.borrow_mut();
        assert!(a.scope.is_none());
        a.pl_mode = Some(pl_mode);
    });
}

/// Inverse replay is checked by the simulator and has its own builder. Keep
/// its construction out of the forward-column emitted-gate census.
pub(super) fn pause() { AUDIT.with(|a| {
    let mut a = a.borrow_mut();
    assert!(a.scope.is_none() && a.paused.is_none());
    a.paused = Some(a.mode);
    a.mode = Mode::Off;
}); }
pub(super) fn resume() { AUDIT.with(|a| {
    let mut a = a.borrow_mut();
    assert!(a.scope.is_none());
    a.mode = a.paused.take().expect("G3P_AUDIT resume without pause");
}); }

pub(super) fn finish() {
    AUDIT.with(|a| {
        let mut a = a.borrow_mut();
        if a.mode == Mode::Off { return; }
        assert!(a.scope.is_none(), "G3P_AUDIT live scope at finish");
        let pl_mode = a.pl_mode.expect("G3P_AUDIT payload mode not set");
        for (&(col, stage), &(checked, excluded)) in &a.counts {
            let scope_present = stage != "hr_stage4" || pl_mode;
            eprintln!("G3P_AUDIT col={col} stage={stage} mode={:?} payload={} checked={checked} excluded={excluded} excluded_scope_present={scope_present}",
                a.mode, if pl_mode { "PL" } else { "NONE" });
            assert!(checked > 0, "G3P_AUDIT empty session col={col} stage={stage}");
            if scope_present {
                assert!(excluded > 0, "G3P_AUDIT empty excluded scope col={col} stage={stage}");
            } else {
                assert_eq!(excluded, 0, "G3P_AUDIT unexpected excluded gate in NONE hr_stage4 col={col}");
            }
        }
        assert!(!a.counts.is_empty(), "G3P_AUDIT no sessions");
        for (&(col, stage, label, lane), &n) in &a.and_targets {
            eprintln!("G3P_AND_TARGET col={col} stage={stage} label={label} lane={lane} count={n} mode={:?}", a.mode);
        }
        eprintln!("G3P_AUDIT_PASS mode={:?} sessions={} calibration_keys={}",
            a.mode, a.counts.len(), a.calibrated.len());
        a.mode = Mode::Off;
    });
}

pub(super) fn enter_session(name: &'static str, sx: &[QubitId], sz: &[QubitId], ph: QubitId) {
    AUDIT.with(|a| {
        let mut a = a.borrow_mut();
        if a.mode == Mode::Off { return; }
        assert!(a.scope.is_none(), "G3P_AUDIT nested session");
        assert_eq!(sx.len(), 8);
        assert_eq!(sz.len(), 8);
        a.scope = Some(Scope { name, sx: sx.to_vec(), sz: sz.to_vec(), ph,
            excluded: 0, gate_nat: 0, checked: 0, omitted: 0 });
    });
}

pub(super) fn exit_session() {
    AUDIT.with(|a| {
        let mut a = a.borrow_mut();
        if a.mode == Mode::Off { return; }
        let s = a.scope.take().expect("G3P_AUDIT exit without session");
        assert_eq!(s.excluded, 0, "G3P_AUDIT excluded scope leaked");
        assert_eq!(s.gate_nat, 0, "G3P_AUDIT gate_nat scope leaked");
        assert!(super::mask::R11O11_DECCC.with(|c| c.borrow().is_empty()),
            "G3P_AUDIT DECCC live at stage exit");
        let col = a.col;
        let prev = a.counts.insert((col, s.name), (s.checked, s.omitted));
        assert!(prev.is_none(), "G3P_AUDIT duplicate stage col={} stage={}", a.col, s.name);
    });
}

pub(super) fn enter_excluded() { AUDIT.with(|a| {
    if let Some(s) = a.borrow_mut().scope.as_mut() { s.excluded += 1; }
}); }
pub(super) fn exit_excluded() { AUDIT.with(|a| {
    if let Some(s) = a.borrow_mut().scope.as_mut() {
        assert!(s.excluded > 0, "G3P_AUDIT excluded underflow"); s.excluded -= 1;
    }
}); }
pub(super) fn enter_gate_nat() { AUDIT.with(|a| {
    if let Some(s) = a.borrow_mut().scope.as_mut() { s.gate_nat += 1; }
}); }
pub(super) fn exit_gate_nat() { AUDIT.with(|a| {
    if let Some(s) = a.borrow_mut().scope.as_mut() {
        assert!(s.gate_nat > 0, "G3P_AUDIT gate_nat underflow"); s.gate_nat -= 1;
    }
}); }

pub(super) fn on_g(b: &B, g: &G) {
    if b.g3p_is_recording() { return; }
    AUDIT.with(|cell| {
        let mut a = cell.borrow_mut();
        if a.mode == Mode::Off { return; }
        let Some(s) = a.scope.as_mut() else { return; };
        if s.excluded > 0 { s.omitted += 1; return; }
        s.checked += 1;
        let name = s.name;
        let label = if s.gate_nat > 0 { "gate_nat" } else { "session" };
        let sx = s.sx.clone();
        let sz = s.sz.clone();
        let ph = s.ph;
        let lanes: Vec<QubitId> = match *g {
            G::X(t) | G::XIf(t, _) | G::ZIf(t, _) => vec![t],
            G::Cx(x, t) | G::Cz(x, t) | G::Swap(x, t) => vec![x, t],
            G::Ccx(x, y, t) | G::AndC(x, y, t) | G::AndU(x, y, t) => vec![x, y, t],
            G::RowAdd(id, _) => b.g3p_row_lanes(id),
            G::DeferredErase(id, _) => panic!("G3P_AUDIT DeferredErase col={} stage={name} id={id}", a.col),
        };
        if a.mode == Mode::Candidate {
            for &q in &lanes {
                for i in [1, 4, 6] {
                    if super::frogdrop_col::c66_direct() {
                        // Q666's three Z bits reside on these sx lanes.
                        // The physical lanes are active size data. Their
                        // arithmetic writes are checked by G-ALIAS-USE's
                        // source-role guard and by the boundary replay.
                        if sz.contains(&q) { continue; }
                        if i == 1 && super::midg::g3p_frame_active() { continue; }
                    }
                    assert_ne!(q, sx[i],
                        "G3P_AUDIT A1 col={} stage={name} label={label} gate={g:?} sx{i}=q{}", a.col, q.0);
                }
            }
        }
        if let G::AndC(_, _, target) | G::AndU(_, _, target) = *g {
            let col = a.col;
            *a.and_targets.entry((col, name, label, target.0)).or_default() += 1;
            let allowed_local = target == sx[0] || (label == "gate_nat" && (target == sx[2] || target == sx[3]));
            let in_s = sx.contains(&target) || sz.contains(&target) || target == ph;
            if !in_s {
                if a.mode == Mode::Control { a.calibrated.insert((name, label, target.0)); }
                else {
                    assert!(a.calibrated.contains(&(name, label, target.0)),
                        "G3P_AUDIT A2 uncalibrated col={} stage={name} label={label} target=q{} gate={g:?}", a.col, target.0);
                }
            } else if a.mode == Mode::Candidate {
                assert!(allowed_local,
                    "G3P_AUDIT A2 local col={} stage={name} label={label} target=q{} gate={g:?}", a.col, target.0);
            }
        }
    });
}
