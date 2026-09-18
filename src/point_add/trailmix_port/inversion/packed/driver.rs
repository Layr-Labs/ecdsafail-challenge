//! The packed per-step driver (`tools/spike/packed_design.md` sections 3.3 and
//! 3.4, plan P4): the exact role compute and clear, the two real substeps
//! under their held hybrid gates, the terminal predicate wire, the swap and
//! the done counter, forward and backward. Replaces the P0 stubs of
//! `p0_shape.rs` (`MIDQ_PACKED_STUBS=1` restores them for the allocation
//! timeline measurement); everything around the step (S_0, teardown,
//! handoff, q resizing, the popcount cache erase at `MIDQ_PREFIX_TERMINAL_FROM`)
//! stays in `p0_shape.rs`.
//!
//! # The step (forward)
//!
//! ```text
//!   active = [counter == 0]                (rows >= FROM; a plain |1> before)
//!   role  ^= active AND [A < B]            role_compute: exact (3.3)
//!   (popcount cache: counter += active * (role ? -1 : +1), rows < FROM)
//!   gate_mul = active AND role  ->  multiply_forward (M1..M12)  -> release
//!   role ^= active                         (X(role) on active rows: role = [A >= B])
//!   gate_div = active AND role  ->  division_forward (D1..D12, `term` live on rows >= FROM) -> release
//!   role  ^= active AND [ca < cb]          role_clear: exact (3.3); role -> 0
//!   swap (257 + 18 cswaps under q_zero [AND active AND a_nonzero on rows >= FROM]),
//!   parity, done counter (rows >= FROM), active uncomputed
//! ```
//!
//! The backward direction runs the mirrored sequence with the inverse of every
//! item (`undo_done_and_swap`, `role_clear` (self-inverse: it sets `role` to
//! `[ca < cb]` = the division role), `division_backward`, `X(role)`,
//! `multiply_backward`, the popcount update inverse, `role_compute` (clears
//! `role`), `active` uncomputed).
//!
//! # The exact role pair (design 3.3)
//!
//! `role_compute`: `m := max(e_ca, e_cb)` by `exponent_arith::max_into_second`
//! (`c = [e_ca < e_cb]`, X, 9 cswaps: `e_cb` holds `m`), then the plain borrow
//! cascade `R1 vs R2` over the cells `[0, 256 - lo_c)` with the borrow captured
//! at the leaf `m` (`capture_compare`, `FieldEnd::BaseMinusAddr(257)`: `k =
//! 257 - m` cells = wires `[0, 257 - m)`), i.e. `role ^= active AND [A mod
//! 2^(257-m) < B mod 2^(257-m)] = active AND [A < B]` exactly, because
//! `max(e_A, e_B) <= 257 - m` on every step-start state (section 1: the fit
//! fact, 0 violations / 8.96M) and both rings are zero on `[max(e_A, e_B),
//! 257 - m)`. Then the cswaps and `c` are undone. `lo_c = max(lo_ca, lo_cb)`
//! is the schedule's lower bound of `m` (`m >= lo_c + 1` on the support, the
//! `lo` miss kinds the design keeps), `hi = W_c`.
//!
//! `role_clear`: the same construction on the coefficients with `m' =
//! max(e_A, e_B)` (`e_B` holds `m'`), the cascade in bit order (cell `j` =
//! wire `256 - j`) over `[0, 256 - lo_v)` and the capture at `k = 257 - m'`:
//! `role ^= active AND [ca < cb]`. After the substeps `[ca < cb]` is exactly
//! the division role (`A_old >= B_old`): a division row leaves `ca < cb`, a
//! multiply row makes `ca_new >= cb`, a draining row is a multiply row, a
//! frozen row has `ca = p > cb` and `active = 0` anyway. `lo_v =
//! max(lo_a, lo_b)` on the mid rows; **0 on the terminal-aware rows** (draining
//! and frozen rows have `e_A = 0`, `e_B = 1`, so `m' = 1` there and the
//! schedule's `lo_a` would put the capture leaf outside the window: the role
//! would never be cleared on a draining row) **and on the late rows**
//! (`sched.lo_b_free()`, `lo_b <= 32`: no `lo_b` dependence anywhere in the
//! step there, `sched::StepWidths::role_clear_lo_v`). `hi = W_A`.
//!
//! Both are rooted at `active` (every write of the step is), so a frozen row
//! never touches `role`; the flip between the substeps is `cx(active, role)`
//! for the same reason (an unconditional X would leave `role = 1` on a frozen
//! row with nothing rooted at `active` able to clear it). The exponent form of the design ("where cheaper the
//! schedule picks it per step") is not built: the plain form is exact
//! everywhere and costs `2n + 2z + 54` per compare (~380 + ~720 T at step
//! 378); the windowed variant is a priced lever.
//!
//! # Per-step invariants
//!
//! `sched::StepWidths::from_schedule(i)` is the one geometry source of the
//! step (both substeps, the role pair): `assert_packed_step` checks `w_q <= 31`
//! (the 5-bit shift word's real bound, `sched.rs` "q envelope") and the D11
//! ring width, and `p.q` must be at the row's envelope. `MIDQ_PACKED_DUMP_SCHED=1`
//! prints every row's geometry (`p0_shape::prefix_forward`).
//!
//! # Environment inside the step
//!
//! The packed scans need `MIDQ_KG_ZERO_LAYER=1` and `MIDQ_CHUNKED_PREFIX != 1`
//! (asserted by `aligned_scan`), and every chunk planner of the step (the
//! direct ctz of D12, the measured demux of D8, the chunked predicates of the
//! swap and of `active` - `MIDQ_PREFIX_QCAP`; the chunked measured compare
//! behind `borrow_compare_refs` in the 9-bit exponent compares -
//! `MIDQ_CHUNK_COMPARE_QCAP`, which at the shipped 974 planned M1's `nz`
//! compare 8 wires above the adder moment) must plan against the packed
//! peak, not the shipped 974: [`StepEnv`] sets the seven `MIDQ_*_QCAP` of
//! the route to `MIDQ_PACKED_QCAP` (default 850) for the duration of one
//! `pass_step` and restores them after, the `with_plain_ladder` pattern of
//! `p0_shape.rs`. A planner that cannot fit falls back to its plain form
//! (the 9-bit compare's plain cascade: 1 scratch wire) or panics with the
//! numbers (the ctz), never silently above the cap.
//!
//! # Moment census (design section 5 acceptance)
//!
//! With `TRACE_PHASE_ACTIVE=1` the builder records the live maximum of every
//! section region; [`pass_step`] classifies the regions of its own step by
//! section name (`D7`/`M5` = the adder moment, `pk.role*` = the role pair,
//! `pk.swap` = the swap, every other `pk.div`/`pk.mul` item = a scan/capture
//! moment; the cap-filling planners `p.cmp.chunk` / `p.ctz.direct` /
//! `chunked.predicate` sit at the cap by construction and are reported apart
//! as `planner`) and returns them, so `p0_shape::report_moments` prints the
//! same `MIDQ_P0_MOMENTS` line as the stub build and `MIDQ_P0_TRACE=1` the
//! per-step `MIDQ_P0_STEP` lines. The acceptance of section 5 is
//! `max(scan, role) <= adder` per step on the structural moments.

use super::super::*;
use super::capture_compare::{capture_compare, CaptureWindow, FieldEnd};
use super::division::{division_backward, division_forward};
use super::exponent_arith::{max_into_second, unmax_into_second};
use super::multiply::{multiply_backward, multiply_forward};
use super::p0_shape::{popcount_on, swap_and_done_forward, terminal_from, undo_done_and_swap, Packed};
use super::sched::{StepWidths, DEFAULT_QCAP, RING};

#[path = "driver_selftest.rs"]
pub(crate) mod driver_selftest;

/// The P0 allocation-timeline stubs instead of the real substeps.
pub(crate) fn stubs_enabled() -> bool {
    std::env::var("MIDQ_PACKED_STUBS").ok().as_deref() == Some("1")
}

/// The packed peak every chunk planner of the step budgets against.
pub(crate) fn packed_cap() -> usize {
    env_usize("MIDQ_PACKED_QCAP", DEFAULT_QCAP)
}

/// Per-step live-count census (module doc). `traced` is false when
/// `TRACE_PHASE_ACTIVE` is unset (all counts 0 then).
#[derive(Clone, Debug, Default)]
pub(crate) struct StepMoments {
    pub traced: bool,
    pub adder: u32,
    pub adder_kind: &'static str,
    pub scan: u32,
    pub scan_kind: &'static str,
    pub role: u32,
    pub swap: u32,
    pub other: u32,
    pub other_kind: &'static str,
    /// Cap-filling planners (the chunked measured compare, the direct ctz,
    /// the chunked predicates): they take whatever room the cap leaves, so
    /// their moment equals the cap by construction and is reported apart.
    pub planner: u32,
    pub planner_kind: &'static str,
}

/// Process-environment guard for one packed step (module doc).
struct StepEnv {
    saved: Vec<(&'static str, Option<std::ffi::OsString>)>,
}

impl StepEnv {
    fn enter() -> Self {
        let cap = packed_cap().to_string();
        let wanted: [(&'static str, String); 9] = [
            ("MIDQ_KG_ZERO_LAYER", "1".to_string()),
            ("MIDQ_CHUNKED_PREFIX", "0".to_string()),
            // every chunk planner the step can reach: the direct ctz, the
            // measured demux and the chunked predicates (PREFIX), the chunked
            // measured compare of the 9-bit exponent compares (CHUNK_COMPARE);
            // the other five are the shipped route's remaining caps, pinned
            // for the same reason (nothing in the step reaches them today).
            ("MIDQ_PREFIX_QCAP", cap.clone()),
            ("MIDQ_CHUNK_COMPARE_QCAP", cap.clone()),
            ("MIDQ_CONTROLLED_ADD_QCAP", cap.clone()),
            ("MIDQ_CELL_QCAP", cap.clone()),
            ("MIDQ_ZERO_SCRATCH_QCAP", cap.clone()),
            ("MIDQ_OUTER_VENT_QCAP", cap.clone()),
            ("MIDQ_PZ_VENT_QCAP", cap),
        ];
        let mut saved = Vec::with_capacity(wanted.len());
        for (k, v) in wanted {
            saved.push((k, std::env::var_os(k)));
            std::env::set_var(k, v);
        }
        Self { saved }
    }

    fn restore(self) {
        for (k, v) in self.saved.into_iter().rev() {
            match v {
                Some(v) => std::env::set_var(k, v),
                None => std::env::remove_var(k),
            }
        }
    }
}

/// `role ^= active AND [A < B]` (exact; module doc).
fn role_compute(c: &mut Circuit, p: &Packed, active: &QReg, role: &QReg, sched: &StepWidths) {
    let sec = c.push_section("pk.role");
    let flag = c.alloc_qreg("pk.rc.c");
    max_into_second(c, p.e_ca(), p.e_cb(), &flag); // e_cb := m = max(e_ca, e_cb)
    let lo_c = sched.lo_ca.max(sched.lo_cb).min(RING - 2);
    let n = RING - 1 - lo_c; // cells [0, n): k = 257 - m <= 256 - lo_c
    let v: Vec<&QReg> = p.r1[..n].iter().collect();
    let u: Vec<&QReg> = p.r2[..n].iter().collect();
    let window = CaptureWindow { lo: lo_c + 1, hi: sched.w_c.max(lo_c + 1), field: FieldEnd::BaseMinusAddr(RING), base: sched.base_c() };
    capture_compare(c, active, &v, &u, p.e_cb(), window, role);
    unmax_into_second(c, p.e_ca(), p.e_cb(), &flag);
    c.zero_and_free(flag);
    c.pop_section(&sec);
}

/// `role ^= active AND [ca < cb]` (exact; module doc). `terminal_row` widens
/// the capture window down to `m' = 1` (draining / frozen rows).
fn role_clear(c: &mut Circuit, p: &Packed, active: &QReg, role: &QReg, sched: &StepWidths, terminal_row: bool) {
    let sec = c.push_section("pk.roleclr");
    let flag = c.alloc_qreg("pk.rc.c");
    max_into_second(c, p.e_a(), p.e_b(), &flag); // e_b := m' = max(e_A, e_B)
    let lo_v = sched.role_clear_lo_v(terminal_row);
    let n = RING - 1 - lo_v;
    let v: Vec<&QReg> = (0..n).map(|j| &p.r2[RING - 1 - j]).collect(); // ca bit j
    let u: Vec<&QReg> = (0..n).map(|j| &p.r1[RING - 1 - j]).collect(); // cb bit j
    let window = CaptureWindow { lo: lo_v + 1, hi: sched.w_a.max(lo_v + 1), field: FieldEnd::BaseMinusAddr(RING), base: sched.base_v() };
    capture_compare(c, active, &v, &u, p.e_b(), window, role);
    unmax_into_second(c, p.e_a(), p.e_b(), &flag);
    c.zero_and_free(flag);
    c.pop_section(&sec);
}

/// One packed prefix row, forward or backward (module doc). `p.q` is already
/// at the row's envelope width; the caller pushes the `pk.step` section.
pub(crate) fn pass_step(c: &mut Circuit, p: &Packed, i: usize, inverse: bool) -> StepMoments {
    let env = StepEnv::enter();
    let sched = StepWidths::from_schedule(i);
    sched.assert_packed_step();
    assert_eq!(p.q.len(), sched.w_q.max(1), "packed step {i}: q register {} is not at the envelope {}", p.q.len(), sched.w_q);
    let no_terminal = i < terminal_from();
    let terminal_row = !no_terminal;
    // The rebased exponents (sched.rs): the terminal-aware rows read the true
    // values e_A = 0 (a_nonzero, the role clear at m' = 1) and e_B = 1 (D0),
    // so their value base must be 0 (w_a <= 127; the thin schedule reaches it
    // at row 280, FROM is 340).
    assert!(no_terminal || sched.base_v() == 0, "packed step {i}: terminal-aware row with value exponent base {} (w_a = {})", sched.base_v(), sched.w_a);
    assert_eq!(p.ex1.len(), 2 * super::sched::EXP_BITS, "packed step {i}: ex1 width");
    let pop = popcount_on(&p.counter);
    let off = p.off.as_ref().expect("packed offset / carry wire is live");
    let region_start = c.b.phase_active_regions.len();
    if !inverse {
        let active_counter: &[QReg] = if no_terminal { &[] } else { &p.counter };
        let active = compute_active(c, active_counter);
        let role = c.alloc_qreg("cross.role");
        role_compute(c, p, &active, &role, &sched);
        if no_terminal && pop {
            prefix_popcount::update(c, &p.counter, &role, &active, false);
        }
        let mul_control = HybridGateControl::new(&active, &role);
        mul_control.with(c, |c, g| {
            multiply_forward(c, &p.r1, &p.r2, &p.ex1, &p.ex2, &p.q, &p.s_rot, off, g, i, &sched);
        });
        mul_control.release(c);
        c.cx(&active, &role); // X(role) on active rows; a frozen row keeps role = 0
        let div_control = HybridGateControl::new(&active, &role);
        let term = terminal_row.then(|| c.alloc_qreg("pk.term"));
        div_control.with(c, |c, g| {
            division_forward(c, &p.r1, &p.r2, &p.ex1, &p.ex2, &p.q, &p.s_rot, off, g, term.as_ref(), i, &sched);
        });
        div_control.release(c);
        if let Some(t) = term {
            c.zero_and_free(t);
        }
        role_clear(c, p, &active, &role, &sched, terminal_row);
        c.zero_and_free(role);
        swap_and_done_forward(c, p, active, no_terminal);
    } else {
        let active = undo_done_and_swap(c, p, no_terminal);
        let role = c.alloc_qreg("cross.role");
        role_clear(c, p, &active, &role, &sched, terminal_row);
        let div_control = HybridGateControl::new(&active, &role);
        let term = terminal_row.then(|| c.alloc_qreg("pk.term"));
        div_control.with(c, |c, g| {
            division_backward(c, &p.r1, &p.r2, &p.ex1, &p.ex2, &p.q, &p.s_rot, off, g, term.as_ref(), i, &sched);
        });
        div_control.release(c);
        if let Some(t) = term {
            c.zero_and_free(t);
        }
        c.cx(&active, &role); // X(role) on active rows; a frozen row keeps role = 0
        let mul_control = HybridGateControl::new(&active, &role);
        mul_control.with(c, |c, g| {
            multiply_backward(c, &p.r1, &p.r2, &p.ex1, &p.ex2, &p.q, &p.s_rot, off, g, i, &sched);
        });
        mul_control.release(c);
        if no_terminal && pop {
            prefix_popcount::update(c, &p.counter, &role, &active, true);
        }
        role_compute(c, p, &active, &role, &sched);
        c.zero_and_free(role);
        let active_counter: &[QReg] = if no_terminal { &[] } else { &p.counter };
        uncompute_active(c, active_counter, &active);
        c.zero_and_free(active);
    }
    env.restore();
    census(c, region_start)
}

/// Classify the step's section regions (module doc).
fn census(c: &mut Circuit, region_start: usize) -> StepMoments {
    let mut m = StepMoments::default();
    if std::env::var_os("TRACE_PHASE_ACTIVE").is_none() {
        return m;
    }
    // every inner section of the step has been popped, so its region is closed
    m.traced = true;
    for (_, phase, max) in &c.b.phase_active_regions[region_start..] {
        let parts: Vec<&str> = phase.split('/').collect();
        if let Some(k) = parts.iter().find(|s| ["p.cmp.chunk", "p.ctz.direct", "chunked.predicate"].contains(s)) {
            if *max > m.planner {
                m.planner = *max;
                m.planner_kind = match *k {
                    "p.cmp.chunk" => "cmp.chunk",
                    "p.ctz.direct" => "ctz",
                    _ => "predicate",
                };
            }
            continue;
        }
        let sub = parts.iter().rposition(|s| s.starts_with("pk.")).map(|k| parts[k]);
        let item: Option<&'static str> = parts.iter().find_map(|s| {
            [
                "D0", "D1", "D3", "D4", "D5", "D6", "D7", "D7b", "D8", "D6p", "D9", "D10", "D11", "D0c", "D12", "M1",
                "M2", "M3", "M4", "M5", "M6", "M8", "M9", "M10", "M11", "M12",
            ]
            .into_iter()
            .find(|k| k == s)
        });
        match (sub, item) {
            (_, Some("D7")) | (_, Some("M5")) => {
                if *max > m.adder {
                    m.adder = *max;
                    m.adder_kind = item.unwrap();
                }
            }
            (_, Some(k)) => {
                if *max > m.scan {
                    m.scan = *max;
                    m.scan_kind = k;
                }
            }
            (Some(s), None) if s.starts_with("pk.role") => m.role = m.role.max(*max),
            (Some("pk.swap"), None) => m.swap = m.swap.max(*max),
            (Some("pk.div") | Some("pk.div.inv") | Some("pk.mul") | Some("pk.mul.inv"), None) => {
                if *max > m.scan {
                    m.scan = *max;
                    m.scan_kind = "gate";
                }
            }
            _ => {
                if *max > m.other {
                    m.other = *max;
                    m.other_kind = if phase.contains("p.orz") || phase.contains("chunked") { "active" } else { "step" };
                }
            }
        }
    }
    m
}

/// Selftest entry (`MIDQ_PACKED_SELFTEST=1`): the full forward prefix and the
/// full cancel on the Simulator (`driver_selftest.rs`).
#[allow(dead_code)]
pub(crate) fn selftest() {
    driver_selftest::run();
}
