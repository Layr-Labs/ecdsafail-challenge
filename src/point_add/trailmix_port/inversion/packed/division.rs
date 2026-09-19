//! Packed DIVISION substep, D0..D12 (`tools/spike/packed_design.md` section 3.1
//! with the 2026-09-13 refuter fixes: the order is D1, D0, D3, D4, D5, D6, D7,
//! D7b, D8, D6', D9, D11 (D11t inside), D10, D0-clear, D12), composed from the
//! six reviewed packed primitives. Nothing here re-implements a primitive; the
//! only local kernel is the D11t constant for windows narrower than 32 (D12 is
//! the shared `packed::ctz` kernel, the same one M2 uses).
//!
//! # State and frames
//!
//! `r1 = [A | gap | cb]`, `r2 = [B | gap | ca]`: two 257-wire rings, values
//! LSB-anchored at wire 0 growing up, coefficients LSB-anchored at wire 256
//! growing down. `ex1 = [e_A | e_cb]`, `ex2 = [e_B | e_ca]` (9-bit bit-lengths,
//! LSB first). `q` at its per-step envelope width, `s_rot` (5 bits), `off`,
//! `gate_div` = the held hybrid gate `active AND NOT role` (materialised by the
//! caller, released by the caller), `term` = the terminal predicate wire on the
//! terminal-aware rows (`Some` from `MIDQ_PREFIX_TERMINAL_FROM`; `None` before).
//! On entry (forward): `s_rot = 0`, `off = 0`, `term = 0`, R1 in the LSB frame.
//! On exit: `A := A - (B << s)` on a division row (`gate_div = 1`), `q ^= 1 << s`,
//! `e_A := bl(A_new)` (0 on the terminal row), `s_rot = 0`, `off = 0`,
//! `term = 0`; `r2`, `e_B`, `e_ca`, `e_cb`, every bit of `r1` above `A_old`
//! and every other bit of `q` untouched. On a `gate_div = 0` row nothing
//! changes (every item is gated at its top end or is a permutation undone by
//! its twin).
//!
//! # Items (forward; the inverse runs the mirrored sequence, each item's twin)
//!
//! | item | primitive | notes |
//! |---|---|---|
//! | D1 | `exponent_arith::xor_diff_low(gate, e_A, e_B, s_rot)` | `s_rot = gate * (e_A - e_B)[0..5] = s_raw` |
//! | D0 | `exponent_arith::term_toggle(gate, e_B, s_rot, R1[0..n0), term)` | rows with `term`; `n0 = min(28, W_A)`; after D1 (shift = s_raw, LSB frame) |
//! | D3 | `ring_rotate(R1[0..W_A), s_rot[..rb], down)` | `A >> s_raw` on `[0, e_B)`, A's low bits wrap to the ring top |
//! | D4 | `capture_compare(gate, R1, R2 cells [cascade_lo, W_A), addr e_B, out off)` | `off ^= [A>>s_raw < B]`, tie residue below `cascade_lo = max(0, lo_B - 32)` |
//! | D5 | `ring_rotate(R1[0..W_A), off, up)` | now `A >> s` on `[0, E)`, `E = e_B + off` |
//! | D6 | `exponent_arith::offset_apply(off, s_rot, e_B)` | `s_rot = s`, `e_B = E` |
//! | D7 | `masked_add_refs(gate, R1[0..W_A) -= R2[0..W_A), zone, Exponent(e_B), subtract)` | field `[0, E)`; zone = [`zone_start`, W_A) |
//! | D7b | `exponent_arith::off_update(gate, off, e_A)` | `e_A -= gate AND off` |
//! | D8 | `set_bit_at_s_gated(q, s_rot, gate)` | `q ^= gate << s` (measured demux) |
//! | D6' | `exponent_arith::offset_release(off, e_B)` | `e_B = e_B` again, before D9 clears `off` |
//! | D9 | X-bracket R2 cells; `capture_compare(gate, R2, R1, addr e_B, out off)` | `off ^= [~B < R]` clears `off` |
//! | D11 | `aligned_scan_top(R1, e_B, e_A, gate, W_A, lo_B, hook)` | `e_A += gate*(k - (n_w-1))`; hook = D11t |
//! | D11t | `e_A -= term*pos; e_A -= term*s_rot; e_A += term*(n_w - 2)` | inside D11 while `pos` is live (`+30` for the 32-window) |
//! | D10 | `ring_rotate(R1[0..W_A), s_rot[..rb], up)` | LSB frame restored |
//! | D0-clear | the same `term_toggle` | shift = s (= s_raw on B = 1 rows) |
//! | D12 | `ctz::ctz_xor(q, s_rot, gate, scratch_room)` | `s_rot ^= gate * ctz(q) = 0` (the packed direct-ctz kernel, shared with M2) |
//!
//! # Schedule (`sched::StepWidths`, the ONE geometry source)
//!
//! Read from the schedule the way `p0_shape.rs` / `driver.rs` do
//! (`sched::StepWidths::from_schedule`: `reg_widths`, `shift_bounds`, every
//! `lo` from `thin_lo`): `W_A = max(env A, env B)`, `W_c = max(env ca, env cb)`
//! (record_sample folds the post-multiply `ca` into `env ca`), `lo_B =
//! thin_lo(env B)` (so `e_B >= lo_B + 1` on the support), `rb = bitlen(shift
//! bound)`. The division's own windows are methods there (review 2026-09-14,
//! findings 1 and 3 - the second `lo_b` source and the second ctz kernel this
//! file used to carry are gone):
//!
//! * D4/D9 cascade over the cells `[div_cascade_lo, W_A)` with
//!   `div_cascade_lo = max(0, lo_B - 32)` (the design's `lo_A = lo_B` made the
//!   window-tie residue `2^-(e_B - lo_B - 1)` the dominant miss kind; it is now
//!   `<= 2^-32`, and 0 once `lo_B <= 32`), capture leaves `e_B` in
//!   `div_capture_window` (`[lo_B + 1, W_A]` while `lo_B > 32`, `[1, W_A]` after);
//! * D7 zone `[div_zone_start, W_A)` with `div_zone_start = min(257 - W_c,
//!   lo_B + 1)` (empty when `257 - W_c >= W_A`): the masked adder's thermometer
//!   starts at 1, so `zone.start <= E` is a precondition on every active row
//!   (masked_add.rs, Support) - at early steps `257 - W_c` exceeds `lo_B + 1`
//!   and rows with `E < 257 - W_c` would add ca's bits into R1 (the `lo_B + 1`
//!   clip), at late steps (`W_c = 256`) the zone starts at wire 1 and D7 is
//!   exact for every `e_B >= 1` (the design's `max(lo_A, 257 - W_c)` clamp
//!   made every B = 1 row with `e_B <= lo_B` and a wide ca a certain failure).
//!   Cost: `+8 T` per zone cell above the design's edge (static schedule: 89
//!   cells at step 10, 27 at 100, 0 from ~190; `+136` T at 350, 0 from ~395).
//! * D11 ring `[max(0, lo_B - 32), W_A)`, window `n_w = div_scan_window`;
//!   D0 window `n0 = div_term_window = min(28, W_A)`.
//!
//! Support of the division on an active row (what the harnesses check; every
//! violation is a priced miss kind, never a crash): `e_A, e_B <= W_A`;
//! `s_raw < 2^rb`; `bl(q) <= w_q` (`w_q <= 31`: D8's demux and D12's gray
//! deposit reach 32 q bits, and the driver asserts the envelope); `e_B` in the
//! capture window (`lo_B` kind; none once `lo_B <= 32`); `E = e_B + off >=
//! div_zone_start` (the D7 zone kind; `E >= 1` on the late rows); `d <= n_w -
//! 1 + off` (`drop_bound`); a terminal division only on a `term` row
//! (`term_row`) with `s <= n0` (`term_window`); no tie of the D4 / D9 windows
//! below the cascade bottom (`residue`, `<= 2^-32` per row).
//!
//! # D10 merged with D11's rotate-back
//!
//! On late rows with L=0 and rb=5 both rotations use the same ring. A single
//! rotation by t7-s replaces their composition; its offset arithmetic borrows
//! the zero off wire. MIDQ_PACKED_FUSED_RETURN=0 retains the reference pair.
//!
//! Environment: `MIDQ_MEASURED_DEMUX=1` for the 1-T-per-leaf D8 (else the
//! `unary_iterate_log_star` fallback at ~6 T per leaf), `MIDQ_KG_ZERO_LAYER=1`
//! and `MIDQ_CHUNKED_PREFIX != 1` as `aligned_scan_top` requires, and
//! `MIDQ_PACKED_QCAP` / `MIDQ_PACKED_CTZ_ROOM` bound D12's clean-prefix chunks
//! (`sched::scratch_room`, the same budget as M2).
//!
//! Selftest: `division_selftest.rs` (`MIDQ_PACKED_SELFTEST=1`).

use super::super::set_bit_at_s_gated;
use super::aligned_scan::aligned_scan_top;
use super::capture_compare::capture_compare;
use super::ctz::ctz_xor;
use super::sched::{scratch_room, StepWidths, EXP_BITS, RING};
use super::exponent_arith::{
    ctrl_add_const, ctrl_sub_reg, ctrl_add_reg, off_update, off_update_inverse, offset_apply,
    offset_apply_inverse, offset_release, offset_release_inverse, term_toggle_with_workspace, xor_diff_low,
};
use super::masked_add::{masked_add_refs, Captures, ZoneMask};
use super::ring_rotate::ring_rotate;
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

#[path = "division_selftest.rs"]
mod division_selftest;

/// D11t for a window of `n_w` cells: `e_A -= term*pos; e_A -= term*shift;
/// e_A += term*(n_w - 2)` (the design's `+30` is the 32-window case: D11 added
/// `k - (n_w - 1)` with garbage `k` on the terminal row where
/// `e_A = 1 + s` after D7b, so `1 + s + k - (n_w-1) - k - s + (n_w - 2) = 0`).
fn terminal_override_nw(c: &mut Circuit, term: &QReg, e_a: &[QReg], pos: &[&QReg], shift: &[QReg], n_w: usize) {
    let prev = c.push_section("p.exp.term_override");
    let ea: Vec<&QReg> = e_a.iter().collect();
    super::aligned_scan::ctrl_sub_narrow(c, term, &ea, pos, false);
    ctrl_sub_reg(c, term, e_a, shift);
    ctrl_add_const(c, term, e_a, n_w as i64 - 2);
    c.pop_section(&prev);
}

/// Inverse of [`terminal_override_nw`].
fn terminal_override_nw_inverse(c: &mut Circuit, term: &QReg, e_a: &[QReg], pos: &[&QReg], shift: &[QReg], n_w: usize) {
    let prev = c.push_section("p.exp.term_override_inv");
    ctrl_add_const(c, term, e_a, -(n_w as i64 - 2));
    ctrl_add_reg(c, term, e_a, shift);
    let ea: Vec<&QReg> = e_a.iter().collect();
    super::aligned_scan::ctrl_add_narrow(c, term, &ea, pos, false);
    c.pop_section(&prev);
}

/// The packed division substep, forward (module doc). `r1`, `r2`: the 257-wire
/// rings; `ex1 = [e_A | e_cb]`, `ex2 = [e_B | e_ca]`; `q`: the quotient at its
/// step envelope; `s_rot`: 5 bits, |0> on entry; `off`: |0> on entry;
/// `gate_div`: the held division gate; `term`: the terminal predicate wire
/// (|0> on entry) on terminal-aware rows, `None` before; `sched.step == step`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn division_forward(
    c: &mut Circuit,
    r1: &[QReg],
    r2: &[QReg],
    ex1: &[QReg],
    ex2: &[QReg],
    q: &[QReg],
    s_rot: &[QReg],
    off: &QReg,
    gate_div: &QReg,
    term: Option<&QReg>,
    step: usize,
    sched: &StepWidths,
) {
    division_step(c, r1, r2, ex1, ex2, q, s_rot, off, gate_div, term, step, sched, false);
}

/// The exact inverse of [`division_forward`] (the backward driver's division):
/// the mirrored sequence with every item's twin. PRE: the forward's POST state
/// (`s_rot = 0`, `off = 0`, `term = 0`, LSB frame).
#[allow(clippy::too_many_arguments)]
pub(crate) fn division_backward(
    c: &mut Circuit,
    r1: &[QReg],
    r2: &[QReg],
    ex1: &[QReg],
    ex2: &[QReg],
    q: &[QReg],
    s_rot: &[QReg],
    off: &QReg,
    gate_div: &QReg,
    term: Option<&QReg>,
    step: usize,
    sched: &StepWidths,
) {
    division_step(c, r1, r2, ex1, ex2, q, s_rot, off, gate_div, term, step, sched, true);
}

#[allow(clippy::too_many_arguments)]
fn division_step(
    c: &mut Circuit,
    r1: &[QReg],
    r2: &[QReg],
    ex1: &[QReg],
    ex2: &[QReg],
    q: &[QReg],
    s_rot: &[QReg],
    off: &QReg,
    gate: &QReg,
    term: Option<&QReg>,
    step: usize,
    sched: &StepWidths,
    inverse: bool,
) {
    assert_eq!(r1.len(), RING, "division: R1 must be the 257-wire ring");
    assert_eq!(r2.len(), RING, "division: R2 must be the 257-wire ring");
    assert_eq!(ex1.len(), 2 * EXP_BITS, "division: ex1 = [e_A | e_cb]");
    assert_eq!(ex2.len(), 2 * EXP_BITS, "division: ex2 = [e_B | e_ca]");
    assert_eq!(sched.step, step, "division: schedule row mismatch");
    assert!(!s_rot.is_empty() && s_rot.len() <= EXP_BITS, "division: s_rot width {}", s_rot.len());
    // D8's demux and D12's gray deposit reach `2^srot` q bits (32); the
    // support's real bound is the q envelope `w_q <= 31` (sched.rs, "q
    // envelope"), asserted per step by the driver.
    assert!(
        q.len() <= 1usize << s_rot.len(),
        "division: q width {} exceeds the {}-bit shift's reach (D8 demux / D12 gray deposit)",
        q.len(),
        s_rot.len()
    );
    let e_a = &ex1[..EXP_BITS];
    let e_b = &ex2[..EXP_BITS];
    let w_a = sched.w_a;
    // The rebased frame (sched.rs): e_A, e_B hold `e - base_v`. The terminal
    // predicate `[e_B == 1]` and the override to `e_A = 0` read the true
    // values, so the terminal-aware rows need base_v = 0 (w_a <= 127).
    let base_v = sched.base_v();
    assert!(term.is_none() || base_v == 0, "division step {step}: terminal-aware row with exponent base {base_v} (w_a = {w_a} > 127)");
    let rb = sched.rb_div.min(s_rot.len());
    let fuse_return = sched.lo_b <= super::aligned_scan::WINDOW && rb == 5
        && std::env::var("MIDQ_PACKED_FUSED_RETURN").ok().as_deref() != Some("0");
    let ring = &r1[..w_a];
    let n0 = sched.div_term_window();
    let zone = sched.div_zone_start()..w_a;
    let window = sched.div_capture_window();
    let lo_a = sched.div_cascade_lo();
    let prev = c.push_section(if inverse { "pk.div.inv" } else { "pk.div" });

    // ---- items as closures so the two directions share one definition ----
    let d1 = |c: &mut Circuit| xor_diff_low(c, gate, e_a, e_b, s_rot);
    let d0 = |c: &mut Circuit| {
        if let Some(t) = term {
            term_toggle_with_workspace(c, gate, e_b, s_rot, &r1[..n0], t, Some(off));
        }
    };
    let d3 = |c: &mut Circuit, inv: bool| ring_rotate(c, ring, &s_rot[..rb], !inv); // down (fwd)
    let d4 = |c: &mut Circuit| {
        let v: Vec<&QReg> = r1[lo_a..w_a].iter().collect();
        let u: Vec<&QReg> = r2[lo_a..w_a].iter().collect();
        capture_compare(c, gate, &v, &u, e_b, window, off);
    };
    let d5 = |c: &mut Circuit, inv: bool| ring_rotate(c, ring, std::slice::from_ref(off), inv); // up (fwd)
    let d7 = |c: &mut Circuit, inv: bool| {
        let target: Vec<&QReg> = r1[..w_a].iter().collect();
        let addend: Vec<&QReg> = r2[..w_a].iter().collect();
        masked_add_refs(c, gate, &target, &addend, zone.clone(), ZoneMask::Rebased(e_b, base_v), !inv, Captures::default());
    };
    let d8 = |c: &mut Circuit| set_bit_at_s_gated(c, q, s_rot, gate);
    let d9 = |c: &mut Circuit| {
        let v: Vec<&QReg> = r2[lo_a..w_a].iter().collect();
        let u: Vec<&QReg> = r1[lo_a..w_a].iter().collect();
        for x in &v {
            c.x(x); // ~B
        }
        capture_compare(c, gate, &v, &u, e_b, window, off);
        for x in &v {
            c.x(x);
        }
    };
    let d10 = |c: &mut Circuit, inv: bool| ring_rotate(c, ring, &s_rot[..rb], inv); // up (fwd)
    let d11 = |c: &mut Circuit, inv: bool| {
        // D9 has cleared off; the inverse also enters D11 with off = 0.
        // term implies gate. For exact division e_A=s+1, so skip the normal
        // drop update and XOR that value instead of cancelling a sentinel.
        if let Some(t) = term { c.cx(t, gate); }
        aligned_scan_top(c, r1, e_b, e_a, gate, w_a, sched.lo_b, base_v, inv, Some(off),
            fuse_return.then_some(&s_rot[..rb]), true, |c, _pos| {
            if let Some(t) = term {
                // The terminal predicate visits only s<=28; s+1 fits five bits.
                super::exponent_arith::add_const(c, s_rot, 1);
                for (src, dst) in s_rot.iter().zip(e_a) { c.ccx(t, src, dst); }
                super::exponent_arith::add_const(c, s_rot, -1);
            }
        });
        if let Some(t) = term { c.cx(t, gate); }
    };
    let d12 = |c: &mut Circuit| {
        let room = scratch_room(c);
        ctz_xor(c, q, s_rot, gate, room);
    };

    // Every item under its own section (`pk.div/<item>/...`) so a phase trace
    // attributes T per design row.
    fn item(c: &mut Circuit, name: &str, body: impl FnOnce(&mut Circuit)) {
        let prev = c.push_section(name);
        body(c);
        c.pop_section(&prev);
    }
    if !inverse {
        item(c, "D1", |c| d1(c));
        item(c, "D0", |c| d0(c));
        item(c, "D3", |c| d3(c, false));
        item(c, "D4", |c| d4(c));
        item(c, "D5", |c| d5(c, false));
        item(c, "D6", |c| offset_apply(c, off, s_rot, e_b));
        item(c, "D7", |c| d7(c, false));
        item(c, "D7b", |c| off_update(c, gate, off, e_a));
        item(c, "D8", |c| d8(c));
        item(c, "D6p", |c| offset_release(c, off, e_b));
        item(c, "D9", |c| d9(c));
        item(c, "D11", |c| d11(c, false));
        if !fuse_return { item(c, "D10", |c| d10(c, false)); }
        item(c, "D0c", |c| d0(c));
        item(c, "D12", |c| d12(c));
    } else {
        item(c, "D12", |c| d12(c));
        item(c, "D0c", |c| d0(c));
        if !fuse_return { item(c, "D10", |c| d10(c, true)); }
        item(c, "D11", |c| d11(c, true));
        item(c, "D9", |c| d9(c));
        item(c, "D6p", |c| offset_release_inverse(c, off, e_b));
        item(c, "D8", |c| d8(c));
        item(c, "D7b", |c| off_update_inverse(c, gate, off, e_a));
        item(c, "D7", |c| d7(c, true));
        item(c, "D6", |c| offset_apply_inverse(c, off, s_rot, e_b));
        item(c, "D5", |c| d5(c, true));
        item(c, "D4", |c| d4(c));
        item(c, "D3", |c| d3(c, true));
        item(c, "D0", |c| d0(c));
        item(c, "D1", |c| d1(c));
    }
    c.pop_section(&prev);
}

/// Selftest entry called by `packed::selftest_all` (`MIDQ_PACKED_SELFTEST=1`).
#[allow(dead_code)]
pub(crate) fn selftest() {
    division_selftest::run();
}
