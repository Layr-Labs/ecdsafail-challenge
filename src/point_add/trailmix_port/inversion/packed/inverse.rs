//! The two substep inverses under the names of the plan (design 3.4, P4):
//! `division_cancel` = `division::division_backward` (D12, D0-clear, D10,
//! D11 (D11t inside), D9, D6', D8, D7b, D7, D6, D5, D4, D3, D0, D1 with each
//! item's twin) and `multiply_cancel` = `multiply::multiply_backward` (M12,
//! M11, M10, M9, M8, M6', M5, M4, M3, M2, M1). Both are exact gate-for-gate
//! mirrors of their forward substep: every self-inverse item (XOR deposits,
//! the capture compares, the one-hot writes, the direct ctz, `term_toggle`)
//! is re-emitted unchanged, every rotation is emitted in the opposite
//! direction, every exponent update by its twin (`ctrl_inc`/`ctrl_dec`,
//! `deposit_sum`/`undeposit_sum`, `offset_apply`/`offset_apply_inverse`, ...)
//! and the masked adders by the X-bracket twin with the same captures.
//! PRE of each: the forward's POST state (`s_rot = 0`, `off = 0`, `term = 0`,
//! LSB frame); POST: the forward's PRE state. Verified row by row by
//! `division_selftest.rs` (34,941 inverses), `multiply_review.rs` (forward,
//! backward and round trip on every multiply row of 256 inputs x 530 steps,
//! both schedules; `multiply_selftest.rs` builds the forward only), and end to end by
//! `driver_selftest.rs` (530 steps forward, 530 steps back, S_0 restored).

#![allow(dead_code)]

use super::division::division_backward;
use super::multiply::multiply_backward;
use super::sched::StepWidths;
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

/// The exact inverse of `division::division_forward` (same signature).
#[allow(clippy::too_many_arguments)]
pub(crate) fn division_cancel(
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
    division_backward(c, r1, r2, ex1, ex2, q, s_rot, off, gate_div, term, step, sched);
}

/// The exact inverse of `multiply::multiply_forward` (same signature).
#[allow(clippy::too_many_arguments)]
pub(crate) fn multiply_cancel(
    c: &mut Circuit,
    r1: &[QReg],
    r2: &[QReg],
    ex1: &[QReg],
    ex2: &[QReg],
    q: &[QReg],
    s_rot: &[QReg],
    off: &QReg,
    gate_mul: &QReg,
    step: usize,
    sched: &StepWidths,
) {
    multiply_backward(c, r1, r2, ex1, ex2, q, s_rot, off, gate_mul, step, sched);
}
