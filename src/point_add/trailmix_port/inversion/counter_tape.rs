//! Exact branch-disjoint counter/tape storage. See counter_tape_proof.md.

use super::{Circuit, QReg};
use crate::point_add::trailmix_port::arith::mcx::mcx_clean_k;
use crate::point_add::trailmix_port::inversion::shrunken_pz_primitives::{ctrl_add, ctrl_sub};

pub(super) const BITS: usize = 8;

pub(super) fn enabled() -> bool {
    std::env::var("MIDQ_COUNTER_TAPE").ok().as_deref() == Some("1")
}

fn xor_terminal(c: &mut Circuit, a: &[QReg], q: &[QReg], out: &QReg) {
    // A=0 alone is insufficient while a pending quotient is being drained.
    let controls: Vec<_> = a.iter().chain(q).collect();
    for bit in &controls {
        c.x(bit);
    }
    mcx_clean_k(c, &controls, out);
    for bit in &controls {
        c.x(bit);
    }
}

pub(super) fn prepare(c: &mut Circuit, a: &[QReg], ca: &[QReg], cb: &[QReg], q: &[QReg]) -> QReg {
    let terminal = c.alloc_qreg("midq.counter_tape.terminal");
    xor_terminal(c, a, q, &terminal);
    ctrl_sub(
        c,
        &terminal,
        &ca.iter().collect::<Vec<_>>(),
        &cb.iter().collect::<Vec<_>>(),
    );
    c.cx(&terminal, &a[0]);
    terminal
}

pub(super) fn restore(
    c: &mut Circuit,
    a: &[QReg],
    ca: &[QReg],
    cb: &[QReg],
    q: &[QReg],
    terminal: QReg,
) {
    c.cx(&terminal, &a[0]);
    ctrl_add(
        c,
        &terminal,
        &ca.iter().collect::<Vec<_>>(),
        &cb.iter().collect::<Vec<_>>(),
    );
    xor_terminal(c, a, q, &terminal);
    c.zero_and_free(terminal);
}

pub(super) fn xor_decoded(c: &mut Circuit, terminal: &QReg, encoded: &QReg, out: &QReg) {
    c.x(terminal);
    c.ccx(terminal, encoded, out);
    c.x(terminal);
}

#[path = "counter_tape_selftest.rs"]
mod tests;
pub(crate) use tests::run as selftest;
