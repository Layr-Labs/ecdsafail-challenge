//! Exact sign representations at the PZ / ping-pong boundary.

use super::{Circuit, QReg};
use crate::point_add::trailmix_port::circuit::BorrowedQReg;

pub(super) fn owned(slot: &mut Option<BorrowedQReg<'_>>) -> QReg {
    match slot.take().expect("live parity wire") {
        BorrowedQReg::Owned(q) => q,
        BorrowedQReg::Borrowed(_) => panic!("cannot release a borrowed parity wire"),
    }
}

pub(super) fn pack_parity(
    c: &mut Circuit,
    cb: &[QReg],
    raw_width: usize,
    parity: &mut Option<BorrowedQReg<'_>>,
) -> bool {
    if std::env::var("MIDQ_PACK_PZ_PARITY").ok().as_deref() != Some("1")
        || raw_width > 248
        || !matches!(parity, Some(BorrowedQReg::Owned(_)))
    {
        return false;
    }
    // Before any modular halving, cb is either raw_cb or p-raw_cb.
    // raw_cb < 2^248 makes bit 255 exactly the complement of parity.
    let q = owned(parity);
    c.x(&q);
    c.cx(&cb[255], &q);
    c.zero_and_free(q);
    true
}

pub(super) fn restore_parity(c: &mut Circuit, cb: &[QReg], parity: &mut Option<BorrowedQReg<'_>>) {
    assert!(parity.is_none(), "packed parity has no live owner");
    let q = c.alloc_qreg("midq.restored.parity");
    c.x(&q);
    c.cx(&cb[255], &q);
    *parity = Some(BorrowedQReg::Owned(q));
}

pub(super) fn negate_odd_rows(c: &mut Circuit, sign: &QReg, a: &[QReg], b: &[QReg]) {
    // For odd z, -z modulo 2^w differs from z in every bit except bit zero.
    for q in a[1..].iter().chain(&b[1..]) {
        c.cx(sign, q);
    }
}

#[path = "sign_storage_selftest.rs"]
mod tests;

pub(crate) fn selftest() {
    tests::run();
}
