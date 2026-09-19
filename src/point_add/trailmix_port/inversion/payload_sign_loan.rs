//! The outer Horner multiplier reads only b[0..256]. Keep its unused high
//! slot occupied by the already-live sign, not a second, known-zero wire.

use super::{Circuit, QReg};

pub(super) fn compact_padding() -> bool {
    std::env::var("MIDQ_PASSENGER_PADDING").ok().as_deref() == Some("1")
        && std::env::var("MIDQ_PAYLOAD_SIGN_LOAN").ok().as_deref() == Some("1")
}

pub(super) fn park_padding(c: &mut Circuit, b: &mut Vec<QReg>) {
    assert_eq!(b.len(), 257);
    c.zero_and_free(b.pop().unwrap());
}

fn toggle_signed_high(c: &mut Circuit, low: &[QReg], sign: &QReg, high: &QReg) {
    use crate::point_add::trailmix_port::arith::compare::compare_geq_const;
    let above = c.alloc_qreg("midq.payload.above_p");
    let threshold = super::p_plus_1_bytes();
    compare_geq_const(c, low, &threshold, &above);
    c.ccx(sign, &above, high);
    compare_geq_const(c, low, &threshold, &above);
    c.zero_and_free(above);
}

// For z = sign ? p-u : u modulo2^257 and any256-bit u, the high bit is
// sign AND (z_low > p). This includes noncanonical u>p, not just field values.
pub(super) fn park_signed_high(c: &mut Circuit, value: &mut Vec<QReg>, sign: &QReg) {
    assert_eq!(value.len(), 257);
    toggle_signed_high(c, &value[..256], sign, &value[256]);
    c.zero_and_free(value.pop().unwrap());
}

pub(super) fn restore_signed_high(c: &mut Circuit, value: &mut Vec<QReg>, sign: &QReg) {
    assert_eq!(value.len(), 256);
    let high = c.alloc_qreg("midq.payload.restored_high");
    toggle_signed_high(c, value, sign, &high);
    value.push(high);
}

pub(super) fn begin(c: &mut Circuit, b: &mut Vec<QReg>, sign: &mut Option<QReg>) -> bool {
    if std::env::var("MIDQ_PAYLOAD_SIGN_LOAN").ok().as_deref() != Some("1") {
        return false;
    }
    if b.len() == 256 {
        assert!(compact_padding(), "padding must have been parked explicitly");
    } else {
        assert_eq!(b.len(), 257, "only the outer 257-bit multiplier interface");
        park_padding(c, b);
    }
    b.push(
        sign.take()
            .expect("transfer the owned sign into the unused slot"),
    );
    true
}

pub(super) fn control<'a>(b: &'a [QReg], sign: &'a Option<QReg>) -> &'a QReg {
    sign.as_ref().unwrap_or_else(|| {
        assert_eq!(b.len(), 257);
        &b[256]
    })
}

pub(super) fn finish(b: &mut Vec<QReg>, sign: &mut Option<QReg>, loaned: bool) {
    if loaned {
        assert!(
            sign.is_none(),
            "the multiplier vector is the sign's sole owner"
        );
        assert_eq!(b.len(), 257);
        *sign = Some(b.pop().expect("restore the original owned sign"));
    }
}

#[path = "payload_sign_loan_selftest.rs"]
mod tests;

pub(crate) fn selftest() {
    tests::run();
}
