//! Exact 14-to-12-bit codec for metadata unused after tail round seven.
//! qtag=0..18, ctz=0..85, selector=0/1; terminal implies (18,0,0).

use super::{Circuit, QReg};
use crate::circuit::QubitId;
use crate::point_add::trailmix_port::arith::{
    compare::compare_geq_const,
    const_add::{controlled_add_const, controlled_sub_const},
    khattar_gidney::xor_and_of_khattar_gidney,
};

pub(super) struct Raw {
    pub qtag: Vec<QReg>,
    pub ctz: Vec<QReg>,
    pub selector: QReg,
    pub terminal: QReg,
}

pub(super) struct Packed {
    pub bits: Vec<QReg>,
}

pub(super) fn enabled() -> bool {
    std::env::var("MIDQ_TAIL_METADATA_CODEC").ok().as_deref() == Some("1")
}

fn xor_terminal(c: &mut Circuit, z: &[QReg], flag: &QReg) {
    for (i, bit) in z.iter().enumerate() {
        if 3268usize >> i & 1 == 0 { c.x(bit); }
    }
    xor_and_of_khattar_gidney(c, z, flag);
    for (i, bit) in z.iter().enumerate() {
        if 3268usize >> i & 1 == 0 { c.x(bit); }
    }
}

// XOR divmod(z,19) into arbitrary destination bits, then undo all division
// scratch. The terminal correction runs after that scratch has been released.
fn xor_decode(c: &mut Circuit, z: &[QReg], out: &Raw) {
    let remainder = c.alloc_qreg_bits("midq.metadata.remainder", 12);
    let quotient = c.alloc_qreg_bits("midq.metadata.quotient", 8);
    for (src, dst) in z.iter().zip(&remainder) { c.cx(src, dst); }
    for i in (0..8).rev() {
        let divisor = (19u16 << i).to_le_bytes();
        compare_geq_const(c, &remainder, &divisor, &quotient[i]);
        controlled_sub_const(c, &quotient[i], &remainder, &divisor);
    }
    for (src, dst) in remainder.iter().zip(&out.qtag) { c.cx(src, dst); }
    c.cx(&quotient[0], &out.selector);
    for (src, dst) in quotient[1..].iter().zip(&out.ctz) { c.cx(src, dst); }
    for i in 0..8 {
        let divisor = (19u16 << i).to_le_bytes();
        controlled_add_const(c, &quotient[i], &remainder, &divisor);
        compare_geq_const(c, &remainder, &divisor, &quotient[i]);
    }
    for (src, dst) in z.iter().zip(&remainder) { c.cx(src, dst); }
    for bit in quotient.into_iter().chain(remainder) { c.zero_and_free(bit); }

    let terminal = c.alloc_qreg("midq.metadata.is_terminal");
    xor_terminal(c, z, &terminal);
    c.cx(&terminal, &out.terminal);
    for (i, bit) in out.qtag.iter().enumerate() {
        if 18usize >> i & 1 != 0 { c.cx(&terminal, bit); }
    }
    for (i, bit) in out.ctz.iter().enumerate() {
        if 86usize >> i & 1 != 0 { c.cx(&terminal, bit); }
    }
    xor_terminal(c, z, &terminal);
    c.zero_and_free(terminal);
}

fn rank(c: &mut Circuit, raw: &Raw, z: &[QReg], inverse: bool) {
    if !inverse {
        for (src, dst) in raw.qtag.iter().zip(z) { c.cx(src, dst); }
    }
    let update = if inverse { controlled_sub_const } else { controlled_add_const };
    update(c, &raw.selector, z, &19u16.to_le_bytes());
    for (i, bit) in raw.ctz.iter().enumerate() {
        update(c, bit, z, &(38u16 << i).to_le_bytes());
    }
    update(c, &raw.terminal, z, &3250u16.to_le_bytes());
    if inverse {
        for (src, dst) in raw.qtag.iter().zip(z) { c.cx(src, dst); }
    }
}

pub(super) fn pack(c: &mut Circuit, raw: Raw) -> Packed {
    assert_eq!(raw.qtag.len(), 5);
    assert_eq!(raw.ctz.len(), 7);
    let prev = c.push_section("midq.metadata.pack");
    let z = c.alloc_qreg_bits("midq.metadata.rank", 12);
    rank(c, &raw, &z, false);
    xor_decode(c, &z, &raw);
    let mut bits = raw.qtag;
    bits.extend(raw.ctz);
    for (old, encoded) in bits.iter().zip(&z) {
        c.b.swap(QubitId(old.id().into()), QubitId(encoded.id().into()));
    }
    for bit in z { c.zero_and_free(bit); }
    c.zero_and_free(raw.selector);
    c.zero_and_free(raw.terminal);
    c.pop_section(&prev);
    Packed { bits }
}

pub(super) fn unpack(c: &mut Circuit, packed: Packed) -> Raw {
    assert_eq!(packed.bits.len(), 12);
    let prev = c.push_section("midq.metadata.unpack");
    let raw = Raw {
        qtag: c.alloc_qreg_bits("midq.metadata.decoded_qtag", 5),
        ctz: c.alloc_qreg_bits("midq.metadata.decoded_ctz", 7),
        selector: c.alloc_qreg("midq.ctz.select_a"),
        terminal: c.alloc_qreg("midq.counter_tape.terminal"),
    };
    xor_decode(c, &packed.bits, &raw);
    rank(c, &raw, &packed.bits, true);
    for (old, decoded) in packed.bits.iter().zip(raw.qtag.iter().chain(&raw.ctz)) {
        c.b.swap(QubitId(old.id().into()), QubitId(decoded.id().into()));
    }
    for bit in raw.qtag.into_iter().chain(raw.ctz) { c.zero_and_free(bit); }
    let mut qtag = packed.bits;
    let ctz = qtag.split_off(5);
    c.pop_section(&prev);
    Raw { qtag, ctz, selector: raw.selector, terminal: raw.terminal }
}

#[path = "tail_metadata_codec_selftest.rs"]
mod selftest;
pub(crate) use selftest::run;
