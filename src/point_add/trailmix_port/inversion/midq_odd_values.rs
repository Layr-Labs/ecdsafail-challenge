//! Default-off odd VALUE representation for the mid-Q ping-pong tail.
//!
//! # Exact map and domain
//!
//! A logical signed W-bit odd value x is represented by its W-1 upper bits
//! X, so x = 2X+1 as a bit pattern. All widths here are LOGICAL full widths.
//! For source x and target y, let s = X[0] xor Y[0]. The original circuit
//! computes wrap_W(y + (-1)^s x), drops its zero low bit, then signed-resizes.
//! Its W-1-bit intermediate is exactly
//!
//!     Z = Y + X + 1 (s=0), or Y - X (s=1), modulo 2^(W-1).
//!
//! Equivalently Z = Y - D, where D = ~X for s=0 and X for s=1. One ordinary
//! W-1-bit adder implements this as ~(~Y + D). No carry-in wire is needed.
//! Z is odd for every X,Y, including signed overflow and non-unit orbits.
//! Drop its known-one low bit and signed-resize the remaining W-2 bits to
//! next_width-1. This is NOT an unbounded sum followed by halving.
//!
//! Backward first resizes X to old_width-1 and the compressed target to
//! old_width-2, prepends a one to reconstruct Z, and computes Y = Z + D.
//! The old sign is then cleared from the restored X[0],Y[0], just as before.
//! Backward is the original backward CHANNEL, not necessarily an inverse
//! after a lossy width reduction. No endpoint convergence is required.
//!
//! Each signed shrink still emits CX(next_high, discarded_high), R(high),
//! in the original target/source (forward) or source/target (backward) order.
//! The discarded bit and its phase obligation are identical under encoding,
//! even when it is nonzero. Couple these semantic R outcomes between circuits;
//! raw PRNG positions need not match after removing/adding clean resets and
//! changing the vent count. All adder HMR phases are corrected internally.
//!
//! Domain: BOTH incoming values must be odd; forward_with_sign additionally
//! requires the supplied logical sign to equal X[0] xor Y[0]. Arbitrary even
//! inputs or corrupt supplied signs cannot be represented by two fewer bits.
//! In particular, do not use a sampled convergence claim to establish this
//! domain, or apply this codec to endpoint selector wires. Widths >=3 keep
//! every original parity bit, even on invalid width-envelope paths.
//!
//! # Integration by the owning worker (not wired by this change)
//!
//! Add `#[path = "midq_odd_values.rs"] mod midq_odd_values;` beside the other
//! modules in shrunken_pz_state_machine.rs. No op stream changes unless the
//! owner explicitly branches on enabled(), i.e. MIDQ_ODD_VALUES=1.
//!
//! Minimal persistent window: rounds 8..taped_rounds. Keep normalization,
//! shared counter rounds 0..8, checkpoint, endpoint, and payload UNCHANGED.
//! In the current implementation the preceding coefficient loan explicitly
//! R-resets both low wires, reacquires their cleaned IDs, then applies X.
//! Thus this entry boundary has low ones even if an earlier low-bit reset
//! was dirty. Retain those earlier resets and their phase obligations.
//! Before forward round 8, compress each row, before allocating its sign.
//! Within this window use signed_resize for loop-entry resizes, forward in
//! place of midq_value_round_forward (same argument order plus vents), and
//! omit BOTH odd-low loan/restore calls around coefficient arithmetic: the
//! lows are already absent. Coefficient arithmetic and tape ownership stay
//! unchanged. Expand both rows immediately after the forward loop, BEFORE
//! checkpoint::forward or any endpoint consumer.
//!
//! Backward: after checkpoint::backward has restored the original odd pair
//! (or after endpoint restoration without checkpoint), compress both rows
//! before the reverse loop. Omit odd-low loan/restore in rounds >=8, and use
//! backward with the original logical old_width. After undoing round 8,
//! expand both rows BEFORE round 7 and its counter-tape decoder. If the
//! compressed window is empty, do none of these conversions. Do not recompute
//! enabled() inconsistently between forward and backward; retain the choice
//! in owner state or use one immutable construction-time setting.
//!
//! Pass the existing midq_value_vents() unchanged. The 225-entry schedule is
//! not edited or tightened: entry W becomes W-1 physical bits per row.
//! Reconstructed low wires have fresh ownership/possibly different IDs;
//! no BorrowedQReg, slice, or saved low ID may survive compress/expand.
//! Full-width checkpoint/endpoint boundaries still cost the original width.
//!
//! Registering this module also registers its #[test] module. The owner may
//! later run `cargo test midq_odd_values -- --test-threads=1` or call selftest()
//! from its existing selftest dispatch. No tests/builds were run for this
//! isolated change, per the laptop/remote serialization restriction.
//!
//! # Static cost, not a benchmark claim
//!
//! Per add, emitted Toffolis change from 2(W-1)-min(vents,W-1) to
//! 2(W-2)-min(vents,W-2): a saving of 1 or 2, with no new Toffolis.
//! The value-adder live set loses two operand bits (and possibly one vent).
//! Coefficient cells already loaned the lows, so do not count another -2
//! there. New X gates and the narrower source complements are Clifford-only.
//! This alone does not establish Q<=1009 or T<12.5M for the full circuit.

use crate::point_add::trailmix_port::arith::gidney_const_adder::hybrid_add_refs;
use crate::point_add::trailmix_port::circuit::{Circuit, QReg};

pub(super) fn enabled() -> bool {
    std::env::var("MIDQ_ODD_VALUES").ok().as_deref() == Some("1")
}

pub(super) fn padding_enabled() -> bool {
    std::env::var("MIDQ_VALUE_PADDING_LOAN").ok().as_deref() == Some("1")
}

pub(super) fn with_forward_padding(c: &mut Circuit, source: &mut Vec<QReg>,
    target: &mut Vec<QReg>, width: usize, next: usize, source_last_width: Option<usize>,
    body: impl FnOnce(&mut Circuit)) {
    assert_eq!(source.len(), next - 1);
    assert_eq!(target.len(), next - 1);
    // A W-bit wrapped sum is halved before sign extension. Its extra sign
    // copy is constructor-proven, even for overflowing or nonconvergent walks.
    if width == next { resize_bits(c, target, next - 2, "midq.odd.target.sign"); }
    if source_last_width == Some(next) { resize_bits(c, source, next - 2, "midq.odd.source.sign"); }
    body(c);
    signed_resize(c, source, next);
    signed_resize(c, target, next);
}

pub(super) fn prepare_backward_target(c: &mut Circuit, target: &mut Vec<QReg>, old: usize) {
    assert_eq!(target.len(), old - 1);
    // This is the SAME possibly-dirty signed-shrink R used by backward().
    // Moving it across coefficient arithmetic is safe: that arithmetic never
    // reads the value registers. Do not substitute a clean-zero assertion.
    resize_bits(c, target, old - 2, "midq.odd.target.sign");
}

/// Consume the known-one low wire. The caller proves oddness, not convergence.
pub(super) fn compress(c: &mut Circuit, value: &mut Vec<QReg>) {
    assert!(value.len() >= 3);
    let low = value.remove(0);
    c.x(&low);
    c.zero_and_free(low);
}

/// Materialize a fresh owned low one, never reacquire a potentially reused ID.
pub(super) fn expand(c: &mut Circuit, value: &mut Vec<QReg>) {
    assert!(value.len() >= 2);
    let low = c.alloc_qreg("midq.odd.low");
    c.x(&low);
    value.insert(0, low);
}

fn resize_bits(c: &mut Circuit, value: &mut Vec<QReg>, bits: usize, name: &str) {
    assert!(bits >= 1 && !value.is_empty());
    while value.len() > bits {
        let high = value.pop().unwrap();
        c.cx(value.last().unwrap(), &high);
        // Deliberately retain the original R, including its off-envelope phase.
        c.zero_and_free(high);
    }
    while value.len() < bits {
        let high = c.alloc_qreg(name);
        c.cx(value.last().unwrap(), &high);
        value.push(high);
    }
}

pub(super) fn signed_resize(c: &mut Circuit, value: &mut Vec<QReg>, width: usize) {
    assert!(width >= 3);
    resize_bits(c, value, width - 1, "midq.odd.sign");
}

fn complement_source(c: &mut Circuit, source: &[QReg], sign: &QReg) {
    for q in source {
        c.x(q);
        c.cx(sign, q);
    }
}

/// Same zero-initialized sign/tape contract as midq_value_round_forward.
pub(super) fn forward(
    c: &mut Circuit,
    source: &mut Vec<QReg>,
    target: &mut Vec<QReg>,
    sign: &QReg,
    next_width: usize,
    vents: usize,
) {
    assert_eq!(source.len(), target.len());
    assert!(source.len() >= 2 && next_width >= 3);
    c.cx(&target[0], sign);
    c.cx(&source[0], sign);
    forward_with_sign(c, source, target, sign, next_width, vents);
}

/// Supplied sign MUST equal source[0] xor target[0]; it is preserved.
pub(super) fn forward_with_sign(
    c: &mut Circuit,
    source: &mut Vec<QReg>,
    target: &mut Vec<QReg>,
    sign: &QReg,
    next_width: usize,
    vents: usize,
) {
    assert_eq!(source.len(), target.len());
    assert!(source.len() >= 2 && next_width >= 3);
    complement_source(c, source, sign);
    for q in target.iter() {
        c.x(q);
    }
    hybrid_add_refs(
        c,
        &target.iter().collect::<Vec<_>>(),
        &source.iter().collect::<Vec<_>>(),
        vents,
    );
    for q in target.iter() {
        c.x(q);
    }
    complement_source(c, source, sign);
    let low = target.remove(0);
    c.x(&low);
    c.zero_and_free(low);
    signed_resize(c, target, next_width);
    signed_resize(c, source, next_width);
}

/// Match the full-width backward channel, including its lossy resizes.
pub(super) fn backward(
    c: &mut Circuit,
    source: &mut Vec<QReg>,
    target: &mut Vec<QReg>,
    sign: QReg,
    old_width: usize,
    vents: usize,
) {
    assert!(target.len() == source.len() || target.len() + 1 == source.len());
    assert!(source.len() >= 2 && !target.is_empty() && old_width >= 3);
    signed_resize(c, source, old_width);
    resize_bits(c, target, old_width - 2, "midq.odd.target.sign");
    let low = c.alloc_qreg("midq.odd.target.low");
    c.x(&low);
    target.insert(0, low);
    complement_source(c, source, &sign);
    hybrid_add_refs(
        c,
        &target.iter().collect::<Vec<_>>(),
        &source.iter().collect::<Vec<_>>(),
        vents,
    );
    complement_source(c, source, &sign);
    c.cx(&source[0], &sign);
    c.cx(&target[0], &sign);
    c.zero_and_free(sign);
}

#[path = "midq_odd_values_tests.rs"]
mod tests;

pub(crate) fn selftest() {
    tests::run();
}
