//! Opt-in research prototype: shorten the live sign tape across the payload.
//!
//! Enable with MIDQ_PAYLOAD_VALUE_REPLAY_START=160 (0/unset disables it).
//! With the unchanged source schedule, 220 signs + 6 checkpoint bits become
//! 160 signs + 48 checkpoint bits, an 18-wire PERSISTENT-STORAGE reduction.
//! The original late forward/backward coefficient-stage peak is unchanged.
//! No whole-circuit qubit or Toffoli improvement is claimed by this module.
//!
//! Contract: on the inherited clean-width, clean-reset support, every added
//! reverse value round is the inverse of its original forward value round.
//! Coefficients are only spectators. Thus pack followed by unpack is identity
//! on that support, with all measured-add phases internally corrected. This
//! argument is NOT an all-input channel equivalence when the inherited signed
//! resizes have discarded non-sign bits. Full phase/ancilla regression against
//! frozen successful inputs is required before promotion.
//!
//! No width table, GCD round count, coefficient operation, or nonce is changed.
//! Reconstruction uses only the original value registers and the consumed tape
//! slots. There is no checkpoint copy. The baseline value-vent setting is retained.

use super::{midq_odd_values, midq_tail_checkpoint, midq_value_vents, Circuit, QReg,
    MIDQ_TAIL_VALUE_WIDTH};

pub(super) fn configured_start() -> Option<usize> {
    let start = super::env_usize("MIDQ_PAYLOAD_VALUE_REPLAY_START", 0);
    if start == 0 { return None; }
    assert!((8..midq_tail_checkpoint::START).contains(&start),
        "payload value replay must retain the shared counter's first eight rounds");
    Some(start)
}

pub(super) fn pack(c: &mut Circuit, a: &mut Vec<QReg>, b: &mut Vec<QReg>,
    tape: &mut Vec<QReg>, start: usize) {
    assert_eq!(tape.len(), midq_tail_checkpoint::START);
    assert_eq!(a.len(), 3);
    assert_eq!(b.len(), 3);
    let previous = c.push_section("midq.payload.value_replay.pack");
    for round in (start..midq_tail_checkpoint::START).rev() {
        let sign = tape.pop().expect("one original sign for every reversed value round");
        let width = MIDQ_TAIL_VALUE_WIDTH[round] as usize;
        if round % 2 == 0 {
            midq_odd_values::backward(c, a, b, sign, width, midq_value_vents());
        } else {
            midq_odd_values::backward(c, b, a, sign, width, midq_value_vents());
        }
    }
    assert_eq!(a.len(), MIDQ_TAIL_VALUE_WIDTH[start] as usize - 1);
    assert_eq!(b.len(), MIDQ_TAIL_VALUE_WIDTH[start] as usize - 1);
    c.pop_section(&previous);
}

pub(super) fn unpack(c: &mut Circuit, a: &mut Vec<QReg>, b: &mut Vec<QReg>,
    tape: &mut Vec<QReg>, start: usize) {
    assert_eq!(tape.len(), start);
    let previous = c.push_section("midq.payload.value_replay.unpack");
    for round in start..midq_tail_checkpoint::START {
        let width = MIDQ_TAIL_VALUE_WIDTH[round] as usize;
        let next_width = MIDQ_TAIL_VALUE_WIDTH[round + 1] as usize;
        midq_odd_values::signed_resize(c, a, width);
        midq_odd_values::signed_resize(c, b, width);
        let sign = c.alloc_qreg(&format!("midq.sign[{round}].replayed"));
        if round % 2 == 0 {
            midq_odd_values::forward(c, a, b, &sign, next_width, midq_value_vents());
        } else {
            midq_odd_values::forward(c, b, a, &sign, next_width, midq_value_vents());
        }
        tape.push(sign);
    }
    assert_eq!(a.len(), 3);
    assert_eq!(b.len(), 3);
    c.pop_section(&previous);
}
