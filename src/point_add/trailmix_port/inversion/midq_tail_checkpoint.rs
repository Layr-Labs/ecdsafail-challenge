//! Default-off, exact checkpoint codec for the four constant-width tail rounds.
//!
//! The six nonconstant bits of the original odd pair remain in a[1..4], b[1..4].
//! They encode every intermediate value and sign, including signed wraparound.
//! No second pair or suffix tape is allocated. All four 257-bit coefficient
//! updates still execute. At the endpoint, the two known-one low wires instead
//! hold the terminal signs. Those are the only value bits read before reversal;
//! terminal magnitudes (including 3, not just 1) remain encoded by the checkpoint.
//! Thus checkpoint + live endpoint selectors occupy eight wires, not 6 + 8.
//! A lookup uses at most one clean scratch, explicitly allocated below.
//!
//! Reversal clears the endpoint selectors, restores the odd lows, recomputes
//! each sign, and undoes every coefficient update. The original pair never
//! changed, so there is no checkpoint erasure. Do not extend this across width
//! reductions: their reset/phase behavior needs a separate channel proof.

use super::{
    midq_loan_odd_low_bits, midq_mod_signed_add_halve, midq_restore_odd_low_bits, Circuit, QReg,
    MIDQ_TAIL_ROUNDS, MIDQ_TAIL_VALUE_WIDTH,
};
use std::sync::OnceLock;

pub(super) const START: usize = 220;
const WIDTH: usize = 4;
const ROUNDS: usize = MIDQ_TAIL_ROUNDS - START;
const INPUT_BITS: usize = 2 * (WIDTH - 1);
const STATES: usize = 1 << INPUT_BITS;

pub(super) fn enabled() -> bool {
    std::env::var("MIDQ_TAIL_CHECKPOINT").ok().as_deref() == Some("1")
}

fn signed(value: i16, width: usize) -> i16 {
    let shift = 16 - width;
    (value << shift) >> shift
}

fn trajectory(input: usize) -> ([u8; ROUNDS], [i16; 2]) {
    let mut pair = [
        signed(((input & 7) * 2 + 1) as i16, WIDTH),
        signed(((input >> 3) * 2 + 1) as i16, WIDTH),
    ];
    let mut signs = [0; ROUNDS];
    for (offset, sign) in signs.iter_mut().enumerate() {
        *sign = ((pair[0] ^ pair[1]) >> 1 & 1) as u8;
        let target = if (START + offset) % 2 == 0 { 1 } else { 0 };
        let source = pair[1 - target];
        let sum = pair[target] + if *sign == 0 { source } else { -source };
        // The original add wraps BEFORE the arithmetic right shift.
        pair[target] = signed(sum, WIDTH) >> 1;
    }
    (signs, pair)
}

fn functions() -> &'static [Vec<u8>] {
    static TABLE: OnceLock<Vec<Vec<u8>>> = OnceLock::new();
    TABLE.get_or_init(|| {
        assert_eq!(ROUNDS, 4);
        assert!(MIDQ_TAIL_VALUE_WIDTH[START..]
            .iter()
            .all(|&w| w as usize == WIDTH));
        let rows: Vec<_> = (0..STATES).map(trajectory).collect();
        (0..ROUNDS + 2 * WIDTH)
            .map(|output| {
                let mut truth: Vec<u8> = rows
                    .iter()
                    .map(|(signs, pair)| {
                        if output < ROUNDS {
                            signs[output]
                        } else {
                            let bit = output - ROUNDS;
                            ((pair[bit / WIDTH] >> (bit % WIDTH)) & 1) as u8
                        }
                    })
                    .collect();
                // Boolean Mobius transform: exact truth table -> XOR of monomials.
                for bit in 0..INPUT_BITS {
                    for mask in 0..STATES {
                        if mask & (1 << bit) != 0 {
                            truth[mask] ^= truth[mask ^ (1 << bit)];
                        }
                    }
                }
                let terms: Vec<u8> = truth
                    .iter()
                    .enumerate()
                    .filter_map(|(mask, &on)| (on != 0).then_some(mask as u8))
                    .collect();
                let limit = if output < ROUNDS { 2 } else { 3 };
                assert!(terms.iter().all(|term| term.count_ones() <= limit));
                terms
            })
            .collect()
    })
}

fn lookup(c: &mut Circuit, a: &[QReg], b: &[QReg], target: &QReg, output: usize) {
    assert_eq!(a.len(), WIDTH);
    assert_eq!(b.len(), WIDTH);
    let inputs: Vec<_> = a[1..].iter().chain(&b[1..]).collect();
    let terms = &functions()[output];
    let scratch = terms
        .iter()
        .any(|term| term.count_ones() == 3)
        .then(|| c.alloc_qreg("midq.checkpoint.lookup"));
    for &term in terms {
        let controls: Vec<_> = inputs
            .iter()
            .enumerate()
            .filter_map(|(bit, &q)| (term & (1 << bit) != 0).then_some(q))
            .collect();
        match controls.as_slice() {
            [] => c.x(target),
            [x] => c.cx(x, target),
            [x, y] => c.ccx(x, y, target),
            [x, y, z] => {
                let tmp = scratch.as_ref().expect("cubic lookup scratch");
                c.ccx(x, y, tmp);
                c.ccx(tmp, z, target);
                c.ccx(x, y, tmp);
            }
            _ => unreachable!("lookup degree is checked"),
        }
    }
    if let Some(scratch) = scratch {
        c.zero_and_free(scratch);
    }
}

fn coefficient_round(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    ca: &[QReg],
    cb: &[QReg],
    offset: usize,
    inverse: bool,
) {
    let sign = c.alloc_qreg("midq.checkpoint.sign");
    lookup(c, a, b, &sign, offset);
    let lows = midq_loan_odd_low_bits(c, a, b);
    if (START + offset) % 2 == 0 {
        midq_mod_signed_add_halve(c, cb, ca, &sign, inverse);
    } else {
        midq_mod_signed_add_halve(c, ca, cb, &sign, inverse);
    }
    midq_restore_odd_low_bits(c, a, b, lows);
    lookup(c, a, b, &sign, offset);
    c.zero_and_free(sign);
}

pub(super) fn forward(c: &mut Circuit, a: &[QReg], b: &[QReg], ca: &[QReg], cb: &[QReg]) {
    for offset in 0..ROUNDS {
        coefficient_round(c, a, b, ca, cb, offset, false);
    }
    c.x(&a[0]);
    c.x(&b[0]);
    lookup(c, a, b, &a[0], ROUNDS + WIDTH - 1);
    lookup(c, a, b, &b[0], ROUNDS + 2 * WIDTH - 1);
}

pub(super) fn backward(c: &mut Circuit, a: &[QReg], b: &[QReg], ca: &[QReg], cb: &[QReg]) {
    lookup(c, a, b, &b[0], ROUNDS + 2 * WIDTH - 1);
    lookup(c, a, b, &a[0], ROUNDS + WIDTH - 1);
    c.x(&b[0]);
    c.x(&a[0]);
    for offset in (0..ROUNDS).rev() {
        coefficient_round(c, a, b, ca, cb, offset, true);
    }
}

#[path = "midq_tail_checkpoint_tests.rs"]
mod tests;

pub(crate) fn selftest() {
    tests::checkpoint_schedule_storage_accounting();
    tests::checkpoint_lookup_exhaustive_values_signs_and_phase();
    tests::checkpoint_value_model_matches_emitted_overflow_behavior();
    tests::checkpoint_full_width_coefficients_match_reference();
}
