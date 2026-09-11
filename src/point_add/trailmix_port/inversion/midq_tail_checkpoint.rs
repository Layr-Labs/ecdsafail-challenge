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

#[path = "checkpoint14_gate.rs"]
mod extension_gate;
pub(super) const START: usize = extension_gate::start(
    &MIDQ_TAIL_VALUE_WIDTH,
    MIDQ_TAIL_ROUNDS,
    super::hybrid_profile::SELECTED.checkpoint_start,
);
const WIDTH: usize = 4;
const ROUNDS: usize = MIDQ_TAIL_ROUNDS - START;
const INPUT_BITS: usize = 2 * (WIDTH - 1);
const STATES: usize = 1 << INPUT_BITS;

pub(super) fn enabled() -> bool {
    let enabled = std::env::var("MIDQ_TAIL_CHECKPOINT").ok().as_deref() == Some("1");
    if enabled && ROUNDS == 14 {
        static REPORTED: std::sync::Once = std::sync::Once::new();
        REPORTED.call_once(|| eprintln!(
            "HYBRID_CHECKPOINT rounds=14 actual_start={} original_start={} width=4 preserved_selected_profile=true stable_sign_cache_wires=1 dirty_lookup_workspace=0",
            START, super::hybrid_profile::SELECTED.checkpoint_start));
    }
    enabled
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
    if ROUNDS == 14 {
        let stable = *signs
            .get(4)
            .expect("fourteen-round trajectory has a fifth sign");
        assert!(
            signs.iter().skip(4).all(|&s| s == stable),
            "all64 wrapping width4 trajectories must have one stable sign after four rounds"
        );
    }
    (signs, pair)
}

fn functions() -> &'static [Vec<u8>] {
    static TABLE: OnceLock<Vec<Vec<u8>>> = OnceLock::new();
    TABLE.get_or_init(|| {
        assert!(matches!(ROUNDS, 4 | 14));
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
                let limit = if output < ROUNDS && output < 4 { 2 } else { 3 };
                assert!(terms.iter().all(|term| term.count_ones() <= limit));
                terms
            })
            .collect()
    })
}

fn lookup(c: &mut Circuit, a: &[QReg], b: &[QReg], target: &QReg, output: usize) {
    lookup_skipping(c, a, b, target, output, None, 0);
}

fn input_bits<'a>(a: &'a [QReg], b: &'a [QReg]) -> Vec<&'a QReg> {
    assert!(matches!(a.len(), 3 | 4) && matches!(b.len(), 3 | 4));
    a[a.len() - 3..].iter().chain(&b[b.len() - 3..]).collect()
}

fn lookup_skipping(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    target: &QReg,
    output: usize,
    omitted: Option<u8>,
    excluded: u8,
) {
    let inputs = input_bits(a, b);
    let terms = &functions()[output];
    let dirty_lookup = std::env::var("MIDQ_DIRTY_CHECKPOINT_LOOKUP")
        .ok()
        .as_deref()
        == Some("1")
        || inplace_endpoints();
    let scratch = (!dirty_lookup && terms.iter().any(|term| term.count_ones() == 3))
        .then(|| c.alloc_qreg("midq.checkpoint.lookup"));
    for &term in terms {
        if omitted == Some(term) || term & excluded != 0 {
            continue;
        }
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
                let tmp = if dirty_lookup {
                    *inputs
                        .iter()
                        .find(|q| {
                            q.id() != target.id() && controls.iter().all(|ctrl| ctrl.id() != q.id())
                        })
                        .expect("six inputs leave a donor outside a cubic monomial")
                } else {
                    scratch.as_ref().expect("cubic lookup scratch")
                };
                c.ccx(x, y, tmp);
                c.ccx(tmp, z, target);
                c.ccx(x, y, tmp);
                if dirty_lookup {
                    c.ccx(tmp, z, target);
                }
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
    let cap_scope = super::checkpoint_cap_aware::enter(c);
    if std::env::var("MIDQ_INPLACE_CHECKPOINT_SIGN")
        .ok()
        .as_deref()
        == Some("1")
    {
        let terms = &functions()[offset];
        let coordinate = (0..INPUT_BITS)
            .find(|&bit| {
                terms.contains(&(1 << bit))
                    && terms
                        .iter()
                        .all(|&term| term == 1 << bit || term & (1 << bit) == 0)
            })
            .expect("each four-round decision has an exclusive linear coordinate");
        let inputs = input_bits(a, b);
        let sign = inputs[coordinate];
        // sigma = coordinate XOR f(other checkpoint bits), so no extra wire
        // is needed while the coefficient cell reads this temporary encoding.
        lookup_skipping(c, a, b, sign, offset, Some(1 << coordinate), 0);
        let lows = (a.len() == WIDTH).then(|| midq_loan_odd_low_bits(c, a, b));
        if (START + offset) % 2 == 0 {
            midq_mod_signed_add_halve(c, cb, ca, sign, inverse);
        } else {
            midq_mod_signed_add_halve(c, ca, cb, sign, inverse);
        }
        if let Some(lows) = lows {
            midq_restore_odd_low_bits(c, a, b, lows);
        }
        lookup_skipping(c, a, b, sign, offset, Some(1 << coordinate), 0);
        super::checkpoint_cap_aware::leave(c, cap_scope);
        return;
    }
    let sign = c.alloc_qreg("midq.checkpoint.sign");
    lookup(c, a, b, &sign, offset);
    let lows = (a.len() == WIDTH).then(|| midq_loan_odd_low_bits(c, a, b));
    if (START + offset) % 2 == 0 {
        midq_mod_signed_add_halve(c, cb, ca, &sign, inverse);
    } else {
        midq_mod_signed_add_halve(c, ca, cb, &sign, inverse);
    }
    if let Some(lows) = lows {
        midq_restore_odd_low_bits(c, a, b, lows);
    }
    lookup(c, a, b, &sign, offset);
    c.zero_and_free(sign);
    super::checkpoint_cap_aware::leave(c, cap_scope);
}

// f4 has cubic monomials, so it cannot use the four-round exclusive-linear
// coordinate trick. Cache it once in one explicit wire. Every cubic term
// borrows a checkpoint input outside its controls and restores that donor.
fn stable_lookup(c: &mut Circuit, a: &[QReg], b: &[QReg], target: &QReg) {
    assert_eq!(ROUNDS, 14);
    let inputs = input_bits(a, b);
    assert!(inputs.iter().all(|q| q.id() != target.id()));
    for &term in &functions()[4] {
        let controls: Vec<_> = inputs
            .iter()
            .enumerate()
            .filter_map(|(i, &q)| (term >> i & 1 != 0).then_some(q))
            .collect();
        match controls.as_slice() {
            [] => c.x(target),
            [x] => c.cx(x, target),
            [x, y] => c.ccx(x, y, target),
            [x, y, z] => {
                let donor = *inputs
                    .iter()
                    .find(|q| controls.iter().all(|ctrl| ctrl.id() != q.id()))
                    .unwrap();
                c.ccx(x, y, donor);
                c.ccx(donor, z, target);
                c.ccx(x, y, donor);
                c.ccx(donor, z, target);
            }
            _ => unreachable!("stable checkpoint sign has degree at most three"),
        }
    }
}

fn with_stable_sign(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    body: impl FnOnce(&mut Circuit, &QReg),
) {
    c.flush_pending_frees();
    let before = c.b.active_qubits;
    let sign = c.alloc_qreg("midq.checkpoint14.stable_sign");
    stable_lookup(c, a, b, &sign);
    c.flush_pending_frees();
    assert_eq!(
        c.b.active_qubits,
        before + 1,
        "stable lookup allocated extra workspace"
    );
    let cache_live = c.b.active_qubits;
    body(c, &sign);
    c.flush_pending_frees();
    let after_body = c.b.active_qubits;
    stable_lookup(c, a, b, &sign);
    c.flush_pending_frees();
    assert_eq!(
        c.b.active_qubits, after_body,
        "stable lookup leaked workspace"
    );
    c.zero_and_free(sign);
    c.flush_pending_frees();
    assert_eq!(
        c.b.active_qubits + 1,
        after_body,
        "stable cache ownership not returned"
    );
    if std::env::var_os("MIDQ_CHECKPOINT14_TRACE").is_some() {
        eprintln!("CHECKPOINT14_LIVE start={} value_bits={} entry={} cached={} after_body={} exit={} allocator_peak={} cache_wires=1 lookup_clean_work=0",
            START,input_bits(a,b).len(),before,cache_live,after_body,c.b.active_qubits,c.b.peak_qubits);
    }
}

fn coefficient_with_sign(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    ca: &[QReg],
    cb: &[QReg],
    sign: &QReg,
    offset: usize,
    inverse: bool,
) {
    let scope = super::checkpoint_cap_aware::enter(c);
    let lows = (a.len() == WIDTH).then(|| midq_loan_odd_low_bits(c, a, b));
    if (START + offset) % 2 == 0 {
        midq_mod_signed_add_halve(c, cb, ca, sign, inverse);
    } else {
        midq_mod_signed_add_halve(c, ca, cb, sign, inverse);
    }
    if let Some(lows) = lows {
        midq_restore_odd_low_bits(c, a, b, lows);
    }
    super::checkpoint_cap_aware::leave(c, scope);
}

pub(super) fn forward(c: &mut Circuit, a: &[QReg], b: &[QReg], ca: &[QReg], cb: &[QReg]) {
    if ROUNDS == 14 {
        for offset in 0..4 {
            coefficient_round(c, a, b, ca, cb, offset, false);
        }
        with_stable_sign(c, a, b, |c, sign| {
            for offset in 4..ROUNDS {
                coefficient_with_sign(c, a, b, ca, cb, sign, offset, false);
            }
        });
    } else {
        for offset in 0..ROUNDS {
            coefficient_round(c, a, b, ca, cb, offset, false);
        }
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
    if ROUNDS == 14 {
        with_stable_sign(c, a, b, |c, sign| {
            for offset in (4..ROUNDS).rev() {
                coefficient_with_sign(c, a, b, ca, cb, sign, offset, true);
            }
        });
        for offset in (0..4).rev() {
            coefficient_round(c, a, b, ca, cb, offset, true);
        }
    } else {
        for offset in (0..ROUNDS).rev() {
            coefficient_round(c, a, b, ca, cb, offset, true);
        }
    }
}

pub(super) fn park_selectors(c: &mut Circuit, a: &mut Vec<QReg>, b: &mut Vec<QReg>) {
    assert_eq!(a.len(), WIDTH);
    assert_eq!(b.len(), WIDTH);
    lookup(c, a, b, &a[0], ROUNDS + WIDTH - 1);
    lookup(c, a, b, &b[0], ROUNDS + 2 * WIDTH - 1);
    c.zero_and_free(a.remove(0));
    c.zero_and_free(b.remove(0));
}

pub(super) fn six_bits_enabled() -> bool {
    std::env::var("MIDQ_SIX_BIT_CHECKPOINT").ok().as_deref() == Some("1")
}

// Endpoint signs remain Boolean functions of the six checkpoint bits. There
// is no need to materialize sign/low wires around the four coefficient cells.
pub(super) fn encoded_rounds(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    ca: &mut Vec<QReg>,
    cb: &mut Vec<QReg>,
    inverse: bool,
) {
    assert_eq!(a.len(), WIDTH - 1);
    assert_eq!(b.len(), WIDTH - 1);
    assert!(super::midq_narrow_coefficients());
    if ROUNDS == 14 {
        let regular = |c: &mut Circuit, ca: &mut Vec<QReg>, cb: &mut Vec<QReg>| {
            for index in 0..4 {
                let offset = if inverse { 3 - index } else { index };
                coefficient_round(c, a, b, ca, cb, offset, inverse);
                let target = if (START + offset) % 2 == 0 {
                    &mut *cb
                } else {
                    &mut *ca
                };
                super::shrunken_pz_resize(c, target, 256, "midq.checkpoint.coefficient");
            }
        };
        let stable = |c: &mut Circuit, ca: &mut Vec<QReg>, cb: &mut Vec<QReg>| {
            with_stable_sign(c, a, b, |c, sign| {
                for index in 0..ROUNDS - 4 {
                    let offset = if inverse {
                        ROUNDS - 1 - index
                    } else {
                        4 + index
                    };
                    coefficient_with_sign(c, a, b, ca, cb, sign, offset, inverse);
                    let target = if (START + offset) % 2 == 0 {
                        &mut *cb
                    } else {
                        &mut *ca
                    };
                    super::shrunken_pz_resize(c, target, 256, "midq.checkpoint.coefficient");
                }
            });
        };
        if inverse {
            stable(c, ca, cb);
            regular(c, ca, cb);
        } else {
            regular(c, ca, cb);
            stable(c, ca, cb);
        }
        return;
    }
    for index in 0..ROUNDS {
        let offset = if inverse { ROUNDS - 1 - index } else { index };
        coefficient_round(c, a, b, ca, cb, offset, inverse);
        // The target's original borrow cleanup has actually HMR-cleared its
        // overflow, including noncanonical inputs. Do not trim the other row.
        let target = if (START + offset) % 2 == 0 {
            &mut *cb
        } else {
            &mut *ca
        };
        super::shrunken_pz_resize(c, target, 256, "midq.checkpoint.coefficient");
    }
}

pub(super) fn inplace_endpoints() -> bool {
    std::env::var("MIDQ_INPLACE_ENDPOINT_SIGNS").ok().as_deref() == Some("1")
}

pub(super) fn with_endpoint_sign(
    c: &mut Circuit,
    a: &[QReg],
    b: &[QReg],
    which: usize,
    body: impl FnOnce(&mut Circuit, &QReg),
) {
    assert!(which < 2);
    assert!((0..STATES).all(|x| ((trajectory(x).1[which]
        ^ trajectory(x ^ (STATES - 1)).1[which])
        & (1 << (WIDTH - 1)))
        != 0));
    let input = input_bits(a, b);
    let pivot = input[0];
    // Common negation flips all six input bits and the endpoint sign.
    // Normalize the other five coordinates against the pivot to expose it
    // as an exclusive linear term of the sign function.
    for &q in &input[1..] {
        c.cx(pivot, q);
    }
    let output = ROUNDS + (which + 1) * WIDTH - 1;
    lookup_skipping(c, a, b, pivot, output, None, 1);
    body(c, pivot);
    lookup_skipping(c, a, b, pivot, output, None, 1);
    for &q in &input[1..] {
        c.cx(pivot, q);
    }
}

pub(super) fn restore_selectors(c: &mut Circuit, a: &mut Vec<QReg>, b: &mut Vec<QReg>) {
    assert_eq!(a.len(), WIDTH - 1);
    assert_eq!(b.len(), WIDTH - 1);
    a.insert(0, c.alloc_qreg("midq.checkpoint.a_sign"));
    b.insert(0, c.alloc_qreg("midq.checkpoint.b_sign"));
    lookup(c, a, b, &a[0], ROUNDS + WIDTH - 1);
    lookup(c, a, b, &b[0], ROUNDS + 2 * WIDTH - 1);
}

#[path = "midq_tail_checkpoint_tests.rs"]
mod tests;

pub(crate) fn selftest() {
    if inplace_endpoints() {
        tests::checkpoint_endpoint_sign_in_place();
    }
    tests::checkpoint_schedule_storage_accounting();
    tests::checkpoint_lookup_exhaustive_values_signs_and_phase();
    tests::checkpoint_value_model_matches_emitted_overflow_behavior();
    tests::checkpoint_full_width_coefficients_match_reference();
}

#[path = "checkpoint14_tests.rs"]
mod extension_tests;

pub(crate) fn extension_selftest() {
    extension_tests::run();
}
