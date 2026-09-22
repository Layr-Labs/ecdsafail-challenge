//! Adversarial review harness for the packed driver (review of 2026-09-14:
//! `division.rs` / `multiply.rs` / `driver.rs` / `inverse.rs` against
//! `tools/spike/packed_design.md` 3.1-3.4). It adds the cases the shipped
//! harnesses (`division_selftest.rs` = static schedule, 64 random inputs;
//! `multiply_selftest.rs` = static schedule; `driver_selftest.rs` = thin
//! schedule, 64 random inputs whose earliest termination is row 397) do not
//! reach, all under the PRODUCTION thin schedule (seed 278, 500k validation
//! draws, `TRAILMIX_THIN_CLZ_WINDOW=78`):
//!
//! 1. **Pool search**: `MIDQ_REVIEW_POOL` (default 32768) Shake256-seeded model
//!    inputs are traced classically (the verbatim `pz_prefix` recurrence of
//!    `tools/packed_prefix_model.py` with the circuit's counter / parity
//!    bookkeeping) and every row of the two widest bands - 284..=313 (q = 29 in
//!    the tree's thin profile, the measured 866 owner) and 378..=413 (the
//!    design's 866 rows) - plus every row anywhere for the four bound metrics is
//!    scored per class: maximal drop `d`, maximal `s`, off = 1 / off = 0 with
//!    `d = 1` (R's MSB at the D11 window top / one below it), R1 gap 0 at a
//!    division (`e_A + e_cb = 257`: cb's MSB one wire above A's), `e_A = W_A`
//!    (A fills the value ring: A's bit 0 is the first wire above the field in
//!    the s-frame), `e_B = lo_B + 1` (D11's maximal alignment amount / ring
//!    bottom) and `e_B = W_A` (amount 0); multiply rows with maximal `s2`,
//!    maximal R2 gap, carry = 1, the tight R2 row `e_B + s2 + e_cb = 257` (B's
//!    MSB is M5's absorb wire), R1 gap 0, `e_B = lo_B + 1` / `e_B = W_B`
//!    (M1's amounts 1 and max). The top two rows per class are kept.
//! 2. **Substep cases**: every kept row is run through `division_forward` /
//!    `division_backward` or `multiply_forward` / `multiply_backward` at the
//!    thin schedule's geometry (`StepWidths::from_schedule`, one source for both substeps
//!    = exactly what `driver::pass_step` passes), with the ctz kernels planned
//!    at the production room (`MIDQ_PACKED_CTZ_ROOM=12`, `MIDQ_PREFIX_QCAP` =
//!    data + 12): value against the oracle (rows off the support - classified by
//!    the driver's own predicate - are excluded from the value claim only),
//!    phase 0, every freed ancilla 0 at its reset, then the inverse on the
//!    outputs must restore the inputs exactly. Where a class has no natural row
//!    in a band (`e_A = W_A`, `e_B = W_A`, `e_B = W_B` are envelope hits) the
//!    row with the largest exponent is run with the envelope NARROWED to it
//!    (`StepWidths::new` with `w_a = e_A` / `w_b = e_B`): the same circuit
//!    family at its tightest legal geometry.
//! 3. **Driver round trips** (the `driver_selftest.rs` loop on chosen inputs):
//!    (a) the earliest-terminating inputs of the pool (terminal step in
//!    [365, 400] where the pool has them: the popcount-erase row 365, the first
//!    terminal-aware rows, draining rows right after 365); (b) the class
//!    winners of (1) so the driver - not only the substep - sees the extreme
//!    rows in context (role pair, swap, counter). 530 rows forward with the
//!    oracle check at every row, 530 rows backward to S_0, phase 0, ancillae 0.
//! 4. **S_0 / teardown boundaries**: `p0_shape::divide_forward` END TO END on
//!    the Simulator under the production route environment (the cut-530 path:
//!    S_0 entry with the ungated 256-wide `e_B` scan, 530 rows, the teardown's
//!    `e_cb` scan / `X(R2[0])` / `load_p`, `lambda = cb * dy` with the
//!    sign/parity fix-up, the dy ghost, `recreate_530`, 530 rows back,
//!    `exit_s0`, `dy_new = lambda * dx`): 64 random `(dx, dy)`, checks
//!    `lambda = dy * dx^-1 mod p`, `dx` and `dy` restored, phase 0 (the ghost
//!    resolves only if `dy_new = dy`), every other qubit 0. This is the first
//!    Simulator run of the packed inversion entry point (the count-only build
//!    checks allocation only; `driver_selftest.rs` builds the registers
//!    directly and never runs `enter_s0` / `teardown_530`).
//!
//! Toffoli is printed per case and compared with design section 4 (division
//! ~4.9k, multiply ~5.5k, step ~12.4k at 378; 25% tolerance asserted at the
//! band steps). Knobs: `MIDQ_REVIEW_POOL`, `MIDQ_REVIEW_SKIP_E2E=1` (skip
//! case 4), `MIDQ_REVIEW_E2E_SHOTS` (default 64).

#![allow(dead_code, clippy::too_many_arguments)]

use super::super::*;
use super::division::{division_backward, division_forward};
use super::multiply::{multiply_backward, multiply_forward};
use super::p0_shape::{backward_step, divide_cancel, divide_forward, forward_step, natural_q_width, popcount_on, terminal_from, Packed};
use super::sched::{StepWidths, EXP_BITS, RING, WINDOW};

/// The inputs of the 4M classical draw (`tools/spike/term_first.py` /
/// `term_dump.py` under R:/Coding/shor2, seeds
/// 2026 / 2027 / 2028, verbatim `pz_prefix`) whose terminal division is before
/// row 372: (terminal step, x). The first is the earliest termination seen in
/// 4M inputs (352); all lie in [FROM = 340, 372) and exercise the terminal-aware
/// rows below the design's old 365 (driver round trip (c)).
const EARLY_TERMINATORS_4M: &[(usize, &str)] = &[
    (352, "0xfe390d2d3316fabbaea583fe48cbb86c044984c8da0fcd9747bdf86e45b9fd62"),
    (356, "0x1ae98933fd4a2d75f366b08f34483899a8d01d4ed75f875fe3530020c1d167e"),
    (361, "0x4d982be45b5a9dd46ada10ce52764b70132d1b73d71b72d1d68e755dee7de2b0"),
    (362, "0x4aab30c828c9e583f852d87264f3c0b52ca60e644da380fe2eb810eebc336236"),
    (362, "0x1e2931d3233ae3c64e6f492fc64e6ddd3a847bf90a33cde1546eec1180ddb012"),
    (362, "0x3a6c6a7907f33c751c8580aec3888c6c973b31a64a6c7eee354a7e4b7145cc34"),
    (363, "0xccd963bfda178357d9bd4201e0dcfcd1fbdb63d89df282698df4fe9a13a68fb9"),
    (364, "0xb2555822aac56e55cab1fce8d347d02cb0cf32134e207113b7875c16972834e8"),
    (366, "0x1fa57cca3366cefd6f7d764d7b0788a7b45b7e16f5d8a402ccdea201e2d8da3"),
    (366, "0x1f3e776468213b576699510ffbd2174b1e38c3b9260b2b078c748131c73df576"),
    (366, "0xffc89d99cfef233ed425ff967ef6d4da7b8b48ca596cef568e704ab0d87ce8c3"),
    (366, "0xc73b11e8c2c47e5f7ff9907080257c5d324ce6668f5721a4391881708722d816"),
    (367, "0xe30546c2497f1e34067334a78ea4ba799e2f767deac95e7b2127dab3b2901003"),
    (368, "0x91ebb00e931c84901a7722a9abce2860acf0aace9e26b1ef9a6465ba4315e36d"),
    (368, "0xa05cc94c041cd189a498b239956f64f091b2ee0432bf845cb9f33f68308ab794"),
    (369, "0x2f4557dff43d327ce3e4c5ebc3f290cc0c0c4c59e2a042f9272619218718c3c7"),
    (369, "0x7b717db5d3ef7407364c408a8aff5b1cdc9b891d5302679c6605ee60381de992"),
    (369, "0x7e708173c16aedb40aa1a170bf0aee868a3fa69a126b6ae70f3268ba0ca79666"),
    (369, "0xaa17cb7e682dd383b603beed0533b82a6f8965970d5c8a81ddcf6fb8bbbc90e6"),
    (369, "0xaaab7fa6e0700e8405773768fddd3e57a209808a6219bd6c6c39b4808851dc71"),
    (370, "0x1ea6f3e16e2de8ff9835f28dd7d66dc0258b20143ccbcf93a214769064995594"),
    (370, "0x2a9890368da0ef8a50286d549d748092827a2fc91a1512dfd2398f46c0e0979a"),
    (370, "0x6e36e2c0f7f5636db07c3493dc501edbae47f36c33f3ebef72d8e53c2d283f24"),
    (370, "0x7ecd3bdf76e0fbf4cc535cce3aae8a6f41179a259859be422b503f4969c4167f"),
    (370, "0xb139ad5b39d5209720be0b73169c2899fd68c6c8515fcfb0fd5ba88db05897f9"),
    (370, "0xef7b5b6f75ba153d1ea0948bbf375aea5604210bb63a4500e3b84a3206a2493c"),
    (370, "0x1f521885b0ea289b7f00ab73a9058c62e13b723427b53d6aea66893d9b7588c7"),
    (371, "0x3f0b69999b02efac01992e74052306cc2c1a87c38ca3df6aebee51378bb67461"),
    (371, "0x49dabfc902b1700ce7b2ea07118a9eae9da37c9e9b2eab590c371f75dbafabb5"),
    (371, "0x797d5c3770758a9f3aca0bb862c882bf3732e82486c16d9ec3743d7bfc3dee55"),
    (371, "0x94316432485e076e573beb33bf9d53d7b0c4e3475dbedde98269a35682ab91a9"),
    (371, "0xb1ec1ffe74a411e48c080a5e8c84c88cae54823fdc8b4e05ca89a3f065cb7993"),
    (371, "0xe53cd1c2c72a08e1986c0ea66270e89daeee8da41dea3a27a1eaec29f7ce512c"),
    (371, "0xace99c22a362c679598130a2b1a335b483490b53ef83b3563460fd5cb25a8d22"),
    (371, "0xf3aac62b85389dbb9849d0adcf825779e287f9857ad76bb36cbeb7b5b0bbb56b"),
];
use crate::circuit::{analyze_ops, BitId, Op, OperationType, QubitId, NO_BIT};
use crate::sim::Simulator;
use ruint::aliases::U512;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};
use std::collections::{BTreeMap, BTreeSet};

const NSTEPS: usize = 530;
const SROT: usize = 5;
const WIDE1: (usize, usize) = (284, 313);
const WIDE2: (usize, usize) = (378, 413);
const ANY: (usize, usize) = (0, NSTEPS - 1);

fn prime() -> U512 {
    (U512::from(1u64) << 256) - (U512::from(1u64) << 32) - U512::from(977u64)
}

fn one() -> U512 {
    U512::from(1u64)
}

fn bl(x: &U512) -> usize {
    x.bit_len()
}

// ---------------------------------------------------------------------------
// The classical oracle (verbatim pz_prefix + the circuit's bookkeeping)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct St {
    a: U512,
    b: U512,
    ca: U512,
    cb: U512,
    q: U512,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Frozen,
    Draining,
    Mul,
    Div,
}

#[derive(Clone, Copy)]
struct Row {
    pre: St,
    kind: Kind,
    /// multiply: (s2, carry)
    mul: Option<(usize, bool)>,
    /// division: (s, off, A_new)
    div: Option<(usize, bool, U512)>,
    mid: St,
    swapped: bool,
    post: St,
    parity: bool,
    counter: usize,
}

struct Trace {
    x: U512,
    rows: Vec<Row>,
    terminal: Option<usize>,
    first_drain: Option<usize>,
}

fn trace(x_orig: U512, term_from: usize, pop: bool) -> Trace {
    let p = prime();
    let half = p >> 1;
    let x = if x_orig > half { p - x_orig } else { x_orig };
    let mut st = St { a: p, b: x, ca: U512::ZERO, cb: one(), q: U512::ZERO };
    let mut parity = true;
    let mut counter = 0usize;
    let mut rows = Vec::with_capacity(NSTEPS);
    let mut terminal = None;
    let mut first_drain = None;
    for step in 0..NSTEPS {
        let pre = st;
        if step == term_from && pop {
            counter = 0;
        }
        if st.a.is_zero() && st.b == one() && st.q.is_zero() {
            if step >= term_from {
                counter += 1;
            }
            rows.push(Row { pre, kind: Kind::Frozen, mul: None, div: None, mid: st, swapped: false, post: st, parity, counter });
            continue;
        }
        let mut mul = None;
        let mut kind = Kind::Mul;
        if st.a < st.b && !st.q.is_zero() {
            let s2 = st.q.trailing_zeros();
            st.q ^= one() << s2;
            let ca_new = st.ca + (st.cb << s2);
            let carry = bl(&ca_new) > bl(&st.cb) + s2;
            st.ca = ca_new;
            mul = Some((s2, carry));
            if pre.a.is_zero() {
                kind = Kind::Draining;
                if first_drain.is_none() {
                    first_drain = Some(step);
                }
            }
        }
        let mut div = None;
        if st.ca < st.cb {
            let s_raw = bl(&st.a) as i64 - bl(&st.b) as i64;
            if s_raw >= 0 {
                let off = st.a < (st.b << (s_raw as usize));
                let s = s_raw - i64::from(off);
                if s >= 0 {
                    let s = s as usize;
                    let bsh = st.b << s;
                    assert!(st.a >= bsh, "model: A < B << s at step {step}");
                    let a_new = st.a - bsh;
                    st.a = a_new;
                    st.q ^= one() << s;
                    div = Some((s, off, a_new));
                    kind = Kind::Div;
                    if a_new.is_zero() && terminal.is_none() {
                        terminal = Some(step);
                    }
                }
            }
        }
        assert!(mul.is_none() || div.is_none(), "both substeps fired at step {step}");
        assert!(mul.is_some() || div.is_some(), "idle row at step {step}");
        assert_eq!(div.is_some(), pre.a >= pre.b, "role rule at step {step}");
        let mid = st;
        if step < term_from {
            if pop {
                if mul.is_some() { counter -= 1 } else { counter += 1 }
            }
        } else if st.q.is_zero() && st.a.is_zero() {
            counter += 1;
        }
        let swapped = st.q.is_zero() && !st.a.is_zero();
        if swapped {
            std::mem::swap(&mut st.a, &mut st.b);
            std::mem::swap(&mut st.ca, &mut st.cb);
            parity = !parity;
        }
        rows.push(Row { pre, kind, mul, div, mid, swapped, post: st, parity, counter });
    }
    Trace { x, rows, terminal, first_drain }
}

/// Lean scan: (terminal step, first draining row) of an input, no rows kept.
fn terminal_lite(x_orig: U512) -> (Option<usize>, Option<usize>) {
    let p = prime();
    let half = p >> 1;
    let x = if x_orig > half { p - x_orig } else { x_orig };
    let (mut a, mut b, mut ca, mut cb, mut q) = (p, x, U512::ZERO, one(), U512::ZERO);
    let (mut terminal, mut first_drain) = (None, None);
    for step in 0..NSTEPS {
        if a.is_zero() && b == one() && q.is_zero() {
            break;
        }
        if a < b && !q.is_zero() {
            let s2 = q.trailing_zeros();
            q ^= one() << s2;
            ca += cb << s2;
            if a.is_zero() && first_drain.is_none() {
                first_drain = Some(step);
            }
        }
        if ca < cb {
            let s_raw = bl(&a) as i64 - bl(&b) as i64;
            if s_raw >= 0 {
                let off = a < (b << (s_raw as usize));
                let s = s_raw - i64::from(off);
                if s >= 0 {
                    let bsh = b << (s as usize);
                    a -= bsh;
                    q ^= one() << (s as usize);
                    if a.is_zero() && terminal.is_none() {
                        terminal = Some(step);
                    }
                }
            }
        }
        if q.is_zero() && !a.is_zero() {
            std::mem::swap(&mut a, &mut b);
            std::mem::swap(&mut ca, &mut cb);
        }
    }
    (terminal, first_drain)
}

/// The driver's support predicate of row `i` (verbatim the driver harness's
/// `support`; the schedule's guarantees the circuit relies on).
fn support(row: &Row, i: usize, s: &StepWidths, wq: usize, term_from: usize) -> Result<(), &'static str> {
    let pre = &row.pre;
    let (e_a, e_b, e_ca, e_cb) = (bl(&pre.a), bl(&pre.b), bl(&pre.ca), bl(&pre.cb));
    let mut checks: Vec<(bool, &'static str)> = vec![
        (e_a <= s.w_a && e_b <= s.w_a, "width_a (pre)"),
        (e_ca <= s.w_c && e_cb <= s.w_c, "width_c (pre)"),
        (bl(&pre.q) <= wq, "width_q (pre)"),
        (bl(&row.post.q) <= wq, "width_q (post)"),
        (bl(&row.post.a) <= s.w_a && bl(&row.post.b) <= s.w_a, "width_a (post)"),
        (bl(&row.post.ca) <= s.w_c && bl(&row.post.cb) <= s.w_c, "width_c (post)"),
        // the 7-bit rebased exponents: every exponent of the row inside [base, base + 127]
        (s.v_in_range(e_a) && s.v_in_range(e_b) && s.c_in_range(e_ca) && s.c_in_range(e_cb), "exp_range (pre)"),
        (
            s.v_in_range(bl(&row.post.a)) && s.v_in_range(bl(&row.post.b)) && s.c_in_range(bl(&row.post.ca)) && s.c_in_range(bl(&row.post.cb)),
            "exp_range (post)",
        ),
    ];
    if row.kind != Kind::Frozen {
        let m = e_ca.max(e_cb);
        let lo_c = s.role_compute_lo_c();
        checks.push((m >= lo_c + 1, "lo_c (role compute)"));
        checks.push((e_a.max(e_b) <= RING - m, "fit fact max(eA,eB) <= 257 - max(eca,ecb)"));
        let mp = bl(&row.mid.a).max(bl(&row.mid.b));
        let lo_v = s.role_clear_lo_v(i >= term_from);
        checks.push((mp >= lo_v + 1 && mp <= s.w_a, "lo_v (role clear)"));
        checks.push((bl(&row.mid.ca).max(bl(&row.mid.cb)) <= RING - mp, "fit fact at the step end"));
    }
    if let Some((s2, carry)) = row.mul {
        let ca_new = row.mid.ca;
        let carry_u = usize::from(carry);
        let lo_c = s.m10_cascade_lo(); // M10's cascade bottom (the tie residue window)
        let d = s2 + carry_u;
        let residue_ok = (((ca_new >> d) >> lo_c) < (pre.cb >> lo_c)) == carry;
        let gap2 = RING - e_b - e_ca;
        checks.extend([
            (residue_ok, "narrow_lt residue (M10 window tie)"),
            (e_b >= s.m1_lo_b().max(1), "lo_B (M1)"),
            (e_b <= s.w_b, "width_b (M1)"),
            (e_cb >= s.lo_cb + 1, "lo_cb (M5 zone)"),
            (bl(&ca_new) <= s.w_c, "width_c (ca_new)"),
            (bl(&ca_new) == e_cb + s2 + carry_u, "bl(ca_new) theorem"),
            (e_b + bl(&ca_new) <= RING, "e_B + bl(ca_new) > 257"),
            (pre.ca.is_zero() || gap2 < WINDOW, "gap_bound (M1)"),
            (s2 <= s.s2_bound, "s2 > bound"),
            (s2 + carry_u < (1 << SROT), "s2 + carry overflows the shift word"),
        ]);
    }
    if let Some((sd, off, a_new)) = row.div {
        let off_u = usize::from(off);
        let s_raw = sd + off_u;
        let e_a_new = bl(&a_new);
        let d = e_a - e_a_new;
        let n_w = s.div_scan_window();
        let n0 = s.div_term_window();
        let terminal = a_new.is_zero();
        let lo = s.div_cascade_lo(); // D4/D9 cascade bottom (the tie residue window)
        let win = s.div_capture_window();
        let e_e = e_b + off_u;
        let mask_e = (one() << e_b) - one();
        let v4 = (pre.a >> s_raw) >> lo;
        let u4 = pre.b >> lo;
        let residue4 = v4 == u4 && (pre.a >> s_raw) < pre.b;
        let r = a_new >> sd;
        let nb = (mask_e ^ pre.b) >> lo;
        let residue9 = nb == (r >> lo) && (mask_e ^ pre.b) < r;
        checks.extend([
            (e_b >= win.lo && e_b <= win.hi, "lo_B (D4/D9 capture window)"),
            (s.div_zone_admits(e_e), "zone (D7: E below the masked zone)"),
            (s_raw < (1usize << s.rb_div.min(SROT)), "s_raw > rotation bound"),
            (!terminal || i >= term_from, "term_row (exact division before FROM)"),
            (!terminal || sd <= n0, "term_window (s > D0 window)"),
            (terminal || d <= n_w - 1 + off_u, "drop_bound (D11)"),
            (!residue4, "D4 tie residue"),
            (!residue9, "D9 tie residue"),
        ]);
    }
    for (ok, why) in checks {
        if !ok {
            return Err(why);
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Classes and the pool search
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Metric {
    DivDrop,
    DivS,
    DivOff1D1,
    DivOff0D1,
    DivTightR1,
    DivEaEqWa,
    DivEbLo,
    DivEbEqWa,
    MulS2,
    MulGap2,
    MulCarry,
    MulTightR2,
    MulTightR1,
    MulEbLo,
    MulEbHi,
    /// `(257 - W_A) - e_cb`: how far cb's field end sits below the design's
    /// M5 zone edge `257 - W_A` (>= 0: the row needs the `lo_cb + 1` clamp of
    /// `StepWidths::mul_zone_start`, else the toggle leaf is never visited).
    MulEcbBelowZone,
}

impl Metric {
    fn is_div(self) -> bool {
        matches!(
            self,
            Metric::DivDrop | Metric::DivS | Metric::DivOff1D1 | Metric::DivOff0D1 | Metric::DivTightR1 | Metric::DivEaEqWa | Metric::DivEbLo | Metric::DivEbEqWa
        )
    }
}

#[derive(Clone, Copy, Debug)]
struct Class {
    name: &'static str,
    metric: Metric,
    lo: usize,
    hi: usize,
}

fn classes() -> Vec<Class> {
    let all = [
        (Metric::DivDrop, "div_drop_max"),
        (Metric::DivS, "div_s_max"),
        (Metric::DivOff1D1, "div_off1_d1"),
        (Metric::DivOff0D1, "div_off0_d1"),
        (Metric::DivTightR1, "div_r1_gap0"),
        (Metric::DivEaEqWa, "div_eA_eq_WA"),
        (Metric::DivEbLo, "div_eB_eq_loB+1"),
        (Metric::DivEbEqWa, "div_eB_eq_WA"),
        (Metric::MulS2, "mul_s2_max"),
        (Metric::MulGap2, "mul_r2_gap_max"),
        (Metric::MulCarry, "mul_carry1"),
        (Metric::MulTightR2, "mul_tight_r2_absorb_is_B_msb"),
        (Metric::MulTightR1, "mul_r1_gap0"),
        (Metric::MulEbLo, "mul_eB_eq_loB+1"),
        (Metric::MulEbHi, "mul_eB_eq_WB"),
        (Metric::MulEcbBelowZone, "mul_ecb_vs_257-WA"),
    ];
    let mut v = Vec::new();
    for (band, (lo, hi)) in [("w1", WIDE1), ("w2", WIDE2)] {
        for (m, n) in all {
            v.push(Class { name: Box::leak(format!("{n}@{band}").into_boxed_str()), metric: m, lo, hi });
        }
    }
    for (m, n) in [(Metric::DivDrop, "div_drop_max"), (Metric::DivS, "div_s_max"), (Metric::MulS2, "mul_s2_max"), (Metric::MulGap2, "mul_r2_gap_max"), (Metric::MulEcbBelowZone, "mul_ecb_vs_257-WA")] {
        v.push(Class { name: Box::leak(format!("{n}@any").into_boxed_str()), metric: m, lo: ANY.0, hi: ANY.1 });
    }
    v
}

/// Score of a row for a metric (higher = more extreme), `None` when the row
/// is not of the metric's kind.
fn score(m: Metric, row: &Row, s: &StepWidths) -> Option<i64> {
    let pre = &row.pre;
    let (e_a, e_b, e_ca, e_cb) = (bl(&pre.a), bl(&pre.b), bl(&pre.ca), bl(&pre.cb));
    if m.is_div() {
        let (sd, off, a_new) = row.div?;
        if a_new.is_zero() {
            return None; // terminal rows: the override, not the scan
        }
        let d = e_a - bl(&a_new);
        Some(match m {
            Metric::DivDrop => d as i64,
            Metric::DivS => sd as i64,
            Metric::DivOff1D1 => return (off && d == 1).then_some(1),
            Metric::DivOff0D1 => return (!off && d == 1).then_some(1),
            Metric::DivTightR1 => return (e_a + e_cb == RING).then_some(1),
            Metric::DivEaEqWa => return (e_a == s.w_a).then_some(if off { 1 } else { 2 }),
            Metric::DivEbLo => 64 - (e_b as i64 - s.lo_b as i64 - 1),
            Metric::DivEbEqWa => return (e_b == s.w_a).then_some(1),
            _ => unreachable!(),
        })
    } else {
        let (s2, carry) = row.mul?;
        Some(match m {
            Metric::MulS2 => s2 as i64,
            Metric::MulGap2 => return (!pre.ca.is_zero()).then_some((RING - e_b - e_ca) as i64),
            Metric::MulCarry => return carry.then_some(1),
            Metric::MulTightR2 => return (e_b + s2 + e_cb == RING).then_some(1),
            Metric::MulTightR1 => return (e_a + e_cb == RING).then_some(1),
            Metric::MulEbLo => 64 - (e_b as i64 - s.m1_lo_b() as i64 - 1),
            Metric::MulEbHi => return (e_b == s.w_b).then_some(1),
            Metric::MulEcbBelowZone => (RING as i64 - s.w_a as i64) - e_cb as i64,
            _ => unreachable!(),
        })
    }
}

#[derive(Clone)]
struct Summary {
    idx: usize,
    x_orig: U512,
    terminal: Option<usize>,
    first_drain: Option<usize>,
    /// the first row whose support predicate fails (the prefilter's verdict)
    first_miss: Option<(usize, &'static str)>,
    /// per class: best (score, step)
    best: Vec<Option<(i64, usize)>>,
}

fn random_inputs(n: usize, tag: &[u8]) -> Vec<U512> {
    let mut seed = Shake256::default();
    seed.update(tag);
    let mut xof = seed.finalize_xof();
    let p = prime();
    (0..n)
        .map(|_| {
            let mut bytes = [0u8; 64];
            xof.read(&mut bytes[..32]);
            let x = U512::from_le_bytes(bytes) % p;
            if x.is_zero() { one() } else { x }
        })
        .collect()
}

fn summarize(idx: usize, x_orig: U512, t: &Trace, cls: &[Class], sw: &[StepWidths], wq_of: &[usize], term_from: usize) -> Summary {
    let mut best = vec![None; cls.len()];
    let first_miss = (0..NSTEPS).find_map(|i| support(&t.rows[i], i, &sw[i], wq_of[i], term_from).err().map(|k| (i, k)));
    for (i, row) in t.rows.iter().enumerate() {
        for (k, c) in cls.iter().enumerate() {
            if i < c.lo || i > c.hi {
                continue;
            }
            if let Some(v) = score(c.metric, row, &sw[i]) {
                if best[k].map_or(true, |(b, _)| v > b) {
                    best[k] = Some((v, i));
                }
            }
        }
    }
    Summary { idx, x_orig, terminal: t.terminal, first_drain: t.first_drain, first_miss, best }
}

// ---------------------------------------------------------------------------
// Register images
// ---------------------------------------------------------------------------

fn ring_lsb(value: &U512, coef: &U512) -> Vec<bool> {
    assert!(bl(value) + bl(coef) <= RING, "packing invariant");
    (0..RING).map(|w| value.bit(w) || coef.bit(RING - 1 - w)).collect()
}

fn bits_of(v: usize, n: usize) -> Vec<bool> {
    (0..n).map(|i| (v >> i) & 1 == 1).collect()
}

fn bits_u512(v: &U512, n: usize) -> Vec<bool> {
    (0..n).map(|i| v.bit(i)).collect()
}

/// Substep harness data wires: r1 | r2 | ex1 | ex2 | q | s_rot | off | gate | term.
fn sub_state(s: &StepWidths, st: &St, wq: usize, gate: bool) -> Vec<bool> {
    let mut v = ring_lsb(&st.a, &st.cb);
    v.extend(ring_lsb(&st.b, &st.ca));
    // the exponents in the row's rebased frame (sched.rs: e - base mod 2^7)
    v.extend(bits_of(s.reb_v(bl(&st.a)), EXP_BITS));
    v.extend(bits_of(s.reb_c(bl(&st.cb)), EXP_BITS));
    v.extend(bits_of(s.reb_v(bl(&st.b)), EXP_BITS));
    v.extend(bits_of(s.reb_c(bl(&st.ca)), EXP_BITS));
    assert!(bl(&st.q) <= wq, "q wider than its register");
    v.extend(bits_u512(&st.q, wq));
    v.extend(bits_of(0, SROT));
    v.push(false); // off
    v.push(gate);
    v.push(false); // term
    v
}

fn sub_wire_name(k: usize, wq: usize) -> String {
    let mut k = k;
    for (name, n) in [("r1", RING), ("r2", RING), ("eA", EXP_BITS), ("ecb", EXP_BITS), ("eB", EXP_BITS), ("eca", EXP_BITS), ("q", wq), ("srot", SROT), ("off", 1), ("gate", 1), ("term", 1)] {
        if k < n {
            return format!("{name}[{k}]");
        }
        k -= n;
    }
    "?".to_string()
}

/// Driver harness data wires: r1 | r2 | ex1 | ex2 | q | counter | s_rot | off | parity.
fn drv_expected(s: &StepWidths, st: &St, wq: usize, nctr: usize, parity: bool, counter: usize) -> Vec<bool> {
    let mut v = ring_lsb(&st.a, &st.cb);
    v.extend(ring_lsb(&st.b, &st.ca));
    v.extend(bits_of(s.reb_v(bl(&st.a)), EXP_BITS));
    v.extend(bits_of(s.reb_c(bl(&st.cb)), EXP_BITS));
    v.extend(bits_of(s.reb_v(bl(&st.b)), EXP_BITS));
    v.extend(bits_of(s.reb_c(bl(&st.ca)), EXP_BITS));
    assert!(bl(&st.q) <= wq, "q wider than its register");
    v.extend(bits_u512(&st.q, wq));
    v.extend(bits_of(counter, nctr));
    v.extend(bits_of(0, SROT));
    v.push(false);
    v.push(parity);
    v
}

fn drv_data_ids(p: &Packed) -> Vec<QubitId> {
    let mut ids: Vec<QubitId> = Vec::new();
    for reg in [&p.r1, &p.r2, &p.ex1, &p.ex2, &p.q, &p.counter, &p.s_rot] {
        ids.extend(reg.iter().map(|q| QubitId(q.id().into())));
    }
    ids.push(QubitId(p.off.as_ref().expect("off").id().into()));
    ids.push(QubitId(p.parity.as_deref().expect("parity").id().into()));
    ids
}

fn drv_wire_name(k: usize, wq: usize, nctr: usize) -> String {
    let mut k = k;
    for (name, n) in [("r1", RING), ("r2", RING), ("eA", EXP_BITS), ("ecb", EXP_BITS), ("eB", EXP_BITS), ("eca", EXP_BITS), ("q", wq), ("counter", nctr), ("srot", SROT), ("off", 1), ("parity", 1)] {
        if k < n {
            return format!("{name}[{k}]");
        }
        k -= n;
    }
    "?".to_string()
}

// ---------------------------------------------------------------------------
// Simulation helpers
// ---------------------------------------------------------------------------

fn toffoli(ops: &[Op]) -> usize {
    ops.iter().filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count()
}

/// Apply `ops` to a growing simulator with reset checks (the driver harness's
/// `apply_chunk`).
fn apply_growing<R: XofReader>(sim: &mut Simulator<'_, R>, ops: &[Op], transitions: &[(usize, &'static str)], live: u64, where_: &str) {
    let (nq, nb, _, _) = analyze_ops(ops.iter());
    let nq = nq as usize;
    let nb = nb as usize + 1;
    if nq > sim.num_qubits {
        sim.qubits.resize(nq, 0);
        sim.num_qubits = nq;
    }
    if nb > sim.num_bits {
        sim.bits.resize(nb, 0);
        sim.num_bits = nb;
    }
    let scratch_bit = BitId((sim.num_bits - 1) as u64);
    sim.bits[scratch_bit.0 as usize] = 0;
    let mut push = Op::empty();
    push.kind = OperationType::PushCondition;
    push.c_condition = scratch_bit;
    let mut pop = Op::empty();
    pop.kind = OperationType::PopCondition;
    let mut stack = Vec::new();
    let mut mask = u64::MAX;
    for (k, op) in ops.iter().enumerate() {
        match op.kind {
            OperationType::PushCondition => {
                stack.push(mask);
                mask &= sim.bit(op.c_condition);
            }
            OperationType::PopCondition => mask = stack.pop().expect("balanced condition"),
            _ => {
                let cond = mask & if op.c_condition == NO_BIT { u64::MAX } else { sim.bit(op.c_condition) };
                if op.kind == OperationType::R {
                    let dirty = sim.qubit(op.q_target) & cond & live;
                    if dirty != 0 {
                        let phase = transitions.iter().rev().find(|(idx, _)| *idx <= k).map_or("?", |(_, ph)| ph);
                        panic!("{where_}: dirty reset of qubit {} at op {k} (shots {dirty:#x}) in section {phase}", op.q_target.0);
                    }
                }
                *sim.bit_mut(scratch_bit) = mask;
                sim.apply_iter([&push, op, &pop].into_iter());
            }
        }
    }
    assert!(stack.is_empty());
}

fn snapshot<R: XofReader>(sim: &Simulator<'_, R>, ids: &[QubitId]) -> Vec<u64> {
    ids.iter().map(|&id| sim.qubit(id)).collect()
}

fn shot_bits(snap: &[u64], shot: usize) -> Vec<bool> {
    snap.iter().map(|w| (w >> shot) & 1 == 1).collect()
}

fn assert_ancillae_clean<R: XofReader>(sim: &Simulator<'_, R>, ids: &[QubitId], live: u64, where_: &str) {
    let data: std::collections::HashSet<u64> = ids.iter().map(|q| q.0).collect();
    for (k, &v) in sim.qubits.iter().enumerate() {
        if !data.contains(&(k as u64)) {
            assert_eq!(v & live, 0, "{where_}: qubit {k} dirty (shots {:#x})", v & live);
        }
    }
}

struct EnvSnapshot(Vec<(std::ffi::OsString, std::ffi::OsString)>);

impl EnvSnapshot {
    fn take() -> Self {
        Self(std::env::vars_os().collect())
    }
    fn restore(&self) {
        for (k, _) in std::env::vars_os() {
            if !self.0.iter().any(|(sk, _)| *sk == k) {
                std::env::remove_var(&k);
            }
        }
        for (k, v) in &self.0 {
            std::env::set_var(k, v);
        }
    }
}

/// The driver harness's production configuration (`driver_selftest.rs`):
/// the thin schedule (seed 278, 500k validation draws), 5-bit shift, 8-bit
/// counter, the measured demux / gate / predicate clears, popcount cache,
/// terminal rows from 365.
fn packed_env() {
    std::env::set_var("TRAILMIX_THIN_SCHEDULE", "1");
    std::env::set_var("TRAILMIX_THIN_SEED", "278");
    std::env::set_var("TRAILMIX_THIN_MARGIN", "0");
    let validate = std::env::var("MIDQ_DRIVER_SELFTEST_VALIDATE").unwrap_or_else(|_| "500000".to_string());
    std::env::set_var("TRAILMIX_THIN_VALIDATE", validate);
    std::env::set_var("TRAILMIX_THIN_CLZ_WINDOW", "78");
    std::env::set_var("TRAILMIX_SROT_W", "5");
    std::env::set_var("TRAILMIX_COUNTER_W", "8");
    std::env::set_var("MIDQ_MEASURED_DEMUX", "1");
    std::env::set_var("LOWQ_COMPACT_KGANC", "1");
    std::env::set_var("LOWQ_ONE_A_ELIM", "1");
    std::env::set_var("TRAILMIX_Q_TARGET", "685");
    std::env::set_var("MIDQ_MEASURE_GATE_AND", "1");
    std::env::set_var("MIDQ_MEASURE_PREDICATE", "1");
    std::env::set_var("MIDQ_CHUNKED_PREDICATE", "1");
    std::env::set_var("MIDQ_PREFIX_POPCOUNT", "1");
    std::env::set_var("MIDQ_PZ_PINGPONG_TAIL", "0");
    std::env::set_var("MIDQ_PREFIX_TERMINAL_FROM", super::p0_shape::DEFAULT_TERMINAL_FROM.to_string());
    std::env::set_var("MIDQ_PACKED_PREFIX", "1");
    for k in ["MIDQ_PACKED_STUBS", "MIDQ_ONEHOT_COHERENT", "MIDQ_PACKED_CTZ_ROOM", "MIDQ_PACKED_QCAP", "MIDQ_P0_TRACE", "MIDQ_TRACE_PZ_STEPS", "TRACE_PHASE_ACTIVE", "MIDQ_PREFIX_NO_TERMINAL", "MIDQ_PREFIX_QCAP", "MIDQ_KG_ZERO_LAYER", "MIDQ_CHUNKED_PREFIX"] {
        std::env::remove_var(k);
    }
}

/// The shipped route's defaults (`trailmix_port::configure_sub1000_trailmix_route`,
/// private there; copied 2026-09-14 so the end-to-end case runs the packed
/// inversion under the production environment of the 530 count build), with
/// the cut-530 packed overrides applied after.
fn route_env_defaults() {
    fn d(name: &str, value: &str) {
        if std::env::var_os(name).is_none() {
            std::env::set_var(name, value);
        }
    }
    for (k, v) in [
        ("TRAILMIX_THIN_SCHEDULE", "1"), ("TRAILMIX_THIN_SEED", "278"), ("TRAILMIX_THIN_CLZ_WINDOW", "78"), ("TRAILMIX_THIN_MARGIN", "0"),
        ("TRAILMIX_THIN_VALIDATE", "500000"), ("TRAILMIX_COUNTER_W", "8"), ("TRAILMIX_Q_CAP", "22"), ("TRAILMIX_Q_TARGET", "685"),
        ("LOWQ_CLZ_DIFF_CONST_FOLD", "1"), ("LOWQ_ONE_A_ELIM", "1"), ("LOWQ_HYBRID_GATE_HOLD", "1"), ("LOWQ_HYBRID_CACHE_CTZ", "1"),
        ("LOWQ_HYBRID_INPLACE_CTZ", "1"), ("LOWQ_BORROW_PASSENGER_CARRY", "1"), ("LOWQ_COMPACT_KGANC", "1"), ("TRAILMIX_FUSE_DIV_CLZ_A", "1"),
        ("TRAILMIX_SROT_W", "5"), ("TRAILMIX_DEFER_Y_MATERIALIZE", "1"), ("TRAILMIX_ZERO_DY_NEWDX_ROUTE", "1"), ("MIDQ_PZ_PINGPONG_TAIL", "1"),
        ("MIDQ_CHECKPOINT_CAP_AWARE", "1"), ("MIDQ_PREFIX_NO_TERMINAL", "1"), ("MIDQ_PREFIX_POPCOUNT", "1"), ("MIDQ_TAIL_TOP_COMPARE", "1"),
        ("MIDQ_TAIL_INVERSE_TOP_COMPARE", "1"), ("MIDQ_FUSED_ROTATION_CELL", "1"), ("MIDQ_DIRECT_CTZ", "1"), ("MIDQ_SYMBOLIC_CLEAN_AND", "1"),
        ("MIDQ_SYMBOLIC_RESIDUAL", "1"), ("MIDQ_PAYLOAD_VALUE_REPLAY_START", "180"), ("MIDQ_FUSE_MUL_CLZ", "1"), ("MIDQ_RELEASE_PZ_SCRATCH", "1"),
        ("MIDQ_CLZ_OFFSET_PARITY", "1"), ("MIDQ_MEASURE_COMPARE", "1"), ("MIDQ_DIRTY_CONST", "1"), ("MIDQ_RETAIN_DIV_LENGTHS", "1"),
        ("MIDQ_RETAIN_MUL_LENGTHS", "1"), ("MIDQ_DIRTY_FIELD_NEG", "1"), ("MIDQ_MEASURE_PREDICATE", "1"), ("MIDQ_MEASURE_GATE_AND", "1"),
        ("MIDQ_OUTER_DIRTY_CONST", "1"), ("MIDQ_TAIL_CHECKPOINT", "1"), ("MIDQ_OUTER_VENT_QCAP", "974"), ("MIDQ_PZ_VENT_QCAP", "974"),
        ("MIDQ_COMPACT_CONST_CARRY", "1"), ("MIDQ_QUOTIENT_CODE", "1"), ("MIDQ_CHUNKED_PREFIX", "1"), ("MIDQ_PREFIX_QCAP", "974"),
        ("MIDQ_CHUNK_COMPARE", "1"), ("MIDQ_CHUNK_COMPARE_QCAP", "974"), ("MIDQ_COUNTER_TAPE", "1"), ("MIDQ_EXACT_BOOLEAN", "1"),
        ("MIDQ_EXACT_BOOLEAN_ALIASES", "1"), ("MIDQ_VARIABLE_CHUNKS", "1"), ("MIDQ_CHUNKED_PREDICATE", "1"), ("MIDQ_MEASURED_DEMUX", "1"),
        ("MIDQ_MEASURED_OUTER_PHASE", "1"), ("MIDQ_CHUNKED_CONTROLLED_ADD", "1"), ("MIDQ_CONTROLLED_ADD_QCAP", "974"), ("MIDQ_CELL_FOLDS", "1"),
        ("MIDQ_CELL_SUM", "1"), ("MIDQ_ALL_CONST_FOLDS", "1"), ("MIDQ_CELL_QCAP", "974"), ("MIDQ_NARROW_COEFFICIENTS", "1"),
        ("MIDQ_PARK_CHECKPOINT_SELECTORS", "1"), ("MIDQ_TAIL_METADATA_CODEC", "1"), ("MIDQ_PACK_PZ_PARITY", "1"), ("MIDQ_ZERO_SCRATCH_NEG", "1"),
        ("MIDQ_ZERO_SCRATCH_QCAP", "974"), ("MIDQ_PAYLOAD_SIGN_LOAN", "1"), ("MIDQ_ROTATED_HALVES", "1"), ("MIDQ_DIRTY_CHECKPOINT_LOOKUP", "1"),
        ("MIDQ_INPLACE_CHECKPOINT_SIGN", "1"), ("MIDQ_INPLACE_ENDPOINT_SIGNS", "1"), ("MIDQ_PASSENGER_PADDING", "1"), ("MIDQ_CELL_RECURSIVE_CARRY", "1"),
        ("MIDQ_ODD_VALUES", "1"), ("MIDQ_CELL_COST_SELECT", "1"), ("MIDQ_SIX_BIT_CHECKPOINT", "1"), ("MIDQ_VALUE_PADDING_LOAN", "1"),
        ("MIDQ_CONTROLLED_ADD_RECURSIVE", "1"), ("CANCEL_DISJOINT_COMMUTING_TOFFOLI", "1"), ("CANCEL_XFAMILY_COMMUTING_TOFFOLI", "1"),
        ("TRAILMIX_TAIL_NONCE", "115378"), ("MIDQ_PACKED_PREFIX", "1"),
    ] {
        d(k, v);
    }
    // the packed 530 point
    std::env::set_var("MIDQ_PZ_PINGPONG_TAIL", "0");
    std::env::set_var("MIDQ_PACKED_PREFIX", "1");
    std::env::set_var("MIDQ_PREFIX_TERMINAL_FROM", super::p0_shape::DEFAULT_TERMINAL_FROM.to_string());
    for k in ["MIDQ_PACKED_STUBS", "MIDQ_P0_TRACE", "MIDQ_TRACE_PZ_STEPS", "TRACE_PHASE_ACTIVE", "TRACE_PEAK", "POINT_ADD_COUNT_ONLY"] {
        std::env::remove_var(k);
    }
}

// ---------------------------------------------------------------------------
// 2. Substep cases
// ---------------------------------------------------------------------------

struct SubHarness {
    ops: Vec<Op>,
    ids: Vec<QubitId>,
    t: usize,
}

fn sub_ids(regs: &[&[QReg]]) -> Vec<QubitId> {
    regs.iter().flat_map(|r| r.iter().map(|q| QubitId(q.id().into()))).collect()
}

fn build_sub(sched: &StepWidths, wq: usize, div: bool, with_term: bool, inverse: bool) -> SubHarness {
    let mut c = Circuit::new();
    let r1 = c.alloc_qreg_bits("r1", RING);
    let r2 = c.alloc_qreg_bits("r2", RING);
    let ex1 = c.alloc_qreg_bits("ex1", 2 * EXP_BITS);
    let ex2 = c.alloc_qreg_bits("ex2", 2 * EXP_BITS);
    let q = c.alloc_qreg_bits("q", wq);
    let s_rot = c.alloc_qreg_bits("srot", SROT);
    let off = c.alloc_qreg("off");
    let gate = c.alloc_qreg("gate");
    let term = c.alloc_qreg("term");
    let ids = sub_ids(&[&r1, &r2, &ex1, &ex2, &q, &s_rot, std::slice::from_ref(&off), std::slice::from_ref(&gate), std::slice::from_ref(&term)]);
    // the production room for the ctz kernels: data + 12 (design: 866 - 854)
    c.flush_pending_frees();
    std::env::set_var("MIDQ_PACKED_CTZ_ROOM", "12");
    std::env::set_var("MIDQ_KG_ZERO_LAYER", "1");
    std::env::set_var("MIDQ_CHUNKED_PREFIX", "0");
    let start = c.b.ops.len();
    if div {
        let t = with_term.then_some(&term);
        if inverse {
            division_backward(&mut c, &r1, &r2, &ex1, &ex2, &q, &s_rot, &off, &gate, t, sched.step, sched);
        } else {
            division_forward(&mut c, &r1, &r2, &ex1, &ex2, &q, &s_rot, &off, &gate, t, sched.step, sched);
        }
    } else if inverse {
        multiply_backward(&mut c, &r1, &r2, &ex1, &ex2, &q, &s_rot, &off, &gate, sched.step, sched);
    } else {
        multiply_forward(&mut c, &r1, &r2, &ex1, &ex2, &q, &s_rot, &off, &gate, sched.step, sched);
    }
    for k in ["MIDQ_PACKED_CTZ_ROOM", "MIDQ_KG_ZERO_LAYER", "MIDQ_CHUNKED_PREFIX"] {
        std::env::remove_var(k);
    }
    let t = toffoli(&c.b.ops[start..]);
    SubHarness { ops: c.b.ops.clone(), ids, t }
}

fn simulate_sub(h: &SubHarness, shots: &[Vec<bool>], label: &str) -> Vec<Vec<bool>> {
    assert!(!shots.is_empty() && shots.len() <= 64);
    let (nq, nb, _, _) = analyze_ops(h.ops.iter());
    let mut seed = Shake256::default();
    seed.update(b"packed-review-sub-v1");
    seed.update(label.as_bytes());
    let mut rng = seed.finalize_xof();
    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
    for (shot, data) in shots.iter().enumerate() {
        assert_eq!(data.len(), h.ids.len(), "{label}: data width");
        for (i, &id) in h.ids.iter().enumerate() {
            if data[i] {
                *sim.qubit_mut(id) |= 1u64 << shot;
            }
        }
    }
    let mask = u64::MAX >> (64 - shots.len());
    super::super::predicate_clear_selftest::checked_apply(&mut sim, &h.ops, mask);
    assert_eq!(sim.phase & mask, 0, "{label}: phase");
    let out: Vec<Vec<bool>> = (0..shots.len()).map(|shot| h.ids.iter().map(|&id| (sim.qubit(id) >> shot) & 1 == 1).collect()).collect();
    for &id in &h.ids {
        *sim.qubit_mut(id) = 0;
    }
    assert!(sim.qubits.iter().all(|&q| q & mask == 0), "{label}: dirty ancilla");
    out
}

struct SubCase {
    class: &'static str,
    input: usize,
    step: usize,
    /// narrowed envelope (synthetic geometry), else the schedule's row
    sched: StepWidths,
    synthetic: bool,
}

/// One substep case: forward on the row's state (value checked when the row
/// is on the support), then the inverse on the outputs restores the state.
/// Returns (kind, on_support, T fwd, T inv, description).
fn run_sub_case(case: &SubCase, t: &Trace, term_from: usize) -> (Kind, Result<(), &'static str>, usize, usize, String) {
    let row = &t.rows[case.step];
    let s = &case.sched;
    let wq = natural_q_width(case.step).max(bl(&row.pre.q)).max(bl(&row.post.q)).clamp(1, 1 << SROT);
    let div = row.kind == Kind::Div;
    let with_term = case.step >= term_from;
    let on_support = support(row, case.step, s, wq, term_from);
    let (e_a, e_b, e_ca, e_cb) = (bl(&row.pre.a), bl(&row.pre.b), bl(&row.pre.ca), bl(&row.pre.cb));
    let desc = if div {
        let (sd, off, a_new) = row.div.unwrap();
        format!(
            "DIV step {} eA {e_a} eB {e_b} eca {e_ca} ecb {e_cb} s {sd} off {} d {} r1gap {} W_A {} W_c {} lo_B {} rb {} zone {} n_w {}",
            case.step, u8::from(off), e_a - bl(&a_new), RING - e_a - e_cb, s.w_a, s.w_c, s.lo_b, s.rb_div, s.div_zone_start(), s.div_scan_window()
        )
    } else {
        let (s2, carry) = row.mul.unwrap();
        format!(
            "MUL step {} eA {e_a} eB {e_b} eca {e_ca} ecb {e_cb} s2 {s2} carry {} r2gap {} r1gap {} W_A {} W_B {} W_c {} lo_B(m1) {} lo_cb {} zone {} rb {}",
            case.step, u8::from(carry), if row.pre.ca.is_zero() { 999 } else { RING - e_b - e_ca }, RING - e_a - e_cb, s.w_a, s.w_b, s.w_c, s.m1_lo_b(), s.lo_cb, s.mul_zone_start(), s.rb_mul
        )
    };
    let data = sub_state(s, &row.pre, wq, true);
    // expected: the mid state (after the substep, before the swap), s_rot/off/term 0
    let mut expect = sub_state(s, &row.mid, wq, true);
    let _ = &mut expect;
    let fwd = build_sub(s, wq, div, with_term, false);
    let inv = build_sub(s, wq, div, with_term, true);
    let label = format!("{}-{}-{}", case.class, case.input, case.step);
    let out = simulate_sub(&fwd, std::slice::from_ref(&data), &format!("{label}-fwd"));
    if on_support.is_ok() && out[0] != expect {
        let first = out[0].iter().zip(&expect).position(|(a, b)| a != b).unwrap();
        panic!("REVIEW {label}: forward differs from the oracle at wire {first} = {} ({desc})", sub_wire_name(first, wq));
    }
    let back = simulate_sub(&inv, &out, &format!("{label}-inv"));
    assert_eq!(back[0], data, "REVIEW {label}: inverse does not restore the input ({desc})");
    (row.kind, on_support, fwd.t, inv.t, desc)
}

// ---------------------------------------------------------------------------
// 3. Driver round trip on chosen inputs
// ---------------------------------------------------------------------------

fn driver_round_trip(inputs: &[U512], label: &str, term_from: usize) -> (usize, usize, Vec<usize>) {
    assert!(!inputs.is_empty() && inputs.len() <= 64);
    let t0 = std::time::Instant::now();
    let mut c = Circuit::new();
    let r1 = c.alloc_qreg_bits("pk.R1", RING);
    let r2 = c.alloc_qreg_bits("pk.R2", RING);
    let mut ex1 = c.alloc_qreg_bits("pk.eA", EXP_BITS);
    ex1.extend(c.alloc_qreg_bits("pk.ecb", EXP_BITS));
    let mut ex2 = c.alloc_qreg_bits("pk.eB", EXP_BITS);
    ex2.extend(c.alloc_qreg_bits("pk.eca", EXP_BITS));
    let q = c.alloc_qreg_bits("pk.q", natural_q_width(0));
    let s_rot = c.alloc_qreg_bits("pk.srot", trailmix_srot_width());
    let off = Some(c.alloc_qreg("pk.off"));
    let parity_q = c.alloc_qreg("pk.par");
    let counter = c.alloc_qreg_bits("pk.ctr", trailmix_counter_width());
    let mut p = Packed { r1, r2, ex1, ex2, q, counter, s_rot, off, parity: Some(BorrowedQReg::Owned(parity_q)) };
    let nctr = p.counter.len();
    let pop = popcount_on(&p.counter);
    assert_eq!(p.s_rot.len(), SROT);
    let traces: Vec<Trace> = inputs.iter().map(|&x| trace(x, term_from, pop)).collect();
    let wq_of: Vec<usize> = (0..NSTEPS).map(natural_q_width).collect();
    let sw: Vec<StepWidths> = (0..NSTEPS).map(StepWidths::from_schedule).collect();
    let first_miss: Vec<Option<(usize, &'static str)>> = traces
        .iter()
        .map(|t| (0..NSTEPS).find_map(|i| support(&t.rows[i], i, &sw[i], wq_of[i], term_from).err().map(|k| (i, k))))
        .collect();
    let ninputs = inputs.len();
    if label.starts_with("early-terminators") {
        for (j, (t, fm)) in traces.iter().zip(&first_miss).enumerate() {
            let frozen = t.rows.iter().position(|r| r.kind == Kind::Frozen);
            eprintln!("REVIEW driver [{label}] input {j} ({:#x}): terminal {:?} first draining {:?} frozen {:?} first miss {:?}", t.x, t.terminal, t.rows.iter().position(|r| r.kind == Kind::Draining), frozen, fm);
        }
    }
    let all: u64 = if ninputs == 64 { u64::MAX } else { (1u64 << ninputs) - 1 };
    // an input is live (reset / phase / ancilla checked) until its first support
    // miss: from there its state is garbage that the prefilter rejects
    let live_at = |i: usize| -> u64 {
        let mut m = all;
        for (j, fm) in first_miss.iter().enumerate() {
            if fm.map_or(false, |(r, _)| r <= i) {
                m &= !(1u64 << j);
            }
        }
        m
    };
    let live_all = live_at(NSTEPS);
    let mut seed = Shake256::default();
    seed.update(b"packed-review-driver-v1");
    seed.update(label.as_bytes());
    let mut rng = seed.finalize_xof();
    let mut sim = Simulator::new(1, 2, &mut rng);
    let s0_ids = drv_data_ids(&p);
    {
        let nq = s0_ids.iter().map(|q| q.0 as usize + 1).max().unwrap();
        sim.qubits.resize(nq, 0);
        sim.num_qubits = nq;
        for (j, t) in traces.iter().enumerate() {
            let st = St { a: prime(), b: t.x, ca: U512::ZERO, cb: one(), q: U512::ZERO };
            let bits = drv_expected(&StepWidths::from_schedule(0), &st, p.q.len(), nctr, true, 0);
            for (k, &id) in s0_ids.iter().enumerate() {
                if bits[k] {
                    *sim.qubit_mut(id) |= 1u64 << j;
                }
            }
        }
    }
    let s0_snap = snapshot(&sim, &s0_ids);
    let mut snaps: Vec<(Vec<QubitId>, Vec<u64>)> = Vec::with_capacity(NSTEPS);
    let mut t_fwd = vec![0usize; NSTEPS];
    let mut checked = 0usize;
    let (mut chk_drain, mut chk_frozen, mut chk_term) = (0usize, 0usize, 0usize);
    let mut chk_at_365 = (0usize, 0usize, 0usize); // (draining, frozen, terminal-division) rows checked AT row 365
    for i in 0..NSTEPS {
        let live = live_at(i);
        let start = c.b.ops.len();
        t_fwd[i] = forward_step(&mut c, &mut p, i);
        let ops: Vec<Op> = c.b.ops.drain(start..).collect();
        let transitions: Vec<(usize, &'static str)> = c.b.phase_transitions.drain(..).collect();
        apply_growing(&mut sim, &ops, &transitions, live, &format!("{label} forward row {i}"));
        assert_eq!(sim.phase & live, 0, "{label} forward row {i}: phase");
        let ids = drv_data_ids(&p);
        assert_ancillae_clean(&sim, &ids, live, &format!("{label} forward row {i}"));
        let snap = snapshot(&sim, &ids);
        let wq = p.q.len();
        for (j, t) in traces.iter().enumerate() {
            if first_miss[j].map_or(false, |(m, _)| i >= m) {
                continue;
            }
            let row = &t.rows[i];
            let want = drv_expected(&StepWidths::from_schedule(i), &row.post, wq, nctr, row.parity, row.counter);
            let got = shot_bits(&snap, j);
            if got != want {
                let k = got.iter().zip(&want).position(|(a, b)| a != b).unwrap();
                panic!(
                    "REVIEW {label}: forward row {i} input {j} ({:#x}, kind {:?}, terminal {:?}): first differing wire {k} = {} (got {}, want {})",
                    t.x, row.kind, t.terminal, drv_wire_name(k, wq, nctr), got[k], want[k]
                );
            }
            checked += 1;
            match row.kind {
                Kind::Draining => chk_drain += 1,
                Kind::Frozen => chk_frozen += 1,
                Kind::Div if row.div.map_or(false, |(_, _, a)| a.is_zero()) => chk_term += 1,
                _ => {}
            }
            if i == term_from {
                match row.kind {
                    Kind::Draining => chk_at_365.0 += 1,
                    Kind::Frozen => chk_at_365.1 += 1,
                    Kind::Div if row.div.map_or(false, |(_, _, a)| a.is_zero()) => chk_at_365.2 += 1,
                    _ => {}
                }
            }
        }
        snaps.push((ids, snap));
    }
    let mut t_bwd = vec![0usize; NSTEPS];
    let live = live_all;
    for i in (0..NSTEPS).rev() {
        let start = c.b.ops.len();
        t_bwd[i] = backward_step(&mut c, &mut p, i);
        let ops: Vec<Op> = c.b.ops.drain(start..).collect();
        let transitions: Vec<(usize, &'static str)> = c.b.phase_transitions.drain(..).collect();
        apply_growing(&mut sim, &ops, &transitions, live, &format!("{label} backward row {i}"));
        assert_eq!(sim.phase & live, 0, "{label} backward row {i}: phase");
        let ids = drv_data_ids(&p);
        assert_ancillae_clean(&sim, &ids, live, &format!("{label} backward row {i}"));
        let (want_ids, want) = if i == 0 { (&s0_ids, &s0_snap) } else { (&snaps[i - 1].0, &snaps[i - 1].1) };
        assert_eq!(ids.len(), want_ids.len(), "{label} backward row {i}: register layout differs"); // ids may differ (driver_selftest.rs)
        let got = snapshot(&sim, &ids);
        if &got != want {
            let wq = p.q.len();
            for j in 0..ninputs {
                if (live >> j) & 1 == 0 {
                    continue;
                }
                let g = shot_bits(&got, j);
                let w = shot_bits(want, j);
                if g != w {
                    let k = g.iter().zip(&w).position(|(a, b)| a != b).unwrap();
                    panic!("REVIEW {label}: backward row {i} input {j} ({:#x}): differs from the pre-forward snapshot at wire {k} = {}", traces[j].x, drv_wire_name(k, wq, nctr));
                }
            }
        }
    }
    // S_0 exactly for every live input
    let ids = drv_data_ids(&p);
    assert_eq!(ids.len(), s0_ids.len());
    let got = snapshot(&sim, &ids);
    for (j, t) in traces.iter().enumerate() {
        if (live >> j) & 1 == 0 {
            continue;
        }
        let st = St { a: prime(), b: t.x, ca: U512::ZERO, cb: one(), q: U512::ZERO };
        let want = drv_expected(&StepWidths::from_schedule(0), &st, p.q.len(), nctr, true, 0);
        assert_eq!(shot_bits(&got, j), want, "REVIEW {label}: input {j}: S_0 not restored after the round trip");
    }
    let on_support = first_miss.iter().filter(|m| m.is_none()).count();
    let misses: BTreeMap<&str, usize> = first_miss.iter().flatten().fold(BTreeMap::new(), |mut m, (_, k)| {
        *m.entry(*k).or_insert(0) += 1;
        m
    });
    let terms: Vec<usize> = traces.iter().filter_map(|t| t.terminal).collect();
    eprintln!(
        "REVIEW driver [{label}]: {ninputs} inputs ({on_support} on the support, misses {misses:?}), terminal steps {:?}..{:?} (<= 400: {}), rows checked {checked} (draining {chk_drain}, frozen {chk_frozen}, terminal divisions {chk_term}; at row {term_from}: draining {} frozen {} terminal {}), T fwd {} bwd {}, T at 378 fwd {} bwd {} ({:.0}s)",
        terms.iter().min(),
        terms.iter().max(),
        terms.iter().filter(|&&t| t <= 400).count(),
        chk_at_365.0,
        chk_at_365.1,
        chk_at_365.2,
        t_fwd.iter().sum::<usize>(),
        t_bwd.iter().sum::<usize>(),
        t_fwd[378],
        t_bwd[378],
        t0.elapsed().as_secs_f64()
    );
    (on_support, checked, t_fwd)
}

// ---------------------------------------------------------------------------
// 4. S_0 / teardown boundaries: divide_forward end to end
// ---------------------------------------------------------------------------

fn e2e_divide_forward(shots: usize) {
    assert!((1..=64).contains(&shots));
    let t0 = std::time::Instant::now();
    let env = EnvSnapshot::take();
    route_env_defaults();
    let p = prime();
    let mut c = Circuit::new();
    let dx = c.alloc_qreg_bits("dx", 257);
    let dy = c.alloc_qreg_bits("dy", 257);
    let dx_ids: Vec<QubitId> = dx.iter().map(|q| QubitId(q.id().into())).collect();
    let dy_ids: Vec<QubitId> = dy.iter().map(|q| QubitId(q.id().into())).collect();
    let (dx_out, dy_new, lambda) = divide_forward(&mut c, dx, dy);
    let out_dx: Vec<QubitId> = dx_out.iter().map(|q| QubitId(q.id().into())).collect();
    let out_dy: Vec<QubitId> = dy_new.iter().map(|q| QubitId(q.id().into())).collect();
    let out_l: Vec<QubitId> = lambda.iter().map(|q| QubitId(q.id().into())).collect();
    let ops = std::mem::take(&mut c.b.ops);
    let t = toffoli(&ops);
    eprintln!("REVIEW e2e: divide_forward built: {} ops, {t} Toffoli, {} qubit ids ({:.0}s)", ops.len(), analyze_ops(ops.iter()).0, t0.elapsed().as_secs_f64());
    env.restore();
    let xs = random_inputs(shots, b"packed-review-e2e-dx-v1");
    let ys: Vec<U512> = random_inputs(shots, b"packed-review-e2e-dy-v1").into_iter().map(|y| y % p).collect();
    let (nq, nb, _, _) = analyze_ops(ops.iter());
    let mut seed = Shake256::default();
    seed.update(b"packed-review-e2e-sim-v1");
    let mut rng = seed.finalize_xof();
    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
    for shot in 0..shots {
        for j in 0..257 {
            if xs[shot].bit(j) {
                *sim.qubit_mut(dx_ids[j]) |= 1u64 << shot;
            }
            if ys[shot].bit(j) {
                *sim.qubit_mut(dy_ids[j]) |= 1u64 << shot;
            }
        }
    }
    let live = u64::MAX >> (64 - shots);
    super::super::predicate_clear_selftest::checked_apply(&mut sim, &ops, live);
    assert_eq!(sim.phase & live, 0, "REVIEW e2e: phase (the dy ghost resolves only when dy_new = dy)");
    let read = |sim: &Simulator<'_, _>, ids: &[QubitId], shot: usize| -> U512 {
        let mut v = U512::ZERO;
        for (j, &id) in ids.iter().enumerate() {
            if (sim.qubit(id) >> shot) & 1 == 1 {
                v |= one() << j;
            }
        }
        v
    };
    for shot in 0..shots {
        let x = xs[shot];
        let y = ys[shot];
        let want = y.mul_mod(x.inv_mod(p).expect("x invertible"), p);
        let gx = read(&sim, &out_dx, shot);
        let gy = read(&sim, &out_dy, shot);
        let gl = read(&sim, &out_l, shot);
        assert_eq!(gx, x, "REVIEW e2e shot {shot}: dx not restored");
        assert_eq!(gy, y, "REVIEW e2e shot {shot}: dy_new != dy");
        assert_eq!(gl, want, "REVIEW e2e shot {shot}: lambda != dy * dx^-1 mod p (x {x:#x} y {y:#x})");
    }
    let data: std::collections::HashSet<u64> = out_dx.iter().chain(&out_dy).chain(&out_l).map(|q| q.0).collect();
    for (k, &v) in sim.qubits.iter().enumerate() {
        if !data.contains(&(k as u64)) {
            assert_eq!(v & live, 0, "REVIEW e2e: qubit {k} dirty after divide_forward");
        }
    }
    eprintln!(
        "REVIEW e2e PASS: divide_forward (cut 530, production route env) on {shots} random (dx, dy): lambda = dy/dx, dx and dy restored, phase 0, every other qubit 0; {t} Toffoli ({:.0}s)",
        t0.elapsed().as_secs_f64()
    );
}

/// The mirror: `divide_cancel(dx, dy, lambda)` with `lambda = dy/dx` must
/// return `(dx, dy)` and free lambda (its ghost resolves only on the right
/// lambda), phase 0, every other qubit 0.
fn e2e_divide_cancel(shots: usize) {
    assert!((1..=64).contains(&shots));
    let t0 = std::time::Instant::now();
    let env = EnvSnapshot::take();
    route_env_defaults();
    let p = prime();
    let mut c = Circuit::new();
    let dx = c.alloc_qreg_bits("dx", 257);
    let dy = c.alloc_qreg_bits("dy", 257);
    let lambda = c.alloc_qreg_bits("lambda", 257);
    let dx_ids: Vec<QubitId> = dx.iter().map(|q| QubitId(q.id().into())).collect();
    let dy_ids: Vec<QubitId> = dy.iter().map(|q| QubitId(q.id().into())).collect();
    let l_ids: Vec<QubitId> = lambda.iter().map(|q| QubitId(q.id().into())).collect();
    let (dx_out, dy_out) = divide_cancel(&mut c, dx, dy, lambda);
    let out_dx: Vec<QubitId> = dx_out.iter().map(|q| QubitId(q.id().into())).collect();
    let out_dy: Vec<QubitId> = dy_out.iter().map(|q| QubitId(q.id().into())).collect();
    let ops = std::mem::take(&mut c.b.ops);
    let t = toffoli(&ops);
    eprintln!("REVIEW e2e: divide_cancel built: {} ops, {t} Toffoli ({:.0}s)", ops.len(), t0.elapsed().as_secs_f64());
    env.restore();
    let xs = random_inputs(shots, b"packed-review-e2e-cancel-dx-v1");
    let ys: Vec<U512> = random_inputs(shots, b"packed-review-e2e-cancel-dy-v1").into_iter().map(|y| y % p).collect();
    let ls: Vec<U512> = xs.iter().zip(&ys).map(|(x, y)| y.mul_mod(x.inv_mod(p).expect("x invertible"), p)).collect();
    let (nq, nb, _, _) = analyze_ops(ops.iter());
    let mut seed = Shake256::default();
    seed.update(b"packed-review-e2e-cancel-sim-v1");
    let mut rng = seed.finalize_xof();
    let mut sim = Simulator::new(nq as usize, nb as usize + 1, &mut rng);
    for shot in 0..shots {
        for j in 0..257 {
            if xs[shot].bit(j) {
                *sim.qubit_mut(dx_ids[j]) |= 1u64 << shot;
            }
            if ys[shot].bit(j) {
                *sim.qubit_mut(dy_ids[j]) |= 1u64 << shot;
            }
            if ls[shot].bit(j) {
                *sim.qubit_mut(l_ids[j]) |= 1u64 << shot;
            }
        }
    }
    let live = u64::MAX >> (64 - shots);
    super::super::predicate_clear_selftest::checked_apply(&mut sim, &ops, live);
    assert_eq!(sim.phase & live, 0, "REVIEW e2e cancel: phase (the lambda ghost resolves only when the recomputed lambda matches)");
    let read = |sim: &Simulator<'_, _>, ids: &[QubitId], shot: usize| -> U512 {
        let mut v = U512::ZERO;
        for (j, &id) in ids.iter().enumerate() {
            if (sim.qubit(id) >> shot) & 1 == 1 {
                v |= one() << j;
            }
        }
        v
    };
    for shot in 0..shots {
        assert_eq!(read(&sim, &out_dx, shot), xs[shot], "REVIEW e2e cancel shot {shot}: dx not restored");
        assert_eq!(read(&sim, &out_dy, shot), ys[shot], "REVIEW e2e cancel shot {shot}: dy not restored");
    }
    let data: std::collections::HashSet<u64> = out_dx.iter().chain(&out_dy).map(|q| q.0).collect();
    for (k, &v) in sim.qubits.iter().enumerate() {
        if !data.contains(&(k as u64)) {
            assert_eq!(v & live, 0, "REVIEW e2e cancel: qubit {k} dirty after divide_cancel");
        }
    }
    eprintln!(
        "REVIEW e2e PASS: divide_cancel (cut 530, production route env) on {shots} random (dx, dy, lambda = dy/dx): dx and dy restored, lambda freed, phase 0, every other qubit 0; {t} Toffoli ({:.0}s)",
        t0.elapsed().as_secs_f64()
    );
}

// ---------------------------------------------------------------------------
// Entry
// ---------------------------------------------------------------------------

/// `MIDQ_REVIEW_PROBE=<hex x>:<step>[:static]`: one substep case on one
/// input's row with full diagnostics (support verdict, every differing wire),
/// under the thin schedule (default) or the static tables. Diagnostics only.
fn probe(spec: &str, term_from: usize, pop: bool) {
    let parts: Vec<&str> = spec.split(':').collect();
    assert!(parts.len() >= 2, "MIDQ_REVIEW_PROBE=<hex>:<step>[:static]");
    let x = U512::from_str_radix(parts[0].trim_start_matches("0x"), 16).expect("hex input");
    let step: usize = parts[1].parse().expect("step");
    let stat = parts.get(2).copied() == Some("static");
    if stat {
        std::env::remove_var("TRAILMIX_THIN_SCHEDULE");
    }
    let t = trace(x, term_from, pop);
    let row = &t.rows[step];
    let mut s = StepWidths::from_schedule(step);
    if let Some(lob) = parts.iter().find_map(|p| p.strip_prefix("lob=")).and_then(|v| v.parse::<usize>().ok()) {
        // force the schedule's lower bound of e_B (the other harness's `thin_lo(W_B, 78)` value)
        s = StepWidths::new(step, s.w_a, s.w_b, s.w_c, s.w_q, lob, lob, s.lo_ca, s.lo_cb, s.s_div_bound, s.s2_bound);
    }
    let wq = natural_q_width(step).max(bl(&row.pre.q)).max(bl(&row.post.q)).clamp(1, 1 << SROT);
    let verdict = support(row, step, &s, wq, term_from);
    let (e_a, e_b, e_ca, e_cb) = (bl(&row.pre.a), bl(&row.pre.b), bl(&row.pre.ca), bl(&row.pre.cb));
    eprintln!(
        "REVIEW probe {x:#x} step {step} ({}): kind {:?} eA {e_a} eB {e_b} eca {e_ca} ecb {e_cb} div {:?} mul {:?} | W_A {} W_B {} W_c {} lo_a {} lo_b {} lo_ca {} lo_cb {} zone_start(D7) {} zone_start(M5) {} n_w {} | support {verdict:?}",
        if stat { "static" } else { "thin" },
        row.kind,
        row.div.map(|(sd, off, a_new)| (sd, off, bl(&a_new))),
        row.mul,
        s.w_a, s.w_b, s.w_c, s.div_cascade_lo(), s.lo_b, s.lo_ca, s.lo_cb, s.div_zone_start(), s.mul_zone_start(), s.div_scan_window()
    );
    if row.kind != Kind::Div && row.kind != Kind::Mul && row.kind != Kind::Draining {
        return;
    }
    let div = row.kind == Kind::Div;
    let data = sub_state(&s, &row.pre, wq, true);
    let expect = sub_state(&s, &row.mid, wq, true);
    let fwd = build_sub(&s, wq, div, step >= term_from, false);
    let inv = build_sub(&s, wq, div, step >= term_from, true);
    let out = simulate_sub(&fwd, std::slice::from_ref(&data), "probe-fwd");
    let bad: Vec<String> = out[0].iter().zip(&expect).enumerate().filter(|(_, (a, b))| a != b).map(|(k, _)| sub_wire_name(k, wq)).collect();
    eprintln!("REVIEW probe forward: T {} differing wires ({}): {:?}", fwd.t, bad.len(), &bad[..bad.len().min(40)]);
    let back = simulate_sub(&inv, &out, "probe-inv");
    eprintln!("REVIEW probe inverse restores the input: {}", back[0] == data);
    if stat {
        std::env::set_var("TRAILMIX_THIN_SCHEDULE", "1");
    }
}

pub(super) fn run() {
    let env = EnvSnapshot::take();
    packed_env();
    if let Ok(spec) = std::env::var("MIDQ_REVIEW_PROBE") {
        let pop = std::env::var("MIDQ_PREFIX_POPCOUNT").ok().as_deref() == Some("1");
        probe(&spec, terminal_from(), pop);
        env.restore();
        return;
    }
    let t0 = std::time::Instant::now();
    let term_from = terminal_from();
    let pool_n = env_usize("MIDQ_REVIEW_POOL", 262144);
    let summary_n = env_usize("MIDQ_REVIEW_SUMMARY", 8192).min(pool_n);
    let cls = classes();
    // the production thin schedule (process-cached; ~21 s the first time)
    let sw: Vec<StepWidths> = (0..NSTEPS).map(StepWidths::from_schedule).collect();
    let wq_of: Vec<usize> = (0..NSTEPS).map(natural_q_width).collect();
    let q_max = wq_of.iter().copied().max().unwrap();
    let q_max_step = wq_of.iter().position(|&w| w == q_max).unwrap();
    eprintln!(
        "REVIEW config: term_from {term_from} pool {pool_n} classes {} q envelope max {q_max} (first at step {q_max_step}); W_A/W_c/q at 284 {} {} {}, 300 {} {} {}, 313 {} {} {}, 378 {} {} {}, 413 {} {} {} ({:.0}s schedule)",
        cls.len(), sw[284].w_a, sw[284].w_c, wq_of[284], sw[300].w_a, sw[300].w_c, wq_of[300], sw[313].w_a, sw[313].w_c, wq_of[313], sw[378].w_a, sw[378].w_c, wq_of[378], sw[413].w_a, sw[413].w_c, wq_of[413],
        t0.elapsed().as_secs_f64()
    );

    // --- 1. pool search ------------------------------------------------------
    let pop = std::env::var("MIDQ_PREFIX_POPCOUNT").ok().as_deref() == Some("1");
    let inputs = random_inputs(pool_n, b"packed-review-pool-v1");
    // lean pass over the whole pool: terminal step / first draining row
    let lite: Vec<(Option<usize>, Option<usize>)> = inputs.iter().map(|&x| terminal_lite(x)).collect();
    let mut term_hist: BTreeMap<usize, usize> = BTreeMap::new();
    for (t, _) in &lite {
        if let Some(ts) = t {
            *term_hist.entry(ts / 10 * 10).or_insert(0) += 1;
        }
    }
    let not_done = lite.iter().filter(|(t, _)| t.is_none()).count();
    let early = lite.iter().filter(|(t, _)| t.map_or(false, |t| t < term_from)).count();
    for (i, (t, _)) in lite.iter().enumerate() {
        if t.map_or(false, |t| t < term_from) {
            eprintln!("REVIEW pool: input {i} ({:#x}) terminates at row {} < {term_from}: a `term_row` miss (the driver has no terminal handling there)", inputs[i], t.unwrap());
        }
    }
    let earliest: Vec<(usize, usize)> = {
        let mut v: Vec<(usize, usize)> = lite.iter().enumerate().filter_map(|(i, (t, _))| t.filter(|&t| t >= term_from).map(|t| (t, i))).collect();
        v.sort();
        v
    };
    eprintln!(
        "REVIEW pool (lean): {pool_n} inputs in {:.0}s; not terminated by 530: {not_done}; terminated before {term_from}: {early}; earliest terminal steps {:?}; terminal-step histogram (by decade) {:?}",
        t0.elapsed().as_secs_f64(),
        earliest.iter().take(24).map(|&(t, _)| t).collect::<Vec<_>>(),
        term_hist
    );
    // full summaries: the first `summary_n` inputs (class search) plus the 128
    // earliest terminators (the driver's (a) set needs their support verdict)
    let mut chosen: Vec<usize> = (0..summary_n).collect();
    for &(_, i) in earliest.iter().take(128) {
        if !chosen.contains(&i) {
            chosen.push(i);
        }
    }
    let mut summaries: Vec<Summary> = Vec::with_capacity(chosen.len());
    for &idx in &chosen {
        let t = trace(inputs[idx], term_from, pop);
        summaries.push(summarize(idx, inputs[idx], &t, &cls, &sw, &wq_of, term_from));
    }
    let pool_n = summaries.len();
    let miss_kinds: BTreeMap<&str, usize> = summaries.iter().filter_map(|s| s.first_miss).fold(BTreeMap::new(), |mut m, (_, k)| {
        *m.entry(k).or_insert(0) += 1;
        m
    });
    let missed = summaries.iter().filter(|s| s.first_miss.is_some()).count();
    eprintln!(
        "REVIEW pool: {pool_n} inputs traced in {:.0}s; not terminated by 530: {not_done}; terminated before {term_from}: {early}; off the thin schedule's support: {missed} ({:.2}%; first-miss kinds {miss_kinds:?}); terminal-step histogram (by decade) {:?}",
        t0.elapsed().as_secs_f64(),
        100.0 * missed as f64 / pool_n as f64,
        term_hist
    );
    // class winners (top 2 per class)
    let top_k = 2usize;
    let mut sub_cases: Vec<SubCase> = Vec::new();
    let mut winner_inputs: Vec<usize> = Vec::new();
    let mut class_report: Vec<String> = Vec::new();
    for (k, c) in cls.iter().enumerate() {
        let mut ranked: Vec<(i64, usize, usize)> = summaries.iter().filter_map(|s| s.best[k].map(|(v, i)| (v, s.idx, i))).collect();
        ranked.sort_by(|a, b| b.0.cmp(&a.0).then(a.2.cmp(&b.2)).then(a.1.cmp(&b.1)));
        let n_hits = ranked.len();
        for &(v, idx, i) in ranked.iter().take(top_k) {
            sub_cases.push(SubCase { class: c.name, input: idx, step: i, sched: sw[i], synthetic: false });
            if !winner_inputs.contains(&idx) {
                winner_inputs.push(idx);
            }
            class_report.push(format!("{}: score {v} input {idx} step {i} (of {n_hits} rows)", c.name));
        }
        if ranked.is_empty() {
            // envelope hits (e_A = W_A, e_B = W_A, e_B = W_B) may not occur in
            // the pool: narrow the envelope to the extreme row instead
            let forced = match c.metric {
                Metric::DivEaEqWa => Some((true, "w_a")),
                Metric::DivEbEqWa => Some((true, "w_a=eB")),
                Metric::MulEbHi => Some((false, "w_b")),
                _ => None,
            };
            if let Some((div, what)) = forced {
                // the row with the largest e_A (division, e_A = e_B for eB_eq_WA) / e_B (multiply) in the band
                let mut best: Option<(usize, usize, usize)> = None; // (metric, input, step)
                for s in summaries.iter().take(2048) {
                    let t = trace(s.x_orig, term_from, pop);
                    for i in c.lo..=c.hi {
                        let row = &t.rows[i];
                        let m = match c.metric {
                            Metric::DivEaEqWa if row.kind == Kind::Div && !row.div.unwrap().2.is_zero() => Some(bl(&row.pre.a)),
                            Metric::DivEbEqWa if row.kind == Kind::Div && !row.div.unwrap().2.is_zero() && bl(&row.pre.a) == bl(&row.pre.b) => Some(bl(&row.pre.b)),
                            Metric::MulEbHi if row.kind == Kind::Mul => Some(bl(&row.pre.b)),
                            _ => None,
                        };
                        if let Some(m) = m {
                            if best.map_or(true, |(b, _, _)| m > b) {
                                best = Some((m, s.idx, i));
                            }
                        }
                    }
                }
                if let Some((m, idx, i)) = best {
                    let s = &sw[i];
                    let narrowed = if div {
                        StepWidths::new(i, m, s.w_b.min(m), s.w_c, s.w_q, s.lo_a.min(m - 1), s.lo_b.min(m - 1), s.lo_ca, s.lo_cb, s.s_div_bound, s.s2_bound)
                    } else {
                        StepWidths::new(i, s.w_a, m, s.w_c, s.w_q, s.lo_a, s.lo_b.min(m - 1), s.lo_ca, s.lo_cb, s.s_div_bound, s.s2_bound)
                    };
                    sub_cases.push(SubCase { class: c.name, input: idx, step: i, sched: narrowed, synthetic: true });
                    class_report.push(format!("{}: no natural row in the band; FORCED {what} = {m} on input {idx} step {i}", c.name));
                } else {
                    class_report.push(format!("{}: no row at all", c.name));
                }
            } else {
                class_report.push(format!("{}: no row in the band", c.name));
            }
        }
    }
    for line in &class_report {
        eprintln!("REVIEW class {line}");
    }

    // --- 2. substep cases ------------------------------------------------------
    let mut trace_cache: BTreeMap<usize, Trace> = BTreeMap::new();
    let mut n_ok = 0usize;
    let mut n_off = 0usize;
    let mut t_div_378: Vec<usize> = Vec::new();
    let mut t_mul_378: Vec<usize> = Vec::new();
    let mut t_div_band: Vec<(usize, usize)> = Vec::new();
    let mut t_mul_band: Vec<(usize, usize)> = Vec::new();
    for case in &sub_cases {
        let t = trace_cache.entry(case.input).or_insert_with(|| trace(inputs[case.input], term_from, pop));
        let (kind, on_support, tf, ti, desc) = run_sub_case(case, t, term_from);
        assert_eq!(tf, ti, "REVIEW {}: forward / inverse Toffoli differ ({desc})", case.class);
        match on_support {
            Ok(()) => n_ok += 1,
            Err(_) => n_off += 1,
        }
        let synth = if case.synthetic { " [narrowed envelope]" } else { "" };
        eprintln!(
            "REVIEW sub {}: {desc} T {tf} {}{synth}",
            case.class,
            match on_support {
                Ok(()) => "value+inverse OK".to_string(),
                Err(k) => format!("OFF SUPPORT ({k}): inverse OK, value not claimed"),
            }
        );
        if !case.synthetic {
            if case.step == 378 {
                if kind == Kind::Div { t_div_378.push(tf) } else { t_mul_378.push(tf) }
            }
            if (WIDE2.0..=WIDE2.1).contains(&case.step) || (WIDE1.0..=WIDE1.1).contains(&case.step) {
                if kind == Kind::Div { t_div_band.push((case.step, tf)) } else { t_mul_band.push((case.step, tf)) }
            }
        }
    }
    eprintln!(
        "REVIEW sub: {} cases ({n_ok} value-checked on the support, {n_off} off-support rows inverse-checked only); division T in the bands {:?}; multiply T in the bands {:?}",
        sub_cases.len(),
        t_div_band,
        t_mul_band
    );
    // design section 4 at 378: the 3.1 table rows sum to 4,403 (+540 with D0
    // on rows >= 365) and the 3.2 rows to 6,893 (the prose says "~4.9k" and
    // "~5.5k"; the table is the priced form and sums to the step's 12,435);
    // asserted at +25% of the table sums
    for (i, t) in &t_div_band {
        if (WIDE2.0..=WIDE2.1).contains(i) {
            assert!(*t <= 4943 * 5 / 4, "REVIEW: division T {t} at step {i} exceeds design 4,943 + 25%");
        }
    }
    for (i, t) in &t_mul_band {
        if (WIDE2.0..=WIDE2.1).contains(i) {
            assert!(*t <= 6893 * 5 / 4, "REVIEW: multiply T {t} at step {i} exceeds design 6,893 + 25%");
        }
    }

    // --- 3. driver round trips ----------------------------------------------------
    // (a) the earliest-terminating inputs (terminal >= term_from)
    let mut by_term: Vec<&Summary> = summaries.iter().filter(|s| s.first_miss.is_none() && s.terminal.map_or(false, |t| t >= term_from)).collect();
    by_term.sort_by_key(|s| (s.terminal.unwrap(), s.idx));
    let early_inputs: Vec<U512> = by_term.iter().take(64).map(|s| s.x_orig).collect();
    let early_terms: Vec<usize> = by_term.iter().take(64).map(|s| s.terminal.unwrap()).collect();
    let early_drains: Vec<Option<usize>> = by_term.iter().take(64).map(|s| s.first_drain).collect();
    eprintln!("REVIEW driver (a): earliest terminal steps {:?}; first draining rows {:?}", &early_terms[..early_terms.len().min(16)], &early_drains[..early_drains.len().min(16)]);
    let (on_a, checked_a, tf_a) = driver_round_trip(&early_inputs, "earliest-terminating", term_from);
    assert!(on_a >= early_inputs.len() / 2, "REVIEW driver (a): fewer than half of the inputs on the support ({on_a})");
    if pool_n >= 32768 {
        assert!(early_terms.iter().any(|&t| t <= 400), "REVIEW driver (a): no input terminates in [365, 400] (pool too small?)");
    }
    // (c) the early terminators of the 4M classical draw (R:/Coding/shor2/tools/spike/
    // term_first.py + term_dump.py, seeds 2026/2027/2028): every input terminating before row 372,
    // i.e. between the branch default FROM = 340 and the design's old 365
    let early4m: Vec<U512> = EARLY_TERMINATORS_4M.iter().map(|(_, h)| U512::from_str_radix(h.trim_start_matches("0x"), 16).expect("hex input")).collect();
    // Under the seed-278 thin schedule the coefficient envelope reaches 256 at
    // row 371 (MIDQ_PACKED_DUMP_SCHED), and the last draining row of every
    // terminating input has ca = p (256 bits): an input frozen before ~372 is a
    // width_c miss whatever FROM is, so most of these are off the support and
    // exercise only the reversibility (garbage round trip); the ones on the
    // support are value-checked at every row incl. their terminal division.
    let (on_c, checked_c, tf_c) = driver_round_trip(&early4m, "early-terminators-4M", term_from);
    assert!(on_c >= 1, "REVIEW driver (c): none of the 4M early terminators on the support");
    assert!(EARLY_TERMINATORS_4M.iter().all(|&(t, _)| t >= term_from), "REVIEW driver (c): an early terminator terminates before MIDQ_PREFIX_TERMINAL_FROM = {term_from}");
    let _ = (checked_c, tf_c);
    // (b) the class winners
    let miss_of = |idx: usize| summaries.iter().find(|s| s.idx == idx).and_then(|s| s.first_miss);
    let winners: Vec<U512> = winner_inputs.iter().filter(|&&i| miss_of(i).is_none()).take(64).map(|&i| inputs[i]).collect();
    eprintln!("REVIEW driver (b): {} class-winner inputs on the support of {} winners", winners.len(), winner_inputs.len());
    let (on_b, checked_b, tf_b) = driver_round_trip(&winners, "class-winners", term_from);
    assert!(on_b >= winners.len() / 2, "REVIEW driver (b): fewer than half of the inputs on the support ({on_b})");
    let step_t_378 = tf_a[378].max(tf_b[378]);
    assert!(step_t_378 <= 12435 * 5 / 4, "REVIEW: step T {step_t_378} at 378 exceeds design 12,435 + 25%");
    let sum_a: usize = tf_a.iter().sum();
    let sum_b: usize = tf_b.iter().sum();
    assert!(sum_a.max(sum_b) <= 5_950_000 * 5 / 4, "REVIEW: traversal T exceeds design 5.95M + 25%");
    let _ = (checked_a, checked_b);

    // --- 4. S_0 / teardown end to end ------------------------------------------
    if std::env::var("MIDQ_REVIEW_SKIP_E2E").ok().as_deref() != Some("1") {
        e2e_divide_forward(env_usize("MIDQ_REVIEW_E2E_SHOTS", 64).clamp(1, 64));
        e2e_divide_cancel(env_usize("MIDQ_REVIEW_E2E_SHOTS", 64).clamp(1, 64));
    } else {
        eprintln!("REVIEW e2e: skipped (MIDQ_REVIEW_SKIP_E2E=1)");
    }

    eprintln!(
        "REVIEW PASS: {} substep cases, 3 driver round trips ({} + {} + {} inputs), {} ({:.0}s)",
        sub_cases.len(),
        early_inputs.len(),
        early4m.len(),
        winners.len(),
        if std::env::var("MIDQ_REVIEW_SKIP_E2E").ok().as_deref() == Some("1") { "e2e skipped" } else { "divide_forward + divide_cancel e2e" },
        t0.elapsed().as_secs_f64()
    );
    let _ = BTreeSet::<usize>::new();
    env.restore();
}
