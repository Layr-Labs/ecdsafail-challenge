//! The ping-pong modular divider: `numerator *= denominator^{-1} (mod p)`, and
//! its inverse `numerator *= denominator`.
//!
//! # The walk
//!
//! `u` and `v` run a fixed-depth binary extended-GCD recurrence seeded with
//! `u = p`, `v = denominator`.  Rounds 0 and 1 lift the pair into the invariant
//! (see [`round0_forward`] and [`round1_forward`]); every later round is
//!
//! ```text
//!     target <- (target + (-1)^sign * source) / 2,   sign = bit 1 of target ^ source
//! ```
//!
//! with `target` and `source` alternating between `u` and `v`.  Both values stay
//! odd, and `sign` is exactly the choice that keeps the halved sum odd.  Their
//! magnitudes shrink, so [`width_schedule`] narrows the registers as it goes and
//! hands the freed wires back to the allocator; bit 0, being a constant one for
//! the whole walk, never occupies a wire at all (see [`park_odd_bits`]).
//!
//! One `sign` qubit per round is kept: the **tape**.
//!
//! # The replay
//!
//! The same round sequence, driven by the tape, is replayed on a second pair of
//! registers (`coefficient`, `numerator`) as modular halvings — which is what
//! turns the GCD into a division.  The tape is fully live while it is replayed,
//! so the tape length is the dominant term in peak width and the replay is where
//! nearly all the Toffoli go.
//!
//! # Interleaving
//!
//! Replaying only at the end would need the whole tape *and* a full-width walk
//! state at once, so [`Plan`] splits the rounds three ways: rounds below `r1`
//! are replayed in one batch once the walk has passed them, rounds in
//! `r1..=r2` are replayed round by round beside the walk, and rounds above `r2`
//! are replayed at the terminal state, where the walk registers collapse to two
//! sign wires and can be loaned to the allocator wholesale.
//!
//! Every carry ladder inside that region is sized against the width left over,
//! and both the replay's ([`chunked_add`]) and the walk's ([`walk_low_chunk`])
//! ask the builder for it rather than modelling it — so peak width is a cap the
//! construction works within, not an outcome.
//!
//! # Direction
//!
//! [`PingPongDirection::Multiply`] is the exact time-reverse of `Divide`: it
//! walks first and replays on the way back, with the doubling cell in place of
//! the halving one.

use super::compare::erase_with_compare;
use super::const_arith::{
    add_const, cadd_const_per_position_trunc, cadd_const_trunc, csub_const_trunc,
    csub_const_trunc_ctrl_low0, sub_const,
};
use super::modular::{add_f_window, f, f_slice, ripple_add};
use super::{fold_guard, pinned_env, required_env, Builder, N, SECP256K1_P};
use crate::circuit::{BitId, QubitId};
use alloy_primitives::U256;

/// Signed envelope the walk values live in: 256 magnitude bits plus room for
/// the sign and the round-0 lift.
const VALUE_WIDTH: usize = N + 3;

/// Narrowest walk register the construction admits. [`walk_add_single`] runs on
/// the bit-1-and-up slice -- `width - 1` wires -- and needs at least four.
const MIN_WALK_WIDTH: usize = 5;

/// Depth of the divide walk. [`width_schedule`] is generated for exactly this
/// many rounds and is wrong for any other, so the two are one fact and the depth
/// is not separately settable: to change it, regenerate the schedule.
fn rounds_div() -> usize {
    width_schedule().len()
}

// Depth of the multiply walk, which converges in slightly fewer rounds. This one
// IS free: it only has to stay within the schedule, and the rounds it drops are
// the narrowest ones.
pinned_env!(rounds_mul, "PP_ROUNDS_MUL");

// Truncation windows for the measured-erasure repairs. Each one trades emitted
// Toffoli against the intrinsic mismatch rate, so they are swept as a group;
// every one is pinned in `point_add::build`.
pinned_env!(replay_chunk_compare, "PP_REPLAY_CHUNK_COMPARE");
pinned_env!(replay_fold_window, "PP_REPLAY_FOLD_WINDOW");
pinned_env!(replay_fold_window_mul, "PP_REPLAY_FOLD_WINDOW_MUL");
pinned_env!(replay_flag_compare, "PP_REPLAY_FLAG_COMPARE");

// The circuit's peak, and the only width knob there is. Both carry-ladder
// sites -- `walk_low_chunk` for the walk's split adds, `chunked_add` for the
// replay's -- size themselves against the live count the builder reports, so
// each lands on exactly this many qubits and neither can drift.
//
// There is deliberately no second budget for the replay side. Sizing it against
// a modelled live set instead gives the same layout at every call: such a model
// is high by exactly `MODEL_OVERCOUNT`, so its budget is only ever this knob plus
// four, and its achieved peak this knob exactly.
pinned_env!(walk_max_qubits, "PP_WALK_MAX_QUBITS");

/// Wires a footprint *model* counts that the allocator has already taken back:
/// the two tape signs [`free_sign_bit`] measures out early, and the walk's
/// bit-0 pair that [`park_odd_bits`] releases for the whole walk.
///
/// Nothing that can ask [`Builder::active_qubits`] needs this. [`head_boundary`]
/// is the one place that cannot -- it picks `r1` before the head batch exists,
/// so it has to predict a footprint rather than measure one.
const MODEL_OVERCOUNT: usize = 4;

// Where the trailing batch takes over. Unlike `r1` (see `head_boundary`) this
// one is NOT determined: its optimum is a wide plateau -- at the pinned budget
// everything from 600 to 658 costs exactly the same -- and the two natural rules
// for deriving it ("interleave while it needs no more chunks than the terminal
// batch would" and "...while it needs strictly fewer") disagree by ~100 rounds
// with neither dominating across budgets. Deriving it would dress a tuning
// choice up as a derivation, so it stays a swept knob.
pinned_env!(plan_r2, "PP_R2");

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PingPongDirection {
    Divide,
    Multiply,
}

// ─── The interleaving plan ─────────────────────────────────────────────────

/// Rounds below `r1` are replayed in one batch; rounds above `r2` are replayed
/// in one batch at the loaned terminal state; rounds in `r1..=r2` are replayed
/// beside their own walk round.
struct Plan {
    direction: PingPongDirection,
    rounds: usize,
    r1: usize,
    r2: usize,
}

impl Plan {
    fn new(direction: PingPongDirection) -> Self {
        // `cell_extra` is what the replay cell holds live across its chunked add,
        // on top of the registers `head_boundary`'s footprint model counts. Only
        // that model needs it: `chunked_add` sees these wires in the live count.
        let (rounds, cell_extra) = match direction {
            // The signed cell's bit-256 wire is the adder's own carry-out.
            PingPongDirection::Divide => (rounds_div(), 0),
            // `doubled_out` lives across the add as well.
            PingPongDirection::Multiply => (rounds_mul(), 1),
        };
        assert!(rounds <= rounds_div(), "no width schedule for that depth");
        let plan = Self {
            direction,
            rounds,
            r1: head_boundary(rounds, cell_extra),
            r2: plan_r2().min(rounds.saturating_sub(1)),
        };
        // The trailing batch is what the peak binds on, and the fold shape only
        // narrows once the walk does, so the batch must not reach back past that.
        assert!(
            plan.tail().start >= fold_ramp_start(),
            "the trailing replay batch reaches back past the fold shape's ramp"
        );
        plan
    }

    /// Rounds replayed in the leading batch, once the walk has passed them.
    fn head(&self) -> std::ops::Range<usize> {
        0..self.r1
    }

    /// Rounds whose replay is interleaved with their own walk round.
    fn mid(&self) -> std::ops::RangeInclusive<usize> {
        self.r1..=self.r2
    }

    /// Rounds replayed in the trailing batch, at the terminal state.
    fn tail(&self) -> std::ops::Range<usize> {
        (self.r2 + 1).max(self.r1)..self.rounds
    }

    /// Fold window for the replay cell at `round`, in bits: the direction's
    /// pinned window plus [`fold_offset`] for that round.
    ///
    /// The shape is what makes this per-round rather than flat, and it is
    /// measured, not derived — see [`fold_shape`]. It also happens to hold the
    /// peak: the cell's fold is the widest thing alive in the trailing batch,
    /// where the tape is at its longest and [`loan_terminal`] has collapsed both
    /// walk registers to a sign wire, and the profile has already narrowed those
    /// rounds by one to four bits. Every other round has slack — ~74 qubits in
    /// the head batch, a couple in the worst interleaved one — which is what
    /// affords the profile's leading `+1` run.
    fn fold_window(&self, round: usize) -> usize {
        let base = match self.direction {
            PingPongDirection::Divide => replay_fold_window(),
            PingPongDirection::Multiply => replay_fold_window_mul(),
        };
        base.checked_add_signed(fold_offset(round))
            .expect("the fold shape keeps the window positive")
    }
}

/// Ladder width at which [`chunk_layout`] first reaches a two-chunk split of the
/// 256-bit replay add. Derived from the same two helpers the layout search uses,
/// so it cannot drift away from them.
fn two_chunk_ladder() -> usize {
    layout_ladder(&equal_split(N, 2))
}

/// `r1`: the last round replayed in the leading batch.
///
/// That batch replays every round below `r1` at ONE frozen footprint — `r1` tape
/// wires, both coefficient registers, and the two walk registers at
/// `value_width(r1)` — so its chunk count is a function of `r1` alone, and
/// staying at two chunks means
///
/// ```text
///     r1 + 2*value_width(r1) <= peak + MODEL_OVERCOUNT
///                                    - 2N - two_chunk_ladder() - cell_extra
/// ```
///
/// Inside such a plateau the batch's cost is flat, while each extra round it
/// swallows takes one walk round out of the split regime ([`walk_low_chunk`])
/// and one replay round off the interleaved allowance, which by then is the
/// worse of the two. So the largest round on the plateau is the one to take, and
/// one round past it the whole batch jumps to three chunks — a step worth
/// hundreds of Toffoli.
///
/// This is why `r1` is computed and not pinned: it is a function of the width
/// schedule and the peak, and it must move whenever either does. Swept and
/// confirmed optimal at peak 1264 (335 divide / 326 multiply) and at 1273
/// (368 / 365); at the pinned 1260 it comes out 313 and 312.
///
/// This is also the one footprint in the file that is predicted rather than
/// measured — `r1` is chosen before the head batch exists — hence
/// [`MODEL_OVERCOUNT`].
fn head_boundary(rounds: usize, cell_extra: usize) -> usize {
    let room = (walk_max_qubits() + MODEL_OVERCOUNT)
        .saturating_sub(2 * N + two_chunk_ladder() + cell_extra);
    (0..rounds)
        .filter(|&r| r + 2 * value_width(r) <= room)
        .max()
        .unwrap_or(0)
}

// ─── Entry point ───────────────────────────────────────────────────────────

/// `numerator /= denominator (mod p)`.
pub fn divide(circ: &mut Builder, numerator: &[QubitId], denominator: &[QubitId]) {
    pingpong(circ, numerator, denominator, PingPongDirection::Divide);
}

/// `numerator *= denominator (mod p)`.
///
/// The exact time-reverse of [`divide`]: it walks all the way out before it
/// replays, and its replay cell doubles where the divide's halves.
pub fn multiply(circ: &mut Builder, numerator: &[QubitId], denominator: &[QubitId]) {
    pingpong(circ, numerator, denominator, PingPongDirection::Multiply);
}

/// The shared frame both directions run in: stand up the walk pair, hand it to
/// the traversal, put the wires back.
///
/// Both caller registers are preserved in place except for the documented
/// numerator result.  The shrinking walk lends its cleared high wires to the
/// tape and scratch allocator.  [`restore_wire_layout`] puts the restored value
/// back onto the original ABI wires before returning.
fn pingpong(
    circ: &mut Builder,
    numerator: &[QubitId],
    denominator: &[QubitId],
    direction: PingPongDirection,
) {
    assert_eq!(denominator.len(), N);
    assert_eq!(numerator.len(), N);

    let mut u = load_const(circ, N, SECP256K1_P);
    u.extend(circ.alloc_qubits(VALUE_WIDTH - N));
    let wanted_u = u.clone();
    let mut v = denominator.to_vec();
    v.extend(circ.alloc_qubits(VALUE_WIDTH - N));
    let wanted_v = v.clone();

    let plan = Plan::new(direction);
    match direction {
        PingPongDirection::Divide => divide_traversal(circ, &plan, &mut u, &mut v, numerator),
        PingPongDirection::Multiply => multiply_traversal(circ, &plan, &mut u, &mut v, numerator),
    }

    // The only phase name that is not statically known: the two traversals each
    // emit their own, because each is only ever reached with its own direction.
    circ.set_phase(match direction {
        PingPongDirection::Divide => "pp_div_restore",
        PingPongDirection::Multiply => "pp_mul_restore",
    });
    restore_wire_layout(circ, &mut u, &mut v, &wanted_u, &wanted_v);

    circ.free_vec(&v[N..]);
    for (i, &q) in u[..N].iter().enumerate() {
        if SECP256K1_P.bit(i) {
            circ.x(q);
        }
    }
    circ.free_vec(&u);
}

/// Walk forwards, replaying each round as soon as the plan allows, then walk
/// back.  Halving order matches the forward walk.
fn divide_traversal(
    circ: &mut Builder,
    plan: &Plan,
    u: &mut Vec<QubitId>,
    v: &mut Vec<QubitId>,
    numerator: &[QubitId],
) {
    circ.set_phase("pp_div_walk");
    let mut tape = Vec::with_capacity(plan.rounds);
    let mut a0_fix = None;
    for r in plan.head() {
        tape.push(walk_round(circ, u, v, r));
        if r == 0 {
            a0_fix = Some(free_sign_bit(circ, tape[0]));
        }
    }

    circ.set_phase("pp_div_replay");
    // `walk_round(r1)` would shrink to `value_width(r1)` anyway; doing it before
    // the batch replay costs the same ops and takes two wires off its footprint.
    if plan.r1 < plan.rounds {
        shrink_to(circ, u, v, value_width(plan.r1));
    }
    let coefficient = circ.alloc_qubits(N);
    // The tape wire is passed in rather than read from `tape` here, so that the
    // interleaved loop can keep appending to it.
    let replay = |circ: &mut Builder, r: usize, sign: QubitId| {
        replay_halving_round(circ, r, sign, &coefficient, numerator, plan.fold_window(r));
    };

    let mut sign1_fix = None;
    for r in plan.head() {
        replay(circ, r, tape[r]);
        // Round 1's sign is dead the moment its own replay is done; the rest of
        // the batch runs one wire lighter.
        if r == 1 {
            sign1_fix = Some(free_sign_bit(circ, tape[1]));
        }
    }

    for r in plan.mid() {
        tape.push(walk_round(circ, u, v, r));
        if r + 1 < plan.rounds {
            shrink_to(circ, u, v, value_width(r + 1));
        }
        replay(circ, r, tape[r]);
    }

    for r in plan.tail() {
        tape.push(walk_round(circ, u, v, r));
    }
    let loans = loan_terminal(circ, u, v);
    for r in plan.tail() {
        replay(circ, r, tape[r]);
    }
    endpoint(circ, plan, u, v, &coefficient, numerator);
    restore_terminal(circ, &loans);
    circ.free_vec(&coefficient);

    circ.set_phase("pp_div_walkback");
    for r in (0..tape.len()).rev() {
        let fix = match r {
            0 => a0_fix,
            1 => sign1_fix,
            _ => None,
        };
        walk_back_round(circ, u, v, r, tape[r], fix);
    }
    grow_to(circ, u, v, VALUE_WIDTH);
}

/// The time-reverse of [`divide_traversal`]: walk all the way out, then replay
/// each round just before its walk-back round.  Doubling order matches the
/// walk-back.
fn multiply_traversal(
    circ: &mut Builder,
    plan: &Plan,
    u: &mut Vec<QubitId>,
    v: &mut Vec<QubitId>,
    numerator: &[QubitId],
) {
    circ.set_phase("pp_mul_walk");
    let mut tape: Vec<QubitId> = (0..plan.rounds)
        .map(|r| walk_round(circ, u, v, r))
        .collect();
    let a0_fix = Some(free_sign_bit(circ, tape[0]));
    let bchain_fix =
        (BCHAIN_J < plan.r1 && plan.r1 < plan.rounds).then(|| free_sign_bit(circ, tape[BCHAIN_J]));

    circ.set_phase("pp_mul_replay");
    let coefficient = circ.alloc_qubits(N);
    // As in `divide`: the sign is a parameter so the loops below can keep
    // popping `tape`.
    let replay = |circ: &mut Builder, r: usize, sign: QubitId| {
        replay_doubling_round(circ, r, sign, &coefficient, numerator, plan.fold_window(r));
    };
    let loans = loan_terminal(circ, u, v);
    endpoint(circ, plan, u, v, &coefficient, numerator);
    for r in plan.tail().rev() {
        replay(circ, r, tape[r]);
    }
    restore_terminal(circ, &loans);

    circ.set_phase("pp_mul_walkback");
    for r in plan.tail().rev() {
        let sign = pop_tape(&mut tape, r);
        walk_back_round(circ, u, v, r, sign, None);
    }
    for r in plan.mid().rev() {
        replay(circ, r, tape[r]);
        let sign = pop_tape(&mut tape, r);
        walk_back_round(circ, u, v, r, sign, None);
    }

    for r in plan.head().rev() {
        if r == BCHAIN_J {
            if let Some(fix) = bchain_fix {
                tape[BCHAIN_J] = recompute_bchain_sign(circ, u, v, &tape, plan.r1, fix);
            }
        }
        replay(circ, r, tape[r]);
    }
    circ.free_vec(&coefficient);

    for r in plan.head().rev() {
        let sign = pop_tape(&mut tape, r);
        walk_back_round(circ, u, v, r, sign, if r == 0 { a0_fix } else { None });
    }
    grow_to(circ, u, v, VALUE_WIDTH);
}

fn pop_tape(tape: &mut Vec<QubitId>, round: usize) -> QubitId {
    let sign = tape.pop().expect("tape has round r");
    assert_eq!(tape.len(), round);
    sign
}

/// At the terminal state `coefficient` and `numerator` hold the same residue up
/// to their two signs, so negating each by its own sign leaves them equal and
/// one XOR clears `coefficient` for release.  The multiply traversal runs the
/// identical steps in the opposite order, to load it.
fn endpoint(
    circ: &mut Builder,
    plan: &Plan,
    u: &[QubitId],
    v: &[QubitId],
    coefficient: &[QubitId],
    numerator: &[QubitId],
) {
    let negate = |circ: &mut Builder| {
        conditional_mod_negate(circ, u[u.len() - 1], coefficient);
        conditional_mod_negate(circ, v[v.len() - 1], numerator);
    };
    match plan.direction {
        PingPongDirection::Divide => {
            negate(circ);
            circ.cx_pairs(&numerator[..N], &coefficient[..N]);
        }
        PingPongDirection::Multiply => {
            circ.cx_pairs(&numerator[..N], &coefficient[..N]);
            negate(circ);
        }
    }
}

/// Restore the compile-time register identity after streamed high wires have
/// served as tape.  If a wanted wire is currently free, swap the semantic bit
/// into it and return the now-zero displaced wire to the allocator.
fn restore_wire_layout(
    circ: &mut Builder,
    u: &mut [QubitId],
    v: &mut [QubitId],
    wanted_u: &[QubitId],
    wanted_v: &[QubitId],
) {
    let mut current: Vec<QubitId> = u.iter().chain(v.iter()).copied().collect();
    let wanted: Vec<QubitId> = wanted_u.iter().chain(wanted_v.iter()).copied().collect();
    assert_eq!(current.len(), wanted.len());

    for i in 0..current.len() {
        let want = wanted[i];
        if current[i] == want {
            continue;
        }
        if let Some(j) = current[i + 1..].iter().position(|&q| q == want) {
            let j = i + 1 + j;
            circ.swap(current[i], current[j]);
            current.swap(i, j);
        } else {
            circ.reacquire(want);
            circ.swap(current[i], want);
            circ.free(current[i]);
            current[i] = want;
        }
    }

    u.copy_from_slice(&current[..u.len()]);
    v.copy_from_slice(&current[u.len()..]);
    assert_eq!(u, wanted_u);
    assert_eq!(v, wanted_v);
}

// ─── Loaning idle walk wires to the allocator ──────────────────────────────

/// Round 0 lifts both values odd and every later round keeps them odd, so from
/// there to the matching walk-back `u[0]` and `v[0]` are a pair of constant ones.
/// Park them: clear each to |0> and hand it back to the allocator, which is free
/// to spend it on tape and ladders for the whole walk.
///
/// Bit 0 then lives at build time only.  The adder reads it as `target0_is_one`
/// and reconstructs its two carries classically; the halving rotation would have
/// used the wire only to feed a provable zero to the top of the register, which
/// an `X` supplies instead.  Index 0 is not read again until it is unparked, so
/// what it holds meanwhile is a dead placeholder.
fn park_odd_bits(circ: &mut Builder, u: &[QubitId], v: &[QubitId]) {
    assert_ne!(u[0], v[0]);
    for q in [u[0], v[0]] {
        circ.x(q);
        circ.release_clean(q);
    }
}

/// Take bit 0 back — on **whatever wire the allocator offers**, not the one that
/// was parked.
///
/// The park lasts the whole walk, and `grow_to` allocates freely across all of
/// it, so a parked wire may well have been spent as a register wire by now.
/// Reacquiring it by id is therefore not sound (and panics when it happens, at a
/// round count that depends only on the pool's history). Taking a fresh wire is:
/// the walk already streams wire identity around, and `restore_wire_layout` puts
/// the ABI wires back at the end.
fn unpark_odd_bits(circ: &mut Builder, u: &mut [QubitId], v: &mut [QubitId]) {
    for reg in [v, u] {
        reg[0] = circ.alloc_qubit();
        circ.x(reg[0]);
    }
}

/// The same trick over the whole terminal state: there every bit below the sign
/// is a copy of the sign (the values are the two's-complement +1 and -1), and the
/// trailing replay batch reads only the two sign wires.  Bit 0 is parked already.
///
/// Each loan records the wire and the sign wire to re-derive it from.
fn loan_terminal(circ: &mut Builder, u: &[QubitId], v: &[QubitId]) -> Vec<(QubitId, QubitId)> {
    let mut loans = Vec::new();
    for reg in [u, v] {
        let sign = reg[reg.len() - 1];
        for &q in &reg[1..reg.len() - 1] {
            circ.cx(sign, q);
            circ.free(q);
            loans.push((q, sign));
        }
    }
    loans
}

fn restore_terminal(circ: &mut Builder, loans: &[(QubitId, QubitId)]) {
    for &(q, sign) in loans.iter().rev() {
        circ.reacquire(q);
        circ.cx(sign, q);
    }
}

// ─── Width schedule ────────────────────────────────────────────────────────

/// Per-round walk width schedule, optimised against the measured per-round
/// magnitude distribution of the recurrence.
///
/// It is a knob only in the sense every other pinned value is -- overridable for
/// a sweep without touching code. It is not fitted data you may hand-edit:
/// narrowing it has been measured repeatedly and loses, and any change re-rolls
/// the shot draw and invalidates the ground nonce.
fn width_schedule() -> &'static [usize] {
    static SLOT: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    SLOT.get_or_init(|| parse_width_schedule(&required_env::<String>("PP_WIDTH_SCHEDULE")))
}

/// Expand `"259x1,258x19,..."`, enforcing what the construction relies on:
/// [`shrink_to`] only ever shrinks, so the schedule must be non-increasing, and
/// no round may ask for more than the envelope [`VALUE_WIDTH`] holds.
fn parse_width_schedule(spec: &str) -> Vec<usize> {
    let mut out: Vec<usize> = Vec::new();
    for run in spec.split(',').map(str::trim).filter(|r| !r.is_empty()) {
        let (width, count) = run.split_once('x').unwrap_or((run, "1"));
        let bad = || panic!("PP_WIDTH_SCHEDULE: {run:?} is not `width` or `width x count`");
        let (width, count) = match (width.trim().parse(), count.trim().parse::<usize>()) {
            (Ok(w), Ok(n)) => (w, n),
            _ => bad(),
        };
        assert!(count > 0, "PP_WIDTH_SCHEDULE: {run:?} has a zero run");
        // 5 is where the construction breaks, not where it stops being a good
        // idea: the walk adder runs on the bit-1-and-up slice, `width - 1` wires,
        // and asserts at least 4 of them. The shipped schedule bottoms out at 8,
        // which is inherited from upstream's `clamp(.., 8, VALUE_WIDTH)` and is a
        // fitted quantile rather than a limit -- going below it builds and runs,
        // it just loses badly: 8 -> 5 saves 96 Toffoli for +2.7 lambda, ~130x
        // off the exchange rate every other width knob trades at.
        assert!(
            (MIN_WALK_WIDTH..=VALUE_WIDTH).contains(&width),
            "PP_WIDTH_SCHEDULE: width {width} is outside \
             {MIN_WALK_WIDTH}..={VALUE_WIDTH}"
        );
        assert!(
            out.last().is_none_or(|&previous| previous >= width),
            "PP_WIDTH_SCHEDULE: {width} rises above the previous run; \
             shrink_to cannot grow the walk registers back"
        );
        out.extend(std::iter::repeat_n(width, count));
    }
    assert!(!out.is_empty(), "PP_WIDTH_SCHEDULE is empty");
    out
}

fn value_width(round: usize) -> usize {
    width_schedule()[round]
}

/// The fold-window shape: how many bits of window a round wants, relative to the
/// pinned base, as a function of **the walk's width at that round**.
///
/// MEASURED, not derived. The replay cell's fold drops the carry off the top of
/// its slice, and the rate at which that carry actually escapes is not the same
/// at every round. Narrowing one block of rounds at a time against a flat
/// baseline and counting the shots that newly fail — 300,000 per point through
/// the classical replay model — gives, relative to the flat region:
///
/// ```text
///   walk width   253..73   54    47    41    35    28    21    15     8
///   rate/flat     0.88-1.06  0.98  0.91  0.70  0.46  0.14  0.074  0.054  0.049
/// ```
///
/// Flat across a 3.5x span of widths, then a monotone collapse once the walk
/// falls below ~45. **The walk's remaining magnitude is the driver, not the
/// round index** — which is why this is keyed on [`value_width`] and not on `r`.
/// Keying it on the round would go stale the moment `PP_WIDTH_SCHEDULE`
/// was regenerated, silently and without changing a single pin.
///
/// Minimising total window bits at fixed total error equalises the PER-ROUND
/// error, so the wanted offset is `round(log2(rate))`, which is the band table.
fn fold_shape() -> &'static [(usize, isize)] {
    static SLOT: std::sync::OnceLock<Vec<(usize, isize)>> = std::sync::OnceLock::new();
    SLOT.get_or_init(|| band_table("PP_FOLD_PROFILE"))
}

// How many leading rounds carry one extra bit. This is the LEVEL, not the shape,
// and it is deliberately a separate quantity: windows are integers and the error
// the fit wants sits between two of them, so a fraction of the flat region has to
// carry the extra bit. Which rounds does not matter -- the ten blocks spanning
// the flat region measure 0.96 to 1.19, i.e. flat well inside what one bit
// resolves. Folding it into the band table as a width threshold would work
// today and would make regenerating the width schedule move the level too.
pinned_env!(fold_widen, "PP_FOLD_WIDEN");

/// Window offset for `round`, relative to the direction's pinned base.
fn fold_offset(round: usize) -> isize {
    band_at(fold_shape(), value_width(round)) + isize::from(round < fold_widen())
}

/// Read a `width:offset` band table out of the environment.
fn band_table(knob: &'static str) -> Vec<(usize, isize)> {
    parse_band_table(knob, &required_env::<String>(knob))
}

/// The offset the table gives a round whose walk register is `width` wide.
fn band_at(bands: &[(usize, isize)], width: usize) -> isize {
    bands
        .iter()
        .find(|&&(from, _)| width >= from)
        .map(|&(_, offset)| offset)
        .expect("a band table covers every width")
}

/// Width of the comparison that repairs a chunk boundary at `round`, in bits.
///
/// MEASURED, the same way and for the same reason as [`fold_shape`]: the repair
/// is wrong when the compared top bits of the chunk's sum and addend agree, and
/// how often that happens is **not** the same at every round. Narrowing the
/// comparison on one band of rounds at a time and reading the failing-shot count
/// off `eval_circuit` gives, per boundary and relative to the wide-walk rate:
///
/// ```text
///   walk width   69..38     37..25     25..8
///   rate          1.00       0.33       0.04
/// ```
///
/// So the late boundaries are two to four bits over-provisioned. Equalising the
/// per-boundary error is what minimises total width at fixed error, hence the
/// bands.
///
/// **The layout keeps the flat width.** [`chunk_layout`] uses
/// `replay_chunk_compare()` to decide which leading chunk gets an exact repair,
/// which makes that knob a structural parameter as well as an error one -- so the
/// shape is applied to the comparison ONLY, and the chunk boundaries themselves
/// are identical with it and without it.
fn chunk_compare(round: usize) -> usize {
    static SLOT: std::sync::OnceLock<Vec<(usize, isize)>> = std::sync::OnceLock::new();
    let bands = SLOT.get_or_init(|| band_table("PP_CHUNK_SHAPE"));
    replay_chunk_compare()
        .checked_add_signed(band_at(bands, value_width(round)))
        .expect("the chunk shape keeps the comparison positive")
}

/// Width of the comparison that repairs the replay cell's overflow flag at
/// `round`, in bits.
///
/// The third window measured this way and the third that turned out not to be
/// flat. Same predicate shape as [`chunk_compare`] -- the top `k` bits of the two
/// replay registers -- and it collapses on the same schedule: per instance,
/// relative to the wide-walk rate, 1.00 at walk widths 69..38, 0.19 at 37..25,
/// 0.044 below. Unlike the chunk compare this width is nothing but an error
/// knob, so the bands apply with nothing to decouple.
fn flag_compare(round: usize) -> usize {
    static SLOT: std::sync::OnceLock<Vec<(usize, isize)>> = std::sync::OnceLock::new();
    let bands = SLOT.get_or_init(|| band_table("PP_FLAG_SHAPE"));
    replay_flag_compare()
        .checked_add_signed(band_at(bands, value_width(round)))
        .expect("the flag shape keeps the comparison positive")
}

/// The first round the shape narrows at, i.e. the first whose walk width has
/// dropped below the top band. The trailing replay batch is the one region whose
/// fold sets the peak, so it must lie entirely above this -- which is what
/// bounds [`plan_r2`] from below.
fn fold_ramp_start() -> usize {
    (0..rounds_div())
        .find(|&r| fold_offset(r) < 0)
        .unwrap_or_else(rounds_div)
}

/// Expand `"38:0,32:-1,..."` -- `width:offset` bands, widest first, each entry a
/// lower bound on the walk width. The last band must start at 0 so every width
/// is covered, and the bands must descend so `find` picks the right one.
fn parse_band_table(knob: &str, spec: &str) -> Vec<(usize, isize)> {
    let mut out: Vec<(usize, isize)> = Vec::new();
    for band in spec.split(',').map(str::trim).filter(|b| !b.is_empty()) {
        let (width, offset) = (|| {
            let (width, offset) = band.split_once(':')?;
            let width = width.trim().parse::<usize>().ok()?;
            let offset = offset.trim().parse::<isize>().ok()?;
            Some((width, offset))
        })()
        .unwrap_or_else(|| panic!("{knob}: {band:?} is not `width:offset`"));
        assert!(
            (-16..=16).contains(&offset),
            "{knob}: offset {offset} is outside -16..=16"
        );
        assert!(
            out.last().is_none_or(|&(previous, _)| previous > width),
            "{knob}: band {width} does not descend below the one before it"
        );
        out.push((width, offset));
    }
    assert!(
        out.last().is_some_and(|&(width, _)| width == 0),
        "{knob} must end at width 0 so every walk width is covered"
    );
    out
}

fn shrink_to(circ: &mut Builder, u: &mut Vec<QubitId>, v: &mut Vec<QubitId>, width: usize) {
    while u.len() > width {
        let (lu, lv) = (u.len(), v.len());
        circ.cx(u[lu - 2], u[lu - 1]);
        circ.cx(v[lv - 2], v[lv - 1]);
        circ.free(u.pop().expect("u has the scheduled width"));
        circ.free(v.pop().expect("v has the scheduled width"));
    }
}

fn grow_to(circ: &mut Builder, u: &mut Vec<QubitId>, v: &mut Vec<QubitId>, width: usize) {
    while u.len() < width {
        let next_u = circ.alloc_qubit();
        let next_v = circ.alloc_qubit();
        circ.cx(u[u.len() - 1], next_u);
        circ.cx(v[v.len() - 1], next_v);
        u.push(next_u);
        v.push(next_v);
    }
}

// ─── The walk ──────────────────────────────────────────────────────────────

/// One forward walk round; returns the sign qubit to append to the tape.
fn walk_round(
    circ: &mut Builder,
    u: &mut Vec<QubitId>,
    v: &mut Vec<QubitId>,
    round: usize,
) -> QubitId {
    let width = value_width(round);
    shrink_to(circ, u, v, width);
    if round == 0 {
        let a0 = round0_forward(circ, v);
        park_odd_bits(circ, u, v);
        return a0;
    }
    if round == 1 {
        return round1_forward(circ, &u[1..width], &v[1..width]);
    }
    let (source, target) = walk_operands(u, v, round, width);
    let m = target.len();
    let sign = circ.alloc_qubit();
    circ.cx(target[0], sign);
    circ.cx(source[0], sign);
    walk_add(circ, sign, source, target, true);
    // Halve: rotate the register down. The sum's bit 1 is one -- that is what
    // `sign` was chosen for -- so the wire it vacates arrives at the top holding
    // a one, and an X leaves it clean for the sign extension.
    rotate_down(circ, target);
    circ.x(target[m - 1]);
    circ.cx(target[m - 2], target[m - 1]);
    sign
}

/// One reverse walk round; consumes and frees the round's sign qubit.
///
/// `fix` is the measurement outcome of a tape wire that [`free_sign_bit`] took
/// out early, whose deferred phase this round has to cancel. Rounds 0 and 1 are
/// the only ones that can carry one, and how many arrive differs by direction:
/// the divide walk-back carries both, the multiply's only round 0's, because
/// [`BCHAIN_J`]'s fix is consumed by [`recompute_bchain_sign`] during the replay
/// and never reaches here.
fn walk_back_round(
    circ: &mut Builder,
    u: &mut Vec<QubitId>,
    v: &mut Vec<QubitId>,
    round: usize,
    sign: QubitId,
    fix: Option<BitId>,
) {
    let width = value_width(round);
    grow_to(circ, u, v, width);
    if round == 0 {
        unpark_odd_bits(circ, u, v);
        let a0 = fix.map_or(sign, |c| {
            let a = recompute_a0(circ, v);
            circ.z_if(a, c);
            circ.free_bit(c);
            a
        });
        return round0_reverse(circ, v, a0);
    }
    if round == 1 {
        let sign = fix.map_or(sign, |c| {
            // sign_1 = NOT v[1]: v is round 1's untouched source and walkback has
            // restored it exactly. Z^c cancels the deferred measurement phase.
            let s = circ.alloc_qubit();
            circ.x(s);
            circ.cx(v[1], s);
            circ.z_if(s, c);
            circ.free_bit(c);
            s
        });
        return round1_reverse(circ, &u[1..width], &v[1..width], sign);
    }
    let (source, target) = walk_operands(u, v, round, width);
    let m = target.len();
    // Double: the mirror of the halving rotation. The top wire is a sign copy, so
    // the CX clears it; it comes back round to the bottom, where bit 1 of twice
    // an odd value is a one.
    circ.cx(target[m - 2], target[m - 1]);
    rotate_up(circ, target);
    circ.x(target[0]);
    circ.x(sign);
    walk_add(circ, sign, source, target, false);
    circ.x(sign);
    circ.cx(target[0], sign);
    circ.cx(source[0], sign);
    circ.free(sign);
}

/// `u` and `v` take turns being the target; even rounds fold `u` into `v`.
/// Index 0 is the parked constant-one bit, so the operands start at bit 1.
fn walk_operands<'a>(
    u: &'a [QubitId],
    v: &'a [QubitId],
    round: usize,
    width: usize,
) -> (&'a [QubitId], &'a [QubitId]) {
    if round.is_multiple_of(2) {
        (&u[1..width], &v[1..width])
    } else {
        (&v[1..width], &u[1..width])
    }
}

// ─── The walk adder ────────────────────────────────────────────────────────

/// Ping-pong's wrapped signed add, `target += (-1)^sign * source`.
///
/// The operands are the walk registers WITHOUT their bit 0: `source[j]` and
/// `target[j]` hold bit `j + 1`.  Both values are odd, so the source's bit 0 is
/// a constant one and the target's is `target0_is_one` (before the complement
/// sandwich), which makes the two lowest carries classical:
///
/// ```text
///     carry into bit 1 = sign ^ target0        carry into bit 2 = source's bit 1
/// ```
///
/// so the generic chain's first two ANDs never have to be emitted — and the two
/// bit-0 wires never have to be held (see [`park_odd_bits`]).
///
/// PRECONDITION: `sign = target[0] ^ source[0]`, which is the choice that keeps
/// the halved sum odd.
///
/// Wide enough, and the ladder is split in two so that only about half the
/// carries are ever live at once. [`walk_low_chunk`] decides that from the live
/// count, which is why the caller passes nothing: both call sites reach here
/// with the round's whole footprint already allocated.
fn walk_add(
    circ: &mut Builder,
    sign: QubitId,
    source: &[QubitId],
    target: &[QubitId],
    target0_is_one: bool,
) {
    match walk_low_chunk(circ, source.len()) {
        Some(low) => walk_add_split(circ, sign, source, target, target0_is_one, low),
        None => walk_add_single(circ, sign, source, target, target0_is_one),
    }
}

/// `q ^= c1`, where `c1 = sign ^ target0` is the carry into bit 1.  It is a
/// classical function of one wire, so it never needs materialising.
fn carry1_into(circ: &mut Builder, sign: QubitId, target0_is_one: bool, q: QubitId) {
    circ.cx(sign, q);
    if target0_is_one {
        circ.x(q);
    }
}

/// [`carry1_into`] backwards. The two gates commute; emitting them in the
/// mirrored order keeps the unwind an exact op-level inverse.
fn carry1_undo(circ: &mut Builder, sign: QubitId, target0_is_one: bool, q: QubitId) {
    if target0_is_one {
        circ.x(q);
    }
    circ.cx(sign, q);
}

fn walk_add_single(
    circ: &mut Builder,
    sign: QubitId,
    source: &[QubitId],
    target: &[QubitId],
    target0_is_one: bool,
) {
    let m = source.len();
    assert_eq!(m, target.len());
    assert!(m >= MIN_WALK_WIDTH - 1, "walk width below MIN_WALK_WIDTH");

    circ.cx_all(sign, target);
    // The carry out of bit 2, and the only carry this function owns: everything
    // above it is a plain wrapped ripple, carried in on this wire.
    let carry2 = circ.alloc_qubit();

    // Bits 1 and 2, whose carries-in are classical.
    carry1_into(circ, sign, target0_is_one, source[0]);
    carry1_into(circ, sign, target0_is_one, target[0]);
    circ.cx(source[0], source[1]);
    carry1_into(circ, sign, target0_is_one, source[1]);
    circ.cx(source[0], target[1]);
    carry1_into(circ, sign, target0_is_one, target[1]);
    circ.ccx(source[1], target[1], carry2);
    circ.cx(source[0], carry2);
    carry1_into(circ, sign, target0_is_one, carry2);

    ripple_add(circ, &source[2..], &target[2..], Some(carry2), None);

    // Bit 2, in reverse: mirrors the special case above.
    circ.cx(source[0], carry2);
    carry1_into(circ, sign, target0_is_one, carry2);
    let measured = circ.alloc_bit();
    circ.hmr(carry2, measured);
    circ.cz_if(source[1], target[1], measured);
    circ.free_bit(measured);
    circ.cx(source[0], source[1]);
    carry1_into(circ, sign, target0_is_one, source[1]);
    circ.cx(source[1], target[1]);

    carry1_into(circ, sign, target0_is_one, source[0]);
    circ.cx(source[0], target[0]);
    circ.free(carry2);

    circ.cx_all(sign, target);
}

/// Bit position to split the walk add at, or `None` for the single-ladder form.
///
/// The high chunk is the binding moment: it holds everything already live plus
/// the boundary carry and its own `m - low + 1 - 2` carries ([`ripple_add`]
/// fuses the top two positions when it has no carry-out), so its width is
/// `live + (m - low)` and the narrowest split that fits [`walk_max_qubits`] is
/// `low = live + m - peak`.  Narrowest is also cheapest: splitting costs exactly
/// `low` emitted Toffoli, and no new truncation at all, because the boundary
/// carry is repaired EXACTLY (see [`walk_add_split`]).
///
/// Asking the builder for the live count is what keeps this honest: it already
/// knows about the tape, the coefficient pair, the parked bit-0 pair and the two
/// tape signs [`free_sign_bit`] retires early, so none of them appear here and
/// none of them can drift.  Rounds where the coefficient pair is not live come
/// out `None` on their own — the ladder has room and no split is called for.
///
/// The two rejections below are both exact, not margins:
///
///   * `low < 4` is where the single ladder still fits. It is three wires
///     lighter than the formula above assumes — no boundary wire, and its two
///     lowest carries are classical ([`walk_add_single`]) — so it peaks at
///     `live + m - 3`, which is under the cap for every `low <= 3`.
///   * `2*low <= n` is the low chunk's own footprint: it holds `low - 1` wires
///     against the high chunk's `m - low`, so a split past the midpoint would
///     move the binding moment rather than relieve it. Splitting cannot help
///     there, and the pinned configuration never reaches it.
///
/// The other two conditions are neither. `low + 2 <= n` is implied by
/// `2*low <= n` once `n >= 12`; it is written out because it is the form
/// [`walk_add_split`]'s `low < m` assert is in. `n < 12` excludes the narrowest
/// rounds from splitting outright. Both were instrumented across the pinned
/// build and neither ever binds -- a round narrow enough for the `n < 12` test
/// never reaches `low >= 4` anyway -- so at this budget `low < 4` is the only
/// live rejection.
fn walk_low_chunk(circ: &Builder, m: usize) -> Option<usize> {
    // `low` is a bit position, so it counts against the full value width.
    let n = m + 1;
    let low = (circ.active_qubits() as usize + m).saturating_sub(walk_max_qubits());
    if n < 12 || low < 4 {
        return None;
    }
    (low + 2 <= n && low * 2 <= n).then_some(low)
}

/// The carry out of bit `low - 1` is kept as the high chunk's carry-in while
/// every carry below it is measurement-uncomputed, so the live ladder is
/// `max(low - 1, n - low)` instead of `n - 1`.  That boundary carry is then erased by
/// measurement and repaired with `sum_low < addend_low` over the *whole* low
/// chunk: the walk add has no carry-in, so that comparison is an identity, the
/// repair is exact, and the walk arithmetic (hence convergence and lambda) is
/// bit-for-bit what the single-ladder form produces.
fn walk_add_split(
    circ: &mut Builder,
    sign: QubitId,
    source: &[QubitId],
    target: &[QubitId],
    target0_is_one: bool,
    low: usize,
) {
    let m = source.len();
    assert_eq!(m, target.len());
    // `walk_low_chunk` never returns a narrower split: the boundary repair
    // compares `low - 2` bits per operand and `cmp_lt_phase` needs at least two.
    assert!(low >= 4 && low < m);

    circ.cx_all(sign, target);

    // Bit 0's carry is the classical `c1` and gets no wire at all; bit 1's is
    // the source's own bit 1, copied out only because that wire is about to
    // absorb `c1`. That copy is the low chunk's carry-in, and the carry off the
    // chunk's top is the boundary the high chunk rides in on.
    let carry1 = circ.alloc_qubit();
    let boundary = circ.alloc_qubit();
    circ.cx(source[0], carry1);
    carry1_into(circ, sign, target0_is_one, source[0]);
    carry1_into(circ, sign, target0_is_one, target[0]);

    // The low chunk vents its top carry onto `boundary` and retires its own
    // ladder in the same call, so the two chunks' ladders are never live
    // together.
    ripple_add(
        circ,
        &source[1..low - 1],
        &target[1..low - 1],
        Some(carry1),
        Some(boundary),
    );
    carry1_undo(circ, sign, target0_is_one, source[0]);
    circ.cx(source[0], carry1);
    circ.cx(source[0], target[0]);
    circ.free(carry1);

    // High chunk, carried in on `boundary` and wrapping at the top.
    assert!(m - low >= 1, "low + 1 <= m leaves a final high carry");
    ripple_add(
        circ,
        &source[low - 1..],
        &target[low - 1..],
        Some(boundary),
        None,
    );

    erase_boundary_carry(circ, source, target, boundary, low);

    circ.cx_all(sign, target);
}

/// Bits `0..low` of the complemented-frame sum are now in `target` and the
/// untouched addend in `source`, so `sum < addend` over them is the boundary
/// carry itself.  Bits 0 and 1 of that comparison are classical: on the forward
/// walk the target's bit 0 is one and `sign = target[0] ^ source[0]`; on walk-back
/// its bits 1:0 are `10` after undoing the halving rotation.  The source's bit 0
/// is one either way, so the borrow out of the first two positions is exactly the
/// source's bit 1 — start the comparator at bit 2 with that as its live carry-in
/// and two nonlinear stages drop out exactly.
fn erase_boundary_carry(
    circ: &mut Builder,
    source: &[QubitId],
    target: &[QubitId],
    boundary: QubitId,
    low: usize,
) {
    // Bits 2..low, with the source's bit 1 standing in for everything below.
    erase_with_compare(
        circ,
        boundary,
        &target[1..low - 1],
        &source[1..low - 1],
        Some(source[0]),
    );
    circ.free(boundary);
}

// ─── Rounds 0 and 1: the lift into the invariant ───────────────────────────

/// Fuse the odd lift `a -= (!a0)*p` with ping-pong's first add and shift.
/// With `p = 2^N-f`, `h=(f-1)/2`, and `q=floor(a/2)`, the four low-bit arms are
/// one sparse map: `q - p + a1*p + a0*(p+1)/2`.
fn round0_forward(circ: &mut Builder, v: &[QubitId]) -> QubitId {
    assert_eq!(v.len(), VALUE_WIDTH);
    let a0 = circ.alloc_qubit();
    circ.cx(v[0], a0);
    rotate_down(circ, v);
    circ.cx(a0, v[VALUE_WIDTH - 1]);

    let not_a1 = circ.alloc_qubit();
    circ.x(not_a1);
    circ.cx(v[0], not_a1);

    round0_correction(circ, v, not_a1, a0);
    circ.cx_all(not_a1, &v[N..]);
    circ.cx(a0, v[N - 1]);

    // The four output ranges are disjoint: a1=0 is negative and a1=1 positive.
    circ.cx(v[VALUE_WIDTH - 1], not_a1);
    circ.free(not_a1);
    a0
}

/// Compute `a AND c` onto a fresh wire: one Toffoli.
fn and_clean(circ: &mut Builder, a: QubitId, c: QubitId) -> QubitId {
    let out = circ.alloc_qubit();
    circ.ccx(a, c, out);
    out
}

/// Erase an `and_clean` wire -- or any wire holding `a AND c`, such as a ripple
/// carry -- by measuring it out in the X basis and cancelling the phase that
/// costs with a CZ on the two inputs. Zero Toffoli.
fn and_uncompute(circ: &mut Builder, out: QubitId, a: QubitId, c: QubitId) {
    let measured = circ.alloc_bit();
    circ.hmr(out, measured);
    circ.cz_if(a, c, measured);
    circ.free_bit(measured);
    circ.free(out);
}

/// The four lift arms as one per-position controlled constant add.
fn round0_correction(circ: &mut Builder, v: &[QubitId], not_a1: QubitId, a0: QubitId) {
    let e = and_clean(circ, not_a1, a0);
    let g = circ.alloc_qubit();
    circ.cx(not_a1, g);
    circ.cx(e, g);
    let gx = circ.alloc_qubit();
    circ.cx(g, gx);
    circ.cx(a0, gx);

    // Every arm's magnitude is `f` or `h`, so this is an ordinary truncated fold
    // of a 33-bit constant and takes the tree-wide slice.
    let width = f_slice();
    let f = f();
    let h = half_f_minus_one();
    let controls: Vec<Option<QubitId>> = (0..width)
        .map(|i| {
            let (in_f, in_h) = (f.bit(i), h.bit(i));
            if i == 0 {
                assert!(in_f && !in_h, "f's bit 0 is set and h's is not");
                return Some(not_a1);
            }
            match (in_f, in_h) {
                (false, false) => None,
                (true, false) => Some(g),
                (false, true) => Some(a0),
                (true, true) => Some(gx),
            }
        })
        .collect();

    // The complement sandwich needs a wire holding `a1` as its CONTROL, but
    // `controls[0]` above already reads `not_a1` itself as the position-0 addend
    // control -- reusing `not_a1` for both (e.g. by X-flipping it in place) would
    // corrupt position 0's control for the very add that reads it. Materialise
    // `a1` on a fresh, Clifford-only (free) ancilla instead, leaving `not_a1`
    // untouched throughout.
    let a1 = circ.alloc_qubit();
    circ.x(a1);
    circ.cx(not_a1, a1);

    circ.cx_all(a1, &v[..N]);
    cadd_const_per_position_trunc(circ, &v[..width], &controls);
    circ.cx_all(a1, &v[..N]);

    circ.cx(not_a1, a1);
    circ.x(a1);
    circ.free(a1);

    circ.cx(a0, gx);
    circ.cx(g, gx);
    circ.free(gx);
    circ.cx(e, g);
    circ.cx(not_a1, g);
    circ.free(g);
    and_uncompute(circ, e, not_a1, a0);
}

/// Recover the canonical denominator from the signed round-zero half-state with
/// one short pseudo-Mersenne carry chain.  If `w` is that state, then
/// `2w = a + k*p`, where `k = a0 - 2*!a1`.  Since `p = 2^256-f`, the low word of
/// `2w` needs only the sparse correction `k*f`.
fn round0_reverse(circ: &mut Builder, v: &[QubitId], a0: QubitId) {
    assert_eq!(v.len(), VALUE_WIDTH);
    let not_a1 = circ.alloc_qubit();
    circ.cx(v[VALUE_WIDTH - 1], not_a1);

    // Arithmetic left shift in the signed 259-bit envelope. The discarded sign
    // copy is redundant; the three new high bits are (a0,!a1,!a1).
    circ.cx(not_a1, v[VALUE_WIDTH - 1]);
    rotate_up(circ, v);

    // k*f is +a0*f when !a1=0 and -(2-a0)*f otherwise. A complement sandwich
    // turns both signs into one selected-magnitude addition.
    let both = and_clean(circ, not_a1, a0);
    let not_a1_and_not_a0 = circ.alloc_qubit();
    circ.cx(not_a1, not_a1_and_not_a0);
    circ.cx(both, not_a1_and_not_a0);
    let selector_xor = circ.alloc_qubit();
    circ.cx(a0, selector_xor);
    circ.cx(not_a1_and_not_a0, selector_xor);
    // The selected magnitude is `f` or `2f`, so the constant is one bit wider
    // than [`f_slice`] assumes and the same guard has to sit above that.
    let width = f_slice() + 1;
    let f = f();
    let controls: Vec<Option<QubitId>> = (0..width)
        .map(|i| match (f.bit(i), i > 0 && f.bit(i - 1)) {
            (false, false) => None,
            (true, false) => Some(a0),
            (false, true) => Some(not_a1_and_not_a0),
            (true, true) => Some(selector_xor),
        })
        .collect();
    circ.cx_all(not_a1, &v[..N]);
    cadd_const_per_position_trunc(circ, &v[..width], &controls);
    circ.cx_all(not_a1, &v[..N]);
    circ.cx(not_a1_and_not_a0, selector_xor);
    circ.cx(a0, selector_xor);
    circ.free(selector_xor);
    circ.cx(both, not_a1_and_not_a0);
    circ.cx(not_a1, not_a1_and_not_a0);
    circ.free(not_a1_and_not_a0);
    and_uncompute(circ, both, not_a1, a0);

    circ.cx(a0, v[N]);
    circ.cx(not_a1, v[N + 1]);
    circ.cx(not_a1, v[N + 2]);
    circ.cx(v[1], not_a1);
    circ.x(not_a1);
    circ.free(not_a1);
    circ.cx(v[0], a0);
    circ.free(a0);
}

/// Borrow window for the sparse `h` correction, in wires of the bit-1-and-up
/// operand.  `h` is even, so what is actually added is `h/2` at bit 1 and up,
/// whose top bit is 30: the `31` is that constant's width, not a knob, and
/// [`fold_guard`] is the headroom above it -- the same shape as
/// [`super::modular::f_slice`], one bit-width down.  Add and subtract use the
/// identical slice, so the pair is an exact mutual inverse; the approximation is
/// only that a borrow which would have run past the slice is dropped
/// (~2^-guard per execution).
///
/// One asymmetry the shared knob does not capture: FOUR call sites pay the
/// Toffoli (forward and reverse, both directions) but only TWO leak, because the
/// walk-back's truncation exactly inverts the forward's. That halves this site's
/// effective sell rate, so it wants about one bit less than the common guard.
/// One bit here is four Toffoli, which is inside the rounding.
fn round1_window(m: usize) -> usize {
    (31 + fold_guard()).min(m)
}

/// `u <- (p + (-1)^sign * v) / 2`, with `u` still holding the classical `p`.
///
/// As everywhere in the walk, `u[j]` and `v[j]` hold bit `j + 1`; bit 0 goes from
/// one (`p`) to one (an odd result) and needs no gate.  The intermediate
/// `(-1)^s (v>>1) - s` has bit 0 = `v[0] ^ sign`, which is one because
/// `sign = p[1] ^ v[0]` and `p[1]` is set, and `(p+1)/2` is even — so no carry
/// crosses into bit 1 either.
fn round1_forward(circ: &mut Builder, u: &[QubitId], v: &[QubitId]) -> QubitId {
    let m = u.len();
    assert_eq!(m, v.len());
    assert!(m >= N);
    let sign = circ.alloc_qubit();
    circ.cx(u[0], sign);
    circ.cx(v[0], sign);
    // u still holds the classical p: clear it.
    for (j, &q) in u.iter().enumerate() {
        if SECP256K1_P.bit(j + 1) {
            circ.x(q);
        }
    }
    // u <- arithmetic v>>1, complemented when sign = 1, i.e. (-1)^s (v>>1) - s.
    for j in 0..m - 1 {
        circ.cx(v[j + 1], u[j]);
    }
    circ.cx(v[m - 1], u[m - 1]);
    circ.cx_all(sign, u);
    // u += (p+1)/2 = 2^255 - h. The two halves touch disjoint slices.
    sub_const(circ, &u[..round1_window(m)], half_f_minus_one() >> 1);
    add_const(circ, &u[N - 2..], U256::from(1));
    sign
}

fn round1_reverse(circ: &mut Builder, u: &[QubitId], v: &[QubitId], sign: QubitId) {
    let m = u.len();
    assert_eq!(m, v.len());
    sub_const(circ, &u[N - 2..], U256::from(1));
    add_const(circ, &u[..round1_window(m)], half_f_minus_one() >> 1);
    circ.cx_all(sign, u);
    circ.cx(v[m - 1], u[m - 1]);
    for j in (0..m - 1).rev() {
        circ.cx(v[j + 1], u[j]);
    }
    for (j, &q) in u.iter().enumerate() {
        if SECP256K1_P.bit(j + 1) {
            circ.x(q);
        }
    }
    circ.cx(u[0], sign);
    circ.cx(v[0], sign);
    circ.free(sign);
}

// ─── Freeing tape wires early ──────────────────────────────────────────────

/// Measure a tape wire out in the X basis and release it, deferring its sign to
/// walkback. The returned outcome is the phase walkback has to cancel.
///
/// TWO tape wires per traversal are freed this way, and each buys a unit of peak
/// width: round 0's lift bit and round 1's sign on the divide traversal, round 0
/// plus [`BCHAIN_J`] on the multiply one. That pair is what [`MODEL_OVERCOUNT`]
/// counts as "the two tape signs". All four are recomputed from state the walk
/// has already restored, so none of them costs a Toffoli.
fn free_sign_bit(circ: &mut Builder, sign: QubitId) -> BitId {
    let c = circ.alloc_bit();
    circ.hmr(sign, c);
    circ.free(sign);
    c
}

/// Recompute the round-0 lift bit `a0` from the restored round-0 output held in
/// `v`.
///
/// The four lift arms make `a0` equal bit 255 of `w`'s low word except on a
/// 2^-225 slice, so one CX does what a truncated 55-Toffoli carry chain over
/// `round1_window` would -- at a miss rate three orders below the 2^-27 that
/// chain itself carried.
fn recompute_a0(circ: &mut Builder, v: &[QubitId]) -> QubitId {
    assert_eq!(v.len(), VALUE_WIDTH);
    let out = circ.alloc_qubit();
    circ.cx(v[N - 1], out);
    out
}

/// The multiply traversal's B-chain round, whose tape wire is erased after the
/// walk and recomputed at the final batch.
const BCHAIN_J: usize = 1;

/// Recompute `tape[BCHAIN_J]` lazily, right before its first consumer.
///
/// The walk registers idle at the pre-round-`r1` state for the whole batch:
/// `b_{r1}`, bit 1 of round `r1`'s target, is live and so is every other tape
/// wire below `r1`, so `sign_J = 1 ^ b_{r1} ^ parity(tape[1..r1] \ J)`.
fn recompute_bchain_sign(
    circ: &mut Builder,
    u: &[QubitId],
    v: &[QubitId],
    tape: &[QubitId],
    r1: usize,
    fix: BitId,
) -> QubitId {
    let s = circ.alloc_qubit();
    circ.x(s);
    let b_r1 = if r1.is_multiple_of(2) { v[1] } else { u[1] };
    circ.cx(b_r1, s);
    for (k, &t) in tape.iter().enumerate().take(r1).skip(1) {
        if k != BCHAIN_J {
            circ.cx(t, s);
        }
    }
    circ.z_if(s, fix);
    s
}

// ─── The replay ────────────────────────────────────────────────────────────

/// The replay's registers take turns the same way the walk's do.
fn replay_operands<'a>(
    x: &'a [QubitId],
    y: &'a [QubitId],
    round: usize,
) -> (&'a [QubitId], &'a [QubitId]) {
    if round.is_multiple_of(2) {
        (x, y)
    } else {
        (y, x)
    }
}

fn replay_halving_round(
    circ: &mut Builder,
    round: usize,
    sign: QubitId,
    x: &[QubitId],
    y: &[QubitId],
    fold_window: usize,
) {
    let (source, target) = replay_operands(x, y, round);
    match round {
        // Rounds 0 and 1 run in the canonical frame; the signed frame is entered
        // once both registers hold a residue in [0,p). Neither folds, so
        // `fold_window` does not reach them -- they keep the pinned width.
        0 => mod_halve_pm(circ, target),
        1 => {
            seed_round_one(circ, sign, source, target);
            mod_halve_pm(circ, target);
        }
        _ => replay_add_halve(circ, sign, source, target, fold_window, round),
    }
}

fn replay_doubling_round(
    circ: &mut Builder,
    round: usize,
    sign: QubitId,
    x: &[QubitId],
    y: &[QubitId],
    fold_window: usize,
) {
    let (source, target) = replay_operands(x, y, round);
    match round {
        0 => mod_double_pm(circ, target),
        1 => {
            mod_double_pm(circ, target);
            seed_round_one_inverse(circ, sign, source, target);
        }
        _ => {
            circ.x(sign);
            replay_double_add(circ, sign, source, target, fold_window, round);
            circ.x(sign);
        }
    }
}

/// `target <- (target + (-1)^sign * source) / 2 (mod p)`, with the halving's
/// pseudo-Mersenne correction fused into the add's own correction ripple.
fn replay_add_halve(
    circ: &mut Builder,
    sign: QubitId,
    source: &[QubitId],
    target: &[QubitId],
    fold_window: usize,
    round: usize,
) {
    let f = f();
    circ.cx_all(sign, target);
    let overflow = chunked_add(circ, source, target, round);

    let parity = circ.alloc_qubit();
    circ.cx(target[0], parity);

    circ.x(sign);
    let not_sign_and_parity = and_clean(circ, sign, parity);
    circ.x(sign);
    let sign_and_parity = circ.alloc_qubit();
    circ.cx(parity, sign_and_parity);
    circ.cx(not_sign_and_parity, sign_and_parity);
    circ.x(overflow);
    let minus_f = and_clean(circ, overflow, not_sign_and_parity);
    circ.x(overflow);
    let plus_2f = and_clean(circ, overflow, sign_and_parity);
    // The fold only needs plus_2f, while its selector remains a Clifford function
    // of two live wires. Release it across the carry ladder and recompute it when
    // plus_2f is measurement-uncomputed.
    circ.cx(not_sign_and_parity, sign_and_parity);
    circ.cx(parity, sign_and_parity);
    circ.free(sign_and_parity);
    // plus_f = parity ^ sign ^ minus_f. The fold does not otherwise use parity,
    // so hold plus_f in that wire and restore parity afterwards.
    circ.cx(sign, parity);
    circ.cx(minus_f, parity);
    fold_selected(
        circ,
        &target[..fold_window],
        f,
        parity,
        Some(plus_2f),
        minus_f,
        not_sign_and_parity,
    );

    circ.cx(minus_f, parity);
    circ.cx(sign, parity);
    let sign_and_parity = circ.alloc_qubit();
    circ.cx(parity, sign_and_parity);
    circ.cx(not_sign_and_parity, sign_and_parity);
    and_uncompute(circ, plus_2f, overflow, sign_and_parity);
    circ.x(overflow);
    and_uncompute(circ, minus_f, overflow, not_sign_and_parity);
    circ.x(overflow);
    circ.cx(parity, sign_and_parity);
    circ.cx(not_sign_and_parity, sign_and_parity);
    circ.free(sign_and_parity);
    circ.x(sign);
    and_uncompute(circ, not_sign_and_parity, sign, parity);
    circ.x(sign);

    circ.cx(overflow, parity);
    circ.cx(sign, parity);
    let k = flag_compare(round);
    circ.record_replay_site('F', round, N, k);
    erase_with_compare(circ, overflow, &target[N - k..], &source[N - k..], None);
    circ.free(overflow);

    circ.cx_all(sign, target);
    finish_halving(circ, target, parity);
}

/// The inverse cell: `target <- 2*target + (-1)^sign * source (mod p)`, again
/// with one pseudo-Mersenne correction ripple instead of two.
fn replay_double_add(
    circ: &mut Builder,
    sign: QubitId,
    source: &[QubitId],
    target: &[QubitId],
    fold_window: usize,
    round: usize,
) {
    let f = f();

    let doubled_out = start_doubling(circ, target);

    circ.cx_all(sign, target);
    let add_out = chunked_add(circ, source, target, round);

    // In the complemented subtraction frame the correction multiple is d+o when
    // sign=0 and o-d when sign=1, hence {-1,0,+1,+2}.
    let sign_xor_add = circ.alloc_qubit();
    circ.cx(sign, sign_xor_add);
    circ.cx(add_out, sign_xor_add);
    let routed = and_clean(circ, doubled_out, sign_xor_add);
    circ.cx(add_out, sign_xor_add);
    circ.cx(sign, sign_xor_add);
    circ.free(sign_xor_add);
    let minus_f = and_clean(circ, routed, sign);
    let plus_2f = circ.alloc_qubit();
    circ.cx(routed, plus_2f);
    circ.cx(minus_f, plus_2f);

    // +/-f is odd and +2f is even, so d^o selects the only bit-0 carry.
    let odd_correction = circ.alloc_qubit();
    circ.cx(doubled_out, odd_correction);
    circ.cx(add_out, odd_correction);
    let first_carry = and_clean(circ, target[0], odd_correction);
    // The fold retains first_carry and does not read odd_correction. Clear and
    // release this Clifford-derived flag across the binding carry ladder, then
    // reconstruct it for the measurement uncompute below.
    circ.cx(add_out, odd_correction);
    circ.cx(doubled_out, odd_correction);
    circ.release_clean(odd_correction);
    // plus_f = add_out ^ doubled_out ^ minus_f. The carry above captures every
    // use of add_out during the fold, so use that wire for plus_f.
    circ.cx(doubled_out, add_out);
    circ.cx(minus_f, add_out);
    fold_selected(
        circ,
        &target[..fold_window],
        f,
        add_out,
        Some(plus_2f),
        minus_f,
        first_carry,
    );

    circ.cx(minus_f, add_out);
    circ.cx(doubled_out, add_out);
    let odd_correction = circ.alloc_qubit();
    circ.cx(doubled_out, odd_correction);
    circ.cx(add_out, odd_correction);
    circ.cx(odd_correction, target[0]);
    and_uncompute(circ, first_carry, target[0], odd_correction);
    circ.cx(odd_correction, target[0]);
    circ.cx(doubled_out, odd_correction);
    circ.cx(add_out, odd_correction);
    circ.free(odd_correction);

    circ.cx(minus_f, plus_2f);
    circ.cx(routed, plus_2f);
    circ.free(plus_2f);
    and_uncompute(circ, minus_f, routed, sign);
    let sign_xor_add = circ.alloc_qubit();
    circ.cx(sign, sign_xor_add);
    circ.cx(add_out, sign_xor_add);
    and_uncompute(circ, routed, doubled_out, sign_xor_add);
    circ.cx(add_out, sign_xor_add);
    circ.cx(sign, sign_xor_add);
    circ.free(sign_xor_add);

    // After the fold, still in the complemented frame,
    // target[0] = sign ^ source[0] ^ d ^ o. Clear d without a second ripple.
    circ.cx(target[0], doubled_out);
    circ.cx(sign, doubled_out);
    circ.cx(source[0], doubled_out);
    circ.cx(add_out, doubled_out);
    circ.free(doubled_out);

    let k = flag_compare(round);
    circ.record_replay_site('F', round, N, k);
    erase_with_compare(circ, add_out, &target[N - k..], &source[N - k..], None);
    circ.free(add_out);
    circ.cx_all(sign, target);
}

// ─── The replay's chunked adder ────────────────────────────────────────────

/// Exact live footprint of chunk `j` inside [`chunked_add`]: the incoming
/// boundary carry (j>0), the outgoing one, and the chunk's own `w-1` owned
/// Gidney carries. Every chunk has an outgoing carry -- the last one's is the
/// adder's carry-out, which its only caller always wants.
///
/// The boundary erasure that follows each ripple is NOT counted, and does not
/// have to be: it holds two carries plus the comparator's own
/// `REPLAY_CHUNK_COMPARE - 1`, which is under this at every window the knob has
/// ever been swept to (21 against a ladder that never falls below 54).
fn chunk_live(j: usize, w: usize) -> usize {
    usize::from(j > 0) + 1 + w.saturating_sub(1)
}

/// Widest chunk that still fits `target` at position `j` -- [`chunk_live`]
/// solved for `w`.
fn widest_chunk(j: usize, target: usize) -> usize {
    (target + 1).saturating_sub(chunk_live(j, 1))
}

fn layout_ladder(sizes: &[usize]) -> usize {
    sizes
        .iter()
        .enumerate()
        .map(|(j, &w)| chunk_live(j, w))
        .max()
        .unwrap_or(0)
}

fn to_bounds(sizes: &[usize]) -> Vec<(usize, usize)> {
    let mut out = Vec::with_capacity(sizes.len());
    let mut lo = 0;
    for &w in sizes {
        out.push((lo, lo + w));
        lo += w;
    }
    out
}

/// Split `width` into `chunks` pieces as evenly as possible, widest first.
fn equal_split(width: usize, chunks: usize) -> Vec<usize> {
    let (base, extra) = (width / chunks, width % chunks);
    (0..chunks).map(|i| base + usize::from(i < extra)).collect()
}

/// Chunk layout whose live ladder fits `target`, using as few *approximate*
/// boundary repairs as possible.
///
/// A boundary is repaired by comparing the top `min(REPLAY_CHUNK_COMPARE, w)`
/// bits of the chunk that produced it, so the repair is only approximate when
/// the producing chunk is wider than the comparison window.  Chunk 0 has no
/// carry-in, so if it is no wider than the window its repair is `sum < addend`
/// over the *whole* chunk, i.e. EXACT and lambda-free.  Adding such a leading
/// chunk therefore buys `window` extra bits of capacity for (almost) no gates,
/// which lets a given number of wide boundaries reach a ~22-bit-narrower ladder
/// than an equal split can.
fn chunk_layout(n: usize, target: usize) -> Option<Vec<(usize, usize)>> {
    let window = replay_chunk_compare();
    // `wide` = number of boundaries whose repair is approximate, i.e. the gate
    // cost. Prefer the cheapest, and within that the narrowest leading chunk.
    for wide in 0..=12usize {
        // (a) equal split into `wide + 1` chunks: every boundary is wide.
        let k = wide + 1;
        if k <= n {
            let sizes = equal_split(n, k);
            if layout_ladder(&sizes) <= target {
                return Some(to_bounds(&sizes));
            }
        }
        // (b) exact-repair leading chunk plus `wide + 1` further chunks. Start
        // every chunk at the widest the target admits and give the excess back
        // below, so the search is over chunk *counts* only.
        let k = wide + 2;
        if k > n {
            continue;
        }
        let mut sizes: Vec<usize> = (0..k).map(|j| widest_chunk(j, target)).collect();
        sizes[0] = sizes[0].min(window);
        if sizes.contains(&0) || sizes.iter().sum::<usize>() < n {
            continue;
        }
        let mut excess = sizes.iter().sum::<usize>() - n;
        // Shrink the leading chunk first (its repair is the one we pay for), then
        // the wide chunks from the top down.
        for j in std::iter::once(0).chain((1..k).rev()) {
            if excess == 0 {
                break;
            }
            let cut = excess.min(sizes[j] - 1);
            sizes[j] -= cut;
            excess -= cut;
        }
        if excess == 0 && layout_ladder(&sizes) <= target {
            return Some(to_bounds(&sizes));
        }
    }
    None
}

/// `acc += addend`, split into chunks narrow enough to keep the live count under
/// [`walk_max_qubits`]. Allocates the carry-out wire itself on the last chunk
/// and returns it.
///
/// The ladder target is what the peak has left over right here, asked of the
/// builder exactly as [`walk_low_chunk`] asks it. Nothing about *what* is live —
/// the tape, the coefficient pair, the walk registers, this cell's own retained
/// wires — appears in it, so none of them can drift out of a model.
fn chunked_add(circ: &mut Builder, addend: &[QubitId], acc: &[QubitId], round: usize) -> QubitId {
    let ladder = walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
    let bounds = chunk_layout(addend.len(), ladder).expect("a chunk layout fits the ladder target");

    let mut carry_in: Option<QubitId> = None;
    let mut previous: Option<(QubitId, usize, usize)> = None;

    for &(lo, hi) in &bounds {
        let next = circ.alloc_qubit();
        ripple_add(circ, &addend[lo..hi], &acc[lo..hi], carry_in, Some(next));
        // Erase the previous chunk's carry as soon as it has been consumed.
        if let Some((carry, plo, phi)) = previous {
            let compare = chunk_compare(round).min(phi - plo);
            circ.record_replay_site('B', round, phi, compare);
            let window = phi - compare..phi;
            erase_with_compare(circ, carry, &acc[window.clone()], &addend[window], None);
            circ.free(carry);
        }
        carry_in = Some(next);
        previous = Some((next, lo, hi));
    }

    carry_in.expect("bounds is non-empty")
}

// ─── The replay's fused correction fold ────────────────────────────────────

/// Build-time context for one [`fold_selected`] carry position, packed for the
/// CCX site trace (see `Builder::ccx_note`). Lets the evaluator's dead-gate list be
/// correlated against the *classical* operand shape at that position.
///
///   bits  0..11 : i (bit position in acc)
///   bits 12..23 : acc width
///   bits 24..35 : msb(f) + 1  (0 when f == 0)
///   bit  36     : f.bit(i)          -- +f contributes here
///   bit  37     : f.bit(i-1)        -- +2f contributes here
///   bit  38     : negative_f[i]     -- -f contributes here
///   bits 40..43 : number of selectors
fn ccx_note_fold(i: usize, width: usize, f: U256, negative_f: &[bool], selectors: usize) -> u64 {
    let msb = (0..256)
        .rev()
        .find(|&b| f.bit(b))
        .map_or(0, |b| b as u64 + 1);
    (i as u64 & 0xfff)
        | (width as u64 & 0xfff) << 12
        | (msb & 0xfff) << 24
        | u64::from(f.bit(i)) << 36
        | u64::from(i > 0 && f.bit(i - 1)) << 37
        | u64::from(negative_f[i]) << 38
        | (selectors as u64 & 0xf) << 40
}

fn twos_complement_bits(value: U256, width: usize) -> Vec<bool> {
    let mut output = vec![false; width];
    let mut carry = true;
    for (i, bit_out) in output.iter_mut().enumerate() {
        let inverted = !value.bit(i);
        *bit_out = inverted ^ carry;
        carry &= inverted;
    }
    output
}

/// Add the one-hot selected member of `{-f, 0, +f, +2f}` without materialising a
/// 56-bit operand.
///
/// Position `i`'s addend bit is the XOR of the selectors that reach it: `+f`
/// contributes where `f` has a bit, `+2f` one position up, and `-f` where the
/// two's complement of `f` has one.  A single roving wire — the first selector,
/// or the incoming carry when there is none — carries that XOR for the length of
/// one ripple stage, so no operand register is ever built.
fn fold_selected(
    circ: &mut Builder,
    acc: &[QubitId],
    f: U256,
    plus_f: QubitId,
    plus_2f: Option<QubitId>,
    minus_f: QubitId,
    first_carry: QubitId,
) {
    let width = acc.len();
    let negative_f = twos_complement_bits(f, width);
    let selectors = |i: usize| {
        let mut out = Vec::with_capacity(3);
        if f.bit(i) {
            out.push(plus_f);
        }
        if i > 0 && f.bit(i - 1) {
            out.extend(plus_2f);
        }
        if negative_f[i] {
            out.push(minus_f);
        }
        out
    };

    // Three positions is the narrowest fold that has a ladder at all, and every
    // caller is at a fold window in the fifties.
    assert!(width >= 3, "fold window narrower than three bits");
    for control in selectors(0) {
        circ.cx(control, acc[0]);
    }

    // The final carry is needed only as an XOR into the top output bit. Emit it
    // directly there -- the same fusion `modular::terminal_step` does for a
    // wrapped ripple -- and retain carry wires only through position width - 3.
    let carries = circ.alloc_qubits(width - 3);
    let previous = |offset: usize| {
        if offset == 0 {
            first_carry
        } else {
            carries[offset - 1]
        }
    };

    for (offset, &carry) in carries.iter().enumerate() {
        let i = offset + 1;
        let sel = selectors(i);
        circ.ccx_note(ccx_note_fold(i, width, f, &negative_f, sel.len()));
        fold_step(circ, acc[i], previous(offset), carry, &sel, false);
    }

    let i = width - 2;
    let sel = selectors(i);
    circ.ccx_note(ccx_note_fold(i, width, f, &negative_f, sel.len()));
    fold_step(
        circ,
        acc[i],
        previous(carries.len()),
        acc[width - 1],
        &sel,
        true,
    );
    for control in selectors(width - 1) {
        circ.cx(control, acc[width - 1]);
    }

    for offset in (0..carries.len()).rev() {
        let i = offset + 1;
        unwind_fold_step(
            circ,
            acc[i],
            previous(offset),
            carries[offset],
            &selectors(i),
        );
    }
    circ.free_vec(&carries);
}

/// One [`fold_selected`] ripple stage: `carry = MAJ(acc, addend, previous)` with
/// the incoming carry applied to `acc` and left there — the sum bits are finished
/// in [`unwind_fold_step`].
///
/// `sel` is the (possibly empty) selector set whose XOR is this position's addend
/// bit; with no selectors the addend bit is zero and `previous` itself stands in
/// as the gate operand, since `MAJ(a, 0, c) = a & c`.  `apply_addend` finishes
/// this position's sum bit here instead, for the terminal stage that has no
/// unwind pass.
fn fold_step(
    circ: &mut Builder,
    acc: QubitId,
    previous: QubitId,
    carry: QubitId,
    sel: &[QubitId],
    apply_addend: bool,
) {
    with_selector_xor(circ, sel, previous, |circ, operand| {
        if operand != previous {
            circ.cx(previous, operand);
        }
        circ.cx(previous, acc);
        circ.ccx(operand, acc, carry);
        circ.cx(previous, carry);
        if operand != previous {
            circ.cx(previous, operand);
            if apply_addend {
                circ.cx(operand, acc);
            }
        }
    });
}

fn unwind_fold_step(
    circ: &mut Builder,
    acc: QubitId,
    previous: QubitId,
    carry: QubitId,
    sel: &[QubitId],
) {
    with_selector_xor(circ, sel, previous, |circ, operand| {
        circ.cx(previous, carry);
        if operand != previous {
            circ.cx(previous, operand);
        }
        let measured = circ.alloc_bit();
        circ.hmr(carry, measured);
        circ.cz_if(operand, acc, measured);
        circ.free_bit(measured);
        if operand != previous {
            circ.cx(previous, operand);
            circ.cx(operand, acc);
        }
    });
}

/// Gather `sel`'s XOR onto its first wire for the length of `body`, restoring the
/// others afterwards. With `sel` empty the addend bit is zero and `fallback`
/// serves as the operand.
fn with_selector_xor(
    circ: &mut Builder,
    sel: &[QubitId],
    fallback: QubitId,
    body: impl FnOnce(&mut Builder, QubitId),
) {
    let operand = sel.first().copied().unwrap_or(fallback);
    for &control in sel.iter().skip(1) {
        circ.cx(control, operand);
    }
    body(circ, operand);
    for &control in sel.iter().skip(1).rev() {
        circ.cx(control, operand);
    }
}

// ─── Modular primitives for rounds 0 and 1 of the replay ───────────────────

/// Close a replay halving: rotate the residue down and consume `parity`, which
/// holds the bit-0 value the modular correction was conditioned on. It lands in
/// the vacated top wire and is swapped back out clean.
fn finish_halving(circ: &mut Builder, target: &[QubitId], parity: QubitId) {
    rotate_down(circ, target);
    circ.cx(parity, target[N - 1]);
    circ.cx(target[N - 1], parity);
    circ.free(parity);
}

/// Open a replay doubling: take the bit shifted off the top onto a wire of its
/// own and rotate the residue up, leaving `target[0]` clear.
fn start_doubling(circ: &mut Builder, target: &[QubitId]) -> QubitId {
    let out = circ.alloc_qubit();
    circ.swap(target[N - 1], out);
    rotate_up(circ, target);
    out
}

fn mod_halve_pm(circ: &mut Builder, target: &[QubitId]) {
    let parity = circ.alloc_qubit();
    circ.cx(target[0], parity);
    // parity is an exact copy of target[0], so applying the bit-0 subtraction
    // early makes target[0] a clean host for the final measured borrow.
    csub_const_trunc_ctrl_low0(circ, &target[..f_slice()], f(), parity);
    finish_halving(circ, target, parity);
}

fn mod_double_pm(circ: &mut Builder, target: &[QubitId]) {
    let overflow = start_doubling(circ, target);
    // The rotation leaves target[0] clear, so the odd `f`'s first carry is
    // provably zero and the fold's ladder starts one position up.
    add_f_window(circ, overflow, target, f_slice(), true);
    circ.cx(target[0], overflow);
    circ.free(overflow);
}

fn seed_round_one(circ: &mut Builder, sign: QubitId, source: &[QubitId], target: &[QubitId]) {
    for i in 0..N {
        circ.cx(source[i], target[i]);
        circ.cx(sign, target[i]);
    }
    csub_const_trunc(circ, &target[..f_slice()], f_minus_one(), sign);
}

fn seed_round_one_inverse(
    circ: &mut Builder,
    sign: QubitId,
    source: &[QubitId],
    target: &[QubitId],
) {
    cadd_const_trunc(circ, &target[..f_slice()], f_minus_one(), sign, false);
    for i in (0..N).rev() {
        circ.cx(sign, target[i]);
        circ.cx(source[i], target[i]);
    }
}

/// `f - 1`, the constant the round-one seed and the conditional negation both
/// correct by.
fn f_minus_one() -> U256 {
    f().wrapping_sub(U256::from(1))
}

/// `(f - 1) / 2`, exact because `f` is odd, and the magnitude BOTH lifts correct
/// by: round 0's `h` arm, and round 1's `(p+1)/2 = 2^255 - (f-1)/2`.
///
/// Derived rather than written out, for the reason [`super::modular::f`] is --
/// this was two separate spellings of one number, a literal here and an inline
/// `(f-1) >> 1` there, and neither lift had any way to notice if the modulus
/// moved under it.
fn half_f_minus_one() -> U256 {
    f_minus_one() >> 1
}

fn conditional_mod_negate(circ: &mut Builder, control: QubitId, value: &[QubitId]) {
    circ.cx_all(control, value);
    // ~x - (f-1) = p-x for p = 2^256-f. The sparse low correction avoids a
    // register-wide constant-add workspace. As elsewhere in this benchmark, the
    // carry window is the deliberately measured approximation.
    csub_const_trunc(circ, &value[..f_slice()], f_minus_one(), control);
}

// ─── Small shared helpers ──────────────────────────────────────────────────

/// Rotate `reg` down one place -- bit `j + 1` moves to `j` and bit 0 comes round
/// to the top -- which is the wire half of a halving. Whatever the top wire
/// carries in is the caller's business: the walk X's it, and the replay lands the
/// modular parity correction there.
fn rotate_down(circ: &mut Builder, reg: &[QubitId]) {
    for i in 0..reg.len() - 1 {
        circ.swap(reg[i], reg[i + 1]);
    }
}

/// [`rotate_down`] backwards, the wire half of a doubling. The swaps commute, but
/// emitting them in the mirrored order keeps the unwind an exact op-level inverse.
fn rotate_up(circ: &mut Builder, reg: &[QubitId]) {
    for i in (0..reg.len() - 1).rev() {
        circ.swap(reg[i], reg[i + 1]);
    }
}

fn load_const(circ: &mut Builder, n: usize, c: U256) -> Vec<QubitId> {
    let qs = circ.alloc_qubits(n);
    for (i, &q) in qs.iter().enumerate() {
        if c.bit(i) {
            circ.x(q);
        }
    }
    qs
}
