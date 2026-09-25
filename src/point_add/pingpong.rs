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
//! registers (`coefficient`, `numerator`) as modular halvings â€” which is what
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
//! ask the builder for it rather than modelling it â€” so peak width is a cap the
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
use super::modular::{
    add_f_window, f, f_slice, ripple_add, ripple_add_lent,
    ripple_add_lent_with_deferred_phase, ripple_add_with_deferred_phase,
};
use super::{env_flag, env_raw, fold_guard, pinned_env, required_env, Builder, N, SECP256K1_P};
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
pinned_env!(flag_widen_div, "PP_FLAG_WIDEN_DIV");

// The circuit's peak, and the only width knob there is. Both carry-ladder
// sites -- `walk_low_chunk` for the walk's split adds, `chunked_add` for the
// replay's -- size themselves against the live count the builder reports, so
// each lands on exactly this many qubits and neither can drift.
//
// There is deliberately no second budget for the replay side. Sizing it against
// a modelled live set instead gives the same layout at every call: such a model
// is high by exactly `MODEL_OVERCOUNT`, so its budget is only ever this knob plus
// four, and its achieved peak this knob exactly.
pinned_env!(pub(super) walk_max_qubits, "PP_WALK_MAX_QUBITS");

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

// Split the replay fold's carry ladder at bit 32 (`PP_SPLIT_FOLD=1`): k*f is
// k*977 + k*2^32, so one ripple adds k*977 into bits 0..32 (mod 2^32) and a
// second adds k into bits 32..W. The low block's wrap/borrow into bit 32 is
// deliberately DROPPED -- a new, bounded approximation (~977*E|k|/2^32 per
// cell), not a bug to repair. Default off; with the gate off the emitted
// stream is byte-identical to the single-ladder form.
fn split_fold() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| super::env_flag("PP_SPLIT_FOLD"))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PingPongDirection {
    Divide,
    Multiply,
}

// â”€â”€â”€ The interleaving plan â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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
            r1: env_raw(match direction {
                PingPongDirection::Divide => "PP_HEAD_DIV",
                PingPongDirection::Multiply => "PP_HEAD_MUL",
            }).or_else(|| env_raw("PP_Q1208_R1"))
              .and_then(|s| s.parse::<usize>().ok())
              .unwrap_or_else(|| head_boundary(rounds, cell_extra)),
            r2: env_raw(match direction {
                PingPongDirection::Divide => "PP_TAIL_DIV",
                PingPongDirection::Multiply => "PP_TAIL_MUL",
            }).and_then(|s| s.parse::<usize>().ok())
              .unwrap_or_else(plan_r2).min(rounds.saturating_sub(1)),
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
    /// measured, not derived â€” see [`fold_shape`]. It also happens to hold the
    /// peak: the cell's fold is the widest thing alive in the trailing batch,
    /// where the tape is at its longest and [`loan_terminal`] has collapsed both
    /// walk registers to a sign wire, and the profile has already narrowed those
    /// rounds by one to four bits. Every other round has slack â€” ~74 qubits in
    /// the head batch, a couple in the worst interleaved one â€” which is what
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
/// That batch replays every round below `r1` at ONE frozen footprint â€” `r1` tape
/// wires, both coefficient registers, and the two walk registers at
/// `value_width(r1)` â€” so its chunk count is a function of `r1` alone, and
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
/// one round past it the whole batch jumps to three chunks â€” a step worth
/// hundreds of Toffoli.
///
/// This is why `r1` is computed and not pinned: it is a function of the width
/// schedule and the peak, and it must move whenever either does. Swept and
/// confirmed optimal at peak 1264 (335 divide / 326 multiply) and at 1273
/// (368 / 365); at the pinned 1260 it comes out 313 and 312.
///
/// This is also the one footprint in the file that is predicted rather than
/// measured â€” `r1` is chosen before the head batch exists â€” hence
/// [`MODEL_OVERCOUNT`].
fn head_boundary(rounds: usize, cell_extra: usize) -> usize {
    let room = (walk_max_qubits() + MODEL_OVERCOUNT)
        .saturating_sub(2 * N + two_chunk_ladder() + cell_extra);
    (0..rounds)
        .filter(|&r| r + 2 * value_width(r) <= room)
        .max()
        .unwrap_or(0)
}

// â”€â”€â”€ Entry point â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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
    let mut depths: Vec<Vec<QubitId>> = Vec::with_capacity(plan.rounds);
    let mut walk_phases: Vec<Option<DeferredWalkPhase>> = Vec::with_capacity(plan.rounds);
    let mut a0_fix = None;
    for r in plan.head() {
        let (sign, depth, phase) = walk_round_phase(circ, u, v, r, defer_walk_phase());
        tape.push(sign);
        depths.push(depth);
        walk_phases.push(phase);
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
    let replay = |circ: &mut Builder, r: usize, sign: QubitId, depth: &[QubitId]| {
        replay_halving_round(
            circ,
            r,
            sign,
            depth,
            &coefficient,
            numerator,
            plan.fold_window(r),
        );
    };

    let mut sign1_fix = None;
    let mut c2fix: Vec<Option<BitId>> = vec![None; plan.rounds];
    for r in plan.head() {
        with_forward_replay_sign_loans(circ,u,v,plan.r1.saturating_sub(1),|circ|replay(circ,r,tape[r],&depths[r]));
        // Round 1's sign is dead the moment its own replay is done; the rest of
        // the batch runs one wire lighter.
        if r == 1 {
            sign1_fix = Some(free_sign_bit(circ, tape[1]));
        }
        if c2_sheds(r, plan.rounds, plan.r1, &depths[r]) {
            c2fix[r] = Some(free_sign_bit(circ, tape[r]));
        }
    }

    let batch_span = env_raw("PP_MID_BATCH_DIV").and_then(|v|v.parse::<usize>().ok()).unwrap_or(0);
    if batch_span>0 {
        // This receiver assumes the H7 one-bit tape and no mid-walk sign
        // shedding. Moving a replay then leaves every walk's live set intact.
        assert!(!mod4_sign() && c2_tailsign()==0 && c2_lead()==0);
    }
    let mut next = plan.r1;
    while next<=plan.r2 {
        let end=(next..=next.saturating_add(batch_span).min(plan.r2))
            .min_by_key(|&r|(r+1+2*value_width((r+1).min(plan.rounds-1)),r)).unwrap();
        for r in next..=end {
            let (sign, depth, phase) = walk_round_phase(circ, u, v, r, defer_walk_phase());
            tape.push(sign);
            depths.push(depth);
            walk_phases.push(phase);
            if r + 1 < plan.rounds {
                shrink_to(circ, u, v, value_width(r + 1));
            }
        }
        for r in next..=end {
            with_forward_replay_sign_loans(circ,u,v,end,|circ|replay(circ,r,tape[r],&depths[r]));
            if c2_sheds(r, plan.rounds, plan.r1, &depths[r]) {
                c2fix[r] = Some(free_sign_bit(circ, tape[r]));
            }
        }
        if env_flag("PP_MID_BATCH_TRACE"){eprintln!("MID_BATCH_DIV {} {}",next,end);}
        next=end+1;
    }

    for r in plan.tail() {
        let (sign, depth, phase) = walk_round_phase(circ, u, v, r, defer_walk_phase());
        tape.push(sign);
        depths.push(depth);
        walk_phases.push(phase);
    }
    let loans = loan_terminal(circ, u, v);
    for r in plan.tail() {
        replay(circ, r, tape[r], &depths[r]);
        // C2-record: this round's tape wire is dead the moment its own replay is
        // done -- the walk-back recomputes it.
        if c2_sheds(r, plan.rounds, plan.r1, &depths[r]) {
            c2fix[r] = Some(free_sign_bit(circ, tape[r]));
        }
    }
    endpoint(circ, plan, u, v, &coefficient, numerator);
    restore_terminal(circ, &loans);
    circ.free_vec(&coefficient);

    circ.set_phase("pp_div_walkback");
    for r in (0..tape.len()).rev() {
        let fix = match r {
            0 => a0_fix,
            1 => sign1_fix,
            _ => c2fix[r],
        };
        walk_back_round_phase(
            circ, u, v, r, tape[r], &depths[r], fix, walk_phases[r].take(),
        );
    }
    assert!(walk_phases.iter().all(Option::is_none), "unconsumed deferred walk phase");
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
    let mut tape: Vec<QubitId> = Vec::with_capacity(plan.rounds);
    let mut depths: Vec<Vec<QubitId>> = Vec::with_capacity(plan.rounds);
    for r in 0..plan.rounds {
        let (sign, depth) = walk_round(circ, u, v, r);
        tape.push(sign);
        depths.push(depth);
    }
    let a0_fix = Some(free_sign_bit(circ, tape[0]));
    // C4-W: `recompute_bchain_sign` telescopes `sign_k = t1 ^ s1` over the head
    // batch, which the quarter step's `sign_k = t1 ^ s1 ^ 1 ^ w_k` breaks (the
    // recomputed sign is then wrong on half the shots: it corrupts only the
    // coefficient, which is freed dirty -- phase garbage, no classical trace).
    // Under the quarter step the round-1 sign stays on the tape: one wire.
    let bchain_fix = (BCHAIN_J < plan.r1 && plan.r1 < plan.rounds && !mod4_sign())
        .then(|| free_sign_bit(circ, tape[BCHAIN_J]));

    // C2-record: the trailing tape window goes out before `coefficient`, which
    // is what takes this traversal to its peak.
    let c2fix = c2_shed_tape(circ, &tape, &depths, plan.rounds, plan.r1);

    circ.set_phase("pp_mul_replay");
    let coefficient = circ.alloc_qubits(N);
    // As in `divide`: the sign is a parameter so the loops below can keep
    // popping `tape`.
    let replay = |circ: &mut Builder, r: usize, sign: QubitId, depth: &[QubitId]| {
        replay_doubling_round(
            circ,
            r,
            sign,
            depth,
            &coefficient,
            numerator,
            plan.fold_window(r),
        );
    };
    let loans = loan_terminal(circ, u, v);
    endpoint(circ, plan, u, v, &coefficient, numerator);
    for r in plan.tail().rev() {
        if c2fix[r].is_some() {
            let s = c2_term_sign(circ, u, v);
            replay(circ, r, s, &depths[r]);
            c2_drop_term_sign(circ, u, v, s);
        } else {
            replay(circ, r, tape[r], &depths[r]);
        }
    }
    restore_terminal(circ, &loans);

    circ.set_phase("pp_mul_walkback");
    // Start only from copies proved before the terminal loan; do not infer
    // convergence from loan_terminal's stronger +/-1 promise. An inverse
    // invalidates its target; fresh grow_to re-establishes both high copies.
    let mut replay_sign_valid=forward_sign_copy_valid(u.len(),plan.rounds-1);
    for r in plan.tail().rev() {
        let sign = pop_tape(&mut tape, r);
        if u.len()<value_width(r){replay_sign_valid=[true,true];}
        walk_back_round(circ, u, v, r, sign, &depths[r], c2fix[r]);
        replay_sign_valid[if r.is_multiple_of(2){1}else{0}]=false;
    }
    let batch_span=env_raw("PP_MID_BATCH_MUL").and_then(|v|v.parse::<usize>().ok()).unwrap_or(0);
    if batch_span>0 {assert!(!mod4_sign() && c2_tailsign()==0 && c2_lead()==0);}
    let footprint=|r:usize|r+1+2*value_width((r+1).min(plan.rounds-1));
    let mut hi=plan.r2;
    while hi>=plan.r1 {
        let mut lo=hi.saturating_sub(batch_span).max(plan.r1);
        for r in (lo..hi).rev() {
            if footprint(r)<footprint(hi) {lo=r+1;break;}
        }
        for r in(lo..=hi).rev() {
            if c2fix[r].is_some() {
                let s=c2_term_sign(circ,u,v);
                with_reverse_replay_sign_loans(circ,u,v,replay_sign_valid,|circ|replay(circ,r,s,&depths[r]));
                c2_drop_term_sign(circ,u,v,s);
            } else {with_reverse_replay_sign_loans(circ,u,v,replay_sign_valid,|circ|replay(circ,r,tape[r],&depths[r]));}
        }
        for r in(lo..=hi).rev() {
            let sign=pop_tape(&mut tape,r);
            if u.len()<value_width(r){replay_sign_valid=[true,true];}
            walk_back_round(circ,u,v,r,sign,&depths[r],c2fix[r]);
            replay_sign_valid[if r.is_multiple_of(2){1}else{0}]=false;
        }
        if env_flag("PP_MID_BATCH_TRACE"){eprintln!("MID_BATCH_MUL {} {}",lo,hi);}
        if lo==plan.r1 {break;}
        hi=lo-1;
    }

    for r in plan.head().rev() {
        if r == BCHAIN_J {
            if let Some(fix) = bchain_fix {
                tape[BCHAIN_J] = recompute_bchain_sign(circ, u, v, &tape, plan.r1, fix);
            }
        }
        if c2fix[r].is_some() {
            let s = c2_term_sign(circ, u, v);
            with_reverse_replay_sign_loans(circ,u,v,replay_sign_valid,|circ|replay(circ,r,s,&depths[r]));
            c2_drop_term_sign(circ, u, v, s);
        } else {
            with_reverse_replay_sign_loans(circ,u,v,replay_sign_valid,|circ|replay(circ,r,tape[r],&depths[r]));
        }
    }
    circ.free_vec(&coefficient);

    for r in plan.head().rev() {
        let sign = pop_tape(&mut tape, r);
        walk_back_round(
            circ,
            u,
            v,
            r,
            sign,
            &depths[r],
            if r == 0 { a0_fix } else { None },
        );
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

// â”€â”€â”€ Loaning idle walk wires to the allocator â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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

/// Take bit 0 back â€” on **whatever wire the allocator offers**, not the one that
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

// â”€â”€â”€ Width schedule â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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
    let width=width_schedule()[round];
    let extra=super::optional_env::<usize>("PP_WALK_GUARD_BITS").unwrap_or(0);
    assert!(extra<=4,"bounded walk guard experiment");
    let threshold=super::optional_env::<usize>("PP_WALK_GUARD_MAX_WIDTH").unwrap_or(VALUE_WIDTH-1).min(VALUE_WIDTH-1);
    // Saturating at threshold+1 prevents an upward jump when a decreasing
    // schedule first enters the guarded band. Never exceed the initial rails.
    if width<=threshold{(width+extra).min(threshold+1)}else{width}
}

// A precision experiment must not silently change the replay's fold/compare
// profiles or seeded predictor policy when the physical integer rails widen.
fn policy_width(round:usize)->usize {
    width_schedule()[round]
}

/// The fold-window shape: how many bits of window a round wants, relative to the
/// pinned base, as a function of **the walk's width at that round**.
///
/// MEASURED, not derived. The replay cell's fold drops the carry off the top of
/// its slice, and the rate at which that carry actually escapes is not the same
/// at every round. Narrowing one block of rounds at a time against a flat
/// baseline and counting the shots that newly fail â€” 300,000 per point through
/// the classical replay model â€” gives, relative to the flat region:
///
/// ```text
///   walk width   253..73   54    47    41    35    28    21    15     8
///   rate/flat     0.88-1.06  0.98  0.91  0.70  0.46  0.14  0.074  0.054  0.049
/// ```
///
/// Flat across a 3.5x span of widths, then a monotone collapse once the walk
/// falls below ~45. **The walk's remaining magnitude is the driver, not the
/// round index** â€” which is why this is keyed on [`value_width`] and not on `r`.
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
    band_at(fold_shape(), policy_width(round)) + isize::from(round < fold_widen())
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
        .checked_add_signed(band_at(bands, policy_width(round)))
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
        .checked_add_signed(band_at(bands, policy_width(round)))
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

// --- The quarter step: the mod-4 sign rule and the depth record -----------

/// `PP_MOD4_SIGN` (default off): flip the walk's sign rule.
///
/// The head emits `sign = bit1(target) ^ bit1(source)`, which is exactly the
/// choice that forces the sum to `2 mod 4` and so keeps the halved sum odd. One
/// free `X` on the tape wire takes the complement, which forces the sum to
/// `0 mod 4` and guarantees `k = v2(sum) >= 2` -- M1's rail mod-4 acting as a
/// component. `X` is not charged, so forcing depth >= 2 costs zero Toffoli.
///
/// What it costs instead is the invariant: with the sum divisible by 4 the
/// halved sum is even, and only taking the halving to the full valuation
/// restores oddness. That is what [`depth_at`] budgets and [`barrel_down`]
/// performs. Scope: this bounds one bit of sign freedom UNDER the oddness
/// invariant and leaves standing any recurrence that tolerates an even rail.
fn mod4_sign() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_MOD4_SIGN"))
}

/// Bits of halving depth recorded per round, as a `width:bits` band table in
/// `PP_DEPTH_PROFILE`.
///
/// Keyed on [`value_width`] and NOT on `r`, for [`fold_shape`]'s own reason:
/// keying a per-round quantity on the round index goes stale the moment
/// `PP_WIDTH_SCHEDULE` is regenerated, silently and without changing a pin.
///
/// `d` bits budget `e = k - 1 <= cap = 2^d - 1`. A round whose true valuation
/// runs past the budget shifts by `cap` and leaves the residual standing in the
/// rail for the next round: a bounded approximation in the same class as the
/// replay fold's deliberately dropped carry, registered as its own replay
/// channel (kind `K`) so `DUMP_REPLAY_SITES=1` and the grind screen both see it.
///
/// Rounds 0 and 1 are the boot rounds and halve plainly, so they carry none.
fn depth_shape() -> &'static [(usize, isize)] {
    static SLOT: std::sync::OnceLock<Vec<(usize, isize)>> = std::sync::OnceLock::new();
    SLOT.get_or_init(|| band_table("PP_DEPTH_PROFILE"))
}

/// Depth bits at `round`, clamped so the budget fits inside the round's own
/// register: the cap has to be addressable as a bit index of the walk slice.
/// The clamp is visible -- the `K` site records the `d` actually used.
fn depth_at(round: usize) -> usize {
    if round < 2 || !mod4_sign() {
        return 0;
    }
    let bits = band_at(depth_shape(), value_width(round));
    assert!(
        (0..=6).contains(&bits),
        "PP_DEPTH_PROFILE: {bits} bits of depth is outside 0..=6"
    );
    let slice = value_width(round) - 1;
    let floor_d = if depth_one() { 1 } else { 2 };
    let mut d = bits as usize;
    while d >= floor_d && (1usize << d) - 1 >= slice {
        d -= 1;
    }
    if d < floor_d {
        0
    } else {
        d
    }
}

/// A controlled swap. One Toffoli with or without clean ancilla -- the floor
/// `HAZARDS.md` H9 records, and the reason every data-dependent shift below
/// prices at `stages x width` and admits no ancilla trade.
fn cswap(circ: &mut Builder, ctrl: QubitId, a: QubitId, b: QubitId) {
    circ.cx(a, b);
    circ.ccx(ctrl, b, a);
    circ.cx(a, b);
}

/// `reg <- reg >> s`, sign-extended, when `ctrl`.
///
/// The bits leaving the bottom are provably zero -- that is what `s <= e`
/// means -- so the cyclic wire rotation IS the arithmetic shift, and the `s`
/// wires it brings round to the top arrive holding those zeros. Each then takes
/// a copy of the shifted value's sign, which by then sits at `reg[m - s - 1]`.
///
/// `m - s` controlled swaps plus `s` sign fills: exactly `m` Toffoli per stage.
fn cshift_down(circ: &mut Builder, ctrl: QubitId, reg: &[QubitId], s: usize, signed: bool) {
    let m = reg.len();
    assert!(s < m, "a shift stage never shifts the register away");
    for j in 0..m - s {
        cswap(circ, ctrl, reg[j], reg[j + s]);
    }
    if signed {
        for j in 0..s {
            circ.ccx(ctrl, reg[m - s - 1], reg[m - 1 - j]);
        }
    }
}

/// [`cshift_down`] backwards, op for op.
fn cshift_up(circ: &mut Builder, ctrl: QubitId, reg: &[QubitId], s: usize, signed: bool) {
    let m = reg.len();
    assert!(s < m, "a shift stage never shifts the register away");
    if signed {
        for j in (0..s).rev() {
            circ.ccx(ctrl, reg[m - s - 1], reg[m - 1 - j]);
        }
    }
    for j in (0..m - s).rev() {
        cswap(circ, ctrl, reg[j], reg[j + s]);
    }
}

/// `reg <- reg >> depth`, sign-extended, for the little-endian shift amount
/// held in `depth`: one controlled shift stage per depth bit.
///
/// `depth.len() * reg.len()` Toffoli. That is M8's `stages x n` exactly, and it
/// is the dominant term of the whole construction.
fn barrel_down(circ: &mut Builder, reg: &[QubitId], depth: &[QubitId], signed: bool) {
    for (b, &ctrl) in depth.iter().enumerate() {
        cshift_down(circ, ctrl, reg, 1usize << b, signed);
    }
}

/// [`barrel_down`] backwards, op for op.
fn barrel_up(circ: &mut Builder, reg: &[QubitId], depth: &[QubitId], signed: bool) {
    for (b, &ctrl) in depth.iter().enumerate().rev() {
        cshift_up(circ, ctrl, reg, 1usize << b, signed);
    }
}

/// XOR `e = k - 1` -- the halving depth beyond the one the rotation has already
/// performed -- into `depth`, read off `reg`.
///
/// `reg` has just been rotated down once, so it holds `(S/2)`'s bits `1..`, and
/// `v2(S/2) = e` puts `reg`'s first one at index `e - 1`. A one-hot chain reads
/// that position: `z[j]` is "`reg[0..=j]` are all zero", `g[j] = z[j-1] AND
/// reg[j]` is "the first one is at `j`", and the last `z` saturates the budget.
/// Every wire in both chains is an AND of wires that stay live, so both
/// measurement-uncompute for free and the charge is `2 * (cap - 2)` Toffoli.
///
/// The binary value goes in by free CX off the one-hot wires, so calling this
/// twice with the same `reg` and `depth` is the identity -- which is how the
/// walk-back erases the record.
fn depth_xor(circ: &mut Builder, reg: &[QubitId], depth: &[QubitId]) {
    let d = depth.len();
    let cap = (1usize << d) - 1;
    assert!(d >= 2 && cap < reg.len(), "the depth budget fits the register");

    // z[j] = reg[0..=j] are all zero, for j in 0..cap-1.
    let mut z: Vec<QubitId> = Vec::with_capacity(cap - 1);
    for j in 0..cap - 1 {
        let out = circ.alloc_qubit();
        if j == 0 {
            circ.cx(reg[0], out);
            circ.x(out);
        } else {
            circ.x(reg[j]);
            circ.ccx(z[j - 1], reg[j], out);
            circ.x(reg[j]);
        }
        z.push(out);
    }

    let write = |circ: &mut Builder, src: QubitId, e: usize| {
        for (b, &q) in depth.iter().enumerate() {
            if (e >> b) & 1 == 1 {
                circ.cx(src, q);
            }
        }
    };
    // e = 1: the first one is at index 0.
    write(circ, reg[0], 1);
    // e = j + 1: the first one is at index j.
    let mut g: Vec<QubitId> = Vec::with_capacity(cap.saturating_sub(2));
    for j in 1..cap - 1 {
        let out = circ.alloc_qubit();
        circ.ccx(z[j - 1], reg[j], out);
        write(circ, out, j + 1);
        g.push(out);
    }
    // e = cap: no one below the budget, so the round saturates and the residual
    // stays in the rail -- the K channel's approximation.
    write(circ, z[cap - 2], cap);

    for (idx, &out) in g.iter().enumerate().rev() {
        and_uncompute(circ, out, z[idx], reg[idx + 1]);
    }
    for j in (0..cap - 1).rev() {
        if j == 0 {
            circ.x(z[0]);
            circ.cx(reg[0], z[0]);
            circ.release_clean(z[0]);
        } else {
            circ.x(reg[j]);
            and_uncompute(circ, z[j], z[j - 1], reg[j]);
            circ.x(reg[j]);
        }
    }
}

/// The round's entry in the depth record: `d` fresh wires holding
/// `min(k - 1, 2^d - 1)`, live from here to this round's replay and on to its
/// walk-back, exactly as the tape sign is.
fn depth_extract(circ: &mut Builder, reg: &[QubitId], round: usize, d: usize) -> Vec<QubitId> {
    circ.record_replay_site('K', round, reg.len(), d);
    let depth = circ.alloc_qubits(d);
    depth_xor(circ, reg, &depth);
    depth
}

/// [`depth_extract`] backwards: recompute the one-hot chain off the restored
/// register, XOR the record back to |0>, and hand the wires back.
fn depth_erase(circ: &mut Builder, reg: &[QubitId], depth: &[QubitId]) {
    depth_xor(circ, reg, depth);
    circ.free_vec(depth);
}

/// [`depth_xor`] keyed to the PRE-rotate register: XOR `e = min(v2(reg), cap)`
/// into `depth`. `z[j]` is "`reg[0..=j]` are all zero" for `j` in `0..cap`,
/// `g[j] = z[j-1] AND reg[j]` is "the first one is at `j`" and writes `j`, and
/// `z[cap-1]` writes `cap`. An odd register writes nothing. Every wire in both
/// chains is an AND of wires that stay live, so both unwind by measurement;
/// `2 * (cap - 1)` Toffoli. Self-inverse, which is how the walk-back erases it.
fn depth_xor_pre(circ: &mut Builder, reg: &[QubitId], depth: &[QubitId]) {
    let d = depth.len();
    let cap = (1usize << d) - 1;
    // W2: at cap = 1 the one-hot chain degenerates to z[0] = !reg[0] and the
    // single write, which this body already emits -- and at zero Toffoli.
    assert!(d >= 1 && cap < reg.len(), "the depth budget fits the register");

    let mut z: Vec<QubitId> = Vec::with_capacity(cap);
    for j in 0..cap {
        let out = circ.alloc_qubit();
        if j == 0 {
            circ.cx(reg[0], out);
            circ.x(out);
        } else {
            circ.x(reg[j]);
            circ.ccx(z[j - 1], reg[j], out);
            circ.x(reg[j]);
        }
        z.push(out);
    }

    let write = |circ: &mut Builder, src: QubitId, e: usize| {
        for (b, &q) in depth.iter().enumerate() {
            if (e >> b) & 1 == 1 {
                circ.cx(src, q);
            }
        }
    };
    let mut g: Vec<QubitId> = Vec::with_capacity(cap - 1);
    for j in 1..cap {
        let out = circ.alloc_qubit();
        circ.ccx(z[j - 1], reg[j], out);
        write(circ, out, j);
        g.push(out);
    }
    write(circ, z[cap - 1], cap);

    for (idx, &out) in g.iter().enumerate().rev() {
        and_uncompute(circ, out, z[idx], reg[idx + 1]);
    }
    for j in (0..cap).rev() {
        if j == 0 {
            circ.x(z[0]);
            circ.cx(reg[0], z[0]);
            circ.release_clean(z[0]);
        } else {
            circ.x(reg[j]);
            and_uncompute(circ, z[j], z[j - 1], reg[j]);
            circ.x(reg[j]);
        }
    }
}

fn depth_extract_pre(circ: &mut Builder, reg: &[QubitId], round: usize, d: usize) -> Vec<QubitId> {
    circ.record_replay_site('K', round, reg.len(), d);
    let depth = circ.alloc_qubits(d);
    depth_xor_pre(circ, reg, &depth);
    depth
}

fn depth_erase_pre(circ: &mut Builder, reg: &[QubitId], depth: &[QubitId]) {
    depth_xor_pre(circ, reg, depth);
    circ.free_vec(depth);
}

// --- C4-W: the overflow guard ----------------------------------------------

/// `PP_MOD4_GUARD` (default off): guard the quarter step against record
/// overflow. Off, the stream is byte-identical to the unguarded quarter step.
fn mod4_guard() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_MOD4_GUARD"))
}

/// `PP_DEPTH_ONE` (default off): admit a ONE-bit depth record, `cap = 1`.
///
/// W2-shedwindow.  `max k = cap + 1 = 2` is the frame the shed window is
/// priced in, and it is the only depth at which the shed width `2^d` equals
/// the explicit record width `d + 1`.  Off, `depth_at` floors at two bits and
/// the stream is byte-identical to the shipped C4-W.
fn depth_one() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_DEPTH_ONE"))
}

/// `w ^= AND_{j = 1..=cap} (target[j] ^ source[j] ^ sigma)`, i.e. "the mod-4
/// sum `target + (-1)^sigma source` is 0 mod 2^(cap+2)".
///
/// Both values are odd and the sum is already 0 mod 4, so the carry into every
/// bit from 2 up is a one (each lower bit summed to exactly two), and bit `j+1`
/// of the sum is `target[j] ^ source[j] ^ sigma ^ 1`. The `cap - 1` AND wires
/// are ANDs of live wires and unwind by measurement; the XOR wires are
/// Clifford. Self-inverse, so the walk-back erases `w` with the same call once
/// the operands are restored.
fn guard_xor(
    circ: &mut Builder,
    w: QubitId,
    sigma: QubitId,
    source: &[QubitId],
    target: &[QubitId],
    cap: usize,
) {
    assert!(cap >= 1 && cap < target.len(), "the guard reads inside the walk slice");
    if cap == 1 {
        // W2: one term, so the AND chain is empty and the guard IS the term.
        // Bit 2 of the mod-4 sum is `target[1] ^ source[1] ^ sigma ^ 1`, so the
        // sum is 0 mod 8 exactly when that XOR is one.  Self-inverse, Clifford.
        circ.cx(target[1], w);
        circ.cx(source[1], w);
        circ.cx(sigma, w);
        return;
    }
    let xs: Vec<QubitId> = (1..=cap)
        .map(|j| {
            let q = circ.alloc_qubit();
            circ.cx(target[j], q);
            circ.cx(source[j], q);
            circ.cx(sigma, q);
            q
        })
        .collect();
    let mut chain: Vec<QubitId> = Vec::with_capacity(cap.saturating_sub(2));
    let mut acc = xs[0];
    for &x in &xs[1..cap - 1] {
        let a = and_clean(circ, acc, x);
        chain.push(a);
        acc = a;
    }
    circ.ccx(acc, xs[cap - 1], w);
    for (i, &a) in chain.iter().enumerate().rev() {
        let prev = if i == 0 { xs[0] } else { chain[i - 1] };
        and_uncompute(circ, a, prev, xs[i + 1]);
    }
    for (j, &q) in xs.iter().enumerate().rev() {
        circ.cx(sigma, q);
        circ.cx(source[j + 1], q);
        circ.cx(target[j + 1], q);
        circ.release_clean(q);
    }
}

/// `w ^= [depth == 0]`. Self-inverse; the record is 0 exactly on a guarded
/// round, so this is how the forward round erases `w` and the walk-back
/// recomputes it.
fn guard_xor_record_zero(circ: &mut Builder, w: QubitId, depth: &[QubitId]) {
    let d = depth.len();
    assert!(d >= 1, "a depth record has at least one bit");
    if d == 1 {
        // W2: [record == 0] is just !depth[0].  Self-inverse, Clifford.
        circ.x(depth[0]);
        circ.cx(depth[0], w);
        circ.x(depth[0]);
        return;
    }
    circ.x_all(depth);
    let mut chain: Vec<QubitId> = Vec::with_capacity(d.saturating_sub(2));
    let mut acc = depth[0];
    for &q in &depth[1..d - 1] {
        let a = and_clean(circ, acc, q);
        chain.push(a);
        acc = a;
    }
    circ.ccx(acc, depth[d - 1], w);
    for (i, &a) in chain.iter().enumerate().rev() {
        let prev = if i == 0 { depth[0] } else { chain[i - 1] };
        and_uncompute(circ, a, prev, depth[i + 1]);
    }
    circ.x_all(depth);
}

/// [`depth_xor`] gated on `!w`: with the guard fired the one-hot chain is all
/// zero and nothing is written, so the record reads 0. `None` is the ungated
/// original, op for op.
fn depth_xor_gated(circ: &mut Builder, reg: &[QubitId], depth: &[QubitId], guard: Option<QubitId>) {
    let Some(w) = guard else {
        return depth_xor(circ, reg, depth);
    };
    let d = depth.len();
    let cap = (1usize << d) - 1;
    assert!(d >= 2 && cap < reg.len(), "the depth budget fits the register");

    // z[0] = !reg[0] AND !w; every later z and g inherits the gate.
    let mut z: Vec<QubitId> = Vec::with_capacity(cap - 1);
    for j in 0..cap - 1 {
        let out = circ.alloc_qubit();
        if j == 0 {
            circ.x(reg[0]);
            circ.x(w);
            circ.ccx(reg[0], w, out);
            circ.x(w);
            circ.x(reg[0]);
        } else {
            circ.x(reg[j]);
            circ.ccx(z[j - 1], reg[j], out);
            circ.x(reg[j]);
        }
        z.push(out);
    }

    let write = |circ: &mut Builder, src: QubitId, e: usize| {
        for (b, &q) in depth.iter().enumerate() {
            if (e >> b) & 1 == 1 {
                circ.cx(src, q);
            }
        }
    };
    // e = 1: the first one is at index 0 -- gated: reg[0] AND !w.
    circ.x(w);
    let one = and_clean(circ, reg[0], w);
    circ.x(w);
    write(circ, one, 1);
    let mut g: Vec<QubitId> = Vec::with_capacity(cap.saturating_sub(2));
    for j in 1..cap - 1 {
        let out = circ.alloc_qubit();
        circ.ccx(z[j - 1], reg[j], out);
        write(circ, out, j + 1);
        g.push(out);
    }
    // e = cap: no one below the budget. Under the guard this is exact, not a
    // saturation: v2 of the halved sum is at most cap - 1 whenever w is 0.
    write(circ, z[cap - 2], cap);

    for (idx, &out) in g.iter().enumerate().rev() {
        and_uncompute(circ, out, z[idx], reg[idx + 1]);
    }
    circ.x(w);
    and_uncompute(circ, one, reg[0], w);
    circ.x(w);
    for j in (0..cap - 1).rev() {
        if j == 0 {
            circ.x(reg[0]);
            circ.x(w);
            and_uncompute(circ, z[0], reg[0], w);
            circ.x(w);
            circ.x(reg[0]);
        } else {
            circ.x(reg[j]);
            and_uncompute(circ, z[j], z[j - 1], reg[j]);
            circ.x(reg[j]);
        }
    }
}

fn depth_extract_gated(
    circ: &mut Builder,
    reg: &[QubitId],
    round: usize,
    d: usize,
    guard: Option<QubitId>,
) -> Vec<QubitId> {
    circ.record_replay_site('K', round, reg.len(), d);
    let depth = circ.alloc_qubits(d);
    depth_xor_gated(circ, reg, &depth, guard);
    depth
}

fn depth_erase_gated(circ: &mut Builder, reg: &[QubitId], depth: &[QubitId], guard: Option<QubitId>) {
    depth_xor_gated(circ, reg, depth, guard);
    circ.free_vec(depth);
}

/// XOR the unary form of the depth record into `unary`: `unary[i]` is
/// `e >= i + 1`, for `i` in `0..cap`.
///
/// A shared-prefix one-hot decode of the binary record (`2^(d+1) - 4` Toffoli,
/// every node an AND of live wires and so free to unwind), then free CX. Self
/// inverse for the same reason [`depth_xor`] is.
fn depth_unary_xor(circ: &mut Builder, depth: &[QubitId], unary: &[QubitId]) {
    let d = depth.len();
    let cap = (1usize << d) - 1;
    assert_eq!(unary.len(), cap, "one unary wire per budgeted step");

    let mut levels: Vec<Vec<QubitId>> = Vec::with_capacity(d);
    for b in 0..d {
        let mut next: Vec<QubitId> = Vec::with_capacity(1usize << (b + 1));
        for value in 0..(1usize << (b + 1)) {
            let set = (value >> b) & 1 == 1;
            let out = circ.alloc_qubit();
            if b == 0 {
                circ.cx(depth[0], out);
                if !set {
                    circ.x(out);
                }
            } else {
                let prev = levels[b - 1][value & ((1usize << b) - 1)];
                if !set {
                    circ.x(depth[b]);
                }
                circ.ccx(prev, depth[b], out);
                if !set {
                    circ.x(depth[b]);
                }
            }
            next.push(out);
        }
        levels.push(next);
    }

    let onehot = levels.last().expect("a depth record has at least two bits");
    for (i, &u) in unary.iter().enumerate() {
        for e in (i + 1)..=cap {
            circ.cx(onehot[e], u);
        }
    }

    for b in (0..d).rev() {
        for value in (0..(1usize << (b + 1))).rev() {
            let set = (value >> b) & 1 == 1;
            let out = levels[b][value];
            if b == 0 {
                if !set {
                    circ.x(out);
                }
                circ.cx(depth[0], out);
                circ.release_clean(out);
            } else {
                let prev = levels[b - 1][value & ((1usize << b) - 1)];
                if !set {
                    circ.x(depth[b]);
                }
                and_uncompute(circ, out, prev, depth[b]);
                if !set {
                    circ.x(depth[b]);
                }
            }
        }
    }
}

fn depth_unary_make(circ: &mut Builder, depth: &[QubitId]) -> Vec<QubitId> {
    let unary = circ.alloc_qubits((1usize << depth.len()) - 1);
    depth_unary_xor(circ, depth, &unary);
    unary
}

fn depth_unary_drop(circ: &mut Builder, depth: &[QubitId], unary: &[QubitId]) {
    depth_unary_xor(circ, depth, unary);
    circ.free_vec(unary);
}

/// `target <- target * 2^-e (mod p)` for the depth record's `e`, on top of the
/// one halving [`replay_add_halve`] already fuses into its own add. `forward`
/// false runs the multiply leg's doubling instead.
///
/// The tree's halving is the `e = 1` case of Hensel's rule: add the multiple of
/// `p` that clears the low bit, then shift. Across `e` steps those multiples are
/// independent -- digit `i` is bit `i` of the running value -- so all `cap`
/// folds go in first, each at its own bit offset and each gated on "is the depth
/// at least `i + 1`", and ONE barrel then performs the whole shift. That buys
/// `d * N` Toffoli of permutation against `cap` folds of `f`, instead of `cap`
/// separately-shifted halvings at `N` Toffoli of permutation each.
///
/// A digit wire stops being an AND of live wires the moment its own fold clears
/// the bit it read, so it erases the way the cell's overflow flag does: a
/// measurement plus a truncated comparison of the two replay registers, at
/// [`flag_compare`]'s width and recorded as a `K` site.
fn replay_extra_shift(
    circ: &mut Builder,
    source: &[QubitId],
    target: &[QubitId],
    depth: &[QubitId],
    round: usize,
    forward: bool,
) {
    let cap = (1usize << depth.len()) - 1;
    let _ = source;
    let unary = depth_unary_make(circ, depth);

    // FIX3.  `T / 2^e (mod p)` is `(T + m*p) / 2^e` for the Hensel multiplier
    // `m = sum_i digit_i 2^i`.  In a 256-bit register `+ m*p` is `- m*f` plus an
    // `m * 2^256` that leaves the top, and after the shift that term comes back
    // as `m * 2^(256-e)`: the digits themselves, in the e wires the shift
    // vacates.  The head's own `finish_halving` lands exactly this as `parity`
    // on the top wire for its `e = 1` case.  So each digit goes BACK into the
    // wire its own fold cleared, the shift is a PLAIN rotation (a sign fill
    // would overwrite the correction with a copy of the top bit), and the digit
    // wire then erases against the wire it was copied into: free, exact, and one
    // fewer approximate replay channel than the sign-filled version had.
    if forward {
        for i in 0..cap {
            let digit = and_clean(circ, unary[i], target[i]);
            csub_const_trunc(circ, &target[i..i + f_slice()], f(), digit);
            circ.cx(digit, target[i]);
            and_uncompute(circ, digit, unary[i], target[i]);
        }
        barrel_down(circ, target, depth, false);
    } else {
        // FIX4.  The doubling leg is the halving leg's mirror, so the barrel and
        // the fold loop swap ORDER as well as direction.
        barrel_up(circ, target, depth, false);
        for i in (0..cap).rev() {
            let digit = and_clean(circ, unary[i], target[i]);
            circ.cx(digit, target[i]);
            cadd_const_trunc(circ, &target[i..i + f_slice()], f(), digit, false);
            and_uncompute(circ, digit, unary[i], target[i]);
        }
    }
    circ.record_replay_site('K', round, N, depth.len());
    depth_unary_drop(circ, depth, &unary);
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

// â”€â”€â”€ The walk â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

/// One forward walk round; returns the sign qubit to append to the tape.
fn walk_round(
    circ: &mut Builder,
    u: &mut Vec<QubitId>,
    v: &mut Vec<QubitId>,
    round: usize,
) -> (QubitId, Vec<QubitId>) {
    let (sign, depth, phase) = walk_round_phase(circ, u, v, round, false);
    assert!(phase.is_none());
    (sign, depth)
}

#[derive(Clone, Copy, Debug)]
struct DeferredWalkPhase {
    measured: BitId,
    low: usize,
}

fn defer_walk_phase() -> bool {
    env_flag("PP_CF_DEFER_WALK_PHASE")
}

fn walk_round_phase(
    circ: &mut Builder,
    u: &mut Vec<QubitId>,
    v: &mut Vec<QubitId>,
    round: usize,
    defer_boundary: bool,
) -> (QubitId, Vec<QubitId>, Option<DeferredWalkPhase>) {
    let width = value_width(round);
    shrink_to(circ, u, v, width);
    if round == 0 {
        let a0 = round0_forward(circ, v);
        park_odd_bits(circ, u, v);
        return (a0, Vec::new(), None);
    }
    if round == 1 {
        return (
            round1_forward(circ, &u[1..width], &v[1..width]),
            Vec::new(),
            None,
        );
    }
    let (source, target) = walk_operands(u, v, round, width);
    let m = target.len();
    // C4-W: a round carries the quarter step only when it also carries a record;
    // a round without one (`depth_at` == 0) is the head's own round, byte for byte.
    let d = depth_at(round);
    let quarter = mod4_sign() && d > 0;
    let sign = circ.alloc_qubit();
    circ.cx(target[0], sign);
    circ.cx(source[0], sign);
    // The mod-4 rule's one free X: the complement of the head's choice, which
    // forces the sum to 0 mod 4 and so guarantees k >= 2.
    if quarter {
        circ.x(sign);
    }
    // C4-W: THE OVERFLOW GUARD. `w` = "the mod-4 sum would be 0 mod 2^(cap+2)",
    // i.e. the record would overflow -- which includes S == 0 at the terminal.
    // On those rounds the head's sign is used instead (S == 2 mod 4, k == 1,
    // record 0), so every round's record is EXACT, the rail is always odd, and
    // the terminal (+-1, +-1) is a fixed point. `w` is an AND of live pre-add
    // wires and is erased below off the record it determines.
    let guard = if quarter && mod4_guard() {
        let w = circ.alloc_qubit();
        guard_xor(circ, w, sign, source, target, (1usize << d) - 1);
        circ.cx(w, sign);
        Some(w)
    } else {
        None
    };
    let rule = if !quarter {
        WalkRule::Head
    } else if let Some(w) = guard {
        WalkRule::Guarded(w)
    } else {
        WalkRule::Quarter
    };
    // Previous forward target is now the source. Its halving explicitly copied
    // its sign bit; retain that promise only if this round did not shrink it.
    let source_sign_loan=env_flag("PP_SOURCE_SIGN_LOAN") && !quarter && round>=3
        && m>=6 && width==value_width(round-1);
    let phase = walk_add(circ, sign, source, target, true, rule, defer_boundary, None, source_sign_loan);
    let depth = if quarter {
        // C4-W: the register holds W = S/2, whose valuation is the halving depth
        // beyond the head's one: v2(W) = k - 1, and 0 on a guarded round (S is
        // 2 mod 4 there, so W is odd) -- the record reads 0 with no gate. Under
        // the guard v2(W) <= cap, so the record is EXACT. The barrel evicts
        // exactly v2(W) provably-zero bits, and what follows is the head's own
        // halving of an odd value, byte for byte.
        let depth = depth_extract_pre(circ, target, round, d);
        barrel_down(circ, target, &depth, true);
        depth
    } else {
        Vec::new()
    };
    // Halve: rotate the register down. The value's bit 0 is one -- under the
    // head's rule that is what `sign` was chosen for, under the quarter step it
    // is what the barrel restored -- so the wire it vacates arrives at the top
    // holding a one, and an X leaves it clean for the sign extension.
    rotate_down(circ, target);
    circ.x(target[m - 1]);
    circ.cx(target[m - 2], target[m - 1]);
    if let Some(w) = guard {
        // Erase `w` off the record, which is 0 exactly when the guard fired.
        guard_xor_record_zero(circ, w, &depth);
        circ.free(w);
    }
    (sign, depth, phase)
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
    depth: &[QubitId],
    fix: Option<BitId>,
) {
    walk_back_round_phase(circ, u, v, round, sign, depth, fix, None);
}

fn walk_back_round_phase(
    circ: &mut Builder,
    u: &mut Vec<QubitId>,
    v: &mut Vec<QubitId>,
    round: usize,
    sign: QubitId,
    depth: &[QubitId],
    fix: Option<BitId>,
    deferred: Option<DeferredWalkPhase>,
) {
    let width = value_width(round);
    let source_grew=u.len()<width;
    grow_to(circ, u, v, width);
    if round == 0 {
        assert!(deferred.is_none());
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
        assert!(deferred.is_none());
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
    // C2-record: a trailing round's tape wire was measured out; recompute the
    // sign from the fixed-point pair and cancel the deferred phase. The round's
    // own tail (`cx(target[0], sign); cx(source[0], sign); free(sign)`) erases
    // this wire against the restored PRE-round operands, so it costs no extra
    // gate to give back.
    let sign = match fix {
        Some(c) => {
            let s = circ.alloc_qubit();
            if !c2_shed() {
                circ.cx(target[0], s);
                circ.cx(source[0], s);
            }
            circ.z_if(s, c);
            circ.free_bit(c);
            s
        }
        None => sign,
    };
    // C4-W: a round is a quarter round exactly when it carries a record; the
    // guard wire is recomputed off that record (0 <=> the guard fired).
    let quarter = !depth.is_empty();
    let guard = if quarter && mod4_guard() {
        let w = circ.alloc_qubit();
        guard_xor_record_zero(circ, w, depth);
        Some(w)
    } else {
        None
    };
    // Double: the mirror of the halving rotation. The top wire is a sign copy, so
    // the CX clears it; it comes back round to the bottom, where bit 1 of twice
    // an odd value is a one.
    circ.cx(target[m - 2], target[m - 1]);
    rotate_up(circ, target);
    circ.x(target[0]);
    if quarter {
        // C4-W: undo the barrel, then erase the record off the restored W.
        barrel_up(circ, target, depth, true);
        depth_erase_pre(circ, target, depth);
    }
    circ.x(sign);
    let rule = if !quarter {
        WalkRule::Head
    } else if let Some(w) = guard {
        WalkRule::Guarded(w)
    } else {
        WalkRule::Quarter
    };
    // grow_to has just created the source's top sign copy. This is a fresh
    // structural promise even on a path already affected by truncation.
    let source_sign_loan=env_flag("PP_SOURCE_SIGN_GROW") && source_grew && !quarter && m>=6;
    let generated = walk_add(circ, sign, source, target, false, rule, false, deferred, source_sign_loan);
    assert!(generated.is_none());
    circ.x(sign);
    if let Some(w) = guard {
        // sign = sigma ^ w: strip w, then erase w off the restored operands --
        // `sign` holds sigma here, before the quarter step's X comes off it.
        circ.cx(w, sign);
        guard_xor(circ, w, sign, source, target, (1usize << depth.len()) - 1);
        circ.free(w);
    }
    if quarter {
        circ.x(sign);
    }
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

// â”€â”€â”€ The walk adder â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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
/// so the generic chain's first two ANDs never have to be emitted â€” and the two
/// bit-0 wires never have to be held (see [`park_odd_bits`]).
///
/// PRECONDITION: `sign = target[0] ^ source[0]`, which is the choice that keeps
/// the halved sum odd.
///
/// Wide enough, and the ladder is split in two so that only about half the
/// carries are ever live at once. [`walk_low_chunk`] decides that from the live
/// count, which is why the caller passes nothing: both call sites reach here
/// with the round's whole footprint already allocated.
///
/// With `PP_CUT_WALKLOAN` set, the add also lends its duplicated bit-1 wire
/// into its own carry ladder: after the bit-1 preamble, `target[0]` is a known
/// function of other live wires (see [`walk_add_single`]), so it parks at |0>
/// for the length of the high ladder and the ladder runs one wire narrower.
fn walk_add(
    circ: &mut Builder,
    sign: QubitId,
    source: &[QubitId],
    target: &[QubitId],
    target0_is_one: bool,
    rule: WalkRule,
    defer_boundary: bool,
    deferred: Option<DeferredWalkPhase>,
    source_sign_loan: bool,
) -> Option<DeferredWalkPhase> {
    assert!(!(defer_boundary && deferred.is_some()));
    let loan = cut_walkloan();
    let split=walk_low_chunk(circ, source.len(), loan, source_sign_loan);
    if source_sign_loan && env_flag("PP_SOURCE_SIGN_LOAN_TRACE") {
        eprintln!("SOURCE_SIGN_LOAN {} {} {}",source.len(),circ.active_qubits(),split.unwrap_or(0));
    }
    match split {
        Some(low) => {
            assert!(deferred.is_none(), "deferred phase reached a split inverse walk");
            walk_add_split(
                circ, sign, source, target, target0_is_one, low, loan, rule, defer_boundary, source_sign_loan,
            )
        }
        None => {
            walk_add_single(
                circ, sign, source, target, target0_is_one, loan, rule, deferred, source_sign_loan,
            );
            None
        }
    }
}

/// C4-W: which sign rule chose `sign`, because two of the walk adder's
/// shortcuts are consequences of the rule and not of the arithmetic.
///
/// With both values odd, the carry into bit 1 is `c1 = sign ^ target0` under
/// any rule. The carry into bit 2 is `maj(t1 ^ sign, s1, c1)`: under the head's
/// rule (`sign = t1 ^ s1`, sum 2 mod 4) that is the source's bit 1; under the
/// quarter step (`sign = t1 ^ s1 ^ 1`, sum 0 mod 4) it is `c1`. Likewise the
/// walk-loan's parked wire holds `t1 ^ 1`, which is `source[0]`'s value under
/// the head's rule and its complement under the quarter step; and on the
/// walk-back the doubled value's bit 1 is a one under the head's rule and a
/// zero under the quarter step. `Guarded(w)` is the C4-W round that picks the
/// head's rule exactly when `w` is set, so every one of these becomes a
/// `w`-selection between the two.
#[derive(Clone, Copy, Debug)]
enum WalkRule {
    Head,
    Quarter,
    Guarded(QubitId),
}

/// `PP_CUT_WALKLOAN` (default ON): lend the walk adder's duplicated bit-1
/// wire into its carry ladder, narrowing every split's boundary repair by one
/// bit. Setting it to 0/false/no/off restores the pre-cut stream bit-for-bit.
fn cut_walkloan() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| {
        env_raw("PP_CUT_WALKLOAN").is_none_or(|value| {
            !matches!(
                value.to_ascii_lowercase().as_str(),
                "0" | "false" | "no" | "off"
            )
        })
    })
}

/// Park the duplicated bit-1 wire at |0> for lending into a carry ladder, or
/// undo that parking. Self-inverse.
///
/// After the bit-1 preamble (`cx_all` plus the two [`carry1_into`]s) the wire
/// is a known function of wires that stay live, so it can be cleared now and
/// rebuilt exactly once the ladder is done with it:
///
///   * forward (`target0_is_one`), where the tape gives `sign = t1 ^ s1`:
///     `target[0] = t1 ^ 1 = source[0]` -- the two wires hold the SAME value,
///     so one CX clears it (and re-creates it).
///   * walk-back (`target0_is_one = false`): `target[0] = D1`, bit 1 of the
///     doubled value, which is the constant one -- the walk-back comment's
///     "bit 1 of twice an odd value is a one", the same fact
///     `erase_boundary_carry`'s classical borrow relies on -- so one X clears
///     it. (The `sign` and `carry1_into` applications cancel out of this wire
///     regardless of the tape value.)
fn walkloan_park(
    circ: &mut Builder,
    source0: QubitId,
    target0: QubitId,
    forward: bool,
    rule: WalkRule,
) {
    if forward {
        circ.cx(source0, target0);
        // Under the quarter step the two wires hold COMPLEMENTARY values.
        match rule {
            WalkRule::Head => {}
            WalkRule::Quarter => circ.x(target0),
            WalkRule::Guarded(w) => {
                circ.x(target0);
                circ.cx(w, target0);
            }
        }
    } else {
        // Bit 1 of the doubled value: a one under the head's rule (twice an
        // odd value), a zero under the quarter step (2^k of it, k >= 2).
        match rule {
            WalkRule::Head => circ.x(target0),
            WalkRule::Quarter => {}
            WalkRule::Guarded(w) => circ.cx(w, target0),
        }
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
    loan: bool,
    rule: WalkRule,
    deferred: Option<DeferredWalkPhase>,
    source_sign_loan: bool,
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
    // With the loan on, `target[0]` is now redundant (see `walkloan_park`) and
    // nothing reads it until the bit-1 unwind below: park it at |0> and lend it
    // to the ripple, whose ladder is then one wire narrower.
    if loan {
        walkloan_park(circ, source[0], target[0], target0_is_one, rule);
    }
    // The carry into bit 2 (see `WalkRule`): every site XORs `c1` in through
    // `carry1_into` and `g` on top of it.
    let g = walk_c2_term(circ, rule, source[0]);
    if let Some(g) = g {
        circ.cx(g, source[1]);
    }
    carry1_into(circ, sign, target0_is_one, source[1]);
    if let Some(g) = g {
        circ.cx(g, target[1]);
    }
    carry1_into(circ, sign, target0_is_one, target[1]);
    circ.ccx(source[1], target[1], carry2);
    if let Some(g) = g {
        circ.cx(g, carry2);
    }
    carry1_into(circ, sign, target0_is_one, carry2);

    // `source[2..]` begins at full bit 3, so the inverse ripple carry equal to
    // a forward boundary entering full bit `low` has local index `low - 4`.
    let deferred = deferred.map(|phase| {
        assert!(phase.low >= 4);
        (phase.low - 4, phase.measured)
    });
    if loan {
        let room = walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
        if source_sign_loan {
            super::modular::ripple_add_source_sign_loan(circ,&source[2..],&target[2..],Some(carry2),Some(target[0]),deferred);
        } else if env_flag("PP_Q1208_HELPERS") && source.len().saturating_sub(5) > room {
            assert!(deferred.is_none(), "compact inverse ripple has no deferred-phase hook");
            let width=source.len()-2;
            super::compact_chunk_add::add(circ,&source[2..],&target[2..],Some(carry2),false,exact_walk_chunk_width(width,room));
        } else {
            ripple_add_lent_with_deferred_phase(
                circ, &source[2..], &target[2..], Some(carry2), target[0], deferred,
            );
        }
        // The lent wire came back clean and `source[0]` is untouched since the
        // park (it only ever reads as a control), so the same gate restores.
        walkloan_park(circ, source[0], target[0], target0_is_one, rule);
    } else if source_sign_loan {
        super::modular::ripple_add_source_sign_loan(circ,&source[2..],&target[2..],Some(carry2),None,deferred);
    } else {
        ripple_add_with_deferred_phase(
            circ, &source[2..], &target[2..], Some(carry2), None, deferred,
        );
    }

    // Bit 2, in reverse: mirrors the special case above.
    if let Some(g) = g {
        circ.cx(g, carry2);
    }
    carry1_into(circ, sign, target0_is_one, carry2);
    let measured = circ.alloc_bit();
    circ.hmr(carry2, measured);
    circ.cz_if(source[1], target[1], measured);
    circ.free_bit(measured);
    if let Some(g) = g {
        circ.cx(g, source[1]);
    }
    carry1_into(circ, sign, target0_is_one, source[1]);
    circ.cx(source[1], target[1]);
    walk_c2_term_drop(circ, rule, source[0], g);

    carry1_into(circ, sign, target0_is_one, source[0]);
    circ.cx(source[0], target[0]);
    circ.free(carry2);

    circ.cx_all(sign, target);
}

/// What the bit-2 carry sites XOR in on top of `c1`, while `source0` holds
/// `s1 ^ c1`: that wire itself under the head's rule (the sites then see
/// `s1`), nothing under the quarter step (they see `c1`), and `w AND source0`
/// -- one Toffoli, an AND of two live wires -- when the round is guarded.
fn walk_c2_term(circ: &mut Builder, rule: WalkRule, source0: QubitId) -> Option<QubitId> {
    match rule {
        WalkRule::Head => Some(source0),
        WalkRule::Quarter => None,
        WalkRule::Guarded(w) => Some(and_clean(circ, w, source0)),
    }
}

fn walk_c2_term_drop(circ: &mut Builder, rule: WalkRule, source0: QubitId, g: Option<QubitId>) {
    if let WalkRule::Guarded(w) = rule {
        and_uncompute(circ, g.expect("the guarded rule made a term"), w, source0);
    }
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
/// out `None` on their own â€” the ladder has room and no split is called for.
///
/// The two rejections below are both exact, not margins:
///
///   * `low < 4` is where the single ladder still fits. It is three wires
///     lighter than the formula above assumes â€” no boundary wire, and its two
///     lowest carries are classical ([`walk_add_single`]) â€” so it peaks at
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
///
/// With the `PP_CUT_WALKLOAN` borrow the picture shifts by one wire: the
/// single ladder's high ripple lends `target[0]`, peaking at `live + m - 4`,
/// so it still fits at `low == 4`; and a split's high chunk lends it too,
/// peaking at `live + (m - low) - 1`, so the split point comes out one bit
/// narrower. The borrow needs a real ladder to lend into: below
/// `MIN_WALK_WIDTH` the high ripple has no carry position to spare and the
/// arithmetic is the pre-loan one.
fn walk_low_chunk(circ: &Builder, m: usize, loan: bool, source_sign_loan: bool) -> Option<usize> {
    // `low` is a bit position, so it counts against the full value width.
    let n = m + 1;
    let low = (circ.active_qubits() as usize + m).saturating_sub(walk_max_qubits());
    let single_fits_below = (if loan && m >= MIN_WALK_WIDTH { 5 } else { 4 })+usize::from(source_sign_loan);
    if n < 12 || low < single_fits_below {
        return None;
    }
    let low = low-usize::from(loan)-usize::from(source_sign_loan);
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
    loan: bool,
    rule: WalkRule,
    defer_boundary: bool,
    source_sign_loan: bool,
) -> Option<DeferredWalkPhase> {
    let m = source.len();
    assert_eq!(m, target.len());
    // `walk_low_chunk` never returns a narrower split: the boundary repair
    // compares `low - 2` bits per operand and `cmp_lt_phase` needs at least two.
    assert!(low >= 4 && low < m);

    circ.cx_all(sign, target);

    // Bit 0's carry is the classical `c1` and gets no wire at all; bit 1's is
    // `carry1` -- the source's own bit 1 under the head's rule, `c1` under the
    // quarter step, their `w`-selection when guarded (see `WalkRule`). That is
    // the low chunk's carry-in, and the carry off the chunk's top is the
    // boundary the high chunk rides in on.
    let carry1 = circ.alloc_qubit();
    let boundary = circ.alloc_qubit();
    match rule {
        WalkRule::Head => {
            circ.cx(source[0], carry1);
            carry1_into(circ, sign, target0_is_one, source[0]);
        }
        WalkRule::Quarter => {
            carry1_into(circ, sign, target0_is_one, source[0]);
            carry1_into(circ, sign, target0_is_one, carry1);
        }
        WalkRule::Guarded(w) => {
            carry1_into(circ, sign, target0_is_one, source[0]);
            carry1_into(circ, sign, target0_is_one, carry1);
            circ.ccx(w, source[0], carry1);
        }
    }
    carry1_into(circ, sign, target0_is_one, target[0]);
    // With the loan on, `target[0]` is now redundant (see `walkloan_park`):
    // park it at |0> for the high chunk's ladder. Neither chunk's ripple nor
    // the boundary erasure reads it; the bit-1 sum it would have accumulated is
    // rebuilt from `sign` and `source[0]` at the restore below.
    if loan {
        walkloan_park(circ, source[0], target[0], target0_is_one, rule);
    }

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
    match rule {
        WalkRule::Head => {
            carry1_undo(circ, sign, target0_is_one, source[0]);
            circ.cx(source[0], carry1);
        }
        WalkRule::Quarter => {
            carry1_undo(circ, sign, target0_is_one, carry1);
            carry1_undo(circ, sign, target0_is_one, source[0]);
        }
        WalkRule::Guarded(w) => {
            circ.ccx(w, source[0], carry1);
            carry1_undo(circ, sign, target0_is_one, carry1);
            carry1_undo(circ, sign, target0_is_one, source[0]);
        }
    }
    if !loan {
        circ.cx(source[0], target[0]);
    }
    circ.free(carry1);

    // High chunk, carried in on `boundary` and wrapping at the top.
    assert!(m - low >= 1, "low + 1 <= m leaves a final high carry");
    if loan {
        if source_sign_loan {
            super::modular::ripple_add_source_sign_loan(circ,&source[low-1..],&target[low-1..],Some(boundary),Some(target[0]),None);
        } else {
        ripple_add_lent(
            circ,
            &source[low - 1..],
            &target[low - 1..],
            Some(boundary),
            target[0],
        );
        }
        // The lent wire came back clean; rebuild the bit-1 value the un-loaned
        // code holds here: `t1 ^ target0` forward (where that is
        // `sign ^ source[0] ^ 1` under the head's rule and `sign ^ source[0]`
        // under the quarter step), bit 1 of the doubled value on walk-back (a
        // one under the head's rule, a zero under the quarter step) -- then the
        // shared CX adds the source's bit 1 to finish the bit-1 sum.
        if target0_is_one {
            circ.cx(sign, target[0]);
            circ.cx(source[0], target[0]);
        }
        match rule {
            WalkRule::Head => circ.x(target[0]),
            WalkRule::Quarter => {}
            WalkRule::Guarded(w) => circ.cx(w, target[0]),
        }
        circ.cx(source[0], target[0]);
    } else if source_sign_loan {
        super::modular::ripple_add_source_sign_loan(circ,&source[low-1..],&target[low-1..],Some(boundary),None,None);
    } else {
        ripple_add(
            circ,
            &source[low - 1..],
            &target[low - 1..],
            Some(boundary),
            None,
        );
    }

    // The comparator's classical carry-in is the borrow out of bits 1:0 of
    // `sum - addend`, which is the same quantity as the addition's carry into
    // bit 2: `s1` under the head's rule, `c1` under the quarter step.
    let deferred = if defer_boundary {
        let measured = circ.alloc_bit();
        circ.hmr(boundary, measured);
        circ.free(boundary);
        Some(DeferredWalkPhase { measured, low })
    } else {
        match rule {
            WalkRule::Head => erase_boundary_carry(circ, source, target, boundary, low, source[0]),
            WalkRule::Quarter => {
            // `c1 = sign ^ target0`, read off the sign wire.
            if target0_is_one {
                circ.x(sign);
            }
            erase_boundary_carry(circ, source, target, boundary, low, sign);
            if target0_is_one {
                circ.x(sign);
            }
            }
            WalkRule::Guarded(w) => {
            let c2 = circ.alloc_qubit();
            carry1_into(circ, sign, target0_is_one, c2);
            carry1_into(circ, sign, target0_is_one, source[0]);
            circ.ccx(w, source[0], c2);
            carry1_undo(circ, sign, target0_is_one, source[0]);
            erase_boundary_carry(circ, source, target, boundary, low, c2);
            carry1_into(circ, sign, target0_is_one, source[0]);
            circ.ccx(w, source[0], c2);
            carry1_undo(circ, sign, target0_is_one, source[0]);
            carry1_undo(circ, sign, target0_is_one, c2);
            circ.release_clean(c2);
            }
        }
        None
    };

    circ.cx_all(sign, target);
    deferred
}

/// Bits `0..low` of the complemented-frame sum are now in `target` and the
/// untouched addend in `source`, so `sum < addend` over them is the boundary
/// carry itself.  Bits 0 and 1 of that comparison are classical: on the forward
/// walk the target's bit 0 is one and `sign = target[0] ^ source[0]`; on walk-back
/// its bits 1:0 are `10` after undoing the halving rotation.  The source's bit 0
/// is one either way, so the borrow out of the first two positions is exactly the
/// source's bit 1 â€” start the comparator at bit 2 with that as its live carry-in
/// and two nonlinear stages drop out exactly.
fn erase_boundary_carry(
    circ: &mut Builder,
    source: &[QubitId],
    target: &[QubitId],
    boundary: QubitId,
    low: usize,
    carry_in: QubitId,
) {
    // Bits 2..low, with the classical borrow out of bits 1:0 standing in for
    // everything below.
    let requested=env_raw("PP_Q1208_WALK_COMPARE").and_then(|s|s.parse::<usize>().ok()).unwrap_or(0);
    let minrail=env_raw("PP_Q1208_COMPARE_MIN_RAIL").and_then(|s|s.parse::<usize>().ok()).unwrap_or(0);
    let keep=if requested==0 || source.len()+1 < minrail {low-2}else{requested.min(low-2)};
    assert!(keep>=2);
    let first=low-1-keep;
    erase_with_compare(
        circ,
        boundary,
        &target[first..low - 1],
        &source[first..low - 1],
        if first==1 {Some(carry_in)} else {None},
    );
    circ.free(boundary);
}

// â”€â”€â”€ Rounds 0 and 1: the lift into the invariant â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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
/// `sign = p[1] ^ v[0]` and `p[1]` is set, and `(p+1)/2` is even â€” so no carry
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

// â”€â”€â”€ Freeing tape wires early â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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


// â”€â”€â”€ C2-record: the trailing tape window â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

/// `PP_C2_TAILSIGN` (default 0): how many trailing tape signs are measured out
/// and recomputed instead of stored.
///
/// The walk reaches its `(+-1, +-1)` fixed point well before round `R` -- that
/// is what [`loan_terminal`] already relies on -- and at the fixed point every
/// bit below the sign is a copy of the sign, so `bit1(target) ^ bit1(source)` is
/// the round's sign whether it is read before the round or after it. A trailing
/// sign is therefore recoverable from two live wires, and the tape wire is not
/// needed between its own round and its own walk-back.
fn c2_tailsign() -> usize {
    static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| {
        env_raw("PP_C2_TAILSIGN")
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(0)
    })
}

/// `PP_C2_SHED` (default off): the INSTRUMENT. Same wire accounting as
/// `PP_C2_TAILSIGN`, no recomputation -- the sign arrives `|0>`. Arithmetically
/// wrong by construction; it exists to measure `dQ/drecord` downward at a fixed
/// arm, which no across-arm slope can do.
fn c2_shed() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_C2_SHED"))
}

/// `PP_C2_LEAD=J` (default 0): INSTRUMENT. Shed a LEADING window -- rounds
/// `2..2+J` -- instead of a trailing one. The peak law says an early wire is
/// live at the argmax and a trailing one is not, so this is the same count of
/// record wires at a different place on the walk.
fn c2_lead() -> usize {
    static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| {
        env_raw("PP_C2_LEAD")
            .and_then(|v| v.parse::<usize>().ok())
            .unwrap_or(0)
    })
}

/// `PP_C2_ALLSHED` (default off): INSTRUMENT. Drop the head-boundary clamp so the
/// window covers the WHOLE record -- the term's own floor, which is what
/// `best_case` asks for. Only meaningful with `PP_C2_SHED`.
fn c2_allshed() -> bool {
    static SLOT: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *SLOT.get_or_init(|| env_flag("PP_C2_ALLSHED"))
}

/// First round of the trailing window. The window never reaches back into the
/// LEADING batch: those rounds are replayed out of `tape` in both traversals and
/// `recompute_bchain_sign` reads the whole of `tape[1..r1]`, so a shed wire there
/// is read after it is gone.
fn c2_lo(rounds: usize, r1: usize) -> usize {
    if c2_tailsign() == 0 {
        return rounds;
    }
    if c2_allshed() {
        return 2;
    }
    rounds.saturating_sub(c2_tailsign()).max(r1).max(2)
}

/// The terminal sign, off the two wires [`loan_terminal`] leaves standing.
fn c2_term_sign(circ: &mut Builder, u: &[QubitId], v: &[QubitId]) -> QubitId {
    let s = circ.alloc_qubit();
    if !c2_shed() {
        circ.cx(u[u.len() - 1], s);
        circ.cx(v[v.len() - 1], s);
    }
    s
}

fn c2_drop_term_sign(circ: &mut Builder, u: &[QubitId], v: &[QubitId], s: QubitId) {
    if !c2_shed() {
        circ.cx(u[u.len() - 1], s);
        circ.cx(v[v.len() - 1], s);
    }
    circ.free(s);
}

/// Does round `r` shed its tape wire? Quarter rounds keep theirs: their sign
/// carries the mod-4 complement and the guard, which this recomputation does not
/// reproduce.
fn c2_sheds(r: usize, rounds: usize, r1: usize, depth: &[QubitId]) -> bool {
    if c2_lead() > 0 {
        return r >= 2 && r < 2 + c2_lead() && depth.is_empty();
    }
    c2_tailsign() > 0 && r >= c2_lo(rounds, r1) && depth.is_empty()
}

/// Measure out the trailing tape wires in one go (the multiply traversal, whose
/// mid and tail replays both run after the peak has already been set).
fn c2_shed_tape(
    circ: &mut Builder,
    tape: &[QubitId],
    depths: &[Vec<QubitId>],
    rounds: usize,
    r1: usize,
) -> Vec<Option<BitId>> {
    let mut fixes: Vec<Option<BitId>> = vec![None; rounds];
    if c2_tailsign() == 0 && c2_lead() == 0 {
        return fixes;
    }
    for r in 0..rounds {
        if c2_sheds(r, rounds, r1, &depths[r]) {
            fixes[r] = Some(free_sign_bit(circ, tape[r]));
        }
    }
    fixes
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

// â”€â”€â”€ The replay â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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
    depth: &[QubitId],
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
        _ => {
            replay_add_halve(circ, sign, source, target, fold_window, round);
            if !depth.is_empty() {
                replay_extra_shift(circ, source, target, depth, round, true);
            }
        }
    }
}

fn replay_doubling_round(
    circ: &mut Builder,
    round: usize,
    sign: QubitId,
    depth: &[QubitId],
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
            if !depth.is_empty() {
                replay_extra_shift(circ, source, target, depth, round, false);
            }
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
    if retained_prebias::try_replay(circ,sign,source,target,fold_window,round) {return;}
    if env_flag("PP_JOINT_PREBIAS_DIV") && joint_prebias::eligible(circ,round) {
        joint_prebias::joint_prebias_div(circ,sign,source,target,fold_window,round);return;
    }
    let f = f();
    circ.cx_all(sign, target);
    let overflow = chunked_add(circ, source, target, round, false);

    if env_flag("PP_REUSE_DIV_PARITY") {
        fold_halve_reused(circ, &target[..fold_window], sign, overflow);
        let mut k = flag_compare(round) + usize::from(policy_width(round) >= flag_widen_div());
        let borrow = if env_flag("CMP_SEED_ALL") { if !seed_keep_width_for(false){k -= 1;} Some(source[N-k-1]) } else {None};
        k=refined_flag_window(k,fold_window,borrow.is_some());
        circ.record_replay_site('F', round, N, k);
        trace_replay_predictor('F',round,false,N,k,source,borrow);
        erase_with_compare(circ, overflow, &target[N-k..], &source[N-k..], borrow);
        circ.free(overflow);
        circ.cx_all(sign, target);
        // The outgoing parity already occupies bit0. Rotate it into bit255.
        rotate_down(circ, target);
        return;
    }

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
    let mut k = flag_compare(round) + usize::from(policy_width(round) >= flag_widen_div());
    let borrow = if env_flag("CMP_SEED_ALL") { if !seed_keep_width_for(false){k -= 1;} Some(source[N-k-1]) } else {None};
    k=refined_flag_window(k,fold_window,borrow.is_some());
    circ.record_replay_site('F', round, N, k);
    trace_replay_predictor('F',round,false,N,k,source,borrow);
    erase_with_compare(circ, overflow, &target[N - k..], &source[N - k..], borrow);
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
    if joint_lowfold::try_replay(circ,sign,source,target,fold_window,round,Some(doubled_out)) {
        circ.cx_all(sign,target);return;
    }
    let add_out = chunked_add(circ, source, target, round, true);

    if env_flag("PP_REUSE_MUL_SELECTORS") {
        if env_flag("PP_JOINT_MUL_FOLD") {
            assert!(!split_fold(),"joint receiver is exact; do not silently compose a split fold");
            fold_double_joint(circ,&target[..fold_window],sign,source[0],doubled_out,add_out);
        } else {
            fold_double_reused(circ, &target[..fold_window], sign, doubled_out, add_out);
        }
    } else {
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

    }

    // After the fold, still in the complemented frame,
    // target[0] = sign ^ source[0] ^ d ^ o. Clear d without a second ripple.
    circ.cx(target[0], doubled_out);
    circ.cx(sign, doubled_out);
    circ.cx(source[0], doubled_out);
    circ.cx(add_out, doubled_out);
    circ.free(doubled_out);

    let wide = policy_width(round) >= 38;
    let mut k = flag_compare(round) + usize::from(a5_policy() == "mul-f-plus1-early200" && (2..202).contains(&round));
    let borrow = if wide && matches!(a5_policy(), "mul-f-seed" | "mul-fb-seed") {
        Some(source[N - k - 1])
    } else if !wide && env_flag("PP_SEED_SHORT_MUL_F") {
        // Extend source-bit prediction to the previously unseeded narrow
        // multiply flag sites. Keep the complete old comparison window;
        // this changes the approximation predicate, not its gate count.
        // Do not silently swap an unseeded refinement for a seeded one.
        for knob in ["PP_REFINE_UNSEEDED_F","PP_REFINE_SEEDED_F"] {
            assert_eq!(super::optional_env::<usize>(knob).unwrap_or(0),0,
                "short multiply seeding excludes flag refinement composition");
        }
        Some(source[N-k-1])
    } else { None };
    k=refined_flag_window(k,fold_window,borrow.is_some());
    circ.record_replay_site('F', round, N, k);
    trace_replay_predictor('F',round,true,N,k,source,borrow);
    erase_with_compare(circ, add_out, &target[N - k..], &source[N - k..], borrow);
    circ.free(add_out);
    circ.cx_all(sign, target);
}

/// Same signed correction as replay_double_add, keeping only nonlinear state.
/// routed becomes plus_2f by XORing minus_f, then returns before its erasure.
/// add_out successively hosts sign^o, d^o, and plus_f; restore before consumers.
/// No comparison window, carry boundary, round, or modular approximation changes.
fn fold_double_reused(circ: &mut Builder, target: &[QubitId], sign: QubitId,
                      doubled_out: QubitId, add_out: QubitId) {
    circ.cx(sign, add_out);
    let routed = and_clean(circ, doubled_out, add_out);
    circ.cx(sign, add_out);
    let minus_f = and_clean(circ, routed, sign);
    circ.cx(minus_f, routed); // plus_2f, without a copied selector wire
    circ.cx(doubled_out, add_out); // odd_correction
    let first_carry = and_clean(circ, target[0], add_out);
    circ.cx(minus_f, add_out); // plus_f
    fold_selected(circ, target, f(), add_out, Some(routed), minus_f, first_carry);
    circ.cx(minus_f, add_out); // odd_correction again
    circ.cx(add_out, target[0]);
    and_uncompute(circ, first_carry, target[0], add_out);
    circ.cx(add_out, target[0]);
    circ.cx(doubled_out, add_out); // original overflow
    circ.cx(minus_f, routed); // original routed predicate
    and_uncompute(circ, minus_f, routed, sign);
    circ.cx(sign, add_out);
    and_uncompute(circ, routed, doubled_out, add_out);
    circ.cx(sign, add_out);
}


/// Combined selector/fold contract from replay_double_add:
/// before folding z0 = sign XOR source0. After its exact bit0 update,
/// z0 = sign XOR source0 XOR doubled_out XOR add_out.
/// Thus doubled_out can be released while the upper fold runs, provided
/// add_out stays in its ORIGINAL frame. Derive plus_f from the new z0
/// instead of retaining it in add_out. All mapping changes are Clifford.
fn fold_double_joint(c:&mut Builder,z:&[QubitId],s:QubitId,v0:QubitId,d:QubitId,o:QubitId) {
    let base=c.active_qubits();let w=z.len();assert!(w>=2);
    assert!(!z.contains(&v0) && ![s,d,o].contains(&v0));
    c.cx(s,o);let a=and_clean(c,d,o);c.cx(s,o);
    let m=and_clean(c,a,s);c.cx(m,a); // a=plus2, m=minus
    c.cx(d,o);let first=and_clean(c,z[0],o);
    c.cx(o,z[0]);c.cx(d,o); // finish bit0 and restore original add_out

    for q in [z[0],s,v0,o] {c.cx(q,d);}
    c.release_clean(d);
    if let Some(bits)=joint_lowfold::GUARD.with(|g|g.get()) {
        assert!((12..=32).contains(&bits)&&bits<=w);
        let small=U256::from(977);let neg=twos_complement_bits(small,bits);
        let mut map=Vec::new();
        for i in 1..bits {
            let mut row=Vec::new();
            if small.bit(i){row.extend([z[0],s,v0,m]);}
            if small.bit(i-1){row.push(a);}
            if neg[i]{row.push(m);}
            let mut unique=Vec::new();for q in row{if let Some(j)=unique.iter().position(|&v|v==q){unique.remove(j);}else{unique.push(q);}}
            map.push(unique);
        }
        let room=walk_max_qubits().saturating_sub(c.active_qubits()as usize);
        let plan=super::width_composition::direct_plan(bits-1,room).expect("retained low-fold capacity");
        super::width_composition::direct_add(c,&map,&z[1..bits],first,&plan);
        let mut high=Vec::new();
        for i in 0..w-32{high.push(if i==0{vec![z[0],s,v0]}else if i==1{vec![a,m]}else{vec![m]});}
        joint_prebias::mapped_zero(c,&z[32..],&high);
    } else {
    let f=f();let neg=twos_complement_bits(f,w);
    let mut map=Vec::new();
    for i in 1..w {
        let mut terms=Vec::new();
        if f.bit(i) {terms.extend([z[0],s,v0,m]);} // plus_f = z0 XOR s XOR v0 XOR minus
        if f.bit(i-1) {terms.push(a);}
        if neg[i] {terms.push(m);}
        // XOR cancellation is necessary if a future constant overlaps terms.
        let mut unique=Vec::new();
        for q in terms {if let Some(j)=unique.iter().position(|&v|v==q){unique.remove(j);}else{unique.push(q);}}
        map.push(unique);
    }
    let n=w-1;let room=walk_max_qubits().saturating_sub(c.active_qubits() as usize);
    let plan=(room..=n.max(room)).find_map(|r|super::width_composition::direct_plan(n,r)).unwrap();
    if env_flag("PP_JOINT_FOLD_TRACE") {eprintln!("JOINT_FOLD {} {} {} {} {}",w,base,room,plan.peak,plan.extra2);}
    super::width_composition::direct_add(c,&map,&z[1..],first,&plan);

    }
    c.reacquire(d);for q in [z[0],s,v0,o] {c.cx(q,d);}
    c.cx(d,o);c.cx(o,z[0]);and_uncompute(c,first,z[0],o);c.cx(o,z[0]);c.cx(d,o);
    c.cx(m,a);and_uncompute(c,m,a,s);
    c.cx(s,o);and_uncompute(c,a,d,o);c.cx(s,o);
    assert_eq!(c.active_qubits(),base,"joint-fold ownership");
}

// Number of physical integer sign copies loaned to this field replay. The
// chunk planner uses the old room to preserve all approximate boundary sites.
thread_local! { static REPLAY_SIGN_LOANS:std::cell::Cell<usize>=const{std::cell::Cell::new(0)}; }
fn with_sign_copy_loans(circ:&mut Builder,loans:&[(QubitId,QubitId)],body:impl FnOnce(&mut Builder)) {
    assert_eq!(REPLAY_SIGN_LOANS.with(|s|s.get()),0);
    for &(q,s)in loans{circ.cx(s,q);circ.release_clean(q);}
    REPLAY_SIGN_LOANS.with(|s|s.set(loans.len()));
    body(circ);
    REPLAY_SIGN_LOANS.with(|s|s.set(0));
    for &(q,s)in loans{circ.reacquire(q);circ.cx(s,q);}
}
fn forward_sign_copy_valid(w:usize,last:usize)->[bool;2] {
    if last<3{return[false,false];}
    let target=if last.is_multiple_of(2){1}else{0};let mut valid=[false,false];
    valid[target]=w==value_width(last);valid[1-target]=w==value_width(last-1);valid
}
fn with_forward_replay_sign_loans(circ:&mut Builder,u:&[QubitId],v:&[QubitId],last:usize,body:impl FnOnce(&mut Builder)) {
    if !env_flag("PP_REPLAY_SIGN_LOAN") || mod4_sign() || last<3 {body(circ);return;}
    assert_eq!(u.len(),v.len());let w=u.len();let mut loans=Vec::new();
    for(reg,valid)in[u,v].into_iter().zip(forward_sign_copy_valid(w,last)){
        if valid{loans.push((reg[w-1],reg[w-2]));}
    }
    if env_flag("PP_REPLAY_SIGN_TRACE"){eprintln!("REPLAY_SIGN_LOANS {} {} {}",last,w,loans.len());}
    with_sign_copy_loans(circ,&loans,body);
}
fn with_reverse_replay_sign_loans(circ:&mut Builder,u:&[QubitId],v:&[QubitId],valid:[bool;2],body:impl FnOnce(&mut Builder)) {
    if !env_flag("PP_REPLAY_SIGN_LOAN_MUL") || mod4_sign(){body(circ);return;}
    let mut loans=Vec::new();
    for(reg,ok)in[u,v].into_iter().zip(valid){if ok{let w=reg.len();loans.push((reg[w-1],reg[w-2]));}}
    if env_flag("PP_REPLAY_SIGN_TRACE"){eprintln!("REPLAY_SIGN_GROW_LOANS {} {}",u.len(),loans.len());}
    with_sign_copy_loans(circ,&loans,body);
}

/// Borrow the tape sign wire as the parity host during the divide fold.
/// The fold always sets bit0 to the original sign, so a SWAP transfers that
/// original sign back without retaining a separate parity copy. All higher
/// output bits equal the ordinary fold; bit0 returns p XOR overflow, ready
/// for the outer sign complement and final rotation.
fn fold_halve_reused(circ: &mut Builder, target: &[QubitId], sign: QubitId, overflow: QubitId) {
    circ.swap(sign, target[0]); // sign hosts p; target0 hosts original s
    circ.x(target[0]);
    let not_sign_and_parity = and_clean(circ, target[0], sign);
    circ.x(target[0]);
    let sign_and_parity = circ.alloc_qubit();
    circ.cx(sign, sign_and_parity);
    circ.cx(not_sign_and_parity, sign_and_parity);
    circ.x(overflow);
    let minus_f = and_clean(circ, overflow, not_sign_and_parity);
    circ.x(overflow);
    let plus_2f = and_clean(circ, overflow, sign_and_parity);
    circ.cx(not_sign_and_parity, sign_and_parity);
    circ.cx(sign, sign_and_parity);
    circ.free(sign_and_parity);
    circ.cx(target[0], sign);
    circ.cx(minus_f, sign); // sign hosts plus_f
    // Undo the already-applied bit0 correction just for the existing fold ABI.
    // fold_selected's first two CXs immediately restore target0 to original s.
    circ.cx(sign, target[0]);
    circ.cx(minus_f, target[0]);
    fold_selected(circ, target, f(), sign, Some(plus_2f), minus_f, not_sign_and_parity);
    circ.cx(minus_f, sign);
    circ.cx(target[0], sign); // original p
    let sign_and_parity = circ.alloc_qubit();
    circ.cx(sign, sign_and_parity);
    circ.cx(not_sign_and_parity, sign_and_parity);
    and_uncompute(circ, plus_2f, overflow, sign_and_parity);
    circ.x(overflow);
    and_uncompute(circ, minus_f, overflow, not_sign_and_parity);
    circ.x(overflow);
    circ.cx(sign, sign_and_parity);
    circ.cx(not_sign_and_parity, sign_and_parity);
    circ.free(sign_and_parity);
    circ.x(target[0]);
    and_uncompute(circ, not_sign_and_parity, target[0], sign);
    circ.x(target[0]);
    circ.swap(sign, target[0]); // restore sign and move p into its outgoing slot
    circ.cx(overflow, target[0]);
}

// C59X defaults to the adopted A5 mul-fb-seed predictor. No new carry is claimed exact.
fn a5_policy() -> &'static str {
    static POLICY: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    POLICY.get_or_init(|| {
        let s = String::from("mul-fb-seed");
        assert!(matches!(s.as_str(), "off" | "mul-f-seed" | "mul-b-seed" | "mul-fb-seed" | "mul-f-plus1-early200"));
        s
    }).as_str()
}

// â”€â”€â”€ The replay's chunked adder â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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
/// builder exactly as [`walk_low_chunk`] asks it. Nothing about *what* is live â€”
/// the tape, the coefficient pair, the walk registers, this cell's own retained
/// wires â€” appears in it, so none of them can drift out of a model.
fn refined_unseeded_width(width:usize,limit:usize,knob:&str)->usize {
    let extra=super::optional_env::<usize>(knob).unwrap_or(0);
    // Bounded refinement of existing windows. F sites must stay above the
    // replay correction fold, so these experiments use at most eight bits.
    assert!(extra<=8,"unseeded refinement limited to eight extra bits");
    (width+extra).min(limit)
}
fn refined_flag_width(width:usize,fold_window:usize)->usize {
    let next=refined_unseeded_width(width,N,"PP_REFINE_UNSEEDED_F");
    if next!=width {assert!(N-next>=fold_window,"refined flag window overlaps the correction fold");}
    next
}

fn refined_seeded_width(width:usize,limit:usize,knob:&str)->usize {
    let next=refined_unseeded_width(width,limit,knob);
    // One adjacent source bit with the SAME source-bit predictor is an
    // identity, not an error improvement. Omit its redundant wire/gates.
    if next==width+1 {width}else{next}
}
fn refined_flag_window(width:usize,fold_window:usize,seeded:bool)->usize {
    if !seeded{return refined_flag_width(width,fold_window);}
    let next=refined_seeded_width(width,N,"PP_REFINE_SEEDED_F");
    assert!(N-next>=fold_window,"seed refinement overlaps the correction fold");
    next
}

// Diagnostic only: record the actual operand-relative predictor passed to
// the comparator, including aliases introduced by seeded window refinement.
fn trace_replay_predictor(kind:char,round:usize,multiply:bool,pos:usize,width:usize,source:&[QubitId],borrow:Option<QubitId>) {
    if env_flag("PP_CAPTURE_REPLAY_PREDICTORS") {
        let index=borrow.map(|q|source.iter().position(|&x|x==q).expect("predictor belongs to source") as isize).unwrap_or(-1);
        eprintln!("REPLAY_PREDICTOR {} {} {} {} {} {} {}",kind,if multiply{"mul"}else{"div"},round,pos,width,index,source.len());
    }
}

fn seed_keep_width_for(boundary:bool)->bool {
    let on=env_flag("CMP_SEED_KEEP_WIDTH") || env_flag(if boundary {"CMP_SEED_KEEP_WIDTH_B"} else {"CMP_SEED_KEEP_WIDTH_F"});
    if on {
        // Changing seed classification would select a different refinement
        // knob. Keep this first transfer isolated; never silently discard an
        // existing unseeded refinement while calling the window unchanged.
        for name in["PP_REFINE_UNSEEDED_B","PP_REFINE_UNSEEDED_F","PP_REFINE_SEEDED_B","PP_REFINE_SEEDED_F"] {
            assert_eq!(super::optional_env::<usize>(name).unwrap_or(0),0,"same-width seed transfer currently excludes refinement composition");
        }
    }
    on
}

fn boundary_repair_spec(round:usize,multiply:bool,lo:usize,hi:usize)->(usize,bool) {
    let mut compare=chunk_compare(round).min(hi-lo);
    let pre_seeded=multiply && policy_width(round)>=38 && compare<hi-lo
        && matches!(a5_policy(),"mul-b-seed"|"mul-fb-seed");
    let seeded_here=env_flag("CMP_SEED_ALL") && !pre_seeded && compare+1<hi-lo;
    if seeded_here && !seed_keep_width_for(true){compare-=1;}
    if !pre_seeded && !seeded_here {compare=refined_unseeded_width(compare,hi-lo,"PP_REFINE_UNSEEDED_B");}
    (compare,pre_seeded||seeded_here)
}

/// Shorten only a whole-word, exact leading repair. Every later approximate
/// endpoint, comparison window and predictor input stays at its old position.
fn loaned_chunk_bounds(old:&[(usize,usize)],room:usize,loans:usize,round:usize,multiply:bool)->Vec<(usize,usize)> {
    let mut out=old.to_vec();
    if loans==0 || old.len()<2 || old[0].0!=0{return out;}
    let first=old[0].1;
    if boundary_repair_spec(round,multiply,0,first)!=(first,false){return out;}
    // Removing this exact boundary is also allowed if the merged first two
    // chunks fit and every surviving repair retains its absolute predicate.
    let mut merged=old[1..].to_vec();merged[0].0=0;
    let merged_sizes:Vec<_>=merged.iter().map(|&(lo,hi)|hi-lo).collect();
    let same=old[1..old.len()-1].iter().zip(&merged[..merged.len()-1]).all(|(&(a,b),&(x,y))|
        b==y && boundary_repair_spec(round,multiply,a,b)==boundary_repair_spec(round,multiply,x,y));
    if same && layout_ladder(&merged_sizes)<=room{return merged;}
    for delta in(1..=loans.min(first.saturating_sub(2))).rev(){
        out[0].1=first-delta;out[1].0=first-delta;
        let sizes:Vec<_>=out.iter().map(|&(lo,hi)|hi-lo).collect();
        let unchanged=old[1..old.len()-1].iter().zip(&out[1..out.len()-1]).all(|(&(a,b),&(x,y))|
            b==y && boundary_repair_spec(round,multiply,a,b)==boundary_repair_spec(round,multiply,x,y));
        if unchanged && layout_ladder(&sizes)<=room{return out;}
    }
    old.to_vec()
}

// A generated baseline table freezes the replay arithmetic independently of
// lifetime scheduling. Rows: round direction width followed by chunk lengths.
// Exact leading-boundary loans are applied before capture; when pinned, keep
// those boundaries too. Over-cap layouts remain visible in the actual peak.
fn pinned_replay_bounds(n:usize,round:usize,multiply:bool)->Option<Vec<(usize,usize)>> {
    type Table=std::collections::HashMap<(usize,bool),(usize,Vec<usize>)>;
    static TABLE:std::sync::OnceLock<Option<Table>>=std::sync::OnceLock::new();
    let table=TABLE.get_or_init(||env_raw("PP_PIN_REPLAY_LAYOUT").map(|path|{
        let data=std::fs::read_to_string(path).expect("read immutable replay layout");
        let mut table=Table::new();
        for line in data.lines().filter(|s|!s.trim().is_empty() && !s.starts_with('#')) {
            let values:Vec<usize>=line.split_whitespace().map(|s|s.parse().expect("numeric layout field")).collect();
            assert!(values.len()>=4 && values[1]<=1);
            assert!(values[3..].iter().all(|&w|w>0));
            assert_eq!(values[3..].iter().sum::<usize>(),values[2]);
            assert!(table.insert((values[0],values[1]!=0),(values[2],values[3..].to_vec())).is_none());
        }table
    }));
    table.as_ref().map(|t|{
        let(width,sizes)=t.get(&(round,multiply)).expect("pinned replay call is in baseline");
        assert_eq!(*width,n);to_bounds(sizes)
    })
}

// Preserve I03's choice of main-adder algorithm. A retained-frame receiver
// uses only ordinary chunk sites; exact/low-work fallbacks remain untouched.
fn composition_bounds(c:&Builder,round:usize,multiply:bool)->Option<Vec<(usize,usize)>> {
    if env_raw("PP_PIN_REPLAY_LAYOUT").is_some(){return None;}
    let room=walk_max_qubits().saturating_sub(c.active_qubits()as usize);
    let loans=REPLAY_SIGN_LOANS.with(|s|s.get());let old=room.saturating_sub(loans);
    let layout=chunk_layout(N,old);
    let fallback=layout.is_none() || old<replay_chunk_compare()+2;
    if env_flag("PP_NEW_REPLAY") {
        let extra=if fallback{2*N}else{layout.as_ref().unwrap()[..layout.as_ref().unwrap().len()-1]
            .iter().map(|&(lo,hi)|{
                let mut k=chunk_compare(round).min(hi-lo);
                let prior=multiply&&policy_width(round)>=38&&k<hi-lo
                    &&matches!(a5_policy(),"mul-b-seed"|"mul-fb-seed");
                if env_flag("CMP_SEED_ALL")&&!seed_keep_width_for(true)&&!prior&&k+1<hi-lo{k-=1;}
                k.saturating_sub(1)
            }).sum()};
        if super::width_composition::plan(N,old.max(2)).unwrap().extra2<extra{return None;}
    }
    if env_flag("PP_Q1208_HELPERS")&&fallback{return None;}
    let layout=layout?;
    Some(loaned_chunk_bounds(&layout,room,loans,round,multiply))
}

// Reserve final-frame room by filling spare earlier chunk capacity.
// No new boundary is introduced. Every surviving approximate comparison
// keeps its width and seed rule, but its absolute endpoint may move: this
// is an explicit phase-predicate change, requiring full-stream qualification.
fn retained_rebalance(c:&Builder, old:&[(usize,usize)], round:usize, multiply:bool)->Vec<(usize,usize)> {
    if !env_flag("PP_RETAIN_REBALANCE") || old.len()<2 {return old.to_vec();}
    let room=walk_max_qubits().saturating_sub(c.active_qubits()as usize);
    let mut sizes:Vec<_>=old.iter().map(|&(lo,hi)|hi-lo).collect();
    let last=sizes.len()-1;
    for j in 0..last {
        let (lo,hi)=old[j];
        if boundary_repair_spec(round,multiply,lo,hi)==(hi-lo,false) {continue;}
        let available=widest_chunk(j,room).saturating_sub(sizes[j]);
        let take=available.min(sizes[last].saturating_sub(2));
        sizes[j]+=take;sizes[last]-=take;
    }
    let new=to_bounds(&sizes);
    assert!(layout_ladder(&sizes)<=room);
    let same=old[..last].iter().zip(&new[..last]).all(|(&(a,b),&(x,y))|
        boundary_repair_spec(round,multiply,a,b)==boundary_repair_spec(round,multiply,x,y));
    if same {new} else {old.to_vec()}
}

fn chunked_add(circ: &mut Builder, addend: &[QubitId], acc: &[QubitId], round: usize, multiply: bool) -> QubitId {
    let ladder = walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
    let loans=REPLAY_SIGN_LOANS.with(|s|s.get());
    let old_ladder=ladder.saturating_sub(loans);
    let pinned=pinned_replay_bounds(addend.len(),round,multiply);
    let layout = pinned.clone().or_else(||chunk_layout(addend.len(), old_ladder));
    if pinned.is_none() && env_flag("PP_NEW_REPLAY") {
        let old_fallback=layout.is_none() || old_ladder<replay_chunk_compare()+2;
        let old_extra2=if old_fallback {2*addend.len()} else {
            let bounds=layout.as_ref().unwrap();
            bounds[..bounds.len()-1].iter().map(|(lo,hi)|{
                let mut k=chunk_compare(round).min(hi-lo);
                let prior=multiply && policy_width(round)>=38 && k<hi-lo
                    && matches!(a5_policy(),"mul-b-seed"|"mul-fb-seed");
                if env_flag("CMP_SEED_ALL") && !seed_keep_width_for(true) && !prior && k+1<hi-lo {k-=1;}
                k.saturating_sub(1)
            }).sum()
        };
        let candidate=super::width_composition::plan(addend.len(),old_ladder.max(2)).unwrap();
        if env_flag("PP_NEW_TRACE") {eprintln!("NEW_REPLAY {} {} {} {} {} {} {}",round,multiply as u8,circ.active_qubits(),ladder,old_fallback as u8,old_extra2,candidate.extra2);}
        if candidate.extra2<old_extra2 {
            let candidate=super::width_composition::plan(addend.len(),ladder.max(2)).unwrap();
            return super::width_composition::add(circ,addend,acc,&candidate);
        }
    }
    if pinned.is_none() && env_flag("PP_Q1208_HELPERS") && (layout.is_none() || old_ladder < replay_chunk_compare()+2) {
        return small_ladder_add(circ, addend, acc);
    }
    let bounds = layout.unwrap_or_else(|| panic!("layout r={} mul={} live={} cap={} room={}", round, multiply, circ.active_qubits(), walk_max_qubits(), ladder));
    let adjusted=if pinned.is_some(){
        if env_flag("PP_PIN_REPLAY_RELAX_EXACT") {loaned_chunk_bounds(&bounds,ladder,addend.len(),round,multiply)}else{bounds.clone()}
    }else{loaned_chunk_bounds(&bounds,ladder,loans,round,multiply)};
    if loans>0 && env_flag("PP_REPLAY_SIGN_TRACE") {
        eprintln!("REPLAY_LOAN_LAYOUT {} {} {} {} {:?} {:?}",round,multiply as u8,old_ladder,ladder,bounds,adjusted);
    }
    let bounds=adjusted;
    if env_flag("PP_CAPTURE_REPLAY_LAYOUT") {
        eprintln!("REPLAY_PIN {} {} {} {}",round,multiply as u8,addend.len(),bounds.iter().map(|(a,b)|(b-a).to_string()).collect::<Vec<_>>().join(" "));
    }

    let mut carry_in: Option<QubitId> = None;
    let mut previous: Option<(QubitId, usize, usize)> = None;

    for &(lo, hi) in &bounds {
        let room=walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
        let next=if pinned.is_some() && env_flag("PP_PIN_REPLAY_FIT") && hi-lo>room {
            let plan=super::width_composition::plan(hi-lo,room.max(2)).unwrap();
            if env_flag("PP_CAPTURE_REPLAY_LAYOUT") {eprintln!("REPLAY_PIN_FIT {} {} {} {} {}",round,multiply as u8,hi-lo,room,plan.extra2);}
            super::width_composition::add_with_carry(circ,&addend[lo..hi],&acc[lo..hi],carry_in,&plan)
        }else{
            let next=circ.alloc_qubit();
            ripple_add(circ,&addend[lo..hi],&acc[lo..hi],carry_in,Some(next));next
        };
        // Erase the previous chunk's carry as soon as it has been consumed.
        if let Some((carry, plo, phi)) = previous {
            let(compare,seeded)=boundary_repair_spec(round,multiply,plo,phi);
            let borrow = if seeded {
                Some(addend[phi - compare - 1])
            } else { None };
            // Freeze the OLD predictor identity before widening the window.
            // The comparator supports that source wire as an interior alias.
            let compare=if seeded{refined_seeded_width(compare,phi-plo,"PP_REFINE_SEEDED_B")}else{compare};
            circ.record_replay_site('B', round, phi, compare);
            trace_replay_predictor('B',round,multiply,phi,compare,addend,borrow);
            let window = phi - compare..phi;
            erase_with_compare(circ, carry, &acc[window.clone()], &addend[window], borrow);
            circ.free(carry);
        }
        carry_in = Some(next);
        previous = Some((next, lo, hi));
    }

    carry_in.expect("bounds is non-empty")
}

// â”€â”€â”€ The replay's fused correction fold â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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
/// two's complement of `f` has one.  A single roving wire â€” the first selector,
/// or the incoming carry when there is none â€” carries that XOR for the length of
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
    // Search-only selective deployment: pay for the dropped low32 carry only
    // at receiving sites where the ordinary fold's ladder exceeds this
    // public headroom threshold. This is still approximate at selected sites.
    if let Some(g)=joint_lowfold::GUARD.with(|s|s.get()) {
        return joint_lowfold::fold(circ,acc,f,plus_f,plus_2f,minus_f,first_carry,g);
    }
    let overage = (circ.active_qubits() as usize + acc.len().saturating_sub(3)) as isize
        - walk_max_qubits() as isize;
    let selected = split_fold() && env_raw("PP_SPLIT_FOLD_OVERAGE")
        .and_then(|v| v.parse::<isize>().ok()).is_none_or(|limit| overage > limit);
    if env_flag("PP_SPLIT_CHOICE_TRACE") {
        eprintln!("SPLIT_CHOICE {} {} {} {}", acc.len(), circ.active_qubits(), overage, selected as u8);
    }
    if selected {
        return fold_selected_split(circ, acc, f, plus_f, plus_2f, minus_f, first_carry);
    }
    fold_selected_single(circ, acc, f, plus_f, plus_2f, minus_f, first_carry)
}

/// The single-ladder fold: one ripple over the whole window. This is the
/// pre-split construction, and also the building block the split calls twice
/// -- the inner calls must NOT re-enter the gate.
pub(crate) fn fold_selected_single(
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

    if env_flag("PP_DIRECT_FOLD") && circ.active_qubits() as usize+width.saturating_sub(3)>walk_max_qubits() {
        let n=width-1;let room=walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
        let p=(room..=n.max(room)).find_map(|r|super::width_composition::direct_plan(n,r)).unwrap();
        if env_flag("PP_NEW_TRACE"){eprintln!("DIRECT_FOLD {} {} {} {} {}",width,circ.active_qubits(),room,p.peak,p.extra2);}
        for control in selectors(0){circ.cx(control,acc[0]);}
        let map:Vec<_>=(1..width).map(selectors).collect();
        super::width_composition::direct_add(circ,&map,&acc[1..],first_carry,&p);
        return;
    }
    if env_flag("PP_NEW_FOLD") && circ.active_qubits() as usize+width.saturating_sub(3)>walk_max_qubits() {
        let n=width-1;let room=walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
        let chunk=(1..=n).min_by_key(|&chunk|{
            let peak=super::width_composition::mapped_peak(n,chunk);
            (peak.saturating_sub(room),super::width_composition::mapped_extra2(n,chunk),peak)
        }).unwrap();
        if env_flag("PP_NEW_TRACE"){eprintln!("NEW_FOLD {} {} {} {} {} {}",width,circ.active_qubits(),room,chunk,super::width_composition::mapped_peak(n,chunk),super::width_composition::mapped_extra2(n,chunk));}
        for control in selectors(0){circ.cx(control,acc[0]);}
        let map:Vec<_>=(1..width).map(selectors).collect();
        super::width_composition::mapped_add(circ,&map,&acc[1..],first_carry,chunk);
        return;
    }

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

/// The bit position the split fold divides the window at: the `2^32` term of
/// `f = 2^32 + 977` goes to the high ripple, the `977` stays in the low one.
const FOLD_SPLIT_BIT: usize = 32;

/// [`fold_selected`] as two sequential ripples, gated by [`split_fold`]:
/// `k*977` into bits `0..FOLD_SPLIT_BIT` (mod `2^32`), then `k` into bits
/// `FOLD_SPLIT_BIT..`.
///
/// The low block's wrap/borrow into bit 32 is DELIBERATELY omitted -- the one
/// place this differs from the single-ladder fold. When the low word `z`
/// satisfies `z + 977*k >= 2^32` (k > 0) or `z < 977*|k|` (k < 0) the true
/// fold carries or borrows across the split and this result is off by `2^32`;
/// the per-cell rate is `~977*E|k| / 2^32`.
///
/// Both halves are the ordinary fold with a smaller constant, so the selector
/// identities fall out of the existing machinery. The high half runs with the
/// constant 1, whose two's complement is all ones: bit 0's addend is
/// `plus_f ^ minus_f`, bit 1's is `plus_2f ^ minus_f`, and every later bit's
/// is `minus_f`. The low half runs with 977, whose bits 0..32 are `f`'s own,
/// so the caller's `first_carry` (bit 0's carry-out) is unchanged.
///
/// Cost against the single ladder: `(32 - 2) + (width - 32 - 2)` ripple
/// Toffoli plus one for the high block's first carry -- which the unsplit
/// form receives from its caller -- against `width - 2`, i.e. one Toffoli
/// cheaper per cell, and the deepest live ladder is `32 - 3` carries rather
/// than `width - 3`, which is what the binding trailing-batch cells feel.
fn fold_selected_split(
    circ: &mut Builder,
    acc: &[QubitId],
    f: U256,
    plus_f: QubitId,
    plus_2f: Option<QubitId>,
    minus_f: QubitId,
    first_carry: QubitId,
) {
    let width = acc.len();
    // The high block must be wide enough to hold a ladder at all, with margin.
    assert!(width >= 36, "split fold needs a window of at least 36 bits");
    let f_low = f & ((U256::from(1) << FOLD_SPLIT_BIT).wrapping_sub(U256::from(1)));
    assert_eq!(
        f >> FOLD_SPLIT_BIT,
        U256::from(1),
        "split fold assumes f = 2^32 + 977"
    );

    // Keep the 977 correction for additional low bits, overlapping the high
    // +k*2^32 update. Its modulus becomes 2^(32+extra); the high update still
    // starts at bit32 and f_low is still 977 (never include the 2^32 term twice).
    // No new register or retained carry. For valid k in {-1,0,1,2}, escape
    // from a wider low window implies escape from the original 32-bit window.
    let extra=super::optional_env::<usize>("PP_SPLIT_OVERLAP_BITS").unwrap_or(0);
    assert!(extra<=8,"bounded overlap precision experiment");
    let low_width=(FOLD_SPLIT_BIT+extra).min(width);

    // Low block: k*977 mod 2^low_width. Bit 0's addend is the same as the unsplit
    // fold's, so the caller-prepared carry into bit 1 serves unchanged. The
    // carry off bit 31 -- the wrap into bit 32 -- is dropped: that drop is
    // the approximation.
    fold_selected_single(
        circ,
        &acc[..low_width],
        f_low,
        plus_f,
        plus_2f,
        minus_f,
        first_carry,
    );

    // High block: k mod 2^(width - 32). The carry out of its bit 0,
    // `acc[32] AND (plus_f ^ minus_f)`, has no caller-prepared wire, so it is
    // computed here -- the one Toffoli the split pays back -- and erased with
    // the restore/uncompute/re-apply discipline `replay_double_add` uses on
    // its own `first_carry`.
    let boundary = circ.alloc_qubit();
    with_selector_xor(circ, &[plus_f, minus_f], plus_f, |circ, operand| {
        circ.ccx(acc[FOLD_SPLIT_BIT], operand, boundary);
    });
    fold_selected_single(
        circ,
        &acc[FOLD_SPLIT_BIT..],
        U256::from(1),
        plus_f,
        plus_2f,
        minus_f,
        boundary,
    );
    with_selector_xor(circ, &[plus_f, minus_f], plus_f, |circ, operand| {
        // The fold left `acc[32] ^ operand` in `acc[32]`; uncomputing the AND
        // needs its compute-time operands back.
        circ.cx(operand, acc[FOLD_SPLIT_BIT]);
        and_uncompute(circ, boundary, acc[FOLD_SPLIT_BIT], operand);
        circ.cx(operand, acc[FOLD_SPLIT_BIT]);
    });
}

/// One [`fold_selected`] ripple stage: `carry = MAJ(acc, addend, previous)` with
/// the incoming carry applied to `acc` and left there â€” the sum bits are finished
/// in [`unwind_fold_step`].
///
/// `sel` is the (possibly empty) selector set whose XOR is this position's addend
/// bit; with no selectors the addend bit is zero and `previous` itself stands in
/// as the gate operand, since `MAJ(a, 0, c) = a & c`.  `apply_addend` finishes
/// this position's sum bit here instead, for the terminal stage that has no
/// unwind pass.
pub(crate) fn fold_step(
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

pub(crate) fn unwind_fold_step(
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
pub(crate) fn with_selector_xor(
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

// â”€â”€â”€ Modular primitives for rounds 0 and 1 of the replay â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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
    let chunk = super::required_env::<usize>("PP_CF_END_CHUNK");
    if chunk == 0 {
        csub_const_trunc(circ, &value[..f_slice()], f_minus_one(), control);
    } else {
        endpoint_sparse_sub(circ, control, value, chunk);
    }
}

// â”€â”€â”€ Small shared helpers â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€â”€

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

fn small_ladder_add(circ: &mut Builder, addend: &[QubitId], acc: &[QubitId]) -> QubitId {
    assert_eq!(addend.len(), acc.len());
    assert!(!acc.is_empty());
    let z = circ.alloc_qubit();
    let out = circ.alloc_qubit();
    for i in 0..acc.len() {
        let prev = if i == 0 { z } else { addend[i - 1] };
        circ.cx(addend[i], acc[i]);
        circ.cx(addend[i], prev);
        circ.ccx(prev, acc[i], addend[i]);
    }
    circ.cx(addend[acc.len()-1], out);
    for i in (0..acc.len()).rev() {
        let prev = if i == 0 { z } else { addend[i - 1] };
        circ.ccx(prev, acc[i], addend[i]);
        circ.cx(addend[i], prev);
        circ.cx(prev, acc[i]);
    }
    circ.release_clean(z);
    out
}
fn exact_walk_chunk_width(width: usize, room: usize) -> usize {
    let extra = |c: usize| width.div_ceil(c).saturating_sub(1) + c.saturating_sub(1);
    (1..=width).filter(|&c| extra(c) <= room).max()
        .unwrap_or_else(|| (1..=width).min_by_key(|&c| extra(c)).unwrap())
}

// Exact replacement of the parent finite-window subtraction. The four low
// zero constant bits and the parent's dropped top carry are unchanged.
pub(crate) fn endpoint_sparse_sub(circ: &mut Builder, control: QubitId, value: &[QubitId], chunk: usize) {
    let constant = f_minus_one();
    if env_flag("PP_DIRECT_ENDPOINT") {
        let target=&value[4..f_slice()];
        let source:Vec<Vec<QubitId>>=(4..f_slice()).map(|i|if constant.bit(i){vec![control]}else{vec![]}).collect();
        let zero=circ.alloc_qubit();
        let room=walk_max_qubits().saturating_sub(circ.active_qubits() as usize);
        let p=(room..=source.len().max(room)).find_map(|r|super::width_composition::direct_plan(source.len(),r)).unwrap();
        if env_flag("PP_NEW_TRACE"){eprintln!("DIRECT_ENDPOINT {} {} {} {} {}",target.len(),circ.active_qubits(),room,p.peak,p.extra2);}
        circ.x_all(target);super::width_composition::direct_add(circ,&source,target,zero,&p);circ.x_all(target);
        circ.release_clean(zero);return;
    }
    let map: Vec<super::compact_mapped_add::SourceBit> = (4..f_slice())
        .map(|i| (if constant.bit(i) {Some(control)} else {None}, false)).collect();
    super::compact_mapped_add::add(circ, &map, &value[4..f_slice()], true, chunk);
}

#[path="joint_lowfold.rs"] mod joint_lowfold;
#[path="joint_prebias.rs"] mod joint_prebias;
#[path="retained_prebias.rs"] mod retained_prebias;
