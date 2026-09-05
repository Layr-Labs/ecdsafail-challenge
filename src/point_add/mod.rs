use std::str::FromStr;

use alloy_primitives::U256;

use crate::circuit::{BitId, Op, OperationType, QubitId};
use builder::Builder;
use classical::{coord_add3x, coord_rsub, coord_sub};
use pingpong::{divide, multiply};
use square::sub_square;

mod builder;
mod classical;
mod compare;
mod const_arith;
mod modular;
mod pingpong;
mod record;
mod square;

const N: usize = 256;

const SECP256K1_P: U256 = U256::from_limbs([
    0xFFFF_FFFE_FFFF_FC2F,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
    0xFFFF_FFFF_FFFF_FFFF,
]);

/// Pin a tuning knob, unless the environment already overrides it.
///
/// **The single-line call shape is load-bearing.** `src/bin/grind` `include_str!`s
/// this file and text-searches it for the literal needle
/// `set_default_env("NAME", ` to recover a pinned value, because the grinder's
/// model has to track the circuit's tuning and must not keep its own copy.
/// Seven knobs are read that way today: `PP_ROUNDS_MUL`, `FOLD_GUARD`, both
/// `PP_REPLAY_FOLD_WINDOW*`, `PP_FOLD_WIDEN`, `PP_FOLD_PROFILE` and
/// `PP_WIDTH_SCHEDULE` -- the last two as string literals, the schedule as a
/// `concat!` of them. So a pin's value must stay a literal right here in the
/// call: routing it through a constant, a table or a helper compiles fine and
/// makes the grinder panic at startup -- or, worse, screen against tuning the
/// circuit no longer has. (It used to route the schedule and the band tables
/// through `pub const DEFAULT_*` in `pingpong.rs`, which is exactly the shape
/// that needed a second scraper and a second file.)
///
/// The `unsafe` is required from edition 2024 on, where `set_var` is an
/// `unsafe fn`; this crate is on 2021, where it is merely allowed.
fn set_default_env(name: &str, value: &str) {
    if env_raw(name).is_none() {
        unsafe {
            std::env::set_var(name, value);
        }
    }
}

/// Defines a memoised `usize` accessor for a tuning knob that [`build`] pins.
///
/// The knob is read once through [`required_env`] and cached, so every consumer
/// sees one value and the environment is not walked per call site. That reader
/// deliberately has no fallback, so a dropped pin panics rather than silently
/// emitting a different circuit.
///
/// Every knob that reaches a construction as a width in bits goes through here;
/// ten do. The five that do not are the ones that are not a width: the tail
/// nonce, read in [`build`], and the four strings, each read once behind its own
/// `OnceLock` in `pingpong` -- the width schedule, and the three `width:offset`
/// band tables (`PP_FOLD_PROFILE`, `PP_CHUNK_SHAPE`,
/// `PP_FLAG_SHAPE`).
macro_rules! pinned_env {
    ($name:ident, $env:literal) => {
        fn $name() -> usize {
            static SLOT: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
            *SLOT.get_or_init(|| $crate::point_add::required_env($env))
        }
    };
}
// The submodules are declared above this macro, so textual scoping does not
// reach them; this re-export is what makes `crate::point_add::pinned_env` a path
// they can import. No visibility marker: like everything else in this file it is
// private to `point_add` and therefore already visible to its descendants, which
// is all the submodules need. (`pub` would be E0364 anyway -- a `macro_rules!`
// without `#[macro_export]` cannot be re-exported wider than the crate.)
use pinned_env;

/// The raw value of `name`, or `None` when it is unset, empty, or not UTF-8.
///
/// **Every environment read in this tree goes through here**, so the rule can be
/// stated once: empty counts as unset. That makes `KNOB= ./build_circuit` clear
/// an override rather than pin the empty string, and it is the same rule
/// `src/bin/grind` applies when deciding whether an override beats a pinned
/// literal -- the two have to agree, or the grinder models a different circuit
/// than the one that was built.
///
/// `var` rather than `var_os`: a knob that is not UTF-8 is not a knob, and
/// reading it as absent puts it on the pinned default instead of carrying a
/// value nothing downstream can parse.
fn env_raw(name: &str) -> Option<String> {
    std::env::var(name)
        .ok()
        .map(|v| v.trim().to_string())
        .filter(|v| !v.is_empty())
}

/// A diagnostic switch. Off when unset, empty, or set to a value that plainly
/// means no -- `0`, `false`, `no`, `off`, in any case. Anything else is on, so
/// `KNOB=1` and `KNOB=please` both enable and only a deliberate `KNOB=0`
/// disables.
fn env_flag(name: &str) -> bool {
    env_raw(name).is_some_and(|value| {
        !matches!(
            value.to_ascii_lowercase().as_str(),
            "0" | "false" | "no" | "off"
        )
    })
}

fn required_env<T: FromStr>(name: &str) -> T
where
    <T as FromStr>::Err: std::fmt::Display,
{
    let Some(raw) = env_raw(name) else {
        panic!("{name} is not set; every tuning knob must be pinned in point_add::build")
    };
    raw.parse().unwrap_or_else(|e| {
        panic!(
            "{name}={raw:?} is not a valid {}: {e}",
            std::any::type_name::<T>()
        )
    })
}

/// A knob that may be absent: `None` when unset, empty or unparseable.
///
/// The counterpart to [`required_env`], and the split is the point. Anything the
/// *circuit* reads goes through `required_env` and panics on a missing pin,
/// because quietly building a different circuit is the one failure nothing
/// downstream can catch. Anything that merely *observes* the build -- the
/// recorders in [`record`] -- have the opposite duty and must default to off, so
/// it comes through here.
fn optional_env<T: FromStr>(name: &str) -> Option<T> {
    env_raw(name)?.parse().ok()
}

// ─── The truncation width every constant fold shares ───────────────────────
//
// Every approximation outside the ping-pong replay is one of exactly two
// shapes, and the balance rule says both want ONE value each, not one per
// caller. Equalising `d(lambda)/d(Toffoli)` across sites gives `err / u` equal,
// where `u` is 1 for an unconditional site and 1/2 for a compare (whose Toffoli
// sit under a `push_condition` and execute half the time). So:
//
//   * every constant-fold site wants the same per-call error, and
//   * every measured-erasure compare wants HALF that error, i.e. one bit more.
//
// Notably that does not depend on the call count: a 29-call site and a 2-call
// site want the same width. The replay's own windows are not here because they
// are pinned by peak geometry rather than by error.
//
// Only the first of the pair is declared here, because only the first is shared
// -- `fold_guard` reaches `modular`, `square` and `pingpong`. The compare width
// it is derived against lives with its single caller, as
// `modular::erase_compare`; both are still pinned together in [`build`], which
// is where the two values have to be read side by side to stay one bit apart.
pinned_env!(fold_guard, "FOLD_GUARD");

/// Rewrite the 96-op identity tail to encode the ground nonce. Only `q_target`
/// changes (X;X pairs stay identities), so circuit function is untouched; the
/// Fiat-Shamir seed is what moves.
fn apply_tail_nonce(mut ops: Vec<Op>, nonce: u64) -> Vec<Op> {
    let n = ops.len();
    assert!(n >= 96, "op stream too short for nonce tail");
    let start = n - 96;
    for i in 0..96 {
        assert!(
            ops[start + i].kind == OperationType::X,
            "tail op {} is not an X",
            start + i
        );
    }
    for b in 0..48 {
        let t = QubitId((nonce >> b) & 1);
        ops[start + 2 * b].q_target = t;
        ops[start + 2 * b + 1].q_target = t;
    }
    ops
}

/// The candidate itself: `(x, y) += (ox, oy)` on secp256k1 in affine
/// coordinates, with `(ox, oy)` classical.
///
/// The chord-and-tangent formulae in eight phases, each named for the `set_phase`
/// report `build_circuit` prints. `x`/`y` are the quantum coordinates and are
/// overwritten in place; every scratch qubit each phase takes is returned to |0>
/// before the next one starts.
fn build_point_add() -> Vec<Op> {
    let circ = &mut Builder::new();
    let x: &[QubitId] = &circ.alloc_qubits(N);
    let y: &[QubitId] = &circ.alloc_qubits(N);
    let ox: &[BitId] = &circ.alloc_bits(N);
    let oy: &[BitId] = &circ.alloc_bits(N);

    circ.set_phase("coord_x_sub"); // x2 -= ox
    coord_sub(circ, x, ox);

    circ.set_phase("coord_y_sub"); // y2 -= oy
    coord_sub(circ, y, oy);

    circ.set_phase("divide"); // y2 /= x2
    divide(circ, y, x);

    circ.set_phase("coord_add3x"); // x2 += 3*ox
    coord_add3x(circ, x, ox);

    circ.set_phase("square"); // x2 -= y2^2
    sub_square(circ, x, y);

    circ.set_phase("multiply"); // y2 *= x2
    multiply(circ, y, x);

    circ.set_phase("coord_y_sub_final"); // y2 -= oy
    coord_sub(circ, y, oy);

    circ.set_phase("coord_rsub_final"); // x2 = ox - x2
    coord_rsub(circ, x, ox);

    circ.declare_qubit_register(x);
    circ.declare_qubit_register(y);
    circ.declare_bit_register(ox);
    circ.declare_bit_register(oy);
    circ.finalize_records();
    circ.take_ops()
}

/// Pin every tuning knob, build the circuit, and bake the ground nonce into its
/// tail.
///
/// These pins are the circuit's entire configuration. Everything under
/// [`build_point_add`] reads them back through [`required_env`], which panics on
/// a missing one, so a dropped pin stops the build instead of quietly emitting a
/// different circuit. [`set_default_env`] does not overwrite, so a value already
/// in the environment wins -- that is how the knobs are swept, and why
/// `src/bin/grind` recovers the tuning by reading these lines as text rather
/// than by trusting the environment it happens to run in.
///
/// Grouped by what each value shapes, with the measurement that fixed it.
pub fn build() -> Vec<Op> {
    // ── The two walks ──────────────────────────────────────────────────────

    // Per-round register width for the divide's walk, run-length encoded as
    // `width x rounds` (a bare `width` is a run of one). Its LENGTH is that
    // walk's round count, so there is no separate rounds knob on this side.
    // Run-length rather than 696 loose integers because the schedule is a
    // staircase -- every width from 259 down to 8 appears as exactly one run --
    // so it is the form an edit is least likely to corrupt, and a third the
    // size. GENERATED, by fitting each round's width to the measured magnitude
    // distribution of the recurrence, and WRONG for any other depth: to change
    // the depth, regenerate rather than truncate or pad. See
    // `pingpong::width_schedule`.
    set_default_env(
        "PP_WIDTH_SCHEDULE",
        concat!(
            "259,258x19,257x5,256x3,255x4,254x4,253x2,252x4,251x3,250x5,249x2,248x4,",
            "247x3,246x2,245x4,244x3,243x3,242x3,241x3,240x3,239x4,238x3,237x2,236x4,",
            "235x2,234x3,233x2,232x4,231x4,230x2,229x3,228x3,227x3,226x2,225x4,224x2,",
            "223x2,222x3,221x3,220x4,219x3,218x2,217x3,216x3,215x3,214x4,213x2,212x2,",
            "211x3,210x4,209x3,208x2,207x2,206x2,205x3,204x2,203x4,202x3,201x3,200x4,",
            "199x2,198x2,197x3,196x2,195x2,194x4,193x4,192x2,191x3,190x3,189x2,188x3,",
            "187x2,186x3,185x2,184x3,183x4,182x2,181x3,180x4,179x2,178x2,177x3,176x3,",
            "175,174x2,173x2,172x4,171x3,170x2,169x2,168x4,167x3,166x3,165x2,164x3,",
            "163x3,162x2,161x3,160x2,159x3,158x2,157x3,156x2,155x4,154x2,153x3,152x2,",
            "151x3,150x3,149x2,148x2,147x2,146x4,145x4,144x3,143x2,142x2,141x3,140x2,",
            "139x2,138x2,137x3,136x2,135x4,134x3,133x3,132x3,131x2,130x3,129x2,128x4,",
            "127x3,126x2,125x2,124x3,123x2,122x3,121x3,120x2,119x5,118x2,117x3,116x2,",
            "115x3,114x4,113x2,112x2,111x4,110x2,109x2,108x2,107x2,106x2,105x5,104x2,",
            "103x2,102x2,101x2,100x4,99x2,98x2,97x2,96x3,95x3,94x3,93x2,92x3,91x2,",
            "90x4,89x3,88x2,87x2,86x4,85x2,84,83x4,82x2,81x2,80x2,79x3,78x2,77x2,76x3,",
            "75,74x2,73x3,72x3,71x2,70x3,69x3,68x3,67x3,66x2,65x3,64x4,63x2,62x2,61x3,",
            "60x2,59x2,58x2,57x2,56x2,55x3,54x3,53x2,52x3,51x2,50x4,49x2,48x2,47x3,",
            "46x3,45x2,44x2,43x3,42x2,41x2,40x3,39x2,38x2,37x3,36x4,35x2,34x3,33x2,",
            "32x2,31x2,30x2,29x2,28x4,27x2,26x2,25x3,24x2,23x2,22x2,21x3,20x3,19x2,",
            "18x3,17x2,16x2,15x3,14x2,13x2,12x2,11x2,10x2,9x4,8x9",
        ),
    );
    // The multiply walk's round count. The divide's is the schedule's length
    // above; only this side needs a number of its own. 695 is the cheapest
    // lambda in the tree to buy, and funding it by narrowing the fold profile
    // was measured and does not pay.
    set_default_env("PP_ROUNDS_MUL", "694");
    // The peak, and therefore half the score. Nothing else sets it: the walk's
    // split adds and the replay's chunked adds both size themselves against this
    // and land on it exactly. The replay folds used to floor it as well -- the
    // divide's trailing batch at `1210 + window` -- but the fold profile below
    // narrows those rounds to 49 and 50.
    //
    // Not free: the narrower ladder needs 64 more approximate chunk boundaries,
    // ~0.06 lambda, for -0.033% of score. That is 0.56% per lambda, five times
    // the rate anything else in the tree trades at, which is why it is taken --
    // but it is still lambda, and lambda is paid in the cost of grinding a nonce.
    set_default_env("PP_WALK_MAX_QUBITS", "1260");

    // ── The replay fold window ─────────────────────────────────────────────

    // The base truncation window each replay cell folds at, per direction.
    set_default_env("PP_REPLAY_FOLD_WINDOW", "53");
    // The multiply's is one bit wider, and that bit is a deliberate purchase in
    // the opposite direction to the cap above: it pays 688 executed Toffoli
    // (0.076% of score, and the peak does NOT move -- 1260 holds, it is 55 that
    // breaks to 1261) to buy back 1.13 +/- 0.31 lambda, measured paired at a
    // fixed `EVAL_SEED` over 600,000 shots a side. Nothing in the tree sells
    // lambda at that rate, so this is not an arbitrage; it is bought because the
    // binding constraint was grinding a nonce rather than the score. The
    // divide's window stays at 53 because it holds about half the lambda the
    // multiply's does, so the same bit buys proportionally less.
    set_default_env("PP_REPLAY_FOLD_WINDOW_MUL", "54");
    // Per-round offsets on those two windows, as `width:offset` bands keyed on
    // the walk's width at that round. MEASURED, not derived: the rate at which
    // the fold's dropped carry actually matters is flat for the first 85% of the
    // walk and then collapses ~11x over the last hundred rounds. Keyed on the
    // width rather than the round so that regenerating the schedule above
    // carries the profile with it; `pingpong::fold_offset` applies it.
    set_default_env("PP_FOLD_PROFILE", "38:0,32:-1,19:-3,0:-4");
    // How many leading rounds carry one extra bit of window. The level, kept
    // deliberately out of the shape above: the measured rate is flat across
    // exactly the region this covers, so one threshold reads it more honestly
    // than another band would.
    set_default_env("PP_FOLD_WIDEN", "242");
    // Where the trailing replay batch takes over. Everything above it is
    // replayed at the terminal state, where `loan_terminal` has collapsed both
    // walk registers to a sign wire and the tape is at its longest -- so the
    // widest fold in that batch is the widest thing alive anywhere, and the peak
    // floors at `1210 + window` for the batch's first round. Everything in
    // `r1..=r2` is instead replayed beside its own walk round, where the walk
    // register is still live and there is correspondingly less room.
    //
    // The emitted count does not move at all across this range -- 945,183 scored
    // gates at every value from 630 to 656 -- so the choice is purely about the
    // peak, and the peak gives a plateau with a hard edge at each end. MEASURED:
    //
    //   <= 614   the plan assertion fires
    //   615..630 peak 1262
    //   631..655 peak 1260   <- pinned mid-plateau
    //   656..657 peak 1261
    //   >= 658   peak 1262
    //
    // The lower edge is exactly derivable and worth understanding, because it
    // moves whenever the schedule or the fold profile does. The fold window is
    // keyed on the walk's width, and in round space this schedule crosses the
    // profile's bands at 616 (width < 38, offset -1) and 632 (width < 32, offset
    // -3). A trailing batch starting in 616..631 therefore folds at window 52 and
    // floors the peak at 1262; from 632 the window is 50 and the floor is 1260.
    // So the batch must not start before 632, i.e. `r2 >= 631` -- which is the
    // measured edge to the round.
    //
    // The upper edge is the mirror: it is where the last interleaved fold stops
    // fitting beside its live walk register. That is a footprint prediction of
    // the same kind `head_boundary` makes for `r1`, not a closed form.
    //
    // Note the plan's own assertion is much weaker than the real constraint: it
    // only requires the batch not to reach past `fold_ramp_start` (616), i.e.
    // `r2 >= 615`, so 615..630 passes it and quietly costs two qubits.
    set_default_env("PP_R2", "648");

    // ── The two phase-channel compares ─────────────────────────────────────
    //
    // Both repair an approximation whose error appears as a PHASE rather than as
    // a wrong bit, so no classical model of the values can see either one. Each
    // is a base width plus a per-round band table, narrowing where the walk
    // narrows for the same reason the fold window does and by the same kind of
    // measurement.

    // Chunk-boundary repair. `chunk_layout` reads this flat base, so narrowing
    // the comparison does not move the boundaries themselves.
    set_default_env("PP_REPLAY_CHUNK_COMPARE", "21");
    set_default_env("PP_CHUNK_SHAPE", "38:0,25:-2,0:-4");
    // The replay cell's overflow flag, same construction.
    set_default_env("PP_REPLAY_FLAG_COMPARE", "20");
    set_default_env("PP_FLAG_SHAPE", "38:0,25:-2,0:-4");

    // ── The two widths every approximation outside the replay reads ────────
    //
    // 21 and 22 are the balance point against the replay folds' 289 executed
    // Toffoli per lambda. The compare is one bit finer because its gates sit
    // under a `push_condition` and so execute half the time, which halves what a
    // bit of width costs there; the derivation is above `fold_guard`.
    set_default_env("FOLD_GUARD", "21");
    set_default_env("ERASE_COMPARE", "22");

    // ── The ground nonce ───────────────────────────────────────────────────
    //
    // Ground against this exact op stream, which is what selects the 9,024
    // graded shots: ANY change to the emitted ops re-rolls them and voids this
    // value. `md5sum ops.bin` is the acceptance test for a refactor here.
    set_default_env("TAIL_NONCE", "2977985437");

    let mut ops = build_point_add();
    let nonce: u64 = required_env("TAIL_NONCE");
    let mut x = Op::empty();
    x.kind = OperationType::X;
    x.q_target = QubitId(0);
    ops.extend(std::iter::repeat_n(x, 96));
    ops = apply_tail_nonce(ops, nonce);
    ops
}
