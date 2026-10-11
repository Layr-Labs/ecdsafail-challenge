//! LEAPFROG GCD walk (research build, flag-gated by `LEAPFROG=1`).
//!
//! Rails R[0], R[1] are odd integers (two's complement, LSB first). Seed: R[0] = d (or d + p when d is even,
//! taking over the denominator's wires), R[1] = p. Tick t updates the TARGET R[t % 2] from the SOURCE
//! R[1 - t % 2] (roles alternate on a fixed schedule: no data-dependent payload route):
//!   * three forced ping-pong steps  T <- (T + s_i B) / 2,  s_i = +1 iff T[1] == B[1]  (keeps T odd; Clifford),
//!   * a fourth step with the deep/flat choice: the two candidates (T +- B) are even and exactly one is
//!     == 0 mod 4 ("deep"); v0 takes the deep one when v2(deep) <= 4 (admissible), else the flat one,
//!   * the extra trailing zeros e = v2(T) in [0,3] are stripped by a 2-stage barrel (k1 = e & 1, k2 = e >> 1).
//! Letter per tick: (s0, s1, s2, s3, k1, k2), six raw qubits on the tape.
//! Payload P[i] = lambda * R[i] (mod p): the same four add-halve steps (the head's replay cells) and a
//! controlled modular 2^-e. Division seed P = (y, 0); at park R = (+-1, +-1) and P = (+-lambda, +-lambda).
//! Reference model and envelope: scratchpad walksim/lf_ref.py, lf_env.py.
use super::builder::Builder;
use super::const_arith::{add_const, cadd_const_trunc, csub_const_trunc, sub_const};
use super::heo::gidney_add;
use super::modular::{f, go_fs, mod_addsub};
use super::pingpong::heo_hooks as cells;
use super::N;
use crate::circuit::{QubitId, NO_BIT};
use std::sync::OnceLock;

pub fn enabled() -> bool {
    std::env::var("LEAPFROG").is_ok_and(|v| v == "1")
}

/// Submission recipe, installed by `build()` on top of the Skywalk recipe (which still configures the shared
/// replay cells, coordinate ops and square): Leapfrog m = 2, sign2 + window choice, fast rails, seed-half, walk
/// cap 1237;
/// the square's B fold stays plain (NATIVE_SFUSE_B=1) and the Skywalk back seam is off (both fuse into its walk).
pub(crate) fn install_recipe() {
    for (k, v) in [
        ("LEAPFROG", "1"),
        ("LEAPFROG_M", "2"),
        ("LF_FAST", "1"),
        ("LF_SEED", "half"),
        // window choice rule: in the equal-sign cases that the low bits do not settle, a compare of the two rails on a
        // window of their top bits decides between deep and flat
        ("LF_W1", "1"),
        // ... in this form on every tick but the first and the last: a 21-bit window, deep or flat by the compare
        // [|T| > 2|B|] and by what the second forced step did (added, subtracted, or subtracted with a sign flip);
        // computed inside that step's rail add, while its carries are on wires. It has its own 138-tick width table
        // and window anchors (see `steps`, `w1_anchor`)
        ("LF_YP8", "21"),
        // ... with a shorter window on the late ticks: 19 bits from tick 90, 17 from 100, 15 from 112, 13 from 118,
        // 11 from 124
        ("LF_YP8_LATE", "90:19,100:17,112:15,118:13,124:11"),
        // tick 0's letter is not held on the tape while a walk sits at the cap: it is measured away after its last
        // read and derived again from the source rail at the walk's end, where the measurement's phase is fixed
        ("LF_T0_FREE", "1"),
        // the last tick has no forced steps: its choice step and shift only (a 3-bit letter)
        ("LF_TAIL_FORCED", "0"),
        // rails held at their already-implied widths through the payload ops
        ("LF_TRIM", "1"),
        // last add-halve cell + payload barrel as one merged Montgomery-style op on the ticks where it fits
        ("LF_MERGED", "1"),
        // ... also on the late ticks (split fold where room is short)
        ("LF_MERGED_LATE", "1"),
        // merged-op fold windows: standard 56 bits; late 58, capped by the standard window.
        // G6 (Track G gate, λ est+2SE <= 19.5): 54 -> 56 is the λ buy-back, +640 T for -0.97 classical failures
        // (paired, CRN); the master/#1 recipe has 54
        ("LF_MERGED_WIN", "56"),
        ("LF_MERGED_LATE_WIN", "58"),
        // ticks 0..77 of the payload-fused traversals split into a rails-only pass (one payload register live: no
        // room-split rail adds) and a payload-only pass over the taped letters (-5.9k T)
        ("LF_REORDER", "76"),
        // y15-room: the divide's and the multiply's boundary set apart (each overrides LF_REORDER for its direction)
        ("LF_REORDER_DIV", "42"),
        ("LF_REORDER_MUL", "77"),
        // spookyfrog: N1 split-carry phase deferral, N2 tail batch with a terminal sign-copy loan, RT0 + T0 one boundary
        ("SL_N2", "2"),
        ("SL_N2_DROP", "all"),
        ("SL_DEFER_T0", "3"),
        ("SL_DEFER_SQ", "1"),
        // spookyfrog: N1 split-carry phase deferral, N2 tail batch with a terminal sign-copy loan, RT0 + T0 one boundary
        ("SL_RT0", "1"),
        ("SL_T0ONE", "1"),
        // plain seeded compares on would-be tie ticks; source-rail sign wire read by the rail adds; seed/unseed fused
        // with the coordinate seams
        ("LF_TIE_SEED", "1"),
        ("LF_SIGNWIRE", "1"),
        ("LF_SEAMS", "1"),
        // peak cap, tuned together with LF_REORDER
        ("HEO_PIN_PP_WALK_MAX_QUBITS", "1236"),
        // the merged step's shared core has 13 ANDs (the rank bound) where it had 14; every fit, split and plan rule
        // counts the wire it no longer holds
        ("LF_CORE_FREED", "all"),
        ("NATIVE_SFUSE_B", "1"),
        // payload cells: fold window floored at 52 bits (Skywalk's late-round profile narrows it to 49),
        // chunk-boundary compare widened by one bit from tick 120 on, flag compare not widened (1 / 0 bits).
        // G6: floor 50 -> 52 is the second λ buy-back knob, +132 T for -0.18 classical failures; master/#1 has 50
        ("LF_CELL_FOLD_MIN", "52"),
        ("LF_CMP_SHIFT", "1,0"),
        ("LF_CMP_FROM", "120"),
        // tie-safe cell mode off (LF_TIE_FROM past the last tick): Leapfrog rail steps never cancel to zero, so the
        // cells see no structural ties
        ("LF_TIE_FROM", "999"),
        // walk room squeeze (see `early()`): odd rails held without their constant bit-0 wire (+2 walk wires, given
        // to the cells), split adders with the minimal low part
        ("LF_EARLY", "1"),
        // G6 exact pieces (no λ: paired classical failures identical with and without them), -39 T at cap 1236, all
        // in the multiply:
        // - merged fold erases up to 3 low carries right after writing the low sum bits (G4, [`lowcar_max`])
        ("LF_G4_LOWCAR", "3"),
        // - room-capped adders: lpa_capped's low chunk takes the full room ([`lpa_capped`]), on every caller
        ("LF_LPA_DENSE", "1"),
        ("LF_LPA_DENSE_ALL", "1"),
        // - a rail add whose two-way split does not fit goes through lpa_capped (U4, [`rail_add`])
        ("LF_RAIL_CAPPED", "1"),
        // G6 recipe totals: Q 1236, T 787,206 (eval, +725 over #1's recipe), score 972.99M (#1 971.66M: NOT below);
        // λ 192 nonces paired vs glam_base: fails -1.06 +- 0.17, proj 18.59, proj + 2se 19.13 <= 19.5 (gate passed)
        ("LF_LOWREL_PAD", "0"),
        // G7 exact phase tricks (same phase functions, no ancilla, lambda-neutral): the multiply's tick-0 phase fix
        // without its two payload rotations (t0_phrot, -763 T), the divide's endpoint measuring P1 unrotated
        // (div_phrot, -390 T), the product kept halved into the phase fix (t0_dbl, -48 T); the two k1k2 AND wires
        // uncomputed by Toffoli (+2 T) so the simulator's random stream stays aligned with G6 (clean paired λ).
        // G7 totals: Q 1236, T 786,007.565 (eval at the baked nonce; 192-nonce mean 786,006.6; model 786,106.8;
        // -1,199 vs G6), score 971,505,350 (#1 971,660,388: below by 155k); λ paired vs glam_base: fails
        // -0.984 +- 0.169 (vs G6 fin +0.078 +- 0.126, mism identical per nonce), proj 18.67; full: 9 cl / 9 ph / 0 anc
        ("LF_T0_PHROT", "1"),
        ("LF_DIV_PHROT", "1"),
        ("LF_T0_DBL", "1"),
        ("LF_PHROT_TOF", "1"),
        // G10: port of the board #1 (krishparadox, ac43304 / submission d7df7706, 971,660,388 = 786,133 x 1,236,
        // built on a2325be) onto G7. Its three λ re-allocations: the rule window back to 22 bits (late 20/18/16/14/12;
        // overrides the 21-bit lines above), the width table refit at budget 7.7e-4 (LF_G10_TABLE=770, its
        // leapfrog_data file copied unchanged), and a per-cell I35 bridge profile (overrides the Skywalk recipe's;
        // re-picked here by the same census method on this recipe, -6.5 T vs theirs). Their MERGED_WIN 55 is not
        // taken (G7 keeps 56). Plus the boundary compare widened from tick 100 instead of 120 (λ buy, +200 T).
        // G10 totals: Q 1236, T 785,519.7 (192-nonce eval mean), score ~970.90M (#1 971.66M); λ paired vs glam_base
        // fails -0.740 +- 0.259 (proj 18.91, proj + 2se 19.43 <= 19.5), vs G7 +0.245 +- 0.244.
        ("LF_YP8", "22"),
        // G12: port of the new board #1 (krishparadox, upstream 76e2661 / submission e9cacd1d, 774,510 x 1,236; on
        // top of leech1996's d6a54d3 early-tick windows "1:13,6:17,11:22" taken here, and jackylee0424's 3405791 I35
        // cells already in the G10 profile): the y15 one-fold payload tick (y15_onefold.rs, unchanged: three unfolded
        // adds and one fold per payload tick, payload-only ticks fwd 0.. / rev 1.., fused ticks fwd <99 / rev <92),
        // LF_REORDER_DIV/MUL 76. G12 totals: Q 1236, T model 773,793.75, 512-nonce eval mean 773,696.1, score
        // ~956.29M (#1 957.29M); λ paired vs glam_base 512 nonces fails -0.773 +- 0.160, proj 18.88, proj+2se 19.20.
        ("LF_YP8_LATE", "1:13,6:17,11:22,90:20,100:18,112:16,118:14,124:12"),
        ("LF_G10_TABLE", "770"),
        ("HEO_PIN_I35_PROFILE", "437:1:1,440:0:1,446:0:2,528:1:1,550:0:1,550:1:1,581:1:1,588:1:2,611:1:1,627:1:1,636:0:2,646:1:1,655:1:1,666:0:1,670:0:2,670:1:1,675:0:2,681:0:2,681:1:1,687:0:3,687:1:2"),
        ("LF_CMP_FROM", "120"),
        // T3 (λ margin into T): boundary compare widened from tick 120 again (-207 T model), with Y15_GUARD 0 in
        // y15_onefold.rs (-742 T). Both are phase-only (classical mismatches identical per nonce to G12).
        ("LF_CMP_FROM", "120"),
        // T6 seed fusion (square's last subtract + the multiply's seed e as one op, [`square_seed_r0`]): exact
        // (classical mismatches identical per nonce on 1,024 nonces), -46.5 T eval (512-nonce mean 772,700.9, Q 1236).
        // OFF: the formal λ gate fails by a hair on the first 512 (fails vs 522cbe3 +0.189 +- 0.091, proj+2SE 19.536);
        // fresh nonces 512..1023 give +0.031 +- 0.091 (pooled +0.110 +- 0.064, phase-noise only). "1" turns it on.
        ("LF_T6_SEEDFUSE", "0"),
        // C1 (T3 + T1 y15 add-2 ripple close in y15_onefold.rs, fused passes fwd <120 / rev <114): exact re-sweep on
        // the combined point, the divide's boundary 76 -> 82 (-40.5 T model; MUL 76 stays optimal) and the square's
        // retained-AND lend mask 3 -> 4 (-9 T). Combined model 770,787 at Q 1236; 512-nonce eval mean 770,692.40,
        // score ~952.58M; λ paired vs glam_base 512 fails -0.777 +- 0.158, proj+2se 19.193 (vs T3 -0.143 +- 0.101).
        ("LF_REORDER_DIV", "42"),
        ("HEO_PIN_SQ_LEND_RETAINED_ANDS", "4"),
        // C1 spend of the combined point's λ margin (192-nonce screens paired vs the combined point, then 512):
        // T6 seed fusion on (-46.6 T, phase-only), merged window 56 -> 54 (-128 T, mism +0.057), late rule windows
        // one bit shorter from tick 90 (-162 T, mism +0.115). Totals: Q 1236, model 770,449.75, 512-nonce eval mean
        // 770,358.13, score ~952.16M; λ paired vs glam_base 512 fails -0.590 +- 0.158, proj+2se 19.380 (margin 0.120);
        // vs the combined point +0.188 +- 0.102 (mism +0.170 +- 0.039).
        ("LF_T6_SEEDFUSE", "1"),
        ("LF_MERGED_WIN", "54"),
        ("LF_YP8_LATE", "1:13,6:17,11:22,90:19,100:17,112:15,118:13,124:11"),
    ] {
        std::env::set_var(k, v);
    }
    if FORCE_MERGED.load(std::sync::atomic::Ordering::Relaxed) {
        std::env::set_var("LF_MERGED", "1");
        for (k, v) in FORCE_EXTRA.lock().unwrap().iter() {
            std::env::set_var(k, v);
        }
    }
    std::env::remove_var("BACK_SEAM_FUSE");
}

/// Test hook: makes [`install_recipe`] (which runs after `build()` clears the process environment) also set
/// LF_MERGED=1, so one test process can build the env-free op stream with and without the merged op.
pub(crate) static FORCE_MERGED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
/// Test hook: extra recipe entries applied with [`FORCE_MERGED`] (paired A/B of recipe knobs, `LF_PAIRED_EXTRA`).
pub(crate) static FORCE_EXTRA: std::sync::Mutex<Vec<(String, String)>> = std::sync::Mutex::new(Vec::new());

/// `LEAPFROG_RULE=v0`: the plain 2-adic choice (deepest admissible); default sign2 (see [`choice_xor`]).
fn rule_v0() -> bool {
    std::env::var("LEAPFROG_RULE").is_ok_and(|v| v == "v0")
}

/// `LEAPFROG_RULE=pp`: plain ping-pong for comparison (one forced add-halve per tick, no choice, no barrel).
fn pp_mode() -> bool {
    std::env::var("LEAPFROG_RULE").is_ok_and(|v| v == "pp")
}

/// `LEAPFROG_M`: forced ping-pong steps per tick before the choice step (default 3; 1 in ping-pong mode).
fn forced() -> usize {
    if pp_mode() {
        return 1;
    }
    std::env::var("LEAPFROG_M").ok().and_then(|v| v.parse().ok()).unwrap_or(3)
}

// ---- profiler (LF_PROF2=1): expected Toffoli per component and per tick ----
thread_local! {
    static PROF: std::cell::RefCell<std::collections::BTreeMap<String, (f64, usize)>> = Default::default();
}
fn prof_on() -> bool {
    std::env::var("LF_PROF2").is_ok_and(|v| v == "1")
}
fn pmark(c: &Builder) -> f64 {
    c.expected_total()
}
fn pacc(c: &Builder, name: &str, t0: f64) {
    if prof_on() {
        let d = c.expected_total() - t0;
        PROF.with(|p| {
            let mut p = p.borrow_mut();
            let e = p.entry(name.to_string()).or_insert((0.0, 0));
            e.0 += d;
            e.1 += 1;
        });
    }
}
pub(crate) fn prof_dump() {
    if prof_on() {
        PROF.with(|p| {
            for (k, (v, n)) in p.borrow().iter() {
                eprintln!("LFPROF\t{k}\t{v:.1}\t{n}");
            }
        });
    }
}

// ---- y28: a deferred phase for the divide's rail boundary carries ----
/// `Y28_DEFER`: in the divide's fused forward pass a split rail add erases its kept boundary carry by a measurement
/// plus an exact compare on the outcome-1 shots ([`capped_add`], [`rail_add`], [`rail_add_mid`] forward). The mirrored
/// subtract of the divide's reverse rail pass rebuilds the same carry on a wire of one whole ladder (the rails are back
/// at the same values; everything in between permutes the basis or is an X measurement with its own fix), so the
/// outcome bit is kept and the phase is one Z under it on that wire: no compare. `false` = the gate list without the
/// change, byte for byte.
/// Measured (y28-loop b2, a copy with the top's measurements in the top's order): the Z's phase differs from the
/// compare's only on shots the top already gets wrong, where the reverse pass does not see the forward pass's rails.
const Y28_DEFER: bool = true;
thread_local! {
    /// the divide's fused forward pass is running (outcome bits are kept) / its reverse rail pass is (they are applied)
    static Y28_KEEP: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static Y28_USE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// the rail step now running, tick * 4 + step (0, 1: forced moves; 2: choice); usize::MAX outside a rail step
    static Y28_KEY: std::cell::Cell<usize> = const { std::cell::Cell::new(usize::MAX) };
    /// kept outcome bits: step key -> (boundary position, target width, bit)
    static Y28_BITS: std::cell::RefCell<std::collections::BTreeMap<usize, (usize, usize, crate::circuit::BitId)>> = const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
    /// the kept bit handed to the next whole ladder: (boundary position, bit)
    static Y28_HOOK: std::cell::Cell<Option<(usize, crate::circuit::BitId)>> = const { std::cell::Cell::new(None) };
    /// (kept, applied) in this divide
    static Y28_COUNT: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((0, 0)) };
}
fn y28_key(k: usize) {
    Y28_KEY.with(|x| x.set(k));
}
/// Forward: keep the measured boundary carry's outcome bit `m` (boundary at position `delta` of a target of `n` wires)
/// for the mirrored subtract. true = kept: the caller runs no compare and does not free the bit.
fn y28_store(delta: usize, n: usize, m: crate::circuit::BitId) -> bool {
    let key = Y28_KEY.with(|k| k.get());
    if !(Y28_DEFER && Y28_KEEP.with(|d| d.get()) && key != usize::MAX) {
        return false;
    }
    let old = Y28_BITS.with(|b| b.borrow_mut().insert(key, (delta, n, m)));
    assert!(old.is_none(), "y28: two boundaries under one step key {key}");
    Y28_COUNT.with(|x| x.set((x.get().0 + 1, x.get().1)));
    true
}
/// Is a kept bit waiting for the rail step now running?
fn y28_pending() -> bool {
    let key = Y28_KEY.with(|k| k.get());
    Y28_DEFER && Y28_USE.with(|d| d.get()) && key != usize::MAX && Y28_BITS.with(|b| b.borrow().contains_key(&key))
}
/// Reverse: the kept bit of this step's boundary, if any, for a subtract on a target of `n` wires.
fn y28_fetch(n: usize) -> Option<(usize, crate::circuit::BitId)> {
    if !y28_pending() {
        return None;
    }
    let key = Y28_KEY.with(|k| k.get());
    let (delta, kn, m) = Y28_BITS.with(|b| b.borrow_mut().remove(&key)).unwrap();
    assert_eq!(kn, n, "y28: step {key}: the mirrored subtract's target width differs from the add's");
    Some((delta, m))
}
/// Inside a whole ladder's carry sweep: `t` holds the carry into position `pos`. If the handed bit's boundary is here,
/// its phase goes on as a Z under the bit, and the bit is returned.
fn y28_apply(c: &mut Builder, hook: &mut Option<(usize, crate::circuit::BitId)>, pos: usize, t: QubitId) {
    let Some((d, m)) = *hook else { return };
    if pos != d {
        return;
    }
    c.z_if(t, m);
    c.free_bit(m);
    *hook = None;
    Y28_COUNT.with(|x| x.set((x.get().0, x.get().1 + 1)));
}

// ---- y16 trace (no effect on the gates): exclusive expected-Toffoli counters by kind ----
// kind 0: ripple adds (`ripple_add`, `ripple_add_consume` without its consumer); 1: measured erases by compare
// (`erase_with_compare`); 2: the consumer inside `ripple_add_consume` (a cell's fold).
thread_local! {
    /// expected Toffoli of the merged op's fold ([`m_fold`]) since it was last read
    static Y16_FOLD: std::cell::Cell<f64> = const { std::cell::Cell::new(0.0) };
    static Y16_ACC: std::cell::Cell<[f64; 3]> = const { std::cell::Cell::new([0.0; 3]) };
    static Y16_NEST: std::cell::Cell<f64> = const { std::cell::Cell::new(0.0) };
}
pub(crate) fn y16_enter(c: &Builder) -> (f64, f64) {
    (c.expected_total(), Y16_NEST.with(|n| n.replace(0.0)))
}
pub(crate) fn y16_leave(c: &Builder, kind: usize, st: (f64, f64)) {
    let total = c.expected_total() - st.0;
    let child = Y16_NEST.with(|n| n.replace(st.1 + total));
    Y16_ACC.with(|a| {
        let mut v = a.get();
        v[kind] += total - child;
        a.set(v);
    });
}
thread_local! { static Y17_LOG: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) }; }
/// y17 trace (no effect on the gates): a detail line for the payload op being traced
pub(crate) fn y17_log(_c: &Builder, f: impl FnOnce() -> String) {
    if y15::trace() {
        let s = f();
        Y17_LOG.with(|l| l.borrow_mut().push(s));
    }
}
/// (room, expected total, counters) before a payload op
type Y16Mark = (usize, f64, [f64; 3]);
/// y17 research price knob: extra wires the cap is read with inside a payload op of a late three-fold pass (ticks
/// 117..=136), by direction (0 forward, 1 reverse) and op (0 = the cell of the first forced letter, 1 = the second,
/// 2 = the merged op). All 0 = no effect on the gates. A non-zero entry is a PRICE, not a build: the peak goes over.
const Y17_PRICE: [[isize; 3]; 2] = [[0, 0, 0], [0, 0, 0]];
/// y17 research knob: the I35 bridge budget forced inside every payload op of the late three-fold passes (-1 = the
/// round's profile, as the base). The bridge is the existing exact split of a ripple that is short of wires.
const Y17_BRIDGE: isize = -1;
/// y17 research knob: every reverse cell of a late three-fold pass runs late (see Y17_PLAN); with Y17_LATE_D the
/// offset d of those cells.
const Y17_LATE_ALL: bool = false;
const Y17_LATE_D: isize = 0;
/// y17 (the late three-fold passes, forward ticks 121..=136 and reverse ticks 117..=136): plan choices per payload op,
/// found by building every op with every choice (experiments/y17-three in the Pensieve repo). An entry is
/// (direction: 0 forward, 1 reverse; tick; op: 0 = the cell of the first forced letter, 1 = of the second, 2 = the
/// merged op; d: the op's add (its route and chunk plan) is made as if the walk cap were d wires lower, its fold reads
/// the true cap; bridge: the I35 bridge budget of the op, -1 = the round's profile; late: a reverse cell runs just
/// before the rail step of its own letter is undone, where the choice and barrel letters are already erased, and not
/// at the tick's start). A plan made for a smaller room always fits, so the peak cannot rise. Y17_ON = false or an
/// empty table: the base, byte for byte.
/// Builder counts at peak 1236 on candidate T (9 October 2026; the comment after an entry is the uniform build its
/// choice was read from and the Toffoli it saves):
///   Y17_ON = false:                                             expected=772220.8 (gate list da162b12, T's own)
///   the table below (24 late reverse cells on 12 passes):       expected=772128.8 (bdfcef82; against T 0 outputs
///     differ on 30 draws and on both stress files)
///   the full table of 35 ops (commit 1ff9ea0: also 6 adds planned for 1 to 3 wires fewer and 5 bridge budgets):
///     expected=772095.2 (d2f3ac05; 0 of 812,160 outputs differ on 90 draws, but on the slope stress file 418 differ
///     and 18 shots are wrong only in the new list)
///   one pass alone (reverse tick 130, its two cells late):      expected=772206.8 (82c47193)
/// No pass saves 15 Toffoli (the best saves 14.0), so the y17-three brief's falsifier fired and the table is off.
/// Uniform builds, each choice on every op: d = -1 / -2 / -3: 772622.8 / 772837.2 / 772989.2; bridge 0 / 1 / 2:
/// 772353.8 / 772340.8 / 772463.8; every reverse cell late with d = 0 / -1: 772261.8 / 772206.8.
const Y17_ON: bool = true;
const Y17_PLAN: &[(usize, usize, usize, isize, isize, bool)] = &[
    // Y17_PLAN_BEGIN
    (1, 121, 1, 0, -1, true), // late0: 2.0
    (1, 121, 0, 0, -1, true), // late0: 2.0
    (1, 122, 1, 0, -1, true), // late0: 4.5
    (1, 122, 0, 0, -1, true), // late0: 4.5
    (1, 123, 1, 0, -1, true), // late0: 6.0
    (1, 123, 0, 0, -1, true), // late0: 6.0
    (1, 124, 1, 0, -1, true), // late0: 6.0
    (1, 124, 0, 0, -1, true), // late0: 6.0
    (1, 125, 1, 0, -1, true), // late0: 1.0
    (1, 125, 0, 0, -1, true), // late0: 1.0
    (1, 128, 1, 0, -1, true), // late0: 2.5
    (1, 128, 0, 0, -1, true), // late0: 2.5
    (1, 129, 1, 0, -1, true), // late0: 6.0
    (1, 129, 0, 0, -1, true), // late0: 6.0
    (1, 130, 1, 0, -1, true), // late0: 7.0
    (1, 130, 0, 0, -1, true), // late0: 7.0
    (1, 131, 1, 0, -1, true), // late0: 1.5
    (1, 131, 0, 0, -1, true), // late0: 1.5
    (1, 133, 1, -1, -1, true), // late1: 3.0
    (1, 133, 0, -1, -1, true), // late1: 3.0
    (1, 135, 1, -1, -1, true), // late1: 3.0
    (1, 135, 0, -1, -1, true), // late1: 3.0
    (1, 136, 1, -1, -1, true), // late1: 3.5
    (1, 136, 0, -1, -1, true), // late1: 3.5
    // Y17_PLAN_END
];
fn y17_plan(dir: usize, t: usize, slot: usize) -> (isize, isize, bool) {
    if t == 136 && dir == 1 && slot < 2 { return (0, 0, true); }

    if !(117..=136).contains(&t) {
        return (0, -1, false);
    }
    if Y17_LATE_ALL && dir == 1 && slot < 2 {
        return (Y17_LATE_D, -1, true);
    }
    if !Y17_ON {
        return (0, -1, false);
    }
    Y17_PLAN.iter().find(|e| e.0 == dir && e.1 == t && e.2 == slot).map_or((0, -1, false), |e| (e.3, e.4, e.5))
}
fn y16_mark(c: &Builder, t: usize, dir: usize, slot: usize) -> Y16Mark {
    Y17_LOG.with(|l| l.borrow_mut().clear());
    if (117..=136).contains(&t) {
        let (d, b, _) = y17_plan(dir, t, slot);
        assert!(d <= 0, "y17: a room offset is never positive");
        super::pingpong::Y17_EXTRA.with(|e| e.set(Y17_PRICE[dir][slot] + d));
        let b = if Y17_BRIDGE >= 0 { Y17_BRIDGE } else { b };
        if b >= 0 {
            super::bridge::Y17_FORCE.with(|v| v.set(Some(b as usize)));
        }
    }
    (cells::cap().saturating_sub(c.active_qubits() as usize), c.expected_total(), Y16_ACC.with(|a| a.get()))
}
/// one payload op: (name, room at its start, cost, ripple adds, compares, consumer)
fn y16_note(c: &Builder, ops: &mut Vec<(&'static str, usize, f64, f64, f64, f64)>, name: &'static str, m: Y16Mark) {
    super::pingpong::Y17_EXTRA.with(|e| e.set(0));
    super::bridge::Y17_FORCE.with(|v| v.set(None));
    let s = Y16_ACC.with(|a| a.get());
    ops.push((name, m.0, c.expected_total() - m.1, s[0] - m.2[0], s[1] - m.2[1], s[2] - m.2[2]));
    if y15::trace() {
        eprintln!("Y17_OP {name} room={} cost={:.1} adds={:.1} cmps={:.1} cons={:.1} :: {}", m.0, c.expected_total() - m.1, s[0] - m.2[0], s[1] - m.2[1], s[2] - m.2[2], Y17_LOG.with(|l| l.borrow_mut().drain(..).collect::<Vec<_>>().join(" ")));
    }
}
fn y16_print(dir: &str, t: usize, room: usize, extra: &str, ops: &[(&'static str, usize, f64, f64, f64, f64)]) {
    let tot = |f: fn(&(&'static str, usize, f64, f64, f64, f64)) -> f64| ops.iter().map(f).sum::<f64>();
    let (cost, adds, cmps, cons) = (tot(|o| o.2), tot(|o| o.3), tot(|o| o.4), tot(|o| o.5));
    let parts: Vec<String> = ops.iter().map(|o| format!("{}@{}:{:.1}/{:.1}/{:.1}/{:.1}", o.0, o.1, o.2, o.3, o.4, o.5)).collect();
    eprintln!("Y16_OLD {dir} t={t} room={room} cost={cost:.1} adds={adds:.1} cmps={cmps:.1} rest={:.1} consumer={cons:.1} {extra} ops=[{}]", cost - adds - cmps, parts.join(" "));
}

/// `LEAPFROG_BARREL=old`: the two nested shift stages (halve + quarter) instead of [`cmod_barrel`].
fn old_barrel() -> bool {
    std::env::var("LEAPFROG_BARREL").is_ok_and(|v| v == "old")
}

fn envelope() -> &'static Vec<usize> {
    static ENV: OnceLock<Vec<usize>> = OnceLock::new();
    ENV.get_or_init(|| {
        if yp8().is_some() {
            // the width table of the LF_YP8 rule carries the envelope as its first column
            return steps().iter().map(|r| r[0]).collect();
        }
        if pp_mode() {
            return include_str!("leapfrog_data/env_pp.txt")
                .lines()
                .map(str::trim)
                .filter(|l| !l.is_empty() && !l.starts_with('#'))
                .map(|l| l.parse().expect("envelope width"))
                .collect();
        }
        match (rule_v0(), forced()) {
            (true, 3) => include_str!("leapfrog_data/env_v0.txt"),
            (false, 3) => include_str!("leapfrog_data/env_sign2.txt"),
            (false, 2) if seed_half() && lf_w1() && lf_peel() => include_str!("leapfrog_data/env_w1_peel139.txt"),
            (false, 2) if seed_half() && lf_w1() && w1_k() == 20 => include_str!("leapfrog_data/env_sign2_m2_w1k20.txt"),
            (false, 2) if seed_half() && lf_w1() => include_str!("leapfrog_data/env_sign2_m2_w1.txt"),
            (false, 2) if seed_half() => include_str!("leapfrog_data/env_sign2_m2_half.txt"),
            (false, 2) => include_str!("leapfrog_data/env_sign2_m2.txt"),
            cfg => panic!("no Leapfrog envelope for (v0, m) = {cfg:?}"),
        }
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty() && !l.starts_with('#'))
            .map(|l| l.parse().expect("envelope width"))
            .collect()
    })
}

fn fredkin(c: &mut Builder, ctrl: QubitId, a: QubitId, b: QubitId) {
    c.cx(b, a);
    c.ccx(ctrl, a, b);
    c.cx(b, a);
}

/// Two's-complement resize: grow by sign extension, trim a top wire that must be a sign copy.
fn resize(c: &mut Builder, reg: &mut Vec<QubitId>, w: usize) {
    while reg.len() < w {
        let q = c.alloc_qubit();
        c.cx(*reg.last().unwrap(), q);
        reg.push(q);
    }
    while reg.len() > w {
        let top = reg.pop().unwrap();
        c.cx(*reg.last().unwrap(), top);
        c.free(top);
    }
}

/// `dst += (-1)^sign * src` on equal widths (sign = 1 subtracts): complement sandwich + carry-in.
fn signed_add(c: &mut Builder, sign: QubitId, src: &[QubitId], dst: &[QubitId]) {
    c.cx_all(sign, src);
    gidney_add(c, src, dst, Some(sign));
    c.cx_all(sign, src);
}

/// `out ^= carry_out(a + b + cin)`: Gidney carries, measurement-uncomputed; a and b restored. With `out = None`
/// it applies the phase (-1)^(NOT carry_out) instead (for MBU erasure of a kept carry, under a condition).
fn carry_out_xor(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: QubitId, out: Option<QubitId>) {
    let n = a.len();
    // Phase-only form: the top carry is never built. carry[n] = c ^ (a ^ c)(b ^ c) with c = carry[n - 1], so
    // (-1)^(NOT carry[n]) is one CZ on the two operand wires (while they hold a ^ c, b ^ c) times (-1)^(NOT c).
    let m = if out.is_none() && n >= 1 { n - 1 } else { n };
    let mut carry = vec![cin];
    for i in 0..m {
        let ci = carry[i];
        c.cx(ci, a[i]);
        c.cx(ci, b[i]);
        let t = and_new(c, a[i], b[i]);
        c.cx(ci, t);
        carry.push(t);
    }
    match out {
        Some(out) => c.cx(carry[n], out),
        None => {
            let ci = carry[m];
            if m < n {
                c.cx(ci, a[m]);
                c.cx(ci, b[m]);
                c.cz(a[m], b[m]);
                c.cx(ci, a[m]);
                c.cx(ci, b[m]);
            }
            c.x(ci);
            c.z_if(ci, NO_BIT);
            c.x(ci);
        }
    }
    for i in (0..m).rev() {
        let (ci, t) = (carry[i], carry[i + 1]);
        c.cx(ci, t);
        and_erase(c, t, a[i], b[i]);
        c.cx(ci, a[i]);
        c.cx(ci, b[i]);
    }
}

/// Rail `dst += (-1)^sign * src` whose carry ladder respects the walk cap: when the full ladder would not fit,
/// the low `delta` bits go first with their carry-out kept on one wire, the high part takes it as carry-in, and
/// the kept carry is erased exactly as [dst_low < src'_low + sign] (src' = sign-complemented source): +delta
/// Toffoli. `LF_RAIL_SPLIT=0` disables.
fn rail_signed_add(c: &mut Builder, sign: QubitId, src: &[QubitId], dst: &[QubitId]) {
    let n = dst.len();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    let off = std::env::var("LF_RAIL_SPLIT").is_ok_and(|v| v == "0");
    if off || n <= 3 || n - 1 <= room {
        signed_add(c, sign, src, dst);
        return;
    }
    let delta = n + 1 - room;
    if delta + 2 > room || delta + 1 >= n {
        signed_add(c, sign, src, dst);
        return;
    }
    c.cx_all(sign, src);
    let (za, cq) = (c.alloc_qubit(), c.alloc_qubit());
    let mut al = src[..delta].to_vec();
    al.push(za);
    let mut bl = dst[..delta].to_vec();
    bl.push(cq);
    gidney_add(c, &al, &bl, Some(sign));
    c.free(za);
    gidney_add(c, &src[delta..], &dst[delta..], Some(cq));
    // cq = NOT carry_out(dst_low + NOT src'_low + NOT sign)
    c.x_all(&src[..delta]);
    c.x(sign);
    carry_out_xor(c, &src[..delta], &dst[..delta], sign, Some(cq));
    c.x(sign);
    c.x_all(&src[..delta]);
    c.x(cq);
    c.free(cq);
    c.cx_all(sign, src);
}

/// [`gidney_add`] with the top carry XORed straight into the top sum wire (one CCX, nothing to erase): the same
/// n - 1 Toffoli on n - 2 carry wires instead of n - 1.
fn gidney_add_lean(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: Option<QubitId>) {
    let n = a.len();
    assert!(n >= 1 && b.len() == n);
    if n < 2 {
        return gidney_add(c, a, b, cin);
    }
    let mut carry: Vec<Option<QubitId>> = vec![None; n];
    carry[0] = cin;
    let mut y28h = Y28_HOOK.with(|x| x.take());
    for i in 0..n - 1 {
        if let Some(ci) = carry[i] {
            c.cx(ci, a[i]);
            c.cx(ci, b[i]);
        }
        if i + 2 == n {
            c.ccx(a[i], b[i], b[n - 1]);
            if let Some(ci) = carry[i] {
                c.cx(ci, b[n - 1]);
            }
        } else {
            let t = and_new(c, a[i], b[i]);
            if let Some(ci) = carry[i] {
                c.cx(ci, t);
            }
            carry[i + 1] = Some(t);
            y28_apply(c, &mut y28h, i + 1, t);
        }
    }
    assert!(y28h.is_none(), "y28: the kept bit's boundary carry is on no wire of this ladder");
    c.cx(a[n - 1], b[n - 1]);
    for i in (0..n - 1).rev() {
        if let Some(next) = carry[i + 1] {
            if let Some(ci) = carry[i] {
                c.cx(ci, next);
            }
            and_erase(c, next, a[i], b[i]);
        }
        c.cx(a[i], b[i]);
        if let Some(ci) = carry[i] {
            c.cx(ci, a[i]);
            c.cx(ci, b[i]);
        }
    }
}

/// `b += a + cin` (Gidney) whose carry ladder respects the walk cap, as [`rail_signed_add`]'s split but for any
/// carry-in (None = 0). The kept carry is [b_low_new < a_low + cin] = NOT carry_out(b_low_new + NOT a_low +
/// NOT cin), erased with an exact compare.
fn capped_add(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: Option<QubitId>) {
    let n = b.len();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    let off = std::env::var("LF_RAIL_SPLIT").is_ok_and(|v| v == "0");
    // the lean ladder holds n - 2 carries (its top carry goes straight into the top sum wire)
    if off || n <= 3 || n - 2 <= room {
        gidney_add_lean(c, a, b, cin);
        return;
    }
    let delta = n - room - split_tight() as usize;
    if std::env::var_os("LF_SPLIT_TRACE").is_some() {
        eprintln!("LF_SPLIT n={n} room={room} delta={delta}");
    }
    if delta + 3 > room || delta + 1 >= n {
        gidney_add_lean(c, a, b, cin);
        return;
    }
    let (za, cq) = (c.alloc_qubit(), c.alloc_qubit());
    let mut al = a[..delta].to_vec();
    al.push(za);
    let mut bl = b[..delta].to_vec();
    bl.push(cq);
    gidney_add_lean(c, &al, &bl, cin);
    c.free(za);
    gidney_add_lean(c, &a[delta..], &b[delta..], Some(cq));
    c.x_all(&a[..delta]);
    let ncin = match cin {
        Some(q) => {
            c.x(q);
            q
        }
        None => {
            let o = c.alloc_qubit();
            c.x(o);
            o
        }
    };
    let q0 = pmark(c);
    if split_mbu() {
        // cq = NOT carry_out(...): measure it away and fix the phase only on shots whose outcome is 1
        let m = c.alloc_bit();
        c.hmr(cq, m);
        c.release_clean(cq);
        // y28: in the divide's fused pass the outcome is kept and its phase applied in the mirrored subtract
        if !y28_store(delta, n, m) {
            c.push_condition(m);
            carry_out_xor(c, &a[..delta], &b[..delta], ncin, None);
            c.pop_condition();
            c.free_bit(m);
        }
    } else {
        carry_out_xor(c, &a[..delta], &b[..delta], ncin, Some(cq));
        c.x(cq);
        c.free(cq);
    }
    pacc(c, "split.rail_erase", q0);
    match cin {
        Some(q) => c.x(q),
        None => {
            c.x(ncin);
            c.free(ncin);
        }
    }
    c.x_all(&a[..delta]);
}

/// `LF_SEED=half`: rails (R0, R1) = (d | d - p, (R0 +- p)/2) (both odd), payload (y, y/2) (rails red-team seed e).
fn seed_half() -> bool {
    std::env::var("LF_SEED").is_ok_and(|v| v == "half")
}

/// `LF_EARLY=1`: the walk room squeeze, i.e. [`lowrel`] + [`split_tight`] (each also has its own flag, which
/// overrides LF_EARLY: `LF_LOWREL=0` / `LF_SPLIT_TIGHT=0`).
fn early() -> bool {
    std::env::var("LF_EARLY").is_ok_and(|v| v == "1")
}

/// `LF_SPLIT_TIGHT=1` (or LF_EARLY): split adders keep the minimal low part. Rails ([`capped_add`], [`rail_add`]):
/// the high part holds n - delta - 1 carries + the kept carry, so delta = n - room (was n + 1 - room). Fold ladders
/// ([`lpa_capped`]): the low chunk is n - room (its kept carry's erase compares only it; was room - 4, i.e. the
/// erase compared ~room bits), and a ladder of n bits fits when n - 1 <= room.
fn split_tight() -> bool {
    std::env::var("LF_SPLIT_TIGHT").map_or(early(), |v| v == "1")
}

/// `LF_SPLIT_MBU=0` disables the MBU-halved erasure of split-adder kept carries.
fn split_mbu() -> bool {
    !std::env::var("LF_SPLIT_MBU").is_ok_and(|v| v == "0")
}

/// `LF_FAST=1` (m = 2, sign2): the rail package of the rails red-team (scratch rails_ops/rails.py): adds that skip
/// the known low carries, the choice and barrel letters from linear forms (5 Toffoli), MBU letter erasure on the
/// reverse tick, a 3-Toffoli sign fill, and per-step widths (leapfrog_data/env_sign2_m2_steps.txt).
fn lf_fast() -> bool {
    std::env::var("LF_FAST").is_ok_and(|v| v == "1") && !pp_mode() && !rule_v0() && forced() == 2
}

/// Per-step widths (W, n0, n1, n2, nb) of the fast path.
fn steps() -> &'static Vec<[usize; 5]> {
    static S: OnceLock<Vec<[usize; 5]>> = OnceLock::new();
    S.get_or_init(|| {
        let u2 = std::env::var("LF_U2_ENV").unwrap_or_default();
        if yp8().is_some() && u2 == "137_1198" {
            include_str!("leapfrog_data/u2_env_137_1198.txt")
        } else if yp8().is_some() && u2 == "136_1192" {
            include_str!("leapfrog_data/u2_env_136_1192.txt")
        } else if yp8().is_some() && u2 == "135_1188" {
            include_str!("leapfrog_data/u2_env_135_1188.txt")
        } else if yp8().is_some() && u2 == "135_1184" {
            include_str!("leapfrog_data/u2_env_135_1184.txt")
        } else if yp8().is_some() && u2 == "135_1182" {
            include_str!("leapfrog_data/u2_env_135_1182.txt")
        } else if yp8().is_some() && u2 == "134_1186" {
            include_str!("leapfrog_data/u2_env_134_1186.txt")
        } else if yp8().is_some() && u2 == "134_1184" {
            include_str!("leapfrog_data/u2_env_134_1184.txt")
        } else if yp8().is_some() && u2 == "134_1182" {
            include_str!("leapfrog_data/u2_env_134_1182.txt")
        } else if yp8().is_some() && u2 == "134_1180" {
            include_str!("leapfrog_data/u2_env_134_1180.txt")
        } else if yp8().is_some() && u2 == "133_1182" {
            include_str!("leapfrog_data/u2_env_133_1182.txt")
        } else if yp8().is_some() && u2 == "133_1180" {
            include_str!("leapfrog_data/u2_env_133_1180.txt")
        } else if yp8().is_some() && u2 == "133_1178" {
            include_str!("leapfrog_data/u2_env_133_1178.txt")
        } else if yp8().is_some() && std::env::var("LF_G10_TABLE").is_ok_and(|v| v == "770") {
            // G10 port of krishparadox's ac43304 (d7df7706, board #1 971,660,388): the same peel fit refit at the
            // looser budget 7.7e-4 per walk under the 22-bit rule (LF_YP8=22, late 20/18/16/14/12)
            include_str!("leapfrog_data/pack_t0hat_tail0_138_steps_k770_lw2.txt")
        } else if yp8().is_some() {
            // 138 ticks, fitted for the pinned recipe: the LF_YP8 rule with its late window lengths, tick 0 on its
            // own rule (LF_T0_FREE) and a last tick without forced steps (LF_TAIL_FORCED=0)
            include_str!("leapfrog_data/pack_t0hat_tail0_138_steps_k700_lw2.txt")
        } else if seed_half() && lf_w1() && lf_peel() {
            include_str!("leapfrog_data/env_w1_peel139_steps.txt")
        } else if seed_half() && lf_w1() && w1_k() == 20 {
            include_str!("leapfrog_data/env_sign2_m2_w1k20_steps.txt")
        } else if seed_half() && lf_w1() {
            include_str!("leapfrog_data/env_sign2_m2_w1_steps.txt")
        } else if seed_half() {
            include_str!("leapfrog_data/env_sign2_m2_half_steps.txt")
        } else {
            include_str!("leapfrog_data/env_sign2_m2_steps.txt")
        }
            .lines()
            .filter(|l| !l.trim().is_empty() && !l.starts_with('#'))
            .map(|l| {
                let v: Vec<usize> = l.split_whitespace().map(|x| x.parse().unwrap()).collect();
                [v[0], v[1], v[2], v[3], v[4]]
            })
            .collect()
    })
}

/// Forced step `t <- (t + (-1)^sign b)/2`, sign = t1 ^ b1: bit 0 sums to 0 (carry 1), bit 1 sums to 1 with carry
/// t1, so the ripple covers bits [2, n) with carry-in t1. Drops t's low wire.
/// `LF_SIGNWIRE=1`: in the payload legs the source rail stays at min(W(t), W(t+1)) bits through the rail adds (the
/// width it is truncated to at the tick's end anyway); the adds read its sign wire for the missing top positions.
fn lf_signwire() -> bool {
    std::env::var("LF_SIGNWIRE").is_ok_and(|v| v == "1")
}

/// `LF_RAIL_CAPPED=1`: see [`rail_add`].
fn rail_capped() -> bool {
    std::env::var("LF_RAIL_CAPPED").is_ok_and(|v| v == "1")
}

/// Rail `b += a + cin` with `a` possibly shorter than `b` (two's complement: positions past `a` read `a`'s sign wire,
/// shared by every such position of the parity ladder); same split policy under the walk cap as the full-width add.
fn rail_add(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: Option<QubitId>) {
    let n = b.len();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    if let Some(h) = y28_fetch(n) {
        // y28: the mirrored subtract of a split forward add. It is one whole ladder here (the same gates as below),
        // which holds the carry into the forward boundary on a wire: the kept outcome's phase goes on there.
        assert!(n <= 3 || n - 2 <= room, "y28: the mirrored subtract must be one whole ladder");
        assert!(h.0 >= 1 && h.0 + 2 <= n, "y28: boundary {} outside the ladder of {n}", h.0);
        Y28_HOOK.with(|x| x.set(Some(h)));
        if a.len() >= b.len() {
            gidney_add_lean(c, a, b, cin);
        } else {
            let sg = *a.last().unwrap();
            let add: Vec<Vec<QubitId>> = (0..b.len()).map(|i| vec![if i < a.len() { a[i] } else { sg }]).collect();
            ladder_parity_add(c, b, &add, cin);
        }
        assert!(Y28_HOOK.with(|x| x.take()).is_none(), "y28: kept bit not taken by the ladder");
        return;
    }
    let off = std::env::var("LF_RAIL_SPLIT").is_ok_and(|v| v == "0");
    // LF_RAIL_CAPPED=1: an add whose two-way split does not fit either (n > ~2 room) goes through the recursive
    // room-sized split of the fold ladders ([`lpa_capped`]) instead of a full-width ladder that overruns the cap
    let deep = rail_capped() && !off && n > 3 && n - 2 > room && {
        let delta = (n - room).saturating_sub(split_tight() as usize);
        delta + 3 > room || delta + 1 >= n || (a.len() < n && delta >= a.len())
    };
    if a.len() >= b.len() && !deep {
        return capped_add(c, a, b, cin);
    }
    let sg = *a.last().unwrap();
    let add: Vec<Vec<QubitId>> = (0..b.len()).map(|i| vec![if i < a.len() { a[i] } else { sg }]).collect();
    if deep {
        let q0 = pmark(c);
        lpa_capped(c, b, &add, cin);
        pacc(c, "split.rail_deep", q0);
        return;
    }
    // capped_add's split: the low `delta` bits first with their carry kept, the rest takes it as carry-in, the kept
    // carry erased (MBU) as NOT carry_out(b_low_new + NOT a_low + NOT cin)
    // the parity ladder holds n - 2 carries (its top carry goes straight into the top sum wire)
    if off || n <= 3 || n - 2 <= room {
        return ladder_parity_add(c, b, &add, cin);
    }
    let delta = n - room - split_tight() as usize;
    if delta + 3 > room || delta + 1 >= n || delta >= a.len() {
        return ladder_parity_add(c, b, &add, cin);
    }
    let cq = c.alloc_qubit();
    let mut lo = b[..delta].to_vec();
    lo.push(cq);
    let mut lo_add = add[..delta].to_vec();
    lo_add.push(vec![]);
    ladder_parity_add(c, &lo, &lo_add, cin);
    ladder_parity_add(c, &b[delta..], &add[delta..], Some(cq));
    let ncin = match cin {
        Some(q) => {
            c.x(q);
            q
        }
        None => {
            let o = c.alloc_qubit();
            c.x(o);
            o
        }
    };
    let q0 = pmark(c);
    let m = c.alloc_bit();
    c.hmr(cq, m);
    c.release_clean(cq);
    // y28: as in [`capped_add`]
    if !y28_store(delta, n, m) {
        c.push_condition(m);
        carry_out_parity_xor(c, &b[..delta], &add[..delta], true, ncin, None);
        c.pop_condition();
        c.free_bit(m);
    }
    pacc(c, "split.rail_erase", q0);
    match cin {
        Some(q) => c.x(q),
        None => {
            c.x(ncin);
            c.free(ncin);
        }
    }
}

fn fast_add_halve_forced(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    c.cx_all(sign, b);
    rail_add(c, &b[2..], &t[2..], Some(t[1]));
    c.x(t[0]);
    c.cx(b[1], t[1]);
    c.x(t[1]);
    c.cx_all(sign, b);
    let low = t.remove(0);
    c.free(low);
}
fn fast_double_sub_forced(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    t.insert(0, c.alloc_qubit());
    c.cx_all(sign, b);
    c.x(t[1]);
    c.cx(b[1], t[1]);
    c.x(t[0]);
    c.x_all(&t[2..]);
    rail_add(c, &b[2..], &t[2..], Some(t[1]));
    c.x_all(&t[2..]);
    c.cx_all(sign, b);
}
/// Choice step, any sign: bit 0 sums to 0 (carry 1), bits [1, n) get t + b' + 1 = NOT(NOT t + NOT b').
fn fast_add_halve_choice(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    c.cx_all(sign, b);
    c.x_all(&b[1..]);
    c.x_all(&t[1..]);
    rail_add(c, &b[1..], &t[1..], None);
    c.x_all(&t[1..]);
    c.x_all(&b[1..]);
    c.x(t[0]);
    c.cx_all(sign, b);
    let low = t.remove(0);
    c.free(low);
}
fn fast_double_sub_choice(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    t.insert(0, c.alloc_qubit());
    c.cx_all(sign, b);
    c.x(t[0]);
    c.x_all(&b[1..]);
    rail_add(c, &b[1..], &t[1..], None);
    c.x_all(&b[1..]);
    c.cx_all(sign, b);
}

/// `LF_LOWREL=1` (or LF_EARLY; fast path): rails are held WITHOUT their bit-0 wire wherever they are odd (both rails
/// at every tick boundary, through the forced steps, the payload ops and the choice add; the target holds it again
/// only from the choice add to the rail barrel). An odd rail's bit 0 is the constant 1, so the wire is released
/// (X + free) and re-materialised (alloc + X) only around the ops that read it: +2 wires of walk room almost
/// everywhere. Rail vectors then hold bit j + 1 at index j.
fn lowrel() -> bool {
    std::env::var("LF_LOWREL").map_or(early(), |v| v == "1") && lf_fast()
}
/// `LF_LOWREL_PAD=1`: the payload ops keep their pre-LOWREL live count (an idle placeholder wire per released bit-0
/// wire), so every cell picks the same route as without LF_LOWREL (its extra room would let a few more cells take
/// the finite-cut retained prebias); only the rail ops get the room.
/// `LF_LOWREL_PAD=2`: pad only the cells (add_halve / double_add, where the prebias routes are chosen); the merged
/// ops and payload barrels keep the extra room.
fn lr_pad_mode() -> u8 {
    std::env::var("LF_LOWREL_PAD").ok().and_then(|v| v.parse().ok()).unwrap_or(if early() { 2 } else { 0 })
}
fn lr_pad_on() -> bool {
    lr_pad_mode() == 1
}
fn lr_pad(c: &mut Builder, n: usize) -> Vec<QubitId> {
    if lr_pad_on() { c.alloc_qubits(n) } else { Vec::new() }
}
/// Cell pad outside any [`lr_pad`] block (modes 1 and 2).
fn lr_pad_c(c: &mut Builder, n: usize) -> Vec<QubitId> {
    if lr_pad_mode() >= 1 { c.alloc_qubits(n) } else { Vec::new() }
}
/// Cell pad inside an [`lr_pad`] block (mode 2 only).
fn lr_pad_c2(c: &mut Builder, n: usize) -> Vec<QubitId> {
    if lr_pad_mode() == 2 { c.alloc_qubits(n) } else { Vec::new() }
}
fn lr_unpad(c: &mut Builder, pads: Vec<QubitId>) {
    for q in pads {
        c.release_clean(q);
    }
}

/// Release an odd rail's bit-0 wire (it holds 1).
fn lr_drop(c: &mut Builder, r: &mut Vec<QubitId>) {
    let q = r.remove(0);
    c.x(q);
    c.free(q);
}
/// Re-materialise an odd rail's bit-0 wire.
fn lr_restore(c: &mut Builder, r: &mut Vec<QubitId>) {
    let q = c.alloc_qubit();
    c.x(q);
    r.insert(0, q);
}
/// [`fast_add_halve_forced`] on bit-0-less rails; the halved target's bit 0 (1) is not held either.
fn fast_add_halve_forced_lr(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    c.cx_all(sign, b);
    // bit 1 of the sum: t1 ^ b1 ^ sign = 0 (the halved rail's bit 0 is 1: released). sign = t1 ^ b1, so the
    // complemented source's bit 1 already equals t1, the carry into bit 2: t's bit-1 wire is cleared and released
    // BEFORE the ladder, which takes its carry-in from the source wire (one more free wire during the add).
    c.cx(b[0], t[0]);
    let low = t.remove(0);
    c.free(low);
    rail_add(c, &b[1..], t, Some(b[0]));
    c.cx_all(sign, b);
}
/// Inverse of [`fast_add_halve_forced_lr`].
fn fast_double_sub_forced_lr(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>) {
    // mirror of the forward step: the ladder's carry-in is the complemented source's bit 1; t's bit-1 wire (the
    // same value) is made only after the ladder
    c.cx_all(sign, b);
    c.x_all(t);
    rail_add(c, &b[1..], t, Some(b[0]));
    c.x_all(t);
    let u = c.alloc_qubit();
    c.cx(b[0], u);
    c.cx_all(sign, b);
    t.insert(0, u);
}
/// [`fast_add_halve_choice`] on bit-0-less rails: the halved (even) target comes out holding its bit 0.
fn fast_add_halve_choice_lr(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &[QubitId]) {
    c.cx_all(sign, b);
    c.x_all(b);
    c.x_all(t);
    rail_add(c, b, t, None);
    c.x_all(t);
    c.x_all(b);
    c.cx_all(sign, b);
}
/// Inverse of [`fast_add_halve_choice_lr`]: even target holding bit 0 in, bit-0-less odd target out.
fn fast_double_sub_choice_lr(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &[QubitId]) {
    c.cx_all(sign, b);
    c.x_all(b);
    rail_add(c, b, t, None);
    c.x_all(b);
    c.cx_all(sign, b);
}

/// Put the choice's linear forms on t's wires: t1 <- dq = t1^b1, t_i <- z_i = t_i^b_i^dq (i = 2,3,4; the deep
/// candidate's bits: -b mod 32 is ~b with bit 0 set, and the carries into bits 2..4 are 1 wherever they are read),
/// t_top <- eq = t_top^b_top^dq (signs equal). Self-inverse up to order: [`zlin_off`].
fn zlin_on(c: &mut Builder, t: &[QubitId], b: &[QubitId]) {
    let top = t.len() - 1;
    c.cx(b[1], t[1]);
    for i in 2..5 {
        c.cx(b[i], t[i]);
        c.cx(t[1], t[i]);
    }
    c.cx(b[top.min(b.len() - 1)], t[top]); // a shorter b (LF_SIGNWIRE): its sign wire
    c.cx(t[1], t[top]);
}
fn zlin_off(c: &mut Builder, t: &[QubitId], b: &[QubitId]) {
    let top = t.len() - 1;
    c.cx(t[1], t[top]);
    c.cx(b[top.min(b.len() - 1)], t[top]);
    for i in 2..5 {
        c.cx(t[1], t[i]);
        c.cx(b[i], t[i]);
    }
    c.cx(b[1], t[1]);
}

/// `LF_W1=1` (fast path, seed half): rule W1-window (rails tail research, scratch letters/tail, w1/): at e = 1 with
/// equal signs, take deep iff |x| > 4|B| in a K-bit window at the tick's fixed anchor (only informative for the slow
/// walks whose rails are still near the envelope top), else sign2.
fn lf_w1() -> bool {
    std::env::var("LF_W1").is_ok_and(|v| v == "1")
}
/// Joint-optimised W1 envelope (`LF_PEEL=1`): survivor maxima after sacrificing the failure budget shot by shot,
/// R = 139 (scratchpad peel fit; same fresh-seed failure as the uniform-quantile envelope).
fn lf_peel() -> bool {
    std::env::var("LF_PEEL").is_ok_and(|v| v == "1")
}

/// Rail trims around the payload ops (`LF_TRIM=1`, see [`fwd_tick_fast`] / [`rev_tick_fast`]).
fn lf_trim() -> bool {
    std::env::var("LF_TRIM").is_ok_and(|v| v == "1")
}

/// Window size K: under `LF_YP8=L` the window holds K + 2 = L bits; without it `LF_W1K` (default 24).
fn w1_k() -> usize {
    static K: OnceLock<usize> = OnceLock::new();
    *K.get_or_init(|| match yp8() {
        Some(l) => l - 2,
        None => std::env::var("LF_W1K").ok().and_then(|v| v.parse().ok()).unwrap_or(24),
    })
}
/// Window size at tick t: [`w1_k`], or under LF_YP8 with `LF_YP8_LATE=t0:L0,t1:L1,...` the window length L from
/// that tick on (later entries win).
fn w1_kt(t: usize) -> usize {
    static LATE: OnceLock<Vec<(usize, usize)>> = OnceLock::new();
    let late = LATE.get_or_init(|| {
        let Some(v) = yp8().and_then(|_| std::env::var("LF_YP8_LATE").ok()) else { return Vec::new() };
        v.split(',')
            .map(|e| {
                let (a, b) = e.split_once(':').expect("LF_YP8_LATE=t0:L0,t1:L1");
                (a.trim().parse().unwrap(), b.trim().parse::<usize>().unwrap() - 2)
            })
            .collect()
    });
    late.iter().filter(|&&(from, _)| t >= from).last().map_or_else(w1_k, |&(_, k)| k)
}
fn w1_anchor(t: usize) -> usize {
    static A: OnceLock<Vec<usize>> = OnceLock::new();
    let a = A.get_or_init(|| {
        // LF_YP8: anchor = the choice step's width - 3, so the window's top is the register's top magnitude bit.
        // Without it, K = 18 reads its window 4 bits lower: every anchor - 4, floored at 3
        let table = if yp8().is_some() {
            include_str!("leapfrog_data/yp8_L22_138_anch.txt")
        } else if w1_k() == 18 {
            include_str!("leapfrog_data/anch_w1_k18a4.txt")
        } else {
            include_str!("leapfrog_data/anch_w1.txt")
        };
        table.split(',').filter_map(|v| v.trim().parse().ok()).collect()
    });
    a[t.min(a.len() - 1)]
}

/// Comparator operand bit: constant or a wire (with an inversion flag).
#[derive(Clone, Copy)]
enum Lit {
    Zero,
    One,
    W(QubitId, bool),
}
/// One AND of the comparator's carry chain, for measurement-based erasure: t = AND(a ^ ia, b ^ ib) (^ c when the
/// Gidney form XORed the incoming carry wire c into a, b and t).
struct AndRec {
    t: QubitId,
    a: QubitId,
    ia: bool,
    b: QubitId,
    ib: bool,
    c: Option<QubitId>,
}
fn lit_and(c: &mut Builder, recs: &mut Vec<AndRec>, (a, ia): (QubitId, bool), (b, ib): (QubitId, bool), cw: Option<QubitId>) -> QubitId {
    if let Some(cw) = cw {
        c.cx(cw, a);
        c.cx(cw, b);
    }
    if ia { c.x(a); }
    if ib { c.x(b); }
    let t = and_new(c, a, b);
    if ib { c.x(b); }
    if ia { c.x(a); }
    if let Some(cw) = cw {
        c.cx(cw, t);
        c.cx(cw, b);
        c.cx(cw, a);
    }
    recs.push(AndRec { t, a, ia, b, ib, c: cw });
    t
}
fn erase_recs(c: &mut Builder, recs: Vec<AndRec>) {
    for r in recs.into_iter().rev() {
        if let Some(cw) = r.c {
            c.cx(cw, r.a);
            c.cx(cw, r.b);
            c.cx(cw, r.t);
        }
        if r.ia { c.x(r.a); }
        if r.ib { c.x(r.b); }
        and_erase(c, r.t, r.a, r.b);
        if r.ib { c.x(r.b); }
        if r.ia { c.x(r.a); }
        if let Some(cw) = r.c {
            c.cx(cw, r.b);
            c.cx(cw, r.a);
        }
    }
}
/// MAJ of three literals (carry of a full adder), folding constants; returns the carry literal.
fn lit_maj(c: &mut Builder, recs: &mut Vec<AndRec>, x: Lit, y: Lit, cin: Lit) -> Lit {
    use Lit::*;
    let and2 = |c: &mut Builder, recs: &mut Vec<AndRec>, p: Lit, q: Lit| -> Lit {
        match (p, q) {
            (Zero, _) | (_, Zero) => Zero,
            (One, o) | (o, One) => o,
            (W(a, ia), W(b, ib)) => W(lit_and(c, recs, (a, ia), (b, ib), None), false),
        }
    };
    let neg = |l: Lit| match l {
        Zero => One,
        One => Zero,
        W(q, i) => W(q, !i),
    };
    let or2 = |c: &mut Builder, recs: &mut Vec<AndRec>, p: Lit, q: Lit| -> Lit { neg(and2(c, recs, neg(p), neg(q))) };
    match (x, y, cin) {
        (Zero, o, k) | (o, Zero, k) | (o, k, Zero) => and2(c, recs, o, k),
        (One, o, k) | (o, One, k) | (o, k, One) => or2(c, recs, o, k),
        (W(a, ia), W(b, ib), W(cw, ic)) => {
            // MAJ = AND(x ^ c, y ^ c) ^ c (Gidney); the wires a, b carry raw values, so fold c's inversion in
            let t = lit_and(c, recs, (a, ia ^ ic), (b, ib ^ ic), Some(cw));
            W(t, ic)
        }
    }
}
/// The W1 window bits of `r` (width >= 6) at tick t: positions [h, h + K + 2), h = max(anchor - K, 0); a position
/// at or above the sign wire is the constant 0 (sign extension XOR sign). Returns the wires (Some) or constants.
fn w1_window(r: &[QubitId], t: usize) -> Vec<Option<QubitId>> {
    let h = w1_anchor(t).saturating_sub(w1_kt(t));
    (h..h + w1_kt(t) + 2).map(|p| (p + 1 < r.len()).then(|| r[p])).collect()
}
/// Conjugate the window wires with their register's sign (ones' complement magnitude); self-inverse.
fn w1_conj(c: &mut Builder, r: &[QubitId], win: &[Option<QubitId>]) {
    let sg = *r.last().unwrap();
    for q in win.iter().flatten() {
        c.cx(sg, *q);
    }
}
/// Carry chain of a + NOT(4b) (window magnitudes of x and B): its carry-out is [a > 4b]. Returns the result literal
/// and the AND records (window conjugation must be ON while building and while erasing).
fn w1_chain(c: &mut Builder, wa: &[Option<QubitId>], wb: &[Option<QubitId>]) -> (Lit, Vec<AndRec>) {
    w1_chain_s(c, wa, wb, 2)
}
/// [`w1_chain`] for the factor 2^s: carry-out of a + NOT(2^s b) = [a > 2^s b].
fn w1_chain_s(c: &mut Builder, wa: &[Option<QubitId>], wb: &[Option<QubitId>], s: usize) -> (Lit, Vec<AndRec>) {
    let l = wa.len();
    let mut recs = Vec::new();
    let mut carry = Lit::Zero;
    for j in 0..l + s {
        let x = match wa.get(j).copied().flatten() {
            Some(q) => Lit::W(q, false),
            None => Lit::Zero,
        };
        let y = if j < s {
            Lit::One
        } else {
            match wb.get(j - s).copied().flatten() {
                Some(q) => Lit::W(q, true),
                None => Lit::One,
            }
        };
        carry = lit_maj(c, &mut recs, x, y, carry);
    }
    (carry, recs)
}

/// sign2 choice into `out` and the barrel letters into k1, k2 (all xor into zero wires), 5 Toffoli:
/// out = dq ^ 1 ^ [z2=z3=z4=0] ^ (z2 & eq); Dsel = out ^ dq (deep taken); k2 = Dsel & !z2; k1 = Dsel ^ (k2 & z3).
fn fast_choice(c: &mut Builder, t: &[QubitId], b: &[QubitId], out: QubitId, k1: QubitId, k2: QubitId, tick: usize) {
    let top = t.len() - 1;
    // LF_T0_FREE: tick 0 takes the low-bit rule (deep iff admissible) with no window compare, and its equal-sign
    // veto reads the sign from the source rail (the `T0_M` branch below), so its letter is a function of the source
    // rail alone (see [`t0_derive`])
    let plain = t0_plain(tick);
    let w1 = (lf_w1() && !plain).then(|| {
        let (wa, wb) = (w1_window(t, tick), w1_window(b, tick));
        w1_conj(c, t, &wa);
        w1_conj(c, b, &wb);
        let (w, recs) = w1_chain(c, &wa, &wb);
        w1_conj(c, b, &wb);
        w1_conj(c, t, &wa);
        (w, recs, wa, wb)
    });
    zlin_on(c, t, b);
    for i in 2..5 {
        c.x(t[i]);
    }
    let a1 = and_new(c, t[2], t[3]);
    let a2 = and_new(c, a1, t[4]);
    for i in 2..5 {
        c.x(t[i]);
    }
    let g0 = (!plain).then(|| and_new(c, t[2], t[top]));
    c.cx(t[1], out);
    c.x(out);
    c.cx(a2, out);
    if let Some(g) = g0 {
        // W1: at e = 1 with equal signs the window can still accept deep: reject only if NOT [|x| > 4|B|]
        match w1.as_ref().map(|v| v.0) {
            None | Some(Lit::Zero) => c.cx(g, out),
            Some(Lit::One) => {}
            Some(Lit::W(wq, inv)) => {
                let mut r2 = Vec::new();
                let g2 = lit_and(c, &mut r2, (g, false), (wq, !inv), None);
                c.cx(g2, out);
                erase_recs(c, r2);
            }
        }
        and_erase(c, g, t[2], t[top]);
    } else if let Some(mh) = T0_M.with(|m| m.get()) {
        // equal-sign veto with the sign read from R1 ([`t0_m_on`]): g = z2 & (!m ^ dq)
        let (a, b) = (Lin::of(&[t[2]]), Lin { w: vec![mh, t[1]], one: true });
        let g = lin_and(c, &a, &b);
        c.cx(g, out);
        lin_and_erase(c, g, &a, &b);
    }
    for i in 2..5 {
        c.x(t[i]);
    }
    // barrel letters as XORs of wires at hand (t2 holds !z2), no Toffoli: k2 = Dsel & !z2 = !z2 ^ a2 (Dsel =
    // 1 ^ a2 ^ g.., g lies inside z2 and a2 inside !z2); k2 & z3 = !z2 & z3 = !z2 ^ a1, so k1 = Dsel ^ !z2 ^ a1
    c.cx(t[2], k2);
    c.cx(a2, k2);
    c.cx(t[2], k1);
    c.cx(a1, k1);
    and_erase(c, a2, a1, t[4]);
    and_erase(c, a1, t[2], t[3]);
    // Dsel on out's wire
    c.cx(t[1], out);
    for i in 2..5 {
        c.x(t[i]);
    }
    c.cx(out, k1);
    c.cx(t[1], out);
    zlin_off(c, t, b);
    if let Some((_, recs, wa, wb)) = w1 {
        w1_conj(c, t, &wa);
        w1_conj(c, b, &wb);
        erase_recs(c, recs);
        w1_conj(c, b, &wb);
        w1_conj(c, t, &wa);
    }
}

/// Conditional (classical bit `m`) phase flip on a & b & d: one AND, fired only when m is set.
fn ccz_if(c: &mut Builder, a: QubitId, b: QubitId, d: QubitId, m: crate::circuit::BitId) {
    c.push_condition(m);
    let q = and_new(c, a, b);
    c.cz(q, d);
    and_erase(c, q, a, b);
    c.pop_condition();
}

/// MBU erase of the choice letter on the reverse tick ((t, b) back at the pre-choice state).
fn fast_choice_erase(c: &mut Builder, t: &[QubitId], b: &[QubitId], out: QubitId, tick: usize) {
    let top = t.len() - 1;
    let m = c.alloc_bit();
    c.hmr(out, m);
    c.release_clean(out);
    // W1: the window compare is only needed for the phase fix, i.e. on shots whose outcome m is 1
    let plain = t0_plain(tick);
    let w1 = (lf_w1() && !plain).then(|| {
        let (wa, wb) = (w1_window(t, tick), w1_window(b, tick));
        c.push_condition(m);
        w1_conj(c, t, &wa);
        w1_conj(c, b, &wb);
        let (w, recs) = w1_chain(c, &wa, &wb);
        w1_conj(c, b, &wb);
        w1_conj(c, t, &wa);
        c.pop_condition();
        (w, recs, wa, wb)
    });
    zlin_on(c, t, b);
    c.x(t[1]);
    c.z_if(t[1], m); // dq ^ 1
    c.x(t[1]);
    for i in 2..5 {
        c.x(t[i]);
    }
    ccz_if(c, t[2], t[3], t[4], m); // !z2 & !z3 & !z4
    for i in 2..5 {
        c.x(t[i]);
    }
    match w1.as_ref().map(|v| v.0) {
        None | Some(Lit::Zero) if plain => {
            if let Some(mh) = T0_M.with(|q| q.get()) {
                // phase of z2 & (!m ^ dq) on shots with outcome 1
                c.cz_if(t[2], mh, m);
                c.cz_if(t[2], t[1], m);
                c.z_if(t[2], m);
            }
        }
        None | Some(Lit::Zero) => c.cz_if(t[2], t[top], m), // z2 & eq
        Some(Lit::One) => {}
        Some(Lit::W(wq, inv)) => {
            // phase of z2 & eq & !w, on shots with m = 1
            c.push_condition(m);
            let q = and_new(c, t[2], t[top]);
            if !inv { c.x(wq); }
            c.cz(q, wq);
            if !inv { c.x(wq); }
            and_erase(c, q, t[2], t[top]);
            c.pop_condition();
        }
    }
    zlin_off(c, t, b);
    if let Some((_, recs, wa, wb)) = w1 {
        c.push_condition(m);
        w1_conj(c, t, &wa);
        w1_conj(c, b, &wb);
        erase_recs(c, recs);
        w1_conj(c, b, &wb);
        w1_conj(c, t, &wa);
        c.pop_condition();
    }
    c.free_bit(m);
}

/// MBU erase of the barrel letters on the reverse tick, from x3 (the target before the barrel):
/// k2 = !t0 & !t1, k1 = !t0 ^ (!t0 & !t1 & t2).
fn fast_k_erase(c: &mut Builder, t: &[QubitId], k1: QubitId, k2: QubitId) {
    c.x(t[0]);
    c.x(t[1]);
    // k1 first, while k2 is still live: k1 = !t0 ^ (k2 & t2), so its phase fix is Z + CZ (no Toffoli)
    let m1 = c.alloc_bit();
    c.hmr(k1, m1);
    c.release_clean(k1);
    c.z_if(t[0], m1);
    c.cz_if(k2, t[2], m1);
    c.free_bit(m1);
    let m2 = c.alloc_bit();
    c.hmr(k2, m2);
    c.release_clean(k2);
    c.cz_if(t[0], t[1], m2);
    c.free_bit(m2);
    c.x(t[1]);
    c.x(t[0]);
}

/// Rail barrel with the sign fill absorbed into re-based reflections (barrel research, scratch barrel_mc/
/// rail_lin_explicit.py): h1 = k1 & S, h2 = k2 & S; rho_0 (k2, minus the pair (1, w-1), done by h2), rho_-2
/// (k1 ^ k2), rho_-3 (k1, minus the no-op pair (w-2, w-1)); 1.5w - 2 Toffoli (even w). Same promise: the e low
/// wires are 0. `LF_RAILLIN=0` keeps [`fast_rail_barrel`]'s sign-fill form.
///
/// `drop0` (forward only; the caller holds an odd result without its bit-0 wire, LF_LOWREL): wire 0 ends as the
/// constant 1, so the last Fredkin that writes it, rho_-3's pair (0, w-3) under k1, needs no Toffoli. When k1 = 1 the
/// partner wire holds the rail's lowest set bit (1) and takes t0; when k1 = 0, t0 already holds that 1. Either way
/// t[w-3] <- t0 ^ t[w-3] ^ 1, and t0 is left holding 1 ^ (k1 & !t[w-3]): it is measured away (phase fix
/// CZ(k1, !t[w-3])) and released here. Returns true when wire 0 was released (the caller only forgets it).
fn lin_rail_barrel(c: &mut Builder, k1: QubitId, k2: QubitId, t: &[QubitId], inverse: bool, drop0: bool) -> bool {
    let w = t.len();
    let drop0 = drop0 && !inverse && w >= 4 && !std::env::var("LF_BARREL_DROP0").is_ok_and(|v| v == "0");
    let mut dropped = false;
    let s = t[w - 1];
    let h1 = and_new(c, k1, s);
    let h2 = and_new(c, k2, s);
    #[derive(Clone, Copy)]
    enum Op {
        Cx(QubitId, usize),
        F(u8, usize, usize),
    }
    let refl = |x: isize| -> Vec<(usize, usize)> {
        (0..w)
            .filter_map(|i| {
                let j = (x - i as isize).rem_euclid(w as isize) as usize;
                (i < j).then_some((i, j))
            })
            .collect()
    };
    let mut ops = vec![Op::Cx(h1, 0), Op::Cx(h2, 1), Op::Cx(h2, w - 1)];
    ops.extend(refl(0).into_iter().filter(|&p| p != (1, w - 1)).map(|(a, b)| Op::F(2, a, b)));
    ops.extend(refl(w as isize - 2).into_iter().map(|(a, b)| Op::F(3, a, b)));
    ops.extend(refl(w as isize - 3).into_iter().filter(|&p| p != (w - 2, w - 1)).map(|(a, b)| Op::F(1, a, b)));
    ops.extend([Op::Cx(h2, w - 2), Op::Cx(h2, w - 1)]);
    if inverse {
        ops.reverse();
    }
    let mut k12 = false; // k2 currently holds k1 ^ k2
    for op in ops {
        match op {
            Op::Cx(h, i) => c.cx(h, t[i]),
            Op::F(kind, a, b) => {
                let want = kind == 3;
                if want != k12 {
                    c.cx(k1, k2);
                    k12 = want;
                }
                let ctrl = if kind == 1 { k1 } else { k2 };
                if drop0 && kind == 1 && (a, b) == (0, w - 3) {
                    c.cx(t[0], t[b]);
                    c.x(t[b]);
                    c.x(t[0]); // now k1 & !t[b]
                    let m = c.alloc_bit();
                    c.hmr(t[0], m);
                    c.x(t[b]);
                    c.cz_if(k1, t[b], m);
                    c.x(t[b]);
                    c.free_bit(m);
                    c.release_clean(t[0]);
                    dropped = true;
                } else {
                    fredkin(c, ctrl, t[a], t[b]);
                }
            }
        }
    }
    if k12 {
        c.cx(k1, k2);
    }
    and_erase(c, h1, k1, t[w - 1]);
    and_erase(c, h2, k2, t[w - 1]);
    dropped
}

/// Rail barrel with the 3-Toffoli sign fill (h = k2 & sg -> t1, t0; h2 = k1 & h -> t2, t0; k1 & sg -> t0).
fn fast_rail_barrel(c: &mut Builder, k1: QubitId, k2: QubitId, t: &[QubitId], inverse: bool, drop0: bool) -> bool {
    if !std::env::var("LF_RAILLIN").is_ok_and(|v| v == "0") {
        return lin_rail_barrel(c, k1, k2, t, inverse, drop0);
    }
    let sg = *t.last().unwrap();
    if inverse {
        rot4(c, k1, k2, t, true);
    }
    let h = and_new(c, k2, sg);
    c.cx(h, t[1]);
    c.cx(h, t[0]);
    let h2 = and_new(c, k1, h);
    c.cx(h2, t[2]);
    c.cx(h2, t[0]);
    c.ccx(k1, sg, t[0]);
    and_erase(c, h2, k1, h);
    and_erase(c, h, k2, sg);
    if !inverse {
        rot4(c, k1, k2, t, false);
    }
    false
}

/// `t <- (t + (-1)^sign * b) / 2` on rails (exact: the sum is even). Widths: t and b at w on entry and exit.
fn rail_add_halve(c: &mut Builder, sign: QubitId, b: &mut Vec<QubitId>, t: &mut Vec<QubitId>) {
    let w = t.len();
    resize(c, t, w + 1);
    resize(c, b, w + 1);
    rail_signed_add(c, sign, b, t);
    resize(c, b, w);
    let low = t.remove(0);
    c.free(low);
}

/// Inverse of [`rail_add_halve`]: `t <- 2 t - (-1)^sign * b`.
fn rail_double_sub(c: &mut Builder, sign: QubitId, b: &mut Vec<QubitId>, t: &mut Vec<QubitId>) {
    let w = t.len();
    let low = c.alloc_qubit();
    t.insert(0, low);
    resize(c, b, w + 1);
    c.x(sign);
    rail_signed_add(c, sign, b, t);
    c.x(sign);
    resize(c, b, w);
    resize(c, t, w);
}

/// [`pp_sign_into`] from the two bit-1 wires.
fn pp_sign_into1(c: &mut Builder, t1: QubitId, b1: QubitId, q: QubitId) {
    c.cx(t1, q);
    c.cx(b1, q);
}

/// Forced ping-pong sign for the next step: 1 (subtract) iff t[1] != b[1].
fn pp_sign_into(c: &mut Builder, t: &[QubitId], b: &[QubitId], q: QubitId) {
    c.cx(t[1], q);
    c.cx(b[1], q);
}

/// AND into a fresh qubit; and its measurement-based uncompute.
#[track_caller]
fn and_new(c: &mut Builder, a: QubitId, b: QubitId) -> QubitId {
    let q = c.alloc_qubit();
    c.ccx(a, b, q);
    q
}
fn and_erase(c: &mut Builder, q: QubitId, a: QubitId, b: QubitId) {
    let m = c.alloc_bit();
    c.hmr(q, m);
    c.cz_if(a, b, m);
    c.free_bit(m);
    c.release_clean(q);
}

/// sign2 fourth-step choice into `out` (xor). dq = t[1] ^ b[1] (1 -> t + b is the deep candidate; the deep
/// sign bit is !dq). The deep candidate D (sc = D mod 32) is taken iff it is admissible (D mod 32 != 0, i.e.
/// e = v2(D) - 1 <= 3) and NOT (e == 1 and sign(t) == sign(+-b)): an e = 1 deep step that adds equal-signed
/// magnitudes grows the rail. a2 = [D == 0 mod 32] and g = [e == 1 and equal signs] are exclusive (g needs
/// sc[2] = 1), so deep = 1 ^ a2 ^ g and out ^= dq ^ deep. Needs t, b at width >= 6 (callers sign-extend).
fn choice_xor(c: &mut Builder, t: &[QubitId], b: &[QubitId], out: QubitId) {
    let (tt, bt) = (*t.last().unwrap(), *b.last().unwrap());
    let dq = c.alloc_qubit();
    c.cx(t[1], dq);
    c.cx(b[1], dq);
    let sc = c.alloc_qubits(5);
    c.cx_pairs(&t[..5], &sc);
    let bl = c.alloc_qubits(5);
    c.cx_pairs(&b[..5], &bl);
    // sc = (t + (-1)^{!dq} b) mod 32
    c.x(dq);
    signed_add(c, dq, &bl, &sc);
    c.x(dq);
    // a2 = (sc2 == sc3 == sc4 == 0)
    for &q in &sc[2..5] {
        c.x(q);
    }
    let a1 = and_new(c, sc[2], sc[3]);
    let a2 = and_new(c, a1, sc[4]);
    c.cx(dq, out);
    c.cx(a2, out);
    c.x(out);
    and_erase(c, a2, a1, sc[4]);
    and_erase(c, a1, sc[2], sc[3]);
    for &q in &sc[2..5] {
        c.x(q);
    }
    if !rule_v0() {
        // equal signs: !(t_top ^ b_top ^ !dq) = t_top ^ b_top ^ dq, held on dq's wire
        c.cx(tt, dq);
        c.cx(bt, dq);
        let g = and_new(c, dq, sc[2]);
        c.cx(g, out);
        and_erase(c, g, dq, sc[2]);
        c.cx(bt, dq);
        c.cx(tt, dq);
    }
    // undo sc: sc -= (-1)^{!dq} b  ==  sc += (-1)^{dq} b
    signed_add(c, dq, &bl, &sc);
    c.cx_pairs(&b[..5], &bl);
    c.free_vec(&bl);
    c.cx_pairs(&t[..5], &sc);
    c.free_vec(&sc);
    c.cx(t[1], dq);
    c.cx(b[1], dq);
    c.free(dq);
}

/// Barrel bits of a target with e = v2(t) <= 3 (xor into k1, k2):
/// k2 = (e >= 2) = !t0 & !t1 ; k1 = (e in {1,3}) = !t0 & (t1 | !t2) = !t0 & !(!t1 & t2).
fn barrel_bits_xor(c: &mut Builder, t: &[QubitId], k1: QubitId, k2: QubitId) {
    c.x(t[0]);
    c.x(t[1]);
    c.ccx(t[0], t[1], k2);
    let u = and_new(c, t[1], t[2]);
    c.x(u);
    c.ccx(t[0], u, k1);
    c.x(u);
    and_erase(c, u, t[1], t[2]);
    c.x(t[1]);
    c.x(t[0]);
}

/// Fredkin pairs of the 4-way cyclic rotation out[i] = in[(i + e) mod n], e = k1 + 2 k2, as three controlled
/// reflections rho_x: i -> x - i (two reflections compose to a rotation): rho_1 on e in {1,3} (ctrl k1),
/// rho_0 on e in {1,2} (ctrl k1 ^ k2, held on k2), rho_-2 on e in {2,3} (ctrl k2). 1.5n - 2 Fredkins instead
/// of the 2n - 3 of two nested shift stages (red-team construction, scratch redteam_rot/rotnet.py).
fn refl4_pairs(n: usize) -> [Vec<(usize, usize)>; 3] {
    let refl = |x: isize| -> Vec<(usize, usize)> {
        (0..n)
            .filter_map(|i| {
                let j = (x - i as isize).rem_euclid(n as isize) as usize;
                (i < j).then_some((i, j))
            })
            .collect()
    };
    [refl(1), refl(0), refl(-2)]
}

/// The 4-way rotation of `t` by e = k1 + 2 k2 (inverse: by -e).
fn rot4(c: &mut Builder, k1: QubitId, k2: QubitId, t: &[QubitId], inverse: bool) {
    if SKIP_ROT4.with(|s| s.get()) {
        return;
    }
    let [r1, r0, rm2] = refl4_pairs(t.len());
    let stages: [(&Vec<(usize, usize)>, u8); 3] = [(&r1, 1), (&r0, 2), (&rm2, 3)];
    let order: Vec<usize> = if inverse { vec![2, 1, 0] } else { vec![0, 1, 2] };
    for s in order {
        let (pairs, kind) = stages[s];
        let ctrl = if kind == 1 { k1 } else { k2 };
        if kind == 2 {
            c.cx(k1, k2);
        }
        for &(a, b) in pairs {
            fredkin(c, ctrl, t[a], t[b]);
        }
        if kind == 2 {
            c.cx(k1, k2);
        }
    }
}

/// Rail barrel: arithmetic shift right by e = k1 + 2 k2 (the e low wires are 0): the sign goes into the e low
/// wires, then one cyclic 4-way rotation carries them to the top. 1.5w + 2 Toffoli (inverse: shift left).
fn rail_barrel(c: &mut Builder, k1: QubitId, k2: QubitId, t: &[QubitId], inverse: bool) {
    let sg = *t.last().unwrap();
    if inverse {
        rot4(c, k1, k2, t, true);
    }
    let a = and_new(c, k1, k2);
    c.cx(k1, a);
    c.cx(k2, a); // a = [e >= 1]
    c.ccx(a, sg, t[0]);
    c.cx(k2, a);
    c.cx(k1, a); // a = [e == 3]
    c.ccx(k2, sg, t[1]);
    c.ccx(a, sg, t[2]);
    and_erase(c, a, k1, k2);
    if !inverse {
        rot4(c, k1, k2, t, false);
    }
}

/// Bits [lo, hi) of m * (f - 1) for m in [0, 8) as XORs of the monomials m0, m1, m2, m0m1, m0m2, m1m2, m0m1m2
/// (algebraic normal form; index = monomial bit mask).
fn fold_anf(lo: usize, hi: usize) -> Vec<Vec<usize>> {
    let fm1: u128 = (1u128 << 32) + 976;
    (lo..hi)
        .map(|b| {
            (1..8usize)
                .filter(|&mask| {
                    let mut coef = 0u128;
                    for sub in 0..8usize {
                        if sub & !mask == 0 {
                            let mv = (0..3).filter(|u| sub >> u & 1 == 1).map(|u| 1u128 << u).sum::<u128>();
                            coef ^= (mv * fm1) >> b & 1;
                        }
                    }
                    coef == 1
                })
                .collect()
        })
        .collect()
}

/// Put (parity of `list`) ^ comp ^ carry on one wire for an AND control; returns the wire. With an empty
/// list the carry wire itself is used (X'd when comp). [`v_off`] undoes it.
fn v_on(c: &mut Builder, list: &[QubitId], comp: bool, ci: Option<QubitId>) -> QubitId {
    let h = match list.split_first() {
        Some((&h, rest)) => {
            for &q in rest {
                c.cx(q, h);
            }
            if let Some(ci) = ci {
                c.cx(ci, h);
            }
            h
        }
        None => ci.expect("live carry"),
    };
    if comp {
        c.x(h);
    }
    h
}
fn v_off(c: &mut Builder, list: &[QubitId], comp: bool, ci: Option<QubitId>) {
    match list.split_first() {
        Some((&h, rest)) => {
            if comp {
                c.x(h);
            }
            if let Some(ci) = ci {
                c.cx(ci, h);
            }
            for &q in rest {
                c.cx(q, h);
            }
        }
        None => {
            if comp {
                c.x(ci.unwrap());
            }
        }
    }
}

/// Gidney ripple `acc += addend + cin (mod 2^len)` where addend bit i is the parity of the wires `add[i]`
/// (possibly none). Carries that are provably 0 are skipped; carries are measurement-uncomputed.
fn ladder_parity_add(c: &mut Builder, acc: &[QubitId], add: &[Vec<QubitId>], cin: Option<QubitId>) {
    let n = acc.len();
    let mut y28h = Y28_HOOK.with(|x| x.take());
    let mut carry: Vec<Option<QubitId>> = vec![None; n];
    carry[0] = cin;
    for i in 0..n - 1 {
        let ci = carry[i];
        if ci.is_none() && add[i].is_empty() {
            continue;
        }
        if let Some(ci) = ci {
            c.cx(ci, acc[i]);
        }
        let v = v_on(c, &add[i], false, ci);
        if i + 2 == n {
            // the carry into the top position is used once, for that position's sum bit: XOR it straight into
            // the top wire (one CCX, nothing to erase) instead of holding it on a carry wire
            c.ccx(acc[i], v, acc[n - 1]);
            v_off(c, &add[i], false, ci);
            if let Some(ci) = ci {
                c.cx(ci, acc[n - 1]);
                c.cx(ci, acc[i]);
            }
            continue;
        }
        let t = and_new(c, acc[i], v);
        v_off(c, &add[i], false, ci);
        if let Some(ci) = ci {
            c.cx(ci, t);
            c.cx(ci, acc[i]);
        }
        carry[i + 1] = Some(t);
        y28_apply(c, &mut y28h, i + 1, t);
    }
    assert!(y28h.is_none(), "y28: the kept bit's boundary carry is on no wire of this ladder");
    for i in (0..n).rev() {
        let ci = carry[i];
        if i + 1 < n {
            if let Some(next) = carry[i + 1] {
                if let Some(ci) = ci {
                    c.cx(ci, next);
                    c.cx(ci, acc[i]);
                }
                let v = v_on(c, &add[i], false, ci);
                and_erase(c, next, acc[i], v);
                v_off(c, &add[i], false, ci);
                if let Some(ci) = ci {
                    c.cx(ci, acc[i]);
                }
            }
        }
        for &q in &add[i] {
            c.cx(q, acc[i]);
        }
        if let Some(ci) = ci {
            c.cx(ci, acc[i]);
        }
    }
}

/// `out ^= carry_out(acc + addend + cin)` (addend bits: parity of `add[i]`, complemented when `comp`);
/// acc unchanged; Gidney carries, measurement-uncomputed.
fn carry_out_parity_xor(c: &mut Builder, acc: &[QubitId], add: &[Vec<QubitId>], comp: bool, cin: QubitId, out: Option<QubitId>) {
    let n = acc.len();
    // Phase-only form: the top carry is never built (see `carry_out_xor`): one CZ on the two AND inputs of the
    // top position and the phase (-1)^(NOT carry[n - 1]).
    let m = if out.is_none() && n >= 1 { n - 1 } else { n };
    let mut carry = vec![cin];
    for i in 0..m {
        let ci = carry[i];
        c.cx(ci, acc[i]);
        let v = v_on(c, &add[i], comp, Some(ci));
        let t = and_new(c, acc[i], v);
        v_off(c, &add[i], comp, Some(ci));
        c.cx(ci, t);
        c.cx(ci, acc[i]);
        carry.push(t);
    }
    match out {
        Some(out) => c.cx(carry[n], out),
        None => {
            let ci = carry[m];
            if m < n {
                c.cx(ci, acc[m]);
                let v = v_on(c, &add[m], comp, Some(ci));
                c.cz(acc[m], v);
                v_off(c, &add[m], comp, Some(ci));
                c.cx(ci, acc[m]);
            }
            c.x(ci);
            c.z_if(ci, NO_BIT);
            c.x(ci);
        }
    }
    for i in (0..m).rev() {
        let (ci, t) = (carry[i], carry[i + 1]);
        c.cx(ci, t);
        c.cx(ci, acc[i]);
        let v = v_on(c, &add[i], comp, Some(ci));
        and_erase(c, t, acc[i], v);
        v_off(c, &add[i], comp, Some(ci));
        c.cx(ci, acc[i]);
    }
}

/// [`ladder_parity_add`] under the walk cap, split recursively: when the ladder does not fit, the low chunk (sized to
/// the room) goes first with its carry-out kept, the rest (recursively) takes it as carry-in, and each kept carry is
/// erased exactly as NOT carry_out(acc_low_new + NOT addend_low + NOT cin) (MBU-halved unless LF_SPLIT_MBU=0).
/// `LF_LPA_DENSE=1`: [`lpa_capped`] fills the room with the low chunk when the room is short (< 8) instead of
/// falling back to a full ladder that overruns the cap (exact: the same split, smaller chunks).
fn lpa_dense() -> bool {
    std::env::var("LF_LPA_DENSE").is_ok_and(|v| v == "1")
}
/// `LF_LPA_DENSE_ALL=1`: ... at every room, not only when it is short: the low chunk is the room (room - 1 with
/// no carry-in) instead of room - 4, so a fold ladder of n bits fits beside r free wires when n <= ~r (r + 1) / 2.
fn lpa_dense_all() -> bool {
    std::env::var("LF_LPA_DENSE_ALL").is_ok_and(|v| v == "1")
}
fn ladder_parity_add_capped(c: &mut Builder, acc: &[QubitId], add: &[Vec<QubitId>]) {
    lpa_capped(c, acc, add, None);
}
fn lpa_capped(c: &mut Builder, acc: &[QubitId], add: &[Vec<QubitId>], cin: Option<QubitId>) {
    let n = acc.len();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    let off = std::env::var("LF_RAIL_SPLIT").is_ok_and(|v| v == "0");
    // the parity ladder holds n - 2 carries (its top carry goes straight into the top sum wire)
    if off || n <= room + 1 + split_tight() as usize {
        ladder_parity_add(c, acc, add, cin);
        return;
    }
    // tight: the minimal low chunk when it fits beside its kept carry; otherwise the room-sized low chunk (recursive)
    let tight = split_tight() && n - room + 2 <= room;
    let mut l = if tight { n - room - 1 } else { room.saturating_sub(4) };
    if !tight && (l < 4 || lpa_dense_all()) && lpa_dense() {
        // low room: the low chunk fills the room exactly (its l - 1 ladder carries + the kept carry; its erase holds
        // l - 1 carries + the inverted carry-in, allocated when there is none). Each level costs one kept carry, so
        // room r covers r (r + 1) / 2 bits; the erase compares only its own chunk, so the Toffoli count is the same.
        l = room.saturating_sub(cin.is_none() as usize).min(n - 2);
    }
    if (!tight && l < 4 && !(lpa_dense() && l >= 1)) || l + 1 >= n {
        ladder_parity_add(c, acc, add, cin);
        return;
    }
    let cq = c.alloc_qubit();
    let mut lo = acc[..l].to_vec();
    lo.push(cq);
    let mut lo_add = add[..l].to_vec();
    lo_add.push(vec![]);
    ladder_parity_add(c, &lo, &lo_add, cin);
    lpa_capped(c, &acc[l..], &add[l..], Some(cq));
    let ncin = match cin {
        Some(q) => {
            c.x(q);
            q
        }
        None => {
            let o = c.alloc_qubit();
            c.x(o);
            o
        }
    };
    let q0 = pmark(c);
    if split_mbu() {
        let m = c.alloc_bit();
        c.hmr(cq, m);
        c.release_clean(cq);
        c.push_condition(m);
        carry_out_parity_xor(c, &acc[..l], &add[..l], true, ncin, None);
        c.pop_condition();
        c.free_bit(m);
    } else {
        carry_out_parity_xor(c, &acc[..l], &add[..l], true, ncin, Some(cq));
        c.x(cq);
        c.free(cq);
    }
    pacc(c, "split.fold_erase", q0);
    match cin {
        Some(q) => c.x(q),
        None => {
            c.x(ncin);
            c.free(ncin);
        }
    }
}

/// Controlled modular scaling of a payload by 2^-e (inverse: 2^e), e = k1 + 2 k2 in [0, 3]. With p == -1 and
/// f == 1 (mod 8): m = P mod 2^e gives P 2^-e = rotr_e(P - m (f - 1)) (mod p); f - 1 = 2^32 + 61 * 16 leaves
/// m in bits 0..2, and the rotation carries it to the top. One fold ladder over bits [4, 4 + fs) whose addend
/// bits are monomials of m, then the 4-way reflection rotation.
fn cmod_barrel(c: &mut Builder, k1: QubitId, k2: QubitId, p: &[QubitId], inverse: bool) {
    let extra: usize = std::env::var("LF_FOLD_EXTRA").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let (lo, hi) = (4, (4 + go_fs("GO_FG_P") + extra).min(N));
    let t = and_new(c, k1, k2);
    if inverse {
        rot4(c, k1, k2, p, true);
    }
    c.cx(k1, t);
    c.cx(k2, t);
    let m0 = and_new(c, t, p[0]); // [e >= 1] & p0
    c.cx(k2, t);
    c.cx(k1, t);
    let m1 = and_new(c, k2, p[1]);
    let m2 = and_new(c, t, p[2]);
    let m01 = and_new(c, m0, m1);
    let m02 = and_new(c, m0, m2);
    let m12 = and_new(c, m1, m2);
    let m012 = and_new(c, m01, m2);
    let mono = [m0, m0, m1, m01, m2, m02, m12, m012]; // index = monomial mask (0 unused)
    let add: Vec<Vec<QubitId>> = fold_anf(lo, hi).into_iter().map(|ms| ms.into_iter().map(|k| mono[k]).collect()).collect();
    let acc = &p[lo..hi];
    if inverse {
        ladder_parity_add_capped(c, acc, &add);
    } else {
        c.x_all(acc);
        ladder_parity_add_capped(c, acc, &add);
        c.x_all(acc);
    }
    and_erase(c, m012, m01, m2);
    and_erase(c, m12, m1, m2);
    and_erase(c, m02, m0, m2);
    and_erase(c, m01, m0, m1);
    and_erase(c, m2, t, p[2]);
    and_erase(c, m1, k2, p[1]);
    c.cx(k1, t);
    c.cx(k2, t);
    and_erase(c, m0, t, p[0]);
    c.cx(k2, t);
    c.cx(k1, t);
    if !inverse {
        rot4(c, k1, k2, p, false);
    }
    and_erase(c, t, k1, k2);
}

// ---- LF_MERGED: last add-halve cell + payload barrel as one Montgomery step (scratch paycell/merged.py) ----
//
// Forward:  T <- (T + (-1)^sg S) 2^-k,  k = 1 + e, e = k1 + 2 k2.  In the sg-complemented frame the production
// chunked adder leaves A (256 bits) and its overflow ov; V = A + ov f == T +- S (mod p).  With p == -1 and
// f == 1 (mod 16), mu = V mod 2^k = (A + ov) mod 2^k and Y = rotr_k(V - mu (f - 1)): one fold ladder over bits
// [0, MW) adds ov (bit 0) and (f - 1)(u - 15) (bits 4..), u = n + 15, n = ov -+ mu in [-15, 16] (5 bits); the
// addend bits are ANF monomials of u.  mu's bits are read off the ladder's own low sum bits (hook after bit 3).
// The overflow is erased exactly from the top ripple's carry frame when the fold fits beside that ripple (exact
// route, [`merged_split`], as the retained-prebias cell does) and otherwise with the production cell's flag
// compare; the rotation by 1 is free (swaps), the rotation by e is the 4-way reflection network.  Reverse: the
// exact inverse map T <- 2^k T - (-1)^sg S (mu = the rotated-in low bits, gated copies erased from the result's
// low bits, S_low and ov).  Used for ticks t < LF_MERGED_MAX (default LF_TIE_FROM: no tie-safe mode) whose
// fold phase fits under the walk cap ([`merged_fits`]); other ticks keep the cell + [`cmod_barrel`].

/// `LF_MERGED=1`: use the merged op on ticks where it fits ([`merged_fits`]).
fn lf_merged() -> bool {
    std::env::var("LF_MERGED").is_ok_and(|v| v == "1")
}
/// Merged fold window (bits [0, MW) of the payload); the constant is < 2^37, so 24 bits of escape margin.
fn merged_win() -> usize {
    static W: OnceLock<usize> = OnceLock::new();
    *W.get_or_init(|| std::env::var("LF_MERGED_WIN").ok().and_then(|v| v.parse().ok()).unwrap_or(61))
}
const M_OFF: i128 = 15;

/// Linear form over wires (XOR of the wires, XOR a constant).
#[derive(Clone, Debug, Default)]
struct Lin {
    w: Vec<QubitId>,
    one: bool,
}
impl Lin {
    fn of(qs: &[QubitId]) -> Lin {
        let mut l = Lin::default();
        for &q in qs {
            l = l.x(&Lin { w: vec![q], one: false });
        }
        l
    }
    fn k(b: bool) -> Lin {
        Lin { w: vec![], one: b }
    }
    fn x(&self, o: &Lin) -> Lin {
        let mut w = self.w.clone();
        for &q in &o.w {
            if let Some(p) = w.iter().position(|&r| r == q) {
                w.remove(p);
            } else {
                w.push(q);
            }
        }
        Lin { w, one: self.one ^ o.one }
    }
}
fn lin_on(c: &mut Builder, l: &Lin, h: QubitId) {
    for &q in &l.w {
        if q != h {
            c.cx(q, h);
        }
    }
    if l.one {
        c.x(h);
    }
}
fn lin_off(c: &mut Builder, l: &Lin, h: QubitId) {
    if l.one {
        c.x(h);
    }
    for &q in l.w.iter().rev() {
        if q != h {
            c.cx(q, h);
        }
    }
}
/// Host two forms on wires (each parity on one of its own wires) so that the second hosting reads no wire the
/// first one changed: the first form is hosted on a wire the second does not contain. Returns
/// (first_is_a, host_a, host_b).
fn lin_hosts(a: &Lin, b: &Lin) -> (bool, QubitId, QubitId) {
    assert!(!a.w.is_empty() && !b.w.is_empty(), "AND of a constant form");
    if let Some(&ha) = a.w.iter().find(|q| !b.w.contains(q)) {
        (true, ha, b.w[0])
    } else {
        let &hb = b.w.iter().find(|q| !a.w.contains(q)).expect("AND of two equal forms");
        (false, a.w[0], hb)
    }
}
fn lin_pair_on(c: &mut Builder, a: &Lin, b: &Lin) -> (QubitId, QubitId) {
    let (af, ha, hb) = lin_hosts(a, b);
    if af {
        lin_on(c, a, ha);
        lin_on(c, b, hb);
    } else {
        lin_on(c, b, hb);
        lin_on(c, a, ha);
    }
    (ha, hb)
}
fn lin_pair_off(c: &mut Builder, a: &Lin, b: &Lin) {
    let (af, ha, hb) = lin_hosts(a, b);
    if af {
        lin_off(c, b, hb);
        lin_off(c, a, ha);
    } else {
        lin_off(c, a, ha);
        lin_off(c, b, hb);
    }
}
/// AND of two linear forms into a fresh wire (one Toffoli).
fn lin_and(c: &mut Builder, a: &Lin, b: &Lin) -> QubitId {
    let q = c.alloc_qubit();
    let (ha, hb) = lin_pair_on(c, a, b);
    c.ccx(ha, hb, q);
    lin_pair_off(c, a, b);
    q
}
/// Measurement-based erasure of a wire holding AND(a, b) (zero Toffoli).
fn lin_and_erase(c: &mut Builder, q: QubitId, a: &Lin, b: &Lin) {
    let m = c.alloc_bit();
    c.hmr(q, m);
    let (ha, hb) = lin_pair_on(c, a, b);
    c.cz_if(ha, hb, m);
    lin_pair_off(c, a, b);
    c.free_bit(m);
    c.release_clean(q);
}
fn lin_xor_into(c: &mut Builder, l: &Lin, t: QubitId) {
    for &q in &l.w {
        assert_ne!(q, t);
        c.cx(q, t);
    }
    if l.one {
        c.x(t);
    }
}

/// AND records of the merged op's helper wires, erased in reverse order.
type Recs = Vec<(QubitId, Lin, Lin)>;
fn m_and(c: &mut Builder, recs: &mut Recs, a: Lin, b: Lin) -> Lin {
    let q = lin_and(c, &a, &b);
    recs.push((q, a, b));
    Lin::of(&[q])
}
fn m_erase(c: &mut Builder, recs: &mut Recs, from: usize) {
    while recs.len() > from {
        let (q, a, b) = recs.pop().unwrap();
        lin_and_erase(c, q, &a, &b);
    }
}

/// ANF of the merged addend: bit b of (f - 1)(u - 15) mod 2^MW over the 5 bits of u, as monomial masks
/// (0 = the constant 1); and the AND construction order (m, a, b) of the nonlinear monomials (m = a | b).
fn merged_tables() -> &'static (Vec<Vec<usize>>, Vec<(usize, usize, usize)>) {
    static T: OnceLock<(Vec<Vec<usize>>, Vec<(usize, usize, usize)>)> = OnceLock::new();
    T.get_or_init(|| {
        let mw = merged_win();
        let g16: i128 = (1i128 << 32) + 976;
        let modw: i128 = 1i128 << mw;
        let vals: Vec<i128> = (0..32i128).map(|u| (g16 * (u - M_OFF)).rem_euclid(modw)).collect();
        let table: Vec<Vec<usize>> = (0..mw)
            .map(|b| {
                let mut a: Vec<u8> = vals.iter().map(|v| (v >> b & 1) as u8).collect();
                for i in 0..5 {
                    for x in 0..32 {
                        if x >> i & 1 == 1 {
                            a[x] ^= a[x ^ (1 << i)];
                        }
                    }
                }
                (0..32).filter(|&x| a[x] == 1).collect()
            })
            .collect();
        assert!(table[..4].iter().all(|r| r.is_empty()), "(f - 1) * n has 4 zero low bits");
        let mut need: Vec<usize> = table.iter().flatten().copied().filter(|m| m.count_ones() >= 2).collect();
        need.sort_by_key(|&m| (m.count_ones(), m));
        need.dedup();
        let mut avail: Vec<usize> = vec![1, 2, 4, 8, 16];
        let mut plan = Vec::new();
        for m in need {
            let mut pick = None;
            'o: for &a in &avail {
                for &b in &avail {
                    if a | b == m && a != m && b != m {
                        pick = Some((a, b));
                        break 'o;
                    }
                }
            }
            let (a, b) = pick.expect("monomial plan needs an intermediate");
            plan.push((m, a, b));
            avail.push(m);
            avail.sort();
        }
        (table, plan)
    })
}

/// u = x + ov + 15*sg, exactly, with four temporary ANDs.
/// Rewrite as (x + ov - sg) + 16*sg: a conditional four-bit increment/decrement.
/// The caller erases these helpers through the existing reverse-order MBU records.
fn m_u_build(c: &mut Builder, recs: &mut Recs, x: &[Lin; 4], ov: &Lin, sg: &Lin) -> [Lin; 5] {
    let mut carry = ov.x(sg);
    let mut u = Vec::with_capacity(5);
    for bit in x {
        u.push(bit.x(&carry));
        carry = m_and(c, recs, bit.x(sg), carry);
    }
    u.push(sg.x(&carry));
    u.try_into().unwrap()
}

/// Bits [0, MW) of (f - 1)(u - 15) mod 2^MW from the 5 bits of u with 10 ANDs (the ANF monomial route takes 19; 10
/// is the rank bound: the 16 distinct output bits span 10 dimensions beyond the affine functions of u). Written
/// over any XOR/AND algebra `T`, so the same code emits the wire forms and checks itself on truth tables.
/// With n = u - 15 in [-15, 16] and (f - 1) = 2^32 + 16 * 61:
///   * bits 4..14 = 61 n mod 2^10 = (64 u + (109 - 3u)) mod 2^10, and 109 - 3u = 3 v + 16 with v = NOT u = 31 - u,
///     in [16, 109]: bits 4..10 are the low 6 bits of 3v + 16 (ripple v + 2v, carries c2 = v0 v1 = 1 ^ u0 ^ u1 ^ u0u1
///     and three MAJ; the + 16 is free), and bits 10..14 are (u + !u4) mod 16 (bit 6 of 109 - 3u is [u <= 15]);
///   * bits 14..32 = s = [n < 0] = !u4 & !(u0 u1 u2 u3) (sign extension of 61 n);
///   * bits 32.. = n - s: (u + !s) mod 16, then 1 ^ u4 ^ u0u1u2u3, then s. The carries of u + !s are
///     !s & p = p ^ (!u4 & p) ^ s ^ !u4 for a prefix product p of u0..u2: XORs of ANDs already made.
fn addend10<T: Clone>(u: &[T; 5], one: &T, zero: &T, mw: usize, x: &dyn Fn(&T, &T) -> T, and: &mut dyn FnMut(T, T) -> T) -> Vec<T> {
    let p1 = and(u[0].clone(), u[1].clone());
    let p2 = and(p1.clone(), u[2].clone());
    let m15 = and(p2.clone(), u[3].clone());
    let nu4 = x(&u[4], one);
    let s = x(&nu4, &and(nu4.clone(), m15.clone()));
    let d1 = and(nu4.clone(), u[0].clone());
    let d2 = and(nu4.clone(), p1.clone());
    let d3 = and(nu4.clone(), p2.clone());
    let v: Vec<T> = u.iter().map(|l| x(l, one)).collect();
    let c2 = x(&x(&x(one, &u[0]), &u[1]), &p1);
    let c3 = x(&and(x(&v[2], &c2), x(&v[1], &c2)), &c2);
    let c4 = x(&and(x(&v[3], &c3), x(&v[2], &c3)), &c3);
    let c5 = x(&and(x(&v[4], &c4), x(&v[3], &c4)), &c4);
    // 3v + 16, bits 0..6
    let b4 = x(&x(&v[4], &v[3]), &c4);
    let low = [v[0].clone(), x(&v[1], &v[0]), x(&x(&v[2], &v[1]), &c2), x(&x(&v[3], &v[2]), &c3), x(&b4, one), x(&x(&v[4], &c5), &b4)];
    let sn = x(&s, &nu4); // !u4 & u0u1u2u3
    let e = [x(&s, one), x(&x(&u[0], &d1), &sn), x(&x(&p1, &d2), &sn), x(&x(&p2, &d3), &sn)];
    let dd = [nu4.clone(), d1, d2, d3];
    (0..mw)
        .map(|b| match b {
            0..=3 => zero.clone(),
            4..=9 => low[b - 4].clone(),
            10..=13 => x(&u[b - 10], &dd[b - 10]),
            14..=31 => s.clone(),
            32..=35 => x(&u[b - 32], &e[b - 32]),
            36 => x(&x(&u[4], one), &m15),
            _ => s.clone(),
        })
        .collect()
}

/// `LF_ADDEND=anf` keeps the ANF monomial route of [`m_addend`] (19 ANDs); default: [`addend10`].
fn lf_addend10() -> bool {
    static A: OnceLock<bool> = OnceLock::new();
    *A.get_or_init(|| {
        if std::env::var("LF_ADDEND").is_ok_and(|v| v == "anf") {
            return false;
        }
        // self-check on truth tables over the 32 values of u (bit i of a table = the value at u = i)
        let mw = merged_win();
        let ut: [u32; 5] = std::array::from_fn(|i| (0..32u32).filter(|v| v >> i & 1 == 1).map(|v| 1u32 << v).sum());
        let mut n_and = 0usize;
        let got = addend10(&ut, &u32::MAX, &0u32, mw, &|a, b| a ^ b, &mut |a, b| {
            n_and += 1;
            a & b
        });
        let g16: i128 = (1i128 << 32) + 976;
        for b in 0..mw {
            let want: u32 = (0..32i128).filter(|&v| (g16 * (v - M_OFF)).rem_euclid(1i128 << mw) >> b & 1 == 1).map(|v| 1u32 << v).sum();
            assert_eq!(got[b], want, "addend10 bit {b}");
        }
        assert_eq!(n_and, 10);
        true
    })
}

/// The nonlinear monomials of u (ANDs into `recs`) and the addend forms of bits [0, MW): bit 0 = ov, 1..3 = 0.
fn m_addend(c: &mut Builder, recs: &mut Recs, u: &[Lin; 5], ov: &Lin) -> Vec<Lin> {
    if lf_addend10() {
        let mut add = addend10(u, &Lin::k(true), &Lin::k(false), merged_win(), &|a: &Lin, b: &Lin| a.x(b), &mut |a: Lin, b: Lin| m_and(c, recs, a, b));
        add[0] = ov.clone();
        return add;
    }
    let (table, plan) = merged_tables();
    let mut mono: Vec<Option<Lin>> = vec![None; 32];
    for i in 0..5 {
        mono[1 << i] = Some(u[i].clone());
    }
    for &(m, a, b) in plan {
        let q = m_and(c, recs, mono[a].clone().unwrap(), mono[b].clone().unwrap());
        mono[m] = Some(q);
    }
    table
        .iter()
        .enumerate()
        .map(|(b, row)| {
            if b == 0 {
                return ov.clone();
            }
            row.iter().fold(Lin::k(false), |acc, &m| if m == 0 { acc.x(&Lin::k(true)) } else { acc.x(mono[m].as_ref().unwrap()) })
        })
        .collect()
}

/// The merged step's shared core with 13 ANDs (the 4 of [`m_u_build`] plus the 10 of [`addend10`] before): bits
/// [0, MW) of (f - 1) n, n = ov + (2 sg - 1) y, straight from the gated mu bits y (4 forms), sg and ov. 13 is the rank
/// bound: the 16 distinct bits span 13 dimensions beyond the affine functions of (y, sg, ov), and every AND of a
/// 13-AND circuit must lie in that span, so the circuit was found by closing the affine forms under products that
/// stay inside it. Masks are over [1, y0, y1, y2, y3, sg, ov, g0..g12]; the last AND is the sign-extension form s.
const CORE13_GATES: [(u32, u32); 13] = [
    (0x2, 0x60),
    (0x24, 0x86),
    (0x8, 0x1e0),
    (0xec, 0x10c),
    (0x18a, 0x4ae),
    (0x4a, 0xb8a),
    (0xb6, 0xc28),
    (0x8, 0x20e4),
    (0x9c8, 0x2038),
    (0x4, 0xa3d8),
    (0x18, 0xa3c0),
    (0xd24, 0x8208),
    (0x21496, 0x21),
];
/// Forms of bits 4..9, 10..13, s (bits 14..31 and 37..), 32..35, 36.
const CORE13_OUT: [u32; 16] = [
    0x42,
    0x86,
    0x1c8,
    0xd2de8,
    0xa82cc,
    0xbc0dc,
    0x3a3a2,
    0xa1410,
    0xa1210,
    0xa0008,
    0x80000,
    0x80042,
    0x1b7b2,
    0xc998a,
    0xc8218,
    0x90000,
];
fn core13<T: Clone>(y: &[T; 4], sg: &T, ov: &T, one: &T, zero: &T, mw: usize, x: &dyn Fn(&T, &T) -> T, and: &mut dyn FnMut(T, T) -> T) -> Vec<T> {
    let mut basis: Vec<T> = vec![one.clone(), y[0].clone(), y[1].clone(), y[2].clone(), y[3].clone(), sg.clone(), ov.clone()];
    let comb = |basis: &Vec<T>, m: u32| -> T {
        let mut acc = zero.clone();
        for (i, b) in basis.iter().enumerate() {
            if m >> i & 1 == 1 {
                acc = x(&acc, b);
            }
        }
        acc
    };
    for &(l, r) in CORE13_GATES.iter() {
        let g = and(comb(&basis, l), comb(&basis, r));
        basis.push(g);
    }
    let o: Vec<T> = CORE13_OUT.iter().map(|&m| comb(&basis, m)).collect();
    (0..mw)
        .map(|b| match b {
            0..=3 => zero.clone(),
            4..=13 => o[b - 4].clone(),
            14..=31 => o[10].clone(),
            32..=36 => o[b - 21].clone(),
            _ => o[10].clone(),
        })
        .collect()
}

/// `LF_CORE=old` (or `LF_ADDEND=anf`) keeps [`m_u_build`] + [`m_addend`] (14 ANDs); default: [`core13`], checked here
/// against the arithmetic on all 64 values of (y, sg, ov).
fn lf_core13() -> bool {
    static A: OnceLock<bool> = OnceLock::new();
    *A.get_or_init(|| {
        if std::env::var("LF_CORE").is_ok_and(|v| v == "old") || std::env::var("LF_ADDEND").is_ok_and(|v| v == "anf") {
            return false;
        }
        let mw = merged_win();
        let col = |i: u32| -> u64 { (0..64u64).filter(|r| r >> i & 1 == 1).map(|r| 1u64 << r).sum() };
        let yt: [u64; 4] = std::array::from_fn(|i| col(i as u32));
        let mut n_and = 0usize;
        let got = core13(&yt, &col(4), &col(5), &u64::MAX, &0u64, mw, &|a, b| a ^ b, &mut |a, b| {
            n_and += 1;
            a & b
        });
        let g16: i128 = (1i128 << 32) + 976;
        for b in 0..mw {
            let want: u64 = (0..64i128)
                .filter(|&r| {
                    let n = (r >> 5 & 1) + (2 * (r >> 4 & 1) - 1) * (r & 15);
                    (g16 * n).rem_euclid(1i128 << mw) >> b & 1 == 1
                })
                .map(|r| 1u64 << r)
                .sum();
            assert_eq!(got[b], want, "core13 bit {b}");
        }
        assert_eq!(n_and, 13);
        true
    })
}

/// The addend forms of bits [0, MW) (bit 0 = ov) from the gated mu bits y, sg and ov; its ANDs go into `recs`.
fn m_core(c: &mut Builder, recs: &mut Recs, y: &[Lin; 4], ov: &Lin, sg: &Lin) -> Vec<Lin> {
    if lf_core13() {
        let mut add = core13(y, sg, ov, &Lin::k(true), &Lin::k(false), merged_win(), &|a: &Lin, b: &Lin| a.x(b), &mut |a: Lin, b: Lin| m_and(c, recs, a, b));
        add[0] = ov.clone();
        return add;
    }
    let one = Lin::k(true);
    let x: [Lin; 4] = std::array::from_fn(|j| y[j].x(sg).x(&one));
    let u = m_u_build(c, recs, &x, ov, sg);
    m_addend(c, recs, &u, ov)
}

/// Gidney carry out of bit i: AND(acc_i ^ c_i, add_i ^ c_i) ^ c_i (and its MBU erase).
fn m_carry(c: &mut Builder, acc: QubitId, add: &Lin, ci: QubitId) -> QubitId {
    let (a, b) = (Lin::of(&[acc, ci]), add.x(&Lin::of(&[ci])));
    let t = lin_and(c, &a, &b);
    c.cx(ci, t);
    t
}
fn m_carry_erase(c: &mut Builder, t: QubitId, acc: QubitId, add: &Lin, ci: QubitId) {
    let (a, b) = (Lin::of(&[acc, ci]), add.x(&Lin::of(&[ci])));
    c.cx(ci, t);
    lin_and_erase(c, t, &a, &b);
}

/// The merged fold ladder acc[0..MW) += ov + addend(u) (mod 2^MW). `hook` runs once the carries into bits 1..4 are
/// live (sum bits 0..3 = acc_j ^ c_j, acc_0 ^ ov) and returns the addend forms of bits [4, MW); the ANDs it
/// records are erased at the mirror point of the backward pass (before bits 3..0 are written).
fn m_fold(c: &mut Builder, acc: &[QubitId], ov: QubitId, recs: &mut Recs, plan: &[usize], k: usize,
          hook: impl FnOnce(&mut Builder, &mut Recs, [Lin; 4], bool) -> Vec<Lin>) {
    let y16_e0 = c.expected_total();
    m_fold_y16(c, acc, ov, recs, plan, k, hook);
    Y16_FOLD.with(|f| f.set(f.get() + c.expected_total() - y16_e0));
}
fn m_fold_y16(c: &mut Builder, acc: &[QubitId], ov: QubitId, recs: &mut Recs, plan: &[usize], k: usize,
          hook: impl FnOnce(&mut Builder, &mut Recs, [Lin; 4], bool) -> Vec<Lin>) {
    let mw = acc.len();
    assert_eq!(plan.iter().sum::<usize>(), mw - 4, "fold plan covers bits [4, MW)");
    let mut car: Vec<QubitId> = Vec::with_capacity(5);
    car.push(ov); // car[0] stands for the bit-0 addend (no carry-in)
    let c1 = and_new(c, acc[0], ov);
    car.push(c1);
    for i in 1..4 {
        let t = and_new(c, acc[i], car[i]);
        car.push(t);
    }
    // LF_G4_LOWCAR ([`lowcar_max`]): write the low sum bits 0..3 now and erase the carries into bits 1..k at once
    // (car_i = car_(i-1) AND NOT new_(i-1): Clifford MBU); the kept car_(k+1) is erased at the end with a k-AND phase
    let early = k > 0;
    assert!(k <= 3);
    let one = Lin::k(true);
    let nu: [Lin; 4] = if early {
        for i in 1..4 {
            c.cx(car[i], acc[i]);
        }
        c.cx(ov, acc[0]);
        for i in (1..=k).rev() {
            lin_and_erase(c, car[i], &Lin::of(&[car[i - 1]]), &Lin::of(&[acc[i - 1]]).x(&one));
        }
        std::array::from_fn(|j| Lin::of(&[acc[j]]))
    } else {
        std::array::from_fn(|j| Lin::of(&[acc[j], car[j]]))
    };
    let base = recs.len();
    let add = hook(c, recs, nu, early);
    // upper ladder [4, MW) in chunks: a non-final chunk keeps its carry-out (the next chunk's carry-in) and is
    // written back at once; kept carries are erased exactly at the end (MBU + [acc < add + cin] phase compare)
    let mut kept: Vec<(usize, usize, QubitId, QubitId)> = Vec::new();
    let (mut lo, mut cin) = (4usize, car[4]);
    for (j, &w) in plan.iter().enumerate() {
        let hi = lo + w;
        let last = j + 1 == plan.len();
        // lean final chunk: the carry into its top bit is used once, so it goes straight into that bit's wire (one
        // CCX, nothing to erase) and the chunk holds w - 2 carries ([`m_fold_plan`] gives it the extra bit)
        let direct = last && w >= 2 && m_fold_lean();
        let mut cc = vec![cin]; // cc[k] = carry into bit lo + k
        for i in lo..(if last { hi - 1 - direct as usize } else { hi }) {
            let t = m_carry(c, acc[i], &add[i], cc[i - lo]);
            cc.push(t);
        }
        if direct {
            let (i, ci) = (hi - 2, cc[w - 2]);
            let (a, b) = (Lin::of(&[acc[i], ci]), add[i].x(&Lin::of(&[ci])));
            let (ha, hb) = lin_pair_on(c, &a, &b);
            c.ccx(ha, hb, acc[hi - 1]);
            lin_pair_off(c, &a, &b);
            c.cx(ci, acc[hi - 1]);
        }
        if lf_merged_trace() && (last || plan.len() > 1) {
            eprintln!("LF_MERGED_FOLD chunk={j} [{lo},{hi}) active={} cap={}", c.active_qubits(), cells::cap());
        }
        assert!(c.active_qubits() as usize <= cells::cap() || std::env::var_os("LF_MERGED_NOCAPCHECK").is_some(),
            "merged fold over the walk cap: {} > {}", c.active_qubits(), cells::cap());
        for i in (lo..hi).rev() {
            lin_xor_into(c, &add[i], acc[i]);
            if direct && i == hi - 1 {
                continue; // its carry is already in the wire
            }
            c.cx(cc[i - lo], acc[i]);
            if i > lo {
                m_carry_erase(c, cc[i - lo], acc[i - 1], &add[i - 1], cc[i - lo - 1]);
            }
        }
        if !last {
            let out = cc[w];
            kept.push((lo, hi, cin, out));
            cin = out;
        }
        lo = hi;
    }
    for (lo, hi, cin, out) in kept.into_iter().rev() {
        let m = c.alloc_bit();
        c.hmr(out, m);
        c.release_clean(out);
        c.push_condition(m);
        lin_lt_phase(c, &acc[lo..hi], &add[lo..hi], cin);
        c.pop_condition();
        c.free_bit(m);
    }
    if early {
        m_erase(c, recs, base);
        for i in ((k + 2)..=4).rev() {
            lin_and_erase(c, car[i], &Lin::of(&[car[i - 1]]), &Lin::of(&[acc[i - 1]]).x(&one));
        }
        // car_(k+1) = ov AND NOT new_0 AND .. AND NOT new_k: measured out, its phase fix (k ANDs) on half the shots
        let m = c.alloc_bit();
        c.hmr(car[k + 1], m);
        c.release_clean(car[k + 1]);
        c.push_condition(m);
        let mut tr: Recs = Vec::new();
        let mut a = Lin::of(&[ov]);
        for j in 0..k {
            a = m_and(c, &mut tr, a, Lin::of(&[acc[j]]).x(&one));
        }
        lin_cz(c, &a, &Lin::of(&[acc[k]]).x(&one));
        m_erase(c, &mut tr, 0);
        c.pop_condition();
        c.free_bit(m);
        return;
    }
    and_erase(c, car[4], acc[3], car[3]);
    m_erase(c, recs, base);
    for i in (1..4).rev() {
        c.cx(car[i], acc[i]);
        and_erase(c, car[i], acc[i - 1], car[i - 1]);
    }
    c.cx(ov, acc[0]);
}

/// CZ between two linear forms (a constant side degenerates to Z or nothing).
fn lin_cz(c: &mut Builder, a: &Lin, b: &Lin) {
    match (a.w.is_empty(), b.w.is_empty()) {
        (true, true) => {
            if a.one && b.one {
                // global phase -1: unobservable inside a classically conditioned block only if unconditional;
                // never produced by the callers (cin and acc forms are never constant)
                panic!("lin_cz of two constants");
            }
        }
        (true, false) | (false, true) => {
            let (k, l) = if a.w.is_empty() { (a, b) } else { (b, a) };
            if k.one {
                let h = l.w[0];
                lin_on(c, l, h);
                c.z_if(h, NO_BIT);
                lin_off(c, l, h);
            }
        }
        (false, false) => {
            let (ha, hb) = lin_pair_on(c, a, b);
            c.cz(ha, hb);
            lin_pair_off(c, a, b);
        }
    }
}

/// Phase (-1)^[a < add + cin] on the current condition (a: w wires, add: w forms, cin: a wire): the carry-out of
/// NOT a + add + cin, Gidney carries measurement-uncomputed, the top carry as three CZs; w - 1 ANDs.
fn lin_lt_phase(c: &mut Builder, a: &[QubitId], add: &[Lin], cin: QubitId) {
    let w = a.len();
    c.x_all(a);
    let mut d = vec![cin];
    for i in 0..w - 1 {
        let t = m_carry(c, a[i], &add[i], d[i]);
        d.push(t);
    }
    let (x, y, z) = (Lin::of(&[a[w - 1]]), add[w - 1].clone(), Lin::of(&[d[w - 1]]));
    lin_cz(c, &x, &y);
    lin_cz(c, &y, &z);
    lin_cz(c, &z, &x);
    for i in (1..w).rev() {
        m_carry_erase(c, d[i], a[i - 1], &add[i - 1], d[i - 1]);
    }
    c.x_all(a);
}

/// Chunk plan of the merged fold's upper ladder (bits [4, MW), n = MW - 4) for `budget` live wires above the fold's
/// fixed part: one chunk when n - 1 carries fit; else the fewest chunks with the final chunk as wide as it can be (a
/// non-final chunk j holds j kept carries + w_j; the final one K-1 kept + w_K - 1). Expected cost of the split:
/// sum over non-final chunks of (w_j - 1) / 2 Toffoli.
fn merged_plan(n: usize, budget: usize) -> Option<Vec<usize>> {
    if budget + 1 >= n {
        return Some(vec![n]);
    }
    for k in 2..=n {
        let wk = (budget + 2).checked_sub(k)?;
        if wk == 0 {
            return None;
        }
        let caps: Vec<usize> = (0..k - 1).map(|j| budget.saturating_sub(j)).collect();
        if caps.contains(&0) {
            return None;
        }
        let rest = n.checked_sub(wk)?;
        if caps.iter().sum::<usize>() < rest {
            continue;
        }
        let mut sizes = Vec::with_capacity(k);
        let mut left = rest;
        if rest < k - 1 {
            return None;
        }
        for &cap in &caps {
            // every non-final chunk at least 1 wide; fill from the bottom
            let take = cap.min(left - (k - 2 - sizes.len()));
            sizes.push(take);
            left -= take;
        }
        if left > 0 || sizes.contains(&0) {
            continue;
        }
        sizes.push(wk);
        return Some(sizes);
    }
    None
}

fn lf_merged_trace() -> bool {
    std::env::var("LF_MERGED_TRACE").is_ok_and(|v| v == "1")
}

/// Rotation of a 256-bit register by one place (free: swaps). down: out[i] = in[i + 1].
fn rot1(c: &mut Builder, p: &[QubitId], down: bool) {
    let n = p.len();
    if down {
        for i in 0..n - 1 {
            c.swap(p[i], p[i + 1]);
        }
    } else {
        for i in (0..n - 1).rev() {
            c.swap(p[i], p[i + 1]);
        }
    }
}

/// Merged fold of the forward op (register in the sg-complemented frame, holding A; `ov` the adder's overflow).
fn m_fold_fwd(c: &mut Builder, acc: &[QubitId], ov: QubitId, sg: QubitId, k1: QubitId, k2: QubitId) {
    let (lsg, lov) = (Lin::of(&[sg]), Lin::of(&[ov]));
    let (plan, lk) = m_fold_plan(c, M_FIXED_FWD - core_freed(true), acc.len());
    m_fold(c, acc, ov, &mut Vec::new(), &plan, lk, |c, recs, nu, _| {
        // low sum bits nu_j = acc_j ^ c_j; mu_j = nu_j ^ sg masked by [k > j]
        let tt = m_and(c, recs, Lin::of(&[k1]), Lin::of(&[k2]));
        let gates = [Lin::of(&[k1, k2]).x(&tt), Lin::of(&[k2]), tt.clone()];
        let mut y = vec![nu[0].x(&lsg)];
        for j in 1..4 {
            let q = m_and(c, recs, gates[j - 1].clone(), nu[j].x(&lsg));
            y.push(q);
        }
        let y: [Lin; 4] = y.try_into().unwrap();
        m_core(c, recs, &y, &lov, &lsg)
    });
}

/// Fold extra (live wires beyond the adder's overflow) of the merged ops: MW - 1 carries plus 31 (forward: k-gate,
/// gated mu bits, u, monomials) or 27 (reverse: u, monomials; its 5 mu copies are live before the add).
fn m_fold_need(rev: bool) -> usize {
    (merged_win() - 1 + if rev { if lf_merged_rev2() { 3 + 4 + 14 } else { 14 } } else { 18 } - core_freed(true)).saturating_sub(g4_fake() + if std::env::var("LF_G4_LOWCAR_NEED").is_ok_and(|v| v == "1") { lowcar_max() } else { 0 })
}

/// `LF_G4_LOWCAR=K` (0..3): the merged fold may erase up to K of its carries into bits 1..3 right after writing the
/// low sum bits first (Clifford), K wires fewer through the hook and the ladder, for K/2 expected Toffoli at the end
/// (the kept carry's measured phase is a (K+2)-literal product). [`m_fold_plan`] picks k <= K per op by the plan's
/// expected cost; [`merged_fits`] and [`m_fold_need`] count K wires fewer.
fn lowcar_max() -> usize {
    std::env::var("LF_G4_LOWCAR").ok().and_then(|v| v.parse().ok()).unwrap_or(0).min(3)
}

/// G4 experiment only: pretend the merged fold's fixed part is this many wires smaller (with LF_MERGED_NOCAPCHECK: T bound).
fn g4_fake() -> usize {
    std::env::var("LF_G4_FAKE").ok().and_then(|v| v.parse().ok()).unwrap_or(0)
}

/// `LF_CORE_FREED`: [`core13`] holds 13 wires where the fit, split and plan rules count 14. Unset: the
/// rules keep 14, so every merged op has the same windows, compares and chunk plan as before. `plan`: only the
/// fold's own chunk plan uses the wire ([`m_fold_slack`]). `all`: every rule counts 13.
fn core_freed(all: bool) -> usize {
    static K: OnceLock<u8> = OnceLock::new();
    let k = *K.get_or_init(|| match std::env::var("LF_CORE_FREED").as_deref() {
        Ok("plan") if lf_core13() => 1,
        Ok("all") if lf_core13() => 2,
        _ => 0,
    });
    usize::from(if all { k == 2 } else { k == 1 })
}

/// Exact-flag split (`LF_MERGED_EXACT`, default 1): the lowest split s such that the top ripple [s, N) (N - s - 1
/// carries + the split carry + the overflow) and the fold fit under the cap during the consumer, with the split
/// compare (and seed) above the fold window. None when infeasible.
fn merged_split(c: &Builder, proxy: usize, multiply: bool, rev: bool) -> Option<usize> {
    if std::env::var("LF_MERGED_EXACT").is_ok_and(|v| v == "0") {
        return None;
    }
    let room = cells::cap().checked_sub(c.active_qubits() as usize)?;
    let mw = merged_win();
    let lo = (N + 1 + m_fold_need(rev)).saturating_sub(room);
    let mut s = lo.max(mw + 30);
    while s < N - 2 && s < mw + cells::split_compare_width(proxy, multiply, s) + 1 {
        s += 1;
    }
    let min_top: usize = std::env::var("LF_MERGED_EXACT_MINTOP").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    (s + min_top <= N).then_some(s)
}

/// Forward merged op: `tgt <- (tgt + (-1)^sg src) 2^-(1 + e) (mod p)`, e = k1 + 2 k2 (the replay cell `add_halve`
/// followed by [`cmod_barrel`]). `proxy` keys the production chunked adder and the flag / split compares. With a
/// split (exact route) the fold runs inside the top ripple and the overflow is erased exactly from its frame;
/// otherwise the overflow is erased with the cell's flag compare.
fn merged_fwd(c: &mut Builder, sg: QubitId, src: &[QubitId], tgt: &[QubitId], k1: QubitId, k2: QubitId, proxy: usize, split: Option<usize>,
              mw: usize) {
    c.cx_all(sg, tgt);
    match split {
        Some(sp) => cells::add_consume_exact(c, src, tgt, proxy, false, sp, |c, ov| m_fold_fwd(c, &tgt[..mw], ov, sg, k1, k2)),
        None => {
            let ov = cells::chunked_add(c, src, tgt, proxy, false);
            m_fold_fwd(c, &tgt[..mw], ov, sg, k1, k2);
            let k = cells::flag_erase(c, ov, tgt, src, mw, proxy, false);
            c.release_clean(ov);
            if lf_merged_trace() {
                eprintln!("LF_MERGED_FLAG fwd proxy={proxy} k={k}");
            }
        }
    }
    c.cx_all(sg, tgt);
    rot1(c, tgt, true);
    rot4(c, k1, k2, tgt, false);
}

/// Reverse merged op (exact inverse map): `tgt <- 2^(1 + e) tgt - (-1)^sg src (mod p)` (the inverse
/// [`cmod_barrel`] followed by the replay cell `double_add` with the sign flipped). `exact`: try the exact route
/// ([`merged_split`], judged once the 5 mu copies are live); the mu copies are erased inside the fold consumer.
fn merged_rev(c: &mut Builder, sg: QubitId, src: &[QubitId], tgt: &[QubitId], k1: QubitId, k2: QubitId, proxy: usize, exact: bool,
              mw: usize) {
    if lf_merged_rev2() {
        return merged_rev2(c, sg, src, tgt, k1, k2, proxy, exact, mw);
    }
    rot4(c, k1, k2, tgt, true);
    rot1(c, tgt, false);
    // copies of the rotated-in low bits (mu), gated by [k > j]
    let mut gl_recs: Recs = Vec::new();
    let g0 = c.alloc_qubit();
    c.cx(tgt[0], g0);
    let tt = m_and(c, &mut gl_recs, Lin::of(&[k1]), Lin::of(&[k2]));
    let gates = [Lin::of(&[k1, k2]).x(&tt), Lin::of(&[k2]), tt.clone()];
    let mut gl = vec![Lin::of(&[g0])];
    for j in 1..4 {
        let q = m_and(c, &mut gl_recs, gates[j - 1].clone(), Lin::of(&[tgt[j]]));
        gl.push(q);
    }
    // the cell's complemented frame: reg ^ sg ^ 1
    c.x_all(tgt);
    c.cx_all(sg, tgt);
    let split = if exact { merged_split(c, proxy, true, true) } else { None };
    if lf_merged_trace() {
        eprintln!("LF_MERGED_SPLIT rev proxy={proxy} split={split:?} active={}", c.active_qubits());
    }
    // fold, then erase the mu copies (R = the rotated-in low bits, recovered from the folded register, S_low, ov)
    let core = |c: &mut Builder, ov: QubitId, mut gl_recs: Recs| {
        let (lsg, lov) = (Lin::of(&[sg]), Lin::of(&[ov]));
        let (plan, lk) = m_fold_plan(c, M_FIXED_REV - core_freed(true), mw);
        let mut recs: Recs = Vec::new();
        let y: [Lin; 4] = std::array::from_fn(|j| gl[j].clone());
        let add = m_core(c, &mut recs, &y, &lov, &lsg);
        m_fold(c, &tgt[..mw], ov, &mut Vec::new(), &plan, lk, |_, _, _, _| add.clone());
        m_erase(c, &mut recs, 0);
        // in the frame: R = ((frame ^ 1) + S_low + ov) ^ sg (mod 16)
        let mut rr: Recs = Vec::new();
        let s_: Vec<Lin> = (0..4).map(|j| Lin::of(&[src[j]])).collect();
        let rg: Vec<Lin> = (0..4).map(|j| Lin::of(&[tgt[j]]).x(&Lin::k(true))).collect();
        let mut sum = vec![rg[0].x(&s_[0]).x(&lov)];
        let mut cc = lov.clone();
        for j in 0..3 {
            let q = m_and(c, &mut rr, rg[j].x(&cc), s_[j].x(&cc));
            cc = q.x(&cc);
            sum.push(rg[j + 1].x(&s_[j + 1]).x(&cc));
        }
        let r: Vec<Lin> = sum.iter().map(|l| l.x(&lsg)).collect();
        lin_xor_into(c, &r[0], g0);
        c.release_clean(g0);
        // gated copies AND(gate_j, R_j), then tt (recorded order: tt, q1, q2, q3)
        let qs: Vec<(QubitId, Lin, Lin)> = gl_recs.drain(1..).collect();
        for (j, (q, gate, _)) in qs.into_iter().enumerate().rev() {
            lin_and_erase(c, q, &gate, &r[j + 1]);
        }
        m_erase(c, &mut gl_recs, 0);
        m_erase(c, &mut rr, 0);
    };
    match split {
        Some(sp) => cells::add_consume_exact(c, src, tgt, proxy, true, sp, |c, ov| core(c, ov, gl_recs)),
        None => {
            let ov = cells::chunked_add(c, src, tgt, proxy, true);
            core(c, ov, gl_recs);
            let k = cells::flag_erase(c, ov, tgt, src, mw, proxy, true);
            c.release_clean(ov);
            if lf_merged_trace() {
                eprintln!("LF_MERGED_FLAG rev proxy={proxy} k={k}");
            }
        }
    }
    c.cx_all(sg, tgt);
    c.x_all(tgt);
}

/// `LF_MERGED_REV2` (default: on with LF_MERGED_LATE): the reverse merged op without mu copies. After the chunked
/// add the register's low bits are L = (F + S_low) mod 16, F the cell frame of W = rotl_k(Y); W_low = (L - S_low) ^ sg ^ 1
/// costs 3 borrow ANDs (the copies' 3-AND recovery is dropped), and every helper is built and erased inside the fold
/// while L is unwritten: nothing extra is live across the chunked add (fewer chunk compares), +2 wires in the fold.
fn lf_merged_rev2() -> bool {
    std::env::var("LF_MERGED_REV2").map_or(lf_merged_late(), |v| v == "1")
}

/// [`merged_rev`] with [`lf_merged_rev2`].
fn merged_rev2(c: &mut Builder, sg: QubitId, src: &[QubitId], tgt: &[QubitId], k1: QubitId, k2: QubitId, proxy: usize, exact: bool,
               mw: usize) {
    rot4(c, k1, k2, tgt, true);
    rot1(c, tgt, false);
    // the cell's complemented frame: reg ^ sg ^ 1
    c.x_all(tgt);
    c.cx_all(sg, tgt);
    let split = if exact { merged_split(c, proxy, true, true) } else { None };
    if lf_merged_trace() {
        eprintln!("LF_MERGED_SPLIT rev2 proxy={proxy} split={split:?} active={}", c.active_qubits());
    }
    let core = |c: &mut Builder, ov: QubitId| {
        let (lsg, lov, one) = (Lin::of(&[sg]), Lin::of(&[ov]), Lin::k(true));
        let (plan, lk) = m_fold_plan(c, M_FIXED_REV2 - core_freed(true), mw);
        m_fold(c, &tgt[..mw], ov, &mut Vec::new(), &plan, lk, |c, recs, _nu, written| {
            // W_low = (L - S_low) ^ sg ^ 1, borrows beta_{j+1} = MAJ(NOT L_j, S_j, beta_j); with the low bits already
            // written (L' = L + ov): W_low = (L' - S_low - ov) ^ sg ^ 1, borrow-in ov, the same 3 ANDs
            let l: Vec<Lin> = (0..4).map(|j| Lin::of(&[tgt[j]])).collect();
            let sl: Vec<Lin> = (0..4).map(|j| Lin::of(&[src[j]])).collect();
            let mut beta = if written {
                let b0 = lov.clone();
                let q = m_and(c, recs, l[0].x(&one).x(&b0), sl[0].x(&b0));
                vec![b0.clone(), q.x(&b0)]
            } else {
                vec![Lin::k(false), m_and(c, recs, l[0].x(&one), sl[0].clone())]
            };
            for j in 1..3 {
                let b = beta[j].clone();
                let q = m_and(c, recs, l[j].x(&one).x(&b), sl[j].x(&b));
                beta.push(q.x(&b));
            }
            let w: Vec<Lin> = (0..4).map(|j| l[j].x(&sl[j]).x(&beta[j]).x(&lsg).x(&one)).collect();
            let tt = m_and(c, recs, Lin::of(&[k1]), Lin::of(&[k2]));
            let gates = [Lin::of(&[k1, k2]).x(&tt), Lin::of(&[k2]), tt.clone()];
            let mut gl = vec![w[0].clone()];
            for j in 1..4 {
                gl.push(m_and(c, recs, gates[j - 1].clone(), w[j].clone()));
            }
            let y: [Lin; 4] = std::array::from_fn(|j| gl[j].clone());
            m_core(c, recs, &y, &lov, &lsg)
        });
    };
    match split {
        Some(sp) => cells::add_consume_exact(c, src, tgt, proxy, true, sp, core),
        None => {
            let ov = cells::chunked_add(c, src, tgt, proxy, true);
            core(c, ov);
            let k = cells::flag_erase(c, ov, tgt, src, mw, proxy, true);
            c.release_clean(ov);
            if lf_merged_trace() {
                eprintln!("LF_MERGED_FLAG rev2 proxy={proxy} k={k}");
            }
        }
    }
    c.cx_all(sg, tgt);
    c.x_all(tgt);
}

/// Live wires of the merged fold beyond the op's starting count, excluding the upper ladder's carries: the fold's
/// own carries into bits 1..4 and its helper ANDs (forward: k-gate, gated mu bits, u, monomials = 31), measured
/// from the fold's start (overflow live); the reverse's u + monomials (27) with its 5 mu copies counted at the op.
const M_FIXED_FWD: usize = 4 + 18;
const M_FIXED_REV: usize = 4 + 14;
/// [`merged_rev2`]: carries into bits 1..4, 3 borrows, k-gate + 3 gated mu bits, u, monomials.
const M_FIXED_REV2: usize = 4 + 3 + 4 + 14;

/// Wires counted in M_FIXED_* that the fold no longer holds: 4 since [`m_u_build`] went from 8 ANDs to 4, and 9 more
/// with [`addend10`]. The fit and split rules ([`merged_fits`], [`merged_split`], [`m_fold_need`]) keep the old
/// counts, so the same ticks run the merged op with the same windows and compares; only the fold's own chunk plan
/// uses the freed room (fewer or shorter kept chunks; a kept carry is erased with an exact compare, so the map does
/// not change). The cap assert inside [`m_fold`] guards the count. `LF_FOLD_SLACK=0` keeps the old plan.
fn m_fold_slack() -> usize {
    if std::env::var("LF_FOLD_SLACK").is_ok_and(|v| v == "0") {
        return 0;
    }
    // the 13 freed wires (4 from the 4-AND u build, 9 from addend10) are no longer in M_FIXED_* or m_fold_need,
    // so the fit and split rules see them too and nothing is left to give back here; `LF_CORE_FREED=plan` gives
    // back the one wire of [`core13`]
    core_freed(false)
}

/// `LF_FOLD_LEAN=0` keeps the merged fold's final chunk with a carry wire for its top bit.
fn m_fold_lean() -> bool {
    !std::env::var("LF_FOLD_LEAN").is_ok_and(|v| v == "0")
}

/// The fold's chunk plan at the current live count (`fixed`: the fold's non-ladder wires still to be allocated).
fn m_fold_plan(c: &Builder, fixed: usize, mw: usize) -> (Vec<usize>, usize) {
    super::pingpong::y17_fold_true_cap();
    let plan_at = |k: usize| -> Option<Vec<usize>> {
        let budget = cells::cap().saturating_sub((c.active_qubits() as usize + fixed - m_fold_slack()).saturating_sub(g4_fake() + k));
        // lean final chunk ([`m_fold`]): it holds one carry fewer, so plan one bit less and give that bit to the final
        // chunk. The fit rule ([`merged_fits`]) keeps the plain plan, so the same ticks run the merged op.
        let lean = if m_fold_lean() && mw >= 7 { merged_plan(mw - 5, budget) } else { None };
        match lean {
            Some(mut p) => {
                *p.last_mut().unwrap() += 1;
                Some(p)
            }
            None => merged_plan(mw - 4, budget),
        }
    };
    // k early-erased low carries cost k/2 expected Toffoli (x2 units: k)
    let (plan, k) = (0..=lowcar_max())
        .filter_map(|k| plan_at(k).map(|p| (p, k)))
        .min_by_key(|(p, k)| (plan_x2(p) + k, *k))
        .expect("merged fold plan (checked by merged_fits)");
    y17_log(c, || format!("mfold(room={},k={k},plan={plan:?})", cells::cap().saturating_sub(c.active_qubits() as usize)));
    if lf_merged_trace() && (plan.len() > 1 || k > 0) {
        eprintln!("LF_MERGED_PLAN k={k} plan={plan:?} x2={}", plan_x2(&plan));
    }
    (plan, k)
}

/// Twice the expected extra Toffoli of a chunk plan (the kept carries' exact compares fire on half the shots).
fn plan_x2(plan: &[usize]) -> usize {
    plan[..plan.len() - 1].iter().map(|w| w - 1).sum()
}

/// `LF_MERGED_LATE=1`: also run the merged op where its fold must be split (late ticks) and on tie-safe ticks (with the
/// tie predicate, as the cells), when the split's extra2 is at most LF_MERGED_LATE_MAXX2 (default 60).
fn lf_merged_late() -> bool {
    std::env::var("LF_MERGED_LATE").is_ok_and(|v| v == "1")
}

/// Merged op on tick t: LF_MERGED=1, before the tie-safe ticks (LF_MERGED_MAX, default LF_TIE_FROM) and when the
/// flag route's fold phase (ov + [`m_fold_need`], + the 5 mu copies on the reverse) fits under the walk cap at
/// `active` (live count at the op).
fn merged_fits(active: usize, t: usize, rev: bool) -> Option<usize> {
    static MAX: OnceLock<usize> = OnceLock::new();
    let max = *MAX.get_or_init(|| {
        std::env::var("LF_MERGED_MAX").ok().and_then(|v| v.parse().ok())
            .unwrap_or_else(|| std::env::var("LF_TIE_FROM").ok().and_then(|v| v.parse().ok()).unwrap_or(0))
    });
    if lf_merged_trace() {
        eprintln!("LF_MERGED_ROOM t={t} rev={rev} active={active} room={}", cells::cap().saturating_sub(active));
    }
    let late = lf_merged_late();
    if !lf_merged() || (t >= max && !late) {
        return None;
    }
    // forward: overflow + fold fixed part; reverse: 5 mu copies + overflow + fold fixed part; then the ladder budget
    let fixed = (1 + if rev { if lf_merged_rev2() { M_FIXED_REV2 } else { 5 + M_FIXED_REV } } else { M_FIXED_FWD } - core_freed(true)).saturating_sub(g4_fake() + lowcar_max());
    let budget = cells::cap().checked_sub(active + fixed)?;
    let mw = merged_win();
    // the standard op: a single-chunk fold before the tie-safe ticks
    if t < max && merged_plan(mw - 4, budget).is_some_and(|p| p.len() == 1) {
        return Some(mw);
    }
    if !late {
        return None;
    }
    // late op: the fold window LF_MERGED_LATE_WIN (default MW), split to the room; taken when the split's expected
    // extra (x2 / 2) is at most LF_MERGED_LATE_GAIN_FWD / _REV (defaults 1000: always) plus the production barrel's
    // own split extra at this room (its fold ladder [4, 4 + fs) beside 8 helpers, lpa_capped)
    let lw: usize = std::env::var("LF_MERGED_LATE_WIN").ok().and_then(|v| v.parse().ok()).unwrap_or(mw).min(mw);
    let plan = merged_plan(lw - 4, budget)?;
    let gain: usize = std::env::var(if rev { "LF_MERGED_LATE_GAIN_REV" } else { "LF_MERGED_LATE_GAIN_FWD" })
        .ok().and_then(|v| v.parse().ok()).unwrap_or(1000);
    let room = cells::cap().saturating_sub(active);
    let fs = go_fs("GO_FG_P");
    let bar_split = if split_tight() {
        (fs + 8).saturating_sub(room) / 2
    } else if fs + 8 > room {
        room.saturating_sub(8 + 4) / 2
    } else {
        0
    };
    let ok = plan_x2(&plan) / 2 <= gain + bar_split;
    if lf_merged_trace() {
        eprintln!("LF_MERGED_FIT t={t} rev={rev} active={active} win={lw} plan={plan:?} x2={} bar_split={bar_split} cap={} ok={ok}",
            plan_x2(&plan), cells::cap());
    }
    ok.then_some(lw)
}

/// Controlled arithmetic shift right by one of a register whose low wire is 0 when `ctrl`.
fn crot_down_fix(c: &mut Builder, ctrl: QubitId, t: &[QubitId]) {
    let w = t.len();
    for i in 0..w - 1 {
        fredkin(c, ctrl, t[i], t[i + 1]);
    }
    c.ccx(ctrl, t[w - 2], t[w - 1]);
}
fn crot_up_fix(c: &mut Builder, ctrl: QubitId, t: &[QubitId]) {
    let w = t.len();
    c.ccx(ctrl, t[w - 2], t[w - 1]);
    for i in (0..w - 1).rev() {
        fredkin(c, ctrl, t[i], t[i + 1]);
    }
}

/// Controlled arithmetic shift right by two of a register whose two low wires are 0 when `ctrl`.
fn crot2_down_fix(c: &mut Builder, ctrl: QubitId, t: &[QubitId]) {
    let w = t.len();
    for i in 0..w - 2 {
        fredkin(c, ctrl, t[i], t[i + 2]);
    }
    c.ccx(ctrl, t[w - 3], t[w - 2]);
    c.ccx(ctrl, t[w - 3], t[w - 1]);
}
fn crot2_up_fix(c: &mut Builder, ctrl: QubitId, t: &[QubitId]) {
    let w = t.len();
    c.ccx(ctrl, t[w - 3], t[w - 1]);
    c.ccx(ctrl, t[w - 3], t[w - 2]);
    for i in (0..w - 2).rev() {
        fredkin(c, ctrl, t[i], t[i + 2]);
    }
}

/// Controlled modular quartering: `p <- ctrl ? p/4 : p (mod p)`. With p == 3 (mod 4), m = p mod 4 makes
/// p + m*P == 0 (mod 4); P = 2^256 - f, so subtract m*f in the fold window, rotate by two and put m on top.
fn cmod_quarter(c: &mut Builder, ctrl: QubitId, p: &[QubitId]) {
    let fs = go_fs("GO_FG_P");
    let m0 = and_new(c, ctrl, p[0]);
    let m1 = and_new(c, ctrl, p[1]);
    csub_const_trunc(c, &p[..fs], f(), m0);
    csub_const_trunc(c, &p[1..1 + fs], f(), m1);
    for i in 0..N - 2 {
        fredkin(c, ctrl, p[i], p[i + 2]);
    }
    c.cx(m0, p[N - 2]);
    c.cx(m1, p[N - 1]);
    c.ccx(ctrl, p[N - 1], m1);
    c.ccx(ctrl, p[N - 2], m0);
    c.release_clean(m1);
    c.release_clean(m0);
}
/// Inverse of [`cmod_quarter`]: `p <- ctrl ? 4p : p (mod p)`.
fn cmod_quadruple(c: &mut Builder, ctrl: QubitId, p: &[QubitId]) {
    let fs = go_fs("GO_FG_P");
    let (m0, m1) = (c.alloc_qubit(), c.alloc_qubit());
    c.ccx(ctrl, p[N - 2], m0);
    c.ccx(ctrl, p[N - 1], m1);
    c.cx(m1, p[N - 1]);
    c.cx(m0, p[N - 2]);
    for i in (0..N - 2).rev() {
        fredkin(c, ctrl, p[i], p[i + 2]);
    }
    cadd_const_trunc(c, &p[1..1 + fs], f(), m1, false);
    cadd_const_trunc(c, &p[..fs], f(), m0, false);
    and_erase(c, m1, ctrl, p[1]);
    and_erase(c, m0, ctrl, p[0]);
}

/// Controlled modular halving of a 256-bit payload: `p <- ctrl ? p/2 : p (mod p)`.
fn cmod_halve(c: &mut Builder, ctrl: QubitId, p: &[QubitId]) {
    let par = and_new(c, ctrl, p[0]);
    csub_const_trunc(c, &p[..go_fs("GO_FG_P")], f(), par);
    for i in 0..N - 1 {
        fredkin(c, ctrl, p[i], p[i + 1]);
    }
    c.cx(par, p[N - 1]);
    c.ccx(ctrl, p[N - 1], par);
    c.release_clean(par);
}
/// Inverse of [`cmod_halve`]: `p <- ctrl ? 2p : p (mod p)`.
fn cmod_double(c: &mut Builder, ctrl: QubitId, p: &[QubitId]) {
    let par = c.alloc_qubit();
    c.ccx(ctrl, p[N - 1], par);
    c.cx(par, p[N - 1]);
    for i in (0..N - 1).rev() {
        fredkin(c, ctrl, p[i], p[i + 1]);
    }
    cadd_const_trunc(c, &p[..go_fs("GO_FG_P")], f(), par, false);
    and_erase(c, par, ctrl, p[0]);
}

pub struct Walk {
    pub r: [Vec<QubitId>; 2],
    tape: Vec<Vec<QubitId>>,
}

fn seed(c: &mut Builder, d: &[QubitId]) -> [Vec<QubitId>; 2] {
    let r = seed_full(c, d);
    lr_walk_drop(c, r)
}
/// LF_LOWREL: the seeded rails (both odd) without their bit-0 wires.
fn lr_walk_drop(c: &mut Builder, r: [Vec<QubitId>; 2]) -> [Vec<QubitId>; 2] {
    let mut r = r;
    if lowrel() {
        lr_drop(c, &mut r[0]);
        lr_drop(c, &mut r[1]);
    }
    r
}
/// LF_LOWREL: the walked-back rails with their bit-0 wires, for the unseed.
fn lr_walk_restore(c: &mut Builder, r: [Vec<QubitId>; 2]) -> [Vec<QubitId>; 2] {
    let mut r = r;
    if lowrel() {
        lr_restore(c, &mut r[1]);
        lr_restore(c, &mut r[0]);
    }
    r
}
fn seed_full(c: &mut Builder, d: &[QubitId]) -> [Vec<QubitId>; 2] {
    if seed_half() {
        return seed_half_rails(c, d);
    }
    let w0 = envelope()[0].max(N + 5);
    // R0 = d + p * [d even], on d's own wires (+ extension); [d even] ends as R0[N] (exact unless d + p < 2^256).
    let mut r0 = d.to_vec();
    r0.extend(c.alloc_qubits(w0 - N));
    let ev = c.alloc_qubit();
    c.cx(r0[0], ev);
    c.x(ev);
    c.cx(ev, r0[N]); // + 2^256
    csub_const_trunc(c, &r0[..go_fs("GO_FG_P")], f(), ev); // - f
    c.cx(r0[N], ev);
    c.free(ev);
    // R1 = 3 R0 + 2p (odd, coprime to R0; payload lambda*R1 == 3y: never zero, never +-P0 early on)
    let r1 = c.alloc_qubits(w0);
    c.cx_pairs(&r0, &r1);
    gidney_add(c, &r0[..w0 - 1], &r1[1..], None); // + 2 R0
    add_const(c, &r1[N + 1..], alloy_primitives::U256::from(1u8)); // + 2^257
    let one = c.alloc_qubit();
    c.x(one);
    csub_const_trunc(c, &r1[1..1 + go_fs("GO_FG_P")], f(), one); // - 2f
    c.x(one);
    c.free(one);
    [r0, r1]
}

fn unseed(c: &mut Builder, r: [Vec<QubitId>; 2], d: &[QubitId]) {
    let r = lr_walk_restore(c, r);
    if seed_half() {
        let r0 = unseed_half_rails(c, r);
        return restore_onto(c, r0, d);
    }
    let [mut r0, mut r1] = r;
    let w0 = envelope()[0].max(N + 5);
    resize(c, &mut r0, w0);
    resize(c, &mut r1, w0);
    let one = c.alloc_qubit();
    c.x(one);
    cadd_const_trunc(c, &r1[1..1 + go_fs("GO_FG_P")], f(), one, false);
    c.x(one);
    c.free(one);
    sub_const(c, &r1[N + 1..], alloy_primitives::U256::from(1u8));
    c.x_all(&r1[1..]);
    gidney_add(c, &r0[..w0 - 1], &r1[1..], None); // R1 - 2 R0 == NOT(NOT R1 + 2 R0)
    c.x_all(&r1[1..]);
    c.cx_pairs(&r0, &r1);
    c.free_vec(&r1);
    let ev = c.alloc_qubit();
    c.cx(r0[N], ev);
    cadd_const_trunc(c, &r0[..go_fs("GO_FG_P")], f(), ev, false);
    c.cx(ev, r0[N]);
    c.x(ev);
    c.cx(r0[0], ev);
    c.free(ev);
    restore_onto(c, r0, d);
}

/// Move d's bits (the low N wires of `cur`) back onto d's own wires (SWAPs are Clifford); free the extension.
fn restore_onto(c: &mut Builder, cur: Vec<QubitId>, d: &[QubitId]) {
    let mut cur = cur;
    let mut resets = cur.len() - N;
    for i in 0..N {
        let want = d[i];
        if cur[i] == want {
            continue;
        }
        if let Some(j) = cur.iter().position(|&q| q == want) {
            c.swap(cur[i], cur[j]);
            cur.swap(i, j);
        } else {
            c.reacquire(want);
            c.swap(cur[i], want);
            c.free(cur[i]);
            cur[i] = want;
            resets += 1;
        }
    }
    c.free_vec(&cur[N..]);
    // N2 (research patch, diagnostic): SL_N2_RPAD idle measurements after the i-th call (aligned copy)
    n2_rpads(c);
    // y28 DIAGNOSTIC, never for an entry (see [`Y28_ALIGNED`]); the log line has no effect on the gates
    if Y28_ALIGNED {
        let call = Y28_RESTORES.with(|x| x.replace(x.get() + 1));
        eprintln!("Y28_RESTORE call={call} resets={resets}");
        for _ in 0..Y28_ALIGN_PADS.get(call).copied().unwrap_or(0) {
            let q = c.alloc_qubit();
            let m = c.alloc_bit();
            c.hmr(q, m);
            c.free_bit(m);
            c.release_clean(q);
        }
    }
}
/// y28 DIAGNOSTIC, false in every entry: the ALIGNED COPY of the y28-loop fold cards. true adds idle measurements (of
/// a wire that holds 0) where the cards' gate list draws fewer random words than entry Y: [`Y28_ALIGN_PADS`] here and
/// `Y28_PADS_FWD` / `Y28_PADS_REV` in y15_onefold.rs (20 in all for the kept set). The copy then has entry Y's number
/// of measurements and resets at every place outside the changed blocks, the checker hands every measurement the
/// random word it has in Y, and a paired run compares phase flags shot by shot. It costs no Toffoli.
const Y28_ALIGNED: bool = false;
/// Idle measurements after the i-th call of [`restore_onto`], with [`Y28_ALIGNED`]. That function resets one wire for
/// every register bit whose home wire is not held by another bit of the register, so its number of resets moves with
/// the wire ids, and a change that hands out wires in another order than the head shifts the checker's random words
/// from there on (the kept set: 204 resets at the end of the divide for Y's 205).
const Y28_ALIGN_PADS: &[usize] = &[1];
thread_local! {
    static Y28_RESTORES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Seed e: R0 = d (d odd) or d - p (d even, negative), on d's wires + extension; R1 = (R0 + s p)/2 with s = +1 iff
/// R0 == 3 (mod 4), so both rails are odd. Constant folds only (no 3 R0 add): R0 - p + [R0 == 3 mod 4] 2p, halved.
fn seed_half_rails(c: &mut Builder, d: &[QubitId]) -> [Vec<QubitId>; 2] {
    let w0 = envelope()[0].max(N + 4);
    let fs = go_fs("GO_FG_P");
    let mut r0 = d.to_vec();
    r0.extend(c.alloc_qubits(w0 - N));
    let ev = c.alloc_qubit();
    c.cx(r0[0], ev);
    c.x(ev); // [d even]
    cadd_const_trunc(c, &r0[..fs], f(), ev, false); // + f
    for i in N..w0 {
        c.cx(ev, r0[i]); // - 2^256: d + f - 2^256 < 0, all high bits set
    }
    c.cx(r0[w0 - 1], ev); // ev == sign
    c.free(ev);
    let r1 = seed_r1(c, &r0);
    [r0, r1]
}

/// R1 = (R0 + s p)/2, s = +1 iff R0 == 3 (mod 4), from R0 at width w0.
fn seed_r1(c: &mut Builder, r0: &[QubitId]) -> Vec<QubitId> {
    let w0 = r0.len();
    let fs = go_fs("GO_FG_P");
    let one_u = alloy_primitives::U256::from(1u8);
    let mut r1 = c.alloc_qubits(w0);
    c.cx_pairs(&r0, &r1);
    if lf_seams() {
        // R0 - p + [R0 == 3 mod 4] 2p = R0 + (sg ? +p : -p): low window +f / -f selected by sg (one ladder)
        let sg = c.alloc_qubit();
        c.cx(r0[1], sg);
        let m = (alloy_primitives::U256::from(1u8) << (fs + 1)) - alloy_primitives::U256::from(1u8);
        add_sel_const(c, &r1[..fs + 1], f() & m, (alloy_primitives::U256::ZERO.wrapping_sub(f())) & m, sg);
        sub_const(c, &r1[N..], one_u);
        cadd_const_trunc(c, &r1[N + 1..], one_u, sg, false);
        c.cx(r0[1], sg);
        c.free(sg);
    } else {
    let one = c.alloc_qubit();
    c.x(one);
    cadd_const_trunc(c, &r1[..fs], f(), one, false); // - p = - 2^256 + f
    c.x(one);
    c.free(one);
    sub_const(c, &r1[N..], one_u);
    let sg = c.alloc_qubit();
    c.cx(r0[1], sg); // [R0 == 3 mod 4]: + 2p
    csub_const_trunc(c, &r1[1..1 + fs], f(), sg);
    cadd_const_trunc(c, &r1[N + 1..], one_u, sg, false);
    c.cx(r0[1], sg);
    c.free(sg);
    }
    let low = r1.remove(0);
    c.free(low);
    resize(c, &mut r1, w0);
    r1
}

/// `LF_SEAMS=1`: seam fusions around the walks (R1's two seed folds as one selected fold; coordinate ops fused
/// into the divide's seed / unseed and the multiply's unseed).
fn lf_seams() -> bool {
    std::env::var("LF_SEAMS").is_ok_and(|v| v == "1")
}

/// `acc += sel ? k1 : k0 (mod 2^len)`: one Gidney ladder whose addend bit i is the parity k0_i ^ sel (k0_i ^ k1_i)
/// (a constant-1 wire for the fixed bits).
fn add_sel_const(c: &mut Builder, acc: &[QubitId], k0: alloy_primitives::U256, k1: alloy_primitives::U256, sel: QubitId) {
    let one = c.alloc_qubit();
    c.x(one);
    let add: Vec<Vec<QubitId>> = (0..acc.len())
        .map(|i| {
            let mut v = Vec::new();
            if k0.bit(i) { v.push(one); }
            if k0.bit(i) != k1.bit(i) { v.push(sel); }
            v
        })
        .collect();
    ladder_parity_add(c, acc, &add, None);
    c.x(one);
    c.free(one);
}

/// Exact inverse of [`seed_half_rails`]; returns R0's wires holding d (+ zero extension).
fn unseed_half_rails(c: &mut Builder, r: [Vec<QubitId>; 2]) -> Vec<QubitId> {
    let r0 = unseed_r1(c, r);
    let w0 = r0.len();
    let fs = go_fs("GO_FG_P");
    let ev = c.alloc_qubit();
    c.cx(r0[w0 - 1], ev);
    for i in N..w0 {
        c.cx(ev, r0[i]);
    }
    csub_const_trunc(c, &r0[..fs], f(), ev);
    c.x(ev);
    c.cx(r0[0], ev);
    c.free(ev);
    r0
}

/// Inverse of [`seed_r1`]: clears R1, returns R0 at width w0.
fn unseed_r1(c: &mut Builder, r: [Vec<QubitId>; 2]) -> Vec<QubitId> {
    let [mut r0, mut r1] = r;
    let w0 = envelope()[0].max(N + 4);
    let fs = go_fs("GO_FG_P");
    let one_u = alloy_primitives::U256::from(1u8);
    resize(c, &mut r0, w0);
    resize(c, &mut r1, w0 - 1);
    r1.insert(0, c.alloc_qubit());
    if lf_seams() {
        let sg = c.alloc_qubit();
        c.cx(r0[1], sg);
        csub_const_trunc(c, &r1[N + 1..], one_u, sg);
        add_const(c, &r1[N..], one_u);
        let m = (alloy_primitives::U256::from(1u8) << (fs + 1)) - alloy_primitives::U256::from(1u8);
        add_sel_const(c, &r1[..fs + 1], (alloy_primitives::U256::ZERO.wrapping_sub(f())) & m, f() & m, sg);
        c.cx(r0[1], sg);
        c.free(sg);
    } else {
    let sg = c.alloc_qubit();
    c.cx(r0[1], sg);
    csub_const_trunc(c, &r1[N + 1..], one_u, sg);
    cadd_const_trunc(c, &r1[1..1 + fs], f(), sg, false);
    c.cx(r0[1], sg);
    c.free(sg);
    add_const(c, &r1[N..], one_u);
    let one = c.alloc_qubit();
    c.x(one);
    csub_const_trunc(c, &r1[..fs], f(), one);
    c.x(one);
    c.free(one);
    }
    c.cx_pairs(&r0, &r1);
    c.free_vec(&r1);
    r0
}

/// Fold window of the seam ops: the wider of the seed's and the coordinate shell's (no new truncation site).
fn seam_fs() -> usize {
    go_fs("GO_FG_P").max(go_fs("GO_FG_M"))
}

/// `mask` of the low `n` bits.
fn low_mask(n: usize) -> alloy_primitives::U256 {
    (alloy_primitives::U256::from(1u8) << n) - alloy_primitives::U256::from(1u8)
}

/// Front seam (`LF_SEAMS`): R0 of seed e straight from x2 and the classical ox, without forming d = x2 - ox mod p.
/// D = x2 - ox lands as (x mod 2^256, ov = [D < 0]); R0 = D - p (D >= 0 even), D + p (D < 0 even), D (odd) is
/// exactly the seed's d or d - p. One selected +-f fold replaces coord_sub's +f fold and the seed's; ov (the choice
/// of representative) is erased as coord_sub erases its borrow, by a top-window phase compare.
fn seed_r0_seam(c: &mut Builder, x: &[QubitId], ox: &[crate::circuit::BitId]) -> Vec<QubitId> {
    let w0 = envelope()[0].max(N + 4);
    let fs = seam_fs();
    c.x_all(x);
    let ov = c.alloc_qubit();
    super::modular::r5_ripple_add_cbits(c, ox, x, ov); // ~x + ox: carry = [ox > x]
    c.x_all(x); // x = D mod 2^256
    let e = c.alloc_qubit();
    c.cx(x[0], e);
    c.x(e); // [D even]
    c.x(ov);
    let g = and_new(c, e, ov); // D >= 0 even: - p
    c.x(ov);
    let mut r0 = x.to_vec();
    let ext = c.alloc_qubits(w0 - N);
    c.cx(ov, ext[0]);
    c.cx(e, ext[0]); // sign(R0) = ov ^ [D even]
    for &q in &ext[1..] {
        c.cx(ext[0], q);
    }
    r0.extend(ext.iter().copied());
    // low window += f g - f (e ^ g): addend bit i = (f_i ^ nf_i) g ^ nf_i e
    let nf = alloy_primitives::U256::ZERO.wrapping_sub(f()) & low_mask(fs);
    let add: Vec<Vec<QubitId>> = (0..fs)
        .map(|i| {
            let mut v = Vec::new();
            if f().bit(i) != nf.bit(i) { v.push(g); }
            if nf.bit(i) { v.push(e); }
            v
        })
        .collect();
    ladder_parity_add(c, &r0[..fs], &add, None);
    c.x(ov);
    and_erase(c, g, e, ov);
    c.x(ov);
    c.cx(ext[0], e);
    c.cx(ov, e); // [D even] = sign ^ ov
    c.free(e);
    // ov = [x2 < ox] = carry out of R0_low + ox (+ f when R0 >= 0): [~R0_top < ox_top] on the top window
    let k = super::modular::erase_compare();
    c.x_all(&r0[N - k..N]);
    let tv = c.alloc_qubits(k);
    for i in 0..k {
        c.x_if_bit(tv[i], ox[N - k + i]);
    }
    super::compare::erase_with_compare(c, ov, &r0[N - k..N], &tv, None);
    for i in 0..k {
        c.x_if_bit(tv[i], ox[N - k + i]);
    }
    c.free_vec(&tv);
    c.x_all(&r0[N - k..N]);
    c.free(ov);
    r0
}

thread_local! {
    /// T6 seed fusion: R0 of the multiply's seed, formed by the square's last subtract ([`square_seed_r0`]).
    static T6_PRESEED: std::cell::RefCell<Option<Vec<QubitId>>> = const { std::cell::RefCell::new(None) };
}

/// `LF_T6_SEEDFUSE=1` (with `LF_SEAMS` and `LF_SEED=half`): the square's last modular subtract and the multiply's
/// seed e as one op. The square leaves D = out - b2 unreduced (out mod 2^256, ov = [D < 0]); R0 of seed e is then
/// formed straight from (D, ov) exactly as [`seed_r0_seam`] does from x2 - ox, with one selected +-f fold in
/// place of the subtract's +f fold and the seed's own +f fold; ov is erased by the same top-window phase compare
/// against b2 (still live). R0 (on out's wires + extension) is handed to the next [`multiply`].
pub fn t6_seedfuse() -> bool {
    std::env::var("LF_T6_SEEDFUSE").is_ok_and(|v| v == "1") && enabled() && lf_seams() && seed_half()
}
pub(crate) fn square_seed_r0(c: &mut Builder, b2: &[QubitId], out: &[QubitId]) {
    let w0 = envelope()[0].max(N + 4);
    let fs = seam_fs();
    let x = out;
    let ov = super::modular::r4_addsub_head(c, b2, x); // ~x + b2: carry = [b2 > x]
    c.x_all(x); // x = D mod 2^256
    let e = c.alloc_qubit();
    c.cx(x[0], e);
    c.x(e); // [D even]
    c.x(ov);
    let g = and_new(c, e, ov); // D >= 0 even: - p
    c.x(ov);
    let mut r0 = x.to_vec();
    // ext outlives the square's fold scope: keep it off the wires the square lent its folds (reacquired after)
    let loans = super::square::SQ_LOANS.with(|l| l.borrow().clone());
    c.set_avoid(&loans);
    let ext = c.alloc_qubits(w0 - N);
    c.set_avoid(&[]);
    c.cx(ov, ext[0]);
    c.cx(e, ext[0]); // sign(R0) = ov ^ [D even]
    for &q in &ext[1..] {
        c.cx(ext[0], q);
    }
    r0.extend(ext.iter().copied());
    let nf = alloy_primitives::U256::ZERO.wrapping_sub(f()) & low_mask(fs);
    let add: Vec<Vec<QubitId>> = (0..fs)
        .map(|i| {
            let mut v = Vec::new();
            if f().bit(i) != nf.bit(i) { v.push(g); }
            if nf.bit(i) { v.push(e); }
            v
        })
        .collect();
    ladder_parity_add(c, &r0[..fs], &add, None);
    c.x(ov);
    and_erase(c, g, e, ov);
    c.x(ov);
    c.cx(ext[0], e);
    c.cx(ov, e);
    c.free(e);
    let k = super::modular::erase_compare();
    c.x_all(&r0[N - k..N]);
    super::compare::erase_with_compare(c, ov, &r0[N - k..N], &b2[N - k..N], None);
    c.x_all(&r0[N - k..N]);
    c.free(ov);
    T6_PRESEED.with(|s| *s.borrow_mut() = Some(r0));
}

/// Back seam (`LF_SEAMS`): from R (odd, |R| < p, two's complement on `r` = low N wires + sign copies) to
/// x = (R + C) mod p on the low N wires (returned; the sign wires are freed), without forming d = R + p [R < 0].
/// The register gets `add` (= C, or C + 1 over a complemented R for the reverse subtraction); `cb` = C. With
/// L = (R_low + C) mod 2^256 and ov its carry, x = L + (ov - sign) f exactly; then sign = 1 ^ x0 ^ C0 ^ ov and
/// ov = [x < C] (erased by a top-window phase compare, as the coordinate shell erases its overflow).
fn seam_add_reduce(c: &mut Builder, r: Vec<QubitId>, add: &[crate::circuit::BitId], cb: &[crate::circuit::BitId]) -> Vec<QubitId> {
    let w = r.len();
    let fs = seam_fs();
    let sgn = r[w - 1];
    for &q in &r[N..w - 1] {
        c.cx(sgn, q);
        c.free(q);
    }
    let low = r[..N].to_vec();
    let ov = c.alloc_qubit();
    super::modular::r5_ripple_add_cbits(c, add, &low, ov);
    c.x(sgn);
    let plus = and_new(c, ov, sgn); // ov & !sign: + f
    c.x(sgn);
    // + f plus - f minus with minus = ov ^ sign ^ plus: addend bit i = (f_i ^ nf_i) plus ^ nf_i (ov ^ sign)
    let nf = alloy_primitives::U256::ZERO.wrapping_sub(f()) & low_mask(fs);
    let lists: Vec<Vec<QubitId>> = (0..fs)
        .map(|i| {
            let mut v = Vec::new();
            if f().bit(i) != nf.bit(i) { v.push(plus); }
            if nf.bit(i) { v.push(ov); v.push(sgn); }
            v
        })
        .collect();
    ladder_parity_add(c, &low[..fs], &lists, None);
    c.x(sgn);
    and_erase(c, plus, ov, sgn);
    c.x(sgn);
    c.cx(low[0], sgn);
    c.cx(ov, sgn);
    c.x(sgn);
    c.x_if_bit(sgn, cb[0]);
    c.free(sgn);
    let k = super::modular::erase_compare();
    let tv = c.alloc_qubits(k);
    for i in 0..k {
        c.x_if_bit(tv[i], cb[N - k + i]);
    }
    super::compare::erase_with_compare(c, ov, &low[N - k..], &tv, None);
    for i in 0..k {
        c.x_if_bit(tv[i], cb[N - k + i]);
    }
    c.free_vec(&tv);
    c.free(ov);
    low
}

/// Tie-safe payload cell: the head's seeded compares need, on exact ties, pred = sign ^ [P_T == -P_S];
/// post-park P = lambda * (+-1, +-1), so the negation flag is the xor of the rails' sign bits. Only ticks in
/// tie-safe mode (see [`tie_from`]) get the predicate wire.
/// `LF_TIE_SEED=1` (pingpong `tie_borrow`): tie mode keeps the routes bypassed but the compares use their own seeded
/// predictors, so the predictor wire is never read: [`tie_pred`] marks tie mode with the cell's sign wire instead of
/// allocating one (one more wire of room for the late cells).
fn tie_seed() -> bool {
    static T: OnceLock<bool> = OnceLock::new();
    *T.get_or_init(|| std::env::var("LF_TIE_SEED").is_ok_and(|v| v == "1"))
}
fn tie_pred(c: &mut Builder, t: usize, s: QubitId, tsign: QubitId, ssign: QubitId) -> Option<QubitId> {
    if t < tie_from() {
        return None;
    }
    if tie_seed() {
        return Some(s);
    }
    let q = c.alloc_qubit();
    c.cx(s, q);
    c.cx(tsign, q);
    c.cx(ssign, q);
    Some(q)
}
fn tie_unpred(c: &mut Builder, q: Option<QubitId>, s: QubitId, tsign: QubitId, ssign: QubitId) {
    let Some(q) = q else { return };
    if tie_seed() {
        return;
    }
    c.cx(s, q);
    c.cx(tsign, q);
    c.cx(ssign, q);
    c.free(q);
}

/// Compare-width shifts (chunk-boundary dB, overflow-flag dF) applied to every Leapfrog payload cell
/// (`LF_CMP_SHIFT=dB,dF`; each +1 halves that compare's miss rate for about one Toffoli per cell).
fn cmp_shift() -> (isize, isize) {
    static S: OnceLock<(isize, isize)> = OnceLock::new();
    *S.get_or_init(|| {
        let v = std::env::var("LF_CMP_SHIFT").unwrap_or_else(|_| "0,0".into());
        let (a, b) = v.split_once(',').expect("LF_CMP_SHIFT=dB,dF");
        (a.trim().parse().unwrap(), b.trim().parse().unwrap())
    })
}

/// Payload ties (P_T = +-P_S) need R_T = +-R_S, i.e. a parked walk (the rails stay coprime); the earliest park in
/// 640k walks is tick 108. Before tick LF_TIE_FROM (default 0 = always) the cells run without the tie-safe mode,
/// which re-enables the replay cell's prebias / width-composition routes.
fn tie_from() -> usize {
    static F: OnceLock<usize> = OnceLock::new();
    *F.get_or_init(|| std::env::var("LF_TIE_FROM").ok().and_then(|v| v.parse().ok()).unwrap_or(0))
}

/// [`cmp_shift`] applied from tick LF_CMP_FROM on (default 0 = every tick).
fn cmp_shift_at(t: usize) -> (isize, isize) {
    static F: OnceLock<usize> = OnceLock::new();
    let from = *F.get_or_init(|| std::env::var("LF_CMP_FROM").ok().and_then(|v| v.parse().ok()).unwrap_or(0));
    if t >= from { cmp_shift() } else { (0, 0) }
}

fn proxy_fold(w: usize, multiply: bool) -> (usize, usize) {
    let w = std::env::var("LF_PROXY_MIN").ok().and_then(|v| v.parse::<usize>().ok()).map_or(w, |m| w.max(m));
    let proxy = cells::proxy_round(w);
    let extra: usize = std::env::var("LF_CELL_FOLD_EXTRA").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let floor: usize = std::env::var("LF_CELL_FOLD_MIN").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    (((cells::fold_window(proxy, multiply) + extra).max(floor)).min(N - 8), proxy)
}

/// `LF_TAIL_FORCED=n` (n = 0 or 1): the last tick keeps its choice step and shift but only n forced steps (a letter
/// of n + 3 bits); the one forced step runs at the row's first width and the choice step at the row's own n2, nb.
/// Unset: 2, a tick like every other. Fewer forced steps raise the walk's failure rate; the pinned width table
/// was fitted with n = 0.
fn tail_forced(t: usize) -> usize {
    static T: OnceLock<usize> = OnceLock::new();
    let n = *T.get_or_init(|| std::env::var("LF_TAIL_FORCED").ok().and_then(|v| v.parse().ok()).map_or(2, |n: usize| n.min(2)));
    if t + 1 == rounds() { n } else { 2 }
}

/// Forward tick t; when `pay` is given, the division payload is updated alongside.
fn fwd_tick(c: &mut Builder, wk: &mut Walk, t: usize, mut pay: Option<&mut [Vec<QubitId>; 2]>) {
    if lf_fast() {
        return fwd_tick_fast(c, wk, t, pay);
    }
    let env = envelope();
    let w = env[t];
    if pay.is_some() && std::env::var_os("LF_PROFILE").is_some() {
        eprintln!("LF_PROF t={t} w={w} active={} peak_so_far={}", c.active_qubits(), c.peak_total());
    }
    let (ti, si) = (t % 2, 1 - t % 2);
    let [r_a, r_b] = &mut wk.r;
    let (tr, br) = if ti == 0 { (r_a, r_b) } else { (r_b, r_a) };
    resize(c, tr, w);
    resize(c, br, w);
    let (fold, proxy) = proxy_fold(w, false);
    let m = forced();
    let mut letter = vec![QubitId(0); if pp_mode() { 1 } else { m + 3 }];
    for i in 0..m {
        let s = c.alloc_qubit();
        pp_sign_into(c, tr, br, s);
        rail_add_halve(c, s, br, tr);
        if let Some(p) = pay.as_deref_mut() {
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            let pr = tie_pred(c, usize::MAX, s, *tr.last().unwrap(), *br.last().unwrap());
            cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::add_halve(c, s, &ps, &pt, fold, proxy)));
            tie_unpred(c, pr, s, *tr.last().unwrap(), *br.last().unwrap());
        }
        letter[i] = s;
    }
    if pp_mode() {
        wk.tape.push(letter);
        let wn = env.get(t + 1).copied().unwrap_or(w);
        resize(c, tr, wn);
        resize(c, br, wn);
        return;
    }
    let s3 = c.alloc_qubit();
    let wq = w.max(6);
    resize(c, tr, wq);
    resize(c, br, wq);
    choice_xor(c, tr, br, s3);
    resize(c, tr, w);
    resize(c, br, w);
    rail_add_halve(c, s3, br, tr);
    if let Some(p) = pay.as_deref_mut() {
        let (pt, ps) = (p[ti].clone(), p[si].clone());
        let pr = tie_pred(c, usize::MAX, s3, *tr.last().unwrap(), *br.last().unwrap());
        cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::add_halve(c, s3, &ps, &pt, fold, proxy)));
        tie_unpred(c, pr, s3, *tr.last().unwrap(), *br.last().unwrap());
    }
    letter[m] = s3;
    let (k1, k2) = (c.alloc_qubit(), c.alloc_qubit());
    barrel_bits_xor(c, tr, k1, k2);
    if old_barrel() {
        crot_down_fix(c, k1, tr);
        crot2_down_fix(c, k2, tr);
    } else {
        rail_barrel(c, k1, k2, tr, false);
    }
    if let Some(p) = pay.as_deref_mut().filter(|_| std::env::var("LF_NOBAR").is_err()) {
        if old_barrel() {
            cmod_halve(c, k1, &p[ti]);
            cmod_quarter(c, k2, &p[ti]);
        } else {
            cmod_barrel(c, k1, k2, &p[ti], false);
        }
    }
    letter[m + 1] = k1;
    letter[m + 2] = k2;
    wk.tape.push(letter);
    let wn = env.get(t + 1).copied().unwrap_or(w);
    resize(c, tr, wn);
    resize(c, br, wn);
}

/// [`fwd_tick`] on the fast rail path (`LF_FAST=1`); same letters and payload cells.
fn fwd_tick_fast(c: &mut Builder, wk: &mut Walk, t: usize, mut pay: Option<&mut [Vec<QubitId>; 2]>) {
    let st = steps();
    let [w, n0, n1, n2, nb] = st[t];
    if pay.is_some() && std::env::var_os("LF_PROFILE").is_some() {
        eprintln!("LF_PROF t={t} w={w} active={} peak_so_far={}", c.active_qubits(), c.peak_total());
    }
    let (ti, si) = (t % 2, 1 - t % 2);
    let [r_a, r_b] = &mut wk.r;
    let (tr, br) = if ti == 0 { (r_a, r_b) } else { (r_b, r_a) };
    let (fold, proxy) = proxy_fold(w, false);
    let fk = if pay.is_some() { "F" } else { "R" };
    let tick0 = pmark(c);
    let mut letter = Vec::with_capacity(5);
    // LF_TRIM: during payload ops hold the rails at the widths this tick truncates them to anyway (target: the
    // next step's width; source: min(W(t), W(t+1))), so the cells get the freed wires as scratch.
    let wn = st.get(t + 1).map(|r| r[0]).unwrap_or(w);
    let trim = lf_trim() && pay.is_some();
    let sw = lf_signwire() && pay.is_some();
    let bw = |n: usize| if sw { n.min(w).min(wn) } else { n };
    // LF_LOWREL: o = 1 while the rails are held without their bit-0 wire (the widths below are full widths)
    let lr = lowrel();
    let o = lr as usize;
    let mut yp8_trio: Option<(QubitId, QubitId, QubitId)> = None;
    let fsteps: Vec<(usize, usize)> = match tail_forced(t) {
        2 => vec![(n0, n1), (n1, n2)],
        1 => vec![(n0, n2)],
        _ => Vec::new(),
    };
    // The LF_YP8 rule runs inside forced move 2's add, so it is off at tick 0 under LF_T0_FREE (that tick keeps its
    // own rule, a function of R1 alone) and on a last tick with fewer forced steps (LF_TAIL_FORCED: that tick takes
    // the LF_W1 rule of [`fast_choice`])
    let yp8_here = yp8().is_some() && !t0_plain(t) && tail_forced(t) == 2;
    // y15-room: on these fused ticks the three payload ops run as one one-fold tick at the merged op's place (the two
    // cells below are left out; they act on the payload registers and read only the letter)
    let y15f = pay.is_some() && y15::fused_fwd_on(t);
    assert!(!y15f || (tail_forced(t) == 2 && t < tie_from() && t > 0), "y15 fused tick out of range");
    let mut y16_ops: Vec<(&'static str, usize, f64, f64, f64, f64)> = Vec::new();
    for (nk, nnext) in fsteps {
        if yp8_here && letter.len() == 1 {
            // LF_YP8: forced move 2's payload cell first (it reads only the letter), then the rail add with the
            // choice inside it
            let s = c.alloc_qubit();
            pp_sign_into1(c, tr[1 - o], br[1 - o], s);
            let q0 = pmark(c);
            if let Some(p) = pay.as_deref_mut().filter(|_| !y15f) {
                let (pt, ps) = (p[ti].clone(), p[si].clone());
                let pads = lr_pad_c(c, 2 * o);
                let pr = tie_pred(c, t, s, *tr.last().unwrap(), *br.last().unwrap());
                let y16_m = y16_mark(c, t, 0, 1);
                cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift_at(t), || cells::add_halve(c, s, &ps, &pt, fold, proxy)));
                y16_note(c, &mut y16_ops, "cell", y16_m);
                tie_unpred(c, pr, s, *tr.last().unwrap(), *br.last().unwrap());
                lr_unpad(c, pads);
            }
            pacc(c, &format!("fwd{fk}.pay_cell"), q0);
            if pay.is_some() {
                pacc(c, &format!("pc.fwd.t{t:03}"), q0);
            }
            resize(c, tr, nk - o);
            resize(c, br, bw(nk) - o);
            let trio = (c.alloc_qubit(), c.alloc_qubit(), c.alloc_qubit());
            let q0 = pmark(c);
            y28_key(t * 4 + 1);
            yp8_add_halve_forced_choice(c, s, br, tr, trio.0, trio.1, trio.2, t);
            y28_key(usize::MAX);
            pacc(c, &format!("fwd{fk}.yp8_forced"), q0);
            yp8_trio = Some(trio);
            letter.push(s);
            continue;
        }
        resize(c, tr, nk - o);
        resize(c, br, bw(nk) - o);
        let s = c.alloc_qubit();
        pp_sign_into1(c, tr[1 - o], br[1 - o], s);
        let q0 = pmark(c);
        y28_key(t * 4 + letter.len());
        if lr {
            fast_add_halve_forced_lr(c, s, br, tr);
        } else {
            fast_add_halve_forced(c, s, br, tr);
        }
        y28_key(usize::MAX);
        pacc(c, &format!("fwd{fk}.rail_forced"), q0);
        let q0 = pmark(c);
        if let Some(p) = pay.as_deref_mut() {
            if trim {
                let (wt, wb) = (tr.len() + o, br.len() + o);
                resize(c, tr, wt.min(nnext) - o);
                resize(c, br, wb.min(w).min(wn) - o);
            }
            if !y15f {
                let (pt, ps) = (p[ti].clone(), p[si].clone());
                let pads = lr_pad_c(c, 2 * o);
                let pr = tie_pred(c, t, s, *tr.last().unwrap(), *br.last().unwrap());
                let y16_m = y16_mark(c, t, 0, letter.len().min(1));
                cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift_at(t), || cells::add_halve(c, s, &ps, &pt, fold, proxy)));
                y16_note(c, &mut y16_ops, "cell", y16_m);
                tie_unpred(c, pr, s, *tr.last().unwrap(), *br.last().unwrap());
                lr_unpad(c, pads);
            }
        }
        pacc(c, &format!("fwd{fk}.pay_cell"), q0);
        if pay.is_some() {
            pacc(c, &format!("pc.fwd.t{t:03}"), q0);
        }
        letter.push(s);
    }
    resize(c, tr, n2 - o);
    resize(c, br, bw(n2) - o);
    let (s3, k1, k2) = match yp8_trio {
        Some(trio) => trio,
        None => (c.alloc_qubit(), c.alloc_qubit(), c.alloc_qubit()),
    };
    let q0 = pmark(c);
    let t0m = t0_plain(t).then(|| t0_m_on(c, br, letter[0], letter[1]));
    if yp8_trio.is_none() {
        if lr {
            lr_restore(c, tr);
            lr_restore(c, br);
        }
        fast_choice(c, tr, br, s3, k1, k2, t);
        if lr {
            lr_drop(c, br);
            lr_drop(c, tr);
        }
    }
    if let Some(m) = t0m {
        if defer_t0_dq() {
            t0_m_off_keep(c, m); // defer: q's phase goes on at t0_derive
        } else {
            t0_m_off(c, m);
        }
    }
    pacc(c, &format!("fwd{fk}.choice"), q0);
    let q0 = pmark(c);
    y28_key(t * 4 + 2);
    if lr {
        fast_add_halve_choice_lr(c, s3, br, tr);
    } else {
        fast_add_halve_choice(c, s3, br, tr);
    }
    y28_key(usize::MAX);
    pacc(c, &format!("fwd{fk}.rail_choice"), q0);
    if trim {
        let wb = br.len() + o;
        resize(c, br, wb.min(w).min(wn) - o);
    }
    // LF_MERGED: the third cell and the payload barrel become one merged op, run after the rail barrel (they act on
    // disjoint registers); the fit is judged at the live count there (tr at width nb; LF_LOWREL: its bit 0 released).
    let at_barrel = (c.active_qubits() as usize + nb).checked_sub(tr.len() + o).unwrap() + if lr_pad_on() { 2 * o } else { 0 };
    // on tie-safe ticks the merged op runs with the cells' tie predicate (one more live wire)
    let merged = if pay.is_some() { merged_fits(at_barrel + usize::from(t >= tie_from() && !tie_seed()), t, false) } else { None };
    let qc3 = pmark(c);
    let q0 = pmark(c);
    if let Some(p) = pay.as_deref_mut().filter(|_| merged.is_none() && !y15f) {
        let (pt, ps) = (p[ti].clone(), p[si].clone());
        let pads = lr_pad_c(c, o);
        let pr = tie_pred(c, t, s3, *tr.last().unwrap(), *br.last().unwrap());
        let y16_m = y16_mark(c, t, 0, 2);
        cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift_at(t), || cells::add_halve(c, s3, &ps, &pt, fold, proxy)));
        y16_note(c, &mut y16_ops, "cell3", y16_m);
        tie_unpred(c, pr, s3, *tr.last().unwrap(), *br.last().unwrap());
        lr_unpad(c, pads);
        pacc(c, &format!("c3cell.fwd.t{t:03}"), q0);
    }
    pacc(c, &format!("fwd{fk}.pay_cell"), q0);
    resize(c, tr, nb);
    let q0 = pmark(c);
    if fast_rail_barrel(c, k1, k2, tr, false, lr) {
        tr.remove(0); // released inside the barrel
    } else if lr {
        lr_drop(c, tr);
    }
    pacc(c, &format!("fwd{fk}.rail_barrel"), q0);
    let q0 = pmark(c);
    let pads = if pay.is_some() { lr_pad(c, 2 * o) } else { Vec::new() };
    // LF_DIV_PHROT: the divide's last tick leaves its target unrotated (the endpoint measures it away)
    let skip_pay_rot = pay.is_some() && SKIP_PAY_ROT_AT.with(|s| s.get()) == t;
    SKIP_ROT4.with(|s| s.set(skip_pay_rot));
    if let Some(p) = pay.as_deref_mut() {
        if y15f {
            assert_eq!(c.active_qubits() as usize, at_barrel);
            let l5 = [letter[0], letter[1], s3, k1, k2];
            y15::fwd_tick(c, t, &l5, p);
            pacc(c, &format!("fwd{fk}.pay_y15"), q0);
        } else if let Some(mw) = merged {
            assert_eq!(c.active_qubits() as usize, at_barrel);
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            let pr = tie_pred(c, t, s3, *tr.last().unwrap(), *br.last().unwrap());
            let y16_m = y16_mark(c, t, 0, 2);
            cells::with_tie(pr, || {
                cells::with_cmp_shift(cmp_shift_at(t), || cells::with_bridge(proxy, false, || {
                    let split = if pr.is_none() { merged_split(c, proxy, false, false) } else { None };
                    if lf_merged_trace() {
                        eprintln!("LF_MERGED_SPLIT fwd t={t} proxy={proxy} split={split:?} active={}", c.active_qubits());
                    }
                    merged_fwd(c, s3, &ps, &pt, k1, k2, proxy, split, mw)
                }))
            });
            y16_note(c, &mut y16_ops, "merged", y16_m);
            tie_unpred(c, pr, s3, *tr.last().unwrap(), *br.last().unwrap());
            pacc(c, &format!("fwd{fk}.pay_merged"), q0);
        } else {
            let y16_m = y16_mark(c, t, 0, 2);
            cmod_barrel(c, k1, k2, &p[ti], false);
            y16_note(c, &mut y16_ops, "barrel", y16_m);
            pacc(c, &format!("c3bar.fwd.t{t:03}"), q0);
        }
        if !y15f && y15::trace() {
            y16_print("fwd", t, cells::cap().saturating_sub(at_barrel), &format!("merged={merged:?} fold_cost={:.1} tie={}", Y16_FOLD.with(|f| f.replace(0.0)), t >= tie_from()), &y16_ops);
        }
    }
    SKIP_ROT4.with(|s| s.set(false));
    lr_unpad(c, pads);
    pacc(c, &format!("fwd{fk}.pay_barrel"), q0);
    if pay.is_some() {
        pacc(c, &format!("c3b.fwd.t{t:03}"), qc3);
    }
    pacc(c, &format!("tick.fwd{fk}.t{:03}", t / 10 * 10), tick0);
    letter.extend([s3, k1, k2]);
    wk.tape.push(letter);
    resize(c, tr, wn - o);
    resize(c, br, wn - o);
}

/// Exact inverse of [`fwd_tick_fast`].
fn rev_tick_fast(c: &mut Builder, wk: &mut Walk, t: usize, mut pay: Option<&mut [Vec<QubitId>; 2]>) {
    let st = steps();
    let [w, n0, n1, n2, nb] = st[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let letter = wk.tape.pop().expect("tape underflow");
    // nf forced letters, then (s3, k1, k2); nf = 2 unless LF_TAIL_FORCED on the last tick (then s1, s0 below name
    // the forced letters that exist, and the loops over them stop at nf)
    let nf = tail_forced(t);
    assert_eq!(letter.len(), nf + 3, "letter size");
    let (s0, s1, s3, k1, k2) = (letter[0], letter[nf.saturating_sub(1)], letter[nf], letter[nf + 1], letter[nf + 2]);
    let [r_a, r_b] = &mut wk.r;
    let (tr, br) = if ti == 0 { (r_a, r_b) } else { (r_b, r_a) };
    // LF_TRIM: the forward tick left the target within min(nb, W(t+1)) bits and the source within
    // min(W(t), W(t+1)); keep them there through the payload ops instead of widening to W(t) first.
    let wn = st.get(t + 1).map(|r| r[0]).unwrap_or(w);
    let sw = lf_signwire() && pay.is_some();
    let bw = |n: usize| if sw { n.min(w).min(wn) } else { n };
    let lr = lowrel();
    let o = lr as usize;
    if lf_trim() && pay.is_some() {
        resize(c, tr, nb.min(wn) - o);
        resize(c, br, w.min(wn) - o);
    } else {
        resize(c, tr, w - o);
        resize(c, br, w - o);
    }
    let (fold, proxy) = proxy_fold(w, true);
    let fk = if pay.is_some() { "F" } else { "R" };
    let tick0 = pmark(c);
    let pads = if pay.is_some() { lr_pad(c, 2 * o) } else { Vec::new() };
    // y15-room: on these fused ticks the three payload ops run as one reverse one-fold tick
    let y15r = pay.is_some() && y15::fused_rev_on(t);
    assert!(!y15r || (nf == 2 && t < tie_from() && t > 0), "y15 fused tick out of range");
    if y15r {
        let q0 = pmark(c);
        let l5 = [s0, s1, s3, k1, k2];
        y15::rev_tick(c, t, &l5, pay.as_deref_mut().unwrap());
        pacc(c, "revF.pay_y15", q0);
    }
    // y17: the trace's ops of this tick-pass, and which reverse cells run late (Y17_PLAN): the cell of forced letter 2
    // may run late only if that of letter 1 does (the payload order is merged op, cell 2, cell 1)
    let mut y16_ops: Vec<(&'static str, usize, f64, f64, f64, f64)> = Vec::new();
    let mut y16_info: Option<(usize, String)> = None;
    let y17_three = pay.is_some() && !y15r && nf == 2;
    let y17_late = [y17_three && y17_plan(1, t, 0).2, y17_three && y17_plan(1, t, 1).2];
    assert!(!y17_late[1] || y17_late[0], "y17: cell 2 late needs cell 1 late");
    if let Some(p) = pay.as_deref_mut().filter(|_| !y15r) {
        let q0 = pmark(c);
        let y16_room = cells::cap().saturating_sub(c.active_qubits() as usize);
        let merged = merged_fits(c.active_qubits() as usize + usize::from(t >= tie_from() && !tie_seed()), t, true);
        if let Some(mw) = merged {
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            // the reverse runs the cell's frame with the sign flipped (as double_add with s^1): predicate of NOT s3
            let pr = (t >= tie_from()).then(|| {
                c.x(s3);
                let pr = tie_pred(c, t, s3, *tr.last().unwrap(), *br.last().unwrap());
                c.x(s3);
                pr
            }).flatten();
            let y16_m = y16_mark(c, t, 1, 2);
            cells::with_tie(pr, || {
                cells::with_cmp_shift(cmp_shift_at(t), || cells::with_bridge(proxy, true, || merged_rev(c, s3, &ps, &pt, k1, k2, proxy, pr.is_none(), mw)))
            });
            y16_note(c, &mut y16_ops, "merged", y16_m);
            if pr.is_some() {
                c.x(s3);
                tie_unpred(c, pr, s3, *tr.last().unwrap(), *br.last().unwrap());
                c.x(s3);
            }
            pacc(c, "revF.pay_merged", q0);
            pacc(c, &format!("c3b.rev.t{t:03}"), q0);
        } else {
            let y16_m = y16_mark(c, t, 1, 2);
            cmod_barrel(c, k1, k2, &p[ti], true);
            y16_note(c, &mut y16_ops, "barrel", y16_m);
            pacc(c, &format!("c3bar.rev.t{t:03}"), q0);
        }
        pacc(c, "revF.pay_barrel", q0);
        let qc3 = q0;
        let q0 = pmark(c);
        for (j, s) in [s3, s1, s0].into_iter().enumerate() {
            if j > nf || (merged.is_some() && s == s3) || (j == 1 && y17_late[1]) || (j == 2 && y17_late[0]) {
                continue;
            }
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            let q0f = pmark(c);
            c.x(s);
            let cp = lr_pad_c2(c, 2 * o);
            let pr = tie_pred(c, t, s, *tr.last().unwrap(), *br.last().unwrap());
            let y16_m = y16_mark(c, t, 1, if s == s3 { 2 } else if s == s1 { 1 } else { 0 });
            cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift_at(t), || cells::double_add(c, s, &ps, &pt, fold, proxy)));
            y16_note(c, &mut y16_ops, if s == s3 { "cell3" } else { "cell" }, y16_m);
            tie_unpred(c, pr, s, *tr.last().unwrap(), *br.last().unwrap());
            lr_unpad(c, cp);
            c.x(s);
            if s == s3 {
                pacc(c, &format!("c3b.rev.t{t:03}"), qc3);
            } else {
                pacc(c, &format!("pc.rev.t{t:03}"), q0f);
            }
        }
        y16_info = Some((y16_room, format!("merged={merged:?} fold_cost={:.1} tie={}", Y16_FOLD.with(|f| f.replace(0.0)), t >= tie_from())));

        pacc(c, "revF.pay_cell", q0);
    }
    lr_unpad(c, pads);
    resize(c, tr, nb - o);
    resize(c, br, bw(n2) - o);
    let q0 = pmark(c);
    if lr {
        lr_restore(c, tr);
    }
    fast_rail_barrel(c, k1, k2, tr, true, false);
    pacc(c, &format!("rev{fk}.rail_barrel"), q0);
    resize(c, tr, n2 - 1);
    let q0 = pmark(c);
    fast_k_erase(c, tr, k1, k2);
    pacc(c, &format!("rev{fk}.k_erase"), q0);
    let q0 = pmark(c);
    y28_key(t * 4 + 2);
    if lr {
        fast_double_sub_choice_lr(c, s3, br, tr);
    } else {
        fast_double_sub_choice(c, s3, br, tr);
    }
    y28_key(usize::MAX);
    pacc(c, &format!("rev{fk}.rail_choice"), q0);
    let q0 = pmark(c);
    // LF_YP8: the choice letter is measured here; its phase fix runs inside the reversal of forced move 2's add
    let yp8_m = yp8().filter(|_| !t0_plain(t) && tail_forced(t) == 2).map(|_| {
        let m = c.alloc_bit();
        c.hmr(s3, m);
        c.release_clean(s3);
        m
    });
    let t0m = t0_plain(t).then(|| t0_m_on(c, br, s0, s1));
    if yp8_m.is_none() {
        if lr {
            lr_restore(c, tr);
            lr_restore(c, br);
        }
        fast_choice_erase(c, tr, br, s3, t);
        if lr {
            lr_drop(c, br);
            lr_drop(c, tr);
        }
    }
    if let Some(m) = t0m {
        t0_m_off(c, m);
    }
    pacc(c, &format!("rev{fk}.choice_erase"), q0);
    for (s, nk) in [(s1, n1), (s0, n0)].into_iter().skip(2 - nf) {
        resize(c, tr, nk - 1 - o);
        resize(c, br, bw(nk) - o);
        // y17: a late cell (it touches the payload registers and reads only its letter, which is still live here)
        let y17_slot = usize::from(s == s1 && nf == 2);
        if y17_late[y17_slot] {
            let p = pay.as_deref_mut().expect("y17: a late cell has a payload");
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            c.x(s);
            let pr = tie_pred(c, t, s, *tr.last().unwrap(), *br.last().unwrap());
            assert!(pr.is_none(), "y17: late cells are not built for tie-safe ticks");
            let y16_m = y16_mark(c, t, 1, y17_slot);
            cells::with_cmp_shift(cmp_shift_at(t), || cells::double_add(c, s, &ps, &pt, fold, proxy));
            y16_note(c, &mut y16_ops, "cell", y16_m);
            c.x(s);
        }
        let q0 = pmark(c);
        y28_key(t * 4 + y17_slot);
        if let (Some(m), true) = (yp8_m, s == s1) {
            yp8_double_sub_forced_erase(c, s, br, tr, m, t);
            c.free_bit(m);
            pacc(c, &format!("rev{fk}.yp8_forced"), q0);
        } else if lr {
            fast_double_sub_forced_lr(c, s, br, tr);
        } else {
            fast_double_sub_forced(c, s, br, tr);
        }
        y28_key(usize::MAX);
        pacc(c, &format!("rev{fk}.rail_forced"), q0);
        pp_sign_into1(c, tr[1 - o], br[1 - o], s);
        c.free(s);
    }
    if let Some((room, extra)) = y16_info {
        if y15::trace() {
            y16_print("rev", t, room, &extra, &y16_ops);
        }
    }
    pacc(c, &format!("tick.rev{fk}.t{:03}", t / 10 * 10), tick0);
    resize(c, tr, w - o);
    resize(c, br, w - o);
}

/// Exact inverse of [`fwd_tick`]; with `pay`, applies the multiply-direction payload cells first.
fn rev_tick(c: &mut Builder, wk: &mut Walk, t: usize, mut pay: Option<&mut [Vec<QubitId>; 2]>) {
    if lf_fast() {
        return rev_tick_fast(c, wk, t, pay);
    }
    let env = envelope();
    let w = env[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let letter = wk.tape.pop().expect("tape underflow");
    let [r_a, r_b] = &mut wk.r;
    let (tr, br) = if ti == 0 { (r_a, r_b) } else { (r_b, r_a) };
    resize(c, tr, w);
    resize(c, br, w);
    let m = forced();
    let (fold, proxy) = proxy_fold(w, true);
    if pp_mode() {
        let s = letter[0];
        if let Some(p) = pay.as_deref_mut() {
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            c.x(s);
            let pr = tie_pred(c, usize::MAX, s, *tr.last().unwrap(), *br.last().unwrap());
            cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::double_add(c, s, &ps, &pt, fold, proxy)));
            tie_unpred(c, pr, s, *tr.last().unwrap(), *br.last().unwrap());
            c.x(s);
        }
        rail_double_sub(c, s, br, tr);
        pp_sign_into(c, tr, br, s);
        c.free(s);
        return;
    }
    let (k1, k2) = (letter[m + 1], letter[m + 2]);
    if let Some(p) = pay.as_deref_mut() {
        if old_barrel() {
            cmod_quadruple(c, k2, &p[ti]);
            cmod_double(c, k1, &p[ti]);
        } else {
            cmod_barrel(c, k1, k2, &p[ti], true);
        }
        for i in (0..=m).rev() {
            let s = letter[i];
            let (pt, ps) = (p[ti].clone(), p[si].clone());
            c.x(s);
            let pr = tie_pred(c, usize::MAX, s, *tr.last().unwrap(), *br.last().unwrap());
            cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::double_add(c, s, &ps, &pt, fold, proxy)));
            tie_unpred(c, pr, s, *tr.last().unwrap(), *br.last().unwrap());
            c.x(s);
        }
    }
    if old_barrel() {
        crot2_up_fix(c, k2, tr);
        crot_up_fix(c, k1, tr);
    } else {
        rail_barrel(c, k1, k2, tr, true);
    }
    barrel_bits_xor(c, tr, k1, k2);
    c.free(k1);
    c.free(k2);
    rail_double_sub(c, letter[m], br, tr);
    let wq = w.max(6);
    resize(c, tr, wq);
    resize(c, br, wq);
    choice_xor(c, tr, br, letter[m]);
    resize(c, tr, w);
    resize(c, br, w);
    c.free(letter[m]);
    for i in (0..m).rev() {
        let s = letter[i];
        rail_double_sub(c, s, br, tr);
        pp_sign_into(c, tr, br, s);
        c.free(s);
    }
}

// ---- choice rule `LF_YP8` (pinned in [`install_recipe`]) ----
//
// `LF_YP8=L` (anchors = choice-step width - 3, see [`w1_anchor`]): in the equal-sign case, with Y = [a > 2b] on
// the L-bit window (ones' complement magnitudes of target and source, window top = the register's top magnitude
// bit) and the class of forced move 2 (added magnitudes / subtracted / subtracted and the target's sign flipped):
//   v = 2: deep iff Y or flipped;   v = 3: flat iff not Y and added;   v = 4: deep;   v >= 5: flat (as without
//   this rule).
// The class needs the target's sign BEFORE forced move 2. After that move it is not a linear function of live wires:
// with c_top = the carry into the top position of the move's add,  added = 1 ^ sign(T) ^ c_top  and
// not flipped = 1 ^ c_top ^ sign(+-B). So the choice logic (forward) and the letter's erase (backward) run INSIDE
// that add, between its carry sweep and its sum sweep, where every carry is still on a wire
// ([`ladder_parity_add_mid`]); the top carry is held on a wire too (the lean ladder XORs it straight into the sum).
fn yp8() -> Option<usize> {
    static Y: OnceLock<Option<usize>> = OnceLock::new();
    *Y.get_or_init(|| {
        let l = std::env::var("LF_YP8").ok().and_then(|v| v.parse::<usize>().ok()).filter(|&l| l >= 4)?;
        assert!(lf_fast() && lf_w1() && lowrel(), "LF_YP8 needs the fast, W1, low-released rail path");
        Some(l)
    })
}

/// [`ladder_parity_add`] with every carry on a wire (the top one too: same Toffoli count, one more wire) and a pause
/// between the carry sweep and the sum sweep: `mid(c, carry)` runs with `acc` untouched and carry[i] = the carry into
/// position i (carry[0] = cin). `mid` must leave every wire as it found it.
fn ladder_parity_add_mid(c: &mut Builder, acc: &[QubitId], add: &[Vec<QubitId>], cin: Option<QubitId>, mid: &mut dyn FnMut(&mut Builder, &[Option<QubitId>])) {
    let n = acc.len();
    let mut y28h = Y28_HOOK.with(|x| x.take());
    let mut carry: Vec<Option<QubitId>> = vec![None; n];
    carry[0] = cin;
    for i in 0..n - 1 {
        let ci = carry[i];
        if ci.is_none() && add[i].is_empty() {
            continue;
        }
        if let Some(ci) = ci {
            c.cx(ci, acc[i]);
        }
        let v = v_on(c, &add[i], false, ci);
        let t = and_new(c, acc[i], v);
        v_off(c, &add[i], false, ci);
        if let Some(ci) = ci {
            c.cx(ci, t);
            c.cx(ci, acc[i]);
        }
        carry[i + 1] = Some(t);
        y28_apply(c, &mut y28h, i + 1, t);
    }
    assert!(y28h.is_none(), "y28: the kept bit's boundary carry is on no wire of this paused ladder");
    mid(c, &carry);
    for i in (0..n).rev() {
        let ci = carry[i];
        if i + 1 < n {
            if let Some(next) = carry[i + 1] {
                if let Some(ci) = ci {
                    c.cx(ci, next);
                    c.cx(ci, acc[i]);
                }
                let v = v_on(c, &add[i], false, ci);
                and_erase(c, next, acc[i], v);
                v_off(c, &add[i], false, ci);
                if let Some(ci) = ci {
                    c.cx(ci, acc[i]);
                }
            }
        }
        for &q in &add[i] {
            c.cx(q, acc[i]);
        }
        if let Some(ci) = ci {
            c.cx(ci, acc[i]);
        }
    }
}

/// `LF_YP8_CHUNK=1`: see [`rail_add_mid`] (both directions).
fn yp8_chunk() -> bool {
    std::env::var("LF_YP8_CHUNK").is_ok_and(|v| v == "1")
}
/// Phase-only [`carry_out_parity_xor`] (`out = None`) under the walk cap: when its carries do not fit, the carry-out
/// of a room-sized low chunk goes onto a kept wire (computed, used as the rest's carry-in, then computed again to
/// clear it; acc is unchanged throughout).
fn carry_out_capped(c: &mut Builder, acc: &[QubitId], add: &[Vec<QubitId>], comp: bool, cin: QubitId, out: Option<QubitId>) {
    let n = acc.len();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    if n + 2 <= room || room < 8 {
        carry_out_parity_xor(c, acc, add, comp, cin, out);
        return;
    }
    let l = room - 4;
    let k = c.alloc_qubit();
    carry_out_parity_xor(c, &acc[..l], &add[..l], comp, cin, Some(k));
    carry_out_capped(c, &acc[l..], &add[l..], comp, k, out);
    carry_out_parity_xor(c, &acc[..l], &add[..l], comp, cin, Some(k));
    c.free(k);
}
/// [`rail_add`] (`b += a + cin`, `a` possibly shorter) with a pause that leaves `reserve` wires of room under the
/// walk cap: `mid(c, add, delta, carry)` runs with positions delta.. of `b` untouched and carry[j] = the carry into
/// position delta + j (so carry.last() is the carry into the top position).
/// Split when the carries plus the reserve do not fit:
///   * `fwd`: the low `delta` positions are added first (their sums are already written at the pause), kept carry
///     erased by the usual MBU compare;
///   * `!fwd`: the low part's carry-out is computed first WITHOUT writing its sums (so all of `b` is untouched at the
///     pause), the high part runs with the pause, and the low add comes last and clears the kept carry by itself
///     (no compare): 2 delta Toffoli for the low part instead of 1.5 delta.
///     With `low = Some((k, lo))` (the logic reads positions 0..k and nothing else below position `lo`) and `lo` in
///     the high part, the low part is added first as in the plain split and positions 0..k are put back to their
///     pre-add values for the pause only (k - 1 ANDs to recompute their carries): 1.5 delta + k - 1.
fn rail_add_mid(c: &mut Builder, a: &[QubitId], b: &[QubitId], cin: QubitId, reserve: usize, fwd: bool, low: Option<(usize, usize)>,
                mid: &mut dyn FnMut(&mut Builder, &[Vec<QubitId>], usize, &[Option<QubitId>])) {
    let sg = *a.last().unwrap();
    let n = b.len();
    let add: Vec<Vec<QubitId>> = (0..n).map(|i| vec![if i < a.len() { a[i] } else { sg }]).collect();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    let whole = |c: &mut Builder, mid: &mut dyn FnMut(&mut Builder, &[Vec<QubitId>], usize, &[Option<QubitId>])| {
        ladder_parity_add_mid(c, b, &add, Some(cin), &mut |c, carry| mid(c, &add, 0, carry));
    };
    // y28: the mirrored subtract of a split forward add: one whole paused ladder, the kept outcome's phase on its
    // carry into the forward boundary (the carry sweep runs before the pause, under no condition)
    let y28h = y28_fetch(n);
    if let Some(h) = y28h {
        assert!(!fwd, "y28: a kept bit is applied in the reverse pass only");
        assert!(n <= 3 || n - 1 + reserve <= room, "y28: the mirrored paused subtract must be one whole ladder");
        assert!(h.0 >= 1 && h.0 + 1 <= n, "y28: boundary {} outside the paused ladder of {n}", h.0);
        Y28_HOOK.with(|x| x.set(Some(h)));
    }
    if n <= 3 || n - 1 + reserve <= room {
        whole(c, mid);
        assert!(Y28_HOOK.with(|x| x.take()).is_none(), "y28: kept bit not taken by the paused ladder");
        return;
    }
    let mut delta = n + reserve - room;
    // backward, low part first: k - 1 more wires at the pause
    let low_first = low.filter(|&(k, lo)| {
        let d = delta + k - 1;
        !fwd && k >= 1 && d >= k && lo >= d && d + 3 <= room && d + 1 < n && d < a.len()
    });
    if let Some((k, _)) = low_first {
        delta += k - 1;
    }
    // LF_YP8_CHUNK: a low part wider than the room is itself added in room-sized chunks
    // ([`lpa_capped`]) and its kept carry made / erased by a chunked compare ([`carry_out_capped`])
    let chunk = yp8_chunk() && delta + 3 > room && room >= 10;
    if (delta + 3 > room && !chunk) || delta + 1 >= n || delta >= a.len() {
        eprintln!("YP8_NOFIT n={n} room={room} reserve={reserve} delta={delta} fwd={fwd}");
        return whole(c, mid);
    }
    let cq = c.alloc_qubit();
    let mut lo = b[..delta].to_vec();
    lo.push(cq);
    let mut lo_add = add[..delta].to_vec();
    lo_add.push(vec![]);
    if chunk && !fwd {
        let q0 = pmark(c);
        carry_out_capped(c, &b[..delta], &add[..delta], false, cin, Some(cq));
        pacc(c, "split.yp8_carry_chunk", q0);
        ladder_parity_add_mid(c, &b[delta..], &add[delta..], Some(cq), &mut |c, carry| mid(c, &add, delta, carry));
        lpa_capped(c, &lo, &lo_add, Some(cin));
        c.free(cq);
    } else if chunk {
        lpa_capped(c, &lo, &lo_add, Some(cin));
        ladder_parity_add_mid(c, &b[delta..], &add[delta..], Some(cq), &mut |c, carry| mid(c, &add, delta, carry));
        c.x(cin);
        let q0 = pmark(c);
        let m = c.alloc_bit();
        c.hmr(cq, m);
        c.release_clean(cq);
        c.push_condition(m);
        carry_out_capped(c, &b[..delta], &add[..delta], true, cin, None);
        c.pop_condition();
        c.free_bit(m);
        pacc(c, "split.yp8_erase_chunk", q0);
        c.x(cin);
    } else if fwd {
        ladder_parity_add(c, &lo, &lo_add, Some(cin));
        ladder_parity_add_mid(c, &b[delta..], &add[delta..], Some(cq), &mut |c, carry| mid(c, &add, delta, carry));
        c.x(cin);
        let q0 = pmark(c);
        let m = c.alloc_bit();
        c.hmr(cq, m);
        c.release_clean(cq);
        // y28: as in [`capped_add`]
        if !y28_store(delta, n, m) {
            c.push_condition(m);
            carry_out_parity_xor(c, &b[..delta], &add[..delta], true, cin, None);
            c.pop_condition();
            c.free_bit(m);
        }
        pacc(c, "split.yp8_erase", q0);
        c.x(cin);
    } else if let Some((k, _)) = low_first {
        ladder_parity_add(c, &lo, &lo_add, Some(cin));
        ladder_parity_add_mid(c, &b[delta..], &add[delta..], Some(cq), &mut |c, carry| {
            // positions 0..k back to their pre-add values: a_j = s_j ^ addend_j ^ c_j, c_{j+1} = MAJ(a_j, addend_j, c_j)
            let q0 = pmark(c);
            let mut lc: Vec<QubitId> = vec![cin];
            for j in 0..k {
                let cj = lc[j];
                for &q in &add[j] {
                    c.cx(q, b[j]);
                }
                c.cx(cj, b[j]);
                if j + 1 < k {
                    c.cx(cj, b[j]);
                    let v = v_on(c, &add[j], false, Some(cj));
                    let t = and_new(c, b[j], v);
                    v_off(c, &add[j], false, Some(cj));
                    c.cx(cj, t);
                    c.cx(cj, b[j]);
                    lc.push(t);
                }
            }
            pacc(c, "split.yp8_lowback", q0);
            mid(c, &add, delta, carry);
            for j in (0..k).rev() {
                let cj = lc[j];
                if j + 1 < k {
                    let t = lc[j + 1];
                    c.cx(cj, t);
                    c.cx(cj, b[j]);
                    let v = v_on(c, &add[j], false, Some(cj));
                    and_erase(c, t, b[j], v);
                    v_off(c, &add[j], false, Some(cj));
                    c.cx(cj, b[j]);
                }
                c.cx(cj, b[j]);
                for &q in &add[j] {
                    c.cx(q, b[j]);
                }
            }
        });
        c.x(cin);
        let q0 = pmark(c);
        let m = c.alloc_bit();
        c.hmr(cq, m);
        c.release_clean(cq);
        c.push_condition(m);
        carry_out_parity_xor(c, &b[..delta], &add[..delta], true, cin, None);
        c.pop_condition();
        c.free_bit(m);
        pacc(c, "split.yp8_erase_rev", q0);
        c.x(cin);
    } else {
        let q0 = pmark(c);
        carry_out_parity_xor(c, &b[..delta], &add[..delta], false, cin, Some(cq));
        pacc(c, "split.yp8_carry", q0);
        ladder_parity_add_mid(c, &b[delta..], &add[delta..], Some(cq), &mut |c, carry| mid(c, &add, delta, carry));
        ladder_parity_add(c, &lo, &lo_add, Some(cin));
        c.free(cq);
    }
}

/// Which window positions of a register of `len` wires (bit 0 included) are wires at tick t (see [`w1_window`]).
fn yp8_mask(len: usize, t: usize) -> Vec<bool> {
    let h = w1_anchor(t).saturating_sub(w1_kt(t));
    (h..h + w1_kt(t) + 2).map(|p| p + 1 < len).collect()
}
/// Number of ANDs of the chain a + NOT(2b) on these window masks (mirrors [`lit_maj`]'s constant folding).
fn yp8_chain_cost(wa: &[bool], wb: &[bool]) -> usize {
    // 0 = constant 0, 1 = constant 1, 2 = a wire
    let (mut carry, mut n) = (0u8, 0usize);
    for j in 0..wa.len() + 1 {
        let x = if wa.get(j).copied().unwrap_or(false) { 2 } else { 0 };
        let y = if j < 1 || !wb[j - 1] { 1 } else { 2 };
        let v = [x, y, carry];
        carry = if let Some(z) = v.iter().position(|&e| e == 0) {
            let o: Vec<u8> = (0..3).filter(|&i| i != z).map(|i| v[i]).collect();
            if o.contains(&0) { 0 } else if o[0] == 1 { o[1] } else if o[1] == 1 { o[0] } else { n += 1; 2 }
        } else if let Some(z) = v.iter().position(|&e| e == 1) {
            let o: Vec<u8> = (0..3).filter(|&i| i != z).map(|i| v[i]).collect();
            if o.contains(&1) { 1 } else { n += 1; 2 }
        } else {
            n += 1;
            2
        };
    }
    n
}
/// Widths of the logic's full-index views of the target (`tl` wires without bit 0) and the source (`bl`).
fn yp8_views(tl: usize, bl: usize) -> (usize, usize) {
    let tv = (tl + 1).max(6);
    (tv, (bl + 1).max(6).min(tv))
}
/// Wires the logic needs at the pause on top of the add's carries.
fn yp8_reserve(tl: usize, bl: usize, t: usize, fwd: bool) -> usize {
    let (tv, bv) = yp8_views(tl, bl);
    let need0 = w1_anchor(t) <= w1_kt(t);
    yp8_chain_cost(&yp8_mask(tv, t), &yp8_mask(bv, t)) + if fwd { 4 } else { 3 } + 2 * need0 as usize + (tv - tl - 1) + (bl + 1).max(6).saturating_sub(bl + 1)
}

/// The YP8 logic at the pause. `t2`, `b`: target after forced move 2 and source, plain, without their bit-0 wires;
/// `s1`: that move's letter; `ct`: the carry into the top position of its add.
/// `outs = Some((out, k1, k2))`: write the choice letter and the barrel letters (xor into zero wires).
/// `outs = None`: apply the phase (-1)^out (the caller holds the erase's measurement condition).
fn yp8_logic(c: &mut Builder, t2: &[QubitId], b: &[QubitId], s1: QubitId, ct: QubitId, tick: usize, outs: Option<(QubitId, QubitId, QubitId)>) {
    let need0 = w1_anchor(tick) <= w1_kt(tick);
    // full-index views: bit 0 (the constant 1 of an odd rail) is a wire only when the window reads it
    let mut tv: Vec<QubitId> = Vec::with_capacity(t2.len() + 1);
    let mut bv: Vec<QubitId> = Vec::with_capacity(b.len() + 1);
    if need0 {
        for v in [&mut tv, &mut bv] {
            let q = c.alloc_qubit();
            c.x(q);
            v.push(q);
        }
    } else {
        tv.push(t2[0]); // placeholders, never read
        bv.push(b[0]);
    }
    tv.extend_from_slice(t2);
    bv.extend_from_slice(b);
    let (t_real, b_real) = (tv.len(), bv.len());
    for v in [&mut tv, &mut bv] {
        while v.len() < 6 {
            let q = c.alloc_qubit();
            c.cx(*v.last().unwrap(), q);
            v.push(q);
        }
    }
    // a source held wider than the target: its wires past the target's width are sign copies
    let bview: Vec<QubitId> = bv[..bv.len().min(tv.len())].to_vec();
    let top = tv.len() - 1;
    let btop = *bview.last().unwrap();
    // window compare Y = [a > 2b]
    let (wa, wb) = (w1_window(&tv, tick), w1_window(&bview, tick));
    w1_conj(c, &tv, &wa);
    w1_conj(c, &bview, &wb);
    let (w, recs) = w1_chain_s(c, &wa, &wb, 1);
    w1_conj(c, &bview, &wb);
    w1_conj(c, &tv, &wa);
    if let Lit::W(q, _) = w {
        assert!(recs.iter().any(|r| r.t == q), "YP8: the compare's result must be an AND wire");
    }
    // hosts: s1's wire <- not flipped = 1 ^ c_top ^ sign(B) ^ s1;  ct's wire <- added = 1 ^ c_top ^ sign(T2)
    c.cx(ct, s1);
    c.cx(btop, s1);
    c.x(s1);
    c.cx(tv[top], ct);
    c.x(ct);
    zlin_on(c, &tv, &bview);
    // !Y as an AND operand
    let ny = |c: &mut Builder| {
        if let Lit::W(wq, false) = w {
            c.x(wq);
        }
    };
    let veto = !matches!(w, Lit::One);
    match outs {
        Some((out, k1, k2)) => {
            for i in 2..5 {
                c.x(tv[i]);
            }
            let a1 = and_new(c, tv[2], tv[3]);
            let a2 = and_new(c, a1, tv[4]);
            c.cx(tv[1], out);
            c.x(out);
            c.cx(a2, out);
            // barrel letters: k2 = Dsel & !z2 = !z2 ^ a2 ^ v3;  k1 = Dsel ^ (k2 & z3) = Dsel ^ !z2 ^ a1 ^ v3
            c.cx(tv[2], k2);
            c.cx(a2, k2);
            and_erase(c, a2, a1, tv[4]);
            if veto {
                // q1 = eq & !Y
                let q1 = match w {
                    Lit::W(wq, _) => {
                        ny(c);
                        let q = and_new(c, tv[top], wq);
                        ny(c);
                        q
                    }
                    _ => tv[top],
                };
                // v = 2: z2 & not flipped
                c.x(tv[2]);
                let r2 = and_new(c, tv[2], s1);
                c.x(tv[2]);
                let v2 = and_new(c, q1, r2);
                c.cx(v2, out);
                and_erase(c, v2, q1, r2);
                c.x(tv[2]);
                and_erase(c, r2, tv[2], s1);
                c.x(tv[2]);
                // v = 3: [v = 3] & added  (a1's wire holds [v = 3] = !z2 & z3 meanwhile)
                c.cx(tv[2], a1);
                let r3 = and_new(c, a1, ct);
                c.cx(tv[2], a1);
                let v3 = and_new(c, q1, r3);
                c.cx(v3, out);
                c.cx(v3, k2);
                c.cx(v3, k1);
                and_erase(c, v3, q1, r3);
                c.cx(tv[2], a1);
                and_erase(c, r3, a1, ct);
                c.cx(tv[2], a1);
                if let Lit::W(wq, _) = w {
                    ny(c);
                    and_erase(c, q1, tv[top], wq);
                    ny(c);
                }
            }
            c.cx(tv[2], k1);
            c.cx(a1, k1);
            and_erase(c, a1, tv[2], tv[3]);
            c.cx(tv[1], out); // Dsel on out's wire
            for i in 2..5 {
                c.x(tv[i]);
            }
            c.cx(out, k1);
            c.cx(tv[1], out);
        }
        None => {
            c.x(tv[1]);
            c.z_if(tv[1], NO_BIT); // dq ^ 1
            c.x(tv[1]);
            for i in 2..5 {
                c.x(tv[i]);
            }
            let a1 = and_new(c, tv[2], tv[3]);
            c.cz(a1, tv[4]); // !z2 & !z3 & !z4
            if veto {
                let q1 = match w {
                    Lit::W(wq, _) => {
                        ny(c);
                        let q = and_new(c, tv[top], wq);
                        ny(c);
                        q
                    }
                    _ => tv[top],
                };
                c.x(tv[2]);
                let r2 = and_new(c, tv[2], s1); // z2 & not flipped
                c.cz(q1, r2);
                and_erase(c, r2, tv[2], s1);
                c.x(tv[2]);
                c.cx(tv[2], a1);
                let r3 = and_new(c, a1, ct); // [v = 3] & added
                c.cz(q1, r3);
                and_erase(c, r3, a1, ct);
                c.cx(tv[2], a1);
                if let Lit::W(wq, _) = w {
                    ny(c);
                    and_erase(c, q1, tv[top], wq);
                    ny(c);
                }
            }
            and_erase(c, a1, tv[2], tv[3]);
            for i in 2..5 {
                c.x(tv[i]);
            }
        }
    }
    zlin_off(c, &tv, &bview);
    c.x(ct);
    c.cx(tv[top], ct);
    c.x(s1);
    c.cx(btop, s1);
    c.cx(ct, s1);
    w1_conj(c, &tv, &wa);
    w1_conj(c, &bview, &wb);
    erase_recs(c, recs);
    w1_conj(c, &bview, &wb);
    w1_conj(c, &tv, &wa);
    for (v, real) in [(&mut bv, b_real), (&mut tv, t_real)] {
        while v.len() > real {
            let q = v.pop().unwrap();
            c.cx(*v.last().unwrap(), q);
            c.free(q);
        }
    }
    if need0 {
        for q in [bv[0], tv[0]] {
            c.x(q);
            c.free(q);
        }
    }
}

/// [`fast_add_halve_forced_lr`] for forced move 2 under LF_YP8, with the choice (letter `out`, barrel letters k1, k2)
/// computed inside the add.
fn yp8_add_halve_forced_choice(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>, out: QubitId, k1: QubitId, k2: QubitId, tick: usize) {
    c.cx_all(sign, b);
    c.cx(b[0], t[0]);
    let low = t.remove(0);
    c.free(low);
    let acc = t.clone();
    let reserve = yp8_reserve(acc.len(), b.len(), tick, true);
    rail_add_mid(c, &b[1..], &acc, b[0], reserve, true, None, &mut |c, add, delta, carry| {
        let flip = |c: &mut Builder| {
            for (j, cj) in carry.iter().enumerate() {
                for &q in &add[delta + j] {
                    c.cx(q, acc[delta + j]);
                }
                if let Some(cj) = *cj {
                    c.cx(cj, acc[delta + j]);
                }
            }
        };
        let ct = carry.last().copied().flatten().expect("top carry");
        let q0 = pmark(c);
        flip(c); // the paused part's sums, by CNOTs: acc holds the new target
        c.cx_all(sign, b);
        yp8_logic(c, &acc, b, sign, ct, tick, Some((out, k1, k2)));
        c.cx_all(sign, b);
        flip(c);
        pacc(c, "yp8.fwd_logic", q0);
    });
    c.cx_all(sign, b);
}

/// [`fast_double_sub_forced_lr`] for forced move 2 under LF_YP8, with the phase fix of the measured choice letter
/// (outcome `m`) applied inside the add.
fn yp8_double_sub_forced_erase(c: &mut Builder, sign: QubitId, b: &[QubitId], t: &mut Vec<QubitId>, m: crate::circuit::BitId, tick: usize) {
    c.cx_all(sign, b);
    c.x_all(t);
    let acc = t.clone();
    let reserve = yp8_reserve(acc.len(), b.len(), tick, false);
    let n = acc.len();
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    // the logic reads the target's bits 1..4 (positions 0..4 here) and, below the sign, only its window
    let h = w1_anchor(tick).saturating_sub(w1_kt(tick));
    let low = (h >= 1).then(|| (4usize, h - 1));
    if n > 3 && n - 1 + reserve > room {
        // The paused add would be split deeper than the plain one, and the pause is only needed on shots whose
        // outcome is 1: run the plain add on the others.
        assert!(!y28_pending(), "y28: a kept bit's Z would sit under the choice outcome here");
        let nm = c.alloc_bit();
        c.bit_store1(nm);
        c.bit_xor_into(nm, m);
        c.push_condition(nm);
        rail_add(c, &b[1..], &acc, Some(b[0]));
        c.pop_condition();
        c.free_bit(nm);
        c.push_condition(m);
        rail_add_mid(c, &b[1..], &acc, b[0], reserve, false, low, &mut |c, _add, _delta, carry| {
            let ct = carry.last().copied().flatten().expect("top carry");
            let q0 = pmark(c);
            c.x_all(&acc);
            c.cx_all(sign, b);
            yp8_logic(c, &acc, b, sign, ct, tick, None);
            c.cx_all(sign, b);
            c.x_all(&acc);
            pacc(c, "yp8.rev_logic", q0);
        });
        c.pop_condition();
    } else {
        rail_add_mid(c, &b[1..], &acc, b[0], reserve, false, low, &mut |c, _add, _delta, carry| {
            let ct = carry.last().copied().flatten().expect("top carry");
            let q0 = pmark(c);
            c.push_condition(m);
            c.x_all(&acc);
            c.cx_all(sign, b);
            yp8_logic(c, &acc, b, sign, ct, tick, None);
            c.cx_all(sign, b);
            c.x_all(&acc);
            c.pop_condition();
            pacc(c, "yp8.rev_logic", q0);
        });
    }
    c.x_all(t);
    let u = c.alloc_qubit();
    c.cx(b[0], u);
    c.cx_all(sign, b);
    t.insert(0, u);
}

fn rounds() -> usize {
    envelope().len()
}

/// `LF_PARITY_LOAN=1` (off by default): one wire lent out wherever the walk sits at the qubit cap, with CNOTs only.
///
/// Invariant (every input): a forced step is T <- (T +- B)/2 with letter s = T1 ^ B1 on odd rails, and for the two
/// forced steps of a tick  s0 ^ s1 = (T1 ^ T2) ^ (B1 ^ B2)  (bits 1 and 2 of the tick's target and source at its
/// start; three-bit arithmetic, the choice step does not enter). The target of tick t is the source of tick t-1, so
/// the sum over ticks 0..b telescopes to (T1 ^ T2 at the seed) ^ (B1 ^ B2 of tick b's source), and the half seed
/// makes R1 = (R0 -+ p)/2 with p = 7 mod 8, which gives R0[2] = R1[1] and so (T1 ^ T2 at the seed) = s0 of tick 0.
/// Hence, with B the source rail of tick b, at any moment between tick b and tick b+1 (either direction):
///     B[1] ^ B[2] ^ s1(0) ^ XOR_{t=1..b} (s0(t) ^ s1(t)) = 0.
/// Any one wire of the relation can be cleared by CNOTs from the others, released, and rebuilt the same way.
/// Used at the reorder boundary (b = LF_REORDER - 1): the parked source rail's bit-1 wire is out through the
/// payload-only passes, and tick 0's s1 letter (not read between the boundary and the walk's return to it) is out
/// through the payload-fused ticks and the endpoints.
/// `LF_PARITY_PAD=1` (test only): hold an idle placeholder wire while a wire is out, so every live count and with
/// it every cell plan is the unchanged circuit's; the gate list then differs by the CNOT fans only.
fn parity_loan() -> bool {
    std::env::var("LF_PARITY_LOAN").is_ok_and(|v| v == "1") && lf_fast() && seed_half() && lf_reorder(false) >= 2 && lf_reorder(false) == lf_reorder(true)
}
fn parity_pad() -> bool {
    std::env::var("LF_PARITY_PAD").is_ok_and(|v| v == "1")
}
/// The relation's wires at the boundary after tick `ahead - 1`: source rail bits 1 and 2, then the forced letters.
fn parity_wires(wk: &Walk, ahead: usize) -> Vec<QubitId> {
    let o = lowrel() as usize;
    let si = 1 - (ahead - 1) % 2;
    let mut ws = vec![wk.r[si][1 - o], wk.r[si][2 - o]];
    for t in 0..ahead {
        if t > 0 {
            ws.push(wk.tape[t][0]);
        }
        ws.push(wk.tape[t][1]);
    }
    ws
}
/// Clear wire `k` of the relation from the others and release it (`pad`: the placeholder taken in its place).
fn parity_out(c: &mut Builder, wk: &Walk, ahead: usize, k: usize) -> Option<QubitId> {
    let ws = parity_wires(wk, ahead);
    for (i, &w) in ws.iter().enumerate() {
        if i != k {
            c.cx(w, ws[k]);
        }
    }
    c.free(ws[k]);
    parity_pad().then(|| c.alloc_qubit())
}
/// Rebuild wire `k` of the relation on a fresh wire; returns it (the caller puts it back in its register).
fn parity_in(c: &mut Builder, wk: &Walk, ahead: usize, k: usize, pad: Option<QubitId>) -> QubitId {
    if let Some(p) = pad {
        c.release_clean(p);
    }
    let q = c.alloc_qubit();
    let ws = parity_wires(wk, ahead);
    for (i, &w) in ws.iter().enumerate() {
        if i != k {
            c.cx(w, q);
        }
    }
    q
}
/// Rail side: the parked source rail's bit-1 wire (relation wire 0).
fn parity_rail_out(c: &mut Builder, wk: &Walk, ahead: usize) -> Option<QubitId> {
    parity_out(c, wk, ahead, 0)
}
fn parity_rail_in(c: &mut Builder, wk: &mut Walk, ahead: usize, pad: Option<QubitId>) {
    let q = parity_in(c, wk, ahead, 0, pad);
    let o = lowrel() as usize;
    wk.r[1 - (ahead - 1) % 2][1 - o] = q;
}
/// Tape side: tick 0's s1 letter (relation wire 2).
fn parity_tape_out(c: &mut Builder, wk: &Walk, ahead: usize) -> Option<QubitId> {
    parity_out(c, wk, ahead, 2)
}
fn parity_tape_in(c: &mut Builder, wk: &mut Walk, ahead: usize, pad: Option<QubitId>) {
    let q = parity_in(c, wk, ahead, 2, pad);
    wk.tape[0][1] = q;
}

thread_local! {
    /// Set while a walk runs with tick 0's letter off the tape (`LF_T0_FREE`): tick 0 takes the low-bit choice rule
    /// with the equal-sign veto read from the source rail ([`t0_m_on`]).
    static T0_PLAIN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
thread_local! {
    /// Set around the payload tick 0 of [`multiply`]'s phase fix under `LF_T0_PHROT=1`: [`rot4`] is a no-op.
    static SKIP_ROT4: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// `LF_DIV_PHROT=1`: the fused forward tick whose payload rotation [`fwd_tick_fast`] skips (usize::MAX: none).
    static SKIP_PAY_ROT_AT: std::cell::Cell<usize> = const { std::cell::Cell::new(usize::MAX) };
}
/// `LF_DIV_PHROT=1`: the divide's endpoint erases P1 = (-1)^x01 P0 (x01 = s0 ^ s1) by a CNOT copy. P1's last op is
/// tick 137's payload rotation rot_e; it is skipped, P1's unrotated wires V are measured (HMR, bits m) and the
/// phase (-1)^(m . V) = (-1)^(m . rot_e^-1(N_x01 P0)) is applied on P0 with [`rot4_phase`] (inverse side):
/// cond-negate P0 by x01, the phase, then cond-negate by s1 (N_x01 then N_s1 = N_s0, the old endpoint's map).
/// Exact (the same phase function on the valid subspace); saves the 1.5n - 2 Fredkins for one AND.
fn t0_dbl() -> bool {
    std::env::var("LF_T0_DBL").is_ok_and(|v| v == "1")
}
fn div_phrot() -> bool {
    std::env::var("LF_DIV_PHROT").is_ok_and(|v| v == "1")
}
/// `LF_T0_PHROT=1`: in the multiply's `LF_T0_FREE` phase fix the payload tick 0 ends with a 4-way rotation (a
/// permutation of the target's wires controlled by the letter bits k1, k2), undone first by the reverse tick. The
/// phase (-1)^(m . rot_e(V)) is applied on the unrotated V instead: for each e the Z pattern is m permuted, and
/// [e == v] has the ANF 1 ^ k1 ^ k2 ^ k1k2 (v = 0), k1 ^ k1k2, k2 ^ k1k2, k1k2: CZs (k1k2 on one AND wire) under
/// the kept bits, so both rotations (2 (1.5n - 2) Fredkins) go for one AND. Exact (the same phase function).
fn t0_phrot() -> bool {
    std::env::var("LF_T0_PHROT").is_ok_and(|v| v == "1")
}
/// Index map of [`rot4`] (forward) for rotation amount e: out[i] = in[map[i]].
fn rot4_map(n: usize, e: usize) -> Vec<usize> {
    let [r1, r0, rm2] = refl4_pairs(n);
    let (k1, k2) = (e & 1 == 1, e & 2 == 2);
    let mut arr: Vec<usize> = (0..n).collect();
    for (pairs, on) in [(&r1, k1), (&r0, k1 ^ k2), (&rm2, k2)] {
        if on {
            for &(a, b) in pairs.iter() {
                arr.swap(a, b);
            }
        }
    }
    arr
}
/// Phase (-1)^(sum_i m_i rot_e(v)_i), e = k1 + 2 k2, on the unrotated `v` (see [`t0_phrot`]); frees the bits.
/// `inv`: the phase (-1)^(sum_i m_i rot_e^-1(v)_i) instead (see [`div_phrot`]).
fn rot4_phase(c: &mut Builder, k1: QubitId, k2: QubitId, v: &[QubitId], bits: Vec<crate::circuit::BitId>, inv: bool) {
    let n = v.len();
    let maps: Vec<Vec<usize>> = (0..4).map(|e| rot4_map(n, e)).collect();
    // monomials: 0 = 1, 1 = k1, 2 = k2, 3 = k1k2; [e == val] in ANF
    let anf: [&[usize]; 4] = [&[0, 1, 2, 3], &[1, 3], &[2, 3], &[3]];
    let mut acc: std::collections::BTreeMap<(usize, usize), Vec<usize>> = std::collections::BTreeMap::new();
    for i in 0..bits.len() {
        for val in 0..4 {
            // m . rot_e(v) = sum_i m_i v_map(i); m . rot_e^-1(v) = sum_i m_map(i) v_i
            let (j, bi) = if inv { (i, maps[val][i]) } else { (maps[val][i], i) };
            for &mono in anf[val] {
                let l = acc.entry((j, mono)).or_default();
                if let Some(p) = l.iter().position(|&x| x == bi) {
                    l.remove(p);
                } else {
                    l.push(bi);
                }
            }
        }
    }
    let t = and_new(c, k1, k2);
    for (&(j, mono), l) in acc.iter() {
        for &i in l {
            match mono {
                0 => c.z_if(v[j], bits[i]),
                1 => c.cz_if(k1, v[j], bits[i]),
                2 => c.cz_if(k2, v[j], bits[i]),
                _ => c.cz_if(t, v[j], bits[i]),
            }
        }
    }
    if std::env::var("LF_PHROT_TOF").is_ok_and(|v| v == "1") {
        // +1 Toffoli, no measurement: keeps the simulator's random stream aligned with the unrotated circuit
        // (clean paired phase-failure comparison)
        c.ccx(k1, k2, t);
        c.release_clean(t);
    } else {
        and_erase(c, t, k1, k2);
    }
    for b in bits {
        c.free_bit(b);
    }
}
fn t0_plain(tick: usize) -> bool {
    tick == 0 && T0_PLAIN.with(|p| p.get())
}
thread_local! {
    /// The wire m of [`t0_m_on`] while tick 0's choice runs under `LF_T0_FREE`.
    static T0_M: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) };
}
const T0_KH: usize = 12;
struct T0M {
    mh: QubitId,
    q: QubitId,
    z: QubitId,
    sg: QubitId,
    s0: QubitId,
    s1: QubitId,
    v: Vec<QubitId>,
    add: Vec<QubitId>,
}
/// NOT C on scratch wires, C = top T0_KH bits of p/5 (0x333) when s0 = 0, of p/3 (0x555) when s0 = 1. Self-inverse.
fn t0_m_consts(c: &mut Builder, add: &[QubitId], s0: QubitId) {
    for (i, &q) in add.iter().enumerate() {
        if (0xCCCusize >> i) & 1 == 1 {
            c.x(q);
        }
        if (0x666usize >> i) & 1 == 1 {
            c.cx(s0, q);
        }
    }
}
/// Tick 0's equal-sign test from the source rail alone. After the two forced steps the target is
/// (u R1 - sign(R1) p) / 4 with u = 5, 3, 1, -1 for (s0, s1) = (0,0), (1,0), (0,1), (1,1), so its sign differs from
/// R1's unless m = !s1 & [|R1| > p/u]; the compare reads the top T0_KH bits of |R1| (ones' complement) against the
/// same bits of p/3 or p/5: this windowed m is the rule's definition (it equals the true sign on all but about 1
/// walk in 12,000), and both directions and [`t0_derive`] compute the same function, so nothing is approximate.
/// eq = !m ^ dq. `r1`: bit-0-less source rail, at least 256 wires. Sets [`T0_M`]; 13 Toffoli.
fn t0_m_on(c: &mut Builder, r1: &[QubitId], s0: QubitId, s1: QubitId) -> T0M {
    let sg = r1[N - 1]; // bit 256: the sign (|R1| < p)
    let v: Vec<QubitId> = (0..T0_KH).map(|i| r1[N - 1 - T0_KH + i]).collect(); // bits 256 - KH .. 255, low first
    let add = c.alloc_qubits(T0_KH);
    t0_m_consts(c, &add, s0);
    let (z, q, mh) = (c.alloc_qubit(), c.alloc_qubit(), c.alloc_qubit());
    for &w in &v {
        c.cx(sg, w);
    }
    carry_out_xor(c, &v, &add, z, Some(q)); // [V > C]
    for &w in &v {
        c.cx(sg, w);
    }
    c.x(s1);
    c.ccx(s1, q, mh);
    c.x(s1);
    T0_M.with(|m| m.set(Some(mh)));
    T0M { mh, q, z, sg, s0, s1, v, add }
}
/// Erase [`t0_m_on`]'s wires by measurement (the compare is redone only on shots whose outcome is 1).
fn t0_m_off(c: &mut Builder, m: T0M) {
    T0_M.with(|x| x.set(None));
    c.x(m.s1);
    and_erase(c, m.mh, m.s1, m.q);
    c.x(m.s1);
    for &w in &m.v {
        c.cx(m.sg, w);
    }
    let b = c.alloc_bit();
    c.hmr(m.q, b);
    c.release_clean(m.q);
    c.push_condition(b);
    carry_out_xor(c, &m.v, &m.add, m.z, None); // (-1)^(NOT carry)
    c.x(m.z);
    c.z_if(m.z, NO_BIT); // times -1
    c.x(m.z);
    c.pop_condition();
    c.free_bit(b);
    for &w in &m.v {
        c.cx(m.sg, w);
    }
    t0_m_consts(c, &m.add, m.s0);
    c.free_vec(&m.add);
    c.free(m.z);
}
// ---- defer (spooky-leapfrog-v1, SL_DEFER_T0): tick 0's veto q deferred (DQ) and t0_derive's state held (T0H) ----
fn sl_defer_t0() -> u8 {
    static V: OnceLock<u8> = OnceLock::new();
    *V.get_or_init(|| std::env::var("SL_DEFER_T0").ok().and_then(|v| v.parse().ok()).unwrap_or(0))
}
fn defer_t0_dq() -> bool {
    let v = sl_defer_t0();
    v == 1 || v == 3 || v >= 9
}
fn defer_t0_hold() -> bool {
    let v = sl_defer_t0();
    (v == 2 || v == 3 || v >= 9) && y15::sl_rt0() != 0
}
fn defer_t0_fault() -> u8 {
    let v = sl_defer_t0();
    if v >= 9 { v } else { 0 }
}
thread_local! {
    /// DQ: the outcome bit of forward tick 0's q, until t0_derive builds q again
    static T0Q_KEEP: std::cell::Cell<Option<crate::circuit::BitId>> = const { std::cell::Cell::new(None) };
    /// T0H: t0_derive's scratch (after its two forced steps, bit-0 wire dropped) and its q, until RT0's letter erase
    static T0H_STASH: std::cell::RefCell<Option<(Vec<QubitId>, QubitId)>> = const { std::cell::RefCell::new(None) };
}
/// [`t0_m_off`] with q measured and its outcome bit kept for t0_derive (no compare).
fn t0_m_off_keep(c: &mut Builder, m: T0M) {
    T0_M.with(|x| x.set(None));
    c.x(m.s1);
    and_erase(c, m.mh, m.s1, m.q);
    c.x(m.s1);
    let b = c.alloc_bit();
    c.hmr(m.q, b);
    c.release_clean(m.q);
    assert!(T0Q_KEEP.with(|k| k.replace(Some(b))).is_none(), "defer DQ: a kept bit from an earlier walk");
    t0_m_consts(c, &m.add, m.s0);
    c.free_vec(&m.add);
    c.free(m.z);
}
/// DQ, in t0_derive: q holds [V > C] again, so the kept bit's phase is one Z on it.
fn defer_t0_apply_q(c: &mut Builder, q: QubitId) {
    if let Some(b) = T0Q_KEEP.with(|k| k.take()) {
        if defer_t0_fault() != 9 {
            c.z_if(q, b);
        }
        c.free_bit(b);
    }
}
/// T0H: [`t0_m_off`] that keeps q (the AND mh and the constants go; q stays for RT0).
fn t0_m_off_hold(c: &mut Builder, m: T0M) -> QubitId {
    T0_M.with(|x| x.set(None));
    c.x(m.s1);
    and_erase(c, m.mh, m.s1, m.q);
    c.x(m.s1);
    t0_m_consts(c, &m.add, m.s0);
    c.free_vec(&m.add);
    c.free(m.z);
    m.q
}
/// T0H: the held state, taken by RT0's letter erase.
fn t0h_take() -> Option<(Vec<QubitId>, QubitId)> {
    T0H_STASH.with(|s| s.borrow_mut().take())
}
/// T0H: wires held for RT0 (0 when nothing is held).
fn t0h_held() -> usize {
    T0H_STASH.with(|s| s.borrow().as_ref().map_or(0, |(ts, _)| ts.len() + 1))
}
/// T0H: mh = AND(!s1, q), as t0_m_on builds it.
fn t0_mh_on(c: &mut Builder, s1: QubitId, q: QubitId) -> QubitId {
    c.x(s1);
    let mh = and_new(c, s1, q);
    c.x(s1);
    mh
}
fn t0_mh_off(c: &mut Builder, mh: QubitId, s1: QubitId, q: QubitId) {
    c.x(s1);
    and_erase(c, mh, s1, q);
    c.x(s1);
}
/// T0H: erase the held q = [V > C] by measurement, the compare of [`t0_m_off`] on the outcome-1 shots.
fn t0_q_erase(c: &mut Builder, r1: &[QubitId], s0: QubitId, q: QubitId) {
    let sg = r1[N - 1];
    let v: Vec<QubitId> = (0..T0_KH).map(|i| r1[N - 1 - T0_KH + i]).collect();
    let add = c.alloc_qubits(T0_KH);
    t0_m_consts(c, &add, s0);
    let z = c.alloc_qubit();
    for &w in &v {
        c.cx(sg, w);
    }
    let b = c.alloc_bit();
    c.hmr(q, b);
    c.release_clean(q);
    if defer_t0_fault() != 10 {
        c.push_condition(b);
        carry_out_xor(c, &v, &add, z, None); // (-1)^(NOT carry)
        c.x(z);
        c.z_if(z, NO_BIT); // times -1
        c.x(z);
        c.pop_condition();
    }
    c.free_bit(b);
    for &w in &v {
        c.cx(sg, w);
    }
    t0_m_consts(c, &add, s0);
    c.free_vec(&add);
    c.free(z);
}

/// `LF_T0_FREE=1|div|mul`: tick 0's letter is kept off the tape wherever a walk sits at the qubit cap (both walks,
/// the divide only, the multiply only).
///
/// The half seed gives R0 = 2 R1 - sign(R1) p, and tick 0 changes only R0, so tick 0's letter is a function of R1,
/// which is alive whenever the walk stands at the boundary after tick 0. Tick 0 takes the low-bit choice rule with
/// the equal-sign veto read from R1's top bits ([`t0_m_on`]), and [`t0_derive`] computes the letter from R1's
/// sign, low bits and those top bits. The five wires are measured away (X basis) after their last read and the
/// measurement's phase is fixed at the walk's end, on the re-derived letter (a phase that is a function of the
/// input can be fixed at any later moment where that function is at hand).
/// Divide: out after payload-only tick 0, re-derived before the last reverse tick. Multiply: out after the forward
/// tick 0; the payload's tick 0 is not run at the reorder boundary: the product is 2 P1 (R0 = 2 R1 mod p), the other
/// register (y R2, a function of the product and the letter) is measured away, and at the walk's end payload tick 0
/// is run forward and back on (product, product / 2) to fix that phase: one payload tick more than without it.
/// It takes the place of the parity loan ([`parity_loan`], one wire out at a time): 4 wires fewer than with the
/// loan. Only the loan's rail side still runs, over the divide's payload-only tick 0.
fn t0_free(multiply: bool) -> bool {
    let v = std::env::var("LF_T0_FREE").unwrap_or_default();
    (v == "1" || v == if multiply { "mul" } else { "div" }) && lf_fast() && seed_half() && lowrel() && forced() == 2 && lf_reorder(multiply) >= 2
}
/// Measure tick 0's letter away; the outcome bits are kept for [`t0_in`].
fn t0_out(c: &mut Builder, wk: &Walk) -> Vec<crate::circuit::BitId> {
    wk.tape[0].iter().map(|&q| {
        let m = c.alloc_bit();
        c.hmr(q, m);
        c.release_clean(q);
        m
    }).collect()
}
/// Re-derive tick 0's letter at the boundary after tick 0 and fix the phase of [`t0_out`]'s measurements on it.
fn t0_in(c: &mut Builder, wk: &mut Walk, bits: Vec<crate::circuit::BitId>) {
    let q0 = pmark(c);
    let letter = t0_derive(c, wk);
    for (&q, m) in letter.iter().zip(bits) {
        c.z_if(q, m);
        c.free_bit(m);
    }
    wk.tape[0] = letter;
    pacc(c, "t0.derive", q0);
}
/// Tick 0's letter (s0, s1, s3, k1, k2) on fresh wires from its source rail R1 (bit-0-less, at least 8 bits wide):
/// a scratch copy of bits 1..7 of R0 = 2 R1 - sign(R1) p, i.e. (R0 >> 1) mod 128 = (R1 mod 128) + (R1 < 0 ? 23 : 104)
/// (p = 47 mod 256), then the tick's own two forced steps and its choice ([`t0_m_on`]'s veto included) on the
/// scratch, undone again.
fn t0_derive(c: &mut Builder, wk: &Walk) -> Vec<QubitId> {
    let u = |v: u8| alloy_primitives::U256::from(v);
    let b = wk.r[1].clone();
    let sg = *b.last().unwrap();
    let mut ts = c.alloc_qubits(7);
    c.x(ts[0]);
    for i in 1..7 {
        c.cx(b[i - 1], ts[i]);
    }
    add_sel_const(c, &ts, u(104), u(23), sg);
    let mut letter = Vec::with_capacity(5);
    for n in [7usize, 6] {
        let s = c.alloc_qubit();
        pp_sign_into1(c, ts[0], b[0], s);
        fast_add_halve_forced_lr(c, s, &b[..n], &mut ts);
        letter.push(s);
    }
    let (s3, k1, k2) = (c.alloc_qubit(), c.alloc_qubit(), c.alloc_qubit());
    lr_restore(c, &mut ts); // bits 0..5 of the twice-stepped target
    let one = c.alloc_qubit();
    c.x(one);
    let mut bb = vec![one];
    bb.extend_from_slice(&b[..5]);
    assert!(t0_plain(0));
    let t0m = t0_m_on(c, &b, letter[0], letter[1]);
    defer_t0_apply_q(c, t0m.q);
    fast_choice(c, &ts, &bb, s3, k1, k2, 0);
    let q_held = if defer_t0_hold() {
        Some(t0_m_off_hold(c, t0m))
    } else {
        t0_m_off(c, t0m);
        None
    };
    c.x(one);
    c.free(one);
    lr_drop(c, &mut ts);
    if let Some(q) = q_held {
        // T0H: the scratch and q stay for RT0's letter erase, which reads exactly this state
        T0H_STASH.with(|s| {
            assert!(s.borrow().is_none(), "defer T0H: state from an earlier walk");
            *s.borrow_mut() = Some((ts, q));
        });
        letter.extend([s3, k1, k2]);
        return letter;
    }
    for (i, n) in [(1usize, 6usize), (0, 7)] {
        fast_double_sub_forced_lr(c, letter[i], &b[..n], &mut ts);
    }
    add_sel_const(c, &ts, u(24), u(105), sg);
    for i in 1..7 {
        c.cx(b[i - 1], ts[i]);
    }
    c.x(ts[0]);
    c.free_vec(&ts);
    letter.extend([s3, k1, k2]);
    letter
}

/// LF_REORDER=T: the payload-fused traversals leave their first T ticks to a rails-only pass plus a payload-only
/// pass (letters read back from the tape). The rail adds then run with one payload register live (no room splits)
/// and the cells run beside the rails parked at tick T. 0 = off. T must stay below the tie-safe ticks.
fn lf_reorder(multiply: bool) -> usize {
    let key = if multiply { "LF_REORDER_MUL" } else { "LF_REORDER_DIV" };
    let r = std::env::var(key).or_else(|_| std::env::var("LF_REORDER")).ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    assert!(r == 0 || r <= tie_from(), "LF_REORDER must not reach the tie-safe ticks");
    r.min(rounds())
}

#[path = "y15_onefold.rs"]
mod y15;

/// Payload half of [`fwd_tick_fast`] on a tick below the tie-safe ticks, its letter already on the tape.
fn pay_fwd_tick(c: &mut Builder, t: usize, letter: &[QubitId], p: &mut [Vec<QubitId>; 2]) {
    if y15::fwd_on(t) {
        return y15::fwd_tick(c, t, letter, p);
    }
    let (y15_e0, y15_a0) = (c.expected_total(), c.active_qubits());
    let [w, ..] = steps()[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let (fold, proxy) = proxy_fold(w, false);
    let (s0, s1, s3, k1, k2) = (letter[0], letter[1], letter[2], letter[3], letter[4]);
    for s in [s0, s1] {
        let q0 = pmark(c);
        let (pt, ps) = (p[ti].clone(), p[si].clone());
        let cp = lr_pad_c2(c, 2 * lowrel() as usize);
        cells::with_tie(None, || cells::with_cmp_shift(cmp_shift_at(t), || cells::add_halve(c, s, &ps, &pt, fold, proxy)));
        lr_unpad(c, cp);
        pacc(c, "fwdP.pay_cell", q0);
    }
    let q0 = pmark(c);
    let (pt, ps) = (p[ti].clone(), p[si].clone());
    if let Some(mw) = merged_fits(c.active_qubits() as usize, t, false) {
        cells::with_tie(None, || {
            cells::with_cmp_shift(cmp_shift_at(t), || cells::with_bridge(proxy, false, || {
                let split = merged_split(c, proxy, false, false);
                merged_fwd(c, s3, &ps, &pt, k1, k2, proxy, split, mw)
            }))
        });
        pacc(c, "fwdP.pay_merged", q0);
    } else {
        let cp = lr_pad_c2(c, 2 * lowrel() as usize);
        cells::with_tie(None, || cells::with_cmp_shift(cmp_shift_at(t), || cells::add_halve(c, s3, &ps, &pt, fold, proxy)));
        lr_unpad(c, cp);
        cmod_barrel(c, k1, k2, &p[ti], false);
        pacc(c, "fwdP.pay_cell_barrel", q0);
    }
    y15::trace_old(c, t, y15_e0, y15_a0);
}

/// Payload half of [`rev_tick_fast`] on a tick below the tie-safe ticks (the tape is read, not popped).
fn pay_rev_tick(c: &mut Builder, t: usize, letter: &[QubitId], p: &mut [Vec<QubitId>; 2]) {
    if y15::rev_on(t) && n2_rev_y15(t) {
        return y15::rev_tick(c, t, letter, p);
    }
    let (y15_e0, y15_a0) = (c.expected_total(), c.active_qubits());
    let [w, ..] = steps()[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let (fold, proxy) = proxy_fold(w, true);
    let (s0, s1, s3, k1, k2) = (letter[0], letter[1], letter[2], letter[3], letter[4]);
    let q0 = pmark(c);
    let merged = merged_fits(c.active_qubits() as usize, t, true);
    if let Some(mw) = merged {
        let (pt, ps) = (p[ti].clone(), p[si].clone());
        n2_extra(t, 2);
        cells::with_tie(None, || {
            cells::with_cmp_shift(cmp_shift_at(t), || cells::with_bridge(proxy, true, || merged_rev(c, s3, &ps, &pt, k1, k2, proxy, true, mw)))
        });
        n2_extra_off();
        pacc(c, "revP.pay_merged", q0);
    } else {
        cmod_barrel(c, k1, k2, &p[ti], true);
        pacc(c, "revP.pay_barrel", q0);
    }
    for s in [s3, s1, s0] {
        if merged.is_some() && s == s3 {
            continue;
        }
        let q0 = pmark(c);
        let (pt, ps) = (p[ti].clone(), p[si].clone());
        c.x(s);
        let cp = lr_pad_c2(c, 2 * lowrel() as usize);
        n2_extra(t, if s == s0 { 0 } else if s == s1 { 1 } else { 2 });
        cells::with_tie(None, || cells::with_cmp_shift(cmp_shift_at(t), || cells::double_add(c, s, &ps, &pt, fold, proxy)));
        n2_extra_off();
        lr_unpad(c, cp);
        c.x(s);
        pacc(c, "revP.pay_cell", q0);
    }
    y15::trace_old_rev(c, t, y15_e0, y15_a0);
}

// ---- lever N2 on spookyfrog (research patch, sim/patch_n2_sf.py): trailing batch with a terminal sign-copy loan ----
/// `SL_N2` (read once; 0 = off, the base byte for byte): 1 divide, 2 divide + multiply, 3 multiply; 6, 7, 8 and 9 are
/// deliberate-fault controls (7 multiply / 8 divide: one lent wire not cleared; 6 divide: the terminal rotation
/// applied although the endpoint's phase repair assumes it skipped; 9 divide: two of P1's positions swapped before the
/// endpoint, a misplaced pair of Z's in its phase repair).
fn sl_n2() -> u8 {
    static V: OnceLock<u8> = OnceLock::new();
    *V.get_or_init(|| std::env::var("SL_N2").ok().and_then(|v| v.parse().ok()).unwrap_or(0))
}
fn n2_div() -> bool {
    matches!(sl_n2(), 1 | 2 | 6 | 8 | 9)
}
fn n2_mul() -> bool {
    matches!(sl_n2(), 2 | 3 | 7)
}
/// First batched tick of the divide / the multiply (default 131: the fused one-folds end at 130 / 126).
fn n2_from(multiply: bool) -> usize {
    static D: OnceLock<usize> = OnceLock::new();
    static M: OnceLock<usize> = OnceLock::new();
    let (cell, key) = if multiply { (&M, "SL_N2_MFROM") } else { (&D, "SL_N2_DFROM") };
    let v = *cell.get_or_init(|| std::env::var(key).ok().and_then(|v| v.parse().ok()).unwrap_or(131));
    assert!(
        lf_reorder(multiply) <= v && v < rounds(),
        "N2: {key} = {v} must lie in [{}, {})",
        lf_reorder(multiply),
        rounds()
    );
    v
}
thread_local! {
    /// Set while the divide's payload-only batch runs (y21's deep shed then follows [`n2_deep`]).
    static N2_FWD_BATCH: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Set while the multiply's payload-only batch runs: [`pay_rev_tick`] takes its three-fold path (except on the
    /// ticks of SL_N2_MY15) and its ops may take a room offset ([`n2_extra`]).
    static N2_THREEFOLD_REV: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The tick of the divide's batch now running (for SL_N2_FX).
    static N2_TICK: std::cell::Cell<usize> = const { std::cell::Cell::new(usize::MAX) };
}
/// A tick-list knob: 'all', 'none' or comma-separated ticks.
fn n2_ticks(key: &str, dflt: &str, t: usize) -> bool {
    let s = std::env::var(key).unwrap_or_else(|_| dflt.into());
    match s.as_str() {
        "all" => true,
        "none" | "" => false,
        l => l.split(',').any(|x| x.trim().parse::<usize>().ok() == Some(t)),
    }
}
/// y21's deep shed on a payload-only tick of a batch: Some(on) inside a batch, None elsewhere (the base's ranges).
pub(crate) fn n2_deep(t: usize, rev: bool) -> Option<bool> {
    if rev {
        return N2_THREEFOLD_REV.with(|f| f.get()).then(|| n2_ticks("SL_N2_MDEEP", "none", t));
    }
    N2_FWD_BATCH.with(|f| f.get()).then(|| n2_ticks("SL_N2_DEEP", "all", t))
}
/// y28's dropped-carry ladder on a payload-only tick of a batch (SL_N2_DROP forward, SL_N2_MDROP reverse; SL_N2_DROPN
/// carries, default 1): Some(n) on a listed batch tick (the y15 body then runs no deep shed), None elsewhere.
pub(crate) fn n2_drop(t: usize, rev: bool) -> Option<usize> {
    let (inb, key) = if rev {
        (N2_THREEFOLD_REV.with(|f| f.get()), "SL_N2_MDROP")
    } else {
        (N2_FWD_BATCH.with(|f| f.get()), "SL_N2_DROP")
    };
    if !inb || !n2_ticks(key, "none", t) {
        return None;
    }
    Some(std::env::var("SL_N2_DROPN").ok().and_then(|v| v.parse().ok()).unwrap_or(1))
}
/// SL_N2_PADS (diagnostic, the aligned copy; never an entry): on the batch ticks where [`n2_drop`] runs the dropped-carry
/// ladder, that many idle measurements at y28's aligned-copy place (y15 `y28_pads`), so that the stream draws the
/// deep-shed stream's number of random words in its order (measured: 9 a tick). None elsewhere (the base's pads).
pub(crate) fn n2_pads(t: usize, rev: bool) -> Option<usize> {
    let n: usize = std::env::var("SL_N2_PADS").ok().and_then(|v| v.parse().ok())?;
    n2_drop(t, rev).map(|_| n)
}
thread_local! {
    /// Calls of restore_onto so far (for SL_N2_RPAD).
    static N2_RESTORES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
/// SL_N2_RPAD (diagnostic, the aligned copy; never an entry): "call:n,..." = n idle measurements (of a fresh wire that
/// holds 0) at the end of the call-th restore_onto (0-based), where two gate lists' wire histories leave different
/// reset counts (measured: the deep-shed stream resets 2 wires fewer in the divide's restore than the drop stream).
fn n2_rpads(c: &mut Builder) {
    let call = N2_RESTORES.with(|x| x.replace(x.get() + 1));
    let Ok(v) = std::env::var("SL_N2_RPAD") else { return };
    let n: usize = v
        .split(',')
        .filter_map(|e| e.split_once(':'))
        .filter(|(k, _)| k.trim().parse::<usize>().ok() == Some(call))
        .filter_map(|(_, n)| n.trim().parse::<usize>().ok())
        .sum();
    for _ in 0..n {
        let q = c.alloc_qubit();
        let m = c.alloc_bit();
        c.hmr(q, m);
        c.free_bit(m);
        c.release_clean(q);
    }
}
/// SL_N2_FX (deliberate fault, diagnostic): 'z<t>' leaves out the dropped-carry ladder's phase fix on divide batch
/// tick t.
pub(crate) fn n2_fx_skip_drop_z() -> bool {
    let Ok(v) = std::env::var("SL_N2_FX") else { return false };
    let t = N2_TICK.with(|x| x.get());
    N2_FWD_BATCH.with(|f| f.get()) && v.strip_prefix('z').and_then(|x| x.parse::<usize>().ok()) == Some(t)
}
/// λ buy-back knob of the divide's batch: SL_N2_CMPX extra bits on every chunk-boundary compare of the batch's
/// one-fold ticks (default 0; 0 outside the batch).
pub(crate) fn n2_cmpx() -> isize {
    if !N2_FWD_BATCH.with(|f| f.get()) {
        return 0;
    }
    std::env::var("SL_N2_CMPX").ok().and_then(|v| v.parse().ok()).unwrap_or(0)
}
/// [`pay_rev_tick`]: may tick t take the y15 reverse one-fold? Always outside the multiply's batch; inside it only on
/// the ticks of SL_N2_MY15 (default none).
fn n2_rev_y15(t: usize) -> bool {
    !N2_THREEFOLD_REV.with(|f| f.get()) || n2_ticks("SL_N2_MY15", "none", t)
}
/// The multiply batch's plan (t/slot/d) from 113bf38's sweeps (cells of 131..135 two wires lower, tick 136's merged op
/// one lower). SL_N2_MD=none: no offsets.
const N2_MD_PLAN: &str = "131/0/-2,131/1/-2,132/0/-2,132/1/-2,133/0/-2,133/1/-2,134/0/-2,134/1/-2,135/0/-2,135/1/-2,136/2/-1";
/// Inside the multiply's batch: the room offset d <= 0 of payload op `slot` of tick t from SL_N2_MD (default
/// [`N2_MD_PLAN`]), set as y17's Y17_EXTRA. Outside the batch: nothing.
fn n2_extra(t: usize, slot: usize) {
    if !N2_THREEFOLD_REV.with(|f| f.get()) {
        return;
    }
    let d = n2_offset("SL_N2_MD", N2_MD_PLAN, t, slot);
    super::pingpong::Y17_EXTRA.with(|e| e.set(d));
}
/// The room offset d <= 0 of (t, slot) in plan knob `key` ("t/slot/d,..."; default `dflt`); 0 when not listed.
fn n2_offset(key: &str, dflt: &str, t: usize, slot: usize) -> isize {
    let s = std::env::var(key).unwrap_or_else(|_| dflt.into());
    let d = s
        .split(',')
        .filter_map(|e| {
            let v: Vec<isize> = e.split(|ch| ch == ':' || ch == '/').filter_map(|x| x.trim().parse().ok()).collect();
            (v.len() == 3 && v[0] == t as isize && v[1] == slot as isize).then(|| v[2])
        })
        .last()
        .unwrap_or(0);
    assert!(d <= 0, "N2: a room offset is never positive");
    d
}
/// SL_N2_FD (default none): room offsets on the divide batch's payload ticks ("t/0/d": the whole one-fold tick t;
/// "137/2/d": the terminal kernel), and SL_N2_MD's "137/2/d" on the multiply's terminal kernel, through Y17_EXTRA
/// (a plan for less room always fits). 0 when not listed: Y17_EXTRA is not touched, the stream is unchanged.
/// `d` > 0 (the negation of an offset) ends the offset: Y17_EXTRA back to 0.
fn n2_extra_set(d: isize) {
    if d != 0 {
        super::pingpong::Y17_EXTRA.with(|e| e.set(d.min(0)));
    }
}
fn n2_extra_off() {
    if N2_THREEFOLD_REV.with(|f| f.get()) {
        super::pingpong::Y17_EXTRA.with(|e| e.set(0));
    }
}
/// The loan: each parked rail (+-1, bit 0 not held) is 5 wires all equal to its sign; CX the sign onto the 4 others
/// (|0> on every parked walk) and release them. SL_N2_LEND: bit mask of the rails lent (default 3 = both).
fn n2_lend(ri: usize) -> bool {
    let m: usize = std::env::var("SL_N2_LEND").ok().and_then(|v| v.parse().ok()).unwrap_or(3);
    m >> ri & 1 == 1
}
thread_local! {
    /// The wire ids each rail lent (for SL_N2_REACQ).
    static N2_LENT: std::cell::RefCell<[Vec<QubitId>; 2]> = const { std::cell::RefCell::new([Vec::new(), Vec::new()]) };
}
/// SL_N2_REACQ (default 0): bit 0 the divide's loan, bit 1 the multiply's, returned on the lent ids where free.
fn n2_reacq(mul: bool) -> bool {
    static V: OnceLock<usize> = OnceLock::new();
    *V.get_or_init(|| std::env::var("SL_N2_REACQ").ok().and_then(|v| v.parse().ok()).unwrap_or(0)) >> usize::from(mul) & 1 == 1
}
fn n2_loan_out(c: &mut Builder, wk: &mut Walk, fault: bool) {
    for (ri, r) in wk.r.iter_mut().enumerate() {
        assert_eq!(r.len(), 5, "N2: a parked rail holds 5 wires (bits 1..5)");
        if !n2_lend(ri) {
            continue;
        }
        let sg = r[4];
        for i in 0..4 {
            if !(fault && ri == 0 && i == 0) {
                c.cx(sg, r[i]);
            }
            c.release_clean(r[i]);
        }
        N2_LENT.with(|l| l.borrow_mut()[ri] = r[0..4].to_vec());
        r.drain(0..4);
    }
}
/// Return the loan: 4 wires per rail (fresh, or with SL_N2_REACQ the lent ids where free), each a CX copy of its sign.
fn n2_loan_in(c: &mut Builder, wk: &mut Walk, mul: bool) {
    for (ri, r) in wk.r.iter_mut().enumerate() {
        if !n2_lend(ri) {
            continue;
        }
        assert_eq!(r.len(), 1, "N2: the rail is lent out");
        let sg = r[0];
        let lent = N2_LENT.with(|l| std::mem::take(&mut l.borrow_mut()[ri]));
        let mut nr = Vec::with_capacity(5);
        for i in 0..4 {
            let q = match lent.get(i) {
                Some(&w) if n2_reacq(mul) && c.n2_take(w) => w,
                _ => c.alloc_qubit(),
            };
            c.cx(sg, q);
            nr.push(q);
        }
        nr.push(sg);
        *r = nr;
    }
}
/// Terminal payload-only kernel, forward (tick 137: no forced steps, letter (s3, k1, k2)): [`fwd_tick_fast`]'s
/// merged branch alone. `skip_rot`: the payload rotation is left out (LF_DIV_PHROT's endpoint repairs the phase).
fn n2_pay_fwd_last(c: &mut Builder, letter: &[QubitId], p: &mut [Vec<QubitId>; 2], skip_rot: bool) {
    let t = rounds() - 1;
    assert_eq!(tail_forced(t), 0, "N2: the last tick has no forced steps");
    assert_eq!(letter.len(), 3, "N2: the last tick's letter is (s3, k1, k2)");
    let [w, ..] = steps()[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let (fold, proxy) = proxy_fold(w, false);
    let (s3, k1, k2) = (letter[0], letter[1], letter[2]);
    let (pt, ps) = (p[ti].clone(), p[si].clone());
    let q0 = pmark(c);
    let merged = merged_fits(c.active_qubits() as usize + usize::from(t >= tie_from() && !tie_seed()), t, false);
    if merged.is_none() {
        cells::with_tie(None, || cells::with_cmp_shift(cmp_shift_at(t), || cells::add_halve(c, s3, &ps, &pt, fold, proxy)));
    }
    SKIP_ROT4.with(|s| s.set(skip_rot));
    if let Some(mw) = merged {
        let fd = n2_offset("SL_N2_FD", "", t, 2);
        n2_extra_set(fd);
        cells::with_tie(None, || {
            cells::with_cmp_shift(cmp_shift_at(t), || cells::with_bridge(proxy, false, || {
                let split = merged_split(c, proxy, false, false);
                merged_fwd(c, s3, &ps, &pt, k1, k2, proxy, split, mw)
            }))
        });
        n2_extra_set(-fd);
    } else {
        cmod_barrel(c, k1, k2, &p[ti], false);
    }
    SKIP_ROT4.with(|s| s.set(false));
    pacc(c, if merged.is_some() { "n2.fwd_last_merged" } else { "n2.fwd_last_barrel" }, q0);
}
/// Terminal payload-only kernel, reverse: [`rev_tick_fast`]'s merged branch alone ([`merged_rev`] rotates up itself).
fn n2_pay_rev_last(c: &mut Builder, letter: &[QubitId], p: &mut [Vec<QubitId>; 2]) {
    let t = rounds() - 1;
    assert_eq!(tail_forced(t), 0, "N2: the last tick has no forced steps");
    assert_eq!(letter.len(), 3, "N2: the last tick's letter is (s3, k1, k2)");
    let [w, ..] = steps()[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let (fold, proxy) = proxy_fold(w, true);
    let (s3, k1, k2) = (letter[0], letter[1], letter[2]);
    let (pt, ps) = (p[ti].clone(), p[si].clone());
    let q0 = pmark(c);
    let merged = merged_fits(c.active_qubits() as usize + usize::from(t >= tie_from() && !tie_seed()), t, true);
    if let Some(mw) = merged {
        let md = n2_offset("SL_N2_MD", N2_MD_PLAN, t, 2);
        n2_extra_set(md);
        cells::with_tie(None, || {
            cells::with_cmp_shift(cmp_shift_at(t), || cells::with_bridge(proxy, true, || merged_rev(c, s3, &ps, &pt, k1, k2, proxy, true, mw)))
        });
        n2_extra_set(-md);
    } else {
        cmod_barrel(c, k1, k2, &p[ti], true);
        c.x(s3);
        cells::with_tie(None, || cells::with_cmp_shift(cmp_shift_at(t), || cells::double_add(c, s3, &ps, &pt, fold, proxy)));
        c.x(s3);
    }
    pacc(c, if merged.is_some() { "n2.rev_last_merged" } else { "n2.rev_last_barrel" }, q0);
}
/// The divide's batch, after the fused ticks below [`n2_from`]: rails-only ticks to the end (under Y28_KEEP, as the
/// fused ticks they replace), the loan, the payload-only ticks (one-fold) and the terminal kernel, the loan returned.
fn n2_div_batch(c: &mut Builder, wk: &mut Walk, pay: &mut [Vec<QubitId>; 2]) {
    let from = n2_from(false);
    let q0 = pmark(c);
    for t in from..rounds() {
        Y28_KEEP.with(|d| d.set(true));
        fwd_tick(c, wk, t, None);
        Y28_KEEP.with(|d| d.set(false));
    }
    pacc(c, "n2.div_rails", q0);
    let q0 = pmark(c);
    n2_loan_out(c, wk, sl_n2() == 8);
    N2_FWD_BATCH.with(|f| f.set(true));
    for t in from..rounds() - 1 {
        let letter = wk.tape[t].clone();
        let pads = lr_pad(c, 2 * lowrel() as usize);
        N2_TICK.with(|x| x.set(t));
        let fd = n2_offset("SL_N2_FD", "", t, 0);
        n2_extra_set(fd);
        pay_fwd_tick(c, t, &letter, pay);
        n2_extra_set(-fd);
        N2_TICK.with(|x| x.set(usize::MAX));
        lr_unpad(c, pads);
    }
    N2_FWD_BATCH.with(|f| f.set(false));
    pacc(c, "n2.div_pay", q0);
    let letter = wk.tape[rounds() - 1].clone();
    n2_pay_fwd_last(c, &letter, pay, sl_n2() != 6);
    if sl_n2() == 9 {
        // control: a relabelling (no gate); the endpoint measures P1 and repairs the phase with two Z's misplaced
        pay[1].swap(100, 101);
    }
    n2_loan_in(c, wk, false);
}
/// The multiply's batch, after the endpoint: the loan, the terminal reverse kernel, the payload-only reverse ticks
/// down to [`n2_from`] (three-fold), the loan returned, the rails-only reverse ticks down to [`n2_from`].
fn n2_mul_batch(c: &mut Builder, wk: &mut Walk, pay: &mut [Vec<QubitId>; 2]) {
    let from = n2_from(true);
    n2_loan_out(c, wk, sl_n2() == 7);
    let letter = wk.tape[rounds() - 1].clone();
    n2_pay_rev_last(c, &letter, pay);
    let q0 = pmark(c);
    N2_THREEFOLD_REV.with(|f| f.set(true));
    for t in (from..rounds() - 1).rev() {
        let letter = wk.tape[t].clone();
        let pads = lr_pad(c, 2 * lowrel() as usize);
        pay_rev_tick(c, t, &letter, pay);
        lr_unpad(c, pads);
    }
    N2_THREEFOLD_REV.with(|f| f.set(false));
    pacc(c, "n2.mul_pay", q0);
    n2_loan_in(c, wk, true);
    let q0 = pmark(c);
    for t in (from..rounds()).rev() {
        rev_tick(c, wk, t, None);
    }
    pacc(c, "n2.mul_rails", q0);
}

/// `y <- y / x (mod p)`, x restored. Division payload fused into the forward walk; rails-only walkback.
pub fn divide(c: &mut Builder, y: &[QubitId], x: &[QubitId]) {
    divide_dbg(c, y, x, false);
}
/// `LF_SEAMS=1`: fuse the coordinate ops into the walks' seeds (see [`seed_r0_seam`], [`seam_add_reduce`]).
pub fn seams() -> bool {
    lf_seams() && seed_half()
}

/// [`divide`] with the coordinate shell fused in (`LF_SEAMS`): x <- x2 - ox enters the seed, and the unseed leaves
/// x = x2 - ox + 3 ox + (square offset) mod p, i.e. the state after coord_x_sub, divide and coord_add3x.
pub fn divide_seamed(c: &mut Builder, y: &[QubitId], x: &[QubitId], ox: &[crate::circuit::BitId]) {
    let c3 = super::classical::add3x_operand(c, ox);
    SEAM_OPS.with(|s| *s.borrow_mut() = Some((ox.to_vec(), c3.clone())));
    divide_dbg(c, y, x, false);
    SEAM_OPS.with(|s| *s.borrow_mut() = None);
    super::classical::release_operand(c, &c3);
}

/// [`multiply`] with coord_rsub_final fused into the unseed (`LF_SEAMS`): leaves x = ox - u mod p.
pub fn multiply_seamed(c: &mut Builder, y: &[QubitId], x: &[QubitId], ox: &[crate::circuit::BitId]) {
    let p1 = super::classical::plus1_operand(c, ox);
    SEAM_MUL.with(|s| *s.borrow_mut() = Some((ox.to_vec(), p1.clone())));
    multiply(c, y, x);
    SEAM_MUL.with(|s| *s.borrow_mut() = None);
    super::classical::release_operand(c, &p1);
}

thread_local! {
    /// Divide seam operands (ox, 3 ox + offset mod p) while [`divide_seamed`] runs.
    static SEAM_OPS: std::cell::RefCell<Option<(Vec<crate::circuit::BitId>, Vec<crate::circuit::BitId>)>> = const { std::cell::RefCell::new(None) };
    /// Multiply seam operands (ox, ox + 1) while [`multiply_seamed`] runs.
    static SEAM_MUL: std::cell::RefCell<Option<(Vec<crate::circuit::BitId>, Vec<crate::circuit::BitId>)>> = const { std::cell::RefCell::new(None) };
}


pub(crate) fn divide_dbg(c: &mut Builder, y: &[QubitId], x: &[QubitId], keep_p1: bool) -> Vec<QubitId> {
    let q0 = pmark(c);
    let r = match SEAM_OPS.with(|s| s.borrow().clone()) {
        Some((ox, _)) => {
            let r0 = seed_r0_seam(c, x, &ox);
            let r1 = seed_r1(c, &r0);
            lr_walk_drop(c, [r0, r1])
        }
        None => seed(c, x),
    };
    pacc(c, "div.seed", q0);
    let mut wk = Walk { r, tape: Vec::new() };
    let ahead = lf_reorder(false);
    let t0f = t0_free(false);
    T0_PLAIN.with(|p| p.set(t0f));
    for t in 0..ahead {
        fwd_tick(c, &mut wk, t, None);
    }
    let q0 = pmark(c);
    let p1 = c.alloc_qubits(N);
    c.cx_pairs(y, &p1);
    if seed_half() {
        cells::mod_halve(c, &p1); // P1 = y/2
    } else {
        cells::mod_double(c, &p1);
        mod_addsub(c, false, y, &p1); // P1 = 3y
    }
    let mut pay = [y.to_vec(), p1];
    pacc(c, "div.p1_setup", q0);
    let loan = parity_loan() && !t0f;
    // LF_T0_FREE: the parity loan's rail side still covers payload-only tick 0 (tick 0's letter is live there)
    let mut loan_pad = if loan || t0f { parity_rail_out(c, &wk, ahead) } else { None };
    let mut t0_bits = None;
    for t in 0..ahead {
        let letter = wk.tape[t].clone();
        let pads = lr_pad(c, 2 * lowrel() as usize);
        pay_fwd_tick(c, t, &letter, &mut pay);
        lr_unpad(c, pads);
        if t0f && t == 0 {
            parity_rail_in(c, &mut wk, ahead, loan_pad.take());
            t0_bits = Some(t0_out(c, &wk));
        }
    }
    if loan {
        parity_rail_in(c, &mut wk, ahead, loan_pad);
        loan_pad = parity_tape_out(c, &wk, ahead);
    }
    let dphrot = div_phrot() && !keep_p1;
    assert!(Y28_BITS.with(|b| b.borrow().is_empty()), "y28: kept bits from an earlier walk");
    Y28_COUNT.with(|x| x.set((0, 0)));
    // N2 (SL_N2): the fused ticks end at the batch, which runs the rest (needs LF_DIV_PHROT's endpoint)
    let n2d = dphrot && n2_div();
    let fused_end = if n2d { n2_from(false) } else { rounds() };
    for t in ahead..fused_end {
        if dphrot && t + 1 == rounds() {
            SKIP_PAY_ROT_AT.with(|s| s.set(t));
        }
        // y28: this pass keeps the outcome bits of its split rail adds' boundary carries for the reverse rail pass
        Y28_KEEP.with(|d| d.set(true));
        fwd_tick(c, &mut wk, t, Some(&mut pay));
        Y28_KEEP.with(|d| d.set(false));
        SKIP_PAY_ROT_AT.with(|s| s.set(usize::MAX));
    }
    if n2d {
        n2_div_batch(c, &mut wk, &mut pay);
    }
    let q0 = pmark(c);
    // endpoint: rails (+-1, +-1); P = (s0 lam, s1 lam)
    let (s0, s1) = (*wk.r[0].last().unwrap(), *wk.r[1].last().unwrap());
    let p1 = if dphrot {
        let last = rounds() - 1;
        assert_eq!(last % 2, 1, "LF_DIV_PHROT: the last tick's target is P1");
        let lt = &wk.tape[last];
        let (k1, k2) = (lt[lt.len() - 2], lt[lt.len() - 1]);
        let p1 = std::mem::take(&mut pay[1]);
        let mut bits = Vec::with_capacity(p1.len());
        for &q in p1.iter() {
            let m = c.alloc_bit();
            c.hmr(q, m);
            c.release_clean(q);
            bits.push(m);
        }
        let x01 = c.alloc_qubit();
        c.cx(s0, x01);
        c.cx(s1, x01);
        cells::cond_negate(c, x01, &pay[0]);
        rot4_phase(c, k1, k2, &pay[0], bits, true);
        c.cx(s0, x01);
        c.cx(s1, x01);
        c.free(x01);
        cells::cond_negate(c, s1, &pay[0]);
        p1
    } else {
        let x01 = c.alloc_qubit();
        c.cx(s0, x01);
        c.cx(s1, x01);
        cells::cond_negate(c, x01, &pay[1]);
        c.cx_pairs(&pay[0], &pay[1]);
        c.cx(s0, x01);
        c.cx(s1, x01);
        c.free(x01);
        let p1 = std::mem::take(&mut pay[1]);
        if !keep_p1 {
            c.free_vec(&p1);
        }
        cells::cond_negate(c, s0, &pay[0]);
        p1
    };
    pacc(c, "div.endpoint", q0);
    let mut rt0_r0: Option<Vec<QubitId>> = None;
    for t in (0..rounds()).rev() {
        if loan && t + 1 == ahead {
            parity_tape_in(c, &mut wk, ahead, loan_pad.take()); // back at the boundary: the relation it left by
        }
        if t == 0 {
            if let Some(bits) = t0_bits.take() {
                t0_in(c, &mut wk, bits);
            }
        }
        if t == 0 && rt0_walk_on() {
            // spooky-leapfrog-v1 RT0 (SL_RT0): R0' measured, its phase paid by an oracle; R0 rebuilt
            let q0 = pmark(c);
            rt0_r0 = Some(rt0_walk(c, &mut wk, None));
            pacc(c, "rt0.div", q0);
            continue;
        }
        Y28_USE.with(|d| d.set(true));
        rev_tick(c, &mut wk, t, None);
        Y28_USE.with(|d| d.set(false));
    }
    assert!(T0Q_KEEP.with(|k| k.get()).is_none() && t0h_held() == 0, "defer: tick-0 state left at the divide's end");
    // y28: every kept outcome bit was consumed by exactly one Z (a key is inserted once and removed once)
    assert!(Y28_BITS.with(|b| b.borrow().is_empty()), "y28: kept bits left over at the end of the divide");
    let (y28_kept, y28_applied) = Y28_COUNT.with(|x| x.get());
    assert_eq!(y28_kept, y28_applied, "y28: kept and applied bits differ");
    if Y28_DEFER {
        eprintln!("Y28_DEFER kept={y28_kept} applied={y28_applied}");
    }
    T0_PLAIN.with(|p| p.set(false));
    let q0 = pmark(c);
    match SEAM_OPS.with(|s| s.borrow().clone()) {
        Some((_, c3)) => {
            let r0 = match rt0_r0.take() {
                Some(r0) => r0,
                None => {
                    let rr = lr_walk_restore(c, wk.r);
                    unseed_r1(c, rr)
                }
            };
            let low = seam_add_reduce(c, r0, &c3, &c3);
            restore_onto(c, low, x);
        }
        None => {
            assert!(rt0_r0.is_none(), "RT0 needs the seam");
            unseed(c, wk.r, x)
        }
    }
    pacc(c, "div.unseed", q0);
    p1
}

/// `y <- y * x (mod p)`, x restored. Rails-only forward, payload fused into the walkback.
pub fn multiply(c: &mut Builder, y: &[QubitId], x: &[QubitId]) {
    let q0 = pmark(c);
    let r = match T6_PRESEED.with(|s| s.borrow_mut().take()) {
        Some(r0) => {
            assert_eq!(&r0[..N], x, "T6 seed fusion: R0 must sit on x's wires");
            let r1 = seed_r1(c, &r0);
            lr_walk_drop(c, [r0, r1])
        }
        None => seed(c, x),
    };
    pacc(c, "mul.seed", q0);
    let mut wk = Walk { r, tape: Vec::new() };
    let t0f = t0_free(true);
    T0_PLAIN.with(|p| p.set(t0f));
    let loan = parity_loan() && !t0f;
    let ahead = lf_reorder(true);
    let mut loan_pad = None;
    let mut t0_bits = None;
    for t in 0..rounds() {
        fwd_tick(c, &mut wk, t, None);
        if t0f && t == 0 {
            t0_bits = Some(t0_out(c, &wk));
        }
        if loan && t + 1 == ahead {
            loan_pad = parity_tape_out(c, &wk, ahead);
        }
    }
    let (s0, s1) = (*wk.r[0].last().unwrap(), *wk.r[1].last().unwrap());
    let q0 = pmark(c);
    let mut pay = [y.to_vec(), c.alloc_qubits(N)];
    cells::cond_negate(c, s0, &pay[0]);
    c.cx_pairs(&pay[0], &pay[1]);
    let x01 = c.alloc_qubit();
    c.cx(s0, x01);
    c.cx(s1, x01);
    cells::cond_negate(c, x01, &pay[1]);
    c.cx(s0, x01);
    c.cx(s1, x01);
    c.free(x01);
    pacc(c, "mul.endpoint", q0);
    // N2 (SL_N2): the batch runs ticks rounds - 1 .. n2_from first
    let fused_top = if n2_mul() {
        n2_mul_batch(c, &mut wk, &mut pay);
        n2_from(true)
    } else {
        rounds()
    };
    for t in (ahead..fused_top).rev() {
        rev_tick(c, &mut wk, t, Some(&mut pay));
    }
    if loan {
        parity_tape_in(c, &mut wk, ahead, loan_pad.take());
        loan_pad = parity_rail_out(c, &wk, ahead);
    }
    for t in (0..ahead).rev() {
        if t0f && t == 0 {
            continue; // LF_T0_FREE: payload tick 0 is not run here (its letter is off the tape)
        }
        let letter = wk.tape[t].clone();
        let pads = lr_pad(c, 2 * lowrel() as usize);
        pay_rev_tick(c, t, &letter, &mut pay);
        lr_unpad(c, pads);
    }
    if loan {
        parity_rail_in(c, &mut wk, ahead, loan_pad.take());
    }
    let q0 = pmark(c);
    let p1 = std::mem::take(&mut pay[1]);
    // LF_T0_DBL=1 (with LF_T0_FREE): the product stays halved (P/2) until tick 0's phase fix, which needs P/2
    // anyway: there P/2 is copied and the product doubled in place (one mod_halve fewer, the same values)
    let t0dbl = t0f && seed_half() && t0_dbl();
    if t0dbl {
        // p1 = P/2
    } else if seed_half() {
        cells::mod_double(c, &p1); // P0
    } else {
        mod_addsub(c, true, &pay[0], &p1); // 2 P0
        cells::mod_halve(c, &p1); // P0
    }
    let mut junk_bits = Vec::new();
    let mut rt0_r0: Option<Vec<QubitId>> = None;
    let mut rt0_pre: Option<Vec<crate::circuit::BitId>> = None;
    if t0f {
        // p1 holds the product (2 y R1 = y R0 mod p); pay[0] holds y R2, a function of the product and tick 0's
        // letter: measured away, the phase fixed at the walk's end. The product moves onto y's wires.
        for &q in pay[0].iter() {
            let m = c.alloc_bit();
            c.hmr(q, m);
            junk_bits.push(m);
        }
        for i in 0..N {
            c.swap(p1[i], pay[0][i]);
        }
    } else {
        c.cx_pairs(&pay[0], &p1);
    }
    c.free_vec(&p1);
    for t in (0..ahead).rev() {
        if t == 0 {
            if let Some(bits) = t0_bits.take() {
                t0_in(c, &mut wk, bits);
                if rt0_walk_on() && y15::sl_t0one() != 0 {
                    // spooky-leapfrog-v1 T0ONE: R0' out first, the phase block below gets its 256 wires
                    rt0_pre = Some(rt0_measure(c, &mut wk));
                }
                let q1 = pmark(c);
                if t0dbl && y15::t0_forms_on(t0_phrot()) {
                    // y26: the same phase on forms over P/2 alone (nothing written, no copy), then the product doubled
                    let letter = wk.tape[0].clone();
                    y15::t0_phase_forms(c, &letter, &pay[0], std::mem::take(&mut junk_bits));
                    if !y15::Y26_FUSE_DBL {
                        cells::mod_double(c, &pay[0]);
                    }
                } else {
                // (-1)^(m . y R2): payload tick 0 forward on (product, product / 2), Z under the kept bits, and back
                let p1 = c.alloc_qubits(N);
                c.cx_pairs(&pay[0], &p1);
                if t0dbl {
                    cells::mod_double(c, &pay[0]); // pay[0]: P/2 -> P; p1 = P/2
                } else {
                    cells::mod_halve(c, &p1);
                }
                let mut pay2 = [pay[0].clone(), p1];
                let letter = wk.tape[0].clone();
                let phrot = t0_phrot();
                if y15::t0_carries_on(phrot) {
                    // y26: the phase block in one call (see Y26_T0)
                    y15::t0_phase(c, &letter, &pay2, std::mem::take(&mut junk_bits));
                } else {
                SKIP_ROT4.with(|s| s.set(phrot));
                pay_fwd_tick(c, 0, &letter, &mut pay2);
                SKIP_ROT4.with(|s| s.set(false));
                if phrot {
                    rot4_phase(c, letter[3], letter[4], &pay2[0], std::mem::take(&mut junk_bits), false);
                } else {
                    for (&q, m) in pay2[0].iter().zip(std::mem::take(&mut junk_bits)) {
                        c.z_if(q, m);
                        c.free_bit(m);
                    }
                }
                SKIP_ROT4.with(|s| s.set(phrot));
                pay_rev_tick(c, 0, &letter, &mut pay2);
                SKIP_ROT4.with(|s| s.set(false));
                }
                let p1 = std::mem::take(&mut pay2[1]);
                cells::mod_double(c, &p1);
                c.cx_pairs(&pay2[0], &p1);
                c.free_vec(&p1);
                }
                pacc(c, "t0.mul_phase", q1);
            }
        }
        if t == 0 && rt0_walk_on() {
            let q0 = pmark(c);
            rt0_r0 = Some(rt0_walk(c, &mut wk, rt0_pre.take()));
            pacc(c, "rt0.mul", q0);
            continue;
        }
        rev_tick(c, &mut wk, t, None);
    }
    T0_PLAIN.with(|p| p.set(false));
    assert!(T0Q_KEEP.with(|k| k.get()).is_none() && t0h_held() == 0, "defer: tick-0 state left at the multiply's end");
    match SEAM_MUL.with(|s| s.borrow().clone()) {
        Some((ox, p1c)) => {
            // ox - R = (-R) + ox: complement R (= -R - 1) and add ox + 1
            let r0 = match rt0_r0.take() {
                Some(r0) => r0,
                None => {
                    let rr = lr_walk_restore(c, wk.r);
                    unseed_r1(c, rr)
                }
            };
            c.x_all(&r0);
            let low = seam_add_reduce(c, r0, &p1c, &ox);
            restore_onto(c, low, x);
        }
        None => {
            assert!(rt0_r0.is_none(), "RT0 needs the seam");
            unseed(c, wk.r, x)
        }
    }
    pacc(c, "mul.p1_unseed", q0);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit::{analyze_ops, QubitOrBit};
    use crate::sim::Simulator;
    use alloy_primitives::U256;
    use sha3::digest::{ExtendableOutput, Update};

    fn modp() -> U256 {
        super::super::SECP256K1_P
    }
    fn mulmod(a: U256, b: U256) -> U256 {
        a.mul_mod(b, modp())
    }
    fn inv(a: U256) -> U256 {
        a.pow_mod(modp() - U256::from(2u8), modp())
    }

    pub(super) fn run_pub(kind: &str, batches: usize) { run(kind, batches) }
    fn run(kind: &str, batches: usize) {
        super::super::install_skywalk_submission_recipe();
        if let Ok(cap) = std::env::var("LF_CAP") { std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", cap); }
        let mut c = Builder::new();
        let x = c.alloc_qubits(N);
        let y = c.alloc_qubits(N);
        let mut extra: Option<Vec<QubitId>> = None;
        let mut extra2: Option<QubitId> = None;
        match kind {
            "div" => divide(&mut c, &y, &x),
            "mul" => multiply(&mut c, &y, &x),
            "rails" | "rails1" => {
                let r = seed(&mut c, &x);
                let mut wk = Walk { r, tape: Vec::new() };
                let n = if kind == "rails1" { 1 } else { rounds() };
                for t in 0..n { fwd_tick(&mut c, &mut wk, t, None); }
                for t in (0..n).rev() { rev_tick(&mut c, &mut wk, t, None); }
                unseed(&mut c, wk.r, &x);
            }
            "seed" => { let r = seed(&mut c, &x); unseed(&mut c, r, &x); }
            "fwdrails" | "fwdpay" | "fwdpaynobar" => {
                let r = seed(&mut c, &x);
                let mut wk = Walk { r, tape: Vec::new() };
                let p1 = c.alloc_qubits(N);
                c.cx_pairs(&y, &p1);
                let mut pay = [y.to_vec(), p1];
                let n = std::env::var("LF_N").ok().and_then(|v| v.parse().ok()).unwrap_or(rounds());
                if kind == "fwdpaynobar" { std::env::set_var("LF_NOBAR", "1"); }
                for t in 0..n { fwd_tick(&mut c, &mut wk, t, if kind == "fwdrails" { None } else { Some(&mut pay) }); }
                std::env::remove_var("LF_NOBAR");
            }
            k if k.starts_with("fr") => {
                // fused forward n ticks, then exact inverse (multiply-direction payload) n ticks: identity
                let n: usize = k[2..].parse().unwrap();
                let r = seed(&mut c, &x);
                let mut wk = Walk { r, tape: Vec::new() };
                let p1 = c.alloc_qubits(N);
                c.cx_pairs(&y, &p1);
                let mut pay = [y.to_vec(), p1];
                for t in 0..n { fwd_tick(&mut c, &mut wk, t, Some(&mut pay)); }
                for t in (0..n).rev() { rev_tick(&mut c, &mut wk, t, Some(&mut pay)); }
                let p1 = std::mem::take(&mut pay[1]);
                c.cx_pairs(&y, &p1);
                c.free_vec(&p1);
                unseed(&mut c, wk.r, &x);
            }
            "cell" => {
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let cw = std::env::var("LF_CELLW").ok().and_then(|v| v.parse().ok()).unwrap_or(200);
                let (fold, proxy) = proxy_fold(cw, false);
                eprintln!("cellw={cw} proxy={proxy} fold={fold}");
                cells::add_halve(&mut c, sg, &x, &y, fold, proxy);
                extra2 = Some(sg);
            }
            "chalve" => { cmod_halve(&mut c, x[0], &y); }
            "cquarter" => { cmod_quarter(&mut c, x[0], &y); }
            "cbarrel" => { cmod_barrel(&mut c, x[0], x[1], &y, false); }
            "cbpair" => { cmod_barrel(&mut c, x[0], x[1], &y, false); cmod_barrel(&mut c, x[0], x[1], &y, true); }
            "rbarrel" => {
                // rail: odd value v * 2^e in a 262-bit register, e = x mod 4; check arithmetic shift right
                let w = 262; let t = c.alloc_qubits(w);
                c.cx_pairs(&y, &t[..N]);
                for q in &t[N..] { c.cx(y[N - 1], *q); }
                rail_barrel(&mut c, x[0], x[1], &t, false);
                rail_barrel(&mut c, x[0], x[1], &t, true);
                for q in &t[N..] { c.cx(y[N - 1], *q); }
                c.cx_pairs(&y, &t[..N]);
                c.free_vec(&t);
            }
            "cqpair" => { cmod_quarter(&mut c, x[0], &y); cmod_quadruple(&mut c, x[0], &y); }
            "celltie" | "celltie261" => {
                let src = c.alloc_qubits(N); c.cx_pairs(&y, &src);
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let (fold, proxy) = proxy_fold(if kind == "celltie" { 200 } else { 261 }, false);
                cells::add_halve(&mut c, sg, &src, &y, fold, proxy);
                c.x(sg);
                cells::double_add(&mut c, sg, &src, &y, fold, proxy);
                c.x(sg);
                c.cx(x[1], sg); c.free(sg);
                c.cx_pairs(&y, &src); c.free_vec(&src);
            }
            "tiesafe" | "tiesafe_neg" => {
                let src = c.alloc_qubits(N); c.cx_pairs(&y, &src);
                if kind == "tiesafe_neg" { let one = c.alloc_qubit(); c.x(one); cells::cond_negate(&mut c, one, &src); c.x(one); c.free(one); }
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let pr = c.alloc_qubit(); c.cx(sg, pr); if kind == "tiesafe_neg" { c.x(pr); }
                let (fold, proxy) = proxy_fold(30, false);
                cells::with_tie(Some(pr), || cells::with_cmp_shift(cmp_shift(), || cells::add_halve(&mut c, sg, &src, &y, fold, proxy)));
                c.x(sg); c.x(pr);
                cells::with_tie(Some(pr), || cells::with_cmp_shift(cmp_shift(), || cells::double_add(&mut c, sg, &src, &y, fold, proxy)));
                c.x(sg); c.x(pr);
                if kind == "tiesafe_neg" { c.x(pr); } c.cx(sg, pr); c.free(pr);
                c.cx(x[1], sg); c.free(sg);
                if kind == "tiesafe_neg" { let one = c.alloc_qubit(); c.x(one); cells::cond_negate(&mut c, one, &src); c.x(one); c.free(one); }
                c.cx_pairs(&y, &src); c.free_vec(&src);
            }
            "cell261" => {
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let (fold, proxy) = proxy_fold(261, false);
                cells::add_halve(&mut c, sg, &x, &y, fold, proxy);
                c.x(sg);
                cells::double_add(&mut c, sg, &x, &y, fold, proxy);
                c.x(sg);
                extra2 = Some(sg);
            }
            "chpair" => { cmod_halve(&mut c, x[0], &y); cmod_double(&mut c, x[0], &y); }
            "cellpair" | "cellpair_m" => {
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let mm = kind == "cellpair_m";
                let (fold, proxy) = proxy_fold(200, false);
                cells::add_halve(&mut c, sg, &x, &y, fold, proxy);
                let (fold2, proxy2) = proxy_fold(200, true);
                let (fold2, proxy2) = if mm { (fold2, proxy2) } else { (fold, proxy) };
                c.x(sg);
                cells::double_add(&mut c, sg, &x, &y, fold2, proxy2);
                c.x(sg);
                extra2 = Some(sg);
            }
            "dbl" => {
                let sg = c.alloc_qubit(); c.cx(x[1], sg);
                let (fold, proxy) = proxy_fold(200, true);
                cells::double_add(&mut c, sg, &x, &y, fold, proxy);
                extra2 = Some(sg);
            }
            "negate" => { cells::cond_negate(&mut c, x[0], &y); }
            "divp1" => { let p1 = divide_dbg(&mut c, &y, &x, true); extra = Some(p1); }
            _ => panic!(),
        }
        if let Some(sg) = extra2 { c.cx(x[1], sg); c.free(sg); }
        c.declare_qubit_register(&x);
        c.declare_qubit_register(&y);
        if let Some(e) = &extra { c.declare_qubit_register(e); }
        let peak = c.peak_total();
        prof_dump();
        let ops = c.take_ops();
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"leapfrog-test");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut rnd = || {
            let mut v = U256::ZERO;
            for i in 0..4 {
                seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
                v |= U256::from(seed) << (64 * i);
            }
            v % modp()
        };
        let (mut bad, mut phase_bad, mut anc_bad, mut shots) = (0, 0, 0, 0);
        let mut phase_shots = 0usize;
        for _ in 0..batches {
            sim.clear_for_shot();
            let mut ins = Vec::new();
            for shot in 0..64 {
                let (xv, yv) = (rnd().max(U256::from(1u8)), rnd());
                sim.set_register(&regs[0], xv, shot);
                sim.set_register(&regs[1], yv, shot);
                ins.push((xv, yv));
            }
            sim.apply_iter(ops.iter());
            if regs.len() > 2 {
                let mut nz = 0;
                let mut ex = None;
                for (shot, &(xv, yv)) in ins.iter().enumerate() {
                    let v = sim.get_register(&regs[2], shot);
                    if v != U256::ZERO { nz += 1; if ex.is_none() { ex = Some((v, mulmod(yv, inv(xv)))); } }
                }
                eprintln!("P1 nonzero in {nz}/64 shots; example (P1, lambda) = {:?}", ex);
            }
            for (shot, &(xv, yv)) in ins.iter().enumerate() {
                let gx = sim.get_register(&regs[0], shot);
                let gy = sim.get_register(&regs[1], shot);
                let want = match kind {
                    "div" | "divp1" => mulmod(yv, inv(xv)),
                    "mul" => mulmod(yv, xv),
                    "cell" => { let h = inv(U256::from(2u8)); let s = if xv.bit(1) { modp() - xv } else { xv }; mulmod(yv.add_mod(s, modp()), h) }
                    "chalve" => if xv.bit(0) { mulmod(yv, inv(U256::from(2u8))) } else { yv },
                    "cquarter" => if xv.bit(0) { mulmod(yv, inv(U256::from(4u8))) } else { yv },
                    "cbarrel" => { let e = (xv.bit(0) as u32) + 2 * (xv.bit(1) as u32); mulmod(yv, inv(U256::from(1u64 << e))) }
                    "cbpair" | "rbarrel" => yv,
                    "cqpair" => yv,
                    "chpair" | "cellpair" | "cellpair_m" | "celltie" | "celltie261" | "cell261" | "tiesafe" | "tiesafe_neg" => yv,
                    "dbl" => { let s = if xv.bit(1) { modp() - xv } else { xv }; yv.add_mod(yv, modp()).add_mod(s, modp()) }
                    "negate" => if xv.bit(0) { (modp() - yv) % modp() } else { yv },
                    _ => yv };
                if gx != xv || gy != want {
                    bad += 1;
                    eprintln!("WRONG kind={kind} x={xv:#x} y={yv:#x} got_x_ok={} got_y={gy:#x} want={want:#x}", gx == xv);
                }
            }
            if sim.phase != 0 {
                phase_bad += 1;
                phase_shots += sim.phase.count_ones() as usize;
                for (shot, &(xv, yv)) in ins.iter().enumerate() {
                    if (sim.phase >> shot) & 1 == 1 {
                        eprintln!("PHASEBAD kind={kind} x={xv:#x} y={yv:#x}");
                    }
                }
            }
            for reg in &regs {
                for qb in reg {
                    if let QubitOrBit::Qubit(q) = *qb {
                        *sim.qubit_mut(q) = 0;
                    }
                }
            }
            if (0..nq).any(|q| sim.qubit(crate::circuit::QubitId(q)) != 0) {
                anc_bad += 1;
            }
            shots += 64;
        }
        let avg_t = sim.stats.toffoli_gates as f64 / shots as f64;
        eprintln!("LEAPFROG {kind}: shots={shots} wrong={bad} phase_bad_batches={phase_bad} phase_bad_shots={phase_shots} ancilla_bad_batches={anc_bad} \
                   avgT={avg_t:.0} peak={peak} qubits={nq} rounds={}", rounds());
        assert_eq!(bad, 0, "wrong results");
        assert_eq!(anc_bad, 0, "ancilla garbage");
    }

    /// Full point addition with LEAPFROG on, simulated like eval_circuit (random k*G points).
    #[test]
    fn leapfrog_point_add() {
        super::super::install_skywalk_submission_recipe();
        std::env::set_var("LEAPFROG", "1");
        std::env::remove_var("BACK_SEAM_FUSE");
        std::env::set_var("NATIVE_SFUSE_B", "1");
        if std::env::var_os("LF_USE_RECIPE").is_some() { install_recipe(); }
        if let Ok(cap) = std::env::var("LF_CAP") { std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", cap); }
        if let Ok(ov) = std::env::var("LF_OVR") {
            for kv in ov.split(';').filter(|k| !k.is_empty()) { let (k, v) = kv.split_once('=').unwrap(); std::env::set_var(k, v); }
        }
        if let Ok(list) = std::env::var("LF_UNSET") {
            for k in list.split(',').filter(|k| !k.is_empty()) { std::env::remove_var(k); }
        }
        let ops = super::super::build_point_add();
        prof_dump();
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        let hx = |h: &str| U256::from_str_radix(h, 16).unwrap();
        let curve = crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
            modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
            a: U256::from(0u8), b: U256::from(7u8),
            gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
            gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
            order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
        };
        let mut h = sha3::Shake256::default();
        h.update(b"leapfrog-pa");
        // LF_PA_MEASSEED: a different measurement-outcome stream (same inputs), to separate phase-prone shots from luck
        if let Ok(ms) = std::env::var("LF_PA_MEASSEED") { h.update(ms.as_bytes()); }
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
        // LF_SIMSEED: a different input stream
        let simseed: u64 = std::env::var("LF_SIMSEED").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
        let mut seed = 0x1234_5678_9abc_def1u64 ^ simseed.wrapping_mul(0x9e37_79b9_7f4a_7c15);
        let mut rnd = || { let mut v = U256::ZERO; for i in 0..4 { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; v |= U256::from(seed) << (64 * i); } v };
        let (mut bad, mut phase_shots, mut anc, mut shots) = (0, 0usize, 0, 0);
        let (mut xbad, mut ybad, mut yneg) = (0, 0, 0);
        let batches = std::env::var("LF_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
        for _ in 0..batches {
            sim.clear_for_shot();
            let mut exp = Vec::new();
            let mut pts = Vec::new();
            let pain: Option<Vec<U256>> = std::env::var("LF_PAIN").ok().map(|v| v.split(',').map(|h| U256::from_str_radix(h.trim().trim_start_matches("0x"), 16).unwrap()).collect());
            for shot in 0..64 {
                let (t, o) = if let Some(pv) = &pain { ((pv[0], pv[1]), (pv[2], pv[3])) } else {
                    (curve.mul(curve.gx, curve.gy, rnd()), curve.mul(curve.gx, curve.gy, rnd())) };
                pts.push((t.0, t.1, o.0, o.1));
                sim.set_register(&regs[0], t.0, shot);
                sim.set_register(&regs[1], t.1, shot);
                sim.set_register(&regs[2], o.0, shot);
                sim.set_register(&regs[3], o.1, shot);
                exp.push(curve.add(t.0, t.1, o.0, o.1));
            }
            sim.apply_iter(ops.iter());
            for (shot, e) in exp.iter().enumerate() {
                let (gx, gy) = (sim.get_register(&regs[0], shot), sim.get_register(&regs[1], shot));
                let ph = (sim.phase >> shot) & 1 == 1;
                if gx != e.0 || gy != e.1 || ph {
                    let (t0, o0) = (pts[shot].0, pts[shot].2);
                    let dx = t0.add_mod(modp() - o0, modp());
                    let xp = o0.add_mod(modp() - e.0, modp());
                    eprintln!("PAFAIL dx={dx:#x} xp={xp:#x} wrong={} phase={}", gx != e.0 || gy != e.1, ph);
                    if std::env::var_os("LF_PAFULL").is_some() { eprintln!("PAINPUT batch={} shot={shot} x2={:#x} y2={:#x} ox={:#x} oy={:#x}", shots / 64, pts[shot].0, pts[shot].1, pts[shot].2, pts[shot].3); }
                }
                if gx != e.0 || gy != e.1 { bad += 1; }
                if gx != e.0 { xbad += 1; }
                if gy != e.1 { ybad += 1; if gy == (modp() - e.1) % modp() { yneg += 1; } }
            }
            phase_shots += sim.phase.count_ones() as usize;
            for reg in &regs { for qb in reg { if let QubitOrBit::Qubit(q) = *qb { *sim.qubit_mut(q) = 0; } } }
            if (0..nq).any(|q| sim.qubit(crate::circuit::QubitId(q)) != 0) { anc += 1; }
            shots += 64;
        }
        let avg_t = sim.stats.toffoli_gates as f64 / shots as f64;
        eprintln!("LEAPFROG point_add: xbad={xbad} ybad={ybad} (y negated: {yneg})");
        eprintln!("LEAPFROG point_add: shots={shots} wrong={bad} phase_bad_shots={phase_shots} ancilla_bad_batches={anc} \
                   avgT={avg_t:.0} qubits={nq} score={:.0}", avg_t * nq as f64);
    }

    /// Single payload cell on parked pairs (LF_UT=1): P_S = lam b, P_T = lam t (t, b = +-1), the walk's sign
    /// (T + (-1)^s B = 2T), at tick LF_UT_T, direction LF_UT_DIR (fwd add_halve / rev double_add), with the live count
    /// padded to the real tick's (512 + 5t + 2W + 3, or LF_UT_ACTIVE). LF_UT_TIE=1 runs the tie-safe mode.
    /// LF_UT_MODE=rand: random P_T, P_S, s (control). Reports value and phase failures.
    #[test]
    fn leapfrog_tie_unit() {
        if std::env::var_os("LF_UT").is_none() { return; }
        super::super::install_skywalk_submission_recipe();
        std::env::set_var("LEAPFROG", "1");
        std::env::remove_var("BACK_SEAM_FUSE");
        std::env::set_var("NATIVE_SFUSE_B", "1");
        install_recipe();
        if let Ok(ov) = std::env::var("LF_OVR") { for kv in ov.split(';').filter(|k| !k.is_empty()) { let (k, v) = kv.split_once('=').unwrap(); std::env::set_var(k, v); } }
        let t: usize = std::env::var("LF_UT_T").ok().and_then(|v| v.parse().ok()).unwrap_or(120);
        let rev = std::env::var("LF_UT_DIR").is_ok_and(|v| v == "rev");
        let tie = std::env::var("LF_UT_TIE").is_ok_and(|v| v == "1");
        let rand = std::env::var("LF_UT_MODE").is_ok_and(|v| v == "rand");
        let w = steps()[t][0];
        let active: usize = std::env::var("LF_UT_ACTIVE").ok().and_then(|v| v.parse().ok()).unwrap_or(512 + 5 * t + 2 * w + 3);
        let mut c = Builder::new();
        let pt = c.alloc_qubits(N);
        let ps = c.alloc_qubits(N);
        let s = c.alloc_qubit();
        let tsg = c.alloc_qubit();
        let ssg = c.alloc_qubit();
        let pad = c.alloc_qubits(active.saturating_sub(c.active_qubits() as usize));
        let (fold, proxy) = proxy_fold(w, rev);
        if rev { c.x(s); }
        let pr = tie.then(|| { let q = c.alloc_qubit(); c.cx(s, q); c.cx(tsg, q); c.cx(ssg, q); q });
        cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift_at(t), || if rev {
            cells::double_add(&mut c, s, &ps, &pt, fold, proxy)
        } else {
            cells::add_halve(&mut c, s, &ps, &pt, fold, proxy)
        }));
        if let Some(q) = pr { c.cx(s, q); c.cx(tsg, q); c.cx(ssg, q); c.free(q); }
        if rev { c.x(s); }
        c.free_vec(&pad);
        c.declare_qubit_register(&pt);
        c.declare_qubit_register(&ps);
        c.declare_qubit_register(&[s]);
        c.declare_qubit_register(&[tsg]);
        c.declare_qubit_register(&[ssg]);
        let ops = c.take_ops();
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        let p = modp();
        let mut h = sha3::Shake256::default();
        h.update(b"leapfrog-tie-unit");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
        let mut seed = 0x2545_f491_4f6c_dd1du64 ^ (t as u64) << 32;
        let mut rnd = || { let mut v = U256::ZERO; for i in 0..4 { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; v |= U256::from(seed) << (64 * i); } v };
        let batches: usize = std::env::var("LF_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(16);
        let (mut bad, mut phb, mut shots) = (0usize, 0usize, 0usize);
        let half = (p + U256::from(1u8)) >> 1; // 1/2 mod p
        for _ in 0..batches {
            sim.clear_for_shot();
            let mut exp = Vec::new();
            for shot in 0..64 {
                let lam = rnd().reduce_mod(p);
                let r = rnd();
                let (tneg, bneg) = (r.bit(0), r.bit(1));
                let fixed = std::env::var("LF_UT_LAM").ok().map(|l| {
                    let lam = U256::from_str_radix(l.trim_start_matches("0x"), 16).unwrap();
                    let m = |k: &str| { let v: i64 = std::env::var(k).unwrap().parse().unwrap();
                        let a = lam.mul_mod(U256::from(v.unsigned_abs()), p); if v < 0 { (p - a) % p } else { a } };
                    (m("LF_UT_PT"), m("LF_UT_PS"), std::env::var("LF_UT_SUB").is_ok_and(|v| v == "1"))
                });
                let (vt, vs, sub) = if let Some(f) = fixed { f } else if rand {
                    (rnd().reduce_mod(p), lam, r.bit(2))
                } else {
                    (if tneg { (p - lam) % p } else { lam }, if bneg { (p - lam) % p } else { lam }, tneg != bneg)
                };
                let sv = if sub { (p - vs) % p } else { vs };
                let want = if rev { vt.add_mod(vt, p).add_mod(p - sv, p) } else { vt.add_mod(sv, p).mul_mod(half, p) };
                sim.set_register(&regs[0], vt, shot);
                sim.set_register(&regs[1], vs, shot);
                sim.set_register(&regs[2], U256::from(sub as u8), shot);
                sim.set_register(&regs[3], U256::from(tneg as u8), shot);
                sim.set_register(&regs[4], U256::from(bneg as u8), shot);
                exp.push(want);
            }
            sim.apply_iter(ops.iter());
            for (shot, e) in exp.iter().enumerate() {
                let got = sim.get_register(&regs[0], shot);
                if got != *e { bad += 1; }
                if (sim.phase >> shot) & 1 == 1 { phb += 1; }
            }
            shots += 64;
        }
        eprintln!("TIEUNIT t={t} rev={rev} tie={tie} rand={rand} active={active} proxy={proxy} fold={fold} shots={shots} wrong={bad} phase_bad={phb}");
    }

    /// Bisect harness: fixed input (LF_X, LF_Y) in every shot; the multiply's fused walk-back stops after tick
    /// LF_N (inclusive) and the payload pair is printed for shot 0 (no cleanup; compare with y * R(n) mod p).
    #[test]
    fn leapfrog_trace() {
        let Ok(xs) = std::env::var("LF_X") else { return };
        super::super::install_skywalk_submission_recipe();
        if let Ok(cap) = std::env::var("LF_CAP") { std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", cap); }
        let xv = U256::from_str_radix(xs.trim_start_matches("0x"), 16).unwrap();
        let yv = U256::from_str_radix(std::env::var("LF_Y").unwrap().trim_start_matches("0x"), 16).unwrap();
        let n: usize = std::env::var("LF_N").unwrap().parse().unwrap();
        let mut c = Builder::new();
        let x = c.alloc_qubits(N);
        let y = c.alloc_qubits(N);
        let r = seed(&mut c, &x);
        let mut wk = Walk { r, tape: Vec::new() };
        for t in 0..rounds() { fwd_tick(&mut c, &mut wk, t, None); }
        let (s0, s1) = (*wk.r[0].last().unwrap(), *wk.r[1].last().unwrap());
        let mut pay = [y.to_vec(), c.alloc_qubits(N)];
        cells::cond_negate(&mut c, s0, &pay[0]);
        c.cx_pairs(&pay[0], &pay[1]);
        let x01 = c.alloc_qubit();
        c.cx(s0, x01); c.cx(s1, x01);
        cells::cond_negate(&mut c, x01, &pay[1]);
        c.cx(s0, x01); c.cx(s1, x01);
        c.free(x01);
        for t in (n..rounds()).rev() { rev_tick(&mut c, &mut wk, t, Some(&mut pay)); }
        c.declare_qubit_register(&x);
        c.declare_qubit_register(&y);
        c.declare_qubit_register(&pay[1]);
        let ops = c.take_ops();
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"leapfrog-trace");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
        sim.clear_for_shot();
        for shot in 0..64 { sim.set_register(&regs[0], xv, shot); sim.set_register(&regs[1], yv, shot); }
        sim.apply_iter(ops.iter());
        eprintln!("TRACE n={n} P0={:#x} P1={:#x} phase={:#x}", sim.get_register(&regs[1], 0), sim.get_register(&regs[2], 0), sim.phase);
    }

    /// Official-semantics failure count over several nonces: the env-free `build()` op stream, re-nonced with
    /// `apply_tail_nonce`, then eval_circuit's exact Fiat-Shamir shot derivation and 64-shot batch simulation.
    /// LF_NONCE0 (start), LF_NONCES (count). Prints distinct failing shots per nonce.
    #[test]
    fn leapfrog_official_lambda() {
        let Ok(n_nonces) = std::env::var("LF_NONCES") else { return };
        let n_nonces: u64 = n_nonces.parse().unwrap();
        let nonce0: u64 = std::env::var("LF_NONCE0").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        let base = super::super::build();
        let hx = |h: &str| U256::from_str_radix(h, 16).unwrap();
        let curve = crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
            modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
            a: U256::from(0u8), b: U256::from(7u8),
            gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
            gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
            order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
        };
        let mut tot = 0usize;
        for k in 0..n_nonces {
            let nonce = nonce0 + k;
            let ops = super::super::apply_tail_nonce(base.clone(), nonce);
            let (nq, nb, _, regs) = analyze_ops(ops.iter());
            let mut h = sha3::Shake256::default();
            h.update(b"quantum_ecc-fiat-shamir-v2");
            h.update(&(ops.len() as u64).to_le_bytes());
            for op in &ops {
                h.update(&[op.kind as u8]);
                h.update(&op.q_control2.0.to_le_bytes());
                h.update(&op.q_control1.0.to_le_bytes());
                h.update(&op.q_target.0.to_le_bytes());
                h.update(&op.c_target.0.to_le_bytes());
                h.update(&op.c_condition.0.to_le_bytes());
                h.update(&op.r_target.0.to_le_bytes());
            }
            let mut xof = h.finalize_xof();
            let (mut tg, mut of, mut ex) = (Vec::new(), Vec::new(), Vec::new());
            for _ in 0..9024 {
                let mut rb = [[0u8; 32]; 2];
                sha3::digest::XofReader::read(&mut xof, &mut rb[0]);
                sha3::digest::XofReader::read(&mut xof, &mut rb[1]);
                let (k1, k2) = (U256::from_le_bytes(rb[0]), U256::from_le_bytes(rb[1]));
                let t = curve.mul(curve.gx, curve.gy, k1);
                let o = curve.mul(curve.gx, curve.gy, k2);
                if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) { continue; }
                ex.push(curve.add(t.0, t.1, o.0, o.1));
                tg.push(t);
                of.push(o);
            }
            let n = tg.len();
            let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
            let (mut fails, mut wrong, mut phase) = (0usize, 0usize, 0usize);
            for b in 0..(n + 63) / 64 {
                let bs = 64.min(n - b * 64);
                let mask: u64 = if bs == 64 { u64::MAX } else { (1u64 << bs) - 1 };
                sim.clear_for_shot();
                for s in 0..bs {
                    let i = b * 64 + s;
                    sim.set_register(&regs[0], tg[i].0, s);
                    sim.set_register(&regs[1], tg[i].1, s);
                    sim.set_register(&regs[2], of[i].0, s);
                    sim.set_register(&regs[3], of[i].1, s);
                }
                sim.apply_iter(ops.iter());
                let ph = sim.phase & mask;
                for s in 0..bs {
                    let i = b * 64 + s;
                    let bad = sim.get_register(&regs[0], s) != ex[i].0 || sim.get_register(&regs[1], s) != ex[i].1;
                    if bad { wrong += 1; }
                    if (ph >> s) & 1 == 1 { phase += 1; }
                    if bad || (ph >> s) & 1 == 1 { fails += 1; }
                }
            }
            tot += fails;
            eprintln!("OFFICIAL nonce={nonce} shots={n} failing={fails} (wrong {wrong}, phase {phase})");
        }
        eprintln!("OFFICIAL mean failing shots per draw = {:.2} over {n_nonces} nonces", tot as f64 / n_nonces as f64);
    }

    fn mprim_win() -> usize {
        std::env::var("LF_MPRIM_WIN").ok().and_then(|v| v.parse().ok()).unwrap_or(merged_win())
    }

    /// LF_MERGED primitives: kinds (LF_MPRIM_KINDS, default all) mfwd / mrev / mpair (merged forward, reverse,
    /// forward-then-reverse) and cfwd / crev (production cell + barrel equivalents, for cost). Inputs: x = S, y = T,
    /// c = (sg, k1, k2); residues mixed uniform / low / high / special values / T = +-S. LF_MPRIM_PAD idle qubits
    /// shrink the cap room (multi-chunk adder layouts); LF_CELLW picks the proxy width.
    #[test]
    fn leapfrog_merged_prims() {
        let Ok(kinds) = std::env::var("LF_MPRIM_KINDS") else { return };
        super::super::install_skywalk_submission_recipe();
        install_recipe();
        if let Ok(cap) = std::env::var("LF_CAP") { std::env::set_var("HEO_PIN_PP_WALK_MAX_QUBITS", cap); }
        let batches: usize = std::env::var("LF_MPRIM_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(16);
        let pad: usize = std::env::var("LF_MPRIM_PAD").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
        let cw: usize = std::env::var("LF_CELLW").ok().and_then(|v| v.parse().ok()).unwrap_or(200);
        let mut tot_bad = 0;
        for kind in kinds.split(',') {
            let mut c = Builder::new();
            let x = c.alloc_qubits(N);
            let y = c.alloc_qubits(N);
            let ctl = c.alloc_qubits(4);
            let padq = c.alloc_qubits(pad);
            let (sg, k1, k2, neg) = (ctl[0], ctl[1], ctl[2], ctl[3]);
            // tie kinds (mt*/ct*): inputs y = +-x, the cells' tie predicate sign ^ [P_T == -P_S] on a live wire
            let tie = kind.starts_with("mt") || kind.starts_with("ct");
            let base_kind = if tie { format!("{}{}", &kind[..1], &kind[2..]) } else { kind.to_string() };
            let mulw = base_kind == "mrev" || base_kind == "crev";
            let (fold, proxy) = proxy_fold(cw, mulw);
            let pred = |c: &mut Builder, flip: bool| -> Option<QubitId> {
                tie.then(|| { let q = c.alloc_qubit(); c.cx(sg, q); c.cx(neg, q); if flip { c.x(q); } q })
            };
            let unpred = |c: &mut Builder, q: Option<QubitId>, flip: bool| {
                if let Some(q) = q { if flip { c.x(q); } c.cx(neg, q); c.cx(sg, q); c.free(q); }
            };
            let fwd = |c: &mut Builder| {
                let pr = pred(c, false);
                cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::with_bridge(proxy, false, || {
                    let split = if pr.is_none() { merged_split(c, proxy, false, false) } else { None };
                    eprintln!("MPRIM split fwd {split:?}");
                    merged_fwd(c, sg, &x, &y, k1, k2, proxy, split, mprim_win())
                })));
                unpred(c, pr, false);
            };
            let rev = |c: &mut Builder| {
                let pr = pred(c, true);
                cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::with_bridge(proxy, true, || merged_rev(c, sg, &x, &y, k1, k2, proxy, pr.is_none(), mprim_win()))));
                unpred(c, pr, true);
            };
            let a0 = c.active_qubits();
            match base_kind.as_str() {
                "mfwd" => fwd(&mut c),
                "mrev" => rev(&mut c),
                "mpair" => { fwd(&mut c); rev(&mut c); }
                "cfwd" => {
                    let pr = pred(&mut c, false);
                    cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::add_halve(&mut c, sg, &x, &y, fold, proxy)));
                    unpred(&mut c, pr, false);
                    cmod_barrel(&mut c, k1, k2, &y, false);
                }
                "crev" => {
                    cmod_barrel(&mut c, k1, k2, &y, true);
                    c.x(sg);
                    let pr = pred(&mut c, false);
                    cells::with_tie(pr, || cells::with_cmp_shift(cmp_shift(), || cells::double_add(&mut c, sg, &x, &y, fold, proxy)));
                    unpred(&mut c, pr, false);
                    c.x(sg);
                }
                _ => panic!("kind {kind}"),
            }
            assert_eq!(c.active_qubits(), a0, "{kind}: live count changed");
            let extra_peak = c.peak_total() - a0;
            c.free_vec(&padq);
            c.declare_qubit_register(&x);
            c.declare_qubit_register(&y);
            c.declare_qubit_register(&ctl);
            let ops = c.take_ops();
            let (nq, nb, _, regs) = analyze_ops(ops.iter());
            let mut h = sha3::Shake256::default();
            h.update(b"leapfrog-merged");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
            let mut seed = 0x5851_f42d_4c95_7f2du64;
            let mut r64 = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
            let p = modp();
            let fv = U256::from((1u64 << 32) + 977);
            let specials = [U256::ZERO, U256::from(1u8), fv - U256::from(1u8), fv, fv + U256::from(1u8), p - U256::from(1u8),
                            p - fv, (p - U256::from(1u8)) >> 1, (p + U256::from(1u8)) >> 1, U256::from(2u8), p - U256::from(2u8)];
            let (mut bad, mut phase_bad, mut anc_bad, mut shots) = (0usize, 0usize, 0usize, 0usize);
            for b in 0..batches {
                sim.clear_for_shot();
                let mut ins = Vec::new();
                for shot in 0..64 {
                    let mut pick = |mode: u64, r64: &mut dyn FnMut() -> u64| -> U256 {
                        match mode {
                            0..=5 => { let mut v = U256::ZERO; for i in 0..4 { v |= U256::from(r64()) << (64 * i); } v % p }
                            6 => U256::from(r64() >> 24),
                            7 => p - U256::from(1u8) - U256::from(r64() >> 24),
                            _ => specials[(r64() % specials.len() as u64) as usize],
                        }
                    };
                    let uni = std::env::var("LF_MPRIM_MODE").is_ok_and(|v| v == "uniform");
                    let mx = if uni { 0 } else { r64() % 9 };
                    let xv = pick(mx, &mut r64);
                    let my = if uni { 0 } else { r64() % 11 };
                    let yv = match my { 9 => xv, 10 => (p - xv) % p, m => pick(m, &mut r64) };
                    let cv = r64() & 7;
                    // tie kinds: y = x or y = -x, neg bit = [y == -x]
                    let (yv, cv) = if tie { if r64() & 1 == 1 { ((p - xv) % p, cv | 8) } else { (xv, cv) } } else { (yv, cv) };
                    // first batch: x, y special values (mixed mode only)
                    let (xv, yv) = if !tie && !uni && b == 0 && shot < 32 { (specials[shot % specials.len()], specials[(shot * 7 + 3) % specials.len()]) } else { (xv, yv) };
                    sim.set_register(&regs[0], xv, shot);
                    sim.set_register(&regs[1], yv, shot);
                    sim.set_register(&regs[2], U256::from(cv), shot);
                    ins.push((xv, yv, cv));
                }
                sim.apply_iter(ops.iter());
                for (shot, &(xv, yv, cv)) in ins.iter().enumerate() {
                    let (sgv, e) = (cv & 1 == 1, ((cv >> 1) & 1) + 2 * ((cv >> 2) & 1));
                    let k = 1 + e as usize;
                    let sx = if sgv { (p - xv) % p } else { xv };
                    let want = match base_kind.as_str() {
                        "mfwd" | "cfwd" => mulmod(yv.add_mod(sx, p), inv(U256::from(1u64 << k))),
                        "mrev" | "crev" => mulmod(yv, U256::from(1u64 << k)).add_mod((p - sx) % p, p),
                        _ => yv,
                    };
                    let (gx, gy, gc) = (sim.get_register(&regs[0], shot), sim.get_register(&regs[1], shot), sim.get_register(&regs[2], shot));
                    if gx != xv || gy != want || gc != U256::from(cv) {
                        bad += 1;
                        if bad <= 8 { eprintln!("MPRIM WRONG {kind} x={xv:#x} y={yv:#x} sg={sgv} e={e} got={gy:#x} want={want:#x} x_ok={} c_ok={}", gx == xv, gc == U256::from(cv)); }
                    }
                    if (sim.phase >> shot) & 1 == 1 {
                        phase_bad += 1;
                        if phase_bad <= 8 { eprintln!("MPRIM PHASE {kind} x={xv:#x} y={yv:#x} sg={sgv} e={e}"); }
                    }
                    if std::env::var_os("LF_MPRIM_DUMP").is_some() && (gy != want || (sim.phase >> shot) & 1 == 1) {
                        eprintln!("MSHOT {kind} {b} {shot} wrong={} phase={} x={xv:#x} y={yv:#x} sg={sgv} e={e}", gy != want, (sim.phase >> shot) & 1);
                    }
                }
                for reg in &regs { for qb in reg { if let QubitOrBit::Qubit(q) = *qb { *sim.qubit_mut(q) = 0; } } }
                if (0..nq).any(|q| sim.qubit(crate::circuit::QubitId(q)) != 0) { anc_bad += 1; }
                shots += 64;
            }
            let avg_t = sim.stats.toffoli_gates as f64 / shots as f64;
            eprintln!("MPRIM {kind}: cellw={cw} proxy={proxy} fold={fold} pad={pad} shots={shots} wrong={bad} phase_bad={phase_bad} anc_bad_batches={anc_bad} avgT={avg_t:.2} extra_peak={extra_peak}");
            tot_bad += bad + phase_bad + anc_bad;
        }
        assert_eq!(tot_bad, 0, "merged primitive failures");
    }

    /// Paired official-semantics comparison: the env-free `build()` op stream without (A) and with (B) LF_MERGED
    /// (via [`FORCE_MERGED`]), each re-nonced with `apply_tail_nonce`; the 9024 shots are derived from A's
    /// Fiat-Shamir hash and run through both streams. LF_PAIRED_NONCES (count), LF_NONCE0 (start).
    #[test]
    fn leapfrog_official_paired() {
        let Ok(n_nonces) = std::env::var("LF_PAIRED_NONCES") else { return };
        let n_nonces: u64 = n_nonces.parse().unwrap();
        let nonce0: u64 = std::env::var("LF_NONCE0").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        // LF_PAIRED_EXTRA="K=V,K=V": B = the recipe plus these entries (default: plus LF_MERGED=1)
        *FORCE_EXTRA.lock().unwrap() = std::env::var("LF_PAIRED_EXTRA").unwrap_or_default().split(',').filter(|e| !e.is_empty())
            .map(|e| { let (k, v) = e.split_once('=').expect("K=V"); (k.to_string(), v.to_string()) }).collect();
        FORCE_MERGED.store(false, std::sync::atomic::Ordering::Relaxed);
        let base_a = super::super::build();
        FORCE_MERGED.store(true, std::sync::atomic::Ordering::Relaxed);
        let base_b = super::super::build();
        FORCE_MERGED.store(false, std::sync::atomic::Ordering::Relaxed);
        let hx = |h: &str| U256::from_str_radix(h, 16).unwrap();
        let curve = crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
            modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
            a: U256::from(0u8), b: U256::from(7u8),
            gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
            gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
            order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
        };
        let fs = |ops: &[crate::circuit::Op]| {
            let mut h = sha3::Shake256::default();
            h.update(b"quantum_ecc-fiat-shamir-v2");
            h.update(&(ops.len() as u64).to_le_bytes());
            for op in ops {
                h.update(&[op.kind as u8]);
                h.update(&op.q_control2.0.to_le_bytes());
                h.update(&op.q_control1.0.to_le_bytes());
                h.update(&op.q_target.0.to_le_bytes());
                h.update(&op.c_target.0.to_le_bytes());
                h.update(&op.c_condition.0.to_le_bytes());
                h.update(&op.r_target.0.to_le_bytes());
            }
            h.finalize_xof()
        };
        let (mut ta, mut tb, mut tw_both, mut tw_a, mut tw_b, mut tp_a, mut tp_b) = (0usize, 0usize, 0, 0, 0, 0, 0);
        let (mut tofa, mut tofb, mut nshots) = (0u64, 0u64, 0usize);
        for k in 0..n_nonces {
            let nonce = nonce0 + k;
            let ops_a = super::super::apply_tail_nonce(base_a.clone(), nonce);
            let ops_b = super::super::apply_tail_nonce(base_b.clone(), nonce);
            let mut xof = fs(&ops_a);
            let (mut tg, mut of, mut ex) = (Vec::new(), Vec::new(), Vec::new());
            for _ in 0..9024 {
                let mut rb = [[0u8; 32]; 2];
                sha3::digest::XofReader::read(&mut xof, &mut rb[0]);
                sha3::digest::XofReader::read(&mut xof, &mut rb[1]);
                let (k1, k2) = (U256::from_le_bytes(rb[0]), U256::from_le_bytes(rb[1]));
                let t = curve.mul(curve.gx, curve.gy, k1);
                let o = curve.mul(curve.gx, curve.gy, k2);
                if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) { continue; }
                ex.push(curve.add(t.0, t.1, o.0, o.1));
                tg.push(t);
                of.push(o);
            }
            let n = tg.len();
            let mut run = |ops: &[crate::circuit::Op], xof_tag: &[u8]| -> (Vec<bool>, Vec<bool>, u64) {
                let (nq, nb, _, regs) = analyze_ops(ops.iter());
                let mut h = sha3::Shake256::default();
                h.update(xof_tag);
                h.update(&nonce.to_le_bytes());
                let mut mx = h.finalize_xof();
                let mut sim = Simulator::new(nq as usize, nb as usize, &mut mx);
                let (mut wrong, mut phase) = (vec![false; n], vec![false; n]);
                for b in 0..(n + 63) / 64 {
                    let bs = 64.min(n - b * 64);
                    sim.clear_for_shot();
                    for s in 0..bs {
                        let i = b * 64 + s;
                        sim.set_register(&regs[0], tg[i].0, s);
                        sim.set_register(&regs[1], tg[i].1, s);
                        sim.set_register(&regs[2], of[i].0, s);
                        sim.set_register(&regs[3], of[i].1, s);
                    }
                    sim.apply_iter(ops.iter());
                    for s in 0..bs {
                        let i = b * 64 + s;
                        wrong[i] = sim.get_register(&regs[0], s) != ex[i].0 || sim.get_register(&regs[1], s) != ex[i].1;
                        phase[i] = (sim.phase >> s) & 1 == 1;
                    }
                }
                (wrong, phase, sim.stats.toffoli_gates)
            };
            let (wa, pa, xa) = run(&ops_a, b"paired-meas");
            let (wb, pb, xb) = run(&ops_b, b"paired-meas");
            let fa = (0..n).filter(|&i| wa[i] || pa[i]).count();
            let fb = (0..n).filter(|&i| wb[i] || pb[i]).count();
            let wboth = (0..n).filter(|&i| wa[i] && wb[i]).count();
            let wonly_a = (0..n).filter(|&i| wa[i] && !wb[i]).count();
            let wonly_b = (0..n).filter(|&i| !wa[i] && wb[i]).count();
            let (pa_n, pb_n) = (pa.iter().filter(|&&x| x).count(), pb.iter().filter(|&&x| x).count());
            eprintln!("PAIRED nonce={nonce} shots={n} failing A={fa} B={fb} | wrong both={wboth} onlyA={wonly_a} onlyB={wonly_b} | phase A={pa_n} B={pb_n} | avgT A={:.1} B={:.1}",
                xa as f64 / n as f64, xb as f64 / n as f64);
            for i in 0..n {
                if wb[i] && !wa[i] { eprintln!("PAIRED_ONLYB_WRONG nonce={nonce} i={i}"); }
            }
            ta += fa; tb += fb; tw_both += wboth; tw_a += wonly_a; tw_b += wonly_b; tp_a += pa_n; tp_b += pb_n;
            tofa += xa; tofb += xb; nshots += n;
        }
        eprintln!("PAIRED total over {n_nonces} nonces: failing A={ta} B={tb} (mean {:.2} / {:.2}) | wrong both={tw_both} onlyA={tw_a} onlyB={tw_b} | phase A={tp_a} B={tp_b} | avgT A={:.1} B={:.1}",
            ta as f64 / n_nonces as f64, tb as f64 / n_nonces as f64, tofa as f64 / nshots as f64, tofb as f64 / nshots as f64);
    }

    #[test]
    fn leapfrog_divide() {
        run("div", std::env::var("LF_DIV_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(16));
    }

    #[test]
    fn leapfrog_prims() {
        for k in ["tiesafe", "tiesafe_neg"] { std::panic::catch_unwind(|| run(k, 2)).ok(); }
    }

    #[test]
    fn leapfrog_bisect() {
        for n in [1usize, 2, 3, 4, 8, 16, 32, 64, 100, 133] {
            let k = format!("fr{n}");
            let k: &'static str = Box::leak(k.into_boxed_str());
            std::panic::catch_unwind(|| run(k, 2)).ok();
        }
    }

    #[test]
    fn leapfrog_divp1() {
        run("divp1", 1);
    }

    #[test]
    fn leapfrog_parts() {
        run("seed", 2);
        run("rails1", 2);
        run("rails", 2);
    }

    #[test]
    fn leapfrog_multiply() {
        run("mul", std::env::var("LF_DIV_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(4));
    }
}
#[cfg(test)]
mod prof {
    #[test]
    fn leapfrog_prim_costs() {
        for k in std::env::var("LF_KINDS").unwrap().split(',').map(|k| &*Box::leak(k.to_string().into_boxed_str())) {
            std::panic::catch_unwind(|| super::tests::run_pub(k, 2)).ok();
        }
    }
}

// ==================================================================================================================
// spooky-leapfrog-v1 research levers RT0 / T0ONE (patch_rt0.py). Off (byte-identical) unless SL_RT0 is set.
// ==================================================================================================================
/// RT0 (SL_RT0, see [`y15::rt0_finish`]) at this walk's last rails reverse tick.
fn rt0_walk_on() -> bool {
    y15::sl_rt0() != 0
}
/// RT0: measure R0' away (X basis): the held wires of tick 0's output, bit j + 1 on wire j. The bits are kept.
fn rt0_measure(c: &mut Builder, wk: &mut Walk) -> Vec<crate::circuit::BitId> {
    let r0p = std::mem::take(&mut wk.r[0]);
    assert_eq!(r0p.len(), N, "RT0: R0' is held on W(1) - 1 = 256 wires");
    r0p.iter()
        .map(|&q| {
            let m = c.alloc_bit();
            c.hmr(q, m);
            c.release_clean(q);
            m
        })
        .collect()
}
/// RT0 in place of `rev_tick(0)`: returns R0 at the seed width w0 with its bit-0 wire (what lr_walk_restore and
/// unseed_r1 return); R1 and the tick-0 letter are consumed. `pre`: R0' already measured (SL_T0ONE).
fn rt0_walk(c: &mut Builder, wk: &mut Walk, pre: Option<Vec<crate::circuit::BitId>>) -> Vec<QubitId> {
    assert!(lf_fast() && lowrel() && seed_half() && lf_seams() && t0_plain(0), "RT0 needs LF_FAST, LF_LOWREL, LF_SEED=half, LF_SEAMS and LF_T0_FREE");
    let bits = match pre {
        Some(b) => b,
        None => rt0_measure(c, wk),
    };
    let r1 = std::mem::take(&mut wk.r[1]);
    let letter = wk.tape.pop().expect("RT0: tick 0's letter");
    assert!(wk.tape.is_empty(), "RT0: tape not empty at tick 0");
    assert_eq!(letter.len(), 5);
    let w0 = envelope()[0].max(N + 4);
    y15::rt0_finish(c, r1, letter, bits, w0)
}
/// The rest of [`unseed_half_rails`] after unseed_r1 (the pilot's unseed of RT0's R0).
fn unseed_half_tail(c: &mut Builder, r0: Vec<QubitId>, d: &[QubitId]) {
    let w0 = r0.len();
    let fs = go_fs("GO_FG_P");
    let ev = c.alloc_qubit();
    c.cx(r0[w0 - 1], ev);
    for i in N..w0 {
        c.cx(ev, r0[i]);
    }
    csub_const_trunc(c, &r0[..fs], f(), ev);
    c.x(ev);
    c.cx(r0[0], ev);
    c.free(ev);
    restore_onto(c, r0, d);
}
/// `RESEARCH_PILOT=rt0`: a one-tick rails walk (seed, tick 0, its letter out and in, then RT0 when SL_RT0 is set or
/// else the head's reverse tick 0, then the unseed), simulated on random inputs. RT0_PILOT_PAD idle wires (default
/// 256, the payload register of the real walks) give RT0 the room it has in the circuit.
pub(crate) fn rt0_pilot() {
    use crate::circuit::{analyze_ops, QubitOrBit};
    use crate::sim::Simulator;
    use ruint::aliases::U256;
    use sha3::digest::{ExtendableOutput, Update};
    let p = U256::MAX - U256::from((1u64 << 32) + 976);
    let batches: usize = std::env::var("RT0_BATCHES").ok().and_then(|v| v.parse().ok()).unwrap_or(64);
    let pad: usize = std::env::var("RT0_PILOT_PAD").ok().and_then(|v| v.parse().ok()).unwrap_or(256);
    let mut c = Builder::new();
    let x = c.alloc_qubits(N);
    let idle = c.alloc_qubits(pad);
    T0_PLAIN.with(|q| q.set(true));
    let r = seed(&mut c, &x);
    let mut wk = Walk { r, tape: Vec::new() };
    fwd_tick(&mut c, &mut wk, 0, None);
    let bits = t0_out(&mut c, &wk);
    t0_in(&mut c, &mut wk, bits);
    let e1 = c.expected_total();
    let a1 = c.active_qubits();
    let rt0 = rt0_walk_on();
    if rt0 {
        let r0 = rt0_walk(&mut c, &mut wk, None);
        eprintln!("RT0PILOT rt0 block expected T {:.1} (live before {a1})", c.expected_total() - e1);
        unseed_half_tail(&mut c, r0, &x);
    } else {
        rev_tick(&mut c, &mut wk, 0, None);
        eprintln!("RT0PILOT head rev_tick(0) expected T {:.1} (live before {a1})", c.expected_total() - e1);
        let rr = lr_walk_restore(&mut c, wk.r);
        let e2 = c.expected_total();
        let r0 = unseed_r1(&mut c, rr);
        eprintln!("RT0PILOT head unseed_r1 expected T {:.1}", c.expected_total() - e2);
        unseed_half_tail(&mut c, r0, &x);
    }
    T0_PLAIN.with(|q| q.set(false));
    c.free_vec(&idle);
    c.declare_qubit_register(&x);
    let peak = c.peak_total();
    let ops = c.take_ops();
    let (nq, nb, _, regs) = analyze_ops(ops.iter());
    let mut h = sha3::Shake256::default();
    h.update(b"rt0-pilot");
    let mut xof = h.finalize_xof();
    let mut sim = Simulator::new(nq as usize, nb as usize, &mut xof);
    let mut seed = 0x9e37_79b9_7f4a_7c15u64 ^ std::env::var("RT0_SEED").ok().and_then(|v| v.parse::<u64>().ok()).unwrap_or(0);
    let mut rnd = move || {
        let mut v = U256::ZERO;
        for i in 0..4 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            v |= U256::from(seed) << (64 * i);
        }
        v
    };
    let (mut bad, mut phb, mut anc, mut shots) = (0usize, 0usize, 0usize, 0usize);
    for _ in 0..batches {
        sim.clear_for_shot();
        let mut ins = Vec::new();
        for shot in 0..64 {
            let xv = rnd().reduce_mod(p).max(U256::from(1u8));
            sim.set_register(&regs[0], xv, shot);
            ins.push(xv);
        }
        sim.apply_iter(ops.iter());
        for (shot, xv) in ins.iter().enumerate() {
            if sim.get_register(&regs[0], shot) != *xv {
                bad += 1;
            }
            if (sim.phase >> shot) & 1 == 1 {
                phb += 1;
            }
        }
        for r in &regs {
            for qb in r {
                if let QubitOrBit::Qubit(q) = *qb {
                    *sim.qubit_mut(q) = 0;
                }
            }
        }
        if (0..nq).any(|q| sim.qubit(QubitId(q)) != 0) {
            anc += 1;
        }
        shots += 64;
    }
    eprintln!(
        "RT0PILOT {}: shots={shots} wrong={bad} phase_bad={phb} ancilla_bad_batches={anc} avgT={:.1} peak={peak} qubits={nq}",
        if rt0 { format!("SL_RT0={}", y15::sl_rt0()) } else { "head".to_string() },
        sim.stats.toffoli_gates as f64 / shots as f64
    );
}
