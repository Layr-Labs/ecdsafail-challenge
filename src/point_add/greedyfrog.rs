//! greedyfrog: the uniform greedy Euclid traversal circuit. Reference: `greedyfrog_model.rs` (layout, slot order, decode).
//!
//! Registers: rings X (target) and Y (source), W lanes each; bit lengths LA, LB (9 bits); DONE counter cnt (8 bits);
//! swap parity par. Every slot is uniform. The forward slot X-measures its decisions (d, r, sw); the inverse slot
//! recomputes them from the post-state (sw and r from the cofactor windows, d from the wrapped lane 0) and repairs
//! their phases.
//!
//! Masked ladders (mask.rs) get their running-mask toggle from a counter whose bits are XORed with the DONE flag z0
//! while the ladder runs: a finished shot then shows 510/511, which matches no lane, so its mask stays off.

use super::arith::{and_dirty, inc_dirty};
use super::builder::B;
use super::mask::{mdown, mup, top_carry, Lad, Mscr, RollRec, Src, ALWAYS};
use super::greedyfrog_model::{CW, MARKER_FREE, W};
use crate::circuit::{BitId, QubitId};

pub const LB_BITS: usize = 9;
pub const CNT_BITS: usize = 8;
pub const R_BITS: usize = 5;
/// bits of a slot's renormalisation rotation rho <= RCAP = 7 (3-stage barrel)
pub const RHO_BITS: usize = 3;
/// lanes of the top-window compares (F2, F9): exact unless the two values agree on all of them. Q825 LS-2: 28 -> 23
/// (paired emulator, 12.8M walks: +0.10 Lambda on NSLOTS 255; a Lambda-neutral swap with the NSLOTS 255 buy)
pub const WC: usize = 23;
/// Q825 LS-2 dev knob: `LS2_WC` overrides WC (inert when unset; the emulator follows it).
pub fn wc() -> usize { super::ftport::modp_ft::ls2k("WC", WC) }
/// lanes added on each side of the measured per-slot envelopes
pub const MARGIN: usize = 2;
/// slots per traversal: steps plus stall slots (200k walks: 8 need >= 257, 4 need 258). Q825 LS-2: 254 -> 255, the
/// buy side of the width market (-0.83 Lambda for +11.1k T)
pub const NSLOTS: usize = 255;
/// borrowed lanes the gate tests hand a slot (random contents, checked restored); the shell lends its 256-lane passenger
pub const TEST_DIRTY: usize = 24;

// ------------------------------------------------------------------ Q825 walk-lane levers (B-WALKLANES)
/// SMALL-01 KT-HOST: while the inverse slot's rows window runs, LB holds kt = mY - mX in 0..31 on every decodable
/// shot, so LB[5..9) are |0> and join the rows' carry pools (both passes). Without `SY_ACT_GATE` finished shots hold
/// kt = sX - 1 - sY in [-8, 30] there: LB[5..8) are then cleared by CX from the sign LB[8], and LB[8] itself is hosted
/// only on act-constant slots.
pub const LB_HOST: bool = true;
/// Gate Y's bottom normalisation in the inverse slot by act: finished shots keep sY = 0 (their Y lanes 0..8 hold
/// the DONE counter, whose trailing ones would otherwise read as slack).
pub const SY_ACT_GATE: bool = true;
/// SMALL-02 sY cut: after the decode's un-swap sY <= 1 (B tA' > p/2 on every correctly decoded active shot, sY = 0 on
/// finished shots with `SY_ACT_GATE`), so sY[1..5) are |0> through the rows window and join the rows' carry pools.
pub const SY_HOST: bool = true;
/// Hosting realisation: false lends the hosted lanes to the two rows pools only; true frees them to the builder for
/// the whole rows window (every room() decision there sees them: rows pools, park, chains) and re-binds fresh |0>
/// lanes at the window's end.
pub const HOST_FREE: bool = true;
/// SMALL-15 realisation (RT-IDLE): on plain-row slots the sweep's g and jl (6 lanes) are |0> while either rows pass
/// runs (jl is written by the sweep after the rows and erased before the inverse rows): lend them to both rows pools.
pub const RT_IDLE_HOST: bool = true;
/// SMALL-03 (Y-TOP): Y[W-1] is B's leading 1 on every shot through the rows window (the source is normalised; on
/// finished shots B = 1): flipped to |0> it joins both rows pools.
pub const YTOP_HOST: bool = true;
/// With the 1-bit sY (SY_HOST + HOST_FREE): jl <- sX - sY - jl as one adder, ~jl + sX + !sY0 (sY0 folded into the
/// carry-in lane g), and its inverse is the same map; drops the two sY adds and their transient pad lanes.
pub const SY_FOLD_CIN: bool = true;
/// Junk-parking reserve (lanes of room kept beside the zn parked lanes): the receiver's 17 = RowTmp 9 + r 3 + a1 1 +
/// the sweep's chain 4. The chain is freed before r and a1 are taken and every later chain is room-checked, so the
/// unconditional need is RowTmp 9 + max(chain 4, r + a1 4) = 13 (once the sY adds take no pad lanes).
pub const PARK_RESERVE: usize = 13;
/// SMALL-04 (Fingerimpo, part 1): the value and cofactor ladders run only mid passes (mup_mid / mdown_mid), which never
/// call the end-of-pass comparators, so their 8-lane comparator chain is never read: allocate the ladders' mask
/// scratch without it (8 more lanes of room in the value/cof sections).
pub const LADDER_NO_CHAIN: bool = true;
/// SMALL-04 (part 2): the cofactor chain's lane-0 source x0 = X[0] & !d needs no lane: in the forward X[0] is 0
/// where d = 1 (F4's borrow cleared A's wrapped MSB), so x0 = X[0]; in the inverse X[0] is A's MSB = 1 where d = 1,
/// so x0 = X[0] ^ d, applied in place by a CX.
pub const LANE0_DIRECT: bool = true;
/// REC-I construction (DIV-TOP): the divisor cofactor's bit length is bounded by construction, mX = bl(tB) <=
/// 257 - LA_pre (A tB < p), and every non-failing step has LA_pre - d >= the slot's LA - d window floor (the forward's
/// cofactor-chain mask), stalls inheriting the last step's tB; so mX <= dtop = 257 - min over earlier slots of that
/// floor. Parked slots read divisor lanes >= dtop as zero and park only lanes [mx, dtop): zn = dtop - mx, so the
/// earliest masked slots (short cofactors) can park.
pub const DIV_TOP_BOUND: bool = true;
/// LA-HOST: on masked-row slots whose divisor bound 257 - (LA - d floor) is <= NB + 32, LA holds u' = NB - mX in
/// -32..NB through the rows window, so LA[5..8) are copies of the sign LA[8] (|0> outright when the bound is <= NB);
/// the masks read LA[0..5) and the sign only. CX-cleared from the sign, freed with HOST_FREE, re-bound and restored
/// before the UOFF offset is undone.
pub const LA_HOST: bool = true;
/// SWEEP-UNARY (UI-SWEEP): the last-row sweep's g_j = act & [kt >= j] is stepped by a unary iteration over kt5 (the
/// retained-prefix one-hot decoder of mask.rs, ~1 T per row) instead of an act & [kt == j] AND chain per row (4-5 T).
/// Needs 5 clean lanes (decoder prefix 4 + the y AND's 1); falls back to the chain sweep otherwise.
pub const SWEEP_UNARY: bool = true;
/// PARK-EDGE: park junk lanes from w.mx - 1 instead of w.mx (the window's floor, mx_min - MARGIN of 200k walks).
/// A parked window with mX < floor keeps junk in lanes [mX, floor) and decodes wrong. The receiver's masked rows run
/// rows j >= NB + 1 - w.mx plain, which read divisor lanes <= w.mx - 2, so they fail only for mX <= w.mx - 2 (the
/// emulator models that); a floor of w.mx made parked slots fail one lane earlier, at mX = w.mx - 1, unseen by the
/// emulator. Eval shot 1639 at nonce 233 (division 2, forward slot 19: mX 5, w.mx 6) hit exactly that. With floor
/// w.mx - 1 a parked slot fails only where the masked rows already do (the emulator flags mX < floor as well).
/// (A floor of 0, fully exact, costs +97k T: most slots stop parking.)
pub const PARK_LO_ZERO: bool = true;

// ------------------------------------------------------------------ Q825 walk lane 2 (B-WALK2): exact Toffoli cuts
/// WRITE-GATE-OFF-MASKED-LANES (route c2 of pass3/WK19.md, ported as specified there): the value / cofactor ladders'
/// masked cells write with no gate (`ALWAYS`, one Toffoli less per masked lane per return pass); the ordinary lanes keep
/// the a1 gate. Stalled shots (act & !a1) get bit 8 of the window register flipped (`mark_stall`, 2 CX), finished
/// shots keep the receiver's done mark, so no a1 = 0 shot turns its running mask on inside a window (a stall has LA <= 249
/// after the full renormalisation that precedes it). Slot 0 has a1 = 1 on every shot (`Win::a1_const`): every lane is
/// ungated there; fully masked value ladders (lb.0 <= 1) also drop the gate on the top carry (c0 = 0 reaches it).
pub const MASKED_WRITE_ALWAYS: bool = true;
/// SMALL-LADDER-POOLED: the 9-bit length-register adders, subtracters, constant adders and the [LA < LB] compare run
/// as logical-AND carry ladders on clean lanes, erased by measurement (n - 1 Toffoli for an n-bit add instead of the
/// Cuccaro 2n - 2, no pad lanes; compare n instead of 2n). Room-checked: Cuccaro where the cap leaves no room.
pub const SMALL_POOLED: bool = true;
/// SWEEP-OR-LANES: the inverse sweep keeps the prefix OR F_j = OR_{i >= j} (q_i & g_i) on clean lanes: forward
/// F_j = F_(j+1) | (!lane & g) (2 Toffoli), jl ^= j (F_j ^ F_(j+1)) by CX, no per-row erase; the backward pass erases
/// F_j by measurement (a CCZ repair, 0.5 Toffoli). Rows beyond the lanes the cap leaves (after the r / a1 section and
/// the backward chain) keep the old row, seeded with f = F_J.
pub const SWEEP_OR_LANES: bool = true;
/// SWEEP-EQ-LANE-LITERAL: in the old sweep row, [jl == j] (j >= 1) already implies the row fired (jl starts |0> and
/// only a firing row sets it, rows visited in descending order), so the erase / backward AND drops the lane literal.
pub const SWEEP_EQ_LIT: bool = true;
/// RHO-ANF: r = act & rho(jl), rho(j) = (j + #{8, 15, 22, 29 <= j}) mod 8, built from its algebraic normal form
/// (5 linear + 9 nonlinear monomials, shared AND chains, measured uncompute) instead of four compare/increment passes.
pub const RHO_ANF: bool = true;

// ------------------------------------------------------------------ Q825 B-LANES2
/// PARK-SPLIT: on a masked-row inverse slot the parked junk z is needed only while a rows pass runs (the sweep, r / a1
/// and the backward sweep read Y, s0, LB and the row temporaries, never X or z). The slot parks, runs the rows,
/// unparks, runs the sweep section with the zn lanes free (the sweep's g / jl are taken only then), reparks and runs the
/// undo rows, then unparks. Live beside z: s0, f, y (+ the pool) in the rows, plus r, a1 in the undo rows, i.e. zn + 7
/// instead of zn + 13, so the masked slots 10-16 park fully at cap 825; the repark / final unpark run a 4-lane decoder
/// (`park_slim`) where the room leaves less than the 6 lanes of `park_junk`. Exact; same failure predicate as the
/// receiver's masked rows (park floor w.mx - 1, unchanged).
pub const PARK_SPLIT: bool = true;
/// Split a slot that would park without it too when its sweep then has fewer than this many clean lanes (room_park -
/// zn - 9): below it the backward sweep runs on borrowed lanes (~1.0k T) against two extra park passes (~70 T).
pub const SPLIT_SWEEP_MIN: usize = 12;
/// NORM-STAGE0: the decode prep normalises the TARGET ring by the funnel's stage 0 only. On a decodable shot the target's
/// slack after the un-swap is <= 1 (SMALL-02, by construction), so a pre-swap ring with slack >= 2 is the divisor:
/// c_r = [ring lanes 0, 1 zero], a_r = [slack == 1] (2-literal ANDs). Both rings take only the stage-0 shift by a_r (28
/// cswaps, the exact normalisation of any ring with slack <= 1); sw = c_y, or the receiver's rule on those rings where
/// neither c is set; after the un-swap the 5-stage funnel runs on X alone. Per inverse slot 2 x (166 - 28 - 28) cswaps
/// fewer plus the target's funnel tests; ring layouts at the rows window identical to the receiver's. Exact: a shot with
/// both slacks >= 2 already fails the SY-HOST predicate (sY > 1).
pub const NORM_STAGE0: bool = true;
fn norm_stage0() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("NORM_STAGE0", NORM_STAGE0));
    *E
}
// ------------------------------------------------------------------ Q825 B-FUNNEL
/// FUNNEL-REV (variant A): `norm_bottom` / `denorm_bottom` shift the window down by s with a telescope of six controlled
/// PREFIX REVERSALS instead of the 5-stage cswap funnel. Rev(c) swaps lanes (i, c - i), i < c - i; with
/// c_j = NB - 1 + 2^j - 1 (58, 42, 34, 30, 28, 27) the steps run under s4, s3^s4, s2^s3, s1^s2, s0^s1, s0. Two
/// consecutive active reversals shift lanes <= the smaller prefix down by the difference; the active set telescopes to a
/// down-shift by s on lanes 0..NB-1 (the promise: lanes 0..s-1 are zero). Lanes >= NB are left in a permuted order,
/// which is free: the decode reads lanes 0..NB-1 only and denorm is the literal inverse. The tests are the funnel's own
/// (s_(j-1) = AND(lanes 0..2^(j-1)-1), same lanes, same T) in the funnel's frame: before each test the first 2^(j-1)
/// pairs are swapped under the known s_j, after it under s_(j-1) (net s_j ^ s_(j-1)). 125 cswaps per call instead of
/// 166; width unchanged (same live bits at every test). Exact (pass3/FUNNEL.md, rotcc/revfunnel.py + revtests.py).
pub const FUNNEL_REV: bool = true;
fn funnel_rev() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("FUNNEL_REV", FUNNEL_REV));
    *E
}
/// Negative controls for the gate tests only (FUNNEL_BREAK=k): 1 drops the last reversal Rev(c_0) (control s_0) in norm
/// AND denorm (round trip intact, odd-s windows wrong), 2 drops it in denorm only (s / ring not restored).
fn funnel_break(k: u32) -> bool {
    cfg!(test) && std::env::var("FUNNEL_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
fn park_split() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("PARK_SPLIT", PARK_SPLIT));
    *E
}
fn split_sweep_min() -> usize {
    static E: std::sync::LazyLock<usize> = std::sync::LazyLock::new(|| {
        std::env::var("WL_SPLIT_MIN").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(SPLIT_SWEEP_MIN)
    });
    *E
}
/// dev knob: force the 4-lane decoder on every split repark / unpark (WL_SLIM_ALL=1, gate tests of park_slim)
fn slim_all() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("WL_SLIM_ALL").is_some());
    *E
}

/// Dev override of a lever constant (`WL_<NAME>=0|1`); the official build runs with an empty environment, where the
/// constant applies.
fn lever(name: &str, dflt: bool) -> bool {
    match std::env::var(format!("WL_{name}")) {
        Ok(v) => v.trim() == "1",
        Err(_) => dflt,
    }
}
static LEVERS: std::sync::LazyLock<[bool; 13]> = std::sync::LazyLock::new(|| {
    [lever("LB_HOST", LB_HOST), lever("SY_ACT_GATE", SY_ACT_GATE), lever("SY_HOST", SY_HOST), lever("HOST_FREE", HOST_FREE),
     lever("RT_IDLE_HOST", RT_IDLE_HOST), lever("YTOP_HOST", YTOP_HOST), lever("SY_FOLD_CIN", SY_FOLD_CIN),
     lever("LADDER_NO_CHAIN", LADDER_NO_CHAIN), lever("LANE0_DIRECT", LANE0_DIRECT), lever("DIV_TOP_BOUND", DIV_TOP_BOUND),
     lever("LA_HOST", LA_HOST), lever("SWEEP_UNARY", SWEEP_UNARY), lever("PARK_LO_ZERO", PARK_LO_ZERO)]
});
pub(crate) fn lb_host() -> bool { LEVERS[0] }
pub(crate) fn sy_act_gate() -> bool { LEVERS[1] }
pub(crate) fn sy_host() -> bool { LEVERS[2] }
pub(crate) fn host_free() -> bool { LEVERS[3] }
pub(crate) fn rt_idle_host() -> bool { LEVERS[4] }
pub(crate) fn ytop_host() -> bool { LEVERS[5] }
pub(crate) fn sy_fold_cin() -> bool { LEVERS[6] }
pub(crate) fn ladder_no_chain() -> bool { LEVERS[7] }
pub(crate) fn lane0_direct() -> bool { LEVERS[8] }
pub(crate) fn div_top_bound() -> bool { LEVERS[9] }
pub(crate) fn la_host() -> bool { LEVERS[10] }
pub(crate) fn sweep_unary() -> bool { LEVERS[11] }
pub(crate) fn park_lo_zero() -> bool { LEVERS[12] }
static LEVERS2: std::sync::LazyLock<[bool; 5]> = std::sync::LazyLock::new(|| {
    [lever("MASKED_WRITE_ALWAYS", MASKED_WRITE_ALWAYS), lever("SMALL_POOLED", SMALL_POOLED), lever("SWEEP_OR_LANES", SWEEP_OR_LANES),
     lever("SWEEP_EQ_LIT", SWEEP_EQ_LIT), lever("RHO_ANF", RHO_ANF)]
});
/// B-CRUMBS (Q825) exact cuts, each behind its constant (dev override `WL_<NAME>=0|1`).
/// SWF-LEX: the swap rule lt | eq & c ([LA < LB] or [LA == LB] and a top-window compare bit c) is one lexicographic
/// compare (LA:low) < (LB:high), i.e. the carry out of ~LA + LB + c: the 9-bit compare takes c as its quantum carry-in,
/// and the [LA == LB] test, its measured erase and the two OR/AND temporaries go (forward F9, its I5 erase, decode I2).
pub const SWF_LEX: bool = true;
/// BIGLB-SPLIT: big = [WC < LB < 257] = !LB8 & [LB[0..8] >= 29] ^ LB8 & [LB[0..8] == 0] (two exclusive terms, one 8-bit
/// comparator and one 9-literal AND, the comparator erased by measurement), and big's own erase by measurement
/// (phase repair) instead of a second coherent pass of two 9-bit comparators.
pub const BIGLB_SPLIT: bool = true;
/// UNREN-COND: unrenorm_top's phase repair (-1)^(m . r(x)) builds only the prefix chain its receipts need, inside
/// classical blocks m0 (chain to p5), !m0 & m1 (to p4), !m0 & !m1 & m2 (to p2); the last prefix of each block is a CZ.
pub const UNREN_COND: bool = true;
/// Z0-MEAS: the inverse slot's I1 temporaries [LA == 0] and [c == 0] are erased by measurement (phase repair) instead
/// of being recomputed.
pub const Z0_MEAS: bool = true;
/// TERM-NC (TERMINAL-CARRY SKIP): ladders whose top carry nobody reads (division rows, cofactor chains) skip the last
/// lane's carry cell; the down pass writes that lane's sum only (mask.rs `mup_mid_nc` / `mdown_mid*_nc`).
pub const TERM_NC: bool = true;
/// FWD-ACT-CONST (ST-001): forward slots with `Win::act_const` (no shot can have finished; the inverse already takes
/// act = 1 classically there) skip the done flag z0, its counter increment and its measured erase.
pub const FWD_ACT_CONST: bool = true;
/// SWEEP-ACT-ROOT (ST-003): on act-live slots the unary sweep's one-hot decoder over kt5 takes act as its root literal
/// (value j + 32 on the 6-bit view (kt5, act)), so each row's g ^= act & o is a CX; one more prefix lane, taken only
/// where the cap leaves room for it.
pub const SWEEP_ACT_ROOT: bool = true;
/// Lanes SWEEP-ACT-ROOT leaves free beside its extra prefix lane (the forward sweep's rows then still find their
/// OR-row temporary and measured-erase chains; the backward sweep, at room 1 on act-live slots, keeps the old decoder).
/// Raw static on final-l2: spare 1 / 2 / 3 / 4 = -3,692 / -3,648 / -3,628 / -160; spare 0 overruns the cap (826).
const ACT_ROOT_SPARE: usize = 2;
/// Dev override `WL_ACT_ROOT_SPARE=n` (empty environment: the constant).
fn act_root_spare() -> usize {
    std::env::var("WL_ACT_ROOT_SPARE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(if root_or() { 0 } else { ACT_ROOT_SPARE })
}
// ------------------------------------------------------------------ Q825 LEVER-AUDIT (coverage extensions)
/// OR-CCZ (SWEEP-OR-LANES coverage): the backward OR row's 3-literal measured-erase repair (-1)^(F_(j+1) !lane g) is one
/// native CCZ (the same Toffoli count as the AND + CZ it replaces) and needs no ancilla, so the backward sweep starts
/// without a repair lane and the OR-lane reserve drops by one: one more OR row (instead of a chain row) per slot.
pub const OR_CCZ: bool = true;
/// SWEEP-ACT-ROOT coverage: on act-live inverse slots keep this many more lanes out of the OR lanes, so the BACKWARD
/// unary sweep finds room for its act root lane too (before: forward only; the backward ran at room 1 on every act-live
/// slot). With OR-CCZ the act-live reserve is then the old 9.
pub const OR_RES_ACT: usize = 1;
/// Lanes the backward unary sweep leaves free beside its SWEEP-ACT-ROOT prefix lane (its OR rows need none with OR-CCZ;
/// its chain rows take their AND lanes after the OR lanes are freed).
const ACT_ROOT_SPARE_BWD: usize = 0;
fn or_ccz() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("OR_CCZ", OR_CCZ));
    *E
}
/// Dev override `WL_OR_RES_ACT=n` (empty environment: the constant).
fn or_res_act() -> usize {
    std::env::var("WL_OR_RES_ACT").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(OR_RES_ACT)
}
/// Dev override `WL_ACT_ROOT_SPARE_BWD=n` (empty environment: the constant).
fn act_root_spare_bwd() -> usize {
    std::env::var("WL_ACT_ROOT_SPARE_BWD").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(ACT_ROOT_SPARE_BWD)
}
static LEVERS3: std::sync::LazyLock<[bool; 7]> = std::sync::LazyLock::new(|| {
    [lever("SWF_LEX", SWF_LEX), lever("BIGLB_SPLIT", BIGLB_SPLIT), lever("UNREN_COND", UNREN_COND), lever("Z0_MEAS", Z0_MEAS),
     lever("TERM_NC", TERM_NC), lever("FWD_ACT_CONST", FWD_ACT_CONST), lever("SWEEP_ACT_ROOT", SWEEP_ACT_ROOT)]
});
pub(crate) fn sweep_act_root() -> bool { LEVERS3[6] }
pub(crate) fn fwd_act_const() -> bool { LEVERS3[5] }
pub(crate) fn term_nc() -> bool { LEVERS3[4] }
/// Negative controls for the gate tests only (CR_BREAK=k): 1 UNREN-COND drops block 3's CZ, 2 SWF-LEX decode drops the
/// !gt flip, 3 BIGLB-SPLIT drops the [LB >= 257] term, 4 Z0-MEAS skips the [c == 0] erase repair (wrong phase),
/// 5 TERM-NC drops the top lane's carry-in (mask.rs), 6 SWEEP-ACT-ROOT decodes act = 0 instead of act = 1,
/// 7 OR-CCZ drops the backward OR row's CCZ (wrong phase), 8 the backward SWEEP-ACT-ROOT decodes act = 0.
pub(crate) fn cr_break(k: u32) -> bool {
    cfg!(test) && std::env::var("CR_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
pub(crate) fn swf_lex() -> bool { LEVERS3[0] }

// ------------------------------------------------------------------ Q825 B-SWCARRY (R-005a)
/// SW-CARRY: inverse slot s + 1 runs before inverse slot s, and its division rows compute Q = floor(tA' / tB) of the
/// current run, whose popcount is the run's step count. A swap ends a run and the next step starts one, so
/// sw_s = a1_(s+1) & [popcount(Q_(s+1)) == 1]. Q's top set bit is row 0 or row 1, so with the sweep's jl before its
/// in-place transform (the last set row, 0 by default) and row 0's sign lane s0 (= !q_0, live until the undo rows):
/// single = [jl == 0] | [jl == 1] & s0. Inverse slot s + 1 leaves c = a1 & single on a fresh lane (6 T); inverse slot
/// s then skips the whole I2 swap decode: unswap controlled by c, the F9 measured erase of c (unchanged), and the
/// decode prep after the unswap (X: the funnel alone, Y: the a-shift). No carry from PARK-SPLIT slots (a held lane at
/// the split repark costs the peak) or from slot 0; inverse slot 253 has no predecessor. Those keep the standard I2.
/// The denormalisation undoes X by the funnel's inverse on every slot (the standard prep's a-shift + funnel has the
/// funnel's lane map and sX). Exact (greedyfrog_model `greedyfrog_swcarry_single_flag`; the gate tests).
pub const SW_CARRY: bool = true;
pub(crate) fn sw_carry() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("SW_CARRY", SW_CARRY));
    *E
}
/// PARK-SPLIT slots carry only where room_park >= zn + this (dev override `WL_SWC_SPLIT_MIN=n`). Raw static on final-cr:
/// never 3,859,630.75; 9 (= 10) 3,846,354.25; 11 3,846,908.75; 8 (every split slot) 3,842,559.25 at peak 826.
pub const SWC_SPLIT_MIN: usize = 9;
fn swc_split_min() -> usize {
    static E: std::sync::LazyLock<usize> = std::sync::LazyLock::new(|| {
        std::env::var("WL_SWC_SPLIT_MIN").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(SWC_SPLIT_MIN)
    });
    *E
}
/// Negative controls for the gate tests only (SWC_BREAK=k): 1 the carry drops the [jl == 1] & s0 term, 2 it reads
/// q_0 (!s0) in place of s0.
fn swc_break(k: u32) -> bool {
    cfg!(test) && std::env::var("SWC_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
pub(crate) fn biglb_split() -> bool { LEVERS3[1] }
pub(crate) fn unren_cond() -> bool { LEVERS3[2] }
pub(crate) fn z0_meas() -> bool { LEVERS3[3] }
pub(crate) fn masked_write_always() -> bool { LEVERS2[0] }
pub(crate) fn small_pooled() -> bool { LEVERS2[1] }
pub(crate) fn sweep_or_lanes() -> bool { LEVERS2[2] }
pub(crate) fn sweep_eq_lit() -> bool { LEVERS2[3] }
pub(crate) fn rho_anf() -> bool { LEVERS2[4] }
/// B-PORT3 S3-001 K1 banked masked carries (SnehalRaj 29f13bac): a masked ladder's up pass keeps f & s' on an idle
/// clean lane per masked cell; the return pass uses it and erases it by measurement (1 Toffoli per cell instead of 2).
/// Bitmask of sites: 1 top_compare_masked, 4 window_gt (the masked division rows site of 29f13bac is not ported: no
/// masked rows remain at 825, and TERM-NC owns that ladder).
/// Exact by construction (the same carries; the bank is |0> before and after). Dev override `WL_K1=<mask>`.
pub const K1: u32 = 5;
/// B-PORT3 K2: the K1 bank in the value / cofactor passes, on the room their ordinary lanes' carry pool leaves idle
/// (late slots: short ordinary tails). Exact (same carries). Dev override `WL_K2=0|1`.
pub const K2: bool = true;
fn k2() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("K2", K2));
    *E
}
fn k1() -> u32 {
    static E: std::sync::LazyLock<u32> = std::sync::LazyLock::new(|| {
        std::env::var("WL_K1").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(K1)
    });
    *E
}

// ------------------------------------------------------------------ Q825 B-ROLL: ROLL-FWD (R-028)
/// ROLL-FWD, value ladder ordinary lanes: F4 runs as the exact inverse of I10 in ONE upward traversal (mask.rs
/// `roll_fwd`; the froghop S5 rolling prefix): each lane writes first (t ^= a1 (s ^ c)), forms I10's next carry on the
/// updated target in one of two clean lanes (1 AND) and X-measures the spent carry; I10's up pass regenerates the very
/// same carry on an addressable wire (Cuccaro source lane / pooled AND lane / running wire) and repays its phase there
/// (`mup_mid_roll`, a z_if). 2 T per ordinary lane instead of the pooled 2 / Cuccaro 3; no carry pool.
pub const ROLL_VALUE: bool = true;
/// ROLL-FWD, value ladder masked cells too (level 2): tmp = f (s ^ c), t ^= tmp, next = c ^ tmp (t' ^ c), tmp erased
/// by measurement: 2 AND + ONE decoder traversal per masked lane (the up+down pair: 2 AND + 2 CCX + two traversals).
/// The running mask's end value is X-measured and repaid on I10's f after its up pass (exact on every shot).
pub const ROLL_VALUE_MASKED: bool = true;
/// ROLL-FWD, cofactor ladder (F5 as the inverse of I11, TERMINAL-CARRY SKIP kept: the last lane only writes).
pub const ROLL_COF: bool = true;
/// ROLL-FWD, cofactor ladder masked cells too.
pub const ROLL_COF_MASKED: bool = true;
static LEVERS4: std::sync::LazyLock<[bool; 4]> = std::sync::LazyLock::new(|| {
    [lever("ROLL_VALUE", ROLL_VALUE), lever("ROLL_VALUE_MASKED", ROLL_VALUE_MASKED), lever("ROLL_COF", ROLL_COF),
     lever("ROLL_COF_MASKED", ROLL_COF_MASKED)]
});
pub(crate) fn roll_value() -> bool { LEVERS4[0] }
pub(crate) fn roll_value_masked() -> bool { LEVERS4[1] }
pub(crate) fn roll_cof() -> bool { LEVERS4[2] }
pub(crate) fn roll_cof_masked() -> bool { LEVERS4[3] }
/// ROLL-ROWS (R-028 on the division rows): plain rows whose forward pass has Cuccaro lanes (carry pool shorter than the
/// row) run as one rolling upward traversal on two pool lanes (write, carry on the updated remainder, measure the spent
/// carry: 1 T per lane with the ungated rows write); the inverted rows pass (i.rows_rev) regenerates every carry in its
/// inverted down pass and repays it there (`mdown_mid*_roll`). Fully pooled rows (1 T per lane already) are unchanged.
pub const ROLL_ROWS: bool = true;
fn roll_rows() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("ROLL_ROWS", ROLL_ROWS));
    *E
}
/// ROWY-ROLL (INTEGRATOR, ROW-Y x ROLL-ROWS): a ROW-Y row whose pool is shorter than its ladder (n - 1 lanes) rolls in
/// the ROW-Y form: `roll_fwd` over the ladder lanes (carry-in m on c0 or the X-flipped sign lane, two pool lanes rolling,
/// the lent zero source y untouched), the top lane written as t ^= c_L (the `top` hook, before c_L is measured) ^ m; the
/// inverted rows pass repairs every carry in its down pass (`mdown_mid_roll`, no TERMINAL-CARRY SKIP: ROW-Y keeps c_L).
/// ROW-Y keeps the lent y / f; ROLL-ROWS' 1 T per rolled lane applies on the short-pool (parked) rows.
/// Dev override `WL_ROWY_ROLL=0|1`.
pub const ROWY_ROLL: bool = true;
fn rowy_roll() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("ROWY_ROLL", ROWY_ROLL));
    *E
}
/// ROLL-ROWS mode of a `division_rows` call.
enum RowRoll<'a> {
    No,
    /// forward rows pass, run directly (not recorded): collect each row's receipts (empty where not rolled)
    Fwd(&'a mut Vec<RollRec>),
    /// the rows pass that is played inverted: repair with these receipts
    Rev(&'a [RollRec]),
}
/// MICRO-WALK (Q825) exact cuts, each behind its constant (dev override `WL_<NAME>=0|1`).
/// SWF-NZ (M-014): the swap AND drops the !z0 literal: z0 = [LA == 0] & [cnt != 0] at F1, and a finished shot keeps
/// LA == 0 through F5-F8 (d = r = 0), so z0 = 1 implies nz = [LA == 0] = 1 and !nz already excludes it.
pub const SWF_NZ: bool = true;
fn swf_nz() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("SWF_NZ", SWF_NZ)); *E }
/// CNT7 (M-015): the DONE counter's arithmetic (inc, dec, zero tests) runs on lanes 0..7 only: c = slots since the
/// finish <= 254 - 153 = 101 on every shot that passes (a walk finishing before the first act-live slot already fails
/// there), so lane 7 never carries and reads constant (the promise CNT7-PARK already takes).
pub const CNT7: bool = true;
fn cnt7() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("CNT7", CNT7)); *E }
/// TC-PHASE (M-011, TERMINAL-CARRY-CCZ): a phase-only compare (out None, no gate) applies (-1)^(carry out of the top
/// lane) as Z(c) CZ(t ^ c, s ^ c) (ordinary lane, no Toffoli) or Z(c) CCZ(f, t ^ c, s ^ c) (masked lane, one AND)
/// instead of building the top carry cell and its inverse (mask.rs `mid_phase_top`).
pub const TC_PHASE: bool = true;
pub(crate) fn tc_phase() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("TC_PHASE", TC_PHASE)); *E }
/// OFF-KEEP (M-001, ST-005 reworked): under NORM-STAGE0 the decode's offsets LA += sX, LB += sY (one-lane a-shift
/// slacks) are kept through the un-swap instead of being restored after I2 and re-added in I6: the I5 erase of sw (the
/// forward's F9, which reads plain LA / LB) runs before the funnel and takes the offsets off and back inside its
/// measured block (half weight), and the funnel's own slack is added to LA as it is formed (a_X is already there).
pub const OFF_KEEP: bool = true;
fn off_keep() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("OFF_KEEP", OFF_KEEP)); *E }
/// X0-HOST (M-003, S3-005): on act_const slots every shot is active and the funnel has bottom-normalised the divisor
/// ring, so X[0] (the divisor cofactor's MSB) is 1; nothing reads X[0] between the rows pass and the undo rows (sweep,
/// r / a1, backward sweep), so it is flipped to |0> and freed to the room there (the sweep's OR lanes take it).
pub const X0_HOST: bool = true;
fn x0_host() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("X0_HOST", X0_HOST)); *E }
/// Negative controls for the gate tests only (MW_BREAK=k): 1 SWF-NZ also drops the nz literal, 2 CNT7 runs the counter
/// on lanes 1..8, 3 TC-PHASE drops the Z(c) term, 4 OFF-KEEP leaves sY on LB inside the I5 erase, 5 X0-HOST frees
/// X[0] without the flip.
pub(crate) fn mw_break(k: u32) -> bool {
    cfg!(test) && std::env::var("MW_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
/// YTOP-SWEEP (M-005, the s0 sign-loan realised on the window's idle constant lane): Y[W-1] is B's leading 1 on every
/// shot through the rows window (YTOP_HOST lends it, flipped to |0>, to both rows pools). Between the rows pass and the
/// undo rows (unpark, sweep, r / a1, backward sweep, repark) nothing reads it, so instead of flipping it back to 1 it
/// stays |0> and the forward sweep takes it as one more OR lane where that raises n_or (the backward sweep frees it as
/// it erases that row; it is re-acquired by id right after, since Y's lane ids are the caller's). Exact (lane
/// allocation only); negative control MW_BREAK=6 lends it holding 1.
pub const YTOP_SWEEP: bool = true;
fn ytop_sweep() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("YTOP_SWEEP", YTOP_SWEEP)); *E }
/// REPARK-X0 (M-008, repark decoder cliff): on X0-HOST slots X[0] = 1 is a known lane outside the parked window
/// (park_lo >= 1). The PARK-SPLIT repark takes it |0> as a fourth decoder lane before it is flipped back to 1, and the
/// final unpark X-flips it to |0>, takes it as a second decoder lane and flips it back. The final unpark then has the
/// 6 lanes of `park_junk_t`; the repark (room 1) has 5, where `park_mid` runs: `park_junk_t`'s decoder without the
/// retained bit-0 level (prefix over u' bits 1..5, the flag toggled by one CCX on the bit-0 literal) instead of the
/// 4-lane `park_slim`. Exact; negative control MW_BREAK=8 drops park_mid's bit-0 literal.
pub const REPARK_X0: bool = true;
fn repark_x0() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("REPARK_X0", REPARK_X0)); *E }
/// dev knob: run `park_mid` on every split repark / unpark that has its 5 lanes (WL_MID_ALL=1, gate tests of park_mid)
fn mid_all() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("WL_MID_ALL").is_some());
    *E
}
/// ROOT-OR (M-010, per-slot variant search): on act-live slots the forward sweep takes one OR lane fewer, so
/// SWEEP-ACT-ROOT's extra prefix lane fits with one spare lane (ACT_ROOT_SPARE 1) on both sweeps. Searched per slot
/// over OR reserves 0..3 x spares 0..2 (GF_SLOTT): reserve 1 / spare 1 is the cheapest on every slot. Exact (lane
/// allocation only). Dev override `WL_ROOT_OR=0|1`; `WL_NOR_RES=n` overrides the reserve.
/// INTEGRATOR re-scan on final-p3 (B-PORT3's ROW_Y / ROW_F / EARLY_GHOST lanes): reserve 0 / spare 0 now fits at 825
/// and is the cheapest of reserve 0..3 x spare 0..2 (-1,040 below 1 / 1), so ROOT-OR is ACT_ROOT_SPARE 0, no reserve.
pub const ROOT_OR: bool = true;
fn root_or() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("ROOT_OR", ROOT_OR)); *E }
fn nor_res_live() -> usize {
    static E: std::sync::LazyLock<usize> = std::sync::LazyLock::new(|| {
        std::env::var("WL_NOR_RES").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0)
    });
    *E
}
/// Lowest window lane parking covers.
fn park_lo(w: &Win) -> usize {
    if park_lo_zero() { w.mx.saturating_sub(1) } else { w.mx }
}
/// B-EXPLORE PARTIAL-PARK: a masked-row slot without room to park its whole junk window [park_lo, top) parks the top
/// zp lanes [top - zp, top) (zp = room - PARTIAL_RESERVE, the masked RowTmp 10 + r, a1 / sweep chain 4) and keeps the
/// running mask only over the divisor lanes below them: those lanes' ladder cells are ordinary (zero-padded on every
/// shot whose divisor is shorter, the arithmetic of a masked-off cell) and use the rows' carry pool. Exact; the failure
/// predicate is the masked rows' own (mX < park_lo).
pub const PARTIAL_PARK: bool = true;
pub const PARTIAL_RESERVE: usize = 18;
fn partial_park() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| match std::env::var("WL_PARTIAL_PARK") {
        Ok(v) => v.trim() == "1",
        Err(_) => PARTIAL_PARK,
    });
    *E
}
fn partial_reserve() -> usize {
    static E: std::sync::LazyLock<usize> = std::sync::LazyLock::new(|| {
        std::env::var("WL_PARTIAL_RESERVE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(PARTIAL_RESERVE)
    });
    *E
}
fn park_reserve() -> usize {
    static E: std::sync::LazyLock<usize> = std::sync::LazyLock::new(|| {
        std::env::var("WL_PARK_RESERVE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(PARK_RESERVE)
    });
    *E
}
/// dev pricing knob: park every masked slot regardless of room (WL_FORCE_PARK=1; breaks the peak)
fn force_park() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("WL_FORCE_PARK").is_some());
    *E
}
/// dev pricing knob: extra cap inside the rows pools only (WL_EXTRA_ROWS=k; breaks the peak, never in a submission)
fn extra_rows() -> u64 {
    static E: std::sync::LazyLock<u64> = std::sync::LazyLock::new(|| {
        std::env::var("WL_EXTRA_ROWS").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0)
    });
    *E
}
/// dev pricing knob (M3): WL_PSP_GIVE=k lets the PARK-SPLIT repark / unpark decide as if k more lanes were free (the
/// 6-lane decoder then runs over the cap: breaks the peak, never in a submission)
fn psp_give() -> usize {
    static E: std::sync::LazyLock<usize> = std::sync::LazyLock::new(|| {
        std::env::var("WL_PSP_GIVE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0)
    });
    *E
}
/// dev instrument: WL_ROWLOG=1 prints one line per inverse slot at the rows window
fn rowlog() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("WL_ROWLOG").is_some());
    *E
}

thread_local! {
    /// test probe: (op index, lanes that must be |0> on every shot there)
    static ZERO_PROBES: std::cell::RefCell<Vec<(usize, Vec<QubitId>)>> = std::cell::RefCell::new(vec![]);
}
/// Record that `lanes` are |0> on every shot at the current stream position (checked by the gate tests).
fn zero_probe(b: &B, lanes: &[QubitId]) {
    if cfg!(test) && !lanes.is_empty() {
        ZERO_PROBES.with(|p| p.borrow_mut().push((b.ops.len(), lanes.to_vec())));
    }
}
/// Take the recorded probes (tests).
pub fn take_zero_probes() -> Vec<(usize, Vec<QubitId>)> {
    ZERO_PROBES.with(|p| std::mem::take(&mut *p.borrow_mut()))
}

/// Classical per-slot windows of the active shots' data-dependent boundaries (greedyfrog_data/env.txt plus MARGIN). Lanes
/// on the far side of a window are classically on or off, so only the window's lanes pay for the running mask.
#[derive(Clone, Debug)]
pub struct Win {
    /// LB range (value chain mask, top compares)
    pub lb: (usize, usize),
    /// LA - d range (cofactor chain mask)
    pub lad: (usize, usize),
    /// lower bound of the bit length of X's cofactor in the post-state, before / after the decode's un-swap
    pub mxp: usize,
    pub mx: usize,
    /// division rows
    pub k: usize,
    /// no shot can have finished by this slot (the envelope's walks all run 40+ slots longer), so act = 1 classically
    pub act_const: bool,
    /// bound on the divisor cofactor's bit length after the decode's un-swap (DIV_TOP_BOUND), at most NB
    pub dtop: usize,
    /// the unclipped bound is <= NB (mX <= NB on every non-failing shot)
    pub dtop_tight: bool,
    /// the unclipped bound is <= NB + 32 (u' = NB - mX >= -32)
    pub dtop_near: bool,
    /// a1 = 1 on every shot (slot 0: LA = 256, X[W-1] = p's MSB)
    pub a1_const: bool,
    /// MARKER_FREE: the renorm prefixes p_i with i >= la_gmin are gated by [LA > i] (7: no gate). Overshoot needs A' = 0,
    /// i.e. a finishing step (LB = 1) at some slot s - k with LA - d = LA_0 and LA_0 - 7k <= 6 at this slot
    pub la_gmin: usize,
    /// MARKER_FREE: LA < 2^la_hb at this slot's renormalisation on every non-failing shot ([LA >= 8] reads LA[3..la_hb))
    pub la_hb: usize,
}

impl Win {
    /// No classical knowledge: every boundary anywhere (masks everywhere, all rows).
    pub fn full() -> Win {
        Win { lb: (1, 256), lad: (0, 256), mxp: 0, mx: 0, k: KROWS, act_const: false, dtop: NB, dtop_tight: false, dtop_near: false, a1_const: false,
              la_gmin: if MARKER_FREE { 1 } else { 7 }, la_hb: LB_BITS }
    }
}

/// slots between the last act-constant slot and the first slot where an envelope walk finished
/// Q825 LS-2: 40 -> 4 (1.28e9-walk tail: the earliest finish is slot 174)
const ACT_MARGIN: usize = 4;

/// walks behind greedyfrog_data/env.txt
const ENV_WALKS: f64 = 200_000.0;

/// B-EXPLORE (ENV-TABLE): use the explicit per-slot window table `greedyfrog_data/win_table.txt` (lines
/// `s lb_lo lb_hi lad_lo lad_hi mxp mx`, margins included) instead of the 200k-walk envelope + MARGIN for the LB, LA-d,
/// mxp and mx windows. Rows k and act_const still come from env.txt.
pub const WIN_TABLE: bool = true;

/// The traversal's windows, slot by slot. Dev only: `GF_WIN=<file>` overrides the table (inert when unset).
pub fn windows() -> Vec<Win> {
    if let Ok(p) = std::env::var("GF_WIN") {
        if p != "base" {
            return windows_with(Some(&std::fs::read_to_string(&p).expect("GF_WIN table")));
        }
        return windows_with(None);
    }
    windows_with(if WIN_TABLE { Some(include_str!("greedyfrog_data/win_table.txt")) } else { None })
}

/// Windows from env.txt + MARGIN, with the LB / LA-d / mxp / mx windows replaced per slot by `ovr` when given.
pub fn windows_with(ovr: Option<&str>) -> Vec<Win> {
    let (mut first_done, mut all_active_upto) = (usize::MAX, 0usize);
    let txt = include_str!("greedyfrog_data/env.txt");
    let mut v = vec![];
    for line in txt.lines().filter(|l| !l.starts_with('#')) {
        let c: Vec<isize> = line.split_whitespace().map(|t| t.parse().unwrap()).collect();
        // s n lb_min lb_max lad_min lad_max cof_min r_max mxp_min mx_min kt_max rows_max slack_max
        let m = MARGIN as isize;
        let lb = ((c[2] - m).max(1) as usize, (c[3] + m).min(256) as usize);
        let lad = ((c[4] - m).max(0) as usize, (c[5] + m).min(256) as usize);
        let mxp = (c[8] - m).max(0) as usize;
        let mx = (c[9] - m).max(0) as usize;
        // rows: the big-quotient tail (P(rows > k) ~ 2^-k per step) is the same at every slot, so a slot holding a
        // fraction f of the shots active keeps the run's expected failures flat with k = KROWS - floor(log2(1/f));
        // slot 0's quotient is a single power of two
        let f = c[1] as f64 / ENV_WALKS;
        let k = if c[0] == 0 { 4 } else { (KROWS as f64 - (1.0 / f).log2().floor()).clamp(8.0, KROWS as f64) as usize };
        v.push(Win { lb, lad, mxp, mx, k, act_const: false, dtop: NB, dtop_tight: false, dtop_near: false, a1_const: false,
                     la_gmin: 7, la_hb: LB_BITS });
        if c[1] as f64 == ENV_WALKS {
            all_active_upto = c[0] as usize;
        } else {
            first_done = first_done.min(c[0] as usize);
        }
    }
    while v.len() < NSLOTS {
        v.push(v.last().unwrap().clone());
    }
    let _ = all_active_upto;
    if let Some(t) = ovr {
        for line in t.lines().filter(|l| !l.trim().is_empty() && !l.starts_with('#')) {
            let c: Vec<usize> = line.split_whitespace().map(|t| t.parse().unwrap()).collect();
            if c[0] < v.len() {
                let w = &mut v[c[0]];
                w.lb = (c[1].max(1), c[2].min(256));
                w.lad = (c[3], c[4].min(256));
                w.mxp = c[5];
                w.mx = c[6];
                // LS-1: optional 8th column = this slot's division rows k (default: the KROWS rule above)
                if let Some(&k) = c.get(7) {
                    w.k = k;
                }
            }
        }
    }
    let mut lad_floor = usize::MAX;
    for (s, w) in v.iter_mut().enumerate() {
        w.act_const = s + super::ftport::modp_ft::ls2k("ACT_MARGIN", ACT_MARGIN) < first_done;
        w.a1_const = s == 0;
        lad_floor = lad_floor.min(w.lad.0);
        w.dtop = CW.saturating_sub(lad_floor).min(NB);
        w.dtop_tight = CW.saturating_sub(lad_floor) <= NB;
        w.dtop_near = CW.saturating_sub(lad_floor) <= NB + 32;
    }
    v.truncate(NSLOTS);
    if MARKER_FREE {
        // LA gate: a shot can overshoot at slot s only if a finishing step (LB = 1 inside the lb window) at s - k had
        // LA - d = LA_0 (inside the lad window) with LA_0 - 7k <= 6 (the step itself, k = 0, or its last stall); any other
        // shot fails the base's own window predicate. la_hb from the largest LA at the renorm (steps: lad.1; stalls
        // following a step at s - k: lad.1(s - k) - 7k).
        let n = v.len();
        for s in 0..n {
            let (mut gmin, mut lamax) = (7usize, 0isize);
            for k in 0..=s {
                let w0 = &v[s - k];
                let (lo, hi) = (w0.lad.0 as isize, w0.lad.1 as isize);
                if w0.lb.0 <= 1 && lo <= 7 * k as isize + 6 {
                    gmin = gmin.min((lo - 7 * k as isize).max(1) as usize);
                }
                lamax = lamax.max(hi - 7 * k as isize);
            }
            let hb = (usize::BITS - (lamax.max(0) as usize).leading_zeros()) as usize;
            v[s].la_gmin = gmin;
            v[s].la_hb = hb.clamp(3, LB_BITS);
        }
        if std::env::var_os("MF_WINLOG").is_some() {
            for (s, w) in v.iter().enumerate() {
                if w.la_gmin < 7 { eprintln!("MF_WIN slot {s} gmin {} hb {}", w.la_gmin, w.la_hb); }
            }
        }
    }
    v
}

#[derive(Clone)]
pub struct GreedyFrog {
    pub x: Vec<QubitId>,
    pub y: Vec<QubitId>,
    pub la: Vec<QubitId>,
    pub lb: Vec<QubitId>,
    pub cnt: Vec<QubitId>,
    pub par: QubitId,
    /// lanes in an unknown state that the slots borrow as AND-chain ancillas and restore (the shell's idle passenger)
    pub dirty: Vec<QubitId>,
    /// live-qubit cap of the circuit: a slot takes clean ancillas and carry pools while the cap leaves room, and
    /// borrowed lanes otherwise
    pub cap: u64,
}

/// Measurement record of one forward slot.
#[derive(Clone, Debug)]
pub struct SlotBits {
    pub d: BitId,
    pub r: Vec<BitId>,
    pub sw: BitId,
    pub a1: BitId,
    /// ROLL-FWD receipts of F4 (value) and F5 (cofactor); empty when the ladder is not rolled
    pub rv: RollRec,
    pub rc: RollRec,
}


thread_local! {
    static PROF: std::cell::RefCell<(u64, &'static str, Vec<(&'static str, u64, u64, u64)>, u64)> =
        std::cell::RefCell::new((0, "", vec![], 0));
}
/// GREEDYFROG_PROF=1: accumulate Toffoli per named section, the peak reached inside it and the section's highest live
/// count (debug aid, no effect on gates).
pub fn prof(b: &B, name: &'static str) {
    if std::env::var_os("GREEDYFROG_PROF").is_none() { return; }
    let sp = b.take_sect_peak();
    PROF.with(|p| {
        let mut p = p.borrow_mut();
        if !p.1.is_empty() {
            let (prev, t0) = (p.1, p.0);
            let pk = if b.peak > p.3 { b.peak } else { 0 };
            if let Some(e) = p.2.iter_mut().find(|e| e.0 == prev) {
                e.1 += b.tof - t0;
                e.2 = e.2.max(pk);
                e.3 = e.3.max(sp);
            } else {
                p.2.push((prev, b.tof - t0, pk, sp));
            }
        }
        p.3 = b.peak;
        p.0 = b.tof;
        p.1 = if name == "end" { "" } else { name };
    });
}
// B-PORT3 dev probe (inert unless P3_PHASE is set; the official build runs with an empty environment):
// P3_PHASE=<name>[,<name>..] (phase boundaries named by `p3` calls below), P3_DIR=hold|give (hold one dummy lane, or
// lend one lane of cap, across the phase), P3_SLOTS=lo-hi | all (default 10-16).
struct P3Cfg {
    phases: Vec<String>,
    give: bool,
    n: u64,
    lo: usize,
    hi: usize,
}
static P3CFG: std::sync::LazyLock<Option<P3Cfg>> = std::sync::LazyLock::new(|| {
    let ph = std::env::var("P3_PHASE").ok()?;
    let give = std::env::var("P3_DIR").map(|d| d == "give").unwrap_or(false);
    let sl = std::env::var("P3_SLOTS").unwrap_or_else(|_| "10-16".into());
    let (lo, hi) = if sl == "all" { (0, usize::MAX) } else {
        let (a, c) = sl.split_once('-').expect("P3_SLOTS lo-hi");
        (a.parse().unwrap(), c.parse().unwrap())
    };
    let n = std::env::var("P3_N").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
    Some(P3Cfg { phases: ph.split(',').map(|s| s.to_string()).collect(), give, n, lo, hi })
});
thread_local! {
    static P3ST: std::cell::RefCell<(usize, Vec<QubitId>, bool)> = const { std::cell::RefCell::new((0, Vec::new(), false)) };
}
/// dev probe: the traversal's current slot index
pub fn p3_slot(s: usize) {
    P3ST.with(|p| p.borrow_mut().0 = s);
}
fn p3(b: &mut B, u: &mut GreedyFrog, name: &str) {
    let Some(c) = P3CFG.as_ref() else { return };
    P3ST.with(|p| {
        let mut p = p.borrow_mut();
        let held = std::mem::take(&mut p.1);
        b.free_n(&held);
        if p.2 {
            u.cap -= c.n;
            p.2 = false;
        }
        if p.0 >= c.lo && p.0 <= c.hi && c.phases.iter().any(|x| x == name) {
            if c.give {
                u.cap += c.n;
                p.2 = true;
            } else {
                p.1 = b.alloc_n(c.n as usize);
            }
        }
    });
}
pub fn prof_dump() {
    PROF.with(|p| {
        for (n, t, pk, sp) in p.borrow().2.iter() {
            eprintln!("GREEDYFROG_PROF {n:16} {t:8} max live {sp:4} {}", if *pk > 0 { format!("new peak {pk}") } else { String::new() });
        }
    });
    PROF.with(|p| p.borrow_mut().2.clear());
}

// ------------------------------------------------------------------ small helpers

/// out ^= AND of literals (qubit, negated), transient ancillas, n - 1 Toffoli (n >= 1).
pub fn and_into(b: &mut B, lits: &[(QubitId, bool)], out: QubitId) {
    let n = lits.len();
    assert!(n >= 1);
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
    if n == 1 {
        b.cx(lits[0].0, out);
    } else if n == 2 {
        b.ccx(lits[0].0, lits[1].0, out);
    } else {
        let anc = b.alloc_n(n - 2);
        b.and_c(lits[0].0, lits[1].0, anc[0]);
        for i in 2..n - 1 {
            b.and_c(anc[i - 2], lits[i].0, anc[i - 1]);
        }
        b.ccx(anc[n - 3], lits[n - 1].0, out);
        for i in (2..n - 1).rev() {
            b.and_u(anc[i - 2], lits[i].0, anc[i - 1]);
        }
        b.and_u(lits[0].0, lits[1].0, anc[0]);
        b.free_n(&anc);
    }
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
}

/// out ^= [v == 0]
pub fn zero_into(b: &mut B, v: &[QubitId], out: QubitId) {
    let lits: Vec<(QubitId, bool)> = v.iter().map(|&q| (q, true)).collect();
    and_into(b, &lits, out);
}

/// Controlled rotation of a lane ring, content moving UP by k (lane j -> lane j + k mod n).
pub fn crot_up(b: &mut B, c: QubitId, v: &[QubitId], k: usize) {
    let n = v.len();
    let k = k % n;
    if k == 0 {
        return;
    }
    // content moves up by k == content moves down by n - k; crot_down(r): lane j <- lane j + r
    crot_down(b, c, v, n - k);
}

/// Controlled rotation, content moving DOWN by k (lane j <- lane j + k mod n).
pub fn crot_down(b: &mut B, c: QubitId, v: &[QubitId], k: usize) {
    let n = v.len();
    let k = k % n;
    if k == 0 {
        return;
    }
    let g = gcd(n, k);
    for s in 0..g {
        let len = n / g;
        let cyc: Vec<usize> = (0..len).map(|i| (s + i * k) % n).collect();
        for i in 0..len - 1 {
            b.cswap(c, v[cyc[i]], v[cyc[i + 1]]);
        }
    }
}

fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// t -= s (little-endian, len(s) <= len(t)), in place, Cuccaro; zero-extends s with transient ancillas.
pub fn sub_small(b: &mut B, t: &[QubitId], s: &[QubitId]) {
    let n = t.len();
    let pad = b.alloc_n(n - s.len());
    let mut ss: Vec<QubitId> = s.to_vec();
    ss.extend(&pad);
    let c0 = b.alloc();
    let ru = super::arith::up_m(b, t, &ss, c0, true);
    b.play(&ru, false);
    let rd = super::arith::down_m(b, t, &ss, c0, super::arith::Dm::Sum, true);
    b.play(&rd, false);
    b.free(c0);
    b.free_n(&pad);
}

/// t += s (little-endian, len(s) <= len(t)), in place.
pub fn add_small(b: &mut B, t: &[QubitId], s: &[QubitId]) {
    let n = t.len();
    let pad = b.alloc_n(n - s.len());
    let mut ss: Vec<QubitId> = s.to_vec();
    ss.extend(&pad);
    let c0 = b.alloc();
    let ru = super::arith::up_m(b, t, &ss, c0, false);
    b.play(&ru, false);
    let rd = super::arith::down_m(b, t, &ss, c0, super::arith::Dm::Sum, false);
    b.play(&rd, false);
    b.free(c0);
    b.free_n(&pad);
}

/// out ^= [a < b] for equal-length little-endian registers (borrow of a - b), registers restored.
pub fn lt_into(b: &mut B, a: &[QubitId], bb: &[QubitId], out: QubitId) {
    // up(t = a, s = bb) complements a and leaves [bb > a] on bb[L-1]
    let c0 = b.alloc();
    let ru = super::arith::up(b, a, bb, c0);
    b.play(&ru, false);
    b.cx(bb[a.len() - 1], out);
    b.play(&ru, true);
    b.free(c0);
}

/// out ^= [a == b] (equal length), registers restored.
/// out ^= [v == 0] with borrowed lanes for the AND.
fn zero_into_d(b: &mut B, v: &[QubitId], out: QubitId, dirty: &[QubitId]) {
    let lits: Vec<(QubitId, bool)> = v.iter().map(|&q| (q, true)).collect();
    and_dirty(b, &lits, out, dirty);
}

/// eq_into with borrowed lanes for the AND.
fn eq_into_d(b: &mut B, a: &[QubitId], bb: &[QubitId], out: QubitId, dirty: &[QubitId]) {
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
    zero_into_d(b, a, out, dirty);
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
}

pub fn eq_into(b: &mut B, a: &[QubitId], bb: &[QubitId], out: QubitId) {
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
    zero_into(b, a, out);
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
}

/// Where g = 0, flip the top bit of a length register: v >= 257 or v == 0 then (LB <= 256), which no top-compare
/// window matches.
fn mark_msb(b: &mut B, g: QubitId, v: &[QubitId]) {
    b.x(g);
    b.cx(g, v[v.len() - 1]);
    b.x(g);
}

/// XOR z0 into every bit of v (a finished shot's counter reads as all ones).
fn mark_done(b: &mut B, z0: QubitId, v: &[QubitId]) {
    for &q in v {
        b.cx(z0, q);
    }
}

// ------------------------------------------------------------------ masked ladders

struct Masked {
    f: QubitId,
    t: QubitId,
    gf: QubitId,
    chain: Vec<QubitId>,
    pre: Vec<QubitId>,
    c0: QubitId,
}

impl Masked {
    /// The value / cofactor ladders' scratch (mid passes only: no comparator chain with LADDER_NO_CHAIN).
    fn alloc_ladder(b: &mut B) -> Masked {
        if ladder_no_chain() { Masked::alloc_lean(b) } else { Masked::alloc(b) }
    }
    /// `alloc_ladder` with the prefix sized for a DEC_NARROW decoder of window top `hi`.
    fn alloc_ladder_w(b: &mut B, hi: usize) -> Masked {
        match (ladder_no_chain(), dec_keep(hi)) {
            (true, Some(h)) => {
                let f = b.alloc();
                Masked { f, t: b.alloc(), gf: f, chain: vec![], pre: b.alloc_n(h), c0: b.alloc() }
            }
            _ => Masked::alloc_ladder(b),
        }
    }
    fn alloc(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: b.alloc_n(LB_BITS - 1), pre: b.alloc_n(LB_BITS - 1), c0: b.alloc() }
    }
    /// The 9-bit decoder without a comparator chain: its comparators borrow lanes (`ge_const_dirty`, `in_range`).
    fn alloc_lean(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: vec![], pre: b.alloc_n(LB_BITS - 1), c0: b.alloc() }
    }
    /// For the decode's masks on the 6-bit u' (prefix 5; comparators borrow lanes) with a given AND temp.
    fn alloc_small_on(b: &mut B, t: QubitId) -> Masked {
        let f = b.alloc();
        Masked { f, t, gf: f, chain: vec![], pre: b.alloc_n(5), c0: b.alloc() }
    }
    /// For the decode's masks on the 6-bit u' (prefix 5; comparators borrow lanes).
    fn alloc_small(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: vec![], pre: b.alloc_n(5), c0: b.alloc() }
    }
    fn sc(&self) -> Mscr {
        Mscr { f: self.f, t: self.t, gf: self.gf, chain: self.chain.clone() }
    }
    fn free(self, b: &mut B) {
        b.free(self.f);
        b.free(self.t);
        b.free_n(&self.chain);
        b.free_n(&self.pre);
        b.free(self.c0);
    }
}

/// Lanes of the value chain: physical lanes W-hi..W-1 (hi = the window's largest LB; lanes below are off for every
/// active shot); f turns on at physical lane W - LB, ladder lanes 0 ..= hi - lo; above the window the lanes are
/// ordinary. The chain's carry out of lane W-1 is d (the borrow that clears A's MSB wrapped into lane 0 where d = 1,
/// or the carry that restores it); `value_pass` applies it to lane 0 explicitly, since lane 0 holds a cofactor bit
/// where d = 0.
fn value_ladder(u: &GreedyFrog, w: &Win) -> (Vec<QubitId>, Vec<QubitId>) {
    let hi = w.lb.1;
    (u.x[W - hi..].to_vec(), u.y[W - hi..].to_vec())
}

/// F4 (cmpl: X -= Y where a1) or I10 (X += Y where a1, and d ^= the carry); X lane 0 ^= a1 & carry out.
/// ROLL-FWD: the forward (cmpl) returns its receipts; the inverse takes them (`roll`, None or empty: not rolled).
fn value_pass(b: &mut B, u: &GreedyFrog, w: &Win, cmpl: bool, a1: QubitId, d: Option<QubitId>, always: bool,
              roll: Option<&RollRec>) -> RollRec {
    let m = Masked::alloc_ladder_w(b, w.lb.1);
    let (t, s) = value_ladder(u, w);
    // MASKED_WRITE_ALWAYS: a fully masked ladder carries c0 = 0 to the top on every marked a1 = 0 shot
    let top_free = always && (w.a1_const || w.lb.0 <= 1);
    if cmpl && roll_value() {
        // ROLL-FWD: F4 as the exact inverse of I10 (I10's frame: no complement), one upward traversal
        let srcs = [value_src(u, &m, w)];
        let sc = m.sc();
        let ld = Lad { t: &t, s: &s, c0: m.c0, srcs: &srcs, f0: false, cmpl: false, sc: &sc, g: &[] };
        let rm = roll_value_masked();
        let lanes = b.alloc_n(if rm { 1 } else { 2 });
        let g_ord = if always && w.a1_const { ALWAYS } else { a1 };
        let g_m = if always { ALWAYS } else { a1 };
        let rec = super::mask::roll_fwd(b, &ld, g_ord, g_m, rm, false, &lanes,
                                        Some((if top_free { ALWAYS } else { a1 }, u.x[0])));
        b.free_n(&lanes);
        m.free(b);
        return rec;
    }
    // carry pool over the ordinary lanes above the LB window
    let pool = pool_for(b, u, t.len() - (w.lb.1 - w.lb.0 + 1), 0);
    let srcs = [value_src(u, &m, w)];
    let sc = m.sc();
    let ld = Lad { t: &t, s: &s, c0: m.c0, srcs: &srcs, f0: false, cmpl, sc: &sc, g: &pool };
    // K2: room the ordinary lanes' carry pool leaves idle banks the masked cells' f & s' (K1 form)
    let bank = if k2() { pool_for(b, u, w.lb.1 - w.lb.0 + 1, 0) } else { vec![] };
    // mid passes: the running mask stays live between the up and down passes (nothing in between touches it), so
    // neither pass spends comparators cleaning it
    let ru = super::mask::mup_mid_bank_roll(b, &ld, &bank, roll.filter(|r| !r.rc.is_empty()));
    b.play(&ru, false);
    let tc = top_carry(&ld);
    if top_free { b.cx(tc, u.x[0]); } else { b.ccx(a1, tc, u.x[0]); }
    if let Some(d) = d {
        if top_free { b.cx(tc, d); } else { b.ccx(a1, tc, d); }
    }
    let rd = if always {
        super::mask::mdown_mid2_bank(b, &ld, Some(ALWAYS), Some(if w.a1_const { ALWAYS } else { a1 }), &bank)
    } else {
        super::mask::mdown_mid_bank(b, &ld, Some(a1), &bank)
    };
    b.play(&rd, false);
    b.free_n(&bank);
    b.free_n(&pool);
    m.free(b);
    RollRec::default()
}

/// ROLL-FWD for F5: the cofactor ladder as the exact inverse of I11 (I11's frame: cmpl; TERMINAL-CARRY SKIP as I11's
/// `masked_pass`), write gate g (a1) on the ordinary lanes, ALWAYS on the masked cells with MASKED_WRITE_ALWAYS.
fn cof_roll_fwd(b: &mut B, t: &[QubitId], s: &[QubitId], src: Src, m: &Masked, g: QubitId, always: bool,
                a1_const: bool) -> RollRec {
    let srcs = [src];
    let sc = m.sc();
    let ld = Lad { t, s, c0: m.c0, srcs: &srcs, f0: false, cmpl: true, sc: &sc, g: &[] };
    let rm = roll_cof_masked();
    let lanes = b.alloc_n(if rm { 1 } else { 2 });
    let g_ord = if always && a1_const { ALWAYS } else { g };
    let g_m = if always { ALWAYS } else { g };
    let rec = super::mask::roll_fwd(b, &ld, g_ord, g_m, rm, term_nc(), &lanes, None);
    b.free_n(&lanes);
    rec
}

/// MASKED_WRITE_ALWAYS: v[8] ^= stall = act & !a1 (act None: act = 1). Self-inverse, Clifford.
fn mark_stall(b: &mut B, act: Option<QubitId>, a1: QubitId, v: &[QubitId]) {
    // negative control for the gate tests only (W2_BREAK_MARK=1 drops the mark: stalled shots must then fail)
    if cfg!(test) && std::env::var_os("W2_BREAK_MARK").is_some() {
        return;
    }
    let v8 = v[LB_BITS - 1];
    match act {
        Some(a) => {
            b.cx(a, v8);
            b.cx(a1, v8);
        }
        None => {
            b.x(a1);
            b.cx(a1, v8);
            b.x(a1);
        }
    }
}

fn value_src(u: &GreedyFrog, m: &Masked, w: &Win) -> Src {
    // ladder lane l <-> physical W - hi + l; toggle where LB == hi - l
    let (lo, hi) = w.lb;
    let v = dec_view(&u.lb, hi);
    Src { lo: 0, hi: hi - lo + 1, a: hi as isize, d: -1, pre: m.pre[..v.len() - 1].to_vec(), v, late: false }
}

/// B-PORT3 DEC_NARROW: the value / cofactor passes' toggle decoder reads only the length bits that can be set inside
/// the slot's window plus the marker bit 8. With hi < 2^h, every toggle value j in [lo, hi] has bits h..8 clear, so
/// [v == j] = [v[0..h) == j] & !v[8] & ![v[h..8) != 0]; the dropped middle bits are 0 on every in-window shot, done-marked
/// finished shots (all ones) and stall-marked shots (bit 8 set) still match no lane, and a shot outside the window
/// already fails (Lambda kinds LB / LA-d). Saves 8 - h decoder ANDs per pass and 8 - h prefix lanes. Exact on
/// non-failing shots. Dev override `WL_DEC_NARROW=0|1`.
pub const DEC_NARROW: bool = true;
fn dec_narrow() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("DEC_NARROW", DEC_NARROW));
    *E
}
/// Number of low bits the decoder keeps for a window top `hi` (None: the full 9-bit register).
fn dec_keep(hi: usize) -> Option<usize> {
    let h = (usize::BITS - hi.leading_zeros()) as usize; // hi < 2^h
    (dec_narrow() && h >= 2 && h < LB_BITS - 1).then_some(h)
}
fn dec_view(v: &[QubitId], hi: usize) -> Vec<QubitId> {
    match dec_keep(hi) {
        // negative control for the gate tests only: P3_BREAK=5 drops the marker bit 8 (stalled / finished shots alias)
        Some(h) if cfg!(test) && std::env::var("P3_BREAK").map_or(false, |x| x.trim() == "5") => {
            v[..h + 1].to_vec()
        }
        Some(h) => v[..h].iter().chain(std::iter::once(&v[LB_BITS - 1])).copied().collect(),
        None => v.to_vec(),
    }
}

/// Cofactor chain: target Y, source X, physical lanes CW-1-lo down to 0 (lo = the window's smallest LA - d);
/// f turns on at physical lane CW - LA - 1 (CW = 257: W - 2 with the marker, W - 1 marker-free). X lane 0's source is `x0` = X[0] & !d (A's MSB sits there where d = 1).
fn cof_ladder(u: &GreedyFrog, w: &Win, x0: QubitId) -> (Vec<QubitId>, Vec<QubitId>) {
    let lo = w.lad.0;
    let t: Vec<QubitId> = (0..=CW - 1 - lo).rev().map(|j| u.y[j]).collect();
    let s: Vec<QubitId> = (0..=CW - 1 - lo).rev().map(|j| if j == 0 { x0 } else { u.x[j] }).collect();
    (t, s)
}

/// x0 ^= X[0] & !d
fn lane0_src(b: &mut B, u: &GreedyFrog, d: QubitId, x0: QubitId) {
    b.x(d);
    b.ccx(d, u.x[0], x0);
    b.x(d);
}

fn cof_src(u: &GreedyFrog, m: &Masked, w: &Win) -> Src {
    // ladder lane k <-> physical CW - 1 - lo - k; toggle where LA == lo + k
    let (lo, hi) = w.lad;
    let v = dec_view(&u.la, hi);
    Src { lo: 0, hi: hi - lo + 1, a: lo as isize, d: 1, pre: m.pre[..v.len() - 1].to_vec(), v, late: false }
}

/// Plain (unmasked) compare of equal-length ladders: out ^= [gate] & [s > t] (cmpl form), registers restored.
fn plain_compare(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, sc: &Mscr, out: Option<QubitId>,
                 gate: Option<(QubitId, bool)>, pool: &[QubitId]) {
    // with a carry pool the up pass keeps logical-AND carries, and replaying it inverted uncomputes them by measurement
    let ld = Lad { t, s, c0, srcs: &[], f0: false, cmpl: true, sc, g: pool };
    if out.is_none() && gate.is_none() && tc_phase() && super::mask::mid_phase_top(b, &ld, &[], mw_break(3)) {
        return;
    }
    let ru = mup(b, &ld);
    b.play(&ru, false);
    let tc = top_carry(&ld);
    match gate {
        Some((g, neg)) => {
            if neg {
                b.x(g);
            }
            match out {
                Some(o) => b.ccx(g, tc, o),
                None => b.cz(g, tc),
            }
            if neg {
                b.x(g);
            }
        }
        None => match out {
            Some(o) => b.cx(tc, o),
            None => b.z(tc),
        },
    }
    b.play(&ru, true);
}

/// Run a masked ladder pair. `cmpl`: subtract/compare form. `write`: Some(g) writes the masked sum where g = 1;
/// None only computes the top carry, XORs it into `carry_out`, and restores.
fn masked_pass(b: &mut B, u: &GreedyFrog, t: &[QubitId], s: &[QubitId], src: Src, m: &Masked, cmpl: bool,
               write: Option<QubitId>, carry_out: Option<QubitId>, pool: &[QubitId], always: bool, a1_const: bool,
               roll: Option<&RollRec>) {
    let nm = src.hi - src.lo;
    let srcs = [src];
    let sc = m.sc();
    let ld = Lad { t, s, c0: m.c0, srcs: &srcs, f0: false, cmpl, sc: &sc, g: pool };
    // K2: room the ordinary lanes' carry pool leaves idle banks the masked cells' f & s' (K1 form)
    let bank = if k2() && write.is_some() { pool_for(b, u, nm, 0) } else { vec![] };
    let roll = roll.filter(|r| !r.rc.is_empty());
    if term_nc() && carry_out.is_none() && write.is_some() {
        let g = write.unwrap();
        let ru = super::mask::mup_mid_nc_bank_roll(b, &ld, &bank, roll);
        b.play(&ru, false);
        let rd = if always {
            super::mask::mdown_mid2_nc_bank(b, &ld, Some(ALWAYS), Some(if a1_const { ALWAYS } else { g }), &bank)
        } else {
            super::mask::mdown_mid_nc_bank(b, &ld, Some(g), &bank)
        };
        b.play(&rd, false);
        b.free_n(&bank);
        return;
    }
    let ru = super::mask::mup_mid_bank_roll(b, &ld, &bank, roll);
    b.play(&ru, false);
    if let Some(co) = carry_out {
        let tc = top_carry(&ld);
        b.cx(tc, co);
    }
    match write {
        Some(g) => {
            let rd = if always {
                super::mask::mdown_mid2_bank(b, &ld, Some(ALWAYS), Some(if a1_const { ALWAYS } else { g }), &bank)
            } else {
                super::mask::mdown_mid_bank(b, &ld, Some(g), &bank)
            };
            b.play(&rd, false);
        }
        None => b.play(&ru, true),
    }
    b.free_n(&bank);
}

/// out ^= act & [Y[W-L..W) > X[W-L..W)] on the top WC lanes (L = LB, already done-marked by the caller). When the
/// slot's window has every active LB >= WC the compare is unmasked and `gate` (the done flag, negated) keeps
/// finished shots at 0; `gate` None leaves finished shots' bit arbitrary (callers that mask it themselves).
/// out ^= the compare (None: the phase (-1)^compare instead, for a measured erase).
fn top_compare(b: &mut B, u: &GreedyFrog, out: Option<QubitId>, w: &Win, gate: Option<(QubitId, bool)>) {
    if w.lb.0 >= wc() {
        let t: Vec<QubitId> = u.x[W - wc()..].to_vec();
        let s: Vec<QubitId> = u.y[W - wc()..].to_vec();
        let c0 = b.alloc();
        let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
        let pool = pool_for(b, u, wc(), 0);
        plain_compare(b, &t, &s, c0, &sc, out, gate, &pool);
        b.free_n(&pool);
        b.free(c0);
        return;
    }
    top_compare_masked(b, u, out);
}

/// big ^= [LB > WC] & [LB < 257] (done-marked LB >= 510 excluded), comparators on a clean chain held only meanwhile.
fn big_lb_flip(b: &mut B, u: &GreedyFrog, big: QubitId) {
    let chain = b.alloc_n(LB_BITS - 1);
    let tmp = b.alloc();
    let lt = b.alloc();
    super::mask::ge_const(b, &u.lb, wc() as isize + 1, tmp, &chain);
    super::mask::ge_const(b, &u.lb, 257, lt, &chain);
    b.x(lt);
    b.ccx(tmp, lt, big);
    b.x(lt);
    super::mask::ge_const(b, &u.lb, 257, lt, &chain);
    super::mask::ge_const(b, &u.lb, wc() as isize + 1, tmp, &chain);
    b.free_n(&[lt, tmp]);
    b.free_n(&chain);
}

/// BIGLB-SPLIT: big ^= [LB >= WC + 1] ^ [LB >= 257] (= [WC < LB < 257], LB >= 257 implies LB >= WC + 1): two
/// comparators straight into big, no temporaries.
fn big_lb_set(b: &mut B, u: &GreedyFrog, big: QubitId) {
    let chain = b.alloc_n(LB_BITS - 1);
    super::mask::ge_const(b, &u.lb, wc() as isize + 1, big, &chain);
    if !cr_break(3) { super::mask::ge_const(b, &u.lb, 257, big, &chain); }
    b.free_n(&chain);
}

fn top_compare_masked(b: &mut B, u: &GreedyFrog, out: Option<QubitId>) {
    // ladder over physical lanes W-WC .. W-1; ladder l <-> physical W - WC + l; f on where LB == WC - l
    let t: Vec<QubitId> = u.x[W - wc()..].to_vec();
    let s: Vec<QubitId> = u.y[W - wc()..].to_vec();
    // shots with LB >= WC start active at lane 0 (f0 = 1 would be wrong for done shots): toggle at l = 0 for any
    // LB >= WC is not expressible as one equality, so the window starts at the lane where LB == WC (l = 0) and
    // shots with LB > WC get an extra toggle source below via the "active from the start" flag `big`, computed
    // before the mask scratch exists (its comparator chain and the ladder's scratch never coexist).
    let big = b.alloc();
    if biglb_split() { big_lb_set(b, u, big); } else { big_lb_flip(b, u, big); }
    let m = Masked::alloc_lean(b);
    // f starts at `big`: emulate f0 = big by toggling f before the ladder; sources toggle where LB == WC - l (l >= 1)
    b.cx(big, m.f);
    let srcs = [Src { lo: 0, hi: wc(), v: u.lb.clone(), a: wc() as isize, d: -1, pre: m.pre.clone(), late: false }];
    let sc = m.sc();
    let ld = Lad { t: &t, s: &s, c0: m.c0, srcs: &srcs, f0: false, cmpl: true, sc: &sc, g: &[] };
    let bank = if k1() & 1 != 0 { pool_for(b, u, t.len(), 0) } else { vec![] };
    if !(out.is_none() && tc_phase() && super::mask::mid_phase_top(b, &ld, &bank, mw_break(3))) {
        let ru = super::mask::mup_mid_bank(b, &ld, &bank);
        b.play(&ru, false);
        let tc = top_carry(&ld);
        match out {
            Some(o) => b.cx(tc, o),
            None => b.z(tc),
        }
        b.play(&ru, true);
    }
    b.free_n(&bank);
    b.cx(big, m.f);
    m.free(b);
    if biglb_split() {
        erase_mbu(b, big, |b| {
            let chain = b.alloc_n(LB_BITS - 1);
            super::mask::ge_const_phase(b, &u.lb, wc() as isize + 1, &chain);
            super::mask::ge_const_phase(b, &u.lb, 257, &chain);
            b.free_n(&chain);
        });
    } else {
        big_lb_flip(b, u, big);
    }
    b.free(big);
}

/// out ^= AND of literals with caller-given |0> ancillas (len >= n - 2); n - 1 Toffoli; usable in a recording.
fn and_into_t(b: &mut B, lits: &[(QubitId, bool)], out: QubitId, anc: &[QubitId]) {
    let n = lits.len();
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
    if n == 1 {
        b.cx(lits[0].0, out);
    } else if n == 2 {
        b.ccx(lits[0].0, lits[1].0, out);
    } else {
        b.and_c(lits[0].0, lits[1].0, anc[0]);
        for i in 2..n - 1 {
            b.and_c(anc[i - 2], lits[i].0, anc[i - 1]);
        }
        b.ccx(anc[n - 3], lits[n - 1].0, out);
        for i in (2..n - 1).rev() {
            b.and_u(anc[i - 2], lits[i].0, anc[i - 1]);
        }
        b.and_u(lits[0].0, lits[1].0, anc[0]);
    }
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
}

/// Literals of [v == j] on the low v.len() bits.
fn eq_lits(v: &[QubitId], j: usize) -> Vec<(QubitId, bool)> {
    v.iter().enumerate().map(|(i, &q)| (q, (j >> i) & 1 == 0)).collect()
}

/// t += s + cin (cin classical), in place.
fn add_c(b: &mut B, t: &[QubitId], s: &[QubitId], cin: bool, sub: bool) {
    let c0 = b.alloc();
    add_c_on(b, t, s, cin, sub, c0);
    b.free(c0);
}

/// add_c with the carry-in on a given |0> lane (restored).
fn add_c_on(b: &mut B, t: &[QubitId], s: &[QubitId], cin: bool, sub: bool, c0: QubitId) {
    let n = t.len();
    let pad = b.alloc_n(n - s.len());
    let mut ss: Vec<QubitId> = s.to_vec();
    ss.extend(&pad);
    if cin {
        b.x(c0);
    }
    let ru = super::arith::up_m(b, t, &ss, c0, sub);
    b.play(&ru, false);
    let rd = super::arith::down_m(b, t, &ss, c0, super::arith::Dm::Sum, sub);
    b.play(&rd, false);
    if cin {
        b.x(c0);
    }
    b.free_n(&pad);
}

/// v += k (sub: v -= k) for a classical k, in place (transient constant register).
/// v += k (or -= k) mod 2^n with borrowed lanes and no constant register: one increment of v[i..] per set bit i of k
/// (a decrement is an increment conjugated by NOT on every bit).
fn add_const_dirty(b: &mut B, v: &[QubitId], k: usize, sub: bool, dirty: &[QubitId]) {
    for i in 0..v.len() {
        if (k >> i) & 1 == 1 {
            if sub {
                for &q in &v[i..] {
                    b.x(q);
                }
            }
            let w = &v[i..];
            for h in (1..w.len()).rev() {
                let lits: Vec<(QubitId, bool)> = w[..h].iter().map(|&q| (q, false)).collect();
                and_dirty(b, &lits, w[h], dirty);
            }
            b.x(w[0]);
            if sub {
                for &q in &v[i..] {
                    b.x(q);
                }
            }
        }
    }
}

pub fn add_const(b: &mut B, v: &[QubitId], k: usize, sub: bool) {
    let c = b.alloc_n(v.len());
    for (i, &q) in c.iter().enumerate() {
        if (k >> i) & 1 == 1 {
            b.x(q);
        }
    }
    add_c(b, v, &c, false, sub);
    for (i, &q) in c.iter().enumerate() {
        if (k >> i) & 1 == 1 {
            b.x(q);
        }
    }
    b.free_n(&c);
}

// ------------------------------------------------------------------ SMALL-LADDER-POOLED (B-WALK2)

/// A pooled ladder's carry: a classical constant or a qubit (a fresh |0> lane, an alias of a register lane, or the
/// caller's carry-in lane).
#[derive(Clone, Copy, Debug)]
enum Cy {
    K(bool),
    Q(QubitId),
}

/// One lane step of a pooled ladder: how the carry out of lane i is formed from the carry into it.
#[derive(Clone, Copy, Debug)]
enum Step {
    /// constant carry out (no gate)
    K(bool),
    /// carry out = an existing qubit (no gate)
    Alias(QubitId),
    /// fresh lane = AND of two literals (qubit, negated), the result itself negated when `neg_out` (an OR)
    And { a: (QubitId, bool), b: (QubitId, bool), neg_out: bool },
    /// fresh lane = MAJ(q, t, s) by the measured-uncompute cell (t ^= q, s ^= q, g = t & s, g ^= q)
    Maj { q: QubitId },
}

/// Plan of t + s + c0 (s zero-extended): the carries into lanes 1..n-1.
fn plan_add(t: &[QubitId], s: &[QubitId], c0: Cy) -> Vec<Step> {
    let n = t.len();
    let mut c = c0;
    let mut v = vec![];
    for i in 0..n - 1 {
        let st = match (c, s.get(i)) {
            (Cy::K(false), None) => Step::K(false),
            (Cy::K(true), None) => Step::Alias(t[i]),
            (Cy::K(false), Some(&si)) => Step::And { a: (t[i], false), b: (si, false), neg_out: false },
            (Cy::K(true), Some(&si)) => Step::And { a: (t[i], true), b: (si, true), neg_out: true },
            (Cy::Q(q), None) => Step::And { a: (q, false), b: (t[i], false), neg_out: false },
            (Cy::Q(q), Some(_)) => Step::Maj { q },
        };
        v.push(st);
        c = match st { Step::K(k) => Cy::K(k), Step::Alias(q) => Cy::Q(q), _ => Cy::Q(QubitId(u64::MAX)) };
    }
    v
}

/// Plan of v + k (classical k): the carries into lanes 1..n-1. c' = k_i ? (v_i | c) : (v_i & c).
fn plan_add_const(v: &[QubitId], k: usize) -> Vec<Step> {
    let n = v.len();
    let mut c = Cy::K(false);
    let mut out = vec![];
    for i in 0..n - 1 {
        let ki = (k >> i) & 1 == 1;
        let st = match (c, ki) {
            (Cy::K(false), false) => Step::K(false),
            (Cy::K(false), true) | (Cy::K(true), false) => Step::Alias(v[i]),
            (Cy::K(true), true) => Step::K(true),
            (Cy::Q(q), false) => Step::And { a: (v[i], false), b: (q, false), neg_out: false },
            (Cy::Q(q), true) => Step::And { a: (v[i], true), b: (q, true), neg_out: true },
        };
        out.push(st);
        c = match st { Step::K(k) => Cy::K(k), Step::Alias(q) => Cy::Q(q), _ => Cy::Q(QubitId(u64::MAX)) };
    }
    out
}

fn plan_lanes(p: &[Step]) -> usize {
    p.iter().filter(|s| matches!(s, Step::And { .. } | Step::Maj { .. })).count()
}

/// The carries into lanes 0..=p.len() (fresh lanes taken from `g` in order), with the planned placeholder qubits
/// resolved: a step's carry-in qubit is the previous step's output.
fn plan_carries(p: &mut [Step], c0: Cy, g: &[QubitId]) -> Vec<Cy> {
    let mut cs = vec![c0];
    let mut gi = 0;
    for i in 0..p.len() {
        // resolve placeholders (u64::MAX) against the actual carry into this lane
        let cin = cs[i];
        let fix = |q: QubitId| if q == QubitId(u64::MAX) { match cin { Cy::Q(r) => r, Cy::K(_) => unreachable!() } } else { q };
        p[i] = match p[i] {
            Step::And { a, b, neg_out } => Step::And { a: (fix(a.0), a.1), b: (fix(b.0), b.1), neg_out },
            Step::Maj { q } => Step::Maj { q: fix(q) },
            st => st,
        };
        let c = match p[i] {
            Step::K(k) => Cy::K(k),
            Step::Alias(q) => Cy::Q(q),
            Step::And { .. } | Step::Maj { .. } => {
                gi += 1;
                Cy::Q(g[gi - 1])
            }
        };
        cs.push(c);
    }
    cs
}

/// Compute the carry out of lane i (up) or uncompute it by measurement (down).
fn carry_step(b: &mut B, p: &[Step], t: &[QubitId], s: &[QubitId], cs: &[Cy], i: usize, up: bool) {
    let Cy::Q(gq) = cs[i + 1] else { return };
    match p[i] {
        Step::And { a, b: bb, neg_out } => {
            if a.1 { b.x(a.0); }
            if bb.1 { b.x(bb.0); }
            if up {
                b.and_c(a.0, bb.0, gq);
                if neg_out { b.x(gq); }
            } else {
                if neg_out { b.x(gq); }
                b.and_u(a.0, bb.0, gq);
            }
            if bb.1 { b.x(bb.0); }
            if a.1 { b.x(a.0); }
        }
        Step::Maj { q } => {
            if up {
                b.cx(q, t[i]);
                b.cx(q, s[i]);
                b.and_c(t[i], s[i], gq);
                b.cx(q, gq);
            } else {
                // leaves t[i] = t ^ c (the caller restores it or writes the sum), s restored
                b.cx(q, gq);
                b.and_u(t[i], s[i], gq);
                b.cx(q, s[i]);
            }
        }
        _ => {}
    }
}

/// t ^= carry (a constant or a qubit)
fn xor_cy(b: &mut B, c: Cy, t: QubitId) {
    match c {
        Cy::K(true) => b.x(t),
        Cy::K(false) => {}
        Cy::Q(q) => b.cx(q, t),
    }
}

/// t += s + c0 (sub: t -= s + c0) mod 2^n, s zero-extended, as a logical-AND carry ladder (at most n - 1 Toffoli,
/// fresh carries erased by measurement). The caller checks the room (`pooled_need_add`).
fn add_pooled(b: &mut B, t: &[QubitId], s: &[QubitId], c0: Cy, sub: bool) {
    let n = t.len();
    assert!(s.len() <= n && n >= 1);
    if sub {
        for &q in t { b.x(q); }
    }
    let mut p = plan_add(t, s, c0);
    let g = b.alloc_n(plan_lanes(&p));
    let cs = plan_carries(&mut p, c0, &g);
    for i in 0..n - 1 {
        carry_step(b, &p, t, s, &cs, i, true);
    }
    // top lane: sum only
    if let Some(&si) = s.get(n - 1) { b.cx(si, t[n - 1]); }
    xor_cy(b, cs[n - 1], t[n - 1]);
    // lanes n-2 .. 0: uncompute the carry out of the lane, then write its sum
    for i in (0..n - 1).rev() {
        carry_step(b, &p, t, s, &cs, i, false);
        match (p[i], s.get(i)) {
            (Step::Maj { .. }, Some(&si)) => b.cx(si, t[i]), // t holds t ^ c, s restored: t ^= s
            (_, Some(&si)) => {
                b.cx(si, t[i]);
                xor_cy(b, cs[i], t[i]);
            }
            (_, None) => xor_cy(b, cs[i], t[i]),
        }
    }
    b.free_n(&g);
    if sub {
        for &q in t { b.x(q); }
    }
}

fn pooled_need_add(t: &[QubitId], s: &[QubitId], c0: Cy) -> usize {
    plan_lanes(&plan_add(t, s, c0))
}

fn const_mod(n: usize, k: usize, sub: bool) -> usize {
    let m = 1usize << n;
    if sub { (m - (k % m)) % m } else { k % m }
}

/// v += k (sub: v -= k) mod 2^n, classical k, as a logical-AND carry ladder (no constant register).
fn add_const_pooled(b: &mut B, v: &[QubitId], k: usize, sub: bool) {
    let n = v.len();
    let k = const_mod(n, k, sub);
    let mut p = plan_add_const(v, k);
    let g = b.alloc_n(plan_lanes(&p));
    let cs = plan_carries(&mut p, Cy::K(false), &g);
    for i in 0..n - 1 {
        carry_step(b, &p, v, &[], &cs, i, true);
    }
    xor_cy(b, cs[n - 1], v[n - 1]);
    if (k >> (n - 1)) & 1 == 1 { b.x(v[n - 1]); }
    for i in (0..n - 1).rev() {
        carry_step(b, &p, v, &[], &cs, i, false);
        xor_cy(b, cs[i], v[i]);
        if (k >> i) & 1 == 1 { b.x(v[i]); }
    }
    b.free_n(&g);
}

/// out ^= [a < bb] (out None: the phase (-1)^[a < bb]) for equal-length registers, restored: the carry out of
/// ~a + bb on a logical-AND ladder (n - 1 ANDs, plus the top MAJ's Toffoli for the XOR form).
fn lt_pooled(b: &mut B, a: &[QubitId], bb: &[QubitId], out: Option<QubitId>) {
    lt_pooled_c(b, a, bb, Cy::K(false), out)
}

/// lt_pooled with a carry-in c0: out ^= the carry out of ~a + bb + c0 = [a < bb + c0].
fn lt_pooled_c(b: &mut B, a: &[QubitId], bb: &[QubitId], c0: Cy, out: Option<QubitId>) {
    let n = a.len();
    for &q in a { b.x(q); }
    let mut p = plan_add(a, bb, c0);
    let g = b.alloc_n(plan_lanes(&p));
    let cs = plan_carries(&mut p, c0, &g);
    for i in 0..n - 1 {
        carry_step(b, &p, a, bb, &cs, i, true);
    }
    // carry out of the top lane = MAJ(a', bb, c) = c ^ ((a' ^ c) & (bb ^ c))
    let (t, s) = (a[n - 1], bb[n - 1]);
    match cs[n - 1] {
        Cy::Q(q) => {
            b.cx(q, t);
            b.cx(q, s);
            match out {
                Some(o) => {
                    b.cx(q, o);
                    b.ccx(t, s, o);
                }
                None => {
                    b.z(q);
                    b.cz(t, s);
                }
            }
            b.cx(q, s);
            b.cx(q, t);
        }
        Cy::K(c) => {
            // c ? t | s : t & s
            if c { b.x(t); b.x(s); }
            match out {
                Some(o) => {
                    b.ccx(t, s, o);
                    if c { b.x(o); }
                }
                None => {
                    b.cz(t, s);
                    if c { b.z(t); b.x(t); b.z(t); b.x(t); }
                }
            }
            if c { b.x(s); b.x(t); }
        }
    }
    for i in (0..n - 1).rev() {
        carry_step(b, &p, a, bb, &cs, i, false);
        if let Step::Maj { q } = p[i] { b.cx(q, a[i]); }
    }
    b.free_n(&g);
    for &q in a { b.x(q); }
}

/// t += s + cin (sub: t -= s + cin) for the walk's small registers: pooled while the cap leaves room, else Cuccaro.
fn add_sm(b: &mut B, u: &GreedyFrog, t: &[QubitId], s: &[QubitId], cin: bool, sub: bool) {
    if small_pooled() && u.room(b) >= pooled_need_add(t, s, Cy::K(cin)) {
        add_pooled(b, t, s, Cy::K(cin), sub);
    } else if s.len() == t.len() || cin {
        add_c(b, t, s, cin, sub);
    } else if sub {
        sub_small(b, t, s);
    } else {
        add_small(b, t, s);
    }
}

/// add_c_on on a carry-in lane c0 (|0>, or holding a quantum carry-in when `qcin`).
fn add_on_sm(b: &mut B, u: &GreedyFrog, t: &[QubitId], s: &[QubitId], cin: bool, sub: bool, c0: QubitId, qcin: bool) {
    let cy = if qcin { Cy::Q(c0) } else { Cy::K(cin) };
    if small_pooled() && u.room(b) >= pooled_need_add(t, s, cy) {
        add_pooled(b, t, s, cy, sub);
    } else {
        add_c_on(b, t, s, cin, sub, c0);
    }
}

fn add_const_sm(b: &mut B, u: &GreedyFrog, v: &[QubitId], k: usize, sub: bool) {
    if small_pooled() && u.room(b) >= plan_lanes(&plan_add_const(v, const_mod(v.len(), k, sub))) {
        add_const_pooled(b, v, k, sub);
    } else {
        add_const_auto(b, u, v, k, sub);
    }
}

/// out ^= [a < bb], or its phase (out None).
fn lt_sm(b: &mut B, u: &GreedyFrog, a: &[QubitId], bb: &[QubitId], out: Option<QubitId>) {
    if small_pooled() && u.room(b) >= pooled_need_add(a, bb, Cy::K(false)) {
        lt_pooled(b, a, bb, out);
    } else {
        match out {
            Some(o) => lt_into(b, a, bb, o),
            None => lt_phase(b, a, bb),
        }
    }
}

/// SWF-LEX: out ^= [a < bb + cin] = [a < bb] | [a == bb] & cin (cin a qubit, restored), or its phase (out None).
fn lt_cin_sm(b: &mut B, u: &GreedyFrog, a: &[QubitId], bb: &[QubitId], cin: QubitId, out: Option<QubitId>) {
    if small_pooled() && u.room(b) >= pooled_need_add(a, bb, Cy::Q(cin)) {
        lt_pooled_c(b, a, bb, Cy::Q(cin), out);
    } else {
        // Cuccaro: up() complements a and leaves the carry out of ~a + bb + c0 on bb's top lane
        let ru = super::arith::up(b, a, bb, cin);
        b.play(&ru, false);
        match out {
            Some(o) => b.cx(bb[a.len() - 1], o),
            None => b.z(bb[a.len() - 1]),
        }
        b.play(&ru, true);
    }
}

/// F6-F8 by binary search: for k = 2..0, r_k ^= act & [top 2^k lanes of X all zero], then X rotates up by 2^k where
/// r_k. r = min(leading zeros of X, 7) (the marker stops the count when A' = 0); the rest is left to stall slots.
fn renorm_top_legacy(b: &mut B, x: &[QubitId], act: Option<QubitId>, r: &[QubitId]) {
    for k in (0..r.len()).rev() {
        let n = 1usize << k;
        let mut lits = act_lits(act);
        lits.extend((0..n).map(|i| (x[W - 1 - i], true)));
        let anc = b.alloc_n(lits.len().saturating_sub(2));
        and_into_t(b, &lits, r[k], &anc);
        b.free_n(&anc);
        crot_up(b, r[k], x, n);
    }
}

/// Inverse of renorm_top: stage by stage, rotate back and erase r_k.
fn unrenorm_top_legacy(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, r: &[QubitId]) {
    let x = &u.x;
    for k in 0..r.len() {
        let n = 1usize << k;
        crot_down(b, r[k], x, n);
        let mut lits = act_lits(act);
        lits.extend((0..n).map(|i| (x[W - 1 - i], true)));
        erase_and(b, u, r[k], &lits);
    }
}


/// B-ROT8 (Q825): drop the one barrel cswap that is a no-op under the renormalisation promise. When shift
/// s = r0+2r1+4r2 > 0 (so act = 1), the top s lanes of X are zero before the forward barrel (prefix_seven counts them),
/// and the same holds in unrenorm_top, whose input is that barrel's output (its own r erase relies on it). Tracking
/// the zero lanes through the four reflections, the stage-3 (ctrl r2) cswap on lanes 3 and 1 swaps two zero lanes for
/// every s in 4..8 and is idle for s < 4: exact on the promise, -1 Toffoli per call (513 -> 512 at W = 258). In the
/// telescoped 4-reflection family every exact 2W-3 gauge (all common axis offsets, bit orders and directions; searched
/// in builds/rot8/model/gauge_search.py, affine_scan.py) admits at most one such deletion, and the present gauge
/// (axes 1, 0, -2, -6) is one of the four that reach it. Off-promise data would be mis-rotated, so only the
/// renorm/unrenorm callers pass promise = true.
pub const ROT8_PROMISE_DELETE: bool = true;

/// Exact 3-bit barrel: four reflections with adjacent-XOR controls.
/// On the reversed ring, axes 1, 0, -2, -6 give an upward shift r0+2r1+4r2.
/// `promise`: the top s lanes of X are zero on input (forward) / the bottom s lanes on input (inverse); see
/// ROT8_PROMISE_DELETE.
fn rotate_three(b: &mut B, x: &[QubitId], r: &[QubitId], inverse: bool, promise: bool) {
    assert_eq!(r.len(), 3);
    let n = x.len() as isize;
    assert!(n >= 16);
    let drop_pair = promise && ROT8_PROMISE_DELETE;
    let stages: Vec<usize> = if inverse { (0..4).rev().collect() } else { (0..4).collect() };
    for stage in stages {
        let axis = [1isize, 0, -2, -6][stage];
        let ctrl = r[stage.min(2)];
        if stage == 1 || stage == 2 { b.cx(r[stage-1], ctrl); }
        for i in 0..n {
            let j = (axis - i).rem_euclid(n);
            // stage 3, reversed index i = n-4 pairs with j = n-2: lanes 3 and 1.
            if drop_pair && stage == 3 && i == n - 4 { debug_assert_eq!(j, n - 2); continue; }
            if i < j { b.cswap(ctrl, x[(n-1-i) as usize], x[(n-1-j) as usize]); }
        }
        if stage == 1 || stage == 2 { b.cx(r[stage-1], ctrl); }
    }
}

/// Prefix j is act AND the first j+1 top lanes being zero.
fn prefix_seven(b: &mut B, x: &[QubitId], act: Option<QubitId>, p: &[QubitId], undo: bool) {
    let is: Vec<usize> = if undo { (0..7).rev().collect() } else { (0..7).collect() };
    for i in is {
        let q = x[W-1-i];
        b.x(q);
        let prev = if i == 0 { act } else { Some(p[i-1]) };
        match prev {
            Some(c) => if undo { b.and_u(c,q,p[i]); } else { b.and_c(c,q,p[i]); },
            None => b.cx(q,p[i]),
        }
        b.x(q);
    }
}
const SHIFT_PREFIXES: [&[usize];3] = [&[0,1,2,3,4,5,6], &[1,3,5], &[3]];

// ------------------------------------------------------------------ G2-01 MARKER-FREE: the LA gate of the renorm prefix
/// A literal (qubit, negated); None = the constant 1.
type Lit = Option<(QubitId, bool)>;

/// Negative control for the gate tests only (MF_BREAK=1: the renorm prefixes are not gated, i.e. the naive leading-zero
/// count of a marker-free ring; finishing steps whose tB has a 0 under the value must then fail).
fn mf_break() -> bool {
    cfg!(test) && std::env::var("MF_BREAK").map_or(false, |v| v.trim() == "1")
}

/// The thermometer e_i = [LA <= i] (i in 1..=6) of the LA register at the renormalisation, for the prefixes p_i the
/// marker-free ring must gate: p'_i = p_i & !e_i (rho = min(lz, LA, 7)). Only the e_i with need[i] are formed. LA < 2^hb
/// on every non-failing shot, so nh = [LA < 8] = AND of !LA[3..hb). Construction (logical ANDs, measured uncompute):
/// e3 = nh & !L2, e1 = e3 & !L1, a = L1 & L0, e2 = e3 & !a; m = nh & L2 = nh ^ e3 (CX only), mn = m & !L1, e5 = e3 ^ mn,
/// x4 = mn & !L0, e4 = e3 ^ x4, x6 = m & !a, e6 = e3 ^ x6 (the XOR terms are disjoint, so XOR = OR); hb - 4 + 8 Toffoli
/// for all six.
struct LaGate {
    /// e_i literal per i (None where not formed)
    e: [Option<(QubitId, bool)>; 7],
    lanes: Vec<QubitId>,
    rec: Vec<super::builder::G>,
}

impl LaGate {
    fn build(b: &mut B, la: &[QubitId], hb: usize, need: [bool; 7]) -> LaGate {
        let (l0, l1, l2) = (la[0], la[1], la[2]);
        let any = |is: &[usize]| is.iter().any(|&i| need[i]);
        let n_hi = hb.saturating_sub(3);
        let n_nh = n_hi.saturating_sub(1);
        let want_e3 = any(&[1, 2, 3, 4, 5, 6]);
        let want_a = any(&[2, 6]);
        let want_m = any(&[4, 5, 6]);
        let want_mn = any(&[4, 5]);
        // lanes, allocated before the recording
        let mut lanes = vec![];
        let mut take = |b: &mut B, on: bool| -> Option<QubitId> {
            if on { let q = b.alloc(); lanes.push(q); Some(q) } else { None }
        };
        let nh_l: Vec<QubitId> = (0..n_nh).map(|_| take(b, true).unwrap()).collect();
        let e3_l = take(b, want_e3 && n_hi > 0);
        let e1_l = take(b, need[1]);
        let a_l = take(b, want_a);
        let e2_l = take(b, need[2]);
        let m_l = take(b, want_m && n_hi > 0);
        let mn_l = take(b, want_mn);
        let x4_l = take(b, need[4]);
        let x6_l = take(b, need[6]);
        b.begin();
        // x & y into the fresh lane t (X conjugation of negated operands); None operands are 1
        let and2 = |b: &mut B, x: Lit, y: Lit, t: QubitId| -> Lit {
            match (x, y) {
                (None, None) => b.x(t),
                (Some((q, ng)), None) | (None, Some((q, ng))) => {
                    b.cx(q, t);
                    if ng { b.x(t); }
                }
                (Some((qa, na)), Some((qb, nb))) => {
                    if na { b.x(qa); }
                    if nb { b.x(qb); }
                    b.and_c(qa, qb, t);
                    if nb { b.x(qb); }
                    if na { b.x(qa); }
                }
            }
            Some((t, false))
        };
        let xor_in = |b: &mut B, l: Lit, t: QubitId| match l {
            None => b.x(t),
            Some((q, ng)) => {
                b.cx(q, t);
                if ng { b.x(t); }
            }
        };
        // nh = AND of !LA[3..hb)
        let nh: Lit = if n_hi == 0 {
            None
        } else if n_hi == 1 {
            Some((la[3], true))
        } else {
            let mut cur = and2(b, Some((la[3], true)), Some((la[4], true)), nh_l[0]);
            for k in 1..n_nh {
                cur = and2(b, cur, Some((la[4 + k], true)), nh_l[k]);
            }
            cur
        };
        let mut e: [Option<(QubitId, bool)>; 7] = [None; 7];
        let e3: Lit = if !want_e3 { None } else if n_hi == 0 { Some((l2, true)) } else { and2(b, nh, Some((l2, true)), e3_l.unwrap()) };
        if need[3] { e[3] = e3; }
        if need[1] { e[1] = and2(b, e3, Some((l1, true)), e1_l.unwrap()); }
        let a: Lit = if want_a { and2(b, Some((l1, false)), Some((l0, false)), a_l.unwrap()) } else { None };
        if need[2] { e[2] = and2(b, e3, Some((a.unwrap().0, true)), e2_l.unwrap()); }
        let m: Lit = if !want_m {
            None
        } else if n_hi == 0 {
            Some((l2, false))
        } else {
            let t = m_l.unwrap();
            xor_in(b, nh, t);
            xor_in(b, e3, t);
            Some((t, false))
        };
        let mn: Lit = if want_mn { and2(b, m, Some((l1, true)), mn_l.unwrap()) } else { None };
        if need[4] { and2(b, mn, Some((l0, true)), x4_l.unwrap()); }
        if need[6] { and2(b, m, Some((a.unwrap().0, true)), x6_l.unwrap()); }
        // e4, e5, e6 in place: x ^= e3 (disjoint terms)
        if need[4] { let t = x4_l.unwrap(); xor_in(b, e3, t); e[4] = Some((t, false)); }
        if need[5] { let t = mn_l.unwrap(); xor_in(b, e3, t); e[5] = Some((t, false)); }
        if need[6] { let t = x6_l.unwrap(); xor_in(b, e3, t); e[6] = Some((t, false)); }
        let rec = b.end();
        b.play(&rec, false);
        LaGate { e, lanes, rec }
    }
    fn unbuild(self, b: &mut B) {
        b.play(&self.rec, true);
        b.free_n(&self.lanes);
    }
    /// g_i = [LA > i] = !e_i as a literal
    fn g(&self, i: usize) -> (QubitId, bool) {
        let (q, ng) = self.e[i].expect("LA gate literal not formed");
        (q, !ng)
    }
}

/// The gate a slot's renormalisation needs: (LA register, la_hb, la_gmin); None without the marker-free ring.
type GateSpec<'a> = Option<(&'a [QubitId], usize, usize)>;
fn gate_spec<'a>(la: &'a [QubitId], w: &Win) -> GateSpec<'a> {
    if MARKER_FREE && w.la_gmin < 7 && !mf_break() { Some((la, w.la_hb, w.la_gmin.max(1))) } else { None }
}
fn gate_need(gmin: usize, is: &[usize]) -> [bool; 7] {
    let mut need = [false; 7];
    for &i in is {
        if i >= gmin && (1..=6).contains(&i) { need[i] = true; }
    }
    need
}

/// t := p & lit in a fresh lane, run `f`, t uncomputed by measurement (lit = (q, negated)).
fn with_and(b: &mut B, p: QubitId, lit: (QubitId, bool), f: impl FnOnce(&mut B, QubitId)) {
    let t = b.alloc();
    if lit.1 { b.x(lit.0); }
    b.and_c(p, lit.0, t);
    if lit.1 { b.x(lit.0); }
    f(b, t);
    if lit.1 { b.x(lit.0); }
    b.and_u(p, lit.0, t);
    if lit.1 { b.x(lit.0); }
    b.free(t);
}

fn renorm_top(b: &mut B, x: &[QubitId], act: Option<QubitId>, r: &[QubitId], gate: GateSpec) {
    let p = b.alloc_n(7);
    prefix_seven(b,x,act,&p,false);
    match gate {
        None => for i in 0..3 { for &j in SHIFT_PREFIXES[i] { b.cx(p[j],r[i]); } },
        Some((la, hb, gmin)) => {
            // MARKER_FREE: p'_j = p_j & [LA > j] for j >= gmin, one logical AND each, its r parities by CX
            let lg = LaGate::build(b, la, hb, gate_need(gmin, &[1, 2, 3, 4, 5, 6]));
            for j in 0..7 {
                let ks: Vec<usize> = (0..3).filter(|&k| SHIFT_PREFIXES[k].contains(&j)).collect();
                if j < gmin {
                    for &k in &ks { b.cx(p[j], r[k]); }
                } else {
                    with_and(b, p[j], lg.g(j), |b, t| for &k in &ks { b.cx(t, r[k]); });
                }
            }
            lg.unbuild(b);
        }
    }
    prefix_seven(b,x,act,&p,true);
    b.free_n(&p);
    rotate_three(b,x,r,false,true);
}
fn unrenorm_top(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, r: &[QubitId], gate: GateSpec) {
    rotate_three(b,&u.x,r,true,true);
    let receipts=b.fresh_bits(3);
    for i in 0..3 { b.hmr_to(r[i],receipts[i]); }
    if unren_cond() { unren_phase_cond(b, &u.x, act, &receipts, gate); return; }
    let p=b.alloc_n(7);
    prefix_seven(b,&u.x,act,&p,false);
    match gate {
        None => for i in 0..3 { for &j in SHIFT_PREFIXES[i] { b.z_if(p[j],receipts[i]); } },
        Some((la, hb, gmin)) => {
            let lg = LaGate::build(b, la, hb, gate_need(gmin, &[1, 2, 3, 4, 5, 6]));
            for i in 0..3 {
                for &j in SHIFT_PREFIXES[i] {
                    if j < gmin {
                        b.z_if(p[j], receipts[i]);
                    } else {
                        // phase (-1)^(m_i p_j [LA > j]): a CZ under the receipt
                        let (q, ng) = lg.g(j);
                        if ng { b.x(q); }
                        b.push_condition(receipts[i]);
                        b.cz(p[j], q);
                        b.pop_condition();
                        if ng { b.x(q); }
                    }
                }
            }
            lg.unbuild(b);
        }
    }
    prefix_seven(b,&u.x,act,&p,true);
    b.free_n(&p);
}

/// UNREN-COND: the phase (-1)^(m0 r0 + m1 r1 + m2 r2) of unrenorm_top's measured r, r = SHIFT_PREFIXES parities of the
/// prefixes p_j = act & z_0 & .. & z_j (z_i = !X[W-1-i]): (-1)^(sum_j c_j p_j), c_j = m0 ^ m1 [j in {1,3,5}] ^ m2 [j == 3].
/// Three exclusive classical blocks: m0 (highest c_j = 1 at j = 6), !m0 & m1 (j = 5), !m0 & !m1 & m2 (j = 3); each builds
/// the chain p_0..p_(J-1) (measured uncompute), applies the inner phases and gets p_J's phase as CZ(p_(J-1), z_J).
fn unren_phase_cond(b: &mut B, x: &[QubitId], act: Option<QubitId>, m: &[BitId], gate: GateSpec) {
    // block on m0; then, with m0 inverted, nested blocks !m0 & m1 and (m1 inverted) !m0 & !m1 & m2; bits restored
    unren_block(b, x, act, 6, &[0, 1, 2, 3, 4, 5], &[(1, m[1]), (3, m[1]), (5, m[1]), (3, m[2])], &[m[0]], gate);
    b.bit_invert(m[0]);
    b.push_condition(m[0]);
    unren_block(b, x, act, 5, &[1, 3], &[(3, m[2])], &[m[1]], gate);
    b.bit_invert(m[1]);
    unren_block(b, x, act, 3, &[], &[], &[m[1], m[2]], gate);
    b.bit_invert(m[1]);
    b.pop_condition();
    b.bit_invert(m[0]);
}

/// One UNREN-COND block under `conds`: chain p_0..p_(jt-1) (measured uncompute), Z on p_j for j in `zs`, z_if on the
/// listed (j, bit) pairs (bits read before any inversion), and p_jt's phase as CZ(p_(jt-1), z_jt).
fn unren_block(b: &mut B, x: &[QubitId], act: Option<QubitId>, jt: usize, zs: &[usize], zifs: &[(usize, BitId)],
               conds: &[BitId], gate: GateSpec) {
    for &c in conds { b.push_condition(c); }
    // MARKER_FREE: the phases sit on p'_j = p_j & [LA > j] (j >= gmin): Z -> CZ(p_j, g_j), z_if -> CZ under the bit,
    // and p'_jt = p_(jt-1) & z_jt & g_jt through one logical AND
    let gmin = gate.map_or(7, |g| g.2);
    let lg = gate.map(|(la, hb, gmin)| {
        let mut is: Vec<usize> = zs.to_vec();
        is.extend(zifs.iter().map(|z| z.0));
        is.push(jt);
        LaGate::build(b, la, hb, gate_need(gmin, &is))
    });
    let z: Vec<QubitId> = (0..=jt).map(|i| x[W - 1 - i]).collect();
    for &q in &z { b.x(q); }
    // p_j for j < jt; act None makes p_0 the lane z_0 itself
    let mut p: Vec<QubitId> = vec![];
    let mut fresh: Vec<QubitId> = vec![];
    for j in 0..jt {
        let prev = if j == 0 { act } else { Some(p[j - 1]) };
        match prev {
            Some(a) => {
                let t = b.alloc();
                b.and_c(a, z[j], t);
                fresh.push(t);
                p.push(t);
            }
            None => p.push(z[0]),
        }
    }
    for &j in zs {
        if j < gmin {
            b.z(p[j]);
        } else {
            let (q, ng) = lg.as_ref().unwrap().g(j);
            if ng { b.x(q); }
            b.cz(p[j], q);
            if ng { b.x(q); }
        }
    }
    for &(j, bit) in zifs {
        if j < gmin {
            b.z_if(p[j], bit);
        } else {
            let (q, ng) = lg.as_ref().unwrap().g(j);
            if ng { b.x(q); }
            b.push_condition(bit);
            b.cz(p[j], q);
            b.pop_condition();
            if ng { b.x(q); }
        }
    }
    // p_jt = p_(jt-1) & z_jt (& g_jt)
    if !(jt == 3 && cr_break(1)) {
        if jt < gmin {
            b.cz(p[jt - 1], z[jt]);
        } else {
            let pj = p[jt - 1];
            with_and(b, z[jt], lg.as_ref().unwrap().g(jt), |b, t| b.cz(pj, t));
        }
    }
    if let Some(lg) = lg { lg.unbuild(b); }
    for j in (0..jt).rev() {
        let prev = if j == 0 { act } else { Some(p[j - 1]) };
        if let Some(a) = prev { b.and_u(a, z[j], p[j]); }
    }
    b.free_n(&fresh);
    for &q in &z { b.x(q); }
    for _ in conds { b.pop_condition(); }
}

impl GreedyFrog {
    /// The DONE counter c lives complemented in Y lanes 0..CNT_BITS: a finished shot's Y is the constant
    /// (B = 1, marker, tA = p), whose lowest lanes hold p's top bits (all ones), so c = !Y[0..8] with c = 0 at the
    /// finish; active shots never touch it.
    pub fn with_cnt(mut self) -> GreedyFrog {
        self.cnt = self.y[..CNT_BITS].to_vec();
        self
    }
    /// The counter lanes the arithmetic touches (CNT7: lanes 0..7).
    fn cntw(&self) -> &[QubitId] {
        if cnt7() { if mw_break(2) { &self.cnt[1..] } else { &self.cnt[..CNT_BITS - 1] } } else { &self.cnt }
    }
    /// c += ctrl
    fn cnt_inc(&self, b: &mut B, ctrl: QubitId) {
        let anc = b.alloc_n(self.cntw().len() - 1);
        super::arith::dec(b, ctrl, self.cntw(), &anc);
        b.free_n(&anc);
    }
    /// c -= ctrl
    fn cnt_dec(&self, b: &mut B, ctrl: QubitId) {
        let anc = b.alloc_n(self.cntw().len() - 1);
        super::arith::inc(b, ctrl, self.cntw(), &anc);
        b.free_n(&anc);
    }
    /// out ^= [c == 0] (all counter lanes one)
    fn cnt_zero_into(&self, b: &mut B, out: QubitId) {
        let lits: Vec<(QubitId, bool)> = self.cntw().iter().map(|&q| (q, false)).collect();
        and_into(b, &lits, out);
    }

    pub fn alloc(b: &mut B) -> GreedyFrog {
        GreedyFrog { x: b.alloc_n(W), y: b.alloc_n(W), la: b.alloc_n(LB_BITS), lb: b.alloc_n(LB_BITS),
              dirty: b.alloc_n(TEST_DIRTY),
              cap: std::env::var("GREEDYFROG_TEST_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(u64::MAX),
              cnt: vec![], par: b.alloc() }.with_cnt()
    }

    /// sw ^= act & [LA != 0] & X[W-1] & (LA < LB | LA == LB & Y top > X top)   (F9). The top compare is unmasked even
    /// when LB < WC: with LA == LB the values differ inside their top LB lanes unless A' == B, and A' == B forces
    /// B = gcd = 1, so LB == 1 is excluded instead (A' == B == 1 never swaps).
    /// sw ^= F9 (out None: the phase (-1)^F9, for a measured erase). The temporaries are erased by measurement.
    fn swap_flag(&self, b: &mut B, z0: Option<QubitId>, out: Option<QubitId>, w: &Win) {
        let lt = b.alloc();
        let eq = b.alloc();
        let cmp = b.alloc();
        let nz = b.alloc();
        if !swf_lex() {
            lt_sm(b, self, &self.la, &self.lb, Some(lt));
            eq_auto(b, self, &self.la, &self.lb, eq);
        }
        let cmp_into = |b: &mut B, u: &GreedyFrog, cmp: Option<QubitId>| {
            let t: Vec<QubitId> = u.x[W - wc()..].to_vec();
            let s: Vec<QubitId> = u.y[W - wc()..].to_vec();
            let c0 = b.alloc();
            let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
            if w.lb.0 <= 1 {
                let ne1 = b.alloc();
                and_auto(b, u, &eq_lits(&u.lb, 1), ne1);
                b.x(ne1);
                let pool = pool_for(b, u, wc(), 0);
                plain_compare(b, &t, &s, c0, &sc, cmp, Some((ne1, false)), &pool);
                b.free_n(&pool);
                b.x(ne1);
                and_auto(b, u, &eq_lits(&u.lb, 1), ne1);
                b.free(ne1);
            } else {
                let pool = pool_for(b, u, wc(), 0);
                plain_compare(b, &t, &s, c0, &sc, cmp, None, &pool);
                b.free_n(&pool);
            }
            b.free(c0);
        };
        if swf_lex() {
            // SWF-LEX: core = lt | eq & cmp = [LA < LB + cmp] (cmp = [Ytop > Xtop] as the 9-bit compare's carry-in)
            b.free_n(&[lt, eq]);
            let core = b.alloc();
            cmp_into(b, self, Some(cmp));
            lt_cin_sm(b, self, &self.la, &self.lb, cmp, Some(core));
            zero_auto(b, self, &self.la, nz); // nz = [LA == 0]
            let mut lits: Vec<(QubitId, bool)> = if swf_nz() { vec![] } else { z0.map(|z| vec![(z, true)]).unwrap_or_default() };
            if !(swf_nz() && mw_break(1)) { lits.push((nz, true)); }
            lits.extend([(self.x[W - 1], false), (core, false)]);
            match out {
                Some(sw) => and_auto(b, self, &lits, sw),
                None => phase_and(b, &lits),
            }
            let zl: Vec<(QubitId, bool)> = self.la.iter().map(|&q| (q, true)).collect();
            erase_and(b, self, nz, &zl);
            erase_mbu(b, core, |b| lt_cin_sm(b, self, &self.la, &self.lb, cmp, None));
            erase_mbu(b, cmp, |b| cmp_into(b, self, None));
            b.free_n(&[core, cmp, nz]);
            return;
        }
        cmp_into(b, self, Some(cmp));
        zero_auto(b, self, &self.la, nz); // nz = [LA == 0]
        // sw ^= !z0 & !nz & X[W-1] & (lt | eq & cmp)  (no swap while renormalisation lanes are still owed)
        let ec = b.alloc();
        b.and_c(eq, cmp, ec);
        let or = b.alloc();
        // or = lt | ec = !(!lt & !ec)
        b.x(lt);
        b.x(ec);
        b.and_c(lt, ec, or);
        b.x(or);
        b.x(ec);
        b.x(lt);
        let mut lits: Vec<(QubitId, bool)> = z0.map(|z| vec![(z, true)]).unwrap_or_default();
        lits.extend([(nz, true), (self.x[W - 1], false), (or, false)]);
        match out {
            Some(sw) => and_auto(b, self, &lits, sw),
            None => phase_and(b, &lits),
        }
        b.x(lt);
        b.x(ec);
        b.x(or);
        b.and_u(lt, ec, or);
        b.x(ec);
        b.x(lt);
        b.free(or);
        b.and_u(eq, cmp, ec);
        b.free(ec);
        let zl: Vec<(QubitId, bool)> = self.la.iter().map(|&q| (q, true)).collect();
        erase_and(b, self, nz, &zl);
        erase_mbu(b, cmp, |b| cmp_into(b, self, None));
        for i in 0..LB_BITS {
            b.cx(self.lb[i], self.la[i]);
        }
        erase_and(b, self, eq, &zl);
        for i in 0..LB_BITS {
            b.cx(self.lb[i], self.la[i]);
        }
        erase_mbu(b, lt, |b| lt_sm(b, self, &self.la, &self.lb, None));
        b.free_n(&[lt, eq, cmp, nz]);
    }

    /// One forward slot (F1..F11). Returns the measurement record.
    pub fn fwd_slot(&mut self, b: &mut B, w: &Win) -> SlotBits {
        super::mask::set_borrowed(&self.dirty);
        prof(b, "f.z0");
        p3(b, self, "f.z0");
        // F1
        // FWD-ACT-CONST (B-CRUMBS, ST-001): on slots where no shot can have finished (the inverse's act_const), act = 1
        // classically: no done flag, no counter increment, no flag erase (the inverse already skips them there)
        let zo = if fwd_act_const() && w.act_const { None } else { Some(b.alloc()) };
        if let Some(z0) = zo {
            zero_into(b, &self.la, z0);
            self.cnt_inc(b, z0);
        }
        // a1 = act & X[W-1]: the slot steps (else it is a stall that only renormalises, or finished)
        let a1 = b.alloc();
        match zo {
            Some(z0) => {
                b.x(z0);
                b.ccx(z0, self.x[W - 1], a1);
                b.x(z0);
            }
            None => b.cx(self.x[W - 1], a1),
        }
        prof(b, "f.dcmp");
        p3(b, self, "f.dcmp");
        // F2: d = a1 & [B > A >> e] (top window)
        let d = b.alloc();
        mark_msb(b, a1, &self.lb);
        top_compare(b, self, Some(d), w, Some((a1, false)));
        mark_msb(b, a1, &self.lb);
        prof(b, "f.drot");
        p3(b, self, "f.drot");
        // F3
        crot_up(b, d, &self.x, 1);
        prof(b, "f.value");
        p3(b, self, "f.value");
        // F4: value chain, subtract where a1
        if let Some(z0) = zo { b.x(z0); } // z0 now holds act
        let act = zo;
        let mwa = masked_write_always();
        mark_done_inv(b, act, &self.lb);
        if mwa { mark_stall(b, act, a1, &self.lb); }
        let pk = act.and_then(|a| act_park(b, a, &self.lb, w.lb));
        let rv = value_pass(b, self, w, true, a1, None, mwa, None);
        if let Some(a) = act { act_unpark(b, a, &self.lb, pk); }
        if mwa { mark_stall(b, act, a1, &self.lb); }
        mark_done_inv(b, act, &self.lb);
        prof(b, "f.cof");
        p3(b, self, "f.cof");
        // F5: LA -= d; cofactor chain, add where a1
        {
            let anc = b.alloc_n(LB_BITS - 1);
            super::arith::dec(b, d, &self.la, &anc);
            b.free_n(&anc);
        }
        mark_done_inv(b, act, &self.la);
        if mwa { mark_stall(b, act, a1, &self.la); }
        let pk = act.and_then(|a| act_park(b, a, &self.la, w.lad));
        let mut rc = RollRec::default();
        if lane0_direct() {
            // x0 = X[0] here (F4 cleared A's wrapped MSB where d = 1)
            let m = Masked::alloc_ladder_w(b, w.lad.1);
            let (t, s) = cof_ladder(self, w, self.x[0]);
            let src = cof_src(self, &m, w);
            if roll_cof() {
                rc = cof_roll_fwd(b, &t, &s, src, &m, a1, mwa, w.a1_const);
            } else {
                let pool = pool_for(b, self, t.len() - (w.lad.1 - w.lad.0 + 1), 0);
                masked_pass(b, self, &t, &s, src, &m, false, Some(a1), None, &pool, mwa, w.a1_const, None);
                b.free_n(&pool);
            }
            m.free(b);
        } else {
            let m = Masked::alloc_ladder_w(b, w.lad.1);
            let x0 = b.alloc();
            lane0_src(b, self, d, x0);
            let (t, s) = cof_ladder(self, w, x0);
            let src = cof_src(self, &m, w);
            // carry pool over the ordinary lanes below the LA - d window
            if roll_cof() {
                rc = cof_roll_fwd(b, &t, &s, src, &m, a1, mwa, w.a1_const);
            } else {
                let pool = pool_for(b, self, t.len() - (w.lad.1 - w.lad.0 + 1), 0);
                masked_pass(b, self, &t, &s, src, &m, false, Some(a1), None, &pool, mwa, w.a1_const, None);
                b.free_n(&pool);
            }
            lane0_src(b, self, d, x0);
            b.free(x0);
            m.free(b);
        }
        if let Some(a) = act { act_unpark(b, a, &self.la, pk); }
        if mwa { mark_stall(b, act, a1, &self.la); }
        mark_done_inv(b, act, &self.la);
        // EARLY-GHOST (B-PORT3): d and a1 are not touched again in this slot, so their X-measurements move here (the
        // forward's F11 ghosting commutes with F6-F10), and their lanes are free through the renormalisation and the swap
        let eg = early_ghost();
        let (bd, ba) = (b.fresh_bits(1)[0], b.fresh_bits(1)[0]);
        if eg {
            // negative control for the gate tests only: P3_BREAK=6 kicks d's phase into a1 before the measurements
            if cfg!(test) && std::env::var("P3_BREAK").map_or(false, |x| x.trim() == "6") {
                b.cx(d, a1);
            }
            b.hmr_to(d, bd);
            b.hmr_to(a1, ba);
            b.free(d);
            b.free(a1);
        }
        prof(b, "f.renorm");
        p3(b, self, "f.renorm");
        // F6, F7, F8 (every active shot: a step's renormalisation, or a stall's)
        let r = b.alloc_n(RHO_BITS);
        renorm_top(b, &self.x, act, &r, gate_spec(&self.la, w));
        if let Some(z0) = zo { b.x(z0); } // back to z0
        add_sm(b, self, &self.la, &r, false, true);
        let br = b.fresh_bits(RHO_BITS);
        if eg {
            // EARLY-GHOST: r is not touched again either
            for i in 0..RHO_BITS {
                b.hmr_to(r[i], br[i]);
            }
            b.free_n(&r);
        }
        prof(b, "f.swap");
        p3(b, self, "f.swap");
        // F9, F10
        let sw = b.alloc();
        self.swap_flag(b, zo, Some(sw), w);
        super::arith::cswap_regs(b, sw, &self.x, &self.y);
        super::arith::cswap_regs(b, sw, &self.la, &self.lb);
        b.cx(sw, self.par);
        prof(b, "f.ghost");
        p3(b, self, "f.ghost");
        // F11: ghost d, r, sw, a1; erase z0 = [LA == 0] & [cnt != 0]
        let bits = SlotBits { d: bd, r: br, sw: b.fresh_bits(1)[0], a1: ba, rv, rc };
        if !eg {
            b.hmr_to(d, bits.d);
            for i in 0..RHO_BITS {
                b.hmr_to(r[i], bits.r[i]);
            }
        }
        b.hmr_to(sw, bits.sw);
        if !eg {
            b.hmr_to(a1, bits.a1);
            b.free(d);
            b.free_n(&r);
        }
        b.free(sw);
        if !eg {
            b.free(a1);
        }
        // z0 = [LA == 0] & [cnt != 0] erased by measurement: the repair computes both zero tests, applies the CZ and
        // erases the tests by measurement in turn
        if let Some(z0) = zo { erase_mbu(b, z0, |b| {
            let cl: Vec<(QubitId, bool)> = self.cntw().iter().map(|&q| (q, false)).collect();
            let zl: Vec<(QubitId, bool)> = self.la.iter().map(|&q| (q, true)).collect();
            let cz = b.alloc();
            and_auto(b, self, &cl, cz); // cz = [cnt == 0]
            let lz = b.alloc();
            and_auto(b, self, &zl, lz);
            phase_and(b, &[(lz, false), (cz, true)]);
            erase_and(b, self, lz, &zl);
            erase_and(b, self, cz, &cl);
            b.free(lz);
            b.free(cz);
        });
        b.free(z0); }
        prof(b, "end");
        p3(b, self, "end");
        bits
    }
}


// ------------------------------------------------------------------ inverse slot (decode + undo)

/// window bits of the decode (cofactor top bits kept after normalisation)
pub const NB: usize = 28;
/// division rows (capacity; per-slot counts come from the envelope)
pub const KROWS: usize = 21;
/// Offset of the divisor-length register while the decode's masks run: LA holds u' = LA + sX - UOFF, so the divisor's
/// bit length is mX = NB - u'. Mask-relevant shots have u' in [0, NB] (bits 0..5); u' < 0 (bit 8) means mX > NB.
const UOFF: usize = CW - NB;

/// The masks' 6-bit view of u': bits 0..4 and the sign bit (values below 32 match only shots with u' >= 0; active
/// shots have u' = NB - mX <= NB - 1).
fn ubits(la: &[QubitId]) -> Vec<QubitId> {
    let mut v = la[..5].to_vec();
    v.push(la[LB_BITS - 1]);
    v
}

/// Bottom-normalise a ring's cofactor window by binary search: for k = 4..0, s_k ^= [lanes 0..2^k all zero], then the
/// lanes shift down by 2^k where s_k. Funnel: stage k swaps (i, i + 2^k) for i < NB + 2^k - 1 only (the lanes the
/// window still needs), a rotation of lanes 0 .. NB + 2^(k+1) - 2. s fresh |0>; slack <= 31.
fn norm_bottom(b: &mut B, u: &GreedyFrog, ring: &[QubitId], s: &[QubitId], act: Option<QubitId>) {
    if funnel_rev() {
        return rev_funnel(b, u, ring, s, act, true);
    }
    for k in (0..R_BITS).rev() {
        let n = 1usize << k;
        let mut lits: Vec<(QubitId, bool)> = (0..n).map(|i| (ring[i], true)).collect();
        lits.extend(act_lits(act));
        and_auto(b, u, &lits, s[k]);
        for i in 0..NB + n - 1 {
            b.cswap(s[k], ring[i], ring[i + n]);
        }
    }
}

/// FUNNEL-REV gate list (norm order); denorm emits it reversed with each test turned into its erasure.
enum FOp {
    /// cswap(control, lane, lane)
    Sw(QubitId, usize, usize),
    /// cx(control, target)
    Cx(QubitId, QubitId),
    /// s[j] ^= AND(lanes 0..2^j all zero, act)
    Test(usize),
}

/// FUNNEL-REV (variant A, frame tests): see `FUNNEL_REV`. `fwd` = norm (computes s), else denorm (erases s).
fn rev_funnel(b: &mut B, u: &GreedyFrog, ring: &[QubitId], s: &[QubitId], act: Option<QubitId>, fwd: bool) {
    let k = R_BITS;
    let c = |j: usize| NB - 1 + (1usize << j) - 1;
    let mut ops: Vec<FOp> = Vec::with_capacity(160);
    // step k: s_(k-1) = [lanes 0..2^(k-1) zero], Rev(c_k) under s_(k-1)
    ops.push(FOp::Test(k - 1));
    let ck = c(k);
    for i in 0..(ck + 1) / 2 {
        ops.push(FOp::Sw(s[k - 1], i, ck - i));
    }
    // steps j = k-1..1: Rev(c_j) under s_j ^ s_(j-1); the first 2^(j-1) pairs are split around the test of s_(j-1)
    for j in (1..k).rev() {
        let (n, cj) = (1usize << (j - 1), c(j));
        for i in 0..n {
            ops.push(FOp::Sw(s[j], i, cj - i));
        }
        ops.push(FOp::Test(j - 1));
        for i in 0..n {
            ops.push(FOp::Sw(s[j - 1], i, cj - i));
        }
        ops.push(FOp::Cx(s[j - 1], s[j]));
        for i in n..(cj + 1) / 2 {
            ops.push(FOp::Sw(s[j], i, cj - i));
        }
        ops.push(FOp::Cx(s[j - 1], s[j]));
    }
    // step 0: Rev(c_0) under s_0 (FUNNEL_BREAK=1 drops it both ways, =2 in denorm only)
    if !(funnel_break(1) || (funnel_break(2) && !fwd)) {
        let c0 = c(0);
        for i in 0..(c0 + 1) / 2 {
            ops.push(FOp::Sw(s[0], i, c0 - i));
        }
    }
    let lits = |j: usize| -> Vec<(QubitId, bool)> {
        let mut l: Vec<(QubitId, bool)> = (0..1usize << j).map(|i| (ring[i], true)).collect();
        l.extend(act_lits(act));
        l
    };
    let emit = |b: &mut B, op: &FOp| match *op {
        FOp::Sw(q, x, y) => b.cswap(q, ring[x], ring[y]),
        FOp::Cx(q, t) => b.cx(q, t),
        FOp::Test(j) => {
            if fwd { and_auto(b, u, &lits(j), s[j]) } else { erase_and(b, u, s[j], &lits(j)) }
        }
    };
    if fwd {
        for op in &ops {
            emit(b, op);
        }
    } else {
        for op in ops.iter().rev() {
            emit(b, op);
        }
    }
}

/// Inverse of norm_bottom (erases s).
fn denorm_bottom(b: &mut B, u: &GreedyFrog, ring: &[QubitId], s: &[QubitId], act: Option<QubitId>) {
    if funnel_rev() {
        return rev_funnel(b, u, ring, s, act, false);
    }
    for k in 0..R_BITS {
        let n = 1usize << k;
        for i in (0..NB + n - 1).rev() {
            b.cswap(s[k], ring[i], ring[i + n]);
        }
        let mut lits: Vec<(QubitId, bool)> = (0..n).map(|i| (ring[i], true)).collect();
        lits.extend(act_lits(act));
        erase_and(b, u, s[k], &lits);
    }
}

/// |0> scratch of the division rows and the last-row sweep (allocated outside their recordings). The sweep's running
/// OR f and one-hot y are |0> while rows run, so they double as the rows' carry-in and top-lane zero source; masked
/// rows lend their idle mask-decoder prefix to the sweep's jl.
struct RowTmp {
    /// sign lane above Y lane 0 (row 0's result)
    s0: QubitId,
    /// act & [kt >= j] while the sweep visits row j
    g: QubitId,
    f: QubitId,
    y: QubitId,
    jl: Vec<QubitId>,
    m: Option<Masked>,
}

impl RowTmp {
    fn alloc(b: &mut B, masked: bool) -> RowTmp {
        let (s0, g, y) = (b.alloc(), b.alloc(), b.alloc());
        if masked {
            let m = Masked::alloc_small_on(b, g);
            RowTmp { s0, g, f: m.c0, y, jl: m.pre[..R_BITS].to_vec(), m: Some(m) }
        } else {
            RowTmp { s0, g, f: b.alloc(), y, jl: b.alloc_n(R_BITS), m: None }
        }
    }
    /// PARK-SPLIT: the rows' lanes only (s0, carry-in f, zero source y); the sweep's g and jl are taken by `attach`.
    fn alloc_slim(b: &mut B) -> RowTmp {
        let (s0, f, y) = (b.alloc(), b.alloc(), b.alloc());
        RowTmp { s0, g: NOQ, f, y, jl: vec![], m: None }
    }
    fn attach(&mut self, b: &mut B) {
        assert!(self.m.is_none() && self.g == NOQ);
        self.g = b.alloc();
        self.jl = b.alloc_n(R_BITS);
    }
    /// g and jl are |0> again after the backward sweep
    fn detach(&mut self, b: &mut B) {
        zero_probe(b, &[self.g]);
        zero_probe(b, &self.jl);
        b.free(self.g);
        b.free_n(&self.jl);
        self.g = NOQ;
        self.jl.clear();
    }
    fn free(self, b: &mut B) {
        b.free_n(&[self.s0, self.y]);
        match self.m {
            // the mask scratch's AND temp is g
            Some(m) => m.free(b),
            None => {
                if self.g != NOQ {
                    b.free(self.g);
                }
                b.free(self.f);
                b.free_n(&self.jl);
            }
        }
    }
    /// carry-in of the rows' adders
    fn c0(&self) -> QubitId {
        self.f
    }
    /// source of each row's top lane (D_j's sign extension)
    fn zero(&self) -> QubitId {
        self.y
    }
    /// rem lane i (i = -1 is s0)
    fn rem(&self, u: &GreedyFrog, i: isize) -> QubitId {
        if i < 0 { self.s0 } else { u.y[i as usize] }
    }
}

/// Junk parking for slots whose divisor cofactor can be shorter than the window: swap the normalised X window's lanes
/// l >= mX (the marker and A's low bits above the divisor cofactor) with the |0> lanes z[l - lo], lo = the window's
/// smallest mX, so that every division row runs as a plain ladder on a zero-padded divisor (whose lanes below the
/// divisor's LSB add 0 and pass the carry: the same arithmetic as the masked rows). LA holds u' (mX = NB - u').
/// Self-inverse: called again with X's window and u' unchanged, it swaps the lanes back. The flag f toggles where
/// u' == NB - l, read off the complemented 6-bit view of u' by a one-hot scan, and is cleared at the end.
fn park_junk(b: &mut B, u: &GreedyFrog, w: &Win, z: &[QubitId], top: usize) {
    let lo = park_lo(w);
    let v = ubits(&u.la);
    for &q in &v {
        b.x(q);
    }
    let f = b.alloc();
    let pre = b.alloc_n(v.len() - 1);
    // !v == l + 63 - NB  <=>  u'_5 == NB - l with sign 0
    super::mask::onehot_scan(b, &v, &pre, lo, top, 63 - NB as isize, |b, l, o| {
        b.cx(o, f);
        b.cswap(f, u.x[l], z[l - lo]);
    });
    b.free_n(&pre);
    for &q in &v {
        b.x(q);
    }
    // f = [lo <= mX <= top - 1] = [NB - top + 1 <= u' <= NB - lo] (u' >= 0)
    ge_auto(b, u, &v, (NB - top + 1) as isize, f);
    ge_auto(b, u, &v, (NB - lo + 1) as isize, f);
    b.free(f);
}

/// placeholder for a RowTmp lane not held (PARK-SPLIT)
const NOQ: QubitId = QubitId(u64::MAX);

/// PARK-SPLIT: `park_junk` (same gates) with f, the decoder prefix and the comparators' chain on the given |0> lanes
/// first, the rest taken from the room.
fn park_junk_t(b: &mut B, u: &GreedyFrog, w: &Win, z: &[QubitId], top: usize, tmp: &[QubitId]) {
    let lo = park_lo(w);
    let v = ubits(&u.la);
    let need = v.len();
    let extra = b.alloc_n(need.saturating_sub(tmp.len()));
    let lanes: Vec<QubitId> = tmp.iter().chain(&extra).copied().take(need).collect();
    let (f, pre) = (lanes[0], &lanes[1..]);
    for &q in &v {
        b.x(q);
    }
    super::mask::onehot_scan(b, &v, pre, lo, top, 63 - NB as isize, |b, l, o| {
        b.cx(o, f);
        b.cswap(f, u.x[l], z[l - lo]);
    });
    for &q in &v {
        b.x(q);
    }
    super::mask::ge_const(b, &v, (NB - top + 1) as isize, f, pre);
    super::mask::ge_const(b, &v, (NB - lo + 1) as isize, f, pre);
    b.free_n(&extra);
}

/// PARK-SPLIT 4-lane park (tmp = f + 3 decoder lanes, |0> in and out): the lane map of `park_junk` (X lane l <-> z[l - lo]
/// for l in [lo, top), l >= mX). `fwd` (z |0> on entry) sets f = [lo <= mX < top] on a chain of z lanes, then for l
/// descending swaps under f and toggles f off at l == mX, so f ends 0; the inverse (`!fwd`, z |0> on exit) runs l
/// ascending (toggle, then swap) and clears f with the same comparators on z's chain. Toggle f ^= [u' == NB - l]:
/// retained pa = !sign & [u'_4 u'_3 match], pb = pa & [u'_2 match]; per value t = pb & [u'_1 match], f ^= t & [u'_0 match].
fn park_slim(b: &mut B, u: &GreedyFrog, w: &Win, z: &[QubitId], top: usize, tmp: &[QubitId], fwd: bool) {
    let lo = park_lo(w);
    let v = ubits(&u.la);
    assert!(tmp.len() >= 4 && z.len() >= v.len() - 1, "park_slim lanes");
    let (f, pa, pb, t) = (tmp[0], tmp[1], tmp[2], tmp[3]);
    let chain: Vec<QubitId> = z[..v.len() - 1].to_vec();
    let cmp = |b: &mut B| {
        super::mask::ge_const(b, &v, (NB - top + 1) as isize, f, &chain);
        super::mask::ge_const(b, &v, (NB - lo + 1) as isize, f, &chain);
    };
    // literal of bit i of val (i = 5: the sign, always 0 for the scanned values)
    let lit = |i: usize, val: usize| -> (QubitId, bool) { (v[i], i < 5 && (val >> i) & 1 == 1) };
    let and2 = |b: &mut B, x: (QubitId, bool), y: (QubitId, bool), t: QubitId, undo: bool| {
        if !x.1 { b.x(x.0); }
        if !y.1 { b.x(y.0); }
        if undo { b.and_u(x.0, y.0, t) } else { b.and_c(x.0, y.0, t) }
        if !y.1 { b.x(y.0); }
        if !x.1 { b.x(x.0); }
    };
    let pa_set = |b: &mut B, val: usize, undo: bool| {
        and2(b, lit(5, val), lit(4, val), t, false);
        and2(b, (t, true), lit(3, val), pa, undo);
        and2(b, lit(5, val), lit(4, val), t, true);
    };
    let pb_set = |b: &mut B, val: usize, undo: bool| and2(b, (pa, true), lit(2, val), pb, undo);
    let mut cur: Option<usize> = None;
    let mut toggle = |b: &mut B, val: usize| {
        match cur {
            None => {
                pa_set(b, val, false);
                pb_set(b, val, false);
            }
            Some(c) if c >> 3 != val >> 3 => {
                pb_set(b, c, true);
                pa_set(b, c, true);
                pa_set(b, val, false);
                pb_set(b, val, false);
            }
            Some(c) if (c >> 2) & 1 != (val >> 2) & 1 => b.cx(pa, pb),
            _ => {}
        }
        cur = Some(val);
        and2(b, (pb, true), lit(1, val), t, false);
        let (q0, p0) = lit(0, val);
        if !p0 { b.x(q0); }
        b.ccx(t, q0, f);
        if !p0 { b.x(q0); }
        and2(b, (pb, true), lit(1, val), t, true);
    };
    // negative control for the gate tests only (W2_BREAK_SPLIT=2 drops the toggle at l == lo: the shortest divisors
    // mX == lo keep junk)
    let brk = cfg!(test) && std::env::var("W2_BREAK_SPLIT").map_or(false, |v| v.trim() == "2");
    if fwd {
        cmp(b);
        for l in (lo..top).rev() {
            b.cswap(f, u.x[l], z[l - lo]);
            if !(brk && l == lo) {
                toggle(b, NB - l);
            }
        }
    } else {
        for l in lo..top {
            if !(brk && l == lo) {
                toggle(b, NB - l);
            }
            b.cswap(f, u.x[l], z[l - lo]);
        }
    }
    if let Some(c) = cur {
        pb_set(b, c, true);
        pa_set(b, c, true);
    }
    if !fwd {
        cmp(b);
    }
}

/// REPARK-X0 5-lane park (tmp = f + 4 decoder lanes, |0> in and out): `park_slim`'s order and comparators (on z's
/// chain: before the scan when `fwd`, z |0> on entry; after it otherwise) with `park_junk_t`'s retained decoder minus its
/// bit-0 level: o = [!u'_(1..6) == (l + 63 - NB) >> 1] on 4 prefix lanes, f ^= o & [bit-0 literal] by one CCX.
fn park_mid(b: &mut B, u: &GreedyFrog, w: &Win, z: &[QubitId], top: usize, tmp: &[QubitId], fwd: bool) {
    let lo = park_lo(w);
    let v = ubits(&u.la);
    assert!(tmp.len() >= v.len() - 1 && z.len() >= v.len() - 1, "park_mid lanes");
    let (f, pre) = (tmp[0], &tmp[1..v.len() - 1]);
    let chain: Vec<QubitId> = z[..v.len() - 1].to_vec();
    let cmp = |b: &mut B| {
        super::mask::ge_const(b, &v, (NB - top + 1) as isize, f, &chain);
        super::mask::ge_const(b, &v, (NB - lo + 1) as isize, f, &chain);
    };
    let brk = mw_break(8);
    if fwd {
        cmp(b);
    }
    for &q in &v {
        b.x(q);
    }
    let ls: Vec<usize> = if fwd { (lo..top).rev().collect() } else { (lo..top).collect() };
    // !v == l + 63 - NB  <=>  u' == NB - l with sign 0
    super::mask::onehot_scan_hi(b, &v, pre, &ls, 63 - NB as isize, |b, l, o, q0, one| {
        let tog = |b: &mut B| {
            if brk {
                b.cx(o, f);
                return;
            }
            if !one { b.x(q0); }
            b.ccx(o, q0, f);
            if !one { b.x(q0); }
        };
        if fwd {
            b.cswap(f, u.x[l], z[l - lo]);
            tog(b);
        } else {
            tog(b);
            b.cswap(f, u.x[l], z[l - lo]);
        }
    });
    for &q in &v {
        b.x(q);
    }
    if !fwd {
        cmp(b);
    }
}

/// PARK-SPLIT repark / unpark: `park_junk_t` where tmp + room give its 6 lanes, else the 4-lane `park_slim`.
fn park_split_pass(b: &mut B, u: &GreedyFrog, w: &Win, z: &[QubitId], top: usize, tmp: &[QubitId], fwd: bool) {
    let need = ubits(&u.la).len();
    // negative control for the gate tests only (W2_BREAK_SPLIT=1: the repark leaves the top junk lane in X)
    let top = if cfg!(test) && fwd && std::env::var("W2_BREAK_SPLIT").map_or(false, |v| v.trim() == "1") { top - 1 } else { top };
    let room = u.room(b);
    if rowlog() {
        eprintln!("WL_PSP fwd {} tmp {} room {} need {} junk_t {}", fwd as u8, tmp.len(), room, need,
                  (!slim_all() && tmp.len() + room + psp_give() >= need) as u8);
    }
    if !slim_all() && !mid_all() && tmp.len() + room + psp_give() >= need {
        park_junk_t(b, u, w, z, top, tmp);
    } else if !slim_all() && repark_x0() && tmp.len() + room >= need - 1 {
        // REPARK-X0: one lane short of park_junk_t
        let extra = b.alloc_n((need - 1).saturating_sub(tmp.len()));
        let lanes: Vec<QubitId> = tmp.iter().chain(&extra).copied().take(need - 1).collect();
        park_mid(b, u, w, z, top, &lanes, fwd);
        b.free_n(&extra);
    } else {
        let extra = b.alloc_n(4usize.saturating_sub(tmp.len()));
        let lanes: Vec<QubitId> = tmp.iter().chain(&extra).copied().take(4).collect();
        park_slim(b, u, w, z, top, &lanes, fwd);
        b.free_n(&extra);
    }
}

/// PARTIAL-PARK: as `park_junk`, over the top lanes [lo_p, top) only: f starts at [0 <= u', mX < lo_p] (every parked
/// lane is junk there), toggles on at l == mX inside the range, and ends at [0 <= u', mX < top]. Self-inverse.
fn park_junk_partial(b: &mut B, u: &GreedyFrog, z: &[QubitId], top: usize, lo_p: usize) {
    let v = ubits(&u.la);
    let f = b.alloc();
    // negative control for the gate tests only (W2_BREAK_PARTIAL=1 drops the start flag: short divisors keep junk)
    let brk = cfg!(test) && std::env::var_os("W2_BREAK_PARTIAL").is_some();
    // [k <= u' <= 31] on the 6-bit view (u' < 0 reads as >= 32)
    if !brk {
        ge_auto(b, u, &v, (NB - lo_p + 1) as isize, f);
        ge_auto(b, u, &v, 32, f);
    }
    for &q in &v {
        b.x(q);
    }
    let pre = b.alloc_n(v.len() - 1);
    super::mask::onehot_scan(b, &v, &pre, lo_p, top, 63 - NB as isize, |b, l, o| {
        b.cx(o, f);
        b.cswap(f, u.x[l], z[l - lo_p]);
    });
    b.free_n(&pre);
    for &q in &v {
        b.x(q);
    }
    ge_auto(b, u, &v, (NB - top + 1) as isize, f);
    ge_auto(b, u, &v, 32, f);
    if brk {
        ge_auto(b, u, &v, (NB - lo_p + 1) as isize, f);
        ge_auto(b, u, &v, 32, f);
    }
    b.free(f);
}

/// Non-restoring division rows on the normalised windows: rem = Y[0..NB) (MSB at lane 0, sign lane s0 above it) and
/// div = X[0..NB). LA holds u = LA + sX (the divisor's bit length is mX = W - 1 - u). Row j (j < w.k), with
/// D_j = div >> j: r_{j+1} = r_j - D_j where r_j >= 0, r_j + D_j where r_j < 0, computed mod 2^(NB - j + 1) over rem
/// lanes j-1 .. NB-1. |r_{j+1}| <= D_j < 2^(NB - j), so r_{j+1}'s sign lands in lane j - 1 and the quotient bit is
/// q_j = [r_{j+1} >= 0] = !lane(j - 1); r_j's sign (lane j - 2, r_0 >= 0) picks the sign of the step and stays put.
/// Rows whose window has an active mX < NB - j + 1 are masked so they start at the divisor's LSB lane mX + j - 1
/// (rem's lower bits are untouched there, which is the exact arithmetic). No gating and no allocation: the caller
/// records this and undoes it by playing the recording inverted.
fn division_rows(b: &mut B, u: &GreedyFrog, w: &Win, rt: &RowTmp, pool: &[QubitId], parked: bool, top: usize,
                 partial: Option<usize>, mut roll: RowRoll) {
    let masked_row = |j: usize| !parked && w.mx < NB - j + 1;
    // ROW-Y: plain rows take their top lane's sign-extension source m from the sign lane itself (or the constant 1)
    let rowy = row_y(rt);
    let sg = u.la[LB_BITS - 1];
    // PARTIAL-PARK: the flag entering a row's masked lanes is big_{max(j, c)}, c = NB - lo_p
    let pc = partial.map(|lo_p| NB - lo_p);
    if let (Some(c), true) = (pc, masked_row(0)) {
        let big = rt.m.as_ref().expect("masked row needs mask scratch").f;
        // big_c = !(!sign & [u'_5 >= c])
        if pool.len() >= 5 {
            let (chain, ge) = (&pool[..4], pool[4]);
            super::mask::ge_const(b, &u.la[..5], c as isize, ge, chain);
            b.x(sg);
            b.ccx(sg, ge, big);
            b.x(sg);
            super::mask::ge_const(b, &u.la[..5], c as isize, ge, chain);
        } else {
            super::mask::ge_const_dirty_gated(b, &u.la[..5], c as isize, big, &[(sg, true)], &u.dirty);
        }
        b.x(big);
    }
    // The masked rows' flag f holds big_j = u'_sign | ![u'_5 >= j] while row j runs (the row pair hands it back
    // unchanged): big_0 = u'_sign, big_j ^ big_(j+1) = !u'_sign & [u'_5 == j], and after the last masked row it is
    // cleared with the comparator. The masked rows are the first ones (j < NB + 1 - mX).
    if masked_row(0) && pc.is_none() {
        b.cx(sg, rt.m.as_ref().expect("masked row needs mask scratch").f);
    }
    for j in 0..w.k {
        let lo = j as isize - 1;
        // PARTIAL-PARK rows stop at lane j + top - 1 (divisor lanes >= top are zero on every non-failing shot)
        let parked = parked || (partial.is_some() && j + top < NB);
        // Parked rows with a divisor bound (top < NB): divisor lanes >= top are zero on every non-failing shot, so rem
        // lanes i >= j + top add a zero source: with the flipped source and carry-in m they stay unchanged and carry m
        // out, which is the ladder's own carry-in c0 = m. The row's ladder therefore stops at lane j + top - 1.
        let hi_i = if parked { (j + top).min(NB) } else { NB } as isize;
        let t: Vec<QubitId> = (lo..hi_i).rev().map(|i| rt.rem(u, i)).collect();
        let mut s: Vec<QubitId> = (lo..hi_i).rev()
            .map(|i| if i >= j as isize { u.x[i as usize - j] } else { rt.zero() }).collect();
        if rowy {
            // the zero source is the last (top) lane's only: it leaves the ladder (written by hand below)
            assert_eq!(s.pop(), Some(rt.zero()));
        }
        // m = 1 subtracts: source ^= m, carry-in m. Row 0 always subtracts; row j >= 1 subtracts where lane j - 2 is 0.
        let sign = if j == 0 { None } else { Some(rt.rem(u, j as isize - 2)) };
        // ROW-F: the carry-in m comes from the sign lane itself (X-flipped: !sign) or, in row 0, from a pool lane set to 1
        let rowf = rowy && row_f();
        let c0f = rt.c0();
        let flip = |b: &mut B| {
            for &q in s.iter().chain((!rowf).then_some(&c0f)) {
                if let Some(sg) = sign {
                    b.cx(sg, q);
                }
                b.x(q);
            }
        };
        flip(b);
        let rolled = match &roll {
            RowRoll::Fwd(_) => !rowy && !masked_row(j) && pool.len() >= 2 && pool.len() < t.len(),
            RowRoll::Rev(recs) => !rowy && !recs[j].rc.is_empty(),
            RowRoll::No => false,
        };
        if rolled && matches!(roll, RowRoll::Fwd(_)) {
            // ROLL-ROWS forward: the row's add as the inverse of its inverted twin (carries of the pre-row remainder,
            // formed on the written lane: the I-frame is the complement), carry-in m held on c0, two pool lanes rolling
            let sc = Mscr { f: rt.c0(), t: rt.c0(), gf: rt.c0(), chain: vec![] };
            let ld = Lad { t: &t, s: &s, c0: rt.c0(), srcs: &[], f0: false, cmpl: true, sc: &sc, g: &[] };
            let rec = super::mask::roll_fwd(b, &ld, ALWAYS, ALWAYS, false, term_nc(), &pool[..2], None);
            if let RowRoll::Fwd(v) = &mut roll { v.push(rec); }
        } else if rowy {
            // ROW-Y rows are not rolled (y / f are lent to the pool; INTEGRATOR: ROW-Y wins on plain rows)
            if let RowRoll::Fwd(v) = &mut roll { v.push(RollRec::default()); }
            // ROW-Y: the ladder over every lane but the top, then the top lane's sum t ^= m ^ c (its carry is discarded
            // mod 2^n, as TERM-NC), m = !sign (row 0: 1); the lane that was the zero source is lent to the pool
            assert!(!masked_row(j) && !pool.is_empty(), "ROW-Y: plain pooled rows only");
            let n = t.len();
            // ROW-F: c0 = the sign lane X-flipped to m = !sign (rows j >= 1), or a pool lane X-flipped to m = 1 (row 0);
            // the pool keeps a lane for ladder lane 0, so the carry-in is only read and holds m throughout
            let (c0, gp): (QubitId, &[QubitId]) = match (rowf, sign) {
                (false, _) => (rt.c0(), pool),
                (true, Some(sg)) => (sg, pool),
                (true, None) => (pool[pool.len() - 1], &pool[..pool.len() - 1]),
            };
            assert!(!rowf || !gp.is_empty(), "ROW-F: lane 0 needs a pool lane");
            if rowf { b.x(c0); }
            let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
            let tt = t[n - 1];
            // ROWY-ROLL forward: the short-pool ROW-Y row as the inverse of its inverted twin (I-frame: the complement)
            let yroll = rowy_roll() && matches!(roll, RowRoll::Fwd(_)) && gp.len() >= 2 && gp.len() < n - 1;
            let yrev = match &roll { RowRoll::Rev(recs) => !recs[j].rc.is_empty(), _ => false };
            if yroll {
                let ldr = Lad { t: &t[..n - 1], s: &s, c0, srcs: &[], f0: false, cmpl: true, sc: &sc, g: &[] };
                let rec = super::mask::roll_fwd(b, &ldr, ALWAYS, ALWAYS, false, false, &gp[..2], Some((ALWAYS, tt)));
                if let RowRoll::Fwd(v) = &mut roll { v.pop(); v.push(rec); }
            }
            let ld = Lad { t: &t[..n - 1], s: &s, c0, srcs: &[], f0: false, cmpl: false, sc: &sc,
                           g: &gp[..gp.len().min(n - 1)] };
            let ru = if yroll { vec![] } else { super::mask::mup_mid(b, &ld) };
            b.play(&ru, false);
            if !yroll { b.cx(top_carry(&ld), tt); }
            // negative control for the gate tests only: P3_BREAK=7 drops the sign term of the top lane
            let brk = cfg!(test) && std::env::var("P3_BREAK").map_or(false, |x| x.trim() == "7");
            if rowf {
                if !brk { b.cx(c0, tt); }
            } else {
                if let Some(sg) = sign {
                    if !brk { b.cx(sg, tt); }
                }
                b.x(tt);
            }
            let rd = match &roll {
                _ if yroll => vec![],
                RowRoll::Rev(recs) if yrev => super::mask::mdown_mid_roll(b, &ld, Some(ALWAYS), &recs[j]),
                _ => super::mask::mdown_mid(b, &ld, Some(ALWAYS)),
            };
            b.play(&rd, false);
            if rowf { b.x(c0); }
        } else if !masked_row(j) && pool.is_empty() {
            assert!(!rolled, "ROLL-ROWS: the inverted rows pass needs a carry pool");
            if let RowRoll::Fwd(v) = &mut roll { v.push(RollRec::default()); }
            let ru = super::arith::up_m(b, &t, &s, rt.c0(), false);
            b.play(&ru, false);
            let rd = super::arith::down_m(b, &t, &s, rt.c0(), super::arith::Dm::Sum, false);
            b.play(&rd, false);
        } else if !masked_row(j) {
            // the same row with logical-AND carries on the pool's lanes (uncomputed by measurement)
            let sc = Mscr { f: rt.c0(), t: rt.c0(), gf: rt.c0(), chain: vec![] };
            let ld = Lad { t: &t, s: &s, c0: rt.c0(), srcs: &[], f0: false, cmpl: false, sc: &sc,
                           g: &pool[..pool.len().min(t.len())] };
            let nc = term_nc();
            let ru = if nc { super::mask::mup_mid_nc(b, &ld) } else { super::mask::mup_mid(b, &ld) };
            b.play(&ru, false);
            let rd = match (&roll, rolled) {
                (RowRoll::Rev(recs), true) => if nc { super::mask::mdown_mid_nc_roll(b, &ld, Some(ALWAYS), &recs[j]) }
                    else { super::mask::mdown_mid_roll(b, &ld, Some(ALWAYS), &recs[j]) },
                _ => if nc { super::mask::mdown_mid_nc(b, &ld, Some(ALWAYS)) } else { super::mask::mdown_mid(b, &ld, Some(ALWAYS)) },
            };
            b.play(&rd, false);
            if let RowRoll::Fwd(v) = &mut roll { v.push(RollRec::default()); }
        } else {
            assert!(!rolled);
            if let RowRoll::Fwd(v) = &mut roll { v.push(RollRec::default()); }
            // LA holds u' (mX = NB - u'): the mask turns on at ladder lane l where mX == NB - j - l, i.e. u' == j + l,
            // and is on from the start where mX >= NB - j + 1, i.e. u' < j: f holds big_j (top of the function)
            let m = rt.m.as_ref().expect("masked row needs mask scratch");
            // big = !(!sign & [u'_5 >= j]), computed straight into the flag (the sign literal gates every comparator
            // cube), so no temporary is held across the ladder and g serves as the masked cells' AND temp
            let big = m.f;
            let (slo, shi, sa, gp) = if let Some(lo_p) = partial {
                // ladder lane l <-> rem lane hi_i - 1 - l; the divisor LSB (lane mX - 1) sits at l = u' - a
                let a = j as isize + NB as isize - hi_i;
                let kj = (hi_i - j as isize - lo_p as isize).max(0) as usize;
                let lmax = NB as isize - park_lo(w) as isize - a;
                let shi = ((lmax + 1).max(0) as usize).min(t.len());
                (kj.min(shi), shi, a, pool)
            } else {
                (0, t.len(), j as isize, &[][..])
            };
            let srcs = [Src { lo: slo, hi: shi, v: ubits(&u.la), a: sa, d: 1, pre: m.pre.clone(), late: false }];
            let sc = m.sc();
            let ld = Lad { t: &t, s: &s, c0: rt.c0(), srcs: &srcs, f0: false, cmpl: false, sc: &sc, g: gp };
            let nc = term_nc();
            let ru = if nc { super::mask::mup_mid_nc(b, &ld) } else { super::mask::mup_mid(b, &ld) };
            b.play(&ru, false);
            let rd = if nc { super::mask::mdown_mid_nc(b, &ld, Some(ALWAYS)) } else { super::mask::mdown_mid(b, &ld, Some(ALWAYS)) };
            b.play(&rd, false);
            // the carry pool is idle in the masked rows (every lane masked): its lanes are the flag's clean chain
            let jc = pc.map_or(j, |c| j.max(c));
            if j + 1 < w.k && masked_row(j + 1) && pc.map_or(false, |c| j + 1 <= c) {
                // partial: big_{max(j+1, c)} == big_c: unchanged
            } else if j + 1 < w.k && masked_row(j + 1) {
                let mut lits = vec![(sg, true)];
                lits.extend(eq_lits(&u.la[..5], jc));
                if pool.len() >= 4 {
                    and_into_t(b, &lits, big, &pool[..4]);
                } else {
                    and_dirty(b, &lits, big, &u.dirty);
                }
            } else if pool.len() >= 5 {
                let (chain, ge) = (&pool[..4], pool[4]);
                b.x(big);
                super::mask::ge_const(b, &u.la[..5], jc as isize, ge, chain);
                b.x(sg);
                b.ccx(sg, ge, big);
                b.x(sg);
                super::mask::ge_const(b, &u.la[..5], jc as isize, ge, chain);
            } else {
                b.x(big);
                super::mask::ge_const_dirty_gated(b, &u.la[..5], jc as isize, big, &[(sg, true)], &u.dirty);
            }
        }
        flip(b);
    }
}

/// The literal list of an optional act flag (None: act = 1 classically).
fn act_lits(act: Option<QubitId>) -> Vec<(QubitId, bool)> {
    act.map(|a| vec![(a, false)]).unwrap_or_default()
}

/// t ^= act & c
fn act_cx(b: &mut B, act: Option<QubitId>, c: QubitId, t: QubitId) {
    match act {
        Some(a) => b.ccx(a, c, t),
        None => b.cx(c, t),
    }
}

impl GreedyFrog {
    /// Lanes the slot may still allocate under the cap.
    fn room(&self, b: &B) -> usize {
        self.cap.saturating_sub(b.live) as usize
    }
}

/// out ^= AND(lits): clean ancillas while the cap leaves room, borrowed lanes otherwise.
fn and_auto(b: &mut B, u: &GreedyFrog, lits: &[(QubitId, bool)], out: QubitId) {
    let need = lits.len().saturating_sub(2);
    if need == 0 || u.room(b) >= need { and_into(b, lits, out) } else { and_dirty(b, lits, out, &u.dirty) }
}

/// Phase (-1)^AND(lits): an AND chain into clean ancillas (uncomputed by measurement) and a CZ, n - 2 Toffoli.
fn phase_and(b: &mut B, lits: &[(QubitId, bool)]) {
    let n = lits.len();
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
    match n {
        0 => {}
        1 => b.z(lits[0].0),
        2 => b.cz(lits[0].0, lits[1].0),
        _ => {
            let anc = b.alloc_n(n - 2);
            b.and_c(lits[0].0, lits[1].0, anc[0]);
            for i in 2..n - 1 {
                b.and_c(anc[i - 2], lits[i].0, anc[i - 1]);
            }
            b.cz(anc[n - 3], lits[n - 1].0);
            for i in (2..n - 1).rev() {
                b.and_u(anc[i - 2], lits[i].0, anc[i - 1]);
            }
            b.and_u(lits[0].0, lits[1].0, anc[0]);
            b.free_n(&anc);
        }
    }
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
}

/// Erase t, known to hold f(state), by an X-basis measurement: the phase (-1)^(m f) it leaves is repaired by `phase`
/// in a block conditioned on the outcome m, so the repair's Toffoli count only on the shots where m = 1 (half of
/// them on average), against a full recomputation for an XOR erase.
fn erase_mbu(b: &mut B, t: QubitId, phase: impl FnOnce(&mut B)) {
    let m = b.fresh_bits(1)[0];
    b.hmr_to(t, m);
    // EFREE (S3-008, after SnehalRaj 81358d68): the measurement leaves t |0>, so it leaves the live count while its
    // phase repair runs (the repair's chains and pools may take it) and is taken back after; the caller frees it as before
    let ef = efree();
    if ef {
        b.free(t);
    }
    b.push_condition(m);
    phase(b);
    b.pop_condition();
    if ef {
        b.acquire(t);
    }
}
/// S3-008 EFREE (exact: a measured lane is |0>). Dev override `WL_EFREE=0|1`.
pub const EFREE: bool = true;
/// B-PORT3 ROW-Y (ROWTOP / INT-005 family): the plain division rows' top lane is sum-only (its carry is discarded mod
/// 2^n, as TERM-NC), so its source m (= !sign, row 0: 1) is applied by hand (t ^= c ^ m) instead of through the
/// flipped zero lane y; y is then |0> through both rows passes and joins the rows' carry pools. Plain-row slots only
/// (no mask scratch); needs YTOP_HOST (a non-empty pool). Dev override `WL_ROW_Y=0|1`.
pub const ROW_Y: bool = true;
/// B-PORT3 ROW-F (with ROW-Y): the plain rows' carry-in m is read from the sign lane itself, X-flipped to !sign (row 0:
/// from a pool lane X-flipped to 1), instead of the flipped lane f; f is then |0> through both rows passes and joins the
/// rows' carry pools. Dev override `WL_ROW_F=0|1`.
pub const ROW_F: bool = true;
fn row_f() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("ROW_F", ROW_F));
    *E
}
fn row_y(rt: &RowTmp) -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("ROW_Y", ROW_Y));
    *E && rt.m.is_none() && ytop_host()
}
/// B-PORT3 EARLY-GHOST: the forward slot X-measures d and a1 right after the cofactor pass and r right after the
/// renormalisation instead of at F11 (exact: nothing in between acts on them). Dev override `WL_EARLY_GHOST=0|1`.
pub const EARLY_GHOST: bool = true;
fn early_ghost() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("EARLY_GHOST", EARLY_GHOST));
    *E
}
fn efree() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("EFREE", EFREE));
    *E
}

/// Erase t = AND(lits) by measurement while the cap leaves room for the repair's chain, by recomputation otherwise.
fn erase_and(b: &mut B, u: &GreedyFrog, t: QubitId, lits: &[(QubitId, bool)]) {
    if u.room(b) >= lits.len().saturating_sub(2) {
        erase_mbu(b, t, |b| phase_and(b, lits));
    } else {
        and_auto(b, u, lits, t);
    }
}

/// Erase t = [v >= k] by measurement (repair on a clean chain) while the cap leaves room, by recomputation otherwise.
fn ge_erase(b: &mut B, u: &GreedyFrog, v: &[QubitId], k: isize, t: QubitId) {
    let need = v.len().saturating_sub(1);
    if u.room(b) >= need {
        let chain = b.alloc_n(need);
        erase_mbu(b, t, |b| super::mask::ge_const_phase(b, v, k, &chain));
        b.free_n(&chain);
    } else {
        super::mask::ge_const_dirty(b, v, k, t, &u.dirty);
    }
}

/// Phase (-1)^[a < b] (lt_into with a phase in place of the XOR), for a measured erase.
fn lt_phase(b: &mut B, a: &[QubitId], bb: &[QubitId]) {
    let c0 = b.alloc();
    let ru = super::arith::up(b, a, bb, c0);
    b.play(&ru, false);
    b.z(bb[a.len() - 1]);
    b.play(&ru, true);
    b.free(c0);
}

/// t ^= [v >= k] on a clean chain while the cap leaves room, on borrowed lanes otherwise.
fn ge_auto(b: &mut B, u: &GreedyFrog, v: &[QubitId], k: isize, t: QubitId) {
    let need = v.len().saturating_sub(1);
    if u.room(b) >= need {
        let chain = b.alloc_n(need);
        super::mask::ge_const(b, v, k, t, &chain);
        b.free_n(&chain);
    } else {
        super::mask::ge_const_dirty(b, v, k, t, &u.dirty);
    }
}

/// bits += ctrl, clean carries while the cap leaves room.
fn inc_auto(b: &mut B, u: &GreedyFrog, ctrl: QubitId, bits: &[QubitId]) {
    let need = bits.len().saturating_sub(1);
    if u.room(b) >= need {
        let anc = b.alloc_n(need);
        super::arith::inc(b, ctrl, bits, &anc);
        b.free_n(&anc);
    } else {
        inc_dirty(b, ctrl, bits, &u.dirty);
    }
}

fn zero_auto(b: &mut B, u: &GreedyFrog, v: &[QubitId], out: QubitId) {
    let lits: Vec<(QubitId, bool)> = v.iter().map(|&q| (q, true)).collect();
    and_auto(b, u, &lits, out);
}

fn eq_auto(b: &mut B, u: &GreedyFrog, a: &[QubitId], bb: &[QubitId], out: QubitId) {
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
    zero_auto(b, u, a, out);
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
}

/// v += k (or -= k): a constant register while the cap leaves room, borrowed-lane increments otherwise.
fn add_const_auto(b: &mut B, u: &GreedyFrog, v: &[QubitId], k: usize, sub: bool) {
    if u.room(b) >= v.len() + 1 { add_const(b, v, k, sub) } else { add_const_dirty(b, v, k, sub, &u.dirty) }
}

/// Clean carry pool for a ladder pass: at most `want` lanes, leaving `reserve` lanes of room.
fn pool_for(b: &mut B, u: &GreedyFrog, want: usize, reserve: usize) -> Vec<QubitId> {
    let n = want.min(u.room(b).saturating_sub(reserve));
    b.alloc_n(n)
}

/// AND / comparator on a clean chain (`clean`) or on borrowed lanes.
fn and_any(b: &mut B, clean: bool, lits: &[(QubitId, bool)], out: QubitId, chain: &[QubitId]) {
    if clean { and_into_t(b, lits, out, chain) } else { and_dirty(b, lits, out, chain) }
}
fn ge_any(b: &mut B, v: &[QubitId], k: isize, t: QubitId, chain: &[QubitId], clean: bool) {
    if clean { super::mask::ge_const(b, v, k, t, chain) } else { super::mask::ge_const_dirty(b, v, k, t, chain) }
}

/// jl ^= the last row with q_j = 1 (rem lane j - 1 clear) among the rows j <= kt of active shots, scanning
/// j = k-1 .. 1 with a running OR f: y = q_j & g_j & !f, jl ^= j y, f ^= y, then y = q_j & [jl == j] is erased (jl == j
/// only where row j fired) by measurement. Row 0 never changes jl (0 is the default), so it is not visited.
/// g_j = act & [kt >= j]; g = 0 on entry and exit. Emitted directly (the measured erases are not recordable); ANDs on
/// `chain` (clean when `clean`, borrowed lanes otherwise).
fn sweep_fwd(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, chain: &[QubitId], clean: bool) {
    let (jl, f, y) = (&rt.jl[..], rt.f, rt.y);
    let kt5 = &u.lb[..R_BITS];
    let k = w.k;
    ge_any(b, kt5, k as isize - 1, y, chain, clean);
    act_cx(b, act, y, rt.g);
    if clean {
        erase_mbu(b, y, |b| super::mask::ge_const_phase(b, kt5, k as isize - 1, chain));
    } else {
        ge_any(b, kt5, k as isize - 1, y, chain, clean);
    }
    for j in (1..k).rev() {
        if j + 1 < k {
            let mut lits = act_lits(act);
            lits.extend(eq_lits(kt5, j));
            and_any(b, clean, &lits, rt.g, chain);
        }
        let lane = rt.rem(u, j as isize - 1);
        and_any(b, clean, &[(lane, true), (rt.g, false), (f, true)], y, chain);
        for (i, &bit) in jl.iter().enumerate() {
            if (j >> i) & 1 == 1 {
                b.cx(y, bit);
            }
        }
        b.cx(y, f);
        let lits = row_elits(lane, jl, j);
        erase_and(b, u, y, &lits);
    }
    // g = act & [kt >= 1] -> act -> 0
    let mut lits = act_lits(act);
    lits.extend(eq_lits(kt5, 0));
    and_any(b, clean, &lits, rt.g, chain);
    match act {
        Some(a) => b.cx(a, rt.g),
        None => b.x(rt.g),
    }
}

/// The exact inverse of `sweep_fwd` (rows in the opposite order), with each row's y erased by measurement through
/// its forward definition !lane & g & !f.
fn sweep_bwd(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, chain: &[QubitId], clean: bool) {
    let (jl, f, y) = (&rt.jl[..], rt.f, rt.y);
    let kt5 = &u.lb[..R_BITS];
    let k = w.k;
    match act {
        Some(a) => b.cx(a, rt.g),
        None => b.x(rt.g),
    }
    let mut lits = act_lits(act);
    lits.extend(eq_lits(kt5, 0));
    and_any(b, clean, &lits, rt.g, chain);
    for j in 1..k {
        let lane = rt.rem(u, j as isize - 1);
        let lits = row_elits(lane, jl, j);
        and_any(b, clean, &lits, y, chain);
        b.cx(y, f);
        for (i, &bit) in jl.iter().enumerate() {
            if (j >> i) & 1 == 1 {
                b.cx(y, bit);
            }
        }
        erase_and(b, u, y, &[(lane, true), (rt.g, false), (f, true)]);
        if j + 1 < k {
            let mut lits = act_lits(act);
            lits.extend(eq_lits(kt5, j));
            and_any(b, clean, &lits, rt.g, chain);
        }
    }
    ge_any(b, kt5, k as isize - 1, y, chain, clean);
    act_cx(b, act, y, rt.g);
    if clean {
        erase_mbu(b, y, |b| super::mask::ge_const_phase(b, kt5, k as isize - 1, chain));
    } else {
        ge_any(b, kt5, k as isize - 1, y, chain, clean);
    }
}

/// RHO-ANF: r ^= act & rho(jl), rho(j) = (j + #{8, 15, 22, 29 <= j}) mod 8 (j = jl, 5 bits), from its algebraic
/// normal form (exhaustively checked over all 32 values):
/// r0 = j0 + j3 + j0j1j2j3 + j1j2j4 + j0j2j3j4, r1 = j1 + j4 + j0j3 + j0j1j2j4 + j1j2j3j4, r2 = j2 + j0j1j3 + j1j4 + j0j3j4.
/// Monomials are built as AND chains rooted at act (act & j0 -> & j3 -> ..., act & j1 -> & j4 -> ...), XORed into r and
/// uncomputed by measurement: 11 Toffoli + 3 for the act-gated linear leaves (9 when act = 1 classically). <= 4 lanes.
/// S2-004 RHO_ANF8 (chart search after gopikannappan ec17ae47 affine_anf): r ^= act & rho(jl) with 5 shared ANDs + 3 act
/// ANDs (act None: 5) instead of 14 (9). rho = F0 + 2 F1 + 4 F2 with P = j0 j3, S = j1 j4, Q = S + P (j1 + j4),
/// G = j2 Q, Z = G (j0 + j3) (= j2 S (j0 + j3), since P (j0 + j3) = 0): F0 = j0 + j3 + G, F1 = j1 + j4 + P + Z, F2 = j2 + Q
/// (checked over all 32 values). Every product lane is erased by measurement. Needs 5 clean lanes. Dev override
/// `WL_RHO_ANF8=0|1`.
pub const RHO_ANF8: bool = true;
fn rho_anf8() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("RHO_ANF8", RHO_ANF8));
    *E
}
fn rho_anf8_into(b: &mut B, act: Option<QubitId>, j: &[QubitId], r: &[QubitId]) {
    let (p, s, xp, g, z) = (b.alloc(), b.alloc(), b.alloc(), b.alloc(), b.alloc());
    b.and_c(j[0], j[3], p);
    b.and_c(j[1], j[4], s);
    b.cx(j[1], j[4]);
    b.and_c(p, j[4], xp);
    b.cx(j[1], j[4]);
    b.cx(xp, s); // s = Q
    b.and_c(j[2], s, g);
    b.cx(j[0], j[3]);
    b.and_c(g, j[3], z);
    b.cx(j[0], j[3]);
    // r_i ^= act & F_i, F_i built in place on a product lane and restored
    let put = |b: &mut B, lane: QubitId, lin: &[QubitId], out: QubitId| {
        for &q in lin {
            b.cx(q, lane);
        }
        match act {
            Some(a) => b.ccx(a, lane, out),
            None => b.cx(lane, out),
        }
        for &q in lin {
            b.cx(q, lane);
        }
    };
    put(b, s, &[j[2]], r[2]);
    put(b, g, &[j[0], j[3]], r[0]);
    // negative control for the gate tests only: P3_BREAK=3 drops P from F1
    if cfg!(test) && std::env::var("P3_BREAK").map_or(false, |v| v.trim() == "3") {
        put(b, z, &[j[1], j[4]], r[1]);
    } else {
        put(b, z, &[j[1], j[4], p], r[1]);
    }
    b.cx(j[0], j[3]);
    b.and_u(g, j[3], z);
    b.cx(j[0], j[3]);
    b.and_u(j[2], s, g);
    b.cx(xp, s);
    b.cx(j[1], j[4]);
    b.and_u(p, j[4], xp);
    b.cx(j[1], j[4]);
    b.and_u(j[1], j[4], s);
    b.and_u(j[0], j[3], p);
    b.free_n(&[p, s, xp, g, z]);
}
fn rho_anf_into(b: &mut B, act: Option<QubitId>, j: &[QubitId], r: &[QubitId]) {
    fn mk(b: &mut B, a: Option<QubitId>, x: QubitId) -> (QubitId, bool) {
        match a {
            None => (x, false),
            Some(a) => {
                let g = b.alloc();
                b.and_c(a, x, g);
                (g, true)
            }
        }
    }
    fn rel(b: &mut B, a: Option<QubitId>, x: QubitId, n: (QubitId, bool)) {
        if n.1 {
            b.and_u(a.unwrap(), x, n.0);
            b.free(n.0);
        }
    }
    // act & j0 subtree
    let p0 = mk(b, act, j[0]);
    b.cx(p0.0, r[0]);
    let p03 = mk(b, Some(p0.0), j[3]);
    b.cx(p03.0, r[1]);
    let p031 = mk(b, Some(p03.0), j[1]);
    b.cx(p031.0, r[2]);
    let p0312 = mk(b, Some(p031.0), j[2]);
    b.cx(p0312.0, r[0]);
    rel(b, Some(p031.0), j[2], p0312);
    rel(b, Some(p03.0), j[1], p031);
    let p034 = mk(b, Some(p03.0), j[4]);
    b.cx(p034.0, r[2]);
    let p0342 = mk(b, Some(p034.0), j[2]);
    b.cx(p0342.0, r[0]);
    rel(b, Some(p034.0), j[2], p0342);
    rel(b, Some(p03.0), j[4], p034);
    rel(b, Some(p0.0), j[3], p03);
    rel(b, act, j[0], p0);
    // linear leaves
    act_cx(b, act, j[3], r[0]);
    act_cx(b, act, j[4], r[1]);
    act_cx(b, act, j[2], r[2]);
    // act & j1 subtree
    let p1 = mk(b, act, j[1]);
    b.cx(p1.0, r[1]);
    let p14 = mk(b, Some(p1.0), j[4]);
    b.cx(p14.0, r[2]);
    let p142 = mk(b, Some(p14.0), j[2]);
    b.cx(p142.0, r[0]);
    let p1420 = mk(b, Some(p142.0), j[0]);
    b.cx(p1420.0, r[1]);
    rel(b, Some(p142.0), j[0], p1420);
    let p1423 = mk(b, Some(p142.0), j[3]);
    b.cx(p1423.0, r[1]);
    rel(b, Some(p142.0), j[3], p1423);
    rel(b, Some(p14.0), j[2], p142);
    rel(b, Some(p1.0), j[4], p14);
    rel(b, act, j[1], p1);
}

/// Literals of a fired row's y at erase time: !lane & [jl == j], or [jl == j] alone with SWEEP_EQ_LIT (j >= 1: jl is
/// j only where row j fired, which needs !lane).
fn row_elits(lane: QubitId, jl: &[QubitId], j: usize) -> Vec<(QubitId, bool)> {
    let mut v = if sweep_eq_lit() { vec![] } else { vec![(lane, true)] };
    v.extend(eq_lits(jl, j));
    v
}

/// SWEEP-OR-LANES row j (1 <= j <= nF) on its prefix-OR lane fj = F_j, nx = F_(j+1) (None on the top row; the running
/// OR f of the chain rows above for j = nF): forward F_j = nx | (!lane & g) and jl ^= j (F_j ^ nx); backward the
/// inverse, F_j erased by measurement (repair Z(nx) CZ(!lane, g) CCZ(nx, !lane, g)) and freed. `tmp` is a |0> lane.
fn or_row(b: &mut B, u: &GreedyFrog, rt: &RowTmp, j: usize, fj: QubitId, nx: Option<QubitId>, tmp: QubitId, fwd: bool) {
    let lane = rt.rem(u, j as isize - 1);
    let g = rt.g;
    let jl_xor = |b: &mut B| {
        for (i, &bit) in rt.jl.iter().enumerate() {
            if (j >> i) & 1 == 1 {
                b.cx(fj, bit);
                if let Some(n) = nx {
                    b.cx(n, bit);
                }
            }
        }
    };
    if fwd {
        b.x(lane);
        match nx {
            None => b.and_c(lane, g, fj),
            Some(n) => {
                b.and_c(lane, g, tmp);
                b.x(n);
                b.x(tmp);
                b.and_c(n, tmp, fj);
                b.x(fj);
                b.x(tmp);
                b.x(n);
                b.and_u(lane, g, tmp);
            }
        }
        b.x(lane);
        jl_xor(b);
    } else {
        jl_xor(b);
        erase_mbu(b, fj, |b| match nx {
            None => phase_and(b, &[(lane, true), (g, false)]),
            Some(n) => {
                b.z(n);
                phase_and(b, &[(lane, true), (g, false)]);
                if or_ccz() {
                    // OR-CCZ: the 3-literal repair as one native CCZ, no ancilla
                    if !cr_break(7) {
                        b.x(lane);
                        b.ccz(n, lane, g);
                        b.x(lane);
                    }
                } else {
                    phase_and(b, &[(n, false), (lane, true), (g, false)]);
                }
            }
        });
        b.free(fj);
    }
}

/// AND lanes of a backward chain row ([jl == j] with or without the lane literal).
fn row_anc() -> usize {
    if sweep_eq_lit() { R_BITS - 2 } else { R_BITS - 1 }
}

/// Row j of the unary sweeps: an OR-lane row for j <= fl.len() (fl[j - 1] = F_j, the low rows, so the backward pass
/// erases and frees them before the chain rows run), else the chain row. `anc` empty: the chain row takes its AND
/// lanes on demand.
fn any_row(b: &mut B, u: &GreedyFrog, rt: &RowTmp, j: usize, k: usize, fl: &[QubitId], anc: &[QubitId], fwd: bool) {
    let nf = fl.len();
    if j > nf {
        if anc.is_empty() {
            let a = b.alloc_n(row_anc());
            sweep_row(b, u, rt, j, &a, fwd);
            b.free_n(&a);
        } else {
            sweep_row(b, u, rt, j, anc, fwd);
        }
        return;
    }
    let nx = if j + 1 >= k { None } else if j == nf { Some(rt.f) } else { Some(fl[j]) };
    if let Some(&t) = anc.first() {
        or_row(b, u, rt, j, fl[j - 1], nx, t, fwd);
    } else if !fwd {
        // the backward row needs no temporary (its repair AND takes its own lane)
        or_row(b, u, rt, j, fl[j - 1], nx, QubitId(u64::MAX), fwd);
    } else {
        let t = b.alloc();
        or_row(b, u, rt, j, fl[j - 1], nx, t, fwd);
        b.free(t);
    }
}

/// One row of the sweep (j >= 1): y = !lane & g & !f, jl ^= j y, f ^= y, then y erased by measurement (fwd); or its
/// inverse (bwd).
fn sweep_row(b: &mut B, u: &GreedyFrog, rt: &RowTmp, j: usize, anc: &[QubitId], fwd: bool) {
    let (jl, f, y) = (&rt.jl[..], rt.f, rt.y);
    let lane = rt.rem(u, j as isize - 1);
    let elits = row_elits(lane, jl, j);
    let ylits = [(lane, true), (rt.g, false), (f, true)];
    if fwd {
        and_into_t(b, &ylits, y, anc);
    } else {
        and_into_t(b, &elits, y, anc);
    }
    if !fwd {
        b.cx(y, f);
    }
    for (i, &bit) in jl.iter().enumerate() {
        if (j >> i) & 1 == 1 {
            b.cx(y, bit);
        }
    }
    if fwd {
        b.cx(y, f);
        erase_and(b, u, y, &elits);
    } else {
        erase_and(b, u, y, &ylits);
    }
}

/// sweep_fwd with g stepped by a unary iteration over kt5 (`SWEEP_UNARY`); `chain` holds >= 5 clean lanes.
fn sweep_fwd_ui(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, chain: &[QubitId], fl: &[QubitId]) {
    let kt5 = &u.lb[..R_BITS];
    let k = w.k;
    let (pre, anc) = (&chain[..R_BITS - 1], &chain[R_BITS - 1..R_BITS]);
    ge_any(b, kt5, k as isize - 1, rt.y, pre, true);
    act_cx(b, act, rt.y, rt.g);
    erase_mbu(b, rt.y, |b| super::mask::ge_const_phase(b, kt5, k as isize - 1, pre));
    if k >= 2 {
        any_row(b, u, rt, k - 1, k, fl, anc, true);
    }
    // j = k-2 .. 0 descending: scan the complemented kt5 (value 31 - j) upward
    for &q in kt5 {
        b.x(q);
    }
    let top = (1usize << R_BITS) - 1;
    // SWEEP-ACT-ROOT: decode (kt5', act) at value val + 32 where an extra prefix lane fits
    let root = match act { Some(a) if sweep_act_root() && u.room(b) >= 1 + act_root_spare() => Some((a, b.alloc())), _ => None };
    if rowlog() { eprintln!("WL_ACTROOT room {} act {} root {}", u.room(b), act.is_some() as u8, root.is_some() as u8); }
    if let Some((a, xl)) = root {
        let mut v6: Vec<QubitId> = kt5.to_vec();
        v6.push(a);
        let mut pre5: Vec<QubitId> = pre.to_vec();
        pre5.push(xl);
        let off: isize = if cr_break(6) { 0 } else { 1 << R_BITS };
        super::mask::onehot_scan(b, &v6, &pre5, top + 2 - k.max(1), top + 1, off, |b, val, o| {
            let j = top - val;
            b.cx(o, rt.g);
            if j >= 1 {
                any_row(b, u, rt, j, k, fl, anc, true);
            }
        });
        b.free(xl);
    } else {
    super::mask::onehot_scan(b, kt5, pre, top + 2 - k.max(1), top + 1, 0, |b, val, o| {
        let j = top - val;
        act_cx(b, act, o, rt.g);
        if j >= 1 {
            any_row(b, u, rt, j, k, fl, anc, true);
        }
    });
    }
    for &q in kt5 {
        b.x(q);
    }
    // g = act -> 0
    match act {
        Some(a) => b.cx(a, rt.g),
        None => b.x(rt.g),
    }
}

/// The exact inverse of `sweep_fwd_ui`; `chain` holds >= 8 clean lanes (decoder prefix 4 + the row's 6-literal AND 4).
fn sweep_bwd_ui(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, chain: &[QubitId], fl: &[QubitId]) {
    let kt5 = &u.lb[..R_BITS];
    let k = w.k;
    let (pre, anc) = (&chain[..R_BITS - 1], &chain[R_BITS - 1..chain.len().min(2 * R_BITS - 2)]);
    match act {
        Some(a) => b.cx(a, rt.g),
        None => b.x(rt.g),
    }
    // j = 0 .. k-2 ascending
    let root = match act { Some(a) if sweep_act_root() && u.room(b) >= 1 + act_root_spare_bwd() => Some((a, b.alloc())), _ => None };
    if rowlog() { eprintln!("WL_ACTROOT room {} act {} root {}", u.room(b), act.is_some() as u8, root.is_some() as u8); }
    if let Some((a, xl)) = root {
        let mut v6: Vec<QubitId> = kt5.to_vec();
        v6.push(a);
        let mut pre5: Vec<QubitId> = pre.to_vec();
        pre5.push(xl);
        let off: isize = if cr_break(8) { 0 } else { 1 << R_BITS };
        super::mask::onehot_scan(b, &v6, &pre5, 0, k.max(1) - 1, off, |b, j, o| {
            if j >= 1 {
                any_row(b, u, rt, j, k, fl, anc, false);
            }
            b.cx(o, rt.g);
        });
        b.free(xl);
    } else {
    super::mask::onehot_scan(b, kt5, pre, 0, k.max(1) - 1, 0, |b, j, o| {
        if j >= 1 {
            any_row(b, u, rt, j, k, fl, anc, false);
        }
        act_cx(b, act, o, rt.g);
    });
    }
    if k >= 2 {
        any_row(b, u, rt, k - 1, k, fl, anc, false);
    }
    ge_any(b, kt5, k as isize - 1, rt.y, pre, true);
    act_cx(b, act, rt.y, rt.g);
    erase_mbu(b, rt.y, |b| super::mask::ge_const_phase(b, kt5, k as isize - 1, pre));
}

/// gt ^= [Y window > X window] over the cofactor lanes [0, mX) (LA holds u = LA + sX, mX = W - 1 - u).
/// S1-001 WGT_TOP1 (odinfree 34665dee Froschfurz): the decode's window compare skips lane 0 of both rings. Wherever its
/// result is consulted (act, both ring slacks <= 1 after the stage-0 shift) both rings are bottom-normalised, so
/// X[0] = Y[0] = 1 and that lane passes the compare's carry unchanged; elsewhere gt is garbage, masked off and erased
/// by the same function. Dev override `WL_WGT_TOP1=0|1`.
pub const WGT_TOP1: bool = true;
fn wgt_top1() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("WGT_TOP1", WGT_TOP1));
    *E
}
fn window_gt(b: &mut B, u: &GreedyFrog, gt: Option<QubitId>, w: &Win) {
    let lo = if wgt_top1() && norm_stage0() { 1 } else { 0 };
    let t: Vec<QubitId> = (lo..NB).rev().map(|i| u.x[i]).collect();
    let sv: Vec<QubitId> = (lo..NB).rev().map(|i| u.y[i]).collect();
    if w.mxp >= NB + 1 {
        let c0 = b.alloc();
        let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
        let pool = pool_for(b, u, NB, 0);
        plain_compare(b, &t, &sv, c0, &sc, gt, None, &pool);
        b.free_n(&pool);
        b.free(c0);
        return;
    }
    // LA holds u (mX = W - 1 - u): offset it to u' = u - UOFF (mX = NB - u'). The mask turns on at ladder lane l where
    // mX == NB - l, i.e. u' == l, and is on from the start where mX >= NB + 1, i.e. u' < 0 (its sign bit).
    add_const_sm(b, u, &u.la, UOFF, true);
    let m = Masked::alloc_small(b);
    let sg = u.la[LB_BITS - 1];
    b.cx(sg, m.f);
    let srcs = [Src { lo: 0, hi: t.len(), v: ubits(&u.la), a: 0, d: 1, pre: m.pre.clone(), late: false }];
    let sc = m.sc();
    let ld = Lad { t: &t, s: &sv, c0: m.c0, srcs: &srcs, f0: false, cmpl: true, sc: &sc, g: &[] };
    let bank = if k1() & 4 != 0 { pool_for(b, u, t.len(), 0) } else { vec![] };
    if !(gt.is_none() && tc_phase() && super::mask::mid_phase_top(b, &ld, &bank, mw_break(3))) {
        let ru = super::mask::mup_mid_bank(b, &ld, &bank);
        b.play(&ru, false);
        let tc = top_carry(&ld);
        match gt {
            Some(o) => b.cx(tc, o),
            None => b.z(tc),
        }
        b.play(&ru, true);
    }
    b.free_n(&bank);
    b.cx(sg, m.f);
    m.free(b);
    add_const_sm(b, u, &u.la, UOFF, false);
}

impl GreedyFrog {
    /// One inverse slot: undo `fwd_slot`, repairing its measurement phases with `bits`.
    pub fn inv_slot(&mut self, b: &mut B, bits: &SlotBits, w: &Win) {
        let c = self.inv_slot_c(b, bits, w, None, false);
        assert!(c.is_none());
    }

    /// `inv_slot` with SW-CARRY: `cin` = this slot's swap flag carried from the next forward slot's inverse (skips the
    /// I2 decode); with `want_out` (and `SW_CARRY`) returns the previous forward slot's swap flag on a fresh lane where
    /// this slot can produce it (not on PARK-SPLIT slots).
    pub fn inv_slot_c(&mut self, b: &mut B, bits: &SlotBits, w: &Win, cin: Option<QubitId>, want_out: bool)
                      -> Option<QubitId> {
        super::mask::set_borrowed(&self.dirty);
        prof(b, "i.z0");
        p3(b, self, "i.z0");
        // I1: z0 = [LA == 0] & [cnt != 0]; on slots where no shot can have finished, act = 1 classically and the
        // flag (and the DONE bookkeeping) is skipped
        let z0 = if w.act_const { None } else { Some(b.alloc()) };
        if let Some(z0) = z0 {
            let cz = b.alloc();
            self.cnt_zero_into(b, cz);
            let lz = b.alloc();
            zero_into(b, &self.la, lz);
            and_into(b, &[(lz, false), (cz, true)], z0);
            if z0_meas() {
                let zl: Vec<(QubitId, bool)> = self.la.iter().map(|&q| (q, true)).collect();
                let cl: Vec<(QubitId, bool)> = self.cntw().iter().map(|&q| (q, false)).collect();
                erase_and(b, self, lz, &zl);
                if cr_break(4) { let m = b.fresh_bits(1)[0]; b.hmr_to(cz, m); } else { erase_and(b, self, cz, &cl); }
            } else {
                zero_into(b, &self.la, lz);
                self.cnt_zero_into(b, cz);
            }
            b.free(lz);
            b.free(cz);
        }
        // z0 holds act = !z0 except around I5 and at the end
        let act = z0;
        if let Some(z0) = z0 {
            b.x(z0);
        }
        p3(b, self, "i.prep");
        let y_act = if sy_act_gate() { act } else { None };
        let ns0 = norm_stage0();
        // OFF-KEEP (MICRO-WALK) runs on the standard I2 path only: a SW-CARRY slot (cin) erases its carried flag
        // on the plain un-swapped registers before its prep, with no decode offsets to keep
        let keep = ns0 && off_keep() && cin.is_none();
        let (mut sx, mut sy, sw_std): (Vec<QubitId>, Vec<QubitId>, Option<QubitId>) = if let Some(c) = cin {
            // SW-CARRY: I3, I4 on the carried flag, its I5 erase (the forward's F9 on the restored pre-swap state),
            // then the decode prep on the un-swapped rings (the receiver's ring layouts at the rows window)
            prof(b, "i.unswap");
            b.z_if(c, bits.sw);
            super::arith::cswap_regs(b, c, &self.x, &self.y);
            super::arith::cswap_regs(b, c, &self.la, &self.lb);
            b.cx(c, self.par);
            prof(b, "i.swerase");
            erase_mbu(b, c, |b| {
                if let Some(z0) = z0 {
                    b.x(z0);
                }
                self.swap_flag(b, z0, None, w);
                if let Some(z0) = z0 {
                    b.x(z0);
                }
            });
            b.free(c);
            prof(b, "i.prep");
            if ns0 {
                // Y (the target, slack <= 1): the a-shift only, sY = a_Y; X (the divisor): the 5-stage funnel alone
                // (its stage 0 is the a-shift's lane map), sX = its slack; the receiver's ring layouts and sX, sY
                let ay = b.alloc();
                let mut l = act_lits(y_act);
                l.extend([(self.y[0], true), (self.y[1], false)]);
                and_auto(b, self, &l, ay);
                for i in 0..NB {
                    b.cswap(ay, self.y[i], self.y[i + 1]);
                }
                let f = b.alloc_n(R_BITS);
                norm_bottom(b, self, &self.x, &f, None);
                (f, vec![ay], None)
            } else {
                let sx = b.alloc_n(R_BITS);
                let sy = b.alloc_n(R_BITS);
                norm_bottom(b, self, &self.x, &sx, None);
                norm_bottom(b, self, &self.y, &sy, y_act);
                (sx, sy, None)
            }
        } else {
        prof(b, "i.prep");
        // decode prep: normalised cofactor windows (slacks sX, sY)
        // NORM-STAGE0: c_r = [ring slack >= 2], a_r = [ring slack == 1]; only the a-shift (the funnel's stage 0) here
        let (mut sx, mut sy, cxy) = if ns0 {
            let (ax, ay, cx_, cy_) = (b.alloc(), b.alloc(), b.alloc(), b.alloc());
            and_auto(b, self, &[(self.x[0], true), (self.x[1], true)], cx_);
            let mut l = act_lits(act);
            l.extend([(self.y[0], true), (self.y[1], true)]);
            and_auto(b, self, &l, cy_);
            and_auto(b, self, &[(self.x[0], true), (self.x[1], false)], ax);
            let mut l = act_lits(y_act);
            l.extend([(self.y[0], true), (self.y[1], false)]);
            and_auto(b, self, &l, ay);
            for i in 0..NB {
                b.cswap(ax, self.x[i], self.x[i + 1]);
            }
            for i in 0..NB {
                b.cswap(ay, self.y[i], self.y[i + 1]);
            }
            (vec![ax], vec![ay], Some((cx_, cy_)))
        } else {
            let sx = b.alloc_n(R_BITS);
            let sy = b.alloc_n(R_BITS);
            norm_bottom(b, self, &self.x, &sx, None);
            norm_bottom(b, self, &self.y, &sy, y_act);
            (sx, sy, None)
        };
        prof(b, "i.swdec");
        p3(b, self, "i.swdec");
        // I2: u = LA + sX, v = LB + sY (cofactor bit lengths mX = W - 1 - u, mY = W - 1 - v):
        // sw = act & (mY < mX | mY == mX & winY <= winX)
        add_sm(b, self, &self.la, &sx, false, false);
        add_sm(b, self, &self.lb, &sy, false, false);
        let sw = b.alloc();
        if swf_lex() {
            // SWF-LEX: lt | eq & !gt = [LA < LB + !gt]
            let gt = b.alloc();
            window_gt(b, self, Some(gt), w);
            let flip = !cr_break(2);
            if flip { b.x(gt); }
            let core = b.alloc();
            lt_cin_sm(b, self, &self.la, &self.lb, gt, Some(core));
            if let Some((cx_, cy_)) = cxy {
                // NORM-STAGE0 (as below): sw = c_y, or the rule where neither ring has slack >= 2
                let brk = if cfg!(test) { std::env::var("W2_BREAK_NORM").unwrap_or_default() } else { String::new() };
                let mut l = act_lits(act);
                l.push((core, false));
                if brk.trim() != "2" {
                    l.push((cx_, true));
                }
                l.push((cy_, true));
                and_auto(b, self, &l, sw);
                if brk.trim() != "1" {
                    b.cx(cy_, sw);
                }
            } else {
                act_cx(b, act, core, sw);
            }
            erase_mbu(b, core, |b| lt_cin_sm(b, self, &self.la, &self.lb, gt, None));
            b.free(core);
            if flip { b.x(gt); }
            erase_mbu(b, gt, |b| window_gt(b, self, None, w));
            b.free(gt);
        } else {
            let lt = b.alloc();
            let eq = b.alloc();
            let gt = b.alloc();
            lt_sm(b, self, &self.la, &self.lb, Some(lt));
            eq_into(b, &self.la, &self.lb, eq);
            window_gt(b, self, Some(gt), w);
            let le = b.alloc();
            b.x(gt);
            b.and_c(eq, gt, le);
            b.x(gt);
            let v = b.alloc();
            b.x(lt);
            b.x(le);
            b.and_c(lt, le, v);
            b.x(v);
            if let Some((cx_, cy_)) = cxy {
                // NORM-STAGE0: a ring with slack >= 2 is the divisor (the target's slack is <= 1, SMALL-02), so
                // sw = c_y, or the receiver's rule (on exactly normalised rings) where neither slack is >= 2
                // negative controls for the gate tests only: W2_BREAK_NORM=1 (a y ring with slack >= 2 is not swapped),
                // =2 (the rule is not masked off where the x ring has slack >= 2)
                let brk = if cfg!(test) { std::env::var("W2_BREAK_NORM").unwrap_or_default() } else { String::new() };
                let mut l = act_lits(act);
                l.push((v, false));
                if brk.trim() != "2" {
                    l.push((cx_, true));
                }
                l.push((cy_, true));
                and_auto(b, self, &l, sw);
                if brk.trim() != "1" {
                    b.cx(cy_, sw);
                }
            } else {
                act_cx(b, act, v, sw);
            }
            b.x(v);
            b.and_u(lt, le, v);
            b.x(le);
            b.x(lt);
            b.free(v);
            b.x(gt);
            b.and_u(eq, gt, le);
            b.x(gt);
            b.free(le);
            erase_mbu(b, gt, |b| window_gt(b, self, None, w));
            for i in 0..LB_BITS {
                b.cx(self.lb[i], self.la[i]);
            }
            let zl: Vec<(QubitId, bool)> = self.la.iter().map(|&q| (q, true)).collect();
            erase_and(b, self, eq, &zl);
            for i in 0..LB_BITS {
                b.cx(self.lb[i], self.la[i]);
            }
            erase_mbu(b, lt, |b| lt_sm(b, self, &self.la, &self.lb, None));
            b.free_n(&[lt, eq, gt]);
        }
        if !keep {
            add_sm(b, self, &self.lb, &sy, false, true);
            add_sm(b, self, &self.la, &sx, false, true);
        }
        if let Some((cx_, cy_)) = cxy {
            // the a-shift leaves [lanes 0, 1 zero] unchanged (it fires only at slack 1)
            erase_and(b, self, cx_, &[(self.x[0], true), (self.x[1], true)]);
            let mut l = act_lits(act);
            l.extend([(self.y[0], true), (self.y[1], true)]);
            erase_and(b, self, cy_, &l);
            b.free_n(&[cx_, cy_]);
        }
        prof(b, "i.unswap");
        p3(b, self, "i.unswap");
        // I3, I4
        b.z_if(sw, bits.sw);
        super::arith::cswap_regs(b, sw, &self.x, &self.y);
        super::arith::cswap_regs(b, sw, &self.la, &self.lb);
        super::arith::cswap_regs(b, sw, &sx, &sy);
        b.cx(sw, self.par);
        if keep {
            // OFF-KEEP: LA, LB hold LA + sX, LB + sY (one lane each); I5 here, on the plain registers inside its block
            prof(b, "i.swerase");
            erase_mbu(b, sw, |b| {
                add_sm(b, self, &self.la, &sx, false, true);
                if !mw_break(4) { add_sm(b, self, &self.lb, &sy, false, true); }
                if let Some(z0) = z0 {
                    b.x(z0);
                }
                self.swap_flag(b, z0, None, w);
                if let Some(z0) = z0 {
                    b.x(z0);
                }
                if !mw_break(4) { add_sm(b, self, &self.lb, &sy, false, false); }
                add_sm(b, self, &self.la, &sx, false, false);
            });
            b.free(sw);
            prof(b, "i.unswap");
        }
        if ns0 {
            // NORM-STAGE0: only the divisor ring X can still have slack (>= 2): the 5-stage funnel on X alone, then
            // sX = funnel + a_X (exclusive: a_X = 1 leaves slack 0), and a_X = [sX == 1] erased
            let ax = sx[0];
            let f = b.alloc_n(R_BITS);
            norm_bottom(b, self, &self.x, &f, None);
            if keep {
                // OFF-KEEP: LA = LA + a_X already; the funnel's part (0 where a_X = 1) goes on now
                add_sm(b, self, &self.la, &f, false, false);
            }
            b.cx(ax, f[0]);
            let mut l = vec![(f[0], false)];
            l.extend(f[1..].iter().map(|&q| (q, true)));
            erase_and(b, self, ax, &l);
            b.free(ax);
            sx = f;
        }
        // OFF-KEEP erased and freed sw after the un-swap
        (sx, sy, if keep { None } else { Some(sw) })
        };
        // SMALL-02: the target's slack is <= 1 from here to the denormalisation
        let mut host: Vec<QubitId> = vec![];
        let free_mode = host_free();
        let mut sy_len = sy.len();
        if sy_host() {
            zero_probe(b, &sy[1..]);
            if free_mode {
                b.free_n(&sy[1..]);
                sy_len = 1;
            } else {
                host.extend(&sy[1..]);
            }
        }
        if let Some(sw) = sw_std {
        prof(b, "i.swerase");
        p3(b, self, "i.swerase");
        // I5: erase sw with the forward's F9 logic
        erase_mbu(b, sw, |b| {
            if let Some(z0) = z0 {
                b.x(z0);
            }
            self.swap_flag(b, z0, None, w);
            if let Some(z0) = z0 {
                b.x(z0);
            }
        });
        b.free(sw);
        }
        prof(b, "i.rows");
        p3(b, self, "i.rows");
        // I6: u = LA + sX in LA, kt = u - (LB + sY) = mY - mX in LB; rows; r = act & (sX - sY - j_last)
        if !keep {
            add_sm(b, self, &self.la, &sx, false, false);
            add_sm(b, self, &self.lb, &sy[..sy_len], false, false);
        }
        for &q in &self.lb {
            b.x(q);
        }
        add_sm(b, self, &self.lb, &self.la, true, false);
        // SMALL-01: LB = kt; its lanes 5..9 are |0> (or, on finished shots without the Y gate, copies of the sign)
        let lb_sign_clear = lb_host() && !sy_act_gate() && !w.act_const;
        if lb_sign_clear {
            for i in R_BITS..LB_BITS - 1 {
                b.cx(self.lb[LB_BITS - 1], self.lb[i]);
            }
        }
        let lb_top = if lb_sign_clear { LB_BITS - 1 } else { LB_BITS };
        if lb_host() {
            zero_probe(b, &self.lb[R_BITS..lb_top]);
            if free_mode {
                b.free_n(&self.lb[R_BITS..lb_top]);
            } else {
                host.extend(&self.lb[R_BITS..lb_top]);
            }
        }
        let masked_rows = w.mx < NB + 1;
        if masked_rows {
            add_const_sm(b, self, &self.la, UOFF, true);
        }
        // LA-HOST: u' = NB - mX in 0..NB here
        // (act-constant slots only: a finished shot's u' is far below -32)
        let la_cut = la_host() && free_mode && masked_rows && w.dtop_near && w.act_const;
        let la_sign = la_cut && !w.dtop_tight;
        if la_sign {
            for i in R_BITS..LB_BITS - 1 {
                b.cx(self.la[LB_BITS - 1], self.la[i]);
            }
        }
        if la_cut {
            zero_probe(b, &self.la[R_BITS..LB_BITS - 1]);
            b.free_n(&self.la[R_BITS..LB_BITS - 1]);
        }
        // Masked-row slots park the divisor window's junk when the cap leaves room for it beside the plain rows'
        // temporaries, r, a1 and the sweep's chain; every row then runs plain (and pooled where room is left).
        let top = if div_top_bound() { w.dtop.max(w.mx).min(NB) } else { NB };
        let zn = top - park_lo(w).min(top);
        let room_park = self.room(b);
        let park_std = masked_rows && (force_park() || room_park >= zn + park_reserve());
        let ytop = ytop_host();
        // PARK-SPLIT: z beside s0, f, y (+ r, a1 in the undo rows); the repark's 4-lane decoder takes f, y, Y[W-1] and
        // one free lane, so a full park needs room_park >= zn + 8 (zn + 6 for the first park)
        let split = park_split() && masked_rows && div_top_bound() && ytop && zn >= R_BITS && room_park >= zn + 8
            && (!park_std || room_park < zn + 9 + split_sweep_min());
        let park = park_std || split;
        // PARTIAL-PARK: park the top zp junk lanes where the whole window does not fit
        let zp = if !park && masked_rows && partial_park() && div_top_bound() {
            room_park.saturating_sub(partial_reserve()).min(zn)
        } else { 0 };
        let partial = (zp >= 2).then(|| top - zp);
        let mut z = if park { b.alloc_n(zn) } else if partial.is_some() { b.alloc_n(zp) } else { vec![] };
        if park {
            park_junk(b, self, w, &z, top);
        } else if let Some(lo_p) = partial {
            park_junk_partial(b, self, &z, top, lo_p);
        }
        p3(b, self, "i.rowsrun");
        let mut rt = if split { RowTmp::alloc_slim(b) } else { RowTmp::alloc(b, masked_rows && !park) };
        // lanes lent to both rows pools: hosted lanes, the sweep's idle g/jl on plain-row slots, the flipped Y[W-1]
        let mut lend = host.clone();
        if rt_idle_host() && rt.m.is_none() && !split {
            lend.push(rt.g);
            lend.extend(&rt.jl);
        }
        if ytop {
            lend.push(self.y[W - 1]);
        }
        if row_y(&rt) {
            // ROW-Y: the rows no longer read the zero source y, which is |0> through both rows passes
            lend.push(rt.y);
            if row_f() {
                // ROW-F: nor the carry-in lane f (|0> at both rows passes: the sweep's found flag is cleared by then)
                lend.push(rt.f);
            }
        }
        let room0 = self.room(b);
        // The rows' carry pool is held only while a rows pass runs: the inverse pass is re-recorded on a pool taken
        // then (the same function), so r, a1 and the sweep's chain can use the lanes in between.
        if ytop {
            b.x(self.y[W - 1]);
        }
        zero_probe(b, &lend);
        self.cap += extra_rows();
        let own = pool_for(b, self, (NB + 1).saturating_sub(lend.len()), 0);
        self.cap -= extra_rows();
        let pool: Vec<QubitId> = own.iter().chain(&lend).copied().take(NB + 1).collect();
        let pool_fwd_len = pool.len();
        let mut row_recs: Vec<RollRec> = vec![];
        if roll_rows() {
            // ROLL-ROWS: the forward rows pass runs directly (its rolled rows measure carries)
            division_rows(b, self, w, &rt, &pool, park, top, partial, RowRoll::Fwd(&mut row_recs));
        } else {
            b.begin();
            division_rows(b, self, w, &rt, &pool, park, top, partial, RowRoll::No);
            let rows = b.end();
            b.play(&rows, false);
        }
        b.free_n(&own);
        zero_probe(b, &lend);
        // YTOP-SWEEP: Y[W-1] stays |0> and is free from here to the undo rows
        let ytsw = ytop && free_mode && ytop_sweep();
        if ytsw {
            if mw_break(6) { b.x(self.y[W - 1]); }
            zero_probe(b, &[self.y[W - 1]]);
        } else if ytop {
            b.x(self.y[W - 1]);
        }
        if split {
            // PARK-SPLIT: unpark (f, y are |0> between the rows passes), then take the sweep's g and jl
            zero_probe(b, &[rt.f, rt.y]);
            park_split_pass(b, self, w, &z, top, &[rt.f, rt.y], false);
            zero_probe(b, &z);
            b.free_n(&z);
            z.clear();
            rt.attach(b);
        }
        // X0-HOST: X[0] = 1 (act_const slots) is a |0> lane from here to the undo rows
        let x0h = x0_host() && ns0 && w.act_const && free_mode;
        if x0h {
            if !mw_break(5) { b.x(self.x[0]); }
            zero_probe(b, &[self.x[0]]);
            b.free(self.x[0]);
        }
        prof(b, "i.sweep");
        p3(b, self, "i.sweep");
        // The sweep runs on a clean 4-lane chain; its inverse runs later beside r and a1, on a clean chain while the
        // cap leaves room and on borrowed lanes otherwise.
        // SWEEP-OR-LANES: OR lanes for the top rows, leaving room for r + a1 (4), the r section's chains (4), the
        // backward unary chain (8) and its repair lane (1)
        let room_sw = self.room(b);
        // SW-CARRY: this slot leaves the previous slot's swap flag c (held from the r / a1 section to the slot's end)
        // (on PARK-SPLIT slots only where the park leaves SWC_SPLIT_MIN lanes of room beside z: the split repark holds
        // s0, f, y, r, a1 and its decoder beside z, so a carried lane there can set the peak)
        let produce = want_out && sw_carry() && (!split || room_park >= zn + swc_split_min());
        let swc = produce as usize;
        let mut fl: Vec<QubitId> = vec![];
        let mut ylent = false;
        if sweep_unary() && room_sw >= R_BITS {
            // ... and only where the backward chain rows (after the OR lanes are freed) still fit: r, a1, prefix, AND
            if sweep_or_lanes() && w.k >= 2 && room_sw >= RHO_BITS + 1 + R_BITS - 1 + row_anc() + swc {
                // OR lanes on rows 1..nF; peak at the backward start: nF + r, a1 (4) + decoder prefix (4) + repair (1;
                // none with OR-CCZ) + the backward act root lane on act-live slots (OR_RES_ACT) (+ SW-CARRY c)
                // (+ the ROOT-OR act-live reserve)
                let nres = if act.is_some() { nor_res_live() } else { 0 };
                let res = RHO_BITS + 1 + R_BITS - 1 + (!or_ccz()) as usize
                    + if act.is_some() && sweep_act_root() { or_res_act() } else { 0 } + swc + nres;
                let n_or = (w.k - 1).min(room_sw.saturating_sub(res));
                // YTOP-SWEEP: Y[W-1] (|0>) is one more OR lane where the rows allow it
                let n_or_y = (w.k - 1).min((room_sw + 1).saturating_sub(res));
                if ytsw && n_or_y > n_or {
                    fl = vec![self.y[W - 1]];
                    fl.extend(b.alloc_n(n_or));
                    ylent = true;
                } else {
                    fl = b.alloc_n(n_or);
                }
            }
            if rowlog() {
                eprintln!("WL_SWEEP room_sw {room_sw} k {} n_or {} park {} masked {}", w.k, fl.len(), park as u8, masked_rows as u8);
            }
            let ch = b.alloc_n(R_BITS);
            sweep_fwd_ui(b, self, act, w, &rt, &ch, &fl);
            b.free_n(&ch);
        } else {
            let ch = b.alloc_n(R_BITS - 1);
            sweep_fwd(b, self, act, w, &rt, &ch, true);
            b.free_n(&ch);
        }
        p3(b, self, "i.ra1");
        let r = b.alloc_n(RHO_BITS);
        let a1 = b.alloc();
        // jl <- sX - sY - jl in place: the rotation since the last step (rho_of in greedyfrog_model). This slot's rotation
        // rho = act & ((jl mod 8) + #{8, 15, 22, 29 <= jl}) mod 8 and a1 = act & [jl < 8] (the slot was a step).
        // Temps: y and g (|0> after the sweep) and the sweep chain.
        let jl = rt.jl.clone();
        let fold = sy_fold_cin() && sy_len == 1;
        // jl -> ~jl + sX + !sY0 (fold) = sX - sY - jl; the map is an involution
        let jl_map = |b: &mut B| {
            for &q in &jl {
                b.x(q);
            }
            b.cx(sy[0], rt.g);
            b.x(rt.g);
            add_on_sm(b, self, &jl, &sx, false, false, rt.g, true);
            b.x(rt.g);
            b.cx(sy[0], rt.g);
        };
        if fold {
            jl_map(b);
        } else {
            for &q in &jl {
                b.x(q);
            }
            add_on_sm(b, self, &jl, &sx, true, false, rt.g, false);
            add_on_sm(b, self, &jl, &sy[..sy_len], false, true, rt.g, false);
        }
        if rho_anf8() && self.room(b) >= 5 {
            rho_anf8_into(b, act, &jl, &r);
            let mut lits = act_lits(act);
            lits.extend([(jl[3], true), (jl[4], true)]);
            and_auto(b, self, &lits, a1);
        } else if rho_anf() && self.room(b) >= 4 {
            rho_anf_into(b, act, &jl, &r);
            let mut lits = act_lits(act);
            lits.extend([(jl[3], true), (jl[4], true)]);
            and_auto(b, self, &lits, a1);
        } else {
            for i in 0..RHO_BITS {
                act_cx(b, act, jl[i], r[i]);
            }
            let (t, c) = (rt.y, rt.g);
            for cst in [8isize, 15, 22, 29] {
                ge_auto(b, self, &jl, cst, t);
                match act {
                    Some(a) => b.and_c(a, t, c),
                    None => b.cx(t, c),
                }
                inc_auto(b, self, c, &r);
                match act {
                    Some(a) => b.and_u(a, t, c),
                    None => b.cx(t, c),
                }
                ge_erase(b, self, &jl, cst, t);
            }
            let mut lits = act_lits(act);
            lits.extend([(jl[3], true), (jl[4], true)]);
            and_auto(b, self, &lits, a1);
        }
        if fold {
            jl_map(b);
        } else {
            add_on_sm(b, self, &jl, &sy[..sy_len], false, false, rt.g, false);
            add_on_sm(b, self, &jl, &sx, true, true, rt.g, false);
            for &q in &jl {
                b.x(q);
            }
        }
        for i in 0..RHO_BITS {
            b.z_if(r[i], bits.r[i]);
        }
        b.z_if(a1, bits.a1);
        p3(b, self, "i.sweepb");
        let cout = if produce {
            // SW-CARRY: jl is back to j_last and s0 = !q_0 is still live: c = a1 & [jl1..4 == 0] & !(jl0 & !s0)
            // (t = jl0 & !s0 on y, |0> after the sweep)
            prof(b, "i.swc");
            let c = b.alloc();
            let t = rt.y;
            let s0neg = !swc_break(2);
            if s0neg { b.x(rt.s0); }
            b.and_c(jl[0], rt.s0, t);
            if s0neg { b.x(rt.s0); }
            let mut l = vec![(a1, false)];
            l.extend(jl[1..R_BITS].iter().map(|&q| (q, true)));
            if !swc_break(1) {
                l.push((t, true));
            } else {
                l.push((jl[0], true));
            }
            and_auto(b, self, &l, c);
            if s0neg { b.x(rt.s0); }
            b.and_u(jl[0], rt.s0, t);
            if s0neg { b.x(rt.s0); }
            prof(b, "i.sweep");
            Some(c)
        } else { None };
        if !fl.is_empty() {
            // the OR rows free their lanes as they are erased; the chain rows above take AND lanes on demand
            assert!(self.room(b) >= R_BITS - or_ccz() as usize, "SWEEP_OR_LANES room");
            let ch2 = b.alloc_n(R_BITS - 1);
            sweep_bwd_ui(b, self, act, w, &rt, &ch2, &fl);
            b.free_n(&ch2);
        } else if sweep_unary() && self.room(b) >= 2 * R_BITS - 2 {
            let ch2 = b.alloc_n(2 * R_BITS - 2);
            sweep_bwd_ui(b, self, act, w, &rt, &ch2, &fl);
            b.free_n(&ch2);
        } else if self.room(b) >= R_BITS - 1 {
            let ch2 = b.alloc_n(R_BITS - 1);
            sweep_bwd(b, self, act, w, &rt, &ch2, true);
            b.free_n(&ch2);
        } else {
            sweep_bwd(b, self, act, w, &rt, &self.dirty, false);
        }
        if ylent {
            // YTOP-SWEEP: the backward sweep freed Y[W-1]'s lane |0>: take the same id back
            b.acquire(self.y[W - 1]);
        }
        // REPARK-X0: X[0] (outside the parked window) is a |0> decoder lane of the repark before it is set to 1
        let x0l = x0h && split && repark_x0() && park_lo(w) >= 1;
        if ytsw { zero_probe(b, &[self.y[W - 1]]); }
        if x0h {
            self.x[0] = b.alloc();
            if !x0l { b.x(self.x[0]); }
        }
        prof(b, "i.rows_rev");
        p3(b, self, "i.rows_rev");
        if !ytsw && ytop {
            b.x(self.y[W - 1]);
        }
        if split {
            // PARK-SPLIT: repark beside s0, r, a1; decoder lanes f, y, Y[W-1] (|0>) and the room
            rt.detach(b);
            z = b.alloc_n(zn);
            let mut tmp = vec![rt.f, rt.y, self.y[W - 1]];
            if x0l { tmp.push(self.x[0]); }
            zero_probe(b, &tmp);
            park_split_pass(b, self, w, &z, top, &tmp, true);
            if x0l { b.x(self.x[0]); }
        }
        p3(b, self, "i.unrowsrun");
        zero_probe(b, &lend);
        let room1 = self.room(b);
        self.cap += extra_rows();
        let own = pool_for(b, self, (NB + 1).saturating_sub(lend.len()), 0);
        self.cap -= extra_rows();
        let pool: Vec<QubitId> = own.iter().chain(&lend).copied().take(NB + 1).collect();
        if rowlog() {
            eprintln!("WL_ROW split {} partial {:?} room_park {room_park} masked {} park {} zn {} k {} mx {} room_rows {} room_rev {} lend {} pool_fwd {} pool_rev {} act_const {}",
                      split as u8, partial, masked_rows as u8, park as u8, zn, w.k, w.mx, room0, room1, lend.len(), pool_fwd_len, pool.len(), w.act_const as u8);
            eprintln!("WL_ROW2 dtop {} tight {} near {} la_cut {} x0h {} lo {} top {} ytop {} free_mode {}", w.dtop, w.dtop_tight as u8,
                      w.dtop_near as u8, la_cut as u8, x0h as u8, park_lo(w), top, ytop as u8, free_mode as u8);
        }
        b.begin();
        division_rows(b, self, w, &rt, &pool, park, top, partial,
                      if row_recs.is_empty() { RowRoll::No } else { RowRoll::Rev(&row_recs) });
        let unrows = b.end();
        b.play(&unrows, true);
        b.free_n(&own);
        zero_probe(b, &lend);
        if split {
            // PARK-SPLIT: final unpark on Y[W-1] (still |0>) and the freed row lanes
            rt.free(b);
            let mut tmp = vec![self.y[W - 1]];
            if x0l {
                b.x(self.x[0]);
                tmp.push(self.x[0]);
            }
            zero_probe(b, &tmp);
            park_split_pass(b, self, w, &z, top, &tmp, false);
            if x0l { b.x(self.x[0]); }
            zero_probe(b, &z);
            b.free_n(&z);
            if ytop {
                b.x(self.y[W - 1]);
            }
        } else {
        if ytop {
            b.x(self.y[W - 1]);
        }
        rt.free(b);
        }
        if split {
        } else if park {
            park_junk(b, self, w, &z, top);
            b.free_n(&z);
        } else if let Some(lo_p) = partial {
            park_junk_partial(b, self, &z, top, lo_p);
            b.free_n(&z);
        }
        if la_cut {
            for i in R_BITS..LB_BITS - 1 {
                self.la[i] = b.alloc();
            }
        }
        if la_sign {
            for i in R_BITS..LB_BITS - 1 {
                b.cx(self.la[LB_BITS - 1], self.la[i]);
            }
        }
        if masked_rows {
            add_const_sm(b, self, &self.la, UOFF, false);
        }
        zero_probe(b, &host);
        if free_mode {
            // re-bind fresh |0> lanes for the freed ones
            if lb_host() {
                for i in R_BITS..lb_top {
                    self.lb[i] = b.alloc();
                }
            }
            if sy_len < sy.len() {
                for i in sy_len..sy.len() {
                    sy[i] = b.alloc();
                }
            }
        }
        if lb_sign_clear {
            for i in R_BITS..LB_BITS - 1 {
                b.cx(self.lb[LB_BITS - 1], self.lb[i]);
            }
        }
        add_sm(b, self, &self.lb, &self.la, true, true);
        for &q in &self.lb {
            b.x(q);
        }
        add_sm(b, self, &self.lb, &sy, false, true);
        add_sm(b, self, &self.la, &sx, false, true);
        prof(b, "i.denorm");
        p3(b, self, "i.denorm");
        if ns0 && sw_carry() {
            // SW-CARRY: X's prep is the funnel alone on carried slots, and on the others the a-shift + funnel, whose lane
            // map and sX are the funnel's (a_X = 1 iff slack 1, where the funnel's stage 0 makes the same shift and
            // sX = 1): both are undone by the funnel's inverse. Y back by its a-shift, sY = [Y slack == 1] erased.
            for i in (0..NB).rev() {
                b.cswap(sy[0], self.y[i], self.y[i + 1]);
            }
            let mut l = act_lits(y_act);
            l.extend([(self.y[0], true), (self.y[1], false)]);
            erase_and(b, self, sy[0], &l);
            denorm_bottom(b, self, &self.x, &sx, None);
        } else if ns0 {
            // NORM-STAGE0 inverse: Y back by its a-shift (sY <= 1), sY = [Y slack == 1] erased; a_X = [sX == 1] back
            // into its own lane, the funnel undone on the funnel bits, X back by its a-shift, a_X = [X slack == 1] erased
            for i in (0..NB).rev() {
                b.cswap(sy[0], self.y[i], self.y[i + 1]);
            }
            let mut l = act_lits(y_act);
            l.extend([(self.y[0], true), (self.y[1], false)]);
            erase_and(b, self, sy[0], &l);
            let ax = b.alloc();
            let mut l = vec![(sx[0], false)];
            l.extend(sx[1..].iter().map(|&q| (q, true)));
            and_auto(b, self, &l, ax);
            b.cx(ax, sx[0]);
            denorm_bottom(b, self, &self.x, &sx, None);
            for i in (0..NB).rev() {
                b.cswap(ax, self.x[i], self.x[i + 1]);
            }
            erase_and(b, self, ax, &[(self.x[0], true), (self.x[1], false)]);
            b.free(ax);
        } else {
            denorm_bottom(b, self, &self.y, &sy, y_act);
            denorm_bottom(b, self, &self.x, &sx, None);
        }
        b.free_n(&sx);
        b.free_n(&sy);
        prof(b, "i.unrenorm");
        p3(b, self, "i.unrenorm");
        // I7, I8, I9
        add_sm(b, self, &self.la, &r, false, false);
        unrenorm_top(b, self, act, &r, gate_spec(&self.la, w));
        b.free_n(&r);
        prof(b, "i.value");
        p3(b, self, "i.value");
        // I10: value add-back where a1; d = a1 & the chain's carry out of lane W-1
        let mwa = masked_write_always();
        mark_done_inv(b, act, &self.lb);
        if mwa { mark_stall(b, act, a1, &self.lb); }
        let d = b.alloc();
        let pk = act.and_then(|a| act_park(b, a, &self.lb, w.lb));
        value_pass(b, self, w, false, a1, Some(d), mwa, Some(&bits.rv));
        if let Some(a) = act { act_unpark(b, a, &self.lb, pk); }
        if mwa { mark_stall(b, act, a1, &self.lb); }
        mark_done_inv(b, act, &self.lb);
        b.z_if(d, bits.d);
        prof(b, "i.cof");
        p3(b, self, "i.cof");
        // I11: cofactor undo (LA = LA_pre - d here)
        mark_done_inv(b, act, &self.la);
        if mwa { mark_stall(b, act, a1, &self.la); }
        let pk = act.and_then(|a| act_park(b, a, &self.la, w.lad));
        if lane0_direct() {
            // x0 = X[0] ^ d here (X[0] holds A's MSB = 1 where d = 1), in place
            let m = Masked::alloc_ladder_w(b, w.lad.1);
            b.cx(d, self.x[0]);
            let (t, s) = cof_ladder(self, w, self.x[0]);
            let src = cof_src(self, &m, w);
            let pool = pool_for(b, self, t.len() - (w.lad.1 - w.lad.0 + 1), 0);
            masked_pass(b, self, &t, &s, src, &m, true, Some(a1), None, &pool, mwa, w.a1_const, Some(&bits.rc));
            b.free_n(&pool);
            b.cx(d, self.x[0]);
            m.free(b);
        } else {
            let m = Masked::alloc_ladder_w(b, w.lad.1);
            let x0 = b.alloc();
            lane0_src(b, self, d, x0);
            let (t, s) = cof_ladder(self, w, x0);
            let src = cof_src(self, &m, w);
            // carry pool over the ordinary lanes below the LA - d window
            let pool = pool_for(b, self, t.len() - (w.lad.1 - w.lad.0 + 1), 0);
            masked_pass(b, self, &t, &s, src, &m, true, Some(a1), None, &pool, mwa, w.a1_const, Some(&bits.rc));
            b.free_n(&pool);
            lane0_src(b, self, d, x0);
            b.free(x0);
            m.free(b);
        }
        if let Some(a) = act { act_unpark(b, a, &self.la, pk); }
        if mwa { mark_stall(b, act, a1, &self.la); }
        mark_done_inv(b, act, &self.la);
        prof(b, "i.dundo");
        p3(b, self, "i.dundo");
        // I12, I13, I14
        {
            let anc = b.alloc_n(LB_BITS - 1);
            super::arith::inc(b, d, &self.la, &anc);
            b.free_n(&anc);
        }
        crot_down(b, d, &self.x, 1);
        mark_msb(b, a1, &self.lb);
        erase_mbu(b, d, |b| top_compare(b, self, None, w, Some((a1, false))));
        mark_msb(b, a1, &self.lb);
        b.free(d);
        prof(b, "i.end15");
        p3(b, self, "i.end15");
        // I15: a1 = act & X[W-1] on the restored pre-state
        let mut lits = act_lits(act);
        lits.push((self.x[W - 1], false));
        erase_mbu(b, a1, |b| phase_and(b, &lits));
        b.free(a1);
        if let Some(z0) = z0 {
            b.x(z0); // z0 = done flag again
            self.cnt_dec(b, z0);
            let zl: Vec<(QubitId, bool)> = self.la.iter().map(|&q| (q, true)).collect();
            erase_and(b, self, z0, &zl);
            b.free(z0);
        }
        prof(b, "end");
        p3(b, self, "end");
        cout
    }
}

/// S1-014 ACT_PARK (odinfree fe65245b Fuerobebier): while the length register v (LB in the value pass, LA - d in the
/// cofactor pass) is done-marked (v_i = len_i ^ !act), a lane i in 1..8 whose bit is 0 for every length in the slot's
/// window (and on finished shots, whose length is 0 or 1) holds !act on every non-failing shot, so the act lane is
/// erased onto it (act ^= !v_i) and left free across the pass, then rebuilt. Shots outside the window already fail
/// (Lambda kinds LB / LA-d). Dev override `WL_ACT_PARK=0|1`.
pub const ACT_PARK: bool = true;
fn act_park_on() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("ACT_PARK", ACT_PARK));
    *E
}
fn act_park(b: &mut B, act: QubitId, v: &[QubitId], win: (usize, usize)) -> Option<usize> {
    if !act_park_on() {
        return None;
    }
    let i = (1..LB_BITS - 1).rev().find(|&i| (win.0..=win.1).all(|x| (x >> i) & 1 == 0))?;
    // negative control for the gate tests only: P3_BREAK=4 parks on bit 0 (not constant)
    let i = if cfg!(test) && std::env::var("P3_BREAK").map_or(false, |v| v.trim() == "4") { 0 } else { i };
    b.x(v[i]);
    b.cx(v[i], act);
    b.x(v[i]);
    b.free(act);
    Some(i)
}
fn act_unpark(b: &mut B, act: QubitId, v: &[QubitId], i: Option<usize>) {
    let Some(i) = i else { return };
    b.acquire(act);
    b.x(v[i]);
    b.cx(v[i], act);
    b.x(v[i]);
}

/// While z0 holds act (= !done), XOR !act into the counter: finished shots read all ones.
fn mark_done_inv(b: &mut B, act: Option<QubitId>, v: &[QubitId]) {
    let Some(act) = act else { return };
    b.x(act);
    for &q in v {
        b.cx(act, q);
    }
    b.x(act);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::Simulator;
    use super::super::greedyfrog_model::{Lanes, Spec, N};
    use sha3::digest::{ExtendableOutput, Update};

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn input(&mut self) -> N {
            let pp = super::super::greedyfrog_model::p();
            loop {
                let mut v = N::ZERO;
                for i in 0..4 {
                    v |= N::from(self.next()) << (64 * i);
                }
                if v != N::ZERO && v < pp {
                    // the shell reflects dx below p/2: x > p/2 makes the first quotient 1 and the second level start
                    // with equal cofactors (tA = tB = 1), which the decode's floor(tA / tB) cannot read
                    let w = pp - v;
                    return if v < w { v } else { w };
                }
            }
        }
    }

    fn load<R: sha3::digest::XofReader>(sim: &mut Simulator<'_, R>, u: &GreedyFrog, shot: usize, st: &Lanes) {
        let bit = 1u64 << shot;
        let mut set = |q: QubitId, v: bool| {
            if v {
                sim.qubits[q.0 as usize] |= bit;
            }
        };
        for j in 0..W {
            set(u.x[j], st.x[j] == 1);
            // finished shots: Y lanes 0..8 are all ones in the model, the circuit's counter is their complement
            let flip = j < CNT_BITS && (st.cnt >> j) & 1 == 1;
            set(u.y[j], (st.y[j] == 1) != flip);
        }
        for i in 0..LB_BITS {
            set(u.la[i], (st.la >> i) & 1 == 1);
            set(u.lb[i], (st.lb >> i) & 1 == 1);
        }
        set(u.par, st.par == 1);
        for (i, &q) in u.dirty.iter().enumerate() {
            set(q, dirty_bit(shot, i));
        }
    }

    /// the random contents the tests load into the borrowed lanes
    fn dirty_bit(shot: usize, lane: usize) -> bool {
        let h = (shot as u64 + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (lane as u64 + 7).wrapping_mul(0xc2b2_ae3d_27d4_eb4f);
        (h ^ (h >> 29)) & 1 == 1
    }

    /// Apply ops[lo..hi), asserting at every recorded zero probe in that range that its lanes are |0> on all shots.
    fn apply_probed<R: sha3::digest::XofReader>(sim: &mut Simulator<'_, R>, ops: &[crate::circuit::Op], lo: usize, hi: usize,
                                                probes: &[(usize, Vec<QubitId>)]) -> usize {
        let mut pos = lo;
        let mut n = 0;
        for (at, lanes) in probes.iter().filter(|(a, _)| *a >= lo && *a < hi) {
            sim.apply_iter(ops[pos..*at].iter());
            pos = *at;
            for &q in lanes {
                assert_eq!(sim.qubits[q.0 as usize], 0, "hosted lane q{} not |0> at op {at}", q.0);
            }
            n += 1;
        }
        sim.apply_iter(ops[pos..hi].iter());
        n
    }

    fn check_dirty<R: sha3::digest::XofReader>(sim: &Simulator<'_, R>, u: &GreedyFrog, shots: usize) {
        for s in 0..shots {
            for (i, &q) in u.dirty.iter().enumerate() {
                assert_eq!((sim.qubits[q.0 as usize] >> s) & 1 == 1, dirty_bit(s, i), "shot {s}: borrowed lane {i} not restored");
            }
        }
    }

    fn read<R: sha3::digest::XofReader>(sim: &Simulator<'_, R>, u: &GreedyFrog, shot: usize) -> Lanes {
        let g = |q: QubitId| ((sim.qubits[q.0 as usize] >> shot) & 1) as u8;
        let num = |v: &[QubitId]| v.iter().enumerate().map(|(i, &q)| (g(q) as usize) << i).sum::<usize>();
        let mut y: Vec<u8> = u.y.iter().map(|&q| g(q)).collect();
        let la = num(&u.la);
        let cnt = if la == 0 { (!num(&u.cnt)) & ((1 << CNT_BITS) - 1) } else { 0 };
        if la == 0 {
            for v in y.iter_mut().take(CNT_BITS) {
                *v = 1;
            }
        }
        Lanes { x: u.x.iter().map(|&q| g(q)).collect(), y, la, lb: num(&u.lb), cnt, par: g(u.par) }
    }

    /// and_dirty on every literal count 1..=8 with random negations: out flips iff the AND holds, every control and
    /// borrowed lane comes back unchanged (64 random shots per count, 4 rounds).
    #[test]
    fn greedyfrog_and_dirty_exact() {
        let mut rng = Rng(0xd1d1_7777_0000_1111);
        for n in 1..=8usize {
            for round in 0..4 {
                let mut b = B::new();
                let c = b.alloc_n(n);
                let out = b.alloc();
                let d = b.alloc_n(n.saturating_sub(2));
                let neg: Vec<bool> = (0..n).map(|_| rng.next() & 1 == 1).collect();
                let lits: Vec<(QubitId, bool)> = c.iter().zip(&neg).map(|(&q, &g)| (q, g)).collect();
                and_dirty(&mut b, &lits, out, &d);
                let mut h = sha3::Shake256::default();
                h.update(b"greedyfrog-and-dirty");
                h.update(&[n as u8, round as u8]);
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(b.width() as usize, 64, &mut xof);
                let init: Vec<u64> = (0..b.width()).map(|_| rng.next()).collect();
                for (q, &v) in init.iter().enumerate() {
                    sim.qubits[q] = v;
                }
                sim.apply_iter(b.ops.iter());
                let mut want = init[out.0 as usize];
                let mut all = !0u64;
                for (i, &q) in c.iter().enumerate() {
                    all &= if neg[i] { !init[q.0 as usize] } else { init[q.0 as usize] };
                }
                want ^= all;
                assert_eq!(sim.qubits[out.0 as usize], want, "n {n} round {round}: wrong AND");
                for &q in c.iter().chain(&d) {
                    assert_eq!(sim.qubits[q.0 as usize], init[q.0 as usize], "n {n} round {round}: lane not restored");
                }
                assert_eq!(sim.phase, 0);
            }
        }
    }

    /// B-CRUMBS SWF-LEX: lt_pooled_c with a quantum carry-in and the Cuccaro form up(a, bb, cin) give
    /// out ^= [a < bb + cin] (or that phase), every lane restored.
    #[test]
    fn crumbs_lt_cin_exact() {
        let mut rng = Rng(0xc0c0_1234_5678_9abc);
        for n in 1..=9usize {
            for mode in 0..4 {
                let mut b = B::new();
                let a = b.alloc_n(n);
                let bb = b.alloc_n(n);
                let cin = b.alloc();
                let out = b.alloc();
                let pooled = mode & 1 == 0;
                let phase = mode & 2 != 0;
                if pooled {
                    lt_pooled_c(&mut b, &a, &bb, Cy::Q(cin), if phase { None } else { Some(out) });
                } else {
                    let ru = super::super::arith::up(&mut b, &a, &bb, cin);
                    b.play(&ru, false);
                    if phase { b.z(bb[n - 1]); } else { b.cx(bb[n - 1], out); }
                    b.play(&ru, true);
                }
                let mut h = sha3::Shake256::default();
                h.update(b"crumbs-lt-cin");
                h.update(&[n as u8, mode as u8]);
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(b.width() as usize, 64, &mut xof);
                let init: Vec<u64> = (0..b.width()).map(|_| rng.next()).collect();
                let anc0 = 2 * n + 2;
                for (q, &v) in init.iter().enumerate() {
                    sim.qubits[q] = if q >= anc0 { 0 } else { v };
                }
                sim.apply_iter(b.ops.iter());
                let mut want = 0u64;
                for sh in 0..64 {
                    let bit = |q: QubitId| (init[q.0 as usize] >> sh) & 1;
                    let av: u64 = (0..n).map(|i| bit(a[i]) << i).sum();
                    let bv: u64 = (0..n).map(|i| bit(bb[i]) << i).sum();
                    if av < bv + bit(cin) { want |= 1 << sh; }
                }
                if phase {
                    assert_eq!(sim.phase, want, "n {n} mode {mode}: wrong phase");
                    assert_eq!(sim.qubits[out.0 as usize], init[out.0 as usize]);
                } else {
                    assert_eq!(sim.phase, 0, "n {n} mode {mode}: phase garbage");
                    assert_eq!(sim.qubits[out.0 as usize], init[out.0 as usize] ^ want, "n {n} mode {mode}: wrong compare");
                }
                for &q in a.iter().chain(&bb).chain(std::iter::once(&cin)) {
                    assert_eq!(sim.qubits[q.0 as usize], init[q.0 as usize], "n {n} mode {mode}: lane not restored");
                }
                for q in anc0..b.width() as usize {
                    assert_eq!(sim.qubits[q], 0, "n {n} mode {mode}: scratch dirty");
                }
            }
        }
    }

    /// One forward slot, 64 shots at random slots (including finished shots), against the lane model.
    #[test]
    fn greedyfrog_fwd_slot_gate_level() {
        let mut b = B::new();
        let mut u = GreedyFrog::alloc(&mut b);
        let start = b.ops.len();
        let _bits = u.fwd_slot(&mut b, &Win::full());
        eprintln!("greedyfrog fwd slot: {} ops, {} Toffoli, live {} peak {}", b.ops.len() - start, b.tof, b.live, b.peak);
        let mut rng = Rng(0xfeed_beef_0101_2323);
        for round in 0..4 {
            let mut states = vec![];
            for _ in 0..64 {
                let x = rng.input();
                let mut sp = Spec::new(x);
                let slot = (rng.next() % 260) as usize;
                for _ in 0..slot {
                    sp.fwd();
                }
                states.push(Lanes::from_spec(&sp));
            }
            let mut h = sha3::Shake256::default();
            h.update(b"greedyfrog-fwd-slot");
            h.update(&[round as u8]);
            let mut xof = h.finalize_xof();
            let nbits = 20_000 + 64;
            let mut sim = Simulator::new(b.width() as usize, nbits, &mut xof);
            for (s, st) in states.iter().enumerate() {
                load(&mut sim, &u, s, st);
            }
            sim.apply_iter(b.ops.iter());
            check_dirty(&sim, &u, 64);
            for (s, st) in states.iter().enumerate() {
                let mut want = st.clone();
                want.fwd();
                let got = read(&sim, &u, s);
                assert_eq!(got, want, "round {round} shot {s}: slot mismatch (la {} lb {} cnt {})", st.la, st.lb, st.cnt);
            }
        }
    }

    /// Forward slot then inverse slot on 64 shots (random slots, finished shots included): the state, the phase and
    /// every scratch qubit must come back to their starting values.
    #[test]
    fn greedyfrog_fwd_inv_roundtrip_gate_level() {
        let mut b = B::new();
        let mut u = GreedyFrog::alloc(&mut b);
        let u0 = u.clone();
        let t0 = b.tof;
        let bits = u.fwd_slot(&mut b, &Win::full());
        let t1 = b.tof;
        u.inv_slot(&mut b, &bits, &Win::full());
        eprintln!("greedyfrog slot pair: fwd {} T, inv {} T, peak {}", t1 - t0, b.tof - t1, b.peak);
        prof_dump();
        let probes = take_zero_probes();
        let mut regs: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
        for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par)).chain(&u.dirty) {
            regs.insert(q.0);
        }
        let mut rng = Rng(0x1357_9bdf_2468_ace0);
        let rounds: usize = std::env::var("GREEDYFROG_ROUNDS").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
        for round in 0..rounds {
            let mut states = vec![];
            for _ in 0..64 {
                let x = rng.input();
                let mut sp = Spec::new(x);
                let slot = (rng.next() % 260) as usize;
                for _ in 0..slot {
                    sp.fwd();
                }
                states.push(Lanes::from_spec(&sp));
            }
            let mut h = sha3::Shake256::default();
            h.update(b"greedyfrog-roundtrip");
            h.update(&[round as u8]);
            let mut xof = h.finalize_xof();
            let nbits_rt = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0]).filter(|&v| v != crate::circuit::NO_BIT.0)
                .max().unwrap_or(0) as usize + 1;
            let mut sim = Simulator::new(b.width() as usize, nbits_rt.max(20_000 + 64), &mut xof);
            for (s, st) in states.iter().enumerate() {
                load(&mut sim, &u0, s, st);
            }
            let np = apply_probed(&mut sim, &b.ops, 0, b.ops.len(), &probes);
            assert_eq!(np, probes.len());
            check_dirty(&sim, &u, 64);
            assert_eq!(sim.phase, 0, "round {round}: phase garbage {:016x}", sim.phase);
            for q in 0..b.width() {
                if !regs.contains(&q) {
                    assert_eq!(sim.qubits[q as usize], 0, "round {round}: scratch qubit {q} dirty");
                }
            }
            for (s, st) in states.iter().enumerate() {
                assert_eq!(&read(&sim, &u, s), st, "round {round} shot {s}: state not restored (la {} lb {} cnt {})",
                           st.la, st.lb, st.cnt);
            }
        }
    }

    /// B-ROLL gate test (ROLL-FWD, batch7 s4 experiment 1): F4 (value_pass, cmpl) built with the current ROLL levers,
    /// then directly its I10 with the z_if repairs, at each listed slot's window, on 64 random shots per round: active
    /// (a1 = 1, LB in the window), stalled (act & !a1, LB anywhere in 1..256, stall-marked) and finished (act = 0, LB = 1,
    /// done-marked) shots. Checks the forward against the arithmetic (top LB lanes of X minus Y's, X[0] ^= a1 & borrow),
    /// then the identity: every register restored, d = a1 & borrow, scratch clean, phase 0. ROLL_BREAK=k must fail.
    #[test]
    fn roll_value_pair_gate_level() {
        let list: Vec<usize> = std::env::var("ROLL_SLOTS").ok()
            .map(|v| v.split(',').map(|t| t.parse().unwrap()).collect())
            .unwrap_or(vec![0, 1, 3, 12, 30, 45, 80, 140, 200, 225, 245, NSLOTS - 1]);
        let rounds: usize = std::env::var("GREEDYFROG_ROUNDS").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
        let ws = windows();
        let mut rng = Rng(0x5011_f00d_0028_0004);
        let mwa = masked_write_always();
        for &slot in &list {
            let w = &ws[slot];
            let mut b = B::new();
            let u = GreedyFrog::alloc(&mut b);
            let act = b.alloc();
            let a1 = b.alloc();
            super::super::mask::set_borrowed(&u.dirty);
            let t0 = b.tof;
            mark_done_inv(&mut b, Some(act), &u.lb);
            if mwa { mark_stall(&mut b, Some(act), a1, &u.lb); }
            let rv = value_pass(&mut b, &u, w, true, a1, None, mwa, None);
            if mwa { mark_stall(&mut b, Some(act), a1, &u.lb); }
            mark_done_inv(&mut b, Some(act), &u.lb);
            let mid = b.ops.len();
            let t1 = b.tof;
            mark_done_inv(&mut b, Some(act), &u.lb);
            if mwa { mark_stall(&mut b, Some(act), a1, &u.lb); }
            let d = b.alloc();
            value_pass(&mut b, &u, w, false, a1, Some(d), mwa, Some(&rv));
            if mwa { mark_stall(&mut b, Some(act), a1, &u.lb); }
            mark_done_inv(&mut b, Some(act), &u.lb);
            let nrec = rv.rc.iter().filter(|r| r.is_some()).count() + rv.fb.is_some() as usize;
            eprintln!("roll value slot {slot} lb {:?}: F4 {} T, I10 {} T, receipts {nrec}, peak {}", w.lb, t1 - t0, b.tof - t1, b.peak);
            let mut regs: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
            for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.dirty).chain([&u.par, &act, &a1, &d]) {
                regs.insert(q.0);
            }
            let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0]).filter(|&v| v != crate::circuit::NO_BIT.0)
                .max().unwrap_or(0) as usize + 1;
            let hi_ok = w.lb.1.min(W - 1);
            for round in 0..rounds {
                let mut h = sha3::Shake256::default();
                h.update(b"roll-value-pair");
                h.update(&[round as u8, slot as u8]);
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(b.width() as usize, nbits, &mut xof);
                // per shot: (kind 0 active / 1 stall / 2 done, LB, X, Y)
                let mut shots = vec![];
                for sh in 0..64usize {
                    let kind = if w.a1_const { 0 } else { [0, 0, 0, 0, 0, 0, 1, 2][sh % 8] };
                    let lbv = match kind {
                        0 => w.lb.0 + (rng.next() as usize) % (hi_ok - w.lb.0 + 1),
                        1 => 1 + (rng.next() as usize) % 255,
                        _ => 1,
                    };
                    let xs: Vec<bool> = (0..W).map(|_| rng.next() & 1 == 1).collect();
                    let ys: Vec<bool> = (0..W).map(|_| rng.next() & 1 == 1).collect();
                    let bit = 1u64 << sh;
                    for j in 0..W {
                        if xs[j] { sim.qubits[u.x[j].0 as usize] |= bit; }
                        if ys[j] { sim.qubits[u.y[j].0 as usize] |= bit; }
                    }
                    for i in 0..LB_BITS {
                        if (lbv >> i) & 1 == 1 { sim.qubits[u.lb[i].0 as usize] |= bit; }
                    }
                    if kind != 2 { sim.qubits[act.0 as usize] |= bit; }
                    if kind == 0 { sim.qubits[a1.0 as usize] |= bit; }
                    for (i, &q) in u.dirty.iter().enumerate() {
                        if dirty_bit(sh, i) { sim.qubits[q.0 as usize] |= bit; }
                    }
                    shots.push((kind, lbv, xs, ys));
                }
                let init: Vec<u64> = sim.qubits.clone();
                sim.apply_iter(b.ops[..mid].iter());
                let mut borrow = 0u64;
                for (sh, (kind, lbv, xs, ys)) in shots.iter().enumerate() {
                    let mut want = xs.clone();
                    if *kind == 0 {
                        let mut br = false;
                        for j in W - lbv..W {
                            let (xv, yv) = (xs[j] as u8, ys[j] as u8);
                            let dv = xv ^ yv ^ br as u8;
                            br = (xv as i8 - yv as i8 - br as i8) < 0;
                            want[j] = dv == 1;
                        }
                        if br {
                            want[0] = !want[0];
                            borrow |= 1 << sh;
                        }
                    }
                    for j in 0..W {
                        assert_eq!((sim.qubits[u.x[j].0 as usize] >> sh) & 1 == 1, want[j],
                                   "slot {slot} round {round} shot {sh} (kind {kind} lb {lbv}): F4 lane {j} wrong");
                    }
                }
                sim.apply_iter(b.ops[mid..].iter());
                assert_eq!(sim.phase, 0, "slot {slot} round {round}: phase garbage {:016x}", sim.phase);
                assert_eq!(sim.qubits[d.0 as usize], borrow, "slot {slot} round {round}: d != a1 & borrow");
                for q in 0..b.width() as u64 {
                    if q == d.0 { continue; }
                    let want = if regs.contains(&q) { init[q as usize] } else { 0 };
                    assert_eq!(sim.qubits[q as usize], want, "slot {slot} round {round}: qubit {q} not restored");
                }
            }
        }
    }

    /// Windowed slots: for each listed slot s, forward then inverse slot with the slot's windows on 64 shots that
    /// are at slot s of their walks (forward result checked against the lane model, then the round trip).
    #[test]
    fn greedyfrog_windowed_slots_gate_level() {
        let list: Vec<usize> = std::env::var("GREEDYFROG_SLOTS").ok()
            .map(|v| v.split(',').map(|t| t.parse().unwrap()).collect())
            .unwrap_or(vec![0, 1, 3, 12, 30, 45, 80, 140, 200, 225, 245, NSLOTS - 1]);
        let ws = windows();
        let rounds: usize = std::env::var("GREEDYFROG_ROUNDS").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        let mut rng = Rng(0x7777_1234_5678_9abc);
        // GREEDYFROG_WIN_STALL=n (B-WALK2, WK19 gate test 2): walk n random inputs on the model and, per slot, put up to
        // 40 inputs whose walk STALLS at that slot (act, lag > 0: a1 = 0) into each 64-shot batch (~0.6 per batch at random)
        let stall_pool: Vec<Vec<N>> = match std::env::var("GREEDYFROG_WIN_STALL").ok().and_then(|v| v.parse::<usize>().ok()) {
            None => vec![],
            Some(n) => {
                let mut pool = vec![vec![]; NSLOTS];
                let mut prng = Rng(0x5747_4c4c_0019_0002);
                for _ in 0..n {
                    let x = prng.input();
                    let mut sp = Spec::new(x);
                    for s in 0..NSLOTS {
                        if sp.la != 0 && sp.lag > 0 {
                            pool[s].push(x);
                        }
                        sp.fwd();
                    }
                }
                eprintln!("WIN_STALL pool: {n} walks, stalls per slot min {} max {}", pool.iter().map(|v| v.len()).min().unwrap(),
                          pool.iter().map(|v| v.len()).max().unwrap());
                pool
            }
        };
        // GREEDYFROG_WIN_SHORT=n (B-LANES2, PARK-SPLIT): walk n random inputs; per masked slot keep the inputs whose
        // divisor after the decode's un-swap is SHORT (mX in [floor, floor + 12], floor = w.mx - 1: the lanes the park
        // actually moves) and force up to 40 of them into each batch (the parked/unparked junk is then non-trivial)
        let short_pool: Vec<Vec<N>> = match std::env::var("GREEDYFROG_WIN_SHORT").ok().and_then(|v| v.parse::<usize>().ok()) {
            None => vec![],
            Some(n) => {
                let mut pool = vec![vec![]; NSLOTS];
                let mut prng = Rng(0x4c41_4e45_5332_0001);
                let slack = |ring: &[u8]| (0..31).take_while(|&j| ring[j] == 0).count();
                for _ in 0..n {
                    let x = prng.input();
                    let mut sp = Spec::new(x);
                    for s in 0..48.min(NSLOTS) {
                        let mut q = sp.clone();
                        q.fwd();
                        let st = Lanes::from_spec(&q);
                        let (sx, sy) = (slack(&st.x), slack(&st.y));
                        let mxv = CW as isize - ((st.la + sx) % 512) as isize;
                        let mxw = CW as isize - ((st.lb + sy) % 512) as isize;
                        let md = mxv.min(mxw);
                        let fl = ws[s].mx as isize - 1;
                        if ws[s].mx < NB + 1 && md >= fl && md <= fl + 12 && pool[s].len() < 4096 {
                            pool[s].push(x);
                        }
                        sp.fwd();
                    }
                }
                eprintln!("WIN_SHORT pool: {n} walks, short-divisor inputs per slot {:?}",
                          pool.iter().take(48).map(|v| v.len()).collect::<Vec<_>>());
                pool
            }
        };
        let mut stall_shots = 0usize;
        let mut short_shots = 0usize;
        for &slot in &list {
            let w = &ws[slot];
            let mut b = B::new();
            let mut u = GreedyFrog::alloc(&mut b);
            let u0 = u.clone();
            let t0 = b.tof;
            let bits = u.fwd_slot(&mut b, w);
            let mid = b.ops.len();
            let t1 = b.tof;
            // SW-CARRY pair mode: forward slot s + 1 and its inverse (standard I2, producing the carry) run between
            // slot s's forward and inverse, so slot s's inverse takes the carried flag (GREEDYFROG_SWC_SINGLE=1: off)
            let pair = sw_carry() && slot + 1 < NSLOTS && std::env::var_os("GREEDYFROG_SWC_SINGLE").is_none();
            if pair {
                let w1 = &ws[slot + 1];
                let bits1 = u.fwd_slot(&mut b, w1);
                let c = u.inv_slot_c(&mut b, &bits1, w1, None, true);
                eprintln!("SWC_PAIR slot {slot}: carried {}", c.is_some());
                let c2 = u.inv_slot_c(&mut b, &bits, w, c, false);
                assert!(c2.is_none());
            } else {
                u.inv_slot(&mut b, &bits, w);
            }
            eprintln!("greedyfrog slot {slot} {:?}: fwd {} T, inv {} T, peak {}", w, t1 - t0, b.tof - t1, b.peak);
            prof_dump();
            let probes = take_zero_probes();
            let mut regs: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
            for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par)).chain(&u.dirty) {
                regs.insert(q.0);
            }
            for round in 0..rounds {
                let mut states = vec![];
                for i in 0..64 {
                    let forced = if i < 40 { stall_pool.get(slot).and_then(|v| v.get(round * 40 + i)).copied() } else { None };
                    let short = if i < 40 && forced.is_none() {
                        short_pool.get(slot).and_then(|v| if v.is_empty() { None } else { v.get((round * 40 + i) % v.len()) }).copied()
                    } else { None };
                    if short.is_some() {
                        short_shots += 1;
                    }
                    let x = forced.or(short).unwrap_or_else(|| rng.input());
                    let mut sp = Spec::new(x);
                    for _ in 0..slot {
                        sp.fwd();
                    }
                    if forced.is_some() {
                        assert!(sp.la != 0 && sp.lag > 0);
                        stall_shots += 1;
                    }
                    states.push(Lanes::from_spec(&sp));
                }
                let mut h = sha3::Shake256::default();
                h.update(b"greedyfrog-windowed");
                h.update(&[round as u8, slot as u8]);
                let mut xof = h.finalize_xof();
                let nbits_rt = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0])
                    .filter(|&v| v != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1;
                let mut sim = Simulator::new(b.width() as usize, nbits_rt.max(20_000 + 64), &mut xof);
                for (sh, st) in states.iter().enumerate() {
                    load(&mut sim, &u0, sh, st);
                }
                sim.apply_iter(b.ops[..mid].iter());
                check_dirty(&sim, &u, 64);
                for (sh, st) in states.iter().enumerate() {
                    let mut want = st.clone();
                    want.fwd();
                    assert_eq!(read(&sim, &u0, sh), want, "slot {slot} round {round} shot {sh}: forward mismatch");
                }
                apply_probed(&mut sim, &b.ops, mid, b.ops.len(), &probes);
                check_dirty(&sim, &u, 64);
                assert_eq!(sim.phase, 0, "slot {slot} round {round}: phase garbage {:016x}", sim.phase);
                for q in 0..b.width() {
                    if !regs.contains(&q) {
                        assert_eq!(sim.qubits[q as usize], 0, "slot {slot} round {round}: scratch qubit {q} dirty");
                    }
                }
                for (sh, st) in states.iter().enumerate() {
                    assert_eq!(&read(&sim, &u, sh), st, "slot {slot} round {round} shot {sh}: state not restored");
                }
            }
        }
        if !stall_pool.is_empty() {
            eprintln!("WIN_STALL: {stall_shots} forced stall shots checked exact");
        }
        if !short_pool.is_empty() {
            eprintln!("WIN_SHORT: {short_shots} forced short-divisor shots checked exact");
        }
    }

    /// Full traversal: 300 forward slots (final state checked against the model: A = 0, B = 1, tA = p,
    /// tB = +-1/x), then 300 inverse slots back to the start (phase 0, scratch clean). 64 shots.
    #[test]
    fn greedyfrog_traversal_gate_level() {
        if std::env::var("GREEDYFROG_TRAV").is_err() {
            return;
        }
        const NS: usize = NSLOTS;
        let ws = windows();
        let mut b = B::new();
        let mut u = GreedyFrog::alloc(&mut b);
        let u0 = u.clone();
        let mut all_bits = vec![];
        let t0 = b.tof;
        for s in 0..NS {
            all_bits.push(u.fwd_slot(&mut b, &ws[s]));
        }
        let mid_ops = b.ops.len();
        let t1 = b.tof;
        let peak_fwd = b.peak;
        let mut carry = None;
        let mut carried = 0;
        for (s, bits) in all_bits.iter().enumerate().rev() {
            carried += carry.is_some() as usize;
            carry = u.inv_slot_c(&mut b, bits, &ws[s], carry, s >= 1);
        }
        assert!(carry.is_none());
        eprintln!("greedyfrog traversal: SW-CARRY {} inverse slots took a carried swap flag", carried);
        eprintln!("greedyfrog traversal: forward {} T, inverse {} T, ops {} (+{}), peak {} (forward {})", t1 - t0, b.tof - t1,
                  mid_ops, b.ops.len() - mid_ops, b.peak, peak_fwd);
        prof_dump();
        let probes = take_zero_probes();
        let mut regs: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
        for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par)).chain(&u.dirty) {
            regs.insert(q.0);
        }
        let mut rng = Rng(0x2468_1357_aaaa_5555);
        let mut starts = vec![];
        let mut finals = vec![];
        let mut xs = vec![];
        // GREEDYFROG_TRAV_X: comma-separated hex inputs replacing the first shots (diagnosis of eval shots)
        let forced: Vec<N> = std::env::var("GREEDYFROG_TRAV_X").ok().map(|v| v.split(',')
            .map(|t| N::from_str_radix(t.trim().trim_start_matches("0x"), 16).unwrap()).collect()).unwrap_or_default();
        for i in 0..64 {
            let x = if i < forced.len() { forced[i] } else { rng.input() };
            let mut sp = Spec::new(x);
            starts.push(Lanes::from_spec(&sp));
            for _ in 0..NS {
                sp.fwd();
            }
            finals.push(Lanes::from_spec(&sp));
            xs.push(x);
        }
        // forward half
        let mut h = sha3::Shake256::default();
        h.update(b"greedyfrog-traversal");
        let mut xof = h.finalize_xof();
        // every classical bit the stream writes or reads (the inverse's measured erases need far more than 8 per slot)
        let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0]).filter(|&v| v != crate::circuit::NO_BIT.0)
            .max().unwrap_or(0) as usize + 1;
        let mut sim = Simulator::new(b.width() as usize, nbits, &mut xof);
        for (s, st) in starts.iter().enumerate() {
            load(&mut sim, &u0, s, st);
        }
        sim.apply_iter(b.ops[..mid_ops].iter());
        check_dirty(&sim, &u, 64);
        // GREEDYFROG_TRAV_SOFT=1 (B-WALK2): report every failing shot (forward vs model, phase, scratch, round trip) as
        // one TRAV_SOFT line instead of stopping at the first, for lever-on / lever-off comparisons of forced inputs
        if std::env::var_os("GREEDYFROG_TRAV_SOFT").is_some() {
            let mut fwd_bad = 0u64;
            for s in 0..64 {
                if read(&sim, &u0, s) != finals[s] {
                    fwd_bad |= 1 << s;
                }
            }
            sim.apply_iter(b.ops[mid_ops..].iter());
            let mut scratch = 0u64;
            for q in 0..b.width() {
                if !regs.contains(&q) {
                    scratch |= sim.qubits[q as usize];
                }
            }
            let mut rt_bad = 0u64;
            for s in 0..64 {
                if read(&sim, &u, s) != starts[s] {
                    rt_bad |= 1 << s;
                }
            }
            eprintln!("TRAV_SOFT fwd {fwd_bad:016x} phase {:016x} scratch {scratch:016x} roundtrip {rt_bad:016x}", sim.phase);
            return;
        }
        for s in 0..64 {
            let got = read(&sim, &u0, s);
            assert_eq!(got, finals[s], "shot {s}: final state differs from the model");
            let sp = got.to_spec();
            let pp = super::super::greedyfrog_model::p();
            assert!(sp.a == N::ZERO && sp.b == N::from(1u64) && sp.ta == pp);
            let t = sp.tb.mul_mod(xs[s], pp);
            assert!(t == N::from(1u64) || t == pp - N::from(1u64), "shot {s}: tB is not +-1/x");
        }
        let np = apply_probed(&mut sim, &b.ops, mid_ops, b.ops.len(), &probes);
        eprintln!("greedyfrog traversal: {np} zero probes checked");
        check_dirty(&sim, &u, 64);
        assert_eq!(sim.phase, 0, "phase garbage {:016x}", sim.phase);
        for q in 0..b.width() {
            if !regs.contains(&q) {
                assert_eq!(sim.qubits[q as usize], 0, "scratch qubit {q} dirty");
            }
        }
        for s in 0..64 {
            if read(&sim, &u, s) != starts[s] {
                eprintln!("TRAV_FAIL shot {s}: start not restored");
            }
        }
        for s in 0..64 {
            assert_eq!(read(&sim, &u, s), starts[s], "shot {s}: start not restored");
        }
        eprintln!("greedyfrog traversal: 64 shots exact, round trip clean");
    }
}

#[cfg(test)]
mod reflection_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{Update,ExtendableOutput};
    #[test]
    fn reflection_barrel_and_prefix_exact() {
        // Exhaust all 256 top-byte patterns with both values of act. For each,
        // compare the whole ring to the independent binary-search implementation.
        for batch in 0..8 {
            let build=|new:bool| {
                let mut b=B::new(); let x=b.alloc_n(W); let a=b.alloc(); let r=b.alloc_n(3);
                if new {renorm_top(&mut b,&x,Some(a),&r,None);} else {renorm_top_legacy(&mut b,&x,Some(a),&r);}
                (b,x,a,r)
            };
            let run=|new:bool| {
                let (b,x,a,r)=build(new);
                let mut h=sha3::Shake256::default();h.update(b"reflection-exact");
                let mut xof=h.finalize_xof();let mut sim=Simulator::new(b.width() as usize,20000,&mut xof);
                for shot in 0..64 {let v=batch*64+shot;
                    for k in 0..W { let bit=if k>=W-8 { ((v&255)>>(W-1-k))&1 } else { ((k*73+v*37)^(k*v))&1 };
                        sim.qubits[x[k].0 as usize]|=(bit as u64)<<shot;
                    }
                    sim.qubits[a.0 as usize]|=((v>>8) as u64)<<shot;
                }
                sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0);
                for q in W+4..b.width() as usize {assert_eq!(sim.qubits[q],0);}
                let mut out:Vec<u64>=x.iter().map(|q|sim.qubits[q.0 as usize]).collect();
                out.extend(r.iter().map(|q|sim.qubits[q.0 as usize]));out
            };
            assert_eq!(run(true),run(false),"batch {batch}");
        }
        // Each of all eight shifts on arbitrary ring contents, then exact inverse.
        for sh in 0..8 {
            let mut b=B::new();let x=b.alloc_n(W);let r=b.alloc_n(3);
            rotate_three(&mut b,&x,&r,false,false);let split=b.ops.len();rotate_three(&mut b,&x,&r,true,false);
            let mut h=sha3::Shake256::default();h.update(b"reflection-all-shifts");let mut xof=h.finalize_xof();
            let mut sim=Simulator::new(b.width() as usize,1,&mut xof);
            let init:Vec<u64>=(0..W).map(|k|(k as u64+3).wrapping_mul(0x9e3779b97f4a7c15).rotate_left((k%64) as u32)).collect();
            for k in 0..W {sim.qubits[x[k].0 as usize]=init[k];}
            for k in 0..3 {sim.qubits[r[k].0 as usize]=if sh>>k&1==1 {!0}else{0};}
            sim.apply_iter(b.ops[..split].iter());
            for k in 0..W {assert_eq!(sim.qubits[x[k].0 as usize],init[(k+W-sh)%W],"shift {sh} lane {k}");}
            sim.apply_iter(b.ops[split..].iter());
            for k in 0..W {assert_eq!(sim.qubits[x[k].0 as usize],init[k]);}assert_eq!(sim.phase,0);
        }
        // B-ROT8 promise barrel: on every shift, 64 shots of random contents whose top sh lanes are zero, the
        // promise barrel equals the target rotation, and its inverse (on the forward output) restores the input.
        // Negative control: without the promise the dropped pair is visible for sh >= 4.
        for sh in 0..8usize {
            let mut b=B::new();let x=b.alloc_n(W);let r=b.alloc_n(3);
            rotate_three(&mut b,&x,&r,false,true);let split=b.ops.len();rotate_three(&mut b,&x,&r,true,true);
            let mut bf=B::new();let _=bf.alloc_n(W);let _=bf.alloc_n(3);
            let xf:Vec<QubitId>=(0..W).map(|k|x[k]).collect();rotate_three(&mut bf,&xf,&r,false,false);
            if ROT8_PROMISE_DELETE {assert_eq!(split+3,bf.ops.len(),"one cswap (cx,ccx,cx) dropped");}
            let mut h=sha3::Shake256::default();h.update(b"rot8-promise");let mut xof=h.finalize_xof();
            let mut sim=Simulator::new(b.width() as usize,64,&mut xof);
            let rnd=|k:usize,salt:u64|(k as u64*2+salt+1).wrapping_mul(0x9e3779b97f4a7c15).rotate_left(((k*7+sh)%64) as u32);
            let init:Vec<u64>=(0..W).map(|k| if k>=W-sh {0} else {rnd(k,sh as u64)}).collect();
            for k in 0..W {sim.qubits[x[k].0 as usize]=init[k];}
            for k in 0..3 {sim.qubits[r[k].0 as usize]=if sh>>k&1==1 {!0}else{0};}
            sim.apply_iter(b.ops[..split].iter());
            for k in 0..W {assert_eq!(sim.qubits[x[k].0 as usize],init[(k+W-sh)%W],"promise shift {sh} lane {k}");}
            sim.apply_iter(b.ops[split..].iter());
            for k in 0..W {assert_eq!(sim.qubits[x[k].0 as usize],init[k],"promise inverse {sh} lane {k}");}
            assert_eq!(sim.phase,0);
            if ROT8_PROMISE_DELETE && sh>=4 {
                let mut h=sha3::Shake256::default();h.update(b"rot8-promise-neg");let mut xof=h.finalize_xof();
                let mut sim=Simulator::new(b.width() as usize,64,&mut xof);
                for k in 0..W {sim.qubits[x[k].0 as usize]=rnd(k,99);}
                for k in 0..3 {sim.qubits[r[k].0 as usize]=if sh>>k&1==1 {!0}else{0};}
                sim.apply_iter(b.ops[..split].iter());
                assert!((0..W).any(|k|sim.qubits[x[k].0 as usize]!=rnd((k+W-sh)%W,99)),"negative control {sh}");
            }
        }
    }
}
