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
/// buy side of the width market (-0.83 Lambda for +11.1k T). Q825 LS-3: 255 -> 256 (-0.47 walk Lambda for +9.4k T),
/// the buyback paired with the NB 28 -> 27 sell (lambda-neutral swap, PR 419 term 3)
pub const NSLOTS: usize = 256;
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
// ------------------------------------------------------------------ Q825 B-MICRO2 (micro wave 2)
/// A-9 SWAP-PRUNE (G3-08, R-007.a, R-032a): the swap / un-swap cswaps are identities on two lanes. Lane W-1: sw has the
/// literal X[W-1] (= 1 where sw = 1) and Y = B is top-normalised (Y[W-1] = 1 on every shot), so cswap(sw, X[W-1],
/// Y[W-1]) is dropped in F10, I4 and the SW-CARRY un-swap. LA[8] / LB[8]: LA <= 255 at every F9 (a step from LA = 256
/// leaves A' < A/2, so rho >= 1; LA only grows by a swap from LB), and LB <= 255 on every slot: the shell reflects the
/// divisor input below 2^255 (refl = x[255], ctrl_neg; div_forward's x' < 2^255), and LB only takes F9 values of LA.
/// So both are 0 at every F10 / I4 and their cswap is dropped (not under OFF-KEEP, whose I4 runs on LA + sX, LB + sY).
/// (Without the reflection, LB = 256 would survive to the first swap, slot <= 36: SWAP_PRUNE_L8 = 37 is the
/// input-independent bound.) Exact on every shot.
/// Dev override `WL_SWAP_PRUNE=0|1`.
pub const SWAP_PRUNE: bool = true;
const SWAP_PRUNE_L8: usize = 0;
fn swap_prune() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("SWAP_PRUNE", SWAP_PRUNE)); *E }
/// B-2 Z0-DEFER (G3-10, z0 part): the forward's F11 measured erase of z0 = [LA == 0] & [cnt != 0] (post-state) no longer
/// recomputes both zero tests in its repair block: the inverse slot's I1 computes the same predicate on the same state
/// as a wire, and takes the repair there as one z_if (Clifford). Slots where the inverse has no z0 (act_const) keep the
/// forward repair. Dev override `WL_Z0_DEFER=0|1`.
pub const Z0_DEFER: bool = true;
fn z0_defer() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("Z0_DEFER", Z0_DEFER)); *E }
/// B-4 TERM-LAST (R-008a TERM-253, on the last slot NSLOTS - 1 = 254): every shot that passes is finished there, or
/// finishes on it with a step that has B = 1 (A' = 0 forces gcd = B), so d = 0, or a stall (a1 = 0, d = 0); and
/// sw = 0 (A' = 0 leaves X[W-1] = 0; finished shots never swap). A shot still mid-walk after the last slot fails anyway.
/// So the last slot drops F2/F3 (d stays |0>), F5's LA -= d, F9/F10 (swap flag, swap, parity), the inverse's I2 decode,
/// I3/I4 un-swap and I5 erase, and I12-I14 (LA += d, the d rotation, d's erase). Dev override `WL_TERM_LAST=0|1`.
pub const TERM_LAST: bool = true;
fn term_last() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("TERM_LAST", TERM_LAST)); *E }
/// Negative controls for the gate tests only (M2_BREAK=k): 1 SWAP-PRUNE also drops lane W-2 of the X/Y swap, 2 Z0-DEFER
/// drops the inverse's z_if, 3 TERM-LAST also runs on slot 200 (mid-walk shots), 4 SWAP-PRUNE also drops LA/LB lane 7
/// from slot SWAP_PRUNE_L8, 5 FUNNEL-THERMO skips the g -> s conversion's last CX (s0 wrong), 6 TOPLANE-SKIP also
/// drops lane W-2, 7 LEN-TRIM on every slot (LA = 256 at slot 0), 8 FUSE-S4 runs the region pairs under r2 alone,
/// 9 FUSE-S4's erase drops the h_1 terms, 10 NORM-ZFILL drops the forward shift's top cswap, 11 YTOP-COF frees
/// Y[W-1] without flipping it.
pub(crate) fn m2_break(k: u32) -> bool {
    cfg!(test) && std::env::var("M2_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
/// O-14 FUNNEL-THERMO (G3-06 / pass3/FUNNEL.md variant B, norm side only): where the cap leaves 30 lanes of room
/// (and no act literal), norm_bottom computes the slack's Gray bits g_i = s_i ^ s_(i+1) up front from the thermometer
/// t_j = [ring lanes 0..j zero] (j = 1..31, one AND chain, 30 T, uncomputed by measurement): g_i = XOR of t_j over the
/// odd multiples j of 2^i (bit i + 1 of s + 2^i), then runs the six reversals under g4, g3, g2, g1, g0 with no frame
/// cswaps, converts g -> s by CX and runs Rev(c_0) under s0: 110 cswaps + 30 T against variant A's 125 + 26. The lane
/// map and s are variant A's (the same reversals under the same controls), so denorm_bottom stays variant A's literal
/// reverse (its MBU erases are cheaper than recomputing the thermometer). Dev override `WL_FUNNEL_THERMO=0|1`.
pub const FUNNEL_THERMO: bool = true;
fn funnel_thermo() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("FUNNEL_THERMO", FUNNEL_THERMO)); *E }
/// W-2 / R-032a TOPLANE-SKIP: the plain (unmasked) top compares [Y top WC > X top WC] of F2 / I14 (gated by a1 =
/// act & X[W-1]) and of the swap flag's cmp (F9 / I5 / the SW-CARRY erase: sw has the literal X[W-1]) only matter where
/// X[W-1] = 1, and Y[W-1] = 1 on every shot (B top-normalised): the top lanes are equal there, so the compare runs on
/// lanes W-WC .. W-2. Every recomputation uses the same function. Dev override `WL_TOPLANE_SKIP=0|1`.
pub const TOPLANE_SKIP: bool = true;
fn toplane_skip() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("TOPLANE_SKIP", TOPLANE_SKIP)); *E }
/// The top end (exclusive) of the plain top compares' lanes.
fn top_cmp_hi() -> usize {
    if toplane_skip() { if m2_break(6) { W - 2 } else { W - 1 } } else { W }
}
/// L-9 LEN-TRIM (R-032b bit 8, G3-11 length group): from slot LEN_TRIM_FROM = 1 the plain LA / LB are <= 255 at every
/// slot boundary (SWAP-PRUNE's bound: LA = 256 only before slot 0's step, LB <= 255 by the shell's reflection; 38
/// without the reflection), so the plain-length arithmetic outside the done-marked passes runs on bits 0..8: F1 / I1 zero tests and
/// their erases, F5 LA -= d, F8 LA -= rho, I7 LA += rho, I12 LA += d, the swap flag's [LA == 0] and [LA < LB + cmp]
/// (F9, I5, the SW-CARRY erase) and the end-of-slot z0 erase. The offset registers of the decode (LA + sX, u', kt) keep
/// their 9 bits. Dev override `WL_LEN_TRIM=0|1`.
pub const LEN_TRIM: bool = true;
const LEN_TRIM_FROM: usize = 1;
fn len_trim() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("LEN_TRIM", LEN_TRIM)); *E }
/// The plain length registers' live bits at this slot.
fn len_n(w: &Win) -> usize {
    let n = if len_trim() && (w.slot >= LEN_TRIM_FROM || m2_break(7)) { LB_BITS - 1 } else { LB_BITS };
    n.min(r8_hb()).min(if r8_m8() { LB_BITS - 1 } else { LB_BITS })
}
// ------------------------------------------------------------------ R8-LANE799 R8_LHF
// R8-LANE799 R8_LHF (cap < 805, forward slots that are not act-constant): LA and LB stay <= M = max(LA-d window top + 1,
// LB window top) through the whole slot on every non-failing shot (LA <= (LA - d) + 1 at F1, LB <= its window at F2,
// both only decrease until the swap exchanges them; finished shots hold 0 / 1), so with hb = bit length of M their bits
// hb..7 are |0>. Bit 8 (the marker) stays. ACT_PARK (which would park act on one of those zero bits) is off where they
// are released, so the pass keeps act's own lane instead. The lanes hb..7 of both registers are released to the builder for the slot and re-bound at its end (a fresh |0> lane where
// the builder still holds the old id). Every plain length operation runs on bits [..hb) (len_n), the done marks skip
// the released bits (decoders read v[..h] + v[8] with h <= hb). Envelope-based (DEC_NARROW's / R6_LBV's window class).
thread_local! {
    /// R8_LHF: bits >= this (below 7) of LA and LB are released in the running forward slot (LB_BITS: none)
    static R8_HB: std::cell::Cell<usize> = const { std::cell::Cell::new(LB_BITS) };
}
fn r8_hb() -> usize { R8_HB.with(|c| c.get()) }
/// R8_LHF releases bits hb..R8_TOP (bit 8, the marker, stays)
const R8_TOP: usize = LB_BITS - 1;
thread_local! {
    /// R8_IUNSW: the inverse's un-swap / swerase stretch adds sX <= 31 (sY <= 31) to the plain lengths
    static R8_OFF: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
fn r8_lhf_hb(u: &GreedyFrog, w: &Win) -> Option<usize> {
    if !(below805(u.cap) && r3_flag("R8_LHF") && (!w.act_const || r3_flag("R8_LHFAC"))) { return None; }
    // two lanes of headroom above the window (already margined) before a bit counts as |0>
    let m = (w.lad.1 + 1).max(w.lb.1) + 2 + R8_OFF.with(|c| c.get());
    // bits 0..5 stay bound: the DCMP7 / R6_LBV views and R_BITS-wide offsets read LB[0..5); la_hb covers stalled
    // shots' LA (the renorm gate's own bound: lad.1 of the step slot less 7 per stall slot)
    let hb = ((usize::BITS - m.leading_zeros()) as usize).max(5).max(w.la_hb);
    // negative control for the gate tests only: R8_BREAK=lhf releases one bit too many (bit hb - 1 is not |0>)
    let hb = if r8_break("lhf") { hb - 1 } else { hb };
    (hb < R8_TOP).then_some(hb)
}
fn r8_break(tag: &str) -> bool {
    cfg!(test) && std::env::var("R8_BREAK").map_or(false, |v| v.trim() == tag)
}
// R8-LANE799 R8_M8 (cap < 805, forward slots >= 1): the sign / marker lanes LA[8] and LB[8] share one physical lane.
// Exact: from slot 1 on, LA <= 255 and LB <= 255 at every slot boundary on every shot (each step lowers LA by >= 1, and
// x' < 2^255), so both bit-8 lanes are |0> there. Inside a forward slot bit 8 is written only by the marks, and LB's
// marks (F2's mark_msb, F4's done / stall marks) and LA's (F5's done / stall marks) are undone before the other
// register's are applied; every other bit-8 reader (renorm gate, F9's [LB == 1], R4_IDLE / R4_CSUB's 9-bit constant
// adds, which are mod 512 and so carry a set bit 8 through unchanged) sees 0 or the register's own mark. LA[8] is
// released at the slot's start and LA re-binds a fresh |0> lane at its end. Bit 8 is never a host lane while shared,
// and swaps run on bits 0..8.
thread_local! {
    static R8_M8_ON: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
fn r8_m8() -> bool { R8_M8_ON.with(|c| c.get()) }
fn r8_m8_open(b: &mut B, u: &mut GreedyFrog, w: &Win) {
    if r8_m8() || !(below805(u.cap) && r3_flag("R8_M8") && w.slot >= 1) { return; }
    if R8_SKIPLB.with(|c| c.borrow().contains(&(LB_BITS - 1))) { return; } // LB[8] released here (R4_LBLATE)
    // with an offset (R8_IUNSW) both registers must stay below 256 on every shot inside the windows
    let off = R8_OFF.with(|c| c.get());
    if off > 0 && (w.lad.1 + 1).max(w.lb.1) + 2 + off > 255 { return; }
    let q = u.la[LB_BITS - 1];
    if q == NOQ && SLDEN8_PEND.with(|c| c.get()) { return; } // b792 SLDEN8: LA[8] deferred
    if cfg!(test) && r3_flag("R8_DBG8") { eprintln!("R8M8 open slot {} la8 q{} lb8 q{} op {}", w.slot, q.0, u.lb[LB_BITS - 1].0, b.ops.len()); }
    if q == NOQ && b792_late() {
        // B792_LATE: LA[8] was never re-bound after the LAOFF add (deferred), so there is nothing to free: bit 8 is shared from here
        zero_probe(b, &[u.lb[LB_BITS - 1]]);
        u.la[LB_BITS - 1] = u.lb[LB_BITS - 1];
        R8_M8_ON.with(|c| c.set(true));
        return;
    }
    zero_probe(b, &[q, u.lb[LB_BITS - 1]]);
    b.free(q);
    u.la[LB_BITS - 1] = u.lb[LB_BITS - 1];
    R8_M8_ON.with(|c| c.set(true));
}
thread_local! { static B792_F8: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
/// B792 probe: under the shared bit-8 holiday (|0> from slot 1) release the shared lane too (forward slots >= B792_F8_FROM)
fn b792_f8_out(b: &mut B, u: &mut GreedyFrog, w: &Win) {
    if std::env::var_os("B792_LALB").is_none() || !r8_m8() || w.slot < 44 || B792_F8.with(|c| c.get()) { return; }
    let q = u.lb[LB_BITS - 1];
    if q == NOQ || u.la[LB_BITS - 1] != q || b.is_free(q) { return; }
    zero_probe(b, &[q]);
    b.free(q);
    u.la[LB_BITS - 1] = NOQ; u.lb[LB_BITS - 1] = NOQ;
    B792_F8.with(|c| c.set(true));
}
fn r8_m8_close(b: &mut B, u: &mut GreedyFrog) {
    if !r8_m8() { return; }
    if B792_F8.with(|c| c.get()) {
        B792_F8.with(|c| c.set(false));
        R8_M8_ON.with(|c| c.set(false));
        u.lb[LB_BITS - 1] = b.alloc(); u.la[LB_BITS - 1] = b.alloc();
        return;
    }
    R8_M8_ON.with(|c| c.set(false));
    // losgahts B: the shared lane is already out; LA[8] stays unbound until KT-HOST (the cap is lowered for it)
    if LA94_B8.with(|c| c.get().0) == 2 {
        assert!(u.la[LB_BITS - 1] == NOQ && u.lb[LB_BITS - 1] == NOQ, "losgahts: bit-8 lanes bound under the holiday");
        u.cap -= 1;
        return;
    }
    // negative control for the gate tests only: R8_BREAK=m8 leaves LB's F4 stall mark on through F5 (see value_pass)
    zero_probe(b, &[u.lb[LB_BITS - 1]]);
    u.la[LB_BITS - 1] = b.alloc();
}
/// The lanes of a 9-bit length register still bound while R8_LHF has released bits hb..7.
fn r8_live(v: &[QubitId]) -> Vec<QubitId> {
    let hb = r8_hb();
    if hb < R8_TOP && v.len() == LB_BITS { v[..hb].iter().chain(&v[R8_TOP..]).copied().collect() } else { v.to_vec() }
}
thread_local! {
    /// R8_IDEN: LB indices another lever holds released at the open (R4_LBLATE); their ids may be stale
    static R8_SKIPLB: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) };
    /// R11_LA7 (fable, 797): LA indices whose re-bind is deferred past the R8_IDEN open (NOQ in the register)
    static R8_SKIPLA: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) };
    /// R8_LHF: the released lanes' ids (gate tests bind a poison id in their place, which no gate may touch)
    static R8_OLD: std::cell::RefCell<Vec<QubitId>> = const { std::cell::RefCell::new(Vec::new()) };
}
/// R8-LANE799: ids the gate tests bind in place of released register lanes (R8_FREECHK rejects any gate on them)
pub const R8_POISON: u64 = 900_000;
fn r8_lhf_open(b: &mut B, u: &mut GreedyFrog, w: &Win) {
    if r8_hb() < R8_TOP { return; } // already open (R8_IDEN opens at the denorm, R8_ITAIL at the un-renorm)
    let Some(hb) = r8_lhf_hb(u, w) else { return };
    let mut old = vec![];
    for (r, v) in [&mut u.la, &mut u.lb].into_iter().enumerate() {
        for k in hb..R8_TOP {
            // a lane another lever already holds released (R4_LBLATE through the denorm) stays so; it is bound with
            // the others at the close
            // R11_LA7: likewise an LA lane whose re-bind R11_LA7 deferred past this open (NOQ in the register)
            if !(r == 1 && R8_SKIPLB.with(|c| c.borrow().contains(&k))) && !(r == 0 && R8_SKIPLA.with(|c| c.borrow().contains(&k))) {
                zero_probe(b, &[v[k]]);
                b.free(v[k]);
            }
            old.push(v[k]);
            if cfg!(test) { v[k] = QubitId(R8_POISON + 16 * r as u64 + k as u64); }
            // negative control for the gate tests only: R8_BREAK=fc touches a released lane (R8_FREECHK must fire)
            if r8_break("fc") { b.x(v[k]); b.x(v[k]); }
        }
    }
    R8_OLD.with(|c| *c.borrow_mut() = old);
    R8_HB.with(|c| c.set(hb));
}
/// b793a EO (B793A_EO): the R8_IUNSW window (LA, LB bits hb..7 and the shared bit-8 lane released, plain lengths + 31 for sX / sY) opened already at the
/// inverse slot's prep on the late non-act-constant slots (the parent opens it at the un-swap, after the swap decode): u = LA + sX and v = LB + sY stay
/// below 2^hb on the window's shots (the same envelope the un-swap stretch rests on). add_sm / lt_cin_sm run on the bound views.
fn b793a_eo_max() -> usize { std::env::var("B793A_EOMAX").ok().and_then(|v| v.parse().ok()).unwrap_or(if r3_flag("B793_S255") { 255 } else { 254 }) }
fn b793a_eopen(b: &mut B, u: &mut GreedyFrog, w: &Win) {
    if !(r3_flag("B793A_EO") && r3_flag("R8_IUNSW") && !w.act_const && w.slot >= 189 && w.slot <= b793a_eo_max()) { return; }
    if r8_hb() < R8_TOP { return; }
    R8_OFF.with(|c| c.set(if b793a_brk("eooff") { 0 } else { (1 << R_BITS) - 1 }));
    r8_lhf_open(b, u, w);
    r8_m8_open(b, u, w);

    R8_OFF.with(|c| c.set(0));
    if std::env::var_os("B793_DBG").is_some() { eprintln!("B793AEO open slot {} hb {} live {}", w.slot, r8_hb(), b.live); }
}
fn r8_lhf_close(b: &mut B, u: &mut GreedyFrog) { r8_lhf_close_k(b, u, false) }
/// R9_LB: `skip_lb` leaves LB's released lanes unbound (NOQ)
fn r8_lhf_close_k(b: &mut B, u: &mut GreedyFrog, skip_lb: bool) { r8_lhf_close_kk(b, u, skip_lb, false) }
fn r8_lhf_close_kk(b: &mut B, u: &mut GreedyFrog, skip_lb: bool, skip_la: bool) {
    let hb = r8_hb();
    if hb >= R8_TOP { return; }
    R8_HB.with(|c| c.set(LB_BITS));
    let old = R8_OLD.with(|c| std::mem::take(&mut *c.borrow_mut()));
    let mut it = old.into_iter();
    for (r, v) in [&mut u.la, &mut u.lb].into_iter().enumerate() {
        for k in hb..R8_TOP {
            let q = it.next().unwrap();
            if r == 1 && skip_lb { v[k] = NOQ; continue; }
            if r == 0 && skip_la { v[k] = NOQ; B792_S255_HELD.with(|c| c.borrow_mut().push(k)); continue; }
            if b.is_free(q) { b.acquire(q); v[k] = q; } else { v[k] = b.alloc(); }
        }
    }
}
/// FUSE-S4 (E-FUSEDNORM A1, invent/FUSEDNORM.md): on the SW-CARRY denorm (X: the funnel's inverse alone, then I7 and
/// unrenorm_top) the denorm's last reversal Rev(58) under s4 and the barrel's first inverse reflection (ctrl r2) act on
/// the same pairs once the barrel is gauge-shifted by +54 (lane sums 58, 54, 52, 51 for stages 3..0 at NB = 28, c_5 = NB + 30 in general: 57/53/51/50 at NB = 27; a common shift
/// of all four axes leaves the even composite unchanged): stage 3 = Rev[0,58] (+) Rev[59,W-1], and its 29 region pairs
/// run once under r2 ^ s4 (-29 cswaps; the ROT8 promise pair is not in this gauge: +1). s4 stays live through the
/// barrel and is MBU-erased in the restored frame while r is live: s4 = [tz >= 16 - r] = t_15 ^ XOR_(k=1..7) h_k
/// (t_(15-k) ^ t_(16-k)), t_q = AND_(i<=q) !X[i], h_k = [r >= k]: Z / CZ phases on a 15-lane chain + 8 h lanes
/// (+9 T in the half-weighted block against the 14-T erase it replaces). Exact. Only where the erase fits the room
/// (decided before the denorm). Dev override `WL_FUSE_S4=0|1`.
pub const FUSE_S4: bool = true;
fn fuse_s4() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("FUSE_S4", FUSE_S4)); *E }
/// FUSE-S4's erase block takes 15 chain + 8 h lanes (s4 itself is free there): room needed at the erase
const FUSE_S4_NEED: usize = 22;
/// A-11 NORM-ZFILL (R-030a): norm_input's stage k fires only where Y's top 2^k lanes are zero (its own control), so
/// the rotation by 2^k is a controlled shift with zero fill (W - 2^k cswaps, the zeros bubble to the bottom) instead of
/// the W - 1 cswap cycle rotation; the undo is the mirror (zeros at the bottom). Same layout. Dev override
/// `WL_NORM_ZFILL=0|1`.
pub const NORM_ZFILL: bool = true;
pub(crate) fn norm_zfill() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("NORM_ZFILL", NORM_ZFILL)); *E }
/// W-2 YTOP-COF (YTOP-PERSIST residual, R-015a A0 on i.cof): Y[W-1] = B's MSB = 1 on every shot, and the inverse
/// cofactor undo's ladder reaches lane CW - 1 - lad.0 < W - 1 where lad.0 >= 1, so there Y[W-1] is X-flipped to |0>
/// and freed across I11 (one more lane for the ladder's pools; TARIFF4 prices i.cof at ~-490 per lane), then
/// re-bound and set back to 1. Dev override `WL_YTOP_COF=0|1`.
pub const YTOP_COF: bool = true;
fn ytop_cof() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("YTOP_COF", YTOP_COF)); *E }
/// TERM-LAST applies at this slot.
fn term(w: &Win) -> bool {
    term_last() && (w.last || (m2_break(3) && w.slot == 200))
}
/// The X/Y and LA/LB lanes the swap must exchange at this slot (`plain`: LA/LB hold plain lengths).
fn swap_lanes(w: &Win, plain: bool) -> (usize, usize) {
    if !swap_prune() {
        return (W, LB_BITS);
    }
    let xn = if m2_break(1) { W - 2 } else { W - 1 };
    let ln = if plain && w.slot >= SWAP_PRUNE_L8 { if m2_break(4) { LB_BITS - 2 } else { LB_BITS - 1 } } else { LB_BITS };
    (xn, ln.min(r8_hb()).min(if r8_m8() { LB_BITS - 1 } else { LB_BITS }))
}

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
/// Q825 LS-3 DCMP-REUSE (resurrect R-034, INVENT A-10 / X-4): on a forward slot whose successor runs the plain top
/// compare (next slot's lb.0 >= WC), F9's swap comparator cmp = [Y top WC > X top WC] is kept instead of erased. After
/// the swap, cmp ^= sw is the successor's F2 compare [Y' top > X' top], except on a full WC-lane top tie at a swap
/// (sw = 1 with cmp = 0 needs LA < LB): a sampled error, priced as a Lambda spend and paired with a buyback. The
/// successor's F2 is then d = a1 & cmp (1 Toffoli instead of the WC-lane compare) and cmp is erased by measurement
/// against the fresh post-swap compare (the conditional cost F9's erase paid before). Dev override `WL_DCMP_REUSE`.
pub const DCMP_REUSE: bool = true;
fn dcmp_reuse() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("DCMP_REUSE", DCMP_REUSE));
    *E
}
/// Negative control for the gate tests only (DCMP_BREAK=1): drop cmp ^= sw after the swap (d wrong on every swap).
fn dcmp_break(k: u32) -> bool {
    cfg!(test) && std::env::var("DCMP_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
/// Q825 B-SYMR25 SYM-R-25 (INV2-R3-DECODE 4.1) ROUND-THE-DIVISOR: division row j >= 1 reads D >> j (the divisor
/// window's low j bits dropped: truncation, biased by up to one ulp per row). Rounding to nearest is free: the row's
/// carry-in lane ^= the top dropped divisor bit b = X[NB - j] before the ladder and again after (2 CX, 0 T; a ROW-F row
/// also takes b back out of its top lane's sign-extension term, 1 CX), so the row subtracts / adds round(D / 2^j)
/// (carry-in m ^ b: r - D_j - b where m = 1, r + D_j + b where m = 0). Only window-plain rows round (w.mx >= NB - j + 1,
/// so X[NB - j] is a real cofactor bit; masked / parked-masked rows are exact and unchanged). Rounding buys ~1.4 lanes
/// of window at equal decode failure: NB 27 -> 25 (-96 T per slot-division). The emulator (`greedyfrog_diag`
/// emu_decode) follows the lever. Dev override `WL_ROUND_DIV=0|1`.
/// R3-VERG: off by default (v3 byte-identity); on with WL_ROUND_DIV=1.
pub const ROUND_DIV: bool = false;
pub(crate) fn round_div() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("ROUND_DIV", ROUND_DIV));
    *E
}
/// Negative controls for the gate tests only (ROUND_BREAK=k): 1 drops the ROW-F top-lane correction (the row's new
/// sign is wrong wherever b = 1), 2 drops the carry-in restore after the ladder (carry-in / sign lane left dirty).
fn round_break(k: u32) -> bool {
    cfg!(test) && std::env::var("ROUND_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
/// Q825 B-SYMR25 RUN-GUARD (INV2-R3-DECODE 3.5): the decode assumes floor(t_k / tB) = 0 at a run start; where t_k >= tB
/// the window quotient carries a spurious units bit (row j = kt fires) and r = sX - sY - kt = LB - LA < 0. A units-bit
/// jl is legitimate only where sX - sY >= kt, so the sweep gates its rows with kt' = kt - c, c = [sX < kt + sY] (row kt
/// skipped exactly where it cannot be the answer; every correct decode is unchanged). c is computed before the forward
/// sweep, kt5 -= c, and both are undone after the backward sweep (c erased by measurement). A Lambda buy, priced in
/// builds/symr25/SYMR25-LOG.md. Dev override `WL_RUN_GUARD=0|1`.
/// R3-VERG: off by default (v3 byte-identity); on with WL_RUN_GUARD=1.
pub const RUN_GUARD: bool = false;
pub(crate) fn run_guard() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("RUN_GUARD", RUN_GUARD));
    *E
}
/// Negative control for the gate tests only (GUARD_BREAK=1): the kt5 restore after the backward sweep is dropped.
fn guard_break(k: u32) -> bool {
    cfg!(test) && std::env::var("GUARD_BREAK").map_or(false, |v| v.trim() == k.to_string())
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
/// R9_LA (r9 worker la, dev knob `R9_LA=1`, off by default): on slots where the R13_LBR restore runs (LB[6..9) unbound
/// across the denormalisation) and R11_LA7 does not defer LA[7], LA[8] is |0> from the end of the undo rows (after the
/// plain rows: LA = u = LA + sX <= 256 - w.mx <= 228, the R3_LA8ROWS bound that already lends it to the rows pools;
/// finished shots u = sX <= 31) through LA -= sX (plain LA <= 255 after slot 0's step) to the denorm's end. On
/// masked-row slots u reaches 256 on short divisor cofactors (measured: freeing LA[8] there fails ~78 % of the fixed
/// inputs), so there LA -= sX runs first, at the free point, and LA[8] of the plain LA is freed. Nothing in between reads it: the R13_LBR restore runs on LB[0..6), sX and sY; LA -= sX runs on LA[0..8) (exact
/// mod 2^8: u - sX = LA, both in 0..255); the R8_IDEN open releases bits hb..7 only and R8_M8 cannot open (LB[8] is
/// R13_LBR-late); the denorm reads X, sX, sY. So LA[8] is freed before the LB re-bind that sets the rows_rev peak and
/// bound fresh |0> after the denorm frees sX and sY (before R13_LBR's LB += LA, its first reader). The cap is lowered by
/// one in between, so the walk's own room-driven choices (self.room) are unchanged; helpers that read the slot-start
/// P2 cap (P2_CAP) see the freed lane and may use it, never above the true cap. `R9_LA_NOMASK=1` keeps masked-row
/// slots out (dev).
/// Negative control `R9_LA_BREAK=1`: LA[7] (information where LA >= 128) is dropped instead.
fn r9_la() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("R9_LA").map_or(false, |v| v.trim() == "1")); *E }
/// R9_LB (r9 worker la, dev knob `R9_LB=1`, off by default; OFF-KEEP slots with KT-HOST in free mode): at the un-swap's
/// R8 close LB's R8_LHF-released lanes hb..7 are not re-bound. LB holds v = LB + sY < 2^hb there (the R8_IUNSW bound,
/// raised by 31, that released them), LA holds u = LA + sX, and the only LB work before KT-HOST frees LB[5..9) is
/// I6's kt = u - v = ~v + u + 1, in 0..31 on every shot (KT-HOST's own zero probe): it runs mod 2^hb on LB[0..hb) and
/// LA[0..hb), and the result's bits hb..8 are 0, which the unbound lanes (and LB[8], untouched) already hold. The cap
/// is lowered by the deferred count until KT-HOST's free, so the walk's own room-driven choices are unchanged (helpers
/// reading the slot-start P2_CAP may use the freed lanes, never above the true cap). Not where KT-HOST's sign clear
/// runs (no SY_ACT_GATE on a slot with finished shots).
/// Negative control `R9_LB_BREAK=1`: the kt add runs on hb - 1 lanes (its bit hb - 1 is then wrong).
fn r9_lb() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("R9_LB").map_or(false, |v| v.trim() == "1")); *E }
/// R9_LU (r9 worker la, dev knob `R9_LU=1`, off by default; OFF-KEEP un-swap where R8_M8 did not share LA[8]): the
/// funnel's 5 lanes are taken while LA holds LA + a_X, whose bit 8 is information on the first slots (u = LA + sX
/// reaches 256 on short divisor cofactors). LA -= a_X runs first instead (plain LA <= 255 after slot 0's step, so LA[8]
/// is |0> and freed), the funnel and the a_X erase run, and after ax is freed LA[8] is bound fresh and LA += sX (the
/// funnel's part plus a_X: a_X = 1 leaves funnel 0) gives the same u. The cap is lowered by one in between, so the
/// walk's own room-driven choices are unchanged (helpers reading the slot-start P2_CAP may use the freed lane). Negative control `R9_LU_BREAK=1`: LA -= a_X is skipped.
fn r9_lu() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("R9_LU").map_or(false, |v| v.trim() == "1")); *E }
/// b793b LAOFF (F9 on the masked slots, la_cut class; dev knob `B793_LAOFF=1`): after the undo rows the length register LA
/// stays in its offset form u' (u' = LA + sX - UOFF, 5 bits + the sign lane) instead of being re-bound to 9 lanes and
/// restored to u = u' + UOFF; the R9_LA masked path's LA -= sX runs on it directly, in a 7-bit two's-complement view
/// (lanes 0..5, one bound copy of the sign as bit 5, the sign lane as bit 6): LA' = u' - sX = LA - UOFF lies in
/// -63..24 on every non-failing shot (la_cut's own premise u' >= -32, hard sX <= 31, LA <= 255), so mod 2^7 is exact. On the la6 slots
/// (u' >= -64, LA[5] a real bound bit, nothing to re-bind) LA' >= -64 is the envelope LA >= 168 (APPROXIMATE: 0 of 400,000 walks reach it, lowest LA 185 at slot 39). LA is
/// plain again after the denormalisation frees sX: bit 7 = a copy of the sign, bit 6 = the sign lane, LA = LA' + UOFF
/// mod 2^8 (plain LA <= 255), and the R9_LA re-bind of LA[8] follows as before. Saves 2 lanes at the LA re-bind, 1 lane
/// from there to the denormalisation's end. Fires only where R9_LA's early path fires (asserted).
/// negative controls for the gate tests only: B793_BREAK=lao1 skips the sign copy into the re-bound LA bit 5, lao2 skips the sign
/// copy into bit 7 at the restore, lao3 restores with UOFF - 1
fn b793b_break(tag: &str) -> bool { cfg!(test) && std::env::var("B793_BREAK").map_or(false, |v| v.trim() == tag) }
/// b793b NONZ (F3 / F4; dev knob `B793_NONZ=1`): on act-constant slots no shot has LA == 0 (act = 1 classically is the same envelope
/// premise, a finished shot already fails there), so the swap flag's [LA != 0] literal is always 1: its lane nz, the zero test
/// and the measured erase are not emitted. Exact under that premise; negative control B793_BREAK=nz1 keeps the dropped
/// literal off a slot whose LA == 0 is possible (gate tests only: drops the literal on non-act-const slots).
/// B792_P4 (worker B792-W1): the done-counter inc/dec uses a borrowed-dirty ripple when the cap leaves < 6 clean lanes.
/// B792_LATE (worker B792-W1): late-band closures (slot 255 done flag; i.unrenorm 0-39 LA re-binds)
/// B792_LATE: out ^= [a < bb] (equal-length registers, restored) with no clean lane: XOR of the mutually exclusive terms !a_i & b_i & AND_{k>i}(a_k == b_k),
/// the equalities read after CX(b_k, a_k) (undone at the end), each term one and_dirty on borrowed dirty lanes. Exhaustively tested in the P9 tree (n <= 5).
fn lt_into_dirty(b: &mut B, a: &[QubitId], bb: &[QubitId], out: QubitId, dirty: &[QubitId]) {
    let n = a.len();
    for i in (0..n).rev() {
        let mut lits: Vec<(QubitId, bool)> = vec![(a[i], true), (bb[i], false)];
        for k in i + 1..n { lits.push((a[k], true)); }
        let ds: Vec<QubitId> = dirty.iter().copied().filter(|q| !a.contains(q) && !bb.contains(q) && *q != out).collect();
        and_dirty(b, &lits, out, &ds);
        if i > 0 { b.cx(bb[i], a[i]); }
    }
    for i in 1..n { b.cx(bb[i], a[i]); }
}
fn b792_late() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| super::B792_LATE || r3_flag("B792_LATE")); *E }
fn b792_p4() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| super::B792_P4 || r3_flag("B792_P4")); *E }
/// B792_P1 (worker B792-W1): the masked ladders' h - 6 level (see `p2_lanes_s`, mask::R792L3)
fn b792_p1() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| super::B792_P1 || matches!(std::env::var("B792_P1").as_deref().map(|v| v.trim()), Ok("1") | Ok("2"))); *E }
/// B792_P1=2 (gate tests at a cap with room): take the h - 6 level at every site that takes the h - 5 level
fn b792_force() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_P1").map_or(false, |v| v.trim() == "2")); *E }
fn b793_nonz() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_NONZ")); *E }
fn b793_nonz_skip(w: &Win) -> bool { b793_nonz() && (w.act_const || b793b_break("nz1")) }
thread_local! {
    /// b793b UNHOST: the lane hosting the next un-renormalisation counter's temporary t (|0> between its steps), taken by i5_rho_counter_x
    static B793_THOST: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) };
}
/// b793b UNHOST (F5; dev knob `B793_UNHOST=1`): the inverse slot's un-renormalisation counter (RCNT) runs its temporary t on LA[8],
/// which is a bound |0> lane there (plain LA <= 255 from slot 1 on, and the counter's LA gate reads bits 3..la_hb with la_hb <= 8
/// on these slots), instead of a fresh lane. Exact.
/// b793b S255 (B793_S255=1): inverse slot 255 (OFF-KEEP does not run there, the sX / sY adds run after the un-swap) takes the R9_LB form too:
/// the early window (B793A_EO with B793A_EOMAX=255) closes with LB[hb..8) unbound and the adds / kt run mod 2^hb (LA + sX, LB + sY < 2^hb)
/// B792_S255: slot 255 keeps LA[hb..8) unbound (NO_QUBIT) after the early window closes: LA < 64 there (u <= 39), so bits 6..8 are |0>
thread_local! { static B792_S255_HELD: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) }; }
/// B792_PL (slots 233-254, exact replacement of ACTRE): LA[hb..8) (|0> by the R8_IUNSW window, the parent's own premise) stay NO_QUBIT after the early window closes; only
/// LA[hb..7) re-bind (into the rows pool); LA[7] re-binds at the end of the undo rows, so the rows pool is one lane shorter and the rt / lend / rowsdone instants are one lane lower.
fn b792_pl(w: &Win) -> bool { w.slot >= 233 && w.slot <= 254 && (super::B792_PL || r3_flag("B792_PL")) }
fn b792_pl_slot() -> bool { (super::B792_PL || r3_flag("B792_PL")) && (233..=254).contains(&(p3_cur_slot() as usize)) }
fn b792_s255(w: &Win) -> bool { b792_pl(w) || (w.slot == 255 && (super::B792_S255 || r3_flag("B792_S255")) && b793_s255(w)) }
fn b793_s255(w: &Win) -> bool { w.slot == 255 && r3_flag("B793_S255") }
thread_local! { static AF_SAVE: std::cell::RefCell<Option<Vec<QubitId>>> = const { std::cell::RefCell::new(None) }; }
thread_local! { static AF_PAIR: std::cell::Cell<Option<(QubitId, QubitId)>> = const { std::cell::Cell::new(None) }; }
fn af_slot(sl: usize) -> bool { let (a, c) = std::env::var("B793_ACTFOLD_SLOTS").ok().as_deref().and_then(|v| v.split_once('-').map(|(a, c)| (a.parse().unwrap_or(189), c.parse().unwrap_or(202)))).unwrap_or((189usize, 202usize)); (a..=c).contains(&sl) && (189..=202).contains(&sl) }
fn b793_fpark() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_FPARK")); *E }
fn b793_actfold() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| matches!(std::env::var("B793_ACTFOLD").as_deref().map(|v| v.trim()), Ok("1") | Ok("2"))); *E }
/// B793_ACTFOLD=2: !act rides on the all-ones code of LA[0..7) (finished shots: LA = sX is redundant with the sX lanes), exact for every active u != 127
fn b793_actfold2() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B793_ACTFOLD").map_or(false, |v| v.trim() == "2")); *E }
thread_local! { static AF_LANES: std::cell::RefCell<Vec<QubitId>> = const { std::cell::RefCell::new(Vec::new()) }; }
fn b793_unhost0() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_UNHOST0")); *E }
fn b793_unhost() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_UNHOST")); *E }
/// b793b SWLAH (F11; dev knob `B793_SWLAH=1`): the swap decode's masked window compare (window_gt_hh) reads LA = u' through its 6-bit view
/// (bits 0..4 and the sign lane) only. On the act-constant masked slots 0-39 (min(LA, LB) >= 168 on every non-failing shot, so u' >= -64)
/// LA[6] and LA[7] are copies of the sign: CX-cleared, freed for the compare and taken back by id, copies restored. Exact within the windows.
fn b793_swlah() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_SWLAH")); *E }
thread_local! {
    /// b793b LAHOLD: LA[8] stays out past R9_LU's funnel until the bit-8 holiday's end (set at the funnel, taken at the holiday end)
    static B793_LAHOLD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
/// b793b LAHOLD (F14 rest, "Buerli" of the h793 design; dev knob `B793_LAHOLD=1`): on act-constant slots 0-43 where R9_LU takes LA[8] out for the
/// un-swap funnel and losgahts B holds LB[8] out until KT-HOST, LA[8] is not re-bound after the funnel: LA += sX runs mod 2^8 (plain LA <= 255 there)
/// and kt = u - v already runs mod 2^8 in the holiday. At the holiday's end LA[8] is bound fresh with bit 8 of u = LA + sX, which is
/// [u mod 256 < sX] (LA <= 255, sX <= 31): LA[5..8) all zero and [LA[0..5) < sX], one 5-lane compare computed and uncomputed. Exact.
fn b793_lahold() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_LAHOLD")); *E }
fn b793_lahold_slot(w: &Win) -> bool { b793_lahold() && w.act_const && p3_cur_slot() <= 43 && LA94_B8.with(|c| c.get().0) == 1 }
/// b793b ZOPF (F7, the h793 design "Zopf-frueh"; dev knob `B793_ZOPF=1`): on the act-constant plain R15-JC slots where Schaffhuuserzopf part 1 fires,
/// its window (LA offset by c, LA[7] out) starts before the sweep's jl lanes are bound instead of after the forward sweep: the jl allocation of the
/// attach is deferred to just after the R3 hosts are lent (nothing reads jl in between on these unmasked slots), part 1's conditions are evaluated there
/// and its offset + free run first. LA is read by nothing from there to the old start (only MJ_PEND's gated branch, off on act-constant slots and
/// required off by part 1). Same field adds, earlier. Exact (part 1's own premise).
fn b793_zopf() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_ZOPF")); *E }
thread_local! {
    /// b793b ZLATE: part 1's (j, k) whose LA[7] re-bind + add-back wait for the end of the undo rows
    static B793_ZLATE: std::cell::Cell<Option<(usize, usize)>> = const { std::cell::Cell::new(None) };
}
/// b793b ZLATE (F10 class A; dev knob `B793_ZLATE=1`, needs B793_ZOPF): on the slots where Schaffhuuserzopf part 1 fires, LA[7] stays out (LA in its offset form,
/// u - c in 0..127) through the sweep's decode AND the undo rows: its re-bind and the add-back of c run right after the undo rows, before any reader of LA
/// (the plain undo rows read none; the LBR restore and LA -= sX come after). The cap is not lowered for the lane, so the undo rows' pool takes it as room and the
/// M1_ROWF=close lending of R10_X0's stand-in lanes (rows_rev site 9254) is not needed. Exact (part 1's premise, same field adds).
/// B792_SLDEN (worker B792-SL): ZLATE's LA[7] re-bind and add-back of c wait for the end of the denormalisation (after the funnel
/// and the sX / sY frees), so LA stays in its 7-lane offset form u - c through the denorm funnel; LA -= sX runs mod 2^7 on lanes 0..7
/// (u - c - sX = LA_plain - c lies in 0..127 under ZLATE's own premise). Default off.
fn b792_den2() -> bool { static V: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_DEN2").map_or(super::B792_DEN2, |v| v.trim() == "1")); *V }
fn b792_gipm() -> bool { static V: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_GIPM").map_or(super::B792_GIPM, |v| v.trim() == "1")); *V }
fn b792_slden() -> bool { static V: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_SLDEN").map_or(super::B792_SLDEN, |v| v.trim() == "1")); *V }
/// B792_SLDEN8 (worker B792-SL, needs B792_SLDEN): LA[8] (|0>, plain LA <= 255) left unbound after the undo rows on plain slots, bound after sX is free
fn b792_slden8() -> bool { static V: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_SLDEN8").map_or(super::B792_SLDEN8, |v| v.trim() == "1")); *V }
thread_local! { static SLDEN8_PEND: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
thread_local! { static SLDEN_PEND: std::cell::Cell<Option<(usize, usize)>> = const { std::cell::Cell::new(None) }; }
fn b793_zlate() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_ZLATE")); *E }
fn b793_laoff() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_LAOFF")); *E }
/// LAOFF slot gate: dev list B793_LAOFF_SLOTS=a-c restricts the slots
fn b793_laoff_slot_ok(_w: &Win) -> bool {
    std::env::var("B793_LAOFF_SLOTS").ok().and_then(|v| { let (a, c) = v.split_once('-')?; Some((a.parse::<usize>().ok()?, c.parse::<usize>().ok()?)) })
        .map_or(true, |(a, c)| (a..=c).contains(&p3_cur_slot()))
}
fn r9_la_break() -> bool { std::env::var("R9_LA_BREAK").map_or(false, |v| v.trim() == "1") }
/// Schaffhuuserzopf (R14 la94-b, knob `R14_LA94B=1`, off by default): LA's bit 7 leaves for the R4-RHO sweep's jl map and
/// decode (from the R15-JC carry-in lane g to the release of the measured res lanes) on act-constant plain slots where it
/// is information. LA holds u = LA + sX = CW - bl(tB) there, inside lo..=hi (below); u is offset in place by c = k 2^j,
/// the multiple of the largest power of two inside hi - 127 ..= lo, which is a constant subtraction of k on the field
/// LA[j..8) alone (u >> j >= k, and (u - c) >> 7 = 0; LA[8] is the parent's lent |0> lane), so bit 7 is |0>; j is 7, 6, 5
/// or 4 on slots 40-142 (Clifford, a CCX, or a borrowed-lane 3-control AND per 2^i term). lo = lad_floor - 7 and
/// hi = lad.1 + 31:
/// - u >= c: a step shot has LA - d inside the slot's lad window (the parent's cofactor-pass envelope, R4_CVIEW's; a shot
///   outside it already fails in the parent), the renorm takes rho <= 7, and sX >= 0, so u = (LA - d) - rho + sX >=
///   lad.0 - 7; a stall shot keeps u since its last step (each stall slot lowers LA by rho and raises sX by rho: u depends
///   on X's cofactor only), and lad_floor (the running minimum of lad.0, CW - dtop_u) is <= that step's lad.0;
/// - u <= hi = min(la94b_hi(s), 255), la94b_hi(s) = max over k of lad.1(s - k) - 7k, plus 31: u = LA + sX with sX <= 31
///   (a 5-lane register), and LA <= lad.1 on a step shot inside the parent's LA - d window, LA <= lad.1(s - k) - 7k on a
///   shot stalling since a step at s - k (the parent's own la_hb rule for stalled shots); on this table the maximum is
///   always k = 0 (lad.1 falls by less than 7 per slot), i.e. R3_LATOP's lad.1 + 31. The 255 cap: LA[8] is the parent's
///   lent |0> lane here (R3_LATOP / R3_LA8).
///   (Not 257 - mx: the mx window is only the parent's NB + 1 threshold there; Fable 5.2 built an in-window walk with
///   u = 193 > 257 - mx at slot 82.)
/// The jl map, the act repair, the decode and the res measurement read none of LA's lanes (r4_pend_apply reads LA only
/// with its gate, off on act-constant slots); LA[7] is bound fresh |0> after the res lanes are freed and c is added back.
/// The cap is lowered by one in between. Negative controls (gate tests only): `R14_LA94B_BREAK=c1` offsets by c + 2^j
/// (above the floor: u - c wraps on the low shots), `=c0` by c - 2^j (u - c reaches 128 on the high shots), `=nosub`
/// frees LA[7] without the offset.
/// Schaffhuuserzopf part 1: the upper bound of u at slot s, stall shots included: max over k of lad.1(s - k) - 7k (the
/// parent's la_hb rule: a shot stalling since a step at s - k has LA <= lad.1(s - k) - 7k at slot s's renorm) plus 31 (sX)
fn la94b_hi(s: usize) -> usize {
    static H: std::sync::LazyLock<Vec<usize>> = std::sync::LazyLock::new(|| {
        let ws = windows();
        (0..ws.len()).map(|s| (0..=s).map(|k| (ws[s - k].lad.1 as isize - 7 * k as isize).max(0) as usize).max().unwrap() + 31).collect()
    });
    H[s.min(H.len() - 1)]
}
/// B792_SLCMIN (worker B792-SL, needs B792_SLDEN): ZOPF's offset c at the smallest value its own constraint (u - c <= 127) allows,
/// c = ceil((hi - 127) / 16) 16 (field LA[4..8)), instead of the largest multiple below lo: SLDEN's LA -= sX on the offset form is exact only
/// where LA_plain = u - sX >= c, and a stall shot can fall below the window floor (REPORT-SLDEN-ATTACK.md); a lower c lowers that rate.
fn b792_slcmin() -> bool { static V: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_SLCMIN").map_or(super::B792_SLCMIN, |v| v.trim() == "1")); *V }
fn b792_slc_jk(lo: usize, hi: usize) -> Option<(usize, usize)> {
    if !(b792_slcmin() && b792_slden()) { return None; }
    let c = (hi.saturating_sub(127) + 15) / 16 * 16;
    (c <= lo && c + 127 >= hi).then_some((4usize, c))
}
/// B792 SLDEN invariant (build-time): LA_plain >= c on every shot that passes the parent's step windows. After a step at s, LA_plain >= lad.0(s) - 7;
/// after a stall at s with remaining lag L the next step is at t = s + 1 + ceil(L/7) and LA at s = LA_pre(t) + L >= min(lad.0(t), lb.0(t)) + L
/// (lb.0 for the swapped case). A table (GF_WIN, R3_ROWS, a re-margin) that breaks this would silently wrap SLDEN's mod-2^7 subtraction.
fn b792_slc_assert(s: usize, c: usize) {
    let ws = windows();
    let f = |t: usize| ws.get(t).map_or(0, |w| w.lad.0.min(w.lb.0));
    let mut b = ws[s].lad.0.saturating_sub(7);
    for l in 0..300usize { b = b.min(f(s + 1 + (l + 6) / 7) + l); }
    let c = c + std::env::var("B792_SLC_ASSERT_PLUS").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(0); // negative control for the assert itself
    assert!(b >= c, "b792 SLDEN invariant: slot {s}: LA_plain bound {b} < c {c} (window table changed?)");
}
fn la94b_field_add(b: &mut B, f: &[QubitId], k: usize, sub: bool, dirty: &[QubitId]) {
    // f += k (sub: f -= k) mod 2^n, n = f.len() <= 4: one increment of f[i..] per set bit i of k (or of 2^n - k)
    let n = f.len();
    assert!(n >= 1 && n <= 4);
    let m = 1usize << n;
    let a = if sub { (m - k % m) % m } else { k % m };
    for i in 0..n {
        if (a >> i) & 1 == 0 { continue; }
        let g = &f[i..];
        match g.len() {
            1 => b.x(g[0]),
            2 => { b.cx(g[0], g[1]); b.x(g[0]); }
            3 => { b.ccx(g[0], g[1], g[2]); b.cx(g[0], g[1]); b.x(g[0]); }
            _ => {
                // g[3] ^= g0 g1 g2 on borrowed lanes (restored), then the 3-lane increment
                let dl: Vec<QubitId> = dirty.iter().copied().filter(|q| !g.contains(q)).collect();
                and_dirty(b, &[(g[0], false), (g[1], false), (g[2], false)], g[3], &dl);
                b.ccx(g[0], g[1], g[2]); b.cx(g[0], g[1]); b.x(g[0]);
            }
        }
    }
}
fn r14_la94b() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("R14_LA94B").map_or(false, |v| v.trim() == "1")); *E }
/// Schaffhuuserzopf parts: '1' the LA[7] offset (act-constant slots), '2' the act-lane decode (dev `R14_LA94B_PARTS`)
fn r14b_part(c: char) -> bool { static P: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R14_LA94B_PARTS").unwrap_or_else(|_| "12".into())); r14_la94b() && P.contains(c) }
/// Schaffhuuserzopf part 2 (R14_LA94B, slots with finished shots, R11_FOLD's act lane, R15-JC, R9 rowtmp c; only where the
/// parent's jl-map carry-in g would cross the cap, i.e. room 0 at the map; dev `R14_LA94B_P2ALL=1` everywhere eligible):
/// - the jl map's carry-in is sY's own lane (negated; SYFOLD's form) instead of g, which holds just !sY;
/// - r4_pend_apply's gated stall phase (-1)^(g q) with g = AND(lits) is applied as phase_and(lits + q) (borrowed lanes at
///   room 0), so no gate lane is taken;
/// - the decode runs on act's own lane, X-flipped to !act, as its sixth wire instead of a fresh e: on active shots it
///   starts |0> and ends as e = a1 (= e ^ !act with !act = 0); finished shots decode t = 0 (the parent's own premise: J = 0,
///   sY = 0, then t ^= !act & sX) from (t, 1), which the tree's permutation sends to (rho 3, res 3, 1), a state no input
///   with e_in = 0 reaches; one transposition (la94b_fin) swaps it with (0, 0, 0) = (rho 0, res 0, a1 0), the parent's
///   finished-shot result. The lane then holds a1, act is (a1 | rho != 0) as R9 rowtmp c records, and the rest (cap,
///   act_el) is R9 rowtmp c's. Exact: checked over all 64 six-wire states (identical on e_in = 0, (0, 1) -> (0, 0, 0)).
/// Needs R12_DECODE_PERM (the transposition is for that permutation). Negative controls (gate tests only):
/// `R14_LA94B_BREAK=p2t` skips the transposition, `=p2p` the stall phase (unobservable: see the report), `=p2l` drops
/// its LA literals.
fn la94b_fin(b: &mut B, j: &[QubitId], e: QubitId, dirty: &[QubitId]) {
    // swap the six-wire basis states (j0..4, e) = (1, 1, 0, 1, 1, 1) and (0, 0, 0, 0, 0, 0)
    let d = [j[0], j[1], j[3], j[4]];
    for &q in &d { b.cx(e, q); }
    let dl: Vec<QubitId> = dirty.iter().copied().filter(|q| !j.contains(q) && *q != e).collect();
    let lits = [(j[2], true), (j[0], true), (j[1], true), (j[3], true), (j[4], true)];
    and_dirty(b, &lits, e, &dl);
    for &q in &d { b.cx(e, q); }
}
fn r14b_break(tag: &str) -> bool { cfg!(test) && std::env::var("R14_LA94B_BREAK").map_or(false, |v| v.trim() == tag) }
/// losgahts (R14 la94, knob `R14_LA94=1`, off by default; the second LA/LB lane at cap 794). Two parts:
/// B "bit-8 holiday" (OFF-KEEP inverse slots, from the un-swap's swerase to KT-HOST): the length registers' bit-8 lanes
///   leave while no gate needs them. Where R8_M8 shares LA[8] = LB[8] (its +31 bound: u = LA + sX and v = LB + sY are
///   <= 255 there) the shared lane is |0> and is freed; the funnel's LA += f runs on the bound view (mod 2^8, or 2^hb
///   with R8_LHF open), R8_M8's close binds no LA[8], I6's kt = ~v + u + 1 runs on LA[0..8), LB[0..8) (exact mod 2^8:
///   kt in 0..31, KT-HOST's own probe, and LB[8] = 0 is what the unbound lane holds), and LA[8] is bound fresh |0>
///   after KT-HOST frees LB[5..9) (u <= 255). Where R8_M8 did not open (the first slots, act-constant: LA's bit 8 is
///   information there) LB[8] alone leaves: after the un-swap v = LB + sY = CW - bl(tA') (Y's slack is its distance to
///   the cofactor frame top, greedyfrog_model.rs `syp`), and tA' = tA + 2^ep tB >= 2 on an active shot, so v <= 255
///   and LB[8] is |0> (Fable review: max v = 255 at every slot on 22k simulated inputs incl. adversarial ones); kt as
///   above (mod 2^8 is exact for u >= 256 too). Mode 2 rests on R8_M8's own +31 window bound (the parent's premise for
///   sharing the lane). The cap is lowered by the lanes out.
/// A "sY out early" (lbr / SYFOLD slots, after the undo rows): Y's denormalisation (its a-shift back under sY, and sY's
///   erase as [Y slack == 1]) commutes with everything between the undo rows and the denorm (they touch LA, LB, sX,
///   X[0] and Y[W-1] only), so it runs right after the RowTmp is released and sY's lane is freed there. The LB
///   restore is formed without sY (R13_LBR: LB[0..6) = sX - kt; SYFOLD: LB[..n] = u - kt) and sY is subtracted after
///   the denorm frees sX, from a fresh lane holding the same predicate r9_sy_erase erased (Y is untouched in between),
///   which is then erased again the same way. No envelope. The cap is lowered by one until the parent's sY free.
/// Negative controls (gate tests only): `R14_LA94_BREAK=ktv` runs B's kt on 7 lanes (bit 7 wrong), `=lav` the funnel's
/// LA += f on 7 lanes, `=lb8` frees B's mode-1 LB[8] before the un-swap's cswap (where it can hold LA's bit 8 = 1),
/// `=psub` skips A's late sY subtraction (LB off by sY), `=pred` drops the predicate's a1 / rho term.
fn r14_la94() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("R14_LA94").map_or(false, |v| v.trim() == "1")); *E }
fn r14_parts(c: char) -> bool { static P: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R14_LA94_PARTS").unwrap_or_else(|_| "AB".into())); r14_la94() && P.contains(c) }
fn r14_break(tag: &str) -> bool { cfg!(test) && std::env::var("R14_LA94_BREAK").map_or(false, |v| v.trim() == tag) }
/// losgahts B: the bound view of a length register (R8_LHF's released lanes and NOQ dropped)
fn la94_view(v: &[QubitId]) -> Vec<QubitId> { r8_live(v).into_iter().filter(|&q| q != NOQ).collect() }
thread_local! {
    /// losgahts B: 0 no holiday, 1 LB[8] out (no R8_M8), 2 the shared LA[8] = LB[8] lane out; the freed id
    static LA94_B8: std::cell::Cell<(u8, QubitId)> = const { std::cell::Cell::new((0, QubitId(u64::MAX))) };
}
fn q792_x0na() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("Q792_X0NA").map_or(false, |v| v.trim() == "1")); *E }
/// FIXX0 (fotl765 R9 worker FIXX0): Q792_X0NA's release of X[0] on non-act-constant slots made exact. X0NA assumed
/// X[0] = 1 after the ungated 5-stage funnel on every shot; a shot whose divisor slack is >= 32 keeps X[0] = 0 there
/// with all five slack flags set (measured: fixed input ab45/4720, division 2, inverse slot 192, a stall with slack 32;
/// X0NA freed that lane holding 1 after its flip and the shot failed classically). The bit is parked instead of lost:
/// FUNNEL-REV's lane map leaves X lanes NB+15..NB+30 holding the ring's lanes 0..15 whenever sX[4] = 1 (the s4 test
/// found them all |0>; checked for every slack and for the thermometer variants), and every slack >= 32 shot has
/// sX[4] = 1. With g = 1 ^ X[0] (1 only where slack >= 32) and Z = X[NB + 30]:
/// - release: X[0] ^= 1 (g), Z ^= X[0] (CX; Z was 0 wherever g can be 1), X[0] ^= Z & sX[4] (CCX: g where sX[4] = 1,
///   0 elsewhere since g = 0 and Z = 0 there or sX[4] = 0) leaves X[0] |0> on every shot;
/// - re-bind: X[0] ^= Z & sX[4] (= g), Z ^= X[0] (Z restored), X[0] ^= 1 (the original X[0]);
/// - where R10_X0 binds X[0] only after the undo rows, their stand-in lane is set to 1 ^ (Z & sX[4]), the true X[0].
/// Exact (no envelope; no lane, no measurement, no room-driven branch moves): one CX and one CCX per release and
/// per re-bind (plus two CCX on R10_X0 slots). Non-act-constant slots only; act-constant slots keep X0-HOST as the
/// parent rows have it. Fail-closed builder checks (`fx0_scan`): between the funnel and the re-bind no other op names
/// Z (the R10_X0 stand-in's CCX excepted) or writes sX[4]; only the plain and R10_X0 re-bind paths may fire.
/// Negative controls (gate tests only): FIXX0_BREAK=1 drops the CX parking g (X0NA's original release); FIXX0_BREAK=2
/// keys the park on sX[3] instead of sX[4] (Z then holds cofactor data on slack 8..15 shots).
fn fixx0_break() -> bool { cfg!(test) && std::env::var("FIXX0_BREAK").map_or(false, |v| v.trim() == "1") }
fn fixx0_break2() -> bool { cfg!(test) && std::env::var("FIXX0_BREAK").map_or(false, |v| v.trim() == "2") }
/// FIXX0 parking lane of X[0]'s bit (see `fixx0_break`'s doc): X lane NB + 30, |0> wherever sX[4] = 1
const FX0_Z: usize = NB + 30;
/// FIXX0 fail-closed scan of ops[lo..]: no op names the parking lane `z` except CCX(z, s4 -> *) (the R10_X0 stand-in), so
/// Z keeps the parked bit and nothing else reads it; no op measures, resets or swaps `s4`. (sX[4] is otherwise only
/// read, or written by the in-place adders and comparators that take sX as an addend and restore it; sX reaches the
/// denormalisation intact on every shot, which the parent's exactness already rests on.)
fn fx0_scan(b: &B, lo: usize, z: QubitId, s4: QubitId, what: &str) {
    use crate::circuit::OperationType as K;
    assert!(!b.recording(), "FIXX0: {what} inside a recording");
    for (i, o) in b.ops.iter().enumerate().skip(lo) {
        let names = |q: QubitId| o.q_target == q || o.q_control1 == q || o.q_control2 == q;
        let stand_in = o.kind == K::CCX && ((o.q_control1 == z && o.q_control2 == s4) || (o.q_control1 == s4 && o.q_control2 == z));
        let names_z = match o.kind {
            K::X | K::Z | K::CX | K::CZ | K::Swap | K::R | K::Hmr | K::CCX | K::CCZ => names(z),
            _ => false,
        };
        assert!(!names_z || stand_in, "FIXX0: op {i} ({:?}) names the parking lane q{} ({what}, slot {})", o.kind, z.0, p3_cur_slot());
        let kills_s4 = match o.kind {
            K::R | K::Hmr => o.q_target == s4,
            K::Swap => o.q_target == s4 || o.q_control1 == s4,
            _ => false,
        };
        assert!(!kills_s4, "FIXX0: op {i} ({:?}) measures, resets or swaps sX[4] q{} ({what}, slot {})", o.kind, s4.0, p3_cur_slot());
    }
}
/// FIXX0 release (X[0] holds g = 1 ^ X[0] after X0-HOST's flip): Z ^= g, X[0] ^= Z & sX[4] (= g): X[0] |0> on every shot.
/// Returns the op index after the park (start of the release..re-bind scan).
fn fx0_park(b: &mut B, x0: QubitId, z: QubitId, s4: QubitId) -> usize {
    let fun = FX0_FUN.with(|c| c.replace(usize::MAX));
    assert!(fun != usize::MAX && fun <= b.ops.len(), "FIXX0: no X funnel recorded before the release (slot {})", p3_cur_slot());
    fx0_scan(b, fun, z, s4, "funnel..release");
    assert!(!FX0_OPEN.with(|c| c.replace(true)), "FIXX0: a park opened twice (slot {})", p3_cur_slot());
    if !fixx0_break() { b.cx(x0, z); }
    b.ccx(z, s4, x0);
    if std::env::var_os("FIXX0_DBG").is_some() { eprintln!("FIXX0 park slot {} x0 q{} z q{} s4 q{}", p3_cur_slot(), x0.0, z.0, s4.0); }
    b.ops.len()
}
/// FIXX0 re-bind on a fresh |0> X[0]: X[0] ^= Z & sX[4] (= g), Z ^= X[0] (restored); the caller flips X[0] to 1 ^ g.
fn fx0_unpark(b: &mut B, x0: QubitId, z: QubitId, s4: QubitId, rel: usize, path: &str) {
    assert!(rel != usize::MAX && rel <= b.ops.len(), "FIXX0: re-bind without a release (slot {})", p3_cur_slot());
    fx0_scan(b, rel, z, s4, "release..re-bind");
    assert!(FX0_OPEN.with(|c| c.replace(false)), "FIXX0: re-bind of a park that is not open (slot {})", p3_cur_slot());
    b.ccx(z, s4, x0);
    b.cx(x0, z);
    if std::env::var_os("FIXX0_DBG").is_some() { eprintln!("FIXX0 unpark slot {} path {path} ops {}", p3_cur_slot(), b.ops.len() - rel); }
}
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
/// R10 (claude-r8) closure knobs: 0 / unset off (the parent's path), 1 where the cap leaves no lane for the parent's
/// allocation, 2 always (exactness checks at a cap with room)
const R13_LBR_DEFAULT: u8 = 2; // Exact LB restore packet; R13_LBR=0 preserves the off switch.
pub(crate) fn r10(name: &str) -> u8 {
    std::env::var(name).ok().and_then(|v| v.trim().parse().ok()).unwrap_or(if name == "R13_LBR" { R13_LBR_DEFAULT } else { 0 })
}
/// R10: whether a closure fires: knob 2, or knob 1 with fewer than `need` lanes of room under the cap
pub(crate) fn r10_on(name: &str, room: usize, need: usize) -> bool {
    match r10(name) { 2 => true, 1 => room < need, _ => false }
}
/// R9_PREFIX (r9 "prefix" worker): closures for the masked-row slots' rows window (i.rows, i.sweep, i.swdec; slots
/// 0-39 of the B tree at cap 795). `R9_PREFIX` = 0 / unset off (the parent's path), 1 where the cap leaves no lane for
/// the parent's allocation, 2 always; `R9P_PARTS` (dev, default "ABCDP") restricts which parts run: A the forward
/// rows in the R5_FOLD form with X[0] released before the RowTmp, P (with A) the RowTmp without y and with R5_PRE4's
/// 4-lane prefix, B Y[W-1] lent before the sweep's prefix lanes are bound, C the undo rows' 1-lane decoder prefix, D
/// the swap decode's 1-lane window-compare prefix (C and D: mask::RSHORT4T).
fn r9p(part: char) -> u8 {
    static V: std::sync::LazyLock<u8> = std::sync::LazyLock::new(|| std::env::var("R9_PREFIX").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0));
    static P: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R9P_PARTS").unwrap_or_else(|_| "ABCDP".into()));
    if P.contains(part) { *V } else { 0 }
}
/// R9_PREFIX dev log (inert unless R9P_DBG is set): one line per firing part
fn r9p_log(part: char, b: &B, room: usize) {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("R9P_DBG").is_some());
    if *E { eprintln!("R9PFIRE {part} slot {} live {} room {room} sect {}", p3_cur_slot(), b.live, super::builder::i5::SECT.with(|c| c.get())); }
}
fn r9p_on(part: char, room: usize, need: usize) -> bool {
    match r9p(part) { 2 => true, 1 => room < need, _ => false }
}
/// R14 "läckBobby" (fotl765 R14 worker pfx94): rows-window scratch closures for the cap-794 rung. `R14_PFX94` = 0 /
/// unset off (the parent's path, byte for byte), 1 where the cap leaves no lane for the parent's allocation, 2 always
/// (exactness checks at a cap with room). `R14P_PARTS` (dev, default "STW") restricts the parts:
/// S the swap decode's window-compare prefix lane hosted on Y[W-1] (= 1, X-flipped to |0> and back),
/// T the swap decode's `core` lane (lt_cin output) hosted on Y[W-1] the same way,
/// W the slim RowTmp's zero source y left unbound through the forward rows where R15-JC frees it right after them.
/// Negative controls (dev, inert unless set): `R14P_BRK=s|t` host Y[W-1] without the flip (holding 1), `R14P_BRK=w`
/// emits one gate on the unbound y (what any reader of y in the forward rows would do).
fn r14p(part: char) -> u8 {
    static V: std::sync::LazyLock<u8> = std::sync::LazyLock::new(|| std::env::var("R14_PFX94").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0));
    static P: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R14P_PARTS").unwrap_or_else(|_| "STW".into()));
    if P.contains(part) { *V } else { 0 }
}
fn r14p_on(part: char, room: usize, need: usize) -> bool {
    match r14p(part) { 2 => true, 1 => room < need, _ => false }
}
/// R14 läckBobby-b (pfx94-b, on top of läckBobby): the masked R9_PREFIX slots' rows window (slots 0-39 of this tree at
/// cap 794), knob `R14_PFX94B` (0 / unset off, 1 where the cap leaves no lane, 2 always), `R14PB_PARTS` (dev, default
/// "FJU"): F the forward masked rows on R12_PF3's 3-lane retained decoder prefix with the bit-1 level formed on the
/// mask's AND temp (mask::RSHORT2T; prefix lane 3 bound at the sweep as R12_PF3 does), J the forward sweep in R15-JC's
/// joint-code form (no one-hot y; g and f untouched, so the VROOM clear is skipped), U the undo masked rows' decoder
/// with no retained level (mask::RSHORT5T: bits 5, 4 ANDed on the AND temp, a 12-CCX borrowed-lane toggle), which
/// releases the measured res lane jl[3]; with U the forward plain rows run unrolled (RowRoll::No) so the undo pass's
/// plain rows need no pool lane (they used that lane as their only R5_MPOOL lane). F decides the package (U planned
/// on the slots where F fires); each part lowers the cap while its lane is out, so room-driven choices are unchanged.
/// Negative controls (dev): `R14P_BRK=f|u` (mask.rs) drop a literal of the transient level, `j` binds y holding 1.
fn r14b(part: char) -> u8 {
    static V: std::sync::LazyLock<u8> = std::sync::LazyLock::new(|| std::env::var("R14_PFX94B").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0));
    static P: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R14PB_PARTS").unwrap_or_else(|_| "FJU".into()));
    if P.contains(part) { *V } else { 0 }
}
fn r14b_on(part: char, room: usize, need: usize) -> bool {
    match r14b(part) { 2 => true, 1 => room < need, _ => false }
}
pub(crate) fn r14p_brk(s: &str) -> bool {
    static E: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R14P_BRK").unwrap_or_default());
    !E.is_empty() && E.trim() == s
}
/// R14 läckBobby dev log (inert unless R14P_DBG is set): one line per firing part
fn r14p_log(part: char, b: &B, room: usize) {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("R14P_DBG").is_some());
    if *E { eprintln!("R14PFIRE {part} slot {} live {} room {room} sect {}", p3_cur_slot(), b.live, super::builder::i5::SECT.with(|c| c.get())); }
}
/// R14 läckBobby S / T: the swap decode's constant-1 host Y[W-1] (Y = B is top-normalised: Y[W-1] = 1 on every shot,
/// the premise SWAP-PRUNE, YTOP-HOST and YTOP-COF already rest on; from the slot's start to the rows nothing writes
/// lane W-1: the a-shift reaches lane NB + 1, the decode's compares read lanes < W - 1 and the un-swap skips lane
/// W - 1 under SWAP-PRUNE). None where a part is off, the lane is unbound (the term prep's release) or the levers
/// that make the premise true are off.
fn r14_ytop(u: &GreedyFrog) -> Option<QubitId> {
    let on = r14p('S') > 0 || r14p('T') > 0;
    (on && ytop_host() && swap_prune() && u.y[W - 1] != NOQ).then(|| u.y[W - 1])
}
/// R3-ROOM dev switch: `NAME=1` (unset: off, the parent's path)
pub(crate) fn r3_flag(name: &str) -> bool {
    std::env::var(name).map_or(false, |v| v.trim() == "1")
}
/// R3-ROOM dev instrument (accounting only): R3_SUBPROF=1 splits i.sweep into i.sweep (forward), i.ra1, i.sweepb
fn r3_subprof() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("R3_SUBPROF").is_some());
    *E
}
/// R5-FIT799: the "cap < 573" guards of R3-FIT799 / R4-* / R5-* were written in gate-test units (GREEDYFROG_TEST_CAP
/// = Q - 232). In a build the walk's cap is the circuit PEAK (Q itself), so those guards never fired there. Below805
/// accepts both: a test cap below 573 or a build cap below 805.
/// R6-ROOM799 dev instrument (no gates): R6_DBG=1 prints room at selected decision points
/// R6_DBG: T since the previous mark and the room, tagged (aggregate the R6T lines offline)
fn r6t(b: &B, tag: &str, room: usize) {
    if !r6dbg() { return; }
    thread_local! { static L: std::cell::Cell<u64> = const { std::cell::Cell::new(0) }; }
    let t = b.tof;
    let d = L.with(|c| { let d = t.saturating_sub(c.get()); c.set(t); d });
    eprintln!("R6T {} {tag} {d} {room}", super::builder::i5::SECT.with(|c| c.get()));
}
fn r6dbg() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("R6_DBG").is_some());
    *E
}
/// R6-ROOM799 R6_GEC (exact, cap < 805): big_lb's two constant compares on a lean chain (last carry step straight
/// into the target, `mask::ge_const_lean`), so they fit one lane lower; the erase also counts big's EFREE lane.
fn r6_gec_need(u: &GreedyFrog) -> Option<usize> {
    let (v, k1, k2) = r6_lbview(u);
    (below805(u.cap) && r3_flag("R6_GEC")).then(|| {
        super::mask::ge_const_lanes(v.len(), k1).max(super::mask::ge_const_lanes(v.len(), k2))
    })
}
/// R6-ROOM799 R6_LBV (envelope, R4_TOPC's class; cap < 805, with R6_GEC): LB[j] for h <= j < 8 (2^j > the window's
/// LB bound) is |0> on every shot at the top compare (window values, finished 0 / 1; the marks touch LB[8] only), so
/// big's two compares read the view LB[0..h) ++ LB[8] with WC + 1 and 2^h + 1 for 257. Fewer lanes and Toffoli.
fn r6_lbview(u: &GreedyFrog) -> (Vec<QubitId>, isize, isize) {
    let h = R6_LBH.with(|c| c.get());
    if h < LB_BITS - 1 && wc() < (1 << h) && below805(u.cap) && r3_flag("R6_LBV") {
        let v: Vec<QubitId> = u.lb[..h].iter().copied().chain([u.lb[LB_BITS - 1]].into_iter().filter(|&q| q != NOQ)).collect();
        (v, wc() as isize + 1, (1isize << h) + 1)
    } else {
        (u.lb.clone(), wc() as isize + 1, 257)
    }
}
/// R6-ROOM799 negative controls (gate tests only): R6_BREAK=tag
fn r6_mix(u: &GreedyFrog) -> bool {
    below805(u.cap) && r3_flag("R6_MIX")
}
fn r6_break(tag: &str) -> bool {
    cfg!(test) && std::env::var("R6_BREAK").map_or(false, |v| v.trim() == tag)
}
pub(crate) fn below805(cap: u64) -> bool {
    if cap >= 700 { cap < 805 } else { cap < 573 }
}
/// R5-FIT799 negative controls for the gate tests only (R5_BREAK=tag): fold (row >= 1 hand cell drops m's constant
/// term), fold0 (row 0 hand cell drops the carry term), x0 (the plain rows' X[0] stand-in is left |0>), lah6 (LA[6] not
/// CX-cleared before it is freed)
fn r5_break(tag: &str) -> bool {
    cfg!(test) && std::env::var("R5_BREAK").map_or(false, |v| v.trim() == tag)
}
/// R5-FIT799 dev instrument (no gates): R5_TL=lo-hi prints live and the section peak so far at tagged points of the
/// inverse slots lo..=hi
fn r5tl(b: &B, tag: &str) {
    static R: std::sync::LazyLock<Option<(i64, i64)>> = std::sync::LazyLock::new(|| std::env::var("R5_TL").ok()
        .and_then(|v| { let (a, c) = v.split_once('-')?; Some((a.trim().parse().ok()?, c.trim().parse().ok()?)) }));
    let Some((lo, hi)) = *R else { return };
    let s = p3_cur_slot() as i64;
    if s >= lo && s <= hi { eprintln!("R5TL {s} {tag} live {} peak {}", b.live, b.sect_peak.get().max(b.live));
        if std::env::var("R10_DUMPTAG").map_or(false, |t| t == tag) { super::builder::r10_dump(tag); } }
}
thread_local! {
    /// R5-FIT799 R5_PRE4: the masked rows of this slot run their 6-bit decoder on a 4-lane retained prefix (retake799's
    /// RSHORT form), so the prefix's fifth lane is idle (|0>) through both rows passes
    static R5P4: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R12_PF3 (fable 796b): the forward masked rows run their 6-bit decoder on a 3-lane retained prefix (R10_SH2's
    /// form); prefix lanes 3 and 4 are bound only for the sweep
    static R12PF3: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R12_SH3 (fable 796b): the undo masked rows run their decoder on a 2-lane retained prefix (RSHORT3 form)
    static R12S3: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R9_PREFIX C: the undo masked rows run their decoder on a 1-lane retained prefix (RSHORT4T form)
    static R9S4: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R14 läckBobby-b U: the undo masked rows run their decoder with no retained level (mask::RSHORT5T)
    static R14S5: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R14 läckBobby-b F: the forward masked rows run their decoder on R12_PF3's 3-lane prefix with the bit-1 level on
    /// the AND temp (mask::RSHORT2T)
    static R14F: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R5_MPOOL for the rows pass being recorded
    static R5MP: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R5_MROWY for the undo rows pass being recorded (masked slots): no zero-source lane
    static R5MY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R5_FOLD for the undo rows pass being recorded (masked slots): no zero-source lane and no X[0] lane
    /// (R9_PREFIX A: for the forward rows pass too)
    static R5FD: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
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
#[track_caller]
fn zero_probe(b: &B, lanes: &[QubitId]) {
    if cfg!(test) && !lanes.is_empty() && std::env::var_os("R8_ZPDBG").is_some() {
        eprintln!("ZP {} {} {:?}", b.ops.len(), std::panic::Location::caller(), lanes.iter().map(|q| q.0).collect::<Vec<_>>());
    }
    if cfg!(test) && !lanes.is_empty() {
        // R10: lanes a closure leaves unbound (NOQ) are not probed
        ZERO_PROBES.with(|p| p.borrow_mut().push((b.ops.len(), lanes.iter().copied().filter(|&q| q != NOQ).collect())));
    }
}
pub const PREMISE_MARK: u64 = u64::MAX - 5;
thread_local! {
    /// b793a: [act_const][X[W-1]][t] counts at the decode's input (gate tests, B793_PREMISE=1)
    pub static PREMISE_HIST: std::cell::RefCell<[[[u64; 32]; 2]; 4]> = std::cell::RefCell::new([[[0; 32]; 2]; 4]);
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
    /// R5-FIT799: the divisor bound 257 - (LA - d floor) is <= NB + 64
    pub dtop_n64: bool,
    /// R11_LA5 (fable, 797): the unclipped divisor bound CW - (LA - d floor) itself (dtop is clipped to NB)
    pub dtop_u: usize,
    /// a1 = 1 on every shot (slot 0: LA = 256, X[W-1] = p's MSB)
    pub a1_const: bool,
    /// MARKER_FREE: the renorm prefixes p_i with i >= la_gmin are gated by [LA > i] (7: no gate). Overshoot needs A' = 0,
    /// i.e. a finishing step (LB = 1) at some slot s - k with LA - d = LA_0 and LA_0 - 7k <= 6 at this slot
    pub la_gmin: usize,
    /// MARKER_FREE: LA < 2^la_hb at this slot's renormalisation on every non-failing shot ([LA >= 8] reads LA[3..la_hb))
    pub la_hb: usize,
    /// Q825 B-MICRO2: the slot's index in the traversal (Win::full: 0) and whether it is the last slot (NSLOTS - 1)
    pub slot: usize,
    pub last: bool,
}

impl Win {
    /// No classical knowledge: every boundary anywhere (masks everywhere, all rows).
    pub fn full() -> Win {
        Win { lb: (1, 256), lad: (0, 256), mxp: 0, mx: 0, k: KROWS, act_const: false, dtop: NB, dtop_tight: false, dtop_near: false, dtop_n64: false, dtop_u: CW, a1_const: false,
              la_gmin: if MARKER_FREE { 1 } else { 7 }, la_hb: LB_BITS, slot: 0, last: false }
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
    // R3-VERG R3_ROWS=1: mochimodev's B-SYMR25 rA table (+1 division row at slots 1-84)
    let rows = std::env::var("R3_ROWS").map_or(false, |v| v.trim() == "1");
    windows_with(if WIN_TABLE { Some(if rows { include_str!("greedyfrog_data/win_table_r3rows.txt") }
                                     else { include_str!("greedyfrog_data/win_table.txt") }) } else { None })
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
        v.push(Win { lb, lad, mxp, mx, k, act_const: false, dtop: NB, dtop_tight: false, dtop_near: false, dtop_n64: false, dtop_u: CW, a1_const: false,
                     la_gmin: 7, la_hb: LB_BITS, slot: 0, last: false });
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
        w.act_const = s + super::ftport::modp_ft::ls2k("ACT_MARGIN", ACT_MARGIN) < first_done
            || s < super::ftport::modp_ft::ls2k("ACT_UPTO", 0); // dev probe (claude-r8): treat slots < ACT_UPTO as act-constant
        w.a1_const = s == 0;
        lad_floor = lad_floor.min(w.lad.0);
        w.dtop = CW.saturating_sub(lad_floor).min(NB);
        w.dtop_tight = CW.saturating_sub(lad_floor) <= NB;
        w.dtop_near = CW.saturating_sub(lad_floor) <= NB + 32;
        w.dtop_n64 = CW.saturating_sub(lad_floor) <= NB + 64;
        w.dtop_u = CW.saturating_sub(lad_floor);
    }
    v.truncate(NSLOTS);
    let nv = v.len();
    for (s, w) in v.iter_mut().enumerate() {
        w.slot = s;
        w.last = s + 1 == nv;
    }
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
    /// LS-3 DCMP-REUSE: the previous forward slot's kept swap comparator (cmp ^ sw), consumed by this slot's F2
    pub cmp_in: Option<QubitId>,
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
    /// Z0-DEFER: the forward's z0 erase outcome, repaired by the inverse's I1 z0 wire
    pub z0m: Option<BitId>,
}


/// I5-LANES dev switches (inert unless set; the official build runs with an empty environment)
pub fn i5_flag(name: &str) -> bool {
    std::env::var_os(name).is_some()
}
fn i5_syfold() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| i5_flag("I5_SYFOLD"));
    *E
}
fn i5_split() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| i5_flag("I5_SPLIT"));
    *E
}
fn i5_dcmp7() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| i5_flag("I5_DCMP7"));
    *E
}
fn i5_rfree() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| i5_flag("I5_RFREE"));
    *E
}

thread_local! {
    static PROF: std::cell::RefCell<(u64, &'static str, Vec<(&'static str, u64, u64, u64)>, u64)> =
        std::cell::RefCell::new((0, "", vec![], 0));
}
/// GREEDYFROG_PROF=1: accumulate Toffoli per named section, the peak reached inside it and the section's highest live
/// count (debug aid, no effect on gates).
thread_local! {
    /// m1-shell diagnostic: division number (1, 2) set by div_forward
    pub static M1DIV: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    /// m1-shell diagnostic: (section name, ops.len() at its start)
    static M1B: std::cell::RefCell<Vec<(&'static str, usize)>> = const { std::cell::RefCell::new(Vec::new()) };
}
/// m1-shell diagnostic: the recorded section boundaries
pub fn m1_take() -> Vec<(&'static str, usize)> { M1B.with(|v| std::mem::take(&mut *v.borrow_mut())) }
thread_local! {
    /// H793: the current profile section's name, tracked in every build (the I5 SECT tracker needs GREEDYFROG_PROF + I5_SNAP)
    static H793_SECT: std::cell::Cell<&'static str> = const { std::cell::Cell::new("-") };
}
pub fn prof(b: &B, name: &'static str) {
    H793_SECT.with(|c| c.set(name));
    if std::env::var_os("GREEDYFROG_PROF").is_none() { return; }
    // m1-shell diagnostic (inert unless M1_EXP is set): op-index boundary of every profile section
    if std::env::var_os("M1_EXP").is_some() { M1B.with(|v| v.borrow_mut().push((name, b.ops.len()))); }
    let sp = b.take_sect_peak();
    if std::env::var_os("I5_SNAP").is_some() {
        let prev = super::builder::i5::SECT.with(|c| c.get());
        let slot = super::builder::i5::SLOT.with(|c| c.get());
        eprintln!("I5SEC {prev} {slot} {sp}");
        super::builder::i5::set_sect(if name == "end" { "-" } else { name });
    }
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
pub fn p3_cur_slot() -> usize {
    P3ST.with(|p| p.borrow().0)
}
pub fn p3_slot(s: usize) {
    P3ST.with(|p| p.borrow_mut().0 = s);
    super::builder::i5::set_slot(s as i64);
}
fn p3(b: &mut B, u: &mut GreedyFrog, name: &str) {
    super::builder::i5::set_lalb(&u.la, &u.lb); // q792 diagnostic (inert unless I5_SNAP is set)
    if std::env::var_os("B792_LALBW").is_some() {
        let nb = |v: &Vec<QubitId>| v.iter().filter(|&&q| q != NOQ && !b.is_free(q)).count();
        let nv = |v: &Vec<QubitId>| v.iter().filter(|&&q| q != NOQ).count();
        let st = |q: QubitId| if q == NOQ { 'N' } else if b.is_free(q) { 'f' } else { 'L' };
        let l8: String = (5..9).map(|i| st(u.la[i])).collect(); let b8: String = (5..9).map(|i| st(u.lb[i])).collect();
        eprintln!("LA8 {} {} la58 {} lb58 {} shared8 {}", name, p3_cur_slot(), l8, b8, (u.la[8] == u.lb[8] && u.la[8] != NOQ) as u8);
        eprintln!("LALBW {} {} la_bound {} la_live {} lb_bound {} lb_live {} live {} cnt {}", name, p3_cur_slot(), nv(&u.la), nb(&u.la), nv(&u.lb), nb(&u.lb), b.live, u.cnt.len());
    }
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
    // R8-LANE799: the generic helpers' cap follows the probe (P3_CAP2=1)
    if std::env::var_os("P3_CAP2").is_some() && name.starts_with("f.") { p2_set_cap(u.cap); }
}
thread_local! {
    /// R3-VERG (port of retake799's MJ, odinfree 70f3fbb): the next inverse slot's (k, plain rows)
    static MJ_NEXT: std::cell::Cell<Option<(usize, bool)>> = std::cell::Cell::new(None);
    /// R3-VERG: the measured jl bits whose stall-shot phase the next inverse slot repairs, and whether that repair
    /// needs the stall gate (marker-free ring, slot not act-constant)
    static MJ_PEND: std::cell::RefCell<Option<(Vec<BitId>, bool)>> = std::cell::RefCell::new(None);
    static MJ_NSLOT: std::cell::Cell<usize> = std::cell::Cell::new(0);
}
/// R3-VERG (dev switch `R3_VERG=1`; off = v3): Vergasslifrosch, the measured erase of J in the inverse sweep
/// (odinfree / worker retake799, row 70f3fbb, marker-free form).
pub(crate) fn verg_on() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("R3_VERG").map_or(false, |v| v.trim() == "1"));
    *E
}
/// R3-VERG: before inverse slot s, the window of inverse slot s-1 (None for slot 0).
pub fn mj_set_next(w: Option<&Win>) {
    MJ_NEXT.with(|c| c.set(w.map(|w| (w.k, w.mx >= NB + 1))));
}
/// R3-VERG: at both ends of an inverse traversal.
pub fn mj_clear() {
    MJ_NEXT.with(|c| c.set(None));
    MJ_PEND.with(|p| *p.borrow_mut() = None);
    R4_PEND.with(|p| *p.borrow_mut() = None);
}

// ------------------------------------------------------------------ R4-RHO: in-place rho / a1 decode
// Dev switches (unset = R3-FIT799's tree): R4_RHO=1 decodes rho and a1 in place on VERG slots: jl -> t = sX - sY - J
// (jl_map, once), then (t, one fresh lane) -> (rho on jl[0..3], a1 on the fresh lane, res = m - 1 on jl[3..5]) and only
// res is X-measured. res = 0 on every step and finished shot, so no step repair is needed and J is never restored.
// A stall at inverse slot k (m-th stall since the step) has t_(k-1) = 7m at the next inverse slot k-1, so its owed
// phase (-1)^(b . res) is (-1)^(b0 t3 + b1 t4) there, on the stall shots only (X[W-1] = 0 and LA != 0 on the post-state;
// X[W-1] = 0 alone where slot k is act-constant). The stall repair needs no equal-k plain neighbour, so
// R4_WIDE=1 also runs the measured erase on plain slots whose next inverse slot is not an equal-k plain one.
thread_local! {
    /// R4-RHO: the measured res bits whose stall-shot phase the next inverse slot repairs, and whether that repair needs
    /// the stall gate (the measuring slot was not act-constant)
    static R4_PEND: std::cell::RefCell<Option<(Vec<BitId>, bool)>> = std::cell::RefCell::new(None);
}
fn r4_on() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("R4_RHO"));
    *E
}
fn r4_wide() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("R4_WIDE"));
    *E
}
/// Negative controls for the gate tests only (R4_BREAK=k): 1 drops the c-erase repair, 2 drops the owed stall
/// repair, 3 repairs on t2, t3 instead of t3, t4, 4 skips the act zeroing, 5 drops the stall gate (X[W-1] only).
fn r4_break(k: u32) -> bool {
    cfg!(test) && std::env::var("R4_BREAK").map_or(false, |v| v.trim() == k.to_string())
}

/// R4-RHO: in place on j = t (5 lanes, t = 0 on finished shots), with two transient lanes (k, c; then e, c; then e,
/// tau): j[0..3] -> rho, j[3..5] -> res (m - 1 on the m-th stall, 0 otherwise), e ^= [t < 8] (e: a |0> lane the caller
/// placed before lending its hosts, so it never lands on a lane re-acquired by id).
/// 7 Toffoli + the c erase's conditioned repair (2 CCZ + 1 AND). Model: R4-RHO/model/decode_exhaustive.py.
fn r4_decode(b: &mut B, j: &[QubitId], e: QubitId) {
    // R12-DEC: carry-tag six-wire rho/res decoder on two already-live dirty hosts.
    // The literal permutation is certified over all 256 six-wire states, including dirty-host restoration.
    if r3_flag("R12_DECODE_PERM") {
        let lanes = [j[0], j[1], j[2], j[3], j[4], e];
        let dirty: Vec<QubitId> = super::mask::borrowed().into_iter().filter(|q| !lanes.contains(q)).collect();
        assert!(dirty.len() >= 2, "R12_DECODE_PERM needs two dirty hosts");
        let q = [lanes[0], lanes[1], lanes[2], lanes[3], lanes[4], lanes[5], dirty[0], dirty[1]];
        b.x(q[3]);
        b.x(q[4]);
        b.ccx(q[3], q[4], q[5]);
        b.x(q[3]);
        b.x(q[4]);
        b.ccx(q[2], q[7], q[5]);
        b.ccx(q[1], q[6], q[7]);
        b.ccx(q[3], q[0], q[6]);
        b.ccx(q[1], q[6], q[7]);
        b.ccx(q[2], q[7], q[5]);
        b.ccx(q[1], q[6], q[7]);
        b.ccx(q[3], q[0], q[6]);
        b.ccx(q[1], q[6], q[7]);
        b.ccx(q[1], q[6], q[2]);
        b.ccx(q[3], q[0], q[6]);
        b.ccx(q[1], q[6], q[2]);
        b.ccx(q[3], q[0], q[6]);
        b.ccx(q[3], q[0], q[1]);
        b.cx(q[3], q[0]);
        b.ccx(q[2], q[6], q[5]);
        b.ccx(q[4], q[1], q[6]);
        b.ccx(q[2], q[6], q[5]);
        b.ccx(q[4], q[1], q[6]);
        b.ccx(q[4], q[1], q[2]);
        b.cx(q[4], q[1]);
        b.ccx(q[5], q[0], q[1]);
        b.cx(q[5], q[0]);
        b.x(q[3]);
        b.x(q[4]);
        b.ccx(q[3], q[4], q[0]);
        b.x(q[3]);
        b.x(q[4]);
        b.x(q[3]);
        b.x(q[4]);
        b.ccx(q[0], q[6], q[1]);
        b.ccx(q[3], q[4], q[6]);
        b.ccx(q[0], q[6], q[1]);
        b.ccx(q[3], q[4], q[6]);
        b.x(q[3]);
        b.x(q[4]);
        b.x(q[5]);
        b.x(q[3]);
        b.ccx(q[5], q[3], q[4]);
        b.x(q[3]);
        b.cx(q[5], q[3]);
        b.x(q[5]);
        b.ccx(q[3], q[4], q[5]);
        b.x(q[2]);
        b.x(q[4]);
        b.x(q[1]);
        b.ccx(q[1], q[7], q[5]);
        b.ccx(q[4], q[6], q[7]);
        b.ccx(q[2], q[3], q[6]);
        b.ccx(q[4], q[6], q[7]);
        b.ccx(q[1], q[7], q[5]);
        b.ccx(q[4], q[6], q[7]);
        b.ccx(q[2], q[3], q[6]);
        b.ccx(q[4], q[6], q[7]);
        b.x(q[2]);
        b.x(q[4]);
        b.x(q[1]);
        b.cx(q[1], q[0]);
        b.x(q[2]);
        b.x(q[3]);
        b.ccx(q[0], q[7], q[5]);
        b.ccx(q[4], q[6], q[7]);
        b.ccx(q[2], q[3], q[6]);
        b.ccx(q[4], q[6], q[7]);
        b.ccx(q[0], q[7], q[5]);
        b.ccx(q[4], q[6], q[7]);
        b.ccx(q[2], q[3], q[6]);
        b.ccx(q[4], q[6], q[7]);
        b.x(q[2]);
        b.x(q[3]);
        b.cx(q[1], q[0]);
        return;
    }
    let (l0, l1, l2, h0, h1) = (j[0], j[1], j[2], j[3], j[4]);
    let c;
    if r3_flag("R11_DEC1") {
        // R11_DEC1 (fable, 797): the same s = l + h mod 8 with carry out c on ONE fresh lane: l += h0 overflows iff
        // l == 7, then l += 2 h1 overflows iff the new l >= 6 (never both: l + h <= 10), each increment on borrowed
        // lanes (inc_dirty); c = XOR of the two overflow predicates. Exact; ~18 Toffoli for 7.
        c = b.alloc();
        let d = super::mask::borrowed();
        super::arith::and_dirty(b, &[(h0, false), (l0, false), (l1, false), (l2, false)], c, &d);
        super::arith::inc_dirty(b, h0, &[l0, l1, l2], &d);
        super::arith::and_dirty(b, &[(h1, false), (l1, false), (l2, false)], c, &d);
        super::arith::inc_dirty(b, h1, &[l1, l2], &d);
    } else {
    // s = l + h (3 bits) with carry out c: half adder on bit 0, Cuccaro MAJ / UMA on bit 1 (carry in k), AND on bit 2
    let k = b.alloc();
    b.and_c(l0, h0, k);
    b.cx(h0, l0);
    b.cx(h1, l1);
    b.cx(h1, k);
    b.ccx(k, l1, h1);
    c = b.alloc();
    b.and_c(h1, l2, c);
    b.cx(h1, l2);
    b.ccx(k, l1, h1);
    b.cx(h1, k);
    b.cx(k, l1);
    b.cx(h0, l0);
    b.and_u(l0, h0, k);
    b.cx(h0, l0);
    b.free(k);
    }
    // end-around carry: rho = s + c (c = 1 leaves s <= 2: no carry into bit 2)
    b.ccx(c, l0, l1);
    b.cx(c, l0);
    // e = [h == 0]; res = h - 1 + c on stalls (h0 ^= e makes the step's h = 0 a 1, then h -= !c mod 4)
    b.x(h0);
    b.x(h1);
    b.and_c(h0, h1, e);
    b.x(h0);
    b.x(h1);
    b.cx(e, h0);
    b.x(c);
    b.x(h0);
    b.ccx(c, h0, h1);
    b.x(h0);
    b.cx(c, h0);
    b.x(c);
    // erase c: c = [res=1][rho=1] ^ [res=2][rho<=2] ^ [res=3] on every reachable (rho, res) (rho >= 1 where res >= 1)
    //            = tau & (!res1 & !rho1 ^ res1 & (rho1 ^ rho0)) ^ res0 & res1,  tau = !rho2 & (res0 ^ res1)
    let m = b.fresh_bits(1)[0];
    b.hmr_to(c, m);
    b.free(c);
    if !r4_break(1) {
        b.push_condition(m);
        b.cx(h1, h0);
        let tau = b.alloc();
        b.x(l2);
        b.and_c(l2, h0, tau);
        b.x(h1);
        b.x(l1);
        b.ccz(tau, h1, l1);
        b.x(l1);
        b.x(h1);
        b.cx(l1, l0);
        b.ccz(tau, h1, l0);
        b.cx(l1, l0);
        b.and_u(l2, h0, tau);
        b.x(l2);
        b.free(tau);
        b.cx(h1, h0);
        b.cz(h0, h1);
        b.pop_condition();
    }
}

// ------------------------------------------------------------------ b793a: Gipfeli (F13 closure at cap 793)
// The R4-RHO decode without its sixth |0> lane: X[W-1] (x) is the sixth wire. Premise (the tree's own R4-RHO premise, used by
// r4_pend_apply): x = 0 only on shots that stalled at the previous inverse slot (t in {7, 14, 21, 28}) or on finished shots
// (t = 0, non-act-const slots). MEASURED (model/PREMISE.txt): on act-const slots x = 0 gives t in {7, 14} only (7,203 shot-slots);
// on non-act-const slots x = 0 also occurs with t = 1..6, 8, 11 (about 2,200 shot-slots), so Gipfeli runs on act-const slots only.
// Model and certificates: lanes/b793a/model (states.py, gip1.py, verify_gip.py).
// Stage 1 (P1, 6 lanes j0..j4, x): res1 = [t >= 22] lands on x's lane, the other five lanes hold the injective code of
// (rho, a1, res0, x) (26 combos); res1 is X-measured (that lane is |0>); stage 2 (P2, same lanes): code -> rho on j0..j2,
// res0 on j3, a1 on j4, x back on its lane; res0 is X-measured on j3. a1 sits on jl[4]; jl[3] is |0>.
// Tables are MCX lists over lanes [j0, j1, j2, j3, j4, x] as (control mask, control values, target), searched by
// lanes/b793a/synth and certified over all 37 valid states by model/verify_gip.py.
const B793_P1: &[(u8, u8, u8)] = &[(32, 0, 0), (16, 0, 5), (24, 24, 1), (38, 38, 4), (24, 16, 5), (36, 32, 4), (56, 32, 1), (34, 32, 3), (34, 32, 2), (24, 24, 5), (38, 36, 3)];
const B793_P2: &[(u8, u8, u8)] = &[(16, 0, 5), (8, 0, 4), (16, 0, 3), (38, 6, 3), (17, 1, 1), (24, 0, 0), (24, 8, 5), (9, 8, 1), (19, 0, 2), (34, 2, 4), (11, 9, 2), (12, 8, 0), (33, 0, 3), (40, 8, 2), (23, 0, 3), (12, 8, 0)];

/// Gipfeli puts a1 on the parent's e id (every later id-driven choice unchanged) from this slot up; below it a1 stays on jl[4]
/// (slots 40-43: the parent's e lands on a lent id and r5_rebind then needs one more lane at the re-acquire).
const B793_MIMIC_FROM: i64 = 44;
/// SOURCE CONSTANT for the F13 closure (worker b793a): true = Gipfeli and NOG on in every build (the official empty environment
/// included); false = off, the parent's stream byte for byte. Env override either way: WL_B793_F13=1 / 0; B793_GIP / B793_NOG=1
/// switch one closure on alone (dev). Not baked on: the 793 rung needs the other families as well.
pub const B793_F13: bool = false;
/// b792w4 P11 (B792_P11): on the act-constant slim R15-JC slots 44-188 the rows' carry pool lane f is a lent pool lane only
/// (ROW-F: the rows read the carry-in from the sign lane; R15-JC frees f right after the forward rows), so it is not bound with the RowTmp
/// b792 rows40 (B792_R40=1): P11 / P11S lower slot bound 40 instead of 44 (slots 40-43 are slim act-constant plain-row slots like 44+)
fn p11_lo() -> usize { if r3_flag("B792_R40") || r3_flag("B792_R40A") { 40 } else { 44 } }
fn p11s_lo() -> usize { if r3_flag("B792_R40") || r3_flag("B792_R40B") { 40 } else { 44 } }
fn b792_p11() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_P11").map_or(super::B792_P11, |v| v.trim() == "1"));
    *E
}
/// b792w4 P11S (B792_P11S): the inverse sweep of the act-constant plain-row slots 44-187 without a jl register (see lanes/b792w4/DESIGN-NOJL.md):
/// (rho, a1) = rho_of((sX - sY - jl) mod 32) is XORed straight into 4 lanes through two passes of commuting involutions
/// on borrowed dirty lanes (search-flag toggles a_j), sX offset in place and restored
fn b792_p11s() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_P11S").map_or(super::B792_P11S, |v| v.trim() == "1"));
    *E
}
/// B792_IDGATE: the P11S free-id gate (`nj_nf` below) accepts every count >= 4 (the requirement: nj_run needs rho (3) + a1 (1) = 4 lanes; 3 free ids is genuine lack of room).
/// nj_nf is width-so-far minus live (builder.rs alloc takes the lowest free id, else grows the width), a build-order count; lowest_free(6) caps it at 6, so `== 5` also refused 6
/// (the ACTREK mode). The 5-free path's hold of the fifth id changes no op on this tree (lanes/b792gate/REPORT.md); a refusal still cascades through the R4_PEND clause of the nj predicate.
fn b792_idgate() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_IDGATE").map_or(super::B792_IDGATE, |v| v.trim() == "1"));
    *E
}
/// b792 SWEEP (B792_SWEEP): the P11S no-jl sweep on the act-live slots 189-232 (act read from the ACTFOLD pair on 189-202, from the lane rt.f on 203-232;
/// bb is gated by act), and needs B792_IDGATE (merge 25) for the 4-free-id picture of a 792-wide build. See lanes/b792sweep/REPORT.md
fn b792_sweep() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_SWEEP").map_or(super::B792_SWEEP, |v| v.trim() == "1"));
    *E
}
fn sweep_live_slot(sl: usize) -> bool { (189..=232).contains(&sl) }
/// dev only (B792_SWEEP_DECLINE=lo-hi): nj_live declines on those slots, so the late-bound jl path runs there and produces R4_PEND for the slot below:
/// exercises the fallback and, one slot below a decline on 189-202, a gated debt arriving at an ACTFOLD pair slot (census + gate must stay exact)
fn sweep_decline(sl: usize) -> bool {
    std::env::var("B792_SWEEP_DECLINE").ok().and_then(|v| v.split_once('-').map(|(a, c)| (a.trim().parse::<usize>().unwrap_or(1000), c.trim().parse::<usize>().unwrap_or(0)))).map_or(false, |(a, c)| (a..=c).contains(&sl))
}
/// rho_of (greedyfrog_model.rs): r < 8: (r, a1 = 1), else ((r mod 8 + #{8, 15, 22, 29 <= r}) mod 8, 0); packed rho | a1 << 3
fn nj_f(r: usize) -> usize {
    let r = r & 31;
    if r < 8 { return r | 8; }
    let m = [8usize, 15, 22, 29].iter().filter(|&&c| r >= c).count();
    ((r & 7) + m) & 7
}
/// ANF monomials (bit masks over r0..r4) of each of the 4 output bits of nj_f
fn nj_anf() -> Vec<Vec<usize>> {
    (0..4).map(|bit| {
        let mut c: Vec<usize> = (0..32).map(|x| (nj_f(x) >> bit) & 1).collect();
        for i in 0..5 { for x in 0..32 { if x >> i & 1 == 1 { c[x] ^= c[x ^ (1 << i)]; } } }
        (0..32).filter(|&x| c[x] == 1).collect()
    }).collect()
}
/// b792 SWEEP (B792_SWEEP): where the act-live no-jl sweep reads act. `Lane(f)`: f = !act (R11-FOLD's running OR lane rt.f, slots 203-232);
/// `Pair(l5, l6)`: !act = l5 & l6 on the pristine ACTFOLD code point (slots 189-202, LA[5], LA[6] untouched); `None`: act-constant slots (out is ungated)
#[derive(Clone, Copy)]
pub enum NjAct { None, Lane(QubitId), Pair(QubitId, QubitId) }
/// out[0..3] ^= rho, out[3] ^= a1 of (sX - sY - jl) where jl = the last row j <= kt with quotient bit 1 (lane_j = 0), else 0.
/// `pend`: measured res bits whose stall phase this slot owes: phase (-1)^(m_i t_{o_i} (1 ^ X[W-1])), t = sX - sY - jl, o = (3, 4)
/// `gp` (the pending repair is gated, owed by a non-act-constant slot): (LA lanes to skip as lent hosts, ACTFOLD's pair): phase (-1)^(m_i t_o (1 ^ X ^ g)),
/// g = !X & [LA == sX on every non-skipped lane] as in r4_pend_apply; LA ^= sX (and the pair CX) around the whole sweep, before sX is offset
fn nj_sweep(b: &mut B, u: &GreedyFrog, w: &Win, rt: &RowTmp, sx: &[QubitId], sy0: QubitId, out: &[QubitId], pend: Option<Vec<BitId>>, gp: Option<(Vec<QubitId>, Option<(QubitId, QubitId)>)>, act: NjAct) {
    let k = w.k;
    let kt5: Vec<QubitId> = u.lb[..R_BITS].to_vec();
    let lanes: Vec<QubitId> = (0..k).map(|j| if j == 0 { NOQ } else { rt.rem(u, j as isize - 1) }).collect();
    nj_run(b, k, &kt5, &lanes, u.x[W - 1], sx, sy0, out, &u.dirty, &u.la, pend, gp, act);
}
fn nj_run(b: &mut B, k: usize, kt5: &[QubitId], lanes: &[QubitId], xt: QubitId, sx: &[QubitId], sy0: QubitId, out: &[QubitId], dirty: &[QubitId], la: &[QubitId],
          pend: Option<Vec<BitId>>, gp: Option<(Vec<QubitId>, Option<(QubitId, QubitId)>)>, act: NjAct) {
    assert!(k >= 2 && k <= 31 && sx.len() == R_BITS && out.len() == 4);
    // FRAME NOTE (lanes/b792sweep/FRAME-VERDICT.md Q1/Q2): the gp wrap rewrites l6 := l5 ^ l6 when the ACTFOLD pair is passed (afp), so a pair read of
    // !act as (l5, l6) = (1, 1) inside it would select ACTIVE shots with u in 32..63. In the build afp is ALWAYS None at an nj call (AF_PAIR is set after the
    // sweep and cleared at R9-c in the same slot, so it is None when the next slot starts): this assert guards a future change, it cannot fire today. With afp None the wrap
    // only XORs LA[0..5) with sX, l5/l6 stay pristine, the pair literal (1,1) is read in the parent's frame, and a pair slot with a gated debt is value-correct
    // (nj's g needs l5 = l6 = 0, the parent's l5 == l6; they differ only on finished shots, whose bb is 0): covered by the kernel gate (mode 2 x gp).
    assert!(!(matches!(act, NjAct::Pair(..)) && gp.as_ref().map_or(false, |(_, afp)| afp.is_some())), "b792 SWEEP: ACTFOLD pair read inside the pair-rewriting gp wrap");
    let kt5: Vec<QubitId> = kt5.to_vec();
    let lane = |j: usize| lanes[j];
    let mut busy: Vec<QubitId> = out.to_vec();
    busy.extend(sx); busy.push(sy0); busy.extend(&kt5); busy.push(xt); busy.extend(la.iter().filter(|&&q| q != NOQ));
    busy.extend((1..k).map(|j| lane(j)));
    match act { NjAct::Lane(f) => busy.push(f), NjAct::Pair(l5, l6) => { busy.push(l5); busy.push(l6); } NjAct::None => {} }
    let pool: Vec<QubitId> = dirty.iter().copied().filter(|q| !busy.contains(q)).collect();
    assert!(pool.len() >= k + 6, "b792 P11S: {} borrowed lanes", pool.len());
    let a: Vec<QubitId> = pool[..k].to_vec();
    let bb = pool[k];
    let d: Vec<QubitId> = pool[k + 1..].to_vec();
    let anf = nj_anf();
    let mut glits: Vec<(QubitId, bool)> = vec![];
    if let Some((skip, afp)) = &gp {
        for (i, &q) in sx.iter().enumerate() { b.cx(q, la[i]); }
        if let Some((l5, l6)) = afp { b.cx(*l5, *l6); }
        glits.push((xt, true));
        glits.extend(la.iter().filter(|q| !skip.contains(q) && afp.map_or(true, |(l5, _)| **q != l5) && !(b792_brk("p11s_la3") && la.len() > 3 && **q == la[3])).map(|&q| (q, true)));
        assert!(glits.iter().all(|l| l.0 != NOQ), "b792 P11S: unbound LA lane in the stall gate");
    }
    // sX -= sY
    for &q in sx { b.x(q); }
    super::arith::inc_dirty(b, sy0, sx, &d);
    for &q in sx { b.x(q); }
    let bb_toggle = |b: &mut B, j: usize| {
        let mut base: Vec<(QubitId, bool)> = vec![(a[j], false)];
        if j > 0 { base.push((lane(j), true)); }
        match act {
            NjAct::None => { if j == 0 { b.cx(a[0], bb); } else { and_dirty(b, &base, bb, &d); } }
            NjAct::Lane(f) => {
                if !b792_brk("sw_gate") && !(j == 0 && b792_brk("sw_row0")) { base.push((f, true)); }
                if base.len() == 1 { b.cx(a[0], bb); } else { and_dirty(b, &base, bb, &d); }
            }
            NjAct::Pair(l5, l6) => {
                // act = 1 ^ (l5 & l6): bb ^= base, then bb ^= base & l5 & l6
                if j == 0 { b.cx(a[0], bb); } else { and_dirty(b, &base, bb, &d); }
                if !b792_brk("sw_pair") && !(j == 0 && b792_brk("sw_row0")) { base.push((l5, false)); base.push((l6, false)); and_dirty(b, &base, bb, &d); }
            }
        }
    };
    let gates = |b: &mut B, j: usize| {
        // bb ^= a_j & !lane_j [& act] (j = 0: a_0 [& act]); act-live: bb itself is gated, so out and the owed phase see act on every use
        bb_toggle(b, j);
        for (bit, ms) in anf.iter().enumerate() {
            for &m in ms {
                if (b792_brk("p11s_mono") || (b792_brk("p11s40") && p3_cur_slot() < 44)) && bit == 0 && m == 1 { continue; }
                let mut lits = vec![(bb, false)];
                lits.extend((0..R_BITS).filter(|&i| (m >> i) & 1 == 1).map(|i| (sx[i], false)));
                and_dirty(b, &lits, out[bit], &d);
            }
        }
        if let Some(mb) = &pend {
            for (i, &m) in mb.iter().enumerate() {
                let o = if i == 0 { 3 } else { 4 };
                b.push_condition(m);
                // (-1)^(q (1 ^ X ^ g)), q = bb & sX[o]: z, cz(X), cz(g) as in r4_pend_apply's lane-free form. The debt is only ever owed by a
                // non-act-constant slot (the stall gate): slot 188 after slot 189, the only slot below 189 that follows a measuring decode
                assert!(gp.is_some(), "b792 P11S: a pending stall phase without the gate is not reachable on slots 44-188");
                // b792 SWEEP: phase_and's room-0 form borrows the PREFIX of mask::borrowed() as ancillas (u.dirty, in order); an ancilla that is also one of the gate's
                // literals (bb, sX[o], X[W-1], an LA lane) would corrupt the phase. In the real build the prefix is far from bb = pool[k] (k >= 19); fail closed if not
                let chk = |b: &B, lits: &[(QubitId, bool)]| {
                    let n = lits.len();
                    if n >= 3 && p2_room(b) < n - 2 {
                        let dl = super::mask::borrowed();
                        assert!(dl.iter().take(n - 1).all(|q| !lits.iter().any(|l| l.0 == *q)), "b792 SWEEP: phase_and's borrowed prefix overlaps its literals");
                    }
                };
                chk(b, &[(bb, false), (sx[o], false), (xt, false)]);
                if !b792_brk("p11s_pend") {
                    phase_and(b, &[(bb, false), (sx[o], false)]);
                    phase_and(b, &[(bb, false), (sx[o], false), (xt, false)]);
                }
                let mut l = glits.clone();
                l.push((bb, false));
                l.push((sx[o], false));
                chk(b, &l);
                if !b792_brk("p11s_gate") { phase_and(b, &l); }
                b.pop_condition();
            }
        }
        bb_toggle(b, j);
    };
    let dec = |b: &mut B| if !b792_brk("p11s_dec") { add_const_dirty(b, sx, 1, true, &d) };
    let inc = |b: &mut B| add_const_dirty(b, sx, 1, false, &d);
    let toggle = |b: &mut B, up: bool| {
        // up: the toggle, else its inverse (the same gates in the reverse order)
        let asc = |b: &mut B| { for j in 0..k - 1 { b.ccx(lane(j + 1), a[j + 1], a[j]); } };
        let ge = |b: &mut B| if !b792_brk("p11s_ge") { super::mask::ge_const_dirty_gated(b, &kt5, k as isize - 1, a[k - 1], &[], &d) };
        if up {
            asc(b);
            ge(b);
            for j in (0..k - 1).rev() { b.ccx(lane(j + 1), a[j + 1], a[j]); and_dirty(b, &eq_lits(&kt5, j), a[j], &d); }
        } else {
            for j in 0..k - 1 { and_dirty(b, &eq_lits(&kt5, j), a[j], &d); b.ccx(lane(j + 1), a[j + 1], a[j]); }
            ge(b);
            for j in (0..k - 1).rev() { b.ccx(lane(j + 1), a[j + 1], a[j]); }
        }
    };
    // pass A: rows 0..k-1 ascending (sX holds R_j = sX - sY - j at row j)
    gates(b, 0);
    for j in 1..k { dec(b); gates(b, j); }
    toggle(b, true);
    // pass B: rows k-1..0 descending
    for j in (1..k).rev() { gates(b, j); inc(b); }
    gates(b, 0);
    toggle(b, false);
    // sX += sY
    super::arith::inc_dirty(b, sy0, sx, &d);
    if let Some((_, afp)) = &gp {
        if let Some((l5, l6)) = afp { b.cx(*l5, *l6); }
        for (i, &q) in sx.iter().enumerate() { b.cx(q, la[i]); }
    }
}
fn b793a_f8() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793A_F8"));
    *E
}
/// slots F8 may touch: the late non-act-constant slots only
fn rt_f8_ok(w: &Win) -> bool { !w.act_const && w.slot >= 189 && (w.slot <= 254 || (w.slot == 255 && r3_flag("B793_S255"))) }
fn b793a_f12() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793A_F12"));
    *E
}
fn b793a_brk(tag: &str) -> bool { cfg!(test) && std::env::var("B793A_BREAK").map_or(false, |v| v.trim() == tag) }
fn b793_f13() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("WL_B793_F13").map_or(B793_F13, |v| v.trim() == "1"));
    *E
}
/// b793b F6 (dev knob `B793_F6=1`, slots `B793_F6_SLOTS=a-c`, default 0-39): the masked rows of the act-constant R9_PREFIX slots run without the mask's AND
/// temp g (RowTmp.g and Masked.t are NOQ): mask.rs NOTEMP cells (three-control cells on one borrowed dirty lane, 4 CCX), the U decoder as a 6-control AND on
/// borrowed lanes, the forward decoder as RSHORT2, the jl map on sY's negated lane (NOG's form) and no g in the decode; see mask.rs `NOTEMP`.
thread_local! { static B793_ACTCAP: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
fn b793_actcap() -> bool { r3_flag("B793_ACTCAP") }
fn b793_f12() -> bool { r3_flag("B793_F12") }
fn b793_f6_mode() -> u8 { static E: std::sync::LazyLock<u8> = std::sync::LazyLock::new(|| std::env::var("B793_F6").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0)); (*E).min(2) + (*E >= 3) as u8 * 0 }
/// B793_F6=2 (cheaper): the forward rows keep the parent's cells and RSHORT2T toggles with the lent Y[W-1] lane (|0> through the whole forward pass) as the AND temp; NOTEMP only in the undo rows
fn b793_f6() -> bool { b793_f6_mode() >= 1 }
fn b793_f6_slot(w: &Win) -> bool {
    b793_f6() && w.act_const && std::env::var("B793_F6_SLOTS").ok().as_deref().unwrap_or("0-39").split_once('-')
        .map_or(false, |(a, c)| matches!((a.parse::<usize>(), c.parse::<usize>()), (Ok(a), Ok(c)) if (a..=c).contains(&p3_cur_slot())))
}
fn b793_gip() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_GIP") || b793_f13());
    *E
}
fn b793_nog() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_NOG") || b793_f13());
    *E
}
/// Negative controls for the gate tests only (B793_BREAK=k): 1 skips the last P1 gate, 2 skips the last P2 gate,
/// 3 measures res0 and res1 on swapped bit ids, 4 drops the first X on sY[0] in the g-free jl map, 5 drops LA's literals from the lane-free stall gate at slot 188 only.
fn b793_break(k: u32) -> bool {
    cfg!(test) && std::env::var("B793_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
/// b793b GIPX (B793_GIPX=1): the Gipfeli tables extended by the x = 0 states t = 6, 13, 20, 27 (7n - 1: the saturated-funnel neighbours of the stall points); synth: lanes/b793b/py/gipx/gen2.py
const B793_P1X: &[(u8, u8, u8)] = &[(32, 0, 0), (22, 22, 3), (16, 0, 5), (24, 24, 1), (40, 40, 4), (16, 16, 5), (34, 32, 2), (25, 24, 1), (44, 36, 4), (50, 48, 3), (30, 22, 5), (40, 32, 2), (26, 24, 5), (29, 25, 1), (40, 32, 1)];
const B793_P2X: &[(u8, u8, u8)] = &[(8, 8, 0), (16, 0, 5), (8, 0, 4), (16, 0, 3), (38, 6, 3), (24, 8, 5), (49, 32, 1), (32, 0, 4), (19, 0, 2), (40, 0, 0), (9, 9, 1), (23, 0, 3), (11, 9, 2), (14, 8, 0), (40, 8, 2), (34, 0, 4)];
fn b793_gipx() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B793_GIPX")); *E }
fn b793_mcx(b: &mut B, lanes: &[QubitId; 6], gates: &[(u8, u8, u8)], dirty: &[QubitId]) {
    for &(cm, cv, t) in gates {
        let lits: Vec<(QubitId, bool)> = (0..6).filter(|i| cm >> i & 1 == 1).map(|i| (lanes[i], cv >> i & 1 == 0)).collect();
        let tg = lanes[t as usize];
        if lits.is_empty() { b.x(tg); } else { super::arith::and_dirty(b, &lits, tg, dirty); }
    }
}
/// The decode on j (5 lanes) and xl (X[W-1]); measures res1 into mb[1] and res0 into mb[0]; returns a1's lane (j[4]).
/// j[3] is |0> afterwards.
fn b793_decode(b: &mut B, j: &[QubitId], xl: QubitId, mb: &[BitId]) -> QubitId {
    let lanes = [j[0], j[1], j[2], j[3], j[4], xl];
    let dirty: Vec<QubitId> = super::mask::borrowed().into_iter().filter(|q| !lanes.contains(q)).collect();
    assert!(dirty.len() >= 3, "B793 Gipfeli needs three dirty hosts, have {}", dirty.len());
    let (t1, t2): (&[(u8, u8, u8)], &[(u8, u8, u8)]) = if b793_gipx() { (B793_P1X, B793_P2X) } else { (B793_P1, B793_P2) };
    let (n1, n2) = (t1.len() - b793_break(1) as usize, t2.len() - b793_break(2) as usize);
    b793_mcx(b, &lanes, &t1[..n1], &dirty);
    b.hmr_to(xl, if b793_break(3) { mb[0] } else { mb[1] });
    b793_mcx(b, &lanes, &t2[..n2], &dirty);
    b.hmr_to(j[3], if b793_break(3) { mb[1] } else { mb[0] });
    j[4]
}

impl GreedyFrog {
    /// R4-RHO: the stall-shot phase owed by the previous inverse slot (if it measured res), on jl = t of this slot.
    /// `skip`: LA lanes freed as hosts (|0>). `g`: a |0> lane for the gate.
    fn r4_pend_apply(&self, b: &mut B, jl: &[QubitId], sx: &[QubitId], skip: &[QubitId], g: QubitId) {
        let Some((mb, gate)) = R4_PEND.with(|p| p.borrow_mut().take()) else { return };
        if r4_break(2) { return; }
        let (o0, o1) = if r4_break(3) { (2, 3) } else { (3, 4) };
        let xt = self.x[W - 1];
        if gate && !r4_break(5) {
            // b793b ACTFOLD=2: finished shots carry LA = 127 (all ones) instead of sX: their stall phase term is !X[W-1] & [LA == 127], a second term of the XOR
            let afl = AF_LANES.with(|c| c.borrow().clone());
            if !afl.is_empty() {
                let mut lb_: Vec<(QubitId, bool)> = vec![(xt, true)];
                lb_.extend(afl.iter().map(|&q| (q, false)));
                if g == NOQ {
                    for (i, &m) in mb.iter().enumerate() {
                        let q = jl[if i == 0 { o0 } else { o1 }];
                        b.push_condition(m);
                        let mut l = lb_.clone();
                        l.push((q, false));
                        phase_and(b, &l);
                        b.pop_condition();
                    }
                } else {
                    and_auto(b, self, &lb_, g);
                    for (i, &m) in mb.iter().enumerate() {
                        let q = jl[if i == 0 { o0 } else { o1 }];
                        b.push_condition(m);
                        b.cz(g, q);
                        b.pop_condition();
                    }
                    erase_and(b, self, g, &lb_);
                }
            }
            // g = !X[W-1] & [u == sX] (LA holds u = LA + sX: a finished shot); phase (-1)^(t_i (1 ^ X ^ g)) per bit
            for (i, &q) in sx.iter().enumerate() {
                b.cx(q, self.la[i]);
            }
            // b793b ACTFOLD: the pair (LA[5], LA[6]) = (1, 1) on finished shots (true bits 0, 0): the literal is l5 == l6 (an active shot's code is never (1, 1))
            let afp = AF_PAIR.with(|c| c.get());
            if let Some((l5, l6)) = afp { b.cx(l5, l6); }
            let mut lits = vec![(xt, true)];
            lits.extend(self.la.iter().filter(|q| **q != NOQ && !skip.contains(q) && afp.map_or(true, |(l5, _)| **q != l5)).map(|&q| (q, true)));
            if g == NOQ {
                // Schaffhuuserzopf part 2: no gate lane: (-1)^(q AND(lits)) as one phase_and per measured bit
                for (i, &m) in mb.iter().enumerate() {
                    let q = jl[if i == 0 { o0 } else { o1 }];
                    b.push_condition(m);
                    b.z(q);
                    b.cz(xt, q);
                    // negative control `p2l` (gate tests only): the phase on (X[W-1], q) alone, LA's literals dropped
                    let mut l = if r14b_break("p2l") || (b793_break(5) && p3_cur_slot() == 188) { lits[..1].to_vec() } else { lits.clone() };
                    l.push((q, false));
                    if !r14b_break("p2p") { phase_and(b, &l); }
                    b.pop_condition();
                }
            } else {
            and_auto(b, self, &lits, g);
            for (i, &m) in mb.iter().enumerate() {
                let q = jl[if i == 0 { o0 } else { o1 }];
                b.push_condition(m);
                b.z(q);
                b.cz(xt, q);
                b.cz(g, q);
                b.pop_condition();
            }
            erase_and(b, self, g, &lits);
            }
            if let Some((l5, l6)) = afp { b.cx(l5, l6); }
            for (i, &q) in sx.iter().enumerate() {
                b.cx(q, self.la[i]);
            }
        } else {
            for (i, &m) in mb.iter().enumerate() {
                let q = jl[if i == 0 { o0 } else { o1 }];
                b.push_condition(m);
                b.z(q);
                b.cz(xt, q);
                b.pop_condition();
            }
        }
    }
}
/// Negative controls for the gate tests only (MJ_BREAK=k, as in retake799's form): 1 drops the step repair, 2 drops
/// the owed stall phase, 3 drops the stall CZ on X[W-1], 4 drops the f clear, 5 wrong J at slot MJ_BREAK_SLOT,
/// 6 drops the stall gate.
fn mj_break() -> String {
    if cfg!(test) { std::env::var("MJ_BREAK").unwrap_or_default().trim().to_string() } else { String::new() }
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

thread_local! {
    /// P2-REBASE: the walk's live-qubit cap for helpers without a GreedyFrog (u64::MAX: no cap known)
    static P2_CAP: std::cell::Cell<u64> = const { std::cell::Cell::new(u64::MAX) };
}
/// P2-REBASE: set the cap the generic helpers (and_into, phase_and) respect; their borrowed lanes are mask::BORROWED.
pub fn p2_set_cap(cap: u64) {
    super::arith::R6_MIX_CAP.with(|c| c.set(if below805(cap) && r3_flag("R6_MIX") { cap } else { 0 }));
    P2_CAP.with(|c| c.set(cap));
}
/// P2-REBASE: lanes left under the generic cap.
/// R3-FIT799 R3F_NOROLL (cap < 573): a rolled ladder pass (ROLL-FWD) whose rolling lanes do not fit in the room
/// runs unrolled (its pool is room-aware); the inverse already takes an empty record as not rolled
fn r3f_roll_ok(b: &B, lanes: usize) -> bool {
    !(below805(P2_CAP.with(|c| c.get())) && r3_flag("R3F_NOROLL") && p2_room(b) < lanes)
}
/// R8-ROOM0 switches (cap < 805 in the walk's units, like R6_*): read once
fn r8_phb() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("R8_PHB"));
    *E && below805(P2_CAP.with(|c| c.get()))
}
fn r8_cc2() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("R8_CC2"));
    *E && super::arith::r8_cc() && below805(P2_CAP.with(|c| c.get()))
}
fn r8_swl(u: &GreedyFrog) -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("R8_SWL"));
    *E && below805(u.cap)
}
thread_local! {
    /// R8_SWL: the swap flag's out lane is a fresh |0> (forward F9)
    static SWL_OUT_FRESH: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
/// R8_SWL: run f with `lanes` (|0>, probed) out of the live count; they are taken back by id after (f frees what it takes)
fn r8_lend<R>(b: &mut B, lanes: &[QubitId], f: impl FnOnce(&mut B) -> R) -> R {
    zero_probe(b, lanes);
    let brk = cfg!(test) && std::env::var("R8_BREAK").map_or(false, |v| v.trim() == "swl");
    for &q in lanes { b.free(q); }
    let r = f(b);
    for &q in lanes { assert!(b.is_free(q), "R8_SWL: lent lane q{} not returned", q.0); b.acquire(q); if brk { b.x(q); } }
    r
}
fn p2_room(b: &B) -> usize {
    P2_CAP.with(|c| c.get()).saturating_sub(b.live) as usize
}

/// out ^= AND of literals (qubit, negated), transient ancillas, n - 1 Toffoli (n >= 1).
pub fn and_into(b: &mut B, lits: &[(QubitId, bool)], out: QubitId) {
    let n = lits.len();
    assert!(n >= 1);
    // P2-REBASE (cap < 813): no room for the ancilla chain: the same AND on borrowed lanes (exact, lanes restored)
    if n >= 3 && p2_room(b) < n - 2 {
        let d = super::mask::borrowed();
        if d.len() >= n - 2 {
            and_dirty(b, lits, out, &d);
            return;
        }
    }
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

// ------------------------------------------------------------------ P2-REBASE: hosted ladder scratch below 813
/// A Clifford map that turns lane q of a 9-lane length register into a constant on every value of a set:
/// v[q] ^= XOR of v[c] (c in ctl) ^ k is |0> there (retake799's RegHost, a2aa080, generalised to several lanes).
struct RegHost {
    q: usize,
    ctl: Vec<usize>,
    k: bool,
}
/// Up to `max` hosts on distinct lanes for the values `vals`; controls never touch a chosen lane.
fn reg_hosts(vals: &[usize], max: usize) -> Vec<RegHost> {
    let mut out: Vec<RegHost> = vec![];
    // R8_LHF: released length bits are neither hosts nor controls
    let hb = r8_hb();
    let m8 = r8_m8();
    let rel = |i: usize| (hb < R8_TOP && i >= hb && i < R8_TOP) || (m8 && i == LB_BITS - 1);
    for q in (0..LB_BITS).rev() {
        if out.len() >= max { break; }
        if rel(q) { continue; }
        let used: Vec<usize> = out.iter().map(|h| h.q).collect();
        let cands: Vec<usize> = (0..LB_BITS).filter(|&c| c != q && !used.contains(&c) && !rel(c)).collect();
        let mut sets: Vec<Vec<usize>> = vec![vec![]];
        for &a in &cands { sets.push(vec![a]); }
        for i in 0..cands.len() { for j in i + 1..cands.len() { sets.push(vec![cands[i], cands[j]]); } }
        for c in sets {
            let f = |v: usize| ((v >> q) & 1) ^ c.iter().fold(0, |a, &k| a ^ ((v >> k) & 1));
            let k0 = f(vals[0]);
            if vals.iter().all(|&v| f(v) == k0) {
                // a later host must not use this lane as a control, nor may this host's controls be re-hosted
                out.push(RegHost { q, ctl: c, k: k0 == 1 });
                break;
            }
        }
    }
    // controls of earlier hosts must not be hosted later: drop any host whose lane is an earlier host's control
    let mut keep: Vec<RegHost> = vec![];
    for h in out {
        if keep.iter().any(|e| e.ctl.contains(&h.q)) { continue; }
        keep.push(h);
    }
    keep
}
thread_local! {
    /// P2-REBASE: (length register, its values on every non-failing shot, extra lanes the pass allocates after the
    /// scratch) for the next ladder-scratch allocation
    static P2_HOSTSPEC: std::cell::RefCell<Option<(Vec<QubitId>, Vec<usize>, usize)>> = const { std::cell::RefCell::new(None) };
    /// P2-REBASE: open hosts (f lane of the Masked, register, hosts, hosted lanes), innermost last
    static P2_HOSTED: std::cell::RefCell<Vec<(QubitId, Vec<QubitId>, Vec<RegHost>, Vec<QubitId>)>> = const { std::cell::RefCell::new(Vec::new()) };
}
/// P2-REBASE: room an inverse slot needs at its sweep to carry its swap flag to the next slot
const P2_SWC_ROOM: usize = 10;
/// P2-REBASE: lanes a cofactor pass allocates after its scratch (x0, rolling lanes)
const P2_COF_EXTRA: usize = 3;
/// P2-REBASE: the next ladder scratch may host lanes on register `v`, whose value on every non-failing shot lies in
/// lo..=hi or is 0 / 1 (finished); `extra` lanes are allocated after the scratch inside the pass.
fn p2_host_spec(v: &[QubitId], lo: usize, hi: usize, extra: usize) {
    let mut vals: Vec<usize> = (lo..=hi.min(511)).collect();
    vals.extend([0, 1]);
    P2_HOSTSPEC.with(|c| *c.borrow_mut() = Some((v.to_vec(), vals, extra)));
}
/// R4-SITES R4_IDLE (cap < 573, act-constant slots): the pass' idle length register (not read by its ladder) is offset
/// in place by -lo (a 9-bit constant add each way) where the scratch would otherwise be short, so its window lo..=hi
/// becomes 0..=hi - lo and its top lanes host the scratch; no finished shots there, so 0 / 1 are not host values.
/// Returns the offset to add back after the scratch is freed. Envelope-based as `p2_host_spec`.
fn r4_idle_spec(b: &mut B, u: &GreedyFrog, w: &Win, v: &[QubitId], lo: usize, hi: usize, need: usize, extra: usize)
                -> Option<usize> {
    let on = below805(u.cap) && w.act_const && lo >= 2 && hi <= 511 && r3_flag("R4_IDLE") && r15_idle_slot();
    if r3_flag("R4_DBG") {
        eprintln!("R4IDLE slot {} sect {} lo {lo} hi {hi} need {need} extra {extra} room {} on {}", p3_cur_slot(),
                  super::builder::i5::SECT.with(|c| c.get()), p2_room(b), on as u8);
    }
    if on {
        let mut vals: Vec<usize> = (lo..=hi).collect();
        vals.extend([0, 1]);
        let room = p2_room(b);
        let h0 = reg_hosts(&vals, need).len();
        let h1 = reg_hosts(&(0..=hi - lo).collect::<Vec<_>>(), need).len();
        if need + extra > room + h0 && h1 > h0 && r15_idle_site(p3_cur_slot(), lo, hi, extra) {
            if r3_flag("R4_DBG") {
                eprintln!("R4FIRE slot {} sect {} lo {lo} hi {hi} need {need} extra {extra} room {room}", p3_cur_slot(),
                          super::builder::i5::SECT.with(|c| c.get()));
            }
            // negative control for the gate tests only: R4_BREAK=idle skips the offset (hosted lanes not constant)
            if !r4s_break("idle") { add_const_sm(b, u, v, lo, true); }
            P2_HOSTSPEC.with(|c| *c.borrow_mut() = Some((v.to_vec(), (0..=hi - lo).collect(), extra)));
            return Some(lo);
        }
    }
    p2_host_spec(v, lo, hi, extra);
    None
}
/// S4 Q796 dev switch R15_IDLE_ONLY=<slot,..>: R4_IDLE only on the listed slots (unset: every slot, the parent)
fn r15_idle_slot() -> bool {
    static E: std::sync::LazyLock<Option<Vec<usize>>> = std::sync::LazyLock::new(|| std::env::var("R15_IDLE_ONLY").ok()
        .map(|v| v.split(',').filter_map(|t| t.trim().parse().ok()).collect()));
    E.as_ref().map_or(true, |l| l.contains(&p3_cur_slot()))
}
/// S4 Q796 R15_IDLE_PARENT: R4_IDLE only at the (slot, lo, hi, extra) sites where the parent Q797 build fires it
/// (the parent's own envelope premises, no new ones); dev switch R15_IDLE_PARENT=<site file> (unset: every site)
fn r15_idle_site(slot: usize, lo: usize, hi: usize, extra: usize) -> bool {
    static E: std::sync::LazyLock<Option<Vec<(usize, usize, usize, usize)>>> = std::sync::LazyLock::new(|| {
        let txt = match std::env::var("R15_IDLE_PARENT") {
            Ok(f) => Some(std::fs::read_to_string(f).expect("R15_IDLE_PARENT file")),
            // R15_IDLE_P=1: the parent's site list, generated from the df9d7d5c build (R4_DBG=1 WALK_STOP, R4FIRE lines)
            Err(_) if r3_flag("R15_IDLE_P") => Some(include_str!("r15_idle_sites.txt").to_string()),
            Err(_) => None,
        };
        txt.map(|t| t.lines()
            .filter_map(|l| { let v: Vec<usize> = l.split_whitespace().filter_map(|t| t.parse().ok()).collect();
                              (v.len() == 4).then(|| (v[0], v[1], v[2], v[3])) }).collect())
    });
    E.as_ref().map_or(true, |l| l.contains(&(slot, lo, hi, extra)))
}
fn r4_idle_close(b: &mut B, u: &GreedyFrog, v: &[QubitId], off: Option<usize>) {
    if let Some(c) = off { if !r4s_break("idle") { add_const_sm(b, u, v, c, false); } }
}
fn r4_need(cv: Option<(usize, usize)>, hi: usize) -> usize {
    match cv { Some((h, _)) => h + 3, None => dec_keep(hi).map_or(LB_BITS + 2, |h| h + 3) }
}
fn p2_host_clear() {
    P2_HOSTSPEC.with(|c| *c.borrow_mut() = None);
}
/// n scratch lanes: hosted lanes first where the cap leaves no room (the rest fresh), in the allocation order of the
/// base (f, t, pre.., c0) so a build with room is unchanged.
fn p2_lanes(b: &mut B, n: usize) -> (Vec<QubitId>, Option<(Vec<QubitId>, Vec<RegHost>, Vec<QubitId>)>) {
    p2_lanes_s(b, n, false)
}
/// `p2_lanes`; with `short` (R10_P2S) one lane fewer (the prefix's last) where the fresh lanes would exceed the cap
fn p2_lanes_s(b: &mut B, n: usize, short: bool) -> (Vec<QubitId>, Option<(Vec<QubitId>, Vec<RegHost>, Vec<QubitId>)>) {
    let spec = P2_HOSTSPEC.with(|c| c.borrow_mut().take());
    let room = p2_room(b);
    let have = room + reg_host_count(&spec, n, room);
    let n = if short && n >= 7 && r10_on("R12_P2S3", have, n - 2) {
        // R14_FWD94 "Vollgasbuebe" L: where even R12_P2S3's form takes fresh lanes above the cap, one lane fewer again
        // (the decoder in mask::RSHORT4T's form, see `p2_masked`)
        if n >= 8 && r14f_ladder(room, (n - 3) - reg_host_count(&spec, n - 3, room)) {
            // H793 "Heieiei" (Vollgasbuebe's second level): where the h - 4 form's fresh lanes still cross the cap, one
            // lane fewer again (decoder bits n-1 .. 5 retained, bit 4 transient on the AND temp, `Dec::xor_ret_tmp_cc5`)
            if n >= 9 && h793_l2(room, (n - 4) - reg_host_count(&spec, n - 4, room)) {
                // B792_P1: one more level (decoder bit 5 transient, bits 4..0 on borrowed lanes) where the h - 5 form's fresh lanes still cross the cap
                if n >= 9 && b792_p1() && (b792_force() || (n - 5) - reg_host_count(&spec, n - 5, room) > room) { n - 6 } else { n - 5 }
            } else { n - 4 }
        } else { n - 3 }
    }
        else if short && r10_on("R10_P2S", have, n) { if r10_on("R10_P2S2", have, n - 1) { n - 2 } else { n - 1 } } else { n };
    if let Some((v, vals, extra)) = spec {
        let deficit = (n + extra).saturating_sub(room);
        if deficit > 0 {
            let hs = reg_hosts(&vals, deficit.min(n));
            if r3_flag("R4_DBG") {
                eprintln!("R4DBG p2_lanes slot {} n {n} extra {extra} room {room} deficit {deficit} hosts {} vals {}..{}",
                          super::builder::i5::SLOT.with(|c| c.get()), hs.len(), vals[0], vals[vals.len() - 3]);
            }
            for h in &hs {
                for &c in &h.ctl { b.cx(v[c], v[h.q]); }
                if h.k { b.x(v[h.q]); }
            }
            let hl: Vec<QubitId> = hs.iter().map(|h| v[h.q]).collect();
            let mut lanes = hl.clone();
            lanes.extend(b.alloc_n(n - hl.len()));
            return (lanes, Some((v, hs, hl)));
        }
    }
    (b.alloc_n(n), None)
}
/// R10_P2S: hosts `p2_lanes_s` would place for `n` lanes at this room
fn reg_host_count(spec: &Option<(Vec<QubitId>, Vec<usize>, usize)>, n: usize, room: usize) -> usize {
    match spec {
        Some((_, vals, extra)) => {
            let deficit = (n + extra).saturating_sub(room);
            if deficit > 0 { reg_hosts(vals, deficit.min(n)).len() } else { 0 }
        }
        None => 0,
    }
}
thread_local! {
    /// R10_P2S: open short-prefix scratches (f lane, RSHORT before), innermost last
    static R10SH: std::cell::RefCell<Vec<(QubitId, bool, bool, bool, bool, bool, bool, bool)>> = const { std::cell::RefCell::new(Vec::new()) };
}
fn p2_masked(b: &mut B, h: usize) -> Masked {
    // R10_P2S (claude-r8): where the hosts and the room leave the scratch one lane short, the decoder keeps a retained
    // prefix one level short (retake799's RSHORT form: bit 0 joins each toggle by a CCX); exact
    let (l, ctx) = p2_lanes_s(b, h + 3, h >= 3);
    let hs = l.len() - 3;
    let m = Masked { f: l[0], t: l[1], gf: l[0], chain: vec![], pre: l[2..2 + hs].to_vec(), c0: l[2 + hs] };
    if let Some((v, hs, hl)) = ctx {
        P2_HOSTED.with(|c| c.borrow_mut().push((m.f, v, hs, hl)));
    }
    if hs < h {
        let rs0 = super::mask::RSHORT.with(|c| c.replace(true));
        let rs20 = super::mask::RSHORT2.with(|c| c.replace(c.get() || hs + 2 == h));
        let rs30 = super::mask::RSHORT3.with(|c| c.replace(c.get() || hs + 3 == h));
        // R14_FWD94 "Vollgasbuebe" L (only `p2_lanes_s`'s R14 level leaves hs + 4 == h): the decoder keeps h - 4
        // retained levels (bits h .. 4) and forms the next level a = o & bit 3 transiently on the ladder's AND temp t
        // (|0> between cells; R9_PREFIX's RSHORT4T prefix shape), and the toggle takes bits 2, 1, 0 on the two literal
        // lanes of a (`Dec::xor_ret_tmp_cc`, R14L set): one lane fewer than RSHORT3 and 6 Toffoli per toggle against its
        // 8; exact (on the base's own envelope where t is a hosted register lane, as its cells)
        let r14 = hs + 4 == h;
        let rs40 = super::mask::RSHORT4T.with(|c| c.replace(c.get() || r14));
        let r14o = super::mask::R14L.with(|c| c.replace(c.get() || r14));
        if r14 { r14f_dbg(b, h, hs); }
        // H793 Heieiei (only `p2_lanes_s`'s H793 level leaves hs + 5 == h)
        let l2 = hs + 5 == h;
        let l2o = super::mask::R14L2.with(|c| c.replace(c.get() || l2));
        if l2 { h793_dbg(b, h, hs); }
        // B792_P1 (only `p2_lanes_s`'s B792 level leaves hs + 6 == h)
        let l3 = hs + 6 == h;
        let l3o = super::mask::R792L3.with(|c| c.replace(c.get() || l3));
        R10SH.with(|c| c.borrow_mut().push((m.f, rs0, rs20, rs30, rs40, r14o, l2o, l3o)));
    }
    m
}
/// R14 fwd94 "Vollgasbuebe" (dev knob `R14_FWD94`; 0 / unset off = the base byte for byte, 1 where the cap leaves no
/// lane for the base's form, 2 always (exactness checks at a cap with room)). Pieces (dev `R14_FWD94_PARTS`, default "L"):
/// L: the masked ladders' scratch (forward top compare F2, value F4 / I10, cofactor F5 / I11, inverse d undo:
///    `p2_masked` via `p2_lanes_s`) one lane under R12_P2S3's form where that form's fresh lanes would cross the cap
///    (knob 2: at every R12_P2S3 site): the decoder prefix keeps h - 4 retained levels, forms the next one on the
///    ladder's AND temp, and toggles on that level's literal lanes (`mask::Dec::xor_ret_tmp_cc`).
fn r14f(part: char) -> u8 {
    static V: std::sync::LazyLock<u8> = std::sync::LazyLock::new(|| std::env::var("R14_FWD94").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0));
    static P: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R14_FWD94_PARTS").unwrap_or_else(|_| "L".into()));
    if P.contains(part) { *V } else { 0 }
}
/// R14_FWD94 L: whether the ladder takes the R14 level, given the room and the fresh lanes R12_P2S3's form would take
fn r14f_ladder(room: usize, fresh3: usize) -> bool {
    match r14f('L') { 2 => true, 1 => fresh3 > room, _ => false }
}
/// H793 "Heieiei" (Q793 Hoppla spike; dev knob `H793_L2`, 0 / unset off = the Q794 tree byte for byte): the masked
/// ladder's h - 5 level where the Vollgasbuebe h - 4 form's fresh lanes still cross the cap. `H793_L2=1`: only in the
/// sections named by `H793_L2_SECT` (comma list, default "i.value,i.cof"); `=2`: every section; `=3`: every R14 site,
/// room or not (exactness checks at a cap with room).
fn h793_l2(room: usize, fresh4: usize) -> bool {
    static V: std::sync::LazyLock<u8> = std::sync::LazyLock::new(|| std::env::var("H793_L2").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0));
    static S: std::sync::LazyLock<Vec<String>> = std::sync::LazyLock::new(|| std::env::var("H793_L2_SECT")
        .unwrap_or_else(|_| "i.value,i.cof".into()).split(',').map(|t| t.trim().to_string()).collect());
    let sect = H793_SECT.with(|c| c.get());
    match *V { 1 => fresh4 > room && S.iter().any(|t| t == sect), 2 => fresh4 > room, 3 => true, _ => false }
}
/// H793 "Spiegelei" (dev knob `H793_SPG`, 0 / unset off): the forward mirror of YTOP-COF on f.cof (see `fwd_slot_next`)
fn h793_spg() -> bool {
    static V: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("H793_SPG").map_or(false, |v| v.trim() == "1"));
    *V
}
/// H793 "Rösti" (dev knob `H793_RST`, 0 / unset off): a_X folded back into X before the un-swap's funnel (see there)
/// b792 P7 (dev knob `B792_P7`, const default off in mod.rs): a_Y folded back into Y around the un-swap's funnel
fn b792_p7() -> bool {
    static V: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_P7").map_or(super::B792_P7, |v| v.trim() == "1"));
    *V
}
/// b792 P6 (dev knob `B792_P6`, const default off in mod.rs): one wide compare for the swap decode on the plain act-constant slots
fn b792_p6() -> bool {
    static V: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_P6").map_or(super::B792_P6, |v| v.trim() == "1"));
    *V
}
/// b792 ACTRE (dev knob `B792_ACTRE`, const default off in mod.rs): !act carried on LA[5] across the rows of the late slots
fn b792_actre() -> bool {
    static V: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("B792_ACTRE").map_or(super::B792_ACTRE, |v| v.trim() == "1"));
    *V
}
fn b792_brk(t: &str) -> bool { cfg!(test) && std::env::var("B792_BREAK").map_or(false, |v| v.trim() == t) }
fn h793_rst() -> bool {
    static V: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("H793_RST").map_or(false, |v| v.trim() == "1"));
    *V
}
/// Spiegelei negative control (dev only): `H793_BRK=spg` frees Y[W-1] without the X (a |1> lane into the pool)
fn h793_spg_brk() -> bool { super::mask::h793_brk("spg") }
fn h793_dbg(b: &B, h: usize, hs: usize) {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("R14F_DBG").is_some());
    if *E {
        eprintln!("H793FIRE L2 slot {} sect {} h {h} pre {hs} live {} room {}", p3_cur_slot(), super::builder::i5::SECT.with(|c| c.get()),
                  b.live, p2_room(b));
    }
}
/// R14_FWD94 dev log (inert unless R14F_DBG is set)
fn r14f_dbg(b: &B, h: usize, hs: usize) {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("R14F_DBG").is_some());
    if *E {
        eprintln!("R14FIRE L slot {} sect {} h {h} pre {hs} live {} room {}", p3_cur_slot(), super::builder::i5::SECT.with(|c| c.get()),
                  b.live, p2_room(b));
    }
}

impl Masked {
    /// The value / cofactor ladders' scratch (mid passes only: no comparator chain with LADDER_NO_CHAIN).
    fn alloc_ladder(b: &mut B) -> Masked {
        if ladder_no_chain() { Masked::alloc_lean(b) } else { Masked::alloc(b) }
    }
    /// `alloc_ladder` with the prefix sized for a DEC_NARROW decoder of window top `hi`.
    fn alloc_ladder_w(b: &mut B, hi: usize) -> Masked {
        match (ladder_no_chain(), dec_keep(hi)) {
            (true, Some(h)) => p2_masked(b, h),
            _ => Masked::alloc_ladder(b),
        }
    }
    fn alloc(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: b.alloc_n(LB_BITS - 1), pre: b.alloc_n(LB_BITS - 1), c0: b.alloc() }
    }
    /// The 9-bit decoder without a comparator chain: its comparators borrow lanes (`ge_const_dirty`, `in_range`).
    fn alloc_lean(b: &mut B) -> Masked {
        p2_masked(b, LB_BITS - 1)
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
        if let Some((rs0, rs20, rs30, rs40, r14o, l2o, l3o)) = R10SH.with(|c| { let mut c = c.borrow_mut(); if c.last().map_or(false, |e| e.0 == self.f) { c.pop().map(|e| (e.1, e.2, e.3, e.4, e.5, e.6, e.7)) } else { None } }) {
            super::mask::R792L3.with(|c| c.set(l3o));
            super::mask::R14L2.with(|c| c.set(l2o));
            super::mask::RSHORT.with(|c| c.set(rs0));
            super::mask::RSHORT2.with(|c| c.set(rs20));
            super::mask::RSHORT3.with(|c| c.set(rs30));
            super::mask::RSHORT4T.with(|c| c.set(rs40));
            super::mask::R14L.with(|c| c.set(r14o));
        }
        let top = P2_HOSTED.with(|c| { let mut c = c.borrow_mut(); if c.last().map_or(false, |e| e.0 == self.f) { c.pop() } else { None } });
        let hl: Vec<QubitId> = top.as_ref().map(|e| e.3.clone()).unwrap_or_default();
        let mut all = vec![self.f, self.t];
        all.extend(&self.chain);
        all.extend(&self.pre);
        all.push(self.c0);
        for q in all {
            if q != NOQ && !hl.contains(&q) { b.free(q); }
        }
        if let Some((_, v, hs, _)) = top {
            for h in hs.iter().rev() {
                if h.k { b.x(v[h.q]); }
                for &c in h.ctl.iter().rev() { b.cx(v[c], v[h.q]); }
            }
        }
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
    // P2-REBASE: below 813 the scratch may sit on LA lanes that are constant over LA's window here (lad.0 ..= lad.1 + 1)
    let rl = if cmpl && roll_value() { if roll_value_masked() { 1 } else { 2 } } else { 0 };
    let cv = r4_cview(u, w, w.lb);
    r4_cv_open(b, u, w, &u.lb, w.lb);
    let off = r4_idle_spec(b, u, w, &u.la, w.lad.0, w.lad.1 + 1, r4_need(cv, w.lb.1), rl);
    let m = r4_alloc_ladder(b, w.lb.1, cv);
    p2_host_clear();
    let (t, s) = value_ladder(u, w);
    // MASKED_WRITE_ALWAYS: a fully masked ladder carries c0 = 0 to the top on every marked a1 = 0 shot
    let top_free = always && (w.a1_const || w.lb.0 <= 1);
    if cmpl && roll_value() && r3f_roll_ok(b, rl) {
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
        r4_idle_close(b, u, &u.la, off);
        r4_cv_close(b, u, w, &u.lb, w.lb);
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
    r4_idle_close(b, u, &u.la, off);
    r4_cv_close(b, u, w, &u.lb, w.lb);
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
    let (v, c) = r4_view(&u.lb, hi, r4_cview(u, w, w.lb));
    Src { lo: 0, hi: hi - lo + 1, a: hi as isize - c, d: -1, pre: m.pre[..(v.len() - 1).min(m.pre.len())].to_vec(), v, late: false }
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
/// R4-SITES R4_CVIEW (cap < 573, act-constant slots): a length register whose window lo..=hi (< 256) shares its bits
/// h..8 (h = bit length of lo ^ hi) decodes on the view v[..h] + marker v[8] with the start value less that common
/// part C (the value pass' a = hi - C, the cofactor pass' a = lo - C): the toggle lanes are the same on every shot in the
/// window, whose bits h..8 equal C's (marked stalls keep v[8]; there are no finished shots). The prefix shrinks from
/// 8 (or bit length of hi) to h lanes, and the unread lanes v[h..8) hold C's bits, so they are freed to the builder as
/// |0> lanes for the pass (X where C has a 1) and taken back after it. Envelope-based exactly like DEC_NARROW's
/// v[..h] view (the window is the parent's per-slot envelope); a shot outside it already fails in the parent.
/// R4_CSUB (with R4_CVIEW): where the window crosses a high power of two (bit length of lo ^ hi >= R4_CSUB_MIN,
/// default 7) and hi - lo is shorter, the register is offset in place by -lo for the pass (a 9-bit constant add each
/// way, `add_const_sm`) so its window becomes 0..=hi - lo: the view and the freed lanes are those of that window
/// (bits h..8 of v - lo are 0; a marked stall reads 256 + v - lo, still marked). Same envelope as R4_CVIEW.
fn r4_cview(u: &GreedyFrog, w: &Win, win: (usize, usize)) -> Option<(usize, usize)> {
    r4_cview3(u, w, win).map(|(h, c, _)| (h, c))
}
fn r4_cview3(u: &GreedyFrog, w: &Win, win: (usize, usize)) -> Option<(usize, usize, bool)> {
    if !(below805(u.cap) && w.act_const && ladder_no_chain() && dec_narrow() && r3_flag("R4_CVIEW")) { return None; }
    let (lo, hi) = win;
    if hi >= 256 || lo > hi { return None; }
    let bl = |x: usize| ((usize::BITS - x.leading_zeros()) as usize).max(2);
    let h = bl(lo ^ hi);
    let smin: usize = std::env::var("R4_CSUB_MIN").ok().and_then(|v| v.parse().ok()).unwrap_or(7);
    if r3_flag("R4_CSUB") && h >= smin && bl(hi - lo) < h {
        return Some((bl(hi - lo), lo, true));
    }
    let c = lo & !((1usize << h) - 1);
    (h < LB_BITS - 1).then_some((h, c, false))
}
fn r8_rel(j: usize) -> bool {
    j >= r8_hb() && j < R8_TOP
}
fn r4_cv_open(b: &mut B, u: &GreedyFrog, w: &Win, v: &[QubitId], win: (usize, usize)) {
    let Some((h, c, sub)) = r4_cview3(u, w, win) else { return };
    if sub { add_const_sm(b, u, v, c, true); }
    for j in (h..LB_BITS - 1).filter(|&j| !r8_rel(j)) {
        if cfg!(test) && std::env::var("R4_BREAK").map_or(false, |x| x.trim() == "cv") && j == h { continue; }
        if !sub && (c >> j) & 1 == 1 { b.x(v[j]); }
        zero_probe(b, &[v[j]]);
        b.free(v[j]);
    }
}
fn r4_cv_close(b: &mut B, u: &GreedyFrog, w: &Win, v: &[QubitId], win: (usize, usize)) {
    let Some((h, c, sub)) = r4_cview3(u, w, win) else { return };
    for j in (h..LB_BITS - 1).filter(|&j| !r8_rel(j)) {
        if cfg!(test) && std::env::var("R4_BREAK").map_or(false, |x| x.trim() == "cv") && j == h { continue; }
        b.acquire(v[j]);
        if !sub && (c >> j) & 1 == 1 { b.x(v[j]); }
    }
    if sub { add_const_sm(b, u, v, c, false); }
}
fn r4_alloc_ladder(b: &mut B, hi: usize, cv: Option<(usize, usize)>) -> Masked {
    match cv {
        Some((h, _)) => p2_masked(b, h),
        None => Masked::alloc_ladder_w(b, hi),
    }
}
fn r4s_break(tag: &str) -> bool {
    cfg!(test) && std::env::var("R4_BREAK").map_or(false, |x| x.trim() == tag)
}
fn r4_view(v: &[QubitId], hi: usize, cv: Option<(usize, usize)>) -> (Vec<QubitId>, isize) {
    match cv {
        // negative control for the gate tests only: R4_BREAK=cva shifts the decoded start value by one
        Some((h, c)) => (v[..h].iter().chain(std::iter::once(&v[LB_BITS - 1])).copied().collect(),
                         c as isize + r4s_break("cva") as isize),
        None => (dec_view(v, hi), 0),
    }
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
    let (v, c) = r4_view(&u.la, hi, r4_cview(u, w, w.lad));
    Src { lo: 0, hi: hi - lo + 1, a: lo as isize - c, d: 1, pre: m.pre[..(v.len() - 1).min(m.pre.len())].to_vec(), v, late: false }
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
        let t: Vec<QubitId> = u.x[W - wc()..top_cmp_hi()].to_vec();
        let s: Vec<QubitId> = u.y[W - wc()..top_cmp_hi()].to_vec();
        let c0 = b.alloc();
        let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
        let pool = pool_for(b, u, t.len(), 0);
        plain_compare(b, &t, &s, c0, &sc, out, gate, &pool);
        b.free_n(&pool);
        b.free(c0);
        return;
    }
    // P2-REBASE: the masked compare's scratch may sit on LA lanes constant over LA's window (lad.0 ..= lad.1 + 1)
    TOPC_SPEC.with(|c| c.set(Some((w.lad.0, w.lad.1 + 1))));
    // R4-SITES R4_TOPC (cap < 573): the DCMP7 view reads LB[0..5), big and LB[8] only; LB[j] for 5 <= j < 8 with
    // 2^j > lb.1 is |0> on every shot (window values and finished 0 / 1; F2's mark touches LB[8] only), so those lanes
    // are freed to the builder for the masked compare's scratch and taken back after it. Envelope-based (the window).
    let tl = if below805(u.cap) && R4_TOPC_ON.with(|c| c.get()) && r3_flag("R4_TOPC") {
        let h = ((usize::BITS - w.lb.1.max(1).leading_zeros()) as usize).max(5);
        (h..LB_BITS - 1).filter(|&j| !(j >= r8_hb() && j < R8_TOP)).collect::<Vec<usize>>()
    } else { vec![] };
    R4_TOPC_LB.with(|c| *c.borrow_mut() = tl);
    R6_LBH.with(|c| c.set(((usize::BITS - w.lb.1.max(1).leading_zeros()) as usize).max(5)));
    top_compare_masked(b, u, out);
    R6_LBH.with(|c| c.set(LB_BITS));
    R4_TOPC_LB.with(|c| c.borrow_mut().clear());
    TOPC_SPEC.with(|c| c.set(None));
}
thread_local! {
    static TOPC_SPEC: std::cell::Cell<Option<(usize, usize)>> = const { std::cell::Cell::new(None) };
    static R4_TOPC_LB: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) };
    /// R4_TOPC: set around the forward's F2 compare only
    static R4_TOPC_ON: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R6_LBV: bit length h of the slot's LB window bound (max 5) around the masked top compare; LB_BITS elsewhere
    static R6_LBH: std::cell::Cell<usize> = const { std::cell::Cell::new(LB_BITS) };
    /// R6-ROOM799 (tests): open erase_mbu condition blocks; zero probes are placed outside them only (the probed
    /// replay splits the op stream at each probe)
    static R6_INCOND: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
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
    if r6dbg() { eprintln!("R6 bls {} room {}", super::builder::i5::SECT.with(|c| c.get()), u.room(b)); }
    if let Some(n) = r6_gec_need(u) {
        if u.room(b) >= n {
            let (v, k1, k2) = r6_lbview(u);
            if v.len() < LB_BITS && R6_INCOND.with(|c| c.get()) == 0 {
                let pl: Vec<QubitId> = (v.len() - 1..LB_BITS - 1).filter(|&j| !r8_rel(j)).map(|j| u.lb[j]).collect();
                zero_probe(b, &pl);
            }
            let chain = b.alloc_n(n);
            super::mask::ge_const_lean(b, &v, k1, big, &chain);
            if !cr_break(3) && k2 < (1isize << v.len()) { super::mask::ge_const_lean(b, &v, k2, big, &chain); }
            b.free_n(&chain);
            return;
        }
    }
    if u.room(b) < LB_BITS - 1 {
        // P2-REBASE (retake799 r803): the two comparisons on borrowed lanes
        // ohMeingott (A794, cap-794 alias fix): they read R6_LBV's view and constants, the same function on the same
        // lanes as R6_GEC's lean chain above (only the scratch differs; R6_LBV's envelope, as there). The full
        // register is wrong here once R8_LHF (h <= hb) has released LB[hb..8): a released id may be re-allocated
        // (as `big` itself: CCX target == control at cap 794, forward slots 167-200), be NOQ (inverse), or be live
        // as another lane (slots 201-202). With an un-narrowed view this is the full register and 257, as before.
        let (v, k1, k2) = r6_lbview(u);
        if v.len() < LB_BITS && R6_INCOND.with(|c| c.get()) == 0 {
            let pl: Vec<QubitId> = (v.len() - 1..LB_BITS - 1).filter(|&j| !r8_rel(j)).map(|j| u.lb[j]).collect();
            zero_probe(b, &pl);
        }
        let old = R8_OLD.with(|c| c.borrow().clone());
        for &q in &v {
            assert!(q != big && q != NOQ && !b.is_free(q) && !old.contains(&q),
                    "ohMeingott: big_lb_set's borrowed-lane compare would read released or aliased LB lane q{} (big q{})", q.0, big.0);
        }
        super::mask::ge_const_dirty(b, &v, k1, big, &u.dirty);
        if !cr_break(3) && k2 < (1isize << v.len()) { super::mask::ge_const_dirty(b, &v, k2, big, &u.dirty); }
        return;
    }
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
    // I5-LANES L5 (DCMP7): the toggle values WC - l are < 32, so [LB == j] = [LB[0..5) == j] & !big & !LB[8] exactly:
    // LB <= WC has bits 5..8 clear; WC < LB < 257 is big; LB >= 257 has bit 8. A 7-literal view, prefix 6 instead of 8.
    let d7 = i5_dcmp7() && wc() < 32;
    let tl: Vec<usize> = if d7 { R4_TOPC_LB.with(|c| c.borrow().clone()) } else { vec![] };
    for &j in &tl {
        if cfg!(test) && std::env::var("R4_BREAK").map_or(false, |x| x.trim() == "topc") { b.x(u.lb[j]); }
        zero_probe(b, &[u.lb[j]]);
        b.free(u.lb[j]);
    }
    if let Some((lo, hi)) = TOPC_SPEC.with(|c| c.get()) { p2_host_spec(&u.la, lo, hi, 0); }
    let m = if d7 { p2_masked(b, 6) } else { Masked::alloc_lean(b) };
    p2_host_clear();
    let view: Vec<QubitId> = if d7 { u.lb[..5].iter().copied().chain([big, u.lb[LB_BITS - 1]]).collect() } else { u.lb.clone() };
    // f starts at `big`: emulate f0 = big by toggling f before the ladder; sources toggle where LB == WC - l (l >= 1)
    b.cx(big, m.f);
    let srcs = [Src { lo: 0, hi: wc(), v: view, a: wc() as isize, d: -1, pre: m.pre.clone(), late: false }];
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
    for &j in &tl {
        b.acquire(u.lb[j]);
        if cfg!(test) && std::env::var("R4_BREAK").map_or(false, |x| x.trim() == "topc") { b.x(u.lb[j]); }
    }
    if r6dbg() { eprintln!("R6 ble {} room {}", super::builder::i5::SECT.with(|c| c.get()), u.room(b)); }
    let r6n = if biglb_split() { r6_gec_need(u) } else { None };
    if let Some(n) = r6n.filter(|&n| u.room(b) + efree() as usize >= n) {
        // R6_GEC: the measured erase on the lean chain (big leaves the live count first under EFREE)
        erase_mbu(b, big, |b| {
            let (v, k1, k2) = r6_lbview(u);
            if v.len() < LB_BITS && R6_INCOND.with(|c| c.get()) == 0 {
                let pl: Vec<QubitId> = (v.len() - 1..LB_BITS - 1).filter(|&j| !r8_rel(j)).map(|j| u.lb[j]).collect();
                zero_probe(b, &pl);
            }
            let chain = b.alloc_n(n);
            super::mask::ge_const_phase_lean(b, &v, k1, &chain);
            if !r6_break("gec") { super::mask::ge_const_phase_lean(b, &v, k2, &chain); }
            b.free_n(&chain);
        });
    } else
    if biglb_split() && u.room(b) < LB_BITS - 1 {
        // P2-REBASE: no room for the measured erase's chain: recompute on borrowed lanes
        big_lb_set(b, u, big);
    } else if biglb_split() {
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
pub(crate) fn and_into_t(b: &mut B, lits: &[(QubitId, bool)], out: QubitId, anc: &[QubitId]) {
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
    // R8_LHF: released bits hb..7 of a length register are |0> (j < 2^hb there)
    let hb = r8_hb();
    let rel = |i: usize| hb < R8_TOP && v.len() == LB_BITS && i >= hb && i < R8_TOP;
    assert!(!(0..LB_BITS).any(|i| rel(i) && (j >> i) & 1 == 1));
    v.iter().enumerate().filter(|&(i, _)| !rel(i)).map(|(i, &q)| (q, (j >> i) & 1 == 0)).collect()
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

/// R10_NI (claude-r8): `add_const` with the carry-in on a lane `c0` that is |0> on every shot (read, restored)
pub fn add_const_on(b: &mut B, v: &[QubitId], k: usize, sub: bool, c0: QubitId) {
    let c = b.alloc_n(v.len());
    for (i, &q) in c.iter().enumerate() {
        if (k >> i) & 1 == 1 {
            b.x(q);
        }
    }
    add_c_on(b, v, &c, false, sub, c0);
    for (i, &q) in c.iter().enumerate() {
        if (k >> i) & 1 == 1 {
            b.x(q);
        }
    }
    b.free_n(&c);
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

/// R6-ROOM799 R6_PTOP (exact): add_pooled whose last carry (into the sum-only top lane, an AND step on a lane with no
/// s bit) is applied to t[n-1] by one Toffoli instead of a fresh lane: same Toffoli count, one lane fewer.
/// None when the plan's last step is not such an AND.
fn r6_ptop_need(t: &[QubitId], s: &[QubitId], c0: Cy) -> Option<usize> {
    let n = t.len();
    if n < 3 || s.len() >= n - 1 { return None; }
    let p = plan_add(t, s, c0);
    matches!(p[n - 2], Step::And { .. }).then(|| plan_lanes(&p) - 1)
}
fn add_pooled_top(b: &mut B, t: &[QubitId], s: &[QubitId], c0: Cy, sub: bool) {
    let n = t.len();
    if sub {
        for &q in t { b.x(q); }
    }
    let mut p = plan_add(t, s, c0);
    let mut g = b.alloc_n(plan_lanes(&p) - 1);
    g.push(QubitId(u64::MAX - 1)); // placeholder for the top carry, never touched
    let cs = plan_carries(&mut p, c0, &g);
    g.pop();
    for i in 0..n - 2 {
        carry_step(b, &p, t, s, &cs, i, true);
    }
    // top lane: t[n-1] ^= c_(n-1) = AND of the last step's literals (negated for an OR)
    let Step::And { a, b: bb, neg_out } = p[n - 2] else { unreachable!() };
    if a.1 { b.x(a.0); }
    if bb.1 { b.x(bb.0); }
    if !r6_break("ptop") { b.ccx(a.0, bb.0, t[n - 1]); }
    if bb.1 { b.x(bb.0); }
    if a.1 { b.x(a.0); }
    if neg_out { b.x(t[n - 1]); }
    // lane n-2 (no s bit): sum = t ^ c_(n-2)
    xor_cy(b, cs[n - 2], t[n - 2]);
    for i in (0..n - 2).rev() {
        carry_step(b, &p, t, s, &cs, i, false);
        match (p[i], s.get(i)) {
            (Step::Maj { .. }, Some(&si)) => b.cx(si, t[i]),
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

/// P2-REBASE (cap < 813; retake799's add_unpadded, a2aa080): t += s + cin (sub: t -= s + cin), len(s) <= len(t), no
/// zero padding: a Cuccaro ladder on the low lanes, its carry into the high lanes by a controlled increment. The carry-in
/// is `c0` (|0>) if given, else a fresh lane, else (room 0) a borrowed lane d whose unknown value the ladder adds too and
/// a controlled increment by d removes afterwards.
fn add_lean(b: &mut B, u: &GreedyFrog, t: &[QubitId], s: &[QubitId], cin: bool, sub: bool, c0: Option<QubitId>) {
    let m = s.len();
    assert!(m >= 1 && m <= t.len());
    let dc = c0.is_none() && u.room(b) == 0;
    let c = match c0 { Some(q) => q, None => if dc { *u.dirty.last().expect("borrowed lanes") } else { b.alloc() } };
    if cin { b.x(c); }
    if sub { for &q in &t[m..] { b.x(q); } }
    let ru = super::arith::up_m(b, &t[..m], s, c, sub);
    b.play(&ru, false);
    if m < t.len() { inc_auto(b, u, s[m - 1], &t[m..]); }
    let rd = super::arith::down_m(b, &t[..m], s, c, super::arith::Dm::Sum, sub);
    b.play(&rd, false);
    if sub { for &q in &t[m..] { b.x(q); } }
    if cin { b.x(c); }
    if dc {
        // the ladder used carry-in d (cin: 1 - d) instead of cin: remove the excess d (cin: add it back)
        let dec = !sub ^ cin;
        let dl = &u.dirty[..u.dirty.len() - 1];
        if dec { for &q in t { b.x(q); } }
        inc_dirty(b, c, t, dl);
        if dec { for &q in t { b.x(q); } }
    } else if c0.is_none() {
        b.free(c);
    }
}

/// t += s + cin (sub: t -= s + cin) for the walk's small registers: pooled while the cap leaves room, else Cuccaro.
fn add_sm(b: &mut B, u: &GreedyFrog, t: &[QubitId], s: &[QubitId], cin: bool, sub: bool) {
    // R8_LHF / R8_IUNSW: a whole length register with released bits adds on its bound view (no carry reaches them:
    // every value stays below 2^hb on the window's shots)
    if r8_hb() < R8_TOP && t.len() == LB_BITS && (t[0] == u.la[0] || t[0] == u.lb[0]) {
        let lv = r8_live(t);
        return add_sm(b, u, &lv, s, cin, sub);
    }
    if small_pooled() && u.room(b) >= pooled_need_add(t, s, Cy::K(cin)) {
        add_pooled(b, t, s, Cy::K(cin), sub);
    } else if small_pooled() && below805(u.cap) && r3_flag("R6_PTOP")
        && r6_ptop_need(t, s, Cy::K(cin)).is_some_and(|n| u.room(b) >= n) {
        add_pooled_top(b, t, s, Cy::K(cin), sub);
    } else if u.room(b) < t.len() - s.len() + 1 {
        // P2-REBASE: no room for the zero padding and the carry lane
        add_lean(b, u, t, s, cin, sub, None);
    } else if s.len() == t.len() || cin {
        add_c(b, t, s, cin, sub);
    } else if i5_split() {
        i5_add_split(b, t, s, sub);
    } else if sub {
        sub_small(b, t, s);
    } else {
        add_small(b, t, s);
    }
}

/// I5-LANES L4 (SPLIT): t += s (sub: t -= s) for len(s) = k < len(t) = n without zero-extending s: a k-lane Cuccaro
/// whose carry out (s[k-1] between the MAJ and UMA passes) increments t's high n - k lanes by a measured-uncompute AND
/// chain (n - k - 2 temporaries, n - k - 1 Toffoli). Subtraction as ~(~t + s). Lanes: c0 + max(0, n - k - 2) instead of
/// n - k pads + c0.
fn i5_add_split(b: &mut B, t: &[QubitId], s: &[QubitId], sub: bool) {
    let (n, k) = (t.len(), s.len());
    assert!(k >= 1 && k < n);
    if sub { for &q in t { b.x(q); } }
    let c0 = b.alloc();
    let ru = super::arith::up_m(b, &t[..k], s, c0, false);
    b.play(&ru, false);
    let c = s[k - 1];
    let h = &t[k..];
    let m = h.len();
    let tmp = b.alloc_n(m.saturating_sub(2));
    // p_i = c & h[0..i) (p_0 = c); temps hold p_1..p_(m-2)
    let p = |i: usize| -> QubitId { if i == 0 { c } else { tmp[i - 1] } };
    for i in 1..m.saturating_sub(1) {
        b.and_c(p(i - 1), h[i - 1], tmp[i - 1]);
    }
    if m == 1 { b.cx(c, h[0]); }
    if cfg!(test) && std::env::var_os("I5_SPLIT_BREAK").is_some() && m >= 3 { b.x(h[m - 1]); }
    if m >= 2 { b.ccx(p(m - 2), h[m - 2], h[m - 1]); }
    for i in (0..m.saturating_sub(1)).rev() {
        b.cx(p(i), h[i]);
        if i >= 1 {
            // p_i = p_(i-1) & h[i-1] (h[i-1] not yet flipped): measured uncompute
            b.and_u(p(i - 1), h[i - 1], tmp[i - 1]);
        }
    }
    b.free_n(&tmp);
    let rd = super::arith::down_m(b, &t[..k], s, c0, super::arith::Dm::Sum, false);
    b.play(&rd, false);
    b.free(c0);
    if sub { for &q in t { b.x(q); } }
}

/// add_c_on on a carry-in lane c0 (|0>, or holding a quantum carry-in when `qcin`).
fn add_on_sm(b: &mut B, u: &GreedyFrog, t: &[QubitId], s: &[QubitId], cin: bool, sub: bool, c0: QubitId, qcin: bool) {
    let cy = if qcin { Cy::Q(c0) } else { Cy::K(cin) };
    if small_pooled() && u.room(b) >= pooled_need_add(t, s, cy) {
        add_pooled(b, t, s, cy, sub);
    } else if !qcin && u.room(b) < t.len() - s.len() {
        // P2-REBASE: no room for the zero padding
        add_lean(b, u, t, s, cin, sub, Some(c0));
    } else {
        add_c_on(b, t, s, cin, sub, c0);
    }
}

fn add_const_sm(b: &mut B, u: &GreedyFrog, v: &[QubitId], k: usize, sub: bool) {
    // R8_LHF: on a length register with released bits the add runs on the bound view v[..hb] ++ v[8], mod 2^(hb + 1);
    // its callers (R4_IDLE / R4_CSUB offsets by the window floor) never carry or borrow across the low hb bits
    if r8_hb() < R8_TOP && v.len() == LB_BITS && (v[0] == u.la[0] || v[0] == u.lb[0]) {
        assert!(k < 1 << r8_hb());
        let lv = r8_live(v);
        return add_const_sm(b, u, &lv, k, sub);
    }
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
    // b793a EO: released high bits (R8_LHF window open) are |0> in both registers: compare on the bound views, as lt_sm does
    if r8_hb() < R8_TOP && a.len() == LB_BITS && bb.len() == LB_BITS && (a[0] == u.la[0] || a[0] == u.lb[0]) {
        let (mut av, mut bv) = (r8_live(a), r8_live(bb));
        if av.last() == bv.last() { av.pop(); bv.pop(); } // R8_M8's shared |0> bit-8 lane
        if b793a_brk("ltview") { av.pop(); bv.pop(); } // negative control: one live bit dropped from the comparison
        return lt_cin_sm(b, u, &av, &bv, cin, out);
    }
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

// ------------------------------------------------------------------ P2-REBASE: renormalisation below the 813 floor
/// GUARD_BITS[i]: the bits of LA[0..3) that are 0 in i; given i <= LA < 8, [LA == i] is their zero test (retake799's
/// Marchsteiversetzer guard, a2aa080).
const GUARD_BITS: [&[usize]; 7] = [&[], &[1, 2], &[0, 2], &[2], &[0, 1], &[1], &[0]];
/// Lanes the base renormalisation's LA gate and its AND lane take on top of the 7 prefixes.
fn gate_lanes(gate: GateSpec) -> usize {
    match gate {
        None => 0,
        Some((_, hb, gmin)) => {
            let need = gate_need(gmin, &[1, 2, 3, 4, 5, 6]);
            let any = |is: &[usize]| is.iter().any(|&i| need[i]);
            let n_hi = hb.saturating_sub(3);
            n_hi.saturating_sub(1) + (any(&[1, 2, 3, 4, 5, 6]) && n_hi > 0) as usize + need[1] as usize
                + any(&[2, 6]) as usize + need[2] as usize + (any(&[4, 5, 6]) && n_hi > 0) as usize
                + any(&[4, 5]) as usize + need[4] as usize + need[6] as usize + 1
        }
    }
}
/// The guard literals of prefix i: prev & z_i (z_i already flipped onto q) & [LA == i] (LA >= i given).
fn guard_lits(prev: Option<QubitId>, q: QubitId, la: &[QubitId], hb: usize, i: usize) -> Vec<(QubitId, bool)> {
    let mut l: Vec<(QubitId, bool)> = prev.map(|c| vec![(c, false)]).unwrap_or_default();
    l.push((q, false));
    l.extend((3..hb).map(|k| (la[k], true)));
    l.extend(GUARD_BITS[i].iter().map(|&k| (la[k], true)));
    l
}
/// The prefixes p'_i = p'_(i-1) & z_i & [LA > i] (i >= gmin; plain below) in the given lanes (len 6 or 7): the guard
/// term p'_(i-1) & z_i & [LA == i] is XORed into the plain AND on borrowed lanes (no lane beyond the prefixes).
fn prefix_lean(b: &mut B, x: &[QubitId], act: Option<QubitId>, p: &[QubitId], gate: GateSpec, undo: bool) {
    let d = super::mask::borrowed();
    let is: Vec<usize> = if undo { (0..p.len()).rev().collect() } else { (0..p.len()).collect() };
    for i in is {
        let q = x[W - 1 - i];
        b.x(q);
        let prev = if i == 0 { act } else { Some(p[i - 1]) };
        let guard = |b: &mut B| {
            if let Some((la, hb, gmin)) = gate {
                if i >= gmin && i >= 1 {
                    and_dirty(b, &guard_lits(prev, q, la, hb, i), p[i], &d);
                }
            }
        };
        if undo { guard(b); }
        match prev {
            Some(c) => if undo { b.and_u(c, q, p[i]); } else { b.and_c(c, q, p[i]); },
            None => b.cx(q, p[i]),
        }
        if !undo { guard(b); }
        b.x(q);
    }
}
/// renorm_top where the cap leaves fewer than 7 + gate lanes: gated prefixes in place (guards on borrowed lanes); with
/// 6 lanes the seventh prefix only feeds r[0] (one Toffoli and its guard straight into r[0]).
fn renorm_top_lean(b: &mut B, x: &[QubitId], act: Option<QubitId>, r: &[QubitId], gate: GateSpec, n: usize) {
    assert!(n == 6 || n == 7);
    let p = b.alloc_n(n);
    prefix_lean(b, x, act, &p, gate, false);
    if n == 6 {
        let q = x[W - 7];
        b.x(q);
        b.ccx(p[5], q, r[0]);
        if let Some((la, hb, gmin)) = gate {
            if 6 >= gmin {
                let d = super::mask::borrowed();
                and_dirty(b, &guard_lits(Some(p[5]), q, la, hb, 6), r[0], &d);
            }
        }
        b.x(q);
    }
    for i in 0..3 { for &j in SHIFT_PREFIXES[i] { if j < n { b.cx(p[j], r[i]); } } }
    prefix_lean(b, x, act, &p, gate, true);
    b.free_n(&p);
    rotate_three(b, x, r, false, true);
}


// ------------------------------------------------------------------ I5-LANES L2: counter-form rho (RCNT)
fn i5_rcnt() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| i5_flag("I5_RCNT"));
    *E
}
type L5 = (QubitId, bool);
/// out ^= AND(lits) (out |0> when 2+ literals), chain temps from `tmp`, measured uncompute of the chain.
fn i5_and(b: &mut B, lits: &[L5], out: QubitId, tmp: &[QubitId]) {
    let n = lits.len();
    assert!(n >= 1 && tmp.len() + 2 >= n, "I5 and: {n} literals, {} temps", tmp.len());
    for &(q, ng) in lits { if ng { b.x(q); } }
    if n == 1 {
        b.cx(lits[0].0, out);
    } else {
        let mut prev = lits[0].0;
        for k in 1..n - 1 {
            b.and_c(prev, lits[k].0, tmp[k - 1]);
            prev = tmp[k - 1];
        }
        b.and_c(prev, lits[n - 1].0, out);
        for k in (1..n - 1).rev() {
            let c = if k == 1 { lits[0].0 } else { tmp[k - 2] };
            b.and_u(c, lits[k].0, tmp[k - 1]);
        }
    }
    for &(q, ng) in lits { if ng { b.x(q); } }
}
/// out ^= AND(lits) when out == AND(lits): measured uncompute (the chain is recomputed).
fn i5_unand(b: &mut B, lits: &[L5], out: QubitId, tmp: &[QubitId]) {
    let n = lits.len();
    assert!(n >= 1 && tmp.len() + 2 >= n);
    for &(q, ng) in lits { if ng { b.x(q); } }
    if n == 1 {
        b.cx(lits[0].0, out);
    } else {
        let mut prev = lits[0].0;
        for k in 1..n - 1 {
            b.and_c(prev, lits[k].0, tmp[k - 1]);
            prev = tmp[k - 1];
        }
        b.and_u(prev, lits[n - 1].0, out);
        for k in (1..n - 1).rev() {
            let c = if k == 1 { lits[0].0 } else { tmp[k - 2] };
            b.and_u(c, lits[k].0, tmp[k - 1]);
        }
    }
    for &(q, ng) in lits { if ng { b.x(q); } }
}
/// [r == v] as literals, valid on r <= v.
fn i5_req(r: &[QubitId], v: usize) -> Vec<L5> {
    match v {
        0 => vec![],
        1 => vec![(r[0], false)],
        2 => vec![(r[1], false)],
        3 => vec![(r[0], false), (r[1], false)],
        4 => vec![(r[2], false)],
        5 => vec![(r[2], false), (r[0], false)],
        6 => vec![(r[2], false), (r[1], false)],
        7 => vec![(r[2], false), (r[1], false), (r[0], false)],
        _ => unreachable!(),
    }
}
/// The sub-terms and literals of E_s = [LA < s] = nh & [L < s] (L = LA[0..3]); sub-terms go to ta, tb.
/// Returns (sub-term ANDs in order: (lits, target)), main literals.
fn i5_es(la: &[QubitId], nh: Option<L5>, s: usize, ta: QubitId, tb: QubitId) -> (Vec<(Vec<L5>, QubitId)>, Vec<L5>) {
    let (l0, l1, l2) = (la[0], la[1], la[2]);
    let mut subs = vec![];
    let mut m: Vec<L5> = nh.into_iter().collect();
    match s {
        1 => m.extend([(l2, true), (l1, true), (l0, true)]),
        2 => m.extend([(l2, true), (l1, true)]),
        3 => { subs.push((vec![(l1, false), (l0, false)], ta)); m.extend([(l2, true), (ta, true)]); }
        4 => m.push((l2, true)),
        5 => {
            subs.push((vec![(l1, true), (l0, true)], ta));
            subs.push((vec![(l2, false), (ta, true)], tb));
            m.push((tb, true));
        }
        6 => { subs.push((vec![(l2, false), (l1, false)], ta)); m.push((ta, true)); }
        7 => {
            subs.push((vec![(l2, false), (l1, false)], ta));
            subs.push((vec![(ta, false), (l0, false)], tb));
            m.push((tb, true));
        }
        _ => unreachable!(),
    }
    (subs, m)
}
/// I5-LANES L2 (RCNT): rho = min(lz, 7, LA) into r (|0> on entry) as a 3-bit counter: step s (1..7) increments r from
/// s-1 to s iff r == s-1 (two literals at most, given r <= s-1), the top lane X[W-s] is 0 and (gated steps, s-1 >= gmin)
/// [LA >= s]; act gates step 1 only. Every temporary returns to |0> inside the recording, so the recording maps
/// (x, LA, act, r = 0) to r = rho exactly and its inverse erases r. Lanes: the returned pool (NH, E, T, 2+ chain temps).
fn i5_rho_counter(b: &mut B, x: &[QubitId], act: Option<QubitId>, r: &[QubitId], gate: GateSpec) -> (Vec<super::builder::G>, Vec<QubitId>) {
    let (rec, lanes, _) = i5_rho_counter_x(b, x, act, r, gate, None);
    (rec, lanes)
}
/// R9 rowtmp (dev knob `R9_ROWTMP`, off by default; "1" = every piece, else the letters a / b / c it contains).
/// a: an ungated counter's chains need one temporary, not two (its ANDs have at most 3 literals).
/// c: act elision on the inverse slot (see `inv_slot_c`): from the decode to the un-renormalisation the act lane is
///    released, act = a1 | (rho != 0) being a function of the decoded a1 and rho; the inverse counter re-forms it on
///    its own lane t (|0> between its steps) right before step 1, the only step that reads act.
/// b: the last slot's Y[W-1] (= 1 on every shot until the rows) is released across the term prep and I6.
fn r9_rt(p: char) -> bool {
    static E: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R9_ROWTMP").unwrap_or_default());
    let v = E.trim();
    v == "1" || (v != "0" && v.contains(p))
}
/// R14 misc94 "DonRwetter" (dev knob `R14_MISC94`, off by default = the parent byte for byte; "1" = every piece, else
/// the letters it contains). Each piece is keyed on structure (slot kind, path), never on the room, so it fires at the
/// same slots at every cap:
/// s: the inverse I5 swap-flag erase (SWF-LEX, phase only) takes cmp, core and nz just in time and frees each after its
///    own erase (the parent takes lt, eq, cmp, nz up front and frees lt / eq unused): 3 fixed lanes at its widest, not 4.
/// d: i.dundo (I12-I14): the act lane leaves across the d erase's top compare (erased on [LA[..ln] == 0], the parent's
///    I15 predicate on the same LA, rebuilt after d is released), on the slots of `m94_dundo_slot`.
/// u: the inverse un-renormalisation's rho counter (i.unrenorm) is recorded lean: one clean temporary fewer, E_s's
///    second sub-term and chain on the counter lane t (|0> there), and the widest step AND (4 literals gated, 3
///    ungated) on borrowed lanes for its missing temporary (`m94_and`). Same map (x, LA, act, r = 0) -> r = rho.
/// r: the same lean counter in the forward renormalisation (f.renorm; in "1" by the coordinator's decision, 11 Nov).
/// p: the term slot (255) forms I1's done flag after I6 releases LB's lanes 5.. instead of at I1: its lane is absent from
///    the term prep (X funnel, a_Y formed without act) and I6's kt; same function and phase repair on the same state.
/// y: R10_RBY's re-bind of Y[W-1] after the undo rows is deferred to the I10 value ladder, its next reader (the lane
///    is absent from the rest of i.rows_rev, i.denorm and i.unrenorm on those slots).
/// x (x2): on inverse slots 40-142 the forward rows run unrolled and the undo rows fold their X[0] cell by hand (its
///    source is the constant 1), so R10_X0 needs one pool lane, not two: the M1BORROW loan over the cap (:8193) goes.
const M94_ALL: &str = "sdupyxr";
fn r14m(p: char) -> bool {
    static E: std::sync::LazyLock<String> = std::sync::LazyLock::new(|| std::env::var("R14_MISC94").unwrap_or_default());
    let v = E.trim();
    (v == "1" && M94_ALL.contains(p)) || (v != "0" && v != "1" && v.contains(p))
}
/// R14 misc94 negative controls (dev only, inert unless set; read in release builds so the fixed-input A/B can run them,
/// the official environment is empty): `R14_M94_BREAK=<tag>`.
fn r14m_break(tag: &str) -> bool {
    std::env::var("R14_M94_BREAK").map_or(false, |v| v.trim() == tag)
}
/// R9 rowtmp negative controls (dev only, inert unless set; read in release builds too so the fasteval A/B can run
/// them, the official build's environment is empty): R9_RT_BREAK=a (the single temporary is t itself),
/// c1 (act released without its erase), c2 (the denorm's sY erase drops the act term), c3 (the counter's re-form of act
/// before step 1 is dropped)
/// B792_LT5 (worker B792-SL, from B792-SX's patch): out ^= [rest all zero] & [a < sX] with the AND taken inside the compare's window: the Cuccaro ladder
/// of the compare (a complemented + sX) leaves the carry out on sX[top]; the AND reads it (as sX[top] == 0 <=> a < sX) with the high-bit literals, then the
/// ladder is undone. One carry lane c0, no flag lane, one compare instead of two. Exact on every 5-bit a, 5-bit sX and every value of the other literals
/// (exhaustively tested: tests::lt5_fold_exhaustive).
fn b792_lt5_fold(b: &mut B, a5: &[QubitId], lits0: &[(QubitId, bool)], sx: &[QubitId], target: QubitId,
                 andf: &mut dyn FnMut(&mut B, &[(QubitId, bool)], QubitId)) {
    let c0 = b.alloc();
    let ru = super::arith::up(b, a5, sx, c0);
    b.play(&ru, false);
    let mut lits = lits0.to_vec();
    lits.push((sx[a5.len() - 1], false));
    andf(b, &lits, target);
    b.play(&ru, true);
    b.free(c0);
}
fn b792_lt5() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| super::B792_LT5 || r3_flag("B792_LT5")); *E }
fn b792_p5() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| r3_flag("B792_P5")); *E }
fn b792_break(tag: &str) -> bool {
    std::env::var("B792_BREAK").map_or(false, |v| v.trim() == tag)
}
fn r9_rt_break(tag: &str) -> bool {
    std::env::var("R9_RT_BREAK").map_or(false, |v| v.trim() == tag)
}
/// R9 rowtmp P2N (dev switch R9_RT_P2N=1, off by default): while a lane is released, the P2 cap moves with `self.cap`
/// too (piece b then lowers `self.cap` as well), so every room-driven form is the parent's. Off: only `self.room`-driven
/// choices are pinned (piece c); `p2_room`-driven forms (and_into / phase_and chains, FUNNEL-THERMO depth, ...) may take
/// the freed lane, never above P2_CAP (the slot cap), each such form exact by its own construction.
fn r9_p2n() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("R9_RT_P2N").map_or(false, |v| v.trim() == "1"));
    *E
}
fn r9_p2_shift(up: bool) {
    if !r9_p2n() { return; }
    let c = P2_CAP.with(|c| c.get());
    p2_set_cap(if up { c.saturating_add(1) } else { c - 1 });
}
/// `i5_rho_counter`; with `el` = Some(a1) (R9 rowtmp c, inverse use only, act None): step 1 reads act from the lane t,
/// which the recording turns from act into |0> right after step 1 (t ^= a1 | r0: after step 1 r0 = [rho >= 1], and
/// act = a1 | [rho >= 1] on every shot), so the inverse re-forms act on t before its step 1 and leaves it there.
/// Returns (recording, lanes, t).
/// b792 P2: the ungated rho counter on borrowed dirty lanes only (restored, any state). Step s (1..7) maps r = s-1 -> s iff
/// the top lane X[W-s] is 0 (step 1: and act), on the promise r <= s-1 (the parent's promise), by gates on r alone:
/// s=1 r0 ^= z act; s=2 controlled swap (r0, r1); s=3 r0 ^= r1 z; s=4 r2 ^= r0 r1 z then r2 clears r0, r1; s=5 r0 ^= r2 z;
/// s=6 controlled swap (r0, r1) on r2 z; s=7 r0 ^= r2 r1 z. Same map (x, LA, act, r = 0) -> r = rho as the parent's counter.
fn i5_rho_counter_p2(b: &mut B, x: &[QubitId], act: Option<QubitId>, r: &[QubitId], el: Option<QubitId>, t: Option<QubitId>) -> Vec<super::builder::G> {
    let dl0 = super::mask::borrowed();
    let brk = b792_break("p2");
    let xand = |b: &mut B, lits: &[L5], out: QubitId| {
        let dl: Vec<QubitId> = dl0.iter().copied().filter(|q| *q != out && !lits.iter().any(|l| l.0 == *q) && !r.contains(q)).collect();
        assert!(dl.len() + 2 >= lits.len(), "b792 P2: {} literals, {} borrowed lanes", lits.len(), dl.len());
        if lits.len() == 1 {
            if lits[0].1 { b.x(lits[0].0); }
            b.cx(lits[0].0, out);
            if lits[0].1 { b.x(lits[0].0); }
        } else {
            super::arith::and_dirty(b, lits, out, &dl);
        }
    };
    b.begin();
    for s in 1..=7usize {
        let z = (x[W - s], true);
        match s {
            1 => {
                let mut l = vec![z];
                if el.is_some() { l.push((t.unwrap(), false)); } else if let Some(a) = act { l.push((a, false)); }
                xand(b, &l, r[0]);
                if let Some(a1) = el {
                    // R9 rowtmp c: t ^= a1 | r0 (= act here), as in the parent
                    let t = t.unwrap();
                    b.x(a1); b.x(r[0]); b.ccx(a1, r[0], t); b.x(a1); b.x(r[0]); b.x(t);
                }
            }
            2 => { b.cx(r[0], r[1]); xand(b, &[(r[1], false), z], r[0]); b.cx(r[0], r[1]); }
            3 => xand(b, &[(r[1], false), z], r[0]),
            4 => { xand(b, &[(r[0], false), (r[1], false), z], r[2]); b.cx(r[2], r[0]); if !brk { b.cx(r[2], r[1]); } }
            5 => xand(b, &[(r[2], false), z], r[0]),
            6 => { b.cx(r[0], r[1]); xand(b, &[(r[2], false), (r[1], false), z], r[0]); b.cx(r[0], r[1]); }
            _ => xand(b, &[(r[2], false), (r[1], false), z], r[0]),
        }
    }
    b.end()
}
fn i5_rho_counter_x(b: &mut B, x: &[QubitId], act: Option<QubitId>, r: &[QubitId], gate: GateSpec, el: Option<QubitId>)
                    -> (Vec<super::builder::G>, Vec<QubitId>, QubitId) {
    assert!(el.is_none() || act.is_none(), "R9 rowtmp: act is re-formed on t");
    let (gmin, hb, la) = match gate { Some((la, hb, gmin)) => (gmin, hb, Some(la)), None => (7, 3, None) };
    let brk = if cfg!(test) { std::env::var("I5_RCNT_BREAK").ok().and_then(|v| v.trim().parse::<u32>().ok()).unwrap_or(0) } else { 0 };
    let gated = la.is_some() && gmin < 7 && brk != 2;
    let nh_lits: Vec<L5> = match la { Some(la) if gated => (3..hb).map(|i| (la[i], true)).collect(), _ => vec![] };
    // R9 rowtmp a: ungated, every AND has <= 3 literals ([r == s-1] <= 2, the top lane, act at step 1 only): 1 temporary
    // b792 P2 (B792_P2): ungated counter without any clean lane (no tmp chain lane, no t): see `i5_rho_counter_p2`
    if !gated && r3_flag("B792_P2") && !super::mask::borrowed().is_empty() {
        // R9 rowtmp c (el): t carries act into step 1 and is |0> after it, as in the parent; otherwise no t at all
        let mut lanes = vec![];
        let t = if el.is_some() {
            Some(match B793_THOST.with(|c| c.take()) { Some(h) => h, None => { let q = b.alloc(); lanes.push(q); q } })
        } else { None };
        let rec = i5_rho_counter_p2(b, x, act, r, el, t);
        return (rec, lanes, t.unwrap_or(NOQ));
    }
    let ntmp = if !gated && r9_rt('a') { 1 } else { 2usize.max(nh_lits.len().saturating_sub(2)) };
    // R14 misc94 "DonRwetter" u / r (lean): one clean temporary fewer (see `m94_and`)
    // the lean form is taken on the counters that hold the most lanes: the gated form with its NH lane (5 lanes) and
    // the last inverse slot 0's ungated form (where the rows' masked RowTmp lanes are still live); structural keys only
    let lean = M94_LEAN.with(|c| c.get()) && (nh_lits.len() >= 2 || (!gated && p3_cur_slot() == 0));
    // the lean form's E_s chain on t needs every gated step to be s >= 2 (t |0> there); gate_spec gives gmin >= 1
    assert!(!lean || !gated || gmin >= 1, "R14 misc94 u: a gated step 1 would chain through t");
    if std::env::var_os("M94_DBG").is_some() {
        eprintln!("M94CNT slot {} sect {} gated {} gmin {gmin} hb {hb} nh {} ntmp {ntmp} el {} lean {}", p3_cur_slot(),
                  super::builder::i5::SECT.with(|c| c.get()), gated as u8, nh_lits.len(), el.is_some() as u8, lean as u8);
    }
    let mut lanes = vec![];
    let tmp = b.alloc_n(if lean { ntmp - 1 } else { ntmp });
    lanes.extend(&tmp);
    let t = match B793_THOST.with(|c| c.take()) { Some(h) => h, None => { let q = b.alloc(); lanes.push(q); q } };
    // negative control (R9 rowtmp a): the single temporary aliases t (the 3-literal chains into t then break)
    let tmp = if ntmp == 1 && r9_rt_break("a") { vec![t] } else { tmp };
    // lean: t is |0> wherever a gated step's E_s is formed or erased (only steps s >= 2 >= gmin + 1 are gated, and t is
    // |0> between steps 2..7 in both the plain and the R9 rowtmp c form), so E_s's sub-terms and chain may use it; the
    // NH chain at the recording's start only where t is not the act literal (el None)
    let etmp: Vec<QubitId> = if lean { tmp.iter().copied().chain([t]).collect() } else { tmp.clone() };
    let e = if gated { let q = b.alloc(); lanes.push(q); Some(q) } else { None };
    // b792 P3 (B792_P3): no stored NH lane; the 2+ NH literals join E_s's AND directly (m94_and: clean temporaries, then borrowed dirty lanes)
    let p3 = nh_lits.len() >= 2 && r3_flag("B792_P3");
    let nhq = if nh_lits.len() >= 2 && !p3 { let q = b.alloc(); lanes.push(q); Some(q) } else { None };
    let nh: Option<L5> = match (nh_lits.len(), nhq) { (0, _) => None, (1, _) => Some(nh_lits[0]), (_, Some(q)) => Some((q, false)), _ if p3 => None, _ => unreachable!() };
    b.begin();
    if let Some(q) = nhq { if lean { m94_and(b, &nh_lits, q, if el.is_none() { &etmp } else { &tmp }, true); } else { i5_and(b, &nh_lits, q, &tmp); } }
    for s in 1..=7usize {
        let z = (x[W - s], true);
        let g = gated && s - 1 >= gmin;
        let mut lits = i5_req(r, s - 1);
        lits.push(z);
        if s == 1 {
            if el.is_some() { lits.push((t, false)); } else if let Some(a) = act { lits.push((a, false)); }
        }
        let es = if g { Some(i5_es(la.unwrap(), nh, s, etmp[0], etmp[1])) } else { None };
        let es = es.map(|(subs, mut m)| { if p3 { let k = nh_lits.len() - b792_break("p3") as usize; m.splice(0..0, nh_lits[..k].iter().copied()); } (subs, m) });
        if let Some((subs, m)) = &es {
            for (sl, q) in subs { i5_and(b, sl, *q, &[]); }
            let used: Vec<QubitId> = subs.iter().map(|x| x.1).collect();
            let free_t: Vec<QubitId> = etmp.iter().copied().filter(|q| !used.contains(q)).collect();
            if lean || p3 { m94_and(b, m, e.unwrap(), &free_t, true); } else { i5_and(b, m, e.unwrap(), &free_t); }
            for (sl, q) in subs.iter().rev() { i5_unand(b, sl, *q, &[]); }
            lits.push((e.unwrap(), true));
        }
        if s == 1 {
            if lean { m94_and(b, &lits, r[0], &tmp, true); } else { i5_and(b, &lits, r[0], &tmp); }
        } else {
            if lean { m94_and(b, &lits, t, &tmp, true); } else { i5_and(b, &lits, t, &tmp); }
            let flips = if brk == 1 && s == 4 { 3 } else { (s - 1) ^ s };
            for k in 0..3 { if flips >> k & 1 == 1 { b.cx(t, r[k]); } }
            if lean { m94_and(b, &i5_req(r, s), t, &tmp, false); } else { i5_unand(b, &i5_req(r, s), t, &tmp); }
        }
        if let Some((subs, m)) = &es {
            for (sl, q) in subs { i5_and(b, sl, *q, &[]); }
            let used: Vec<QubitId> = subs.iter().map(|x| x.1).collect();
            let free_t: Vec<QubitId> = etmp.iter().copied().filter(|q| !used.contains(q)).collect();
            if lean || p3 { m94_and(b, m, e.unwrap(), &free_t, false); } else { i5_unand(b, m, e.unwrap(), &free_t); }
            for (sl, q) in subs.iter().rev() { i5_unand(b, sl, *q, &[]); }
        }
        if s == 1 {
            if let Some(a1) = el {
                // R9 rowtmp c: t ^= a1 | r0 (= act here): t is |0> for steps 2..7; the inverse re-forms act on t
                if !r9_rt_break("c3") {
                    b.x(a1);
                    b.x(r[0]);
                    b.ccx(a1, r[0], t);
                    b.x(a1);
                    b.x(r[0]);
                    b.x(t);
                }
            }
        }
    }
    if let Some(q) = nhq { if lean { m94_and(b, &nh_lits, q, &etmp, false); } else { i5_unand(b, &nh_lits, q, &tmp); } }
    (b.end(), lanes, t)
}
thread_local! {
    /// R14 misc94 x2: the undo rows being recorded fold their X[0] cell (set by the undo rows' caller)
    static M94X: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R14 misc94 x2: the forward rows being emitted are not ROW-Y rolled (set by the forward rows' caller)
    static M94NR: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
/// R14 misc94 x2 slot set (coordinator decision 09:16): the inverse slots 40-142 (the i.rows_rev band where the cap-794
/// undo rows' M1BORROW loan crossed the cap). A fixed slot range: the same slots at every cap.
fn m94x_slot(w: &Win) -> bool {
    r14m('x') && ((40..=142).contains(&w.slot) || (r3_flag("B793_X2EXT") && (143..=187).contains(&w.slot)) || (r3_flag("B793_X2FX") && (188..=202).contains(&w.slot)))
}
thread_local! {
    /// R14 misc94 u / r: the rho counter being recorded takes the lean form (set by `m94_lean` around the call)
    static M94_LEAN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
/// R14 misc94 u / r: run `f` (a rho-counter recording) with the lean form on where `on`.
fn m94_lean<T>(on: bool, f: impl FnOnce() -> T) -> T {
    let old = M94_LEAN.with(|c| c.replace(on));
    let r = f();
    M94_LEAN.with(|c| c.set(old));
    r
}
/// R14 misc94 "DonRwetter" u / r: the lean counter's AND. With enough clean temporaries (|0>, restored) for the chain it
/// is the parent's `i5_and` (out |0> on entry, `fresh`) or `i5_unand` (out == AND on entry, measured uncompute), gate for
/// gate. Otherwise out ^= AND(lits) as an XOR (valid for both, so its inverse play is itself): the first r + 1 literals
/// on the r clean temporaries by a measured-uncompute chain, the remaining n - r on borrowed lanes in any state
/// (`and_dirty`, Barenco, restored): r + 4 (n - r - 2) Toffoli. Every borrowed lane it takes is asserted distinct from
/// the literals, the target and the temporaries (the cap-794 alias blocker was a stale borrowed list).
fn m94_and(b: &mut B, lits: &[L5], out: QubitId, tmp: &[QubitId], fresh: bool) {
    let n = lits.len();
    if tmp.len() + 2 >= n {
        if fresh { i5_and(b, lits, out, tmp) } else { i5_unand(b, lits, out, tmp) }
        return;
    }
    let r = tmp.len();
    let dl = super::mask::borrowed();
    let need = n - r - 2 + (r == 0) as usize * 0;
    assert!(dl.len() >= need, "m94_and: {n} literals, {r} temps, {} borrowed lanes", dl.len());
    for q in &dl[..need] {
        assert!(*q != out && !lits.iter().any(|l| l.0 == *q) && !tmp.contains(q), "m94_and: borrowed lane q{} in use", q.0);
    }
    // negative control (dev only): the borrowed-lane form drops its last literal
    let lits_b: Vec<L5> = if r14m_break("u") { lits[..n - 1].to_vec() } else { lits.to_vec() };
    let lits = &lits_b[..];
    if r == 0 {
        super::arith::and_dirty(b, lits, out, &dl);
        return;
    }
    let n = lits.len();
    for &(q, ng) in &lits[..r + 1] { if ng { b.x(q); } }
    b.and_c(lits[0].0, lits[1].0, tmp[0]);
    for i in 2..=r { b.and_c(tmp[i - 2], lits[i].0, tmp[i - 1]); }
    let mut rest: Vec<L5> = vec![(tmp[r - 1], false)];
    rest.extend_from_slice(&lits[r + 1..n]);
    super::arith::and_dirty(b, &rest, out, &dl);
    for i in (2..=r).rev() { b.and_u(tmp[i - 2], lits[i].0, tmp[i - 1]); }
    b.and_u(lits[0].0, lits[1].0, tmp[0]);
    for &(q, ng) in &lits[..r + 1] { if ng { b.x(q); } }
}

fn renorm_top(b: &mut B, x: &[QubitId], act: Option<QubitId>, r: &[QubitId], gate: GateSpec) {
    if i5_rcnt() {
        // b793b UNHOST (F2): on the forward slots 189-202 the counter's temporary t runs on LA[8] (a bound |0> lane at the renorm: plain
        // LA <= 255, bit 8 is written only by the F2 / F4 / F5 marks, none of which is live here; the LA gate reads bits below 8)
        if b793_unhost() && (189..=202).contains(&p3_cur_slot()) {
            if let Some((la, hb, _)) = gate {
                if hb <= LB_BITS - 1 && la.len() == LB_BITS && la[LB_BITS - 1] != NOQ && !b.is_free(la[LB_BITS - 1]) {
                    B793_THOST.with(|c| c.set(Some(la[LB_BITS - 1])));
                    if std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE unhost_fwd slot {}", p3_cur_slot()); }
                }
            }
        }
        let (rec, lanes) = m94_lean(r14m('r'), || i5_rho_counter(b, x, act, r, gate));
        B793_THOST.with(|c| c.set(None));
        b.play(&rec, false);
        b.free_n(&lanes);
        rotate_three(b, x, r, false, true);
        return;
    }
    // P2-REBASE: below the 813 floor the prefixes and the LA gate do not fit beside the walk's state
    let room = p2_room(b);
    if room < 7 + gate_lanes(gate) {
        assert!(room >= 6, "renorm_top_lean: room {room}");
        return renorm_top_lean(b, x, act, r, gate, room.min(7));
    }
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
/// FUSE-S4: the inverse barrel in the +54 gauge (lane sums 51, 52, 54, 58 for stages 0..3), stage 3's region pairs
/// (lanes <= 58) under r2 ^ s4 (the denorm's held-back Rev(58)[s4] merged in). No promise deletion.
fn rotate_three_fused_inv(b: &mut B, x: &[QubitId], r: &[QubitId], s4: QubitId) {
    let n = x.len();
    // (51, 52, 54, 58) at NB = 28: stage 3 sums to c_5 = NB + 30 (the denorm's Rev(c_5)), the others keep the
    // telescope's differences 4, 2, 1
    let c5 = NB + 30;
    let sums = [c5 - 7, c5 - 6, c5 - 4, c5];
    for stage in (0..4).rev() {
        let ctrl = r[stage.min(2)];
        if stage == 1 || stage == 2 { b.cx(r[stage - 1], ctrl); }
        let sm = sums[stage];
        if stage == 3 {
            for p in sm + 1..n {
                let q = sm + n - p;
                if p < q { b.cswap(ctrl, x[p], x[q]); }
            }
            let merge = !m2_break(8);
            if merge { b.cx(s4, ctrl); }
            for p in 0..=sm {
                let q = sm - p;
                if p < q { b.cswap(ctrl, x[p], x[q]); }
            }
            if merge { b.cx(s4, ctrl); }
        } else {
            for p in 0..n {
                let q = (sm + n - p) % n;
                if p < q { b.cswap(ctrl, x[p], x[q]); }
            }
        }
        if stage == 1 || stage == 2 { b.cx(r[stage - 1], ctrl); }
    }
}
/// FUSE-S4: s4 = [tz(X) >= 16 - r] on the restored ring, erased by measurement; the repair is Z(t_15) and
/// CZ(h_k, t_(15-k)) CZ(h_k, t_(16-k)) for k = 1..7 (t_q = AND_(i<=q) !X[i], h_k = [r >= k]), all Clifford on a
/// measured-uncompute chain (15 T) and the r thermometer (8 T).
fn fuse_s4_erase(b: &mut B, x: &[QubitId], r: &[QubitId], s4: QubitId) {
    erase_mbu(b, s4, |b| {
        let t = b.alloc_n(15);
        b.x(x[0]);
        for q in 1..=15 {
            let prev = if q == 1 { x[0] } else { t[q - 2] };
            b.x(x[q]);
            b.and_c(prev, x[q], t[q - 1]);
            b.x(x[q]);
        }
        let tq = |q: usize| t[q - 1];
        // h lanes: a = r1|r0, h1 = a|r2, h2 = r1|r2, c = r1&r0, h3 = r2|c, h5 = r2&a, h6 = r2&r1, h7 = h6&r0
        let hl = b.alloc_n(8);
        let (a, h1, h2, c, h3, h5, h6, h7) = (hl[0], hl[1], hl[2], hl[3], hl[4], hl[5], hl[6], hl[7]);
        // t = x | y = !(!x & !y)
        let or2 = |b: &mut B, x: QubitId, y: QubitId, t: QubitId, undo: bool| {
            b.x(x);
            b.x(y);
            if undo {
                b.x(t);
                b.and_u(x, y, t);
            } else {
                b.and_c(x, y, t);
                b.x(t);
            }
            b.x(y);
            b.x(x);
        };
        let and2 = |b: &mut B, x: QubitId, y: QubitId, t: QubitId, undo: bool| {
            if undo { b.and_u(x, y, t); } else { b.and_c(x, y, t); }
        };
        or2(b, r[1], r[0], a, false);
        or2(b, a, r[2], h1, false);
        or2(b, r[1], r[2], h2, false);
        and2(b, r[1], r[0], c, false);
        or2(b, r[2], c, h3, false);
        and2(b, r[2], a, h5, false);
        and2(b, r[2], r[1], h6, false);
        and2(b, h6, r[0], h7, false);
        let h = [h1, h2, h3, r[2], h5, h6, h7];
        b.z(tq(15));
        for k in 1..=7 {
            if k == 1 && m2_break(9) { continue; }
            b.cz(h[k - 1], tq(15 - k));
            b.cz(h[k - 1], tq(16 - k));
        }
        and2(b, h6, r[0], h7, true);
        and2(b, r[2], r[1], h6, true);
        and2(b, r[2], a, h5, true);
        or2(b, r[2], c, h3, true);
        and2(b, r[1], r[0], c, true);
        or2(b, r[1], r[2], h2, true);
        or2(b, a, r[2], h1, true);
        or2(b, r[1], r[0], a, true);
        b.free_n(&hl);
        for q in (1..=15).rev() {
            let prev = if q == 1 { x[0] } else { t[q - 2] };
            b.x(x[q]);
            b.and_u(prev, x[q], t[q - 1]);
            b.x(x[q]);
        }
        b.x(x[0]);
        b.free_n(&t);
    });
}
fn unrenorm_top(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, r: &[QubitId], gate: GateSpec) {
    unrenorm_top_s4(b, u, act, r, gate, None)
}
fn unrenorm_top_s4(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, r: &[QubitId], gate: GateSpec, s4: Option<QubitId>) {
    unrenorm_top_s4f(b, u, act, r, gate, s4);
}
/// unrenorm_top_s4; true when the lean form already freed r (measured, |0>).
fn unrenorm_top_s4f(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, r: &[QubitId], gate: GateSpec, s4: Option<QubitId>) -> bool {
    match s4 {
        Some(s4) => {
            rotate_three_fused_inv(b, &u.x, r, s4);
            assert!(u.room(b) + 1 >= FUSE_S4_NEED + 1, "FUSE-S4 erase room");
            fuse_s4_erase(b, &u.x, r, s4);
            b.free(s4);
        }
        None => rotate_three(b,&u.x,r,true,true),
    }
    if i5_rcnt() {
        // RCNT: erase r coherently by the counter's inverse on the restored ring (r freed by the caller)
        // b793b UNHOST: t on LA[8] where it is a bound |0> lane (slots >= 1; the gate reads LA bits below 8 only)
        if b793_unhost() && p3_cur_slot() >= 1 && p3_cur_slot() <= 43 && gate.map_or(true, |(_, hb, _)| hb <= LB_BITS - 1) {
            // bit 8 of LA / LB: |0> from slot 1 on; under R8_M8 the shared lane (LA[8] = LB[8]) is the host
            let h = if r8_m8() { u.lb[LB_BITS - 1] } else { u.la[LB_BITS - 1] };
            if h != NOQ && !b.is_free(h) && u.lb[LB_BITS - 1] != NOQ {
                B793_THOST.with(|c| c.set(Some(h)));
                if std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE unhost slot {}", p3_cur_slot()); }
                // negative control (gate tests only): the host lane is left holding 1
                if b793b_break("unh1") { b.x(h); }
            }
        }
        // b793b UNHOST0 (F5 slot 0, knob B793_UNHOST0): at the last inverse slot LA = 256 on every shot (bit 8 set, bits 0..7 are |0>),
        // and the counter is ungated there (gate None: no LA literal is read), so t runs on LA[0]
        if b793_unhost0() && p3_cur_slot() == 0 && gate.is_none() && u.la.len() == LB_BITS && u.la[0] != NOQ && !b.is_free(u.la[0]) {
            B793_THOST.with(|c| c.set(Some(u.la[0])));
            if std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE unhost0 slot 0"); }
            // negative control (gate tests only): the host lane is left holding 1
            if b793b_break("unh0") { b.x(u.la[0]); }
        }
        let (rec, lanes) = m94_lean(r14m('u'), || i5_rho_counter(b, &u.x, act, r, gate));
        B793_THOST.with(|c| c.set(None));
        b.play(&rec, true);
        b.free_n(&lanes);
        if i5_rfree() { b.free_n(r); }
        return i5_rfree();
    }
    let receipts=b.fresh_bits(3);
    for i in 0..3 { b.hmr_to(r[i],receipts[i]); }
    // I5-LANES L1 (dev switch I5_RFREE, inert unless set): r is |0> after its X-basis measurement, so its lanes go
    // back to the pool before the phase repair's prefix chain (the caller then skips its free)
    if i5_rfree() { b.free_n(r); }
    // P2-REBASE: below the 813 floor the blocks' chain, LA gate and AND lane do not fit: gated chain in place
    if unren_cond() && u.room(b) < 6 + gate_lanes(gate) {
        if !i5_rfree() { b.free_n(r); }
        LEAN_UNREN.with(|c| c.set(true));
        unren_phase_cond(b, &u.x, act, &receipts, gate);
        LEAN_UNREN.with(|c| c.set(false));
        return true;
    }
    if unren_cond() { unren_phase_cond(b, &u.x, act, &receipts, gate); return i5_rfree(); }
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
    i5_rfree()
}

/// R9 rowtmp c: `unrenorm_top_s4f` (no s4, RCNT) on a slot whose act lane is released: the inverse counter re-forms
/// act = a1 | [rho >= 1] on its lane t before step 1 (see `i5_rho_counter_x`); returns t (= act). r freed as there.
fn unrenorm_rcnt_el(b: &mut B, u: &GreedyFrog, r: &[QubitId], gate: GateSpec, a1: QubitId) -> QubitId {
    rotate_three(b, &u.x, r, true, true);
    let (rec, lanes, t) = m94_lean(r14m('u'), || i5_rho_counter_x(b, &u.x, None, r, gate, Some(a1)));
    b.play(&rec, true);
    let rest: Vec<QubitId> = lanes.iter().copied().filter(|&q| q != t).collect();
    zero_probe(b, &rest);
    b.free_n(&rest);
    if i5_rfree() { zero_probe(b, r); b.free_n(r); }
    t
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
thread_local! {
    /// P2-REBASE: unren_block runs its lean form (gated chain in place, guards on borrowed lanes)
    static LEAN_UNREN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
/// P2-REBASE: unren_block's lean form. The chain p'_0..p'_(jt-1) is gated in place (prefix_lean's guard), so the
/// phases sit on the chain lanes directly; p'_jt's phase is CZ(p'_(jt-1), z_jt) times the guard term's phase.
fn unren_block_lean(b: &mut B, x: &[QubitId], act: Option<QubitId>, jt: usize, zs: &[usize], zifs: &[(usize, BitId)],
                    conds: &[BitId], gate: GateSpec) {
    for &c in conds { b.push_condition(c); }
    // act None: p_0 is the lane z_0 itself (not gated: gmin >= 1); the chain lanes are fresh for j >= 1 (or j >= 0)
    let fresh: Vec<QubitId> = b.alloc_n(if act.is_some() { jt } else { jt - 1 });
    let p: Vec<QubitId> = if act.is_some() { fresh.clone() } else {
        std::iter::once(x[W - 1]).chain(fresh.iter().copied()).collect()
    };
    if act.is_some() {
        prefix_lean(b, x, act, &p, gate, false);
    } else {
        // p_0 = z_0 (the X-flipped lane); prefix_lean for j >= 1 with p_0 as the lane itself
        b.x(x[W - 1]);
        let d = super::mask::borrowed();
        for i in 1..jt {
            let q = x[W - 1 - i];
            b.x(q);
            b.and_c(p[i - 1], q, p[i]);
            if let Some((la, hb, gmin)) = gate { if i >= gmin { and_dirty(b, &guard_lits(Some(p[i - 1]), q, la, hb, i), p[i], &d); } }
            b.x(q);
        }
    }
    for &j in zs { b.z(p[j]); }
    for &(j, bit) in zifs { b.z_if(p[j], bit); }
    // p'_jt = p'_(jt-1) & z_jt & [LA != jt] (jt >= gmin): CZ(p'_(jt-1), z_jt) and the guard term's phase
    if !(jt == 3 && cr_break(1)) {
        let q = x[W - 1 - jt];
        b.x(q);
        b.cz(p[jt - 1], q);
        if let Some((la, hb, gmin)) = gate {
            if jt >= gmin { phase_and(b, &guard_lits(Some(p[jt - 1]), q, la, hb, jt)); }
        }
        b.x(q);
    }
    if act.is_some() {
        prefix_lean(b, x, act, &p, gate, true);
    } else {
        let d = super::mask::borrowed();
        for i in (1..jt).rev() {
            let q = x[W - 1 - i];
            b.x(q);
            if let Some((la, hb, gmin)) = gate { if i >= gmin { and_dirty(b, &guard_lits(Some(p[i - 1]), q, la, hb, i), p[i], &d); } }
            b.and_u(p[i - 1], q, p[i]);
            b.x(q);
        }
        b.x(x[W - 1]);
    }
    b.free_n(&fresh);
    for _ in conds { b.pop_condition(); }
}

fn unren_block(b: &mut B, x: &[QubitId], act: Option<QubitId>, jt: usize, zs: &[usize], zifs: &[(usize, BitId)],
               conds: &[BitId], gate: GateSpec) {
    if LEAN_UNREN.with(|c| c.get()) {
        return unren_block_lean(b, x, act, jt, zs, zifs, conds, gate);
    }
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
        let need = self.cntw().len() - 1;
        if b792_p4() && self.room(b) < need {
            // B792_P4: no clean lane left under the cap: borrowed-dirty ripple on the restored dy lanes (exact, same function)
            let w = self.cntw();
            for &q in w { b.x(q); }
            inc_dirty(b, ctrl, w, &self.dirty);
            for &q in w { b.x(q); }
            return;
        }
        let anc = b.alloc_n(need);
        super::arith::dec(b, ctrl, self.cntw(), &anc);
        b.free_n(&anc);
    }
    /// c -= ctrl
    fn cnt_dec(&self, b: &mut B, ctrl: QubitId) {
        let need = self.cntw().len() - 1;
        if b792_p4() && self.room(b) < need {
            let w = self.cntw();
            inc_dirty(b, ctrl, if b793b_break("p4") { &w[1..] } else { w }, &self.dirty);
            return;
        }
        let anc = b.alloc_n(need);
        super::arith::inc(b, ctrl, self.cntw(), &anc);
        b.free_n(&anc);
    }
    /// out ^= [c == 0] (all counter lanes one)
    fn cnt_zero_into(&self, b: &mut B, out: QubitId) {
        let lits: Vec<(QubitId, bool)> = self.cntw().iter().map(|&q| (q, false)).collect();
        and_into(b, &lits, out);
    }

    pub fn alloc(b: &mut B) -> GreedyFrog {
        GreedyFrog { cmp_in: None, x: b.alloc_n(W), y: b.alloc_n(W), la: b.alloc_n(LB_BITS), lb: b.alloc_n(LB_BITS),
              dirty: b.alloc_n(std::env::var("B792_TD").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(TEST_DIRTY)),
              cap: std::env::var("GREEDYFROG_TEST_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(u64::MAX),
              cnt: vec![], par: b.alloc() }.with_cnt()
    }

    /// sw ^= act & [LA != 0] & X[W-1] & (LA < LB | LA == LB & Y top > X top)   (F9). The top compare is unmasked even
    /// when LB < WC: with LA == LB the values differ inside their top LB lanes unless A' == B, and A' == B forces
    /// B = gcd = 1, so LB == 1 is excluded instead (A' == B == 1 never swaps).
    /// sw ^= F9 (out None: the phase (-1)^F9, for a measured erase). The temporaries are erased by measurement.
    fn swap_flag(&self, b: &mut B, z0: Option<QubitId>, out: Option<QubitId>, w: &Win, keep: bool) -> Option<QubitId> {
        if out.is_none() && !keep && swf_lex() && r14m('s') {
            self.swap_flag_phase_jit(b, z0, w);
            return None;
        }
        let nzs = swf_lex() && b793_nonz_skip(w);
        if nzs && std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE nonz swap_flag slot {}", p3_cur_slot()); }
        // b792 P5 (B792_P5): the SWF-LEX path never reads lt / eq (it frees them unused), so they are not taken at all
        let p5_nolteq = swf_lex() && b792_p5();
        let lt = if p5_nolteq { NOQ } else { b.alloc() };
        let eq = if p5_nolteq { NOQ } else { b.alloc() };
        let cmp = b.alloc();
        let nz = if nzs { NOQ } else { b.alloc() };
        if !swf_lex() {
            lt_sm(b, self, &self.la, &self.lb, Some(lt));
            eq_auto(b, self, &self.la, &self.lb, eq);
        }
        let cmp_into = |b: &mut B, u: &GreedyFrog, cmp: Option<QubitId>| {
            let t: Vec<QubitId> = u.x[W - wc()..top_cmp_hi()].to_vec();
            let s: Vec<QubitId> = u.y[W - wc()..top_cmp_hi()].to_vec();
            let c0 = b.alloc();
            let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
            if w.lb.0 <= 1 {
                let ne1 = b.alloc();
                and_auto(b, u, &eq_lits(&u.lb, 1), ne1);
                b.x(ne1);
                let pool = pool_for(b, u, t.len(), 0);
                plain_compare(b, &t, &s, c0, &sc, cmp, Some((ne1, false)), &pool);
                b.free_n(&pool);
                b.x(ne1);
                and_auto(b, u, &eq_lits(&u.lb, 1), ne1);
                b.free(ne1);
            } else {
                let pool = pool_for(b, u, t.len(), 0);
                plain_compare(b, &t, &s, c0, &sc, cmp, None, &pool);
                b.free_n(&pool);
            }
            b.free(c0);
        };
        if swf_lex() {
            // SWF-LEX: core = lt | eq & cmp = [LA < LB + cmp] (cmp = [Ytop > Xtop] as the 9-bit compare's carry-in)
            // (LEN-TRIM: bits 0..ln)
            let ln = len_n(w);
            if !p5_nolteq { b.free_n(&[lt, eq]); }
            // R8-ROOM0 R8_SWL (exact): the forward's fresh sw is |0> until the final AND: it leaves the live count during
            // the three passes before it (taken back by id), so they get its lane as room
            let lend: Vec<QubitId> = if r8_swl(self) { out.into_iter().filter(|_| SWL_OUT_FRESH.with(|c| c.get())).collect() } else { vec![] };
            let core = b.alloc();
            r6t(b, "sf0", self.room(b));
            r8_lend(b, &lend, |b| cmp_into(b, self, Some(cmp)));
            r6t(b, "sf.cmp", self.room(b));
            r8_lend(b, &lend, |b| lt_cin_sm(b, self, &self.la[..ln], &self.lb[..ln], cmp, Some(core)));
            r6t(b, "sf.ltcin", self.room(b));
            if !nzs { r8_lend(b, &lend, |b| zero_auto(b, self, &self.la[..ln], nz)); } // nz = [LA == 0]
            r6t(b, "sf.nz", self.room(b));
            let mut lits: Vec<(QubitId, bool)> = if swf_nz() { vec![] } else { z0.map(|z| vec![(z, true)]).unwrap_or_default() };
            if !(swf_nz() && mw_break(1)) && !nzs { lits.push((nz, true)); }
            lits.extend([(self.x[W - 1], false), (core, false)]);
            match out {
                Some(sw) => and_auto(b, self, &lits, sw),
                None => phase_and(b, &lits),
            }
            r6t(b, "sf.and", self.room(b));
            let zl: Vec<(QubitId, bool)> = self.la[..ln].iter().map(|&q| (q, true)).collect();
            if !nzs { erase_and(b, self, nz, &zl); }
            r6t(b, "sf.enz", self.room(b));
            erase_mbu(b, core, |b| lt_cin_sm(b, self, &self.la[..ln], &self.lb[..ln], cmp, None));
            r6t(b, "sf.ecore", self.room(b));
            if keep {
                // DCMP-REUSE: cmp stays live for the successor's F2 (fwd_slot applies cmp ^= sw after the swap)
                b.free_n(&[core]);
                if !nzs { b.free(nz); }
                return Some(cmp);
            }
            erase_mbu(b, cmp, |b| cmp_into(b, self, None));
            r6t(b, "sf.ecmp", self.room(b));
            b.free_n(&[core, cmp]);
            if !nzs { b.free(nz); }
            return None;
        }
        assert!(!keep, "DCMP-REUSE needs the SWF-LEX swap flag");
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
        None
    }

    /// R14 misc94 "DonRwetter" s: `swap_flag` with out None and keep false on the SWF-LEX path (the inverse's I5 erase
    /// repair, (-1)^F9), with the same gates in the same order as the parent's; only the lane lifetimes change. cmp is
    /// taken for the top compare, core for lt_cin, nz for the zero test, each just before its first gate, and each is
    /// freed right after its own measured erase. The parent takes lt, eq, cmp, nz before anything (lt and eq are freed
    /// unused on this path) and core before the compare, so its widest fixed instant is 4 lanes; this one is 3.
    fn swap_flag_phase_jit(&self, b: &mut B, z0: Option<QubitId>, w: &Win) {
        let cmp_into = |b: &mut B, u: &GreedyFrog, cmp: Option<QubitId>| {
            let t: Vec<QubitId> = u.x[W - wc()..top_cmp_hi()].to_vec();
            let s: Vec<QubitId> = u.y[W - wc()..top_cmp_hi()].to_vec();
            let c0 = b.alloc();
            let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
            if w.lb.0 <= 1 {
                let ne1 = b.alloc();
                and_auto(b, u, &eq_lits(&u.lb, 1), ne1);
                b.x(ne1);
                let pool = pool_for(b, u, t.len(), 0);
                plain_compare(b, &t, &s, c0, &sc, cmp, Some((ne1, false)), &pool);
                b.free_n(&pool);
                b.x(ne1);
                and_auto(b, u, &eq_lits(&u.lb, 1), ne1);
                b.free(ne1);
            } else {
                let pool = pool_for(b, u, t.len(), 0);
                plain_compare(b, &t, &s, c0, &sc, cmp, None, &pool);
                b.free_n(&pool);
            }
            b.free(c0);
        };
        let ln = len_n(w);
        // b792 P5 (B792_P5): lane-free form. core = [LA < LB + cmp] = [LA || Xwin < LB || Ywin] (lexicographic = numeric compare
        // of the concatenated operands; cmp = [Xwin < Ywin] when LB > 1 is known at the slot), and the phase (-1)^(X[W-1] & core)
        // is formed on a TTK-style in-operand carry ladder: no cmp lane, no core lane, no c0 lane.
        if b792_p5() && b793_nonz_skip(w) && (swf_nz() || z0.is_none()) && w.lb.0 > 1 && top_cmp_hi() < W {
            let t_w: Vec<QubitId> = self.x[W - wc()..top_cmp_hi()].to_vec();
            let s_w: Vec<QubitId> = self.y[W - wc()..top_cmp_hi()].to_vec();
            let (mut av, mut bv): (Vec<QubitId>, Vec<QubitId>) = (self.la[..ln].to_vec(), self.lb[..ln].to_vec());
            if r8_hb() < R8_TOP && av.len() == LB_BITS && bv.len() == LB_BITS {
                av = r8_live(&av);
                bv = r8_live(&bv);
                if av.last() == bv.last() { av.pop(); bv.pop(); }
            }
            let mut tt = t_w; tt.extend(av);
            let mut ss = s_w; ss.extend(bv);
            let (l, n) = (self.x[W - 1], tt.len());
            if std::env::var_os("B792_DBG").is_some() { eprintln!("B792FIRE p5 slot {} n {}", p3_cur_slot(), n); }
            assert_eq!(n, ss.len());
            assert!(n >= 3 && !tt.contains(&l) && !ss.contains(&l), "b792 P5: X[W-1] is an operand lane");
            // c_n = A_{n-1} ^ B'_{n-1} A'_{n-1}, A = !T, B = S: the first term while A_{n-1} still holds its input
            b.x(tt[n - 1]);
            b.cz(l, tt[n - 1]);
            b.x(tt[n - 1]);
            b.begin();
            for &q in &tt { b.x(q); }
            for i in 1..n { b.cx(tt[i], ss[i]); }
            for i in (1..n - 1).rev() { b.cx(tt[i], tt[i + 1]); }
            for i in 0..n - 1 { b.ccx(ss[i], tt[i], tt[i + 1]); }
            let ru = b.end();
            b.play(&ru, false);
            if b792_break("p5z") { b.z(l); } else if !b792_break("p5") { b.ccz(l, ss[n - 1], tt[n - 1]); }
            if b792_break("p5a") { b.cz(l, tt[n - 1]); }
            b.play(&ru, true);
            return;
        }
        let cmp = b.alloc();
        cmp_into(b, self, Some(cmp));
        let core = b.alloc();
        lt_cin_sm(b, self, &self.la[..ln], &self.lb[..ln], cmp, Some(core));
        let nzs = b793_nonz_skip(w);
        let nz = if nzs { NOQ } else { b.alloc() };
        if !nzs { zero_auto(b, self, &self.la[..ln], nz); } // nz = [LA == 0]
        let mut lits: Vec<(QubitId, bool)> = if swf_nz() { vec![] } else { z0.map(|z| vec![(z, true)]).unwrap_or_default() };
        if !(swf_nz() && mw_break(1)) && !nzs { lits.push((nz, true)); }
        lits.extend([(self.x[W - 1], false), (core, false)]);
        // negative control (dev only): drop the core literal from the repair
        if r14m_break("s") { lits.pop(); }
        phase_and(b, &lits);
        let zl: Vec<(QubitId, bool)> = self.la[..ln].iter().map(|&q| (q, true)).collect();
        if !nzs { erase_and(b, self, nz, &zl); b.free(nz); }
        erase_mbu(b, core, |b| lt_cin_sm(b, self, &self.la[..ln], &self.lb[..ln], cmp, None));
        b.free(core);
        erase_mbu(b, cmp, |b| cmp_into(b, self, None));
        b.free(cmp);
    }

    /// R14 misc94 p: I1's done flag z0 = [LA[..ln] == 0] & [cnt != 0] on a fresh lane, gate for gate the parent's I1
    /// (temporaries, Z0-DEFER repair, measured erases).
    fn m94_i1_z0(&self, b: &mut B, w: &Win, bits: &SlotBits) -> QubitId {
        let z0 = b.alloc();
        if b792_late() {
            // B792_LATE: z0 = [LA == 0] & [c != 0] = [LA == 0] ^ [LA == 0] & [c == 0] straight into z0 through borrowed dirty lanes: no cz,
            // no lz lane (the term slot's census instant)
            let lnz0 = if b792_s255(w) { len_n(w).min(self.la_bound_prefix().len()) } else { len_n(w) };
            let mut lits: Vec<(QubitId, bool)> = self.la[..lnz0].iter().map(|&q| (q, true)).collect();
            and_dirty(b, &lits, z0, &self.dirty);
            if !b792_brk("latez") { lits.extend(self.cntw().iter().map(|&q| (q, false))); }
            and_dirty(b, &lits, z0, &self.dirty);
            if let Some(m) = bits.z0m {
                if !m2_break(2) { b.z_if(z0, m); }
            }
            return z0;
        }
        let cz = b.alloc();
        self.cnt_zero_into(b, cz);
        let lz = b.alloc();
        let lnz = if b792_s255(w) { len_n(w).min(self.la_bound_prefix().len()) } else { len_n(w) };
        zero_into(b, &self.la[..lnz], lz);
        and_into(b, &[(lz, false), (cz, true)], z0);
        if let Some(m) = bits.z0m {
            if !m2_break(2) { b.z_if(z0, m); }
        }
        if z0_meas() {
            let zl: Vec<(QubitId, bool)> = self.la[..lnz].iter().map(|&q| (q, true)).collect();
            let cl: Vec<(QubitId, bool)> = self.cntw().iter().map(|&q| (q, false)).collect();
            erase_and(b, self, lz, &zl);
            if cr_break(4) { let m = b.fresh_bits(1)[0]; b.hmr_to(cz, m); } else { erase_and(b, self, cz, &cl); }
        } else {
            zero_into(b, &self.la[..lnz], lz);
            self.cnt_zero_into(b, cz);
        }
        b.free(lz);
        b.free(cz);
        z0
    }
    /// B792_S255: LA[hb..8) held out of the whole rows stretch are bound fresh |0> again (where the parent takes its R3_LATOP hosts back)
    /// The fresh lanes join `lend` (the undo rows' pool), where the parent's R3_LATOP hosts of the same bits stand.
    /// `defer7` (the r5_rebind path, R11_LA7 on a plain slot): LA[7] stays unbound and re-binds at the end of the undo rows, as the parent's does.
    fn b792_s255_rebind(&mut self, b: &mut B, lend: &mut Vec<QubitId>, defer7: bool) {
        if cfg!(test) && std::env::var_os("B792_S255_DBG").is_some() { B792_S255_HELD.with(|c| eprintln!("B792S255 FIRE rebind held {:?} defer7 {}", c.borrow(), defer7)); }
        for k in B792_S255_HELD.with(|c| std::mem::take(&mut *c.borrow_mut())) {
            assert!(self.la[k] == NOQ, "B792_S255: LA[{k}] was bound while held out");
            if (defer7 || b792_pl_slot()) && k == LB_BITS - 2 { R10LA2.with(|c| c.borrow_mut().push(k)); continue; }
            self.la[k] = b.alloc();
            // negative control (gate tests only): B793_BREAK=s255rb re-binds LA[6] holding 1 (it must be |0>)
            if b793b_break("s255rb") && k == R_BITS + 1 { b.x(self.la[k]); }
            // negative control (gate tests only): B792_BREAK=plrb re-binds LA[6] holding 1 on the B792_PL slots
            if b792_brk("plrb") && b792_pl_slot() && k == R_BITS + 1 { b.x(self.la[k]); }
            lend.push(self.la[k]);
        }
    }
    /// B792_S255: the leading run of LA lanes that are bound (LA[hb..8) are NO_QUBIT while the knob holds them out)
    fn la_bound_prefix(&self) -> Vec<QubitId> {
        let n = self.la.iter().position(|&q| q == NOQ).unwrap_or(self.la.len());
        self.la[..n].to_vec()
    }

    /// One forward slot (F1..F11). Returns the measurement record.
    pub fn fwd_slot(&mut self, b: &mut B, w: &Win) -> SlotBits {
        self.fwd_slot_next(b, w, None)
    }

    /// One forward slot (F1..F11) followed by the forward slot with window `next` (None: no successor, or the
    /// successor is not run by this caller). LS-3 DCMP-REUSE hands F9's comparator to a plain successor's F2.
    pub fn fwd_slot_next(&mut self, b: &mut B, w: &Win, next: Option<&Win>) -> SlotBits {
        super::mask::set_borrowed(&self.dirty);
        p2_set_cap(self.cap);
        r8_lhf_open(b, self, w);
        r8_m8_open(b, self, w);
        b792_f8_out(b, self, w);
        if r3_flag("R4_DBG") {
            eprintln!("R4WIN slot {} lb {:?} lad {:?} act_const {} a1_const {} mxp {} k {} live {}", super::builder::i5::SLOT.with(|c| c.get()),
                      w.lb, w.lad, w.act_const, w.a1_const, w.mxp, w.k, b.live);
        }
        prof(b, "f.z0");
        p3(b, self, "f.z0");
        // F1
        // FWD-ACT-CONST (B-CRUMBS, ST-001): on slots where no shot can have finished (the inverse's act_const), act = 1
        // classically: no done flag, no counter increment, no flag erase (the inverse already skips them there)
        let mut zo = if fwd_act_const() && w.act_const { None } else { Some(b.alloc()) };
        let ln = len_n(w);
        if let Some(z0) = zo {
            zero_into(b, &self.la[..ln], z0);
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
        // R9-DONE (F1 -> F4): zo = [LA[..ln] == 0] and LA is unchanged until F5: zo leaves its lane across F2 / F3
        let r9 = zo.is_some() && r9_done_slot(self, w, ln);
        let r9z = r9 && r9_site(1);
        if r9z { r9_dbg(w, "F1", zo.unwrap(), &r9_zero_lits(&self.la[..ln])); r9_erase(b, self, zo.unwrap(), &r9_zero_lits(&self.la[..ln]), 1); }
        prof(b, "f.dcmp");
        p3(b, self, "f.dcmp");
        // F2: d = a1 & [B > A >> e] (top window)
        let d = b.alloc();
        // TERM-LAST: d = 0 on every passing shot of the last slot (d stays |0>; a carried DCMP comparator is consumed)
        let tm = term(w);
        if let Some(c) = self.cmp_in.take() {
            // DCMP-REUSE: c = the predecessor's cmp ^ sw = [Y top > X top] (top tie at a swap excepted)
            assert!(w.lb.0 >= wc(), "DCMP-REUSE successor must run the plain top compare");
            b.and_c(a1, c, d);
            erase_mbu(b, c, |b| top_compare(b, self, None, w, None));
            b.free(c);
        } else if !tm {
            mark_msb(b, a1, &self.lb);
            R4_TOPC_ON.with(|c| c.set(true));
            top_compare(b, self, Some(d), w, Some((a1, false)));
            R4_TOPC_ON.with(|c| c.set(false));
            mark_msb(b, a1, &self.lb);
        }
        prof(b, "f.drot");
        p3(b, self, "f.drot");
        // F3
        if !tm {
            crot_up(b, d, &self.x, 1);
        }
        prof(b, "f.value");
        p3(b, self, "f.value");
        // F4: value chain, subtract where a1
        // R9-DONE: zo back on a fresh lane (the F1 test on the same LA)
        if r9z { zo = Some(r9_rebuild(b, &r9_zero_lits(&self.la[..ln]), 1)); }
        if let Some(z0) = zo { b.x(z0); } // z0 now holds act
        let mut act = zo;
        let mwa = masked_write_always();
        mark_done_inv(b, act, &self.lb);
        if mwa { mark_stall(b, act, a1, &self.lb); }
        let pk = act.and_then(|a| act_park(b, a, &self.lb, w.lb));
        // R9-DONE (F4): LA is still the F1 value: act = ![LA[..ln] == 0] leaves its lane across the value ladder
        let r9v = r9 && pk.is_none() && r9_site(2);
        if r9v { let a = act.unwrap(); r9_dbg(w, "F4", a, &r9_zero_lits(&self.la[..ln])); b.x(a); r9_erase(b, self, a, &r9_zero_lits(&self.la[..ln]), 2); }
        let rv = value_pass(b, self, w, true, a1, None, mwa, None);
        if r9v { let a = r9_rebuild(b, &r9_zero_lits(&self.la[..ln]), 2); b.x(a); act = Some(a); zo = act; }
        if let Some(a) = act { act_unpark(b, a, &self.lb, pk); }
        if mwa { mark_stall(b, act, a1, &self.lb); }
        mark_done_inv(b, act, &self.lb);
        if r8_m8() && r8_break("m8") { mark_stall(b, act, a1, &self.lb); }
        prof(b, "f.cof");
        p3(b, self, "f.cof");
        // H793 "Spiegelei" (forward mirror of YTOP-COF): Y[W-1] = B's MSB = 1 on every shot, and the forward cofactor
        // chain's ladder reaches lane CW - 1 - lad.0 < W - 1 where lad.0 >= 1; nothing else in F5 (LA decrement, done /
        // stall marks, act park, R9-DONE erase, the ladder's scratch, pools and borrowed passenger lanes, EARLY-GHOST)
        // names Y, so Y[W-1] is X-flipped to |0> and freed across f.cof, then re-bound and set back to 1
        let spg = h793_spg() && host_free() && w.lad.0 >= 1 && self.y[W - 1] != NOQ;
        let spg_q = self.y[W - 1];
        if spg {
            if !h793_spg_brk() { b.x(self.y[W - 1]); }
            zero_probe(b, &[self.y[W - 1]]);
            b.free(self.y[W - 1]);
            self.y[W - 1] = NOQ;
        }
        // F5: LA -= d; cofactor chain, add where a1
        if !tm {
            if r10_on("R10_DEC", self.room(b), ln - 1) {
                // R10_DEC (claude-r8): no room for the ln - 1 carry lanes: the decrement on borrowed lanes (exact)
                for &q in &self.la[..ln] { b.x(q); }
                inc_dirty(b, d, &self.la[..ln], &self.dirty);
                for &q in &self.la[..ln] { b.x(q); }
            } else {
            let anc = b.alloc_n(ln - 1);
            super::arith::dec(b, d, &self.la[..ln], &anc);
            b.free_n(&anc);
            }
        }
        mark_done_inv(b, act, &self.la);
        if mwa { mark_stall(b, act, a1, &self.la); }
        let pk = act.and_then(|a| act_park(b, a, &self.la, w.lad));
        // R9-DONE (F5): done-marked LA - d reads all ones on LA[..ln] exactly where the shot is finished
        let r9c = r9 && pk.is_none() && r9_site(4) && r9_cof_ok(w, ln);
        if r9c { let a = act.unwrap(); r9_dbg(w, "F5", a, &r9_one_lits(&self.la[..ln])); b.x(a); r9_erase(b, self, a, &r9_one_lits(&self.la[..ln]), 4); }
        let mut rc = RollRec::default();
        if lane0_direct() {
            // x0 = X[0] here (F4 cleared A's wrapped MSB where d = 1)
            let cv = r4_cview(self, w, w.lad);
            r4_cv_open(b, self, w, &self.la, w.lad);
            let off = r4_idle_spec(b, self, w, &self.lb, w.lb.0, w.lb.1, r4_need(cv, w.lad.1), P2_COF_EXTRA);
            let m = r4_alloc_ladder(b, w.lad.1, cv);
            p2_host_clear();
            let (t, s) = cof_ladder(self, w, self.x[0]);
            let src = cof_src(self, &m, w);
            if roll_cof() && r3f_roll_ok(b, if roll_cof_masked() { 1 } else { 2 }) {
                rc = cof_roll_fwd(b, &t, &s, src, &m, a1, mwa, w.a1_const);
            } else {
                let pool = pool_for(b, self, t.len() - (w.lad.1 - w.lad.0 + 1), 0);
                masked_pass(b, self, &t, &s, src, &m, false, Some(a1), None, &pool, mwa, w.a1_const, None);
                b.free_n(&pool);
            }
            m.free(b);
            r4_idle_close(b, self, &self.lb, off);
            r4_cv_close(b, self, w, &self.la, w.lad);
        } else {
            let cv = r4_cview(self, w, w.lad);
            r4_cv_open(b, self, w, &self.la, w.lad);
            let off = r4_idle_spec(b, self, w, &self.lb, w.lb.0, w.lb.1, r4_need(cv, w.lad.1), P2_COF_EXTRA);
            let m = r4_alloc_ladder(b, w.lad.1, cv);
            p2_host_clear();
            let x0 = b.alloc();
            lane0_src(b, self, d, x0);
            let (t, s) = cof_ladder(self, w, x0);
            let src = cof_src(self, &m, w);
            // carry pool over the ordinary lanes below the LA - d window
            if roll_cof() && r3f_roll_ok(b, if roll_cof_masked() { 1 } else { 2 }) {
                rc = cof_roll_fwd(b, &t, &s, src, &m, a1, mwa, w.a1_const);
            } else {
                let pool = pool_for(b, self, t.len() - (w.lad.1 - w.lad.0 + 1), 0);
                masked_pass(b, self, &t, &s, src, &m, false, Some(a1), None, &pool, mwa, w.a1_const, None);
                b.free_n(&pool);
            }
            lane0_src(b, self, d, x0);
            b.free(x0);
            m.free(b);
            r4_idle_close(b, self, &self.lb, off);
            r4_cv_close(b, self, w, &self.la, w.lad);
        }
        if r9c { let a = r9_rebuild(b, &r9_one_lits(&self.la[..ln]), 4); b.x(a); act = Some(a); zo = act; }
        if let Some(a) = act { act_unpark(b, a, &self.la, pk); }
        if mwa { mark_stall(b, act, a1, &self.la); }
        mark_done_inv(b, act, &self.la);
        if r8_m8() && r8_break("m8") { mark_stall(b, act, a1, &self.lb); }
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
        if spg {
            // the same id back (the shell and the gate test read the forward's result through the slot-start ids)
            if b.is_free(spg_q) { b.acquire(spg_q); self.y[W - 1] = spg_q; }
            else {
                if std::env::var_os("R14F_DBG").is_some() { eprintln!("H793SPG id-taken slot {}", p3_cur_slot()); }
                self.y[W - 1] = b.alloc();
            }
            b.x(self.y[W - 1]);
        }
        prof(b, "f.renorm");
        p3(b, self, "f.renorm");
        // F6, F7, F8 (every active shot: a step's renormalisation, or a stall's)
        let r = b.alloc_n(RHO_BITS);
        renorm_top(b, &self.x, act, &r, gate_spec(&self.la, w));
        if let Some(z0) = zo { b.x(z0); } // back to z0
        add_sm(b, self, &self.la[..ln], &r, false, true);
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
        // TERM-LAST: sw = 0 on every passing shot of the last slot (sw stays |0>)
        if !tm {
            let keep = dcmp_reuse() && swf_lex() && w.lb.0 > 1 && next.map_or(false, |n| n.lb.0 >= wc());
            SWL_OUT_FRESH.with(|c| c.set(true));
            let kc = self.swap_flag(b, zo, Some(sw), w, keep);
            SWL_OUT_FRESH.with(|c| c.set(false));
            let (xn, ln) = swap_lanes(w, true);
            super::arith::cswap_regs(b, sw, &self.x[..xn], &self.y[..xn]);
            super::arith::cswap_regs(b, sw, &self.la[..ln], &self.lb[..ln]);
            b.cx(sw, self.par);
            if let Some(c) = kc {
                if !dcmp_break(1) {
                    b.cx(sw, c);
                }
                self.cmp_in = Some(c);
            }
        }
        prof(b, "f.ghost");
        p3(b, self, "f.ghost");
        // F11: ghost d, r, sw, a1; erase z0 = [LA == 0] & [cnt != 0]
        let mut bits = SlotBits { d: bd, r: br, sw: b.fresh_bits(1)[0], a1: ba, rv, rc, z0m: None };
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
        // Z0-DEFER: where the inverse computes the same z0 as a wire (not act_const), the repair goes there
        if let Some(z0) = zo { if z0_defer() && !w.act_const {
            let m = b.fresh_bits(1)[0];
            b.hmr_to(z0, m);
            bits.z0m = Some(m);
        } else { erase_mbu(b, z0, |b| {
            let cl: Vec<(QubitId, bool)> = self.cntw().iter().map(|&q| (q, false)).collect();
            let zl: Vec<(QubitId, bool)> = self.la[..ln].iter().map(|&q| (q, true)).collect();
            let cz = b.alloc();
            and_auto(b, self, &cl, cz); // cz = [cnt == 0]
            let lz = b.alloc();
            and_auto(b, self, &zl, lz);
            phase_and(b, &[(lz, false), (cz, true)]);
            erase_and(b, self, lz, &zl);
            erase_and(b, self, cz, &cl);
            b.free(lz);
            b.free(cz);
        }); }
        b.free(z0); }
        r8_m8_close(b, self);
        r8_lhf_close(b, self);
        prof(b, "end");
        p3(b, self, "end");
        bits
    }
}


// ------------------------------------------------------------------ inverse slot (decode + undo)

/// window bits of the decode (cofactor top bits kept after normalisation). Q825 LS-3 NB-SELL: 28 -> 27 (-25.2k T for
/// +0.40 walk Lambda, decode kind; paired with the NSLOTS 256 + park-unlock 9/17 buybacks). Q825 B-SYMR25 SYM-R-25: 27 -> 25
/// under ROUND_DIV was the spec; on the circuit's non-restoring rows rounding is worth only ~0.3 lanes (emulator, 12.8M
/// walks), so the Lambda-neutral swap ships NB 26 + ROUND_DIV + RUN_GUARD + rows +1 at slots 1-84 (win_table)
/// R3-VERG: NB 26 only when built with the compile-time env R3_NB26=1 (default 27 = v3).
/// R6-PORT799: compile-time `R6_NB=<2 digits>` overrides. R9: NB 25 is the 799 default; `R3_NB26` (set at compile
/// time) restores the inherited 26 / 27 choice.
pub const NB: usize = match option_env!("R6_NB") {
    Some(t) => { let c = t.as_bytes(); ((c[0] - b'0') as usize) * 10 + (c[1] - b'0') as usize }
    None => match option_env!("R3_NB26") { None => 25, v => if r3_env1(v) { 26 } else { 27 } },
};
const fn r3_env1(v: Option<&str>) -> bool {
    match v { Some(t) => { let c = t.as_bytes(); c.len() == 1 && c[0] == b'1' } None => false }
}
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
    rev_funnel_k(b, u, ring, s, act, fwd, false)
}
/// `keep_s4` (denorm only, FUSE-S4): the reversed list stops before its last reversal Rev(c_k) under s[k-1] and the
/// erase of s[k-1], which is left live.
fn rev_funnel_k(b: &mut B, u: &GreedyFrog, ring: &[QubitId], s: &[QubitId], act: Option<QubitId>, fwd: bool,
                keep_s4: bool) {
    let k = R_BITS;
    let c = |j: usize| NB - 1 + (1usize << j) - 1;
    // FUNNEL-THERMO depth h: the top h slack bits come from the thermometer (chain to t_(32 - 2^(4-h)), needing
    // 29 / 27 / 23 lanes for h = 4 / 3 / 2: -11 / -10 / -7 T against variant A); the rest runs variant A's frame steps
    let h = if fwd && act.is_none() && funnel_thermo() {
        let r = u.room(b);
        if r >= 29 { 4 } else if r >= 27 { 3 } else if r >= 23 { 2 } else { 0 }
    } else { 0 };
    if cfg!(test) && fwd && std::env::var_os("M2_LOG").is_some() { eprintln!("M2LOG thermo h {h}"); }
    let mut ops: Vec<FOp> = Vec::with_capacity(160);
    let jtop = if h > 0 { k - h } else { k - 1 };
    if h > 0 {
        // g_i (i >= k - h) into s[i] from t_j = [ring lanes 0..j zero], j = 1..tmax (t_1 = !ring[0] in place)
        let tmax = (1usize << k) - (1usize << (k - h));
        let anc = b.alloc_n(tmax - 1);
        b.x(ring[0]);
        let bitof = |j: usize| j.trailing_zeros() as usize;
        if bitof(1) >= k - h {
            b.cx(ring[0], s[0]);
        }
        let prev = |j: usize| if j == 2 { ring[0] } else { anc[j - 3] };
        for j in 2..=tmax {
            b.x(ring[j - 1]);
            b.and_c(prev(j), ring[j - 1], anc[j - 2]);
            b.x(ring[j - 1]);
            if bitof(j) >= k - h {
                b.cx(anc[j - 2], s[bitof(j)]);
            }
        }
        for j in (2..=tmax).rev() {
            b.x(ring[j - 1]);
            b.and_u(prev(j), ring[j - 1], anc[j - 2]);
            b.x(ring[j - 1]);
        }
        b.x(ring[0]);
        b.free_n(&anc);
        // Rev(c_j) under g_(j-1) for j = k .. k - h + 1, then g -> s on the top h bits
        for j in (k - h + 1..=k).rev() {
            let cj = c(j);
            for i in 0..(cj + 1) / 2 {
                ops.push(FOp::Sw(s[j - 1], i, cj - i));
            }
        }
        for i in (k - h..k - 1).rev() {
            if !(i == k - h && m2_break(5)) {
                ops.push(FOp::Cx(s[i + 1], s[i]));
            }
        }
    } else {
        // step k: s_(k-1) = [lanes 0..2^(k-1) zero], Rev(c_k) under s_(k-1)
        ops.push(FOp::Test(k - 1));
        let ck = c(k);
        for i in 0..(ck + 1) / 2 {
            ops.push(FOp::Sw(s[k - 1], i, ck - i));
        }
    }
    // steps j = jtop..1: Rev(c_j) under s_j ^ s_(j-1); the first 2^(j-1) pairs are split around the test of s_(j-1)
    for j in (1..=jtop).rev() {
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
            let l = lits(j);
            let need = l.len().saturating_sub(2);
            if r6_mix(u) && u.room(b) < need && (fwd || u.room(b) + efe_slack() < need) {
                // R6_MIX: the funnel's flags s[0..j) are |0> while s[j] is tested (tests run from high j to low j), so
                // they are the clean part of the AND's chain, topped up from the room
                zero_probe(b, &s[..j]);
                if !fwd && j >= 1 && !b.recording() && super::mask::borrowed().len() >= l.len() {
                    // the erase: measured, its phase on the clean chain s[0..j) then the borrowed-lane phase form
                    let r8 = super::arith::r8_cc() && j < l.len() - 2;
                    if r8 { zero_probe(b, &s[..j]); }
                    erase_mbu(b, s[j], |b| {
                        // R8-ROOM0 R8_CC: the conditionally clean form on the clean chain s[0..j)
                        if r8 {
                            // R8_CC2: the room inside the repair (EFREE frees s[j]) tops up the clean chain
                            let extra = if r8_cc2() { b.alloc_n(p2_room(b).min(l.len() - 3 - j)) } else { vec![] };
                            let cl: Vec<QubitId> = s[..j].iter().chain(&extra).copied().collect();
                            super::arith::and_cc(b, &l, None, &cl, &super::mask::borrowed());
                            b.free_n(&extra);
                            return;
                        }
                        let r = j.min(l.len() - 2);
                        let anc = &s[..r];
                        for &(q, ng) in &l[..r + 1] { if ng { b.x(q); } }
                        b.and_c(l[0].0, l[1].0, anc[0]);
                        for i in 2..=r { b.and_c(anc[i - 2], l[i].0, anc[i - 1]); }
                        for &(q, ng) in &l[..r + 1] { if ng { b.x(q); } }
                        let mut rest = vec![(anc[r - 1], false)];
                        rest.extend_from_slice(&l[r + 1..]);
                        phase_and(b, &rest);
                        for &(q, ng) in &l[..r + 1] { if ng { b.x(q); } }
                        for i in (2..=r).rev() { b.and_u(anc[i - 2], l[i].0, anc[i - 1]); }
                        b.and_u(l[0].0, l[1].0, anc[0]);
                        for &(q, ng) in &l[..r + 1] { if ng { b.x(q); } }
                    });
                } else {
                let extra = b.alloc_n(u.room(b).min(need.saturating_sub(j)));
                let clean: Vec<QubitId> = s[..j].iter().chain(&extra).copied().collect();
                super::arith::and_mixed_on(b, &l, s[j], &clean, &u.dirty);
                b.free_n(&extra);
                }
            } else if fwd { and_auto(b, u, &l, s[j]) } else { erase_and(b, u, s[j], &l) }
        }
    };
    if fwd {
        for op in &ops {
            emit(b, op);
        }
    } else {
        // FUSE-S4: ops[0] = Test(k-1), ops[1..=(c_k+1)/2] = Rev(c_k) under s[k-1] (variant A's head; denorm has h = 0)
        let skip = if keep_s4 { 1 + (c(k) + 1) / 2 } else { 0 };
        assert!(!keep_s4 || (matches!(ops[0], FOp::Test(j) if j == k - 1) && h == 0));
        for op in ops[skip..].iter().rev() {
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
    /// R5_PRE4: the masked RowTmp with its prefix lane 4 unbound (NOQ) until the sweep
    fn alloc_p4(b: &mut B, pf3: bool, noy: bool, nog: bool) -> RowTmp {
        let (s0, g) = (b.alloc(), if nog { NOQ } else { b.alloc() });
        let y = if noy { NOQ } else { b.alloc() };
        let f = b.alloc();
        let mut pre = b.alloc_n(if pf3 { 3 } else { 4 });
        while pre.len() < R_BITS { pre.push(NOQ); }
        let m = Masked { f, t: g, gf: f, chain: vec![], pre, c0: if b792_cz() { NOQ } else { b.alloc() } };
        RowTmp { s0, g, f: m.c0, y, jl: m.pre[..R_BITS].to_vec(), m: Some(m) }
    }
    /// PARK-SPLIT: the rows' lanes only (s0, carry-in f, zero source y); the sweep's g and jl are taken by `attach`.
    /// `noy` (R14 läckBobby W): y left unbound (NOQ)
    fn alloc_slim(b: &mut B, noy: bool, nof: bool, s0h: Option<QubitId>) -> RowTmp {
        // b792 S0Y: s0 is hosted on a caller-owned |0> lane (no alloc)
        let s0 = match s0h { Some(q) => q, None => b.alloc() };
        let f = if nof { NOQ } else { b.alloc() };
        let y = if noy { NOQ } else { b.alloc() };
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
        // b792 S0Y: a hosted s0 (NOQ here) is released by its owner
        if self.s0 != NOQ { b.free(self.s0); }
        if self.y != NOQ { b.free(self.y); }
        match self.m {
            // the mask scratch's AND temp is g
            Some(m) => m.free(b),
            None => {
                if self.g != NOQ {
                    b.free(self.g);
                }
                if self.f != NOQ { b.free(self.f); }
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
thread_local! {
    /// R10_RBL: LA's sign lane waits for its re-binding until the undo rows are done
    static R10LA: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R10_RBL2 (claude-r8, 797): LA lanes 5..8 whose re-bind is deferred to the end of the undo rows
    static R10LA2: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) };
    /// R10_SH2: the undo rows of this slot run the 3-lane retained prefix
    static R10S2: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R10_RBY: Y[W-1] waits for its re-binding until the undo rows are done
    static R10YT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R10_X0: the undo rows of this (plain, act-constant) slot run without the X[0] lane: a pool lane set to 1 stands
    /// for it
    static R10X0: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// FIXX0: (Z, sX[4]) while an R10_X0 undo-rows pass runs on a FIXX0 slot: the stand-in lane is 1 ^ (Z & sX[4])
    static FX0P: std::cell::Cell<Option<(QubitId, QubitId)>> = const { std::cell::Cell::new(None) };
    /// FIXX0: op index right after this inverse slot's X funnel (start of the fail-closed scan)
    static FX0_FUN: std::cell::Cell<usize> = const { std::cell::Cell::new(usize::MAX) };
    /// FIXX0: a park is open (released, not yet re-bound); checked at every inverse slot's X0-HOST decision
    static FX0_OPEN: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// R11_LA5 (fable, 797): the offset c by which LA holds u'' = u' + c while the masked rows run (0: the parent's u')
    static R11C: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

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
/// I4-ONCE PDW-0 pricing probe (dev only, `I4_PDW0_PRICE=1`; inert when unset; NOT functional: counts only): the
/// rows' down pass takes a run-start write gate (stand-in lane `par`) and the slot's unrows are not played.
fn pdw0_price() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var_os("I4_PDW0_PRICE").is_some());
    *E
}
/// b792w5 P12X: X[0]'s (constant 1) re-bind after the undo rows is deferred to the denorm funnel's start (dev env B792_P12X=1)
fn rr_mode(m: &str) -> bool { std::env::var("RR_MODE").map_or(false, |v| v == m) }
fn b792_rr2_slot() -> bool { (super::B792_RR2 || r3_flag("B792_RR2")) && (203..=232).contains(&p3_cur_slot()) }
fn b792_rr() -> bool {
    let s = p3_cur_slot();
    let ov = std::env::var("RR_SLOTS").ok().and_then(|v| { let (a, c) = v.split_once('-')?; Some((a.parse::<usize>().ok()?, c.parse::<usize>().ok()?)) });
    match ov {
        Some((a, c)) => (super::B792_RR || r3_flag("B792_RR") || b792_rr2_slot()) && (a..=c).contains(&s),
        None => ((super::B792_RR || r3_flag("B792_RR")) && s <= 202) || b792_rr2_slot(),
    }
}
/// B792_CZERO (B792-CZERO): the masked slots' carry wire c0 is a borrowed dirty dy lane; every row conjugates its t and s lanes by e = d ^ m (the ladders are self-dual).
fn b792_cz() -> bool {
    let s = p3_cur_slot();
    let ov = std::env::var("CZ_SLOTS").ok().and_then(|v| { let (a, c) = v.split_once('-')?; Some((a.parse::<usize>().ok()?, c.parse::<usize>().ok()?)) });
    let (lo, hi) = ov.unwrap_or((0, 39));
    (super::B792_CZERO || r3_flag("B792_CZERO")) && (lo..=hi).contains(&s)
}
/// negative controls for the gate tests only (B792CZ_BREAK=k): 1 drops the opening conjugation of every row, 2 the masked-fold hand-lane fix-up, 3 the plain-row closing conjugation, 4 the no-g plain row's top-lane fix-up
fn cz_break(k: u32) -> bool { cfg!(test) && std::env::var("B792CZ_BREAK").map_or(false, |v| v.trim() == k.to_string()) }
fn b792_rr_break(tag: &str) -> bool { cfg!(test) && std::env::var("B792_BREAK").map_or(false, |v| v.trim() == tag) }
fn b792_p12x() -> bool { super::B792_P12X || r3_flag("B792_P12X") }
fn i4_gate(u: &GreedyFrog) -> QubitId { if pdw0_price() { u.par } else { ALWAYS } }
fn division_rows(b: &mut B, u: &GreedyFrog, w: &Win, rt: &RowTmp, pool: &[QubitId], parked: bool, top: usize,
                 partial: Option<usize>, mut roll: RowRoll) {
    let masked_row = |j: usize| !parked && w.mx < NB - j + 1;
    // ROW-Y: plain rows take their top lane's sign-extension source m from the sign lane itself (or the constant 1)
    let rowy = row_y(rt);
    let sg = u.la[LB_BITS - 1];
    // B792_CZERO: the carry wire is a borrowed dirty lane (value d), restored by every row
    let cz = b792_cz() && rt.m.is_some();
    assert!(!cz || rt.f == NOQ, "B792_CZERO: the RowTmp lane c0 must be unbound on a CZ slot");
    let c0q: QubitId = if cz { *u.dirty.last().expect("B792_CZERO: a borrowed dy lane") } else { rt.f };
    // PARTIAL-PARK: the flag entering a row's masked lanes is big_{max(j, c)}, c = NB - lo_p
    let pc = partial.map(|lo_p| NB - lo_p);
    // R11_LA5: LA holds u'' = u' + c11 (c11 = 0: the parent's u'); the masked rows' constants and matched values shift
    // by c11, and the decoder writes nothing at lanes whose matched value is >= 32 (a negative u'' reads as >= 32)
    let c11 = R11C.with(|c| c.get());
    assert!(c11 == 0 || (!parked && partial.is_none() && rt.m.is_some() && c11 <= 31), "R11_LA5 row shape");
    if c11 > 0 { super::mask::TVMAX.with(|t| t.set(31)); }
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
    if masked_row(0) && pc.is_none() && c11 == 0 {
        b.cx(sg, rt.m.as_ref().expect("masked row needs mask scratch").f);
    } else if masked_row(0) && pc.is_none() {
        // R11_LA5: big_0 = [u' < 0] = sign | ![u''_5 >= c11] (the PARTIAL-PARK big_c form)
        let big = rt.m.as_ref().expect("masked row needs mask scratch").f;
        if pool.len() >= 5 {
            let (chain, ge) = (&pool[..4], pool[4]);
            super::mask::ge_const(b, &u.la[..5], c11 as isize, ge, chain);
            b.x(sg);
            b.ccx(sg, ge, big);
            b.x(sg);
            super::mask::ge_const(b, &u.la[..5], c11 as isize, ge, chain);
        } else {
            super::mask::ge_const_dirty_gated(b, &u.la[..5], c11 as isize, big, &[(sg, true)], &u.dirty);
        }
        b.x(big);
    }
    // R5-FIT799 R5_MPOOL (masked RowTmp, no partial park): the plain rows of a masked slot run after its last masked
    // row, where the mask scratch (f cleared by the comparator, its AND temp, the decoder prefix) is |0>: those lanes
    // lead the plain rows' carry pool
    let mpool: Vec<QubitId> = match rt.m.as_ref() {
        Some(m) if partial.is_none() && R5MP.with(|c| c.get()) => {
            let mut v: Vec<QubitId> = m.pre.iter().copied().filter(|&q| q != NOQ).collect();
            let fd = R5FD.with(|c| c.get());
            if !R5MY.with(|c| c.get()) && !fd && m.t != NOQ { v.push(m.t); }
            if !fd { v.push(m.f); }
            let rest: Vec<QubitId> = pool.iter().copied().filter(|q| !v.contains(q)).collect();
            v.extend(rest);
            v
        }
        _ => pool.to_vec(),
    };
    // R5-FIT799 R5_MROWY (undo rows of masked slots, TERM-NC): the masked rows' top cell takes its source m from the
    // sign lane (mask.rs TOPM), the plain rows take the idle mask AND temp as their zero source: RowTmp's y is unused
    let mrowy = R5MY.with(|c| c.get()) && term_nc() && rt.m.is_some() && partial.is_none();
    // R5-FIT799 R5_FOLD (undo rows of masked slots): every masked row's top two cells (zero source m, divisor MSB X[0] = 1,
    // flipped to !m) are always active and are written by hand between the ladder's up and down passes on the
    // ladder's carry wire, so neither the zero source nor X[0] is a lane; the plain rows take the idle mask AND temp as
    // their zero source and the cleared mask flag, set to 1, as X[0]
    let fold = R5FD.with(|c| c.get()) && rt.m.is_some() && partial.is_none();
    let mut x0s_on = false;
    // R10_X0 (claude-r8): X[0] = 1 is not bound here: the pool's last lane, set to 1, is the rows' X[0] source
    let r10x0 = R10X0.with(|c| c.get());
    let m1close = std::env::var("M1_ROWF").ok().as_deref() == Some("close");
    // R14 misc94 x2: undo rows with their X[0] cell folded by hand (see the ROW-Y branch): R10_X0 takes no stand-in lane
    let m94x = M94X.with(|c| c.get());
    assert!(!m94x || (matches!(roll, RowRoll::Rev(_) | RowRoll::No) && rowy && row_f() && m1close && rt.m.is_none() && !parked
                      && partial.is_none()), "R14 misc94 x2: row shape");
    assert!(!r10x0 || (rt.m.is_none() && !parked && partial.is_none() && pool.len() >= if m94x { !b792_rr() as usize } else if m1close { 2 - b792_rr() as usize } else { 3 }), "R10_X0 row shape");
    let x0p = if r10x0 && !m94x { pool[pool.len() - 1] } else { NOQ };
    let (pool, mpool): (&[QubitId], Vec<QubitId>) = if r10x0 && !m94x { (&pool[..pool.len() - 1], mpool[..mpool.len() - 1].to_vec()) } else { (pool, mpool) };
    if r10x0 && !m94x { b.x(x0p); }
    // FIXX0: on a FIXX0 slot the stand-in is the true X[0] = 1 ^ (Z & sX[4]) (Z parks X[0]'s bit there)
    // b793b X2FX: on the FIXX0 slots 188-202 the folded X[0] cell carries e = Z & sX[4] (X[0] = 1 ^ e): the cell's source is sign ^ e
    let fx0e = if m94x { FX0P.with(|c| c.get()) } else { None };
    let fx0p = if r10x0 && !m94x { FX0P.with(|c| c.get()) } else { None };
    if let Some((z, s4)) = fx0p { b.ccx(z, s4, x0p); }
    for j in 0..w.k {
        let pool: &[QubitId] = if masked_row(j) { pool } else { &mpool };
        let lo = j as isize - 1;
        // PARTIAL-PARK rows stop at lane j + top - 1 (divisor lanes >= top are zero on every non-failing shot)
        let parked = parked || (partial.is_some() && j + top < NB);
        // Parked rows with a divisor bound (top < NB): divisor lanes >= top are zero on every non-failing shot, so rem
        // lanes i >= j + top add a zero source: with the flipped source and carry-in m they stay unchanged and carry m
        // out, which is the ladder's own carry-in c0 = m. The row's ladder therefore stops at lane j + top - 1.
        let hi_i = if parked { (j + top).min(NB) } else { NB } as isize;
        let t: Vec<QubitId> = (lo..hi_i).rev().map(|i| rt.rem(u, i)).collect();
        let zsrc = if !mrowy && !fold { rt.zero() } else if masked_row(j) { NOQ } else { rt.m.as_ref().unwrap().t };
        let x0src = if r10x0 { x0p } else if fold && masked_row(j) { NOQ } else if fold { rt.m.as_ref().unwrap().f } else { u.x[0] };
        if fold && !masked_row(j) && !x0s_on {
            // the mask flag is |0> after the last masked row: it stands for X[0] = 1 in the plain rows
            if !r5_break("x0") { b.x(x0src); }
            x0s_on = true;
        }
        let mut s: Vec<QubitId> = (lo..hi_i).rev()
            .map(|i| if i > j as isize { u.x[i as usize - j] } else if i == j as isize { x0src } else { zsrc }).collect();
        // b793b F6: the masked slots' plain rows without the zero-source lane (the AND temp is gone): the top lane's source m is not a lane
        let nog_plain = fold && !masked_row(j) && rt.m.as_ref().map_or(false, |m| m.t == NOQ);
        if nog_plain {
            assert_eq!(s.pop(), Some(NOQ), "b793 F6: the zero-source cell is the top lane's");
        }
        if rowy {
            // the zero source is the last (top) lane's only: it leaves the ladder (written by hand below)
            assert_eq!(s.pop(), Some(rt.zero()));
        }
        if m94x {
            // R14 misc94 x2: the X[0] cell (source X[0] = 1: R10_X0's constant, or the bound X[0]) leaves the ladder too
            let q = s.pop();
            assert!(q == Some(NOQ) || q == Some(u.x[0]), "R14 misc94 x2: the cell below the top is not X[0]'s");
        }
        // m = 1 subtracts: source ^= m, carry-in m. Row 0 always subtracts; row j >= 1 subtracts where lane j - 2 is 0.
        let sign = if j == 0 { None } else { Some(rt.rem(u, j as isize - 2)) };
        // ROW-F: the carry-in m comes from the sign lane itself (X-flipped: !sign) or, in row 0, from a pool lane set to 1
        let rowf = rowy && row_f();
        let c0f = c0q;
        let flip = |b: &mut B| {
            for &q in s.iter().chain((!rowf && !cz).then_some(&c0f)).filter(|&&q| q != NOQ) {
                if let Some(sg) = sign {
                    b.cx(sg, q);
                }
                b.x(q);
            }
        };
        if std::env::var_os("I4_ROWLANES").is_some() && !matches!(roll, RowRoll::Rev(_)) {
            // I4-ONCE pricing log (inert when unset): source lanes of this row that carry a divisor bit (not the zero source)
            let ns = s.iter().filter(|&&q| q != rt.zero()).count();
            eprintln!("I4ROW slot {} j {} t {} src {} masked {}", w.slot, j, t.len(), ns, masked_row(j) as u8);
        }
        flip(b);
        // SYM-R-25 ROUND-THE-DIVISOR: carry-in ^= the top dropped divisor bit X[NB - j] (window-plain rows j >= 1; the
        // full-width ladder: hi_i == NB). The carry-in lane is the sign lane on ROW-F rows, f otherwise; read-only in
        // the ladder, restored before the second flip.
        let rb = (round_div() && j >= 1 && w.mx >= NB - j + 1 && hi_i == NB as isize).then(|| u.x[NB - j]);
        let cin_lane = match (rowf, sign) { (true, Some(sg)) => sg, _ => c0f };
        if let Some(r) = rb {
            assert!(!masked_row(j) && !s.contains(&r));
            if !cz { b.cx(r, cin_lane); }
        }
        // B792_CZERO: x = c0 -> e = d ^ m ^ r (r: the SYM-R-25 dropped divisor bit), x -> e is its own inverse
        let cz_e = |b: &mut B| {
            if let Some(sg_) = sign { b.cx(sg_, c0q); }
            b.x(c0q);
            if let Some(r) = rb { b.cx(r, c0q); }
        };
        let cz_fan = |b: &mut B| {
            for &q in t.iter().chain(s.iter()).filter(|&&q| q != NOQ) { b.cx(c0q, q); }
        };
        if cz {
            assert!(!round_break(2));
            // the dirty carry wire must be disjoint from every operand of the row (t, s, sign, pool, the decoder's v / prefix, the mask lanes, the dropped divisor bit)
            let mm = rt.m.as_ref().expect("masked slot");
            assert!(!t.contains(&c0q) && !s.contains(&c0q) && sign != Some(c0q) && rb != Some(c0q) && !pool.contains(&c0q) && !u.la.contains(&c0q)
                && !mm.pre.contains(&c0q) && mm.f != c0q && mm.t != c0q && !mm.chain.contains(&c0q) && rt.s0 != c0q && rt.g != c0q && rt.y != c0q && !rt.jl.contains(&c0q),
                "B792_CZERO: the dirty carry wire collides with a row operand");
            cz_e(b); if !cz_break(1) { cz_fan(b); } cz_e(b);
        }
        let rolled = match &roll {
            RowRoll::Fwd(_) => !rowy && !masked_row(j) && pool.len() >= 2 && pool.len() < t.len(),
            RowRoll::Rev(recs) => !rowy && !recs[j].rc.is_empty(),
            RowRoll::No => false,
        };
        assert!(!(cz && (rolled || rowy)), "B792_CZERO: rolled / ROW-Y rows are not conjugated");
        if rolled && matches!(roll, RowRoll::Fwd(_)) {
            // ROLL-ROWS forward: the row's add as the inverse of its inverted twin (carries of the pre-row remainder,
            // formed on the written lane: the I-frame is the complement), carry-in m held on c0, two pool lanes rolling
            let sc = Mscr { f: c0q, t: c0q, gf: c0q, chain: vec![] };
            let ld = Lad { t: &t, s: &s, c0: c0q, srcs: &[], f0: false, cmpl: true, sc: &sc, g: &[] };
            let rec = super::mask::roll_fwd(b, &ld, ALWAYS, ALWAYS, false, term_nc(), &pool[..2], None);
            if let RowRoll::Fwd(v) = &mut roll { v.push(rec); }
        } else if nog_plain {
            // b793b F6: the ladder over every lane but the top (the MSB: rem(j - 1)); the top lane's sum t ^= c ^ m, m = !sign (row 0: 1), is
            // written by hand between the up and the down pass (its carry is discarded mod 2^n, as TERM-NC), so no lane holds the zero source
            assert!(!rolled, "b793 F6: a rolled plain row");
            if let RowRoll::Fwd(v) = &mut roll { v.push(RollRec::default()); }
            let n = t.len();
            assert!(n >= 2 && s.len() == n - 1, "b793 F6: plain row shape");
            if std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE f6plain slot {} row {}", p3_cur_slot(), j); }
            let tt = t[n - 1];
            let sc = Mscr { f: c0q, t: c0q, gf: c0q, chain: vec![] };
            let ld = Lad { t: &t[..n - 1], s: &s, c0: c0q, srcs: &[], f0: false, cmpl: false, sc: &sc,
                           g: &pool[..pool.len().min(n - 1)] };
            let ru = super::mask::mup_mid(b, &ld);
            b.play(&ru, false);
            b.cx(top_carry(&ld), tt);
            if let Some(sgl) = sign { if !b793b_break("f63") { b.cx(sgl, tt); } }
            if !b793b_break("f64") { b.x(tt); }
            let rd = super::mask::mdown_mid(b, &ld, Some(i4_gate(u)));
            b.play(&rd, false);
            // B792_CZERO: closing conjugation; the top lane's written sum used the carry (conjugated) and constants (not): tt ^= e
            if cz { cz_e(b); cz_fan(b); if !cz_break(4) { b.cx(c0q, tt); } cz_e(b); }
        } else if rowy {
            // ROW-Y rows are not rolled (y / f are lent to the pool; INTEGRATOR: ROW-Y wins on plain rows)
            if let RowRoll::Fwd(v) = &mut roll { v.push(RollRec::default()); }
            // ROW-Y: the ladder over every lane but the top, then the top lane's sum t ^= m ^ c (its carry is discarded
            // mod 2^n, as TERM-NC), m = !sign (row 0: 1); the lane that was the zero source is lent to the pool
            assert!(!masked_row(j) && (!pool.is_empty() || b792_rr()), "ROW-Y: plain pooled rows only");
            let n = t.len();
            // R14 misc94 x2: the ladder stops below the X[0] cell (lane n - 2), as it stops below the top lane
            let nl = if m94x { n - 2 } else { n - 1 };
            assert!(!m94x || nl >= 1, "R14 misc94 x2: a row needs a ladder cell below the X[0] cell");
            // ROW-F: c0 = the sign lane X-flipped to m = !sign (rows j >= 1), or a pool lane X-flipped to m = 1 (row 0);
            // the pool keeps a lane for ladder lane 0, so the carry-in is only read and holds m throughout
            let (c0, gp): (QubitId, &[QubitId]) = match (rowf, sign) {
                (false, _) => (c0q, pool),
                (true, Some(sg)) => (sg, pool),
                (true, None) if (pool.is_empty() || rr_mode("p0")) && b792_rr() => (*u.dirty.last().unwrap(), &pool[..]),
                (true, None) => (pool[pool.len() - 1], &pool[..pool.len() - 1]),
            };
            // b792 RR: m94x undo rows with an empty pool (the M1 lane is not lent): row 0 takes its carry-in from a borrowed dirty dy lane d (value v) and
            // adds 1 - v back at the end; rows j >= 1 run lane 0 as an in-place MAJ (no AND lane), which XORs the lane-0 source into c0, so every read of
            // c0 (= m) is moved before the up pass (see the reordered hand block)
            let p12d = b792_rr() && rowf && sign.is_none() && (pool.is_empty() || rr_mode("p0"));
            let (gp, rr_re): (&[QubitId], bool) = if b792_rr() && rowf && sign.is_some() && (gp.is_empty() || rr_mode("re")) { (&[][..], true) } else { (gp, false) };
            let _ = {
                ()
            };
            // m1-shell diagnostic (inert unless M1_ROWF is set): where ROW-F row 0 meets a one-lane pool.
            // M1_ROWF=borrow: c0 is a fresh lane over the cap (the pool keeps its lane); M1_ROWF=close: c0 = the pool's
            // only lane, the ladder runs with no carry pool (lane 0 MAJ/UMA) and the top lane's m = 1 is an X.
            let m1 = std::env::var("M1_ROWF").ok();
            let m1_fire = rowf && sign.is_none() && gp.is_empty() && m1.is_some() && !p12d;
            let mut m1_lane = NOQ;
            let mut m1_close = false;
            let (c0, gp): (QubitId, &[QubitId]) = if m1_fire {
                let dir = match &roll { RowRoll::Fwd(_) => "fwd", RowRoll::Rev(_) => "rev", RowRoll::No => "no" };
                eprintln!("M1ROWF div {} sect {} slot {} dir {} pool {} n {} live {} mode {}",
                          M1DIV.with(|c| c.get()), super::builder::i5::SECT.with(|c| c.get()),
                          super::builder::i5::SLOT.with(|c| c.get()), dir, pool.len(), t.len(), b.live,
                          m1.as_deref().unwrap_or(""));
                if m1.as_deref() == Some("close") { m1_close = true; (c0, gp) }
                else { panic!("M1_ROWF=borrow: the call site should have lent the lane"); }
            } else { (c0, gp) };
            assert!(!rowf || !gp.is_empty() || m1_close || p12d || rr_re, "ROW-F: lane 0 needs a pool lane");
            if rowf && !p12d { b.x(c0); }
            let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
            let tt = t[n - 1];
            // ROWY-ROLL forward: the short-pool ROW-Y row as the inverse of its inverted twin (I-frame: the complement)
            // R14 misc94 x2: on the slots whose undo rows fold the X[0] cell, the forward rows are not rolled (the undo
            // replays no carry receipts there)
            // b792 RR2: on i.rows_rev 203-232 the forward rows are not rolled: the undo's row-0 dirty carry changes the carries, so a replayed roll receipt (z_if on a carry wire) would be wrong
            let yroll = rowy_roll() && !M94NR.with(|c| c.get()) && !(b792_rr2_slot() && !b792_rr_break("rr5")) && matches!(roll, RowRoll::Fwd(_)) && gp.len() >= 2 && gp.len() < n - 1;
            let yrev = match &roll { RowRoll::Rev(recs) => !recs[j].rc.is_empty(), _ => false };
            if yroll {
                let ldr = Lad { t: &t[..n - 1], s: &s, c0, srcs: &[], f0: false, cmpl: true, sc: &sc, g: &[] };
                let rec = super::mask::roll_fwd(b, &ldr, ALWAYS, ALWAYS, false, false, &gp[..2], Some((ALWAYS, tt)));
                if let RowRoll::Fwd(v) = &mut roll { v.pop(); v.push(rec); }
            }
            assert!(!m94x || (!yrev && !yroll), "R14 misc94 x2: a rolled row");
            let ld = Lad { t: &t[..nl], s: &s, c0, srcs: &[], f0: false, cmpl: false, sc: &sc,
                           g: &gp[..gp.len().min(nl)] };
            // b792 RR reorder (rows j >= 1, no pool lane): every term that reads m = c0 is applied before the up pass, with c0 still = m
            //   tt ^= tx m ^ tx ^ m ; tx ^= m ;  after the up pass: tt ^= (tx ^ m) c ^ c ; tx ^= c ^ 1   (= the original A..F sequence)
            if rr_re && !m94x {
                // non-folded rows: the only read of m after the ladder is the top lane's sign-extension term tt ^= m: moved before the up pass
                if let Some(r) = rb { b.cx(r, c0); }
                if !b792_rr_break("rr4") { b.cx(c0, t[n - 1]); }
                if let Some(r) = rb { b.cx(r, c0); }
            }
            if rr_re && m94x {
                let (tx, tt) = (t[n - 2], t[n - 1]);
                // SYM-R-25: c0 = m ^ b here; read m through c0 ^ b
                if let Some(r) = rb { assert!(r != tx && r != tt && r != c0); b.cx(r, c0); }
                if !b792_rr_break("rr1") { b.ccx(c0, tx, tt); }
                b.cx(tx, tt);
                b.cx(c0, tt);
                if let Some((z, s4)) = fx0e { if !b793b_break("x2e") { super::mask::ccc_dirty(b, z, s4, tx, tt); } }
                b.cx(c0, tx);
                if let Some(r) = rb { b.cx(r, c0); }
            }
            let ru = if yroll { vec![] } else { super::mask::mup_mid(b, &ld) };
            b.play(&ru, false);
            if m94x {
                // R14 misc94 "DonRwetter" x2: the X[0] cell by hand. Its source is the constant X[0] = 1 after the flip
                // (q ^= sign, q ^= 1): sigma = sign = !m (rows j >= 1) or 0 (row 0, m = 1). With a = its lane and c = the
                // ladder's carry into it, the top lane gets the cell's carry out maj(a, sigma, c) = a c ^ sigma (a ^ c)
                // (the parent's tt ^= c of the cell above), and a becomes the sum a ^ sigma ^ c. The ladder's down pass
                // does not read a; c is only read; c0 holds m (^ b with SYM-R-25) on ROW-F rows j >= 1.
                let tx = t[n - 2];
                let c = top_carry(&ld);
                assert!(c != tx && c != tt && c != c0 && tx != c0 && tt != c0, "R14 misc94 x2: lane aliasing");
                let brk = r14m_break("x");
                match sign {
                    None => {
                        b.ccx(tx, c, tt);
                        if !brk { b.cx(c, tx); }
                        if let Some((z, s4)) = fx0e {
                            // source e: carry out gets e (a ^ c) (tx = a ^ c now), the sum a ^ e
                            if !b793b_break("x2e") { super::mask::ccc_dirty(b, z, s4, tx, tt); b.ccx(z, s4, tx); }
                        }
                    }
                    Some(_) if rr_re => {
                        // b792 RR: the m-reads were applied before the up pass (tx now holds tx ^ m)
                        b.ccx(tx, c, tt);
                        if !b792_rr_break("rr2") { b.cx(c, tt); }
                        b.cx(c, tx);
                        b.x(tx);
                        if let Some((z, s4)) = fx0e {
                            if !b793b_break("x2e") { super::mask::ccc_dirty(b, z, s4, c, tt); b.ccx(z, s4, tx); }
                        }
                    }
                    Some(_) => {
                        assert!(rowf);
                        if let Some(r) = rb { assert!(r != c && r != tx && r != tt && r != c0); b.cx(r, c0); }
                        if !r14m_break("xc") { b.ccx(tx, c, tt); }
                        b.cx(c, tx);
                        b.x(c0);
                        if !r14m_break("xs") { b.ccx(c0, tx, tt); }
                        b.x(c0);
                        if let Some((z, s4)) = fx0e {
                            // source sign ^ e: the e part of the carry out is e (a ^ c), tx = a ^ c here; the sum gets e
                            if !b793b_break("x2e") { super::mask::ccc_dirty(b, z, s4, tx, tt); b.ccx(z, s4, tx); }
                        }
                        if !brk { b.cx(c0, tx); }
                        b.x(tx);
                        if let Some(r) = rb { b.cx(r, c0); }
                    }
                }
            } else if !yroll { b.cx(top_carry(&ld), tt); }
            // negative control for the gate tests only: P3_BREAK=7 drops the sign term of the top lane
            let brk = cfg!(test) && std::env::var("P3_BREAK").map_or(false, |x| x.trim() == "7");
            if rowf {
                if m1_close || p12d { b.x(tt); } else if rr_re { } else if !brk { b.cx(c0, tt); }
                // SYM-R-25: c0 holds m ^ b; the top lane's sign-extension term is m
                if let (Some(r), false) = (rb, round_break(1)) { if !rr_re { b.cx(r, tt); } }
            } else {
                if let Some(sg) = sign {
                    if !brk { b.cx(sg, tt); }
                }
                b.x(tt);
            }
            let rd = match &roll {
                _ if yroll => vec![],
                RowRoll::Rev(recs) if yrev => super::mask::mdown_mid_roll(b, &ld, Some(ALWAYS), &recs[j]),
                _ => super::mask::mdown_mid(b, &ld, Some(i4_gate(u))),
            };
            b.play(&rd, false);
            if rowf && !p12d { b.x(c0); }
            if p12d {
                // the row added T + S' + v (c0 = d, value v); the carry-in should be 1: add 1 - v (control !v) with inc_dirty on the other dy lanes
                if !b792_rr_break("rr3") {
                    b.x(c0);
                    let mut bor: Vec<QubitId> = u.dirty[..u.dirty.len() - 1].to_vec();
                    if bor.len() + 2 < t.len() { bor.extend(s.iter().copied().filter(|&q| q != NOQ)); }
                    super::arith::inc_dirty(b, c0, &t, &bor);
                    b.x(c0);
                }
            }
            if m1_lane != NOQ { b.free(m1_lane); }
        } else if !masked_row(j) && pool.is_empty() {
            assert!(!rolled, "ROLL-ROWS: the inverted rows pass needs a carry pool");
            if let RowRoll::Fwd(v) = &mut roll { v.push(RollRec::default()); }
            if pdw0_price() { eprintln!("I4PDW0 cuccaro row lanes {}", t.len()); }
            let ru = super::arith::up_m(b, &t, &s, c0q, false);
            b.play(&ru, false);
            let rd = super::arith::down_m(b, &t, &s, c0q, super::arith::Dm::Sum, false);
            b.play(&rd, false);
            if cz { cz_e(b); if !cz_break(3) { cz_fan(b); } cz_e(b); }
        } else if !masked_row(j) {
            // the same row with logical-AND carries on the pool's lanes (uncomputed by measurement)
            let sc = Mscr { f: c0q, t: c0q, gf: c0q, chain: vec![] };
            let ld = Lad { t: &t, s: &s, c0: c0q, srcs: &[], f0: false, cmpl: false, sc: &sc,
                           g: &pool[..pool.len().min(t.len())] };
            let nc = term_nc();
            let ru = if nc { super::mask::mup_mid_nc(b, &ld) } else { super::mask::mup_mid(b, &ld) };
            b.play(&ru, false);
            let rd = match (&roll, rolled) {
                (RowRoll::Rev(recs), true) => if nc { super::mask::mdown_mid_nc_roll(b, &ld, Some(ALWAYS), &recs[j]) }
                    else { super::mask::mdown_mid_roll(b, &ld, Some(ALWAYS), &recs[j]) },
                _ => if nc { super::mask::mdown_mid_nc(b, &ld, Some(i4_gate(u))) } else { super::mask::mdown_mid(b, &ld, Some(i4_gate(u))) },
            };
            b.play(&rd, false);
            if cz { cz_e(b); if !cz_break(3) { cz_fan(b); } cz_e(b); }
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
                // R11_LA5: the LSB lane l = u' - j = u'' - (j + c11)
                (0, t.len(), j as isize + c11 as isize, &[][..])
            };
            let p4 = R5P4.with(|c| c.get());
            let pre = if R14S5.with(|c| c.get()) { vec![] } else if R9S4.with(|c| c.get()) { m.pre[..1].to_vec() } else if R12S3.with(|c| c.get()) { m.pre[..2].to_vec() } else if R10S2.with(|c| c.get()) { m.pre[..3].to_vec() } else if R12PF3.with(|c| c.get()) { m.pre[..3].to_vec() } else if p4 { m.pre[..4].to_vec() } else { m.pre.clone() };
            if fold {
                let n = t.len();
                assert!(n >= 3 && partial.is_none() && s[n - 1] == NOQ && s[n - 2] == NOQ, "R5_FOLD row shape");
                let srcs = [Src { lo: 0, hi: n - 2, v: ubits(&u.la), a: sa, d: 1, pre, late: false }];
                let sc = m.sc();
                let ld = Lad { t: &t[..n - 2], s: &s[..n - 2], c0: c0q, srcs: &srcs, f0: false, cmpl: false, sc: &sc, g: &[] };
                let rs0 = super::mask::RSHORT.with(|c| c.replace(c.get() || p4));
                let rs2f = super::mask::RSHORT2.with(|c| c.replace(c.get() || R12PF3.with(|c| c.get())));
                let ru = super::mask::mup_mid(b, &ld);
                b.play(&ru, false);
                // carry wire x = carry into the X[0] cell; t2 = rem(j) (source !m), t1 = rem(j - 1) (source m, sum only)
                let (x, t2, t1) = (c0q, t[n - 2], t[n - 1]);
                match sign {
                    Some(sg) => {
                        // carry c3 = maj(t2, sign, x) = sign (t2 ^ x) ^ t2 x; t1 ^= m ^ c3, m = !sign; t2 ^= sign ^ x
                        b.cx(x, t2);
                        b.ccx(sg, t2, t1);
                        b.cx(x, t2);
                        b.ccx(t2, x, t1);
                        b.cx(sg, t1);
                        if !r5_break("fold") { b.x(t1); }
                        b.cx(sg, t2);
                        b.cx(x, t2);
                    }
                    None => {
                        // row 0: m = 1, X[0]'s flipped source 0: c3 = t2 x; t1 ^= 1 ^ c3; t2 ^= x
                        if !r5_break("fold0") { b.ccx(t2, x, t1); }
                        b.x(t1);
                        b.cx(x, t2);
                    }
                }
                let rd = super::mask::mdown_mid(b, &ld, Some(i4_gate(u)));
                super::mask::RSHORT.with(|c| c.set(rs0));
                super::mask::RSHORT2.with(|c| c.set(rs2f));
                b.play(&rd, false);
                // B792_CZERO: closing conjugation, then H = t2 + 2 t1 += e (1 + 2 sign) on the two hand lanes (their sources are constants / sign, not lanes)
                if cz {
                    cz_e(b); cz_fan(b);
                    let (t2c, t1c) = (t[n - 2], t[n - 1]);
                    if let Some(sg) = sign { b.cx(sg, t2c); }
                    if !cz_break(2) { b.ccx(c0q, t2c, t1c); }
                    if let Some(sg) = sign { b.cx(sg, t2c); }
                    b.cx(c0q, t2c);
                    cz_e(b);
                }
            } else {
            assert!(!cz, "B792_CZERO: non-fold masked row");
            let srcs = [Src { lo: slo, hi: shi, v: ubits(&u.la), a: sa, d: 1, pre, late: false }];
            let sc = m.sc();
            let ld = Lad { t: &t, s: &s, c0: c0q, srcs: &srcs, f0: false, cmpl: false, sc: &sc, g: gp };
            let nc = term_nc();
            let rs0 = super::mask::RSHORT.with(|c| c.replace(c.get() || p4));
            let rs2f = super::mask::RSHORT2.with(|c| c.replace(c.get() || R12PF3.with(|c| c.get())));
            assert!(!mrowy || nc, "R5_MROWY needs TERM-NC");
            if mrowy { super::mask::TOPM.with(|c| c.set(Some(sign.unwrap_or(super::mask::NO_LANE)))); }
            let ru = if nc { super::mask::mup_mid_nc(b, &ld) } else { super::mask::mup_mid(b, &ld) };
            b.play(&ru, false);
            let rd = if nc { super::mask::mdown_mid_nc(b, &ld, Some(i4_gate(u))) } else { super::mask::mdown_mid(b, &ld, Some(i4_gate(u))) };
            super::mask::TOPM.with(|c| c.set(None));
            super::mask::RSHORT.with(|c| c.set(rs0));
            super::mask::RSHORT2.with(|c| c.set(rs2f));
            b.play(&rd, false);
            }
            // the carry pool is idle in the masked rows (every lane masked): its lanes are the flag's clean chain
            // (R11_LA5: [u'' == j + c11] / [u'' >= j + c11] on the nonnegative view, the sign literal gating both)
            let jc = pc.map_or(j, |c| j.max(c)) + c11;
            assert!(jc < 32, "R11_LA5: row constant outside the 5-bit view");
            if j + 1 < w.k && masked_row(j + 1) && pc.map_or(false, |c| j + 1 <= c) {
                // partial: big_{max(j+1, c)} == big_c: unchanged
            } else if j + 1 < w.k && masked_row(j + 1) {
                let mut lits = vec![(sg, true)];
                lits.extend(eq_lits(&u.la[..5], jc));
                if pool.len() >= 4 {
                    and_into_t(b, &lits, big, &pool[..4]);
                } else if r6_mix(u) {
                    // R6_MIX: the mask's AND temp (|0> between rows) and the idle pool's lanes as the clean part of the chain
                    let mut cl: Vec<QubitId> = if m.t != NOQ { vec![m.t] } else { vec![] };
                    cl.extend_from_slice(pool);
                    if r6_break("mt") { b.x(m.t); }
                    super::arith::and_mixed_on(b, &lits, big, &cl, &u.dirty);
                    if r6_break("mt") { b.x(m.t); }
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
        if let (Some(r), false, false) = (rb, round_break(2), cz) {
            b.cx(r, cin_lane);
        }
        flip(b);
    }
    if x0s_on && !r5_break("x0") {
        b.x(rt.m.as_ref().unwrap().f);
    }
    if let Some((z, s4)) = fx0p { b.ccx(z, s4, x0p); }
    if r10x0 && !m94x { b.x(x0p); }
    if c11 > 0 { super::mask::TVMAX.with(|t| t.set(isize::MAX)); }
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
    /// R3-ROOM: LA's top lanes that hold |0> on plain-row slots from I6 (LA = u = LA + sX) to the denormalisation.
    /// LA[8]: u = 256 - mX <= 255 on every active shot (mX >= 1); a finished shot has LA = 0, so u = sX <= 31
    /// (act-live slots only with R3_LA8LIVE). R3_LATOP: also LA[k] for 2^k > lad.1 + 31 >= u (LA <= lad.1 on every
    /// shot inside the parent's LA - d window, sX <= 31), retake799's m803y bound; envelope-based like that window.
    fn r3_la_free(&self, w: &Win, act: Option<QubitId>, masked_rows: bool) -> Vec<QubitId> {
        if self.cap >= 813 || masked_rows || (act.is_some() && !r3_flag("R3_LA8LIVE")) {
            return vec![];
        }
        let mut lo = LB_BITS - 1;
        if r3_flag("R3_LATOP") {
            let ub = w.lad.1 + 31;
            let bl = (usize::BITS - ub.leading_zeros()) as usize;
            lo = lo.min(bl.max(R_BITS));
        }
        // R8-LANE799 R8_LAMX (cap < 805): u = 256 - mX <= 256 - w.mx on every active shot inside the parent's mX window
        // (plain rows need mX >= w.mx), finished shots u = sX <= 31: LA[k] for 2^k > max(256 - w.mx, 31) is |0> too.
        // Envelope-based (the mx window that already gates the plain rows).
        if below805(self.cap) && r3_flag("R8_LAMX") && w.mx <= 256 {
            let ub = (256 - w.mx).max(31);
            let bl = (usize::BITS - ub.leading_zeros()) as usize;
            // negative control for the gate tests only: R8_BREAK=lamx frees one bit below the bound
            let bl = if r8_break("lamx") { bl - 1 } else { bl };
            lo = lo.min(bl.max(R_BITS - r8_break("lamx") as usize));
        }
        // negative control for the gate tests only: R3_BREAK=1 hosts LA[5..9) on every plain-row slot (u >= 32 there)
        if cfg!(test) && r3_flag("R3_BREAK") { lo = R_BITS; }
        if B792_S255_HELD.with(|c| c.borrow().is_empty()) { self.la[lo..LB_BITS].to_vec() } else { self.la[lo..LB_BITS].iter().copied().filter(|&q| q != NOQ).collect() }
    }
    /// R5-FIT799: take lent lanes back by id where free; a lane now held by another value (rho, res, a1 = `keep`, or
    /// any lane taken while it was lent) keeps that value, and its owner register lane is re-bound to a fresh |0> lane
    /// (after every free lent lane is back, so a fresh lane never lands on a lent one). `lanes` is updated in place.
    fn r5_rebind(&mut self, b: &mut B, lanes: &mut Vec<QubitId>, rt: &mut RowTmp, lend: &mut Vec<QubitId>, keep: QubitId) {
        let mut busy: Vec<QubitId> = vec![];
        // R11_LA7 (fable, 797): on plain slots LA[7] (|0> while lent, R8_LAMX) is not taken back here even where its id
        // is free: its re-bind is deferred as R10_RBL2 defers a busy lane's (to the end of the undo rows, or past the
        // R8_IDEN open where that releases bit 7 again)
        let la7 = self.la[LB_BITS - 2];
        // (free: not taken back; busy: its holder keeps the lane, as R10_RBL2 does, here without the room gate)
        if r3_flag("R11_LA7") && rt.m.is_none() && la7 != NOQ && lanes.contains(&la7) && rt.f != la7 && rt.y != la7
            && rt.g != la7 {
            self.la[LB_BITS - 2] = NOQ;
            R10LA2.with(|c| c.borrow_mut().push(LB_BITS - 2));
            lend.retain(|&x| x != la7);
            lanes.retain(|&x| x != la7);
        }
        // b792 SLDEN8: LA[8] (|0>, plain LA <= 255), lent and free, is not taken back here on late plain slots: its re-bind waits (R10LA) past the denorm funnel
        if b792_slden8() && b792_slden() && p3_cur_slot() >= 189 && rt.m.is_none() && self.la[LB_BITS - 1] != NOQ && lanes.contains(&self.la[LB_BITS - 1])
            && self.la[LB_BITS - 1] != keep && b.is_free(self.la[LB_BITS - 1]) && rt.f != self.la[LB_BITS - 1] && rt.y != self.la[LB_BITS - 1] && rt.g != self.la[LB_BITS - 1]
            && self.y[W - 1] != self.la[LB_BITS - 1] && !R10LA.with(|c| c.get()) {
            let q8 = self.la[LB_BITS - 1];
            self.la[LB_BITS - 1] = NOQ;
            R10LA.with(|c| c.set(true));
            lend.retain(|&x| x != q8);
            lanes.retain(|&x| x != q8);
        }
        for &q in lanes.iter() {
            if q != keep && b.is_free(q) { b.acquire(q); } else if !busy.contains(&q) { busy.push(q); }
        }
        for q in busy {
            if r10("R10_DBG") == 1 {
                let who = if rt.f == q { "f" } else if rt.y == q { "y" } else if rt.g == q { "g" } else if self.y[W - 1] == q { "ytop" } else { "la" };
                let li = self.la.iter().position(|&x| x == q).map_or(-1, |i| i as isize);
                eprintln!("R10RB slot {} who {who} keep {} room {} masked {} la {li}", p3_cur_slot(), (q == keep) as u8, self.room(b), rt.m.is_some() as u8);
            }
            // R10_RBF (claude-r8): on plain ROW-Y / ROW-F slots the rows' carry-in lane f is only a carry-pool lane (|0>
            // through both rows passes, read by nothing else after the decode): with no room it is not re-bound; the
            // undo rows' pool is one lane shorter
            if rt.f == q && rt.m.is_none() && row_y(rt) && row_f() && r10_on("R10_RBF", self.room(b), 1) {
                rt.f = NOQ;
                lend.retain(|&x| x != q);
                lanes.retain(|&x| x != q);
                continue;
            }
            // R10_RBL (claude-r8): LA's sign lane (|0>, lent to both plain rows passes by R3_LA8ROWS, read by neither) is
            // re-bound only after the undo rows have released their scratch
            // R10_RBY (claude-r8): likewise Y[W-1] (|0> and lent through the undo rows on YTOP-SWEEP slots) is re-bound
            // after them
            if rt.m.is_none() && self.y[W - 1] == q && r10_on("R10_RBY", self.room(b), 1) {
                self.y[W - 1] = NOQ;
                R10YT.with(|c| c.set(true));
                lend.retain(|&x| x != q);
                lanes.retain(|&x| x != q);
                continue;
            }
            if rt.m.is_none() && self.la[LB_BITS - 1] == q && r10_on("R10_RBL", self.room(b), 1) {
                self.la[LB_BITS - 1] = NOQ;
                R10LA.with(|c| c.set(true));
                lend.retain(|&x| x != q);
                lanes.retain(|&x| x != q);
                continue;
            }
            // R10_RBL2 (claude-r8, 797): the same deferral for LA's lent lanes 5..8 (|0> when lent, garbage after the rows)
            if let Some(i) = self.la.iter().position(|&x| x == q) {
                if rt.m.is_none() && i >= R_BITS && i < LB_BITS - 1 && rt.f != q && rt.y != q && rt.g != q
                    && r10_on("R10_RBL2", self.room(b), 1) {
                    self.la[i] = NOQ;
                    R10LA2.with(|c| c.borrow_mut().push(i));
                    lend.retain(|&x| x != q);
                    lanes.retain(|&x| x != q);
                    continue;
                }
            }
            let nq = b.alloc();
            if rt.f == q { rt.f = nq; if let Some(m) = rt.m.as_mut() { m.c0 = nq; } }
            else if rt.y == q { rt.y = nq; }
            else if rt.g == q { rt.g = nq; if let Some(m) = rt.m.as_mut() { m.t = nq; } }
            else if self.y[W - 1] == q { self.y[W - 1] = nq; }
            else { let i = self.la.iter().position(|&x| x == q).expect("R5 rebind"); self.la[i] = nq; }
            for x in lend.iter_mut() { if *x == q { *x = nq; } }
            for x in lanes.iter_mut() { if *x == q { *x = nq; } }
        }
    }
    /// The denorm's sY erase, sY = act & !Y0 & Y1. R9 rowtmp c (act released, `el` = (a1, rho)): act = a1 | (rho != 0),
    /// so the repair is (-1)^(!Y0 Y1) (-1)^(!Y0 Y1 !a1 !rho) (OR = 1 ^ AND of the complements); else the parent's erase.
    fn r9_sy_erase(&self, b: &mut B, s: QubitId, y_act: Option<QubitId>, el: &Option<(QubitId, [QubitId; RHO_BITS])>) {
        let base = [(self.y[0], true), (self.y[1], false)];
        match (el, y_act) {
            (Some((a1, r)), Some(_)) => {
                // the 6-literal repair takes the borrowed-lane form when the room is short (the passenger's lanes)
                assert!(super::mask::borrowed().len() >= 5, "R9 rowtmp c: sY erase needs 5 borrowed lanes");
                let mut l6 = base.to_vec();
                l6.push((*a1, true));
                l6.extend(r.iter().map(|&q| (q, true)));
                erase_mbu(b, s, |b| {
                    phase_and(b, &base);
                    if !r9_rt_break("c2") { phase_and(b, &l6); }
                });
            }
            _ => {
                let mut l = act_lits(y_act);
                l.extend(base);
                erase_and(b, self, s, &l);
            }
        }
    }
    /// losgahts A: Y's denormalisation moved up to right after the undo rows (its a-shift back under sY, sY erased as
    /// [Y slack == 1] by r9_sy_erase, the lane freed); the cap is lowered by one until the parent's sY free
    fn la94_sy_out(&mut self, b: &mut B, sy: &[QubitId], y_act: Option<QubitId>, el: &Option<(QubitId, [QubitId; RHO_BITS])>) {
        assert!(sy.len() == 1);
        for i in (0..NB).rev() {
            b.cswap(sy[0], self.y[i], self.y[i + 1]);
        }
        self.r9_sy_erase(b, sy[0], y_act, el);
        b.free(sy[0]);
        self.cap -= 1;
        if std::env::var_os("R9_DBG").is_some() { eprintln!("LA94A fire slot {}", p3_cur_slot()); }
    }
    /// losgahts A: p ^= the predicate r9_sy_erase erases (sY's value on every shot, from the un-shifted Y)
    fn la94_sy_pred(&self, b: &mut B, p: QubitId, y_act: Option<QubitId>, el: &Option<(QubitId, [QubitId; RHO_BITS])>) {
        let base = [(self.y[0], true), (self.y[1], false)];
        match (el, y_act) {
            (Some((a1, r)), Some(_)) => {
                let mut l6 = base.to_vec();
                l6.push((*a1, true));
                l6.extend(r.iter().map(|&q| (q, true)));
                and_auto(b, self, &base, p);
                if !r14_break("pred") { and_auto(b, self, &l6, p); }
            }
            _ => {
                let mut l = act_lits(y_act);
                l.extend(base);
                and_auto(b, self, &l, p);
            }
        }
    }
    /// Lanes the slot may still allocate under the cap.
    fn room(&self, b: &B) -> usize {
        self.cap.saturating_sub(b.live) as usize
    }
}

/// out ^= AND(lits): clean ancillas while the cap leaves room, borrowed lanes otherwise.
#[track_caller]
fn and_auto(b: &mut B, u: &GreedyFrog, lits: &[(QubitId, bool)], out: QubitId) {
    let need = lits.len().saturating_sub(2);
    if need == 0 || u.room(b) >= need { and_into(b, lits, out) } else { and_dirty(b, lits, out, &u.dirty) }
}

/// Phase (-1)^AND(lits): an AND chain into clean ancillas (uncomputed by measurement) and a CZ, n - 2 Toffoli.
#[track_caller]
fn phase_and(b: &mut B, lits: &[(QubitId, bool)]) {
    let n = lits.len();
    // P2-REBASE (cap < 813; retake799's phase_auto form): no room for the chain: AND of all but the last literal into a
    // borrowed lane d, CZ(d, last), twice (d restored; the phase is (-1)^(d ^ AND) (-1)^d = (-1)^AND on the last)
    if n >= 3 && p2_room(b) < n - 2 {
        let dl = super::mask::borrowed();
        if dl.len() >= n - 1 && r8_phb() {
            // R8-ROOM0 R8_PHB (exact): r = room clean lanes carry the AND of the first r + 1 literals (measured
            // uncompute), the rest takes the borrowed-lane phase form: r + 4(n - r) - 10 Toffoli (CZ when n - r = 2)
            let r = if b.recording() { 0 } else { p2_room(b).min(n - 2) };
            if r >= 1 && r8_cc2() {
                // R8_CC2: the conditionally clean form on the room's r clean lanes
                let anc = b.alloc_n(r);
                super::arith::and_cc(b, lits, None, &anc, &dl);
                b.free_n(&anc);
                return;
            }
            let anc = b.alloc_n(r);
            for &(q, ng) in &lits[..if r > 0 { r + 1 } else { 0 }] { if ng { b.x(q); } }
            if r > 0 { b.and_c(lits[0].0, lits[1].0, anc[0]); }
            for i in 2..=r { b.and_c(anc[i - 2], lits[i].0, anc[i - 1]); }
            let mut rest: Vec<(QubitId, bool)> = if r > 0 { vec![(anc[r - 1], false)] } else { vec![] };
            rest.extend_from_slice(&lits[if r > 0 { r + 1 } else { 0 }..]);
            if rest.len() == 2 {
                for &(q, ng) in &rest { if ng { b.x(q); } }
                b.cz(rest[0].0, rest[1].0);
                for &(q, ng) in &rest { if ng { b.x(q); } }
            } else {
                super::arith::phase_dirty(b, &rest, &dl);
            }
            for i in (2..=r).rev() { b.and_u(anc[i - 2], lits[i].0, anc[i - 1]); }
            if r > 0 { b.and_u(lits[0].0, lits[1].0, anc[0]); }
            for &(q, ng) in &lits[..if r > 0 { r + 1 } else { 0 }] { if ng { b.x(q); } }
            b.free_n(&anc);
            return;
        }
        if dl.len() >= n - 1 {
            let (d, chain) = (dl[0], &dl[1..]);
            let (last, ng) = lits[n - 1];
            for _ in 0..2 {
                and_dirty(b, &lits[..n - 1], d, chain);
                if ng { b.x(last); }
                b.cz(d, last);
                if ng { b.x(last); }
            }
            return;
        }
    }
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
    R6_INCOND.with(|c| c.set(c.get() + 1));
    phase(b);
    R6_INCOND.with(|c| c.set(c.get() - 1));
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

/// I4-ONCE ERASE-EFREE (dev switch `I4_EFE=1`; off = the parent): with EFREE the measured lane t leaves the live count
/// before its repair runs, so the repair's chain may take t's own lane: the measured erase fits where room + 1 lanes
/// cover the chain (the parent asks for room alone and falls back to a recomputation). The repair's peak is
/// live - 1 + chain <= cap, so the slot's peak is unchanged.
fn efe_slack() -> usize {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("I4_EFE").map_or(false, |v| v.trim() == "1"));
    (*E && efree()) as usize
}
/// Erase t = AND(lits) by measurement while the cap leaves room for the repair's chain, by recomputation otherwise.
#[track_caller]
fn erase_and(b: &mut B, u: &GreedyFrog, t: QubitId, lits: &[(QubitId, bool)]) {
    if u.room(b) + efe_slack() >= lits.len().saturating_sub(2) {
        // negative control for the gate tests only: I4_EFE_BREAK=1 drops the repair on the erases ERASE-EFREE adds
        let brk = cfg!(test) && u.room(b) < lits.len().saturating_sub(2)
            && std::env::var("I4_EFE_BREAK").map_or(false, |v| v.trim() == "1");
        if brk { erase_mbu(b, t, |_b| {}); return; }
        erase_mbu(b, t, |b| phase_and(b, lits));
    } else if r6_mix(u) && lits.len() >= 3 && super::mask::borrowed().len() >= lits.len() - 1 && !b.recording() {
        // R6_MIX: the measured erase with the borrowed-lane phase form (two (n-1)-literal ANDs at half weight) is never
        // dearer in expected Toffoli than the XOR re-computation of the n-literal AND
        erase_mbu(b, t, |b| phase_and(b, lits));
    } else {
        and_auto(b, u, lits, t);
    }
}

/// Erase t = [v >= k] by measurement (repair on a clean chain) while the cap leaves room, by recomputation otherwise.
fn ge_erase(b: &mut B, u: &GreedyFrog, v: &[QubitId], k: isize, t: QubitId) {
    let need = v.len().saturating_sub(1);
    if efe_slack() == 1 && u.room(b) < need && u.room(b) + 1 >= need {
        // ERASE-EFREE: the chain is taken inside the repair, after t has left the live count
        erase_mbu(b, t, |b| {
            let chain = b.alloc_n(need);
            super::mask::ge_const_phase(b, v, k, &chain);
            b.free_n(&chain);
        });
    } else if u.room(b) >= need {
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

#[track_caller]
fn zero_auto(b: &mut B, u: &GreedyFrog, v: &[QubitId], out: QubitId) {
    let lits: Vec<(QubitId, bool)> = v.iter().map(|&q| (q, true)).collect();
    and_auto(b, u, &lits, out);
}

#[track_caller]
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
#[track_caller]
fn pool_for(b: &mut B, u: &GreedyFrog, want: usize, reserve: usize) -> Vec<QubitId> {
    let n = want.min(u.room(b).saturating_sub(reserve));
    let v = b.alloc_n(n);
    super::builder::r8idle::pend("pool", &v, (want - n) as u64);
    v
}

/// AND / comparator on a clean chain (`clean`) or on borrowed lanes.
/// The sweeps' g = AND (act, kt5 == j). R6_MIX on the borrowed-lane path: RowTmp's y is |0> at every such AND (each
/// row's y is erased before the next g), so it leads the clean part of the chain, topped up from the room.
fn sweep_g_and(b: &mut B, u: &GreedyFrog, clean: bool, lits: &[(QubitId, bool)], rt: &RowTmp, chain: &[QubitId]) {
    if !clean && r6_mix(u) && !b.recording() && lits.len() >= 3 {
        if R6_INCOND.with(|c| c.get()) == 0 { zero_probe(b, &[rt.y]); }
        let extra = b.alloc_n(u.room(b).min(lits.len() - 3));
        let mut cl = vec![rt.y];
        cl.extend(&extra);
        if r6_break("swg") { b.x(rt.y); }
        super::arith::and_mixed_on(b, lits, rt.g, &cl, chain);
        if r6_break("swg") { b.x(rt.y); }
        b.free_n(&extra);
    } else {
        and_any(b, clean, lits, rt.g, chain);
    }
}
#[track_caller]
fn and_any(b: &mut B, clean: bool, lits: &[(QubitId, bool)], out: QubitId, chain: &[QubitId]) {
    if clean { and_into_t(b, lits, out, chain) } else { and_dirty(b, lits, out, chain) }
}
#[track_caller]
fn ge_any(b: &mut B, v: &[QubitId], k: isize, t: QubitId, chain: &[QubitId], clean: bool) {
    if clean { super::mask::ge_const(b, v, k, t, chain) } else { super::mask::ge_const_dirty(b, v, k, t, chain) }
}

/// jl ^= the last row with q_j = 1 (rem lane j - 1 clear) among the rows j <= kt of active shots, scanning
/// j = k-1 .. 1 with a running OR f: y = q_j & g_j & !f, jl ^= j y, f ^= y, then y = q_j & [jl == j] is erased (jl == j
/// only where row j fired) by measurement. Row 0 never changes jl (0 is the default), so it is not visited.
/// g_j = act & [kt >= j]; g = 0 on entry and exit. Emitted directly (the measured erases are not recordable); ANDs on
/// `chain` (clean when `clean`, borrowed lanes otherwise).
fn sweep_fwd(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, chain: &[QubitId], clean: bool) {
    sweep_fwd_d(b, u, act, w, rt, chain, clean, None)
}
/// `sweep_fwd` with SWEEP-DEFER (`defer`): each row's y is X-measured without its repair; the outcome is kept per row
/// and repaid by `sweep_bwd_d` as a Z on the identical y it regenerates (ROLL's repayment, applied to the sweep).
fn sweep_fwd_d(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, chain: &[QubitId], clean: bool,
               mut defer: Option<&mut Vec<Option<BitId>>>) {
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
            sweep_g_and(b, u, clean, &lits, rt, chain);
        }
        let lane = rt.rem(u, j as isize - 1);
        and_any(b, clean, &[(lane, true), (rt.g, false), (f, true)], y, chain);
        for (i, &bit) in jl.iter().enumerate() {
            if (j >> i) & 1 == 1 {
                b.cx(y, bit);
            }
        }
        b.cx(y, f);
        let lits = row_elits(lane, jl, j, k);
        if let Some(d) = defer.as_mut() {
            let m = b.fresh_bits(1)[0];
            b.hmr_to(y, m);
            if d.len() <= j { d.resize(j + 1, None); }
            d[j] = Some(m);
        } else {
            erase_and(b, u, y, &lits);
        }
    }
    // g = act & [kt >= 1] -> act -> 0
    let mut lits = act_lits(act);
    lits.extend(eq_lits(kt5, 0));
    sweep_g_and(b, u, clean, &lits, rt, chain);
    match act {
        Some(a) => b.cx(a, rt.g),
        None => b.x(rt.g),
    }
}

/// The exact inverse of `sweep_fwd` (rows in the opposite order), with each row's y erased by measurement through
/// its forward definition !lane & g & !f.
fn sweep_bwd(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, chain: &[QubitId], clean: bool) {
    sweep_bwd_d(b, u, act, w, rt, chain, clean, None)
}
fn sweep_bwd_d(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, chain: &[QubitId], clean: bool,
               rep: Option<&[Option<BitId>]>) {
    let (jl, f, y) = (&rt.jl[..], rt.f, rt.y);
    let kt5 = &u.lb[..R_BITS];
    let k = w.k;
    match act {
        Some(a) => b.cx(a, rt.g),
        None => b.x(rt.g),
    }
    let mut lits = act_lits(act);
    lits.extend(eq_lits(kt5, 0));
    sweep_g_and(b, u, clean, &lits, rt, chain);
    for j in 1..k {
        let lane = rt.rem(u, j as isize - 1);
        let lits = row_elits(lane, jl, j, k);
        and_any(b, clean, &lits, y, chain);
        if let Some(Some(m)) = rep.and_then(|r| r.get(j).copied()) {
            // SWEEP-DEFER: repay the forward erase of this row's y on its regenerated twin (negative control for the
            // gate tests only: I4_DEFER_BREAK=1 drops the repayment)
            if !(cfg!(test) && std::env::var("I4_DEFER_BREAK").map_or(false, |v| v.trim() == "1")) {
                b.z_if(y, m);
            }
        }
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
            sweep_g_and(b, u, clean, &lits, rt, chain);
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

/// R15-JC (S4 lane-free sweep, port of the old greedyfrog's GF_JC, rows 255aed36 -> d624b2a2): on R11_FOLD slim slots
/// (f = !act, act folded) the forward sweep keeps the search flag S and jl jointly in jl's 5 lanes: S = jl[4]
/// ("searching" = code 16; a found row j has code j, or 31 for j = 16), each row one transposition 16 <-> code(j)
/// controlled by !lane on borrowed lanes. No g, no running OR in f, no one-hot y: the sweep needs jl alone (f only as
/// the act gate). Final cleanup s ^= !f & [jl[0..4] == 0] maps an active shot's unfound 16 to 0 and leaves finished shots
/// (never searching) at 0, so jl is the parent's: the last row j <= kt with q_j = 1, 0 otherwise, 0 on finished shots;
/// f is unchanged (= !act, the parent's f after its VROOM clear). Dev switch `R15_JC=1` (off = the parent).
fn r15_jc_on() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("R15_JC").map_or(false, |v| v.trim() == "1"));
    *E
}
fn r15_brk(s: &str) -> bool {
    cfg!(test) && std::env::var("R15_BREAK").map_or(false, |v| v.trim() == s)
}
fn jc_find(b: &mut B, jl: &[QubitId], lane: QubitId, j: usize, d: &[QubitId]) {
    let code = if j == 16 { 31 } else { j };
    if code < 16 {
        let ones: Vec<usize> = (0..4).filter(|&i| (code >> i) & 1 == 1).collect();
        for &i in &ones { b.cx(jl[4], jl[i]); }
        let mut lits = vec![(lane, true)];
        lits.extend((0..4).map(|i| (jl[i], (code >> i) & 1 == 0)));
        and_dirty(b, &lits, jl[4], d);
        for &i in &ones { b.cx(jl[4], jl[i]); }
    } else {
        let c = code - 16;
        let p = c.trailing_zeros() as usize;
        let others: Vec<usize> = (0..4).filter(|&i| i != p && (c >> i) & 1 == 1).collect();
        for &i in &others { b.cx(jl[p], jl[i]); }
        let mut lits = vec![(lane, true), (jl[4], false)];
        for i in 0..4 { if i != p { lits.push((jl[i], true)); } }
        and_dirty(b, &lits, jl[p], d);
        for &i in &others { b.cx(jl[p], jl[i]); }
    }
}
/// transposition 16 <-> 31 (self-inverse)
fn jc_31_16(b: &mut B, jl: &[QubitId], d: &[QubitId]) {
    for i in 1..4 { b.cx(jl[0], jl[i]); }
    and_dirty(b, &[(jl[4], false), (jl[1], true), (jl[2], true), (jl[3], true)], jl[0], d);
    for i in 1..4 { b.cx(jl[0], jl[i]); }
}
fn sweep_fwd_jc(b: &mut B, u: &GreedyFrog, gate: &[(QubitId, bool)], w: &Win, rt: &RowTmp) { sweep_fwd_jc_g(b, u, gate, None, w, rt) }
/// b793b ACTFOLD: `fg` = Some((LA[5], LA[6])): act = !(LA[5] & LA[6]) (the pair (1,1) carries !act); every act-gated XOR becomes the ungated one plus the one with the pair as two more controls
fn sweep_fwd_jc_g(b: &mut B, u: &GreedyFrog, gate: &[(QubitId, bool)], fg: Option<Vec<QubitId>>, w: &Win, rt: &RowTmp) {
    let jl = &rt.jl[..];
    assert!(jl.len() == R_BITS && jl.iter().all(|&q| q != NOQ));
    let s = jl[4];
    let kt5 = &u.lb[..R_BITS];
    let k = w.k;
    assert!(k >= 2 && k <= 31, "R15_JC: k = {k} (code 31 is reserved; the row-0 toggle needs k >= 2)");
    let mut busy: Vec<QubitId> = jl.to_vec();
    busy.extend(kt5);
    busy.extend(gate.iter().map(|l| l.0));
    if let Some(fl) = &fg { busy.extend(fl.iter().copied()); }
    busy.extend((0..k.saturating_sub(1)).map(|i| u.y[i]));
    let d: Vec<QubitId> = u.dirty.iter().copied().filter(|q| !busy.contains(q)).collect();
    assert!(d.len() >= 5, "R15_JC: {} borrowed lanes", d.len());
    let d = &d[..];
    match &fg {
        None => super::mask::ge_const_dirty_gated(b, kt5, k as isize - 1, s, gate, d),
        Some(fl) => {
            super::mask::ge_const_dirty_gated(b, kt5, k as isize - 1, s, gate, d);
            let mut g2 = gate.to_vec();
            g2.extend(fl.iter().map(|&q| (q, false)));
            super::mask::ge_const_dirty_gated(b, kt5, k as isize - 1, s, &g2, d);
        }
    }
    let gand = |b: &mut B, lits: &[(QubitId, bool)]| {
        let mut l = gate.to_vec();
        l.extend_from_slice(lits);
        and_dirty(b, &l, s, d);
        if let Some(fl) = &fg { l.extend(fl.iter().map(|&q| (q, false))); and_dirty(b, &l, s, d); }
    };
    for j in (1..k).rev() {
        if j + 1 < k {
            gand(b, &eq_lits(kt5, j));
        }
        jc_find(b, jl, rt.rem(u, j as isize - 1), j, d);
    }
    gand(b, &eq_lits(kt5, 0));
    // negative control R15_BREAK=gate: the old tree's ungated cleanup (finished shots end at 16)
    if r15_brk("gate") { let lits: Vec<(QubitId, bool)> = (0..4).map(|i| (jl[i], true)).collect(); and_dirty(b, &lits, s, d); }
    else { let lits: Vec<(QubitId, bool)> = (0..4).map(|i| (jl[i], true)).collect(); gand(b, &lits); }
    if k >= 17 && !r15_brk("3116") { jc_31_16(b, jl, d); }
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
fn row_elits(lane: QubitId, jl: &[QubitId], j: usize, k: usize) -> Vec<(QubitId, bool)> {
    let mut v = if sweep_eq_lit() { vec![] } else { vec![(lane, true)] };
    if sweep_wit() && sweep_eq_lit() {
        v.extend(wit_bits(j, k).into_iter().map(|bit| (jl[bit], (j >> bit) & 1 == 0)));
    } else {
        v.extend(eq_lits(jl, j));
    }
    v
}

/// I4-ONCE SWEEP-ROT (dev switch `I4_ROT=1`, used only where the parent falls back to its non-unary sweep; off = the
/// parent). The parent masks every row j of the last-row sweep with g = act & [kt >= j], toggled by a 6-literal
/// [kt == j] per row and pass (borrowed chains at 799). SWEEP-ROT instead rotates the k sign lanes (rows 0..k-1: s0,
/// Y[0..k-2]) cyclically by -m, m = min(kt, k-1), with 5 cswap stages (no ancilla; stage controls from kt's bits and
/// big = [kt >= k-1]), so scan step i (position -i mod k) holds row m - i: the valid rows m..0 come first and the
/// garbage rows (j > kt) last. The scan needs no mask: y = q & !f (2 literals), jl ^= (31 - i) y, f ^= y, y erased
/// through the fewest jl bits separating 31 - i from {0} U [32 - i, 31] (forward) or through (q, !f) (backward). f
/// starts at !act, so finished shots never fire. The unrotation adds m to jl (its stage controls drive controlled
/// power-of-two increments) and jl += 1, so jl = m - i_found: the parent's jl on every decodable active shot (garbage,
/// erased the same way, on finished or undecodable shots, where r, a1 and the carried flag are act-gated already).
/// I4-ONCE SWEEP-DEFER (dev switch `I4_DEFER=1`; off = the parent): on slots that run the non-unary forward sweep, each
/// row's one-hot y is X-measured with no repair; the backward sweep regenerates the identical y = [jl == j] (jl at the
/// backward row j equals jl after the forward row j: later forward fires are cleared by the earlier backward rows, and
/// the r / a1 section restores jl) and repays the phase there as a classically conditioned Z (Clifford), as ROLL repays
/// measured carries on the matched inverse ladder.
fn sweep_defer_on() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("I4_DEFER").map_or(false, |v| v.trim() == "1"));
    *E
}
fn sweep_rot_on() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("I4_ROT").map_or(false, |v| v.trim() == "1"));
    *E
}
/// Fewest bit positions of a 5-bit register whose values at v separate v from every value in `others`.
fn min_sep(v: usize, others: &[usize]) -> Vec<usize> {
    let mut best: Option<Vec<usize>> = None;
    for mask in 0u32..32 {
        let bits: Vec<usize> = (0..R_BITS).filter(|&bt| mask >> bt & 1 == 1).collect();
        if others.iter().all(|&o| bits.iter().any(|&bt| (o >> bt) & 1 != (v >> bt) & 1)) {
            if best.as_ref().map_or(true, |bb| bits.len() < bb.len()) {
                best = Some(bits);
            }
        }
    }
    best.expect("separable")
}
/// SWEEP-ROT stage control into the |0> lane y: m_bt = big ? bit bt of (k - 1) : kt_bt (g holds big).
fn rot_ctrl(b: &mut B, kt5: &[QubitId], g: QubitId, y: QubitId, k: usize, bt: usize, on: bool) {
    let kb = ((k - 1) >> bt) & 1 == 1;
    if !on && kb { b.x(y); }
    if kb { b.x(kt5[bt]); }
    b.x(g);
    if on { b.and_c(kt5[bt], g, y); } else { b.and_u(kt5[bt], g, y); }
    b.x(g);
    if kb { b.x(kt5[bt]); }
    if on && kb { b.x(y); }
}
/// Cyclic rotation of `blk` by -s under c: new[p] = old[(p + s) mod n] (`inv`: its inverse).
fn rot_blk(b: &mut B, blk: &[QubitId], s: usize, c: QubitId, inv: bool) {
    let n = blk.len();
    let mut sw: Vec<(usize, usize)> = vec![];
    let gg = gcd(n, s);
    for st in 0..gg {
        let mut x = st;
        loop {
            let nx = (x + s) % n;
            if nx == st { break; }
            sw.push((x, nx));
            x = nx;
        }
    }
    if inv { sw.reverse(); }
    for (a, c2) in sw {
        b.cswap(c, blk[a], blk[c2]);
    }
}
fn sweep_rot(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, fwd: bool) {
    let (jl, f, y, g) = (&rt.jl[..], rt.f, rt.y, rt.g);
    let kt5 = &u.lb[..R_BITS];
    let k = w.k;
    assert!(k >= 2 && k <= 31 && jl.len() == R_BITS);
    let blk: Vec<QubitId> = (0..k).map(|p| rt.rem(u, p as isize - 1)).collect();
    let stages: Vec<(usize, usize)> = (0..R_BITS).map(|bt| (bt, (1usize << bt) % k)).filter(|&(_, s)| s != 0).collect();
    let wlits = |i: usize| -> Vec<(QubitId, bool)> {
        let v = 31 - i;
        let others: Vec<usize> = std::iter::once(0).chain(v + 1..32).collect();
        let mut bits = min_sep(v, &others);
        if cfg!(test) && std::env::var("I4_ROT_BREAK").map_or(false, |x| x.trim() == "1") && bits.len() >= 2 { bits.pop(); }
        bits.into_iter().map(|bt| (jl[bt], (v >> bt) & 1 == 0)).collect()
    };
    let set_v = |b: &mut B, i: usize| {
        let v = 31 - i;
        for bt in 0..R_BITS {
            if (v >> bt) & 1 == 1 { b.cx(y, jl[bt]); }
        }
    };
    let erase_lits = |b: &mut B, lits: &[(QubitId, bool)]| {
        if lits.len() == 1 {
            let (q, ng) = lits[0];
            if ng { b.x(q); }
            b.cx(q, y);
            if ng { b.x(q); }
        } else {
            erase_and(b, u, y, lits);
        }
    };
    if fwd {
        ge_auto(b, u, kt5, k as isize - 1, g);
        for &(bt, s) in &stages {
            rot_ctrl(b, kt5, g, y, k, bt, true);
            rot_blk(b, &blk, s, y, false);
            rot_ctrl(b, kt5, g, y, k, bt, false);
        }
        if let Some(a) = act { b.cx(a, f); b.x(f); }
        for i in 0..k {
            let lane = blk[(k - i) % k];
            b.x(lane); b.x(f);
            b.and_c(lane, f, y);
            b.x(f); b.x(lane);
            set_v(b, i);
            b.cx(y, f);
            let lits = wlits(i);
            erase_lits(b, &lits);
        }
        for &(bt, s) in stages.iter().rev() {
            rot_ctrl(b, kt5, g, y, k, bt, true);
            rot_blk(b, &blk, s, y, true);
            inc_auto(b, u, y, &jl[bt..]);
            rot_ctrl(b, kt5, g, y, k, bt, false);
        }
        add_const_auto(b, u, jl, 1, false);
        ge_auto(b, u, kt5, k as isize - 1, g);
    } else {
        ge_auto(b, u, kt5, k as isize - 1, g);
        add_const_auto(b, u, jl, 1, true);
        for &(bt, s) in &stages {
            rot_ctrl(b, kt5, g, y, k, bt, true);
            for &q in &jl[bt..] { b.x(q); }
            inc_auto(b, u, y, &jl[bt..]);
            for &q in &jl[bt..] { b.x(q); }
            rot_blk(b, &blk, s, y, false);
            rot_ctrl(b, kt5, g, y, k, bt, false);
        }
        for i in (0..k).rev() {
            let lane = blk[(k - i) % k];
            let lits = wlits(i);
            if lits.len() == 1 {
                let (q, ng) = lits[0];
                if ng { b.x(q); }
                b.cx(q, y);
                if ng { b.x(q); }
            } else {
                and_auto(b, u, &lits, y);
            }
            b.cx(y, f);
            set_v(b, i);
            erase_and(b, u, y, &[(lane, true), (f, true)]);
        }
        if let Some(a) = act { b.x(f); b.cx(a, f); }
        for &(bt, s) in stages.iter().rev() {
            rot_ctrl(b, kt5, g, y, k, bt, true);
            rot_blk(b, &blk, s, y, true);
            rot_ctrl(b, kt5, g, y, k, bt, false);
        }
        ge_auto(b, u, kt5, k as isize - 1, g);
    }
}

/// I4-ONCE SWEEP-WIT (dev switch `I4_WIT=1`; off = the parent's literals): wherever row j's one-hot y is computed or
/// erased through [jl == j], the sweep's state already restricts jl to {0} U [j, k-1] (one fire at most, rows visited
/// k-1 .. 1 forward and 1 .. k-1 backward, jl = j only where row j fired). So [jl == j] equals the AND of the fewest jl
/// bits (at j's values) that separate j from {0} U [j+1, k-1]: on average 3 literals instead of 5 at k = 21 (1 to 5),
/// which shrinks every recomputed / borrowed-lane AND and every measured erase's repair.
fn sweep_wit() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| std::env::var("I4_WIT").map_or(false, |v| v.trim() == "1"));
    *E
}
/// Fewest bit positions of a 5-bit jl whose values at j separate j from every v in {0} U [j+1, k-1] (smallest subset in
/// size order, ties by the lowest positions; exhaustive over the 32 subsets).
fn wit_bits(j: usize, k: usize) -> Vec<usize> {
    assert!(j >= 1 && j < k && k <= 32);
    let others: Vec<usize> = std::iter::once(0).chain(j + 1..k).collect();
    let mut best: Option<Vec<usize>> = None;
    for mask in 0u32..32 {
        let bits: Vec<usize> = (0..R_BITS).filter(|&bt| mask >> bt & 1 == 1).collect();
        if others.iter().all(|&v| bits.iter().any(|&bt| (v >> bt) & 1 != (j >> bt) & 1)) {
            if best.as_ref().map_or(true, |bb| bits.len() < bb.len()) {
                best = Some(bits);
            }
        }
    }
    let mut w = best.expect("j itself separates");
    // negative control for the gate tests only: I4_WIT_BREAK=1 drops the highest witness bit of multi-bit witnesses
    if cfg!(test) && std::env::var("I4_WIT_BREAK").map_or(false, |v| v.trim() == "1") && w.len() >= 2 {
        w.pop();
    }
    w
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
            sweep_row(b, u, rt, j, k, &a, fwd);
            b.free_n(&a);
        } else {
            sweep_row(b, u, rt, j, k, anc, fwd);
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
fn sweep_row(b: &mut B, u: &GreedyFrog, rt: &RowTmp, j: usize, k: usize, anc: &[QubitId], fwd: bool) {
    let (jl, f, y) = (&rt.jl[..], rt.f, rt.y);
    let lane = rt.rem(u, j as isize - 1);
    let elits = row_elits(lane, jl, j, k);
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
    window_gt_h(b, u, gt, w, None)
}
fn window_gt_h(b: &mut B, u: &GreedyFrog, gt: Option<QubitId>, w: &Win, th: Option<QubitId>) {
    window_gt_hh(b, u, gt, w, th, None)
}
/// R4-SITES (cap < 573): R4_SWC0 hosts the masked ladder's carry-in c0 on !Y[0] (odinfree / retake799 Froschfurz's
/// hosting half: lane 0 is skipped by WGT_TOP1 and is 1 wherever gt is consulted; elsewhere gt is garbage, masked
/// off and erased by the same function, and the up / down pair restores every lane for any c0). `th`: the mask's
/// AND temp on a lane that is |0> here (R4_SWT, odinfree Froschunterhoesli: sw before it is written).
fn r4_swc0(u: &GreedyFrog) -> bool { below805(u.cap) && wgt_top1() && norm_stage0() && r3_flag("R4_SWC0") }
/// `yh` (R14 läckBobby part S): a lane holding the classical constant 1 on every shot that nothing here reads (the
/// swap decode passes Y[W-1], see `r14_ytop`): where the R9_PREFIX D form takes its single retained prefix lane and the
/// cap leaves no lane for it, the lane is X-flipped to |0>, serves as that prefix lane (the decoder leaves its prefix
/// |0> again: the up pass is played back inverted) and is flipped back to 1. No Toffoli.
fn window_gt_hh(b: &mut B, u: &GreedyFrog, gt: Option<QubitId>, w: &Win, th: Option<QubitId>, yh: Option<QubitId>) {
    let lo = if wgt_top1() && norm_stage0() { 1 } else { 0 };
    let t: Vec<QubitId> = (lo..NB).rev().map(|i| u.x[i]).collect();
    let sv: Vec<QubitId> = (lo..NB).rev().map(|i| u.y[i]).collect();
    if w.mxp >= NB + 1 {
        // R8-ROOM0 R8_SWL: the unmasked compare does not use th (sw, |0> here): it is lent to the compare's pool
        let l: Vec<QubitId> = if r8_swl(u) && !b.recording() { th.into_iter().collect() } else { vec![] };
        r8_lend(b, &l, |b| {
            let c0 = b.alloc();
            let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
            let pool = pool_for(b, u, NB, 0);
            plain_compare(b, &t, &sv, c0, &sc, gt, None, &pool);
            b.free_n(&pool);
            b.free(c0);
        });
        return;
    }
    // LA holds u (mX = W - 1 - u): offset it to u' = u - UOFF (mX = NB - u'). The mask turns on at ladder lane l where
    // mX == NB - l, i.e. u' == l, and is on from the start where mX >= NB + 1, i.e. u' < 0 (its sign bit).
    add_const_sm(b, u, &u.la, UOFF, true);
    // b793b SWLAH: LA[6], LA[7] are sign copies for the compare's duration (u' >= -64): free them (see b793_swlah)
    let swlah = b793_swlah() && w.act_const && p3_cur_slot() <= 39 && u.la[6] != NOQ && u.la[7] != NOQ && u.la[6] != u.la[LB_BITS - 1]
        && !b.is_free(u.la[6]) && !b.is_free(u.la[7]) && r8_hb() >= R8_TOP;
    let swlah_ids = [u.la[6], u.la[7]];
    if swlah {
        if std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE swlah slot {}", p3_cur_slot()); }
        for &i in &[6usize, 7] { if !(i == 7 && b793b_break("sl1")) { b.cx(u.la[LB_BITS - 1], u.la[i]); } }
        if R6_INCOND.with(|c| c.get()) == 0 { zero_probe(b, &swlah_ids); }
        b.free_n(&swlah_ids);
    }
    let c0y = r4_swc0(u);
    // R10_WGT (claude-r8): with no lane for the 5-lane retained prefix, the decoder of u' keeps a 4-lane retained
    // prefix (retake799's RSHORT form: bits 5..1 retained, bit 0 joins each toggle by a CCX); exact
    let wshort = (th.is_some() || c0y) && r10_on("R10_WGT", u.room(b), 1 + th.is_none() as usize + 5);
    // R10_WGT2: one lane shorter still: a 3-lane retained prefix (R10_SH2's form, bits 1 and 0 through a borrowed lane)
    let wshort2 = wshort && r10_on("R10_WGT2", u.room(b), th.is_none() as usize + 5);
    // R12_WGT3 (fable 796b): a 2-lane retained prefix (RSHORT3 form, bits 2..0 through two borrowed lanes)
    let wshort3 = wshort2 && r10_on("R12_WGT3", u.room(b), th.is_none() as usize + 4);
    let rs0 = super::mask::RSHORT.with(|c| c.replace(c.get() || wshort));
    let rs20 = super::mask::RSHORT2.with(|c| c.replace(c.get() || wshort2));
    let rs30 = super::mask::RSHORT3.with(|c| c.replace(c.get() || wshort3));
    // R9_PREFIX D (r9 prefix): a 1-lane retained prefix (bits 5, 4), bit 3 formed on the mask's AND temp t between
    // cells (t is |0> there), bits 2..0 through two borrowed lanes (mask::RSHORT4T); where the 2-lane prefix leaves no
    // lane for the cap: f, t (if fresh), 2 prefix lanes, c0 (if fresh)
    let wshort4 = wshort3 && (th.is_some() || c0y)
        && r9p_on('D', u.room(b), 1 + th.is_none() as usize + 2 + (!c0y) as usize);
    if wshort4 { r9p_log('D', b, u.room(b)); }
    let rs40 = super::mask::RSHORT4T.with(|c| c.replace(c.get() || wshort4));
    let mut yh_used = false;
    let m = if th.is_some() || c0y {
        let f = b.alloc();
        let t = th.unwrap_or_else(|| b.alloc());
        // R14 läckBobby S: the 1-lane prefix on the hosted constant-1 lane where the cap leaves no lane for it
        let pre = match yh {
            Some(h) if wshort4 && r14p_on('S', u.room(b), 1) => {
                r14p_log('S', b, u.room(b));
                if !r14p_brk("s") { b.x(h); }
                // (inside the erase's condition block the flip only acts on m = 1 shots: probe outside blocks only)
                if R6_INCOND.with(|c| c.get()) == 0 { zero_probe(b, &[h]); }
                yh_used = true;
                vec![h]
            }
            _ => b.alloc_n(if wshort4 { 1 } else if wshort3 { 2 } else if wshort2 { 3 } else if wshort { 4 } else { 5 }),
        };
        // negative control for the gate tests only: R4_BREAK=c0 leaves Y[0] unflipped (carry-in 1 where gt counts)
        let c0 = if c0y { if !r4s_break("c0") { b.x(u.y[0]); } u.y[0] } else { b.alloc() };
        Masked { f, t, gf: f, chain: vec![], pre, c0 }
    } else { Masked::alloc_small(b) };
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
    if th.is_some() || c0y {
        b.free(m.f);
        if yh_used {
            // R14 läckBobby S: the prefix lane is |0> again; back to its constant 1
            if R6_INCOND.with(|c| c.get()) == 0 { zero_probe(b, &m.pre); }
            if !r14p_brk("s") { b.x(m.pre[0]); }
        } else {
            b.free_n(&m.pre);
        }
        if th.is_none() { b.free(m.t); }
        if c0y { if !r4s_break("c0") { b.x(u.y[0]); } } else { b.free(m.c0); }
    } else { m.free(b); }
    super::mask::RSHORT.with(|c| c.set(rs0));
    super::mask::RSHORT2.with(|c| c.set(rs20));
    super::mask::RSHORT3.with(|c| c.set(rs30));
    super::mask::RSHORT4T.with(|c| c.set(rs40));
    if swlah {
        for &q in &swlah_ids { b.acquire(q); }
        for &i in &[6usize, 7] { b.cx(u.la[LB_BITS - 1], u.la[i]); }
    }
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
        p2_set_cap(self.cap);
        prof(b, "i.z0");
        p3(b, self, "i.z0");
        // I1: z0 = [LA == 0] & [cnt != 0]; on slots where no shot can have finished, act = 1 classically and the
        // flag (and the DONE bookkeeping) is skipped
        // R14 misc94 "DonRwetter" p: on the term slot the I1 flag is formed after I6 releases LB's lanes 5.. (see there)
        let m94p = r14m('p') && !w.act_const && term(w) && cin.is_none() && norm_stage0() && sy_act_gate()
            && r3_flag("R12_TERM");
        let mut z0 = if w.act_const || m94p { None } else { Some(b.alloc()) };
        if let Some(z0) = z0 {
            let cz = b.alloc();
            self.cnt_zero_into(b, cz);
            let lz = b.alloc();
            zero_into(b, &self.la[..len_n(w)], lz);
            and_into(b, &[(lz, false), (cz, true)], z0);
            // Z0-DEFER: the forward's F11 z0 erase is repaired here, on the same predicate of the same state
            if let Some(m) = bits.z0m {
                if !m2_break(2) { b.z_if(z0, m); }
            }
            if z0_meas() {
                let zl: Vec<(QubitId, bool)> = self.la[..len_n(w)].iter().map(|&q| (q, true)).collect();
                let cl: Vec<(QubitId, bool)> = self.cntw().iter().map(|&q| (q, false)).collect();
                erase_and(b, self, lz, &zl);
                if cr_break(4) { let m = b.fresh_bits(1)[0]; b.hmr_to(cz, m); } else { erase_and(b, self, cz, &cl); }
            } else {
                zero_into(b, &self.la[..len_n(w)], lz);
                self.cnt_zero_into(b, cz);
            }
            b.free(lz);
            b.free(cz);
        }
        // z0 holds act = !z0 except around I5 and at the end
        let mut act = z0;
        if let Some(z0) = z0 {
            b.x(z0);
        }
        p3(b, self, "i.prep");
        if std::env::var_os("B792_LALB").is_some() && w.act_const && w.slot >= 43 {
            R8_OFF.with(|c| c.set((1 << R_BITS) - 1));
            r8_m8_open(b, self, w);

            R8_OFF.with(|c| c.set(0));
        }
        let mut y_act = if sy_act_gate() { act } else { None };
        let ns0 = norm_stage0();
        // OFF-KEEP (MICRO-WALK) runs on the standard I2 path only: a SW-CARRY slot (cin) erases its carried flag
        // on the plain un-swapped registers before its prep, with no decode offsets to keep
        let keep = ns0 && off_keep() && cin.is_none() && !term(w);
        // R9 rowtmp b: Y[W-1] = 1 on every shot from the slot's start to the rows (YTOP-HOST flips and lends it there,
        // probed |0>); the last slot's term prep and I6 never read it, so it is X-cleared and released from the term
        // prep to the LB release after I6 (the stretch where z0, sX, sY and LA / LB at 9 lanes each are all live)
        let mut r9yt = false;
        let mut p7y_pend = false;
        let (mut sx, mut sy, sw_std): (Vec<QubitId>, Vec<QubitId>, Option<QubitId>) = if let Some(c) = cin {
            // SW-CARRY: I3, I4 on the carried flag, its I5 erase (the forward's F9 on the restored pre-swap state),
            // then the decode prep on the un-swapped rings (the receiver's ring layouts at the rows window)
            prof(b, "i.unswap");
            b.z_if(c, bits.sw);
            let (xn, ln) = swap_lanes(w, true);
            super::arith::cswap_regs(b, c, &self.x[..xn], &self.y[..xn]);
            super::arith::cswap_regs(b, c, &self.la[..ln], &self.lb[..ln]);
            b.cx(c, self.par);
            prof(b, "i.swerase");
            erase_mbu(b, c, |b| {
                if let Some(z0) = z0 {
                    b.x(z0);
                }
                self.swap_flag(b, z0, None, w, false);
                if let Some(z0) = z0 {
                    b.x(z0);
                }
            });
            b.free(c);
            prof(b, "i.prep");
        b793a_eopen(b, self, w);
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
                norm_bottom(b, self, &self.x, &f, None); FX0_FUN.with(|c| c.set(b.ops.len())); if std::env::var_os("FIXX0_DBG").is_some() { eprintln!("FIXX0 funnel slot {} op {} f {:?}", p3_cur_slot(), b.ops.len(), f.iter().map(|q| q.0).collect::<Vec<_>>()); }
                (f, vec![ay], None)
            } else {
                let sx = b.alloc_n(R_BITS);
                let sy = b.alloc_n(R_BITS);
                norm_bottom(b, self, &self.x, &sx, None);
                norm_bottom(b, self, &self.y, &sy, y_act);
                (sx, sy, None)
            }
        } else if term(w) && ns0 {
            // R12_TERM: finish X's funnel and erase ax before binding ay.
            // act is the separate z0 flag; X normalization does not modify Y or act.
            // The passenger dirty pool is restored by each X helper. No live-data reset.
            let late_y = r3_flag("R12_TERM");
            if r9_rt('b') && ytop_host() && lb_host() && host_free() {
                let q = self.y[W - 1];
                if !r9_rt_break("b") { b.x(q); }
                zero_probe(b, &[q]);
                b.free(q);
                self.y[W - 1] = NOQ;
                if r9_p2n() { self.cap -= 1; }
                r9_p2_shift(false);
                r9yt = true;
            }
            prof(b, "i.prep");
        b793a_eopen(b, self, w);
            let ax = b.alloc();
            let mut ay = if late_y { None } else { Some(b.alloc()) };
            and_auto(b, self, &[(self.x[0], true), (self.x[1], false)], ax);
            if let Some(ay) = ay {
                let mut l = act_lits(y_act);
                l.extend([(self.y[0], true), (self.y[1], false)]);
                and_auto(b, self, &l, ay);
            }
            for i in 0..NB { b.cswap(ax, self.x[i], self.x[i + 1]); }
            if let Some(ay) = ay {
                for i in 0..NB { b.cswap(ay, self.y[i], self.y[i + 1]); }
            }
            let f = b.alloc_n(R_BITS);
            norm_bottom(b, self, &self.x, &f, None); FX0_FUN.with(|c| c.set(b.ops.len())); if std::env::var_os("FIXX0_DBG").is_some() { eprintln!("FIXX0 funnel slot {} op {} f {:?}", p3_cur_slot(), b.ops.len(), f.iter().map(|q| q.0).collect::<Vec<_>>()); }
            b.cx(ax, f[0]);
            let mut l = vec![(f[0], false)];
            l.extend(f[1..].iter().map(|&q| (q, true)));
            erase_and(b, self, ax, &l);
            b.free(ax);
            if late_y && m94p {
                // R14 misc94 p: act is not formed yet. Where Y[0] = 0 the counter c = !Y[0..] is nonzero, so there
                // act = !([LA[..ln] == 0] & [c != 0]) = [LA[..ln] != 0]: a_Y = act & !Y0 & Y1 = !Y0 & Y1 & [LA[..ln] != 0]
                // on every basis state, formed as AND(!Y0, Y1) ^ AND(!Y0, Y1, LA[..ln] == 0)
                let q = b.alloc();
                let l = [(self.y[0], true), (self.y[1], false)];
                and_auto(b, self, &l, q);
                let mut l3 = l.to_vec();
                l3.extend(r9_zero_lits(&self.la[..len_n(w)]));
                if !r14m_break("p2") { and_auto(b, self, &l3, q); }
                for i in 0..NB { b.cswap(q, self.y[i], self.y[i + 1]); }
                ay = Some(q);
            } else if late_y {
                let q = b.alloc();
                let mut l = act_lits(y_act);
                l.extend([(self.y[0], true), (self.y[1], false)]);
                and_auto(b, self, &l, q);
                // Test-only wrong Y-shift control must be caught by traversal.
                if cfg!(test) && r3_flag("R12_TERM_BREAK") { b.x(q); }
                for i in 0..NB { b.cswap(q, self.y[i], self.y[i + 1]); }
                ay = Some(q);
            }
            (f, vec![ay.unwrap()], None)
        } else {
        prof(b, "i.prep");
        b793a_eopen(b, self, w);
        // decode prep: normalised cofactor windows (slacks sX, sY)
        // NORM-STAGE0: c_r = [ring slack >= 2], a_r = [ring slack == 1]; only the a-shift (the funnel's stage 0) here
        // R4-SITES R4_SWCXY (cap < 573, SWF-LEX): after the a-shift c_x = !X[0] and c_y = act & !Y[0] on every basis
        // state (slack 0: X[0] = 1; slack 1: shifted, X[0] = 1; slack >= 2: X[0] = X[1] = 0, unshifted), and the decode
        // (WGT_TOP1) leaves lane 0 untouched, so the rule reads X[0] / Y[0] and c_x, c_y take no lanes. Exact.
        let cxy_lit = ns0 && swf_lex() && (below805(self.cap) || r3_flag("R4_SWCXY_ANYCAP")) && r3_flag("R4_SWCXY");
        let (mut sx, mut sy, cxy) = if ns0 && cxy_lit {
            let (ax, ay) = (b.alloc(), b.alloc());
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
            (vec![ax], vec![ay], None)
        } else if ns0 {
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
        // b793b F12 (dev knob B793_F12=1): R8_IUNSW's release of LA / LB bits hb..7 (bound raised by 31 for LA + sX, LB + sY) opens here on the late slots
        // instead of after the un-swap: the swap decode runs on the bound view, 4 lanes fewer from slot ~190 on. The un-swap's own open returns early (already open).
        if b793_f12() && r3_flag("R8_IUNSW") && (189..=254).contains(&p3_cur_slot()) && r8_hb() >= R8_TOP {
            R8_OFF.with(|c| c.set(if b793b_break("f121") { 0 } else { (1 << R_BITS) - 1 }));
            r8_lhf_open(b, self, w);
            R8_OFF.with(|c| c.set(0));
            if std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE f12 slot {} hb {}", p3_cur_slot(), r8_hb()); }
        }
        // I2: u = LA + sX, v = LB + sY (cofactor bit lengths mX = W - 1 - u, mY = W - 1 - v):
        // sw = act & (mY < mX | mY == mX & winY <= winX)
        // b793a F12 (B793A_F12): on the late plain-compare slots (189-254) u = LA + sX < 128 and v = LB + sY < 128 by the windows the parent's
        // rows already rest on (R3_LATOP: u <= lad.1 + 31, R8_LHF: hb), so lanes 7 and 8 of LA and LB are |0> through the decode: they leave the
        // adders / comparators (7-lane views, exact: no carry out of bit 6) and are free for the decode's transients (sw, gt, c0, the pool);
        // every one is |0> again and re-acquired by id after the compare. The cap is not changed (the room grows, room-driven shapes may get cheaper).
        let f12 = b793a_f12() && swf_lex() && !w.act_const && w.slot >= 189 && w.slot <= 254 && w.mxp >= NB + 1
            && w.lad.1 + 31 < 128 && w.lb.1 + 31 < 128 && 256 - w.mx.min(256) + 31 < 128;
        let mut f12_lanes: Vec<QubitId> = vec![];
        if f12 {
            for q in [self.la[LB_BITS - 2], self.la[LB_BITS - 1], self.lb[LB_BITS - 2], self.lb[LB_BITS - 1]] {
                assert!(q != NOQ && !b.is_free(q), "B793A F12: slot {} lane not bound", p3_cur_slot());
                if !f12_lanes.contains(&q) { f12_lanes.push(q); }
            }
            if std::env::var_os("B793_DBG").is_some() { eprintln!("B793AF12 fire slot {} lanes {}", p3_cur_slot(), f12_lanes.len()); }
        }
        let nv = if f12 { LB_BITS - 2 - b793a_brk("f12short") as usize } else { LB_BITS };
        if !f12_lanes.is_empty() {
            add_sm(b, self, &self.la[..nv], &sx, false, false);
            add_sm(b, self, &self.lb[..nv], &sy, false, false);
            zero_probe(b, &f12_lanes);
            b.free_n(&f12_lanes);
        } else {
        add_sm(b, self, &self.la, &sx, false, false);
        add_sm(b, self, &self.lb, &sy, false, false);
        }
        let sw = b.alloc();
        // b792 P6 (B792_P6): on the act-constant plain-window slots the swap decode is ONE wide compare, no gt / core / c0 lane.
        // sw = [(u, wY) <= (v, wX)] with u = LA + sX, v = LB + sY and wX / wY the NB-1 low-index window lanes as the low bits:
        // u < v | u == v & wY <= wX, exactly the parent's lt | eq & !gt with gt = [wY > wX]. The Cuccaro ladder runs on the
        // concatenated lanes with the constant-1 lane Y[W-1] as carry-in (restored), the rule's X[0] / Y[0] literals gate
        // the carry onto sw through one borrowed dirty lane.
        let p6yh = if b792_p6() && swf_lex() && f12_lanes.is_empty() && w.mxp >= NB + 1 && w.act_const && act.is_none() && cxy.is_none()
            && !b792_brk("p6off") { r14_ytop(self) } else { None };
        if let Some(one) = p6yh {
            let lo = if wgt_top1() && norm_stage0() { 1 } else { 0 };
            let (mut lav, mut lbv) = if r8_hb() < R8_TOP { (r8_live(&self.la), r8_live(&self.lb)) } else { (self.la.to_vec(), self.lb.to_vec()) };
            if r8_hb() < R8_TOP && lav.last() == lbv.last() { lav.pop(); lbv.pop(); }
            let mut av: Vec<QubitId> = (lo..NB).rev().map(|i| self.y[i]).collect();
            av.extend(lav);
            let mut bv: Vec<QubitId> = (lo..NB).rev().map(|i| self.x[i]).collect();
            bv.extend(lbv);
            assert!(av.len() == bv.len() && !av.iter().chain(&bv).any(|&q| q == NOQ), "b792 P6: operand lanes");
            if cxy_lit {
                b.x(self.y[0]);
                b.cx(self.y[0], sw);
                b.x(self.y[0]);
            }
            let ru = super::arith::up(b, &av, &bv, one);
            b.play(&ru, false);
            let top = bv[bv.len() - 1];
            if cxy_lit {
                if !b792_brk("p6a") { super::mask::ccc_dirty(b, top, self.x[0], self.y[0], sw); }
            } else {
                b.cx(top, sw);
            }
            b.play(&ru, true);
        } else if let Some(h) = (b792_p6() && swf_lex() && f12_lanes.is_empty() && w.mxp < NB + 1 && w.act_const && act.is_none() && cxy.is_none()
            && !b792_brk("p6off")).then(|| r14_ytop(self)).flatten() {
            // b792 P6, masked slots: gt lives on the constant-1 lane Y[W-1] (flipped to |0>) instead of a fresh lane, and core is
            // never stored: the LA / LB compare (lane-free Cuccaro ladder, carry-in gt) is gated onto sw by the rule's X[0] / Y[0] literals
            let gt = h;
            b.x(gt);
            let th = (below805(self.cap) && r3_flag("R4_SWT")).then_some(sw);
            window_gt_hh(b, self, Some(gt), w, th, None);
            b.x(gt); // gt = [wY <= wX] (the parent's flipped gt)
            let (mut lav, mut lbv) = if r8_hb() < R8_TOP { (r8_live(&self.la), r8_live(&self.lb)) } else { (self.la.to_vec(), self.lb.to_vec()) };
            if r8_hb() < R8_TOP && lav.last() == lbv.last() { lav.pop(); lbv.pop(); }
            assert!(lav.len() == lbv.len() && !lav.iter().chain(&lbv).any(|&q| q == NOQ), "b792 P6m: operand lanes");
            if cxy_lit {
                b.x(self.y[0]);
                b.cx(self.y[0], sw);
                b.x(self.y[0]);
            }
            let ru = super::arith::up(b, &lav, &lbv, gt);
            b.play(&ru, false);
            let top = lbv[lbv.len() - 1];
            if cxy_lit {
                if !b792_brk("p6b") { super::mask::ccc_dirty(b, top, self.x[0], self.y[0], sw); }
            } else {
                b.cx(top, sw);
            }
            b.play(&ru, true);
            b.x(gt);
            erase_mbu(b, gt, |b| window_gt_hh(b, self, None, w, None, None));
            zero_probe(b, &[gt]);
            b.x(gt);
        } else
        if swf_lex() {
            // SWF-LEX: lt | eq & !gt = [LA < LB + !gt]
            let gt = b.alloc();
            let th = (below805(self.cap) && r3_flag("R4_SWT")).then_some(sw);
            // R14 läckBobby S / T: Y[W-1] = 1 here on every shot (SWAP-PRUNE / YTOP-HOST: Y = B is top-normalised and
            // nothing from the slot's start to the rows writes lane W-1), so it hosts the window compare's prefix lane
            // and the core lane where the cap leaves no lane for them
            let yh = r14_ytop(self);
            window_gt_hh(b, self, Some(gt), w, th, yh);
            let flip = !cr_break(2);
            if flip { b.x(gt); }
            let core_h = yh.filter(|_| r14p_on('T', self.room(b), 1));
            let core = if let Some(h) = core_h {
                r14p_log('T', b, self.room(b));
                if !r14p_brk("t") { b.x(h); }
                zero_probe(b, &[h]);
                h
            } else { b.alloc() };
            lt_cin_sm(b, self, &self.la[..nv], &self.lb[..nv], gt, Some(core));
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
            } else if cxy_lit {
                // R4_SWCXY: sw = act & core & X[0] & Y[0] ^ act & !Y[0] (the rule above with c_x, c_y as literals)
                let brk = if cfg!(test) { std::env::var("W2_BREAK_NORM").unwrap_or_default() } else { String::new() };
                let mut l = act_lits(act);
                l.push((core, false));
                if brk.trim() != "2" {
                    l.push((self.x[0], false));
                }
                l.push((self.y[0], false));
                and_auto(b, self, &l, sw);
                if brk.trim() != "1" {
                    b.x(self.y[0]);
                    act_cx(b, act, self.y[0], sw);
                    b.x(self.y[0]);
                }
            } else {
                act_cx(b, act, core, sw);
            }
            erase_mbu(b, core, |b| lt_cin_sm(b, self, &self.la[..nv], &self.lb[..nv], gt, None));
            if core_h.is_some() {
                // R14 läckBobby T: core is |0> again (measured); Y[W-1] back to 1
                zero_probe(b, &[core]);
                if !r14p_brk("t") { b.x(core); }
            } else {
                b.free(core);
            }
            if flip { b.x(gt); }
            erase_mbu(b, gt, |b| window_gt_hh(b, self, None, w, None, yh));
            b.free(gt);
            for &q in &f12_lanes { assert!(b.is_free(q), "B793A F12: lent lane q{} not returned", q.0); b.acquire(q); }
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
        // R8-LANE799 R8_IUNSW: from the un-swap to I6 LA and LB hold plain lengths, or (OFF-KEEP) LA + sX and LB + sY
        // with sX, sY < 2^R_BITS: R8_LHF / R8_M8 release the same lanes with the bound raised by 31
        let r8u = r3_flag("R8_IUNSW");
        if r8u {
            R8_OFF.with(|c| c.set((1 << R_BITS) - 1 - if r8_break("iunsw") { 31 } else { 0 }));
            r8_lhf_open(b, self, w);
            r8_m8_open(b, self, w);

            R8_OFF.with(|c| c.set(0));
        }
        // I3, I4
        b.z_if(sw, bits.sw);
        if r14_break("lb8") && r14_parts('B') && keep && !r8_m8() && r8_hb() >= R8_TOP && w.act_const {
            // losgahts negative control (gate tests only): LB[8] probed and freed before the un-swap (it then holds the
            // post-swap register's bit 8), bound fresh again after it
            let q = self.lb[LB_BITS - 1];
            zero_probe(b, &[q]);
            b.free(q);
            self.lb[LB_BITS - 1] = b.alloc();
        }
        let (xn, ln) = swap_lanes(w, !keep);
        super::arith::cswap_regs(b, sw, &self.x[..xn], &self.y[..xn]);
        super::arith::cswap_regs(b, sw, &self.la[..ln], &self.lb[..ln]);
        super::arith::cswap_regs(b, sw, &sx, &sy);
        b.cx(sw, self.par);
        if keep {
            // OFF-KEEP: LA, LB hold LA + sX, LB + sY (one lane each); I5 here, on the plain registers inside its block
            prof(b, "i.swerase");
            erase_mbu(b, sw, |b| {
                r6t(b, "k0", self.room(b));
                add_sm(b, self, &self.la, &sx, false, true);
                r6t(b, "k.addla", self.room(b));
                if !mw_break(4) { add_sm(b, self, &self.lb, &sy, false, true); }
                r6t(b, "k.addlb", self.room(b));
                if let Some(z0) = z0 {
                    b.x(z0);
                }
                self.swap_flag(b, z0, None, w, false);
                if let Some(z0) = z0 {
                    b.x(z0);
                }
                r6t(b, "k.sf", self.room(b));
                if !mw_break(4) { add_sm(b, self, &self.lb, &sy, false, false); }
                r6t(b, "k.sublb", self.room(b));
                add_sm(b, self, &self.la, &sx, false, false);
                r6t(b, "k.subla", self.room(b));
            });
            b.free(sw);
            prof(b, "i.unswap");
            // losgahts B (R14_LA94): the bit-8 holiday starts here (see r14_la94)
            if r14_parts('B') && host_free() && lb_host() && sy_act_gate() && r3_flag("R8_IUNSW") {
                let q = self.lb[LB_BITS - 1];
                if r8_m8() && q != NOQ && self.la[LB_BITS - 1] == q && !b.is_free(q) {
                    zero_probe(b, &[q]);
                    b.free(q);
                    self.la[LB_BITS - 1] = NOQ;
                    self.lb[LB_BITS - 1] = NOQ;
                    self.cap -= 1;
                    LA94_B8.with(|c| c.set((2, q)));
                } else if !r8_m8() && r8_hb() >= R8_TOP && q != NOQ && !b.is_free(q) && w.act_const
                    && !r14_break("lb8") {
                    // v = LB + sY = CW - bl(tA') <= 255 (tA' >= 2 on an active shot)
                    zero_probe(b, &[q]);
                    b.free(q);
                    self.lb[LB_BITS - 1] = NOQ;
                    self.cap -= 1;
                    LA94_B8.with(|c| c.set((1, q)));
                }
                if std::env::var_os("R9_DBG").is_some() && LA94_B8.with(|c| c.get().0) > 0 {
                    eprintln!("LA94B fire slot {} mode {}", p3_cur_slot(), LA94_B8.with(|c| c.get().0));
                }
            }
        }
        if ns0 {
            // NORM-STAGE0: only the divisor ring X can still have slack (>= 2): the 5-stage funnel on X alone, then
            // sX = funnel + a_X (exclusive: a_X = 1 leaves slack 0), and a_X = [sX == 1] erased
            let ax = sx[0];
            // R9_LU: plain LA (bit 8 |0>) while the funnel's lanes are taken; LA += sX after ax is gone
            let r9lu = r9_lu() && keep && !r8_m8() && self.la[LB_BITS - 1] != NOQ;
            if r9lu {
                if !r3_flag("R9_LU_BREAK") { add_sm(b, self, &self.la, &[ax], false, true); }
                zero_probe(b, &[self.la[LB_BITS - 1]]);
                b.free(self.la[LB_BITS - 1]);
                self.la[LB_BITS - 1] = NOQ;
                self.cap -= 1;
                if std::env::var_os("R9_DBG").is_some() { eprintln!("R9LU fire slot {}", p3_cur_slot()); }
            }
            // H793 "Rösti" (dev knob H793_RST): a_X is folded back into X before the funnel instead of being carried
            // through it. LA = LA + a_X loses a_X first (R9_LU's own subtraction; on the bound view while LA[8] is out),
            // the a-shift is undone under a_X (its cswap ladder reversed: X gets its slack-1 layout back), a_X =
            // [X[0] == 0 & X[1] == 1] is erased on X's two bottom lanes (the predicate it was formed from at the prep;
            // the un-swap moved Y's act-gated a_Y here only where sw = 1, i.e. on active shots), and the funnel then
            // runs all 5 stages (SW-CARRY's form: its stage 0 is the a-shift's lane map) and returns sX itself. One
            // lane fewer at the funnel's allocation (f without a_X). After the funnel the state is the parent's.
            let rst = h793_rst() && keep && ax != NOQ;
            if rst {
                if !r9lu {
                    if LA94_B8.with(|c| c.get().0) == 2 { let lv = la94_view(&self.la); add_sm(b, self, &lv, &[ax], false, true); }
                    else { add_sm(b, self, &self.la, &[ax], false, true); }
                }
                if !super::mask::h793_brk("rst") { for i in (0..NB).rev() { b.cswap(ax, self.x[i], self.x[i + 1]); } }
                erase_and(b, self, ax, &[(self.x[0], true), (self.x[1], false)]);
                b.free(ax);
                if std::env::var_os("R14F_DBG").is_some() { eprintln!("H793RST fire slot {} r9lu {} live {}", p3_cur_slot(), r9lu as u8, b.live); }
            }
            // b792 P7 (B792_P7): a_Y folded back into Y before the funnel, as Rosti does for a_X (a_Y lives one lane for
            // the whole funnel otherwise). After the un-swap sY[0] = act & [Y0 == 0 & Y1 == 1] on the unshifted Y (sw = 1
            // implies act = 1, and a_X carries no act literal), so the a-shift ladder is undone under it and it is erased
            // on Y's two bottom lanes; it is formed and shifted again after the funnel (Y is untouched by the funnel).
            let p7y = b792_p7() && keep && p3_cur_slot() <= 232 && sy.len() == 1 && sy[0] != NOQ;
            if p7y {
                let ay = sy[0];
                if !b792_brk("p7a") { for i in (0..NB).rev() { b.cswap(ay, self.y[i], self.y[i + 1]); } }
                let mut l = act_lits(y_act);
                l.extend([(self.y[0], true), (self.y[1], false)]);
                erase_and(b, self, ay, &l);
                b.free(ay);
            }
            let f = b.alloc_n(R_BITS);
            norm_bottom(b, self, &self.x, &f, None); FX0_FUN.with(|c| c.set(b.ops.len())); if std::env::var_os("FIXX0_DBG").is_some() { eprintln!("FIXX0 funnel slot {} op {} f {:?}", p3_cur_slot(), b.ops.len(), f.iter().map(|q| q.0).collect::<Vec<_>>()); }
            if rst {
                // f = sX: LA = LA_plain + sX = u (R9_LU: LA[8] bound again first)
                if r9lu && b793_lahold_slot(w) {
                    // b793b LAHOLD: LA[8] stays out (the cap stays lowered), LA += sX mod 2^8
                    let lv: Vec<QubitId> = self.la[..LB_BITS - 1].to_vec();
                    add_sm(b, self, &lv, &f, false, false);
                    B793_LAHOLD.with(|c| c.set(true));
                }
                else if r9lu { self.la[LB_BITS - 1] = b.alloc(); self.cap += 1; add_sm(b, self, &self.la, &f, false, false); }
                else if LA94_B8.with(|c| c.get().0) == 2 { let lv = la94_view(&self.la); add_sm(b, self, &lv, &f, false, false); }
                else { add_sm(b, self, &self.la, &f, false, false); }
            } else {
            if keep && !r9lu {
                // OFF-KEEP: LA = LA + a_X already; the funnel's part (0 where a_X = 1) goes on now
                // losgahts B: on the bound view while LA[8] is out (u <= 255, R8_M8's bound)
                if LA94_B8.with(|c| c.get().0) == 2 {
                    let mut lv = la94_view(&self.la);
                    if r14_break("lav") { lv.truncate(lv.len() - 1); }
                    add_sm(b, self, &lv, &f, false, false);
                }
                else { add_sm(b, self, &self.la, &f, false, false); }
            }
            b.cx(ax, f[0]);
            let mut l = vec![(f[0], false)];
            l.extend(f[1..].iter().map(|&q| (q, true)));
            erase_and(b, self, ax, &l);
            b.free(ax);
            if r9lu && b793_lahold_slot(w) {
                // b793b LAHOLD: LA[8] stays out (the cap stays lowered), LA += sX mod 2^8
                let lv: Vec<QubitId> = self.la[..LB_BITS - 1].to_vec();
                add_sm(b, self, &lv, &f, false, false);
                B793_LAHOLD.with(|c| c.set(true));
                if std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE lahold slot {}", p3_cur_slot()); }
            } else if r9lu {
                self.la[LB_BITS - 1] = b.alloc();
                self.cap += 1;
                // f = sX now: LA = LA + sX = u
                add_sm(b, self, &self.la, &f, false, false);
            }
            }
            if p7y { sy = vec![NOQ]; p7y_pend = true; }
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
            self.swap_flag(b, z0, None, w, false);
            if let Some(z0) = z0 {
                b.x(z0);
            }
        });
        b.free(sw);
        }
        // R9_LB: LB's released lanes stay unbound until KT-HOST frees LB[5..9) (kt runs mod 2^hb)
        // (not where KT-HOST's sign clear runs: without SY_ACT_GATE it CXs LB[8] into LB[5..8), lanes left unbound here)
        let r9lb_hb = (r9_lb() && (keep || b793_s255(w)) && free_mode && lb_host() && r3_flag("R8_IUNSW") && r8_hb() < R8_TOP
            && r8_hb() > R_BITS && (sy_act_gate() || w.act_const)).then(|| r8_hb());
        r5tl(b, "r8c0");
        if r3_flag("R8_IUNSW") {
            r8_m8_close(b, self);
            r8_lhf_close_kk(b, self, r9lb_hb.is_some(), r9lb_hb.is_some() && b792_s255(w));
        }
        r5tl(b, "r8c1");
        if let Some(hb) = r9lb_hb {
            self.cap -= (R8_TOP - hb) as u64;
            if std::env::var_os("R9_DBG").is_some() { eprintln!("R9LB fire slot {} hb {hb}", p3_cur_slot()); }
        }
        prof(b, "i.rows");
        p3(b, self, "i.rows");
        r5tl(b, "rows0");
        // I6: u = LA + sX in LA, kt = u - (LB + sY) = mY - mX in LB; rows; r = act & (sX - sY - j_last)
        // I5-LANES L3 (SYFOLD): LB += sY; LB = ~LB + LA + 1 is LB = ~LB + LA + !sY, with sY's own lane (negated) as the
        // adder's quantum carry-in: no zero-extension of sY, no extra carry lane
        let syfold = i5_syfold() && !keep && sy_len == 1 && sy.len() == 1;
        if !keep {
            // negative control (gate tests only): B793_BREAK=s255la adds sX on a 1-lane-short view of LA (carries into LA[hb-1] are lost; NOTE this control PASSED 16/16 at 1 lane short and fails by a structural assert at 3: the add and its undo share the view, so it is not a valid control; see REPORT-S255)
            let lav = if b792_s255(w) { let mut v = self.la_bound_prefix(); if b793b_break("s255la") { v.truncate(v.len() - 1); } v } else { self.la.clone() };
            add_sm(b, self, &lav, &sx, false, false);
            // b793b S255: LB's bits hb..8 are unbound here (R9_LB form on the last slot): LB + sY < 2^hb on the window's shots
            let lbv: Vec<QubitId> = match r9lb_hb { Some(hb) if b793_s255(w) => self.lb[..hb - 3 * b793b_break("s255") as usize].to_vec(), _ => self.lb.clone() };
            if !syfold { add_sm(b, self, &lbv, &sy[..sy_len], false, false); }
        }
        // R9_LB: kt = ~v + u + 1 mod 2^hb on LB[0..hb), LA[0..hb) (negative control R9_LB_BREAK: one lane short)
        let la94b = LA94_B8.with(|c| c.get());
        let (ktl, kta): (Vec<QubitId>, Vec<QubitId>) = match r9lb_hb {
            Some(hb) => { let n = hb - r3_flag("R9_LB_BREAK") as usize - 4 * (b793_s255(w) && b793b_break("s255")) as usize; (self.lb[..n].to_vec(), self.la[..n].to_vec()) }
            // losgahts B: kt mod 2^8 on LB[0..8), LA[0..8) while bit 8 is out
            None if la94b.0 > 0 => { let n = LB_BITS - 1 - r14_break("ktv") as usize; (self.lb[..n].to_vec(), self.la[..n].to_vec()) }
            None => (self.lb.clone(), self.la.clone()),
        };
        assert!(la94b.0 == 0 || !ktl.iter().chain(&kta).any(|&q| q == NOQ), "losgahts: kt view holds an unbound lane");
        for &q in &ktl {
            b.x(q);
        }
        if syfold {
            b.x(sy[0]);
            add_on_sm(b, self, &ktl, &kta, false, false, sy[0], true);
            b.x(sy[0]);
        } else {
            add_sm(b, self, &ktl, &kta, true, false);
        }
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
                // R9_LB: the lanes left unbound at the un-swap's close are already free
                let bound: Vec<QubitId> = self.lb[R_BITS..lb_top].iter().copied().filter(|&q| q != NOQ).collect();
                b.free_n(&bound);
            } else {
                host.extend(&self.lb[R_BITS..lb_top]);
            }
        }
        if let Some(hb) = r9lb_hb { self.cap += (R8_TOP - hb) as u64; }
        if p7y_pend {
            // b792 P7: a_Y re-formed on the unshifted Y and shifted again (I6's kt and the LB release did not read sY or Y)
            assert!(sy.len() == 1 && sy[0] == NOQ && keep, "b792 P7: fold state");
            let q = b.alloc();
            let mut l = act_lits(y_act);
            l.extend([(self.y[0], true), (self.y[1], false)]);
            and_auto(b, self, &l, q);
            for i in 0..NB { b.cswap(q, self.y[i], self.y[i + 1]); }
            sy = vec![q];
            p7y_pend = false;
        }
        if la94b.0 > 0 {
            // losgahts B: the holiday ends; LB[8] keeps the freed id (KT-HOST's parent frees it here), LA[8] is bound
            // fresh |0> (u <= 255) where it was the shared lane
            assert!(self.lb[LB_BITS - 1] == NOQ, "losgahts: LB[8] re-bound during the holiday");
            self.lb[LB_BITS - 1] = la94b.1;
            if la94b.0 == 2 {
                assert!(self.la[LB_BITS - 1] == NOQ);
                self.la[LB_BITS - 1] = b.alloc();
                self.cap += 2;
            } else {
                self.cap += 1;
            }
            if B793_LAHOLD.with(|c| c.replace(false)) {
                // b793b LAHOLD: LA[8] bound fresh with bit 8 of u = [u mod 256 < sX] = [LA[5..8) == 0] & [LA[0..5) < sX]
                assert!(la94b.0 == 1 && self.la[LB_BITS - 1] == NOQ && sx.len() == R_BITS, "b793 LAHOLD: holiday state");
                self.la[LB_BITS - 1] = b.alloc();
                self.cap += 1;
                if b792_lt5() {
                    // b792 LT5: LA[8] ^= [LA[5..8) == 0] & [LA[0..5) < sX] with the AND taken inside the compare's window (the
                    // borrow sits on sX[4] between the Cuccaro up and its inverse): no lt5 lane, one compare instead of two
                    let lits0: Vec<(QubitId, bool)> = (R_BITS..LB_BITS - 1).map(|i| (self.la[i], true)).collect();
                    let a5: Vec<QubitId> = self.la[..R_BITS].to_vec();
                    let tgt = self.la[LB_BITS - 1];
                    let brk = b793b_break("lah1");
                    let me: &GreedyFrog = &*self;
                    b792_lt5_fold(b, &a5, &lits0, &sx, tgt, &mut |b, l, o| { if !brk { and_auto(b, me, l, o); } });
                } else {
                let lt5 = b.alloc();
                lt_sm(b, self, &self.la[..R_BITS], &sx, Some(lt5));
                let mut lits: Vec<(QubitId, bool)> = (R_BITS..LB_BITS - 1).map(|i| (self.la[i], true)).collect();
                lits.push((lt5, false));
                if !b793b_break("lah1") { and_auto(b, self, &lits, self.la[LB_BITS - 1]); }
                lt_sm(b, self, &self.la[..R_BITS], &sx, Some(lt5));
                b.free(lt5);
                }
            }
            LA94_B8.with(|c| c.set((0, NOQ)));
        }
        // (merge with la94: after losgahts B, so LA[8] is bound again)
        if m94p {
            // R14 misc94 p: I1's flag z0 = [LA[..ln] == 0] & [c != 0], formed here on I1's own state: LA -= sX undoes I6's
            // LA += sX, and the counter lanes Y[0..] are I1's wherever the Y a-shift fired (a_Y = 1 needs LA != 0, so
            // z0 = 0 there either way). Nothing from I1 to here reads z0 / act (the term slot skips I2-I5, a_Y is formed
            // without act, I6's kt and LB host do not read it); Z0-DEFER's z_if is the same phase on the same function.
            let lav = if b792_s255(w) { self.la_bound_prefix() } else { self.la.clone() };
            if !r14m_break("p") { add_sm(b, self, &lav, &sx, false, true); }
            let z = self.m94_i1_z0(b, w, bits);
            if !r14m_break("p") { add_sm(b, self, &lav, &sx, false, false); }
            b.x(z);
            z0 = Some(z);
            act = z0;
            y_act = if sy_act_gate() { act } else { None };
        }
        if r9yt {
            // R9 rowtmp b: Y[W-1] back (= 1) once LB's lanes 5.. are released
            if r9_p2n() { self.cap += 1; }
            r9_p2_shift(true);
            self.y[W - 1] = b.alloc();
            b.x(self.y[W - 1]);
        }
        let masked_rows = w.mx < NB + 1;
        r5tl(b, "lbhost");
        // LA-HOST: u' = NB - mX in 0..NB here
        // (act-constant slots only: a finished shot's u' is far below -32)
        // R5-FIT799 R5_NEAR8 (cap < 573, APPROXIMATE): LA-HOST also where the divisor bound is only <= NB + 64; a shot
        // whose decode-time divisor is longer than NB + 32 there (u' < -32) fails (priced by `r5_mx_tail` and pab)
        let near8 = !w.dtop_near && w.dtop_n64 && below805(self.cap) && r3_flag("R5_NEAR8");
        let la_cut = la_host() && free_mode && masked_rows && (w.dtop_near || near8) && w.act_const;
        if cfg!(test) && r3_flag("R8_DBGW") {
            eprintln!("R8W slot {} masked {} near {} n64 {} tight {} act_const {} mx {} mxp {} dtop {} lad {:?} lb {:?} free_mode {}",
                      w.slot, masked_rows, w.dtop_near, w.dtop_n64, w.dtop_tight, w.act_const, w.mx, w.mxp, w.dtop, w.lad, w.lb, free_mode);
        }
        // R5-FIT799 R5_LAH6 (cap < 573): where the divisor bound is <= NB + 64 (not <= NB + 32), u' lies in -64..NB, so
        // LA[6..8) are copies of the sign: CX-cleared, freed, re-bound and restored as LA-HOST does with LA[5..8)
        // (envelope class: LA-HOST's own, the DIV-TOP bound)
        let la6 = !la_cut && la_host() && free_mode && masked_rows && !w.dtop_near && w.dtop_n64 && w.act_const
            && below805(self.cap) && r3_flag("R5_LAH6");
        // R11_LA5 (fable, 797): on the la6 slots LA holds u'' = u' + c through the masked stretch, c = (unclipped divisor
        // bound) - (NB + 32) >= 1, so u'' >= -32 is the DIV-TOP bound itself (la6's class) and u'' <= 31 holds on every
        // shot with mX >= c - 6 (weaker than the mx window the plain rows already rest on): LA[5..8) are then all sign
        // copies and LA[5] is freed with LA[6..8). The masked rows read u'' (division_rows: big_0 = sign | ![u'' >= c]
        // by a comparator, every row constant + c, the decoder's matched values + c, and mask::TVMAX keeps the decoder
        // from writing at lanes whose matched value is >= 32, which only a shot with mX < c - 6 could own). The cap is
        // lowered by one in between so every room-driven choice is unchanged. Not with a pending gated stall repair
        // (MJ_PEND / R4_PEND read the full LA value).
        let pend_gated = MJ_PEND.with(|p| p.borrow().as_ref().map_or(false, |(_, g)| *g))
            || R4_PEND.with(|p| p.borrow().as_ref().map_or(false, |(_, g)| *g));
        let la5c = if la6 && r3_flag("R11_LA5") && !pend_gated { w.dtop_u.saturating_sub(NB + 32) } else { 0 };
        let la5 = la5c >= 1 && la5c + NB <= 31 + w.mx && la5c <= 31;
        let la5c = if la5 { la5c } else { 0 };
        if cfg!(test) && r3_flag("R8_DBGW") { eprintln!("R11LA5 slot {} la6 {} la5 {} c {} dtop_u {} mx {}", w.slot, la6 as u8, la5 as u8, la5c, w.dtop_u, w.mx); }
        if masked_rows {
            add_const_sm(b, self, &self.la, UOFF - la5c, true);
        }
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
        // R11_LA5: LA[5] too (u'' in -32..31)
        let la6_lo = if la5 { R_BITS } else { R_BITS + 1 };
        if la6 {
            for i in la6_lo..LB_BITS - 1 {
                if !(i == R_BITS + 1 && r5_break("lah6")) { b.cx(self.la[LB_BITS - 1], self.la[i]); }
            }
            zero_probe(b, &self.la[la6_lo..LB_BITS - 1]);
            b.free_n(&self.la[la6_lo..LB_BITS - 1]);
            if la5 { self.cap -= 1; }
        }
        // Masked-row slots park the divisor window's junk when the cap leaves room for it beside the plain rows'
        // temporaries, r, a1 and the sweep's chain; every row then runs plain (and pooled where room is left).
        let top = if div_top_bound() { w.dtop.max(w.mx).min(NB) } else { NB };
        let zn = top - park_lo(w).min(top);
        let room_park = self.room(b);
        let park_std = masked_rows && (force_park() || room_park >= zn + park_reserve());
        let ytop = ytop_host();
        // R14 misc94 y: Y[W-1]'s deferred re-bind (Some(set to 1)), done before the I10 value ladder
        let mut m94y: Option<bool> = None;
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
        assert!(!la5 || (!park && !split && partial.is_none()), "R11_LA5: the slot took a park path");
        let mut z = if park { b.alloc_n(zn) } else if partial.is_some() { b.alloc_n(zp) } else { vec![] };
        if park {
            park_junk(b, self, w, &z, top);
        } else if let Some(lo_p) = partial {
            park_junk_partial(b, self, &z, top, lo_p);
        }
        p3(b, self, "i.rowsrun");
        // R3-FIT799 R3F_SLIM (cap < 573): on plain-row slots the sweep's g and jl are |0> and only lent to the rows
        // pools; they are taken after the rows pass (attach) and given back after the backward sweep (detach), so the
        // rows pool takes the same lanes from the room instead
        let slim = !split && !(masked_rows && !park) && below805(self.cap) && r3_flag("R3F_SLIM");
        let r5p4v = std::env::var("R5_PRE4").ok().and_then(|v| v.trim().parse::<u8>().ok()).unwrap_or(0);
        // R5_PRE4=3: undo rows only, and only on slots without LA-HOST's near bound (the 8 slots it does not reach)
        let r5p4 = masked_rows && !park && !split && !slim && partial.is_none() && below805(self.cap) && r5p4v > 0
            && (r5p4v != 3 || !w.dtop_near);
        // R10_P4F (claude-r8): where the masked RowTmp does not fit, its prefix lane 4 is bound only after the rows pass
        // (R5_PRE4=1's form on this slot), and after X0-HOST's X[0] release where that follows the rows
        let r10p4f = r5p4 && r5p4v != 1 && r10_on("R10_P4F", self.room(b), 10);
        let r5p4f = r5p4 && (r5p4v == 1 || r10p4f);
        // R12_PF3 (fable 796b): the forward masked rows on a 3-lane retained prefix (lanes 3, 4 bound at the sweep)
        // R9_PREFIX A (r9 prefix; see the release before the RowTmp below): the slot class, then the room gate
        let r9a_base = x0_host() && ns0 && (w.act_const || q792_x0na()) && free_mode && r5p4f && masked_rows && !park
            && !split && !slim && partial.is_none() && below805(self.cap) && r3_flag("R5_FOLD") && r3_flag("R5_MPOOL");
        let r9a = r9a_base && r9p_on('A', self.room(b), 8);
        // R9_PREFIX P: with A the forward rows read no zero source, so RowTmp's y is bound only for the sweep (after
        // X0-HOST's release point) and its lane holds the masked decoder's fourth prefix lane through the rows instead
        // (R5_PRE4's 4-lane RSHORT form, not R12_PF3's 3-lane one)
        let r9y = r9a && r9p('P') > 0;
        let r12pf3 = r5p4f && !r9y && r10_on("R12_PF3", self.room(b), 11);
        // R14 läckBobby-b F: on R9_PREFIX P slots where the 8-lane masked RowTmp does not fit, R12_PF3's 3-lane prefix (lane
        // 3 bound at the sweep, as R12_PF3 does) with the bit-1 level on the AND temp instead of RSHORT2's borrowed lane
        let r14f = r9y && r14b_on('F', self.room(b), 8);
        if r14f { r14p_log('F', b, self.room(b)); }
        // R14 läckBobby-b U planned on the F slots: the forward plain rows then run unrolled (see `r14b`)
        let r14u_plan = r14f && r14b('U') > 0;
        let r12pf3 = r12pf3 || r14f;
        // R12_JLF (fable 796b): the sweep's jl lane 4 is the mask's idle flag lane f (|0> from the end of the forward
        // rows to the undo rows; jl[4] is X-measured and reset before the undo rows read f again): no lane bound
        let r12jlf = r5p4f && r10_on("R12_JLF", self.room(b), 11);
        if r10("R10_DBG") == 3 { eprintln!("R10P4 slot {} masked {} park {} split {} slim {} partial {:?} near {} room {} live {} cap {} r5p4 {} r10p4f {}", p3_cur_slot(), masked_rows as u8, park as u8, split as u8, slim as u8, partial, w.dtop_near as u8, self.room(b), b.live, self.cap, r5p4 as u8, r10p4f as u8); }
        if std::env::var_os("R9P_DBG").is_some() { eprintln!("R9PDBG slot {} k {} mx {} mxp {} dtop {} act_const {} masked {} la_cut {} la6 {} la5 {} park {} split {} slim {} partial {:?} r5p4 {} r10p4f {} r12pf3 {} r12jlf {} room {} live {} cap {} ytop {} free_mode {} keep {} syfold {} sylen {} act {}", p3_cur_slot(), w.k, w.mx, w.mxp, w.dtop, w.act_const as u8, masked_rows as u8, la_cut as u8, la6 as u8, la5 as u8, park as u8, split as u8, slim as u8, partial, r5p4 as u8, r10p4f as u8, r12pf3 as u8, r12jlf as u8, self.room(b), b.live, self.cap, ytop as u8, free_mode as u8, keep as u8, syfold as u8, sy_len, act.is_some() as u8); }
        // R9_PREFIX A (r9 prefix): on masked R5_FOLD slots with X0-HOST the forward rows run in the R5_FOLD form too
        // (the undo rows' own form, so the undo rows stay the exact inverse of the same recording): every masked row's
        // top two cells are written by hand, the plain rows read the cleared mask flag (set to 1) as X[0], so neither
        // the zero source y nor X[0] is read by the forward rows. X[0] = 1 (X0-HOST's premise) is then flipped to |0>
        // and released before the RowTmp is taken instead of after the rows pass; the cap is lowered by one until
        // X0-HOST's own release point, so every room-driven choice in between is unchanged.
        if r9a {
            r9p_log('A', b, self.room(b));
            // negative control (dev, inert unless set): R9_BRK=a releases X[0] still holding 1
            if !mw_break(5) && !super::mask::r9_brk("a") { b.x(self.x[0]); }
            zero_probe(b, &[self.x[0]]);
            b.free(self.x[0]);
            self.cap -= 1;
        }
        // R14 läckBobby W: on slim ROW-Y slots the zero source y is only a lent pool lane through both rows passes (the
        // rows never read it: ROW-Y writes the top lane's source by hand), and where R15-JC follows (every slim slot of the
        // B tree) it is released right after the forward rows. Where the cap leaves no lane for it, y is left unbound
        // (NOQ: a reader would emit an invalid op) and the cap is lowered by one until that release point, so every
        // room-driven choice in between is unchanged; the forward rows' pool is one lane shorter. Off R15-JC it is bound
        // fresh (|0>, lent as the parent's) at that point instead.
        let r14w = slim && !split && ytop_host() && lever("ROW_Y", ROW_Y) && r14p_on('W', self.room(b), 3);
        let mut r14j = false;
        let mut r14u = false;
        // b793b F6: no AND temp on the R9_PREFIX P / F / U slots (the only masked shape the NOTEMP forms cover)
        let f6 = b793_f6_slot(w) && masked_rows && r5p4f && r14f && r14u_plan && r9y && r9a && r12pf3 && r12jlf && !park && !split && partial.is_none() && !slim;
        if f6 && std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE f6 slot {}", p3_cur_slot()); }
        if std::env::var_os("B793A_LEDGER").is_some() {
            let st = |v: &[QubitId]| v.iter().map(|&q| if q == NOQ { '.' } else if b.is_free(q) { 'f' } else { '#' }).collect::<String>();
            eprintln!("B793AWIN slot {} mx {} mxp {} lb {:?} lad {:?} dtop_u {}", p3_cur_slot(), w.mx, w.mxp, w.lb, w.lad, w.dtop_u);
            eprintln!("B793ALEDGER slot {} live {} cap {} room {} act {} LA {} LB {} X0 {} Ytop {} cnt {} par {} split {} slim {} r14w {} masked {} act_const {}", p3_cur_slot(), b.live, self.cap, self.room(b), act.is_some() as u8, st(&self.la), st(&self.lb),
                st(&self.x[..1]), st(&self.y[W - 1..]), st(&self.cnt), st(&[self.par]), split as u8, slim as u8, r14w as u8, masked_rows as u8, w.act_const as u8);
        }
        // b793a F8 (B793A_F8): on the late slim R15-JC slots the rows' carry pool lane f is not bound with the RowTmp (it is only a pool lane
        // through the rows: R15-JC frees it at attach) but right after the forward rows; the cap is lowered by one meanwhile so every
        // room-driven choice is unchanged, the forward rows' pool is one lane shorter. Fail-closed where jc / row-f do not hold.
        let b8f = b793a_f8() && slim && !split && r14w && row_f() && rt_f8_ok(w);
        let b7p11 = b792_p11() && slim && !split && r14w && row_f() && w.act_const && act.is_none() && w.slot >= p11_lo() && w.slot <= 188
            && r15_jc_on() && w.k >= 2 && w.k <= 31 && !masked_rows && !park && partial.is_none();
        // b792 ACTRE (B792_ACTRE): on the late slots every active u = LA + sX is <= 256 - mx < 31 and a finished shot has u = sX (<= 31, redundant with the
        // sX lanes), so the 5-lane all-ones code LA = 31 is free: finished shots carry LA := 31 (LA[i] ^= !act & !sX[i]) through the rows, the act lane
        // is erased on AND(LA[0..5)) = !act and released; it is re-formed (act = !AND(LA[0..5)), LA := sX again) right before the R11 fold, the first
        // reader. Plain rows read no LA lane (the masks that do are masked-slot only) and no act. (ACTFOLD=2's code on the late slots.)
        let mut actre = false;
        if b792_actre() && !masked_rows && !w.act_const && !term(w) && cin.is_none() && act.is_some() && act == z0 && w.mx <= 256 && 256 - w.mx < 31
            && sx.len() == R_BITS && self.la[..R_BITS].iter().all(|&q| q != NOQ && !b.is_free(q)) && sx.iter().all(|&q| q != NOQ && !b.is_free(q)) {
            let a = act.unwrap();
            for i in 0..R_BITS {
                if !(i == 0 && b792_brk("ar1")) { and_auto(b, self, &[(a, true), (sx[i], true)], self.la[i]); }
            }
            b.x(a);
            let ones: Vec<(QubitId, bool)> = self.la[..R_BITS].iter().map(|&q| (q, false)).collect();
            erase_and(b, self, a, &ones);
            zero_probe(b, &[a]);
            b.free(a);
            act = Some(NOQ);
            z0 = Some(NOQ);
            y_act = if sy_act_gate() { act } else { None };
            actre = true;
        }
        // b792 S0Y (B792_S0Y): on the act-live slim slots 189-232 RowTmp's s0 is hosted on Y[W-1] (idle: the constant-1 top lane, |0> once
        // flipped for the rows pool) instead of a fresh lane, so the rows-start instant (where live = cap + 1 with s0) fits. Y[W-1] leaves the
        // rows pool and the YTOP-SWEEP lends (the rest of the sweep sees live exactly as with a separate s0: Y[W-1] not lent, s0 not bound);
        // `self.cap` is lowered by one over the forward rows so every room-driven choice there is unchanged.
        let s0y = r3_flag("B792_S0Y") && slim && !split && r14w && ytop && free_mode && ytop_sweep() && !masked_rows && !park && partial.is_none()
            && act.is_some() && !w.act_const && (189..=232).contains(&(p3_cur_slot() as usize)) && self.y[W - 1] != NOQ && !b.is_free(self.y[W - 1]);
        if s0y && std::env::var_os("B793_DBG").is_some() { eprintln!("B792FIRE s0y slot {}", p3_cur_slot()); }
        let mut rt = if split || slim { RowTmp::alloc_slim(b, r14w, b8f || b7p11, if s0y { Some(self.y[W - 1]) } else { None }) } else if r5p4f { RowTmp::alloc_p4(b, r12pf3, r9y, f6) } else { RowTmp::alloc(b, masked_rows && !park) };
        // R14 läckBobby-b F: prefix lane 3 unbound until the sweep; the cap is lowered by one meanwhile (room-driven
        // choices of the forward rows, their pool included, see the parent's room)
        if r14f { self.cap -= 1; }
        if b8f { self.cap -= 1; }
        if b7p11 { self.cap -= 1; }
        if s0y { self.cap -= 1; }
        // negative control (gate tests only): B792_BREAK=s0y binds the hosted s0 lane holding 1 (not |0>)
        if s0y && b792_brk("s0y") { b.x(rt.s0); }
        // negative control (gate tests only): B792_BREAK=p11 binds the carry pool lane f holding 1 (a lent pool lane that is not |0>)
        if b7p11 && cfg!(test) && std::env::var("B792_BREAK").map_or(false, |v| v == "p11" || (v == "p11r40" && w.slot < 44)) { rt.f = b.alloc(); b.x(rt.f); }
        if r14w {
            r14p_log('W', b, self.room(b));
            self.cap -= 1;
            // negative control (dev, inert unless set): R14P_BRK=w touches the unbound y (an op on NO_QUBIT, which
            // Op::validate / FABLE_CHK rejects), as any reader of y in the rows would
            if r14p_brk("w") { b.x(rt.y); }
        }
        r5tl(b, "rt");
        // lanes lent to both rows pools: hosted lanes, the sweep's idle g/jl on plain-row slots, the flipped Y[W-1]
        let mut lend = host.clone();
        if rt_idle_host() && rt.m.is_none() && !split && !slim {
            lend.push(rt.g);
            lend.extend(&rt.jl);
        }
        // b793b F6=2: Y[W-1] (|0> through the forward rows once flipped) is the forward rows' AND temp instead of a pool lane
        let f6y = f6 && b793_f6_mode() == 2 && ytop;
        if ytop && !f6y && !s0y {
            lend.push(self.y[W - 1]);
        }
        if f6y {
            rt.g = self.y[W - 1];
            rt.m.as_mut().unwrap().t = self.y[W - 1];
        }
        // R3_LA8ROWS (cap < 813): on plain-row slots LA[8] is |0> (u <= 228, see R3_LA8) and the plain rows never read
        // LA's sign lane (only masked rows do): it joins both rows pools; act-constant slots only unless R3_LA8LIVE
        if self.cap < 813 && r3_flag("R3_LA8ROWS") {
            lend.extend(self.r3_la_free(w, act, masked_rows));
        }
        if row_y(&rt) {
            // ROW-Y: the rows no longer read the zero source y, which is |0> through both rows passes
            // (R14 läckBobby W: not bound at all)
            if rt.y != NOQ { lend.push(rt.y); }
            if row_f() && rt.f != NOQ {
                // ROW-F: nor the carry-in lane f (|0> at both rows passes: the sweep's found flag is cleared by then)
                lend.push(rt.f);
            }
        }
        // R5_PRE4 (cap < 573): masked unparked slots; the prefix's lane 4 is idle in both rows passes (not yet bound)
        if r5p4f { R5P4.with(|c| c.set(true)); }
        if r12pf3 { R12PF3.with(|c| c.set(true)); }
        if r14f { R14F.with(|c| c.set(true)); }
        let mut p4_out = false;
        let mut gipm_pend = false;
        let room0 = self.room(b);
        r5tl(b, "lend");
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
        let r5mp = rt.m.is_some() && partial.is_none() && below805(self.cap) && r3_flag("R5_MPOOL");
        R5MP.with(|c| c.set(r5mp));
        R11C.with(|c| c.set(la5c));
        // negative control (dev, inert unless set): R9_BRK=nofold runs the forward rows in the plain form after X[0]'s
        // early release (they then read the released X[0] lane)
        if r9a && !super::mask::r9_brk("nofold") { R5FD.with(|c| c.set(true)); }
        let rs2t = super::mask::RSHORT2T.with(|c| c.replace(R14F.with(|c| c.get()) && !(f6 && !f6y)));
        let f6_nt = super::mask::NOTEMP.with(|c| c.replace(f6 && !f6y));
        if roll_rows() && !r14u_plan {
            // ROLL-ROWS: the forward rows pass runs directly (its rolled rows measure carries)
            // R14 misc94 x2: not rolled on the x2 slots (their undo rows fold the X[0] cell and replay no receipts)
            M94NR.with(|c| c.set(m94x_slot(w)));
            division_rows(b, self, w, &rt, &pool, park, top, partial, RowRoll::Fwd(&mut row_recs));
            M94NR.with(|c| c.set(false));
        } else {
            b.begin();
            division_rows(b, self, w, &rt, &pool, park, top, partial, RowRoll::No);
            let rows = b.end();
            b.play(&rows, false);
        }
        R5FD.with(|c| c.set(false));
        super::mask::NOTEMP.with(|c| c.set(f6_nt));
        if f6y { rt.g = NOQ; rt.m.as_mut().unwrap().t = NOQ; }
        super::mask::RSHORT2T.with(|c| c.set(rs2t));
        R14F.with(|c| c.set(false));
        R11C.with(|c| c.set(0));
        r5tl(b, "rowsdone");
        if std::env::var("R10_REGS").map_or(false, |v| v.parse::<usize>().ok() == Some(p3_cur_slot() as usize)) {
            eprintln!("R10REGS la {:?} lb {:?} cnt {:?} par {:?} x0..3 {:?} y[W-3..] {:?} x[W-3..] {:?}", self.la, self.lb, self.cnt, self.par, &self.x[..3], &self.y[W - 3..], &self.x[W - 3..]);
        }
        R5MP.with(|c| c.set(false));
        b.free_n(&own);
        zero_probe(b, &lend);
        let r5yoff = r5mp && ytop && free_mode && ytop_sweep() && r3_flag("R5_YOFF");
        let mut y_out = false;
        let r5fold = rt.m.is_some() && partial.is_none() && !park && !split && below805(self.cap) && r3_flag("R5_FOLD");
        let r5mrowy = (r5mp && term_nc() && r3_flag("R5_MROWY")) || r5fold;
        let mut y_rt_out = false;
        if r5p4f {
            // the sweep's jl needs all 5 prefix lanes
            R5P4.with(|c| c.set(false));
            R12PF3.with(|c| c.set(false));
        }
        let p4_x0 = r10p4f && x0_host() && ns0 && w.act_const && free_mode;
        if r5p4f && !p4_x0 {
            if r12pf3 {
                // R14 läckBobby-b F: the parent's prefix lane 3 was live since the RowTmp: the cap comes back
                if r14f { self.cap += 1; }
                let q = b.alloc();
                rt.m.as_mut().unwrap().pre[3] = q;
                rt.jl[3] = q;
            }
            let q = if r12jlf { rt.m.as_ref().unwrap().f } else { b.alloc() };
            rt.m.as_mut().unwrap().pre[4] = q;
            rt.jl[4] = q;
        }
        // YTOP-SWEEP: Y[W-1] stays |0> and is free from here to the undo rows
        let ytsw = ytop && free_mode && ytop_sweep() && !s0y;
        if ytsw {
            if mw_break(6) { b.x(self.y[W - 1]); }
            zero_probe(b, &[self.y[W - 1]]);
        } else if ytop && !s0y {
            b.x(self.y[W - 1]);
        }
        // b792 S0Y: Y[W-1] now holds s0 (row 0's result) and stays bound and unlent to the end of the undo rows (the cap, lowered by one
        // meanwhile, comes back at the R4-RHO lending point below)
        // R9_PREFIX B (r9 prefix): on masked R5_YOFF slots Y[W-1] (|0> from here, YTOP-SWEEP) is lent to the room now
        // instead of at R4-RHO's lending point below, so the sweep's prefix lanes 3 / 4 (bound after X0-HOST's release)
        // and its RUN-GUARD fit under the cap. R5_EARLY's move on slim slots: the cap is lowered by one until that
        // point (every room-driven choice in between is unchanged), where the lane joins the R3-ROOM hosts (r3h) and
        // stays out through the undo rows (R5_YOFF); its id is taken back after them where free, else re-bound.
        let r9b = ytsw && rt.m.is_some() && r5yoff && r3_flag("R3_YTOPB") && r4_on() && self.cap < 813
            && MJ_PEND.with(|p| p.borrow().is_none()) && r9p_on('B', self.room(b), 1);
        if r9b {
            r9p_log('B', b, self.room(b));
            // negative control (dev, inert unless set): R9_BRK=b lends Y[W-1] holding 1
            if super::mask::r9_brk("b") { b.x(self.y[W - 1]); }
            b.free(self.y[W - 1]);
            self.cap -= 1;
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
        // Q792 X0NA (dev, Q792_X0NA=1): X0-HOST on non-act-constant slots too (needs X[0] = 1 on finished shots as well)
        let x0h = x0_host() && ns0 && (w.act_const || q792_x0na()) && free_mode;
        assert!(!FX0_OPEN.with(|c| c.get()), "FIXX0: the previous slot left a park open (slot {})", p3_cur_slot());
        assert!(!r9a || x0h, "R9_PREFIX A: X[0] released early on a non-X0-HOST slot");
        // R5-FIT799 R5_EARLY (cap < 573, slim slots): X[0] is freed before the sweep's g / jl are attached, and the
        // R3-ROOM hosts R4-RHO lends at the sweep start are lent here already (attach, RUN-GUARD and the forward sweep
        // may land on them). The cap is lowered by the lent count until R4-RHO's own lending point, so every
        // room-driven choice in between is unchanged; there the lanes stay lent (R4 slot) or come back (rebind).
        let r5e = slim && below805(self.cap) && r3_flag("R5_EARLY");
        let x0_early = x0h && r5e;
        // FIXX0: X0NA's release on a non-act-constant slot parks X[0]'s bit on Z = X[NB + 30] (see `fixx0_break`)
        let fx0 = x0h && !w.act_const;
        assert!(!fx0 || (!r9a && sx.len() == R_BITS), "FIXX0: R9_PREFIX A or a short sX on a non-act-constant slot");
        let fx0z = if fx0 { self.x[FX0_Z] } else { NOQ };
        let fx0s4 = if fx0 { sx[R_BITS - 1 - fixx0_break2() as usize] } else { NOQ };
        let mut fx0_rel = usize::MAX;
        if x0_early {
            if !mw_break(5) { b.x(self.x[0]); }
            if fx0 { fx0_rel = fx0_park(b, self.x[0], fx0z, fx0s4); }
            zero_probe(b, &[self.x[0]]);
            b.free(self.x[0]);
        }
        let mut r5pre: Vec<QubitId> = vec![];
        if r5e && r4_on() && MJ_PEND.with(|p| p.borrow().is_none()) {
            if r3_flag("R3_LA8") { r5pre.extend(self.r3_la_free(w, act, masked_rows)); }
            if r3_flag("R3_YTOPB") && ytsw { r5pre.push(self.y[W - 1]); }
            zero_probe(b, &r5pre);
            b.free_n(&r5pre);
            self.cap -= r5pre.len() as u64;
        }
        // R11_FOLD (fable, 797): on slim VERG slots the act lane is folded into the sweep's running OR f before the
        // sweep's g / jl are attached: f = !act (so no row of a finished shot ever fires: y = !lane & g & !f = 0 and
        // jl stays 0, the value every witness erase separates from), the sweep runs its act-constant form
        // (g = [kt >= j], no act literal), and after the VROOM clear f = !act | found ^ [jl != 0] = !act (found => act)
        // hands act back to a fresh lane (CX, CX, X: no Toffoli). The cap is lowered by one in between so every
        // room-driven choice is unchanged. Code-space exact (jl <= k - 1 on active shots, 0 on finished ones).
        let r11f = r3_flag("R11_FOLD") && act.is_some() && slim && (rt.f != NOQ || b8f) && verg_on() && !sweep_rot_on()
            && !masked_rows && !park && !split && partial.is_none() && r4_on() && r3_flag("R3_VROOM")
            && sy_fold_cin() && sy_len == 1 && !(want_out && sw_carry() && self.room(b) >= P2_SWC_ROOM)
            && MJ_NEXT.with(|c| c.get()).map_or(true, |(_, plain1)| plain1);
        if actre {
            // b792 ACTRE: act back on a fresh lane (act = !AND(LA[0..5))), LA := sX again on the finished shots
            let z = b.alloc();
            let ones: Vec<(QubitId, bool)> = self.la[..R_BITS].iter().map(|&q| (q, false)).collect();
            and_auto(b, self, &ones, z);
            b.x(z);
            for i in 0..R_BITS {
                if !(i == 0 && b792_brk("ar2")) { and_auto(b, self, &[(z, true), (sx[i], true)], self.la[i]); }
            }
            act = Some(z);
            z0 = Some(z);
            y_act = if sy_act_gate() { act } else { None };
        }
        let mut act_sw = act;
        assert!(!b8f || r11f, "B793A F8: slot {} is not an R11-FOLD slot", p3_cur_slot());
        if r11f && b8f {
            // b793a F8: the fold moves act from its lane a to the pool lane f (cx, X, cx, X) and frees a; with f never bound the same state is
            // reached by one X on a: that lane becomes f = !act (the cap was lowered by F8 at the RowTmp, where the fold lowers it)
            let a = act.unwrap();
            if !b793a_brk("f8x") { b.x(a); }
            rt.f = a;
            act_sw = None;
        } else if r11f {
            let a = act.unwrap();
            zero_probe(b, &[rt.f]);
            b.cx(a, rt.f);
            if !(cfg!(test) && std::env::var("R11_BRK").map_or(false, |v| v == "fold")) { b.x(rt.f); }
            b.cx(rt.f, a);
            b.x(a);
            zero_probe(b, &[a]);
            b.free(a);
            act_sw = None;
            self.cap -= 1;
        }
        // R15-JC: the joint-code sweep needs jl alone; y (|0> after the rows) leaves RowTmp and the lent pool here, as
        // the parent's R11 re-home does after its sweep, and g is never taken
        // act-constant slots (act None): no gate, and f (the running OR, |0> after the rows) leaves RowTmp too
        let jc = r15_jc_on() && (r11f || act.is_none()) && slim && w.k >= 2 && w.k <= 31;
        let jc_ac = jc && !r11f;
        let mut jc_y_lent = false;
        let mut zopf_defer = false;
        let mut sweep_defer = false;
        if std::env::var_os("R15_DBG").is_some() {
            eprintln!("R15DBG slot {} k {} slim {} split {} r11f {} act {} masked {} park {} verg {} r4 {} vroom {} sycin {} sylen {} want {} room {} mjn {:?} jc {}",
                p3_cur_slot(), w.k, slim as u8, split as u8, r11f as u8, act.is_some() as u8, masked_rows as u8, park as u8, verg_on() as u8,
                r4_on() as u8, r3_flag("R3_VROOM") as u8, sy_fold_cin() as u8, sy_len, want_out as u8, self.room(b), MJ_NEXT.with(|c| c.get()), jc as u8);
        }
        let mut jc_f_lent = false;
        if r14w && !jc {
            // R14 läckBobby W off R15-JC: y bound fresh here (|0>, as the parent's after the rows), lent as the parent's
            assert!(rt.y == NOQ);
            self.cap += 1;
            rt.y = b.alloc();
            // the parent's lend order: y just before f (ROW-F)
            match lend.iter().position(|&q| q == rt.f) { Some(i) if row_f() => lend.insert(i, rt.y), _ => lend.push(rt.y) }
        }
        if jc && r14w {
            // R14 läckBobby W: y was never bound; the parent's y was lent (ROW-Y) and is released here: the cap comes back
            assert!(rt.m.is_none() && rt.g == NOQ && rt.y == NOQ);
            jc_y_lent = true;
            self.cap += 1;
        } else if jc {
            assert!(rt.m.is_none() && rt.g == NOQ && rt.y != NOQ);
            let yq = rt.y;
            zero_probe(b, &[yq]);
            jc_y_lent = lend.contains(&yq);
            b.free(yq);
            lend.retain(|&q| q != yq);
            rt.y = NOQ;
        }
        // b793b ACTFOLD (B793_ACTFOLD=1): !act rides on the code point (LA[5], LA[6]) = (1, 1) from here to the end of the forward sweep; the lane rt.f is free meanwhile
        // (u = LA + sX is <= 256 - w.mx < 96 on every active shot, the parent's R8_LAMX window; a finished shot has u = sX <= 31: neither uses the pair (1, 1))
        let mut actfold: Option<(QubitId, QubitId)> = None;
        let mut af7: Vec<QubitId> = vec![];
        if b793_actfold() && b8f && r11f && jc && af_slot(p3_cur_slot()) && rt.f != NOQ && !lend.contains(&rt.f) {
            let (l5, l6) = (self.la[R_BITS], self.la[R_BITS + 1]);
            assert!(l5 != NOQ && l6 != NOQ && !b.is_free(l5) && !b.is_free(l6) && !lend.contains(&l5) && !lend.contains(&l6), "b793 ACTFOLD: LA[5], LA[6] not bound");
            assert!(b793_actfold2() || (w.mx <= 256 && 256 - w.mx <= 95), "b793 ACTFOLD: u bound {} >= 96 on slot {}", 256 - w.mx, p3_cur_slot());
            if cfg!(test) && std::env::var_os("B793_AFPROBE").is_some() {
                let t = b.alloc();
                b.ccx(l5, l6, t);
                zero_probe(b, &[t]);
                b.ccx(l5, l6, t);
                b.free(t);
            }
            if cfg!(test) && std::env::var("B793_AFPROBE").map_or(false, |v| v == "2") {
                let c = b.alloc_n(2);
                b.cx(l5, c[0]);
                b.cx(l6, c[1]);
                AF_SAVE.with(|x| *x.borrow_mut() = Some(c));
            }
            if cfg!(test) && std::env::var("B793_AFPROBE").map_or(false, |v| v == "3") {
                let c = b.alloc_n(1);
                b.cx(rt.f, c[0]);
                AF_SAVE.with(|x| *x.borrow_mut() = Some(c));
            }
            let f = rt.f;
            if b793_actfold2() {
                // ACTFOLD=2: a finished shot (f = 1) has LA = sX; LA := 127 (LA[i] ^= f & !sX[i], i < 5; LA[5], LA[6] ^= f), then f ^= AND(LA[0..7))
                af7 = self.la[..R_BITS + 2].to_vec();
                assert!(af7.iter().all(|&q| q != NOQ && !b.is_free(q) && !lend.contains(&q)), "b793 ACTFOLD=2: LA[0..7) not bound");
                let dl: Vec<QubitId> = super::mask::borrowed().into_iter().filter(|q| !af7.contains(q) && !sx.contains(q) && *q != f).collect();
                assert!(dl.len() >= 6, "b793 ACTFOLD=2: {} borrowed lanes", dl.len());
                for i in 0..R_BITS {
                    b.x(sx[i]);
                    if !(i == 0 && b793b_break("af21")) { b.ccx(f, sx[i], self.la[i]); }
                    b.x(sx[i]);
                }
                b.cx(f, l5);
                b.cx(f, l6);
                let lits: Vec<(QubitId, bool)> = af7.iter().map(|&q| (q, false)).collect();
                and_dirty(b, &lits, f, &dl);
            } else {
            b.cx(f, l5);
            if !b793b_break("af1") { b.cx(f, l6); }
            b.ccx(l5, l6, f);
            }
            zero_probe(b, &[f]);
            b.free(f);
            rt.f = NOQ;
            self.cap -= 1;
            actfold = Some((l5, l6));
            if std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE actfold slot {} op {}", p3_cur_slot(), b.ops.len()); }
        }
        if jc {
            jc_f_lent = lend.contains(&rt.f) || (b8f && row_f()) || b7p11;
            assert!(!b8f || jc, "B793A F8: slot {} is not an R15-JC slot", p3_cur_slot());
            if jc_ac {
                let fq = rt.f;
                if b7p11 && fq == NOQ {
                    self.cap += 1;
                } else {
                zero_probe(b, &[fq]);
                b.free(fq);
                lend.retain(|&q| q != fq);
                rt.f = NOQ;
                }
            }
            // b793b ZOPF: jl is bound after the R3 hosts are lent (part 1's window opens first)
            zopf_defer = b793_zopf() && r14b_part('1') && rt.m.is_none() && w.act_const && act.is_none() && !masked_rows && jc_ac;
            // b792 SWEEP: the act-live nj decision needs r4 and the lent hosts, so jl is bound in the deferred block too (as it is on the ZOPF slots);
            // the pre-conditions that do not need r4 are tested here, the rest at the decision (a miss falls back to the jl path there)
            sweep_defer = b792_sweep() && b792_p11s() && jc && r11f && !jc_ac && !w.act_const && act.is_some() && rt.m.is_none() && !masked_rows && sweep_live_slot(w.slot)
                && (actfold.is_some() || rt.f != NOQ) && !zopf_defer;
            if !zopf_defer && !sweep_defer { rt.jl = b.alloc_n(R_BITS); }
        } else if slim { rt.attach(b); }
        r5tl(b, "attach");
        if r9a {
            // R9_PREFIX A: X[0] is out since the rows pass; the cap comes back here
            self.cap += 1;
            // R14 läckBobby-b J: on act-constant R9_PREFIX P slots the forward sweep runs in R15-JC's joint-code form, which
            // reads no y (and leaves g and f untouched), so y is not bound at all where the cap leaves no lane for it; the
            // cap is lowered by one until the R4-RHO release of f and y (every room-driven choice in between is unchanged).
            // Checked again at the sweep (fallback: y bound there).
            if r9y && act.is_none() && r15_jc_on() && w.k >= 2 && w.k <= 31 && r5mrowy && r14b_on('J', self.room(b), 1) {
                r14p_log('J', b, self.room(b));
                r14j = true;
                self.cap -= 1;
            } else if r9y {
                // R9_PREFIX P: the sweep's one-hot lane y, fresh |0>
                assert!(rt.y == NOQ);
                rt.y = b.alloc();
                // negative control (dev, inert unless set): R9_BRK=p binds y holding 1
                if super::mask::r9_brk("p") { b.x(rt.y); }
                zero_probe(b, &[rt.y]);
            }
        } else if x0h && !x0_early {
            if !mw_break(5) { b.x(self.x[0]); }
            if fx0 { fx0_rel = fx0_park(b, self.x[0], fx0z, fx0s4); }
            zero_probe(b, &[self.x[0]]);
            b.free(self.x[0]);
        }
        if p4_x0 {
            // R10_P4F: the sweep's jl lane 4 after X[0] is released
            if r12pf3 {
                // R14 läckBobby-b F: the parent's prefix lane 3 was live since the RowTmp: the cap comes back
                if r14f { self.cap += 1; }
                let q = b.alloc();
                rt.m.as_mut().unwrap().pre[3] = q;
                rt.jl[3] = q;
            }
            let q = if r12jlf { rt.m.as_ref().unwrap().f } else { b.alloc() };
            rt.m.as_mut().unwrap().pre[4] = q;
            rt.jl[4] = q;
        }
        prof(b, "i.sweep");
        p3(b, self, "i.sweep");
        r5tl(b, "sweep0");
        r6t(b, "sw.sweep0", self.room(b));
        // RUN-GUARD: c = [sX < kt + sY] (a units-bit jl = kt would give r < 0), kt5 -= c over both sweeps
        let kt5v: Vec<QubitId> = self.lb[..R_BITS].to_vec();
        let mut guard = if run_guard() {
            let c = b.alloc();
            lt_cin_sm(b, self, &sx, &kt5v, sy[0], Some(c));
            for &q in &kt5v { b.x(q); }
            inc_auto(b, self, c, &kt5v);
            for &q in &kt5v { b.x(q); }
            Some(c)
        } else { None };
        // The sweep runs on a clean 4-lane chain; its inverse runs later beside r and a1, on a clean chain while the
        // cap leaves room and on borrowed lanes otherwise.
        // SWEEP-OR-LANES: OR lanes for the top rows, leaving room for r + a1 (4), the r section's chains (4), the
        // backward unary chain (8) and its repair lane (1)
        let room_sw = self.room(b);
        r5tl(b, "guard");
        r6t(b, "sw.guard", self.room(b));
        // SW-CARRY: this slot leaves the previous slot's swap flag c (held from the r / a1 section to the slot's end)
        // (on PARK-SPLIT slots only where the park leaves SWC_SPLIT_MIN lanes of room beside z: the split repark holds
        // s0, f, y, r, a1 and its decoder beside z, so a carried lane there can set the peak)
        let produce = want_out && sw_carry() && (!split || room_park >= zn + swc_split_min())
            // P2-REBASE: below 813 the carried flag's lane does not fit beside the sweep, r and a1: the next slot
            // decodes its swap flag itself (the base's exact path)
            && !(self.cap < 813 && self.room(b) < P2_SWC_ROOM);
        let swc = produce as usize;
        // R3-VERG: this slot's jl is measured where it and the next inverse slot run plain rows with equal k
        // R4-RHO: the in-place decode needs VROOM, SYFOLD's 1-bit sY, no carried swap flag, and a next inverse slot whose
        // stall gate can read LA (plain rows) unless this slot is act-constant (the gate is then X[W-1] alone)
        let r4_elig = r4_on() && r3_flag("R3_VROOM") && !produce && sy_fold_cin() && sy_len == 1
            && (w.act_const || MJ_NEXT.with(|c| c.get()).map_or(true, |(_, plain1)| plain1));
        // R4_MASK=1 (with R4_WIDE): masked-row slots (no park) too; rho is re-homed off the mask's decoder prefix
        let r4m = r4_elig && r4_wide() && r3_flag("R4_MASK") && masked_rows && !park && !split && partial.is_none()
            && verg_on() && !sweep_rot_on();
        let mj = (verg_on() && !sweep_rot_on() && !masked_rows && !park && !split && partial.is_none()
            && (MJ_NEXT.with(|c| c.get()).map_or(false, |(k1, plain1)| plain1 && k1 == w.k) || (r4_elig && r4_wide())))
            || r4m;
        let r4 = mj && r4_elig;
        // R4-RHO: the R3-ROOM hosts (|0> from the rows pass to the undo rows) are lent from here, before the forward
        // sweep and its RUN-GUARD erase (VERG slots run no OR lanes, so Y[W-1] is never an OR lane here)
        let mut r3h: Vec<QubitId> = vec![];
        if s0y { self.cap += 1; }
        if !r5pre.is_empty() {
            // R5_EARLY: the cap comes back; the early-lent hosts stay lent where R4-RHO lends them here, else return
            self.cap += r5pre.len() as u64;
            if r4 && self.cap < 813 && MJ_PEND.with(|p| p.borrow().is_none()) {
                r3h = std::mem::take(&mut r5pre);
            } else {
                let mut back = std::mem::take(&mut r5pre);
                self.r5_rebind(b, &mut back, &mut rt, &mut lend, NOQ);
                zero_probe(b, &back);
            }
        } else if r9b {
            // R9_PREFIX B: the cap comes back; Y[W-1] (lent since the rows pass) joins the hosts without a second free
            self.cap += 1;
            assert!(r4 && self.cap < 813 && MJ_PEND.with(|p| p.borrow().is_none()), "R9_PREFIX B: not an R4-RHO lending slot");
            if r3_flag("R3_LA8") { r3h.extend(self.r3_la_free(w, act, masked_rows)); }
            zero_probe(b, &r3h);
            b.free_n(&r3h);
            r3h.push(self.y[W - 1]);
        } else
        if r4 && self.cap < 813 && MJ_PEND.with(|p| p.borrow().is_none()) {
            if r3_flag("R3_LA8") { r3h.extend(self.r3_la_free(w, act, masked_rows)); }
            if r3_flag("R3_YTOPB") && ytsw { r3h.push(self.y[W - 1]); }
            zero_probe(b, &r3h);
            b.free_n(&r3h);
        }
        let r3h_early = !r3h.is_empty();
        // b793b ZOPF: Schaffhuuserzopf part 1's window opens here (before the jl lanes are bound), see b793_zopf
        let mut zopf_early: Option<(usize, usize)> = None;
        let mut nj = false;
        let mut nj_hold = NOQ;
        let mut nj_out: Vec<QubitId> = vec![];
        if zopf_defer || sweep_defer {
          if zopf_defer {
            assert!(jc && r4 || !r4, "b793 ZOPF: defer without JC");
            let fold_e = sy_fold_cin() && sy_len == 1;
            let lad_floor = CW.saturating_sub(w.dtop_u);
            let lo = lad_floor.saturating_sub(7);
            let hi = la94b_hi(w.slot).min(255);
            let jk = b792_slc_jk(lo, hi).or_else(|| (4..LB_BITS - 1).rev().map(|j| (j, (lo >> j) << j)).find(|&(_, c)| c + 127 >= hi && c <= lo));
            let lent: Vec<QubitId> = r3h.iter().chain(lend.iter()).copied().collect();
            let view_ok = (0..LB_BITS - 1).all(|i| self.la[i] != NOQ && !lent.contains(&self.la[i]) && !b.is_free(self.la[i]))
                && (lent.contains(&self.la[LB_BITS - 1]) || b.is_free(self.la[LB_BITS - 1]));
            zopf_early = jk.filter(|_| r4 && slim && fold_e && view_ok && hi <= 255 && hi >= lo
                && R4_PEND.with(|p| p.borrow().as_ref().map_or(true, |(_, g)| !*g))
                && MJ_PEND.with(|p| p.borrow().is_none()))
                .map(|(j, c)| (j, (c >> j)));
            if let Some((j, k)) = zopf_early {
                let lv: Vec<QubitId> = self.la[j..LB_BITS - 1].to_vec();
                if !b793b_break("zp1") { la94b_field_add(b, &lv, k, true, &self.dirty); }
                let q = self.la[LB_BITS - 2];
                zero_probe(b, &[q]);
                b.free(q);
                self.la[LB_BITS - 2] = NOQ;
                if !b793_zlate() { self.cap -= 1; }
                if std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE zopf slot {} j {j} k {k}", p3_cur_slot()); }
            }
          }
            // b792w4 P11S: no jl register; rho (3 lanes) and a1 on the lanes the parent's decode ends on (rho = jl[0..3), a1 = the lowest free id beyond jl[3], jl[4])
            nj = b792_p11s() && r4 && slim && rt.m.is_none() && w.act_const && act.is_none() && !masked_rows && jc_ac && b793_nog() && sy_len == 1 && sy_fold_cin()
                && b793_gip() && r3_flag("R12_DECODE_PERM") && w.slot >= p11s_lo() && w.slot <= 188 && MJ_PEND.with(|p| p.borrow().is_none())
                && AF_LANES.with(|c| c.borrow().is_empty()) && sx.len() == R_BITS
                && R4_PEND.with(|p| p.borrow().as_ref().map_or(true, |(_, g)| *g));
            // b792 SWEEP: the act-live slots (see sweep_defer); the same conditions otherwise, act read from the pair / the lane rt.f
            // !r14j: under r14j the code after the sweep binds rt.y (a fifth lane on an empty pool) when jl holds NOQ lanes; r14j needs act.is_none(), so it is false on every act-live slot, tested here anyway
            let nj_live = sweep_defer && !r14j && r4 && slim && b793_nog() && sy_len == 1 && sy_fold_cin() && b793_gip() && r3_flag("R12_DECODE_PERM")
                && MJ_PEND.with(|p| p.borrow().is_none()) && AF_LANES.with(|c| c.borrow().is_empty()) && sx.len() == R_BITS
                && R4_PEND.with(|p| p.borrow().as_ref().map_or(true, |(_, g)| *g))
                && (actfold.is_some() || (rt.f != NOQ && !b.is_free(rt.f) && !lend.contains(&rt.f)));
            nj = nj || (nj_live && !sweep_decline(w.slot));
            // the parent's lane picture: jl takes the 5 lowest free ids f1..f5 and the decode ends with rho on f1..f3, a1 on jl[3]'s id (f4) when no
            // other id is free, f5 free; f5 stays out of the pool (not live) until the decode point, as it is live in the parent
            let nj_nf = b.lowest_free(6).len();
            let nj_ids = nj_nf == 5 || (nj_nf >= 4 && b792_idgate());
            nj = nj && (nj_ids || (cfg!(test) && r3_flag("B792_NJFORCE")));
            if std::env::var_os("B792_SWDBG").is_some() { eprintln!("B792SW slot {} defer {} nj {} nfree {} live {} actfold {} f {:?}", p3_cur_slot(), sweep_defer as u8, nj as u8, nj_nf, b.live, actfold.is_some() as u8, rt.f); }
            if nj {
                let rho = b.alloc_n(RHO_BITS);
                let a1 = b.alloc();
                // B792_NJFORCE (gate tests only): the id-hold path runs whenever a free id exists, so the shipped hold/unhold code is exercised; the gate's lane
                // inventory has other free-id counts than the 793 build. Which free id is held never changes the gates: rho / a1 are ordinary |0> lanes either way.
                // with 4 free ids (B792_IDGATE) the four allocs above leave no id to hold: hold only in the 5-free picture
                if nj_nf == 5 || (cfg!(test) && r3_flag("B792_NJFORCE") && !b.lowest_free(1).is_empty()) {
                    let f5 = b.lowest_free(1)[0];
                    b.hold_id(f5);
                    nj_hold = f5;
                }
                rt.jl = vec![rho[0], rho[1], rho[2], NOQ, NOQ];
                nj_out = vec![rho[0], rho[1], rho[2], a1];
            } else {
            rt.jl = b.alloc_n(R_BITS);
            }
        }
        r5tl(b, "r3h");
        r6t(b, "sw.r3h", self.room(b));
        let mut fl: Vec<QubitId> = vec![];
        let mut ylent = false;
        let mut rot_used = false;
        let mut defer_bits: Option<Vec<Option<BitId>>> = None;
        // R3-VERG R3_VUF=1: on VERG slots no backward sweep follows, so the unary forward sweep needs only its chain
        let vuf = mj && std::env::var("R3_VUF").map_or(false, |v| v.trim() == "1") && room_sw >= R_BITS;
        if r14j {
            // R14 läckBobby-b J: the joint-code sweep needs a VERG / R4-RHO / VROOM slot with no gated stall repair pending
            // (that repair reads y) and no carried swap flag; else y is bound here after all (fresh |0>, the cap back)
            let mj_gate = MJ_PEND.with(|p| p.borrow().as_ref().map_or(false, |(_, g)| *g));
            let vroom0 = mj && std::env::var("R3_VROOM").map_or(false, |v| v.trim() == "1");
            if !(mj && r4 && vroom0 && !produce && !mj_gate && rt.m.is_some() && rt.jl.len() == R_BITS && rt.jl.iter().all(|&q| q != NOQ)) {
                self.cap += 1;
                rt.y = b.alloc();
                zero_probe(b, &[rt.y]);
                r14j = false;
            }
        }
        assert!(!f6 || r14j, "b793 F6: the joint-code sweep is required (slot {})", p3_cur_slot());
        if nj {
            let pend = R4_PEND.with(|p| p.borrow_mut().take());
            let gp = pend.as_ref().filter(|(_, g)| *g).map(|_| (r3h.clone(), AF_PAIR.with(|c| c.get())));
            let nj_act = if w.act_const { NjAct::None } else if let Some((l5, l6)) = actfold { NjAct::Pair(l5, l6) } else { NjAct::Lane(rt.f) };
            if std::env::var_os("B792_SWDBG").is_some() {
                let sk: Vec<usize> = gp.as_ref().map_or(vec![], |(sk, _)| (0..self.la.len()).filter(|&i| sk.contains(&self.la[i]) || self.la[i] == NOQ).collect());
                eprintln!("B792SWGP slot {} gp {} afp {} la_len {} skipped_or_noq_la_positions {:?}", p3_cur_slot(), gp.is_some() as u8, gp.as_ref().map_or(0, |(_, a)| a.is_some() as u8), self.la.len(), sk);
            }
            nj_sweep(b, self, w, &rt, &sx, sy[0], &nj_out, pend.map(|(mb, _)| mb), gp, nj_act);
        } else if r14j {
            // negative control (dev, inert unless set): R14P_BRK=j binds y holding 1 (the parent's sweep then reads it)
            if r14p_brk("j") {
                self.cap += 1;
                rt.y = b.alloc();
                b.x(rt.y);
                r14j = false;
                sweep_fwd(b, self, act_sw, w, &rt, &self.dirty, false);
            } else {
                sweep_fwd_jc(b, self, &[], w, &rt);
            }
        } else if jc {
            assert!(mj, "R15_JC: not a VERG slot");
            let gate: Vec<(QubitId, bool)> = if jc_ac || actfold.is_some() { vec![] } else { vec![(rt.f, true)] };
            sweep_fwd_jc_g(b, self, &gate, actfold.map(|(l5, l6)| if af7.is_empty() { vec![l5, l6] } else { af7.clone() }), w, &rt);
        } else if sweep_unary() && (vuf || room_sw >= R_BITS + RHO_BITS + 1 - (self.cap >= 813) as usize * (RHO_BITS + 1)) {
            // ... and only where the backward chain rows (after the OR lanes are freed) still fit: r, a1, prefix, AND
            if !mj && sweep_or_lanes() && w.k >= 2 && room_sw >= RHO_BITS + 1 + R_BITS - 1 + row_anc() + swc {
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
            sweep_fwd_ui(b, self, act_sw, w, &rt, &ch, &fl);
            b.free_n(&ch);
        } else if sweep_rot_on() {
            rot_used = true;
            sweep_rot(b, self, act_sw, w, &rt, true);
        } else if self.room(b) < R_BITS - 1 {
            // P2-REBASE (retake799 r806): the sweep's chain on borrowed lanes
            sweep_fwd(b, self, act_sw, w, &rt, &self.dirty, false);
        } else {
            let ch = b.alloc_n(R_BITS - 1);
            if sweep_defer_on() && !mj {
                let mut d: Vec<Option<BitId>> = vec![];
                sweep_fwd_d(b, self, act_sw, w, &rt, &ch, true, Some(&mut d));
                defer_bits = Some(d);
            } else {
                sweep_fwd(b, self, act_sw, w, &rt, &ch, true);
            }
            b.free_n(&ch);
        }
        r5tl(b, "fwdsweep");
        r6t(b, "sw.fwdsweep", self.room(b));
        // R3-VERG x RUN-GUARD: with the backward sweep gone, kt5 is not read again: restore it and erase c here
        if mj {
            if let Some(c) = guard.take() {
                if !guard_break(1) { inc_auto(b, self, c, &kt5v); }
                erase_mbu(b, c, |b| lt_cin_sm(b, self, &sx, &kt5v, sy[0], None));
                b.free(c);
            }
        }
        // R3-VERG: the stall shots of the inverse slot just run owe (-1)^(m . J); here jl = J (the same plain division
        // on the same inputs) and those shots have X[W-1] = 0. Where that slot was not act-constant, shots that
        // finished at this slot (u == sX) are excluded by the stall gate.
        if let Some((mb, gate)) = MJ_PEND.with(|p| p.borrow_mut().take()) {
            let brk = mj_break();
            if gate && brk != "6" && jc {
                // R15-JC: no y; the parity m . J is applied on jl directly: (-1)^(m.J (1 + X[W-1] + g)), the parent's phase
                for (i, &m) in mb.iter().enumerate() {
                    b.push_condition(m);
                    b.z(rt.jl[i]);
                    b.cz(self.x[W - 1], rt.jl[i]);
                    b.pop_condition();
                }
                for (i, &q) in sx.iter().enumerate() {
                    b.cx(q, self.la[i]);
                }
                let mut lits = vec![(self.x[W - 1], true)];
                lits.extend(self.la.iter().filter(|&&q| q != NOQ).map(|&q| (q, true)));
                let g = b.alloc();
                and_auto(b, self, &lits, g);
                if !r15_brk("mj") {
                    for (i, &m) in mb.iter().enumerate() {
                        b.push_condition(m);
                        b.cz(g, rt.jl[i]);
                        b.pop_condition();
                    }
                }
                erase_and(b, self, g, &lits);
                b.free(g);
                for (i, &q) in sx.iter().enumerate() {
                    b.cx(q, self.la[i]);
                }
            } else if gate && brk != "6" {
                for (i, &m) in mb.iter().enumerate() {
                    b.push_condition(m);
                    b.cx(rt.jl[i], rt.y);
                    b.pop_condition();
                }
                b.z(rt.y);
                b.cz(self.x[W - 1], rt.y);
                for (i, &q) in sx.iter().enumerate() {
                    b.cx(q, self.la[i]);
                }
                let mut lits = vec![(self.x[W - 1], true)];
                lits.extend(self.la.iter().filter(|&&q| q != NOQ).map(|&q| (q, true)));
                and_auto(b, self, &lits, rt.g);
                b.cz(rt.g, rt.y);
                erase_and(b, self, rt.g, &lits);
                for (i, &q) in sx.iter().enumerate() {
                    b.cx(q, self.la[i]);
                }
                for (i, &m) in mb.iter().enumerate() {
                    b.push_condition(m);
                    b.cx(rt.jl[i], rt.y);
                    b.pop_condition();
                }
            } else {
                for (i, &m) in mb.iter().enumerate() {
                    b.push_condition(m);
                    b.z(rt.jl[i]);
                    if brk != "3" {
                        b.cz(self.x[W - 1], rt.jl[i]);
                    }
                    b.pop_condition();
                }
            }
        }
        // R3-VERG R3_VROOM=1: on VERG slots f = [jl != 0] is cleared here, before r / a1 (jl is unchanged until the
        // measured erase), so f is |0> through the rho section; g and y are |0> there too (the anf routes do not read
        // them): those lanes are lent to the rho section and taken back after it
        r5tl(b, "mjpend");
        r6t(b, "sw.mjpend", self.room(b));
        let vroom = mj && std::env::var("R3_VROOM").map_or(false, |v| v.trim() == "1");
        if vroom && mj_break() != "4" && !jc && !r14j {
            b.x(rt.f);
            let lits: Vec<(QubitId, bool)> = rt.jl.iter().map(|&q| (q, true)).collect();
            and_auto(b, self, &lits, rt.f);
        }
        // R11_FOLD: f = !act here; act back on a fresh lane (y, |0> after the sweep and the owed repair, is released
        // first so the count never rises; its id is taken back or re-bound at postacq as every lent lane is)
        assert!(!r11f || (mj && r4 && vroom && mj_break() != "4"), "R11_FOLD: slot is not a VROOM / R4 slot");
        if r11f && jc {
            // R15-JC: f = !act was never touched by the sweep: act is f's own lane (X); f leaves RowTmp and the lent pool
            // until the re-acquire, where it is taken fresh
            if actfold.is_some() {
                // b793b ACTFOLD: !act stays on the code point; the lane comes back after the R4-RHO frees (see af_restore), the cap rises there
                rt.f = NOQ;
                self.cap += 1;
                z0 = Some(NOQ);
                act = Some(NOQ);
                AF_PAIR.with(|c| c.set(if af7.is_empty() { actfold } else { None }));
                AF_LANES.with(|c| *c.borrow_mut() = af7.clone());
            } else {
            let z = rt.f;
            b.x(z);
            rt.f = NOQ;
            lend.retain(|&q| q != z);
            self.cap += 1;
            z0 = Some(z);
            act = Some(z);
            }
            y_act = if sy_act_gate() { act } else { None };
        } else if r11f {
            // act takes y's own lane (|0> here); y leaves RowTmp and the undo rows' lent pool (ROW-Y: the plain rows
            // never read the zero source), as R5_MROWY does on masked slots, so no id is ever re-acquired or re-bound
            let z = rt.y;
            zero_probe(b, &[z]);
            b.cx(rt.f, z);
            b.cx(z, rt.f);
            b.x(z);
            zero_probe(b, &[rt.f]);
            rt.y = NOQ;
            lend.retain(|&q| q != z);
            self.cap += 1;
            z0 = Some(z);
            act = Some(z);
            y_act = if sy_act_gate() { act } else { None };
        }
        if rowlog() {
            eprintln!("R3_RA1 k {} mj {} room_sw {room_sw} room_ra1 {} act {} masked {} park {} fl {} defer {}", w.k, mj as u8,
                      self.room(b), act.is_some() as u8, masked_rows as u8, park as u8, fl.len(), defer_bits.is_some() as u8);
        }
        if rowlog() {
            eprintln!("WL_SW room_sw {room_sw} path {} n_or {} act {} masked {} park {} split {} room_ra1 {}", if rot_used { "rot" } else if defer_bits.is_some() { "defer" } else if !fl.is_empty() || (sweep_unary() && room_sw >= R_BITS + RHO_BITS + 1 - (self.cap >= 813) as usize * (RHO_BITS + 1)) { "unary" } else { "dirty" },
                      fl.len(), act.is_some() as u8, masked_rows as u8, park as u8, split as u8, self.room(b));
        }
        r6t(b, "sw.vroom", self.room(b));
        if r3_subprof() { prof(b, "i.ra1"); }
        p3(b, self, "i.ra1");
        // R4-RHO: no fresh r (rho lands on jl[0..3]); a1 is taken in the decode, after the hosts are lent
        let (mut r, mut a1) = if r4 { (vec![], NOQ) } else { (b.alloc_n(RHO_BITS), b.alloc()) };
        // R3-ROOM hosts (dev switches, cap < 813; off = the parent): lanes that hold |0> on every shot from here to the
        // end of the backward sweep go to the room, after r and a1 are placed, so only transients (rho's product lanes,
        // a1's AND lane, the backward sweep's chain) land on them; they are re-acquired by id after the backward sweep.
        // Not with a carried swap flag (its lane lives past the re-acquire).
        // - R3_LA8: LA[8] on plain-row slots. LA holds u = 256 - mX here, u <= 256 - w.mx <= 228 on every shot inside
        //   the parent's envelope (plain rows need mX >= w.mx >= NB + 1); act-constant slots only unless R3_LA8LIVE.
        // - R3_YTOPB: Y[W-1] (YTOP-SWEEP: |0> from the rows pass to the undo rows) where the forward sweep did not
        //   take it as an OR lane.
        if self.cap < 813 && !produce && !r3h_early {
            if r3_flag("R3_LA8") { r3h.extend(self.r3_la_free(w, act, masked_rows)); }
            if r3_flag("R3_YTOPB") && ytsw && !ylent { r3h.push(self.y[W - 1]); }
            zero_probe(b, &r3h);
            b.free_n(&r3h);
        }
        // jl <- sX - sY - jl in place: the rotation since the last step (rho_of in greedyfrog_model). This slot's rotation
        // rho = act & ((jl mod 8) + #{8, 15, 22, 29 <= jl}) mod 8 and a1 = act & [jl < 8] (the slot was a step).
        // Temps: y and g (|0> after the sweep) and the sweep chain.
        let jl = rt.jl.clone();
        // R9 rowtmp c: (a1, rho) lanes while act's lane is released (act = a1 | (rho != 0)); None: act is a lane
        let mut act_el: Option<(QubitId, [QubitId; RHO_BITS])> = None;
        r5tl(b, "prejl");
        let fold = sy_fold_cin() && sy_len == 1;
        // Schaffhuuserzopf (R14_LA94B): LA[7] out across the jl map and the decode, LA offset by c = lad_floor - 7
        let la94b: Option<(usize, usize)> = if zopf_early.is_some() { zopf_early } else {
            let lad_floor = CW.saturating_sub(w.dtop_u);
            let lo = lad_floor.saturating_sub(7);
            // (and u <= 255: LA[8] is the parent's lent |0> lane here, view_ok below)
            let hi = la94b_hi(w.slot).min(255);
            // c = k 2^j: the largest j (<= 7, field LA[j..8) of at most 4 lanes) with a multiple of 2^j in hi - 127 ..= lo
            let jk = b792_slc_jk(lo, hi).or_else(|| (4..LB_BITS - 1).rev().map(|j| (j, (lo >> j) << j)).find(|&(_, c)| c + 127 >= hi && c <= lo));
            let lent: Vec<QubitId> = r3h.clone();
            let view_ok = (0..LB_BITS - 1).all(|i| self.la[i] != NOQ && !lent.contains(&self.la[i]) && !b.is_free(self.la[i]))
                && (lent.contains(&self.la[LB_BITS - 1]) || b.is_free(self.la[LB_BITS - 1]));
            jk.filter(|_| r14b_part('1') && jc && r4 && slim && w.act_const && act.is_none() && !masked_rows && fold && view_ok
                && hi <= 255 && hi >= lo && R4_PEND.with(|p| p.borrow().as_ref().map_or(true, |(_, g)| !*g)))
                .map(|(j, c)| (j, ((c >> j) + r14b_break("c1") as usize).saturating_sub(r14b_break("c0") as usize)))
        };
        if let Some((j, k)) = la94b.filter(|_| zopf_early.is_none()) {
            let lv: Vec<QubitId> = self.la[j..LB_BITS - 1].to_vec();
            if !r14b_break("nosub") { la94b_field_add(b, &lv, k, true, &self.dirty); }
            let c = k << j;
            let q = self.la[LB_BITS - 2];
            zero_probe(b, &[q]);
            b.free(q);
            self.la[LB_BITS - 2] = NOQ;
            self.cap -= 1;
            if std::env::var_os("R9_DBG").is_some() { eprintln!("LA94BF fire slot {} c {c}", p3_cur_slot()); }
        }
        // Schaffhuuserzopf part 2 (see la94b_fin): no g, the decode on act's lane
        let la94b2 = !nj && actfold.is_none() && !(cfg!(test) && r3_flag("B793_GIPFORCE")) && r14b_part('2') && jc && fold && r4 && slim && !w.act_const && act.is_some() && act == z0
            && r9_rt('c') && i5_rcnt() && ns0 && sy_act_gate() && la94b.is_none() && r3_flag("R12_DECODE_PERM")
            && (self.room(b) == 0 || std::env::var_os("R14_LA94B_P2ALL").is_some());
        if la94b2 && std::env::var_os("R9_DBG").is_some() { eprintln!("LA94B2 fire slot {}", p3_cur_slot()); }
        if std::env::var_os("B793_DBG").is_some() {
            eprintln!("B793F13 slot {} act_const {} jc {} fold {} r4 {} slim {} masked {} act {} la94b {} la94b2 {} room {} live {} cap {} r3h {} pend_gate {:?}", p3_cur_slot(), w.act_const as u8, jc as u8, fold as u8, r4 as u8,
                slim as u8, masked_rows as u8, act.is_some() as u8, la94b.is_some() as u8, la94b2 as u8, self.room(b), b.live, self.cap, r3h.len(),
                R4_PEND.with(|p| p.borrow().as_ref().map(|(_, g)| *g)));
        }
        // b793a (B793_NOG): no g on any R15-JC slot: the jl map's carry-in is sY[0]'s own lane negated (Schaffhuuserzopf part 2's
        // form) and the stall gate is the lane-free phase_and form of r4_pend_apply
        let b793g = (b793_nog() && jc && !la94b2 && fold && r4 && sy_len == 1) || (f6 && fold && r4 && sy_len == 1);
        if jc && !la94b2 && !b793g {
            // R15-JC: the jl map's carry-in / the stall repair's gate lane g, taken only now (the parent holds it from attach)
            assert!(rt.g == NOQ && fold && r4);
            rt.g = b.alloc();
        }
        // jl -> ~jl + sX + !sY0 (fold) = sX - sY - jl; the map is an involution
        let jl_map = |this: &GreedyFrog, b: &mut B| {
            for &q in &jl {
                b.x(q);
            }
            b.cx(sy[0], rt.g);
            b.x(rt.g);
            add_on_sm(b, this, &jl, &sx, false, false, rt.g, true);
            b.x(rt.g);
            b.cx(sy[0], rt.g);
        };
        // R4-RHO: f (cleared by VROOM), y and the VROOM_Y lane are |0> from here to the end of the decode; g after the
        // jl map (its carry-in) and the owed stall repair (its gate lane)
        let vy4 = r4 && ytsw && r3_flag("R3_VROOM_Y") && !r3h.contains(&self.y[W - 1]);
        let mut vl4: Vec<QubitId> = vec![];
        if r4 {
            // R11_FOLD: y is the act lane now (NOQ in RowTmp)
            vl4 = [rt.f, rt.y].into_iter().filter(|&q| q != NOQ).collect();
            if vy4 { vl4.push(self.y[W - 1]); }
            zero_probe(b, &vl4);
            b.free_n(&vl4);
            // R14 läckBobby-b J: the parent's y is released here; the cap comes back
            if r14j { self.cap += 1; }
        }
        if nj {
            // b792w4 P11S: (rho, a1) were computed by nj_sweep; no jl map
        } else if la94b2 || b793g {
            // Schaffhuuserzopf part 2: jl -> ~jl + sX + !sY0 on sY's own lane (negated) as the quantum carry-in
            for &q in &jl {
                b.x(q);
            }
            if !(b793g && b793_break(4)) { b.x(sy[0]); }
            add_on_sm(b, self, &jl, &sx, false, false, sy[0], true);
            b.x(sy[0]);
        } else if fold {
            jl_map(self, b);
        } else {
            for &q in &jl {
                b.x(q);
            }
            add_on_sm(b, self, &jl, &sx, true, false, rt.g, false);
            add_on_sm(b, self, &jl, &sy[..sy_len], false, true, rt.g, false);
        }
        if r4 && !r4_break(4) && !nj {
            // (b792 SWEEP: not under nj: jl[0..3) are the rho lanes and jl[3], jl[4] are NOQ; out was gated by act inside nj_run)
            // finished shots have J = 0 and sY = 0, so t = sX: t ^= !act & sX zeroes them (rho = 0, res = 0, e = 1)
            if !af7.is_empty() {
                let dl: Vec<QubitId> = self.dirty.iter().copied().filter(|q| !sx.contains(q) && !jl.contains(q) && !af7.contains(q)).collect();
                for i in 0..R_BITS {
                    let mut l: Vec<(QubitId, bool)> = af7.iter().map(|&q| (q, false)).collect();
                    l.push((sx[i], false));
                    and_dirty(b, &l, jl[i], &dl);
                }
            } else if let Some((l5, l6)) = actfold {
                // b793b ACTFOLD: !act = LA[5] & LA[6]
                let dl: Vec<QubitId> = self.dirty.iter().copied().filter(|q| !sx.contains(q) && !jl.contains(q) && *q != l5 && *q != l6).collect();
                for i in 0..R_BITS {
                    and_dirty(b, &[(l5, false), (l6, false), (sx[i], false)], jl[i], &dl);
                }
            } else if let Some(a) = act {
                b.x(a);
                for i in 0..R_BITS {
                    b.ccx(a, sx[i], jl[i]);
                }
                b.x(a);
            }
        }
        r5tl(b, "jlmap");
        // R4-RHO: the stall phase owed by the previous inverse slot, on t (any slot type: t is this slot's own decode)
        self.r4_pend_apply(b, &jl, &sx, &r3h, rt.g);
        if cfg!(test) && r4 && std::env::var_os("B793_PREMISE").is_some() && std::env::var("B793_PREMISE").map_or(true, |v| v != "3") {
            // b793a gate-test probe (no gates): histogram of (act_const, X[W-1], t) at the decode's input
            let mut v = vec![QubitId(PREMISE_MARK), self.x[W - 1]];
            v.extend(jl.iter().copied());
            v.push(QubitId(if std::env::var("B793_PREMISE").map_or(false, |x| x == "4") { (std::env::var("B793_PREMISE_SLOT").ok().and_then(|v| v.parse::<usize>().ok()) == Some(p3_cur_slot())) as u64 } else if std::env::var("B793_PREMISE").map_or(false, |x| x == "2") { (189..=202).contains(&p3_cur_slot()) as u64 } else { w.act_const as u64 }));
            ZERO_PROBES.with(|p| p.borrow_mut().push((b.ops.len(), v)));
        }
        if r4 {
            zero_probe(b, &[rt.g]);
            if rt.g != NOQ {
            b.free(rt.g);
            vl4.push(rt.g);
            }
            // b793a Gipfeli: X[W-1] is the sixth wire (plain rows, slim detach, no act-lane decode)
            // b792 GIPM (B792_GIPM): masked slots 0-43 (act_const: no finished shot, x = 0 only on stalled shots t in {7,14,21,28}):
            // Gipfeli's decode on the masked sweep's jl lanes, X[W-1] the sixth wire. a1 stays on jl[4] (the mask f's lane, JLF); f gets a fresh lane at the undo rows.
            let gipm = b792_gipm() && rt.m.is_some() && r5p4 && r12jlf && r14u_plan && w.act_const && p3_cur_slot() <= 43 && !la94b2 && actfold.is_none() && af7.is_empty()
                && r3_flag("R12_DECODE_PERM") && rt.m.as_ref().unwrap().pre[3] == jl[3] && rt.m.as_ref().unwrap().pre[4] == jl[4];
            let gip_elig = gipm || (!la94b2 && slim && rt.m.is_none() && r3_flag("R12_DECODE_PERM") && jc && (w.act_const || actfold.is_some() || (cfg!(test) && r3_flag("B793_GIPFORCE") && (189..=202).contains(&p3_cur_slot()))));
            assert!(actfold.is_none() || (gip_elig && b793_gip()) || (cfg!(test) && r3_flag("B793_NOGIPFOLD")), "b793 ACTFOLD: needs Gipfeli");
            let gip = b793_gip() && gip_elig && !(cfg!(test) && r3_flag("B793_NOGIPFOLD"));
            // B793_SWAPHMR=1 (paired-comparison control arm only): the parent decode measures res1 before res0 on the Gipfeli-eligible
            // slots, so its Hmr coins line up with Gipfeli's (res1 first) shot for shot; the circuit is the same up to the commuting order
            let swaphmr = r3_flag("B793_SWAPHMR") && gip_elig && !gip;
            let e = if nj { if nj_hold != NOQ { b.unhold_id(nj_hold); } nj_out[3] } else if la94b2 {
                // Schaffhuuserzopf part 2: act's lane, X-flipped to !act, is the decode's sixth wire
                let a = act.unwrap();
                b.x(a);
                a
            } else if gip { NOQ } else { b.alloc() };
            let mb = if nj { vec![] } else { b.fresh_bits(2) };
            let e = if nj { e } else if gip {
                assert!(self.x[W - 1] != NOQ && !b.is_free(self.x[W - 1]), "B793 Gipfeli: X[W-1] is not a live lane");
                if std::env::var_os("B793_DBG").is_some() { eprintln!("B793GIP fire slot {} live {}", p3_cur_slot(), b.live); }
                // b793b FPARK (B793_FPARK=1): the shots that finish at this slot (LA_post = 0 on an active slot) carry the cofactor's low bit on X[W-1]; park x = 1 on them
                // (sY = 0 there: B tA = p), so Gipfeli sees (t, 1), valid for all 32 t; undone right after the decode
                let mut fpk: Option<(Vec<(QubitId, bool)>, Vec<QubitId>)> = None;
                if b793_fpark() && actfold.is_some() {
                    let xl = self.x[W - 1];
                    for i in 0..R_BITS { b.cx(sx[i], self.la[i]); }
                    let pf: Vec<(QubitId, bool)> = self.la.iter().filter(|&&q| q != NOQ && !r3h.contains(&q) && !(b793b_break("fp4") && actfold.map_or(false, |(l5, l6)| q == l5 || q == l6))).map(|&q| (q, true)).collect();
                    let dl: Vec<QubitId> = super::mask::borrowed().into_iter().filter(|q| !pf.iter().any(|l| l.0 == *q) && *q != xl && *q != sy[0] && !jl.contains(q)).collect();
                    assert!(dl.len() >= 6 && (pf.len() == 7 || b793b_break("fp4")), "b793 FPARK: {} borrowed lanes, {} LA literals", dl.len(), pf.len());
                    let prem = std::env::var("B793_PREMISE").map_or(false, |v| v == "3") && cfg!(test);
                    let mut fl = NOQ;
                    if cfg!(test) {
                        // test probes: F lane for the histogram; AND(pf) & sY is |0>
                        fl = b.alloc();
                        and_into(b, &pf, fl, );
                        let t1 = b.alloc();
                        let mut l = pf.clone(); l.push((sy[0], false));
                        and_into(b, &l, t1);
                        if !b793b_break("fp4") { zero_probe(b, &[t1]); }
                        and_into(b, &l, t1);
                        b.free(t1);
                        if prem {
                            let mut v = vec![QubitId(PREMISE_MARK), xl];
                            v.extend(jl.iter().copied());
                            v.push(QubitId(0));
                            v.push(fl);
                            ZERO_PROBES.with(|p| p.borrow_mut().push((b.ops.len(), v)));
                        }
                    }
                    let mut l1 = pf.clone(); l1.push((xl, true));
                    let mut l2 = pf.clone(); l2.push((sy[0], false));
                    if b793b_break("fp5") { and_dirty(b, &l2, xl, &dl); and_dirty(b, &l1, sy[0], &dl); } else if !b793b_break("fp1") { and_dirty(b, &l1, sy[0], &dl); and_dirty(b, &l2, xl, &dl); }
                    if cfg!(test) {
                        let t2 = b.alloc();
                        let mut l = pf.clone(); l.push((xl, true));
                        and_into(b, &l, t2);
                        if !b793b_break("fp1") && !b793b_break("fp4") && !b793b_break("fp5") { zero_probe(b, &[t2]); }
                        and_into(b, &l, t2);
                        b.free(t2);
                        if prem {
                            let mut v = vec![QubitId(PREMISE_MARK), xl];
                            v.extend(jl.iter().copied());
                            v.push(QubitId(2));
                            v.push(fl);
                            ZERO_PROBES.with(|p| p.borrow_mut().push((b.ops.len(), v)));
                        }
                        and_into(b, &pf, fl);
                        b.free(fl);
                    }
                    fpk = Some((pf, dl));
                }
                let a1l = b793_decode(b, &jl, self.x[W - 1], &mb);
                if let Some((pf, dl)) = fpk {
                    let xl = self.x[W - 1];
                    let mut l1 = pf.clone(); l1.push((xl, true));
                    let mut l2 = pf.clone(); l2.push((sy[0], false));
                    if !b793b_break("fp2") { and_dirty(b, &l2, xl, &dl); }
                    if !b793b_break("fp3") { and_dirty(b, &l1, sy[0], &dl); }
                    for i in 0..R_BITS { b.cx(sx[i], self.la[i]); }
                }
                if (p3_cur_slot() as i64) >= B793_MIMIC_FROM {
                    // a1 moves to the lane the parent's e would have taken (the lowest free id other than jl[3]'s), so every
                    // later id-driven choice (R11_LA7's lent-id test, r5_rebind) sees the parent's lane picture: peak = pre-decode live
                    zero_probe(b, &[jl[3]]);
                    b.free(jl[3]);
                    let en = b.alloc_avoid(&[jl[3]]);
                    b.cx(a1l, en);
                    b.cx(en, a1l);
                    zero_probe(b, &[a1l]);
                    b.free(a1l);
                    en
                } else {
                    // slots below B793_MIMIC_FROM: a1 stays on jl[4] (no lent-id collision at r5_rebind; see REPORT)
                    if !gipm { // GIPM: jl[3] (|0>) is released by the R14 U early release below, as on the parent's masked slots
                    zero_probe(b, &[jl[3]]);
                    b.free(jl[3]);
                    }
                    a1l
                }
            } else {
                r4_decode(b, &jl, e);
                if la94b2 && !r14b_break("p2t") { la94b_fin(b, &jl, e, &self.dirty); }
                e
            };
            // res is |0> on steps and finished shots: X-measure it; the stall shots' phase is owed to the next slot
            r5tl(b, "decode");
            if nj {
            } else if swaphmr {
                b.hmr_to(jl[4], mb[1]);
                b.hmr_to(jl[3], mb[0]);
            } else if !gip {
            b.hmr_to(jl[3], mb[0]);
            b.hmr_to(jl[4], mb[1]);
            }
            if nj {
                // b792 SWEEP: out = act & (rho, a1) already (nj_run gates bb): a1 = e is final, no a1 = e ^ !act step
            } else if !af7.is_empty() {
                let dl: Vec<QubitId> = self.dirty.iter().copied().filter(|q| *q != e && !jl.contains(q) && !af7.contains(q)).collect();
                let l: Vec<(QubitId, bool)> = af7.iter().map(|&q| (q, false)).collect();
                if !b793b_break("af3") { and_dirty(b, &l, e, &dl); }
            } else if let Some((l5, l6)) = actfold {
                // b793b ACTFOLD: a1 = e ^ !act with !act = LA[5] & LA[6] (finished shots decode t = 0: e = 1)
                if !b793b_break("af3") { b.ccx(l5, l6, e); }
            } else if let (Some(a), false) = (act, la94b2) {
                // a1 = e ^ !act (finished shots have e = 1)
                b.cx(a, e);
                b.x(e);
            }
            if !nj { R4_PEND.with(|p| *p.borrow_mut() = Some((mb, !w.act_const))); }
            if slim {
                // R3F_SLIM: g and the measured res lanes are detached here, before the hosts are re-acquired
                vl4.retain(|&q| q != rt.g);
                // (Gipfeli frees jl[3] and jl[4] itself)
                if !gip && !nj {
                    zero_probe(b, &jl[RHO_BITS..]);
                    b.free_n(&jl[RHO_BITS..]);
                }
                rt.g = NOQ;
            }
            if let Some((j, k)) = la94b.filter(|_| zopf_early.is_some() && b793_zlate()) {
                // b793b ZLATE: LA[7] stays out through the undo rows (see b793_zlate)
                B793_ZLATE.with(|c| c.set(Some((j, k))));
            } else if let Some((j, k)) = la94b {
                // Schaffhuuserzopf: LA[7] back as a fresh |0> lane, the offset added back (u again)
                assert!(self.la[LB_BITS - 2] == NOQ, "Schaffhuuserzopf: LA[7] re-bound inside the sweep");
                // never on a lent lane's id: lent lanes are taken back by id later (r5_rebind, R11_LA7's LA[7] test)
                let mut avoid: Vec<QubitId> = vl4.clone();
                avoid.extend(&r3h);
                avoid.extend(&lend);
                self.la[LB_BITS - 2] = b.alloc_avoid(&avoid);
                assert!(!avoid.contains(&self.la[LB_BITS - 2]), "Schaffhuuserzopf: LA[7] re-bound on a lent id");
                self.cap += 1;
                let lv: Vec<QubitId> = self.la[j..LB_BITS - 1].to_vec();
                if !r14b_break("nosub") { la94b_field_add(b, &lv, k, false, &self.dirty); }
            }
            if rt.m.is_some() && r5p4 {
                // R5_PRE4: the measured res lane jl[4] is the undo rows' idle prefix lane: released before the hosts
                // come back (Masked::free skips the NOQ left in its place)
                if gipm {
                    // GIPM: jl[4] holds a1 (the parent's e), not |0>: the mask's f is re-bound fresh at the undo rows
                    let m = rt.m.as_mut().unwrap();
                    m.f = NOQ; m.gf = NOQ;
                    gipm_pend = true;
                } else {
                zero_probe(b, &[jl[4]]);
                // R12_JLF: the lane is the mask's f, kept (|0> after the X-measure)
                if !r12jlf { b.free(jl[4]); }
                }
                rt.m.as_mut().unwrap().pre[4] = NOQ;
                p4_out = true;
            }
            // R14 läckBobby-b U: on the U-planned slots the measured res lane jl[3] (|0>) is released here too, before
            // the hosts come back (the parent keeps it as the undo decoder's retained level); the cap is lowered by one
            // until after the undo rows. If the R9 C chain does not take the RSHORT5T form below, a fresh |0> lane takes
            // its place there (same state).
            let mut r14u_early = false;
            if rt.m.is_some() && r5p4 && r14u_plan && rt.m.as_ref().unwrap().pre[3] == jl[3] {
                zero_probe(b, &[jl[3]]);
                b.free(jl[3]);
                rt.m.as_mut().unwrap().pre[3] = NOQ;
                r14u_early = true;
                self.cap -= 1;
            }
            if r14j && rt.m.is_some() && r5mrowy {
                // R14 läckBobby-b J: y was never bound: the parent's R5_MROWY outcome (y out through the undo rows)
                assert!(rt.y == NOQ);
                y_rt_out = true;
            } else if rt.m.is_some() && r5mrowy && vl4.contains(&rt.y) {
                // R5_MROWY: RowTmp's zero source y stays lent through the undo rows and is not bound again
                let yq = rt.y;
                vl4.retain(|&q| q != yq);
                rt.y = NOQ;
                y_rt_out = true;
            }
            if rt.m.is_some() && r5yoff {
                // R5_YOFF: Y[W-1] (|0>, YTOP-SWEEP) stays out from here to the end of the undo rows; their plain rows
                // take the idle mask scratch as pool (R5_MPOOL)
                let yq = self.y[W - 1];
                if vl4.contains(&yq) || r3h.contains(&yq) {
                    vl4.retain(|&q| q != yq);
                    r3h.retain(|&q| q != yq);
                } else {
                    zero_probe(b, &[self.y[W - 1]]);
                    b.free(self.y[W - 1]);
                }
                lend.retain(|&q| q != self.y[W - 1]);
                y_out = true;
            }
            // R9 rowtmp c (act elision): a1 = e and rho = jl[0..3] are final here. On every shot act = a1 | (rho != 0):
            // finished shots decode t = 0 forced to rho = 0, e = 1, so a1 = e ^ !act = 0; on active shots a1 = e = [t < 8]
            // and the decode's rho is 0 only at t = 0 (t >= 8 gives rho in 1..7). So !act = AND(!a1, !rho) is erased by
            // measurement and act's lane released until the un-renormalisation's counter re-forms it; `self.cap` is
            // lowered by one meanwhile so every `self.room`-driven choice in between is unchanged (P2_CAP too with
            // R9_RT_P2N). Readers of act in between: only the denorm's sY erase (`r9_sy_erase`, reads a1 / rho
            // instead); the un-renormalisation re-forms act. Needs SY_ACT_GATE (finished shots: sY = 0, so t = 0).
            assert!(!la94b2 || (r9_rt('c') && act.is_some() && act == z0 && i5_rcnt() && ns0 && sy_act_gate()),
                    "Schaffhuuserzopf part 2: act's lane holds a1 but R9 rowtmp c does not take over act");
            if r9_rt('c') && act.is_some() && act == z0 && i5_rcnt() && ns0 && sy_act_gate() {
                let a = act.unwrap();
                if !af7.is_empty() {
                    // ACTFOLD=2: !act = AND(!a1, !rho): LA := sX on those shots (LA[i] ^= !sX[i], i < 5; LA[5], LA[6] ^= 1)
                    let lits = [(e, true), (jl[0], true), (jl[1], true), (jl[2], true)];
                    let dl: Vec<QubitId> = self.dirty.iter().copied().filter(|q| *q != e && !jl.contains(q) && !af7.contains(q) && !sx.contains(q)).collect();
                    for i in 0..R_BITS {
                        let mut l = lits.to_vec();
                        l.push((sx[i], true));
                        if !(i == 0 && b793b_break("af22")) { and_dirty(b, &l, self.la[i], &dl); }
                    }
                    and_dirty(b, &lits, self.la[R_BITS], &dl);
                    and_dirty(b, &lits, self.la[R_BITS + 1], &dl);
                    AF_PAIR.with(|c| c.set(None));
                    AF_LANES.with(|c| c.borrow_mut().clear());
                } else if let Some((l5, l6)) = actfold {
                    // b793b ACTFOLD: !act = AND(!a1, !rho) puts the pair back on the true bits of u (finished shots: 0, 0)
                    let lits = [(e, true), (jl[0], true), (jl[1], true), (jl[2], true)];
                    let dl: Vec<QubitId> = self.dirty.iter().copied().filter(|q| *q != e && !jl.contains(q) && *q != l5 && *q != l6).collect();
                    if cfg!(test) && std::env::var("B793_AFPROBE").map_or(false, |v| v == "3") {
                        let c = AF_SAVE.with(|x| x.borrow_mut().take()).unwrap();
                        and_dirty(b, &lits, c[0], &dl);
                        zero_probe(b, &c);
                        and_dirty(b, &lits, c[0], &dl);
                        b.free_n(&c);
                    }
                    if !b793b_break("af2") { and_dirty(b, &lits, l5, &dl); }
                    and_dirty(b, &lits, l6, &dl);
                    AF_PAIR.with(|c| c.set(None));
                    if let Some(c) = AF_SAVE.with(|x| x.borrow_mut().take()) {
                        b.cx(l5, c[0]);
                        b.cx(l6, c[1]);
                        zero_probe(b, &c);
                        b.cx(l5, c[0]);
                        b.cx(l6, c[1]);
                        b.free_n(&c);
                    }
                } else if !la94b2 {
                let lits = [(e, true), (jl[0], true), (jl[1], true), (jl[2], true)];
                b.x(a);
                if !r9_rt_break("c1") { erase_and(b, self, a, &lits); }
                zero_probe(b, &[a]);
                b.free(a);
                }
                // (Schaffhuuserzopf part 2: act's lane already holds a1 = e; live is the parent's here, the cap follows it)
                // b793b ACTCAP: on slots 188-202 the cap is not lowered for the released act lane (room for the undo rows' pool); the cap is not raised again at the un-renormalisation
                let actcap = b793_actcap() && (188..=202).contains(&p3_cur_slot());
                B793_ACTCAP.with(|c| c.set(actcap));
                if actfold.is_some() { if actcap { self.cap += 1; } } else if !actcap { self.cap -= 1; }
                r9_p2_shift(false);
                act_el = Some((e, [jl[0], jl[1], jl[2]]));
                // poison ids: any reader of act left unconverted touches a lane that does not exist
                act = Some(NOQ);
                z0 = Some(NOQ);
                y_act = if sy_act_gate() { act } else { None };
            }
            // re-acquire the lent lanes (r3h too: no backward sweep follows); a1 may sit on one of them, whose owner
            // then takes a fresh |0> lane (after every other lent lane is back, so it cannot land on one)
            vl4.extend(r3h.drain(..));
            r5tl(b, "preacq");
            if r5e {
                // R5_EARLY: any lent lane may now hold rho, res or a1: each such lane's owner is re-bound
                self.r5_rebind(b, &mut vl4, &mut rt, &mut lend, e);
            } else {
            for &q in &vl4 { if q != e { b.acquire(q); } }
            }
            if !r5e && vl4.contains(&e) {
                let nq = b.alloc();
                if rt.f == e { rt.f = nq; if let Some(m) = rt.m.as_mut() { m.c0 = nq; } }
                else if rt.y == e { rt.y = nq; }
                else if rt.g == e { rt.g = nq; if let Some(m) = rt.m.as_mut() { m.t = nq; } }
                else if self.y[W - 1] == e { self.y[W - 1] = nq; }
                else { let i = self.la.iter().position(|&q| q == e).expect("R4 rebind"); self.la[i] = nq; }
                for q in lend.iter_mut() { if *q == e { *q = nq; } }
                for q in vl4.iter_mut() { if *q == e { *q = nq; } }
            }
            zero_probe(b, &vl4);
            self.b792_s255_rebind(b, &mut lend, r5e && r3_flag("R11_LA7") && rt.m.is_none());
            if jc {
                // R15-JC: the rows' f, taken fresh where the parent re-acquires it (R10_RBF: on plain ROW-Y / ROW-F slots
                // with no room it is left out, the undo rows' pool one lane shorter)
                assert!(rt.f == NOQ);
                if row_y(&rt) && row_f() && r10_on("R10_RBF", self.room(b), 1) {
                    // stays NOQ
                } else {
                    rt.f = b.alloc();
                    zero_probe(b, &[rt.f]);
                    if jc_f_lent { lend.push(rt.f); }
                }
                if jc_ac {
                    // the zero source y, taken fresh where the parent re-acquires it; on ROW-Y slots (the undo rows never
                    // read it, as on R11 slots, where y leaves for good) only where the room allows: the undo rows' pool
                    // is then one lane shorter (R10_RBF's rule for f)
                    assert!(rt.y == NOQ);
                    if !(row_y(&rt) && self.room(b) < 1) {
                        rt.y = b.alloc();
                        zero_probe(b, &[rt.y]);
                        if jc_y_lent { lend.push(rt.y); }
                    }
                }
            }
            a1 = e;
            r = jl[..RHO_BITS].to_vec();
            // rt keeps only the measured res lanes (none once detached); the rows pools must not take r's lanes
            let s2 = rt.m.as_ref().map_or(false, |m| r5p4 && m.pre[4] == NOQ) && r10_on("R10_SH2", self.room(b), RHO_BITS);
            if r14u_early && !s2 {
                // R14 läckBobby-b U fallback (the R9 C chain does not run here): the parent's lane 3, fresh |0>
                self.cap += 1;
                rt.m.as_mut().unwrap().pre[3] = b.alloc();
                r14u_early = false;
            }
            if let (true, Some(m)) = (s2, rt.m.as_mut()) {
                // R10_SH2 (claude-r8): the undo rows' decoder keeps a 3-lane retained prefix (bits 1 and 0 join each
                // toggle through a borrowed lane): 2 fresh |0> lanes and the measured res lane jl[3]
                // R12_SH3 (fable 796b): one level shorter still: 1 fresh |0> lane and the measured res lane jl[3]
                let s3 = r10_on("R12_SH3", self.room(b), RHO_BITS - 1);
                // R9_PREFIX C (r9 prefix): no fresh lane at all: the measured res lane jl[3] is the decoder's only
                // retained level (bits 5, 4); bit 3 is formed on the mask's AND temp g between cells (mask::RSHORT4T)
                let s4 = s3 && r9p_on('C', self.room(b), 1);
                // R14 läckBobby-b U (on the slots F planned it for): no retained level at all: the
                // measured res lane jl[3] (|0>) is released and bits 5, 4 join the AND temp at each toggle (RSHORT5T)
                let s5 = s4 && r14u_early;
                if r14u_early && !s5 {
                    // (not the RSHORT5T form after all: the parent's lane 3, fresh and |0>, the cap back)
                    self.cap += 1;
                    m.pre[3] = b.alloc();
                }
                if s5 {
                    r14p_log('U', b, self.room(b));
                    for i in 0..4 { m.pre[i] = NOQ; }
                    R14S5.with(|c| c.set(true));
                    // the parent's retained lane lives through the undo rows: the cap stays lowered until after them
                    r14u = true;
                } else if s4 {
                    r9p_log('C', b, self.room(b));
                    m.pre[0] = m.pre[3];
                    m.pre[1] = NOQ;
                    m.pre[2] = NOQ;
                    m.pre[3] = NOQ;
                    R9S4.with(|c| c.set(true));
                } else if s3 {
                    let nf = b.alloc();
                    m.pre[1] = m.pre[3];
                    m.pre[2] = NOQ;
                    m.pre[3] = NOQ;
                    m.pre[0] = nf;
                    R12S3.with(|c| c.set(true));
                } else {
                let nf = b.alloc_n(RHO_BITS - 1);
                m.pre[2] = m.pre[3];
                m.pre[3] = NOQ;
                m.pre[..RHO_BITS - 1].copy_from_slice(&nf);
                }
                R10S2.with(|c| c.set(true));
                rt.jl = m.pre.iter().copied().take(R_BITS).filter(|&q| q != NOQ).collect();
                zero_probe(b, &rt.jl);
            } else if let Some(m) = rt.m.as_mut() {
                // masked rows: jl is the mask's decoder prefix, which the undo rows need |0>: rho keeps its lanes and
                // the prefix takes 3 fresh |0> lanes in their place (no gates)
                let nf = b.alloc_n(RHO_BITS);
                m.pre[..RHO_BITS].copy_from_slice(&nf);
                rt.jl = m.pre.iter().copied().take(R_BITS).filter(|&q| q != NOQ).collect();
                zero_probe(b, &rt.jl);
            } else {
                rt.jl = if slim { vec![] } else { zero_probe(b, &jl[RHO_BITS..]); jl[RHO_BITS..].to_vec() };
            }
            lend.retain(|q| !r.contains(q));
            r5tl(b, "postacq");
            if rowlog() { eprintln!("R4LIVE end-of-decode live {} masked {} act {}", b.live, masked_rows as u8, act.is_some() as u8); }
        } else {
        // R3-VERG pricing instrument only (R3_RHO_EXTRA=n raises the cap by n inside the rho section)
        let rho_x: u64 = std::env::var("R3_RHO_EXTRA").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0);
        self.cap += rho_x;
        // (YTOP-SWEEP: Y[W-1] is |0> here too on VERG slots, which run no OR lanes; R3_VROOM_Y=1 lends it as well)
        let vy = vroom && ytsw && std::env::var("R3_VROOM_Y").map_or(false, |v| v.trim() == "1");
        let vlent: Vec<QubitId> = if vroom {
            let mut l = if self.room(b) + 3 + vy as usize >= 4 { vec![rt.f, rt.y, rt.g] } else { vec![rt.f] };
            // R3-FIT799: not when R3_YTOPB already hosts Y[W-1] (r3h)
            if vy && !r3h.contains(&self.y[W - 1]) { l.push(self.y[W - 1]); }
            l
        } else { vec![] };
        zero_probe(b, &vlent);
        for &q in &vlent { b.free(q); }
        // R3_RA1YG (cap < 813): y and g are |0> between the two jl maps; they go to the room for rho's product lanes
        // (the fallback below takes them back first: it uses them as t and c)
        // R3-FIT799: not where VROOM already lent y and g
        let mut r3yg = self.cap < 813 && r3_flag("R3_RA1YG") && !vlent.contains(&rt.y);
        if r3yg {
            zero_probe(b, &[rt.y, rt.g]);
            b.free_n(&[rt.y, rt.g]);
        }
        // R3_ANF3 (cap < 813): with act = 1 classically rho_anf's AND tree is 3 deep, so 3 lanes suffice
        let anf_need = if self.cap < 813 && r3_flag("R3_ANF3") && act.is_none() { 3 } else { 4 };
        if rho_anf8() && self.room(b) >= 5 {
            rho_anf8_into(b, act, &jl, &r);
            let mut lits = act_lits(act);
            lits.extend([(jl[3], true), (jl[4], true)]);
            and_auto(b, self, &lits, a1);
        } else if rho_anf() && self.room(b) >= anf_need {
            rho_anf_into(b, act, &jl, &r);
            let mut lits = act_lits(act);
            lits.extend([(jl[3], true), (jl[4], true)]);
            and_auto(b, self, &lits, a1);
        } else {
            if r3yg {
                b.acquire(rt.y);
                b.acquire(rt.g);
                r3yg = false;
            }
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
        if r3yg {
            b.acquire(rt.y);
            b.acquire(rt.g);
        }
        self.cap -= rho_x;
        for &q in &vlent { b.acquire(q); }
        zero_probe(b, &vlent);
        if fold {
            jl_map(self, b);
        } else {
            add_on_sm(b, self, &jl, &sy[..sy_len], false, false, rt.g, false);
            add_on_sm(b, self, &jl, &sx, true, true, rt.g, false);
            for &q in &jl {
                b.x(q);
            }
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
        if rowlog() { eprintln!("WL_SWB room {} fl {}", self.room(b), fl.len()); }
        if r3_subprof() { prof(b, "i.sweepb"); }
        if r4 {
            // R4-RHO: J is gone (res measured in the decode): no step repair, no backward sweep
        } else if mj {
            // R3-VERG: f = [jl != 0] cleared exactly, jl X-measured; step shots repaired here with J = jl_map(r) on
            // jl's freed lanes, stall shots at the next inverse slot (MJ_PEND)
            let brk = mj_break();
            let nslot = MJ_NSLOT.with(|c| { let v = c.get(); c.set(v + 1); v });
            let wrong = brk == "5" && nslot == std::env::var("MJ_BREAK_SLOT").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0);
            if brk != "4" && !vroom {
                b.x(rt.f);
                let lits: Vec<(QubitId, bool)> = jl.iter().map(|&q| (q, true)).collect();
                and_auto(b, self, &lits, rt.f);
            }
            let mbits = b.fresh_bits(R_BITS);
            for i in 0..R_BITS {
                b.hmr_to(jl[i], mbits[i]);
            }
            if brk != "1" {
                for i in 0..RHO_BITS {
                    b.cx(r[i], jl[i]);
                }
                if !wrong {
                    if fold {
                        // jl_map (inlined: the closure's borrow of self ends before p3)
                        for &q in &jl {
                            b.x(q);
                        }
                        b.cx(sy[0], rt.g);
                        b.x(rt.g);
                        add_on_sm(b, self, &jl, &sx, false, false, rt.g, true);
                        b.x(rt.g);
                        b.cx(sy[0], rt.g);
                    } else {
                        for &q in &jl {
                            b.x(q);
                        }
                        add_on_sm(b, self, &jl, &sx, true, false, rt.g, false);
                        add_on_sm(b, self, &jl, &sy[..sy_len], false, true, rt.g, false);
                    }
                }
                for i in 0..R_BITS {
                    b.push_condition(mbits[i]);
                    b.cz(a1, jl[i]);
                    b.pop_condition();
                }
                if !wrong {
                    if fold {
                        // jl_map (inlined: the closure's borrow of self ends before p3)
                        for &q in &jl {
                            b.x(q);
                        }
                        b.cx(sy[0], rt.g);
                        b.x(rt.g);
                        add_on_sm(b, self, &jl, &sx, false, false, rt.g, true);
                        b.x(rt.g);
                        b.cx(sy[0], rt.g);
                    } else {
                        add_on_sm(b, self, &jl, &sy[..sy_len], false, false, rt.g, false);
                        add_on_sm(b, self, &jl, &sx, true, true, rt.g, false);
                        for &q in &jl {
                            b.x(q);
                        }
                    }
                }
                for i in 0..RHO_BITS {
                    b.cx(r[i], jl[i]);
                }
            }
            if brk != "2" {
                MJ_PEND.with(|p| *p.borrow_mut() = Some((mbits, MARKER_FREE && !w.act_const)));
            }
        } else if rot_used {
            sweep_rot(b, self, act, w, &rt, false);
        } else if let Some(d) = defer_bits.as_ref() {
            // SWEEP-DEFER: the backward pass must regenerate every forward y (the non-unary sweep_bwd)
            if self.room(b) >= R_BITS - 1 {
                let ch2 = b.alloc_n(R_BITS - 1);
                sweep_bwd_d(b, self, act, w, &rt, &ch2, true, Some(d));
                b.free_n(&ch2);
            } else {
                sweep_bwd_d(b, self, act, w, &rt, &self.dirty, false, Some(d));
            }
        } else if !fl.is_empty() {
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
        for &q in &r3h {
            b.acquire(q);
        }
        self.b792_s255_rebind(b, &mut lend, false);
        if let Some(c) = guard {
            if !guard_break(1) { inc_auto(b, self, c, &kt5v); }
            erase_mbu(b, c, |b| lt_cin_sm(b, self, &sx, &kt5v, sy[0], None));
            b.free(c);
        }
        if slim && !r4 { rt.detach(b); }
        r5tl(b, "bwd");
        // REPARK-X0: X[0] (outside the parked window) is a |0> decoder lane of the repark before it is set to 1
        let x0l = x0h && split && repark_x0() && park_lo(w) >= 1;
        if ytsw && !y_out { zero_probe(b, &[self.y[W - 1]]); }
        // R5_FOLD: the undo rows read no X[0] lane; it is bound again after them
        let x0_late = x0h && r5fold && y_rt_out && !x0l;
        // R10_X0 (claude-r8): on plain act-constant slots with no room left, X[0] (= 1) is bound only after the undo
        // rows, which read a pool lane set to 1 in its place
        let r10x0 = x0h && !x0_late && !x0l && rt.m.is_none() && !park && !split && partial.is_none() && !y_out
            && r10_on("R10_X0", self.room(b), 1);
        let x0_late = x0_late || r10x0;
        // b792w5 P12X: X[0] (= 1) is bound only where the denormalisation's X funnel first reads it; nothing between the undo rows and there reads X[0]
        let x0_def = b792_p12x() && x0_late && !split && ns0 && sw_carry();
        if x0_def { self.x[0] = NOQ; }
        // FIXX0: only the plain and the R10_X0 re-binds are handled on non-act-constant slots
        assert!(!fx0 || (!x0l && (!x0_late || r10x0)), "FIXX0: unhandled X[0] re-bind path (x0l {} x0_late {} r10x0 {}, slot {})",
                x0l as u8, x0_late as u8, r10x0 as u8, p3_cur_slot());
        if x0h && !x0_late {
            self.x[0] = b.alloc();
            if fx0 { fx0_unpark(b, self.x[0], fx0z, fx0s4, fx0_rel, "plain"); }
            if !x0l { b.x(self.x[0]); }
        }
        prof(b, "i.rows_rev");
        p3(b, self, "i.rows_rev");
        r5tl(b, "rowsrev0");
        if rowlog() && r4 { eprintln!("R4LIVE rows_rev live {}", b.live); }
        assert!(!(R10YT.with(|c| c.get()) && (!ytsw || split || y_out)), "R10_RBY: Y[W-1] read by the undo rows");
        if !ytsw && ytop && !s0y {
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
        if gipm_pend {
            let q = b.alloc();
            let m = rt.m.as_mut().unwrap();
            m.f = q; m.gf = q;
            gipm_pend = false;
        }
        if r5p4 && !p4_out {
            let q = rt.m.as_ref().unwrap().pre[4];
            zero_probe(b, &[q]);
            b.free(q);
            rt.m.as_mut().unwrap().pre[4] = NOQ;
            p4_out = true;
        }
        let room1 = self.room(b);
        self.cap += extra_rows();
        let own = pool_for(b, self, (NB + 1).saturating_sub(lend.len()), 0);
        self.cap -= extra_rows();
        let mut pool: Vec<QubitId> = own.iter().chain(&lend).copied().take(NB + 1).collect();
        // m1-shell diagnostic (inert unless M1_ROWF is set): lanes the undo rows' ROW-F / R10_X0 shapes need beyond the
        // pool; borrow: every shortfall is lent fresh lanes over the cap; close: ROW-F row 0 runs pool-free (in
        // division_rows) and only R10_X0 is lent up to 2 lanes
        let m1mode = std::env::var("M1_ROWF").ok();
        // R14 misc94 x2: on the x2 slots the undo rows fold their X[0] cell (the forward rows ran unrolled there), so
        // R10_X0 needs one pool lane (ROW-F row 0's carry-in), not two
        // r10x0: the fold replaces exactly the parent's constant-1 stand-in (no new X[0] premise); act-constant, no FIXX0
        let x2fx = r3_flag("B793_X2FX") && (188..=202).contains(&w.slot);
        let m94x = m94x_slot(w) && r10x0 && (w.act_const || x2fx) && (!fx0 || x2fx) && m1mode.as_deref() == Some("close") && row_y(&rt) && row_f() && rt.m.is_none()
            && row_recs.iter().all(|r| r.rc.is_empty()) && w.k + 1 <= NB && !park && !split && partial.is_none();
        if std::env::var_os("M94_DBG").is_some() && m94x_slot(w) { eprintln!("M94X fire {} div {} slot {} r10x0 {} fx0 {} rolled {} k {}", m94x as u8, M1DIV.with(|c| c.get()), p3_cur_slot(), r10x0 as u8, fx0 as u8, row_recs.iter().filter(|r| !r.rc.is_empty()).count(), w.k); }
        let mut m1b: Vec<QubitId> = vec![];
        if let Some(m) = m1mode.as_deref() {
            let rowf_need = row_y(&rt) && row_f();
            let need = match m { "borrow" => if rowf_need { 2 + r10x0 as usize } else if r10x0 { 3 } else { 0 }, _ => if r10x0 { if b792_rr() && !rr_mode("p0") && !rr_mode("re") { 1 - m94x as usize } else { 2 - m94x as usize } } else { 0 } };
            if pool.len() < need {
                eprintln!("M1BORROW div {} slot {} sect i.unrows pool {} need {} r10x0 {} rowf {} live {} cap {} mode {}",
                          M1DIV.with(|c| c.get()), p3_cur_slot(), pool.len(), need, r10x0 as u8, rowf_need as u8, b.live, self.cap, m);
                if std::env::var_os("M94_DBG").is_some() {
                    eprintln!("M94RT slot {} s0 {} g {} f {} y {} jl {:?} lend {:?} own {:?} ytop {} x0 {}", p3_cur_slot(), rt.s0.0, rt.g.0, rt.f.0, rt.y.0,
                              rt.jl.iter().map(|q| q.0).collect::<Vec<_>>(), lend.iter().map(|q| q.0).collect::<Vec<_>>(), own.iter().map(|q| q.0).collect::<Vec<_>>(), self.y[W - 1].0, self.x[0].0);
                }
                if std::env::var_os("RR_PROBE").is_some() { b.live -= (need - pool.len()) as u64; }
                m1b = b.alloc_n(need - pool.len());
                pool.extend(&m1b);
            }
        }
        if rowlog() {
            eprintln!("WL_ROW split {} partial {:?} room_park {room_park} masked {} park {} zn {} k {} mx {} room_rows {} room_rev {} lend {} pool_fwd {} pool_rev {} act_const {}",
                      split as u8, partial, masked_rows as u8, park as u8, zn, w.k, w.mx, room0, room1, lend.len(), pool_fwd_len, pool.len(), w.act_const as u8);
            eprintln!("WL_ROW2 dtop {} tight {} near {} la_cut {} x0h {} lo {} top {} ytop {} free_mode {}", w.dtop, w.dtop_tight as u8,
                      w.dtop_near as u8, la_cut as u8, x0h as u8, park_lo(w), top, ytop as u8, free_mode as u8);
        }
        r5tl(b, "revpool");
        r6t(b, "ur0", pool.len());
        b.begin();
        if r5p4 { R5P4.with(|c| c.set(true)); }
        R10X0.with(|c| c.set(r10x0));
        M94X.with(|c| c.set(m94x));
        FX0P.with(|c| c.set(if r10x0 && fx0 { Some((fx0z, fx0s4)) } else { None }));
        let rs2 = super::mask::RSHORT2.with(|c| c.replace(R10S2.with(|c| c.get())));
        let rs3 = super::mask::RSHORT3.with(|c| c.replace(R12S3.with(|c| c.get())));
        let rs4 = super::mask::RSHORT4T.with(|c| c.replace(R9S4.with(|c| c.get())));
        let rs5 = super::mask::RSHORT5T.with(|c| c.replace(R14S5.with(|c| c.get())));
        let f6_nt_u = super::mask::NOTEMP.with(|c| c.replace(f6));
        R5MP.with(|c| c.set(r5mp));
        R5MY.with(|c| c.set(y_rt_out && !r5fold));
        R5FD.with(|c| c.set(r5fold && y_rt_out));
        R11C.with(|c| c.set(la5c));
        division_rows(b, self, w, &rt, &pool, park, top, partial,
                      if row_recs.is_empty() { RowRoll::No } else { RowRoll::Rev(&row_recs) });
        R11C.with(|c| c.set(0));
        R5MY.with(|c| c.set(false));
        R5FD.with(|c| c.set(false));
        R5MP.with(|c| c.set(false));
        R5P4.with(|c| c.set(false));
        super::mask::RSHORT2.with(|c| c.set(rs2));
        super::mask::RSHORT3.with(|c| c.set(rs3));
        super::mask::RSHORT4T.with(|c| c.set(rs4));
        super::mask::RSHORT5T.with(|c| c.set(rs5));
        super::mask::NOTEMP.with(|c| c.set(f6_nt_u));
        R10S2.with(|c| c.set(false));
        R12S3.with(|c| c.set(false));
        R9S4.with(|c| c.set(false));
        R14S5.with(|c| c.set(false));
        R10X0.with(|c| c.set(false));
        M94X.with(|c| c.set(false));
        FX0P.with(|c| c.set(None));
        let unrows = b.end();
        if !pdw0_price() { b.play(&unrows, true); }
        r6t(b, "ur.rows", pool.len());
        b.free_n(&own);
        if !m1b.is_empty() { if std::env::var_os("RR_PROBE").is_some() { b.live += m1b.len() as u64; } b.free_n(&m1b); }
        zero_probe(b, &lend);
        // R14 läckBobby-b U: the cap comes back after the undo rows
        if r14u { self.cap += 1; }
        // losgahts A (R14_LA94): sY out right after the RowTmp is released, where the LB restore below is R13_LBR or
        // the SYFOLD inverse (both re-formed without sY) and the denorm is NORM-STAGE0's (Y's part is the a-shift back)
        let la94a_ok = r14_parts('A') && ns0 && i5_syfold() && sy.len() == 1 && sy_len == 1 && free_mode && lb_host()
            && !lb_sign_clear && lb_top == LB_BITS && r3_flag("R4_LBLATE") && below805(self.cap);
        let mut la94a = false;
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
        } else if y_out {
            // R5_YOFF: Y[W-1] comes back after the mask scratch is released (by id where free, else re-bound)
            rt.free(b);
            if la94a_ok { self.la94_sy_out(b, &sy, y_act, &act_el); la94a = true; }
            if x0_late && !x0_def {
                self.x[0] = b.alloc();
                if fx0 { fx0_unpark(b, self.x[0], fx0z, fx0s4, fx0_rel, "r10x0"); }
                b.x(self.x[0]);
            }
            if b792_den2() && ytop && r14m('y') && ns0 && !b792_break("den2off") {
                // b792 DEN2 (B792_DEN2): the y_out path's Y[W-1] (released across the undo rows, |0>) is not re-bound here but at the
                // I10 value ladder, exactly as the plain path's R14 misc94 y does (m94y): nothing between names Y[W-1] (denorm Y a-shift on
                // lanes 0..=NB, sY erase on Y0/Y1, un-renorm on X). Same fresh state (|0>, X'd where ytop) at I10.
                self.y[W - 1] = NOQ;
                m94y = Some(ytop && !b792_break("den2x")); // den2x: negative control, the later bind drops the X (Y[W-1] = 0 instead of 1)
            } else {
            let q = self.y[W - 1];
            if b.is_free(q) { b.acquire(q); } else { self.y[W - 1] = b.alloc(); }
            zero_probe(b, &[self.y[W - 1]]);
            if ytop {
                b.x(self.y[W - 1]);
            }
            }
        } else {
        // b792 S0Y: the undo rows have returned s0 (= Y[W-1]) to |0>; hand the lane back to the Y[W-1] path below, rt.free must not free it
        if s0y { assert!(rt.s0 == self.y[W - 1]); zero_probe(b, &[self.y[W - 1]]); rt.s0 = NOQ; }
        if ytop && !R10YT.with(|c| c.get()) {
            if r14m('y') && ns0 {
                // R14 misc94 y (plain path): Y[W-1] was lent |0> through both rows passes (YTOP-HOST flipped it) and is
                // read next by the I10 value ladder: released here (zero-probed) and re-bound there with the X, as on the
                // R10_RBY path, so piece y does not depend on R10_RBY's room-0 decision
                let q = self.y[W - 1];
                zero_probe(b, &[q]);
                b.free(q);
                self.y[W - 1] = NOQ;
                m94y = Some(true);
            } else {
            b.x(self.y[W - 1]);
            }
        }
        rt.free(b);
        if la94a_ok { self.la94_sy_out(b, &sy, y_act, &act_el); la94a = true; }
        if x0_late && !x0_def {
            self.x[0] = b.alloc();
            if fx0 { fx0_unpark(b, self.x[0], fx0z, fx0s4, fx0_rel, "r10x0"); }
            b.x(self.x[0]);
        }
        }
        if split {
        } else if park {
            park_junk(b, self, w, &z, top);
            b.free_n(&z);
        } else if let Some(lo_p) = partial {
            park_junk_partial(b, self, &z, top, lo_p);
            b.free_n(&z);
        }
        r5tl(b, "rtfree");
        if R10LA.with(|c| c.replace(false)) {
            if b792_slden8() && b792_slden() && !masked_rows && !la_cut && !la6 && !la_sign && p3_cur_slot() >= 189 {
                self.la[LB_BITS - 1] = NOQ;
                SLDEN8_PEND.with(|c| c.set(true));
            } else {
            self.la[LB_BITS - 1] = b.alloc();
            }
        }
        // R11_LA7 (fable, 797): LA[7]'s deferred re-bind (R10_RBL2) is held back once more, past the R8_IDEN open that
        // releases bit 7 again at the denormalisation: it is |0> here (u <= 256 - mx < 128, the R8_LAMX bound that
        // lent it), the SYFOLD inverse runs on hl <= 7 lanes and LA -= sX runs on the bound view (no borrow leaves bit
        // 6: u - sX >= 0). Bound at the R8 close with the other released bits. The cap is lowered by one meanwhile.
        let mut la7_pend = false;
        let mut slden_la7 = false;
        for i in R10LA2.with(|c| std::mem::take(&mut *c.borrow_mut())) {
            if i == LB_BITS - 2 && r3_flag("R11_LA7") && r3_flag("R8_IDEN") && !masked_rows && !la_cut && !la6 && !la_sign
                && r8_lhf_hb(self, w).is_some_and(|hb| hb <= LB_BITS - 2) {
                la7_pend = true;
                self.cap -= 1;
                continue;
            }
            // b792 SLDEN: where no R8 open will release bit 7 (R8_LHF off for the slot) LA[7] (|0>, R8_LAMX) is held out past the
            // denorm funnel instead of being bound before it; bound after sX / sY are free (see the re-bind there)
            if i == LB_BITS - 2 && b792_slden() && r3_flag("R11_LA7") && r3_flag("R8_IDEN") && !masked_rows && !la_cut && !la6 && !la_sign
                && r8_lhf_hb(self, w).is_none() {
                la7_pend = true;
                slden_la7 = true;
                self.cap -= 1;
                continue;
            }
            self.la[i] = b.alloc();
        }
        if R10YT.with(|c| c.replace(false)) {
            if r14m('y') && ns0 {
                // R14 misc94 "DonRwetter" y: R10_RBY's re-bind of Y[W-1] (a fresh lane, set to 1 where YTOP-HOST) waits
                // for its next reader, the I10 value ladder (lanes W - lb.1 .. W - 1): nothing from here to there names
                // Y[W-1] (the rest of the undo rows' close, the denormalisation's Y a-shift on lanes 0..=NB and its sY
                // erase on Y0 / Y1, the un-renormalisation on X); the lane stays NOQ meanwhile, so a missed reader
                // would touch the poison id (no op does: builder width and loads checked). Same fresh state at I10.
                m94y = Some(ytop);
            } else {
            self.y[W - 1] = b.alloc();
            if ytop { b.x(self.y[W - 1]); }
            }
        }
        // b793b LAOFF: LA stays in its offset form (see b793_laoff); la_cut slots only
        let la_off = b793_laoff() && (la_cut || la6) && masked_rows && r9_la() && b793_laoff_slot_ok(w);
        if la_off && std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE laoff slot {} la_cut {} la5 {}", p3_cur_slot(), la_cut as u8, la5 as u8); }
        if la_off {
            if la_cut {
                // bit 5: a fresh lane holding a copy of the sign (u' in -32..25: bits 5.. are sign copies)
                self.la[R_BITS] = b.alloc();
                if la_sign && !b793b_break("lao1") { b.cx(self.la[LB_BITS - 1], self.la[R_BITS]); }
            } else if la5 {
                // R11_LA5: u'' in -32..31, bit 5 a copy of the sign (the cap comes back as in the parent's re-bind)
                self.cap += 1;
                self.la[R_BITS] = b.alloc();
                if !b793b_break("lao1") { b.cx(self.la[LB_BITS - 1], self.la[R_BITS]); }
            }
            // (la6 without la5: LA[5] stays bound as a real bit, u' in -64..25) bits 6, 7 stay unbound
            self.la[R_BITS + 1] = NOQ;
            self.la[R_BITS + 2] = NOQ;
        } else {
        if la_cut {
            for i in R_BITS..LB_BITS - 1 {
                self.la[i] = b.alloc();
            }
        }
        if la6 {
            if la5 { self.cap += 1; }
            for i in la6_lo..LB_BITS - 1 {
                self.la[i] = b.alloc();
                b.cx(self.la[LB_BITS - 1], self.la[i]);
            }
        }
        if la_sign {
            for i in R_BITS..LB_BITS - 1 {
                b.cx(self.la[LB_BITS - 1], self.la[i]);
            }
        }
        if masked_rows {
            add_const_sm(b, self, &self.la, UOFF - la5c, false);
        }
        }
        zero_probe(b, &host);
        // R4-SITES R4_LBLATE (cap < 573, SYFOLD): the length restore LB = ~(kt + LA + !sY) runs on LB's low hl lanes only
        // (hl = max(5, bit length of lb.1)): mod 2^hl the low bits are exact, and the restored LB lies in the slot's
        // window (or is 0 / 1 on a finished shot), so its bits hl..lb_top are 0 and those lanes are bound fresh only
        // after the denormalisation has freed sX and sY. Envelope-based (the window), as DEC_NARROW.
        let hl = ((usize::BITS - w.lb.1.max(1).leading_zeros()) as usize).max(R_BITS);
        // R10_LB8 (claude-r8): a window lb.0 ..= 256 (lb.0 >= 129) on a slot with no finished shot: LB is restored mod 2^8
        // and its bit 8 (1 only at LB = 256, the one window value whose low byte is 0) is bound after the
        // denormalisation as [LB mod 2^8 == 0]; envelope-based exactly as R4_LBLATE
        // R10_LB7 (claude-r8, 797): the same window, LB restored mod 2^7: below 256 the low 7 bits are LB - 128 >= 1, at 256
        // they are 0, so bit 8 = [LB mod 2^7 == 0] and bit 7 = !bit 8, both bound after the denormalisation
        let lb7z = w.lb.1 == 256 && w.lb.0 >= 129 && w.act_const && hl == LB_BITS && free_mode && lb_host() && !lb_sign_clear
            && i5_syfold() && sy.len() == 1 && lb_top == LB_BITS && r3_flag("R4_LBLATE")
            && r10_on("R10_LB7", self.room(b), lb_top - R_BITS - 1);
        let lb8z = lb7z || w.lb.1 == 256 && w.lb.0 >= 129 && w.act_const && hl == LB_BITS && free_mode && lb_host() && !lb_sign_clear
            && i5_syfold() && sy.len() == 1 && lb_top == LB_BITS && r3_flag("R4_LBLATE")
            && r10_on("R10_LB8", self.room(b), lb_top - R_BITS);
        // R10_LBT (claude-r8): the same for a window lb.0 ..= lb.1 with top bit tb (2^tb <= lb.1 < 2^(tb+1)) whose width
        // is below 2^tb, on a slot with no finished shot: LB is restored mod 2^tb and bit tb is bound after the
        // denormalisation as 1 (lb.0 >= 2^tb) or as [LB mod 2^tb < lb.0] (the window crosses 2^tb: below it the low
        // part is >= lb.0, above it <= lb.1 - 2^tb < lb.0); bits above tb are 0 there (R4_LBLATE)
        let tb = (usize::BITS - w.lb.1.max(1).leading_zeros()) as usize - 1;
        let lbt = !lb8z && tb > R_BITS && tb < LB_BITS && w.lb.1 - w.lb.0 < (1 << tb) && w.act_const && free_mode && lb_host()
            && !lb_sign_clear && i5_syfold() && sy.len() == 1 && r3_flag("R4_LBLATE")
            && r10_on("R10_LBT", self.room(b), lb_top - R_BITS - (lb_top - hl.min(lb_top)));
        let hl = if lb7z { LB_BITS - 2 } else if lb8z { LB_BITS - 1 } else if lbt { tb } else { hl };
        // R13_LBK (opus-q796): the R10_LBT form at the smallest k >= R_BITS with window width below 2^k: LB is restored
        // mod 2^k and bits k..lb_top are bound after the denormalisation from the window: LB = lb.0 + ((LB mod 2^k -
        // lb.0) mod 2^k), so its high part is lb.0 >> k where LB mod 2^k >= lb.0 mod 2^k, else lb.1 >> k; each high bit
        // is a constant or [LB mod 2^k >= lb.0 mod 2^k] (or its complement). Envelope-based exactly as R10_LBT.
        let lbk_k = (R_BITS..LB_BITS).find(|&k| w.lb.1 - w.lb.0 < (1 << k)).unwrap_or(LB_BITS);
        let lbk = lbk_k < hl && lbk_k < lb_top && w.act_const && free_mode && lb_host() && !lb_sign_clear
            && i5_syfold() && sy.len() == 1 && r3_flag("R4_LBLATE") && r10_on("R13_LBK", self.room(b), hl - R_BITS);
        if cfg!(test) && lbk && r3_flag("R13_DBG") { eprintln!("R13LBK fire slot {} k {lbk_k} lb {:?}", p3_cur_slot(), w.lb); }
        let hl = if lbk { lbk_k } else { hl };
        // R13_LBR (opus-q796): no envelope. The fold left LB = kt with LB[5..9) |0> on every shot (zero-probed and freed
        // above), so kt in 0..31, sX in 0..31, sY in {0, 1} and r = sX - sY - kt = LB - LA lies in [-32, 31]. Before the
        // denormalisation r is formed mod 2^6 on LB[0..6) from kt, sX and sY (the SYFOLD inverse with sX in place of LA);
        // after it (LA plain again) r is sign-extended and LA added: LB = LA + r mod 2^m, m = 9, or R8's hb where
        // LB, LA < 2^hb. LB[6..9) stay unbound across the denormalisation.
        let lbr = !lbk && hl > R_BITS + 1 && lb_top == LB_BITS && free_mode && lb_host() && !lb_sign_clear
            && i5_syfold() && sy.len() == 1 && r3_flag("R4_LBLATE") && r8_lhf_hb(self, w).map_or(true, |hb| hb > R_BITS)
            && r10_on("R13_LBR", self.room(b), hl - R_BITS);
        if cfg!(test) && lbr && r3_flag("R13_DBG") { eprintln!("R13LBR fire slot {} lb {:?}", p3_cur_slot(), w.lb); }
        let hl = if lbr { R_BITS + 1 } else { hl };
        let lb_late: Vec<usize> = if lbr { (R_BITS + 1..LB_BITS).collect() } else if lbk { (lbk_k..lb_top).collect() } else if lb7z { vec![LB_BITS - 2, LB_BITS - 1] } else if lb8z { vec![LB_BITS - 1] } else if lbt { (tb..lb_top).collect() } else if (below805(self.cap) || r3_flag("R4_LBLATE_ANYCAP")) && r3_flag("R4_LBLATE") && free_mode && lb_host() && !lb_sign_clear
            && i5_syfold() && sy.len() == 1 && hl < lb_top { (hl..lb_top).collect() } else { vec![] };
        if r10("R10_DBG") == 2 && free_mode {
            eprintln!("R10LB slot {} hl {hl} lb_top {lb_top} lb {:?} lb_late {:?} room {} sy {} sy_len {sy_len} sign_clear {} r {:?} a1 {:?}", p3_cur_slot(), w.lb, lb_late, self.room(b), sy.len(), lb_sign_clear as u8, r, a1);
        }
        // R9_LA: LA[8] (|0>, see r9_la) leaves before the LB re-bind; bound again after the denorm frees sX, sY
        let r9la_k = if r9_la_break() { LB_BITS - 2 } else { LB_BITS - 1 };
        let r9la = r9_la() && lbr && (!la7_pend || b792_slden()) && lb_late.contains(&(LB_BITS - 1)) && !r8_m8() && r8_hb() >= R8_TOP
            && !(masked_rows && r3_flag("R9_LA_NOMASK")) && self.la[r9la_k] != NOQ && !b.is_free(self.la[r9la_k])
            && std::env::var("R9_LA_SLOTS").ok().and_then(|v| { let (a, c) = v.split_once('-')?; Some((a.parse::<usize>().ok()?, c.parse::<usize>().ok()?)) })
                .map_or(true, |(a, c)| (a..=c).contains(&p3_cur_slot()));
        // on masked-row slots LA = u = LA + sX may reach 256 (short divisor cofactors): LA -= sX runs here instead (it
        // commutes with the R13_LBR restore, which reads sX and sY and writes LB only), leaving the plain LA <= 255
        // negative control `R9_LA_NOEARLY=1`: masked rows free LA[8] of u without the early LA -= sX (must fail)
        let r9la_early = r9la && masked_rows && !r3_flag("R9_LA_NOEARLY");
        if la_off {
            assert!(r9la_early && !la7_pend, "b793 LAOFF: R9_LA's early path does not fire on slot {} (lbr {} r9la {})", p3_cur_slot(), lbr, r9la);
            // LA' = u' - sX on the 7-bit view (lanes 0..6, sign lane as bit 6)
            let d7: Vec<QubitId> = self.la[..=R_BITS].iter().copied().chain([self.la[LB_BITS - 1]]).collect();
            assert!(d7.iter().all(|&q| q != NOQ), "b793 LAOFF: unbound lane in the 7-bit view");
            add_sm(b, self, &d7, &sx, false, true);
        } else if r9la_early { add_sm(b, self, &self.la, &sx, false, true); }
        if la_off {
            // the sign lane stays bound (bit 6); the cap is not lowered (the lane is live, as in the parent before its free)
        } else if r9la {
            if !r9_la_break() { zero_probe(b, &[self.la[r9la_k]]); }
            b.free(self.la[r9la_k]);
            self.la[r9la_k] = NOQ;
            self.cap -= 1;
            if std::env::var_os("R9_DBG").is_some() { eprintln!("R9LA fire slot {} masked {} k {r9la_k}", p3_cur_slot(), masked_rows as u8); }
        }
        if free_mode {
            // re-bind fresh |0> lanes for the freed ones
            if lb_host() {
                for i in R_BITS..lb_top {
                    if lb_late.contains(&i) { continue; }
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
        r6t(b, "ur.mid", self.room(b));
        // R11_LA7: the deferral holds only where the SYFOLD inverse runs on at most 7 lanes; else LA[7] is bound here
        if la7_pend && !(i5_syfold() && sy.len() == 1 && !lb_late.is_empty() && hl <= LB_BITS - 2) {
            self.la[LB_BITS - 2] = b.alloc();
            self.cap += 1;
            la7_pend = false;
            slden_la7 = false;
        }
        // losgahts A: the lanes the late sY subtraction runs on (R13_LBR's r, or the SYFOLD inverse's view)
        let la94_n = if lbr { R_BITS + 1 } else if lb_late.is_empty() { LB_BITS } else { hl };
        assert!(!la94a || lbr || (i5_syfold() && sy.len() == 1), "losgahts: sY out on an unhandled LB restore path");
        // (LB holds the restore without -sY through R8_IDEN's open: its R8_M8 open must stay skipped, LB[8] late)
        assert!(!la94a || lb_late.contains(&(LB_BITS - 1)), "losgahts: sY out with LB[8] bound through the denorm");
        if lbr {
            // R13_LBR: LB[0..6) = ~(kt - sX - !sY) = sX - sY - kt mod 2^6
            let n = R_BITS + 1;
            // negative control for the gate tests only: R4_BREAK=lbrc drops the !sY carry-in (r off by one)
            let brc = r4s_break("lbrc");
            if la94a {
                // losgahts A: sY is out: LB[0..6) = ~(kt - sX - 1) = sX - kt, sY subtracted after the denorm
                if std::env::var_os("R9_DBG").is_some() { eprintln!("LA94F slot {} room {}", p3_cur_slot(), self.room(b)); }
                add_lean(b, self, &self.lb[..n], &sx, true, true, None);
            } else {
            if !brc { b.x(sy[0]); }
            // the carry-out ladder on LB[0..5) toggles LB[5] (no zero pad for the 5-lane sX)
            add_lean(b, self, &self.lb[..n], &sx, false, true, Some(sy[0]));
            if !brc { b.x(sy[0]); }
            }
            for &q in &self.lb[..n] {
                b.x(q);
            }
        } else if i5_syfold() && sy.len() == 1 {
            assert!(B793_ZLATE.with(|c| c.get().is_none()), "b793 ZLATE: the SYFOLD inverse reads LA before its restore (slot {})", p3_cur_slot());
            // SYFOLD inverse: LB = kt - LA - !sY = ~(LB + sY); then ~LB
            let n = if lb_late.is_empty() { LB_BITS } else { hl };
            if la94a {
                // losgahts A: sY is out: LB[..n] = ~(kt - LA - 1) = LA - kt, sY subtracted after the denorm
                assert!(!self.la[..n].iter().any(|&q| q == NOQ), "losgahts: SYFOLD view holds an unbound LA lane");
                add_sm(b, self, &self.lb[..n], &self.la[..n], true, true);
            } else {
            b.x(sy[0]);
            add_on_sm(b, self, &self.lb[..n], &self.la[..n], false, true, sy[0], true);
            b.x(sy[0]);
            }
            for &q in &self.lb[..n] {
                b.x(q);
            }
        } else {
        assert!(B793_ZLATE.with(|c| c.get().is_none()), "b793 ZLATE: the plain LB restore reads LA before its restore (slot {})", p3_cur_slot());
        add_sm(b, self, &self.lb, &self.la, true, true);
        for &q in &self.lb {
            b.x(q);
        }
        add_sm(b, self, &self.lb, &sy, false, true);
        }
        r6t(b, "ur.syf", self.room(b));
        // b793b ZLATE: LA[7] back (fresh |0>, never on a lent id) and c added back, before LA -= sX, the first reader of LA after the undo rows
        if let Some((j, k)) = B793_ZLATE.with(|c| c.take()) {
            assert!(self.la[LB_BITS - 2] == NOQ, "b793 ZLATE: LA[7] bound");
            if b792_slden() && lbr && !la7_pend && !la_off && r8_lhf_hb(self, w).is_none() {
                // b792 SLDEN: LA[7] stays out (offset form) through LA -= sX and the denorm funnel; see the re-bind after sY's free
                SLDEN_PEND.with(|c| c.set(Some((j, k))));
                b792_slc_assert(p3_cur_slot(), k << j);
                if std::env::var_os("B792_SLCK").is_some() { eprintln!("SLCK slot {} j {} k {} c {}", p3_cur_slot(), j, k, k << j); }
                self.cap -= 1;
            } else {
            let mut avoid: Vec<QubitId> = r3h.clone();
            avoid.extend(&lend);
            self.la[LB_BITS - 2] = b.alloc_avoid(&avoid);
            let lv: Vec<QubitId> = self.la[j..LB_BITS - 1].to_vec();
            if !b793b_break("zl1") { la94b_field_add(b, &lv, k, false, &self.dirty); }
            if std::env::var_os("B793_DBG").is_some() { eprintln!("B793FIRE zlate slot {}", p3_cur_slot()); }
            }
        }
        if let Some(_) = SLDEN_PEND.with(|c| c.get()) {
            // b792 SLDEN: LA[0..7) holds u - c; LA - sX = LA_plain - c in 0..127 (mod 2^7 exact: ZLATE's window premise)
            let lv: Vec<QubitId> = self.la[..LB_BITS - 2].to_vec();
            assert!(lv.iter().all(|&q| q != NOQ), "b792 SLDEN: unbound lane in the 7-lane view");
            let mut lv = lv;
            if b792_brk("slden2") { lv.truncate(lv.len() - 1); } // negative control: the view one lane short (mod 2^6)
            add_sm(b, self, &lv, &sx, false, true);
        } else if la7_pend {
            // R11_LA7: LA -= sX on the bound view (bits 0..7 and the marker): u < 128 and u - sX >= 0
            // (b792 SLDEN: LA[8] may be out as well (R9_LA's free ran above): u < 128 and u - sX >= 0, so mod 2^7 is exact)
            let mut lv: Vec<QubitId> = self.la[..LB_BITS - 2].iter().chain(&self.la[LB_BITS - 1..]).copied().filter(|&q| q != NOQ).collect();
            if b792_brk("slden8") && SLDEN8_PEND.with(|c| c.get()) { let n: usize = std::env::var("B792_SLBRK_N").ok().and_then(|v| v.parse().ok()).unwrap_or(2); lv.truncate(lv.len() - n); } // negative control: LA -= sX one lane short
            add_sm(b, self, &lv, &sx, false, true);
        } else if r9la_early {
            // R9_LA (masked rows): LA -= sX already ran before LA[8] was freed
        } else if r9la {
            // R9_LA: LA -= sX on the bound lanes (exact mod 2^8: u and u - sX lie in 0..255)
            let lv: Vec<QubitId> = self.la.iter().copied().filter(|&q| q != NOQ).collect();
            add_sm(b, self, &lv, &sx, false, true);
        } else {
        add_sm(b, self, &self.la, &sx, false, true);
        }
        r6t(b, "ur.lasx", self.room(b));
        prof(b, "i.denorm");
        p3(b, self, "i.denorm");
        r5tl(b, "denorm0");
        // R8-LANE799 R8_IDEN: LA and LB are plain lengths again from here (I6 undone), so the tail's releases start at the
        // denormalisation (R4_LBLATE's lanes among them stay released and are bound at the slot's end)
        if la7_pend && !slden_la7 { self.cap += 1; }
        if r3_flag("R8_IDEN") {
            R8_SKIPLB.with(|c| *c.borrow_mut() = lb_late.clone());
            if la7_pend || SLDEN_PEND.with(|c| c.get()).is_some() { R8_SKIPLA.with(|c| *c.borrow_mut() = vec![LB_BITS - 2]); }
            r8_lhf_open(b, self, w);
            r8_m8_open(b, self, w);
            b792_f8_out(b, self, w);
            R8_SKIPLB.with(|c| c.borrow_mut().clear());
            R8_SKIPLA.with(|c| c.borrow_mut().clear());
        }
        if la7_pend && !slden_la7 && !r8_rel(LB_BITS - 2) {
            // R11_LA7: the open did not release bit 7 after all: bind it now
            self.la[LB_BITS - 2] = b.alloc();
        }
        if slden_la7 { assert!(!r8_rel(LB_BITS - 2), "b792 SLDEN: an R8 open released bit 7 on a held-out slot"); }
        // FUSE-S4: decided here (the erase after the barrel sees this room + sX0..3 + sY freed, s4 freed by EFREE)
        let fuse = fuse_s4() && ns0 && sw_carry() && funnel_rev() && sy.len() == 1
            && self.room(b) + R_BITS - 1 + 1 + 1 >= FUSE_S4_NEED + 1;
        if cfg!(test) && ns0 && sw_carry() && std::env::var_os("M2_LOG").is_some() { eprintln!("M2LOG fuse {}", fuse as u8); }
        if ns0 && sw_carry() {
            // SW-CARRY: X's prep is the funnel alone on carried slots, and on the others the a-shift + funnel, whose lane
            // map and sX are the funnel's (a_X = 1 iff slack 1, where the funnel's stage 0 makes the same shift and
            // sX = 1): both are undone by the funnel's inverse. Y back by its a-shift, sY = [Y slack == 1] erased.
            if !la94a {
            for i in (0..NB).rev() {
                b.cswap(sy[0], self.y[i], self.y[i + 1]);
            }
            self.r9_sy_erase(b, sy[0], y_act, &act_el);
            }
            if x0_def {
                self.x[0] = b.alloc();
                if fx0 { fx0_unpark(b, self.x[0], fx0z, fx0s4, fx0_rel, "p12def"); }
                if !b792_break("p12x") { b.x(self.x[0]); }
            }
            if fuse {
                rev_funnel_k(b, self, &self.x, &sx, None, false, true);
            } else {
                denorm_bottom(b, self, &self.x, &sx, None);
            }
        } else if ns0 {
            // NORM-STAGE0 inverse: Y back by its a-shift (sY <= 1), sY = [Y slack == 1] erased; a_X = [sX == 1] back
            // into its own lane, the funnel undone on the funnel bits, X back by its a-shift, a_X = [X slack == 1] erased
            if !la94a {
            for i in (0..NB).rev() {
                b.cswap(sy[0], self.y[i], self.y[i + 1]);
            }
            self.r9_sy_erase(b, sy[0], y_act, &act_el);
            }
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
            assert!(!la94a);
            denorm_bottom(b, self, &self.y, &sy, y_act);
            denorm_bottom(b, self, &self.x, &sx, None);
        }
        let s4 = if fuse { Some(sx[R_BITS - 1]) } else { None };
        b.free_n(&sx[..if fuse { R_BITS - 1 } else { R_BITS }]);
        if la94a {
            // losgahts A: the cap back where the parent frees sY; LB[..n] -= sY from a fresh lane holding sY's predicate
            // (Y untouched since its denorm), which is then erased as sY was
            self.cap += 1;
            let p = b.alloc();
            self.la94_sy_pred(b, p, y_act, &act_el);
            if !r14_break("psub") { add_sm(b, self, &self.lb[..la94_n], &[p], false, true); }
            self.r9_sy_erase(b, p, y_act, &act_el);
            b.free(p);
        } else {
        b.free_n(&sy);
        }
        if slden_la7 {
            // b792 SLDEN: LA[7] = |0> (u < 128, R8_LAMX) bound after the funnel, sX and sY free; the cap comes back
            assert!(self.la[LB_BITS - 2] == NOQ, "b792 SLDEN: LA[7] bound");
            let mut avoid: Vec<QubitId> = r3h.clone();
            avoid.extend(&lend);
            self.la[LB_BITS - 2] = b.alloc_avoid(&avoid);
            self.cap += 1;
        }
        if SLDEN8_PEND.with(|c| c.replace(false)) {
            assert!(self.la[LB_BITS - 1] == NOQ, "b792 SLDEN8: LA[8] bound early");
            self.la[LB_BITS - 1] = b.alloc();
        }
        if let Some((j, k)) = SLDEN_PEND.with(|c| c.take()) {
            // b792 SLDEN: sX and sY are free: LA[7] back (fresh |0>, never on a lent id), then c added back (LA_plain = (LA_plain - c) + c)
            assert!(self.la[LB_BITS - 2] == NOQ, "b792 SLDEN: LA[7] bound");
            let mut avoid: Vec<QubitId> = r3h.clone();
            avoid.extend(&lend);
            self.la[LB_BITS - 2] = b.alloc_avoid(&avoid);
            self.cap += 1;
            let lv: Vec<QubitId> = self.la[j..LB_BITS - 1].to_vec();
            if !b792_brk("slden1") { la94b_field_add(b, &lv, k, false, &self.dirty); }
        }
        if la_off {
            // b793b LAOFF: LA = LA' + UOFF mod 2^8: bit 7 = a copy of the sign, bit 6 = the sign lane; then LA[8] is bound fresh
            let sgn = self.la[LB_BITS - 1];
            self.la[R_BITS + 1] = sgn;
            self.la[LB_BITS - 1] = NOQ;
            self.la[R_BITS + 2] = b.alloc();
            if !b793b_break("lao2") { b.cx(sgn, self.la[R_BITS + 2]); }
            add_const_sm(b, self, &self.la[..LB_BITS - 1], UOFF - la5c - b793b_break("lao3") as usize, false);
            if !(b792_late() && w.slot >= 1) { self.la[r9la_k] = b.alloc(); }
        } else if r9la {
            // R9_LA: LA[8] back as a fresh |0> lane (sX and sY are free now), the cap restored
            self.la[r9la_k] = b.alloc();
            self.cap += 1;
        }
        if lbr {
            // R13_LBR: bind LB[6..m) (R8-released lanes stay unbound, |0> as LB < 2^hb), sign-extend r, add LA
            assert!(!r8_m8() && r8_hb() > R_BITS, "R13_LBR: bit 8 shared or bit 5 released");
            // m = 9 with R8 closed (LA[8] is LA's bit 8 here, LB = 256 possible on the first slots), else R8's hb
            let m = if r8_hb() >= R8_TOP { LB_BITS } else { r8_hb() };
            for i in R_BITS + 1..LB_BITS {
                if r8_rel(i) { continue; }
                self.lb[i] = b.alloc();
                // negative control for the gate tests only: R4_BREAK=lbrs drops the sign extension
                if i < m && !r4s_break("lbrs") { b.cx(self.lb[R_BITS], self.lb[i]); }
            }
            // negative control for the gate tests only: R4_BREAK=lbr flips LB[0]
            if r4s_break("lbr") { b.x(self.lb[0]); }
            let lt: Vec<QubitId> = self.lb[..m].to_vec();
            if b792_late() && m == LB_BITS && self.la[LB_BITS - 1] == NOQ && lt[LB_BITS - 1] != NOQ {
                // B792_LATE: LA[8] (= 0, deferred) is not bound: LB += LA as an 8-bit add plus the carry into LB[8], carry = [new LB[..8] < LA[..8]]
                // on borrowed dirty lanes (lt_into_dirty), no pad lane and no LA[8] lane
                let l8: Vec<QubitId> = lt[..LB_BITS - 1].to_vec();
                let a8: Vec<QubitId> = self.la[..LB_BITS - 1].to_vec();
                add_sm(b, self, &l8, &a8, false, false);
                if !b792_brk("latec") { lt_into_dirty(b, &l8, &a8, lt[LB_BITS - 1], &self.dirty); }
            } else {
            let ls: Vec<QubitId> = self.la[..m].to_vec();
            add_sm(b, self, &lt, &ls, false, false);
            }
        }
        // R13_LBK: one shared flag lane (the first varying high bit) carries [LB mod 2^k >= lb.0 mod 2^k]
        let mut lbk_f: Option<(QubitId, bool)> = None;
        for &i in &lb_late {
            if lbr { break; }
            if lbk {
                let j = i - lbk_k;
                let (b0, b1) = ((w.lb.0 >> lbk_k >> j) & 1 == 1, (w.lb.1 >> lbk_k >> j) & 1 == 1);
                if r8_rel(i) { assert!(!b0 && !b1, "R13_LBK: set bit released"); continue; }
                let q = b.alloc();
                self.lb[i] = q;
                if b0 != b1 {
                    // bit = b0 where the low part >= lb.0 mod 2^k, else b1 (= !b0)
                    match lbk_f {
                        None => {
                            let low: Vec<QubitId> = self.lb[..lbk_k].to_vec();
                            super::mask::ge_const_dirty(b, &low, (w.lb.0 & ((1 << lbk_k) - 1)) as isize, q, &self.dirty);
                            if !b0 { b.x(q); }
                            // negative control for the gate tests only: R4_BREAK=lbkf inverts the window flag
                            if r4s_break("lbkf") { b.x(q); }
                            lbk_f = Some((q, b0));
                        }
                        Some((f, fb0)) => {
                            b.cx(f, q);
                            if fb0 != b0 { b.x(q); }
                        }
                    }
                } else if b0 {
                    b.x(q);
                }
                if r4s_break("lbk") { b.x(q); }
                continue;
            }
            if lb7z {
                assert!(!r8_rel(LB_BITS - 2) && !r8_rel(LB_BITS - 1), "R10_LB7: released bit");
                if i == LB_BITS - 2 { continue; }
                let (q7, q8) = (b.alloc(), b.alloc());
                self.lb[LB_BITS - 2] = q7;
                self.lb[LB_BITS - 1] = q8;
                let lits: Vec<(QubitId, bool)> = self.lb[..LB_BITS - 2].iter().map(|&q| (q, true)).collect();
                and_auto(b, self, &lits, q8);
                b.cx(q8, q7);
                b.x(q7);
                continue;
            }
            if r8_rel(i) { assert!(!(lbt && i == tb), "R10_LBT: top bit released"); continue; } // R8_IDEN: bound at the slot's end
            self.lb[i] = b.alloc();
            if lb8z {
                let lits: Vec<(QubitId, bool)> = self.lb[..LB_BITS - 1].iter().map(|&q| (q, true)).collect();
                and_auto(b, self, &lits, self.lb[i]);
            }
            if lbt && i == tb {
                if w.lb.0 >= 1 << tb {
                    b.x(self.lb[i]);
                } else {
                    let low: Vec<QubitId> = self.lb[..tb].to_vec();
                    super::mask::ge_const_dirty(b, &low, w.lb.0 as isize, self.lb[i], &self.dirty);
                    b.x(self.lb[i]);
                }
            }
            // negative control for the gate tests only: R4_BREAK=lbl binds LB's late lane as |1>
            if r4s_break("lbl") { b.x(self.lb[i]); }
        }
        prof(b, "i.unrenorm");
        p3(b, self, "i.unrenorm");
        // R8-LANE799 R8_ITAIL: the inverse slot's tail (I7..I15) is the forward's F1..F8 mirror on plain lengths
        // (LA <= lad.1 + 1, LB <= lb.1 from here to the slot's end), so R8_LHF / R8_M8 release the same lanes there
        let r8t = r3_flag("R8_ITAIL");
        if r8t {
            r8_lhf_open(b, self, w);
            // negative control for the gate tests only: R8_BREAK=itail shares bit 8 on slot 0 too (LA = 256 there)
            if r8_break("itail") && w.slot == 0 && r3_flag("R8_M8") {
                let mut w0 = w.clone();
                w0.slot = 1;
                r8_m8_open(b, self, &w0);
                b792_f8_out(b, self, &w0);
            } else {
                r8_m8_open(b, self, w);
                b792_f8_out(b, self, w);
            }
        }
        // I7, I8, I9
        add_sm(b, self, &self.la[..len_n(w)], &r, false, false);
        if let Some((a1q, rq)) = act_el.take() {
            // R9 rowtmp c: act comes back here, the cap with it
            // dev switch R9_RT_FORCEFB=1 (inert unless set): take the fail-closed arm on every elided slot (its check)
            if s4.is_none() && i5_rcnt() && std::env::var_os("R9_RT_FORCEFB").is_none() {
                let t = unrenorm_rcnt_el(b, self, &r, gate_spec(&self.la, w), a1q);
                if !i5_rfree() { b.free_n(&r); }
                if !B793_ACTCAP.with(|c| c.replace(false)) { self.cap += 1; }
                r9_p2_shift(true);
                act = Some(t);
            } else {
                // fail closed: act re-formed on a fresh lane while rho is intact, then the parent's form
                if !B793_ACTCAP.with(|c| c.replace(false)) { self.cap += 1; }
                r9_p2_shift(true);
                let q = b.alloc();
                let mut l: Vec<(QubitId, bool)> = vec![(a1q, true)];
                l.extend(rq.iter().map(|&x| (x, true)));
                and_auto(b, self, &l, q);
                b.x(q);
                act = Some(q);
                if !unrenorm_top_s4f(b, self, act, &r, gate_spec(&self.la, w), s4) {
                    b.free_n(&r);
                }
            }
            z0 = act;
            y_act = if sy_act_gate() { act } else { None };
            let _ = y_act;
        } else if !unrenorm_top_s4f(b, self, act, &r, gate_spec(&self.la, w), s4) {
            b.free_n(&r);
        }
        prof(b, "i.value");
        p3(b, self, "i.value");
        // I10: value add-back where a1; d = a1 & the chain's carry out of lane W-1
        let mwa = masked_write_always();
        mark_done_inv(b, act, &self.lb);
        if mwa { mark_stall(b, act, a1, &self.lb); }
        let d = b.alloc();
        let pk = act.and_then(|a| act_park(b, a, &self.lb, w.lb));
        // R9-DONE (I10): done = !a1 & [LA[..ln] == 0] (LA = LA_pre - d; a stall has d = 0 and LA_pre >= 1, a step a1 = 1)
        let iln = len_n(w);
        let r9 = act.is_some() && r9_done_slot(self, w, iln);
        let r9v = r9 && pk.is_none() && r9_site(8);
        let i10l = || { let mut l = vec![(a1, true)]; l.extend(r9_zero_lits(&self.la[..iln])); l };
        if r9v { let a = act.unwrap(); r9_dbg(w, "I10", a, &i10l()); b.x(a); r9_erase(b, self, a, &i10l(), 8); }
        if let Some(yt) = m94y.take() {
            assert!(self.y[W - 1] == NOQ, "R14 misc94 y: Y[W-1] re-bound early");
            self.y[W - 1] = b.alloc();
            if yt && !r14m_break("y") { b.x(self.y[W - 1]); }
        }
        value_pass(b, self, w, false, a1, Some(d), mwa, Some(&bits.rv));
        if r9v { let a = r9_rebuild(b, &i10l(), 8); b.x(a); act = Some(a); z0 = act; }
        if let Some(a) = act { act_unpark(b, a, &self.lb, pk); }
        if mwa { mark_stall(b, act, a1, &self.lb); }
        mark_done_inv(b, act, &self.lb);
        b.z_if(d, bits.d);
        prof(b, "i.cof");
        p3(b, self, "i.cof");
        // I11: cofactor undo (LA = LA_pre - d here)
        // YTOP-COF: Y[W-1] (= 1) is a free |0> lane across the cofactor undo where its ladder stays below it
        let ytc = ytop_cof() && host_free() && w.lad.0 >= 1;
        if ytc {
            if !m2_break(11) { b.x(self.y[W - 1]); }
            zero_probe(b, &[self.y[W - 1]]);
            b.free(self.y[W - 1]);
        }
        mark_done_inv(b, act, &self.la);
        if mwa { mark_stall(b, act, a1, &self.la); }
        let pk = act.and_then(|a| act_park(b, a, &self.la, w.lad));
        // R9-DONE (I11): done-marked LA_pre - d reads all ones on LA[..ln] exactly where the shot is finished
        let r9c = r9 && pk.is_none() && r9_site(16) && r9_cof_ok(w, iln);
        if r9c { let a = act.unwrap(); r9_dbg(w, "I11", a, &r9_one_lits(&self.la[..iln])); b.x(a); r9_erase(b, self, a, &r9_one_lits(&self.la[..iln]), 16); }
        if lane0_direct() {
            // x0 = X[0] ^ d here (X[0] holds A's MSB = 1 where d = 1), in place
            let cv = r4_cview(self, w, w.lad);
            r4_cv_open(b, self, w, &self.la, w.lad);
            let off = r4_idle_spec(b, self, w, &self.lb, w.lb.0, w.lb.1, r4_need(cv, w.lad.1), P2_COF_EXTRA);
            let m = r4_alloc_ladder(b, w.lad.1, cv);
            p2_host_clear();
            b.cx(d, self.x[0]);
            let (t, s) = cof_ladder(self, w, self.x[0]);
            let src = cof_src(self, &m, w);
            let pool = pool_for(b, self, t.len() - (w.lad.1 - w.lad.0 + 1), 0);
            masked_pass(b, self, &t, &s, src, &m, true, Some(a1), None, &pool, mwa, w.a1_const, Some(&bits.rc));
            b.free_n(&pool);
            b.cx(d, self.x[0]);
            m.free(b);
            r4_idle_close(b, self, &self.lb, off);
            r4_cv_close(b, self, w, &self.la, w.lad);
        } else {
            let cv = r4_cview(self, w, w.lad);
            r4_cv_open(b, self, w, &self.la, w.lad);
            let off = r4_idle_spec(b, self, w, &self.lb, w.lb.0, w.lb.1, r4_need(cv, w.lad.1), P2_COF_EXTRA);
            let m = r4_alloc_ladder(b, w.lad.1, cv);
            p2_host_clear();
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
            r4_idle_close(b, self, &self.lb, off);
            r4_cv_close(b, self, w, &self.la, w.lad);
        }
        if r9c { let a = r9_rebuild(b, &r9_one_lits(&self.la[..iln]), 16); b.x(a); act = Some(a); z0 = act; }
        if let Some(a) = act { act_unpark(b, a, &self.la, pk); }
        if mwa { mark_stall(b, act, a1, &self.la); }
        mark_done_inv(b, act, &self.la);
        if ytc {
            self.y[W - 1] = b.alloc();
            b.x(self.y[W - 1]);
        }
        prof(b, "i.dundo");
        p3(b, self, "i.dundo");
        // R14 misc94 d (see below): the slots whose LB window top sets the top live bit (R9-DONE mode 1's structural
        // criterion: no length lane is constant over the window, so the d erase's compare ladder gets no register host)
        let m94d = r14m('d') && !term(w) && act.is_some() && m94_dundo_slot(self, w);
        let m94l: Vec<(QubitId, bool)> = if m94d { r9_zero_lits(&self.la[..len_n(w)]) } else { vec![] };
        // I12, I13, I14 (TERM-LAST: d = 0 on every passing shot of the last slot: nothing to undo, d is |0>)
        if !term(w) {
            {
                let ln = len_n(w);
                if r10_on("R10_DEC", self.room(b), ln - 1) {
                    // R10_DEC (claude-r8): the increment on borrowed lanes where the room is short (exact)
                    inc_dirty(b, d, &self.la[..ln], &self.dirty);
                } else {
                let anc = b.alloc_n(ln - 1);
                super::arith::inc(b, d, &self.la[..ln], &anc);
                b.free_n(&anc);
                }
            }
            crot_down(b, d, &self.x, 1);
            mark_msb(b, a1, &self.lb);
            if below805(self.cap) && r3_flag("R6_LBV") && w.lb.0 < wc() {
                let h = ((usize::BITS - w.lb.1.max(1).leading_zeros()) as usize).max(5);
                if h < LB_BITS - 1 {
                    if r6_break("lbv") { b.x(self.lb[h]); }
                    let pl: Vec<QubitId> = (h..LB_BITS - 1).filter(|&j| !r8_rel(j)).map(|j| self.lb[j]).collect();
                    zero_probe(b, &pl);
                }
            }
            // R14 misc94 "DonRwetter" d: act is idle across the d erase (top_compare is not passed it) and is a function
            // of LA there: after I12's LA += d, LA is the slot's pre-state LA_pre, and the done flag is [LA[..ln] == 0],
            // the predicate the parent's own I15 erase uses on the same LA (nothing between here and I15 writes LA). So
            // the flag is erased by measurement before the compare and rebuilt on a fresh lane after d is released.
            if m94d {
                let a = act.unwrap();
                r9_dbg(w, "M94D", a, &m94l);
                b.x(a);
                if r14m_break("d") { erase_mbu(b, a, |_b| {}); } else { erase_and(b, self, a, &m94l); }
                b.free(a);
            }
            erase_mbu(b, d, |b| top_compare(b, self, None, w, Some((a1, false))));
            mark_msb(b, a1, &self.lb);
        }
        b.free(d);
        if m94d {
            let q = b.alloc();
            if r14m_break("d2") { and_into(b, &m94l[1..], q); } else { and_into(b, &m94l, q); }
            b.x(q);
            act = Some(q);
            z0 = act;
        }
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
            let zl: Vec<(QubitId, bool)> = self.la[..len_n(w)].iter().map(|&q| (q, true)).collect();
            erase_and(b, self, z0, &zl);
            b.free(z0);
        }
        if r8t || r3_flag("R8_IDEN") {
            r8_m8_close(b, self);
            r8_lhf_close(b, self);
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
    // R8_LHF: the zero bits are released lanes; act keeps its own lane
    if i >= r8_hb() { return None; }
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

// ------------------------------------------------------------------ R9-DONE (r9 closure "done", dev knob)
/// R9-DONE (dev knob `R9_DONE`; unset / 0 = off = the parent, byte for byte): the done flag (forward zo / act, the
/// inverse's act) does not keep its own lane across the ladders it does not read: the forward's F2 / F3 (top compare),
/// the value ladders (F4 / I10) and the cofactor ladders (F5 / I11). At each of those points it is a function of live
/// registers, so it is erased by measurement (`erase_and`: X-measure, the CZ-chain repair at half weight) before the
/// ladder and rebuilt on a fresh lane after it (an AND chain):
/// - forward F1 .. F4: LA is the F1 value until F5's LA -= d, so zo = [LA[..ln] == 0], the F1 test itself. Exact on
///   every shot.
/// - forward F5 / inverse I11 (LA = LA_pre - d, done-marked on its live bits): a finished shot reads LA[..ln] all ones;
///   an active shot's LA - d stays below 2^ln - 1 (`r9_cof_ok`), so it does not: done = AND(LA[..ln]).
/// - inverse I10 (LA = LA_pre - d, d is rebuilt only inside the value ladder): a finished shot has LA = 0 and a1 = 0,
///   a step has a1 = 1, a stall has a1 = d = 0 and LA = LA_pre >= 1: done = !a1 & [LA[..ln] == 0]. Exact on every
///   shot (the parent's own zero test plus its decoded a1).
/// The F5 / I11 test is envelope-based like DEC_NARROW's decoder and R8_LHF: it needs every active shot's LA there
/// below 2^ln - 1, which `r9_cof_ok` checks against the window table (steps and stalls). R9_DONE=2: every slot with a done flag; R9_DONE=1: only slots whose LB window top sets the
/// top live bit ln - 1 (no register lane is constant over the window, so the ladders get no register host, the
/// late-band binder of the cap-795 traversal).
fn r9_done_mode() -> u32 {
    static E: std::sync::LazyLock<u32> = std::sync::LazyLock::new(|| std::env::var("R9_DONE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(0));
    *E
}
fn r9_done_slot(u: &GreedyFrog, w: &Win, ln: usize) -> bool {
    let mode = r9_done_mode();
    if mode == 0 || ln < 3 || ln > LB_BITS - 1 { return false; }
    if u.la[..ln].iter().any(|&q| q == NOQ) { return false; }
    mode == 2 || w.lb.1 >= 1 << (ln - 1)
}
/// R9-DONE premise of the cofactor-pass test (F5 / I11): no active shot has LA[..ln] all ones there. Steps have
/// LA - d <= lad.1 (TERM-LAST: LA <= lad.1 + 1); a stall k slots after its step at s - k has LA <= lad.1(s - k) - 7k
/// (the step and every earlier stall renormalised by RCAP = 7; MARKER_FREE's la_hb bound, kept as a value)
fn r9_cof_ok(w: &Win, ln: usize) -> bool {
    static E: std::sync::LazyLock<Vec<isize>> = std::sync::LazyLock::new(|| {
        let ws = windows();
        (0..ws.len()).map(|s| (1..=s).fold(ws[s].lad.1 as isize + 1, |m, k| m.max(ws[s - k].lad.1 as isize - 7 * k as isize))).collect()
    });
    E.get(w.slot).map_or(false, |&m| m < (1isize << ln) - 1)
}
/// R9-DONE dev print (R9_DBG=1): slot, site, flag lane and literal lanes (no gates); the flag must not be a literal
fn r9_dbg(w: &Win, site: &str, t: QubitId, lits: &[(QubitId, bool)]) {
    assert!(lits.iter().all(|&(q, _)| q != t && q != NOQ), "R9-DONE: flag lane among its literals");
    if std::env::var_os("R9_DBG").is_some() {
        eprintln!("R9 slot {} site {site} lb {:?} lad {:?} n {} lits {:?}", w.slot, w.lb, w.lad, lits.len(), lits.iter().map(|l| l.0 .0).collect::<Vec<_>>());
    }
}
fn r9_zero_lits(v: &[QubitId]) -> Vec<(QubitId, bool)> { v.iter().map(|&q| (q, true)).collect() }
/// R14 misc94 d slot set: 3 <= ln <= 8, LA[..ln] bound, and the LB window's top sets the top live bit ln - 1 (R9-DONE
/// mode 1's criterion, without its knob). Structural (window table), never room-driven.
fn m94_dundo_slot(u: &GreedyFrog, w: &Win) -> bool {
    let ln = len_n(w);
    if ln < 3 || ln > LB_BITS - 1 { return false; }
    if u.la[..ln].iter().any(|&q| q == NOQ) { return false; }
    w.lb.1 >= 1 << (ln - 1)
}
fn r9_one_lits(v: &[QubitId]) -> Vec<(QubitId, bool)> { v.iter().map(|&q| (q, false)).collect() }
/// R9-DONE dev mask `R9_SITES` (default 31 = all): 1 F1 -> F4 (top compare), 2 F4 (value ladder), 4 F5 (cofactor
/// ladder), 8 I10 (inverse value ladder), 16 I11 (inverse cofactor ladder)
fn r9_site(k: u32) -> bool {
    static E: std::sync::LazyLock<u32> = std::sync::LazyLock::new(|| std::env::var("R9_SITES").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(31));
    *E & k != 0
}
/// R9-DONE negative controls (dev only): `R9_BREAK` = erase (drop the repair) / lit (repair without the lowest
/// literal) / low2 (repair on the two lowest literals only) / rebuild (rebuild without the lowest literal) / rebuild2
/// (rebuild on the two lowest literals only), at the sites of the mask `R9_BRKSITE` (default all)
fn r9_brk(site: u32) -> Option<String> {
    if !cfg!(test) { return None; }
    let m: u32 = std::env::var("R9_BRKSITE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(31);
    std::env::var("R9_BREAK").ok().filter(|_| m & site != 0)
}
/// R9-DONE: t holds AND(lits): erased by measurement and released
fn r9_erase(b: &mut B, u: &GreedyFrog, t: QubitId, lits: &[(QubitId, bool)], site: u32) {
    let brk = r9_brk(site);
    match brk.as_deref() {
        Some("erase") => erase_mbu(b, t, |_b| {}),
        Some("lit") => erase_and(b, u, t, &lits[1..]),
        Some("low2") => erase_and(b, u, t, &lits[..2]),
        _ => erase_and(b, u, t, lits),
    }
    b.free(t);
}
/// R9-DONE: a fresh lane holding AND(lits)
#[track_caller]
fn r9_rebuild(b: &mut B, lits: &[(QubitId, bool)], site: u32) -> QubitId {
    let t = b.alloc();
    match r9_brk(site).as_deref() {
        Some("rebuild") => and_into(b, &lits[1..], t),
        Some("rebuild2") => and_into(b, &lits[..2], t),
        _ => and_into(b, lits, t),
    }
    t
}

/// While z0 holds act (= !done), XOR !act into the counter: finished shots read all ones.
fn mark_done_inv(b: &mut B, act: Option<QubitId>, v: &[QubitId]) {
    let Some(act) = act else { return };
    b.x(act);
    for &q in &r8_live(v) {
        b.cx(act, q);
    }
    b.x(act);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::Simulator;

    /// R15-JC local check (S4): `sweep_fwd_jc` against an independent classical reference, jl = the largest row
    /// j in [1, min(kt, k - 1)] whose rem lane y[j - 1] is 0 (active), 0 otherwise and on finished shots; every other
    /// lane (kt, y, the gate lane f, the borrowed lanes in random states) unchanged; no phase. Forced states put the
    /// first zero lane at every row (j = 16 included) for every kt and both gate values. R15_UNIT=1 to run;
    /// R15_BREAK=3116 / gate must fail it.
    #[test]
    fn r15_jc_sweep_unit() {
        if std::env::var_os("R15_UNIT").is_none() { return; }
        use sha3::digest::{ExtendableOutput, Update};
        let mut rng = Rng(0x5eed_1234_9876_abcd);
        let mut fails = 0u64;
        let mut cases = 0u64;
        for &k in &[2usize, 3, 8, 16, 17, 18, 21, 22, 27, 31] {
            for &gated in &[false, true] {
                let mut b = B::new();
                let mut u = GreedyFrog::alloc(&mut b);
                u.cap = 1 << 30;
                let f = b.alloc();
                let jl = b.alloc_n(R_BITS);
                let rt = RowTmp { s0: NOQ, g: NOQ, f, y: NOQ, jl: jl.clone(), m: None };
                let mut w = windows()[0].clone();
                w.k = k;
                let gate: Vec<(QubitId, bool)> = if gated { vec![(f, true)] } else { vec![] };
                sweep_fwd_jc(&mut b, &u, &gate, &w, &rt);
                // 64-shot batches: shot (kt, zero row z, act) forced, the rest of the y lanes random
                let mut shots: Vec<(usize, usize, bool)> = vec![];
                for kt in 0..32 { for z in 0..=k { for a in [false, true] { shots.push((kt, z, a)); } } }
                for chunk in shots.chunks(64) {
                    let mut h = sha3::Shake256::default();
                    h.update(b"r15");
                    let mut xof = h.finalize_xof();
                    let mut sim = Simulator::new(b.width() as usize, 1, &mut xof);
                    for q in 0..b.width() as usize { sim.qubits[q] = rng.next(); }
                    for &q in &jl { sim.qubits[q.0 as usize] = 0; }
                    let mut want = vec![0usize; chunk.len()];
                    for (s, &(kt, z, a)) in chunk.iter().enumerate() {
                        let bit = 1u64 << s;
                        for i in 0..R_BITS { let q = u.lb[i].0 as usize; if (kt >> i) & 1 == 1 { sim.qubits[q] |= bit } else { sim.qubits[q] &= !bit } }
                        // rows above z: lane 1 (not found) half the time; row z: lane 0; below z random
                        for j in 1..k {
                            let q = u.y[j - 1].0 as usize;
                            if j == z { sim.qubits[q] &= !bit; } else if j > z && rng.next() & 1 == 1 { sim.qubits[q] |= bit; } else if j > z { sim.qubits[q] |= bit; }
                        }
                        let act = !gated || a;
                        if gated { if a { sim.qubits[f.0 as usize] &= !bit } else { sim.qubits[f.0 as usize] |= bit } }
                        let _ = act;
                    }
                    let before = sim.qubits.clone();
                    for (s, &(kt, _, a)) in chunk.iter().enumerate() {
                        let act = !gated || a;
                        let mut r = 0;
                        if act {
                            for j in (1..k.min(kt + 1)).rev() {
                                if (before[u.y[j - 1].0 as usize] >> s) & 1 == 0 { r = j; break; }
                            }
                        }
                        want[s] = r;
                    }
                    sim.apply_iter(b.ops.iter());
                    let n = chunk.len();
                    let mask = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
                    for s in 0..n {
                        let got: usize = (0..R_BITS).map(|i| (((sim.qubits[jl[i].0 as usize] >> s) & 1) as usize) << i).sum();
                        cases += 1;
                        if got != want[s] { fails += 1; if fails < 5 { eprintln!("R15UNIT k {k} gated {gated} shot {:?} got {got} want {}", chunk[s], want[s]); } }
                    }
                    for q in 0..b.width() as usize {
                        if jl.iter().any(|x| x.0 as usize == q) { continue; }
                        if (sim.qubits[q] ^ before[q]) & mask != 0 { fails += 1; eprintln!("R15UNIT k {k} gated {gated}: lane q{q} changed"); }
                    }
                    if sim.phase & mask != 0 { fails += 1; eprintln!("R15UNIT k {k} gated {gated}: phase {:x}", sim.phase & mask); }
                }
            }
        }
        eprintln!("R15UNIT cases {cases} fails {fails}");
        assert_eq!(fails, 0);
    }

    /// I4-ONCE gate-level price of a run-start-gated division row (the PDW-0 rows): the stack's pooled ladder
    /// (mup_mid / mdown_mid, as `division_rows` plain pooled rows) with the down pass's write gate ALWAYS (today's row) vs
    /// a quantum gate lane g. Checks t += s + c0 where g = 1 and identity where g = 0, clean pool, no phase, on 64 shots
    /// per gate value; prints the Toffoli count of each (I4_GATED_ROW=1).
    #[test]
    fn i4_gated_row_price() {
        if std::env::var_os("I4_GATED_ROW").is_none() { return; }
        use super::super::mask::{mup_mid, mdown_mid, Lad, Mscr, ALWAYS};
        use sha3::digest::{ExtendableOutput, Update};
        for &n in &[8usize, 16, 27] {
            for &(gated, pooln) in &[(false, n), (true, n), (false, 2), (true, 2), (false, 0), (true, 0)] {
                let mut b = B::new();
                let t = b.alloc_n(n);
                let sv = b.alloc_n(n);
                let c0 = b.alloc();
                let gq = b.alloc();
                let pool = b.alloc_n(pooln);
                let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
                let ld = Lad { t: &t, s: &sv, c0, srcs: &[], f0: false, cmpl: false, sc: &sc, g: &pool[..pooln.min(n)] };
                let t0 = b.tof;
                let ru = mup_mid(&mut b, &ld);
                b.play(&ru, false);
                let rd = mdown_mid(&mut b, &ld, Some(if gated { gq } else { ALWAYS }));
                b.play(&rd, false);
                let tof = b.tof - t0;
                let mut ok = true;
                for gv in [0u64, u64::MAX] {
                    let mut h = sha3::Shake256::default();
                    h.update(format!("i4-gated-row-{n}-{gated}-{pooln}-{gv}").as_bytes());
                    let mut xof = h.finalize_xof();
                    let nb_ = b.fresh_bits(1)[0].0 as usize + 1;
                    let mut sim = Simulator::new(b.width() as usize, nb_, &mut xof);
                    let mut rnd = 0x1234_5678_9abc_def1u64 ^ (n as u64) ^ gv;
                    let mut nx = || { rnd ^= rnd << 13; rnd ^= rnd >> 7; rnd ^= rnd << 17; rnd };
                    for q in t.iter().chain(sv.iter()).chain([c0].iter()) { sim.qubits[q.0 as usize] = nx(); }
                    sim.qubits[gq.0 as usize] = if gated { gv } else { u64::MAX };
                    let rd_ = |sim: &Simulator<_>, v: &[QubitId], sh: usize| -> u64 {
                        v.iter().enumerate().map(|(i, q)| ((sim.qubits[q.0 as usize] >> sh) & 1) << i).sum() };
                    let before: Vec<(u64, u64, u64)> = (0..64).map(|sh| (rd_(&sim, &t, sh), rd_(&sim, &sv, sh), (sim.qubits[c0.0 as usize] >> sh) & 1)).collect();
                    sim.apply_iter(b.ops.iter());
                    let mask = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
                    for sh in 0..64 {
                        let (tv, svv, cv) = before[sh];
                        let g1 = !gated || gv != 0;
                        let want = if g1 { (tv + svv + cv) & mask } else { tv };
                        if rd_(&sim, &t, sh) != want || rd_(&sim, &sv, sh) != svv { ok = false; }
                        for q in &pool { if (sim.qubits[q.0 as usize] >> sh) & 1 != 0 { ok = false; } }
                    }
                    if sim.phase != 0 { ok = false; }
                }
                eprintln!("I4GATED n {n} pool {pooln} gated {} builder_T {tof} ok {ok}", gated as u8);
                assert!(ok);
            }
        }
    }
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
            if !lanes.is_empty() && lanes[0].0 == PREMISE_MARK {
                for sh in (0..64).filter(|s| skip_mask() >> s & 1 == 0) {
                    let g = |q: QubitId| ((sim.qubits[q.0 as usize] >> sh) & 1) as usize;
                    let x = g(lanes[1]);
                    let t: usize = (0..5).map(|i| g(lanes[2 + i]) << i).sum();
                    let mut c = lanes[7].0 as usize;
                    if lanes.len() > 8 { c += g(lanes[8]); }
                    PREMISE_HIST.with(|h| h.borrow_mut()[c][x][t] += 1);
                    if sh == 0 && c == 1 && std::env::var("B793_PREMISE").map_or(false, |v| v == "4") { eprintln!("PREMDEC x {x} t {t}"); }
                }
                continue;
            }
            for &q in lanes {
                assert_eq!(sim.qubits[q.0 as usize] & !skip_mask(), 0, "hosted lane q{} not |0> at op {at}", q.0);
            }
            n += 1;
        }
        sim.apply_iter(ops[pos..hi].iter());
        n
    }

    /// B-SYMR25 GREEDYFROG_EMU_SKIP (test-only): shots the emulator predicts to fail (a sampled Lambda event: windows,
    /// compares, decode, walk-lane hosts) are excluded from the exactness checks of the windowed / traversal tests;
    /// each excluded shot is reported (and whether the circuit indeed got it wrong).
    static EMU_SKIP_MASK: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    fn skip_mask() -> u64 { EMU_SKIP_MASK.load(std::sync::atomic::Ordering::Relaxed) }
    fn set_skip(m: u64) { EMU_SKIP_MASK.store(m, std::sync::atomic::Ordering::Relaxed) }
    fn check_dirty<R: sha3::digest::XofReader>(sim: &Simulator<'_, R>, u: &GreedyFrog, shots: usize) {
        for s in (0..shots).filter(|s| skip_mask() >> s & 1 == 0) {
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


    /// B792_LT5: exhaustive classical check of the folded compare: every (la[0..8), sX[0..5)) = 8192 states, target ^= [la[5..8) == 0] & [la[0..5) < sX],
    /// all other lanes (la, sX, the carry lane) restored, no phase.
    fn lt5_fold_bad(flip: bool) -> usize {
        let mut b = B::new();
        let la: Vec<QubitId> = (0..8).map(|_| b.alloc()).collect();
        let sx: Vec<QubitId> = (0..5).map(|_| b.alloc()).collect();
        let tgt = b.alloc();
        let anc: Vec<QubitId> = (0..3).map(|_| b.alloc()).collect();
        let lits0: Vec<(QubitId, bool)> = (5..8).map(|i| (la[i], true)).collect();
        let a5 = la[..5].to_vec();
        b792_lt5_fold(&mut b, &a5, &lits0, &sx, tgt, &mut |b, l, o| {
            let mut l = l.to_vec();
            if flip { let n = l.len(); l[n - 1].1 = !l[n - 1].1; }
            let l = &l[..];
            // reference AND chain on clean ancillas, uncomputed by the reverse chain
            for &(q, pol) in l { if pol { b.x(q); } }
            b.ccx(l[0].0, l[1].0, anc[0]);
            b.ccx(anc[0], l[2].0, anc[1]);
            b.ccx(anc[1], l[3].0, anc[2]);
            b.cx(anc[2], o);
            b.ccx(anc[1], l[3].0, anc[2]);
            b.ccx(anc[0], l[2].0, anc[1]);
            b.ccx(l[0].0, l[1].0, anc[0]);
            for &(q, pol) in l { if pol { b.x(q); } }
        });
        let nq = b.width() as usize;
        let mut bad = 0usize;
        for batch in 0..128usize {
            let mut h = sha3::Shake256::default();
            h.update(b"lt5-fold");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(nq, 1, &mut xof);
            for q in 0..nq { sim.qubits[q] = 0; }
            for sh in 0..64usize {
                let st = batch * 64 + sh; // bits 0..8 la, 8..13 sx
                for i in 0..8 { if (st >> i) & 1 == 1 { sim.qubits[la[i].0 as usize] |= 1 << sh; } }
                for i in 0..5 { if (st >> (8 + i)) & 1 == 1 { sim.qubits[sx[i].0 as usize] |= 1 << sh; } }
            }
            sim.apply_iter(b.ops.iter());
            assert_eq!(sim.phase, 0);
            for sh in 0..64usize {
                let st = batch * 64 + sh;
                let (l, x) = (st & 255, (st >> 8) & 31);
                let want = ((l >> 5) == 0 && (l & 31) < x) as u64;
                let got = (sim.qubits[tgt.0 as usize] >> sh) & 1;
                if got != want { bad += 1; }
                for i in 0..8 { assert_eq!((sim.qubits[la[i].0 as usize] >> sh) & 1, ((st >> i) & 1) as u64, "la restored"); }
                for i in 0..5 { assert_eq!((sim.qubits[sx[i].0 as usize] >> sh) & 1, ((st >> (8 + i)) & 1) as u64, "sx restored"); }
            }
            for q in nq - 1..nq { let _ = q; }
            for q in 0..nq as u64 { if la.iter().chain(&sx).chain(std::iter::once(&tgt)).any(|x| x.0 == q) { continue; } assert_eq!(sim.qubits[q as usize], 0, "scratch qubit {q} dirty"); }
        }
        bad
    }
    #[test]
    fn lt5_fold_exhaustive() {
        let bad = lt5_fold_bad(false);
        assert_eq!(bad, 0, "folded compare differs from the reference on {bad} of 8192 states");
    }
    /// negative control: the carry literal flipped must be caught by the same exhaustive check
    #[test]
    fn lt5_fold_control_flipped_literal() {
        assert!(lt5_fold_bad(true) > 0, "the exhaustive check cannot see a flipped carry literal");
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
            // SW-CARRY pair mode: forward slot s + 1 and its inverse (standard I2, producing the carry) run between
            // slot s's forward and inverse, so slot s's inverse takes the carried flag (GREEDYFROG_SWC_SINGLE=1: off)
            let pair = sw_carry() && slot + 1 < NSLOTS && std::env::var_os("GREEDYFROG_SWC_SINGLE").is_none();
            // LS-3 DCMP-REUSE: in pair mode slot s hands its comparator to slot s + 1
            let bits = u.fwd_slot_next(&mut b, w, if pair { Some(&ws[slot + 1]) } else { None });
            let mid = b.ops.len();
            let t1 = b.tof;
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
                    let fx: Option<N> = std::env::var("GREEDYFROG_FORCE_X").ok().and_then(|v| v.split(',').nth(i).and_then(|h| N::from_str_radix(h.trim().trim_start_matches("0x"), 16).ok()));
                    let x = fx.or(forced).or(short).unwrap_or_else(|| rng.input());
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
                let skip = if std::env::var_os("GREEDYFROG_EMU_SKIP").is_some() {
                    states.iter().enumerate().fold(0u64, |m, (sh, st)| {
                        let bad = super::super::greedyfrog_diag::emu_slot_check(st, w, ws.get(slot + 1)).is_some()
                            || (pair && { let mut l = st.clone(); l.fwd();
                                          super::super::greedyfrog_diag::emu_slot_check(&l, &ws[slot + 1], ws.get(slot + 2)).is_some() });
                        if bad { m | 1 << sh } else { m }
                    })
                } else { 0 };
                set_skip(skip);
                sim.apply_iter(b.ops[..mid].iter());
                check_dirty(&sim, &u, 64);
                for (sh, st) in states.iter().enumerate().filter(|(sh, _)| skip >> sh & 1 == 0) {
                    let mut want = st.clone();
                    want.fwd();
                    assert_eq!(read(&sim, &u0, sh), want, "slot {slot} round {round} shot {sh}: forward mismatch");
                }
                apply_probed(&mut sim, &b.ops, mid, b.ops.len(), &probes);
                check_dirty(&sim, &u, 64);
                assert_eq!(sim.phase & !skip, 0, "slot {slot} round {round}: phase garbage {:016x}", sim.phase);
                let mut scr = 0u64;
                for q in 0..b.width() {
                    if !regs.contains(&q) {
                        scr |= sim.qubits[q as usize];
                        assert_eq!(sim.qubits[q as usize] & !skip, 0, "slot {slot} round {round}: scratch qubit {q} dirty");
                    }
                }
                let mut bad = sim.phase | scr;
                for (sh, st) in states.iter().enumerate() {
                    if &read(&sim, &u, sh) != st { bad |= 1 << sh; }
                    if skip >> sh & 1 == 1 { continue; }
                    assert_eq!(&read(&sim, &u, sh), st, "slot {slot} round {round} shot {sh}: state not restored");
                }
                if skip != 0 {
                    eprintln!("EMU_SKIP slot {slot} round {round}: skipped {skip:016x} circuit_bad {:016x}", bad & skip);
                }
                set_skip(0);
            }
        }
        if !stall_pool.is_empty() {
            eprintln!("WIN_STALL: {stall_shots} forced stall shots checked exact");
        }
        if !short_pool.is_empty() {
            eprintln!("WIN_SHORT: {short_shots} forced short-divisor shots checked exact");
        }
    }

    /// R8-LANE799 envelope check (R8_ENVN=n): walk n random inputs on the integer model and count, per slot, shots whose
    /// LA or LB at the slot start reaches 2^hb (hb as R8_LHF computes it, every slot), split by whether the walk stays
    /// inside the parent's LB / LA-d windows at every active slot (a shot outside them already fails in the parent).
    #[test]
    fn r8_env_check() {
        let Some(n) = std::env::var("R8_ENVN").ok().and_then(|v| v.parse::<usize>().ok()) else { return };
        let ws = windows();
        let mut rng = Rng(0x5238_4c41_4e45_0799 ^ std::env::var("R8_ENVSEED").ok().and_then(|v| v.parse::<u64>().ok()).unwrap_or(0));
        let hbs: Vec<usize> = ws.iter().map(|w| {
            let m = (w.lad.1 + 1).max(w.lb.1) + 2;
            ((usize::BITS - m.leading_zeros()) as usize).max(5).max(w.la_hb)
        }).collect();
        let (mut viol_in, mut viol_out, mut walks_out, mut stall_viol) = (0usize, 0usize, 0usize, 0usize);
        let mut min_slack = i64::MAX;
        for _ in 0..n {
            let x = rng.input();
            let mut sp = Spec::new(x);
            let mut inside = true;
            let mut v: Vec<(usize, bool)> = vec![];
            for s in 0..NSLOTS {
                let (la, lb, act, stall) = (sp.la, sp.lb, sp.la != 0, sp.la != 0 && sp.lag > 0);
                let w = &ws[s];
                if hbs[s] < LB_BITS - 1 {
                    let top = 1usize << hbs[s];
                    min_slack = min_slack.min(top as i64 - 1 - la.max(lb) as i64);
                    if la >= top || lb >= top { v.push((s, stall)); }
                }
                let st = sp.fwd();
                if let super::super::greedyfrog_model::Slot::Step { d, .. } = st {
                    if act && (lb < w.lb.0 || lb > w.lb.1 || la - d < w.lad.0 || la - d > w.lad.1) { inside = false; }
                }
            }
            if !inside { walks_out += 1; }
            for &(_, stall) in &v { if stall { stall_viol += 1; } }
            if !v.is_empty() { if inside { viol_in += 1; } else { viol_out += 1; } }
        }
        eprintln!("R8ENV walks {n} outside-windows {walks_out} | hb violations: walks inside {viol_in}, outside {viol_out}, stall-slot hits {stall_viol} | min slack {min_slack}");
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
        // R8-LANE799 dev instrument (test only): R8_BUMP="F|I:lo-hi:n,..." lends n lanes of cap on those slots;
        // R8_SLOTT=1 records each slot's op range for the per-slot expected Toffoli print
        let cap0 = u.cap;
        let bump = |dir: char, s: usize| -> u64 {
            std::env::var("R8_BUMP").ok().map_or(0, |v| v.split(',').filter_map(|e| {
                let p: Vec<&str> = e.split(':').collect();
                let (a, c) = p[1].split_once('-')?;
                (p[0].starts_with(dir) && (a.parse::<usize>().ok()?..=c.parse::<usize>().ok()?).contains(&s))
                    .then(|| p[2].parse::<u64>().unwrap())
            }).sum())
        };
        let mut r8_rng: Vec<(char, usize, usize, usize)> = vec![];
        for s in 0..NS {
            super::super::builder::i5::set_slot(s as i64);
            u.cap = cap0 + bump('F', s);
            p3_slot(s);
            let o0 = b.ops.len();
            all_bits.push(u.fwd_slot_next(&mut b, &ws[s], ws.get(s + 1)));
            r8_rng.push(('F', s, o0, b.ops.len()));
        }
        u.cap = cap0;
        assert!(u.cmp_in.is_none());
        let mid_ops = b.ops.len();
        let t1 = b.tof;
        let peak_fwd = b.peak;
        let mut carry = None;
        let mut carried = 0;
        mj_clear();
        for (s, bits) in all_bits.iter().enumerate().rev() {
            super::super::builder::i5::set_slot(1000 + s as i64);
            carried += carry.is_some() as usize;
            mj_set_next(if s > 0 { Some(&ws[s - 1]) } else { None });
            u.cap = cap0 + bump('I', s);
            p3_slot(s);
            let o0 = b.ops.len();
            carry = u.inv_slot_c(&mut b, bits, &ws[s], carry, s >= 1);
            r8_rng.push(('I', s, o0, b.ops.len()));
        }
        u.cap = cap0;
        mj_clear();
        assert!(carry.is_none());
        eprintln!("greedyfrog traversal: SW-CARRY {} inverse slots took a carried swap flag", carried);
        super::super::builder::p2_over_dump(); // R3-FIT799: dev probe, inert unless P2_OVER is set
        eprintln!("greedyfrog traversal: forward {} T, inverse {} T, ops {} (+{}), peak {} (forward {})", t1 - t0, b.tof - t1,
                  mid_ops, b.ops.len() - mid_ops, b.peak, peak_fwd);
        prof_dump();
        super::super::builder::r8idle::dump();
        {
            // R6-ROOM799: static expected Toffoli (a CCX inside d open condition blocks counts 2^-d), as SL_COND
            let ex = |ops: &[crate::circuit::Op]| {
                let (mut d, mut e) = (0i32, 0f64);
                for o in ops {
                    match o.kind {
                        crate::circuit::OperationType::PushCondition => d += 1,
                        crate::circuit::OperationType::PopCondition => d -= 1,
                        crate::circuit::OperationType::CCX => e += 0.5f64.powi(d),
                        _ => {}
                    }
                }
                e
            };
            if std::env::var_os("R8_SLOTT").is_some() {
                for &(d, s, a, c) in &r8_rng { eprintln!("R8SLOT {d} {s} {:.1}", ex(&b.ops[a..c])); }
            }
            let (ef, ei) = (ex(&b.ops[..mid_ops]), ex(&b.ops[mid_ops..]));
            eprintln!("greedyfrog traversal: expected forward {ef:.1} inverse {ei:.1} total {:.1}", ef + ei);
        }
        // R9 rowtmp dev diagnostic (test only, R9_POISON_DBG=1): the first ops touching an R8_LHF poison id, by slot
        if std::env::var_os("R9_POISON_DBG").is_some() {
            let mut shown = 0;
            for (i, o) in b.ops.iter().enumerate() {
                let qs = [o.q_target.0, o.q_control1.0, o.q_control2.0];
                if qs.iter().any(|&q| q >= R8_POISON && q < R8_POISON + 64) {
                    let sl = r8_rng.iter().find(|&&(_, _, a, c)| i >= a && i < c).map(|&(d, s, _, _)| format!("{d}{s}"));
                    eprintln!("R9POISON op {i} {:?} slot {:?} kind {:?}", qs, sl, o.kind);
                    shown += 1;
                    if shown >= 12 { break; }
                }
            }
        }
        let probes = take_zero_probes();
        let mut regs: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
        for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par)).chain(&u.dirty) {
            regs.insert(q.0);
        }
        let mut rng = Rng(std::env::var("I5_SEED").ok().and_then(|v| v.parse::<u64>().ok()).map_or(0x2468_1357_aaaa_5555, |k| 0x2468_1357_aaaa_5555 ^ k.wrapping_mul(0x9e37_79b9_7f4a_7c15)));
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
            if std::env::var_os("GREEDYFROG_SLOTDUMP").is_some() {
                let mut pos = mid_ops;
                for &(d, sl, _o0, o1) in r8_rng.iter().filter(|r| r.0 == 'I') {
                    sim.apply_iter(b.ops[pos..o1].iter());
                    pos = o1;
                    let st = read(&sim, &u, 1);
                    let hx = |v: &Vec<u8>| v.iter().fold(0xcbf29ce484222325u64, |h, &b| (h ^ b as u64).wrapping_mul(0x100000001b3));
                    eprintln!("SLOTDUMP {d}{sl} la {} lb {} cnt {} par {} xh {:016x} yh {:016x}", st.la, st.lb, st.cnt, st.par, hx(&st.x), hx(&st.y));
                }
                sim.apply_iter(b.ops[pos..].iter());
            } else {
            sim.apply_iter(b.ops[mid_ops..].iter());
            }
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
        let skip = if std::env::var_os("GREEDYFROG_EMU_SKIP").is_some() {
            (0..64).fold(0u64, |m, s| if super::super::greedyfrog_diag::diag_walk(xs[s], &ws).is_some() { m | 1 << s } else { m })
        } else { 0 };
        if skip != 0 { eprintln!("EMU_SKIP traversal: skipped {skip:016x}"); }
        set_skip(skip);
        for s in (0..64).filter(|s| skip >> s & 1 == 0) {
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
        if std::env::var_os("B793_PREMISE").is_some() {
            PREMISE_HIST.with(|h| { let h = h.borrow(); for c in 0..4 { for x in 0..2 {
                eprintln!("PREMISE act_const {c} x {x}: {}", (0..32).map(|t| format!("{t}:{}", h[c][x][t])).filter(|s| !s.ends_with(":0")).collect::<Vec<_>>().join(" "));
            } } });
        }
        check_dirty(&sim, &u, 64);
        assert_eq!(sim.phase & !skip, 0, "phase garbage {:016x}", sim.phase);
        for q in 0..b.width() {
            if !regs.contains(&q) {
                assert_eq!(sim.qubits[q as usize] & !skip, 0, "scratch qubit {q} dirty");
            }
        }
        for s in 0..64 {
            if read(&sim, &u, s) != starts[s] {
                eprintln!("TRAV_FAIL shot {s}: start not restored");
            }
        }
        for s in (0..64).filter(|s| skip >> s & 1 == 0) {
            assert_eq!(read(&sim, &u, s), starts[s], "shot {s}: start not restored");
        }
        set_skip(0);
        eprintln!("greedyfrog traversal: 64 shots exact, round trip clean");
    }
}


#[cfg(test)]
mod b793_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{Update, ExtendableOutput};
    /// b793a Gipfeli: the emitted MCX stages (b793_mcx on real builder ops with and_dirty) over all 37 valid states
    /// (x = 1: t = 0..31; x = 0: t in {0, 7, 14, 21, 28}), dirty hosts random and restored. After P1 lane x must hold
    /// res1 = [t >= 22]; with that lane cleared (the X-measurement), P2 must leave rho on j0..j2, res0 on j3, a1 on j4,
    /// x on its lane. Negative controls: a dropped last gate of either stage must break some state.
    /// b793b FPARK: PRE (sY ^= F & !x; x ^= F & sY) + Gipfeli + POST on F = 1 (pf all zero, sY = 0, every (t, x)) equals the on-table decode of t and
    /// restores x and sY; on F = 0 (one pf lane set, any sY, the 37 table states) it is Gipfeli alone. Negative controls: PRE dropped, POST's x step dropped,
    /// POST's sY step dropped must each break some state.
    /// b793b ACTFOLD=2: encode (LA := 127 on f = 1, f cleared), the gate read AND(LA[0..7)), and the restore (LA := sX on f' = 1) over every active u in 0..=126
    /// (f = 0, sX arbitrary), every finished shot (f = 1, LA = sX, sX 0..31) and the constructed active u = 96..=126 band; u = 127 is the one documented
    /// collision (read as finished). Controls: a dropped encode bit, a dropped restore bit.
    #[test]
    fn b793_actfold2_exhaustive() {
        for brk in 0..3usize {
            let mut states: Vec<(usize, usize, usize)> = vec![]; // (f, LA value, sX)
            for u in 0..=126usize { for &sxv in &[0usize, 1, 5, 17, 31] { states.push((0, u, sxv)); } }
            for sxv in 0..32usize { states.push((1, sxv, sxv)); }
            let mut bad_total = 0usize;
            for chunk in states.chunks(64) {
                let mut b = B::new();
                let la = b.alloc_n(7);
                let sx = b.alloc_n(5);
                let f = b.alloc();
                let fp = b.alloc();
                let dirty = b.alloc_n(7);
                for i in 0..5 { b.x(sx[i]); if !(i == 0 && brk == 1) { b.ccx(f, sx[i], la[i]); } b.x(sx[i]); }
                b.cx(f, la[5]);
                b.cx(f, la[6]);
                let lits: Vec<(QubitId, bool)> = la.iter().map(|&q| (q, false)).collect();
                and_dirty(&mut b, &lits, f, &dirty);
                let mid = b.ops.len();
                // gate read: fp ^= AND(LA) (= !act), then it plays the role of !a1 & !rho in the restore
                and_dirty(&mut b, &lits, fp, &dirty);
                for i in 0..5 { b.x(sx[i]); if !(i == 0 && brk == 2) { b.ccx(fp, sx[i], la[i]); } b.x(sx[i]); }
                b.cx(fp, la[5]);
                b.cx(fp, la[6]);
                let mut h = sha3::Shake256::default();
                h.update(b"b793-af2");
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(b.width() as usize, 8, &mut xof);
                let mut rs: u64 = 0x3234_5678_9abc_def1;
                let mut nx = || { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; rs };
                for &q in &dirty { sim.qubits[q.0 as usize] = nx(); }
                let dirty0: Vec<u64> = dirty.iter().map(|q| sim.qubits[q.0 as usize]).collect();
                for (sh, &(fv, uv, sxv)) in chunk.iter().enumerate() {
                    if fv == 1 { sim.qubits[f.0 as usize] |= 1 << sh; }
                    for i in 0..7 { if uv >> i & 1 == 1 { sim.qubits[la[i].0 as usize] |= 1 << sh; } }
                    for i in 0..5 { if sxv >> i & 1 == 1 { sim.qubits[sx[i].0 as usize] |= 1 << sh; } }
                }
                let g = |sim: &Simulator<'_, _>, q: QubitId, sh: usize| ((sim.qubits[q.0 as usize] >> sh) & 1) as usize;
                sim.apply_iter(b.ops[..mid].iter());
                let mut bad = 0usize;
                for (sh, &(fv, uv, _)) in chunk.iter().enumerate() {
                    let code: usize = (0..7).map(|i| g(&sim, la[i], sh) << i).sum();
                    if g(&sim, f, sh) != 0 { bad += 1; }
                    if fv == 1 && code != 127 { bad += 1; }
                    if fv == 0 && code != uv { bad += 1; }
                }
                sim.apply_iter(b.ops[mid..].iter());
                for (sh, &(fv, uv, sxv)) in chunk.iter().enumerate() {
                    let code: usize = (0..7).map(|i| g(&sim, la[i], sh) << i).sum();
                    if g(&sim, fp, sh) != fv { bad += 1; }
                    let want = if fv == 1 { sxv } else { uv };
                    if code != want { bad += 1; }
                }
                for (i, &q) in dirty.iter().enumerate() { if sim.qubits[q.0 as usize] != dirty0[i] { bad += 1000; } }
                bad_total += bad;
            }
            if brk == 0 { assert_eq!(bad_total, 0, "ACTFOLD=2 wrong on {bad_total} checks"); } else { assert!(bad_total > 0, "negative control {brk} did not break"); }
            eprintln!("B793 actfold2 brk {brk}: bad {bad_total}");
        }
    }
    #[test]
    fn b793_fpark_exhaustive() {
        for brk in 0..4usize {
            let mut states: Vec<(usize, usize, usize, usize, usize)> = vec![]; // (pf one-hot index or 7 = none, t, x, sy)
            for t in 0..32 { for x in 0..2 { states.push((7, t, x, 0, 1)); } }
            for k in 0..7 { for sy in 0..2 { for t in 0..32 { states.push((k, t, 1, sy, 0)); } for &t in &[0usize, 7, 14, 21, 28] { states.push((k, t, 0, sy, 0)); } } }
            let mut bad_total = 0usize;
            for chunk in states.chunks(64) {
                let mut b = B::new();
                let pfq = b.alloc_n(7);
                let syq = b.alloc();
                let jq = b.alloc_n(5);
                let xl = b.alloc();
                let dirty = b.alloc_n(7);
                let lanes: [QubitId; 6] = [jq[0], jq[1], jq[2], jq[3], jq[4], xl];
                let pf: Vec<(QubitId, bool)> = pfq.iter().map(|&q| (q, true)).collect();
                let mut l1 = pf.clone(); l1.push((xl, true));
                let mut l2 = pf.clone(); l2.push((syq, false));
                if brk != 1 { and_dirty(&mut b, &l1, syq, &dirty); and_dirty(&mut b, &l2, xl, &dirty); }
                b793_mcx(&mut b, &lanes, &B793_P1, &dirty);
                let mid = b.ops.len();
                b793_mcx(&mut b, &lanes, &B793_P2, &dirty);
                let post = b.ops.len();
                if brk != 2 { and_dirty(&mut b, &l2, xl, &dirty); }
                if brk != 3 { and_dirty(&mut b, &l1, syq, &dirty); }
                let mut h = sha3::Shake256::default();
                h.update(b"b793-fpark");
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(b.width() as usize, 8, &mut xof);
                let mut rs: u64 = 0x2234_5678_9abc_def1;
                let mut nx = || { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; rs };
                for &q in &dirty { sim.qubits[q.0 as usize] = nx(); }
                let dirty0: Vec<u64> = dirty.iter().map(|q| sim.qubits[q.0 as usize]).collect();
                for (sh, &(k, t, x, sy, _f)) in chunk.iter().enumerate() {
                    if k < 7 { sim.qubits[pfq[k].0 as usize] |= 1 << sh; }
                    if sy == 1 { sim.qubits[syq.0 as usize] |= 1 << sh; }
                    for i in 0..5 { if t >> i & 1 == 1 { sim.qubits[jq[i].0 as usize] |= 1 << sh; } }
                    if x == 1 { sim.qubits[xl.0 as usize] |= 1 << sh; }
                }
                let pre = b.ops.len() - 0; let _ = pre;
                sim.apply_iter(b.ops[..mid].iter());
                let g = |sim: &Simulator<'_, _>, q: QubitId, sh: usize| ((sim.qubits[q.0 as usize] >> sh) & 1) as usize;
                let mut bad = 0usize;
                for (sh, &(_k, t, _x, _sy, _f)) in chunk.iter().enumerate() {
                    let m = [8usize, 15, 22, 29].iter().filter(|&&c| t >= c).count();
                    let res = if t >= 8 { m - 1 } else { 0 };
                    if g(&sim, xl, sh) != res >> 1 { bad += 1; }
                }
                sim.qubits[xl.0 as usize] = 0;
                sim.apply_iter(b.ops[mid..post].iter());
                sim.apply_iter(b.ops[post..].iter());
                for (sh, &(k, t, x, sy, _f)) in chunk.iter().enumerate() {
                    let (rho, a1) = super::super::greedyfrog_model::rho_of(t);
                    let m = [8usize, 15, 22, 29].iter().filter(|&&c| t >= c).count();
                    let res = if t >= 8 { m - 1 } else { 0 };
                    let got_rho: usize = (0..3).map(|i| g(&sim, jq[i], sh) << i).sum();
                    if got_rho != rho || g(&sim, jq[3], sh) != (res & 1) || g(&sim, jq[4], sh) != a1 as usize { bad += 1; }
                    if g(&sim, xl, sh) != x || g(&sim, syq, sh) != sy { bad += 1; }
                    for i in 0..7 { if g(&sim, pfq[i], sh) != (i == k) as usize { bad += 1; } }
                }
                for (i, &q) in dirty.iter().enumerate() { if sim.qubits[q.0 as usize] != dirty0[i] { bad += 1000; } }
                bad_total += bad;
            }
            if brk == 0 { assert_eq!(bad_total, 0, "FPARK wrong on {bad_total} checks"); } else { assert!(bad_total > 0, "negative control {brk} did not break"); }
            eprintln!("B793 fpark brk {brk}: bad {bad_total}");
        }
    }
    /// b792w4 P11S: the no-jl sweep on classical states: (rho, a1) = rho_of(sX - sY - jl) with jl the last row j <= kt, j >= 1 with lane_j = 0 (else 0);
    /// every other lane (dirty pool, kt, lanes, sX, sY, X[W-1]) restored. Negative controls B792_BREAK=p11s_mono / p11s_ge (dev env) must make it fail.
    #[test]
    fn b792_p11s_exhaustive() {
        let mut rs: u64 = 0x1234_5678_9abc_def1;
        let mut nx = || { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; rs };
        let mut bad_total = 0usize; let mut n = 0usize;
        for &k in &[2usize, 3, 4, 7, 16, 17, 22, 31] {
            let mut states: Vec<(usize, Vec<usize>, usize, usize)> = vec![]; // (kt, lane bits j=1..k, sx, sy)
            if k <= 7 {
                for kt in 0..32 { for lb in 0..(1usize << (k - 1)) { for sx in [0usize, 1, 7, 8, 15, 16, 31] { for sy in 0..2 { states.push((kt, (0..k - 1).map(|i| lb >> i & 1).collect(), sx, sy)); } } } }
            } else {
                for _ in 0..40000 { let kt = (nx() % 32) as usize; let lb = nx(); states.push((kt, (0..k - 1).map(|i| (lb >> i & 1) as usize).collect(), (nx() % 32) as usize, (nx() % 2) as usize)); }
                for kt in 0..32 { for sx in 0..32 { states.push((kt, vec![1; k - 1], sx, 1)); states.push((kt, vec![0; k - 1], sx, 0)); } }
            }
            for chunk in states.chunks(64) {
                let mut b = B::new();
                let kt5 = b.alloc_n(5); let lq = b.alloc_n(k - 1); let sx = b.alloc_n(5); let sy = b.alloc(); let xt = b.alloc();
                let out = b.alloc_n(4); let dirty = b.alloc_n(k + 12);
                let mut lanes = vec![NOQ]; lanes.extend(&lq);
                nj_run(&mut b, k, &kt5, &lanes, xt, &sx, sy, &out, &dirty, &[], None, None, NjAct::None);
                let mut h = sha3::Shake256::default();
                h.update(b"b792-p11s");
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(b.width() as usize, 8, &mut xof);
                for &q in &dirty { sim.qubits[q.0 as usize] = nx(); }
                let dirty0: Vec<u64> = dirty.iter().map(|q| sim.qubits[q.0 as usize]).collect();
                let xt0 = nx(); sim.qubits[xt.0 as usize] = xt0;
                for (sh, (kt, lb, sxv, syv)) in chunk.iter().enumerate() {
                    for i in 0..5 { if kt >> i & 1 == 1 { sim.qubits[kt5[i].0 as usize] |= 1 << sh; } if sxv >> i & 1 == 1 { sim.qubits[sx[i].0 as usize] |= 1 << sh; } }
                    for (i, &v) in lb.iter().enumerate() { if v == 1 { sim.qubits[lq[i].0 as usize] |= 1 << sh; } }
                    if *syv == 1 { sim.qubits[sy.0 as usize] |= 1 << sh; }
                }
                sim.apply_iter(b.ops.iter());
                let g = |sim: &Simulator<'_, _>, q: QubitId, sh: usize| ((sim.qubits[q.0 as usize] >> sh) & 1) as usize;
                for (sh, (kt, lb, sxv, syv)) in chunk.iter().enumerate() {
                    let mut jl = 0usize;
                    for j in 1..k { if j <= *kt && lb[j - 1] == 0 { jl = j; } }
                    let want = nj_f((*sxv + 64 - *syv - jl) & 31);
                    let got: usize = (0..4).map(|i| g(&sim, out[i], sh) << i).sum();
                    n += 1;
                    if got != want { bad_total += 1; }
                    let sxg: usize = (0..5).map(|i| g(&sim, sx[i], sh) << i).sum();
                    if sxg != *sxv || g(&sim, sy, sh) != *syv { bad_total += 1; }
                    for i in 0..5 { if g(&sim, kt5[i], sh) != (kt >> i & 1) { bad_total += 1; } }
                    for (i, &v) in lb.iter().enumerate() { if g(&sim, lq[i], sh) != v { bad_total += 1; } }
                }
                for (i, &q) in dirty.iter().enumerate() { if sim.qubits[q.0 as usize] != dirty0[i] { bad_total += 1000; } }
                if sim.qubits[xt.0 as usize] != xt0 { bad_total += 1000; }
            }
        }
        eprintln!("B792 p11s exhaustive: {n} states, bad {bad_total}");
        if std::env::var_os("B792_BREAK").is_some() { assert!(bad_total > 0, "negative control did not break"); } else { assert_eq!(bad_total, 0); }
    }
    /// b792 R40 (B792-ROWS): the no-jl sweep at k = 21 (the slots 40-44 value) EXHAUSTIVELY through the real emitted gates. The kernel's inputs are the 5-bit kt5,
    /// the 5-bit sX, sY and the 20 row lanes, none of them slot-specific, so "the ranges slots 40-43 take" are the full input spaces.
    /// Part A: all 2^20 lane patterns x all 32 kt5, (sX, sY) from a deterministic mix that covers all 64 pairs for every kt5 (2^25 states).
    /// Part B: all 32 kt5 x 32 sX x 2 sY x the lane patterns {all ones, all zeros, every single-zero, every double-zero} (2^11 x 232 states).
    /// Checks per state: (rho, a1) = rho_of(sX - sY - jl); kt5, lanes, sX, sY, X[W-1] and every dirty lane restored bit for bit; the phase is 0;
    /// no other qubit exists. Negative control: B792_BREAK=p11s_mono (build-time, the same code path) must make `bad` positive.
    #[test]
    fn b792_p11s_k21_exhaustive() {
        let k = 21usize;
        let mut b = B::new();
        let kt5 = b.alloc_n(5); let lq = b.alloc_n(k - 1); let sx = b.alloc_n(5); let sy = b.alloc(); let xt = b.alloc();
        let out = b.alloc_n(4); let dirty = b.alloc_n(k + 12);
        let nq_alloc = b.width() as usize;
        let mut lanes = vec![NOQ]; lanes.extend(&lq);
        nj_run(&mut b, k, &kt5, &lanes, xt, &sx, sy, &out, &dirty, &[], None, None, NjAct::None);
        assert_eq!(b.width() as usize, nq_alloc, "the kernel allocated a qubit");
        let ops = &b.ops;
        eprintln!("b792 p11s k21: {} ops, {} qubits", ops.len(), nq_alloc);
        let mut states: Vec<(usize, u32, usize, usize)> = vec![]; // (kt, lane bits, sx, sy)
        let full = std::env::var_os("B792_K21_PARTA").is_some() || std::env::var_os("B792_BREAK").is_none();
        let part_a: u64 = if full { 1u64 << 25 } else { 1u64 << 18 };
        let mut total_bad = 0usize; let mut n = 0u64;
        let nthreads = 8u64;
        let run_batch = |chunk: &[(usize, u32, usize, usize)], seed: u64| -> usize {
            let mut bad = 0usize;
            let mut rs: u64 = 0x1234_5678_9abc_def1 ^ seed.wrapping_mul(0x9e37_79b9_7f4a_7c15);
            let mut nx = || { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; rs };
            let mut h = sha3::Shake256::default();
            h.update(b"b792-p11s-k21");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(nq_alloc, 8, &mut xof);
            for &q in &dirty { sim.qubits[q.0 as usize] = nx(); }
            let dirty0: Vec<u64> = dirty.iter().map(|q| sim.qubits[q.0 as usize]).collect();
            let xt0 = nx(); sim.qubits[xt.0 as usize] = xt0;
            for (sh, &(kt, lb, sxv, syv)) in chunk.iter().enumerate() {
                for i in 0..5 { if kt >> i & 1 == 1 { sim.qubits[kt5[i].0 as usize] |= 1 << sh; } if sxv >> i & 1 == 1 { sim.qubits[sx[i].0 as usize] |= 1 << sh; } }
                for i in 0..k - 1 { if lb >> i & 1 == 1 { sim.qubits[lq[i].0 as usize] |= 1 << sh; } }
                if syv == 1 { sim.qubits[sy.0 as usize] |= 1 << sh; }
            }
            let init: Vec<u64> = sim.qubits.clone();
            sim.apply_iter(ops.iter());
            let g = |sim: &Simulator<'_, _>, q: QubitId, sh: usize| ((sim.qubits[q.0 as usize] >> sh) & 1) as usize;
            let live: u64 = if chunk.len() == 64 { !0 } else { (1u64 << chunk.len()) - 1 };
            if sim.phase & live != 0 { bad += (sim.phase & live).count_ones() as usize; }
            for (sh, &(kt, lb, sxv, syv)) in chunk.iter().enumerate() {
                let mut jl = 0usize;
                for j in 1..k { if j <= kt && (lb >> (j - 1)) & 1 == 0 { jl = j; } }
                let want = nj_f((sxv + 64 - syv - jl) & 31);
                let got: usize = (0..4).map(|i| g(&sim, out[i], sh) << i).sum();
                if got != want { bad += 1; }
            }
            // restoration of every input lane: all qubits except `out` equal their initial words on the live shots
            for q in 0..nq_alloc {
                if out.iter().any(|o| o.0 as usize == q) { continue; }
                if (sim.qubits[q] ^ init[q]) & live != 0 { bad += 1000; }
            }
            for i in 0..4 { let _ = dirty0.len() + i; }
            bad
        };
        // Part B states
        let mut pats: Vec<u32> = vec![(1u32 << (k - 1)) - 1, 0];
        for i in 0..k - 1 { pats.push(((1u32 << (k - 1)) - 1) ^ (1 << i)); }
        for i in 0..k - 1 { for j in i + 1..k - 1 { pats.push(((1u32 << (k - 1)) - 1) ^ (1 << i) ^ (1 << j)); } }
        for &lb in &pats { for kt in 0..32usize { for sxv in 0..32usize { for syv in 0..2usize { states.push((kt, lb, sxv, syv)); } } } }
        let part_b = states.len() as u64;
        let total = part_a + part_b;
        let counter = std::sync::atomic::AtomicU64::new(0);
        let bad_sum = std::sync::atomic::AtomicUsize::new(0);
        let states_ref = &states;
        let lanes_mask = (1u64 << (k - 1)) - 1;
        std::thread::scope(|sc| {
            for t in 0..nthreads {
                let counter = &counter; let bad_sum = &bad_sum; let run_batch = &run_batch;
                sc.spawn(move || {
                    loop {
                        let c = counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let start = c * 64;
                        if start >= total { break; }
                        let end = (start + 64).min(total);
                        let mut chunk: Vec<(usize, u32, usize, usize)> = Vec::with_capacity(64);
                        for idx in start..end {
                            if idx < part_a {
                                let kt = ((idx >> 20) & 31) as usize; let lb = (idx & lanes_mask) as u32;
                                let hsh = (idx.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 58) as usize; // 6 bits
                                // mix so that every kt5 sees all 64 (sx, sy) pairs over its lane patterns
                                let pair = (hsh ^ (idx as usize >> 14)) & 63;
                                chunk.push((kt, lb, pair & 31, pair >> 5));
                            } else { chunk.push(states_ref[(idx - part_a) as usize]); }
                        }
                        let bad = run_batch(&chunk, c ^ t);
                        if bad > 0 { bad_sum.fetch_add(bad, std::sync::atomic::Ordering::Relaxed); }
                    }
                });
            }
        });
        n += total; total_bad += bad_sum.load(std::sync::atomic::Ordering::Relaxed);
        eprintln!("B792 p11s k21 exhaustive: {n} states (part A {part_a}, part B {part_b}), bad {total_bad}");
        if std::env::var_os("B792_BREAK").is_some() { assert!(total_bad > 0, "negative control did not break"); } else { assert_eq!(total_bad, 0); }
    }
    /// b792w4 P11S, the stall branch: the phase owed by the previous (non-act-constant) slot, (-1)^(m_i t_o (1 ^ X ^ g)), o = (3, 4), g = !X & [LA == sX],
    /// t = sX - sY - jl, paid inside the sweep (gp = Some): checked per shot on classical states with X = 0 / 1, LA == sX / not, random measured bits m.
    /// Negative controls (dev env B792_BREAK): p11s_gate (drops the g term), p11s_pend (drops the whole phase).
    #[test]
    fn b792_p11s_stall_phase() {
        let mut rs: u64 = 0x9e37_79b9_7f4a_7c15;
        let mut nx = || { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; rs };
        let (mut bad, mut n, mut fired) = (0usize, 0usize, 0usize);
        for &k in &[2usize, 5, 22, 31] {
            for round in 0..40 {
                let mut b = B::new();
                let kt5 = b.alloc_n(5); let lq = b.alloc_n(k - 1); let sx = b.alloc_n(5); let sy = b.alloc(); let xt = b.alloc();
                let out = b.alloc_n(4); let dirty = b.alloc_n(k + 14); let la = b.alloc_n(5);
                let mb = b.fresh_bits(2);
                let mut lanes = vec![NOQ]; lanes.extend(&lq);
                nj_run(&mut b, k, &kt5, &lanes, xt, &sx, sy, &out, &dirty, &la, Some(mb.clone()), Some((vec![], None)), NjAct::None);
                let mut h = sha3::Shake256::default();
                h.update(b"b792-p11s-stall");
                h.update(&[k as u8, round as u8]);
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(b.width() as usize, 10_100, &mut xof);
                for &q in &dirty { sim.qubits[q.0 as usize] = nx(); }
                let dirty0: Vec<u64> = dirty.iter().map(|q| sim.qubits[q.0 as usize]).collect();
                let (m0, m1, xv) = (nx(), nx(), nx());
                sim.bits[mb[0].0 as usize] = m0; sim.bits[mb[1].0 as usize] = m1;
                sim.qubits[xt.0 as usize] = xv;
                let mut st = vec![];
                for sh in 0..64 {
                    let kt = (nx() % 32) as usize; let lb = nx(); let sxv = (nx() % 32) as usize; let syv = (nx() % 2) as usize;
                    let lav = if nx() % 2 == 0 { sxv } else { (nx() % 32) as usize };
                    for i in 0..5 {
                        if kt >> i & 1 == 1 { sim.qubits[kt5[i].0 as usize] |= 1 << sh; }
                        if sxv >> i & 1 == 1 { sim.qubits[sx[i].0 as usize] |= 1 << sh; }
                        if lav >> i & 1 == 1 { sim.qubits[la[i].0 as usize] |= 1 << sh; }
                    }
                    for i in 0..k - 1 { if lb >> i & 1 == 1 { sim.qubits[lq[i].0 as usize] |= 1 << sh; } }
                    if syv == 1 { sim.qubits[sy.0 as usize] |= 1 << sh; }
                    st.push((kt, (0..k - 1).map(|i| (lb >> i & 1) as usize).collect::<Vec<_>>(), sxv, syv, lav));
                }
                sim.apply_iter(b.ops.iter());
                let mut want = 0u64;
                for (sh, (kt, lb, sxv, syv, lav)) in st.iter().enumerate() {
                    let mut jl = 0usize;
                    for j in 1..k { if j <= *kt && lb[j - 1] == 0 { jl = j; } }
                    let t = (*sxv + 64 - *syv - jl) & 31;
                    let x = (xv >> sh) & 1 == 1;
                    let g = !x && lav == sxv;
                    let ph = |m: u64, o: usize| ((m >> sh) & 1 == 1) && (t >> o & 1 == 1) && (true ^ x ^ g);
                    if ph(m0, 3) ^ ph(m1, 4) { want |= 1 << sh; fired += 1; }
                    n += 1;
                }
                if sim.phase != want { bad += (sim.phase ^ want).count_ones() as usize; }
                for (i, &q) in dirty.iter().enumerate() { if sim.qubits[q.0 as usize] != dirty0[i] { bad += 1000; } }
                for i in 0..5 { let _ = i; }
            }
        }
        eprintln!("B792 p11s stall: {n} shots, {fired} with phase, bad {bad}");
        assert!(fired > 100, "the test state must exercise the phase");
        if std::env::var_os("B792_BREAK").is_some() { assert!(bad > 0, "negative control did not break"); } else { assert_eq!(bad, 0); }
    }
    // ---------------------------------------------------------------------------------------------------------------------------------------------
    // b792 SWEEP kernel gate (lanes/b792sweep): nj_run with act gating (NjAct::{None, Lane, Pair}) and the gated-pend wrap, over the kernel's own input
    // space on classical states. Value, zero phase (or exactly the owed stall phase), and bit-for-bit restoration of every input lane, every borrowed
    // dirty lane (random per batch), X[W-1], the LA lanes, the act lane / the ACTFOLD pair; no extra qubit.
    #[derive(Clone, Copy, Default)]
    struct SwSt { kt: u8, lanes: u32, sx: u8, sy: u8, x: u8, a: u8, lav: u8, m: u8 }
    /// the rest of the state besides (lanes, kt): act code (Lane: f in 0..2; Pair: (l5, l6) in 0..4), sX, sY, X, LA value (gp), measured bits m (gp)
    fn sw_rests(mode: u8, gp: bool, skip: bool) -> Vec<SwSt> {
        let mut v = vec![];
        let acts: Vec<u8> = match mode { 0 => vec![0], 1 => vec![0, 1], _ => vec![0, 1, 2, 3] };
        for &a in &acts { for sx in 0..32u8 { for sy in 0..2u8 { for x in 0..2u8 {
            if !gp { v.push(SwSt { a, sx, sy, x, ..Default::default() }); continue; }
            // LA[0..5): equal to sX (eq 0) or differing in exactly one lane (eq 1..=5): a dropped LA literal is caught by the state that differs only there
            for eq in 0..6u8 { for hi in 0..(if mode == 2 { 1u8 } else if skip { 2u8 } else { 4u8 }) { for m in 0..4u8 {
                let low = if eq == 0 { sx } else { (sx ^ (1 << (eq - 1))) & 31 };
                v.push(SwSt { a, sx, sy, x, lav: low | (hi << 5), m, ..Default::default() });
            } } }
        } } } }
        v
    }
    /// run the circuit on the given states (64 per batch); returns the number of bad checks
    fn sw_batch_run(k: usize, mode: u8, gp: bool, skip: bool, st: &[SwSt]) -> usize {
        let mut b = B::new();
        let kt5 = b.alloc_n(5); let lq = b.alloc_n(k - 1); let sx = b.alloc_n(5); let sy = b.alloc(); let xt = b.alloc();
        let out = b.alloc_n(4); let dirty = b.alloc_n(k + 14); let la = b.alloc_n(7);
        let f = b.alloc();
        let mb = b.fresh_bits(2);
        let mut lanes = vec![NOQ]; lanes.extend(&lq);
        let act = match mode { 0 => NjAct::None, 1 => NjAct::Lane(f), _ => NjAct::Pair(la[5], la[6]) };
        // skip: LA[6] is a lent |0> host (slot 232 in the real build binds one LA lane fewer into the gate: n = 9 literals, not 10): it is skipped as a literal and holds 0
        let gpv = if gp { Some((if skip { vec![la[6]] } else { vec![] }, None)) } else { None };
        let pend = if gp { Some(mb.clone()) } else { None };
        let nq0 = b.width();
        // B792_SWEEP_ROOM0=1: the form the real build emits at room 0 (live == cap): phase_and takes its borrowed-lane form on u.dirty (set_borrowed), no ancilla
        // is allocated; without it the test builder has unlimited room and phase_and allocates its chain (the form the old stall test covered).
        let room0 = std::env::var_os("B792_SWEEP_ROOM0").is_some();
        // the real build: nj's bb (the k-th lane of the pool) is far from the borrowed prefix (k >= 19); at small k the prefix would contain it, so it is removed from the list
        if room0 { let mut bl = dirty.clone(); bl.remove(k.min(bl.len() - 1)); super::super::mask::set_borrowed(&bl); p2_set_cap(0); }
        nj_run(&mut b, k, &kt5, &lanes, xt, &sx, sy, &out, &dirty, &la, pend, gpv, act);
        if room0 { assert_eq!(b.width(), nq0, "nj_run allocated a qubit at room 0"); }
        let mut h = sha3::Shake256::default();
        sha3::digest::Update::update(&mut h, b"b792-sweep");
        let mut xof = sha3::digest::ExtendableOutput::finalize_xof(h);
        let mut rs: u64 = 0x2545_f491_4f6c_dd1d ^ (st.len() as u64);
        let mut nx = || { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; rs };
        let mut bad_total = 0usize;
        let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0]).filter(|&v| v != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1 + 8;
        for chunk in st.chunks(64) {
            let mut sim = Simulator::new(b.width() as usize, nbits, &mut xof);
            for &q in &dirty { sim.qubits[q.0 as usize] = nx(); }
            let dirty0: Vec<u64> = dirty.iter().map(|q| sim.qubits[q.0 as usize]).collect();
            for (sh, s) in chunk.iter().enumerate() {
                let set = |sim: &mut Simulator<'_, _>, q: QubitId, v: bool| { if v { sim.qubits[q.0 as usize] |= 1 << sh; } };
                for i in 0..5 { set(&mut sim, kt5[i], s.kt >> i & 1 == 1); set(&mut sim, sx[i], s.sx >> i & 1 == 1); }
                for i in 0..k - 1 { set(&mut sim, lq[i], s.lanes >> i & 1 == 1); }
                set(&mut sim, sy, s.sy == 1); set(&mut sim, xt, s.x == 1);
                match mode {
                    1 => set(&mut sim, f, s.a == 1),
                    2 => { set(&mut sim, la[5], s.a & 1 == 1); set(&mut sim, la[6], s.a >> 1 & 1 == 1); if !gp { for i in 0..5 { set(&mut sim, la[i], (s.lanes >> (i + 3)) & 1 == 1); } } }
                    _ => {}
                }
                if gp { for i in 0..(if mode == 2 { 5 } else { 7 }) { set(&mut sim, la[i], s.lav >> i & 1 == 1); } }
                if gp { if s.m & 1 == 1 { sim.bits[mb[0].0 as usize] |= 1 << sh; } if s.m >> 1 & 1 == 1 { sim.bits[mb[1].0 as usize] |= 1 << sh; } }
            }
            let snap: Vec<u64> = sim.qubits.clone();
            sim.apply_iter(b.ops.iter());
            let g = |sim: &Simulator<'_, _>, q: QubitId, sh: usize| ((sim.qubits[q.0 as usize] >> sh) & 1) as usize;
            let g0 = |q: QubitId, sh: usize| ((snap[q.0 as usize] >> sh) & 1) as usize;
            let mut want_phase = 0u64;
            for (sh, s) in chunk.iter().enumerate() {
                let (kt, lanes, sxv, syv) = (s.kt as usize, s.lanes, s.sx as usize, s.sy as usize);
                let mut jl = 0usize;
                for j in 1..k { if j <= kt && (lanes >> (j - 1)) & 1 == 0 { jl = j; } }
                let t = (sxv + 64 - syv - jl) & 31;
                let actv = match mode { 0 => true, 1 => s.a == 0, _ => s.a != 3 };
                let want = if actv { nj_f(t) } else { 0 };
                let got: usize = (0..4).map(|i| g(&sim, out[i], sh) << i).sum();
                if got != want { bad_total += 1; }
                for &q in kt5.iter().chain(lq.iter()).chain(sx.iter()).chain(la.iter()).chain([sy, xt, f].iter()) { if g(&sim, q, sh) != g0(q, sh) { bad_total += 1; } }
                if gp {
                    let x = s.x == 1;
                    let gg = !x && (s.lav & 31) == s.sx && if mode == 2 { s.a == 0 } else { (s.lav >> 5) == 0 };
                    let ph = |m: u8, o: usize| (m == 1) && actv && (t >> o & 1 == 1) && (true ^ x ^ gg);
                    if ph(s.m & 1, 3) ^ ph(s.m >> 1 & 1, 4) { want_phase |= 1 << sh; }
                }
            }
            // unused shots of a short last chunk carry |0..0> states: their phase is not predicted, mask to the used shots
            let used = if chunk.len() == 64 { !0u64 } else { (1u64 << chunk.len()) - 1 };
            if (sim.phase ^ want_phase) & used != 0 { bad_total += ((sim.phase ^ want_phase) & used).count_ones() as usize; }
            for (i, &q) in dirty.iter().enumerate() { if sim.qubits[q.0 as usize] != dirty0[i] { bad_total += 1000; } }
        }
        bad_total
    }
    /// product space driver, split over threads. full_rest: every (lanes, kt) x every rest; else (lanes x kt) with the rest index-strided (mixed)
    fn sw_drive(k: usize, mode: u8, gp: bool, skip: bool, lk: &[(u32, u8)], full_rest: bool, mix_stride: usize, threads: usize) -> (usize, u64) {
        let rests = sw_rests(mode, gp, skip);
        let nlk = if lk.is_empty() { (1u64 << (k - 1)) * 32 } else { lk.len() as u64 };
        let n: u64 = if full_rest { nlk * rests.len() as u64 } else { nlk };
        let per = (n + threads as u64 - 1) / threads as u64;
        let mk = |i: u64| -> SwSt {
            let (lki, ri) = if full_rest { (i % nlk, (i / nlk) as usize) } else { (i, (i as usize).wrapping_mul(mix_stride) % rests.len()) };
            let (l, t) = if lk.is_empty() { ((lki % (1u64 << (k - 1))) as u32, (lki >> (k - 1)) as u8) } else { lk[lki as usize] };
            let mut s = rests[ri]; s.kt = t; s.lanes = l; s
        };
        let total = std::sync::atomic::AtomicUsize::new(0);
        std::thread::scope(|sc| {
            for th in 0..threads as u64 {
                let (lo, hi) = (th * per, ((th + 1) * per).min(n));
                let total = &total; let mk = &mk;
                sc.spawn(move || {
                    let mut bad = 0usize;
                    let mut i = lo;
                    while i < hi {
                        let e = (i + (1u64 << 16)).min(hi);
                        let st: Vec<SwSt> = (i..e).map(|j| mk(j)).collect();
                        bad += sw_batch_run(k, mode, gp, skip, &st);
                        i = e;
                    }
                    total.fetch_add(bad, std::sync::atomic::Ordering::Relaxed);
                });
            }
        });
        (total.load(std::sync::atomic::Ordering::Relaxed), n)
    }
    fn sw_structured_lk(k: usize) -> Vec<(u32, u8)> {
        let full = (1u32 << (k - 1)) - 1;
        let mut pats = vec![full, 0];
        for i in 0..k - 1 { pats.push(full ^ (1 << i)); pats.push(1 << i); for j in i + 1..k - 1 { pats.push(full ^ (1 << i) ^ (1 << j)); } }
        pats.sort(); pats.dedup();
        let mut v = vec![]; for &p in &pats { for kt in 0..32u8 { v.push((p, kt)); } }
        v
    }
    /// B792_SWEEP_GATE=1 to run (B792_SWEEP_BIG=1 adds the full lanes x kt space with the rest mixed at k in {20, 21, 22}; B792_SWEEP_THREADS).
    /// Full cartesian product for k <= 11 and for the structured lane set (all-ones, all-zero, every single and double zero/one lane) at k in {19..22, 31}.
    /// Controls (build-time B792_BREAK): sw_pair (drops the pair term), sw_gate (drops act from bb on the Lane form), sw_row0 (row 0 ungated)
    #[test]
    fn b792_sweep_kernel() {
        if std::env::var_os("B792_SWEEP_GATE").is_none() { return; }
        let th = std::env::var("B792_SWEEP_THREADS").ok().and_then(|v| v.parse().ok()).unwrap_or(8usize);
        let big = std::env::var_os("B792_SWEEP_BIG").is_some();
        let mut bad_all = 0usize; let mut n_all = 0u64;
        for mode in 0..3u8 { for (gp, skip) in [(false, false), (true, false), (true, true)] {
            if mode == 2 && skip { continue; }
            for &k in &[2usize, 3, 5, 8, 11] {
                let (bad, n) = sw_drive(k, mode, gp, skip, &[], true, 1, th);
                eprintln!("sweep kernel k {k} mode {mode} gp {gp} skip {skip} FULL: {n} states bad {bad}");
                bad_all += bad; n_all += n;
            }
            for &k in &[19usize, 20, 21, 22, 31] {
                let lk = sw_structured_lk(k);
                let (bad, n) = sw_drive(k, mode, gp, skip, &lk, true, 1, th);
                eprintln!("sweep kernel k {k} mode {mode} gp {gp} skip {skip} STRUCT x rest: {n} states bad {bad}");
                bad_all += bad; n_all += n;
            }
            if big { for &k in &[20usize, 21, 22] {
                let (bad, n) = sw_drive(k, mode, gp, skip, &[], false, 7919, th);
                eprintln!("sweep kernel k {k} mode {mode} gp {gp} skip {skip} LANES x KT FULL, rest mixed: {n} states bad {bad}");
                bad_all += bad; n_all += n;
            } }
        } }
        eprintln!("B792 sweep kernel: {n_all} states, bad {bad_all}");
        if std::env::var_os("B792_BREAK").is_some() { assert!(bad_all > 0, "negative control did not break"); } else { assert_eq!(bad_all, 0); }
    }
    /// b793b GIPX: the extended tables on the 37 table states plus x = 0, t in {6, 13, 20, 27} (and the finishing t = 0 / 1 / 2 / 3 stay FPARK's); res1 lane after P1, rho / res0 / a1 / x after P2.
    #[test]
    fn b793_gipx_exhaustive() {
        for brk in 0..3usize {
            let mut b = B::new();
            let lanes_v = b.alloc_n(6);
            let dirty = b.alloc_n(4);
            let lanes: [QubitId; 6] = [lanes_v[0], lanes_v[1], lanes_v[2], lanes_v[3], lanes_v[4], lanes_v[5]];
            let n1 = B793_P1X.len() - (brk == 1) as usize;
            let n2 = B793_P2X.len() - (brk == 2) as usize;
            b793_mcx(&mut b, &lanes, &B793_P1X[..n1], &dirty);
            let mid = b.ops.len();
            b793_mcx(&mut b, &lanes, &B793_P2X[..n2], &dirty);
            let mut states: Vec<(usize, usize)> = (0..32).map(|t| (t, 1)).collect();
            states.extend([0usize, 7, 14, 21, 28, 6, 13, 20, 27].iter().map(|&t| (t, 0)));
            let mut h = sha3::Shake256::default();
            h.update(b"b793-gipx");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(b.width() as usize, 8, &mut xof);
            let mut rs: u64 = 0x1234_5678_9abc_def1;
            let mut nx = || { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; rs };
            for &q in &dirty { sim.qubits[q.0 as usize] = nx(); }
            let dirty0: Vec<u64> = dirty.iter().map(|q| sim.qubits[q.0 as usize]).collect();
            for (sh, &(t, x)) in states.iter().enumerate() {
                for i in 0..5 { if t >> i & 1 == 1 { sim.qubits[lanes[i].0 as usize] |= 1 << sh; } }
                if x == 1 { sim.qubits[lanes[5].0 as usize] |= 1 << sh; }
            }
            sim.apply_iter(b.ops[..mid].iter());
            let g = |sim: &Simulator<'_, _>, q: QubitId, sh: usize| ((sim.qubits[q.0 as usize] >> sh) & 1) as usize;
            let mut bad = 0usize;
            let mut codes: std::collections::HashMap<usize, (usize, usize, usize, usize)> = std::collections::HashMap::new();
            for (sh, &(t, x)) in states.iter().enumerate() {
                let (rho, a1) = super::super::greedyfrog_model::rho_of(t);
                let m = [8usize, 15, 22, 29].iter().filter(|&&c| t >= c).count();
                let res = if t >= 8 { m - 1 } else { 0 };
                if g(&sim, lanes[5], sh) != res >> 1 { bad += 1; }
                let code: usize = (0..5).map(|i| g(&sim, lanes[i], sh) << i).sum();
                let combo = (rho, a1 as usize, res & 1, x);
                if let Some(c) = codes.insert(code, combo) { if c != combo { bad += 1; } }
            }
            sim.qubits[lanes[5].0 as usize] = 0;
            sim.apply_iter(b.ops[mid..].iter());
            for (sh, &(t, x)) in states.iter().enumerate() {
                let (rho, a1) = super::super::greedyfrog_model::rho_of(t);
                let m = [8usize, 15, 22, 29].iter().filter(|&&c| t >= c).count();
                let res = if t >= 8 { m - 1 } else { 0 };
                let got_rho: usize = (0..3).map(|i| g(&sim, lanes[i], sh) << i).sum();
                if got_rho != rho || g(&sim, lanes[3], sh) != (res & 1) || g(&sim, lanes[4], sh) != a1 as usize || g(&sim, lanes[5], sh) != x { bad += 1; }
            }
            for (i, &q) in dirty.iter().enumerate() { if sim.qubits[q.0 as usize] != dirty0[i] { bad += 1000; } }
            if brk == 0 { assert_eq!(bad, 0, "GIPX tables wrong on {bad} checks"); } else { assert!(bad > 0, "negative control {brk} did not break"); }
            let t1: u64 = b.ops.iter().filter(|o| matches!(o.kind, crate::circuit::OperationType::CCX)).count() as u64;
            eprintln!("B793 gipx brk {brk}: bad {bad}, CCX {t1}");
        }
    }
    #[test]
    fn b793_gipfeli_exhaustive() {
        for brk in 0..3usize {
            let mut b = B::new();
            let lanes_v = b.alloc_n(6);
            let dirty = b.alloc_n(4);
            let lanes: [QubitId; 6] = [lanes_v[0], lanes_v[1], lanes_v[2], lanes_v[3], lanes_v[4], lanes_v[5]];
            let n1 = B793_P1.len() - (brk == 1) as usize;
            let n2 = B793_P2.len() - (brk == 2) as usize;
            b793_mcx(&mut b, &lanes, &B793_P1[..n1], &dirty);
            let mid = b.ops.len();
            b793_mcx(&mut b, &lanes, &B793_P2[..n2], &dirty);
            let mut states: Vec<(usize, usize)> = (0..32).map(|t| (t, 1)).collect();
            states.extend([0usize, 7, 14, 21, 28].iter().map(|&t| (t, 0)));
            assert_eq!(states.len(), 37);
            let mut h = sha3::Shake256::default();
            h.update(b"b793-gip");
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(b.width() as usize, 8, &mut xof);
            let mut rs: u64 = 0x1234_5678_9abc_def1;
            let mut nx = || { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; rs };
            for &q in &dirty { sim.qubits[q.0 as usize] = nx(); }
            let dirty0: Vec<u64> = dirty.iter().map(|q| sim.qubits[q.0 as usize]).collect();
            for (sh, &(t, x)) in states.iter().enumerate() {
                for i in 0..5 { if t >> i & 1 == 1 { sim.qubits[lanes[i].0 as usize] |= 1 << sh; } }
                if x == 1 { sim.qubits[lanes[5].0 as usize] |= 1 << sh; }
            }
            sim.apply_iter(b.ops[..mid].iter());
            let g = |sim: &Simulator<'_, _>, q: QubitId, sh: usize| ((sim.qubits[q.0 as usize] >> sh) & 1) as usize;
            let mut bad = 0usize;
            let mut codes: std::collections::HashMap<usize, (usize, usize, usize, usize)> = std::collections::HashMap::new();
            for (sh, &(t, x)) in states.iter().enumerate() {
                let (rho, a1) = super::super::greedyfrog_model::rho_of(t);
                let m = [8usize, 15, 22, 29].iter().filter(|&&c| t >= c).count();
                let res = if t >= 8 { m - 1 } else { 0 };
                if g(&sim, lanes[5], sh) != res >> 1 { bad += 1; }
                let code: usize = (0..5).map(|i| g(&sim, lanes[i], sh) << i).sum();
                let combo = (rho, a1 as usize, res & 1, x);
                if let Some(c) = codes.insert(code, combo) { if c != combo { bad += 1; } }
            }
            sim.qubits[lanes[5].0 as usize] = 0;
            sim.apply_iter(b.ops[mid..].iter());
            for (sh, &(t, x)) in states.iter().enumerate() {
                let (rho, a1) = super::super::greedyfrog_model::rho_of(t);
                let m = [8usize, 15, 22, 29].iter().filter(|&&c| t >= c).count();
                let res = if t >= 8 { m - 1 } else { 0 };
                let got_rho: usize = (0..3).map(|i| g(&sim, lanes[i], sh) << i).sum();
                if got_rho != rho || g(&sim, lanes[3], sh) != (res & 1) || g(&sim, lanes[4], sh) != a1 as usize || g(&sim, lanes[5], sh) != x { bad += 1; }
            }
            for (i, &q) in dirty.iter().enumerate() { if sim.qubits[q.0 as usize] != dirty0[i] { bad += 1000; } }
            if brk == 0 { assert_eq!(bad, 0, "Gipfeli tables wrong on {bad} (state, check) pairs"); } else { assert!(bad > 0, "negative control {brk} did not break the tables"); }
            let t1: u64 = b.ops.iter().filter(|o| matches!(o.kind, crate::circuit::OperationType::CCX)).count() as u64;
            eprintln!("B793 gipfeli brk {brk}: bad {bad}, CCX {t1}");
        }
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

#[cfg(test)]
mod i5_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{Update, ExtendableOutput};

    /// I5-LANES L2: the counter-form rho against the parent's prefix/parity definition on every (top 7 lanes, act, LA)
    /// for every (la_hb, la_gmin) the windows can produce, then the inverse recording erases r; temporaries |0>,
    /// phase 0. I5_RCNT_BREAK=1/2 (negative controls) must fail.
    #[test]
    fn i5_rcnt_exhaustive() {
        let mut checked = 0u64;
        let mut bad = 0u64;
        for hb in 3..=LB_BITS {
            for gmin in 1..=7usize {
                let mut b = B::new();
                let x = b.alloc_n(W);
                let la = b.alloc_n(LB_BITS);
                let act = b.alloc();
                let r = b.alloc_n(RHO_BITS);
                let gate: GateSpec = if gmin < 7 { Some((&la, hb, gmin)) } else { None };
                let (rec, lanes) = i5_rho_counter(&mut b, &x, Some(act), &r, gate);
                b.play(&rec, false);
                let mid = b.ops.len();
                b.play(&rec, true);
                b.free_n(&lanes);
                let shots: Vec<(u32, u32, u32)> = (0..128u32).flat_map(|t| (0..2u32).flat_map(move |a| (0..(1u32 << hb)).map(move |l| (t, a, l)))).collect();
                for chunk in shots.chunks(64) {
                    let mut h = sha3::Shake256::default();
                    h.update(b"i5-rcnt");
                    let mut xof = h.finalize_xof();
                    let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0]).filter(|&v| v != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1;
                    let mut sim = Simulator::new(b.width() as usize, nbits, &mut xof);
                    for (i, &(t, a, l)) in chunk.iter().enumerate() {
                        for k in 0..7 { if t >> k & 1 == 1 { sim.qubits[x[W - 1 - k].0 as usize] |= 1 << i; } }
                        if a == 1 { sim.qubits[act.0 as usize] |= 1 << i; }
                        for k in 0..LB_BITS { if l >> k & 1 == 1 { sim.qubits[la[k].0 as usize] |= 1 << i; } }
                    }
                    sim.apply_iter(b.ops[..mid].iter());
                    for (i, &(t, a, l)) in chunk.iter().enumerate() {
                        // parent definition: p_j = act & top j+1 lanes zero; p'_j = p_j & [LA > j] for j >= gmin
                        let pp: Vec<bool> = (0..7).map(|j| {
                            let pj = a == 1 && (0..=j).all(|k| t >> k & 1 == 0);
                            pj && (j < gmin || l as usize > j)
                        }).collect();
                        let mut want = 0u32;
                        for k in 0..3 { if SHIFT_PREFIXES[k].iter().fold(false, |acc, &j| acc ^ pp[j]) { want |= 1 << k; } }
                        let got: u32 = (0..3).map(|k| ((sim.qubits[r[k].0 as usize] >> i & 1) as u32) << k).sum();
                        let dirty = lanes.iter().any(|q| sim.qubits[q.0 as usize] >> i & 1 == 1);
                        if got != want || dirty { bad += 1; }
                        checked += 1;
                    }
                    sim.apply_iter(b.ops[mid..].iter());
                    let rl = r.iter().chain(&lanes).fold(0u64, |acc, q| acc | sim.qubits[q.0 as usize]);
                    if rl != 0 || sim.phase != 0 { bad += chunk.len() as u64; }
                }
            }
        }
        eprintln!("I5 RCNT exhaustive: {checked} cases, {bad} bad");
        assert_eq!(bad, 0);
    }

    /// I5-LANES L4: the split-carry small add / subtract against t +- s mod 2^n on every (t, s), n = 9, k = 1..5;
    /// carry lane and temporaries |0>, phase 0. I5_SPLIT_BREAK (negative control) must fail.
    #[test]
    fn i5_split_exhaustive() {
        let n = 9usize;
        let (mut checked, mut bad) = (0u64, 0u64);
        for k in 1..=5usize {
            for sub in [false, true] {
                let mut b = B::new();
                let t = b.alloc_n(n);
                let sq = b.alloc_n(k);
                let w0 = b.width();
                i5_add_split(&mut b, &t, &sq, sub);
                let cases: Vec<(u32, u32)> = (0..(1u32 << n)).flat_map(|x| (0..(1u32 << k)).map(move |y| (x, y))).collect();
                for chunk in cases.chunks(64) {
                    let mut h = sha3::Shake256::default();
                    h.update(b"i5-split");
                    let mut xof = h.finalize_xof();
                    let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0]).filter(|&v| v != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1;
                    let mut sim = Simulator::new(b.width() as usize, nbits, &mut xof);
                    for (i, &(x, y)) in chunk.iter().enumerate() {
                        for j in 0..n { if x >> j & 1 == 1 { sim.qubits[t[j].0 as usize] |= 1 << i; } }
                        for j in 0..k { if y >> j & 1 == 1 { sim.qubits[sq[j].0 as usize] |= 1 << i; } }
                    }
                    sim.apply_iter(b.ops.iter());
                    let scratch = (w0..b.width()).fold(0u64, |a, q| a | sim.qubits[q as usize]);
                    for (i, &(x, y)) in chunk.iter().enumerate() {
                        let want = if sub { x.wrapping_sub(y) } else { x + y } & ((1 << n) - 1);
                        let got: u32 = (0..n).map(|j| ((sim.qubits[t[j].0 as usize] >> i & 1) as u32) << j).sum();
                        let gs: u32 = (0..k).map(|j| ((sim.qubits[sq[j].0 as usize] >> i & 1) as u32) << j).sum();
                        if got != want || gs != y || scratch >> i & 1 == 1 || sim.phase >> i & 1 == 1 { bad += 1; }
                        checked += 1;
                    }
                }
            }
        }
        eprintln!("I5 SPLIT exhaustive: {checked} cases, {bad} bad");
        assert_eq!(bad, 0);
    }
}

#[cfg(test)]
mod r9_rowtmp_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{Update, ExtendableOutput};

    /// R9 rowtmp c, the identity behind the act elision: the inverse slot's rho / res decoder (`r4_decode`, both the
    /// R12_DECODE_PERM gate list and the legacy form) on every 5-bit t (borrowed lanes random): e = [t < 8], rho = the
    /// model's rho_of(t), borrowed lanes restored, and (e, rho) != (0, 0) on every t (t = 0 gives (1, 0)). Finished
    /// shots decode t = 0 and fold a1 = e ^ 1 = 0, so act = a1 | (rho != 0) on every shot. Run with --test-threads=1.
    #[test]
    fn r9_decode_identity() {
        for perm in [true, false] {
            if perm { std::env::set_var("R12_DECODE_PERM", "1"); } else { std::env::remove_var("R12_DECODE_PERM"); }
            for round in 0..8u64 {
                let mut b = B::new();
                let j = b.alloc_n(R_BITS);
                let e = b.alloc();
                let d = b.alloc_n(4);
                super::super::mask::set_borrowed(&d);
                r4_decode(&mut b, &j, e);
                super::super::mask::set_borrowed(&[]);
                let mut h = sha3::Shake256::default();
                h.update(b"r9-decode");
                h.update(&[perm as u8, round as u8]);
                let mut xof = h.finalize_xof();
                let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0]).filter(|&v| v != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1;
                let mut sim = Simulator::new(b.width() as usize, nbits.max(1), &mut xof);
                let mut rng = 0x9e37_79b9_7f4a_7c15u64 ^ round.wrapping_mul(0x5851_f42d_4c95_7f2d);
                let mut dinit = vec![];
                for &q in &d { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; sim.qubits[q.0 as usize] = rng; dinit.push(rng); }
                // shots 0..31: t = shot; 32..63: t = shot - 32 again (other dirty bits)
                for s in 0..64usize { let t = s % 32; for k in 0..R_BITS { if t >> k & 1 == 1 { sim.qubits[j[k].0 as usize] |= 1 << s; } } }
                sim.apply_iter(b.ops.iter());
                for s in 0..64usize {
                    let t = s % 32;
                    let ev = sim.qubits[e.0 as usize] >> s & 1;
                    let rho: usize = (0..RHO_BITS).map(|k| ((sim.qubits[j[k].0 as usize] >> s & 1) as usize) << k).sum();
                    let (mrho, ma1) = super::super::greedyfrog_model::rho_of(t);
                    assert_eq!(ev == 1, t < 8, "perm {perm} t {t}: e");
                    assert_eq!(ev == 1, ma1, "perm {perm} t {t}: e vs model a1");
                    assert_eq!(rho, mrho, "perm {perm} t {t}: rho");
                    assert!(ev == 1 || rho != 0, "perm {perm} t {t}: (e, rho) = (0, 0)");
                    if t == 0 { assert!(ev == 1 && rho == 0); }
                }
                for (i, &q) in d.iter().enumerate() { assert_eq!(sim.qubits[q.0 as usize], dinit[i], "perm {perm}: borrowed lane not restored"); }
            }
        }
        std::env::set_var("R12_DECODE_PERM", "1");
        eprintln!("R9 decode identity: 2 decoders x 32 t x 8 rounds ok");
    }

    /// R9 rowtmp c, the un-renormalisation with act released: the forward counter (act a lane) gives r = rho; act is
    /// then erased as the slot does (X, act ^= AND(!a1, !r)) and the inverse counter with `el` = a1 must leave r = 0,
    /// its temporaries |0>, phase 0, and t = act, on every (top 7 lanes, act, LA, a1) with a1 consistent with act and rho
    /// (act = 0: a1 = 0; act = 1, rho = 0: a1 = 1; else either), for every (la_hb, la_gmin). R9_RT_BREAK=c3 must fail.
    #[test]
    fn r9_rcnt_el_exhaustive() {
        let (mut checked, mut bad) = (0u64, 0u64);
        for hb in 3..=LB_BITS {
            for gmin in 1..=7usize {
                let mut b = B::new();
                let x = b.alloc_n(W);
                let la = b.alloc_n(LB_BITS);
                let act = b.alloc();
                let a1 = b.alloc();
                let r = b.alloc_n(RHO_BITS);
                let gate: GateSpec = if gmin < 7 { Some((&la, hb, gmin)) } else { None };
                let (rec, lanes) = i5_rho_counter(&mut b, &x, Some(act), &r, gate);
                b.play(&rec, false);
                b.free_n(&lanes);
                b.x(act);
                let lits = [(a1, true), (r[0], true), (r[1], true), (r[2], true)];
                and_into(&mut b, &lits, act);
                let mid = b.ops.len();
                let (rec2, lanes2, t) = i5_rho_counter_x(&mut b, &x, None, &r, gate, Some(a1));
                b.play(&rec2, true);
                let rest: Vec<QubitId> = lanes2.iter().copied().filter(|&q| q != t).collect();
                let rho_def = |tt: u32, a: u32, l: u32| -> u32 {
                    let pp: Vec<bool> = (0..7).map(|jj| {
                        let pj = a == 1 && (0..=jj).all(|k| tt >> k & 1 == 0);
                        pj && (jj < gmin || l as usize > jj)
                    }).collect();
                    let mut want = 0u32;
                    for k in 0..3 { if SHIFT_PREFIXES[k].iter().fold(false, |acc, &jj| acc ^ pp[jj]) { want |= 1 << k; } }
                    want
                };
                let mut shots: Vec<(u32, u32, u32, u32)> = vec![];
                for tt in 0..128u32 { for a in 0..2u32 { for l in 0..(1u32 << hb) {
                    let rho = rho_def(tt, a, l);
                    let a1s: Vec<u32> = if a == 0 { vec![0] } else if rho == 0 { vec![1] } else { vec![0, 1] };
                    for a1v in a1s { shots.push((tt, a, l, a1v)); }
                } } }
                for chunk in shots.chunks(64) {
                    let mut h = sha3::Shake256::default();
                    h.update(b"r9-rcnt-el");
                    let mut xof = h.finalize_xof();
                    let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0]).filter(|&v| v != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1;
                    let mut sim = Simulator::new(b.width() as usize, nbits.max(1), &mut xof);
                    for (i, &(tt, a, l, a1v)) in chunk.iter().enumerate() {
                        for k in 0..7 { if tt >> k & 1 == 1 { sim.qubits[x[W - 1 - k].0 as usize] |= 1 << i; } }
                        if a == 1 { sim.qubits[act.0 as usize] |= 1 << i; }
                        if a1v == 1 { sim.qubits[a1.0 as usize] |= 1 << i; }
                        for k in 0..LB_BITS { if l >> k & 1 == 1 { sim.qubits[la[k].0 as usize] |= 1 << i; } }
                    }
                    sim.apply_iter(b.ops[..mid].iter());
                    let act_left = sim.qubits[act.0 as usize];
                    sim.apply_iter(b.ops[mid..].iter());
                    let rl = r.iter().chain(&rest).fold(0u64, |acc, q| acc | sim.qubits[q.0 as usize]);
                    for (i, &(_, a, _, a1v)) in chunk.iter().enumerate() {
                        let tv = sim.qubits[t.0 as usize] >> i & 1;
                        let a1g = sim.qubits[a1.0 as usize] >> i & 1;
                        if act_left >> i & 1 == 1 || rl >> i & 1 == 1 || sim.phase >> i & 1 == 1 || tv != a as u64 || a1g != a1v as u64 { bad += 1; }
                        checked += 1;
                    }
                }
            }
        }
        eprintln!("R9 RCNT-EL exhaustive: {checked} cases, {bad} bad");
        assert_eq!(bad, 0);
    }
}

#[cfg(test)]
mod m94_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{Update, ExtendableOutput};

    fn rho_def(gmin: usize, tt: u32, a: u32, l: u32) -> u32 {
        let pp: Vec<bool> = (0..7).map(|jj| {
            let pj = a == 1 && (0..=jj).all(|k| tt >> k & 1 == 0);
            pj && (jj < gmin || l as usize > jj)
        }).collect();
        let mut want = 0u32;
        for k in 0..3 { if SHIFT_PREFIXES[k].iter().fold(false, |acc, &jj| acc ^ pp[jj]) { want |= 1 << k; } }
        want
    }

    /// R14 misc94 "DonRwetter" u: the lean rho counter (one clean temporary fewer, borrowed lanes for the widest AND)
    /// against the definition on every (top 7 lanes, act, LA < 2^hb) for every (la_hb, la_gmin), with random borrowed
    /// lanes: after the forward play r = rho and every counter lane |0>; after the inverse play r = 0, phase 0 and the
    /// borrowed lanes restored. Also: the lean form holds exactly one lane fewer where it applies. R14_M94_BREAK=u must
    /// fail (run alone: `cargo test m94_lean_counter -- --test-threads=1`).
    #[test]
    fn m94_lean_counter_exhaustive() {
        let (mut checked, mut bad, mut lean_forms) = (0u64, 0u64, 0u64);
        for hb in 3..=LB_BITS {
            for gmin in 1..=7usize {
                let mut b = B::new();
                let x = b.alloc_n(W);
                let la = b.alloc_n(LB_BITS);
                let act = b.alloc();
                let r = b.alloc_n(RHO_BITS);
                let d = b.alloc_n(8);
                super::super::mask::set_borrowed(&d);
                let gate: GateSpec = if gmin < 7 { Some((&la, hb, gmin)) } else { None };
                let (_, lanes0) = i5_rho_counter(&mut b, &x, Some(act), &r, gate);
                b.free_n(&lanes0);
                let n0 = b.ops.len();
                let (rec, lanes) = m94_lean(true, || i5_rho_counter(&mut b, &x, Some(act), &r, gate));
                super::super::mask::set_borrowed(&[]);
                assert_eq!(b.ops.len(), n0);
                if lanes.len() + 1 == lanes0.len() { lean_forms += 1; } else { assert_eq!(lanes.len(), lanes0.len()); }
                b.play(&rec, false);
                let mid = b.ops.len();
                b.play(&rec, true);
                b.free_n(&lanes);
                let shots: Vec<(u32, u32, u32)> = (0..128u32).flat_map(|t| (0..2u32).flat_map(move |a| (0..(1u32 << hb)).map(move |l| (t, a, l)))).collect();
                for (ci, chunk) in shots.chunks(64).enumerate() {
                    let mut h = sha3::Shake256::default();
                    h.update(b"m94-lean");
                    let mut xof = h.finalize_xof();
                    let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0]).filter(|&v| v != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1;
                    let mut sim = Simulator::new(b.width() as usize, nbits.max(1), &mut xof);
                    let mut rng = 0x9e37_79b9_7f4a_7c15u64 ^ ((hb * 8 + gmin) as u64).wrapping_mul(0x5851_f42d_4c95_7f2d) ^ ci as u64;
                    let mut dinit = vec![];
                    for &q in &d { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; sim.qubits[q.0 as usize] = rng; dinit.push(rng); }
                    for (i, &(t, a, l)) in chunk.iter().enumerate() {
                        for k in 0..7 { if t >> k & 1 == 1 { sim.qubits[x[W - 1 - k].0 as usize] |= 1 << i; } }
                        if a == 1 { sim.qubits[act.0 as usize] |= 1 << i; }
                        for k in 0..LB_BITS { if l >> k & 1 == 1 { sim.qubits[la[k].0 as usize] |= 1 << i; } }
                    }
                    sim.apply_iter(b.ops[..mid].iter());
                    let dl = lanes.iter().fold(0u64, |acc, q| acc | sim.qubits[q.0 as usize]);
                    let dd = d.iter().enumerate().fold(0u64, |acc, (k, q)| acc | (sim.qubits[q.0 as usize] ^ dinit[k]));
                    for (i, &(t, a, l)) in chunk.iter().enumerate() {
                        let got: u32 = (0..3).map(|k| ((sim.qubits[r[k].0 as usize] >> i & 1) as u32) << k).sum();
                        if got != rho_def(gmin, t, a, l) || dl >> i & 1 == 1 || dd >> i & 1 == 1 { bad += 1; }
                        checked += 1;
                    }
                    sim.apply_iter(b.ops[mid..].iter());
                    let rl = r.iter().chain(&lanes).fold(0u64, |acc, q| acc | sim.qubits[q.0 as usize]);
                    let dd = d.iter().enumerate().fold(0u64, |acc, (k, q)| acc | (sim.qubits[q.0 as usize] ^ dinit[k]));
                    if rl != 0 || sim.phase != 0 || dd != 0 { bad += chunk.len() as u64; }
                }
            }
        }
        eprintln!("M94 lean counter exhaustive: {checked} cases, {lean_forms} lean forms, {bad} bad");
        assert!(lean_forms >= 1);
        assert_eq!(bad, 0);
    }

    /// R14 misc94 r (the forward renormalisation's lean counter, act absent on act-constant slots): as
    /// `m94_lean_counter_exhaustive` with act = None (the shots' act is 1), forward play r = rho, every counter lane |0>,
    /// inverse play r = 0, phase 0, borrowed lanes restored.
    #[test]
    fn m94_lean_counter_noact_exhaustive() {
        let (mut checked, mut bad, mut lean_forms) = (0u64, 0u64, 0u64);
        for hb in 3..=LB_BITS {
            for gmin in 1..=7usize {
                let mut b = B::new();
                let x = b.alloc_n(W);
                let la = b.alloc_n(LB_BITS);
                let r = b.alloc_n(RHO_BITS);
                let d = b.alloc_n(8);
                super::super::mask::set_borrowed(&d);
                let gate: GateSpec = if gmin < 7 { Some((&la, hb, gmin)) } else { None };
                let (_, lanes0) = i5_rho_counter(&mut b, &x, None, &r, gate);
                b.free_n(&lanes0);
                let (rec, lanes) = m94_lean(true, || i5_rho_counter(&mut b, &x, None, &r, gate));
                super::super::mask::set_borrowed(&[]);
                if lanes.len() + 1 == lanes0.len() { lean_forms += 1; } else { assert_eq!(lanes.len(), lanes0.len()); }
                b.play(&rec, false);
                let mid = b.ops.len();
                b.play(&rec, true);
                b.free_n(&lanes);
                let shots: Vec<(u32, u32)> = (0..128u32).flat_map(|t| (0..(1u32 << hb)).map(move |l| (t, l))).collect();
                for (ci, chunk) in shots.chunks(64).enumerate() {
                    let mut h = sha3::Shake256::default();
                    h.update(b"m94-lean-noact");
                    let mut xof = h.finalize_xof();
                    let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0]).filter(|&v| v != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1;
                    let mut sim = Simulator::new(b.width() as usize, nbits.max(1), &mut xof);
                    let mut rng = 0x6a09_e667_f3bc_c908u64 ^ ((hb * 8 + gmin) as u64).wrapping_mul(0x5851_f42d_4c95_7f2d) ^ ci as u64;
                    let mut dinit = vec![];
                    for &q in &d { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; sim.qubits[q.0 as usize] = rng; dinit.push(rng); }
                    for (i, &(t, l)) in chunk.iter().enumerate() {
                        for k in 0..7 { if t >> k & 1 == 1 { sim.qubits[x[W - 1 - k].0 as usize] |= 1 << i; } }
                        for k in 0..LB_BITS { if l >> k & 1 == 1 { sim.qubits[la[k].0 as usize] |= 1 << i; } }
                    }
                    sim.apply_iter(b.ops[..mid].iter());
                    let dl = lanes.iter().fold(0u64, |acc, q| acc | sim.qubits[q.0 as usize]);
                    let dd = d.iter().enumerate().fold(0u64, |acc, (k, q)| acc | (sim.qubits[q.0 as usize] ^ dinit[k]));
                    for (i, &(t, l)) in chunk.iter().enumerate() {
                        let got: u32 = (0..3).map(|k| ((sim.qubits[r[k].0 as usize] >> i & 1) as u32) << k).sum();
                        if got != rho_def(gmin, t, 1, l) || dl >> i & 1 == 1 || dd >> i & 1 == 1 { bad += 1; }
                        checked += 1;
                    }
                    sim.apply_iter(b.ops[mid..].iter());
                    let rl = r.iter().chain(&lanes).fold(0u64, |acc, q| acc | sim.qubits[q.0 as usize]);
                    let dd = d.iter().enumerate().fold(0u64, |acc, (k, q)| acc | (sim.qubits[q.0 as usize] ^ dinit[k]));
                    if rl != 0 || sim.phase != 0 || dd != 0 { bad += chunk.len() as u64; }
                }
            }
        }
        eprintln!("M94 lean counter (act None) exhaustive: {checked} cases, {lean_forms} lean forms, {bad} bad");
        assert!(lean_forms >= 1);
        assert_eq!(bad, 0);
    }

    /// R14 misc94 u on the R9 rowtmp c form: as `r9_rcnt_el_exhaustive` with the inverse counter (el = a1) recorded lean
    /// and random borrowed lanes: r = 0, its temporaries |0>, phase 0, t = act, a1 and the borrowed lanes unchanged.
    #[test]
    fn m94_lean_el_exhaustive() {
        let (mut checked, mut bad, mut lean_forms) = (0u64, 0u64, 0u64);
        for hb in 3..=LB_BITS {
            for gmin in 1..=7usize {
                let mut b = B::new();
                let x = b.alloc_n(W);
                let la = b.alloc_n(LB_BITS);
                let act = b.alloc();
                let a1 = b.alloc();
                let r = b.alloc_n(RHO_BITS);
                let d = b.alloc_n(8);
                super::super::mask::set_borrowed(&d);
                let gate: GateSpec = if gmin < 7 { Some((&la, hb, gmin)) } else { None };
                let (rec, lanes) = i5_rho_counter(&mut b, &x, Some(act), &r, gate);
                b.play(&rec, false);
                b.free_n(&lanes);
                b.x(act);
                let lits = [(a1, true), (r[0], true), (r[1], true), (r[2], true)];
                and_into(&mut b, &lits, act);
                let mid = b.ops.len();
                let (_, lanes0, _) = i5_rho_counter_x(&mut b, &x, None, &r, gate, Some(a1));
                b.free_n(&lanes0);
                let (rec2, lanes2, t) = m94_lean(true, || i5_rho_counter_x(&mut b, &x, None, &r, gate, Some(a1)));
                super::super::mask::set_borrowed(&[]);
                if lanes2.len() + 1 == lanes0.len() { lean_forms += 1; } else { assert_eq!(lanes2.len(), lanes0.len()); }
                b.play(&rec2, true);
                let rest: Vec<QubitId> = lanes2.iter().copied().filter(|&q| q != t).collect();
                let mut shots: Vec<(u32, u32, u32, u32)> = vec![];
                for tt in 0..128u32 { for a in 0..2u32 { for l in 0..(1u32 << hb) {
                    let rho = rho_def(gmin, tt, a, l);
                    let a1s: Vec<u32> = if a == 0 { vec![0] } else if rho == 0 { vec![1] } else { vec![0, 1] };
                    for a1v in a1s { shots.push((tt, a, l, a1v)); }
                } } }
                for (ci, chunk) in shots.chunks(64).enumerate() {
                    let mut h = sha3::Shake256::default();
                    h.update(b"m94-lean-el");
                    let mut xof = h.finalize_xof();
                    let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0]).filter(|&v| v != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1;
                    let mut sim = Simulator::new(b.width() as usize, nbits.max(1), &mut xof);
                    let mut rng = 0x2545_f491_4f6c_dd1du64 ^ ((hb * 8 + gmin) as u64).wrapping_mul(0x5851_f42d_4c95_7f2d) ^ ci as u64;
                    let mut dinit = vec![];
                    for &q in &d { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; sim.qubits[q.0 as usize] = rng; dinit.push(rng); }
                    for (i, &(tt, a, l, a1v)) in chunk.iter().enumerate() {
                        for k in 0..7 { if tt >> k & 1 == 1 { sim.qubits[x[W - 1 - k].0 as usize] |= 1 << i; } }
                        if a == 1 { sim.qubits[act.0 as usize] |= 1 << i; }
                        if a1v == 1 { sim.qubits[a1.0 as usize] |= 1 << i; }
                        for k in 0..LB_BITS { if l >> k & 1 == 1 { sim.qubits[la[k].0 as usize] |= 1 << i; } }
                    }
                    sim.apply_iter(b.ops[..mid].iter());
                    let act_left = sim.qubits[act.0 as usize];
                    sim.apply_iter(b.ops[mid..].iter());
                    let rl = r.iter().chain(&rest).fold(0u64, |acc, q| acc | sim.qubits[q.0 as usize]);
                    let dd = d.iter().enumerate().fold(0u64, |acc, (k, q)| acc | (sim.qubits[q.0 as usize] ^ dinit[k]));
                    for (i, &(_, a, _, a1v)) in chunk.iter().enumerate() {
                        let tv = sim.qubits[t.0 as usize] >> i & 1;
                        let a1g = sim.qubits[a1.0 as usize] >> i & 1;
                        if act_left >> i & 1 == 1 || rl >> i & 1 == 1 || sim.phase >> i & 1 == 1 || tv != a as u64 || a1g != a1v as u64 || dd >> i & 1 == 1 { bad += 1; }
                        checked += 1;
                    }
                }
            }
        }
        eprintln!("M94 lean RCNT-EL exhaustive: {checked} cases, {lean_forms} lean forms, {bad} bad");
        assert!(lean_forms >= 1);
        assert_eq!(bad, 0);
    }
}
