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
/// the buyback paired with the NB 28 -> 27 sell (lambda-neutral swap)
pub const NSLOTS: usize = 256; // STALL-PAIR: a stall spends one more slot; 254 + 2 keeps lambda neutral (paired emulator)
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
/// STALL-PAIR: the ordinary ladder lanes write with no a1 gate. A shot that does not step (a stall or a finished shot)
/// still takes the ungated write on those lanes, so it spends two slots: a "fake" slot (no d, no rotation, no swap) whose
/// ladders write only the ordinary lanes (the masked cells stay off on a1 = 0 shots, MASKED_WRITE_ALWAYS's mark), and the
/// next slot, the "add-back", which runs the same ladders in the complement frame of those lanes and restores them,
/// then rotates and swaps as a stall did. A governor-held shot does the same with no rotation. On a fake slot's post-state
/// the decode is gated off: rho, a1 and the swap flag by !ns, and Y's bottom normalisation by !ns, so the junk sum on Y's
/// lanes cannot break the hosted lanes' promises (sY = 0, kt = LA + sX - LB). One flag lane `sf` carries "this slot is an
/// add-back" across slot boundaries.
/// With s = the flag on entry and ns = the flag on exit, exactly one of (a1, s, ns) holds on every shot, so
/// ns = !(s ^ a1): the lane is rewritten in place on both traversals and nothing is measured for it. The last slot is
/// gated by a1 | s instead (no fake there): a passing shot's s there is !a1 & !(finished & counter odd).
pub const STALL_PAIR: bool = true;
pub(crate) fn stall_pair() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("STALL_PAIR", STALL_PAIR)); *E }
/// Slots whose ladders run with no write gate on the ordinary lanes (slot 0 has a1 = 1 on every shot anyway).
fn stall_free(w: &Win) -> bool { stall_pair() && w.slot >= 1 && !w.last }
/// Negative controls for the gate tests only (SP_BREAK=k): 1 no complement-frame flip on the add-back, 2 the decode's
/// rho / a1 are not gated by the fake flag, 3 the forward's swap flag is not gated, 4 the counter lanes are not protected
/// on finished shots.
fn sp_break(k: u32) -> bool {
    cfg!(test) && std::env::var("SP_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
/// STALL-PAIR value ladder of a slot: the masked prefix's end, the flag toggles and the add-back's lanes. A fake at slot s
/// and its add-back at s + 1 write the same lanes X[pv(s)..W), pv(s) above both slots' masked windows: the lanes between a
/// slot's window and the lanes all three kinds write (step, fake, add-back) run as masked cells, with f turned on where
/// that kind's lanes start (a stepping shot's f is on there already).
fn sp_value(u: &GreedyFrog, w: &Win, fr: bool, si: Option<QubitId>, a1: QubitId, ap: Option<QubitId>) -> (super::mask::LadX, Vec<QubitId>) {
    let base = W - w.lb.1;
    let mut o = W - w.lb.0 + 1;
    if fr { o = o.max(w.pv); }
    if si.is_some() { o = o.max(w.pvp); }
    let mut togs = vec![];
    if fr && w.pv < o {
        let mut c = vec![ap.unwrap_or(a1)];
        c.extend(si);
        togs.push((w.pv - base, c, ap.is_none()));
    }
    if let (Some(q), true) = (si, w.pvp < o) {
        togs.push((w.pvp - base, vec![q], false));
    }
    let mut fix = vec![];
    if fr && w.pv >= o {
        let mut c = vec![ap.unwrap_or(a1)];
        c.extend(si);
        fix.push((c, ap.is_none()));
    }
    if let (Some(q), true) = (si, w.pvp >= o) { fix.push((vec![q], false)); }
    let flips = if si.is_some() { u.x[w.pvp..W].to_vec() } else { vec![] };
    (super::mask::LadX { ext: o - base, togs, fix: (fr && w.act_const).then_some(fix) }, flips)
}
/// STALL-PAIR cofactor ladder of a slot, as `sp_value`: a fake at slot s and its add-back write Y[..=jc(s)].
fn sp_cof(u: &GreedyFrog, w: &Win, fr: bool, si: Option<QubitId>, a1: QubitId, ap: Option<QubitId>) -> (super::mask::LadX, Vec<QubitId>) {
    let lo = w.lad.0 as isize;
    let l_of = |j: isize| (CW as isize - 1 - lo - j) as usize;
    let mut o = CW as isize - 2 - w.lad.1 as isize;
    if fr { o = o.min(w.jc); }
    if si.is_some() { o = o.min(w.jcp); }
    let mut togs = vec![];
    if fr && w.jc > o && w.jc >= 0 {
        let mut c = vec![ap.unwrap_or(a1)];
        c.extend(si);
        togs.push((l_of(w.jc), c, ap.is_none()));
    }
    if let (Some(q), true) = (si, w.jcp > o && w.jcp >= 0) {
        togs.push((l_of(w.jcp), vec![q], false));
    }
    let mut fix = vec![];
    if fr && !(w.jc > o && w.jc >= 0) {
        let mut c = vec![ap.unwrap_or(a1)];
        c.extend(si);
        fix.push((c, ap.is_none()));
    }
    if let (Some(q), false) = (si, w.jcp > o && w.jcp >= 0) { fix.push((vec![q], false)); }
    let flips = if si.is_some() && w.jcp >= 0 { u.y[..=w.jcp as usize].to_vec() } else { vec![] };
    (super::mask::LadX { ext: l_of(o), togs, fix: (fr && w.act_const).then_some(fix) }, flips)
}
/// Ladder lanes [m..] flip in the add-back's complement frame (Clifford).
fn sp_flip(b: &mut B, sl: Option<QubitId>, t: &[QubitId]) {
    let Some(q) = sl else { return };
    if sp_break(1) { return; }
    for &l in t { b.cx(q, l); }
}

/// CK-LADDER: the inverse ladders' ordinary lanes on a segmented carry chain whose anchors erase by measurement, at
/// 1.5 expected Toffoli per lane past the pool instead of the Cuccaro fallback's 2 (mask.rs `ck_ordinary`). Runs where the
/// ordinary lanes have no write gate (STALL-PAIR's free slots). K2's masked bank takes the lanes past the chain's minimum
/// (a banked masked lane saves 1 Toffoli, a pool lane 1/2).
pub const CK_LADDER: bool = false; // persona-mochimodev Q820: off (its room-sized plan moves classical support when the cap drops)
pub(crate) fn ck_split() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("CK_SPLIT", true)); *E }
fn ck_ladder() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("CK_LADDER", CK_LADDER)); *E }
/// One inverse ladder pass on CK-LADDER where it fits; false: the caller runs the plain pass.
/// ORD-DEC threshold 5 (390668eb; 6 before). Dev override `WL_ORD_DEC5=0|1`.
fn ord_dec_th() -> usize { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("ORD_DEC5", true)); if *E { 5 } else { 6 } }
fn ck_try(b: &mut B, u: &GreedyFrog, t: &[QubitId], s: &[QubitId], src: Src, m: &Masked, cmpl: bool, roll: Option<&RollRec>,
          nc: bool, top: impl FnOnce(&mut B, QubitId)) -> bool {
    if !ck_ladder() || !super::mask::ord_gate_free() { return false; }
    let srcs = [src];
    let sc = m.sc();
    let ld = Lad { t, s, c0: m.c0, srcs: &srcs, f0: false, cmpl, sc: &sc, g: &[] };
    let mn = super::mask::masked_prefix(&ld);
    let n = t.len() - mn;
    if n < 2 { return false; }
    let carries = if nc { n - 1 } else { n };
    let room = u.room(b);
    let need = super::mask::ck_need(carries);
    // ORD-IDLE: the masked scratch joins the chain's lanes in the ordinary section
    let e0 = super::mask::ord_idle_fixed(&ld);
    // ORD-DEC only where the lanes grow the bank past the decoder's rebuild
    super::mask::set_ord_dec(false);
    {
        let (i0, h) = (e0 + super::mask::ord_idle_bank(&ld), super::mask::ord_dec_lanes(&ld));
        let nbf = |ex: usize| mn.min(room).min((room + i0 + ex).saturating_sub(need));
        if k2() && h > 0 && nbf(h) >= nbf(0) + ord_dec_th() { super::mask::set_ord_dec(true); }
    }
    let idle = |nb: usize| e0 + if nb > 0 { super::mask::ord_idle_bank(&ld) } else { 0 };
    let total = |nb: usize| room + idle(nb) - nb;
    if total(0) < need { return false; }
    // the lanes past the chain's minimum go to the bank, as far as the top segment still holds the protected tail
    let mut nb = if k2() { mn.min(room).min((room + idle(1)).saturating_sub(need)) } else { 0 };
    let fits = |nb: usize| {
        if total(nb) < need { return false; }
        let r = carries.min(total(nb));
        let (_, top_n) = super::mask::ck_plan(carries, r);
        super::mask::ord_tail() <= n - carries + top_n
    };
    while nb > 0 && !fits(nb) { nb -= 1; }
    if !fits(nb) {
        return false;
    }
    // the anchors against the segments' interiors and the chain: a lane past the chain's minimum is worth more on either side
    // depending on how the prefix's segments fall
    // (6 lanes hold the interiors of a 4-cell segment)
    let pool_n = |n: usize| total(n).saturating_sub(idle(n)).min(carries.saturating_sub(idle(n)).max(6));
    if ck_split() {
        let score = |n: usize| {
            super::mask::ck_masked_cost(&ld, n, pool_n(n)) + (carries - carries.min(total(n))) as f64 / 2.0
        };
        let mut best = (score(nb), nb);
        for n in (0..nb).rev() {
            if fits(n) {
                let c = score(n);
                if c < best.0 { best = (c, n); }
            }
        }
        nb = best.1;
    }
    let r = if ck_split() { pool_n(nb) } else { carries.min(total(nb)).saturating_sub(idle(nb)) };
    let bank = b.alloc_n(nb);
    let pool = b.alloc_n(r);
    super::mask::ck_pass(b, &ld, &bank, &pool, roll.filter(|r| !r.rc.is_empty()), nc, top);
    b.free_n(&pool);
    b.free_n(&bank);
    true
}

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
/// Ported late-slot length bound. OFF is the exact parent path; ON uses the current traversal length.
pub const LEN_TAIL_PORT: bool = true;
fn len_tail_port() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("LEN_TAIL_PORT", LEN_TAIL_PORT)); *E }
/// The plain length registers' live bits at this slot.
fn len_n(w: &Win) -> usize {
    let n = if len_trim() && (w.slot >= LEN_TRIM_FROM || m2_break(7)) { LB_BITS - 1 } else { LB_BITS };
    if !len_tail_port() { return n; }
    // Activated control: the minimum-width plain length is too narrow at an early live slot.
    let tail_n = if cfg!(test) && std::env::var("WL_LEN_TAIL_BREAK_PORT").is_ok() && w.slot >= 1 { RHO_BITS } else { w.lenb };
    n.min(tail_n)
}
/// Ported DONE-counter tail bound; OFF retains the parent's full CNT7 window.
pub const CNT_TAIL_PORT: bool = true;
fn cnt_tail_port() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("CNT_TAIL_PORT", CNT_TAIL_PORT)); *E }
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
/// L3 VALUE-TEMP-HOST: Y[W-1] is the source's normalised leading 1 during an inverse value pass.
/// If its cell is ordinary, the masked prefix borrows that lane as its ephemeral AND temporary, X-flipping it
/// around each use and restoring it before any ordinary cell. One dedicated scratch lane is then available to
/// K2 / the existing carry allocator; no round, window or arithmetic is changed. Forward ROLL has no pool benefit.
pub const VALUE_TEMP_HOST: bool = true;
fn value_temp_host() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("VALUE_TEMP_HOST", VALUE_TEMP_HOST));
    *E
}
fn ytop_cof() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("YTOP_COF", YTOP_COF)); *E }
/// TERM-LAST applies at this slot.
fn term(w: &Win) -> bool {
    term_last() && (w.last || (m2_break(3) && w.slot == 200))
}
/// SLOT0-D: slot 0's d is 0 on every input: X holds p, whose top 223 bits are ones, so 2^e B > p needs B to agree with
/// them. No top compare, no d rotation, no LA - d on that slot, as on the last slot.
pub const SLOT0_D: bool = true;
/// TC-TIE: where B can be shorter than the top compare's WC lanes (lb.0 < WC), d = a1 & [Y top > X top] & [D < LB], with D
/// the number of leading equal lanes, instead of a masked ladder over the WC lanes. If the first difference lies inside B
/// the plain compare is right; if not, the top LB lanes tie and d = 0. D is a thermometer's parities (WC - 2 ANDs, CX only).
/// Exact: the same d on every shot with X[W-1] = Y[W-1] = 1, which a1 implies. Dev override `WL_TC_TIE=0|1`.
pub const TC_TIE: bool = true;
pub(crate) fn tc_tie() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("TC_TIE", TC_TIE)); *E }
/// The d compare of this slot reads no lanes under B
pub(crate) fn tc_plain(w: &Win) -> bool { w.lb.0 >= wc() }
/// LADDER-IDLE: while one inverse ladder runs the other length register is plain and unread, and its top lanes are |0>: bit 8
/// on every shot (LA, LB <= 255 from slot 1), and the bits above the slot's window + LADDER_IDLE_MARGIN, a bound no passing
/// shot reaches (a stall's length can sit above the window, which only counts steps). They join the ladder's room.
/// Dev override `WL_LADDER_IDLE=0|1`.
pub const LADDER_IDLE: bool = true;
const LADDER_IDLE_MARGIN: usize = 16;
/// (first shared lane, the shared bits' value) of a length with passing values in lo..=hi (<= 255)
pub(crate) fn idle_k(lo: usize, hi: usize, min: usize) -> (usize, usize) {
    let k = len_k(lo, hi, min, LB_BITS - 1);
    (k, hi >> k)
}
/// IDLE-SHARED: above the bits a slot's lengths can differ in they all read the same: flipped to |0>, those lanes join the room.
/// `other`: the length register the ladder does not read (lane 8 too); else the ladder's own, whose decoder keeps its low bits
/// and the mark on lane 8. A stall's length sits up to 7 above the window; none reaches 256 from slot 1.
pub(crate) fn other_idle(win: (usize, usize)) -> (usize, usize) {
    idle_k(win.0.saturating_sub(8), (win.1 + 8).min((1 << (LB_BITS - 1)) - 1), 1)
}
pub(crate) fn own_idle(win: (usize, usize)) -> (usize, usize) {
    let h = dec_keep(win).map_or(LB_BITS - 1, |d| d.0);
    idle_k(win.0.saturating_sub(8), (win.1 + 8).min((1 << (LB_BITS - 1)) - 1), h)
}
fn idle_shared() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("IDLE_SHARED", true)); *E }
fn idle_take(b: &mut B, v: &[QubitId], kk: (usize, usize), top: usize) -> (Vec<QubitId>, Vec<QubitId>) {
    let (k, kv) = kk;
    if k >= top { return (vec![], vec![]); }
    let l: Vec<QubitId> = v[k..top].to_vec();
    let on: Vec<QubitId> = (k..top).filter(|&i| kv >> (i - k) & 1 == 1).map(|i| v[i]).collect();
    for &q in &on { b.x(q); }
    zero_probe(b, &l);
    b.free_n(&l);
    (l, on)
}
fn idle_give(b: &mut B, t: (Vec<QubitId>, Vec<QubitId>)) {
    for &q in &t.0 { b.acquire(q); }
    zero_probe(b, &t.0);
    for &q in &t.1 { b.x(q); }
}
fn ladder_idle(b: &mut B, v: &[QubitId], win: (usize, usize)) -> (Vec<QubitId>, Vec<QubitId>) {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("LADDER_IDLE", LADDER_IDLE));
    if !*E { return (vec![], vec![]); }
    if idle_shared() { return idle_take(b, v, other_idle(win), LB_BITS); }
    let h = ((usize::BITS - (win.1 + LADDER_IDLE_MARGIN).leading_zeros()) as usize).min(LB_BITS - 1);
    idle_take(b, v, (h, 0), LB_BITS)
}
fn ladder_idle_back(b: &mut B, l: (Vec<QubitId>, Vec<QubitId>)) {
    idle_give(b, l);
}
/// CMP-D: on an act-constant plain successor F9's comparator is gated by the successor's a1 = X[W-1] & !ns on the way out (a
/// swap needs both anyway, so the rule cannot tell), and then it is the successor's d after cmp ^= sw: no AND and no erase.
/// Dev override `WL_CMP_D=0|1`.
pub const CMP_D: bool = true;
fn cmp_share() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("CMP_SHARE", true)); *E }
/// Negative controls for the gate tests only (CMPD_BREAK=k): 1 the inverse skips cmp ^= sw, 2 its comparator lane is measured with no repair.
fn cmpd_break(k: u32) -> bool {
    cfg!(test) && std::env::var("CMPD_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
pub(crate) fn cmp_is_d(n: &Win) -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("CMP_D", CMP_D));
    *E && tc_plain(n) && n.act_const && !no_d(n) && gov_cfg_at(n.slot).is_none()
}
/// LEN-K: the lanes of a length operation whose operands, on every passing shot, share their bits above them
fn len_k(lo: usize, hi: usize, min: usize, ln: usize) -> usize {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("LEN_K", true));
    if !*E { return ln; }
    ((usize::BITS - (lo ^ hi).leading_zeros()) as usize).clamp(min, ln)
}
/// F9's [LA < LB + cmp] and F10's length swap: a swap needs X[W-1] = 1, so LA is within RCAP + 1 of the window below and
/// a stall's excess above it (LADDER_IDLE_MARGIN's bound)
pub(crate) fn f9_lanes(w: &Win, ln: usize) -> usize {
    len_k(w.lb.0.min(w.lad.0).saturating_sub(8), w.lb.1.max(w.lad.1) + 8, 2, ln)
}
/// LA -+ rho: a stall's LA can sit above the window (worst excess 7 in 2e6 walks; LADDER_IDLE_MARGIN)
pub(crate) fn rho_lanes(w: &Win, ln: usize) -> usize {
    len_k(w.lad.0.saturating_sub(8), w.lad.1 + LADDER_IDLE_MARGIN, 3, ln)
}
/// KT-K: the decode's u = LA + sX, v = LB + sY and kt = u - v (mod 2^k: kt <= 31) on the lanes below the bits every passing
/// shot's LA and LB share (a stall's lengths sit up to 7 above the window, and none reaches 256 from slot 1); the shared
/// bits are CX and X gates. A carry out of lane k - 1 is dropped on both, and nothing reads u's upper lanes.
fn kt_hi(w: &Win) -> usize { (w.lb.1.max(w.lad.1) + 8).min((1 << (LB_BITS - 1)) - 1) }
pub(crate) fn kt_lanes(w: &Win) -> usize {
    // (masked rows: u - UOFF in -64..64 by sign extension from lane k - 1)
    len_k(w.lb.0.min(w.lad.0.saturating_sub(8)), kt_hi(w), if w.mx < NB + 1 { 7 } else { R_BITS + 1 }, LB_BITS)
}
pub(crate) fn kt_top(w: &Win) -> usize { kt_hi(w) >> kt_lanes(w) }
/// F9 of slot w keeps its comparator for the successor's F2
pub(crate) fn dcmp_keep(w: &Win, next: Option<&Win>) -> bool {
    next.map_or(false, |n| if tc_tie() { !no_d(n) } else { w.lb.0 > 1 && tc_plain(n) })
}
/// Negative controls for the gate tests only (TIE_BREAK=k): 1 d ignores the tie check, 2 D loses its top bit.
fn tie_break(k: u32) -> bool {
    cfg!(test) && std::env::var("TIE_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
fn slot0_d() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("SLOT0_D", SLOT0_D)); *E }
/// Slots with d = 0 on every passing shot
fn no_d(w: &Win) -> bool { term(w) || (slot0_d() && w.a1_const) }
/// The X/Y and LA/LB lanes the swap must exchange at this slot (`plain`: LA/LB hold plain lengths).
fn swap_lanes(w: &Win, plain: bool) -> (usize, usize) {
    if !swap_prune() {
        return (W, LB_BITS);
    }
    let xn = if m2_break(1) { W - 2 } else { W - 1 };
    let ln = if plain && w.slot >= SWAP_PRUNE_L8 { if m2_break(4) { LB_BITS - 2 } else { f9_lanes(w, LB_BITS - 1) } } else { LB_BITS };
    (xn, ln)
}

// ------------------------------------------------------------------ Q825 B-SYNCGOV (invent/GOVERNOR.md, SYNC record)
/// SYNC GOVERNOR (E-GOVERNOR's exact device). Slot t = s* - 1 writes, after its F8, a b-bit level index
/// c = #{j >= 1 : M <= th_j} into a fresh record (M = LA + LB, swap-invariant, i.e. the sync slot's pre-state M; th_j:
/// the shot is at least L[j] slots ahead of the median, ceil(16 (T - M) / r16) >= L[j]); the shot is then FROZEN for
/// slots s* .. e = s* + L[c] - 1: a1 and the renormalisation are gated by !h_s (h_s = [L[c] > s - s*] = [c >= j(s)], a
/// compare of c with a classical constant), so a held slot steps nothing and rotates nothing. DEFERRED SWAP: every F9 on
/// slots t .. s* + 13 is gated by !h_(s+1), so a held shot skips t's swap, sits un-swapped (t's post-F8 state) through
/// its hold and swaps at the F10 of e (F9 reads sw_t again on the unchanged state). The forward and the inverse of every
/// held slot then see the same layout (the ladders' measured receipts match), and each slot's sw is ghosted and repaired
/// at its own slot. Inverse: rho, a1, unrenorm's phase repair and I15 gated by !h_s; every swap-flag erase (carried or
/// I5) gated by !h_(s+1) exactly as the forward's F9; held slots produce cout = a1 & single = 0, and slot e takes
/// cout(e + 1) = sw_e as any slot. The record is erased in inverse slot t right after its I5 (plain LA / LB, the same
/// M); it lives from forward slot t through the turnaround. The window table is the governed one (E-GOVERNOR
/// make_tables.py, 1e6 paired walks, eps 1e-5), baked as greedyfrog_data/win_table.txt. Window slots must be
/// act-constant and carried (asserted). Dev overrides `WL_SYNC_GOV=0|1`, `WL_GOV_BITS=1|2|3` (the 1- / 3-bit records
/// need their own governed table via GF_WIN).
pub const SYNC_GOV: bool = true;
/// record bits (1, 2 or 3)
pub const GOV_BITS: usize = 2;
/// The sync points of the walk (slot:T:16 x rate:hold levels; even holds, see STALL_PAIR).
pub const GOV_SYNCS: &str = "90:307:36:0-4-8-16"; // mport: single record (E-GOV2 needs the table refit; priced separately)
/// (s*, T, 16 x rate, hold levels) per record width: GOVERNOR.md 2.3 configs M:100/.7/0-7, M:90/.5/0-4-8-15,
/// M:100/.5/0-2-4-7-10-14-19-25 (T = the M quantile at s*, rate = the median slope (q(s*-8) - q(s*+8)) / 16)
const GOV_CFGS: [(usize, usize, usize, &[usize]); 3] = [
    (100, 291, 37, &[0, 7]),
    (90, 307, 36, &[0, 4, 8, 16]), // STALL-PAIR: even holds (a held shot with no lag leaves on an add-back; 15 -> 16)
    (100, 284, 37, &[0, 2, 4, 7, 10, 14, 19, 25]),
];
/// The sync record's classical schedule.
#[derive(Clone, Debug)]
pub struct GovCfg {
    pub slot: usize,
    pub bits: usize,
    pub levels: Vec<usize>,
    /// th[j] (j >= 1): the record is >= j iff M <= th[j]
    pub th: Vec<usize>,
}
impl GovCfg {
    pub fn new(bits: usize) -> GovCfg {
        let (slot, t, r16, levels) = GOV_CFGS[bits - 1];
        GovCfg::with(slot, t, r16, levels)
    }
    pub fn with(slot: usize, t: usize, r16: usize, levels: &[usize]) -> GovCfg {
        let bits = levels.len().trailing_zeros() as usize;
        assert_eq!(levels.len(), 1 << bits);
        // ceil(16 (T - m) / r16) >= L  <=>  16 (T - m) > r16 (L - 1)
        let th = levels.iter().map(|&l| {
            if l == 0 { return usize::MAX; }
            (0..=1023usize).rev().find(|&m| 16 * (t as i64 - m as i64) > (r16 * (l - 1)) as i64).unwrap()
        }).collect();
        GovCfg { slot, bits, levels: levels.to_vec(), th }
    }
    /// record value for M = LA + LB (0 on finished shots)
    pub fn level_of(&self, la: usize, lb: usize) -> usize {
        if la == 0 { return 0; }
        (1..self.levels.len()).filter(|&j| la + lb <= self.th[j]).count()
    }
    /// first slot after the longest hold
    pub fn end(&self) -> usize { self.slot + self.levels[self.levels.len() - 1] }
    /// the shot with record c is held at slot s
    pub fn held(&self, c: usize, s: usize) -> bool { s >= self.slot && self.levels[c] > s - self.slot }
    /// h_s = [c >= j]: Some(j) on the slots where a hold can be on
    pub fn jmin(&self, s: usize) -> Option<usize> {
        if s < self.slot || s >= self.end() { return None; }
        (1..self.levels.len()).find(|&j| self.levels[j] > s - self.slot)
    }
    /// the record value whose last held slot is s
    pub fn last_of(&self, s: usize) -> Option<usize> {
        (1..self.levels.len()).find(|&j| self.slot + self.levels[j] == s + 1)
    }
}
pub fn sync_gov() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("SYNC_GOV", SYNC_GOV)); *E }
pub fn gov_cfg() -> Option<&'static GovCfg> {
    gov_cfgs().first()
}
/// The sync points in slot order. Dev override `WL_GOV_SYNCS=slot:T:r16:l0-l1-l2-l3,...`.
pub fn gov_cfgs() -> &'static [GovCfg] {
    static G: std::sync::LazyLock<Vec<GovCfg>> = std::sync::LazyLock::new(|| {
        let txt = std::env::var("WL_GOV_SYNCS").unwrap_or_else(|_| GOV_SYNCS.to_string());
        txt.split(',').filter(|t| !t.trim().is_empty()).map(|t| {
            let f: Vec<&str> = t.trim().split(':').collect();
            let levels: Vec<usize> = f[3].split('-').map(|v| v.parse().unwrap()).collect();
            GovCfg::with(f[0].parse().unwrap(), f[1].parse().unwrap(), f[2].parse().unwrap(), &levels)
        }).collect()
    });
    if sync_gov() { &G } else { &[] }
}
/// The sync point whose record slot or window holds slot s.
pub fn gov_cfg_at(s: usize) -> Option<&'static GovCfg> {
    gov_cfgs().iter().find(|g| s + 1 >= g.slot && s < g.end())
}
/// Negative controls for the gate tests only (GOV_BREAK=k): 1 the inverse reads the hold level of the next record value
/// (corrupt hold level), 2 the inverse's swap-flag erases are not gated by !h_(s+1), 3 the forward's F9 is not gated
/// (no deferred swap).
fn gov_break(k: u32) -> bool {
    cfg!(test) && std::env::var("GOV_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
/// Lift a literal (q, negated) to a lane holding it (X in place for a negated record lane); undo with gov_act_off.
fn gov_act_on(b: &mut B, l: (QubitId, bool)) -> QubitId {
    if l.1 { b.x(l.0); }
    l.0
}
fn gov_act_off(b: &mut B, l: (QubitId, bool)) {
    if l.1 { b.x(l.0); }
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
pub const ROUND_DIV: bool = true;
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
pub const RUN_GUARD: bool = true;
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
/// NO-YSHIFT: on SW-CARRY slots the target's window is not shifted for its slack: only the windows' relative alignment
/// matters, so a slack of 1 is a leading zero of the remainder (one row later, one window bit less) with kt' = LA + sX - LB
/// = kt + sY and t = sX - J' unchanged. No AND, no 2 x NB cswaps, no LB + sY adds, no sY lane.
pub const NO_YSHIFT: bool = true;
pub(crate) fn no_yshift() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("NO_YSHIFT", NO_YSHIFT)); *E }
/// Record that `lanes` are |0> on every shot at the current stream position (checked by the gate tests).
pub(crate) fn zero_probe(b: &B, lanes: &[QubitId]) {
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
    /// Q825 B-MICRO2: the slot's index in the traversal (Win::full: 0) and whether it is the last slot (NSLOTS - 1)
    pub slot: usize,
    pub last: bool,
    /// Late-slot live bits of the plain LA/LB registers.
    pub lenb: usize,
    /// Late-slot live bits of the complemented DONE counter.
    pub cntb: usize,
    /// The DONE counter's largest live width over the traversal
    pub cntn: usize,
    /// STALL-PAIR: a fake at this slot (and its add-back) writes value lanes pv.. and cofactor lanes ..=jc; pvp, jcp the
    /// previous slot's
    pub pv: usize,
    pub pvp: usize,
    pub jc: isize,
    pub jcp: isize,
    /// B5SPEND REFIT-1 (LS-4 NB-TAIL): the division rows' window at this slot (rem / div lanes 0..nb; nb < NB only on
    /// slots whose rows are all window-plain, w.mx >= NB + 1: the plain rows skip the window's low NB - nb lanes).
    /// 9th win_table column (default NB).
    pub nb: usize,
    /// B5SPEND REFIT-1 (LS-4 GUARD-TAIL): RUN_GUARD runs at this slot (10th win_table column 0/1; default 1).
    pub guard: bool,
}

impl Win {
    /// No classical knowledge: every boundary anywhere (masks everywhere, all rows).
    pub fn full() -> Win {
        Win { lb: (1, 256), lad: (0, 256), mxp: 0, mx: 0, k: KROWS, act_const: false, dtop: NB, dtop_tight: false, dtop_near: false, a1_const: false,
              la_gmin: if MARKER_FREE { 1 } else { 7 }, la_hb: LB_BITS, slot: 0, last: false, lenb: LB_BITS, cntb: CNT_BITS - 1, pv: W, pvp: W, jc: -1, jcp: -1, cntn: CNT_BITS - 1, nb: NB, guard: true }
    }
}

/// slots between the last act-constant slot and the first slot where an envelope walk finished
/// Q825 LS-2: 40 -> 4 (1.28e9-walk tail: the earliest finish is slot 174)
const ACT_MARGIN: usize = 4;
/// STALL-PAIR: holds and two-slot stalls delay the earliest finish (3e6 governed walks: slot 199, 6 shots; the tail falls
/// by about 1.8x per slot), so no passing shot has finished before this slot.
const FIRST_DONE_PAIR: usize = 200;

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
                     la_gmin: 7, la_hb: LB_BITS, slot: 0, last: false, lenb: LB_BITS, cntb: CNT_BITS - 1, pv: W, pvp: W, jc: -1, jcp: -1, cntn: CNT_BITS - 1, nb: NB, guard: true });
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
                // B5SPEND REFIT-1 (LS-4 NB-TAIL): optional 9th column = this slot's division-row window nb (default NB)
                if let Some(&n) = c.get(8) {
                    assert!(n <= NB && n >= 16 && (n == NB || (w.mx >= NB + 1 && n > w.k)), "NB-TAIL: nb {n} at slot {} (mx {}, k {})", c[0], w.mx, w.k);
                    w.nb = n;
                }
                // B5SPEND REFIT-1 (LS-4 GUARD-TAIL): optional 10th column = RUN_GUARD at this slot (0/1)
                if let Some(&g) = c.get(9) {
                    assert!(g <= 1, "GUARD-TAIL: column 10 is 0/1");
                    w.guard = g == 1;
                }
            }
        }
    }
    if stall_pair() { first_done = first_done.max(FIRST_DONE_PAIR); }
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
    let nv = v.len();
    for (s, w) in v.iter_mut().enumerate() {
        w.slot = s;
        w.last = s + 1 == nv;
        let m = 1 + 8 * (nv - s);
        w.lenb = ((usize::BITS - m.leading_zeros()) as usize).clamp(RHO_BITS, LB_BITS);
    }
    // Derive the counter boundary from this 255-slot schedule, not donor049's 256-slot table.
    let first_live = v.iter().position(|w| !w.act_const).unwrap_or(nv);
    for (s, w) in v.iter_mut().enumerate() {
        if s >= first_live {
            let m = s + 1 - first_live;
            w.cntb = ((usize::BITS - m.leading_zeros()) as usize).clamp(2, CNT_BITS - 1);
        }
    }
    let cntn = v.iter().map(|w| w.cntb).max().unwrap_or(CNT_BITS - 1);
    for w in v.iter_mut() { w.cntn = cntn; }
    // STALL-PAIR: the lanes a fake and its add-back share
    let (a_v, h_c): (Vec<usize>, Vec<isize>) = v.iter().map(|w| (W - w.lb.0 + 1, CW as isize - 2 - w.lad.1 as isize)).unzip();
    for s in 0..nv {
        let t = (s + 1).min(nv - 1);
        v[s].pv = a_v[s].max(a_v[t]);
        v[s].jc = h_c[s].min(h_c[t]);
        if s > 0 {
            v[s].pvp = a_v[s - 1].max(a_v[s]);
            v[s].jcp = h_c[s - 1].min(h_c[s]);
        }
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
                // STALL-PAIR: a stall pair rotates at most 7 per two slots
                lamax = lamax.max(hi - 7 * (if stall_pair() { k / 2 } else { k }) as isize);
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
    /// B-SYNCGOV: the sync record c (LSB first; empty outside forward slot s* .. inverse slot s* - 1)
    pub gov: Vec<QubitId>,
    /// STALL-PAIR: the flag lane between slots (forward: the next slot is an add-back)
    pub sf: Option<QubitId>,
    /// The earlier sync points' records under `gov`, and the sync slot `gov` belongs to
    pub gov_stack: Vec<Vec<QubitId>>,
    pub gov_slot: usize,
    /// CMP-SHARE: the comparator lane handed from an inverse slot to its predecessor's swap-flag erase
    pub cmp_held: Option<QubitId>,
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
pub(crate) fn l3_profile_context() -> (usize, &'static str) {
    (P3ST.with(|p| p.borrow().0), PROF.with(|p| p.borrow().1))
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

// ------------------------------------------------------------------ IN-PLACE DECODE (after jieyilong's R4-RHO, row 325f07e7)
/// R4-DECODE: rho and a1 are functions of t = sX - sY - J (5 bits), so jl -> t in place, then (t, one fresh lane) -> (rho on
/// jl[0..3], a1 on the fresh lane, res on jl[3..5]), and res is X-measured. J is never restored, so no backward sweep runs.
/// res = m - 1 on the m-th stall since the last step and 0 on every other shot. Under STALL-PAIR a stall (add-back) at inverse
/// slot k follows a fake at k - 1, whose decode is gated off, so the phase it owes is repaid at k - 2, whose own t = 7m:
/// (-1)^(b0 t3 + b1 t4) on the shots with X[W-1] = 0 there. The sweep runs gated by the slot's act, so a fake or finished
/// shot has J = 0 and t = sX, zeroed by a CCX per bit. SW-CARRY's single flag is taken from J before the map: c = a1 & single,
/// and single is X-measured: a step's is c, a fake or finished shot's is 1, a stall's is owed to k - 2's own single flag.
/// Plain-row slots outside the governor's window. Dev override `WL_R4_DECODE=0|1`.
pub const R4_DECODE: bool = true;
fn r4_on() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("R4_DECODE", R4_DECODE)); *E }
/// Negative controls for the gate tests only (R4_BREAK=k): 1 drops the c erase's repair, 2 drops the owed res repair,
/// 3 drops the owed single-flag repair, 4 skips the t zeroing, 5 leaves h on its lane.
fn r4_break(k: u32) -> bool {
    cfg!(test) && std::env::var("R4_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
fn r4_slot(w: &Win) -> bool {
    r4_on() && hsweep_on() && !w.last && w.k >= 2 && w.slot >= 2 && stall_pair()
        && gov_cfg_at(w.slot).is_none()
}
#[derive(Clone)]
struct R4Owed { res: Vec<BitId>, sing: Option<BitId> }
thread_local! { static R4_OWED: std::cell::RefCell<Vec<(usize, R4Owed)>> = std::cell::RefCell::new(vec![]); }
#[cfg(test)]
fn r4_clear() { R4_OWED.with(|v| v.borrow_mut().clear()); }
fn r4_owe(slot: usize, o: R4Owed) { R4_OWED.with(|v| v.borrow_mut().push((slot, o))); }
fn owe_dirty() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("OWE_DIRTY", true)); *E }
/// negative control (tests only): OWE_BREAK=1 drops the second phase block of OWE-DIRTY
fn owe_break() -> bool { cfg!(test) && std::env::var("OWE_BREAK").map_or(false, |v| v.trim() == "1") }
fn r4_take(slot: usize) -> Option<R4Owed> {
    R4_OWED.with(|v| {
        let mut v = v.borrow_mut();
        v.iter().position(|e| e.0 == slot).map(|i| v.remove(i).1)
    })
}
/// In place on j = t (5 lanes): j[0..3] -> rho, j[3..5] -> res, e ^= [t < 8]. 7 Toffoli + the c erase's conditioned repair
/// (2 CCZ + 1 AND). rho = t - 7m: with t = 8h + l, s = l + h with carry c, rho = s + c.
fn r4_decode(b: &mut B, j: &[QubitId], e: QubitId) {
    let (l0, l1, l2, h0, h1) = (j[0], j[1], j[2], j[3], j[4]);
    // s = l + h (3 bits) with carry out c: half adder on bit 0, Cuccaro MAJ / UMA on bit 1 (carry in k), AND on bit 2
    let k = b.alloc();
    b.and_c(l0, h0, k);
    b.cx(h0, l0);
    b.cx(h1, l1);
    b.cx(h1, k);
    b.ccx(k, l1, h1);
    let c = b.alloc();
    b.and_c(h1, l2, c);
    b.cx(h1, l2);
    b.ccx(k, l1, h1);
    b.cx(h1, k);
    b.cx(k, l1);
    b.cx(h0, l0);
    b.and_u(l0, h0, k);
    b.cx(h0, l0);
    b.free(k);
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
    t_owned: bool,
}

impl Masked {
    /// The value / cofactor ladders' scratch (mid passes only: no comparator chain with LADDER_NO_CHAIN).
    fn alloc_ladder(b: &mut B) -> Masked {
        if ladder_no_chain() { Masked::alloc_lean(b) } else { Masked::alloc(b) }
    }
    /// `alloc_ladder` with the prefix sized for a DEC_NARROW decoder of window top `hi`.
    fn alloc_ladder_w(b: &mut B, win: (usize, usize)) -> Masked {
        match (ladder_no_chain(), dec_keep(win)) {
            (true, Some((h, _))) => {
                let f = b.alloc();
                let h = h - if gap_src(win) { super::greedyfrog_model::GAP_LOG } else { 0 };
                Masked { f, t: b.alloc(), gf: f, chain: vec![], pre: b.alloc_n(h), c0: b.alloc(), t_owned: true }
            }
            _ => Masked::alloc_ladder(b),
        }
    }
    fn alloc(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: b.alloc_n(LB_BITS - 1), pre: b.alloc_n(LB_BITS - 1), c0: b.alloc(), t_owned: true }
    }
    /// The 9-bit decoder without a comparator chain: its comparators borrow lanes (`ge_const_dirty`, `in_range`).
    fn alloc_lean(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: vec![], pre: b.alloc_n(LB_BITS - 1), c0: b.alloc(), t_owned: true }
    }
    /// For the decode's masks on the 6-bit u' (prefix 5; comparators borrow lanes) with a given AND temp.
    fn alloc_small_on(b: &mut B, t: QubitId) -> Masked {
        let f = b.alloc();
        Masked { f, t, gf: f, chain: vec![], pre: b.alloc_n(5), c0: b.alloc(), t_owned: true }
    }
    /// For the decode's masks on the 6-bit u' (prefix 5; comparators borrow lanes).
    fn alloc_small(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: vec![], pre: b.alloc_n(5), c0: b.alloc(), t_owned: true }
    }
    fn sc(&self) -> Mscr {
        Mscr { f: self.f, t: self.t, gf: self.gf, chain: self.chain.clone() }
    }
    fn host_temp_one(&mut self, b: &mut B, q: QubitId) {
        assert!(self.t_owned);
        b.free(self.t);
        self.t = q;
        self.t_owned = false;
        super::mask::set_temp_one_host(Some(q));
        if cfg!(test) {
            b.x(q);
            zero_probe(b, &[q]);
            b.x(q);
        }
    }
    fn free(self, b: &mut B) {
        b.free(self.f);
        if self.t_owned {
            b.free(self.t);
        } else {
            super::mask::set_temp_one_host(None);
        }
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
thread_local! {
    /// TOP-D: the forward value pass's d lane
    static FWD_D: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) };
}
pub const TOP_D: bool = true;
pub const NZ_CONST: bool = true;
/// LA-D: LA +- d only on the lanes it can change: d = 1 only on a step, whose LA - d lies in the slot's window, so no
/// carry leaves the low k lanes when [lo, hi + 1] shares its bits above k.
pub const LA_D: bool = true;
fn la_d_lanes(w: &Win, ln: usize) -> usize {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("LA_D", LA_D));
    if !*E { return ln; }
    let (lo, hi) = (w.lad.0, w.lad.1 + 1);
    let k = (usize::BITS - (lo ^ hi).leading_zeros()) as usize;
    k.clamp(2, ln)
}
fn nz_const() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("NZ_CONST", NZ_CONST)); *E }
fn top_d() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("TOP_D", TOP_D)); *E }
fn value_ladder(u: &GreedyFrog, w: &Win) -> (Vec<QubitId>, Vec<QubitId>) {
    let hi = w.lb.1;
    (u.x[W - hi..].to_vec(), u.y[W - hi..].to_vec())
}

/// F4 (cmpl: X -= Y where a1) or I10 (X += Y where a1, and d ^= the carry); X lane 0 ^= a1 & carry out.
/// ROLL-FWD: the forward (cmpl) returns its receipts; the inverse takes them (`roll`, None or empty: not rolled).
fn value_pass(b: &mut B, u: &GreedyFrog, w: &Win, cmpl: bool, a1: QubitId, d: Option<QubitId>, always: bool,
              roll: Option<&RollRec>) -> RollRec {
    value_pass_shared(b, u, w, cmpl, a1, d, always, roll, None)
}
fn value_pass_shared(b: &mut B, u: &GreedyFrog, w: &Win, cmpl: bool, a1: QubitId, d: Option<QubitId>, always: bool,
              roll: Option<&RollRec>, live: Option<(Vec<QubitId>, usize, Vec<QubitId>, usize)>) -> RollRec {
    let fwd_d = FWD_D.with(|c| c.get());
    let (mut m, start) = match live {
        Some((pre,j,view,base)) => {
            let (current_view,current_base)=dec_view(&u.lb,w.lb);
            assert_eq!(view,current_view,"L8 physical view/order changed");
            assert_eq!(base,current_base,"L8 base/frame changed");
            assert_eq!(base,0,"nonzero-base sharing forbidden");
            assert_eq!(j,wc(),"L8 cursor frame mismatch");
            assert!(cmpl && roll_value() && dec_keep(w.lb)==Some((pre.len(),0)));
            let f=b.alloc();
            (Masked { f, t:b.alloc(), gf:f, chain:vec![], pre, c0:b.alloc(), t_owned: true },Some(j))
        }
        None => (Masked::alloc_ladder_w(b,w.lb),None),
    };
    let (t, s) = value_ladder(u, w);
    if !cmpl && roll.is_some() && value_temp_host() {
        let srcs = [value_src(u, &m, w)];
        let sc = m.sc();
        let ld = Lad { t: &t, s: &s, c0: m.c0, srcs: &srcs, f0: false, cmpl, sc: &sc, g: &[] };
        // The actual extended STALL-PAIR mask, not just the table window, must leave the top source cell ordinary.
        if super::mask::masked_prefix(&ld) < t.len() {
            let q = u.y[W - 1];
            assert_eq!(s.last(), Some(&q));
            assert!(!t.contains(&q));
            m.host_temp_one(b, q);
        }
    }
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
        // TOP-D: a step's borrow out of the top lane is d (2A - 2^W < A < B where d = 1, A >= B where d = 0), and
        // a1 = 0 writes nothing, so X[0] ^= d is a CX on its own lane (a shot whose window compare decided d wrong fails
        // already). `fwd_d` is the forward's d lane.
        let topw = if let (true, Some(dq)) = (top_d(), fwd_d) { b.cx(dq, u.x[0]); None } else { Some((if top_free { ALWAYS } else { a1 }, u.x[0])) };
        let rec = super::mask::roll_fwd_from(b, &ld, g_ord, g_m, rm, false, &lanes, topw, start);
        b.free_n(&lanes);
        m.free(b);
        return rec;
    }
    assert!(start.is_none());
    // CK-LADDER
    if !cmpl && roll.is_some() {
        let tf = top_free;
        let x0 = u.x[0];
        if ck_try(b, u, &t, &s, value_src(u, &m, w), &m, cmpl, roll, false, |b, tc| {
            match (d, tf, top_d()) {
                (Some(d), false, true) => {
                    // TOP-D: d = a1 & carry, and X[0] ^= d
                    a1_ccx(b, a1, tc, d);
                    b.cx(d, x0);
                }
                _ => {
                    if tf { b.cx(tc, x0); } else { a1_ccx(b, a1, tc, x0); }
                    if let Some(d) = d {
                        if tf { b.cx(tc, d); } else { a1_ccx(b, a1, tc, d); }
                    }
                }
            }
        }) {
            m.free(b);
            return RollRec::default();
        }
    }
    // (a fully masked ladder under MASK-CARRY-FULL reads a1 at its top only)
    let full = !cmpl && always && roll.is_some() && {
        let srcs = [value_src(u, &m, w)];
        let sc = m.sc();
        let ld = Lad { t: &t, s: &s, c0: m.c0, srcs: &srcs, f0: false, cmpl, sc: &sc, g: &[] };
        super::mask::mask_carry_full_on(&ld)
    };
    let a1p = a1;
    let a1l = if full { None } else { a1_copy(b) };
    let a1 = a1l.unwrap_or(a1);
    // carry pool over the ordinary lanes above the LB window
    let pool = pool_for(b, u, t.len() - (w.lb.1 - w.lb.0 + 1), 0);
    let srcs = [value_src(u, &m, w)];
    let sc = m.sc();
    let ld = Lad { t: &t, s: &s, c0: m.c0, srcs: &srcs, f0: false, cmpl, sc: &sc, g: &pool };
    // K2: room the ordinary lanes' carry pool leaves idle banks the masked cells' f & s' (K1 form)
    let bank = if k2() { pool_for(b, u, w.lb.1 - w.lb.0 + 1, 0) } else { vec![] };
    // L3: all-masked value ladders have no ordinary CK section. Reuse the same masked carry-bank rewrite
    // on their existing bank, preserving the original allocation and top-carry consumers.
    if full {
        let ok = super::mask::mask_carry_full(b, &ld, &bank, roll, |b, tc| {
            if top_free { b.cx(tc, u.x[0]); } else { a1_ccx(b, a1p, tc, u.x[0]); }
            if let Some(d) = d {
                if top_free { b.cx(tc, d); } else { a1_ccx(b, a1p, tc, d); }
            }
        });
        assert!(ok, "MASK-CARRY-FULL needs its bank");
        b.free_n(&bank);
        b.free_n(&pool);
        m.free(b);
        return RollRec::default();
    }
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
    a1_copy_free(b, a1l);
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

/// STALL-PAIR: the ordinary cofactor write literal for the counter lanes on act-live slots: (lanes, act literal).
/// `pk` = the act lane parked on length lane v[i] (v[i] = !act): the literal reads that lane.
fn sp_tail(u: &GreedyFrog, w: &Win, act: Option<QubitId>, pk: Option<usize>) -> Option<(usize, QubitId, bool)> {
    let a = act?;
    if !stall_pair() || sp_break(4) { return None; }
    // a fake and its add-back must protect the same lanes, so the protected width does not follow the live counter width
    let n = w.cntn.min(u.cnt.len());
    Some(match pk { Some(i) => (n, u.la[i], true), None => (n, a, false) })
}
/// STALL-PAIR, last slot: q ^= !a1 & !(finished & counter odd), the add-back flag of every passing shot (a finished shot
/// alternates from its first finished slot, where the counter reads 1). `act` holds act here.
fn sp_last(u: &GreedyFrog, b: &mut B, act: Option<QubitId>, a1: QubitId, q: QubitId) {
    let Some(a) = act else {
        b.x(a1);
        b.cx(a1, q);
        b.x(a1);
        return;
    };
    let t = b.alloc();
    let c0 = u.cnt[0]; // the counter is complemented on Y[0..)
    let lits = [(a, true), (c0, true)];
    and_auto(b, u, &lits, t);
    and_auto(b, u, &[(a1, true), (t, true)], q);
    erase_and(b, u, t, &lits);
    b.free(t);
}

/// A1-MARK: while an inverse ladder's marks are on, v[8] = !a1 on every shot (0 on a plain length <= 255, then the stall mark;
/// a finished shot reads 1 from the done mark): a1's lane joins the ladder's room, the mask toggles and the top read v[8].
/// Dev override `WL_A1_MARK=0|1`.
pub const A1_MARK: bool = true;
fn a1_mark_on() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("A1_MARK", A1_MARK)); *E }
thread_local! { static A1_PARKED: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) }; }
fn a1_park(b: &mut B, ok: bool, a1: QubitId, v: &[QubitId]) -> Option<QubitId> {
    if !(ok && a1_mark_on()) { return None; }
    let v8 = v[LB_BITS - 1];
    b.x(v8);
    b.cx(v8, a1);
    b.x(v8);
    zero_probe(b, &[a1]);
    b.free(a1);
    A1_PARKED.with(|c| c.set(Some(v8)));
    Some(v8)
}
fn a1_unpark(b: &mut B, a1: QubitId, pk: Option<QubitId>) {
    let Some(v8) = pk else { return };
    A1_PARKED.with(|c| c.set(None));
    b.acquire(a1);
    b.x(v8);
    b.cx(v8, a1);
    b.x(v8);
}
/// A1-MARK: a ladder that falls back from its anchored chain writes under a lane holding a1
fn a1_copy(b: &mut B) -> Option<QubitId> {
    let v8 = A1_PARKED.with(|c| c.get())?;
    let q = b.alloc();
    b.x(v8);
    b.cx(v8, q);
    b.x(v8);
    Some(q)
}
fn a1_copy_free(b: &mut B, q: Option<QubitId>) {
    let (Some(q), Some(v8)) = (q, A1_PARKED.with(|c| c.get())) else { return };
    b.x(v8);
    b.cx(v8, q);
    b.x(v8);
    b.free(q);
}
/// tgt ^= a1 & tc, a1 parked or not
fn a1_ccx(b: &mut B, a1: QubitId, tc: QubitId, tgt: QubitId) {
    match A1_PARKED.with(|c| c.get()) {
        Some(v8) => {
            b.x(v8);
            b.ccx(v8, tc, tgt);
            b.x(v8);
        }
        None => b.ccx(a1, tc, tgt),
    }
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

/// GAP-MASK: a ring's value and cofactor are GAP zero lanes apart (W = CW + GAP), so a ladder may start one lane early: the
/// source there is 0 and the carry stays 0. The running mask then only toggles at every second lane, on the length >> 1, which
/// halves the decoder's ANDs (about 1 T per lane walk) and takes a lane off its prefix. Dev override `WL_GAP_MASK=0|1`.
pub const GAP_MASK: bool = true;
fn gap_mask() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("GAP_MASK", GAP_MASK)); *E }
/// Negative controls for the gate tests only (GAP_BREAK=k): the wrong lane of each pair toggles, 1 value, 2 cofactor.
fn gap_break(k: u32) -> bool {
    cfg!(test) && std::env::var("GAP_BREAK").map_or(false, |v| v.trim() == k.to_string())
}
fn gap_src(win: (usize, usize)) -> bool {
    gap_mask() && super::greedyfrog_model::GAP >= 1 && win.1 >= win.0 + 2 && dec_keep(win).map_or(true, |d| d.0 >= 2 + super::greedyfrog_model::GAP_LOG)
}
fn value_src(u: &GreedyFrog, m: &Masked, w: &Win) -> Src {
    // ladder lane l <-> physical W - hi + l; toggle where LB == hi - l
    let (lo, hi) = w.lb;
    let (v, base) = dec_view(&u.lb, w.lb);
    if gap_src(w.lb) {
        let v = v[super::greedyfrog_model::GAP_LOG..].to_vec();
        return Src { lo: 0, hi: hi - lo + 1, a: (hi - base) as isize, d: if gap_break(1) { 2 } else { -2 }, pre: m.pre[..v.len() - 1].to_vec(), v, late: false };
    }
    Src { lo: 0, hi: hi - lo + 1, a: (hi - base) as isize, d: -1, pre: m.pre[..v.len() - 1].to_vec(), v, late: false }
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
/// DECODER7 compatibility port. OFF preserves the parent's high-trimmed view.
pub const DECODER7_PORT: bool = true;
fn decoder7_port() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("DECODER7_PORT", DECODER7_PORT)); *E }
/// Kept low bits and the dropped high base for a window (OFF: parent's narrow view, base zero).
fn dec_keep(win: (usize, usize)) -> Option<(usize, usize)> {
    let (lo, hi) = win;
    let bl = |x: usize| (usize::BITS - x.leading_zeros()) as usize;
    let h = bl(hi);
    let narrow = (dec_narrow() && h >= 2 && h < LB_BITS - 1).then_some(h);
    if !decoder7_port() || hi >= 1 << (LB_BITS - 1) || lo > hi {
        return narrow.map(|h| (h, 0));
    }
    let cap = narrow.unwrap_or(LB_BITS - 1);
    let mut k = bl(lo ^ hi).max(2);
    if lo != 0 { k = k.max(lo.trailing_zeros() as usize + 1); }
    if k >= cap { return narrow.map(|h| (h, 0)); }
    let base = lo & !((1usize << k) - 1);
    // Activated controls perturb either the retained marker or the dropped-high base.
    if cfg!(test) && std::env::var("WL_DECODER7_BREAK_PORT").map_or(false, |v| v == "base") {
        return Some((k, base ^ 1));
    }
    Some((k, base))
}
fn dec_view(v: &[QubitId], win: (usize, usize)) -> (Vec<QubitId>, usize) {
    match dec_keep(win) {
        // negative control for the gate tests only: P3_BREAK=5 drops the marker bit 8 (stalled / finished shots alias)
        Some((h, base)) if cfg!(test) && std::env::var("P3_BREAK").map_or(false, |x| x.trim() == "5") => {
            (v[..h + 1].to_vec(), base)
        }
        Some((h, base)) if cfg!(test) && std::env::var("WL_DECODER7_BREAK_PORT").map_or(false, |v| v == "marker") => {
            (v[..h + 1].to_vec(), base)
        }
        Some((h, base)) => (v[..h].iter().chain(std::iter::once(&v[LB_BITS - 1])).copied().collect(), base),
        None => (v.to_vec(), 0),
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
    let (v, base) = dec_view(&u.la, w.lad);
    if gap_src(w.lad) {
        let v = v[super::greedyfrog_model::GAP_LOG..].to_vec();
        return Src { lo: 0, hi: hi - lo + 1, a: (lo - base) as isize, d: if gap_break(2) { -2 } else { 2 }, pre: m.pre[..v.len() - 1].to_vec(), v, late: false };
    }
    Src { lo: 0, hi: hi - lo + 1, a: (lo - base) as isize, d: 1, pre: m.pre[..v.len() - 1].to_vec(), v, late: false }
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

/// TC-TIE's room: LA's top lanes above the slot's window, where every passing shot reads 0 (late slots only; a window whose
/// shared top bits are not all 0 lends nothing here).
/// Dev override `WL_TC_IDLE=0|1` (this room and LA's shared top lanes on TC-TIE's comparator).
fn tc_idle_on() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("TC_IDLE", true)); *E }
fn tc_idle_lanes(u: &GreedyFrog, w: &Win) -> Vec<QubitId> {
    if !tc_idle_on() { return vec![]; }
    let (k, kv) = other_idle(w.lad);
    if kv != 0 || k >= LB_BITS || tc_plain(w) { vec![] } else { u.la[k..].to_vec() }
}
fn tc_idle(b: &mut B, u: &GreedyFrog, w: &Win) -> Vec<QubitId> {
    let l = tc_idle_lanes(u, w);
    b.free_n(&l);
    l
}
fn tc_idle_probe(b: &B, u: &GreedyFrog, w: &Win) {
    zero_probe(b, &tc_idle_lanes(u, w));
    zero_probe(b, &tie_lb_lanes(u, w, LB_BITS - 1));
}
/// B5HUNT-WALK TIE-LB: TC-TIE reads LB's bits below hb only (bits 0..5 in the borrow chain, 5..hb through g), so LB's
/// lanes from max(hb, k) up (k: IDLE-SHARED's first shared bit of the slot's window + 8, the bound that covers a stall's
/// excess) whose shared value is 0 are |0> on every passing shot and join the tie compare's room, like dd3's LA lanes.
/// `top`: LB_BITS where LB is unmarked (F2's DCMP), LB_BITS - 1 under mark_msb (lane 8 holds !a1: F2's gated compare,
/// I14's erase). No probes inside (the erase runs in a condition block); `tc_idle_probe` checks them before it.
/// Dev override `WL_TIE_LB=0|1`; negative control TIE_BREAK=3 (one live lane below hb lent too).
pub const TIE_LB: bool = true;
fn tie_lb_lanes(u: &GreedyFrog, w: &Win, top: usize) -> Vec<QubitId> {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("TIE_LB", TIE_LB));
    if !*E || tc_plain(w) { return vec![]; }
    let hb = ((usize::BITS - w.lb.1.max(wc()).leading_zeros()) as usize).min(LB_BITS);
    let (k, kv) = other_idle(w.lb);
    let lo = if tie_break(3) { hb.max(k) - 1 } else { hb.max(k) };
    (lo..top).filter(|&i| i < k || (kv >> (i - k)) & 1 == 0).map(|i| u.lb[i]).collect()
}
fn tie_lb(b: &mut B, u: &GreedyFrog, w: &Win, top: usize) -> Vec<QubitId> {
    let l = tie_lb_lanes(u, w, top);
    b.free_n(&l);
    l
}

/// out ^= act & [Y[W-L..W) > X[W-L..W)] on the top WC lanes (L = LB, already done-marked by the caller). When the
/// slot's window has every active LB >= WC the compare is unmasked and `gate` (the done flag, negated) keeps
/// finished shots at 0; `gate` None leaves finished shots' bit arbitrary (callers that mask it themselves).
/// out ^= the compare (None: the phase (-1)^compare instead, for a measured erase).
/// TC-DIRTY-H: dev override `WL_TC_DIRTY_H=0|1` (see top_compare).
fn tc_dirty_h() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("TC_DIRTY_H", true)); *E }
fn top_compare(b: &mut B, u: &GreedyFrog, out: Option<QubitId>, w: &Win, gate: Option<(QubitId, bool)>) {
    if tc_tie() && !tc_plain(w) {
        if let Some(g) = gate {
            // (the erase runs this in a condition block: no zero probes inside, `tc_idle_probe` checks those lanes before it)
            let il = tc_idle(b, u, w);
            let ll = tie_lb(b, u, w, LB_BITS - 1);
            let (r, lanes, lt, e) = tie_rec_d(b, u, w, out.is_none());
            b.play(&r, false);
            // TC-DIRTY-H (zfor-transfer, Q824): where the cap leaves no room for h, the phase (-1)^(a1 & [D < LB] & Y_first)
            // runs on a borrowed passenger lane t: t ^= g & lt; phase(t); t ^= g & lt; phase(t). The t-dependent parts cancel
            // and t comes back unchanged, so the net phase is the same (-1)^((g & lt) Y_first), for 2 CCX + 2 (WC - 1) CCZ.
            if out.is_none() && u.room(b) == 0 && tc_dirty_h() && !tie_break(1) {
                let t = match lt { Lt::One(_) => u.dirty[0], Lt::Or(..) => *u.dirty.last().unwrap() };
                if g.1 { b.x(g.0); }
                lt_and_into(b, u, &[(g.0, false)], lt, t);
                tie_phase(b, u, &e, t);
                lt_and_into(b, u, &[(g.0, false)], lt, t);
                tie_phase(b, u, &e, t);
                if g.1 { b.x(g.0); }
                b.play(&r, true);
                b.free_n(&lanes);
                for &q in &il { b.acquire(q); }
                for &q in &ll { b.acquire(q); }
                return;
            }
            // a1 & [D < LB] on a lane of its own, then the first difference's Y bit
            let h = b.alloc();
            if g.1 { b.x(g.0); }
            match lt {
                _ if tie_break(1) => b.cx(g.0, h),
                Lt::One(q) => b.and_c(g.0, q, h),
                Lt::Or(..) => lt_and_into(b, u, &[(g.0, false)], lt, h),
            }
            match out {
                Some(o) => {
                    // gate-level tests and non-reuse only: H-free form through a CCX on every lane
                    for j in 1..wc() {
                        let y = u.y[W - 1 - j];
                        if j == 1 {
                            b.x(e[0]);
                            let t = b.alloc();
                            b.and_c(h, e[0], t);
                            b.ccx(t, y, o);
                            b.and_u(h, e[0], t);
                            b.free(t);
                            b.x(e[0]);
                        } else {
                            b.cx(e[j - 1], e[j - 2]);
                            let t = b.alloc();
                            b.and_c(h, e[j - 2], t);
                            b.ccx(t, y, o);
                            b.and_u(h, e[j - 2], t);
                            b.free(t);
                            b.cx(e[j - 1], e[j - 2]);
                        }
                    }
                }
                None => tie_phase(b, u, &e, h),
            }
            match lt {
                _ if tie_break(1) => b.cx(g.0, h),
                Lt::One(q) => b.and_u(g.0, q, h),
                Lt::Or(..) => { lt_and_into(b, u, &[(g.0, false)], lt, h); zero_probe(b, &[h]); }
            }
            if g.1 { b.x(g.0); }
            b.free(h);
            b.play(&r, true);
            b.free_n(&lanes);
            for &q in &il { b.acquire(q); }
            for &q in &ll { b.acquire(q); }
            return;
        }
    }
    if tc_plain(w) || (tc_tie() && gate.is_none()) {
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
    top_compare_masked(b, u, out);
}

/// TC-TIE's recording: lt = [D < LB]. D, the leading equal lanes of X and Y from the top (lane W - 1 equal by a1), comes from
/// the thermometer e_j = [top j lanes equal]; bit k of D is the parity of the e_j with 2^k | j. X's lanes hold !(X ^ Y) while it
/// plays (e_2 is lane 1 itself), and [D < LB] runs in place on D's and LB's low 5 lanes, so the room need is WC + 5 lanes.
/// Returns (recording, lanes to free, lt, e), e[j - 2] = e_j.
/// TIE-OR (persona-mochimodev): [D < LB] as the OR of the borrow x and LB's merged high lane l, left unmaterialised, where
/// the cap leaves no room for the g lane (ng = 1). Consumers AND it with other literals: lits & (x | l) = lits ^ (lits & !x & !l).
/// Dev override `WL_TIE_OR=0|1`.
#[derive(Clone, Copy)]
enum Lt { One(QubitId), Or(QubitId, QubitId) }
fn tie_or() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("TIE_OR", true)); *E }
/// out ^= AND(lits) & lt
fn lt_and_into(b: &mut B, u: &GreedyFrog, lits: &[(QubitId, bool)], lt: Lt, out: QubitId) {
    match lt {
        Lt::One(q) => { let mut l = lits.to_vec(); l.push((q, false)); and_auto(b, u, &l, out); }
        Lt::Or(x, l) => {
            and_auto(b, u, lits, out);
            let mut l2 = lits.to_vec();
            l2.push((x, true));
            l2.push((l, true));
            and_auto(b, u, &l2, out);
        }
    }
}
/// TIE-DIET (zfor-transfer, Q823), ported: where the cap leaves no room for the whole recording, the last m thermometer
/// lanes are not stored; their D-bit reads and tie-phase terms are formed from e_(n-m) and the X lanes on borrowed lanes.
fn diet_break(k: u32) -> bool { std::env::var("ZX_DIET_BREAK").ok().and_then(|v| v.parse::<u32>().ok()) == Some(k) }
/// TIE-DIET literals of the tie-phase term j >= n - m: e_(n-m), x_(n-m) .. x_(j-1), !x_j.
fn diet_term_lits(u: &GreedyFrog, e: &[QubitId], n: usize, m: usize, j: usize) -> Vec<(QubitId, bool)> {
    let xl = |i: usize| u.x[W - 1 - i];
    let mut lits = vec![(e[n - m - 2], false)];
    for i in (n - m)..j { lits.push((xl(i), false)); }
    lits.push((xl(j), true));
    lits
}
fn tie_diet() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("TIE_DIET", true)); *E }
fn tie_rec(b: &mut B, u: &GreedyFrog, w: &Win) -> (Vec<super::builder::G>, Vec<QubitId>, Lt, Vec<QubitId>) {
    tie_rec_d(b, u, w, false)
}
fn tie_rec_d(b: &mut B, u: &GreedyFrog, w: &Win, diet_ok: bool) -> (Vec<super::builder::G>, Vec<QubitId>, Lt, Vec<QubitId>) {
    let n = wc();
    assert!(n < 32);
    let hb = ((usize::BITS - w.lb.1.max(n).leading_zeros()) as usize).min(LB_BITS);
    // LB < 96 here: bits 5 and 6 are never both on, so their OR is their XOR
    let merge = hb == 7 && w.lb.1 < 96;
    let ng = if hb <= 5 { 0 } else if merge { 1 } else { hb - 5 };
    let orf = ng == 1 && tie_or() && u.room(b) < (n - 2) + 5 + 1 + ng;
    let ng = if orf { 0 } else { ng };
    let need = (n - 2) + 5 + 1 + ng;
    let m = if diet_ok && tie_diet() { need.saturating_sub(u.room(b)).min(4) } else { 0 };
    let diet = m > 0;
    let chain = b.alloc_n(n - 2 - m);
    let dv = b.alloc_n(5);
    let c0 = b.alloc();
    let g = b.alloc_n(ng);
    let xl = |j: usize| u.x[W - 1 - j];
    let yl = |j: usize| u.y[W - 1 - j];
    let mut e = vec![xl(1)];
    e.extend(&chain);
    b.begin();
    for j in 1..n {
        b.cx(yl(j), xl(j));
        b.x(xl(j));
    }
    for j in 2..(n - m) {
        b.and_c(e[j - 2], xl(j), e[j - 1]);
    }
    b.x(dv[0]);
    let kn = if tie_break(2) { 4 } else { 5 };
    for j in 2..=n {
        for k in 0..kn {
            if j % (1 << k) == 0 {
                if diet && j > n - m {
                    let mut lits = vec![(e[n - m - 2], false)];
                    for i in (n - m)..j { lits.push((xl(i), false)); }
                    if !diet_break(1) { and_dirty(b, &lits, dv[k], &u.dirty); }
                } else {
                    b.cx(e[j - 2], dv[k]);
                }
            }
        }
    }
    // the borrow out of D - LB
    let mut x = c0;
    for i in 0..5 {
        let (t, l) = (dv[i], u.lb[i]);
        b.x(t);
        b.cx(l, t);
        b.cx(l, x);
        b.ccx(x, t, l);
        x = l;
    }
    // D's higher bits are 0: the borrow out is x | LB[i]
    if merge { b.cx(u.lb[6], u.lb[5]); }
    for (k, &q) in g.iter().enumerate() {
        let l = u.lb[5 + k];
        b.x(x);
        b.x(l);
        b.and_c(x, l, q);
        b.x(q);
        b.x(x);
        b.x(l);
        x = q;
    }
    let r = b.end();
    let lt = if orf { Lt::Or(x, u.lb[5]) } else { Lt::One(x) };
    let mut lanes = chain;
    lanes.extend(dv);
    lanes.push(c0);
    lanes.extend(g);
    (r, lanes, lt, e)
}

/// d = lits & the first difference's Y bit, on the thermometer of `tie_rec`: x ^= l & (e_j ^ e_(j + 1)) & Y_j over lanes j = 1..WC,
/// as a phase (`x` None) on the literal lane l.
fn tie_phase(b: &mut B, u: &GreedyFrog, e: &[QubitId], l: QubitId) {
    let n = wc();
    let m = (n - 1) - e.len();
    for j in 1..n {
        let y = u.y[W - 1 - j];
        if m > 0 && j >= n - m {
            // TIE-DIET: (-1)^(l & P & y), P = e_(n-m) & x_(n-m) & .. & x_(j-1) & !x_j, on a borrowed lane d (toggle twice)
            let lits = diet_term_lits(u, e, n, m, j);
            let free: Vec<QubitId> = u.dirty.iter().copied().filter(|&q| q != l).collect();
            let (d, rest) = (free[0], &free[1..]);
            for &(q, ng) in &lits { if ng { b.x(q); } }
            let pos: Vec<(QubitId, bool)> = lits.iter().map(|&(q, _)| (q, false)).collect();
            and_dirty(b, &pos, d, rest);
            b.ccz(l, d, y);
            and_dirty(b, &pos, d, rest);
            if !diet_break(2) { b.ccz(l, d, y); }
            for &(q, ng) in &lits { if ng { b.x(q); } }
        } else if j == 1 {
            b.x(e[0]);
            b.ccz(l, e[0], y);
            b.x(e[0]);
        } else {
            b.cx(e[j - 1], e[j - 2]);
            b.ccz(l, e[j - 2], y);
            b.cx(e[j - 1], e[j - 2]);
        }
    }
}

/// The phase of the plain top compare on the thermometer of `tie_rec`: the first difference's Y bit, no Toffoli.
fn tie_phase_plain(b: &mut B, u: &GreedyFrog, e: &[QubitId]) {
    let n = wc();
    let m = (n - 1) - e.len();
    for j in 1..n {
        let y = u.y[W - 1 - j];
        if m > 0 && j >= n - m {
            // TIE-DIET: (-1)^(P & y); two literals: one CCZ; more: a borrowed lane d (toggle twice)
            let lits = diet_term_lits(u, e, n, m, j);
            for &(q, ng) in &lits { if ng { b.x(q); } }
            if lits.len() == 2 {
                if !diet_break(3) { b.ccz(lits[0].0, lits[1].0, y); }
            } else {
                let (d, rest) = (u.dirty[0], &u.dirty[1..]);
                let pos: Vec<(QubitId, bool)> = lits.iter().map(|&(q, _)| (q, false)).collect();
                and_dirty(b, &pos, d, rest);
                b.cz(d, y);
                and_dirty(b, &pos, d, rest);
                if !diet_break(3) { b.cz(d, y); }
            }
            for &(q, ng) in &lits { if ng { b.x(q); } }
        } else if j == 1 {
            b.x(e[0]);
            b.cz(e[0], y);
            b.x(e[0]);
        } else {
            b.cx(e[j - 1], e[j - 2]);
            b.cz(e[j - 2], y);
            b.cx(e[j - 1], e[j - 2]);
        }
    }
}
fn tie_erase() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("TIE_ERASE", true)); *E }
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


// Minimal L-8 port from mochimodev decb04b3/cc55b536. No DECODER-7 or new window policy.
pub const L8_SHARE_PORT:bool=true;
fn l8_share_port()->bool {static E:std::sync::LazyLock<bool>=std::sync::LazyLock::new(||lever("L8_SHARE_PORT",L8_SHARE_PORT));*E}
fn l8_tc_only()->bool {std::env::var_os("L8_TC_ONLY").is_some()}
fn l8_break(n:u32)->bool {cfg!(test)&&std::env::var("L8_BREAK").map_or(false,|v|v==n.to_string())}
fn l8_compatible(w:&Win)->Option<usize>{
    let h=(usize::BITS-w.lb.1.max(wc()).leading_zeros())as usize;
    (!tc_plain(w)&&!tc_tie()&&roll_value()&&masked_write_always()&&h>=2&&h<LB_BITS-1&&dec_keep(w.lb)==Some((h,0))).then_some(h)
}
fn top_compare_masked(b: &mut B, u: &GreedyFrog, out: Option<QubitId>) {
    let _=top_compare_masked_shared(b,u,out,None,false);
}
fn top_compare_masked_shared(b: &mut B, u: &GreedyFrog, out: Option<QubitId>, keep: Option<usize>, keep_live: bool) -> Option<(Vec<QubitId>, usize, Vec<QubitId>, usize)> {
    // ladder over physical lanes W-WC .. W-1; ladder l <-> physical W - WC + l; f on where LB == WC - l
    let t: Vec<QubitId> = u.x[W - wc()..].to_vec();
    let s: Vec<QubitId> = u.y[W - wc()..].to_vec();
    // shots with LB >= WC start active at lane 0 (f0 = 1 would be wrong for done shots): toggle at l = 0 for any
    // LB >= WC is not expressible as one equality, so the window starts at the lane where LB == WC (l = 0) and
    // shots with LB > WC get an extra toggle source below via the "active from the start" flag `big`, computed
    // before the mask scratch exists (its comparator chain and the ladder's scratch never coexist).
    let big = b.alloc();
    if biglb_split() { big_lb_set(b, u, big); } else { big_lb_flip(b, u, big); }
    let m=match keep {Some(h)=>{let f=b.alloc(); Masked {f,t:b.alloc(),gf:f,chain:vec![],pre:b.alloc_n(h),c0:b.alloc(), t_owned: true }},None=>Masked::alloc_lean(b)};
    let view:Vec<QubitId>=match keep {Some(h)=>u.lb[..h].iter().chain(std::iter::once(&u.lb[LB_BITS-1])).copied().collect(),None=>u.lb.clone()};
    // f starts at `big`: emulate f0 = big by toggling f before the ladder; sources toggle where LB == WC - l (l >= 1)
    b.cx(big, m.f);
    let srcs = [Src { lo: 0, hi: wc(), v: view, a: wc() as isize, d: -1, pre: m.pre.clone(), late: false }];
    let sc = m.sc();
    let ld = Lad { t: &t, s: &s, c0: m.c0, srcs: &srcs, f0: false, cmpl: true, sc: &sc, g: &[] };
    let bank = if k1() & 1 != 0 { pool_for(b, u, t.len(), 0) } else { vec![] };
    let start=keep_live.then(|| { assert!(out.is_some() && keep.is_some()); super::mask::onehot_goto(b,&srcs[0].v,&m.pre,wc()); wc() });
    if !(out.is_none() && tc_phase() && super::mask::mid_phase_top(b, &ld, &bank, mw_break(3))) {
        let ru = super::mask::mup_mid_bank_from(b, &ld, &bank, start);
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
    let live=if keep_live {
        b.free(m.f);b.free(m.t);b.free(m.c0);
        Some((m.pre,if l8_break(1) {wc()^2}else{wc()},srcs[0].v.clone(),0))
    }else{m.free(b);None};
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
    live
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

/// LT-INLINE: run `f` with core = [a < bb + cin] on the |0> lane `core`, the compare's chain held open: its uncompute is the
/// chain's measured one, with no separate erase of core. Falls back to a compute and a measured erase without the room.
fn lt_cin_with(b: &mut B, u: &GreedyFrog, a: &[QubitId], bb: &[QubitId], cin: QubitId, core: QubitId, f: impl FnOnce(&mut B)) {
    if !(small_pooled() && u.room(b) >= pooled_need_add(a, bb, Cy::Q(cin))) {
        lt_cin_sm(b, u, a, bb, cin, Some(core));
        f(b);
        erase_mbu(b, core, |b| lt_cin_sm(b, u, a, bb, cin, None));
        return;
    }
    let n = a.len();
    for &q in a { b.x(q); }
    let mut p = plan_add(a, bb, Cy::Q(cin));
    let g = b.alloc_n(plan_lanes(&p));
    let cs = plan_carries(&mut p, Cy::Q(cin), &g);
    for i in 0..n - 1 {
        carry_step(b, &p, a, bb, &cs, i, true);
    }
    let (t, s) = (a[n - 1], bb[n - 1]);
    let Cy::Q(q) = cs[n - 1] else { panic!("LT-INLINE: constant top carry") };
    b.cx(q, t);
    b.cx(q, s);
    b.and_c(t, s, core);
    b.cx(q, core);
    f(b);
    b.cx(q, core);
    b.and_u(t, s, core);
    b.cx(q, s);
    b.cx(q, t);
    for i in (0..n - 1).rev() {
        carry_step(b, &p, a, bb, &cs, i, false);
        if let Step::Maj { q } = p[i] { b.cx(q, a[i]); }
    }
    b.free_n(&g);
    for &q in a { b.x(q); }
}

/// SWF-LEX: out ^= [a < bb + cin] = [a < bb] | [a == bb] & cin (cin a qubit, restored), or its phase (out None).
/// [a < bb + sY] on the 1-lane sY, or [a < bb] under NO-YSHIFT (`tmp`, |0>, stands in where there is no room for a pooled compare).
fn lt_sy(b: &mut B, u: &GreedyFrog, a: &[QubitId], bb: &[QubitId], sy: &[QubitId], tmp: QubitId, out: Option<QubitId>) {
    match sy.first() {
        Some(&c) => lt_cin_sm(b, u, a, bb, c, out),
        None if small_pooled() && u.room(b) >= pooled_need_add(a, bb, Cy::K(false)) => lt_pooled_c(b, a, bb, Cy::K(false), out),
        None => {
            zero_probe(b, &[tmp]);
            lt_cin_sm(b, u, a, bb, tmp, out);
        }
    }
}

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
fn rot_zero() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("ROT_ZERO", true)); *E }
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
            // ROT-ZERO: stage 3 leaves lane 0 at 0 on every shot (a step's rho >= 1 wraps a zero top lane there, rho = 0 with L = 0
            // has slack >= 1, and a fake never follows a swap). So where ctrl is 1 lane 4 was 0, where 0 lane 0 was: lane 4 ^= lane 0,
            // and lane 0 = ctrl & lane 4 erases by measurement.
            if promise && !inverse && stage == 3 && i == n - 5 && rot_zero() {
                let (z, k) = (x[0], x[4]);
                b.cx(z, k);
                b.and_u(ctrl, k, z);
                continue;
            }
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
    unrenorm_top_g(b, u, act, r, gate, s4, None, None)
}
/// unrenorm_top_s4 with B-SYNCGOV's hold gate: on window slots (gj = Some(j)) the measured r's phase repair recomputes
/// the prefixes with act = !h (taken after the barrel and the FUSE-S4 erase, which do not read act).
fn unrenorm_top_g(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, r: &[QubitId], gate: GateSpec, s4: Option<QubitId>,
                  gj: Option<usize>, ns: Option<QubitId>) {
    match s4 {
        Some(s4) => {
            rotate_three_fused_inv(b, &u.x, r, s4);
            assert!(u.room(b) + 1 >= FUSE_S4_NEED + 1, "FUSE-S4 erase room");
            fuse_s4_erase(b, &u.x, r, s4);
            b.free(s4);
        }
        None => rotate_three(b,&u.x,r,true,true),
    }
    let receipts=b.fresh_bits(3);
    for i in 0..3 { b.hmr_to(r[i],receipts[i]); }
    if let Some(j) = gj {
        assert!(act.is_none());
        let (l, t) = u.gov_lit(b, j, true);
        let ga = gov_act_on(b, l);
        match ns {
            None => unrenorm_phase(b, u, Some(ga), &receipts, gate),
            Some(n) => with_and(b, ga, (n, true), |b, aa| unrenorm_phase(b, u, Some(aa), &receipts, gate)),
        }
        gov_act_off(b, l);
        u.gov_lit_free(b, j, t, true);
        return;
    }
    match (act, ns) {
        (_, None) => unrenorm_phase(b, u, act, &receipts, gate),
        (Some(a), Some(n)) => with_and(b, a, (n, true), |b, aa| unrenorm_phase(b, u, Some(aa), &receipts, gate)),
        (None, Some(n)) => {
            b.x(n);
            unrenorm_phase(b, u, Some(n), &receipts, gate);
            b.x(n);
        }
    }
}
/// The phase repair of unrenorm's measured r (the prefixes recomputed with `act`).
fn unrenorm_phase(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, receipts: &[BitId], gate: GateSpec) {
    let receipts = receipts.to_vec();
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
            // UNREN-CCZ (persona-mochimodev): the phase (-1)^(p & z & g) as one CCZ instead of an AND onto a fresh lane
            // and a CZ (the lane bound the peak at cap 818). Exact. Dev override WL_UNREN_CCZ=0|1.
            let (g, ng) = lg.as_ref().unwrap().g(jt);
            if std::env::var("WL_UNREN_CCZ").map_or(true, |v| v.trim() == "1") {
                if ng { b.x(g); }
                b.ccz(pj, z[jt], g);
                if ng { b.x(g); }
            } else {
                with_and(b, z[jt], (g, ng), |b, t| b.cz(pj, t));
            }
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
    /// The counter lanes the arithmetic touches (CNT7, optionally narrowed to the current schedule tail).
    fn cntw(&self, w: &Win) -> &[QubitId] {
        let c: &[QubitId] = if cnt7() { if mw_break(2) { &self.cnt[1..] } else { &self.cnt[..CNT_BITS - 1] } } else { &self.cnt };
        if cnt_tail_port() && !mw_break(2) {
            // Activated control removes a live counter bit on a non-trivial tail boundary.
            let n = if cfg!(test) && std::env::var("WL_CNT_TAIL_BREAK_PORT").is_ok() && w.slot >= 245 {
                w.cntb.saturating_sub(1).max(1)
            } else { w.cntb };
            &c[..n.min(c.len())]
        } else { c }
    }
    /// c += ctrl
    fn cnt_inc(&self, b: &mut B, ctrl: QubitId, w: &Win) {
        let anc = b.alloc_n(self.cntw(w).len() - 1);
        super::arith::dec(b, ctrl, self.cntw(w), &anc);
        b.free_n(&anc);
    }
    /// c -= ctrl
    fn cnt_dec(&self, b: &mut B, ctrl: QubitId, w: &Win) {
        let anc = b.alloc_n(self.cntw(w).len() - 1);
        super::arith::inc(b, ctrl, self.cntw(w), &anc);
        b.free_n(&anc);
    }
    /// out ^= [c == 0] (all counter lanes one)
    fn cnt_zero_into(&self, b: &mut B, out: QubitId, w: &Win) {
        let lits: Vec<(QubitId, bool)> = self.cntw(w).iter().map(|&q| (q, false)).collect();
        and_into(b, &lits, out);
    }

    pub fn alloc(b: &mut B) -> GreedyFrog {
        GreedyFrog { cmp_in: None, cmp_held: None, gov: vec![], sf: None, gov_stack: vec![], gov_slot: 0, x: b.alloc_n(W), y: b.alloc_n(W), la: b.alloc_n(LB_BITS), lb: b.alloc_n(LB_BITS),
              dirty: b.alloc_n(TEST_DIRTY),
              cap: std::env::var("GREEDYFROG_TEST_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(u64::MAX),
              cnt: vec![], par: b.alloc() }.with_cnt()
    }

    /// sw ^= act & [LA != 0] & X[W-1] & (LA < LB | LA == LB & Y top > X top)   (F9). The top compare is unmasked even
    /// when LB < WC: with LA == LB the values differ inside their top LB lanes unless A' == B, and A' == B forces
    /// B = gcd = 1, so LB == 1 is excluded instead (A' == B == 1 never swaps).
    /// sw ^= F9 (out None: the phase (-1)^F9, for a measured erase). The temporaries are erased by measurement.
    fn swap_flag(&self, b: &mut B, z0: Option<QubitId>, out: Option<QubitId>, w: &Win, keep: bool) -> Option<QubitId> {
        self.swap_flag_g(b, z0, out, w, keep, &[], false)
    }

    // ---------------------------------------------------------------- B-SYNCGOV record helpers
    /// A literal true iff c < j (the shot is not held where h = [c >= j]), with the lane computed for it (None: a record
    /// lane itself). [c < j] = OR over the set bits i of j of (c_i = 0 and c above i equal to j above i): disjoint terms.
    /// `inv`: GOV_BREAK=1 reads the neighbouring level there.
    fn gov_lit(&self, b: &mut B, j: usize, inv: bool) -> ((QubitId, bool), Option<QubitId>) {
        let nb = self.gov.len();
        let k = 1usize << nb;
        let j = if inv && gov_break(1) { if j + 1 < k { j + 1 } else { j - 1 } } else { j };
        let terms = self.gov_terms(j);
        if terms.len() == 1 && terms[0].len() == 1 {
            return (terms[0][0], None);
        }
        let t = b.alloc();
        for term in &terms {
            and_auto(b, self, term, t);
        }
        ((t, false), Some(t))
    }
    fn gov_terms(&self, j: usize) -> Vec<Vec<(QubitId, bool)>> {
        let nb = self.gov.len();
        let mut terms = vec![];
        for i in (0..nb).rev() {
            if (j >> i) & 1 == 1 {
                let mut l = vec![(self.gov[i], true)];
                for h in i + 1..nb {
                    l.push((self.gov[h], (j >> h) & 1 == 0));
                }
                terms.push(l);
            }
        }
        terms
    }
    /// Erase gov_lit's lane (measured; the repair is the XOR of the terms' phases).
    fn gov_lit_free(&self, b: &mut B, j: usize, t: Option<QubitId>, inv: bool) {
        let Some(t) = t else { return };
        let nb = self.gov.len();
        let j = if inv && gov_break(1) { if j + 1 < (1 << nb) { j + 1 } else { j - 1 } } else { j };
        let terms = self.gov_terms(j);
        erase_mbu(b, t, |b| for term in &terms { phase_and(b, term); });
        b.free(t);
    }
    /// c ^= level(LA + LB): LB += LA (M <= 510 in 9 bits), thermometer g_j = [M <= th_j], c_i = XOR of g_j over the
    /// multiples j of 2^i, thermometer erased, LB restored. The same map writes the record (forward) and erases it.
    fn gov_thermo(&self, b: &mut B, g: &GovCfg, c: &[QubitId]) {
        add_sm(b, self, &self.lb, &self.la, false, false);
        let k = g.levels.len();
        let t = b.alloc_n(k - 1);
        for j in 1..k {
            ge_auto(b, self, &self.lb, g.th[j] as isize + 1, t[j - 1]);
            b.x(t[j - 1]);
        }
        for (i, &ci) in c.iter().enumerate() {
            for j in 1..k {
                if j % (1 << i) == 0 {
                    b.cx(t[j - 1], ci);
                }
            }
        }
        for j in (1..k).rev() {
            b.x(t[j - 1]);
            ge_erase(b, self, &self.lb, g.th[j] as isize + 1, t[j - 1]);
        }
        b.free_n(&t);
        add_sm(b, self, &self.lb, &self.la, false, true);
    }
    /// Erase the record (inverse slot s* - 1, plain LA / LB, M = LA + LB as at the sync slot's pre-state).
    fn gov_erase(&mut self, b: &mut B) {
        let g = gov_cfgs().iter().find(|g| g.slot == self.gov_slot).expect("SYNC-GOV record without config");
        let c = std::mem::take(&mut self.gov);
        self.gov_thermo(b, g, &c);
        b.free_n(&c);
        self.gov = self.gov_stack.pop().unwrap_or_default();
        let at = gov_cfgs().iter().position(|h| h.slot == g.slot).unwrap();
        self.gov_slot = if at == 0 { 0 } else { gov_cfgs()[at - 1].slot };
    }
    /// swap_flag with extra literals `g` in the flag's AND (B-SYNCGOV: !h_(s+1) on the inverse erases; STALL-PAIR: !ns).
    fn swap_flag_g(&self, b: &mut B, z0: Option<QubitId>, out: Option<QubitId>, w: &Win, keep: bool,
                   g: &[(QubitId, bool)], gate_d: bool) -> Option<QubitId> {
        self.swap_flag_h(b, z0, out, w, keep, g, gate_d, None)
    }
    /// CMP-D: out ^= [Y top > X top] & X[W-1] & g (at most the one flag literal), or its phase (out None).
    fn cmp_gated(&self, b: &mut B, out: Option<QubitId>, g: &[(QubitId, bool)]) {
        let t: Vec<QubitId> = self.x[W - wc()..top_cmp_hi()].to_vec();
        let s: Vec<QubitId> = self.y[W - wc()..top_cmp_hi()].to_vec();
        let c0 = b.alloc();
        let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
        assert!(g.len() <= 1, "CMP-D: the flag alone gates the rule");
        let xt = self.x[W - 1];
        let gq = g.first().map(|&(n, ng)| {
            let q = b.alloc();
            if ng { b.x(n); }
            b.and_c(xt, n, q);
            if ng { b.x(n); }
            q
        });
        let pool = pool_for(b, self, t.len(), 0);
        plain_compare(b, &t, &s, c0, &sc, out, Some((gq.unwrap_or(xt), false)), &pool);
        b.free_n(&pool);
        if let (Some(q), Some(&(n, ng))) = (gq, g.first()) {
            if ng { b.x(n); }
            b.and_u(xt, n, q);
            if ng { b.x(n); }
            b.free(q);
        }
        b.free(c0);
    }
    /// `held` (phase only, CMP-D): the comparator is already on this lane, gated as `cmp_gated`, and stays there.
    #[allow(clippy::too_many_arguments)]
    fn swap_flag_h(&self, b: &mut B, z0: Option<QubitId>, out: Option<QubitId>, w: &Win, keep: bool,
                   g: &[(QubitId, bool)], gate_d: bool, held: Option<QubitId>) -> Option<QubitId> {
        let lt = b.alloc();
        let eq = b.alloc();
        let cmp = b.alloc();
        let nz = b.alloc();
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
            b.free_n(&[lt, eq]);
            let core = b.alloc();
            // TC-TIE: a kept comparator is the plain one on every shot; the rule's carry-in takes [LB != 1] on a lane of its own.
            // NE1-NZ: that lane also replaces [LA != 0]: LA = 0 needs B = 1 (gcd 1), and with LB = 1 the rule never swaps
            let raw = tc_tie() && w.lb.0 <= 1;
            let (cin, ne1) = if raw {
                let t: Vec<QubitId> = self.x[W - wc()..top_cmp_hi()].to_vec();
                let s: Vec<QubitId> = self.y[W - wc()..top_cmp_hi()].to_vec();
                let c0 = b.alloc();
                let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
                let pool = pool_for(b, self, t.len(), 0);
                plain_compare(b, &t, &s, c0, &sc, Some(cmp), None, &pool);
                b.free_n(&pool);
                b.free(c0);
                let ne1 = b.alloc();
                and_auto(b, self, &eq_lits(&self.lb[..ln], 1), ne1);
                b.x(ne1);
                let cg = b.alloc();
                b.and_c(cmp, ne1, cg);
                (cg, Some(ne1))
            } else if let Some(h) = held {
                (h, None)
            } else if gate_d {
                // CMP-D: cmp = [Y top > X top] & X[W-1] & !ns
                self.cmp_gated(b, Some(cmp), g);
                (cmp, None)
            } else {
                cmp_into(b, self, Some(cmp));
                (cmp, None)
            };
            let lk = f9_lanes(w, ln);
            // NZ-CONST: on act-constant slots no passing shot reaches LA = 0 (a finishing step fails there already)
            let nz_on = !(nz_const() && w.act_const) && ne1.is_none();
            if nz_on { zero_auto(b, self, &self.la[..ln], nz); } // nz = [LA == 0]
            let mut lits: Vec<(QubitId, bool)> = if swf_nz() { vec![] } else { z0.map(|z| vec![(z, true)]).unwrap_or_default() };
            if nz_on && !(swf_nz() && mw_break(1)) { lits.push((nz, true)); }
            if let Some(n) = ne1 { lits.push((n, false)); }
            lits.extend([(self.x[W - 1], false), (core, false)]);
            lits.extend(g.iter().copied());
            lt_cin_with(b, self, &self.la[..lk], &self.lb[..lk], cin, core, |b| match out {
                Some(sw) => and_auto(b, self, &lits, sw),
                None => phase_and(b, &lits),
            });
            let zl: Vec<(QubitId, bool)> = self.la[..ln].iter().map(|&q| (q, true)).collect();
            if nz_on { erase_and(b, self, nz, &zl); }
            if let Some(ne1) = ne1 {
                b.and_u(cmp, ne1, cin);
                b.free(cin);
                b.x(ne1);
                erase_and(b, self, ne1, &eq_lits(&self.lb[..ln], 1));
                b.free(ne1);
            }
            if keep {
                // DCMP-REUSE: cmp stays live for the successor's F2 (fwd_slot applies cmp ^= sw after the swap)
                b.free_n(&[core, nz]);
                return Some(cmp);
            }
            if held.is_some() {
            } else if raw {
                let t: Vec<QubitId> = self.x[W - wc()..top_cmp_hi()].to_vec();
                let s: Vec<QubitId> = self.y[W - wc()..top_cmp_hi()].to_vec();
                erase_mbu(b, cmp, |b| {
                    let c0 = b.alloc();
                    let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
                    let pool = pool_for(b, self, t.len(), 0);
                    plain_compare(b, &t, &s, c0, &sc, None, None, &pool);
                    b.free_n(&pool);
                    b.free(c0);
                });
            } else {
                erase_mbu(b, cmp, |b| cmp_into(b, self, None));
            }
            b.free_n(&[core, cmp, nz]);
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
        lits.extend(g.iter().copied());
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

    /// One forward slot (F1..F11). Returns the measurement record.
    pub fn fwd_slot(&mut self, b: &mut B, w: &Win) -> SlotBits {
        self.fwd_slot_next(b, w, None)
    }

    /// One forward slot (F1..F11) followed by the forward slot with window `next` (None: no successor, or the
    /// successor is not run by this caller). LS-3 DCMP-REUSE hands F9's comparator to a plain successor's F2.
    pub fn fwd_slot_next(&mut self, b: &mut B, w: &Win, next: Option<&Win>) -> SlotBits {
        super::mask::set_borrowed(&self.dirty);
        // B-SYNCGOV: window slots gate a1 and rho by !h (the record is written by slot s* - 1, after its F8)
        let gv = gov_cfg_at(w.slot);
        let gj = if self.gov.is_empty() { None } else { gv.and_then(|g| g.jmin(w.slot)) };
        prof(b, "f.z0");
        p3(b, self, "f.z0");
        // F1
        // FWD-ACT-CONST (B-CRUMBS, ST-001): on slots where no shot can have finished (the inverse's act_const), act = 1
        // classically: no done flag, no counter increment, no flag erase (the inverse already skips them there)
        let zo = if fwd_act_const() && w.act_const { None } else { Some(b.alloc()) };
        // window slots are act-constant (all shots active); with FWD_ACT_CONST off the forward still carries act
        assert!(gj.is_none() || w.act_const, "SYNC-GOV window slots must be act-constant");
        let ln = len_n(w);
        if let Some(z0) = zo {
            zero_into(b, &self.la[..ln], z0);
            self.cnt_inc(b, z0, w);
        }
        // STALL-PAIR: si = this slot is an add-back (a1 = 0 there)
        let si = self.sf.take();
        let fr = stall_free(w);
        // a1 = act & X[W-1]: the slot steps (else it is a stall that only renormalises, or finished)
        let a1 = b.alloc();
        match (zo, gj) {
            (_, Some(j)) => {
                // B-SYNCGOV: a1 = act & X[W-1] & !h (a held shot is a zero-rotation stall)
                let (l, t) = self.gov_lit(b, j, false);
                let mut lits = vec![(self.x[W - 1], false), l];
                if let Some(z0) = zo { lits.push((z0, true)); }
                if let Some(q) = si { lits.push((q, true)); }
                and_into(b, &lits, a1);
                self.gov_lit_free(b, j, t, false);
            }
            (Some(z0), None) => {
                if let Some(q) = si {
                    and_into(b, &[(z0, true), (self.x[W - 1], false), (q, true)], a1);
                } else {
                b.x(z0);
                b.ccx(z0, self.x[W - 1], a1);
                b.x(z0);
                }
            }
            (None, None) => {
                if let Some(q) = si {
                    b.x(q);
                    b.ccx(q, self.x[W - 1], a1);
                    b.x(q);
                } else {
                    b.cx(self.x[W - 1], a1)
                }
            }
        }
        prof(b, "f.dcmp");
        p3(b, self, "f.dcmp");
        // F2: d = a1 & [B > A >> e] (top window)
        let mut d = b.alloc();
        // TERM-LAST: d = 0 on every passing shot of the last slot (d stays |0>; a carried DCMP comparator is consumed)
        let tm = term(w);
        let nd = no_d(w);
        let mut live=None;
        if let Some(c) = self.cmp_in.take() {
            // DCMP-REUSE: c = the predecessor's cmp ^ sw = [Y top > X top] (top tie at a swap excepted)
            assert!(tc_plain(w) || tc_tie(), "DCMP-REUSE successor must run the plain top compare");
            if cmp_is_d(w) {
                b.free(d);
                d = c;
            } else if tc_plain(w) {
                b.and_c(a1, c, d);
            } else {
                // TC-TIE: the comparator stands in for the plain compare (LA's shared top lanes lend room)
                let il = if tc_idle_on() { ladder_idle(b, &self.la, w.lad) } else { (vec![], vec![]) };
                zero_probe(b, &tie_lb_lanes(self, w, LB_BITS));
                let ll = tie_lb(b, self, w, LB_BITS);
                let (r, lanes, lt, e) = tie_rec_d(b, self, w, true);
                b.play(&r, false);
                let lits = vec![(a1, false), (c, false)];
                if tie_break(1) { and_auto(b, self, &lits, d); } else { lt_and_into(b, self, &lits, lt, d); }
                // TIE-ERASE: on the live thermometer the plain compare's phase is Clifford: Z(c) = prod CZ(e_j ^ e_(j+1), Y_j)
                if tie_erase() {
                    erase_mbu(b, c, |b| tie_phase_plain(b, self, &e));
                }
                b.play(&r, true);
                b.free_n(&lanes);
                for &q in &ll { b.acquire(q); }
                ladder_idle_back(b, il);
                if tie_erase() {
                    b.free(c);
                }
            }
            if !cmp_is_d(w) && (tc_plain(w) || !tie_erase()) {
                erase_mbu(b, c, |b| top_compare(b, self, None, w, None));
                b.free(c);
            }
        } else if !nd && (l8_share_port() || l8_tc_only()) && l8_compatible(w).is_some() {
            if std::env::var_os("L8_PROFILE").is_some(){eprintln!("L8_PORT slot={} share={} h={}",w.slot,l8_share_port(),l8_compatible(w).unwrap());}
            mark_msb(b,a1,&self.lb);
            live=top_compare_masked_shared(b,self,Some(d),l8_compatible(w),l8_share_port());
            if live.is_none(){mark_msb(b,a1,&self.lb);}
        } else if !nd {
            mark_msb(b, a1, &self.lb);
            top_compare(b, self, Some(d), w, Some((a1, false)));
            mark_msb(b, a1, &self.lb);
        }
        prof(b, "f.drot");
        p3(b, self, "f.drot");
        // F3
        if !nd {
            crot_up(b, d, &self.x, 1);
        }
        prof(b, "f.value");
        p3(b, self, "f.value");
        // F4: value chain, subtract where a1
        if let Some(z0) = zo { b.x(z0); } // z0 now holds act
        let act = zo;
        let mwa = masked_write_always();
        if live.is_some(){
            if !l8_break(2){mark_done_inv(b,act,&self.lb[..LB_BITS-1]);}
            if l8_break(3){b.cz(self.x[0],self.x[1]);}
        }else{
            mark_done_inv(b, act, &self.lb);
            if mwa { mark_stall(b, act, a1, &self.lb); }
        }
        // B-SYNCGOV: no ACT_PARK on window slots (FWD_ACT_CONST off only): a held shot's LB / LA - d need not lie in
        // the slot's step window
        // STALL-PAIR: the last slot gates the ordinary lanes by a1 | s; the others do not gate them
        let eg_last = if stall_pair() && !fr && si.is_some() {
            let e = b.alloc();
            b.cx(a1, e);
            b.cx(si.unwrap(), e);
            Some(e)
        } else { None };
        let pk = act.filter(|_| gj.is_none()).and_then(|a| act_park(b, a, &self.lb, w.lb));
        assert!(live.is_none()||pk.map_or(true,|i|i>=live.as_ref().unwrap().0.len()),"L8 ACT_PARK aliases view");
        if fr { super::mask::set_ord_gate(Some(ALWAYS), None); } else if let Some(e) = eg_last { super::mask::set_ord_gate(Some(e), None); }
        let vord = if stall_pair() && w.slot >= 1 {
            let (xv, fl) = sp_value(self, w, fr, si, a1, None);
            super::mask::set_ladx(Some(xv));
            fl
        } else { vec![] };
        sp_flip(b, si, &vord);
        FWD_D.with(|c| c.set(Some(d)));
        let rv = value_pass_shared(b, self, w, true, a1, None, mwa, None, live);
        FWD_D.with(|c| c.set(None));
        sp_flip(b, si, &vord);
        super::mask::set_ladx(None);
        if let Some(a) = act { act_unpark(b, a, &self.lb, pk); }
        if mwa { mark_stall(b, act, a1, &self.lb); }
        mark_done_inv(b, act, &self.lb);
        prof(b, "f.cof");
        p3(b, self, "f.cof");
        // F5: LA -= d; cofactor chain, add where a1
        if !nd {
            let ld = la_d_lanes(w, ln);
            let anc = b.alloc_n(ld - 1);
            super::arith::dec(b, d, &self.la[..ld], &anc);
            b.free_n(&anc);
        }
        mark_done_inv(b, act, &self.la);
        if mwa { mark_stall(b, act, a1, &self.la); }
        let pk = act.filter(|_| gj.is_none()).and_then(|a| act_park(b, a, &self.la, w.lad));
        let mut rc = RollRec::default();
        // STALL-PAIR: finished shots keep their DONE counter lanes (Y[0..n), the ladder's last lanes): those write under act
        let tail = sp_tail(self, w, act, pk);
        if fr { super::mask::set_ord_gate(Some(ALWAYS), tail); } else if let Some(e) = eg_last { super::mask::set_ord_gate(Some(e), tail); }
        let cord = if stall_pair() && w.slot >= 1 {
            let (xc, fl) = sp_cof(self, w, fr, si, a1, None);
            super::mask::set_ladx(Some(xc));
            fl
        } else { vec![] };
        sp_flip(b, si, &cord);
        if lane0_direct() {
            // x0 = X[0] here (F4 cleared A's wrapped MSB where d = 1)
            let m = Masked::alloc_ladder_w(b, w.lad);
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
            let m = Masked::alloc_ladder_w(b, w.lad);
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
        sp_flip(b, si, &cord);
        super::mask::set_ladx(None);
        super::mask::set_ord_gate(None, None);
        if let Some(e) = eg_last {
            b.cx(si.unwrap(), e);
            b.cx(a1, e);
            b.free(e);
        }
        if let Some(a) = act { act_unpark(b, a, &self.la, pk); }
        if mwa { mark_stall(b, act, a1, &self.la); }
        mark_done_inv(b, act, &self.la);
        // STALL-PAIR: the flag lane goes from s to ns = !(s ^ a1) (the last slot: s is erased; no fake there)
        let ns = if fr {
            let q = match si { Some(q) => q, None => b.alloc() };
            b.cx(a1, q);
            b.x(q);
            Some(q)
        } else {
            if let Some(q) = si {
                sp_last(self, b, act, a1, q);
                zero_probe(b, &[q]);
                b.free(q);
            }
            None
        };
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
        if let Some(j) = gj {
            // B-SYNCGOV: rho = !h & min(lz, LA, 7) (act = 1 classically on window slots)
            let (l, t) = self.gov_lit(b, j, false);
            let ga = gov_act_on(b, l);
            match (act, ns) {
                // FWD_ACT_CONST off: act' = act & !h on a fresh lane
                (Some(a), None) => with_and(b, a, (ga, false), |b, aa| renorm_top(b, &self.x, Some(aa), &r, gate_spec(&self.la, w))),
                (None, None) => renorm_top(b, &self.x, Some(ga), &r, gate_spec(&self.la, w)),
                (Some(a), Some(n)) => with_and(b, a, (ga, false), |b, aa| with_and(b, aa, (n, true), |b, ab| renorm_top(b, &self.x, Some(ab), &r, gate_spec(&self.la, w)))),
                (None, Some(n)) => with_and(b, ga, (n, true), |b, aa| renorm_top(b, &self.x, Some(aa), &r, gate_spec(&self.la, w))),
            }
            gov_act_off(b, l);
            self.gov_lit_free(b, j, t, false);
        } else {
            match (act, ns) {
                (_, None) => renorm_top(b, &self.x, act, &r, gate_spec(&self.la, w)),
                (Some(a), Some(n)) => with_and(b, a, (n, true), |b, aa| renorm_top(b, &self.x, Some(aa), &r, gate_spec(&self.la, w))),
                (None, Some(n)) => {
                    b.x(n);
                    renorm_top(b, &self.x, Some(n), &r, gate_spec(&self.la, w));
                    b.x(n);
                }
            }
        }
        if let Some(z0) = zo { b.x(z0); } // back to z0
        add_sm(b, self, &self.la[..rho_lanes(w, ln)], &r, false, true);
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
        // B-SYNCGOV: slot s* - 1 writes the record from its post-F8 state (M = LA + LB, swap-invariant: the sync slot's
        // pre-state M); from here to the hold's end F9 is gated by !h_(s+1) (a held shot's swap is deferred to the F10
        // of its last held slot, where F9 reads it again on the unchanged state)
        if let Some(g) = gv {
            if w.slot + 1 == g.slot && self.gov_slot != g.slot {
                prof(b, "f.gov");
                assert!(w.act_const, "SYNC-GOV: the record slot must be act-constant");
                let c = b.alloc_n(g.bits);
                self.gov_thermo(b, g, &c);
                if !self.gov.is_empty() { self.gov_stack.push(std::mem::take(&mut self.gov)); }
                self.gov = c;
                self.gov_slot = g.slot;
                prof(b, "f.renorm");
            }
        }
        let gj1 = if self.gov.is_empty() || gov_break(3) { None } else { gv.and_then(|g| g.jmin(w.slot + 1)) };
        // F9, F10
        let sw = b.alloc();
        // TERM-LAST: sw = 0 on every passing shot of the last slot (sw stays |0>)
        if !tm {
            let keep = dcmp_reuse() && swf_lex() && dcmp_keep(w, next);
            let gl = gj1.map(|j| self.gov_lit(b, j, false));
            let mut gs: Vec<(QubitId, bool)> = gl.iter().map(|l| l.0).collect();
            if let (Some(n), false) = (ns, sp_break(3)) { gs.push((n, true)); }
            let kc = self.swap_flag_g(b, zo, Some(sw), w, keep, &gs, keep && next.map_or(false, cmp_is_d));
            if let (Some(j), Some((_, t))) = (gj1, gl) { self.gov_lit_free(b, j, t, false); }
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
            let cl: Vec<(QubitId, bool)> = self.cntw(w).iter().map(|&q| (q, false)).collect();
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
        self.sf = ns;
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
pub const NB: usize = 24;
/// division rows (capacity; per-slot counts come from the envelope)
pub const KROWS: usize = 21;
/// Offset of the divisor-length register while the decode's masks run: LA holds u' = LA + sX - UOFF, so the divisor's
/// bit length is mX = NB - u'. Mask-relevant shots have u' in [0, NB] (bits 0..5); u' < 0 (bit 8) means mX > NB.
pub(crate) const UOFF: usize = CW - NB;

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
            if fwd { and_auto(b, u, &lits(j), s[j]) } else { erase_and(b, u, s[j], &lits(j)) }
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
fn park_junk(b: &mut B, u: &GreedyFrog, w: &Win, z: &[QubitId], top: usize, fwd: bool) {
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
        park_cell(b, f, u.x[l], z[l - lo], fwd);
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

/// PARK-AND: a parked lane is z = f & x with x cleared where f, on a |0> z: parking is one AND, and the return x ^= z leaves z
/// = f & x, erased by measurement for no Toffoli. Dev override `WL_PARK_AND=0|1`.
fn park_cell(b: &mut B, f: QubitId, x: QubitId, z: QubitId, fwd: bool) {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("PARK_AND", true));
    if !*E {
        b.cswap(f, x, z);
    } else if fwd {
        b.and_c(f, x, z);
        b.cx(z, x);
    } else {
        b.cx(z, x);
        b.and_u(f, x, z);
    }
}

/// CK-ROWS: the undo rows are recorded and played backwards; a recording holds no measurement, so an anchored row leaves its
/// position here. Played backwards a row's ladder is t + s + c0 in the complement frame: on ~t' the sum is ~t and each carry
/// is the original's (s == c: both s; s != c: ~t' = t and the carry is t), so the same chain forms the receipts' carries.
#[allow(clippy::type_complexity)]
thread_local! { static CK_ROW_Q: std::cell::RefCell<Vec<(usize, Vec<QubitId>, Vec<QubitId>, QubitId, Vec<QubitId>, Vec<Option<BitId>>, QubitId)>> = const { std::cell::RefCell::new(vec![]) }; }
fn play_undo_rows(b: &mut B, rec: &[super::builder::G]) {
    let items = CK_ROW_Q.with(|q| std::mem::take(&mut *q.borrow_mut()));
    let mut end = rec.len();
    for (pos, t, s, c0, gp, rc, tt) in items.into_iter().rev() {
        b.play(&rec[pos..end], true);
        for &q in &t { b.x(q); }
        super::mask::ck_ordinary(b, &t, &s, c0, &gp, &rc, false, |b, tc| b.cx(tc, tt));
        for &q in &t { b.x(q); }
        end = pos;
    }
    b.play(&rec[..end], true);
}
fn ck_rows() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("CK_ROWS", true)); *E }
/// placeholder for a RowTmp lane not held (PARK-SPLIT)
const NOQ: QubitId = QubitId(u64::MAX);

/// PARK-SPLIT: `park_junk` (same gates) with f, the decoder prefix and the comparators' chain on the given |0> lanes
/// first, the rest taken from the room.
fn park_junk_t(b: &mut B, u: &GreedyFrog, w: &Win, z: &[QubitId], top: usize, tmp: &[QubitId], fwd: bool) {
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
        park_cell(b, f, u.x[l], z[l - lo], fwd);
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
            park_cell(b, f, u.x[l], z[l - lo], fwd);
            if !(brk && l == lo) {
                toggle(b, NB - l);
            }
        }
    } else {
        for l in lo..top {
            if !(brk && l == lo) {
                toggle(b, NB - l);
            }
            park_cell(b, f, u.x[l], z[l - lo], fwd);
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
            park_cell(b, f, u.x[l], z[l - lo], fwd);
            tog(b);
        } else {
            tog(b);
            park_cell(b, f, u.x[l], z[l - lo], fwd);
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
        park_junk_t(b, u, w, z, top, tmp, fwd);
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
    // B5SPEND REFIT-1 (LS-4 NB-TAIL): plain rows run over the window's top nb lanes (rem / div lanes 0..nb)
    let nb = w.nb;
    assert!(nb == NB || (w.mx >= NB + 1 && !parked && partial.is_none()), "NB-TAIL: nb < NB needs window-plain rows");
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
        let hi_i = if parked { (j + top).min(NB) } else { nb } as isize;
        let nbt1 = nb < NB && cfg!(test) && std::env::var("NBT_BREAK").map_or(false, |v| v.trim() == "1");
        let t: Vec<QubitId> = (lo..hi_i).rev().map(|i| rt.rem(u, i)).collect();
        let mut s: Vec<QubitId> = (lo..hi_i).rev()
            .map(|i| if i >= j as isize { u.x[i as usize - j + usize::from(nbt1)] } else { rt.zero() }).collect();
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
        // SYM-R-25 ROUND-THE-DIVISOR: carry-in ^= the top dropped divisor bit X[NB - j] (window-plain rows j >= 1; the
        // full-width ladder: hi_i == NB). The carry-in lane is the sign lane on ROW-F rows, f otherwise; read-only in
        // the ladder, restored before the second flip.
        let rb = (round_div() && j >= 1 && w.mx >= nb - j + 1 && hi_i == nb as isize && !nbt1).then(|| u.x[nb - j]);
        let cin_lane = match (rowf, sign) { (true, Some(sg)) => sg, _ => c0f };
        if let Some(r) = rb {
            assert!(!masked_row(j) && !s.contains(&r));
            b.cx(r, cin_lane);
        }
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
            // CK-ROWS: an undo row longer than its pool takes the anchored chain instead of Cuccaro cells past the pool
            let ck_row = matches!(roll, RowRoll::Rev(_)) && ck_rows() && !gp.is_empty() && gp.len() < n - 1
                && gp.len() >= super::mask::ck_need(n - 1);
            if ck_row {
                let rc = match &roll { RowRoll::Rev(recs) => recs[j].rc.clone(), _ => vec![] };
                let pos = b.mark_pos();
                CK_ROW_Q.with(|q| q.borrow_mut().push((pos, t[..n - 1].to_vec(), s.clone(), c0, gp.to_vec(), rc, tt)));
            } else {
            let ru = if yroll { vec![] } else { super::mask::mup_mid(b, &ld) };
            b.play(&ru, false);
            if !yroll { b.cx(top_carry(&ld), tt); }
            }
            // negative control for the gate tests only: P3_BREAK=7 drops the sign term of the top lane
            let brk = cfg!(test) && std::env::var("P3_BREAK").map_or(false, |x| x.trim() == "7");
            if rowf {
                if !brk { b.cx(c0, tt); }
                // SYM-R-25: c0 holds m ^ b; the top lane's sign-extension term is m
                if let (Some(r), false) = (rb, round_break(1)) { b.cx(r, tt); }
            } else {
                if let Some(sg) = sign {
                    if !brk { b.cx(sg, tt); }
                }
                b.x(tt);
            }
            let rd = match &roll {
                _ if yroll || ck_row => vec![],
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
        if let (Some(r), false) = (rb, round_break(2)) {
            b.cx(r, cin_lane);
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

/// PHASE-DIRTY (persona-mochimodev): (-1)^AND(lits) where the cap leaves no room for phase_and's n - 2 clean ancillas:
/// f = AND(lits[..n-1]) is toggled onto a borrowed lane t twice around a CZ with the last literal, (t ^ f) y + t y = f y,
/// and t comes back unchanged. Dev override `WL_PHASE_DIRTY=0|1`; negative control (tests) PHASE_DIRTY_BREAK=1.
fn phase_dirty() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("PHASE_DIRTY", true)); *E }
fn phase_and_room(b: &mut B, u: &GreedyFrog, lits: &[(QubitId, bool)]) {
    let n = lits.len();
    if n <= 2 || u.room(b) >= n - 2 || !phase_dirty() { return phase_and(b, lits); }
    let t = *u.dirty.last().unwrap();
    assert!(!lits.iter().any(|l| l.0 == t), "PHASE-DIRTY: borrowed lane is a literal");
    let (head, last) = lits.split_at(n - 1);
    let (y, ny) = last[0];
    let brk = cfg!(test) && std::env::var("PHASE_DIRTY_BREAK").map_or(false, |v| v.trim() == "1");
    for pass in 0..2 {
        and_auto(b, u, head, t);
        if pass == 1 && brk { continue; }
        if ny { b.x(y); }
        b.cz(t, y);
        if ny { b.x(y); }
    }
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
// Ported from mochimodev row decb04b3 / cc55b536. OFF by default for matched control.
pub const RA1_LEND_PORT: bool = false;
fn ra1_lend_port() -> bool { static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("RA1_LEND_PORT", RA1_LEND_PORT)); *E }


fn rho_anf8() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("RHO_ANF8", RHO_ANF8));
    *E
}
fn rho_anf8_into(b: &mut B, act: Option<QubitId>, j: &[QubitId], r: &[QubitId]) {
    rho_anf8_into_ext(b, act, j, r, None)
}
/// `rho_anf8_into` with two external |0> lanes (returned |0>) as its first two product lanes (B-ROWSALL R5-07).
fn rho_anf8_into_ext(b: &mut B, act: Option<QubitId>, j: &[QubitId], r: &[QubitId], ext: Option<[QubitId; 2]>) {
    let (p, s) = match ext { Some([a, c]) => (a, c), None => (b.alloc(), b.alloc()) };
    let (xp, g, z) = (b.alloc(), b.alloc(), b.alloc());
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
    if !(ext.is_some() && cfg!(test) && std::env::var("RA1_BREAK").as_deref() == Ok("1")) { b.and_u(j[0], j[3], p); }
    if ext.is_some() && cfg!(test) && std::env::var("RA1_BREAK").as_deref() == Ok("2") { b.cz(j[0], j[1]); }
    if ext.is_none() { b.free_n(&[p, s]); }
    b.free_n(&[xp, g, z]);
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

// ------------------------------------------------------------------ lyc-lead2 02-hsweep: H-SWEEP on this tree
/// H-SWEEP (lyc-lead2 l4b-sweep, ported from our 046cfc2d build): the sweep section's two scans (`sweep_fwd_ui` /
/// `sweep_bwd_ui` and their fallbacks) are replaced by one flag h = rt.f = act & [kt5 >= j] & [no hit in (j, K]]
/// (K = k - 1) while row j is visited: the hit y = q_j & h is one Toffoli (rem lane j - 1 holds !q_j), jl ^= j y,
/// h ^= y, and y is erased by measurement through the shortest affine cube on jl that tells j from 0 and from the rows
/// above (jl is j only where row j fired). h's kt5 toggles ([kt5 >= K] as dyadic blocks, then [kt5 == j] for
/// j = K-1 .. 1) come from a depth-first decoder trie on kt5 held on path lanes (rt.g is the depth-2 lane). The record
/// is the tree's own (jl = J in binary), so jl_map, RHO_ANF8 / RHO_ANF / threshold, a1, B-SYNCGOV's ract, the phase
/// repairs and SW-CARRY's i.swc run unchanged between the scans; h stays on rt.f there (nothing reads it) and the
/// backward scan is the forward's exact mirror (y recomputed by the cube, erased through !lane & h: a CZ). RUN-GUARD's
/// kt5 -= c stays around both scans. Taken where the room at the sweep entry covers r, a1, the SW-CARRY lane and the
/// scan's own peak (`HPlan::need`), the tree's own sweeps otherwise. Dev override `WL_HSWEEP=0|1`.
pub const HSWEEP: bool = true;
fn hsweep_on() -> bool {
    static E: std::sync::LazyLock<bool> = std::sync::LazyLock::new(|| lever("HSWEEP", HSWEEP));
    *E
}

/// Where a kt5 trie node's indicator lives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Hold {
    /// the root while act = 1 classically
    One,
    /// the root with a quantum act
    Act,
    /// a depth-1 node while act = 1 classically: kt5 bit (negated)
    Lit(usize, bool),
    /// the path lane of this depth
    Lane(usize),
}

/// One step of the h-sweep's trie walk.
#[derive(Clone, Copy, Debug)]
enum Tev {
    /// h ^= holder
    Toggle(Hold),
    /// h ^= holder & (kt[bit] ^ neg), one Toffoli for a lone terminal child
    CcxToggle(Hold, usize, bool),
    /// lane[d] = holder & (kt[bit] ^ neg) (and_c)
    Compute(Hold, usize, bool, usize),
    /// lane[d] = holder & (kt[bit] ^ neg) -> |0> (and_u)
    Uncompute(Hold, usize, bool, usize),
    /// lane[d] ^= holder: the sibling (P & !b = P ^ (P & b))
    Flip(Hold, usize),
    /// visit row j
    Row(usize),
}

/// The trie's terminal nodes: the dyadic blocks covering [K, 31] (their union is [kt5 >= K]) and the leaves j < K.
struct HTrie {
    kk: usize,
    blocks: Vec<(usize, usize)>,
}

impl HTrie {
    fn is_block(&self, n: (usize, usize)) -> bool {
        self.blocks.contains(&n)
    }
    fn is_leaf(&self, n: (usize, usize)) -> bool {
        n.0 == R_BITS && n.1 >= 1 && n.1 < self.kk
    }
    fn range(n: (usize, usize)) -> (usize, usize) {
        let span = 1usize << (R_BITS - n.0);
        (n.1 * span, n.1 * span + span - 1)
    }
    fn needed(&self, n: (usize, usize)) -> bool {
        if self.is_block(n) || self.is_leaf(n) {
            return true;
        }
        let (a, z) = Self::range(n);
        if self.blocks.iter().any(|&bl| {
            let (x, y) = Self::range(bl);
            x >= a && y <= z
        }) {
            return true;
        }
        (1..self.kk).any(|j| a <= j && j <= z)
    }
    fn visit(&self, ev: &mut Vec<(Tev, bool)>, n: (usize, usize), hold: Hold, qact: bool) {
        let (d, p) = n;
        if self.is_block(n) || self.is_leaf(n) {
            ev.push((Tev::Toggle(hold), self.is_block(n)));
            if self.is_leaf(n) {
                ev.push((Tev::Row(p), false));
            }
            return;
        }
        if d == R_BITS {
            return;
        }
        let (c1, c0) = ((d + 1, 2 * p + 1), (d + 1, 2 * p));
        let (n1, n0) = (self.needed(c1), self.needed(c0));
        let bit = R_BITS - 1 - d;
        let lane = d + 1;
        if d == 0 && !qact {
            if n1 {
                self.visit(ev, c1, Hold::Lit(bit, false), qact);
            }
            if n0 {
                self.visit(ev, c0, Hold::Lit(bit, true), qact);
            }
            return;
        }
        let term = |c: (usize, usize)| self.is_block(c) || self.is_leaf(c);
        if n1 != n0 && term(if n1 { c1 } else { c0 }) {
            let (c, neg) = if n1 { (c1, false) } else { (c0, true) };
            ev.push((Tev::CcxToggle(hold, bit, neg), self.is_block(c)));
            if self.is_leaf(c) {
                ev.push((Tev::Row(c.1), false));
            }
            return;
        }
        if n1 && n0 {
            ev.push((Tev::Compute(hold, bit, false, lane), false));
            self.visit(ev, c1, Hold::Lane(lane), qact);
            ev.push((Tev::Flip(hold, lane), false));
            self.visit(ev, c0, Hold::Lane(lane), qact);
            ev.push((Tev::Uncompute(hold, bit, true, lane), false));
        } else if n1 {
            ev.push((Tev::Compute(hold, bit, false, lane), false));
            self.visit(ev, c1, Hold::Lane(lane), qact);
            ev.push((Tev::Uncompute(hold, bit, false, lane), false));
        } else if n0 {
            ev.push((Tev::Compute(hold, bit, true, lane), false));
            self.visit(ev, c0, Hold::Lane(lane), qact);
            ev.push((Tev::Uncompute(hold, bit, true, lane), false));
        }
    }
}

/// The h-sweep's depth-first walk of the kt5 decoder trie (MSB first, 1-children first, so the rows come in
/// descending order): the blocks of [kt5 >= K] (row K follows the last block toggle), then [kt5 == j] for
/// j = K-1 .. 1, each followed by row j.
fn hsweep_trie(kk: usize, qact: bool) -> Vec<Tev> {
    let mut blocks = vec![];
    let mut lo = kk;
    while lo <= 31 {
        let mut size = 1usize;
        while lo % (size * 2) == 0 && lo + size * 2 - 1 <= 31 {
            size *= 2;
        }
        let d = R_BITS - size.trailing_zeros() as usize;
        blocks.push((d, lo >> (R_BITS - d)));
        lo += size;
    }
    let t = HTrie { kk, blocks };
    let mut ev = vec![];
    t.visit(&mut ev, (0, 0), if qact { Hold::Act } else { Hold::One }, qact);
    let nb = ev.iter().filter(|e| e.1).count();
    let (mut out, mut seen) = (vec![], 0);
    for (e, block) in ev {
        out.push(e);
        if block {
            seen += 1;
            if seen == nb {
                out.push(Tev::Row(kk));
            }
        }
    }
    out
}

/// The affine subspaces of GF(2)^5 as membership masks, by decreasing dimension.
static HSWEEP_SUBS: std::sync::LazyLock<Vec<u32>> = std::sync::LazyLock::new(|| {
    let mut seen: std::collections::HashMap<u32, usize> = std::collections::HashMap::new();
    seen.insert(1, 0);
    let mut order: Vec<(u32, usize)> = vec![(1, 0)];
    let mut frontier = vec![1u32];
    let mut d = 0;
    while !frontier.is_empty() {
        let mut nxt = vec![];
        for &s in &frontier {
            for v in 0..32u32 {
                if (s >> v) & 1 == 1 {
                    continue;
                }
                let mut t = s;
                for x in 0..32u32 {
                    if (s >> x) & 1 == 1 {
                        t |= 1 << (x ^ v);
                    }
                }
                if let std::collections::hash_map::Entry::Vacant(e) = seen.entry(t) {
                    e.insert(d + 1);
                    order.push((t, d + 1));
                    nxt.push(t);
                }
            }
        }
        frontier = nxt;
        d += 1;
    }
    order.sort_by_key(|e| std::cmp::Reverse(e.1));
    order.into_iter().map(|e| e.0).collect()
});

/// Fewest affine literals (mask over jl, negated) whose AND is 1 at t and 0 at every excluded value: the largest coset
/// t + S that misses them, written by the dual basis of S.
fn hsweep_cube(subs: &[u32], t: usize, excl: &[usize]) -> Vec<(u32, bool)> {
    let mut dm = 0u32;
    for &x in excl {
        dm |= 1 << (t ^ x);
    }
    let s = *subs.iter().find(|&&s| s & dm == 0).expect("no separating cube");
    let members: Vec<u32> = (0..32).filter(|&x| (s >> x) & 1 == 1).collect();
    let (mut basis, mut span) = (vec![], 1u32);
    for a in 0..32u32 {
        if members.iter().all(|&m| (a & m).count_ones() % 2 == 0) && (span >> a) & 1 == 0 {
            basis.push(a);
            let mut ns = span;
            for x in 0..32u32 {
                if (span >> x) & 1 == 1 {
                    ns |= 1 << (x ^ a);
                }
            }
            span = ns;
        }
    }
    basis.into_iter().map(|a| (a, (a & t as u32).count_ones() % 2 == 0)).collect()
}

/// CX moves that put each cube literal's parity on its own lane of jl (distinct pivots; the literal masks are
/// independent), and the literal list on those lanes. Undo: the moves in reverse.
fn hsweep_cube_lanes(e: &[QubitId], cube: &[(u32, bool)]) -> (Vec<(usize, usize)>, Vec<(QubitId, bool)>) {
    let mut rows: Vec<u32> = (0..R_BITS).map(|i| 1u32 << i).collect();
    let mut used = [false; R_BITS];
    let (mut moves, mut lits) = (vec![], vec![]);
    for &(a, neg) in cube {
        let sub = (0..1u32 << R_BITS)
            .find(|&m| (0..R_BITS).filter(|&i| (m >> i) & 1 == 1).fold(0, |acc, i| acc ^ rows[i]) == a)
            .expect("literal mask outside the span");
        let p = (0..R_BITS).find(|&i| (sub >> i) & 1 == 1 && !used[i]).expect("dependent cube literals");
        for q in 0..R_BITS {
            if q != p && (sub >> q) & 1 == 1 {
                moves.push((q, p));
                rows[p] ^= rows[q];
            }
        }
        used[p] = true;
        lits.push((e[p], neg));
    }
    (moves, lits)
}

/// t ^= l & m (kind 0: ccx), t = l & m into |0> (1: and_c), t = l & m -> |0> (2: and_u), on literals.
fn hsweep_gate(b: &mut B, l: (QubitId, bool), m: (QubitId, bool), t: QubitId, kind: u8) {
    for q in [l, m] {
        if q.1 {
            b.x(q.0);
        }
    }
    match kind {
        0 => b.ccx(l.0, m.0, t),
        1 => b.and_c(l.0, m.0, t),
        _ => b.and_u(l.0, m.0, t),
    }
    for q in [m, l] {
        if q.1 {
            b.x(q.0);
        }
    }
}

fn hsweep_lit(hold: Hold, act: Option<QubitId>, kt: &[QubitId], lanes: &[Option<QubitId>]) -> (QubitId, bool) {
    match hold {
        Hold::Act => (act.expect("act lane"), false),
        Hold::Lit(bit, neg) => (kt[bit], neg),
        Hold::Lane(d) => (lanes[d].expect("trie lane not held"), false),
        Hold::One => panic!("the constant root has no lane"),
    }
}

/// Row j of the h-sweep. Forward: y = q_j & h, jl ^= j y, h ^= y, y erased by measurement through the cube that tells
/// j from 0 and from the rows above. Backward: the exact mirror, y recomputed by the cube and erased through q_j & h
/// (and_u: a CZ).
fn hsweep_row(b: &mut B, u: &GreedyFrog, rt: &RowTmp, j: usize, cube: &[(u32, bool)], bwd: bool) {
    let (h, y, rec) = (rt.f, rt.y, &rt.jl[..]);
    let lane = rt.rem(u, j as isize - 1);
    let (mv, lits) = hsweep_cube_lanes(rec, cube);
    if !bwd {
        hsweep_gate(b, (lane, true), (h, false), y, 1);
        for (i, &bit) in rec.iter().enumerate() {
            if (j >> i) & 1 == 1 {
                b.cx(y, bit);
            }
        }
        b.cx(y, h);
        for &(q, p) in &mv {
            b.cx(rec[q], rec[p]);
        }
        erase_mbu(b, y, |b| phase_and(b, &lits));
        for &(q, p) in mv.iter().rev() {
            b.cx(rec[q], rec[p]);
        }
    } else {
        for &(q, p) in &mv {
            b.cx(rec[q], rec[p]);
        }
        // negative control for the gate tests only: HSWEEP_BREAK=1 drops the last cube literal of the backward rows
        let brk = cfg!(test) && lits.len() >= 2 && std::env::var("HSWEEP_BREAK").map_or(false, |v| v.trim() == "1");
        and_into(b, &lits[..lits.len() - brk as usize], y);
        for &(q, p) in mv.iter().rev() {
            b.cx(rec[q], rec[p]);
        }
        b.cx(y, h);
        for (i, &bit) in rec.iter().enumerate() {
            if (j >> i) & 1 == 1 {
                b.cx(y, bit);
            }
        }
        hsweep_gate(b, (lane, true), (h, false), y, 2);
    }
}

/// One trie event, forward or mirrored (the backward scan plays the events in reverse with compute <-> uncompute).
#[allow(clippy::too_many_arguments)]
fn hsweep_event(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, rt: &RowTmp, lanes: &mut [Option<QubitId>],
                ev: Tev, bwd: bool, cubes: &[Vec<(u32, bool)>]) {
    let kt = &u.lb[..R_BITS];
    let h = rt.f;
    match ev {
        Tev::Toggle(Hold::One) => b.x(h),
        Tev::Toggle(hd) => {
            let l = hsweep_lit(hd, act, kt, lanes);
            b.cx(l.0, h);
            if l.1 {
                b.x(h);
            }
        }
        Tev::CcxToggle(Hold::One, bit, neg) => {
            b.cx(kt[bit], h);
            if neg {
                b.x(h);
            }
        }
        Tev::CcxToggle(hd, bit, neg) => {
            let l = hsweep_lit(hd, act, kt, lanes);
            hsweep_gate(b, l, (kt[bit], neg), h, 0);
        }
        Tev::Compute(hd, bit, neg, d) | Tev::Uncompute(hd, bit, neg, d) => {
            let compute = matches!(ev, Tev::Compute(..)) != bwd;
            let l = hsweep_lit(hd, act, kt, lanes);
            if compute {
                assert!(lanes[d].is_none(), "trie lane {d} busy");
                let q = if d == 2 { rt.g } else { b.alloc() };
                lanes[d] = Some(q);
                hsweep_gate(b, l, (kt[bit], neg), q, 1);
            } else {
                let q = lanes[d].take().expect("trie lane not held");
                hsweep_gate(b, l, (kt[bit], neg), q, 2);
                if d != 2 {
                    b.free(q);
                }
            }
        }
        Tev::Flip(hd, d) => {
            let l = hsweep_lit(hd, act, kt, lanes);
            let q = lanes[d].expect("trie lane not held");
            b.cx(l.0, q);
            if l.1 {
                b.x(q);
            }
        }
        Tev::Row(j) => hsweep_row(b, u, rt, j, &cubes[j], bwd),
    }
}

/// A slot's h-sweep schedule: the trie walk, the per-row cubes on jl, and the scan's peak above its entry (fresh trie
/// path lanes + the row's cube AND temporaries; the same in both directions).
struct HPlan {
    ev: Vec<Tev>,
    cubes: Vec<Vec<(u32, bool)>>,
    need: usize,
}

impl HPlan {
    fn new(k: usize, qact: bool) -> HPlan {
        assert!(k >= 2 && k <= 1 << R_BITS, "h-sweep rows k {k}");
        let kk = k - 1;
        let cubes: Vec<Vec<(u32, bool)>> = (0..=kk)
            .map(|j| {
                if j == 0 {
                    return vec![];
                }
                let excl: Vec<usize> = std::iter::once(0).chain(j + 1..=kk).collect();
                hsweep_cube(&HSWEEP_SUBS, j, &excl)
            })
            .collect();
        let ev = hsweep_trie(kk, qact);
        let (mut held, mut need) = (0usize, 0usize);
        for e in &ev {
            match *e {
                Tev::Compute(_, _, _, d) if d != 2 => {
                    held += 1;
                    need = need.max(held);
                }
                Tev::Uncompute(_, _, _, d) if d != 2 => held -= 1,
                Tev::Row(j) => need = need.max(held + cubes[j].len().saturating_sub(2)),
                _ => {}
            }
        }
        HPlan { ev, cubes, need }
    }
}

/// The h-sweep's scan: forward (h = rt.f, y = rt.y, jl = rt.jl from |0>; leaves jl = J and
/// h = act & [kt5 >= 1] & [J == 0], y and rt.g |0>), or its mirror (bwd).
fn hsweep_scan(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, rt: &RowTmp, plan: &HPlan, bwd: bool) {
    let mut lanes: [Option<QubitId>; R_BITS + 1] = [None; R_BITS + 1];
    if bwd {
        for &e in plan.ev.iter().rev() {
            hsweep_event(b, u, act, rt, &mut lanes, e, true, &plan.cubes);
        }
    } else {
        for &e in &plan.ev {
            hsweep_event(b, u, act, rt, &mut lanes, e, false, &plan.cubes);
        }
    }
    assert!(lanes.iter().all(|l| l.is_none()), "trie lanes left held");
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
        // B-SYNCGOV: h_s (this slot's hold, gates rho / a1), h_(s+1) (gates the swap-flag erase), the record value whose
        // last held slot this is (sw_t handover), and the record erase on slot s* - 1
        let gv = gov_cfg_at(w.slot);
        let rec = !self.gov.is_empty();
        let gj = if rec { gv.and_then(|g| g.jmin(w.slot)) } else { None };
        let gj1 = if rec { gv.and_then(|g| g.jmin(w.slot + 1)) } else { None };
        let mut gerase = rec && gv.map_or(false, |g| w.slot + 1 == g.slot);
        assert!(!(gj.is_some() || gj1.is_some()) || w.act_const, "SYNC-GOV window slots must be act-constant");
        let gsw = if gov_break(2) { None } else { gj1 };
        // STALL-PAIR: ns = this slot was a fake (decode gated off; rewritten to s = "was an add-back" before the ladders)
        let fr = stall_free(w);
        let ns = if fr { self.sf.take() } else { None };
        let nsg: Vec<(QubitId, bool)> = ns.iter().map(|&q| (q, true)).collect();
        prof(b, "i.z0");
        p3(b, self, "i.z0");
        // I1: z0 = [LA == 0] & [cnt != 0]; on slots where no shot can have finished, act = 1 classically and the
        // flag (and the DONE bookkeeping) is skipped
        let z0 = if w.act_const { None } else { Some(b.alloc()) };
        if let Some(z0) = z0 {
            let cz = b.alloc();
            self.cnt_zero_into(b, cz, w);
            let lz = b.alloc();
            zero_into(b, &self.la[..len_n(w)], lz);
            and_into(b, &[(lz, false), (cz, true)], z0);
            // Z0-DEFER: the forward's F11 z0 erase is repaired here, on the same predicate of the same state
            if let Some(m) = bits.z0m {
                if !m2_break(2) { b.z_if(z0, m); }
            }
            if z0_meas() {
                let zl: Vec<(QubitId, bool)> = self.la[..len_n(w)].iter().map(|&q| (q, true)).collect();
                let cl: Vec<(QubitId, bool)> = self.cntw(w).iter().map(|&q| (q, false)).collect();
                erase_and(b, self, lz, &zl);
                if cr_break(4) { let m = b.fresh_bits(1)[0]; b.hmr_to(cz, m); } else { erase_and(b, self, cz, &cl); }
            } else {
                zero_into(b, &self.la[..len_n(w)], lz);
                self.cnt_zero_into(b, cz, w);
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
        let keep = ns0 && off_keep() && cin.is_none() && !term(w);
        let (mut sx, mut sy, sw_std): (Vec<QubitId>, Vec<QubitId>, Option<QubitId>) = if let Some(c) = cin {
            // SW-CARRY: I3, I4 on the carried flag, its I5 erase (the forward's F9 on the restored pre-swap state),
            // then the decode prep on the un-swapped rings (the receiver's ring layouts at the rows window)
            prof(b, "i.unswap");
            b.z_if(c, bits.sw);
            // CMP-SHARE: the successor's d is F9's comparator ^ sw: the swap flag's erase reads it, then it erases on this state
            let held = self.cmp_held.take();
            if let (Some(h), false) = (held, cmpd_break(1)) { b.cx(c, h); }
            let (xn, ln) = swap_lanes(w, true);
            super::arith::cswap_regs(b, c, &self.x[..xn], &self.y[..xn]);
            super::arith::cswap_regs(b, c, &self.la[..ln], &self.lb[..ln]);
            b.cx(c, self.par);
            prof(b, "i.swerase");
            erase_mbu(b, c, |b| {
                if let Some(z0) = z0 {
                    b.x(z0);
                }
                let gl = gsw.map(|j| self.gov_lit(b, j, true));
                let gs: Vec<(QubitId, bool)> = gl.iter().map(|l| l.0).chain(nsg.iter().copied()).collect();
                self.swap_flag_h(b, z0, None, w, false, &gs, false, held);
                if let (Some(j), Some((_, t))) = (gsw, gl) { self.gov_lit_free(b, j, t, true); }
                if let Some(z0) = z0 {
                    b.x(z0);
                }
            });
            b.free(c);
            if let Some(h) = held {
                assert!(z0.is_none() && gsw.is_none());
                if cmpd_break(2) {
                    let m = b.fresh_bits(1)[0];
                    b.hmr_to(h, m);
                } else {
                    erase_mbu(b, h, |b| self.cmp_gated(b, None, &nsg));
                }
                b.free(h);
            }
            if gerase {
                prof(b, "i.gov");
                self.gov_erase(b);
                // B5SPEND E-GOV2: erased here; with a second record the next one is now in self.gov (no second erase)
                gerase = false;
            }
            prof(b, "i.prep");
            if ns0 {
                // Y (the target, slack <= 1): the a-shift only, sY = a_Y; X (the divisor): the 5-stage funnel alone
                // (its stage 0 is the a-shift's lane map), sX = its slack; the receiver's ring layouts and sX, sY
                let sy0 = if no_yshift() { vec![] } else {
                    let ay = b.alloc();
                    let mut l = act_lits(y_act);
                    l.extend(nsg.iter().copied());
                    l.extend([(self.y[0], true), (self.y[1], false)]);
                    and_auto(b, self, &l, ay);
                    for i in 0..NB {
                        b.cswap(ay, self.y[i], self.y[i + 1]);
                    }
                    vec![ay]
                };
                let f = b.alloc_n(R_BITS);
                norm_bottom(b, self, &self.x, &f, None);
                (f, sy0, None)
            } else {
                let sx = b.alloc_n(R_BITS);
                let sy = b.alloc_n(R_BITS);
                norm_bottom(b, self, &self.x, &sx, None);
                norm_bottom(b, self, &self.y, &sy, y_act);
                (sx, sy, None)
            }
        } else if term(w) && ns0 {
            // TERM-LAST: sw = 0 on every passing shot: no I2 decode, no un-swap, no I5; the standard NORM-STAGE0 prep
            // alone (both a-shifts, then the funnel on X, sX = funnel + a_X)
            prof(b, "i.prep");
            let (ax, ay) = (b.alloc(), b.alloc());
            and_auto(b, self, &[(self.x[0], true), (self.x[1], false)], ax);
            let mut l = act_lits(y_act);
            l.extend(nsg.iter().copied());
            l.extend([(self.y[0], true), (self.y[1], false)]);
            and_auto(b, self, &l, ay);
            for i in 0..NB {
                b.cswap(ax, self.x[i], self.x[i + 1]);
            }
            for i in 0..NB {
                b.cswap(ay, self.y[i], self.y[i + 1]);
            }
            let f = b.alloc_n(R_BITS);
            norm_bottom(b, self, &self.x, &f, None);
            b.cx(ax, f[0]);
            let mut l = vec![(f[0], false)];
            l.extend(f[1..].iter().map(|&q| (q, true)));
            erase_and(b, self, ax, &l);
            b.free(ax);
            (f, vec![ay], None)
        } else {
        prof(b, "i.prep");
        // decode prep: normalised cofactor windows (slacks sX, sY)
        // NORM-STAGE0: c_r = [ring slack >= 2], a_r = [ring slack == 1]; only the a-shift (the funnel's stage 0) here
        let (mut sx, mut sy, cxy) = if ns0 {
            let (ax, ay, cx_, cy_) = (b.alloc(), b.alloc(), b.alloc(), b.alloc());
            and_auto(b, self, &[(self.x[0], true), (self.x[1], true)], cx_);
            let mut l = act_lits(act);
            l.extend(nsg.iter().copied());
            l.extend([(self.y[0], true), (self.y[1], true)]);
            and_auto(b, self, &l, cy_);
            and_auto(b, self, &[(self.x[0], true), (self.x[1], false)], ax);
            let mut l = act_lits(y_act);
            l.extend(nsg.iter().copied());
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
                l.extend(nsg.iter().copied());
                l.push((core, false));
                if brk.trim() != "2" {
                    l.push((cx_, true));
                }
                l.push((cy_, true));
                and_auto(b, self, &l, sw);
                if brk.trim() != "1" {
                    if let Some(&(n, _)) = nsg.first() {
                        b.x(n);
                        b.ccx(n, cy_, sw);
                        b.x(n);
                    } else {
                    b.cx(cy_, sw);
                    }
                }
            } else {
                assert!(nsg.is_empty(), "STALL-PAIR runs with NORM-STAGE0");
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
            l.extend(nsg.iter().copied());
            l.extend([(self.y[0], true), (self.y[1], true)]);
            erase_and(b, self, cy_, &l);
            b.free_n(&[cx_, cy_]);
        }
        prof(b, "i.unswap");
        p3(b, self, "i.unswap");
        // I3, I4
        b.z_if(sw, bits.sw);
        let (xn, ln) = swap_lanes(w, !keep);
        super::arith::cswap_regs(b, sw, &self.x[..xn], &self.y[..xn]);
        super::arith::cswap_regs(b, sw, &self.la[..ln], &self.lb[..ln]);
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
                let gl = gsw.map(|j| self.gov_lit(b, j, true));
                let gs: Vec<(QubitId, bool)> = gl.iter().map(|l| l.0).chain(nsg.iter().copied()).collect();
                self.swap_flag_g(b, z0, None, w, false, &gs, false);
                if let (Some(j), Some((_, t))) = (gsw, gl) { self.gov_lit_free(b, j, t, true); }
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
        if sy_host() && !sy.is_empty() {
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
            let gl = gsw.map(|j| self.gov_lit(b, j, true));
            let gs: Vec<(QubitId, bool)> = gl.iter().map(|l| l.0).chain(nsg.iter().copied()).collect();
            self.swap_flag_g(b, z0, None, w, false, &gs, false);
            if let (Some(j), Some((_, t))) = (gsw, gl) { self.gov_lit_free(b, j, t, true); }
            if let Some(z0) = z0 {
                b.x(z0);
            }
        });
        b.free(sw);
        }
        if gerase && !self.gov.is_empty() {
            // B-SYNCGOV: record erase on slot s* - 1 (standard I2 path; the carried path erased it at its I5). OFF-KEEP
            // holds LA + sX, LB + sY here: plain around the erase.
            prof(b, "i.gov");
            if keep {
                add_sm(b, self, &self.la, &sx, false, true);
                add_sm(b, self, &self.lb, &sy[..sy_len], false, true);
            }
            self.gov_erase(b);
            if keep {
                add_sm(b, self, &self.lb, &sy[..sy_len], false, false);
                add_sm(b, self, &self.la, &sx, false, false);
            }
        }
        prof(b, "i.rows");
        p3(b, self, "i.rows");
        // I6: u = LA + sX in LA, kt = u - (LB + sY) = mY - mX in LB; rows; r = act & (sX - sY - j_last)
        let kk = if keep || w.slot == 0 { LB_BITS } else { kt_lanes(w) };
        if !keep {
            add_sm(b, self, &self.la[..kk], &sx, false, false);
            if sy_len > 0 { add_sm(b, self, &self.lb[..kk], &sy[..sy_len], false, false); }
        }
        for &q in &self.lb {
            b.x(q);
        }
        add_sm(b, self, &self.lb[..kk], &self.la[..kk], true, false);
        for i in kk..LB_BITS {
            b.cx(self.la[i], self.lb[i]);
            b.x(self.lb[i]);
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
                b.free_n(&self.lb[R_BITS..lb_top]);
            } else {
                host.extend(&self.lb[R_BITS..lb_top]);
            }
        }
        let masked_rows = w.mx < NB + 1;
        // (the bits above kk: LA's constant, then the sign of u')
        let kh = kt_hi(w) >> kk;
        if masked_rows {
            add_const_sm(b, self, &self.la[..kk], UOFF, true);
            for i in kk..LB_BITS {
                if kh >> (i - kk) & 1 == 1 { b.x(self.la[i]); }
                b.cx(self.la[kk - 1], self.la[i]);
            }
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
            park_junk(b, self, w, &z, top, true);
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
        let produce = want_out && sw_carry() && (!split || room_park >= zn + swc_split_min());
        let (r, a1, cout, _) = self.sweep_section(b, bits, w, act, &rt, &sx, &sy, sy_len, gj, produce, ytsw, park,
                                                  masked_rows, None, ns);
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
        play_undo_rows(b, &unrows);
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
            park_junk(b, self, w, &z, top, false);
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
            for i in kk..LB_BITS {
                b.cx(self.la[kk - 1], self.la[i]);
                if kh >> (i - kk) & 1 == 1 { b.x(self.la[i]); }
            }
            add_const_sm(b, self, &self.la[..kk], UOFF, false);
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
        for i in kk..LB_BITS {
            b.x(self.lb[i]);
            b.cx(self.la[i], self.lb[i]);
        }
        add_sm(b, self, &self.lb[..kk], &self.la[..kk], true, true);
        for &q in &self.lb {
            b.x(q);
        }
        if !sy.is_empty() { add_sm(b, self, &self.lb[..kk], &sy, false, true); }
        add_sm(b, self, &self.la[..kk], &sx, false, true);
        prof(b, "i.denorm");
        p3(b, self, "i.denorm");
        // FUSE-S4: decided here (the erase after the barrel sees this room + sX0..3 + sY freed, s4 freed by EFREE)
        let fuse = fuse_s4() && ns0 && sw_carry() && funnel_rev() && sy.len() <= 1
            && self.room(b) + R_BITS - 1 + sy.len() + 1 >= FUSE_S4_NEED + 1;
        if cfg!(test) && ns0 && sw_carry() && std::env::var_os("M2_LOG").is_some() { eprintln!("M2LOG fuse {}", fuse as u8); }
        if ns0 && sw_carry() {
            // SW-CARRY: X's prep is the funnel alone on carried slots, and on the others the a-shift + funnel, whose lane
            // map and sX are the funnel's (a_X = 1 iff slack 1, where the funnel's stage 0 makes the same shift and
            // sX = 1): both are undone by the funnel's inverse. Y back by its a-shift, sY = [Y slack == 1] erased.
            if let Some(&ay) = sy.first() {
                for i in (0..NB).rev() {
                    b.cswap(ay, self.y[i], self.y[i + 1]);
                }
                let mut l = act_lits(y_act);
                l.extend(nsg.iter().copied());
                l.extend([(self.y[0], true), (self.y[1], false)]);
                erase_and(b, self, ay, &l);
            }
            if fuse {
                rev_funnel_k(b, self, &self.x, &sx, None, false, true);
            } else {
                denorm_bottom(b, self, &self.x, &sx, None);
            }
        } else if ns0 {
            // NORM-STAGE0 inverse: Y back by its a-shift (sY <= 1), sY = [Y slack == 1] erased; a_X = [sX == 1] back
            // into its own lane, the funnel undone on the funnel bits, X back by its a-shift, a_X = [X slack == 1] erased
            for i in (0..NB).rev() {
                b.cswap(sy[0], self.y[i], self.y[i + 1]);
            }
            let mut l = act_lits(y_act);
            l.extend(nsg.iter().copied());
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
        let s4 = if fuse { Some(sx[R_BITS - 1]) } else { None };
        b.free_n(&sx[..if fuse { R_BITS - 1 } else { R_BITS }]);
        b.free_n(&sy);
        prof(b, "i.unrenorm");
        p3(b, self, "i.unrenorm");
        // I7, I8, I9
        add_sm(b, self, &self.la[..rho_lanes(w, len_n(w))], &r, false, false);
        unrenorm_top_g(b, self, act, &r, gate_spec(&self.la, w), s4, gj, ns);
        b.free_n(&r);
        // STALL-PAIR: the flag lane goes from ns to s = !(ns ^ a1) (the last slot: s from its passing-shot formula)
        let si = if fr {
            let q = match ns { Some(q) => q, None => b.alloc() };
            b.cx(a1, q);
            b.x(q);
            if w.slot == 1 {
                zero_probe(b, &[q]);
                b.free(q);
                None
            } else { Some(q) }
        } else if stall_pair() && w.last {
            let q = b.alloc();
            sp_last(self, b, act, a1, q);
            Some(q)
        } else { None };
        let eg_last = if stall_pair() && !fr && si.is_some() {
            let e = b.alloc();
            b.cx(a1, e);
            b.cx(si.unwrap(), e);
            Some(e)
        } else { None };
        prof(b, "i.value");
        p3(b, self, "i.value");
        // I10: value add-back where a1; d = a1 & the chain's carry out of lane W-1
        let mwa = masked_write_always();
        mark_done_inv(b, act, &self.lb);
        if mwa { mark_stall(b, act, a1, &self.lb); }
        let d = b.alloc();
        let pk = act.and_then(|a| act_park(b, a, &self.lb, w.lb));
        let ap = a1_park(b, mwa && fr && w.slot >= 1 && w.lb.1 <= 255, a1, &self.lb);
        if fr { super::mask::set_ord_gate(Some(ALWAYS), None); } else if let Some(e) = eg_last { super::mask::set_ord_gate(Some(e), None); }
        let vord = if stall_pair() && w.slot >= 1 {
            let (xv, fl) = sp_value(self, w, fr, si, a1, ap);
            super::mask::set_ladx(Some(xv));
            fl
        } else { vec![] };
        sp_flip(b, si, &vord);
        // (slot 0's pre-state has LA = 256)
        let il = if w.slot >= 1 { ladder_idle(b, &self.la, w.lad) } else { (vec![], vec![]) };
        let ol = if w.slot >= 1 && w.act_const && idle_shared() { idle_take(b, &self.lb, own_idle(w.lb), LB_BITS - 1) } else { (vec![], vec![]) };
        value_pass(b, self, w, false, a1, Some(d), mwa, Some(&bits.rv));
        idle_give(b, ol);
        ladder_idle_back(b, il);
        sp_flip(b, si, &vord);
        super::mask::set_ladx(None);
        a1_unpark(b, a1, ap);
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
        let ap = a1_park(b, mwa && fr && w.slot >= 1 && w.lad.1 <= 255, a1, &self.la);
        let tail = sp_tail(self, w, act, pk);
        if fr { super::mask::set_ord_gate(Some(ALWAYS), tail); } else if let Some(e) = eg_last { super::mask::set_ord_gate(Some(e), tail); }
        let cord = if stall_pair() && w.slot >= 1 {
            let (xc, fl) = sp_cof(self, w, fr, si, a1, ap);
            super::mask::set_ladx(Some(xc));
            fl
        } else { vec![] };
        sp_flip(b, si, &cord);
        let il = if w.slot >= 1 { ladder_idle(b, &self.lb, w.lb) } else { idle_take(b, &self.lb, (LB_BITS - 1, 0), LB_BITS) };
        let ol = if w.slot >= 1 && w.act_const && idle_shared() { idle_take(b, &self.la, own_idle(w.lad), LB_BITS - 1) } else { (vec![], vec![]) };
        if lane0_direct() {
            // x0 = X[0] ^ d here (X[0] holds A's MSB = 1 where d = 1), in place
            let m = Masked::alloc_ladder_w(b, w.lad);
            b.cx(d, self.x[0]);
            let (t, s) = cof_ladder(self, w, self.x[0]);
            let src = cof_src(self, &m, w);
            if !ck_try(b, self, &t, &s, cof_src(self, &m, w), &m, true, Some(&bits.rc), term_nc(), |_, _| {}) {
            let a1l = a1_copy(b);
            let pool = pool_for(b, self, t.len() - (w.lad.1 - w.lad.0 + 1), 0);
            masked_pass(b, self, &t, &s, src, &m, true, Some(a1l.unwrap_or(a1)), None, &pool, mwa, w.a1_const, Some(&bits.rc));
            b.free_n(&pool);
            a1_copy_free(b, a1l);
            }
            b.cx(d, self.x[0]);
            m.free(b);
        } else {
            let m = Masked::alloc_ladder_w(b, w.lad);
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
        idle_give(b, ol);
        ladder_idle_back(b, il);
        sp_flip(b, si, &cord);
        super::mask::set_ladx(None);
        super::mask::set_ord_gate(None, None);
        a1_unpark(b, a1, ap);
        if let Some(e) = eg_last {
            b.cx(si.unwrap(), e);
            b.cx(a1, e);
            b.free(e);
        }
        if let Some(a) = act { act_unpark(b, a, &self.la, pk); }
        if mwa { mark_stall(b, act, a1, &self.la); }
        mark_done_inv(b, act, &self.la);
        if ytc {
            self.y[W - 1] = b.alloc();
            b.x(self.y[W - 1]);
        }
        prof(b, "i.dundo");
        p3(b, self, "i.dundo");
        // I12, I13, I14 (TERM-LAST, SLOT0-D: d = 0 on every passing shot of the slot: nothing to undo, d is |0>)
        if !no_d(w) {
            {
                let ld = la_d_lanes(w, len_n(w));
                let anc = b.alloc_n(ld - 1);
                super::arith::inc(b, d, &self.la[..ld], &anc);
                b.free_n(&anc);
            }
            crot_down(b, d, &self.x, 1);
            if !(cmp_share() && cmp_is_d(w) && cout.is_some()) {
                mark_msb(b, a1, &self.lb);
                tc_idle_probe(b, self, w);
                erase_mbu(b, d, |b| top_compare(b, self, None, w, Some((a1, false))));
                mark_msb(b, a1, &self.lb);
            }
        }
        if !no_d(w) && cmp_share() && cmp_is_d(w) && cout.is_some() {
            self.cmp_held = Some(d);
        } else {
            b.free(d);
        }
        prof(b, "i.end15");
        p3(b, self, "i.end15");
        // I15: a1 = act & X[W-1] on the restored pre-state (B-SYNCGOV: & !h on window slots)
        let mut lits = act_lits(act);
        lits.push((self.x[W - 1], false));
        if let Some(q) = si { lits.push((q, true)); }
        erase_mbu(b, a1, |b| {
            let gl = gj.map(|j| self.gov_lit(b, j, true));
            if let Some((l, _)) = gl { lits.push(l); }
            phase_and(b, &lits);
            if let (Some(j), Some((_, t))) = (gj, gl) { self.gov_lit_free(b, j, t, true); }
        });
        b.free(a1);
        if let Some(z0) = z0 {
            b.x(z0); // z0 = done flag again
            self.cnt_dec(b, z0, w);
            let zl: Vec<(QubitId, bool)> = self.la[..len_n(w)].iter().map(|&q| (q, true)).collect();
            erase_and(b, self, z0, &zl);
            b.free(z0);
        }
        self.sf = si;
        prof(b, "end");
        p3(b, self, "end");
        cout
    }

    /// The inverse slot's sweep section (RUN-GUARD, forward sweep, jl -> sX - sY - jl, r / a1 with B-SYNCGOV's ract,
    /// the phase repairs, SW-CARRY's i.swc, backward sweep, guard undo), moved out of `inv_slot_c` unchanged so the gate
    /// tests can drive it on a slot-shaped register set; H-SWEEP is dispatched inside. `produce`: this slot leaves the
    /// SW-CARRY lane. `force` (tests only): Some(false) the tree's own sweeps, Some(true) the h-sweep regardless of
    /// room. Returns (r, a1, the SW-CARRY lane, whether the h-sweep ran).
    #[allow(clippy::too_many_arguments)]
    /// IN-PLACE DECODE: g = !X[W-1] & [LA == 0] on a clean lane where a shot can finish (LA holds LA + sX here); None on act-constant slots.
    fn r4_fin(&self, b: &mut B, w: &Win, sx: &[QubitId]) -> Option<(QubitId, Vec<(QubitId, bool)>)> {
        if w.act_const { return None; }
        for (i, &q) in sx.iter().enumerate() { b.cx(q, self.la[i]); }
        // (with L = 0 lane W - 1 is tB's low bit, so a finished shot can read X[W-1] = 1 as well: it is out either way)
        let mut l = vec![(self.x[W - 1], true)];
        l.extend(self.la.iter().map(|&q| (q, true)));
        let g = b.alloc();
        and_auto(b, self, &l, g);
        Some((g, l))
    }
    fn r4_fin_off(&self, b: &mut B, sx: &[QubitId], g: QubitId, l: &[(QubitId, bool)]) {
        erase_and(b, self, g, l);
        b.free(g);
        for (i, &q) in sx.iter().enumerate() { b.cx(q, self.la[i]); }
    }

    /// SW-CARRY's single flag, Q has one set bit, is [J == the top positive row], as literals on J (and rt.y, |0> here).
    /// Y normalised: the top row is 0 or 1, so J = 0, or J = 1 with s0 negative. NO-YSHIFT: a slack of 1 moves it down one,
    /// so with p = s0 & Y[0] the top row is (s0 ^ p) + 2 p: J is compared to that in place, for the same one AND.
    fn sing_on(&self, b: &mut B, rt: &RowTmp, s0: QubitId, jl: &[QubitId], noshift: bool) -> Vec<(QubitId, bool)> {
        let t = rt.y;
        if noshift {
            b.and_c(s0, self.y[0], t);
            b.cx(s0, jl[0]);
            b.cx(t, jl[0]);
            b.cx(t, jl[1]);
            return jl[..R_BITS].iter().map(|&q| (q, true)).collect();
        }
        b.x(rt.s0);
        b.and_c(jl[0], rt.s0, t);
        b.x(rt.s0);
        let mut l = vec![(t, true)];
        l.extend(jl[1..R_BITS].iter().map(|&q| (q, true)));
        l
    }
    fn sing_off(&self, b: &mut B, rt: &RowTmp, s0: QubitId, jl: &[QubitId], noshift: bool) {
        let t = rt.y;
        if noshift {
            b.cx(t, jl[1]);
            b.cx(t, jl[0]);
            b.cx(s0, jl[0]);
            b.and_u(s0, self.y[0], t);
            return;
        }
        b.x(rt.s0);
        b.and_u(jl[0], rt.s0, t);
        b.x(rt.s0);
    }

    /// IN-PLACE DECODE of a slot (see `R4_DECODE`): the sweep gated by the slot's act, t in place on jl, rho / a1 / res, no
    /// backward sweep. Same (r, a1, cout) as the sweep path on every passing shot.
    fn sweep_r4(&mut self, b: &mut B, bits: &SlotBits, w: &Win, act: Option<QubitId>, rt: &RowTmp, sx: &[QubitId],
                sy: &[QubitId], ns: Option<QubitId>, produce: bool, guard: Option<QubitId>, kt5v: &[QubitId])
                -> (Vec<QubitId>, QubitId, Option<QubitId>, bool) {
        let xt = self.x[W - 1];
        let jl = rt.jl.clone();
        // act of this slot's decode: a fake or finished shot has J = 0, sY = 0, so t = sX
        let ns = if sp_break(2) { None } else { ns };
        let ract_t = match (act, ns) {
            (Some(a), Some(n)) => {
                let t = b.alloc();
                b.x(n);
                b.and_c(a, n, t);
                b.x(n);
                Some(t)
            }
            _ => None,
        };
        if let (None, Some(n)) = (act, ns) { b.x(n); }
        let ract = match (act, ns, ract_t) { (_, _, Some(t)) => Some(t), (None, Some(n), _) => Some(n), _ => act };
        let plan = HPlan::new(w.k, ract.is_some());
        hsweep_scan(b, self, ract, rt, &plan, false);
        // h = ract & [kt5 >= 1] & [J == 0]
        if !r4_break(5) {
            erase_mbu(b, rt.f, |b| {
                let z = b.alloc();
                let zl: Vec<(QubitId, bool)> = kt5v.iter().map(|&q| (q, true)).collect();
                and_into(b, &zl, z);
                let mut l = act_lits(ract);
                l.extend(jl.iter().map(|&q| (q, true)));
                l.push((z, true));
                phase_and(b, &l);
                erase_mbu(b, z, |b| phase_and(b, &zl));
                b.free(z);
            });
        }
        // RUN-GUARD: kt5 is not read again
        if let Some(c) = guard {
            if !guard_break(1) { inc_auto(b, self, c, kt5v); }
            erase_mbu(b, c, |b| lt_sy(b, self, sx, kt5v, sy, rt.y, None));
            b.free(c);
        }
        prof(b, "i.ra1");
        let owed = r4_take(w.slot);
        // SW-CARRY's single flag from J, while J is there
        let sing = if produce {
            let q = b.alloc();
            // (NO-YSHIFT: s0 under ract, so a fake or finished shot's single flag is still 1: J = 0, the top row reads 0)
            let sg = match (sy.is_empty(), ract) {
                (true, Some(a)) => { let g = b.alloc(); b.and_c(a, rt.s0, g); Some(g) }
                _ => None,
            };
            let s0g = sg.unwrap_or(rt.s0);
            let l = self.sing_on(b, rt, s0g, &jl, sy.is_empty());
            and_auto(b, self, &l, q);
            self.sing_off(b, rt, s0g, &jl, sy.is_empty());
            if let (Some(g), Some(a)) = (sg, ract) { b.and_u(a, rt.s0, g); b.free(g); }
            Some(q)
        } else { None };
        // the stall shots of slot k: X[W-1] = 0, not finished here or earlier (LA holds LA + sX), not a fake
        let lg = if owed.is_some() { self.r4_fin(b, w, sx) } else { None };
        if let Some(m) = owed.as_ref().and_then(|o| o.sing) {
            // OWE-DIRTY (persona-mochimodev): where this slot does not produce its single flag (room-gated `produce`), the owed
            // phase (-1)^(f (1 ^ xt ^ g)) under m is applied with f on a borrowed lane t, by the toggle-twice identity
            // (t ^ f) L + t L = f L (zfor-transfer's TC-DIRTY-H pattern); t comes back unchanged. Dev override WL_OWE_DIRTY=0|1;
            // WL_OWE_CLEAN=1 puts f on a fresh clean lane instead (compute, phase, uncompute).
            if sing.is_none() && owe_dirty() && !r4_break(3) {
                let clean = std::env::var("WL_OWE_CLEAN").map_or(false, |v| v.trim() == "1");
                let t = if clean { b.alloc() } else { *self.dirty.last().unwrap() };
                let passes = if clean { 1 } else { 2 };
                for pass in 0..passes {
                    let sg = match (sy.is_empty(), ract) {
                        (true, Some(a)) => { let g = b.alloc(); b.and_c(a, rt.s0, g); Some(g) }
                        _ => None,
                    };
                    let s0g = sg.unwrap_or(rt.s0);
                    let l = self.sing_on(b, rt, s0g, &jl, sy.is_empty());
                    assert!(!l.iter().any(|x| x.0 == t), "OWE-DIRTY: borrowed lane is a literal");
                    and_auto(b, self, &l, t);
                    self.sing_off(b, rt, s0g, &jl, sy.is_empty());
                    if let (Some(g), Some(a)) = (sg, ract) { b.and_u(a, rt.s0, g); b.free(g); }
                    if pass == 0 || !clean {
                        if !(pass == 1 && owe_break()) {
                            b.push_condition(m);
                            b.z(t);
                            b.cz(xt, t);
                            if let Some((g, _)) = &lg { b.cz(*g, t); }
                            b.pop_condition();
                        }
                    }
                }
                if clean {
                    // uncompute f on the clean lane
                    let sg = match (sy.is_empty(), ract) {
                        (true, Some(a)) => { let g = b.alloc(); b.and_c(a, rt.s0, g); Some(g) }
                        _ => None,
                    };
                    let s0g = sg.unwrap_or(rt.s0);
                    let l = self.sing_on(b, rt, s0g, &jl, sy.is_empty());
                    and_auto(b, self, &l, t);
                    self.sing_off(b, rt, s0g, &jl, sy.is_empty());
                    if let (Some(g), Some(a)) = (sg, ract) { b.and_u(a, rt.s0, g); b.free(g); }
                    zero_probe(b, &[t]);
                    b.free(t);
                }
                // the q-independent part of the repayment, once
                if let Some(n) = ns {
                    b.push_condition(m);
                    if act.is_none() { b.x(n); }
                    b.x(xt);
                    match &lg {
                        Some((g, _)) => { b.x(*g); b.ccz(n, xt, *g); b.x(*g); }
                        None => b.cz(n, xt),
                    }
                    b.x(xt);
                    if act.is_none() { b.x(n); }
                    b.pop_condition();
                }
            } else {
            let q = sing.expect("owed swap-flag phase without a single flag");
            if !r4_break(3) {
                b.push_condition(m);
                b.z(q);
                b.cz(xt, q);
                if let Some((g, _)) = &lg { b.cz(*g, q); }
                if let Some(n) = ns {
                    // a fake's single flag is 1 (a finished shot is already out through g); n is flipped on act-constant slots
                    if act.is_none() { b.x(n); }
                    b.x(xt);
                    match &lg {
                        Some((g, _)) => { b.x(*g); b.ccz(n, xt, *g); b.x(*g); }
                        None => b.cz(n, xt),
                    }
                    b.x(xt);
                    if act.is_none() { b.x(n); }
                }
                b.pop_condition();
            }
            }
        }
        // t = sX - sY - J in place
        for &q in &jl { b.x(q); }
        if let Some(&s) = sy.first() { b.cx(s, rt.g); }
        b.x(rt.g);
        add_on_sm(b, self, &jl, sx, false, false, rt.g, true);
        b.x(rt.g);
        if let Some(&s) = sy.first() { b.cx(s, rt.g); }
        if !r4_break(4) {
            if let Some(a) = ract {
                b.x(a);
                for i in 0..R_BITS {
                    b.ccx(a, sx[i], jl[i]);
                }
                b.x(a);
            }
        }
        if let Some(o) = &owed {
            if !r4_break(2) {
                // (a shot that finished on a stall has t >= 8 here and owes nothing)
                for (i, &m) in o.res.iter().enumerate() {
                    b.push_condition(m);
                    b.z(jl[3 + i]);
                    b.cz(xt, jl[3 + i]);
                    if let Some((g, _)) = &lg { b.cz(*g, jl[3 + i]); }
                    b.pop_condition();
                }
            }
        }
        if let Some((g, l)) = lg { self.r4_fin_off(b, sx, g, &l); }
        let e = b.alloc();
        r4_decode(b, &jl, e);
        let mb = b.fresh_bits(2);
        b.hmr_to(jl[3], mb[0]);
        b.hmr_to(jl[4], mb[1]);
        if let Some(a) = ract {
            // a1 = e ^ !ract (t = 0 leaves e = 1 there)
            b.cx(a, e);
            b.x(e);
        }
        let r = b.alloc_n(RHO_BITS);
        for i in 0..RHO_BITS {
            b.swap(jl[i], r[i]);
        }
        let a1 = e;
        for i in 0..RHO_BITS {
            b.z_if(r[i], bits.r[i]);
        }
        b.z_if(a1, bits.a1);
        prof(b, "i.swc");
        let mut msing = None;
        let cout = sing.map(|q| {
            let c = b.alloc();
            b.and_c(q, a1, c);
            // a step's single flag is c; a fake or finished shot's is 1; a stall's is owed to its own decode two slots down
            let m = b.fresh_bits(1)[0];
            b.hmr_to(q, m);
            b.free(q);
            b.push_condition(m);
            b.z(c);
            if let Some(a) = ract {
                b.x(a);
                b.z(a);
                b.x(a);
            }
            b.pop_condition();
            msing = Some(m);
            c
        });
        prof(b, "i.ra1");
        if let (Some(a), Some(n), Some(t)) = (act, ns, ract_t) {
            b.x(n);
            b.and_u(a, n, t);
            b.x(n);
            b.free(t);
        }
        if let (None, Some(n)) = (act, ns) { b.x(n); }
        if w.slot >= 2 { r4_owe(w.slot - 2, R4Owed { res: mb, sing: msing }); }
        prof(b, "i.sweep");
        (r, a1, cout, true)
    }

    fn sweep_section(&mut self, b: &mut B, bits: &SlotBits, w: &Win, act: Option<QubitId>, rt: &RowTmp, sx: &[QubitId],
                     sy: &[QubitId], sy_len: usize, gj: Option<usize>, produce: bool, ytsw: bool, park: bool,
                     masked_rows: bool, force: Option<bool>, ns: Option<QubitId>) -> (Vec<QubitId>, QubitId, Option<QubitId>, bool) {
        prof(b, "i.sweep");
        p3(b, self, "i.sweep");
        // RUN-GUARD: c = [sX < kt + sY] (a units-bit jl = kt would give r < 0), kt5 -= c over both sweeps
        let kt5v: Vec<QubitId> = self.lb[..R_BITS].to_vec();
        let guard = if run_guard() && w.guard {
            let c = b.alloc();
            lt_sy(b, self, &sx, &kt5v, sy, rt.y, Some(c));
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
        // SW-CARRY: this slot leaves the previous slot's swap flag c (held from the r / a1 section to the slot's end)
        // (on PARK-SPLIT slots only where the park leaves SWC_SPLIT_MIN lanes of room beside z: the split repark holds
        // s0, f, y, r, a1 and its decoder beside z, so a carried lane there can set the peak)
        let swc = produce as usize;
        // H-SWEEP where the room covers r, a1 (4), the SW-CARRY lane and the scan's peak; the tree's own sweeps otherwise
        let hplan = match force {
            Some(false) => None,
            _ if !(force == Some(true) || hsweep_on()) || w.k < 2 => None,
            _ => Some(HPlan::new(w.k, act.is_some())),
        }
        .filter(|p| force == Some(true) || room_sw >= RHO_BITS + 1 + swc + p.need);
        if rowlog() {
            if let Some(p) = &hplan {
                eprintln!("WL_HSWEEP room_sw {room_sw} k {} need {} park {} masked {}", w.k, RHO_BITS + 1 + swc + p.need,
                          park as u8, masked_rows as u8);
            }
        }
        // IN-PLACE DECODE: no backward sweep where the slot allows it
        let fold0 = sy_fold_cin() && sy_len <= 1;
        if force.is_none() && fold0 && r4_slot(w) && (!masked_rows || park) && hplan.is_some() && room_sw >= hplan.as_ref().unwrap().need + 10 + swc {
            return self.sweep_r4(b, bits, w, act, rt, sx, sy, ns, produce, guard, &kt5v);
        }
        let mut fl: Vec<QubitId> = vec![];
        let mut ylent = false;
        if let Some(pl) = &hplan {
            hsweep_scan(b, self, act, rt, pl, false);
        } else if sweep_unary() && room_sw >= R_BITS {
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
            sweep_fwd_ui(b, self, act, w, rt, &ch, &fl);
            b.free_n(&ch);
        } else {
            let ch = b.alloc_n(R_BITS - 1);
            sweep_fwd(b, self, act, w, rt, &ch, true);
            b.free_n(&ch);
        }
        p3(b, self, "i.ra1");
        prof(b, "i.ra1");
        let r = b.alloc_n(RHO_BITS);
        let a1 = b.alloc();
        // jl <- sX - sY - jl in place: the rotation since the last step (rho_of in greedyfrog_model). This slot's rotation
        // rho = act & ((jl mod 8) + #{8, 15, 22, 29 <= jl}) mod 8 and a1 = act & [jl < 8] (the slot was a step).
        // Temps: y and g (|0> after the sweep) and the sweep chain.
        let jl = rt.jl.clone();
        let fold = sy_fold_cin() && sy_len <= 1;
        // jl -> ~jl + sX + !sY0 (fold) = sX - sY - jl; the map is an involution
        let jl_map = |b: &mut B| {
            for &q in &jl {
                b.x(q);
            }
            if let Some(&s) = sy.first() { b.cx(s, rt.g); }
            b.x(rt.g);
            add_on_sm(b, self, &jl, &sx, false, false, rt.g, true);
            b.x(rt.g);
            if let Some(&s) = sy.first() { b.cx(s, rt.g); }
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
        // B-SYNCGOV: on window slots rho and a1 take !h as their act (act = 1 classically there)
        let gl = gj.map(|j| (j, self.gov_lit(b, j, true)));
        let ract0 = match gl { Some((_, (l, _))) => Some(gov_act_on(b, l)), None => act };
        // STALL-PAIR: a fake slot's rho and a1 are 0
        let ns = if sp_break(2) { None } else { ns };
        let ract_t = match (ract0, ns) {
            (Some(a), Some(n)) => {
                let t = b.alloc();
                b.x(n);
                b.and_c(a, n, t);
                b.x(n);
                Some(t)
            }
            _ => None,
        };
        if let (None, Some(n)) = (ract0, ns) { b.x(n); }
        let ract = match (ract0, ns, ract_t) { (_, _, Some(t)) => Some(t), (None, Some(n), _) => Some(n), _ => ract0 };
        // IN-PLACE DECODE: what the in-place slot two above owes, on this slot's own t, sum t and t's top bits
        let owed = r4_take(w.slot);
        if let Some(o) = &owed {
            assert!(fold, "owed repair needs the mapped t");
            if !r4_break(2) {
                let xt = self.x[W - 1];
                let lg = self.r4_fin(b, w, sx);
                for (i, &m) in o.res.iter().enumerate() {
                    b.push_condition(m);
                    b.x(xt);
                    match ract {
                        Some(a) => b.ccz(a, xt, jl[3 + i]),
                        None => b.cz(xt, jl[3 + i]),
                    }
                    b.x(xt);
                    // not a shot that finished on a stall
                    if let Some((g, _)) = &lg {
                        match ract {
                            Some(a) => b.ccz(a, *g, jl[3 + i]),
                            None => b.cz(*g, jl[3 + i]),
                        }
                    }
                    b.pop_condition();
                }
                if let Some((g, l)) = lg { self.r4_fin_off(b, sx, g, &l); }
            }
        }
        if std::env::var_os("RA1_PROFILE").is_some() { eprintln!("RA1_PORT room={} enabled={}", self.room(b), ra1_lend_port()); }
        if rho_anf8() && ra1_lend_port() && self.room(b) >= 3 {
            zero_probe(b, &[rt.y, rt.g]);
            rho_anf8_into_ext(b, ract, &jl, &r, Some([rt.y, rt.g]));
            zero_probe(b, &[rt.y, rt.g]);
            let mut lits = act_lits(ract);
            lits.extend([(jl[3], true), (jl[4], true)]);
            and_auto(b, self, &lits, a1);
        } else if rho_anf8() && self.room(b) >= 5 {
            rho_anf8_into(b, ract, &jl, &r);
            let mut lits = act_lits(ract);
            lits.extend([(jl[3], true), (jl[4], true)]);
            and_auto(b, self, &lits, a1);
        } else if rho_anf() && self.room(b) >= 4 {
            rho_anf_into(b, ract, &jl, &r);
            let mut lits = act_lits(ract);
            lits.extend([(jl[3], true), (jl[4], true)]);
            and_auto(b, self, &lits, a1);
        } else {
            for i in 0..RHO_BITS {
                act_cx(b, ract, jl[i], r[i]);
            }
            let (t, c) = (rt.y, rt.g);
            for cst in [8isize, 15, 22, 29] {
                ge_auto(b, self, &jl, cst, t);
                match ract {
                    Some(a) => b.and_c(a, t, c),
                    None => b.cx(t, c),
                }
                inc_auto(b, self, c, &r);
                match ract {
                    Some(a) => b.and_u(a, t, c),
                    None => b.cx(t, c),
                }
                ge_erase(b, self, &jl, cst, t);
            }
            let mut lits = act_lits(ract);
            lits.extend([(jl[3], true), (jl[4], true)]);
            and_auto(b, self, &lits, a1);
        }
        if let (None, Some(n)) = (ract0, ns) { b.x(n); }
        if let (Some(a), Some(n), Some(t)) = (ract0, ns, ract_t) {
            b.x(n);
            b.and_u(a, n, t);
            b.x(n);
            b.free(t);
        }
        if let Some((j, (l, t))) = gl {
            gov_act_off(b, l);
            self.gov_lit_free(b, j, t, true);
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
        prof(b, "i.sweep");
        p3(b, self, "i.sweepb");
        // IN-PLACE DECODE: jl is J again: the owed swap-flag phase, on the stall shots' own single flag
        if let Some(m) = owed.as_ref().and_then(|o| o.sing) {
            if !r4_break(3) {
                b.push_condition(m);
                let sl = self.sing_on(b, rt, rt.s0, &jl, sy.is_empty());
                let lg = self.r4_fin(b, w, sx);
                let mut l = vec![(self.x[W - 1], true)];
                l.extend(sl);
                l.extend(act_lits(act));
                if let Some(n) = ns { l.push((n, true)); }
                if let Some((g, _)) = &lg { l.push((*g, true)); }
                phase_and_room(b, self, &l);
                if let Some((g, ll)) = lg { self.r4_fin_off(b, sx, g, &ll); }
                self.sing_off(b, rt, rt.s0, &jl, sy.is_empty());
                b.pop_condition();
            }
        }
        let cout = if produce {
            // SW-CARRY: jl is back to j_last and s0 = !q_0 is still live: c = a1 & [jl1..4 == 0] & !(jl0 & !s0)
            // (t = jl0 & !s0 on y, |0> after the sweep)
            prof(b, "i.swc");
            let c = b.alloc();
            if sy.is_empty() {
                let mut l = vec![(a1, false)];
                l.extend(self.sing_on(b, rt, rt.s0, &jl, true));
                and_auto(b, self, &l, c);
                self.sing_off(b, rt, rt.s0, &jl, true);
            } else {
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
            }
            prof(b, "i.sweep");
            Some(c)
        } else { None };
        prof(b, "i.sweepb");
        if let Some(pl) = &hplan {
            hsweep_scan(b, self, act, rt, pl, true);
        } else if !fl.is_empty() {
            // the OR rows free their lanes as they are erased; the chain rows above take AND lanes on demand
            assert!(self.room(b) >= R_BITS - or_ccz() as usize, "SWEEP_OR_LANES room");
            let ch2 = b.alloc_n(R_BITS - 1);
            sweep_bwd_ui(b, self, act, w, rt, &ch2, &fl);
            b.free_n(&ch2);
        } else if sweep_unary() && self.room(b) >= 2 * R_BITS - 2 {
            let ch2 = b.alloc_n(2 * R_BITS - 2);
            sweep_bwd_ui(b, self, act, w, rt, &ch2, &fl);
            b.free_n(&ch2);
        } else if self.room(b) >= R_BITS - 1 {
            let ch2 = b.alloc_n(R_BITS - 1);
            sweep_bwd(b, self, act, w, rt, &ch2, true);
            b.free_n(&ch2);
        } else {
            sweep_bwd(b, self, act, w, rt, &self.dirty, false);
        }
        if ylent {
            // YTOP-SWEEP: the backward sweep freed Y[W-1]'s lane |0>: take the same id back
            b.acquire(self.y[W - 1]);
        }
        prof(b, "i.sweep");
        if let Some(c) = guard {
            if !guard_break(1) { inc_auto(b, self, c, &kt5v); }
            erase_mbu(b, c, |b| lt_sy(b, self, &sx, &kt5v, sy, rt.y, None));
            b.free(c);
        }
        (r, a1, cout, hplan.is_some())
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
pub(crate) mod tests {
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

    #[test]
    fn decoder7_tail_port_schedule_map() {
        let ws = windows();
        assert_eq!(NSLOTS, 256);
        assert_eq!(ws.len(), NSLOTS);
        for (s, w) in ws.iter().enumerate() {
            let m = 1 + 8 * (NSLOTS - s);
            assert_eq!(w.lenb, ((usize::BITS - m.leading_zeros()) as usize).clamp(RHO_BITS, LB_BITS));
            if len_tail_port() && std::env::var("WL_LEN_TAIL_BREAK_PORT").is_err() {
                let parent_n = if len_trim() && w.slot >= LEN_TRIM_FROM { LB_BITS - 1 } else { LB_BITS };
                assert_eq!(len_n(w), parent_n.min(w.lenb), "tail must not widen parent slot {s}");
            }
        }
        let first_live = ws.iter().position(|w| !w.act_const).unwrap_or(NSLOTS);
        for (s, w) in ws.iter().enumerate() {
            let want = if s >= first_live {
                let m = s + 1 - first_live;
                ((usize::BITS - m.leading_zeros()) as usize).clamp(2, CNT_BITS - 1)
            } else {
                CNT_BITS - 1
            };
            assert_eq!(w.cntb, want);
        }
        if decoder7_port() {
            let win = (131, 185);
            assert_eq!(dec_keep(win), Some((6, 128)));
            let v: Vec<QubitId> = (0..LB_BITS as u64).map(QubitId).collect();
            let (view, base) = dec_view(&v, win);
            assert_eq!(base, 128);
            let marker_break = std::env::var("WL_DECODER7_BREAK_PORT").map_or(false, |x| x == "marker");
            assert_eq!(view[6], if marker_break { v[6] } else { v[LB_BITS - 1] });
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

    /// B-SYNCGOV model, one slot of the governed walk (deferred swap): slot s* - 1 writes the record from its post-step
    /// state and keeps a held shot un-swapped; held slots are identities except the hold's last slot e, whose F9 / F10
    /// swap the shot if the (unchanged) state asks for it. Returns whether the slot swapped.
    pub(crate) fn gov_spec_step(sp: &mut Spec, s: usize, c: &mut usize) -> bool {
        use super::super::greedyfrog_model::Slot;
        let gv = gov_cfg_at(s);
        if let Some(g) = gv {
            if g.held(*c, s) {
                // STALL-PAIR: a held slot is a fake or an add-back; the deferred swap needs an add-back
                let ns = stall_pair() && !sp.sf;
                if stall_pair() { sp.sf = ns; }
                if !ns && s + 1 == g.slot + g.levels[*c] && sp.lag == 0 && sp.a != N::ZERO && sp.a < sp.b {
                    spec_swap(sp);
                    return true;
                }
                return false;
            }
        }
        let r = sp.fwd();
        let mut sw = matches!(r, Slot::Step { sw: true, .. } | Slot::Stall { sw: true, .. });
        if let Some(g) = gv {
            if s + 1 == g.slot {
                *c = g.level_of(sp.la, sp.lb);
                if *c >= 1 && sw {
                    spec_swap(sp);
                    sw = false;
                }
            }
        }
        sw
    }
    fn spec_swap(sp: &mut Spec) {
        std::mem::swap(&mut sp.a, &mut sp.b);
        std::mem::swap(&mut sp.ta, &mut sp.tb);
        std::mem::swap(&mut sp.la, &mut sp.lb);
        sp.par ^= 1;
    }
    /// B-SYNCGOV model: walk x to slot `to` (exclusive): (pre-state at `to`, record (0 before slot s* - 1), whether
    /// slot s* - 1's step asked for a swap (deferred on held shots), lag at the sync slot)
    pub(crate) fn gov_walk(x: N, to: usize) -> (Spec, usize, bool, usize) {
        use super::super::greedyfrog_model::Slot;
        let mut sp = Spec::new(x);
        let (mut c, mut swt, mut lag) = (0, false, 0);
        for s in 0..to {
            if gov_cfg_at(s).map_or(false, |g| s + 1 == g.slot) {
                let mut q = sp.clone();
                let r = q.fwd();
                swt = matches!(r, Slot::Step { sw: true, .. } | Slot::Stall { sw: true, .. });
                lag = q.lag;
            }
            gov_spec_step(&mut sp, s, &mut c);
        }
        (sp, c, swt, lag)
    }
    /// One governed lane-model slot (as gov_spec_step).
    fn gov_fwd(ln: &mut Lanes, s: usize, c: &mut usize) {
        if let Some(g) = gov_cfg_at(s) {
            if g.held(*c, s) {
                let ns = stall_pair() && !ln.sf;
                if stall_pair() { ln.sf = ns; }
                ln.fake = ns;
                if !ns && s + 1 == g.slot + g.levels[*c] {
                    let mut sp = ln.to_spec();
                    if sp.lag == 0 && sp.a != N::ZERO && sp.a < sp.b {
                        spec_swap(&mut sp);
                        sp.cnt = ln.cnt;
                        *ln = Lanes::from_spec(&sp);
                    }
                }
                return;
            }
        }
        let (_, _, sw, _) = ln.fwd();
        if let Some(g) = gov_cfg_at(s) {
            if s + 1 == g.slot {
                *c = g.level_of(ln.la, ln.lb);
                if *c >= 1 && sw {
                    std::mem::swap(&mut ln.x, &mut ln.y);
                    std::mem::swap(&mut ln.la, &mut ln.lb);
                    ln.par ^= 1;
                }
            }
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
        Lanes { x: u.x.iter().map(|&q| g(q)).collect(), y, la, lb: num(&u.lb), cnt, par: g(u.par), sf: false, fake: false }
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
    /// TC-TIE: the compare against its definition on rings forced to tie on 0..WC top lanes, for every LB in the window:
    /// d = a1 & [first difference inside the top min(LB, WC) lanes, with Y's bit set]. Lanes and phase must come back.
    fn greedyfrog_tc_tie_gate_level() {
        let w = Win { lb: (1, 74), slot: 200, ..Win::full() };
        let n = wc();
        let mut rng = Rng(0x7469_6531_0000_0001);
        for out_form in [true, false] {
            let mut b = B::new();
            let u = GreedyFrog::alloc(&mut b);
            let a1 = b.alloc();
            let o = b.alloc();
            let start = b.ops.len();
            top_compare(&mut b, &u, if out_form { Some(o) } else { None }, &w, Some((a1, false)));
            eprintln!("tc_tie form {out_form}: {} ops", b.ops.len() - start);
            for round in 0..40u8 {
                let mut h = sha3::Shake256::default();
                h.update(b"greedyfrog-tc-tie");
                h.update(&[round, out_form as u8]);
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(b.width() as usize, 20_000 + 64, &mut xof);
                let mut want = 0u64;
                let mut lanes: Vec<(u64, u64, usize, bool)> = vec![];
                for sh in 0..64usize {
                    let lb = 1 + (rng.next() % 74) as usize;
                    let tie = 1 + (rng.next() % n as u64) as usize;
                    let (mut xv, mut yv) = (rng.next() | 1 << 63, rng.next() | 1 << 63);
                    // the top `tie` lanes agree (bit 63 = lane W - 1)
                    if tie > 0 {
                        let mask = !0u64 << (64 - tie);
                        yv = (yv & !mask) | (xv & mask);
                    }
                    if tie < 64 && tie < n && rng.next() & 1 == 0 {
                        // force a real difference at the tie lane
                        let bit = 1u64 << (63 - tie);
                        xv = (xv & !bit) | if yv & bit == 0 { bit } else { 0 };
                    }
                    let act = rng.next() % 8 != 0;
                    for i in 0..n {
                        if xv >> (63 - i) & 1 == 1 { sim.qubits[u.x[W - 1 - i].0 as usize] |= 1 << sh; }
                        if yv >> (63 - i) & 1 == 1 { sim.qubits[u.y[W - 1 - i].0 as usize] |= 1 << sh; }
                    }
                    for i in 0..LB_BITS {
                        if lb >> i & 1 == 1 { sim.qubits[u.lb[i].0 as usize] |= 1 << sh; }
                    }
                    if act { sim.qubits[a1.0 as usize] |= 1 << sh; }
                    let nn = lb.min(n);
                    let mut gt = false;
                    for i in 0..nn {
                        let (yb, xb) = (yv >> (63 - i) & 1, xv >> (63 - i) & 1);
                        if yb != xb { gt = yb > xb; break; }
                    }
                    if act && gt { want |= 1 << sh; }
                    lanes.push((xv, yv, lb, act));
                }
                sim.apply_iter(b.ops[start..].iter());
                if out_form {
                    assert_eq!(sim.qubits[o.0 as usize], want, "round {round}: d");
                    assert_eq!(sim.phase, 0, "round {round}: phase");
                } else {
                    assert_eq!(sim.phase, want, "round {round}: phase form");
                }
                for (sh, &(xv, yv, lb, act)) in lanes.iter().enumerate() {
                    for i in 0..n {
                        assert_eq!(sim.qubits[u.x[W - 1 - i].0 as usize] >> sh & 1, xv >> (63 - i) & 1, "x lane");
                        assert_eq!(sim.qubits[u.y[W - 1 - i].0 as usize] >> sh & 1, yv >> (63 - i) & 1, "y lane");
                    }
                    for i in 0..LB_BITS { assert_eq!(sim.qubits[u.lb[i].0 as usize] >> sh & 1, (lb >> i & 1) as u64, "lb lane"); }
                    assert_eq!(sim.qubits[a1.0 as usize] >> sh & 1, act as u64, "a1");
                }
            }
        }
    }

    #[test]
    fn greedyfrog_fwd_slot_gate_level() {
        let mut b = B::new();
        let mut u = GreedyFrog::alloc(&mut b);
        let start = b.ops.len();
        // STALL-PAIR: slot 1's form (a shot that cannot step fakes; slot 0 has a1 = 1 on every shot)
        u.sf = Some(b.alloc());
        let _bits = u.fwd_slot(&mut b, &Win { slot: 1, ..Win::full() });
        eprintln!("greedyfrog fwd slot: {} ops, {} Toffoli, live {} peak {}", b.ops.len() - start, b.tof, b.live, b.peak);
        let mut rng = Rng(0xfeed_beef_0101_2323);
        for round in 0..4 {
            let mut states = vec![];
            for _ in 0..64 {
                let x = rng.input();
                let mut sp = Spec::new(x);
                let slot = 1 + (rng.next() % 259) as usize;
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
                // STALL-PAIR: a fake slot's ordinary lanes hold the sum its add-back undoes
                if want.sf { continue; }
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
                    let mut ys: Vec<bool> = (0..W).map(|_| rng.next() & 1 == 1).collect();
                    // VALUE_TEMP_HOST borrows the normalised source's leading one. Real value-pass callers
                    // maintain this promise even on stalled/finished shots; the unrestricted random-source
                    // kernel remains covered by this same test with WL_VALUE_TEMP_HOST=0.
                    if value_temp_host() { ys[W - 1] = true; }
                    // GAP-MASK: a ring holds zero lanes between its value and cofactor
                    if super::super::greedyfrog_model::GAP >= 1 && kind == 0 && lbv < W { ys[W - lbv - 1] = false; }
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
                    let mut c = 0;
                    for s in 0..NSLOTS {
                        if sp.la != 0 && sp.lag > 0 {
                            pool[s].push(x);
                        }
                        // B-SYNCGOV: the governed walk
                        gov_spec_step(&mut sp, s, &mut c);
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
        let gv = gov_cfg();
        let mut gov_shots = [0usize; 3];
        for &slot in &list {
            r4_clear();
            let w = &ws[slot];
            let mut b = B::new();
            let mut u = GreedyFrog::alloc(&mut b);
            // STALL-PAIR: every slot after the first enters with the flag lane (add-back due)
            if stall_pair() && slot >= 1 { u.sf = Some(b.alloc()); }
            // B-SYNCGOV: slots inside the hold window run on a loaded record (written by forward slot s* - 1)
            let gv = gov_cfg_at(slot);
            let grec = gv.filter(|g| slot >= g.slot && slot < g.end());
            if let Some(g) = grec {
                u.gov = b.alloc_n(g.bits);
                u.gov_slot = g.slot;
            }
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
            for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par)).chain(&u.dirty)
                .chain(&u.gov).chain(&u0.gov).chain(u0.sf.iter()) {
                regs.insert(q.0);
            }
            for round in 0..rounds {
                let mut states = vec![];
                // B-SYNCGOV per shot: the record the slots run on (written by slot s* - 1; loaded on later window slots)
                let mut recs = vec![];
                for i in 0..64 {
                    let forced = if i < 40 { stall_pool.get(slot).and_then(|v| v.get(round * 40 + i)).copied() } else { None };
                    let short = if i < 40 && forced.is_none() {
                        short_pool.get(slot).and_then(|v| if v.is_empty() { None } else { v.get((round * 40 + i) % v.len()) }).copied()
                    } else { None };
                    if short.is_some() {
                        short_shots += 1;
                    }
                    let x = forced.or(short).unwrap_or_else(|| rng.input());
                    let (sp, c, swt, _) = gov_walk(x, slot);
                    if let Some(g) = gv {
                        if c >= 1 && g.held(c, slot) {
                            gov_shots[0] += 1;
                            if swt { gov_shots[1] += 1; }
                        }
                    }
                    if forced.is_some() {
                        assert!(sp.la != 0 && sp.lag > 0);
                        stall_shots += 1;
                    }
                    // STALL-PAIR: a state owed an add-back holds the fake's sum on its ordinary lanes, which the model does not
                    // track, so such a shot runs as the fake that precedes it (the pair mode's slot s + 1 covers the add-back)
                    states.push(Lanes::from_spec(&sp));
                    recs.push(c);
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
                    for (i, &q) in u0.gov.iter().enumerate() {
                        if (recs[sh] >> i) & 1 == 1 {
                            sim.qubits[q.0 as usize] |= 1u64 << sh;
                        }
                    }
                }
                let skip = if std::env::var_os("GREEDYFROG_EMU_SKIP").is_some() {
                    states.iter().enumerate().fold(0u64, |m, (sh, st)| {
                        let bad = super::super::greedyfrog_diag::emu_slot_check(st, w, ws.get(slot + 1)).is_some()
                            || (pair && { let mut l = st.clone(); l.fwd();
                                          super::super::greedyfrog_diag::emu_slot_check(&l, &ws[slot + 1], ws.get(slot + 2)).is_some() });
                        if bad { m | 1 << sh } else { m }
                    })
                } else { 0 };
                // STALL-PAIR: on the last slot a finished shot with an odd counter is an add-back whose inverse rebuilds the flag
                // from the counter's parity; it holds the fake's sum, so only the traversal test can run it
                let skip = skip | if w.last && stall_pair() {
                    states.iter().enumerate().fold(0u64, |m, (sh, st)| if st.la == 0 && st.cnt % 2 == 1 { m | 1 << sh } else { m })
                } else { 0 };
                // IN-PLACE DECODE: a shot that fakes here takes its add-back at slot + 1, whose phase is repaid at slot - 1, which
                // this pair does not run (the traversal test does)
                let skip = skip | if pair && r4_slot(&ws[slot + 1]) {
                    states.iter().enumerate().fold(0u64, |m, (sh, st)| if st.la != 0 && st.x[W - 1] == 0 { m | 1 << sh } else { m })
                } else { 0 };
                set_skip(skip);
                sim.apply_iter(b.ops[..mid].iter());
                check_dirty(&sim, &u, 64);
                for (sh, st) in states.iter().enumerate().filter(|(sh, _)| skip >> sh & 1 == 0) {
                    let mut want = st.clone();
                    let mut c = recs[sh];
                    gov_fwd(&mut want, slot, &mut c);
                    // STALL-PAIR: a fake slot's ordinary lanes hold the sum its add-back undoes
                    if want.sf { continue; }
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
                    let got: usize = u.gov.iter().enumerate().map(|(i, &q)| (((sim.qubits[q.0 as usize] >> sh) & 1) as usize) << i).sum();
                    if !u.gov.is_empty() {
                        assert_eq!(got, recs[sh], "slot {slot} round {round} shot {sh}: SYNC-GOV record changed");
                    }
                }
                if skip != 0 {
                    eprintln!("EMU_SKIP slot {slot} round {round}: skipped {skip:016x} circuit_bad {:016x}", bad & skip);
                }
                set_skip(0);
            }
        }
        if gv.is_some() {
            eprintln!("SYNC-GOV windowed: {} held shot-slots ({} with a deferred swap) checked", gov_shots[0], gov_shots[1]);
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
            all_bits.push(u.fwd_slot_next(&mut b, &ws[s], ws.get(s + 1)));
        }
        assert!(u.cmp_in.is_none());
        let mid_ops = b.ops.len();
        let t1 = b.tof;
        let peak_fwd = b.peak;
        let mut carry = None;
        let mut carried = 0;
        let gv = gov_cfg();
        for (s, bits) in all_bits.iter().enumerate().rev() {
            carried += carry.is_some() as usize;
            if let Some(g) = gov_cfg_at(s) {
                if sw_carry() && !u.gov.is_empty() && s + 1 >= g.slot && s < g.end() {
                    assert!(carry.is_some(), "SYNC-GOV window slot {s} without a carried swap flag");
                }
            }
            carry = u.inv_slot_c(&mut b, bits, &ws[s], carry, s >= 1);
        }
        assert!(u.gov.is_empty(), "SYNC-GOV record not erased");
        assert!(carry.is_none());
        eprintln!("greedyfrog traversal: SW-CARRY {} inverse slots took a carried swap flag", carried);
        eprintln!("greedyfrog traversal: forward {} T, inverse {} T, ops {} (+{}), peak {} (forward {})", t1 - t0, b.tof - t1,
                  mid_ops, b.ops.len() - mid_ops, b.peak, peak_fwd);
        {
            let c0 = super::super::counts(&b.ops[..mid_ops]);
            let c1 = super::super::counts(&b.ops[mid_ops..]);
            eprintln!("greedyfrog traversal: expected forward {:.1} inverse {:.1} total {:.1}", c0.2, c1.2, c0.2 + c1.2);
        }
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
        let mut forced: Vec<N> = std::env::var("GREEDYFROG_TRAV_X").ok().map(|v| v.split(',')
            .map(|t| N::from_str_radix(t.trim().trim_start_matches("0x"), 16).unwrap()).collect()).unwrap_or_default();
        // B-SYNCGOV (GREEDYFROG_TRAV_GOV=n, GREEDYFROG_TRAV_SEED): walk n inputs under the governor and force into the
        // 64 shots: 16 held shots whose slot s* - 1 swapped (un-swap handover), 12 held shots stalled at s* (lag tail
        // under the hold), 6 per nonzero record value, the rest random (unheld, finishing shots at the end)
        if let (Some(g), Some(n)) = (gv, std::env::var("GREEDYFROG_TRAV_GOV").ok().and_then(|v| v.parse::<usize>().ok())) {
            let seed: u64 = std::env::var("GREEDYFROG_TRAV_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
            let mut prng = Rng(0x5347_4f56_0000_0001 ^ seed.wrapping_mul(0x9e37_79b9_7f4a_7c15));
            let k = g.levels.len();
            let (mut a, mut l, mut per) = (vec![], vec![], vec![vec![]; k]);
            for _ in 0..n {
                let x = prng.input();
                let (_, c, swt, lag) = gov_walk(x, g.slot + 1);
                if c >= 1 && swt && a.len() < 16 { a.push(x); continue; }
                if c >= 1 && lag > 0 && l.len() < 12 { l.push(x); continue; }
                if c >= 1 && per[c].len() < 6 { per[c].push(x); }
            }
            forced.extend(a);
            forced.extend(l);
            for v in per { forced.extend(v); }
            forced.truncate(48);
            for _ in 0..seed { rng.next(); }
        }
        r4_clear();
        // IN-PLACE DECODE (GREEDYFROG_TRAV_STALLS=n): walk n inputs and force those with 2 or more stalls in a row since a step
        // (res != 0) and those that finish on a stall into the shots, longest runs first
        if let Some(n) = std::env::var("GREEDYFROG_TRAV_STALLS").ok().and_then(|v| v.parse::<usize>().ok()) {
            use super::super::greedyfrog_model::Slot;
            let seed: u64 = std::env::var("GREEDYFROG_TRAV_SEED").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
            let mut prng = Rng(0x5354_414c_4c00_0001 ^ seed.wrapping_mul(0x9e37_79b9_7f4a_7c15));
            let (mut runs, mut fins): (Vec<(usize, N)>, Vec<N>) = (vec![], vec![]);
            for _ in 0..n {
                let x = prng.input();
                let mut sp = Spec::new(x);
                let (mut m, mut best, mut fin) = (0usize, 0usize, false);
                for _ in 0..NSLOTS {
                    match sp.fwd() {
                        Slot::Stall { .. } => {
                            m += 1;
                            best = best.max(m);
                            if sp.la == 0 { fin = true; }
                        }
                        Slot::Step { .. } => m = 0,
                        _ => {}
                    }
                    if sp.la == 0 { break; }
                }
                if best >= 2 { runs.push((best, x)); }
                if fin { fins.push(x); }
            }
            runs.sort_by(|a, b| b.0.cmp(&a.0));
            eprintln!("greedyfrog traversal: stall runs >= 2: {} (longest {}), finish on a stall: {}", runs.len(),
                      runs.first().map_or(0, |r| r.0), fins.len());
            forced.extend(fins.into_iter().take(8));
            forced.extend(runs.into_iter().map(|r| r.1).take(40));
        }
        let (mut nheld, mut nswt) = (0, 0);
        for i in 0..64 {
            let x = if i < forced.len() { forced[i] } else { rng.input() };
            let sp0 = Spec::new(x);
            starts.push(Lanes::from_spec(&sp0));
            let (sp, c, swt, _) = gov_walk(x, NS);
            if c >= 1 { nheld += 1; if swt { nswt += 1; } }
            finals.push(Lanes::from_spec(&sp));
            xs.push(x);
        }
        if gv.is_some() {
            eprintln!("greedyfrog traversal: SYNC-GOV held shots {nheld} (sw_t = 1: {nswt}) of 64");
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

    // ---------------------------------------------------------------- lyc-lead2 02-hsweep: h-sweep == the tree's section

    /// The inverse slot's sweep section (`sweep_section`, RUN-GUARD as built) emitted alone on a slot-shaped register
    /// set: rings, LA / LB (kt5 = LB[0..5]), borrowed lanes, act, sX, sY (one lane with SY_FOLD_CIN, else five), the
    /// B-SYNCGOV record and RowTmp. mode 0: act constant, 1: act quantum, 2: act constant with ract = [record < gj]
    /// (the SYNC-GOV window slots).
    struct SecRig {
        b: B,
        u: GreedyFrog,
        act: Option<QubitId>,
        sx: Vec<QubitId>,
        sy: Vec<QubitId>,
        s0: QubitId,
        inputs: Vec<QubitId>,
        outs: Vec<QubitId>,
        tof: u64,
        peak_above: u64,
        nbits: usize,
        hs: bool,
        need: u64,
    }

    #[derive(Clone, Copy, Debug)]
    struct SecCfg {
        k: usize,
        mode: u8,
        gj: usize,
        masked: bool,
        fold: bool,
        produce: bool,
    }

    #[derive(Clone, Copy, Debug)]
    struct SecCase {
        q: u32,
        kt5: usize,
        act: bool,
        sx: usize,
        sy: usize,
        rec: usize,
        s0: bool,
    }

    fn sec_rig(force: Option<bool>, c: SecCfg, slack: Option<u64>) -> SecRig {
        let mut b = B::new();
        let mut u = GreedyFrog::alloc(&mut b);
        if c.mode == 2 {
            u.gov = b.alloc_n(GOV_BITS);
        }
        let act = if c.mode == 1 { Some(b.alloc()) } else { None };
        let sx = b.alloc_n(R_BITS);
        let sy = b.alloc_n(if c.fold { 1 } else { R_BITS });
        let rt = RowTmp::alloc(&mut b, c.masked);
        let bits = SlotBits { d: b.fresh_bits(1)[0], r: b.fresh_bits(RHO_BITS), sw: b.fresh_bits(1)[0],
                              a1: b.fresh_bits(1)[0], rv: RollRec::default(), rc: RollRec::default(), z0m: None };
        let w = Win { k: c.k, act_const: c.mode != 1, ..Win::full() };
        let mut inputs: Vec<QubitId> = vec![];
        inputs.extend(u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par))
            .chain(&u.dirty).chain(&u.gov).chain(act.iter()).chain(&sx).chain(&sy).chain(std::iter::once(&rt.s0)));
        let entry = b.live;
        if let Some(s) = slack {
            u.cap = entry + s;
        }
        let need = if c.k >= 2 {
            (RHO_BITS + 1 + c.produce as usize + HPlan::new(c.k, act.is_some()).need) as u64
        } else {
            u64::MAX
        };
        let t0 = b.tof;
        let gj = (c.mode == 2).then_some(c.gj);
        let (r, a1, cout, hs) = u.sweep_section(&mut b, &bits, &w, act, &rt, &sx, &sy, sy.len(), gj, c.produce, false,
                                                false, c.masked, force, None);
        let tof = b.tof - t0;
        let peak_above = b.peak - entry;
        let mut outs = r.clone();
        outs.push(a1);
        outs.extend(cout.iter());
        let nbits = b.fresh_bits(1)[0].0 as usize + 64;
        SecRig { b, u, act, sx, sy, s0: rt.s0, inputs, outs, tof, peak_above, nbits, hs, need }
    }

    fn sec_setb(v: &mut [u64], q: QubitId, s: usize, on: bool) {
        if on {
            v[q.0 as usize] |= 1 << s;
        } else {
            v[q.0 as usize] &= !(1 << s);
        }
    }

    /// Simulates a rig on <= 64 cases (the other shots random): phase 0 on all 64 shots, every input lane unchanged,
    /// every lane that is neither an input nor an output |0>. Returns the outputs per case (r, a1, the SW-CARRY lane).
    fn sec_sim(rig: &SecRig, k: usize, cases: &[SecCase], salt: u64) -> Vec<usize> {
        let mut h = sha3::Shake256::default();
        h.update(b"lyc-hsweep-section");
        h.update(&salt.to_le_bytes());
        let mut xof = h.finalize_xof();
        let width = rig.b.width() as usize;
        let mut sim = Simulator::new(width, rig.nbits, &mut xof);
        let mut rng = Rng(0x5eed_0000_0000_0001 ^ salt.wrapping_mul(0x9e37_79b9_7f4a_7c15));
        let inset: std::collections::BTreeSet<u64> = rig.inputs.iter().map(|q| q.0).collect();
        for &q in &inset {
            sim.qubits[q as usize] = rng.next();
        }
        for (s, c) in cases.iter().enumerate() {
            for j in 1..k {
                sec_setb(&mut sim.qubits, rig.u.y[j - 1], s, (c.q >> (j - 1)) & 1 == 0);
            }
            for i in 0..R_BITS {
                sec_setb(&mut sim.qubits, rig.u.lb[i], s, (c.kt5 >> i) & 1 == 1);
                sec_setb(&mut sim.qubits, rig.sx[i], s, (c.sx >> i) & 1 == 1);
            }
            for (i, &q) in rig.sy.iter().enumerate() {
                sec_setb(&mut sim.qubits, q, s, (c.sy >> i) & 1 == 1);
            }
            if let Some(a) = rig.act {
                sec_setb(&mut sim.qubits, a, s, c.act);
            }
            for (i, &q) in rig.u.gov.iter().enumerate() {
                sec_setb(&mut sim.qubits, q, s, (c.rec >> i) & 1 == 1);
            }
            sec_setb(&mut sim.qubits, rig.s0, s, c.s0);
        }
        let init = sim.qubits.clone();
        sim.apply_iter(rig.b.ops.iter());
        assert_eq!(sim.phase, 0, "salt {salt}: phase garbage {:016x}", sim.phase);
        let outs: std::collections::BTreeSet<u64> = rig.outs.iter().map(|q| q.0).collect();
        for q in 0..width {
            if inset.contains(&(q as u64)) {
                assert_eq!(sim.qubits[q], init[q], "salt {salt}: input lane {q} changed");
            } else if !outs.contains(&(q as u64)) {
                assert_eq!(sim.qubits[q], 0, "salt {salt}: scratch lane {q} dirty");
            }
        }
        (0..cases.len())
            .map(|s| rig.outs.iter().enumerate().map(|(i, q)| (((sim.qubits[q.0 as usize] >> s) & 1) as usize) << i).sum())
            .collect()
    }

    /// Independent reference of the section: RUN-GUARD kt' = kt5 - [sX < kt5 + sY0] (mod 32); J = the last row j in
    /// [1, k-1] with q_j & act & [kt' >= j]; R = (sX - sY - J) mod 32; ract = act, or [record < gj] on SYNC-GOV slots;
    /// rho = ract & ((R mod 8) + #{8, 15, 22, 29 <= R}) mod 8, a1 = ract & [R < 8]; SW-CARRY c = a1 & ([J == 0] |
    /// [J == 1] & s0).
    fn sec_ref(c: &SecCfg, x: &SecCase) -> usize {
        let sy0 = x.sy & 1;
        let g = if run_guard() { (x.sx < x.kt5 + sy0) as usize } else { 0 };
        let kt = (x.kt5 + 32 - g) % 32;
        let act = c.mode != 1 || x.act;
        let j = if act { (1..c.k).rev().find(|&j| (x.q >> (j - 1)) & 1 == 1 && kt >= j).unwrap_or(0) } else { 0 };
        let sy = if c.fold { sy0 } else { x.sy };
        let rr = (x.sx + 64 - sy - j) % 32;
        let ract = match c.mode {
            1 => x.act,
            2 => x.rec < c.gj,
            _ => true,
        };
        let rho = if ract { (rr % 8 + [8usize, 15, 22, 29].iter().filter(|&&t| rr >= t).count()) % 8 } else { 0 };
        let a1 = ract && rr < 8;
        let mut o = rho | (a1 as usize) << RHO_BITS;
        if c.produce {
            o |= ((a1 && (j == 0 || (j == 1 && x.s0))) as usize) << (RHO_BITS + 1);
        }
        o
    }

    /// q patterns x every kt5 (x act on mode 1): exhaustive while k - 1 <= `exh`, else `nrand` per kt5 (half uniform,
    /// half sparse); sX, sY, the record and s0 random per case.
    fn sec_cases(rng: &mut Rng, c: &SecCfg, exh: usize, nrand: usize) -> Vec<SecCase> {
        let kk = c.k - 1;
        let mut cases = vec![];
        for act in if c.mode == 1 { vec![false, true] } else { vec![true] } {
            for kt5 in 0..32 {
                let qs: Vec<u32> = if kk <= exh {
                    (0..1u32 << kk).collect()
                } else {
                    (0..nrand)
                        .map(|i| {
                            if i % 2 == 0 {
                                (rng.next() as u32) & ((1 << kk) - 1)
                            } else {
                                (0..kk).filter(|_| rng.next() % 6 == 0).fold(0, |q, j| q | 1 << j)
                            }
                        })
                        .collect()
                };
                for q in qs {
                    let sy = (rng.next() % if c.fold { 2 } else { 32 }) as usize;
                    cases.push(SecCase { q, kt5, act, sx: (rng.next() % 32) as usize, sy, rec: (rng.next() % 4) as usize,
                                         s0: rng.next() & 1 == 1 });
                }
            }
        }
        cases
    }

    /// H-SWEEP against the tree's own sweep section (the same `sweep_section` forced onto this tree's sweeps) and an
    /// independent reference: k = 2 .. 22; act constant, act quantum and B-SYNCGOV ract (gj 1, 2, 3); plain and masked
    /// RowTmp; sY folded (one lane) and five lanes; SW-CARRY lane on and off; RUN-GUARD as built. Exhaustive q
    /// patterns x every kt5 x act for k - 1 <= 12 on the production shape (plain, folded, SW-CARRY), 192 random q
    /// patterns per kt5 for k = 14 .. 22 on every shape. Outputs (r, a1, c) equal on every case for both and equal to
    /// the reference; inputs unchanged, every other lane |0>, phase 0 on every batch (both). Then the dispatch at the
    /// cap: room = need takes the h-sweep within the cap, need - 1 the tree's sweeps.
    #[test]
    fn greedyfrog_hsweep_vs_tree() {
        let mut rng = Rng(0x4853_5745_4550_0825);
        let g = run_guard() as u64;
        let mut ncases = 0usize;
        let mut nrand = 0usize;
        let modes: [(u8, usize); 5] = [(0, 1), (1, 1), (2, 1), (2, 2), (2, 3)];
        let shapes: [(bool, bool, bool); 4] = [(false, true, true), (true, true, false), (false, false, true), (true, true, true)];
        for k in 2..=22usize {
            for &(mode, gj) in &modes {
                for (si, &(masked, fold, produce)) in shapes.iter().enumerate() {
                    let c = SecCfg { k, mode, gj, masked, fold, produce };
                    let tree = sec_rig(Some(false), c, None);
                    let hsw = sec_rig(Some(true), c, None);
                    assert!(hsw.hs && !tree.hs);
                    if si == 0 && (mode < 2 || gj == 1) {
                        eprintln!("HSWEEP k {k:2} mode {mode}: tree {:4} T peak +{:2} | h-sweep {:4} T peak +{:2} (need {})",
                                  tree.tof, tree.peak_above, hsw.tof, hsw.peak_above, hsw.need + g);
                    }
                    let exh = if si == 0 { 12 } else { 6 };
                    let cases = sec_cases(&mut rng, &c, exh, if k >= 14 { 192 } else { 24 });
                    for (bi, chunk) in cases.chunks(64).enumerate() {
                        let salt = ((((k * 8 + mode as usize) * 4 + gj) * 4 + si) * 1_000_000 + bi) as u64;
                        let (ot, oh) = (sec_sim(&tree, k, chunk, salt), sec_sim(&hsw, k, chunk, salt));
                        for (s, x) in chunk.iter().enumerate() {
                            let want = sec_ref(&c, x);
                            assert_eq!(ot[s], want, "tree vs reference: {c:?} {x:?}");
                            assert_eq!(oh[s], want, "h-sweep vs tree / reference: {c:?} {x:?}");
                        }
                    }
                    ncases += cases.len();
                    if k >= 14 {
                        nrand += cases.len();
                    }
                }
            }
        }
        // the dispatch at the cap (room counted after RUN-GUARD's lane): room >= need takes the h-sweep and stays under
        // the cap; need - 1 runs the tree's sweeps; both match the reference
        let mut nd = 0;
        for k in [4usize, 13, 21, 22] {
            for &(mode, gj) in &modes[..3] {
                for produce in [false, true] {
                    let c = SecCfg { k, mode, gj, masked: false, fold: true, produce };
                    let need = sec_rig(Some(true), c, None).need + g;
                    for slack in [need - 1, need, need + 1] {
                        let rig = sec_rig(None, c, Some(slack));
                        assert_eq!(rig.hs, slack >= need, "dispatch {c:?} slack {slack}");
                        if rig.hs {
                            assert!(rig.peak_above <= slack, "h-sweep over the cap: {c:?} +{} > {slack}", rig.peak_above);
                        }
                        let cases = sec_cases(&mut rng, &c, 0, 16);
                        for (bi, chunk) in cases.chunks(64).enumerate() {
                            let o = sec_sim(&rig, k, chunk, 77_000_000 + (nd * 1000 + bi) as u64);
                            for (s, x) in chunk.iter().enumerate() {
                                assert_eq!(o[s], sec_ref(&c, x), "dispatch slack {slack}: {c:?} {x:?}");
                            }
                        }
                        if k == 22 && produce {
                            eprintln!("HSWEEP dispatch k {k} mode {mode} slack {slack}: h {} {} T peak +{}", rig.hs as u8,
                                      rig.tof, rig.peak_above);
                        }
                        nd += 1;
                    }
                }
            }
        }
        eprintln!("HSWEEP {ncases} cases ({nrand} at k 14..22): tree == h-sweep == reference, phase 0, scratch clean; \
                   {nd} dispatch rigs ok");
    }

    /// GREEDYFROG_HSWEEP_FULL=1: the h-sweep section on EVERY q pattern x kt5 x act at k = 14 .. 22 (act constant,
    /// act quantum, SYNC-GOV ract gj 2; production shape; sX, sY, record, s0 random per case) against the reference,
    /// phase 0 and clean scratch on every batch.
    #[test]
    fn greedyfrog_hsweep_full() {
        if std::env::var("GREEDYFROG_HSWEEP_FULL").is_err() {
            return;
        }
        let mut rng = Rng(0x4853_5745_4550_08ff);
        let mut n = 0u64;
        for k in 14..=22usize {
            for (mode, gj) in [(0u8, 1usize), (1, 1), (2, 2)] {
                let c = SecCfg { k, mode, gj, masked: false, fold: true, produce: true };
                let hs = sec_rig(Some(true), c, None);
                for act in if mode == 1 { vec![false, true] } else { vec![true] } {
                    for kt5 in 0..32 {
                        for q0 in (0..1u32 << (k - 1)).step_by(64) {
                            let chunk: Vec<SecCase> = (0..64u32)
                                .map(|i| SecCase { q: q0 + i, kt5, act, sx: (rng.next() % 32) as usize, sy: (rng.next() % 2) as usize,
                                                   rec: (rng.next() % 4) as usize, s0: rng.next() & 1 == 1 })
                                .collect();
                            let o = sec_sim(&hs, k, &chunk, 9_000_000_000 + n);
                            for (s, x) in chunk.iter().enumerate() {
                                assert_eq!(o[s], sec_ref(&c, x), "full: {c:?} {x:?}");
                            }
                            n += 64;
                        }
                    }
                }
                eprintln!("HSWEEP full k {k} mode {mode}: exhaustive q x kt5 x act ok ({n} cases so far)");
            }
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
                    // (ROT-ZERO: lane 0 ends at 0: a shift of 0 keeps it, as no real slot has it set there)
                    for k in 0..W { let bit=if k==0 { 0 } else if k>=W-8 { ((v&255)>>(W-1-k))&1 } else { ((k*73+v*37)^(k*v))&1 };
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
            if ROT8_PROMISE_DELETE && !rot_zero() {assert_eq!(split+3,bf.ops.len(),"one cswap (cx,ccx,cx) dropped");}
            let mut h=sha3::Shake256::default();h.update(b"rot8-promise");let mut xof=h.finalize_xof();
            let mut sim=Simulator::new(b.width() as usize,64,&mut xof);
            let rnd=|k:usize,salt:u64|(k as u64*2+salt+1).wrapping_mul(0x9e3779b97f4a7c15).rotate_left(((k*7+sh)%64) as u32);
            let init:Vec<u64>=(0..W).map(|k| if k>=W-sh || (sh==0 && k==0) {0} else {rnd(k,sh as u64)}).collect();
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
mod l8_frame_test {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput,Update};
    #[test]
    fn l8_prefix_frame_exhaustive_channels(){
        for h in 5..=7 {for (av,sv) in [(false,false),(true,false),(true,true)] {for batch in 0..((1usize<<h)+63)/64 {
            let mut b=B::new();let lb=b.alloc_n(LB_BITS);let act=b.alloc();let step=b.alloc();let pre=b.alloc_n(h);
            let view:Vec<QubitId>=lb[..h].iter().chain(std::iter::once(&lb[LB_BITS-1])).copied().collect();
            mark_msb(&mut b,step,&lb);super::super::mask::onehot_goto(&mut b,&view,&pre,wc());
            if !l8_break(2){mark_done_inv(&mut b,Some(act),&lb[..LB_BITS-1]);}
            if l8_break(3){b.cz(lb[0],lb[1]);}
            super::super::mask::clear_onehot_dec(&mut b,&view,&pre,if l8_break(1){wc()^2}else{wc()});
            mark_done_inv(&mut b,Some(act),&lb[..LB_BITS-1]);mark_msb(&mut b,step,&lb);
            let mut hash=sha3::Shake256::default();hash.update(b"l8-frame-independent-channel-test");let mut xof=hash.finalize_xof();
            let mut sim=Simulator::new(b.width()as usize,2000,&mut xof);
            for shot in 0..64{let n=(batch*64+shot)% (1<<h);for k in 0..h{sim.qubits[lb[k].0 as usize]|=(((n>>k)&1)as u64)<<shot;}}
            sim.qubits[act.0 as usize]=if av{!0}else{0};sim.qubits[step.0 as usize]=if sv{!0}else{0};
            sim.apply_iter(b.ops.iter());assert_eq!(sim.phase,0,"phase h={h} act={av} step={sv}");
            for shot in 0..64 {let n=(batch*64+shot)%(1<<h);for k in 0..LB_BITS{assert_eq!((sim.qubits[lb[k].0 as usize]>>shot)&1,((n>>k)&1)as u64,"LB changed h={h} act={av} step={sv}");}}
            assert_eq!(sim.qubits[act.0 as usize],if av{!0}else{0});assert_eq!(sim.qubits[step.0 as usize],if sv{!0}else{0});
            for q in pre {assert_eq!(sim.qubits[q.0 as usize],0,"prefix dirty");}
        }}}
    }
}

#[cfg(test)]
mod ra1_port_test {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{Update,ExtendableOutput};
    #[test]
    fn ra1_port_exhaustive_channels() {
        for controlled in [false,true] { for init in 0..8usize {
            let mut b=B::new(); let j=b.alloc_n(5); let r=b.alloc_n(3); let a=b.alloc(); let e=b.alloc_n(2);
            rho_anf8_into_ext(&mut b,if controlled {Some(a)} else {None},&j,&r,Some([e[0],e[1]]));
            let mut hash=sha3::Shake256::default(); hash.update(b"ra1-public-port-independent-oracle"); let mut xof=hash.finalize_xof();
            let mut sim=Simulator::new(b.width() as usize,2000,&mut xof);
            for shot in 0..64 {let n=shot&31;for k in 0..5 {sim.qubits[j[k].0 as usize]|=(((n>>k)&1) as u64)<<shot;}
                for k in 0..3 {sim.qubits[r[k].0 as usize]|=(((init>>k)&1) as u64)<<shot;}
                sim.qubits[a.0 as usize]|=((shot>>5) as u64)<<shot;
            }
            sim.apply_iter(b.ops.iter());
            assert_eq!(sim.phase,0,"phase controlled={controlled} init={init}");
            for shot in 0..64 {let n=shot&31; let act= !controlled || shot>=32;
                let rho=((n&7)+[8,15,22,29].into_iter().filter(|&t|n>=t).count())&7;
                let want=init ^ if act {rho} else {0};
                for k in 0..3 {assert_eq!((sim.qubits[r[k].0 as usize]>>shot)&1,((want>>k)&1) as u64,"output n={n} init={init} controlled={controlled}");}
                for k in 0..5 {assert_eq!((sim.qubits[j[k].0 as usize]>>shot)&1,((n>>k)&1) as u64,"input changed");}
                assert_eq!((sim.qubits[a.0 as usize]>>shot)&1,(shot>>5) as u64,"control changed");
            }
            for q in 9..b.width() as usize {assert_eq!(sim.qubits[q],0,"borrowed/scratch q{q}");}
        }}
    }
}

#[cfg(test)]
mod fullstack_frame_test {
 use super::*;
 #[test] fn basezero_and_nonzero_fallback() {
  let ws=windows();let mut eligible=0;let mut fallback=0;
  for w in &ws {
   if let Some(h)=l8_compatible(w){let(keep,base)=dec_keep(w.lb).unwrap();assert_eq!(base,0);assert_eq!(h,keep);eligible+=1;}
   if let Some((_,base))=dec_keep(w.lb){if base!=0{assert!(l8_compatible(w).is_none());fallback+=1;}}
  }
  // TC-TIE: the masked compare, and with it the decoder handoff, is gone
  assert!(tc_tie() || eligible>0,"base-zero handoff never eligible");
  if decoder7_port(){assert!(fallback>0,"nonzero-base fallback never activated");}
  eprintln!("FULLSTACK_FRAME eligible={} nonzero_fallback={}",eligible,fallback);
 }
}
