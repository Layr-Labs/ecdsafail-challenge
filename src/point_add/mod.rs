//! Low-qubit point addition around a self-inverse Euclid inverter F: |x>|0> -> |a>|par>|0>, a = +-1/x mod p.
//! F is an exact restoring-row Euclid walk with no history tape: quotient digits grow in the freed top lanes of the
//! dividend ring and are consumed by the inverse of the same row on the cofactors, so the reverse pass is the reversed
//! gate list. The N ring is its own clock: its root rises one wire per slot and acts when it reaches the top wire, so
//! the only length register is E = F - L_frame mod 32. Translated from emit/srm2.py + emit/pa2.py.
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::atomic::{AtomicBool, Ordering};

// ---- DS_* (Draeaeschiibe, lane dial768 / sam765): the page dial on this tree. Every switch is inert at PAGE_D = 11 (the
// published stream byte for byte); below 11 it takes the parent's own fallback for every lever that is written for page 11.
/// DS_PAGE_EDITS: the two edits that let the page move: conv_fwd's spare bound = the real limit (the spares stay below the
/// two freed lanes page_cases_xy reads as literals; the published "<= 6" refused every page below 11), and even11's digit
/// list fixed at ten lanes (the published "0..PAGE_D.min(10)" drops the tenth digit below page 10; same lanes at 10 and 11).
const DS_PAGE_EDITS: bool = true;
/// DS_GATE11: every lever of this tree written for page 11 only (compile- or run-time asserts on PAGE_D == 11, a ring width
/// of 235, digit-count recipes certified at page 11, stored page-11 packets) is switched off below page 11; its switch
/// comment documents "false = the parent stream", which is then what runs. At PAGE_D = 11 nothing changes.
const DS_GATE11: bool = true;
const DS_P11: bool = !DS_GATE11 || PAGE_D == 11;
/// DS_K2_ALLW: the AKK2 K2 kernels at every page width: the compile assert's PAGE_D == 11 dropped (its real contract is the
/// K2C helpers and the HOPP hop), S2 (hop_c by mac_sgn) and S3 (PCONV cv by cv_conj) at widths >= 3, H1 by invp_lo at
/// 6..10 and invp12 at 12 (cat_invp at 3..5, as the parent's fallback). Unit tests: dial_tests.rs (cfg(test)).
const DS_K2_ALLW: bool = true;

// PO: default-off pi10 independent high-carry hold.
// PO2: default off; -1 enables all certified odd sites, or select one site for a probe.
const PO2_ODD_FREE_RISE: bool = DS_P11; // DS_GATE11 (published: true)
const PO2_ODD_SITE: i32 = -1;
const _: () = assert!(!PO2_ODD_FREE_RISE || (LOOK16 && PAGE_G && PAGE_N && PAGE_D == 11 && CAD4 && CAD4B && ECAP == 17));
// SW3R: share s[i] & F within ordinary TOGV downward cells. Default off.
const SW3R_VMASK: bool = DS_P11; // DS_GATE11 (published: true)
const PO_PI10_HOLD: bool = DS_P11; // DS_GATE11 (published: true)
// PO: default-off shared even-post routing.
const PO_EVEN_REFLECT: bool = DS_P11; // DS_GATE11 (published: true)
/// NR_PARK_V (default off): the start mask taken out of even11's V rows 2..9 at the plain full ladder slots
/// (EVJS, no tier sharing). Before row 2: F = act_4 = yt & h1 & !y1 & !y2 is held, and the source bits below each shot's
/// junction (the three zone lanes y[wv - t/2 + 1..=3]) are swapped out of the chain under F: wire 0 into y1, wire 1 into y2
/// (zero lanes of every class >= 4), wire 2 (classes 8, 9 with wait 0) into ZB. A restoring cell with source 0 and carry 0 is
/// inert, so rows 2..9 run plain cells with no mask and no toggles; their act cubes read F (row 3: [F] and [yt, h1, !y1, !F]).
/// ZB holds a parked bit through the rows: ZB_BUSY is set, the first decision MCX takes x0 as its clean lane (mclean), the
/// others take the dirty form. After row 9 the list is reversed. Shots without F are not touched; the rows are the identity
/// on them as before. Python gate check (V2b): equal to the parent on all 765 lanes.
/// BUILDER, first check: the marker roles and the pre-cancel accept data on ZB_LANE while ZB_BUSY is set (TOGC is the
/// precedent for a held ZB). false = the stream of e056d67.
const NR_PARK_V: bool = DS_P11; // DS_GATE11 (published: true)
/// SM_L3B (port of the 783 tree's L3B; default off): in a SW3R V row (row_vmask) whose toggle list XORs to the empty
/// cube at the last key (every shot has the mask lane at 1 there; mask lane F clean at entry), the last key's forward and backward
/// toggle cubes and the mask on the cell at that key are dropped: that cell runs plain, the mask covers cells below the key only.
/// Exact by cancellation (the cumulative cube XOR is syntactically [()], checked in the build). Python gate check:
/// false = the parent stream.
const SM_L3B: bool = true;
const _: () = assert!(!NR_PARK_V || (TOGV && EVJS && CAD4 && CAD4B && PAGE_G && PAGE_D == 11 && ZB > 0 && !TOGC));
const N: usize = 256;
const W: usize = N + 1;
const NONE: u32 = u32::MAX;
const EB: usize = 2;
/// Clean lane for the AND of many controls inside F.
const ZB: usize = if PAGE_G { 1 } else { 0 };
/// the clean AND lane (first lane allocated); P1 uses it also as the sandwich's AND lane Z (MCX into it: Barenco)
const ZB_LANE: u32 = 512;
/// f_circuit's y0, y1 (ring Y's two non-x lanes at F's input): 513, 514 when ZB is on
const Y0_LABEL: u32 = 512 + ZB as u32;
const Y1_LABEL: u32 = 513 + ZB as u32;
static IN_F: AtomicBool = AtomicBool::new(false);
/// P1: the ZB lane is held (the sandwich's AND lane): every MCX takes the Barenco form meanwhile.
static ZB_BUSY: AtomicBool = AtomicBool::new(false);
/// debug marks (trace only): slot DBG_T records (100000 + k, gate index) at mk(t, k)
static DBG_T: std::sync::atomic::AtomicI32 = std::sync::atomic::AtomicI32::new(-1);
static DBG_M: std::sync::Mutex<Vec<(i32, usize)>> = std::sync::Mutex::new(Vec::new());
const PIW: usize = 26; // fb-r7s dd9b468b (~0.004 / 9,024): was 48
const ECAP: i32 = 17; // was 18, 24 (ob-ladder2-e24 twin, fb-r7b 514c1e0c), 26 before that
/// SD1 (tier split, v4 SDP.md section 3): first big class that waits for a slot 0 mod 16 (its offset has four bits).
/// 0 = off: every big class acts at the next slot 0 mod 8, which is the stream of d4dd7eb1. NOT YET WIRED beyond
/// big_pairs11: see notes v4/SD1_progress.md before setting it.
const TIER_LONG: i32 = if W4HOST { 16 } else if L1 || CAD4 { 0 } else { 16 };
/// L-C banded cadence (op-layout 1e952d1, op-check 09fea3e): with TIER_LONG > 0 a big arrival at slot tn in
/// [CUT_T, CUT_S - 17] that turns out to be a long class (e >= TIER_LONG) waits for a slot 0 mod 16 (wait w up to 15, its
/// 4th bit on the lane W4); every other arrival keeps cadence 8 (the 16 slots above each cut, and the native ends). W4 is
/// set only by those arrivals and cleared at their act slot, so it is 0 at every boundary >= CUT_S - 16 and < CUT_T.
fn long16(tn: i32) -> bool { TIER_LONG > 0 && (CUT_T..=CUT_S - 17).contains(&tn) }
/// cubes over the (hi or u or v mod 16, w) points of big-class cases: p = h | w << 4, p < 256; bit 7 of p (w >= 8) is lane w4
fn hw_cubes(on: &[usize], off: &[usize], lanes: &[u32], w4: u32) -> Vec<Vec<Lit>> {
    let lit = |c: &Cubes| -> Vec<Vec<Lit>> { c.iter().map(|x_| x_.iter().map(|&(v, bt)| (lanes[v], bt == 1)).collect()).collect() };
    let (mut on2, mut off2) = ([0u128; 2], [0u128; 2]);
    for &p_ in on { on2[p_ >> 7] |= 1u128 << (p_ & 127); }
    for &p_ in off { off2[p_ >> 7] |= 1u128 << (p_ & 127); }
    let vs = [0usize, 1, 2, 3, 4, 5, 6];
    if on2[1] == 0 && off2[1] == 0 {
        return if on2[0] == 0 { vec![] } else { lit(&dtree(on2[0], off2[0], &vs, 3)) };
    }
    let mut out: Vec<Vec<Lit>> = vec![];
    for sd in 0..2usize {
        if on2[sd] == 0 { continue; }
        if on2[1 - sd] == 0 && on2[sd] & off2[1 - sd] == 0 {
            return lit(&dtree(on2[sd], off2[sd] | off2[1 - sd], &vs, 3));
        }
        for mut c in lit(&dtree(on2[sd], off2[sd], &vs, 3)) {
            c.push((w4, sd == 1));
            out.push(c);
        }
    }
    out
}
/// P5 shell (op-p5, branch q765-v5-p5shell): the frogdrop product stage at s = 0, w = 5 (module fd2, transplanted
/// from q765-v4-shell 58658f3) around this tree's walk F. false = the stream of d4dd7eb1 (S3 shell, sha of P0).
const P5SHELL: bool = true;
/// P1 (v5 TEAM_40M, op-build): fixed page of the low words between the cuts. false = the stream of d4dd7eb1.
/// Step (a): `page_in` at the boundary below slot T + 1 (T in PAGE_CUTS) and its inverse right after it, no page work.
const PAGE: bool = false;
/// L1: frame page width 10 with tier cadence 8 (TIER_LONG = 0, no W4 lane); W4's lane is the
/// converter's sixth lifted bit. false = width 11 with the cadence-16 tiers (the stream of 561c6ff1).
const L1: bool = false;
const PAGE_D: usize = if L1 { 10 } else { 5 };
/// L3X0: the sandwich's conjunctions that target ZB use the clean X[0] (its z2) as the
/// AND lane (2k - 3) instead of the dirty Barenco form (4k - 8). false = the stream of 561c6ff1.
const L3X0: bool = true;
/// r7e JSWAP: big-phase junction swap (see Machine::jswap): the big classes' rows run as plain ring rows on the low words
/// swapped into the rings at the shot's junction; replaces the page cells, windows and slides of big_phase. false = beff6dda.
const JSWAP: bool = true;
const JSWAP_V: bool = true;
const JSWAP_C: bool = true;
/// r7e W4HOST: the 4th wait bit of the long classes (cadence 16, TIER_LONG = 16) lives on the waiter's own zero lanes, so the
/// frame needs no W4 lane of its own. While waiting: y[8] (zero for every big waiter). In the phase of a slot 0 mod 16 it
/// rides CAD4's lane W1: every W1 waiter acted in the slot's low work (c4p clears W1) and the next W1 arrivals are marked after
/// the phase, so W1 is 0 on every shot for the whole phase. The acting shots' W4 moves y[8] -> W1 before the marker -> hi
/// conversion (y[8] is hi's bit 3) and the phase then runs exactly as with a W4 lane (the last rotation by 8 clears it).
/// (v1 hosted it on y[9] / x[wv-11] / x[wv-3] / x[wv-5] inside the phase: x[wv-11] is ring data for the class e = 10, and the
/// C rows 9..0 read it as W4: every e = 10 shot at a slot 0 mod 16 failed, fb-r7e w4diff 2026-11-14.) At a slot 8 mod 16 the
/// not-acting long waiters are memoed on F for the end terms (F = fl & code 01 & y[8], exact before the acted shots leave
/// code 11 and after their fl is erased). false = TIER_LONG 0 with CAD4 (or the W4 lane of 561c6ff1 without CAD4).
const W4HOST: bool = false; // off at ECAP 18 (TIER_LONG 0 with CAD4), -228k measured there
const _: () = assert!((JSWAP && JSWAP_V && JSWAP_C && CAD4) || !W4HOST);
/// MERGE1 (dv-r7a): gap-1 second-form class (sp1 / sp1c) rides generic row 1 in even11 (exact, 0 extra lanes).
const MERGE1: bool = true;
/// CAD4 (fb-r7a A2): banded cadence 4 of the low classes. A low shot with e in 4..9 that reaches the top for a slot
/// tn = 2 or 3 mod 4, tn in [CUT_T + 2, CUT_S - 5], waits (code 01 kept, flag on the real lane W1 = the D11 frame's one
/// spare lane, the old W4) for the next slot 0 mod 4, where it acts with l, f both one larger (the geometry of slot
/// t + 2). The slots 2 mod 4 in [CUT_T + 2, CUT_S - 6] then run only the classes 0..3. The big classes (e >= 10) keep
/// their own wait bits and never set W1. W1 is 0 at both cuts. Needs D = 11 (L1 off) and TIER_LONG = 0.
const CAD4: bool = true;
/// CAD4B (fb-r7a A2b, exact trims of CAD4's slots; false = the gates of A2): (1) at a slot 2 mod 4 the big waiters step aside
/// together with the W1 waiters before the rows (one rotation of ring Y instead of two; literal Y[1] = 0 as in the public
/// 775 frame); (2) one W1 conjugation per ladder page site over the union of the lanes its uses touch, instead of one per
/// class or group; (3) a waiter is a class >= 4: its start cubes drop the literals Y[1], Y[2] (V rows), the digit lanes
/// 2, 3 and the lifted-marker literal h0 of the rows 2, 3 (C rows).
const CAD4B: bool = true;
/// EVJS (fb-r7a, 2026-11-14): junction swap for the low classes at the ladder slots of even11 (classes 2..9 all present),
/// the big phase's JSWAP geometry per (class, wait): V form VB[b] <-> y[wv - l + b], VA[b] <-> x[wv - f + b]; C form
/// VB[b] <-> y[wv - l + 2D - 1 - b], SC[b] <-> x[wv - f + 2D - 1 - b]; the rows run as plain ring rows (pd = 0): no page cells,
/// no per-row slides, no window rotations; the W1 waiters (l, f one larger) by one W1 up-rotation of the union span.
const EVJS: bool = true;
fn evjs_on() -> bool { EVJS && std::env::var("R7A_NO_EVJS").is_err() }
/// FW_WINDOW_GROUPS: at the four EVJS ladder sites (V-win-in, V-win-out, cw, C-win-out) the
/// junction swap is done per window, not per class. Classes sharing l (lf: 2,3 / 4,5 / 6,7 / 8,9) share the Y-side
/// swap and classes sharing f (3,4 / 5,6 / 7,8) share the X-side swap, under a group flag that the parent walk
/// already holds (or that one CX / one CCX toggled in and out puts on a lane) at the kept-op position in FW_GRP;
/// e = 0 and e = 1 share their Y window (l equal) inside one flag walk sp0, sp0 ^ sp1, sp1. Every flag is the XOR
/// of the parent's one-hot use flags on all 2^11 code-lane inputs.
/// Needs SW2_LADDER_SEM over all sites (positions index the certified kept-op list). false = the parent stream.
const FW_WINDOW_GROUPS: bool = DS_P11; // DS_GATE11 (published: true)
/// FW: the sites the switch covers (empty = all four); the first build step is ["V-win-in"] alone.
const FW_SITES: &[&str] = &[];
fn fw_on(site: &str) -> bool { FW_WINDOW_GROUPS && (FW_SITES.is_empty() || FW_SITES.contains(&site)) }
/// FW: (site, kept ops, [(kept-op position after which the group use goes, Y side, first class, control lane, prep)])
static FW_GRP: &[(&str, usize, &[(u16, bool, i32, N, &[LOp])])] = &[
    ("V-win-in", 142, &[(10, true, 2, N::D, &[LOp::Cx(N::F, N::D), LOp::Cx(N::ZB, N::D)]),
        (31, false, 3, N::ZB, &[LOp::Cx(N::F, N::ZB), LOp::Cx(N::D, N::ZB)]),
        (50, false, 5, N::ZB, &[LOp::Cx(N::D, N::ZB)]),
        (55, true, 6, N::F, &[LOp::Ccx(N::Y(6), N::D, N::F)]),
        (84, false, 7, N::ZB, &[LOp::Cx(N::F, N::ZB), LOp::Cx(N::D, N::ZB)]),
        (88, true, 8, N::F, &[LOp::Ccx(N::Y(8), N::D, N::F)])]),
    ("V-win-out", 142, &[(10, true, 2, N::D, &[LOp::Cx(N::F, N::D), LOp::Cx(N::ZB, N::D)]),
        (31, false, 3, N::ZB, &[LOp::Cx(N::F, N::ZB), LOp::Cx(N::D, N::ZB)]),
        (50, false, 5, N::ZB, &[LOp::Cx(N::D, N::ZB)]),
        (55, true, 6, N::F, &[LOp::Ccx(N::Y(6), N::D, N::F)]),
        (84, false, 7, N::ZB, &[LOp::Cx(N::F, N::ZB), LOp::Cx(N::D, N::ZB)]),
        (88, true, 8, N::F, &[LOp::Ccx(N::Y(8), N::D, N::F)])]),
    ("cw", 204, &[(6, true, 2, N::ZB, &[LOp::Ccx(N::Y(2), N::D, N::ZB)]),
        (25, false, 3, N::ZB, &[LOp::Ccx(N::Yt, N::D, N::ZB)]),
        (50, true, 4, N::ZB, &[LOp::Ccx(N::Yt, N::D, N::ZB)])]),
    ("C-win-out", 204, &[(6, true, 2, N::ZB, &[LOp::Ccx(N::Xt(3), N::D, N::ZB)]),
        (25, false, 3, N::ZB, &[LOp::Ccx(N::Yt, N::D, N::ZB)]),
        (50, true, 4, N::ZB, &[LOp::Ccx(N::Yt, N::D, N::ZB)])]),
];
const _: () = assert!(!FW_WINDOW_GROUPS || (SW2_LADDER_SEM && SW2_LAD_SITES.is_empty() && EVJS && LADDER && PAGE_D == 11));
/// TOGV / TOGC (fb-r7a, fb-r7s's R7_S s13 lever): the low rows of even11 in toggle form. The inline cube list of a wire is an
/// XOR decomposition of "this shot's chain is active here"; a mask lane m toggled at each wire by the symmetric difference of
/// its list and the previous wire's holds that indicator, and the zone cells are gated by (s, t, m) once. V rows: m = F (0 for
/// every shot before the sandwich); C rows: m = ZB (MCX of the row then take dirty lanes: ZB_BUSY).
const TOGV: bool = true;
const TOGC: bool = false;
/// NR_CTOG_Y1 (default off): at the plain full ladder slots of even11 (EVJS, no tier sharing) the C rows
/// 3..9 take the toggle form on y1 that E3C uses at the tier slots, here without a big family: the inline cube list of each
/// zone wire becomes toggles of the mask lane y1, and the zone cells are gated by (s, t, y1) once. y1 is 0 on every acting
/// shot of rows >= 3 (class >= 3; only row 2 uses y1, as its top). The mask above the zone is 1, so the reset around the
/// decision (lik reads y1) is the empty cube. Rows 0..2 keep the inline form. Checked in Python
/// (LE's native C block against the integer oracle). false = the stream of e056d67.
const NR_CTOG_Y1: bool = true;
/// SM_L2V (the V-site half of the 783 tree's L2; default off): in odd11's V row 0 hook, `actv & d -> y0` becomes CX(d, y0).
/// Exact because d is written only by actv-controlled gates in the odd V rows and starts 0 (x0 is flipped to 0 at odd11's head), so d
/// implies actv there. Python check (CL's odd V block, 20,000 real e = 1 actors, non-actors, planted faults).
/// The C-side sites of L2 and all of L9 are NOT included (premise unchecked or false). false = the parent stream.
const SM_L2V: bool = true;
const _: () = assert!(!NR_CTOG_Y1 || (EVJS && CAD4 && CAD4B && ZB > 0 && !TOGC));
/// CM_FAMB (default off): in even11's E3C shared C rows (k >= 2) the big family's start toggles read !h1
/// instead of famb = yt & !h1 & W1. Only the actors' mask matters in a toggle cube (non-actors have d = 0 and see an identity
/// row), and on the row's actors (lik = yt & h1 & .., famb) !h1 alone separates the families. Likewise a low wait-0 cube (!W1)
/// is 0 on every big actor (W1 = 1), so it drops the family literal h1. With these cubes the reset around the decision is the
/// empty cube: the decision reads y1 only through lik (h1 = 1), where every big cube is 0. The act cubes, hooks and every other
/// famb read are unchanged. Checked in Python. false = the stream of 144df3d.
const CM_FAMB: bool = true;
const _: () = assert!(!CM_FAMB || (E3C && E3C2R2 && LOOK16));
/// CM_YT (default off): even11's C rows that still use the inline form at the EVJS slots (no E3C sharing;
/// NR_CTOG_Y1 rows excluded) take the toggle form with the mask on yt = y[wv - 1], which is 1 on every actor of every C row
/// (lik, sp0, sp1, sp1c and famb all contain yt) and is no lane of the row. The empty cube is dropped from the first toggle,
/// so the mask is yt xor (the inline list) and returns to yt at the end of the zone on every shot: no reset is needed.
/// Checked in Python. false = the stream of 144df3d.
const CM_YT: bool = true;
const _: () = assert!(!CM_YT || (EVJS && ZB > 0 && !TOGC));
/// CM_HOLD (default off): plain C rows 3..7 at the EVJS slots (no E3 sharing) take CM_YT's toggle form (mask on
/// yt) and hold the class tests of `cm_hold_table` (a run of zero literals "class >= yy" on h0 and the consumed digit lanes) on
/// y[1..k-2], which are 0 on every actor of row k (lik reads !y[1..k-2]) and no lane of the row. The tests are built through
/// row_vzr's cv (before and after each sweep, so lik reads the restored lanes at the decision); each toggle cube then reads the lane
/// instead of the run. Y0 is NOT usable: it holds the row-0 digit q_0 during these rows. Takes precedence over NR_CTOG_Y1 and
/// CM_YT on rows 3..7. Checked in Python. false = the stream of CM.patch.
const CM_HOLD: bool = true;
const _: () = assert!(!CM_HOLD || (EVJS && CAD4 && CAD4B && ZB > 0 && !TOGC));
/// BK_D1 (default off): at the LOOK16 kept tiers the big family's start toggle cubes of the E3 shared rows drop
/// the family literal !h1 when the cube has a positive literal on a lane the row's low act cube lik(k) = yt & h1 & !y[1..k-2]
/// negates. Every h1 shot that acts in the row has that lane 0, so the cube is 0 on it with or without !h1 (an identity of lik,
/// no reachability invariant). V rows 4..9 (mask F, read by no act cube; y2 / y3 / y7 carry U3): the shots that do not act
/// cancel (d = x0 = 0 at entry, same mask both sweeps). C rows 6..9 with CM_FAMB (mask y1, which lik reads at the decision): the
/// care set is every yt & h1 & !y[2..k-2] shot and holds the same zeros (y4 / y5 / y6 carry ac0..ac2 until their moves at
/// rows 5 / 6 / 7). Checked in Python. false = the parent stream.
const BK_D1: bool = true;
const _: () = assert!(!BK_D1 || (LOOK16 && E3C && E3C2R2 && TOGV && EVJS));
/// CM_HOLD: the held class tests of plain C row k as digit sets (digit k = h0, digit j >= k + 1 = x[wv - j]), in lane order y1, y2.
/// From the exhaustive search (the same plan at 64 of the 66 plain slots).
fn cm_hold_table(k: i32) -> Vec<Vec<i32>> {
    match k {
        3 => vec![vec![3, 4, 5, 6, 7, 8]],
        4 => vec![vec![4, 5, 6], vec![4, 5, 6, 7, 8]],
        5 => vec![vec![5, 6], vec![5, 6, 7, 8]],
        6 => vec![vec![6, 7, 8]],
        7 => vec![vec![7, 8]],
        _ => vec![],
    }
}
/// CVHV (fb-r7a, fb-r7s s13 'conversions'): in the big V rows k <= min e the act cube is plain cl (exact(k) has no hi
/// literal), so the hi -> u conversion cv_v is applied once around that run of rows instead of 4 times per row. Exact: the
/// rows read u only through the start toggles, and nothing between those rows reads the hosted lanes.
const CVHV: bool = true;
fn cvhv_on() -> bool { CVHV && std::env::var("R7A_NO_CVHV").is_err() }
/// CVHC: the same for the big C rows k <= min e. The C loop's moves relocate the hosted bits of the ACTING shots only, so
/// the hoisted conversion is gated by cl (non-acting shots keep their lanes; they see identity through the rows anyway).
const CVHC: bool = true;
fn cvhc_on() -> bool { CVHC && std::env::var("R7A_NO_CVHC").is_err() }
/// E3V (fb-r7a): at a tier slot the big shots' V rows 0..9 move into even11; rows 2..9 are SHARED with the low rows (one
/// chain: carry h0 with the big actors' h0 toggled to 0 around the row, start mask F with a family literal on every start
/// toggle; big act cube yt & !h1 & !y1 & !h0 there). Big rows 0, 1 run alone in even11 (mask F, carry y[9]). Before the low
/// post the big shots are parked like waiters (hi -> marker again, row-0 digit y0 -> y7, conversion undone) and step aside
/// (extra hold term: code 01, x1 = x2 = 0, y0 = y1 = 0; the acted e = 1 second form has y0 | y1 = 1, so sp1c gets that
/// literal at a tier slot); big_phase moves the digit back, redoes its prefix and resumes at V row 10.
const E3V: bool = true;
fn e3v_on() -> bool { E3V && std::env::var("R7A_NO_E3V").is_err() }
/// E3V bisect: first shared row (default 2; 10 = no shared row; env R7A_E3_NOSHARE = 10, R7A_E3_FROM = j)
fn e3from() -> i32 {
    if std::env::var("R7A_E3_NOSHARE").is_ok() { return 10; }
    std::env::var("R7A_E3_FROM").ok().and_then(|v| v.parse().ok()).unwrap_or(2)
}
/// E3C (M4 Path 2): the cofactor-side mirror of E3V. At an E3 slot (TIER_LONG 0) the big-only block of
/// big_phase (V rows 10..e, the sandwich, C rows e..10) runs inside even11 between the low V and C blocks; ONE merged
/// sandwich serves both families (its K2 hop is unconditional, so two cannot be open at once); the big C rows 9..3 share
/// the low C rows (toggle form on y1, the mask reset around the decision because lik reads y1); big C rows 2..0 run
/// alone; the big shots park y0, y1, y2 on x[wv-1..wv-3] for the low post; big_phase keeps the marker and its post.
/// false = the stream of cdd86ed4.
const E3C: bool = true;
fn e3c_on() -> bool { E3C && std::env::var("R7A_NO_E3C").is_err() }
static E3C_T: AtomicBool = AtomicBool::new(false);
/// E3C2 (extends E3C): in the big-only rows k >= 11 the hosted lanes stay converted (V: u from row 0 to the
/// last V row, C: v from the first C row) and the class test e >= k rides one flag lane per side (V: y1, C: y9), toggled
/// between rows by family-gated cubes [e == k] on the converted (u or v, w) points (e = 2u + w = 2v - w), instead of four
/// conversions per row and exact(k) cubes on (hi, w0). Needs E3C. false = the stream of e37a4b3.
const E3C2: bool = true;
fn e3c2_on() -> bool { E3C2 && std::env::var("R7A_NO_E3C2").is_err() }
/// E3C2R2: the big C row 2 also shares the low C row 2: the low cubes stay inline (TOGC off), the big family
/// rides one inline cube [!h1 & !m] per wire on the mask m = x[wv - 3] (0 on big shots at row 2, never toggled on low shots:
/// the big group toggles are family-gated), [] ^ [!h1 & !m] = h1 | m. y1 is row 2's top, so the y1 form of rows 9..3 does not
/// apply. (A first form on ZB with the dirty MCX forms measured +25k raw.) Needs E3C. false = the stream with E3C2 alone.
const E3C2R2: bool = true;
/// PO: normal even-slot waiters share the post's down-turn. Default off.
const PO_EVEN_MERGE_TURN: bool = DS_P11; // DS_GATE11 (published: true)
const _: () = assert!(!PO_EVEN_MERGE_TURN || (PAGE_G && PAGE_N && PAGE_D == 11 && CAD4B && (ECAP == 17 || ECAP == 18)));
fn e3c2r2_on() -> bool { E3C2R2 && std::env::var("R7A_NO_E3C2R2").is_err() }
/// AKB_E3C2_KEY (8396ec91 S5a / M1a adapted to E3C2): E3C2's ladder toggles [e == k] / [e >= 11] read
/// a class-coded hosted register instead of the converted points, where a class is a diagonal (4 cubes on the V side, 8 on the
/// C side). V side: before the first toggle B[1..3] += A mod 8 under famb, so B' = (2 U3 + r) mod 16 = e - 4 (late and early
/// cases); the big V rows 11.. key on A only, so B may hold it; undone after the last toggle. C side: before the first toggle
/// A += B[0..2] mod 8 under famb, so A' = (U3 + V4) mod 8 = (e - 3) mod 8 (with V4 the map is one to one); the big C rows key on
/// B only; undone after the k = 10 clear. Same ladder values on y1 / y9 at every row. false = the stream of e056d67.
const AKB_E3C2_KEY: bool = true;
const _: () = assert!(!AKB_E3C2_KEY || (LOOK16 && E3C2));
/// LOOK16 (mechanism E): tier slots every 16 with early service. Big service runs at
/// the slots 0 mod 16 in [CUT_T, CUT_S - 16] in the h1 hosted code (A = y2, y3, y7: hi' = (e >> 1) - 5, then U3 = u - 2;
/// B = y4, y5, y6, y8: r = tn mod 16, then V4 = v - 1) and at CUT_S - 8 in the parent form; the slots 8 mod 16 in
/// [CUT_T + 8, CUT_S - 24] have no big service and release the frozen shots. At a kept tier T >= CUT_T + 16 a big shot due at
/// T - d (d = 1..8) whose late wait would exceed e - 4 (EA: e < 20 - d) is pulled to the top (detector + normaliser, code 01,
/// r = 16 - d), acts with u = (e + d) / 2, v = (e - d) / 2, is frozen (flag y[wv-2], release bits y[wv-3..wv-5], code 11, not at
/// the top) and released at T - 8 by an up-rotation of 8 - d. false = the stream of b7104bb.
const LOOK16: bool = true;
/// LR_V01 ("V sharing change", h1 port): at every E3 tier the big V rows 0 and 1 join the
/// shared V rows (as rows 2..9 already do): the old low start mask is kept verbatim, [!H1, W1] cancels its constant one on the
/// big actors, the big start groups enter with the same family literals (keys: LOOK16 h1 U3 on A at kept tiers, the parent's
/// hi/u lanes at 424), H0 is the shared carry (cleared on the big actors by the existing W1 & !H1 bracket), the gap-0 / gap-1
/// presets and the row-1 d & !H1 header correction get !W1, the old separate big rows 0 / 1 and their hooks are not emitted.
/// Rows go through row_vmask like every ordinary V row (SW3R's cell identity does not read the mask's cubes).
const LR_V01: bool = true;
const _: () = assert!(!LR_V01 || (E3V && TOGV && EVJS && CAD4 && CAD4B && JSWAP && JSWAP_V && !W4HOST && TIER_LONG == 0 && MERGE1 && ZB > 0 && PAGE_G));
/// AK_PCONV (port of the public P10_CONV, rows 72ffb1ca / 8396ec91, GM_K2AND form): post_page's
/// format switch (both values odd after the step: SC <- tA') moves into the sandwich close, where the page holds r = A'/B,
/// p/B and tB between the inverse of hop_c (the K2 MAC) and the inverse of hop_ab: under c = act & !F & r0 (on z2),
/// SC <- p/B - r SC (cimul + cadd on the clean [z], AND markers kept); the next post_page emits only its role swap.
/// With SW1_GROUP_K2 the group packet ends with exactly hop_c's gates (asserted), so the close splits it there.
/// E3C's merged even sandwich converts only its low acts (CONV_ACTS): the big family keeps its full post in big_phase.
const AK_PCONV: bool = true;
/// AK_PCONV_S3 (8396ec91 S3_CV_CONJ): the close's cv by hop2::cv_conj (x1 conjugation, 157 T) instead of cimul + cadd.
const AK_PCONV_S3: bool = true;
const _: () = assert!(!AK_PCONV_S3 || AK_PCONV);
thread_local! {
    static CONV_PEND: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static CONV_ACTS: std::cell::RefCell<Option<Vec<Vec<Lit>>>> = const { std::cell::RefCell::new(None) };
}
/// AK_PCONV counters: closes converted, post_pages switch skipped, post_pages full, closes without conversion
static AK_CONV_CNT: [std::sync::atomic::AtomicUsize; 4] = [const { std::sync::atomic::AtomicUsize::new(0) }; 4];
/// PK3_PCONV_BIG (default off; needs AK_PCONV): E3C's merged even sandwich converts the big family too
/// (CONV_ACTS = acts + famb, so the close's cg covers famb & !F & r0), and big_phase's h2_post_page emits only its role swap
/// (CONV_PEND_BIG). The close arithmetic is AK_PCONV's (M). Between the close (even11's sw_post, emitted
/// after the C rows) and big_phase's h2_post_page nothing writes VA / VB / SC on family shots (source trace).
/// Premises from the parent's own contracts, not checked on walks in Python: famb at the close is the shot set that takes
/// big_phase's role swap (ctl = yt & h0 & h1 there), and acts2 is pairwise disjoint (sandwich_x). Gate: fixed seed 876 0 / 0.
/// false = the parent stream.
const PK3_PCONV_BIG: bool = true;
const _: () = assert!(!PK3_PCONV_BIG || (AK_PCONV && LOOK16 && E3C && E3C2));
thread_local! {
    static PK3_FAM: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static CONV_PEND_BIG: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static PK3_IN_BIG_POST: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
/// PK3_PCONV_BIG counters: merged closes that converted the family, big posts emitted as role swap only
static PK3_PB_CNT: [std::sync::atomic::AtomicUsize; 2] = [const { std::sync::atomic::AtomicUsize::new(0) }; 2];
/// L16_TRIM (needs LOOK16): (1) the four h1 junction swaps run inside the hosted form already present (V side
/// after bcv: A = U3, only B -> V4 inside; C side after the hoisted conversion: no conversion inside), so the unconditional
/// convert / revert pairs inside l16_jswap go; (2) the detector's late-class exclusion cube is emitted only for the distances
/// d where an in-cap class is late (e >= 20 - d with e <= ECAP); a detected over-cap shot fails in the cap model either way.
/// false = the stream of 58d2b4f with the same switches.
const L16_TRIM: bool = true;
const _: () = assert!(!L16_TRIM || LOOK16);
/// AKB_BRM_BARREL (8396ec91 S6a adapted to E3C): at the LOOK16 h1 tiers the merged sandwich's big digit
/// reversal brm (one class flag pair + a reversal of y0 / x[wv-1..wv-e] per class) becomes one funnel barrel on the family:
/// x0 = famb held; for the key x = e - 10 = 2 hi' + r0 (bit 0 on B0 = y4, bit k >= 1 on A[k-1]; r = e mod 2 on every case) the
/// stages b = 3..0 shift the span down by 2^b under ZB = x0 & bit (AND compute / measured uncompute), only over the positions
/// the 11-digit window can still occupy; then a fixed reversal of positions 0..10. Q = y0, x[wv-1..wv-10] then holds weight j
/// on lane j as before; span lanes above Q land elsewhere and nothing between the two blocks reads them (S);
/// the second emission (after the role swap) is the gate reverse. false = the stream of e056d67.
const AKB_BRM_BARREL: bool = DS_P11; // DS_GATE11 (published: true)
const _: () = assert!(!AKB_BRM_BARREL || LOOK16);
/// LT_JSWAP_FUNNEL (needs L16_TRIM): l16_jswap_f's one-hot demux over the U3 windows (Y side, page VB)
/// and the V4 windows (X side, page VA or SC) becomes a funnel per side. The family cube goes on d once per call; stages
/// b >= 1 move the window hull down by 2^b under ZB = d & key bit b (an AND bracket, measured uncompute); stage 0 is fused
/// with the page swap (ZB = d & b0, then ZB = d & !b0); then the stages run reversed. Each stage's span is trimmed from the
/// tier's key set, so the funnel touches only wires inside the hull of the listed windows. The permutation equals the
/// parent's for every family shot whose key is in the tier's case list (Python check: exhaustive on the control lanes
/// at every kept tier and site, and on cap-17 walk states). false = the stream of e056d67.
const LT_JSWAP_FUNNEL: bool = true;
const _: () = assert!(!LT_JSWAP_FUNNEL || (LOOK16 && L16_TRIM));
/// LT_JSWAP_FUNNEL: one side of the funnel. wins: key -> [(page lane, ring index); PAGE_D] with consecutive keys one ring
/// wire apart; ring: the ring's lanes; kb: the key lanes (LSB first); d: the family flag. Returns the gates and the lanes
/// of the ring it touches.
fn lt_funnel_side(wins: &BTreeMap<i32, Vec<(u32, usize)>>, ring: &[u32], kb: &[u32], d: u32) -> (GL, Vec<u32>) {
    let dd = PAGE_D;
    let ks: Vec<i32> = wins.keys().cloned().collect();
    let k0 = ks[0];
    let w0: Vec<i64> = wins[&k0].iter().map(|p| p.1 as i64).collect();
    let mut s: i64 = 0;
    for &k in &ks {
        if k == k0 { continue; }
        for bq in 0..dd {
            let dl = wins[&k][bq].1 as i64 - w0[bq];
            let ss = dl / (k - k0) as i64;
            assert!(dl == ss * (k - k0) as i64 && (ss == 1 || ss == -1) && (s == 0 || s == ss), "LT funnel: windows not one wire apart");
            s = ss;
        }
    }
    if s == 0 { s = 1; }
    let origin: i64 = if s == 1 { *w0.iter().min().unwrap() - k0 as i64 } else { *w0.iter().max().unwrap() + k0 as i64 };
    let pos = |i: i64| -> u32 { let j = origin + s * i; assert!(j >= 0 && (j as usize) < ring.len(), "LT funnel: hull off the ring"); ring[j as usize] };
    let rel = |w: i64| -> i64 { s * (w - origin) };
    let mut rel0: Vec<i64> = vec![];
    for bq in 0..dd {
        let r = rel(w0[bq]) - k0 as i64;
        for &k in &ks { assert!(rel(wins[&k][bq].1 as i64) - k as i64 == r, "LT funnel: window order differs between keys"); }
        rel0.push(r);
    }
    let mut srt = rel0.clone();
    srt.sort();
    assert!(srt == (0..dd as i64).collect::<Vec<i64>>(), "LT funnel: a window is not PAGE_D consecutive wires");
    let kmax = *ks.last().unwrap();
    assert!(kmax >= 0 && (kmax as usize) < (1usize << kb.len()), "LT funnel: key wider than its lanes");
    let nb = 32 - (kmax as u32).leading_zeros();
    let bt = |v: i32, i: u32| -> bool { (v >> i) & 1 == 1 };
    let mut touched: Vec<u32> = vec![];
    let mut stages: Vec<(u32, GL)> = vec![];
    for b in (1..nb).rev() {
        let kbs: Vec<i32> = ks.iter().cloned().filter(|&k| bt(k, b)).collect();
        if kbs.is_empty() { continue; }
        let lo = kbs.iter().map(|k| k % (1 << b)).min().unwrap() as i64;
        let hi = kbs.iter().map(|k| k % (1 << b)).max().unwrap() as i64 + dd as i64;
        let mut sw: GL = vec![];
        for i in lo..hi {
            cswap(ZB_LANE, pos(i), pos(i + (1i64 << b)), &mut sw);
            touched.push(pos(i));
            touched.push(pos(i + (1i64 << b)));
        }
        stages.push((b, sw));
    }
    let mut g: GL = vec![];
    for (b, sw) in &stages {
        g.extend(and2(d, kb[*b as usize], ZB_LANE));
        g.extend_from_slice(sw);
        g.extend(and2(d, kb[*b as usize], ZB_LANE));
    }
    // stage 0 fused with the page swap: the window now sits at [k & 1, (k & 1) + PAGE_D)
    for par in [1i64, 0] {
        if !ks.iter().any(|&k| (k & 1) as i64 == par) { continue; }
        let mut fx: GL = vec![];
        for bq in 0..dd {
            let w = pos(rel0[bq] + par);
            cswap(ZB_LANE, wins[&k0][bq].0, w, &mut fx);
            touched.push(w);
        }
        let flip: GL = if par == 1 { vec![] } else { vec![gx(kb[0])] };
        g.extend_from_slice(&flip);
        g.extend(and2(d, kb[0], ZB_LANE));
        g.extend(fx);
        g.extend(and2(d, kb[0], ZB_LANE));
        g.extend_from_slice(&flip);
    }
    for (b, sw) in stages.iter().rev() {
        g.extend(and2(d, kb[*b as usize], ZB_LANE));
        g.extend(rev(sw));
        g.extend(and2(d, kb[*b as usize], ZB_LANE));
    }
    (g, touched)
}
/// LOOK16_ENC (test only): the h1 hosted code at every mid tier slot in [CUT_T, CUT_S - 16] at the parent's schedule
/// (cadence 8, r = w, no early service). false = the stream of b7104bb.
const LOOK16_ENC: bool = false;
const _: () = assert!(!(LOOK16 && LOOK16_ENC));
/// AKB_KERASE_HOLD (8396ec91 S7a adapted): at the LOOK16 h1 tiers big_phase's act-flag erase holds each
/// group's common literals [xt (gg = 0) or !xt (gg = 1), code 11, !y0] on ctl = x0 (clean here: the end rotations clear it) so
/// every cube's MCX is [x0] + its own literals; the u = 2 (code 01) cubes are emitted unchanged after the held ones (all target
/// the act flag and none reads it: they commute). Same Boolean function on every state. false = the stream of e056d67.
const AKB_KERASE_HOLD: bool = true;
const _: () = assert!(!AKB_KERASE_HOLD || LOOK16);
/// BK_L3B_E3 (default off): L3B on the E3 shared V rows 2..9 of the LOOK16 kept tiers (176 rows per
/// traversal). Their toggle list never XORs to [()] syntactically (the big groups' minterm cubes), so SM_L3B skips them; but on
/// every shot that satisfies one of the row's act cubes the cubes XOR to 1, checked here by a truth table over the lanes the
/// toggle and act cubes read (bk_l3b_cut). Then the last key's forward and backward toggles go and the cell at that key runs
/// plain (BK_WCUT shortens the zone to the cells below it): for an actor the mask there is 1 anyway; a shot that does not act
/// cancels (d = x0 = 0 at entry, F read by no act cube, the remaining toggles still balanced). Python gate checks:
/// false = the parent stream.
const BK_L3B_E3: bool = DS_P11; // DS_GATE11 (published: true)
const _: () = assert!(!BK_L3B_E3 || (LOOK16 && E3C && TOGV && EVJS && SW3R_VMASK));
/// BK_L3B_E3: the zone cut of the one row_vmask call that is under it (usize::MAX = none).
static BK_WCUT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(usize::MAX);
/// BK_L3B_E3: (last key, toggle map with that key's cubes emptied) when on every assignment of the lanes read by the toggle
/// cubes and the act cubes that satisfies an act cube the toggle cubes XOR to 1 (a cube with clashing literals is 0); None else.
fn bk_l3b_cut(tog: &BTreeMap<usize, Vec<Vec<Lit>>>, acts: &[Vec<Lit>], n: usize) -> Option<(usize, BTreeMap<usize, Vec<Vec<Lit>>>)> {
    let last = *tog.keys().next_back()?;
    if last >= n || tog[&last].is_empty() || acts.is_empty() {
        return None;
    }
    let mut lanes: Vec<u32> = tog.values().flatten().chain(acts.iter()).flat_map(|c| c.iter().map(|x| x.0)).collect();
    lanes.sort();
    lanes.dedup();
    if lanes.len() > 20 {
        return None;
    }
    let val = |c: &Vec<Lit>, a: u32| -> bool { c.iter().all(|&(q0, p)| ((a >> lanes.binary_search(&q0).unwrap()) & 1 == 1) == p) };
    for a in 0u32..(1u32 << lanes.len()) {
        if !acts.iter().any(|c| val(c, a)) {
            continue;
        }
        let mut x = false;
        for c in tog.values().flatten() {
            if val(c, a) {
                x = !x;
            }
        }
        if !x {
            return None;
        }
    }
    let mut t2 = tog.clone();
    t2.insert(last, vec![]);
    Some((last, t2))
}
/// PK3_SW3B (default off): BK lead L-SW3B. On even11's E3C big rows (V 10..kkb-1, C kkb-1..10, C 1..0 at
/// the LOOK16 kept tiers) each masked cell's down half takes SW3R's shared form (ZB = s & m by AND compute / measured uncompute,
/// then CCX(ZB, t, c), CX(c, t), CCX(d, ZB, t)) instead of two 3-literal MCX: one CCX less per masked cell. ZB is the clean lane
/// the parent's own 3+ literal MCX already use in these rows (taken only when ZB_BUSY is clear). Python gate check:
/// false = the parent stream.
const PK3_SW3B: bool = true;
/// PK3_L3BS (default off): BK lead L3B-S. On the E3C big V rows (mask m = F) whose toggle cubes XOR to the
/// constant 1 as a Boolean function (truth table over the lanes they read; none of them is written by the row's forward half),
/// with no act cube reading F and no conversion inside the row: the last key's toggles go (key kept, empty) and the cell at that
/// key runs plain (wcut). For an actor (F = 0 at entry, the parent row's own requirement) the mask there is 1 anyway; a shot that
/// does not act (d = x0 = 0) cancels. Checked in Python. false = the parent stream.
const PK3_L3BS: bool = true;
/// PK3 counters: big rows with the shared down cell, big V rows cut by L3B-S
static PK3_CNT: [std::sync::atomic::AtomicUsize; 2] = [const { std::sync::atomic::AtomicUsize::new(0) }; 2];
const _: () = assert!(!(PK3_SW3B || PK3_L3BS) || (LOOK16 && E3C && E3C2 && ZB > 0));
/// PK3_L3BS: true when the toggle cubes XOR to 1 on every assignment of the lanes they read (a clashing cube is 0), the map has
/// at least one non-empty key below n, and no toggle lane is among `written`.
fn pk3_cum_one(tog: &BTreeMap<usize, Vec<Vec<Lit>>>, n: usize, written: &[u32]) -> bool {
    let last = match tog.keys().next_back() { Some(&l) => l, None => return false };
    if last >= n || tog[&last].is_empty() {
        return false;
    }
    let mut lanes: Vec<u32> = tog.values().flatten().flat_map(|c| c.iter().map(|x| x.0)).collect();
    lanes.sort();
    lanes.dedup();
    if lanes.len() > 20 || lanes.iter().any(|q0| written.contains(q0)) {
        return false;
    }
    let val = |c: &Vec<Lit>, a: u32| -> bool { c.iter().all(|&(q0, p)| ((a >> lanes.binary_search(&q0).unwrap()) & 1 == 1) == p) };
    for a in 0u32..(1u32 << lanes.len()) {
        let mut x = false;
        for c in tog.values().flatten() {
            if val(c, a) {
                x = !x;
            }
        }
        if !x {
            return false;
        }
    }
    true
}
const _: () = assert!(!(LOOK16 || LOOK16_ENC) || ((ECAP == 17 || ECAP == 18) && !W4HOST && TIER_LONG == 0 && CAD4 && CAD4B && EVJS && JSWAP && JSWAP_V && JSWAP_C && E3V && E3C && E3C2 && TOGV && PAGE_G && ZB > 0));
/// the tier slots that use the h1 hosted code
/// R765_PROF: slot class tag (the 0 mod 8 tiers split into LOOK16's kept tiers and the rest)
fn slot_class(t: i32) -> &'static str {
    if !(mid_even(t) || mid_odd(t)) { "ends" } else if t % 2 == 1 { "odd" } else if t % 4 == 2 { "even_t4_2" } else if t % 8 == 4 { "even_t8_4" }
    else if l16h(t) { "even_t8_0_kept" } else if l16_gone(t) { "even_t8_0_gone" } else { "even_t8_0_low" }
}
fn l16h(t: i32) -> bool { (LOOK16 || LOOK16_ENC) && t % 8 == 0 && (CUT_T..=CUT_S - 16).contains(&t) && (LOOK16_ENC || t % 16 == 0) }
/// LOOK16: the slots that lost big service (release sites)
fn l16_gone(t: i32) -> bool { LOOK16 && t.rem_euclid(16) == 8 && (CUT_T + 8..=CUT_S - 24).contains(&t) }
/// LOOK16: the kept tiers with early service
fn l16_early(t: i32) -> bool { LOOK16 && l16h(t) && t >= CUT_T + 16 }
/// LOOK16: the slots that can hold a frozen shot (T - 1 .. T - 8 of a kept tier T >= CUT_T + 16)
fn l16_frz(t: i32) -> bool { LOOK16 && (CUT_T + 8..=CUT_S - 17).contains(&t) && t.rem_euclid(16) >= 8 }
/// LOOK16: arrivals that take r = tn mod 16 (bit 3 on y8)
fn l16_arr(tn: i32) -> bool { LOOK16 && (CUT_T..=CUT_S - 9).contains(&tn) }
/// LOOK16 h1: cubes of a set of group keys (vals - off) against the others, on the lanes of the key (LSB first)
fn l16_keys(vals: &BTreeSet<i32>, others: &BTreeSet<i32>, lanes: &[u32], off: i32) -> Vec<Vec<Lit>> {
    let n = lanes.len();
    let (mut on, mut of) = (0u128, 0u128);
    for &v in vals { let k = v - off; assert!(k >= 0 && k < (1 << n), "LOOK16: key {v} out of range"); on |= 1u128 << k; }
    for &v in others { let k = v - off; assert!(k >= 0 && k < (1 << n), "LOOK16: key {v} out of range"); of |= 1u128 << k; }
    assert!(on & of == 0, "LOOK16: key groups collide");
    if on == 0 { return vec![]; }
    let vs: Vec<usize> = (0..n).collect();
    dtree(on, of, &vs, 0).iter().map(|c| c.iter().map(|&(v, b)| (lanes[v], b == 1)).collect()).collect()
}
/// LOOK16 h1: 7-bit point of a case (e, w, u, v) on [A0, A1, A2, B0, B1, B2, B3]; form 0 = (hi', r), 1 = (U3, r), 2 = (U3, V4)
fn l16_pt(form: u8, c: &(i32, i32, i32, i32)) -> usize {
    let (e, w, u, v) = *c;
    let r = w.rem_euclid(16);
    let (a, b) = match form { 0 => ((e >> 1) - 5, r), 1 => (u - 2, r), _ => (u - 2, v - 1) };
    assert!((0..8).contains(&a) && (0..16).contains(&b), "LOOK16: point out of range");
    (a | (b << 3)) as usize
}
/// LOOK16 h1: cubes over 7-bit points (on against off) on the 7 hosted lanes
fn l16_cubes(on: &[usize], off: &[usize], lanes7: &[u32]) -> Vec<Vec<Lit>> {
    let (mut a, mut b) = (0u128, 0u128);
    for &p in on { a |= 1u128 << p; }
    for &p in off { b |= 1u128 << p; }
    assert!(a & b == 0, "LOOK16: point sets collide");
    if a == 0 { return vec![]; }
    dtree(a, b, &[0, 1, 2, 3, 4, 5, 6], 3).iter().map(|c| c.iter().map(|&(v, bt)| (lanes7[v], bt == 1)).collect()).collect()
}
/// NK_F1_TRIE (trie shared_group): in sandwich_x's F = 1
/// block at quotient lengths 4 / 10 / 11 (CAD4-low, full ordinary, merged E3C) and source bits i <= 8, the whole source-bit
/// group becomes one shared group: root ZB = F & VB[i] as an AND marker with F and VB[i] then made conditionally clean
/// (CX from ZB), the lanes that only ever appear as negative cube literals conjugated once, and per digit term the
/// Khattar-Gidney scaffold of its cube (class literals, then the digit) with the common prefix of the sorted terms kept
/// between terms, an AND marker on X[0] (z2) around that term's add. The adds of one source bit commute (each writes VB
/// above bit i and reads none of the scaffold lanes); with a digit's cubes pairwise disjoint by an opposite literal the
/// sum of the per-cube adds is the parent's add on the OR. A call or group outside that contract emits the parent.
/// false = the stream of b7104bb.
const NK_F1_TRIE: bool = DS_P11; // DS_GATE11 (published: true)
/// NK_F0_BODY (predicate_add, combined F0 bracket rows): at the recipe's
/// F = 0 digits (qn 2: j 0-1, qn 4: j 1-3, qn 10: j 1-9, qn 11: j 7-10) each disjoint act cube's flag is computed once as a
/// clean conjunction (Khattar-Gidney scaffold on X[0], AND marker on ZB) and kept through that cube's subtract, then released,
/// instead of flag / subtract / flag on ZB. false = the parent's gates.
const NK_F0_BODY: bool = DS_P11; // DS_GATE11 (published: true)
/// NK_SELECT_LSB (select): at certified calls the bit-0 select swap becomes two CX (F = 1
/// implies VA[0] = 1, VB[0] = 0), mirrored by the post's rev(sel). false = the parent's gates.
const NK_SELECT_LSB: bool = DS_P11; // DS_GATE11 (published: true)
/// DB_F1_SIGN: in sandwich_x's F = 1 multiply, a term with s = i + j <=
/// DB_F1_SMAX adds (2b - 1) y_s, y_s = VA[1..] placed at bit s, by an UNcontrolled TTK subtract of y_s from VB[s..]
/// conjugated by a CX fan-out of its flag b (X0) onto VB[s..]: 2 (ln + 1) - 2 Toffoli instead of the controlled 3 ln - 2.
/// The missing + y_s of every signed term is one compensation VB += (VA >> 1) K at the end of mul (K = sum of 2^s over the
/// signed adds, cheapest signed-digit list of uncontrolled TTK adds). Every pending y_s sits at bits >= i + 1 when group i
/// reads VB_i. A j = 0 term (s = i) flips VB_i by VA_1 until the compensation: on the held path the bit flag's release and
/// the SW_Z2D direct flags run inside CX(VA_1 -> VB_i); in the NK trie (VB_i is a scaffold lane) it leaves the trie and runs
/// after the group with its own AND pair (F & VB_i -> ZB, ZB & q0 -> X0). false = the stream of e056d67.
const DB_F1_SIGN: bool = true;
/// DB_F1_SIGN: terms with s <= DB_F1_SMAX are signed (the signed form is cheaper for ln = 10 - s >= 3; 8 measured best)
const DB_F1_SMAX: usize = 8;
/// DB_F0_SIGN: in sandwich_x's F = 0 block at qn in {4, 10, 11} (digit 0 on the parent
/// path, no one0 terms), a digit j in 1..=DB_F0_JMAX with flag b adds (1 - 2b) SC at bit j - 1 by an UNcontrolled TTK add
/// conjugated by a CX fan-out of b (ZB) onto VB[j-1..] (2 (d - j + 1) - 2 T instead of the controlled 3 (d - j) - 2), and
/// digit 0's controlled subtract becomes a controlled add under NOT ZB (VB += (1 - c0) SC). One VB -= (K0 + 1) SC at the
/// block end (K0 = sum of 2^(j-1) over the signed adds) makes it the parent's VB -= c SC. F0 never reads VB.
/// false = the stream of e056d67.
const DB_F0_SIGN: bool = DS_P11; // DS_GATE11 (published: true)
const DB_F0_JMAX: usize = 9;
/// DB census: calls with a compensation, signed adds, j = 0 terms, compensation Toffoli
static DB_CNT: [std::sync::atomic::AtomicUsize; 4] = [const { std::sync::atomic::AtomicUsize::new(0) }; 4];
/// DB_F1_SIGN: fan(z2 -> VB[s..]); VB[s..] -= (VA >> 1) 2^s mod 2^d (uncontrolled TTK; s = 0: the (d-1)-bit form with its
/// carry-out on VB[d-1]); fan(z2 -> VB[s..]). Adds (2 z2 - 1) y_s. Writes VB[s..] only, reads VA[1..] and z2.
fn db_sign_body(z2: u32, va: &[u32], vb: &[u32], s: usize) -> GL {
    use self::window_prims::{self as wp, Cfg};
    let d = vb.len();
    assert!(va.len() == d && s + 2 <= d && !va.contains(&z2) && !vb.contains(&z2), "DB_F1_SIGN: body lanes");
    let (qa, qb) = (Machine::qs(va), Machine::qs(vb));
    let mut pb = self::prims_builder::B::new();
    let sub = Machine::pgl(wp::rec(&mut pb, |b| wp::undo(b, |b| {
        if s == 0 { wp::add(b, Cfg::PY, &qa[1..d], &qb[0..d - 1], Some(qb[d - 1])) } else { wp::add(b, Cfg::PY, &qa[1..1 + d - s], &qb[s..], None) }
    })));
    let fan: GL = vb[s..].iter().map(|&t| gc(z2, t)).collect();
    let mut g: GL = fan.clone();
    g.extend(sub);
    g.extend(fan);
    g
}
/// DB_F1_SIGN: VB += (VA >> 1) K mod 2^d by the cheapest signed-digit list of uncontrolled TTK adds (DP over bits with carry;
/// a digit at shift t costs 2 (d - t) - 2, at t = 0 2 (d - 1) - 1). Returns the gates and their Toffoli count.
fn db_comp(va: &[u32], vb: &[u32], k: u64) -> (GL, usize) {
    use self::window_prims::{self as wp, Cfg};
    let d = vb.len();
    let digits = db_digits(k, d, &|t: usize| -> usize { if t == 0 { 2 * (d - 1) - 1 } else { (2 * (d - t)).saturating_sub(2) } });
    let (qa, qb) = (Machine::qs(va), Machine::qs(vb));
    let mut pb = self::prims_builder::B::new();
    let mut g: GL = vec![];
    for &(t, dg) in &digits {
        let addf = |b: &mut self::prims_builder::B| {
            if t == 0 { wp::add(b, Cfg::PY, &qa[1..d], &qb[0..d - 1], Some(qb[d - 1])) } else { wp::add(b, Cfg::PY, &qa[1..1 + d - t], &qb[t..], None) }
        };
        g.extend(Machine::pgl(wp::rec(&mut pb, |b| if dg > 0 { addf(b) } else { wp::undo(b, |b| addf(b)) })));
    }
    let n = g.iter().filter(|x| x.2 != NONE).count();
    (g, n)
}
/// DB_F0_SIGN: VB -= SC K mod 2^d by the cheapest signed-digit list of uncontrolled TTK adds (SC[0..d-t] into VB[t..],
/// 2 (d - t) - 2 T each). Returns the gates and their Toffoli count.
fn db_comp_sc(sc: &[u32], vb: &[u32], k: u64) -> (GL, usize) {
    use self::window_prims::{self as wp, Cfg};
    let d = vb.len();
    let digits = db_digits(k, d, &|t: usize| -> usize { (2 * (d - t)).saturating_sub(2) });
    let (qc, qb) = (Machine::qs(sc), Machine::qs(vb));
    let mut pb = self::prims_builder::B::new();
    let mut g: GL = vec![];
    for &(t, dg) in &digits {
        let addf = |b: &mut self::prims_builder::B| wp::add(b, Cfg::PY, &qc[0..d - t], &qb[t..], None);
        g.extend(Machine::pgl(wp::rec(&mut pb, |b| if dg > 0 { wp::undo(b, |b| addf(b)) } else { addf(b) })));
    }
    let n = g.iter().filter(|x| x.2 != NONE).count();
    (g, n)
}
/// DB: the cheapest signed-digit list [(shift, +-1)] of K mod 2^d under a per-shift price (DP over bits with carry; the
/// carry out of bit d - 1 is dropped; ties keep the first of -1, 0, 1)
fn db_digits(k: u64, d: usize, cost: &dyn Fn(usize) -> usize) -> Vec<(usize, i8)> {
    let k = k & ((1u64 << d) - 1);
    // best[t][c]: cheapest digits for the bits t.. of K plus a carry c into bit t (the carry out of bit d - 1 is dropped)
    let mut best: Vec<[(usize, Vec<(usize, i8)>); 2]> = vec![[(0, vec![]), (0, vec![])]; d + 1];
    for t in (0..d).rev() {
        for c in 0..2usize {
            let bit = ((k >> t) & 1) as i64 + c as i64;
            let mut cur: Option<(usize, Vec<(usize, i8)>)> = None;
            for dg in [-1i64, 0, 1] {
                let v = bit - dg;
                if v % 2 != 0 { continue; }
                let nc = v / 2;
                if !(0..=1).contains(&nc) { continue; }
                let sub = &best[t + 1][nc as usize];
                let cst = sub.0 + if dg != 0 { cost(t) } else { 0 };
                if cur.as_ref().map_or(true, |x| cst < x.0) {
                    let mut ds = if dg != 0 { vec![(t, dg as i8)] } else { vec![] };
                    ds.extend_from_slice(&sub.1);
                    cur = Some((cst, ds));
                }
            }
            best[t][c] = cur.expect("DB: compensation DP");
        }
    }
    best[0][0].1.clone()
}
/// NK census: trie groups, kept (disjointness), kept (lane contract), F0 brackets, select CX pairs, F0 kept
static NK_CNT: [std::sync::atomic::AtomicUsize; 6] = [const { std::sync::atomic::AtomicUsize::new(0) }; 6];
/// NK_F0_BODY recipe: the F = 0 digits whose combined choice is the bracket (recipes.json, all five templates)
fn nk_f0_bracket_j(qn: usize, j: usize) -> bool {
    match qn { 2 => j <= 1, 4 => (1..=3).contains(&j), 10 => (1..=9).contains(&j), 11 => (7..=10).contains(&j), _ => false }
}
/// NK predicate_add: target ^= AND(lits) as a clean conjunction kept through body, then released; the scaffold's
/// root is an AND marker on helper. None = the lane contract fails (body touches a control or the helper, or writes target).
fn nk_pred_add(lits: &[Lit], target: u32, helper: u32, body: &GL) -> Option<GL> {
    use self::gl_loader::{ANDC, ANDU};
    let Some(norm) = nk_norm(lits) else { return Some(vec![]) };
    let cs: Vec<u32> = norm.iter().map(|x| x.0).collect();
    if cs.contains(&target) || cs.contains(&helper) || target == helper { return None; }
    for g in body {
        let (k, t, c) = g_parts(*g);
        if g.0 == MAC || t == helper || cs.contains(&t) || t == target || c.iter().take(k as usize).any(|x| cs.contains(x) || *x == helper) { return None; }
    }
    let neg: GL = norm.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
    let mut g: GL = neg.clone();
    let k = cs.len();
    if k < 2 {
        let o: GL = if k == 0 { vec![gx(target)] } else { vec![gc(cs[0], target)] };
        g.extend_from_slice(&o);
        g.extend_from_slice(body);
        g.extend(rev(&o));
    } else if k == 2 {
        g.push(G(cs[0], cs[1], target | ANDC));
        g.extend_from_slice(body);
        g.push(G(cs[0], cs[1], target | ANDU));
    } else {
        let mut left: GL = vec![G(cs[0], cs[1], helper | ANDC), gc(helper, cs[0]), gc(helper, cs[1])];
        let (walk, pair) = nk_scaffold(&cs, helper);
        left.extend(walk);
        g.extend_from_slice(&left);
        g.push(G(pair.0, pair.1, target | ANDC));
        g.extend_from_slice(body);
        g.push(G(pair.0, pair.1, target | ANDU));
        g.extend(rev_and(&left));
    }
    g.extend(rev(&neg));
    Some(g)
}
/// NK_F0_BODY: one predicate_add per cube (cubes pairwise disjoint by an opposite literal), each around its own body copy
fn nk_bracket_all(cubes: &[Vec<Lit>], target: u32, helper: u32, body: &GL) -> Option<GL> {
    let norms: Vec<Vec<Lit>> = cubes.iter().filter_map(|c| nk_norm(c)).collect();
    for a in 0..norms.len() {
        for b in a + 1..norms.len() {
            if !norms[a].iter().any(|&(q0, p)| norms[b].iter().any(|&(q1, p1)| q1 == q0 && p1 != p)) { NK_CNT[5].fetch_add(1, Ordering::Relaxed); return None; }
        }
    }
    let mut g: GL = vec![];
    for c in cubes {
        match nk_pred_add(c, target, helper, body) { Some(x) => g.extend(x), None => { NK_CNT[5].fetch_add(1, Ordering::Relaxed); return None; } }
    }
    NK_CNT[3].fetch_add(1, Ordering::Relaxed);
    Some(g)
}
/// NK: literal list normalized (first occurrence order, duplicates merged); None when contradictory
fn nk_norm(l: &[Lit]) -> Option<Vec<Lit>> {
    let mut out: Vec<Lit> = Vec::with_capacity(l.len());
    for &(q0, p) in l {
        match out.iter().find(|x| x.0 == q0) {
            Some(x) => { if x.1 != p { return None; } }
            None => out.push((q0, p)),
        }
    }
    Some(out)
}
/// NK scaffold: the Khattar-Gidney walk of cs beyond its root pair (cs[0], cs[1]), which the caller has already
/// ANDed onto zb and made conditionally clean; returns the walk and the final AND pair (onto the term's clean lane)
fn nk_scaffold(cs: &[u32], zb: u32) -> (GL, (u32, u32)) {
    let k = cs.len();
    let m = k / 2;
    assert!(k >= 3, "NK scaffold: fewer than three controls");
    let mut up: GL = vec![];
    let (mut guards, mut aa, mut bb) = (vec![zb], vec![cs[0]], vec![cs[1]]);
    for i in 1..m {
        let (a, b) = (cs[2 * i], cs[2 * i + 1]);
        let g = aa[i - 1];
        up.extend_from_slice(&[gt(a, b, g), gc(g, a), gc(g, b)]);
        guards.push(g);
        aa.push(a);
        bb.push(b);
    }
    let mut cur = guards[m - 1];
    if k % 2 == 1 {
        if m == 1 { return (up, (zb, cs[k - 1])); }
        up.push(gt(cur, cs[k - 1], bb[m - 2]));
        cur = bb[m - 2];
    }
    let mut i = m as isize - 2;
    while i >= 1 {
        let iu = i as usize;
        up.push(gt(cur, guards[iu], bb[iu - 1]));
        cur = bb[iu - 1];
        i -= 1;
    }
    (up, (cur, guards[0]))
}
/// NK: a total order on plain gates for sorting the term prefixes (any total order gives a DFS of the prefix trie)
fn nk_key(g: &G) -> (u8, u32, u32, u32) {
    if g.2 != NONE { (1, g.0, g.1, g.2) } else if g.1 != NONE { (0, g.0, g.1, 0) } else { (2, g.0, 0, 0) }
}
fn nk_geq(a: &G, b: &G) -> bool { a.0 == b.0 && a.1 == b.1 && a.2 == b.2 }
/// NK_F1_TRIE: one F = 1 source-bit group. terms: (digit index j, digit lane, cube); bodies[j]: the add controlled on z2.
/// None = keep the parent group (counted in NK_CNT).
fn nk_trie_group(f: u32, vbi: u32, z: u32, z2: u32, digits: &[(usize, u32, Vec<Vec<Lit>>)], bodies: &BTreeMap<usize, GL>) -> Option<GL> {
    use self::gl_loader::{ANDC, ANDU};
    let (mut pos, mut neg): (BTreeSet<u32>, BTreeSet<u32>) = (BTreeSet::new(), BTreeSet::new());
    pos.insert(f);
    pos.insert(vbi);
    let mut terms: Vec<(usize, u32, Vec<Lit>)> = vec![];
    for (j, dq, cubes) in digits {
        pos.insert(*dq);
        let norms: Vec<Vec<Lit>> = cubes.iter().filter_map(|ex| nk_norm(&[&[(f, true), (vbi, true), (*dq, true)][..], &ex[..]].concat())).collect();
        for a in 0..norms.len() {
            for b in a + 1..norms.len() {
                if !norms[a].iter().any(|&(q0, p)| norms[b].iter().any(|&(q1, p1)| q1 == q0 && p1 != p)) {
                    NK_CNT[1].fetch_add(1, Ordering::Relaxed);
                    return None;
                }
            }
        }
        for ex in cubes {
            for &(q0, p) in ex { if p { pos.insert(q0); } else { neg.insert(q0); } }
            terms.push((*j, *dq, ex.clone()));
        }
    }
    let negonly: BTreeSet<u32> = neg.difference(&pos).copied().collect();
    // every lane the scaffold may write (conditionally or by conjugation): a body may not touch one, nor write z2
    let mut scaf: BTreeSet<u32> = pos.union(&neg).copied().collect();
    scaf.insert(z);
    if scaf.contains(&z2) { NK_CNT[2].fetch_add(1, Ordering::Relaxed); return None; }
    for body in bodies.values() {
        for g in body {
            let (k, t, cs) = g_parts(*g);
            if t == z2 || scaf.contains(&t) || cs.iter().take(k as usize).any(|c| scaf.contains(c)) || g.0 == MAC {
                NK_CNT[2].fetch_add(1, Ordering::Relaxed);
                return None;
            }
        }
    }
    let conj: GL = negonly.iter().map(|&q0| gx(q0)).collect();
    let mut packets: Vec<(GL, (u32, u32), usize)> = vec![];
    for (j, dq, ex) in &terms {
        let lits: Vec<Lit> = [&[(f, true), (vbi, true)][..], &ex[..], &[(*dq, true)][..]].concat();
        let Some(norm) = nk_norm(&lits) else { continue };
        let cs: Vec<u32> = norm.iter().map(|x| x.0).collect();
        if cs.len() < 3 || cs[0] != f || cs[1] != vbi || cs.contains(&z) || cs.contains(&z2) {
            NK_CNT[2].fetch_add(1, Ordering::Relaxed);
            return None;
        }
        let mut prefix: GL = norm.iter().filter(|x| !x.1 && !negonly.contains(&x.0)).map(|x| gx(x.0)).collect();
        let (walk, pair) = nk_scaffold(&cs, z);
        prefix.extend(walk);
        packets.push((prefix, pair, *j));
    }
    packets.sort_by(|a, b| a.0.iter().map(nk_key).cmp(b.0.iter().map(nk_key)));
    let root: GL = vec![G(f, vbi, z | ANDC), gc(z, f), gc(z, vbi)];
    let mut g: GL = conj.clone();
    g.extend_from_slice(&root);
    let mut active: GL = vec![];
    for (prefix, pair, j) in &packets {
        let mut common = 0;
        while common < active.len().min(prefix.len()) && nk_geq(&active[common], &prefix[common]) { common += 1; }
        g.extend(rev(&active[common..]));
        g.extend_from_slice(&prefix[common..]);
        g.push(G(pair.0, pair.1, z2 | ANDC));
        g.extend_from_slice(&bodies[j]);
        g.push(G(pair.0, pair.1, z2 | ANDU));
        active = prefix.clone();
    }
    g.extend(rev(&active));
    g.extend(rev_and(&root));
    g.extend(rev(&conj));
    NK_CNT[0].fetch_add(1, Ordering::Relaxed);
    Some(g)
}
fn togv_on() -> bool { TOGV && std::env::var("R7A_NO_TOGV").is_err() }
fn togc_on() -> bool { TOGC && std::env::var("R7A_NO_TOGC").is_err() }
/// toggle map of an inline cube map (keys 0..n contiguous): tog[i] = cubes of il[i] XOR il[i - 1] (il[-1] = empty)
fn tog_of(il: &BTreeMap<usize, Vec<Vec<Lit>>>) -> BTreeMap<usize, Vec<Vec<Lit>>> {
    let norm = |c: &Vec<Lit>| -> Vec<Lit> { let mut v = c.clone(); v.sort(); v };
    let mut out: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
    let mut prev: Vec<Vec<Lit>> = vec![];
    let n = il.keys().next_back().map(|k| k + 1).unwrap_or(0);
    for i in 0..n {
        let cur: Vec<Vec<Lit>> = il[&i].iter().map(norm).collect();
        let mut cnt: BTreeMap<Vec<Lit>, usize> = BTreeMap::new();
        for c in prev.iter().chain(cur.iter()) { *cnt.entry(c.clone()).or_insert(0) += 1; }
        let d: Vec<Vec<Lit>> = cnt.into_iter().filter(|(_, k)| k % 2 == 1).map(|(c, _)| c).collect();
        if !d.is_empty() { out.insert(i, d); }
        prev = cur;
    }
    out
}
const _: () = assert!(!CAD4 || (!L1 && CONV && PAGE_G && PAGE_N));
/// CAD4: arrivals that take the W1 wait; the slots that run only e <= 3; the slots where W1 waiters act
fn cad4_arr(tn: i32) -> bool { CAD4 && (CUT_T + 2..=CUT_S - 5).contains(&tn) && tn.rem_euclid(4) >= 2 }
fn cad4_low(t: i32) -> bool { CAD4 && (CUT_T + 2..=CUT_S - 6).contains(&t) && t.rem_euclid(4) == 2 }
fn cad4_p4(t: i32) -> bool { CAD4 && (CUT_T..=CUT_S - 8).contains(&t) && t.rem_euclid(4) == 0 }
/// CAD4: the slots (odd or even) at which a W1 waiter can sit at the top
fn cad4_band(t: i32) -> bool { CAD4 && (CUT_T..=CUT_S - 5).contains(&t) }
/// D11 converter: true = the frame runs at page width PAGE_D (set 11) while page_in / page_out, start765,
/// phys765 and the tail stay at PAGE_DI = 16; a converter after page_in(CUT_S - 1) lifts bits 11..15 of the implicit word
/// (K2-LIFT), routes the explicit tops by B's parity and reopens a 10-lane hole per ring at the shot's junction; its inverse
/// runs before page_out(CUT_T - 1). false = every width is PAGE_D (the stream of ae715bcf).
const CONV: bool = true;
/// module-interface page width (= PAGE_D when CONV is off)
const PAGE_DI: usize = if CONV { 16 } else { PAGE_D };
/// ring width at the interfaces after page_in's narrowing
const WHI: usize = W - 2 * PAGE_DI;
/// insertion index of the 10 converter lanes in the narrowed (WHI) ring lists, (ring X, ring Y), at the start and tail cuts
/// (checked in a gate-level model: exact at these values; insertion at the top fails)
const CONV_K_S: (usize, usize) = (27, 25);
const CONV_K_T: (usize, usize) = (203, 187);
/// Catalyst-swap hop: the K2 half's in-place p/B in the frame sandwich by the catalyst swap
/// (D - 1 passenger lanes read as an odd g: X <- X g, G <- G / X, X <- X G, swap) instead of invp. HOPA: dirt restored
/// inside the hop (drop-in). HOPP (implies the hop): the third multiply is left to the post (the catalyst lanes hold B g
/// between pre and post; post = the reversed gates). Both false = the K2 half of ae715bcf.
const HOPA: bool = false;
const HOPP: bool = true;
static HOP_SEEN: AtomicBool = AtomicBool::new(false);
/// SW1. false = the parent stream byte for byte.
/// SW1_GROUP_K2: the K2 half (pre) of every sandwich is the typed packet K2_ak23_group_opt_fwd.glz (group reciprocal in
/// multiplicative coordinates on K2C's helpers z = ZB and z2 = X[0]; 435 executed T one way), relabelled onto the frame; the
/// native hop still runs (its builder state), its gates are dropped; the post stays rev_and(k2).
/// SW1_K2_AND_ROLES: the native K2C half keeps its AND compute / measured-uncompute roles (pgl_and without the SW_T2C guard).
/// SW1_CONV_HOP: conv_gates' lift (K2 half, five controlled copies, inverse K2 half) is the packet converter_parked_lift_fwd.glz.
const SW1_GROUP_K2: bool = DS_P11; // DS_GATE11 (published: true)
const SW1_K2_AND_ROLES: bool = false;
const SW1_CONV_HOP: bool = DS_P11; // DS_GATE11 (published: true)
/// ECAP 17 allowed (the packet is a K2 hop, independent of the cap; the in-build SW1CHK adapter controls must stay diff 0).
const _: () = assert!(!SW1_GROUP_K2 || (SW_K2C && PAGE_D == 11 && (ECAP == 18 || ECAP == 17) && HOPP && !HOPA));
const _: () = assert!(!(SW1_GROUP_K2 && SW1_K2_AND_ROLES), "SW1: group packet and roles transport are alternatives");
const _: () = assert!(!SW1_CONV_HOP || (CONV && PAGE_DI == 16 && PAGE_D == 11));
/// AKK2: the public 8396ec91 K2 kernels ported onto the native K2 half (hop2::hop). Any switch on
/// replaces the SW1 group packet with the native hop, emitted through pgl_roles (AND compute / measured uncompute kept on
/// K2C's helpers z = ZB, z2 = X[0]); post = rev_and(k2) as before. All false = the parent stream byte for byte.
/// AKK2_H1: in-place Hensel p / VB (hop2::invp11, 47 T; replaces the group reciprocal, 150 T, and the parked catalyst).
/// AKK2_X1: idiv by the sign trick with the x1 conjugation (window_prims::idiv_sgn2, 91 T; parent idiv 128).
/// AKK2_S2: hop_c's multiply-accumulate by the sign trick (hop2::mac_sgn, 120 T; parent undo(mac) 157).
/// Per K2 direction: 435 (SW1) -> 332 (H1) -> 295 (H1 + S2) -> 258 (H1 + S2 + X1). X1 / S2 without H1 fall back to the
/// parked catalyst inverse (cat_invp), which is dearer than the group packet: they need H1.
const AKK2_H1: bool = true;
const AKK2_X1: bool = true;
const AKK2_S2: bool = true;
const AKK2_K2: bool = AKK2_H1 || AKK2_X1 || AKK2_S2;
const _: () = assert!(!(AKK2_X1 || AKK2_S2) || AKK2_H1, "AKK2: X1 / S2 need H1 (else the native hop uses cat_invp)");
const _: () = assert!(!AKK2_K2 || (SW_K2C && (PAGE_D == 11 || DS_K2_ALLW) && HOPP && !HOPA), "AKK2: K2C helpers and the HOPP hop are the ABI");
static SW1_K2_GROUP_FWD: &[u8] = include_bytes!("gl_data/sw1/K2_ak23_group_opt_fwd.glz");
static SW1_K2_GROUP_INV: &[u8] = include_bytes!("gl_data/sw1/K2_ak23_group_opt_inv.glz");
static SW1_K2_PARENT_LIT: &[u8] = include_bytes!("gl_data/sw1/K2_ak23_parent_literal_fwd.glz");
static SW1_K2_PARENT_ROLES: &[u8] = include_bytes!("gl_data/sw1/K2_ak23_parent_roles_fwd.glz");
static SW1_CONV_PARKED: &[u8] = include_bytes!("gl_data/sw1/converter_parked_lift_fwd.glz");
static SW1_CONV_PARENT: &[u8] = include_bytes!("gl_data/sw1/converter_parent_lift_fwd.glz");
static SW1_SEEN: AtomicBool = AtomicBool::new(false);
/// SW1 adapter control counters over every sandwich: literal eq / diff, roles eq / diff, inverse eq / diff, group packets emitted
static SW1_CHK: [std::sync::atomic::AtomicUsize; 7] = [const { std::sync::atomic::AtomicUsize::new(0) }; 7];
/// SW2_LADDER_SEM: certified table emissions
static SW2_CNT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
/// SW1: decode a packet (sha3 pinned), relabel through m (flags kept on targets)
fn sw1_packet(z: &[u8], sha: &str, m: &dyn Fn(u32) -> u32) -> GL {
    assert_eq!(gl_loader::sha3_hex(z), sha, "SW1: packet sha3");
    let f = gl_loader::decode(z);
    assert_eq!(f.n_lanes, 765, "SW1: packet ABI");
    f.gates.iter().map(|g| gl_loader::relabel(g, m)).collect()
}
fn sw1_same(a: &[G], b: &[G]) -> String {
    if a.len() != b.len() { return format!("DIFFERENT length {} vs {}", a.len(), b.len()); }
    match a.iter().zip(b.iter()).position(|(x, y)| (x.0, x.1, x.2) != (y.0, y.1, y.2)) {
        None => format!("EQUAL ({} gates)", a.len()),
        Some(i) => format!("DIFFERENT at gate {i} of {}: ({}, {}, {}) vs ({}, {}, {})", a.len(), a[i].0, a[i].1, a[i].2, b[i].0, b[i].1, b[i].2),
    }
}
/// P5 cut slots (multiples of 8): the start module covers the slots t >= CUT_S, the tail module the slots t < CUT_T;
/// the paged frame runs slots CUT_S - 1 .. CUT_T (page_in at the boundary below slot CUT_S, page_out below CUT_T).
const CUT_S: i32 = 432;
const CUT_T: i32 = 80;
const PAGE_CUTS: [i32; 2] = [CUT_S - 1, CUT_T - 1];
/// the even / odd frame slots between the cuts (paged with PAGE_G)
fn mid_even(t: i32) -> bool { (CUT_T..=CUT_S - 2).contains(&t) }
fn mid_odd(t: i32) -> bool { (CUT_T + 1..=CUT_S - 1).contains(&t) }
/// P1 step (b), test mode: the V rows of the low classes (e = 2..9) at the even slots 446..64 run through the page
/// (KT5 sliding window), with a per-slot local gather of the acting shots' A and B low words (the rest stays native).
const PAGE_V: bool = false;
/// P1 step (b2), test mode (implies PAGE_V's V rows): the four low words of the acting low-class shots are gathered per
/// slot, the implicit cofactor word is erased, and the C rows run through the page behind the K2 sandwich.
const PAGE_C: bool = false;
/// P1 global page: page_in at the boundary below slot 448, page_out (its inverse) at the boundary below slot 64; in
/// between every slot is page-aware: low classes and e = 0 through the page, e = 1 rows and the big classes still
/// native behind a per-slot controlled unpage / repage (counter 6), a page swap and format switch at every act.
const PAGE_G: bool = true;
/// P5 step 1: with the global page, the rings are narrowed to WH = 257 - 2D wires between the cuts (page_in also
/// closes each ring's 2D-lane hole; the top 2D lanes of each ring are freed). Needs PAGE_G.
const PAGE_N: bool = true;
/// P5 lever L-D (op-lever's lever 1, team40/flags/LEVERS.md): the class flags of the six even-slot page sites (V-win-in,
/// V rows 0..8, V-win-out, cw, C rows 9..1, C-win-out) as thermometer-ladder schedules on d, ZB (and F in the V phase)
/// instead of one fresh AND per class and use (fl_cls / fl_cit). Needs PAGE_G; used where the classes 2..9 all act.
const LADDER: bool = true;
/// SW2_POST_AND: the ordinary odd11 / even11 post_page keeps its AND markers
/// (measured uncompute on ZB); the big-phase call keeps the parent conversion. false = the parent stream byte for byte.
const SW2_POST_AND: bool = true;
/// AR: preserve existing post arithmetic roles at the 44 big-phase calls.
const AR_POST_AND: bool = true;
const _: () = assert!(!AR_POST_AND || (POST_ZB && ZB > 0 && HMR_AND));
const _: () = assert!(!SW2_POST_AND || (POST_ZB && ZB > 0 && HMR_AND));
/// P5 frame lever 1 (op-build2): the format switch of post_page (controlled D-bit multiply / divide) with ZB as its one
/// clean lane (ZB is 0 at every post: the sandwich's post has run): each doubly-controlled add is AND + 1 adder instead of
/// the dirty complement trick's 2 adders. AND pairs are emitted as CCX.
const POST_ZB: bool = true;
/// P5 765 assembly (op-p5b, P5_CHECKLIST s9 A2): with a Start splice that ends in the PAGED form at the boundary below CUT_S (M2e at 431),
/// page_in(CUT_S - 1) emits no gates (its software state, the PAGE_N narrowing and W4, still runs).
const ASM_START_PAGED: bool = true;
/// P5 765 assembly (A3): with a Tail splice, page_out(CUT_T - 1) and the re-widening belong to the tail region (the list unpacks the page
/// itself, M3a): the region's gate index is taken before the cut; its labels (y_tail) after it, as before.
const ASM_TAIL_UNPACK: bool = false;
/// op-p5b diagnostic (count builds only): print the frame's labels at the cuts and every label used by gates strictly between
/// page_in(CUT_S - 1) and page_out(CUT_T - 1) (lines ASMDUMP), to build the 765 relabel (A6). No gate changes.
const ASM_DUMP: bool = false;
/// start765 mode (op-p5b): true = after the list, MOVE its output by CX swaps (no Toffoli) onto the native frame's own labels at 1431,
/// so the frame from 431 on is the native one (start-alone fault split, P5_CHECKLIST s8); false = re-point the frame's labels at the
/// list's (the 765 form; needs the 765 tail so that F's output lands on the labels 0..511 + y0, y1).
const START765_SWAP: bool = false;
/// 765 assembly test mode (op-p5b): with start765 in re-point mode and the NATIVE tail, move F's end data by CX swaps onto the labels of
/// the 765 end form (ring Y on phys Y773 = [512, 513, 0..254] through the label table at 79, PAR on the re-pointed par), so the start
/// re-point + label compaction are graded before the real tail list exists (width > 765: the native tail uses T2 and the ring tops).
const TAIL_SWAP765: bool = false;
/// 765 assembly: renumber the labels >= 512 used by F densely (fc.next = 512 + used), so the emitter allocates only used lanes.
const ASM765_COMPACT: bool = true;
/// TAIL765 = 3 (op-p5b): the registered tail list gl_data/tail765.glz + gl_data/tail765.lay (include_bytes, sha3 checked).
const TAIL765_SHA3: &str = "718d206b1292ce8693f22e17c94bcef182a57a264da6203ff53291f48ed40890";
/// P5 frame lever 2 (op-build2, team40/p1/LEVER2.md): the big-class slide flags (after V row k by u, before C row k by
/// v = f - t/2) as a demux walk on the 4 hosted bits (V: prefix lanes F and ZB, C: ZB with d as aux) instead of one fresh
/// decision-tree AND per group; groups with inactive cases of the same u / v get w cubes on the leaf.
const SLIDE_LAD: bool = true;
/// LEVER2 C side: its prefix A (cl & 2 bits on ZB) by cc_core with d as the aux lane (off: Barenco on ZB)
const SLIDE_LAD_CA: bool = true;
/// P5 765 tail splice (op-build2; contract team40/p5b/SPLICE765.md): the region page_out(CUT_T - 1) + ticks CUT_T - 1 .. 3 in
/// MAP765_v2 PHYSICAL lanes (phys765: the frame state at label CUT_T - 1). 0 off; 1 = dump the native region (macro pass off)
/// to TAIL765_DUMP + its end ring layout (.lay); 2 = splice the GLV1 list TAIL765_LIST in its place, then rings X / Y
/// relabelled from TAIL765_LIST.lay ("Y <phys...>", "X <phys...>"; a real tail765 list: Y = Y773 [512, 513, 0..254]).
const TAIL765: u8 = 3;
const TAIL765_DUMP: &str = "/tmp/q765-op-build2/tail765_rt.glz";
const TAIL765_LIST: &str = "/tmp/q765-op-build2/tail765_rt.glz";
static TAIL765_DATA: &[u8] = gl_loader::NO_DATA;
/// TAIL765_CL (ob-tail, NOTES/v8/pivot/clean/tailc.py): tail765 with M3e = the clean-lane narrow machine (s765c, per-slot pool
/// <= 110 fold-placed clean lanes, Gidney low-carry compares + clean-lane controlled adds; AND markers op 3 / 4): 1,322,089 T per
/// pass vs 1,562,503 (list cl110b). false = tail765.
const TAIL765_CL: bool = true;
/// fb-r7d (NOTES/v9/r7_d/NF_DESIGN.md, tailnf.py): list tail765_nf102 = tail765 with M3e = the NARROW NATIVE F module (public 777 F
/// generator at a 103-lane ring on the dual walk, window modulus 2^102 - 1, decode + extra-step + in-place window erase end):
/// 1,076,284 T per pass vs 1,562,503.
// HO: exact arithmetic hand-over block. false retains the parent file.
const TAIL765_HO: bool = true;
/// TAIL765_HO_FINAL: HO's final tail (three exact hand-over rewrites, sha3
/// d1a996d6, static -77,384 over four vs the parent tail) replaces TAIL765_HO's file. false = the TAIL765_HO choice above.
const TAIL765_HO_FINAL: bool = true;
const TAIL765C_SHA3: &str = if AK_ENDS == 1 {
    "f653ad5755c9653abf9fc33747204517b04b984a16fd88dfd604a8fa76b0f335"
} else if AK_ENDS == 2 {
    "219eea4d6daf2f15acc5908917addd0e4fcebd0d164babf61655e7fe85a5a11a"
} else if TAIL765_HO_FINAL {
    "d1a996d63635185cffef59a1c1f4156b6e5609d0db785b921fb1d90ac704cfb4"
} else if TAIL765_HO {
    "58a6ed344ea27e540753cdeff4ede49744ccb5a0f3cfe359d7283d2e46b5c725"
} else {
    "f3fc6f70eebe51a8b146bf8e8328f7961e437c97df5382094fcba558a0cc32e5"
};
static TAIL765C_DATA: &[u8] = if AK_ENDS == 1 {
    gl_loader::NO_DATA
} else if AK_ENDS == 2 {
    include_bytes!("gl_data/tail765c_t2.glz")
} else if TAIL765_HO_FINAL {
    gl_loader::NO_DATA
} else if TAIL765_HO {
    gl_loader::NO_DATA
} else {
    gl_loader::NO_DATA
};
/// AKEND: the public 8396ec91 end lists and its four forward measured-erase (MBU) blocks.
/// AK_ENDS: 0 = our lists (SW4_MAJ start, TAIL765_HO_FINAL tail: the parent stream), 1 = his X2 lists (NF-CLEAN v1m,
/// start765_d4_v1m.glz / tail765c_v1m.glz), 2 = his X2 + T2 lists (start765_d4_t2.glz / tail765c_t2.glz). All map the same
/// F input to the same start-cut state and the same tail-cut state to the canonical F output (M).
pub(super) const AK_ENDS: u8 = 2;
/// PR2_PROD: the M2E product stage replays PR2's re-recorded sh1 / sh2 (NEGD table): every 1/bit
/// overflow fold of P1, the square and P4 merged with the next doubling fold into one window add of h(c-1) + (2s-1)2kc after
/// the frame undo (605 merges), and the square's 257-step halving pre-scale run four steps per fold (64 groups). Same NBITS,
/// points, live sets and walk seams; sh0 / sh3 / sh4 unchanged. Static CCX -46,639 per shot (M). false = m2e_data_n byte for byte.
const PR2_PROD: bool = true;
/// EN2_LAD (default off): with AK_ENDS = 2, the start list start765_d4_t2_en2p.glz = start765_d4_t2 with
/// 66 dirty Barenco multi-controlled X ladders of the start hand-over (4k - 8 CCX each) rewritten as the tree's cc_core on one
/// clean lane (2k - 3 CCX, inner AND measured: ANDC / ANDU markers). Every clean lane is PROVEN zero structurally (F input
/// interface lanes 513..764, AND measured-uncompute targets, restoring identical-gate pairs); all sites are
/// after M2c, so AK_START's M2c block is unchanged. -2,160 T per traversal (list, M). false = start765_d4_t2 byte for byte.
const EN2_LAD: bool = true;
/// AKEND MBU switches, one per block, default off; exact on valid states for every AK_ENDS (M):
/// AK_M2C start M2c (pure erase, 53 lanes, no FIX); AK_T1 tail core (HMR 189 lanes, then caf_fix 20,915 T on the freed
/// lanes); AK_GAD tail gadget backward half (HMR 144 lanes, then 78 CX; needs AK_M3E: it leaves B un-created on
/// 620..658, which M3E then neither measures nor Zs); AK_M3E (m3e_fix_t2 15,756 T, then HMR of TB / TA 567..660).
const AK_M2C: bool = true;
const AK_T1: bool = true;
const AK_GAD: bool = true;
const AK_M3E: bool = true;
/// AK_MBU_NEG (negative control only): the inverse walks do not pay the MBU blocks' phase debt (must fail)
const AK_MBU_NEG: bool = false;
/// (tail list length, T1, gadget, M3E) per AK_ENDS: (a, b, list CCX incl. both AND marker roles) in tail-list coordinates
const AK_TAIL: (usize, (usize, usize, usize), (usize, usize, usize), (usize, usize, usize)) = match AK_ENDS {
    0 => (2_278_123, (29_124, 512_961, 204_744), (737_132, 959_841, 77_564), (1_107_316, 2_274_129, 383_100)),
    1 => (2_170_261, (29_124, 564_477, 224_090), (788_648, 1_011_357, 77_564), (1_158_832, 2_166_267, 376_956)),
    _ => (2_237_372, (29_124, 564_477, 224_090), (816_440, 1_067_254, 71_675), (1_225_943, 2_233_378, 376_956)),
};
/// (start list length, M2c) per AK_ENDS, start-list coordinates
const AK_START: (usize, (usize, usize, usize)) = match AK_ENDS {
    0 => (2_386_040, (1_404_818, 1_875_129, 163_672)),
    1 => (2_175_606, (1_194_384, 1_664_695, 163_672)),
    _ => (if EN2_LAD { 2_234_565 } else { 2_234_303 }, (1_196_769, 1_723_392, 151_340)),
};
static AK_CAF_FIX: &[u8] = include_bytes!("gl_data/caf_fix.glz");
static AK_GAD_FIX: &[u8] = include_bytes!("gl_data/gfix_tail.glz");
static AK_M3E_FIX: &[u8] = include_bytes!("gl_data/m3e_fix_t2.glz");
static AK_M2C_FIX: &[u8] = include_bytes!("gl_data/m2c_fix.glz");
static AK_CAF_MEAS: &str = include_str!("gl_data/caf_fix_measure.txt");
static AK_GAD_MEAS: &str = include_str!("gl_data/gfix_tail_measure.txt");
static AK_M2C_MEAS: &str = include_str!("gl_data/m2c_fix_measure.txt");
/// PK HX: measured erase of the start hand-over's length-counter recompute. The block is
/// R1 + gap + R2 of the start list, where R1 == R2 gate for gate (18,460 gates each): the 6-bit counter 757..762 is XORed with a
/// priority function of the word on lanes 0..48 (wide dirty-ladder tests into flag 763, every one gated by 764; R1 acts on
/// 764 = 1 shots, R2 on the others). The block is gate-identical in the SW4, v1m and T2 start lists. Forward walks: FIX =
/// R1's first ladder (763 ^= t0) + R1's net X flips + the gap (unchanged) + the same ladder and flips again, then X-measure
/// 757..762; the block is skipped. Inverse walks: unchanged; Z_if on 757..762 right after the reversed block (the counter holds
/// its pre-R1 value there). Needs the AKEND MBU machinery; independent of AK_M2C. -25,056 CCX per forward walk (M, list level).
/// Checked in Python on 720,896 real shots + edge inputs. Default off.
const PK_HX: bool = true;
/// (block start, block end, block CCX) in start-list coordinates per AK_ENDS
const PK_HX_BLK: (usize, usize, usize) = match AK_ENDS { 0 => (2_334_656, 2_382_574, 29_606), 1 => (2_124_222, 2_172_140, 29_606), _ => if EN2_LAD { (2_183_181, 2_231_099, 29_606) } else { (2_182_919, 2_230_837, 29_606) } };
// with EN2_LAD the en2p start list is 262 gates longer before HX (66 ladder sites in [1,723,410, 1,732,367]),
// so the HX block moves +262; its 29,606 CCX are unchanged (asserted by mbu_register).
static PK_HX_FIX: &[u8] = include_bytes!("gl_data/hx_fix.glz");
static PK_HX_MEAS: &str = include_str!("gl_data/hx_fix_measure.txt");
fn ak_fix_pins() {
    for (n, d, s) in [("caf_fix", AK_CAF_FIX, "3f7335ac5ee22249842946a023366bf9502dc83135fb4ca1a52921707cc49765"),
                      ("gfix_tail", AK_GAD_FIX, "6a2fb79267df348d8126517904b71950a2a6bb0a823d57117e52af3a3db255e6"),
                      ("m3e_fix_t2", AK_M3E_FIX, "de531552d14511e45e49d9ff462963d9c90393a606857b17e075fe3d66bacece"),
                      ("m2c_fix", AK_M2C_FIX, "cf2042255891ebb817465bf8931f852d3d35a10b5dd6a7f3ed6ab8387346eb82")] {
        assert_eq!(gl_loader::sha3_hex(d), s, "AKEND: {n} sha3");
    }
}
/// p10 MBU machinery, verbatim from the public 8396ec91 mod.rs (MbuPend, MbuBlk, mbu_lanes, mbu_register)
struct MbuPend {
    name: &'static str,
    /// index in mc.b.gates of the block's first gate at the splice (MAC expansion may shift it; the search is global)
    base: usize,
    /// the block's gates as spliced
    pat: Vec<G>,
    ccx: usize,
    meas: Vec<u32>,
    fix: Vec<G>,
    fix_first: bool,
    skip: Vec<u32>,
    /// M3E: PAR's label, for the cross-check against the exit-pattern anchor
    par: Option<u32>,
}
static MBU_PEND: std::sync::Mutex<Vec<MbuPend>> = std::sync::Mutex::new(Vec::new());
/// a located block in fc.gates: forward = FIX / HMR(meas) in `fix_first` order, gates [b0, b1) skipped; inverse = Z_if(meas) after gate b0
struct MbuBlk {
    name: &'static str,
    b0: usize,
    b1: usize,
    meas: Vec<u32>,
    fix: Vec<G>,
    fix_first: bool,
    /// lanes the blocks after this one must neither measure nor Z
    skip: Vec<u32>,
}
fn mbu_lanes(txt: &str) -> Vec<u32> { txt.split_whitespace().filter_map(|w| w.parse().ok()).collect() }
/// register block [a, b) of `list` (the list as just spliced at mc.b.gates[base..], lane map `rl`: list lane -> label)
#[allow(clippy::too_many_arguments)]
fn mbu_register(name: &'static str, list: &[G], base: usize, (a, b, ccx_note): (usize, usize, usize), meas: Vec<u32>, n_meas: usize,
                fix: &[u8], fix_first: bool, skip: Vec<u32>, par: Option<u32>, rl: &dyn Fn(u32) -> u32) {
    let m = |q: u32| if q == NONE { NONE } else { rl(q) };
    let pat = list[a..b].to_vec();
    let ccx = pat.iter().filter(|g| g.2 != NONE).count();
    let fx = gl_loader::decode(fix);
    eprintln!("p10 MBU {name}: list [{a}, {b}) at mc.b {}: {} gates, {ccx} CCX (notes {ccx_note}), {} measured lanes, FIX {} gates {} CCX",
              base + a, b - a, meas.len(), fx.gates.len(), fx.n_ccx);
    assert_eq!(ccx, ccx_note, "p10 MBU {name}: block CCX differs from the notes");
    assert_eq!(meas.len(), n_meas, "p10 MBU {name}: measured lane count");
    // aris-eng T1 (review condition d): keep the ANDC / ANDU flags of FIX gates (relabel keeps them); MarkerWalk::emit_fix dispatches
    let nand = fx.gates.iter().filter(|g| g.2 != NONE && gl_loader::flag_of(g.2) != 0).count();
    eprintln!("p10 MBU {name}: FIX AND-marker gates {nand} (emitted at 0 T / measured by emit_fix)");
    let fix: Vec<G> = fx.gates.iter().map(|g| gl_loader::relabel(g, &m)).collect();
    MBU_PEND.lock().unwrap().push(MbuPend { name, base: base + a, pat, ccx, meas: meas.into_iter().map(m).collect(), fix, fix_first,
                                             skip: skip.into_iter().map(m).collect(), par: par.map(m) });
}
static TAIL765_LAY: &str = include_str!("gl_data/tail765.lay");
#[derive(Clone, Copy)]
enum N { D, ZB, F, Yt, H1, Y(u8), Xt(u8) }
#[derive(Clone, Copy)]
enum LOp { X(N), Cx(N, N), Ccx(N, N, N), U(usize, N) }
#[path = "ladder_data.rs"]
mod ladder_data;
/// SW2_LADDER_SEM (ladder certificates): each thermometer-ladder table keeps only
/// its certified LOp indices and tags the certified CCX as AND compute (ANDC) / measured release (ANDU); the uses expand through
/// the parent's uop unchanged. SW2_LAD_SITES empty = all 22 tables. false = the parent stream byte for byte.
const SW2_LADDER_SEM: bool = true;
const SW2_LAD_SITES: &[&str] = &[];
mod sw2_ladder;
const WH: usize = W - 2 * PAGE_D;
/// P1 cost counters (CCX of the page parts as emitted, MCX macros priced as expanded): 0 gather (test only),
/// 1 page cells, 2 window rotations, 3 window swaps, 4 class flags of 0, 2, 3.
static PG_CNT: [std::sync::atomic::AtomicU64; 20] = [const { std::sync::atomic::AtomicU64::new(0) }; 20];
/// count only: the big_phase flag site being emitted (1..6), its flag CCX also go to PG_CNT[10 + site]
static BIG_SITE: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
fn pg_cost(g: &[G]) -> u64 {
    let t = MACS.lock().unwrap();
    g.iter().map(|x| if x.0 == MAC { let m = &t[x.1 as usize]; let k = m.lits.len() as u64; if m.an.is_empty() { 2 * k - 3 } else { 4 * k - 8 } } else if x.2 != NONE { 1 } else { 0 }).sum()
}
fn pg_add(i: usize, g: &[G]) {
    let c = pg_cost(g);
    PG_CNT[i].fetch_add(c, Ordering::Relaxed);
    let st = BIG_SITE.load(Ordering::Relaxed);
    if i == 4 && st > 0 { PG_CNT[10 + st].fetch_add(c, Ordering::Relaxed); }
}
const RW: usize = 64;
/// Clean lanes for the merged fold chain.
const ZL: usize = 4;
/// Each fold chain runs this many wires from its own start: a carry gets j wires with 2^-j.
const CHW: usize = 33;
/// ov is read back on this many top wires.
const CMPW: usize = 34;
/// LEAN_SQ (lane arxiv-research): x += lam^2 by three Karatsuba half-squares in one 258-wire register (Haener,
/// Tripier, Young et al. arXiv:2609.05625 section VII.1 squarer form, Gidney 1709.06648 halved adders whose AND
/// ancillae are the register's still-clean upper wires), folded into x with the parent's chains. Off re-emits the parent.
const LEAN_SQ: bool = true;
const LEAN_NEGCTL: bool = false;
/// LEAN_SB: 256-wire register, cross product L*H by controlled adds (no S^2); LEAN_ZL = fold lanes (3 at Q773).
const LEAN_SB: bool = true;
const LEAN_ZL: usize = 3;
/// carry window above a spill addend (the carry past it is dropped: 2^-64 per spill add)
const SPILL_W: usize = 64;
/// Multiplier bits consumed into the product.
const CAPW: usize = 2;
/// Low lanes read when a seed tests a product for zero.
const ZW: usize = 64;
const C0M1: [usize; 6] = [4, 6, 7, 8, 9, 32]; // bits of 2^32 + 976
const P0: [u64; 4] = [0xFFFFFFFEFFFFFC2F, u64::MAX, u64::MAX, u64::MAX];

fn pbit(i: usize) -> bool {
    (P0[i / 64] >> (i % 64)) & 1 == 1
}

#[derive(Clone, Copy)]
struct G(u32, u32, u32);
type Lit = (u32, bool);
type GL = Vec<G>;
#[inline]
fn gx(a: u32) -> G {
    G(a, NONE, NONE)
}
#[inline]
fn gc(a: u32, b: u32) -> G {
    G(a, b, NONE)
}
#[inline]
fn gt(a: u32, b: u32, c: u32) -> G {
    G(a, b, c)
}
fn rev(g: &[G]) -> GL {
    g.iter().rev().cloned().collect()
}
/// fb-r7b T2C: reverse a list that may hold measured AND markers (gl_loader::ANDC / ANDU on the target): the reversed
/// pair is still compute-then-uncompute, so the two flags trade places.
fn rev_and(g: &[G]) -> GL {
    use self::gl_loader::{ANDC, ANDU, AFLAGS};
    g.iter().rev().map(|x| {
        if x.2 == NONE { return *x; }
        let f = x.2 & AFLAGS;
        let l = x.2 & !AFLAGS;
        G(x.0, x.1, if f == ANDC { l | ANDU } else if f == ANDU { l | ANDC } else { x.2 })
    }).collect()
}

/// AND of k controls on one clean lane, 2k-3 T: conditionally clean wires, Khattar-Gidney 2024.
fn cc_core(cs: &[u32], tgt: u32, z: u32) -> GL {
    let k = cs.len();
    let m = k / 2;
    let mut up: GL = vec![gt(cs[0], cs[1], z), gc(z, cs[0]), gc(z, cs[1])];
    let (mut guards, mut aa, mut bb) = (vec![z], vec![cs[0]], vec![cs[1]]);
    for i in 1..m {
        let (a, b) = (cs[2 * i], cs[2 * i + 1]);
        let g = aa[i - 1];
        up.extend_from_slice(&[gt(a, b, g), gc(g, a), gc(g, b)]);
        guards.push(g);
        aa.push(a);
        bb.push(b);
    }
    let mut cur = guards[m - 1];
    let mut walk: GL = vec![];
    let mut out = up.clone();
    if k % 2 == 1 {
        let x = cs[k - 1];
        if m == 1 {
            out.push(gt(z, x, tgt));
            out.extend(rev(&up));
            return out;
        }
        walk.push(gt(cur, x, bb[m - 2]));
        cur = bb[m - 2];
    }
    if m >= 2 {
        let mut i = m - 2;
        while i >= 1 {
            walk.push(gt(cur, guards[i], bb[i - 1]));
            cur = bb[i - 1];
            i -= 1;
        }
    }
    out.extend_from_slice(&walk);
    out.push(gt(cur, guards[0], tgt));
    out.extend(rev(&walk));
    out.extend(rev(&up));
    out
}

mod mac_merge;
/// R7D experiment switches: env R7D_<NAME>=1 turns a pass on (all off = the 488f8c1f stream byte for byte).
/// ob-ladder: the 777-order post-pass stack (fb-r7d v2: HANDOFF_POSTPASS + SIMP_PRE/MID/POST) is ON by default (the graded
/// build runs with an empty environment); env R7D_<NAME>=0 turns a default off, =1 turns any other switch on.
const R7D_DEFAULT_ON: [&str; 4] = ["HANDOFF_POSTPASS", "SIMP_PRE", "SIMP_MID", "SIMP_POST"];
pub(crate) fn r7d(name: &str) -> bool {
    match std::env::var(format!("R7D_{name}")) { Ok(v) => v == "1", Err(_) => R7D_DEFAULT_ON.contains(&name) || (AK_K4 && name == "COND_US") }
}
/// AK_K4 (8396ec91 K4): the condition post-pass (cond_pass::run_levers "mufsr" + deep peephole + deep gate fold,
/// already in this tree, byte-identical to his) runs on the final stream by default (his R7D_DEFAULT_ON adds COND_US).
/// His note: every rewrite is a per-site identity or identical on every correct shot (-20,011 on his row).
const AK_K4: bool = true;
const MAC_ON: bool = true;
const MAC: u32 = u32::MAX - 1;
#[derive(Clone)]
struct Mac { lits: Vec<Lit>, tgt: u32, an: Vec<u32>, /// inner clean lane of the cc_core form (512 = ZB; another lane: fb-r7b HMR_AUX)
    z: u32 }
static MACS: std::sync::Mutex<Vec<Mac>> = std::sync::Mutex::new(Vec::new());
/// Expand one dirty-ancilla MCX (Barenco, the original emission).
fn mac_expand(m: &Mac, out: &mut GL) {
    let l = &m.lits; let k = l.len(); let tgt = m.tgt; let an = &m.an;
    let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
    out.extend_from_slice(&pre);
    let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
    if an.is_empty() && k == 2 { out.push(gt(cs[0], cs[1], tgt)); out.extend_from_slice(&pre); return; }
    if an.is_empty() { out.extend(cc_core(&cs, tgt, m.z)); out.extend_from_slice(&pre); return; }
    let mut up = vec![gt(cs[k - 1], an[k - 3], tgt)];
    let mut i = k - 2;
    while i > 1 { up.push(gt(cs[i], an[i - 2], an[i - 1])); i -= 1; }
    let mid = gt(cs[0], cs[1], an[0]);
    out.extend_from_slice(&up); out.push(mid); out.extend(up.iter().rev().cloned());
    out.extend_from_slice(&up[1..]); out.push(mid); out.extend(up[1..].iter().rev().cloned());
    out.extend_from_slice(&pre);
}
/// Macro-level analysis + expansion of the F gate list.
fn mac_finish(gates: Vec<G>) -> Vec<G> {
    let t = MACS.lock().unwrap().clone();
    let key = |m: &Mac| { let mut v = m.lits.clone(); v.sort(); v };
    // fb-r7b HMR_AUX: a macro whose inner clean lane is not ZB (mclean, the demux A gate) is only tracked for the measured
    // uncompute: it takes no part in the fusions, so the gate list is the one of the plain emission
    let fz = |m: &Mac| m.z == 512 || !m.an.is_empty();
    let (mut r1, mut r1t, mut adj, mut sw2, mut sw3) = (0u64, 0u64, 0u64, 0u64, 0u64);
    let mut prev: Option<usize> = None; let mut prev2: Option<usize> = None;
    for g in &gates {
        if g.0 == MAC && fz(&t[g.1 as usize]) {
            let id = g.1 as usize;
            if let Some(p) = prev {
                adj += 1;
                let (a, b) = (&t[p], &t[id]);
                if key(a) == key(b) && a.tgt != b.tgt && !b.lits.iter().any(|x| x.0 == a.tgt) && !a.lits.iter().any(|x| x.0 == b.tgt) { r1 += 1; r1t += 4 * (a.lits.len() as u64) - 8; }
                // swap pair: a = MCX(S+b.tgt -> a.tgt), b = MCX(S+a.tgt -> b.tgt)
                let mut ka: Vec<Lit> = a.lits.iter().filter(|x| x.0 != b.tgt).cloned().collect(); ka.sort();
                let mut kb: Vec<Lit> = b.lits.iter().filter(|x| x.0 != a.tgt).cloned().collect(); kb.sort();
                if a.lits.contains(&(b.tgt, true)) && b.lits.contains(&(a.tgt, true)) && ka == kb {
                    sw2 += 1;
                    if let Some(p2) = prev2 { let c = &t[p2]; if c.tgt == a.tgt && key(c) == key(a) { sw3 += 1; } }
                }
            }
            prev2 = prev; prev = Some(id);
        } else { prev = None; prev2 = None; }
    }
    eprintln!("MAC: {} macros, adjacent pairs {adj}, same-controls pairs {r1} (~{r1t} T), swap pairs {sw2}, swap triples {sw3}", t.len());
    // optimize runs of adjacent macros
    let mut opt: Vec<G> = Vec::with_capacity(gates.len());
    let mut osrc: Vec<u32> = Vec::with_capacity(gates.len());
    let (mut n_sw, mut n_fan, mut n_fan_t) = (0u64, 0u64, 0u64);
    let mut i = 0usize;
    let n = gates.len();
    while i < n {
        let g = gates[i];
        if g.0 != MAC { opt.push(g); osrc.push(i as u32); i += 1; continue; }
        // (a) swap triple
        if !fz(&t[g.1 as usize]) { opt.push(g); osrc.push(i as u32); i += 1; continue; }
        if OPT_SWAP && i + 2 < n && gates[i + 1].0 == MAC && gates[i + 2].0 == MAC && fz(&t[gates[i + 1].1 as usize]) && fz(&t[gates[i + 2].1 as usize]) {
            let (m1, m2, m3) = (&t[g.1 as usize], &t[gates[i + 1].1 as usize], &t[gates[i + 2].1 as usize]);
            let (a, b) = (m1.tgt, m2.tgt);
            let mut s1: Vec<Lit> = m1.lits.iter().filter(|x| x.0 != b).cloned().collect(); s1.sort();
            let mut s2: Vec<Lit> = m2.lits.iter().filter(|x| x.0 != a).cloned().collect(); s2.sort();
            if a != b && m3.tgt == a && key(m1) == key(m3) && m1.lits.contains(&(b, true)) && m2.lits.contains(&(a, true)) && s1 == s2
                && !s1.iter().any(|x| x.0 == a || x.0 == b) {
                opt.push(gc(b, a)); opt.push(gates[i + 1]); opt.push(gc(b, a));
                osrc.extend_from_slice(&[i as u32, i as u32 + 1, i as u32 + 2]);
                n_sw += 1; i += 3; continue;
            }
        }
        // (b) same-controls run -> one MCX + CX fanout
        if OPT_FAN {
            let k0 = key(&t[g.1 as usize]);
            let mut j = i + 1;
            let mut tg: Vec<u32> = vec![t[g.1 as usize].tgt];
            while j < n && gates[j].0 == MAC {
                let m = &t[gates[j].1 as usize];
                if !fz(m) || key(m) != k0 || tg.contains(&m.tgt) { break; }
                tg.push(m.tgt); j += 1;
            }
            if j - i >= 2 {
                for &tt in &tg[1..] { opt.push(gc(tg[0], tt)); osrc.push(i as u32); }
                opt.push(g); osrc.push(i as u32);
                for &tt in &tg[1..] { opt.push(gc(tg[0], tt)); osrc.push(i as u32); }
                n_fan += 1; n_fan_t += (j - i - 1) as u64; i = j; continue;
            }
        }
        opt.push(g); osrc.push(i as u32); i += 1;
    }
    eprintln!("MAC opt: swap triples {n_sw}, fanout groups {n_fan} removing {n_fan_t} MCX");
    let opt = if r7d("MAC_E1") || r7d("MAC_E2") { mac_merge::run(opt, &t, r7d("MAC_E1"), r7d("MAC_E2")) } else { opt };
    let mut out = Vec::with_capacity(opt.len() * 3);
    let mut and_idx: Vec<usize> = vec![];
    let prof = r765_prof();
    let mut src: Vec<u32> = vec![];
    for (g, &sx) in opt.into_iter().zip(osrc.iter()) {
        let n0 = out.len();
        if g.0 == MAC {
            let m = &t[g.1 as usize];
            let s = out.len();
            mac_expand(m, &mut out);
            if m.an.is_empty() {
                // cc_core on its clean lane (512, or the aux lane of an HMR_AUX macro): its first gate (AND compute) and its last
                // gate (the same AND, uncompute)
                let np = m.lits.iter().filter(|x| !x.1).count();
                and_idx.push(s + np);
                if m.lits.len() > 2 { and_idx.push(out.len() - 1 - np); }
            }
        } else { out.push(g); }
        if prof { src.extend(std::iter::repeat(sx).take(out.len() - n0)); }
    }
    if prof { *MAC_SRC.lock().unwrap() = src; }
    *AND_IDX.lock().unwrap() = and_idx;
    out
}
const OPT_SWAP: bool = true;
const OPT_FAN: bool = true;
/// ob-hmr (brief_PIVOT REVISION 2): the clean-lane AND of every cc_core call on ZB (lane 512, the MAC expansions) is
/// uncomputed by X-basis measurement (Hmr) and CZ(c0, c1) under the outcome (Gidney arXiv:1709.06648) instead of the
/// unitary Toffoli: -1 T per call; mechanism of the public 777 row's AND_FLAG (284e7612). false = the stream of 488f8c1f.
/// The environment variable OB_HMR (1 / 0) overrides it for experiments; OB_HMR_NEG=1 drops the CZ (negative control).
const HMR_AND: bool = true;
/// fb-r7b (R7_B.md, measured-uncompute census): the cc_core calls outside the MAC table (mclean: the sandwich's ANDs on
/// ZB with X[0] as the inner clean lane; the demux A gate on ZB with d) are recorded as macros with their own inner lane, so
/// their inner AND is uncomputed by measurement like the lane-512 ones. Needs HMR_AND. false (or OB_HMR_AUX=0) = the stream
/// of the parent.
const HMR_AUX: bool = true;
/// fb-r7b D1 (sandwich_x, F = 1 block): the bit flag z = f & vb[i] is one Toffoli (the act cubes are implied by f) and it and
/// the single-term z2 flag are AND brackets (measured uncompute with HMR_AUX). false = the parent's gates.
const SW_F1Z: bool = true;
/// fb-r7b T2C: the page word T2 (the implicit word's temporary) is 0 throughout every sandwich (erase_blk; probed at
/// the four edges of all 396 sandwiches per pass, 16,384 shots): its 11 lanes are the clean carry lanes of every adder
/// of the K2 half and the F = 0 / F = 1 blocks (Gidney forms, measured uncompute). false = the stream of 1fdad261.
const SW_T2C: bool = false;
/// fb-r7b K2C: the K2 half of every sandwich (pre and post) runs its adders in the hybrid form on w = 2 clean lanes: z (the
/// sandwich's AND lane = ZB, the frame's global clean lane: no macro inside the K2 half) and z2 (the caller's clean AND
/// target, X[0]); census: both 0 at both K2 edges in all 792 K2 windows per pass (odd / t%4==2 / t%4==0 incl. big).
/// Overridable at compile time: R7B_K2C=0. false = the stream of 1fdad261 (with the precancel marker rule).
const SW_K2C: bool = match option_env!("R7B_K2C") { Some(v) => !matches!(v.as_bytes(), b"0"), None => true };
mod r7b_fail;
/// fb-r7a S2 (sandwich_x, F = 1 block; needs SW_F1Z): a digit flag whose cubes all carry two or more extra literals is
/// computed straight from f, vb[i], the digit and the cube as a clean macro on X[0] (inner lane ZB, 2k - 3, inner AND
/// measured) after the bit flag is released, instead of the dirty-ancilla form (4k - 8) that reads the bit flag on ZB.
/// Same Boolean function, same adds; the adds of one bit commute. false = the parent's gates.
const SW_Z2D: bool = true;
fn hmr_aux() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| hmr_and() && MAC_ON && env_bool("OB_HMR_AUX", HMR_AUX))
}
/// fb-r7b: one half of a bracket tgt ^= a & b on a lane that is 0 before the first half, with a, b and tgt unwritten up
/// to the second half (the same call): the two Toffolis become AND compute / measured uncompute. Off: a plain Toffoli.
fn and2(a: u32, b: u32, tgt: u32) -> GL {
    if !(hmr_aux() && IN_F.load(Ordering::Relaxed)) { return vec![gt(a, b, tgt)]; }
    let mut t = MACS.lock().unwrap();
    t.push(Mac { lits: vec![(a, true), (b, true)], tgt, an: Vec::new(), z: NONE });
    vec![G(MAC, (t.len() - 1) as u32, NONE)]
}
/// an HMR_AUX macro: tgt ^= AND(l) by cc_core with inner clean lane z (k >= 3 literals, distinct lanes)
fn mac_aux(l: &[Lit], tgt: u32, z: u32) -> GL {
    let mut t = MACS.lock().unwrap();
    t.push(Mac { lits: l.to_vec(), tgt, an: Vec::new(), z });
    vec![G(MAC, (t.len() - 1) as u32, NONE)]
}
fn env_bool(k: &str, d: bool) -> bool { std::env::var(k).map(|v| v.trim() == "1").unwrap_or(d) }
pub fn hmr_and() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| env_bool("OB_HMR", HMR_AND))
}
fn hmr_negctl() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| env_bool("OB_HMR_NEG", false))
}
/// ob-hmr: positions in mac_finish's output of the two AND gates of every cc_core call on lane 512
static AND_IDX: std::sync::Mutex<Vec<usize>> = std::sync::Mutex::new(Vec::new());
/// ob-hmr: (kind, target, controls) of a G gate
fn g_parts(g: G) -> (u8, u32, [u32; 2]) {
    // ob-tail AND markers (gl_loader::ANDC / ANDU on the target): kind 3 / 4, so they never pair with a plain CCX
    if g.2 != NONE && gl_loader::flag_of(g.2) != 0 {
        (if gl_loader::flag_of(g.2) == gl_loader::ANDC { 3 } else { 4 }, gl_loader::lane_of(g.2), [g.0.min(g.1), g.0.max(g.1)])
    } else if g.2 != NONE { (2, g.2, [g.0.min(g.1), g.0.max(g.1)]) } else if g.1 != NONE { (1, g.1, [g.0, NONE]) } else { (0, g.0, [NONE, NONE]) }
}
/// ob-hmr: B's CancelIndex rule (fd2/cancel_index.rs) on F's G list: a gate cancels the last earlier identical gate when
/// no live gate since reads its target or writes one of its controls (windows of 2^18 live gates, as B). Run before the
/// AND uncomputes become measurements, so back-to-back cc_core calls sharing (c0, c1, z) still cancel. A pair with one
/// AND gate and one plain gate is kept (not cancelled). Exact: deletes commuting identical self-inverse pairs only.
fn hmr_precancel(gates: &[G], fl: &[bool], bar: &[bool]) -> (Vec<G>, Vec<bool>, u64, u64, Vec<usize>) {
    let n = gates.len();
    assert!(bar.is_empty() || bar.len() == n);
    let mut bars: Vec<usize> = vec![];
    let nl = gates.iter().flat_map(|g| [g.0, g.1, g.2]).filter(|&q| q != NONE).map(gl_loader::lane_of).max().unwrap_or(0) as usize + 1;
    let mut alive = vec![true; n];
    let (mut writes, mut reads): (Vec<Vec<u32>>, Vec<Vec<u32>>) = (vec![vec![]; nl], vec![vec![]; nl]);
    let mut keys: HashMap<(u8, u32, u32, u32), Vec<u32>> = HashMap::new();
    let (mut live, mut cancelled, mut kept_mixed) = (0usize, 0u64, 0u64);
    fn top(v: &mut Vec<u32>, alive: &[bool]) -> Option<u32> {
        while v.last().is_some_and(|&j| !alive[j as usize]) { v.pop(); }
        v.last().copied()
    }
    for i in 0..n {
        let at_bar = !bar.is_empty() && bar[i];
        if at_bar { bars.push(i); }
        if live >= 1 << 18 || (at_bar && live > 0) {
            for v in writes.iter_mut().chain(reads.iter_mut()) { v.clear(); }
            keys.clear();
            live = 0;
        }
        let (k, t, cs) = g_parts(gates[i]);
        let key = (k, t, cs[0], cs[1]);
        let nc = k as usize;
        let ent = keys.entry(key).or_default();
        if let Some(j) = top(ent, &alive) {
            let mut blocked = top(&mut reads[t as usize], &alive).is_some_and(|p| p > j);
            for &c in cs.iter().take(nc) { blocked |= top(&mut writes[c as usize], &alive).is_some_and(|p| p > j); }
            if !blocked && fl[i] != fl[j as usize] { blocked = true; kept_mixed += 1; }
            if !blocked {
                alive[j as usize] = false;
                alive[i] = false;
                keys.get_mut(&key).unwrap().pop();
                cancelled += 1;
                continue;
            }
        }
        keys.get_mut(&key).unwrap().push(i as u32);
        writes[t as usize].push(i as u32);
        // fb-r7b: an AND marker (kind 3 compute into |0>, kind 4 measured uncompute) depends on its target's VALUE at that
        // instant, so it is also a read of the target: no identical pair may cancel across it
        if k >= 3 { reads[t as usize].push(i as u32); }
        for &c in cs.iter().take(nc) { reads[c as usize].push(i as u32); }
        live += 1;
    }
    let mut g2 = Vec::with_capacity(n);
    let mut f2 = Vec::with_capacity(n);
    let mut pos = Vec::with_capacity(bars.len());
    let mut nb = 0usize;
    for i in 0..n {
        if nb < bars.len() && bars[nb] == i { pos.push(g2.len()); nb += 1; }
        if alive[i] { g2.push(gates[i]); f2.push(fl[i]); }
    }
    if r765_prof() { *PRE_ALIVE.lock().unwrap() = alive.clone(); }
    (g2, f2, cancelled, kept_mixed, pos)
}
/// ob-hmr: role of every gate of F's list in forward order: 0 plain, 1 AND compute, 2 AND measured uncompute. Asserts
/// that on every lane the AND gates alternate compute / uncompute with the same controls, that no other gate writes a
/// lane while it holds an AND, and that no lane holds an AND at the end of the list.
fn hmr_roles(gates: &[G], fl: &[bool]) -> Vec<u8> {
    let nl = gates.iter().flat_map(|g| [g.0, g.1, g.2]).filter(|&q| q != NONE).map(gl_loader::lane_of).max().unwrap_or(0) as usize + 1;
    let mut hold: Vec<Option<(u32, u32)>> = vec![None; nl];
    let mut role = vec![0u8; gates.len()];
    for (i, &g) in gates.iter().enumerate() {
        let (k, t, _) = g_parts(g);
        if k >= 3 {
            // ob-tail AND marker: its own pairing (structural, checked by the list's generator); role 3 = compute, 4 = uncompute
            assert!(!fl[i] && hold[t as usize].is_none(), "ob-tail: AND marker on a lane holding an ob-hmr AND at gate {i}");
            role[i] = k;
            continue;
        }
        if fl[i] {
            assert!(g.2 != NONE, "ob-hmr: AND flag on a non-Toffoli");
            let c = (g.0.min(g.1), g.0.max(g.1));
            match hold[t as usize] {
                None => { hold[t as usize] = Some(c); role[i] = 1; }
                Some(h) => { assert!(h == c, "ob-hmr: AND uncompute with other controls at gate {i}"); hold[t as usize] = None; role[i] = 2; }
            }
        } else {
            assert!(hold[t as usize].is_none(), "ob-hmr: gate {i} writes lane {t} while it holds an AND");
        }
    }
    assert!(hold.iter().all(|h| h.is_none()), "ob-hmr: AND held at the end of F");
    role
}
fn mcx(lits: &[Lit], tgt: u32, dirty: &[u32]) -> GL {
    let mut l: Vec<Lit> = Vec::with_capacity(lits.len());
    for &(q0, p) in lits {
        match l.iter().find(|x| x.0 == q0) {
            Some(x) => {
                if x.1 != p {
                    return vec![];
                }
            }
            None => l.push((q0, p)),
        }
    }
    let k = l.len();
    if k == 0 {
        return vec![gx(tgt)];
    }
    let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
    let mut g = pre.clone();
    if k == 1 {
        g.push(gc(l[0].0, tgt));
    } else if k == 2 {
        g.push(gt(l[0].0, l[1].0, tgt));
    } else if ZB > 0 && IN_F.load(Ordering::Relaxed) && tgt != ZB_LANE && !ZB_BUSY.load(Ordering::Relaxed) {
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        if MAC_ON {
            let mut t = MACS.lock().unwrap();
            t.push(Mac { lits: l.clone(), tgt, an: Vec::new(), z: 512 });
            return vec![G(MAC, (t.len() - 1) as u32, NONE)];
        }
        g.extend(cc_core(&cs, tgt, 512));
    } else {
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        let mut an: Vec<u32> = Vec::with_capacity(k - 2);
        for &d in dirty {
            if d != tgt && !cs.contains(&d) {
                an.push(d);
                if an.len() == k - 2 {
                    break;
                }
            }
        }
        assert!(an.len() == k - 2);
        if MAC_ON && IN_F.load(Ordering::Relaxed) {
            let mut t = MACS.lock().unwrap();
            t.push(Mac { lits: l.clone(), tgt, an: an.clone(), z: NONE });
            return vec![G(MAC, (t.len() - 1) as u32, NONE)];
        }
        let mut up = vec![gt(cs[k - 1], an[k - 3], tgt)];
        let mut i = k - 2;
        while i > 1 {
            up.push(gt(cs[i], an[i - 2], an[i - 1]));
            i -= 1;
        }
        let mid = gt(cs[0], cs[1], an[0]);
        g.extend_from_slice(&up);
        g.push(mid);
        g.extend(up.iter().rev().cloned());
        g.extend_from_slice(&up[1..]);
        g.push(mid);
        g.extend(up[1..].iter().rev().cloned());
    }
    g.extend_from_slice(&pre);
    g
}

fn cswap(c: u32, a: u32, b: u32, g: &mut GL) {
    g.push(gc(b, a));
    g.push(gt(c, a, b));
    g.push(gc(b, a));
}

fn po_reflect(c: u32, lanes: &[u32], j: isize) -> GL {
    let mut g: GL = vec![];
    let n = lanes.len();
    for i in 0..n {
        let k = (j - i as isize).rem_euclid(n as isize) as usize;
        if i < k { cswap(c, lanes[i], lanes[k], &mut g); }
    }
    g
}

fn rotate_up(ctl: u32, w: &[u32], r: usize) -> GL {
    let n = w.len();
    let r = r % n;
    let mut g = vec![];
    if r == 0 {
        return g;
    }
    let mut seen = vec![false; n];
    for st in 0..n {
        if seen[st] {
            continue;
        }
        let mut i = st;
        let mut cyc = vec![];
        while !seen[i] {
            seen[i] = true;
            cyc.push(i);
            i = (i + r) % n;
        }
        for j in 1..cyc.len() {
            cswap(ctl, w[cyc[0]], w[cyc[j]], &mut g);
        }
    }
    g
}

fn inc_ctl(reg: &[u32], lits: &[Lit], dirty: &[u32]) -> GL {
    let mut g = vec![];
    for i in (0..reg.len()).rev() {
        let mut l: Vec<Lit> = lits.to_vec();
        for j in 0..i {
            l.push((reg[j], true));
        }
        g.extend(mcx(&l, reg[i], dirty));
    }
    g
}
fn dec_ctl(reg: &[u32], lits: &[Lit], dirty: &[u32]) -> GL {
    rev(&inc_ctl(reg, lits, dirty))
}

fn add_chain(t: &[u32], s: &[u32], c: u32) -> GL {
    let n = t.len();
    let mut g = Vec::with_capacity(7 * n);
    for i in 0..n {
        g.push(gc(c, s[i]));
        g.push(gc(c, t[i]));
        g.push(gt(s[i], t[i], c));
    }
    for i in (0..n).rev() {
        g.push(gt(s[i], t[i], c));
        g.push(gc(c, t[i]));
        g.push(gc(s[i], t[i]));
        g.push(gc(c, s[i]));
    }
    g
}

fn inc_long(reg: &[u32], ctl: u32, dirty: &[u32], c: u32) -> GL {
    let mut r = vec![ctl];
    r.extend_from_slice(reg);
    let mut d: Vec<u32> = Vec::with_capacity(r.len());
    for &q0 in dirty {
        if q0 != c && !r.contains(&q0) {
            d.push(q0);
            if d.len() == r.len() {
                break;
            }
        }
    }
    assert!(d.len() == r.len());
    let sub = rev(&add_chain(&r, &d, c));
    let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
    let mut g = sub.clone();
    g.extend_from_slice(&nots);
    g.extend_from_slice(&sub);
    g.extend_from_slice(&nots);
    g.push(gx(ctl));
    g
}

fn aligned_blocks(vals: &BTreeSet<i32>) -> Vec<(i32, usize)> {
    let mut out = vec![];
    let mut vals = vals.clone();
    while let Some(&v) = vals.iter().next() {
        let mut k = 0usize;
        loop {
            let k2 = k + 1;
            if v & ((1 << k2) - 1) != 0 {
                break;
            }
            if (0..(1 << k2)).all(|i| vals.contains(&(v + i))) {
                k = k2;
            } else {
                break;
            }
        }
        out.push((v, k));
        for i in 0..(1 << k) {
            vals.remove(&(v + i));
        }
    }
    out
}

const fn maskv(v: usize) -> u128 {
    let mut m = 0u128;
    let mut p = 0;
    while p < 128 {
        if (p >> v) & 1 == 0 {
            m |= 1u128 << p;
        }
        p += 1;
    }
    m
}
const MASKV: [u128; 7] = [maskv(0), maskv(1), maskv(2), maskv(3), maskv(4), maskv(5), maskv(6)];
type Cubes = Vec<Vec<(usize, u8)>>;
/// Minimum cost disjoint decision tree over the hi bits (vars 0..3) and the parity (var 4).
fn tree_rec(on: u128, off: u128, n: i32, base: i32, vs: &[usize], memo: &mut HashMap<(u128, u128, i32), (i64, Cubes)>) -> (i64, Cubes) {
    if on == 0 {
        return (0, vec![]);
    }
    if off == 0 {
        let l = n + base;
        let c = if l <= 1 { 0 } else if l == 2 { 1 } else { 4 * (l as i64 - 2) };
        return (c, vec![vec![]]);
    }
    if let Some(r) = memo.get(&(on, off, n)) {
        return r.clone();
    }
    let mut best: Option<(i64, Cubes)> = None;
    for &v in vs {
        let z = MASKV[v];
        let (on0, on1, off0, off1) = (on & z, on & !z, off & z, off & !z);
        if (on0 == 0 && off0 == 0) || (on1 == 0 && off1 == 0) {
            continue;
        }
        let (c0, l0) = tree_rec(on0, off0, n + 1, base, vs, memo);
        let (c1, l1) = tree_rec(on1, off1, n + 1, base, vs, memo);
        if best.is_none() || c0 + c1 < best.as_ref().unwrap().0 {
            let mut lst: Cubes = vec![];
            for x in &l0 {
                let mut y = vec![(v, 0u8)];
                y.extend_from_slice(x);
                lst.push(y);
            }
            for x in &l1 {
                let mut y = vec![(v, 1u8)];
                y.extend_from_slice(x);
                lst.push(y);
            }
            best = Some((c0 + c1, lst));
        }
    }
    let r = best.expect("cover");
    memo.insert((on, off, n), r.clone());
    r
}
fn dtree(on: u128, off: u128, vs: &[usize], base: i32) -> Cubes {
    let mut memo = HashMap::new();
    tree_rec(on, off, 0, base, vs, &mut memo).1
}


/// r7e profiler (count only, env R7E_PROF=1): CCX of every list passed to B::t, by the current tag and extra keys.
static R7E_TAG: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());
static R7E_KEYS: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());
static R7E_ACC: std::sync::Mutex<BTreeMap<String, [u64; 4]>> = std::sync::Mutex::new(BTreeMap::new());
fn r7e_on() -> bool { static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new(); *ON.get_or_init(|| std::env::var("R7E_PROF").is_ok()) }
fn r7e_tag(s: &str) { if r7e_on() { *R7E_TAG.lock().unwrap() = s.to_string(); if !s.contains('/') && !s.starts_with("big:") { *R7E_CLASS.lock().unwrap() = s.to_string(); } } }
/// R765_PROF sub-section inside the slot class set by slot() (read-only; only with R7E_PROF)
static R7E_CLASS: std::sync::Mutex<String> = std::sync::Mutex::new(String::new());
fn r7e_sub(part: &str) { if r7e_on() && r765_prof() { let c = R7E_CLASS.lock().unwrap().clone(); *R7E_TAG.lock().unwrap() = format!("{c}/{part}"); } }
/// R765_PROF: (sel, K2) lengths of the last sandwich_x pre list; (role-swap, K2) lengths of the last sw_post built
static SWX_LAST: std::sync::Mutex<(usize, usize)> = std::sync::Mutex::new((0, 0));
static SWP_LAST: std::sync::Mutex<(usize, usize)> = std::sync::Mutex::new((0, 0));
fn swx_last() -> (usize, usize) { *SWX_LAST.lock().unwrap() }
fn swp_note(rs_len: usize) { if r765_prof() { let k = SWX_LAST.lock().unwrap().1; *SWP_LAST.lock().unwrap() = (rs_len, k); } }
fn swp_last() -> (usize, usize) { *SWP_LAST.lock().unwrap() }
fn r7e_keys(k: &[String]) { if r7e_on() { *R7E_KEYS.lock().unwrap() = k.to_vec(); } }
fn r7e_add(g: &[G]) {
    if !r7e_on() { return; }
    let mut c = [0u64; 4];
    {
        let t = MACS.lock().unwrap();
        for x in g {
            if x.0 == MAC { let m = &t[x.1 as usize]; let k = m.lits.len() as u64; c[3] += 1; if m.an.is_empty() { c[1] += 2 * k - 3 } else { c[2] += 4 * k - 8 } } else if x.2 != NONE { c[0] += 1 }
        }
    }
    let tag = R7E_TAG.lock().unwrap().clone();
    let keys = R7E_KEYS.lock().unwrap().clone();
    let mut a = R7E_ACC.lock().unwrap();
    let mut put = |k: String| { let e = a.entry(k).or_insert([0; 4]); for i in 0..4 { e[i] += c[i]; } };
    put(format!("TAG {tag}"));
    if tag.starts_with("big:") { for k in keys { put(format!("KEY {k}")); put(format!("KT {k} {tag}")); } }
}
/// fb-r7a count only (R7E_PROF): CCX of one sandwich part under the slot tag, n = times the list is emitted
fn r7a_sw(part: &str, g: &[G], n: u64) {
    if !r7e_on() { return; }
    let c = pg_cost(g) * n;
    let tag = R7E_TAG.lock().unwrap().clone();
    let mut a = R7E_ACC.lock().unwrap();
    a.entry(format!("SW {tag} {part}")).or_insert([0; 4])[0] += c;
    a.entry(format!("SWALL {part}")).or_insert([0; 4])[0] += c;
}
/// R765_PROF (env, read-only profile): per-gate section of F's list from the r7e tags in force at each B::t, carried
/// through mac_finish, compaction and the ob-hmr pre-cancel; emitted per traversal into the fd2 builder's raw dump.
pub(crate) fn r765_prof() -> bool {
    static P: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *P.get_or_init(|| std::env::var("R765_PROF").is_ok())
}
static SECMARKS: std::sync::Mutex<Vec<(usize, u16)>> = std::sync::Mutex::new(Vec::new());
static SECNAMES: std::sync::Mutex<Vec<String>> = std::sync::Mutex::new(Vec::new());
static MAC_SRC: std::sync::Mutex<Vec<u32>> = std::sync::Mutex::new(Vec::new());
static PRE_ALIVE: std::sync::Mutex<Vec<bool>> = std::sync::Mutex::new(Vec::new());
fn sec_id(name: &str) -> u16 {
    let mut v = SECNAMES.lock().unwrap();
    if v.is_empty() { v.push("untagged".to_string()); }
    if let Some(i) = v.iter().position(|x| x == name) { return i as u16; }
    v.push(name.to_string());
    (v.len() - 1) as u16
}
fn sec_mark_cur(pos: usize) {
    if !r765_prof() { return; }
    let name = R7E_TAG.lock().unwrap().clone();
    let id = sec_id(if name.is_empty() { "untagged" } else { &name });
    let mut m = SECMARKS.lock().unwrap();
    if m.last().map_or(true, |&(_, l)| l != id) { m.push((pos, id)); }
}
fn sec_trunc(pos: usize) {
    if r765_prof() { SECMARKS.lock().unwrap().retain(|&(p, _)| p < pos); }
}
fn sec_tags(n: usize) -> Vec<u16> {
    let m = SECMARKS.lock().unwrap();
    let mut t = vec![0u16; n];
    let (mut cur, mut j) = (0u16, 0usize);
    for p in 0..n {
        while j < m.len() && m[j].0 <= p { cur = m[j].1; j += 1; }
        t[p] = cur;
    }
    t
}
fn r7e_print() {
    if !r7e_on() { return; }
    let a = R7E_ACC.lock().unwrap();
    for (k, c) in a.iter() {
        eprintln!("R7E {:44} total {:9} plain {:9} cc {:9} barenco {:8} macs {:7}", k, c[0] + c[1] + c[2], c[0], c[1], c[2], c[3]);
    }
}
/// lane allocator of the stored inverter (virtual lanes)
struct B {
    free: Vec<u32>,
    next: u32,
    gates: Vec<G>,
}
impl B {
    fn alloc(&mut self) -> u32 {
        if let Some(q0) = self.free.pop() {
            q0
        } else {
            self.next += 1;
            self.next - 1
        }
    }
    fn release(&mut self, q0: u32) {
        self.free.push(q0);
        self.free.sort_by(|a, b| b.cmp(a));
    }
    fn t(&mut self, g: &[G]) {
        r7e_add(g);
        if r765_prof() { sec_mark_cur(self.gates.len()); }
        self.gates.extend_from_slice(g);
    }
}

struct Machine {
    b: B,
    dirty: Vec<u32>,
    pas: Vec<u32>,
    x: Vec<u32>,
    y: Vec<u32>,
    e: Vec<u32>,
    par: u32,
    /// P1 page lanes (empty when PAGE is off): VA, VB, SC, T2 (T2 is the implicit word's temporary), PAGE_D each.
    pg: Vec<u32>,
    /// ring width (W, or WH between the cuts with PAGE_N) and the lanes freed by the narrowing
    wr: usize,
    freed: Vec<u32>,
    /// L-C: the 4th wait bit of the long classes (a lane freed by the narrowing; NONE outside the cuts)
    w4: u32,
    /// CAD4: the wait flag of the low classes 4..9 (the frame's spare lane between the cuts; NONE outside)
    w1: u32,
    /// CONV: the D16 T2 lanes and the D16 freed list saved by the start converter for the tail converter
    cv_t2: Vec<u32>,
    cv_freed: Vec<u32>,
    /// CONV: the D16 narrowed ring lists and page at the start converter (their label sets / positions are restored at the tail)
    cv_x16: Vec<u32>,
    cv_y16: Vec<u32>,
    cv_pg16: Vec<u32>,
    /// E3V: this tier slot's big rows 0..9 ran in even11 (set by even11 for big_phase)
    e3t: bool,
}

fn lf(t: i32, e: i32) -> (i32, i32) {
    if t % 2 == 1 {
        return ((t - 1) / 2, (t + 1) / 2);
    }
    let m = e >> 1;
    (t / 2 - m, t / 2 + m + (e & 1))
}
fn pairs(t: i32) -> Vec<i32> {
    let n = N as i32;
    if t % 2 == 1 {
        let (l, f) = lf(t, 1);
        return if l >= 1 && f <= n { vec![1] } else { vec![] };
    }
    (0..=ECAP)
        .filter(|&e| {
            let (l, f) = lf(t, e);
            l >= 1 && f <= n && f >= l
        })
        .collect()
}

/// Uncontrolled rotation (CX swaps, no Toffoli): content of w[i] -> w[(i + r) mod n].
fn rot_free(w: &[u32], r: usize) -> GL {
    let mut g = vec![];
    for x in rotate_up(NONE, w, r).chunks(3) {
        // rotate_up emits cswap(c, a, b) = [CX(b, a), CCX(c, a, b), CX(b, a)]: replace by SWAP(a, b)
        let (a, b) = (x[1].1, x[1].2);
        g.extend_from_slice(&[gc(a, b), gc(b, a), gc(a, b)]);
    }
    g
}
fn swap_free(a: u32, b: u32) -> GL { vec![gc(a, b), gc(b, a), gc(a, b)] }
/// Rotate a wire list up by one under c: w[i] to w[i+1], top wraps to the bottom.
fn rot1(c: u32, w: &[u32]) -> GL {
    let mut g = vec![];
    for i in (1..w.len()).rev() {
        cswap(c, w[i], w[i - 1], &mut g);
    }
    g
}

impl Machine {
    /// one ladder site: its flag gates (counted as flags) with use i replaced by uop(set_i, control lane)
    fn ladder(&self, site: &str, uop: &dyn Fn(&[i32], u32) -> GL) -> GL {
        let (sets, ops) = ladder_data::LADDER.iter().find(|s| s.0 == site).map(|s| (s.1, s.2)).expect("ladder site");
        // SW2_LADDER_SEM: the site's certificate (kept LOp indices, AND tags) when the switch is on and the site is selected
        let cert = if SW2_LADDER_SEM && (SW2_LAD_SITES.is_empty() || SW2_LAD_SITES.contains(&site)) {
            Some(sw2_ladder::SW2_LAD.iter().find(|c| c.0 == site).expect("SW2: no certificate for ladder site"))
        } else { None };
        if cert.is_some() { SW2_CNT.fetch_add(1, Ordering::Relaxed); }
        let wv = self.wr;
        let lane = |n: N| -> u32 {
            match n {
                N::D => self.x[0],
                N::ZB => self.pg[4 * PAGE_D + 1],
                N::F => self.pg[4 * PAGE_D],
                N::Yt => self.y[wv - 1],
                N::H1 => self.e[1],
                N::Y(j) => self.y[j as usize],
                N::Xt(j) => self.x[wv - j as usize],
            }
        };
        let (mut g, mut fl): (GL, GL) = (vec![], vec![]);
        for (oi, op) in ops.iter().enumerate() {
            if let Some(c) = cert {
                if c.1.binary_search(&(oi as u16)).is_err() {
                    assert!(!matches!(*op, LOp::U(..)), "SW2: certificate {site} drops a use (LOp {oi})");
                    continue;
                }
            }
            let mut q = match *op {
                LOp::X(a) => gx(lane(a)),
                LOp::Cx(a, b) => gc(lane(a), lane(b)),
                LOp::Ccx(a, b, c) => gt(lane(a), lane(b), lane(c)),
                LOp::U(i, c) => { g.extend(uop(sets[i], lane(c))); continue; }
            };
            if let Some(c) = cert {
                if let Some(&(_, k)) = c.2.iter().find(|x| x.0 as usize == oi) {
                    assert!(matches!(*op, LOp::Ccx(..)), "SW2: certificate {site} tags a non-CCX (LOp {oi})");
                    q = G(q.0, q.1, q.2 | if k == 1 { gl_loader::ANDC } else { gl_loader::ANDU });
                }
            }
            g.push(q);
            fl.push(q);
        }
        pg_add(4, &fl);
        g
    }
    /// FW_WINDOW_GROUPS: Machine::ladder with a hook after every kept op (its position in the kept-op list)
    fn ladder_h(&self, site: &str, uop: &dyn Fn(&[i32], u32) -> GL, hook: &dyn Fn(usize, &dyn Fn(N) -> u32) -> GL) -> (GL, usize) {
        let (sets, ops) = ladder_data::LADDER.iter().find(|s| s.0 == site).map(|s| (s.1, s.2)).expect("ladder site");
        let cert = if SW2_LADDER_SEM && (SW2_LAD_SITES.is_empty() || SW2_LAD_SITES.contains(&site)) {
            Some(sw2_ladder::SW2_LAD.iter().find(|c| c.0 == site).expect("SW2: no certificate for ladder site"))
        } else { None };
        if cert.is_some() { SW2_CNT.fetch_add(1, Ordering::Relaxed); }
        let wv = self.wr;
        let lane = |n: N| -> u32 {
            match n {
                N::D => self.x[0],
                N::ZB => self.pg[4 * PAGE_D + 1],
                N::F => self.pg[4 * PAGE_D],
                N::Yt => self.y[wv - 1],
                N::H1 => self.e[1],
                N::Y(j) => self.y[j as usize],
                N::Xt(j) => self.x[wv - j as usize],
            }
        };
        let (mut g, mut fl): (GL, GL) = (vec![], vec![]);
        let mut kp = 0usize;
        for (oi, op) in ops.iter().enumerate() {
            if let Some(c) = cert {
                if c.1.binary_search(&(oi as u16)).is_err() {
                    assert!(!matches!(*op, LOp::U(..)), "SW2: certificate {site} drops a use (LOp {oi})");
                    continue;
                }
            }
            let mut q = match *op {
                LOp::X(a) => gx(lane(a)),
                LOp::Cx(a, b) => gc(lane(a), lane(b)),
                LOp::Ccx(a, b, c) => gt(lane(a), lane(b), lane(c)),
                LOp::U(i, c) => { g.extend(uop(sets[i], lane(c))); g.extend(hook(kp, &lane)); kp += 1; continue; }
            };
            if let Some(c) = cert {
                if let Some(&(_, k)) = c.2.iter().find(|x| x.0 as usize == oi) {
                    q = G(q.0, q.1, q.2 | if k == 1 { gl_loader::ANDC } else { gl_loader::ANDU });
                }
            }
            g.push(q);
            fl.push(q);
            g.extend(hook(kp, &lane));
            kp += 1;
        }
        pg_add(4, &fl);
        (g, kp)
    }
    /// FW_WINDOW_GROUPS: the EVJS swaps of class geometry (l, f) under c, Y part (py) and / or X part (px) (even11's ejs)
    fn fw_ejs(&self, l: i32, f: i32, c: u32, cof: bool, py: bool, px: bool) -> GL {
        let (wv, dd, lu, fu) = (self.wr, PAGE_D, l as usize, f as usize);
        let mut g: GL = vec![];
        for b in 0..dd {
            if cof {
                if py { cswap(c, self.pg[dd + b], self.y[wv - lu + 2 * dd - 1 - b], &mut g); }
                if px { cswap(c, self.pg[2 * dd + b], self.x[wv - fu + 2 * dd - 1 - b], &mut g); }
            } else {
                if py { cswap(c, self.pg[dd + b], self.y[wv - lu + b], &mut g); }
                if px { cswap(c, self.pg[b], self.x[wv - fu + b], &mut g); }
            }
        }
        pg_add(3, &g);
        g
    }
    /// FW_WINDOW_GROUPS: even11's digit remap rmb (reverse dig[0..=e], dig = y0, x[wv - 1..wv - 9])
    fn fw_rmb(&self, c: u32, e: i32) -> GL {
        let wv = self.wr;
        let dig = |k: usize| -> u32 { if k == 0 { self.y[0] } else { self.x[wv - k] } };
        let (mut rm, eu, mut i): (GL, usize, usize) = (vec![], e as usize, 0);
        while i < eu - i {
            cswap(c, dig(i), dig(eu - i), &mut rm);
            i += 1;
        }
        pg_add(5, &rm);
        rm
    }
    /// FW_WINDOW_GROUPS: one EVJS ladder site with the window-group uses; rm: -1 remap before the swaps (cw), 1 after
    /// (V-win-out), 0 none
    fn fw_ladder(&self, t: i32, site: &str, cof: bool, rm: i8) -> GL {
        let (_, nk, grp) = *FW_GRP.iter().find(|s| s.0 == site).expect("FW: site");
        let ydone = |e: i32| grp.iter().any(|q| q.1 && (q.2 == e || q.2 + 1 == e));
        let xdone = |e: i32| grp.iter().any(|q| !q.1 && (q.2 == e || q.2 + 1 == e));
        for q in grp.iter() { assert!(lf(t, q.2) == if q.1 { (lf(t, q.2 + 1).0, lf(t, q.2).1) } else { (lf(t, q.2).0, lf(t, q.2 + 1).1) }, "FW: group does not share its window"); }
        let (g, kp) = self.ladder_h(site, &|set, c| {
            let e = set[0];
            assert!(set.len() == 1, "FW: singleton ladder sets only");
            let (l, f) = lf(t, e);
            let mut r: GL = vec![];
            if rm < 0 { r.extend(self.fw_rmb(c, e)); }
            r.extend(self.fw_ejs(l, f, c, cof, !ydone(e), !xdone(e)));
            if rm > 0 { r.extend(self.fw_rmb(c, e)); }
            r
        }, &|kp, lane| {
            let mut g: GL = vec![];
            for q in grp.iter().filter(|q| q.0 as usize == kp) {
                let prep: GL = q.4.iter().map(|op| match *op {
                    LOp::X(a) => gx(lane(a)),
                    LOp::Cx(a, b) => gc(lane(a), lane(b)),
                    LOp::Ccx(a, b, c) => gt(lane(a), lane(b), lane(c)),
                    LOp::U(..) => panic!("FW: a use in a prep"),
                }).collect();
                let (l, f) = lf(t, q.2);
                g.extend_from_slice(&prep);
                g.extend(self.fw_ejs(l, f, lane(q.3), cof, q.1, !q.1));
                g.extend(rev(&prep));
            }
            g
        });
        assert!(kp == nk, "FW: kept-op count of {site} changed: the plan positions are stale");
        g
    }
    /// FW_WINDOW_GROUPS: the e = 0 and e = 1 brackets of an EVJS site with their shared Y window (l(0) = l(1)):
    /// D = sp0 (X of e = 0), D = sp0 ^ sp1 (Y of both: the cubes differ in h0), D = sp1 (X of e = 1), D = 0
    fn fw_e01(&self, t: i32, cof: bool, sp0: &[Lit], s1: &[Vec<Lit>], d: u32, zf: u32) -> GL {
        let ((l0, f0), (l1, f1)) = (lf(t, 0), lf(t, 1));
        assert!(l0 == l1, "FW: e = 0 and e = 1 do not share l");
        assert!(sp0.iter().any(|a| s1.iter().all(|c| c.contains(&(a.0, !a.1)))), "FW: sp0 and the e = 1 cubes are not disjoint");
        let fl0 = self.mz(sp0, d, zf);
        let fl1: GL = s1.iter().flat_map(|l_| self.mz(l_, d, zf)).collect();
        pg_add(4, &fl0); pg_add(4, &fl0); pg_add(4, &fl1); pg_add(4, &fl1);
        let mut g: GL = vec![];
        g.extend_from_slice(&fl0);
        g.extend(self.fw_ejs(l0, f0, d, cof, false, true));
        g.extend_from_slice(&fl1);
        g.extend(self.fw_ejs(l0, f0, d, cof, true, false));
        g.extend_from_slice(&fl0);
        g.extend(self.fw_ejs(l1, f1, d, cof, false, true));
        g.extend_from_slice(&fl1);
        g
    }
    /// LEVER2 demux walk: for every group (value v of the 4 bits ub, LSB first; leaf cubes ex; use gates on control d):
    /// d = cl AND [ub == v] AND cube around the use. fa = Some(F): A = cl & ub3 ub2 on F (aux ZB), B = A & ub1 on ZB,
    /// leaf = B & ub0; fa = None: A = cl & ub3 ub2 on ZB, leaf = A & ub1 & ub0 (Barenco while ZB holds A).
    fn demux(&self, cl: &[Lit], ub: &[u32], groups: &mut Vec<(i32, Vec<Vec<Lit>>, GL)>, d: u32, fa: Option<u32>) -> GL {
        let zb = ZB_LANE;
        let bt = |v: i32, i: usize| -> bool { (v >> i) & 1 == 1 };
        groups.sort_by_key(|x| x.0);
        let (mut g, mut fl): (GL, GL) = (vec![], vec![]);
        let a_g = |me: &Self, v: i32| -> GL {
            let mut l = cl.to_vec();
            l.push((ub[3], bt(v, 3)));
            l.push((ub[2], bt(v, 2)));
            match fa {
                Some(f) => me.m(&l, f),
                None => {
                    // A on ZB with d (clean here: no leaf is up) as the AND's aux lane: 2k - 3 instead of Barenco
                    if SLIDE_LAD_CA && hmr_aux() && IN_F.load(Ordering::Relaxed) && l.len() >= 3 {
                        mac_aux(&l, zb, d)
                    } else if SLIDE_LAD_CA {
                        let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
                        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
                        let mut q = pre.clone();
                        q.extend(cc_core(&cs, zb, d));
                        q.extend(pre);
                        q
                    } else {
                        me.m(&l, zb)
                    }
                }
            }
        };
        let b_g = |me: &Self, v: i32| -> GL { me.m(&[(fa.unwrap(), true), (ub[1], bt(v, 1))], zb) };
        let (mut ca, mut cb): (Option<i32>, Option<i32>) = (None, None);
        for (v, ex, us) in groups.iter() {
            let v = *v;
            if ca != Some(v >> 2) {
                if let Some(b0) = cb.take() { let q = b_g(self, b0 << 1); fl.extend_from_slice(&q); g.extend(q); }
                if let Some(a0) = ca { let q = a_g(self, a0 << 2); fl.extend_from_slice(&q); g.extend(q); }
                let q = a_g(self, v);
                fl.extend_from_slice(&q);
                g.extend(q);
                ca = Some(v >> 2);
            }
            if fa.is_some() && cb != Some(v >> 1) {
                if let Some(b0) = cb { let q = b_g(self, b0 << 1); fl.extend_from_slice(&q); g.extend(q); }
                let q = b_g(self, v);
                fl.extend_from_slice(&q);
                g.extend(q);
                cb = Some(v >> 1);
            }
            let base: Vec<Lit> = if fa.is_some() { vec![(zb, true), (ub[0], bt(v, 0))] } else { vec![(zb, true), (ub[1], bt(v, 1)), (ub[0], bt(v, 0))] };
            let mut lf: GL = vec![];
            ZB_BUSY.store(true, Ordering::Relaxed);
            for c in ex {
                let mut l = base.clone();
                l.extend_from_slice(c);
                lf.extend(self.m(&l, d));
            }
            ZB_BUSY.store(false, Ordering::Relaxed);
            fl.extend_from_slice(&lf);
            fl.extend_from_slice(&lf);
            g.extend_from_slice(&lf);
            g.extend_from_slice(us);
            g.extend(lf);
        }
        if let Some(b0) = cb { let q = b_g(self, b0 << 1); fl.extend_from_slice(&q); g.extend(q); }
        if let Some(a0) = ca { let q = a_g(self, a0 << 2); fl.extend_from_slice(&q); g.extend(q); }
        pg_add(4, &fl);
        g
    }
    /// MAP765_v2 physical lane -> frame label at the boundary below slot CUT_T (paged, narrowed): YH 0..224, VA 225..240,
    /// VB 241..254 + 512, 513, PAR 255, PAS 256..511, XH 514..738, SC 739..754, h 755, 756, W4 757 + spares 758..762 (freed[0..6]),
    /// ZB 763, F 764; then (test only, >= 765) every other allocated lane in increasing order (T2, the other freed lanes, ...).
    fn phys765(&self, nl: u32) -> Vec<u32> {
        assert!(PAGE_G && PAGE_N && PAGE_DI == 16 && self.wr == 225, "phys765 needs the D16 narrowed frame");
        let (d, pg) = (PAGE_DI, &self.pg);
        let mut t: Vec<u32> = vec![NONE; 765];
        for i in 0..225 {
            t[i] = self.y[i];
            t[514 + i] = self.x[i];
        }
        for j in 0..16 {
            t[225 + j] = pg[j];
            t[739 + j] = pg[2 * d + j];
        }
        for j in 0..14 {
            t[241 + j] = pg[d + j];
        }
        t[512] = pg[d + 14];
        t[513] = pg[d + 15];
        t[255] = self.par;
        for i in 0..256 {
            t[256 + i] = self.pas[i];
        }
        t[755] = self.e[0];
        t[756] = self.e[1];
        for i in 0..6 {
            t[757 + i] = self.freed[i];
        }
        t[763] = pg[4 * d + 1];
        t[764] = pg[4 * d];
        assert!(t.iter().all(|&q| q != NONE));
        let used: BTreeSet<u32> = t.iter().cloned().collect();
        assert_eq!(used.len(), 765, "phys765: lanes not distinct");
        for q in 0..nl {
            if !used.contains(&q) {
                t.push(q);
            }
        }
        t
    }
    fn mk(&self, t: i32, k: i32) {
        if DBG_T.load(Ordering::Relaxed) == t {
            DBG_M.lock().unwrap().push((100000 + k, self.b.gates.len()));
        }
    }
    fn m(&self, l: &[Lit], t: u32) -> GL {
        mcx(l, t, &self.dirty)
    }
    fn hl(&self, v: i32) -> Vec<Lit> {
        (0..EB).map(|i| (self.e[i], (v >> i) & 1 == 1)).collect()
    }
    fn init(&mut self) {
        r7e_tag("init");
        let mut g: GL = vec![gx(self.x[0])];
        for i in 0..N {
            if pbit(i) {
                g.push(gx(self.x[i + 1]));
            }
        }
        let xl: Vec<u32> = self.y[2..].to_vec();
        for &q0 in &xl {
            g.push(gc(self.par, q0));
        }
        let cl = self.e[0];
        for &i in &C0M1 {
            g.extend(rev(&inc_long(&xl[i..], self.par, &self.dirty, cl)));
        }
        self.b.t(&g);
    }
    #[allow(clippy::too_many_arguments)]
    fn row(&self, t: &[u32], s: &[u32], top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>) -> GL {
        let n = t.len();
        let mut g: GL = Vec::with_capacity(12 * n);
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        if top != NONE {
            conj.push(gx(top));
        }
        g.extend_from_slice(&conj);
        let wend = match inline {
            Some(il) => il.keys().next_back().map(|k| k + 1).unwrap_or(0),
            None => tog.keys().next_back().map(|k| k + 1).unwrap_or(0),
        };
        let gate3 = |g: &mut GL, a0: u32, a1: u32, tgt: u32, i: usize| {
            if let Some(il) = inline {
                for li in &il[&i] {
                    let mut l = vec![(a0, true), (a1, true)];
                    l.extend_from_slice(li);
                    g.extend(self.m(&l, tgt));
                }
            } else {
                g.extend(self.m(&[(a0, true), (a1, true), (m, true)], tgt));
            }
        };
        for i in 0..n {
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
            g.push(gc(c, s[i]));
            g.push(gc(c, t[i]));
            if i < wend {
                gate3(&mut g, s[i], t[i], c, i);
            } else {
                g.push(gt(s[i], t[i], c));
            }
        }
        for li in active {
            g.extend(self.m(li, d));
        }
        if top != NONE {
            for li in active {
                let mut l = li.clone();
                l.extend_from_slice(&[(c, true), (top, true)]);
                g.extend(self.m(&l, d));
            }
            g.push(gt(d, c, top));
        } else {
            for li in active {
                let mut l = li.clone();
                l.push((c, true));
                g.extend(self.m(&l, d));
            }
        }
        for i in (0..n).rev() {
            if i < wend {
                gate3(&mut g, s[i], t[i], c, i);
            } else {
                g.push(gt(s[i], t[i], c));
            }
            g.push(gc(c, t[i]));
            if i < wend {
                gate3(&mut g, d, s[i], t[i], i);
            } else {
                g.push(gt(d, s[i], t[i]));
            }
            g.push(gc(c, s[i]));
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
        }
        g.extend_from_slice(&conj);
        g
    }
    #[allow(clippy::too_many_arguments)]
    /// PK3_SW3B / PK3_L3BS: even11's E3C big rows. Both off: row_v, byte for byte.
    #[allow(clippy::too_many_arguments)]
    fn row_big(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], cv: Option<&GL>) -> GL {
        if !(PK3_SW3B || PK3_L3BS) {
            return self.row_v(t, s, t1, top, d, c, m, tog, active, None, cv);
        }
        let zl = [d, c, m, t1, top];
        let share = PK3_SW3B && ZB > 0 && m != NONE && !ZB_BUSY.load(Ordering::Relaxed)
            && !zl.contains(&ZB_LANE) && !t.contains(&ZB_LANE) && !s.contains(&ZB_LANE);
        let mut written: Vec<u32> = t.iter().chain(s.iter()).cloned().collect();
        written.extend_from_slice(&zl);
        let l3 = PK3_L3BS && cv.is_none() && m != NONE && self.pg.len() > 4 * PAGE_D && m == self.pg[4 * PAGE_D]
            && !active.iter().flatten().any(|x| x.0 == m) && pk3_cum_one(tog, t.len(), &written);
        if l3 {
            let last = *tog.keys().next_back().unwrap();
            let mut t2 = tog.clone();
            t2.insert(last, vec![]);
            PK3_CNT[1].fetch_add(1, Ordering::Relaxed);
            if share { PK3_CNT[0].fetch_add(1, Ordering::Relaxed); }
            return self.row_vzr_impl2(t, s, t1, top, d, c, m, &t2, active, None, cv, false, NONE, &[], share, Some(last));
        }
        if share { PK3_CNT[0].fetch_add(1, Ordering::Relaxed); }
        self.row_vzr_impl2(t, s, t1, top, d, c, m, tog, active, None, cv, false, NONE, &[], share, None)
    }
    fn row_v(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>) -> GL {
        self.row_vz(t, s, t1, top, d, c, m, tog, active, inline, cv, false)
    }
    fn row_vz(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>, nz: bool) -> GL {
        self.row_vzx(t, s, t1, top, d, c, m, tog, active, inline, cv, nz, NONE)
    }
    #[allow(clippy::too_many_arguments)]
    fn row_vzx(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>, nz: bool, xh1: u32) -> GL {
        self.row_vzr(t, s, t1, top, d, c, m, tog, active, inline, cv, nz, xh1, &[])
    }
    /// SW3R is called ONLY by even11's ordinary V loop, including E3V shared rows.
    #[allow(clippy::too_many_arguments)]
    fn row_vmask(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], nz: bool) -> GL {
        // SW3R's checked domain is the mid region's D11 page layout (pg = VA, VB, SC, T2 x 11 + F + ZB: the 176 even
        // slots of its census). The full-width outer slots (D16 page, 66 lanes, m = pg[44] is not F there) keep the parent row.
        if !SW3R_VMASK || self.pg.len() != 4 * PAGE_D + 2 {
            return self.row_vz(t, s, t1, top, d, c, m, tog, active, None, None, nz);
        }
        assert!(PAGE_G && PAGE_N && PAGE_D == 11 && ZB > 0 && togv_on());
        assert!(m == self.pg[4 * PAGE_D] && self.pg[4 * PAGE_D + 1] == ZB_LANE);
        assert!(!ZB_BUSY.load(Ordering::Relaxed));
        assert!(![d, c, m, t1, top].contains(&ZB_LANE));
        assert!(!t.contains(&ZB_LANE) && !s.contains(&ZB_LANE));
        if SM_L3B {
            if let Some(&last) = tog.keys().next_back() {
                // cumulative XOR of every toggle cube (zero cubes dropped, literals sorted and deduplicated)
                let mut cum: std::collections::BTreeSet<Vec<Lit>> = std::collections::BTreeSet::new();
                for cubes in tog.values() {
                    for cb in cubes {
                        let mut v: Vec<Lit> = cb.clone();
                        v.sort();
                        v.dedup();
                        if v.windows(2).any(|w| w[0].0 == w[1].0) { continue; }
                        if !cum.remove(&v) { cum.insert(v); }
                    }
                }
                if last < t.len() && cum.len() == 1 && cum.contains(&Vec::<Lit>::new()) {
                    let mut tog2 = tog.clone();
                    tog2.remove(&last);
                    return self.row_vzr_impl2(t, s, t1, top, d, c, m, &tog2, active, None, None, nz, NONE, &[], true, Some(last));
                }
            }
        }
        self.row_vzr_impl(t, s, t1, top, d, c, m, tog, active, None, None, nz, NONE, &[], true)
    }
    /// NR_PARK_V: swap(a, b) when the cube holds. The cube reads neither lane. aux: a lane that is clean here (mclean), or
    /// NONE for the frame's own MCX form.
    fn nr_cswap_cube(&self, cube: &[Lit], a: u32, b: u32, aux: u32) -> GL {
        assert!(a != b && !cube.iter().any(|x| x.0 == a || x.0 == b), "NR_PARK_V: the cube reads a swapped lane");
        let mut l: Vec<Lit> = cube.to_vec();
        l.push((a, true));
        let mut g: GL = vec![gc(b, a)];
        g.extend(if aux == NONE { self.m(&l, b) } else { self.mclean(&l, b, aux) });
        g.push(gc(b, a));
        g
    }
    /// NR_PARK_V: the park list of even slot t, emitted before V row 2; its reverse is emitted after V row 9.
    fn nr_park_v(&self, t: i32) -> GL {
        let wv = self.wr;
        let y = &self.y;
        let (h1, w1, x0) = (self.e[1], self.w1, self.x[0]);
        let (yt, f) = (y[wv - 1], self.pg[4 * PAGE_D]);
        assert!(self.pg.len() == 4 * PAGE_D + 2 && self.pg[4 * PAGE_D + 1] == ZB_LANE && !ZB_BUSY.load(Ordering::Relaxed));
        let base = wv - (t / 2) as usize;
        // the zone lanes sit above the class register y[1..=8] and below the row tops
        assert!(base + 1 > 8 && base + 3 < wv - 11, "NR_PARK_V: zone lanes out of range");
        let zl = [y[base + 1], y[base + 2], y[base + 3]];
        let mut g = self.m(&[(yt, true), (h1, true), (y[1], false), (y[2], false)], f);
        g.extend(self.nr_cswap_cube(&[(f, true), (w1, false)], zl[0], y[1], NONE));
        g.extend(self.nr_cswap_cube(&[(f, true), (w1, true), (y[3], false), (y[4], false)], zl[0], y[1], NONE));
        g.extend(self.nr_cswap_cube(&[(f, true), (w1, false), (y[3], false), (y[4], false)], zl[1], y[2], NONE));
        g.extend(self.nr_cswap_cube(&[(f, true), (w1, true), (y[3], false), (y[4], false), (y[5], false), (y[6], false)], zl[1], y[2], NONE));
        // the third bit goes onto ZB itself: x0 is the clean lane of this MCX (x0 is 0 between rows)
        g.extend(self.nr_cswap_cube(&[(f, true), (w1, false), (y[3], false), (y[4], false), (y[5], false), (y[6], false)], zl[2], ZB_LANE, x0));
        g
    }
    /// NR_PARK_V: a restoring V row with plain cells (no mask, no toggles) and the pairwise disjoint act cubes `acts`.
    /// Same gate order as row_vzr_impl with m = NONE; called with ZB_BUSY set, so the first decision MCX takes d = x0
    /// (clean before the decision) as its AND lane and the later ones take the dirty form.
    fn nr_row_plain(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, acts: &[Vec<Lit>]) -> GL {
        assert!(top != NONE && ZB_BUSY.load(Ordering::Relaxed));
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        let mut g: GL = Vec::with_capacity(8 * n + 64);
        g.extend_from_slice(&conj);
        for i in 0..n {
            g.push(gc(c, s[i]));
            g.push(gc(c, t[i]));
            g.push(gt(s[i], t[i], c));
        }
        for li in acts {
            let mut a2: Vec<Lit> = li.clone();
            a2.extend_from_slice(&[(c, false), (t1, false)]);
            g.extend(self.mclean(&a2, top, d));
        }
        for li in acts {
            let mut a3: Vec<Lit> = li.clone();
            a3.push((top, true));
            g.extend(self.m(&a3, d));
        }
        g.extend(self.m(&[(d, true), (c, false)], t1));
        for i in (0..n).rev() {
            g.push(gt(s[i], t[i], c));
            g.push(gc(c, t[i]));
            g.push(gt(d, s[i], t[i]));
            g.push(gc(c, s[i]));
        }
        g.extend_from_slice(&conj);
        g
    }
    /// row_vzx with a mask reset: rst (cubes on m) is applied right before and right after the decision block, so the act
    /// cubes see m at its entry value (E3C: the mask y1 is read by lik; rst = the XOR of the last wire's toggle cubes).
    #[allow(clippy::too_many_arguments)]
    fn row_vzr(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>, nz: bool, xh1: u32, rst: &[Vec<Lit>]) -> GL {
        self.row_vzr_impl(t, s, t1, top, d, c, m, tog, active, inline, cv, nz, xh1, rst, false)
    }
    #[allow(clippy::too_many_arguments)]
    fn row_vzr_impl(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>, nz: bool, xh1: u32, rst: &[Vec<Lit>], share_vmask: bool) -> GL {
        self.row_vzr_impl2(t, s, t1, top, d, c, m, tog, active, inline, cv, nz, xh1, rst, share_vmask, None)
    }
    /// wcut: SM_L3B, masked cells are i < wcut (the dropped last key) instead of i < last key + 1.
    #[allow(clippy::too_many_arguments)]
    fn row_vzr_impl2(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>, nz: bool, xh1: u32, rst: &[Vec<Lit>], share_vmask: bool, wcut: Option<usize>) -> GL {
        let n = t.len();
        let mut g: GL = Vec::with_capacity(12 * n);
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        g.extend_from_slice(&conj);
        let wend = match inline {
            Some(il) => il.keys().next_back().map(|k| (k + 1).min(n)).unwrap_or(0),
            None => tog.keys().next_back().map(|k| (k + 1).min(n)).unwrap_or(0),
        };
        let wend = match wcut { Some(w) => w.min(wend), None => wend };
        if let Some(cg) = cv {
            g.extend_from_slice(cg);
        }
        // BK_L3B_E3: the cell at the dropped last key runs plain
        let wend = { let wc = BK_WCUT.load(Ordering::Relaxed); if BK_L3B_E3 && wc != usize::MAX { wc.min(wend) } else { wend } };
        for i in 0..n {
            if inline.is_none() || m != NONE {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.mz(l, m, d));
                    }
                }
            }
            g.push(gc(c, s[i]));
            g.push(gc(c, t[i]));
            if i < wend && inline.is_some() {
                for li in &inline.unwrap()[&i] {
                    let mut l = vec![(s[i], true), (t[i], true)];
                    l.extend_from_slice(li);
                    g.extend(if nz { self.m(&l, c) } else { self.mz(&l, c, d) });
                }
            } else if m != NONE && i < wend {
                g.extend(self.mz(&[(s[i], true), (t[i], true), (m, true)], c, d));
            } else {
                g.push(gt(s[i], t[i], c));
            }
        }
        if let Some(cg) = cv {
            g.extend(rev(cg));
        }
        for l in rst {
            g.extend(self.m(l, m));
        }
        if top != NONE {
            for li in active {
                let mut a2: Vec<Lit> = li.clone();
                a2.extend_from_slice(&[(c, false), (t1, false)]);
                g.extend(self.mz(&a2, top, d));
            }
            for li in active {
                let mut a3: Vec<Lit> = li.clone();
                a3.push((top, true));
                g.extend(self.m(&a3, d));
            }
        } else {
            for li in active {
                let mut a2: Vec<Lit> = li.clone();
                a2.extend_from_slice(&[(c, false), (t1, false)]);
                g.extend(self.m(&a2, d));
            }
        }
        for l in rst {
            g.extend(self.m(l, m));
        }
        if xh1 != NONE {
            g.extend(self.m(&[(d, true), (xh1, false), (c, true)], top));
            g.extend(self.m(&[(d, true), (xh1, false), (c, false), (t1, true)], top));
        }
        g.extend(self.m(&[(d, true), (c, false)], t1));
        if let Some(cg) = cv {
            g.extend_from_slice(cg);
        }
        for i in (0..n).rev() {
            if share_vmask && inline.is_none() && m != NONE && i < wend {
                // ZB = s[i] & m. The two controls stay unchanged until release.
                // No MCX, toggle, or source-write occurs inside this bracket.
                g.extend(and2(s[i], m, ZB_LANE));
                g.push(gt(ZB_LANE, t[i], c));
                g.push(gc(c, t[i]));
                g.push(gt(d, ZB_LANE, t[i]));
                g.extend(and2(s[i], m, ZB_LANE));
                g.push(gc(c, s[i]));
            } else {
                if i < wend && inline.is_some() {
                    for li in &inline.unwrap()[&i] {
                        let mut l = vec![(s[i], true), (t[i], true)];
                        l.extend_from_slice(li);
                        g.extend(self.m(&l, c));
                    }
                } else if m != NONE && i < wend {
                    g.extend(self.m(&[(s[i], true), (t[i], true), (m, true)], c));
                } else {
                    g.push(gt(s[i], t[i], c));
                }
                g.push(gc(c, t[i]));
                if i < wend && inline.is_some() {
                    for li in &inline.unwrap()[&i] {
                        let mut l = vec![(d, true), (s[i], true)];
                        l.extend_from_slice(li);
                        g.extend(self.m(&l, t[i]));
                    }
                } else if m != NONE && i < wend {
                    g.extend(self.m(&[(d, true), (s[i], true), (m, true)], t[i]));
                } else {
                    g.push(gt(d, s[i], t[i]));
                }
                g.push(gc(c, s[i]));
            }
            if inline.is_none() || m != NONE {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
        }
        if let Some(cg) = cv {
            g.extend(rev(cg));
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain_vt(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        conj.push(gx(top));
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        g.extend(self.m(&[(d, true), (c, true)], top));
        g.extend(self.m(&[(d, true), (c, false), (t1, true)], top));
        g.extend(self.m(&[(d, true), (c, false)], t1));
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain_v(&self, t: &[u32], s: &[u32], t1: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        g.extend(self.m(&[(d, true), (c, false)], t1));
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain(&self, t: &[u32], s: &[u32], top: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        if top != NONE {
            conj.push(gx(top));
        }
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        if top != NONE {
            g.push(gt(d, c, top));
        }
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn pi_gates(&self, t: i32, cc: u32, f1: u32, f2: u32, f3: u32) -> GL {
        let l = ((t - 1).div_euclid(2)) as usize;
        let x = &self.x;
        let mut y: Vec<u32> = self.y[1..].to_vec();
        y.push(self.y[0]);
        let last = |v: Vec<usize>| -> Vec<usize> {
            let k = v.len().saturating_sub(PIW);
            v[k..].to_vec()
        };
        let mut g = vec![];
        // the top lane of this frame is a known zero (it holds the act flag): only its carry-out matters
        let idx = {
            let v: Vec<usize> = ((W - l)..(W - 1)).collect();
            let k = v.len().saturating_sub(PIW - 1);
            v[k..].to_vec()
        };
        let mut fw = vec![];
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.push(gt(cc, x[W - 1], f1));
        g.extend(rev(&fw));
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.extend_from_slice(&[gc(cc, f2), gc(x[1], f2), gc(y[1], f2)]);
        g.extend(rev(&fw));
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w - 1])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, y[w]), gc(cc, x[w - 1]), gt(y[w], x[w - 1], cc)]);
        }
        g.extend_from_slice(&fw);
        g.push(gt(cc, y[1], f3));
        g.extend(rev(&fw));
        g
    }
    fn flag_e(&self, fl: u32, xt: u32, y: &[u32]) -> GL {
        let h = &self.e;
        let ctl = self.x[0];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        // act shots, hi=0: xt -> 15; not xt, y0=1 -> 13; not xt, y0=0 -> stays 0
        let mut g = self.m(&cat(&[(fl, true), (xt, true)], &self.hl(0)), ctl);
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hl(0)), ctl));
        g.extend_from_slice(&[gc(ctl, h[0]), gc(ctl, h[2]), gc(ctl, h[3])]);
        g.extend(self.m(&[(ctl, true), (xt, true)], h[1]));
        g.extend(self.m(&cat(&[(fl, true), (xt, true), (y[0], true)], &self.hl(15)), ctl));
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hl(13)), ctl));
        g
    }
    /// L3: MCX onto t with aux a lane known clean here (cc_core, 2k - 3), whatever ZB is doing; mcx's literal merging.
    fn mclean(&self, l0: &[Lit], t: u32, aux: u32) -> GL {
        let mut l: Vec<Lit> = Vec::with_capacity(l0.len());
        for &(q0, p) in l0 {
            match l.iter().find(|x| x.0 == q0) {
                Some(x) => { if x.1 != p { return vec![]; } }
                None => l.push((q0, p)),
            }
        }
        if l.len() < 3 { return self.m(&l, t); }
        assert!(aux != t && !l.iter().any(|x| x.0 == aux || x.0 == t), "mclean: aux or target among the controls");
        if hmr_aux() && IN_F.load(Ordering::Relaxed) { return mac_aux(&l, t, aux); }
        let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        let mut g = pre.clone();
        g.extend(cc_core(&cs, t, aux));
        g.extend_from_slice(&pre);
        g
    }
    /// As m, with z a lane that is clean here: AND of k controls in 2k-3 T.
    fn mz(&self, l0: &[Lit], t: u32, z: u32) -> GL {
        let mut l: Vec<Lit> = Vec::with_capacity(l0.len());
        for &(q0, p) in l0 {
            match l.iter().find(|x| x.0 == q0) {
                Some(x) => {
                    if x.1 != p {
                        return vec![];
                    }
                }
                None => l.push((q0, p)),
            }
        }
        if l.len() < 3 || ZB > 0 {
            return self.m(l0, t);
        }
        let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        let mut g = pre.clone();
        g.extend(cc_core(&cs, t, z));
        g.extend_from_slice(&pre);
        g
    }
    fn hc(&self, c: i32) -> Vec<Lit> {
        vec![(self.e[0], c & 1 == 1), (self.e[1], (c >> 1) & 1 == 1)]
    }
    fn page_alloc(&mut self) {
        if PAGE || PAGE_V || PAGE_C || PAGE_G {
            self.pg = (0..4 * PAGE_DI + 1).map(|_| self.b.alloc()).collect();
            // Z of the sandwich: the frame's clean AND lane when ZB is on (MAP765: 3 clean lanes X[0], F, ZB)
            let z = if ZB > 0 { ZB_LANE } else { self.b.alloc() };
            self.pg.push(z);
        }
    }
    /// One clock value: the P1 format switches at the cuts, then the slot.
    fn tick(&mut self, t: i32) {
        self.cut(t);
        self.slot(t);
    }
    /// the P1 / P5 format switches at the cuts (before slot t)
    fn cut(&mut self, t: i32) {
        r7e_tag("cut_page");
        if PAGE && PAGE_CUTS.contains(&t) {
            let g = self.page_in(t);
            self.b.t(&g);
            self.b.t(&rev(&g));
        }
        if PAGE_G && t == CUT_S - 1 {
            let g = self.page_in(CUT_S - 1);
            if !(ASM_START_PAGED && gl_loader::has(gl_loader::At::Start)) {
                self.b.t(&g);
            }
            if PAGE_N {
                self.freed = self.x[WHI..].to_vec();
                self.freed.extend_from_slice(&self.y[WHI..]);
                self.x.truncate(WHI);
                self.y.truncate(WHI);
                self.wr = WHI;
                if TIER_LONG > 0 && !W4HOST {
                    self.w4 = self.freed[0];
                }
                if CAD4 {
                    self.w1 = self.freed[0];
                }
            }
            if CONV {
                self.conv_fwd(CUT_S - 1);
            }
            assert!(TIER_LONG == 0 || (PAGE_N && CUT_S % 16 == 0 && CUT_T % 16 == 0), "L-C needs PAGE_N and cuts 0 mod 16");
        }
        if PAGE_G && t == CUT_T - 1 {
            if PAGE_N {
                assert!(self.wr == WHI, "re-widen from the interface width");
                let fx = self.freed[..W - WHI].to_vec();
                let fy = self.freed[W - WHI..].to_vec();
                self.x.extend_from_slice(&fx);
                self.y.extend_from_slice(&fy);
                self.wr = W;
                self.w4 = NONE;
                self.w1 = NONE;
            }
            let g = rev(&self.page_in(CUT_T - 1));
            self.b.t(&g);
        }
    }
    /// The terms (literal sets, pairwise disjoint) that say "this shot has F = f" at the boundary below slot T + 1,
    /// one entry per f, with E = 2 f - T (odd). Layout facts: notes v3/KT7_progress.md (step 3 groundwork) and
    /// v5/team40/p1/cutlay.py, cutfeat.py: code h0 h1 = 00 -> E = 1; 10 -> E = -1 (yt = 0) or a big shot that waits
    /// (r = 0, e = E >= 11, yt = 1, marker Y[E-1], offset bits Y[4..6]); 01 -> E >= 3, marker Y[E-1], zero below;
    /// 11 -> E <= -3, marker Y[W+E-g], zero above it, g = top zeros of ring X (0 or 1).
    fn page_cases(&self, tt: i32) -> Vec<(i32, Vec<Vec<Lit>>)> {
        self.page_cases_xy(&self.x, &self.y, tt)
    }
    fn page_cases_xy(&self, x: &[u32], y: &[u32], tt: i32) -> Vec<(i32, Vec<Vec<Lit>>)> {
        let h = &self.e;
        let (h0, h1) = (h[0], h[1]);
        let yt = y[W - 1];
        let wi = W as i32;
        let mut out = vec![];
        for ee in (-29..=25).filter(|v: &i32| v.rem_euclid(2) == 1) {
            let f = (tt + ee) / 2;
            let mut terms: Vec<Vec<Lit>> = vec![];
            if ee == 1 {
                terms.push(vec![(h0, false), (h1, false)]);
            } else if ee == -1 {
                terms.push(vec![(h0, true), (h1, false), (yt, false)]);
            } else if ee >= 3 {
                let mut l = vec![(h0, false), (h1, true), (y[ee as usize - 1], true)];
                for j in (2..=(ee - 3)).step_by(2) {
                    l.push((y[j as usize], false));
                }
                terms.push(l);
                if ee >= 11 {
                    let mut l = vec![(h0, true), (h1, false), (yt, true), (y[ee as usize - 1], true)];
                    for j in (10..=(ee - 3)).step_by(2) {
                        l.push((y[j as usize], false));
                    }
                    terms.push(l);
                }
            } else {
                for g in 0..=1 {
                    let mk = (wi + ee - g) as usize;
                    let mut l = vec![(h0, true), (h1, true), (y[mk], true)];
                    for j in (mk + 1)..W {
                        l.push((y[j], false));
                    }
                    if g == 0 {
                        l.push((x[W - 1], true));
                    } else {
                        l.extend_from_slice(&[(x[W - 1], false), (x[W - 2], true)]);
                    }
                    terms.push(l);
                }
            }
            out.push((f, terms));
        }
        out
    }
    /// Format switch explicit -> paged at the boundary below slot tt + 1: gather A, B, tB, tA low words of every
    /// shot into VA, VB, T1, T2 (one case per F, flag on X[0] which is tB's leading one, flipped to 0), select
    /// SC = T1 by the parity of B (B even: SC = tA_low), and erase the implicit word T2 with
    /// T2 = T2 * pivot + other * SC - p = 0 mod 2^D (A tB + B tA = p). The ring lanes of the four words are left 0.
    fn page_in(&self, tt: i32) -> GL {
        let d = PAGE_DI;
        let (x, y) = (&self.x, &self.y);
        let (va, vb, t1, t2) = (&self.pg[0..d], &self.pg[d..2 * d], &self.pg[2 * d..3 * d], &self.pg[3 * d..4 * d]);
        let x0 = x[0];
        let wi = W as i32;
        let mut g: GL = vec![gx(x0)];
        for (f, terms) in self.page_cases(tt) {
            let bx = wi - f;
            let by = (wi - tt + f).rem_euclid(wi);
            let mut fl: GL = vec![];
            for l in &terms {
                fl.extend(self.m(l, x0));
            }
            g.extend_from_slice(&fl);
            // with PAGE_N the compaction below moves every lane above a hole down 2D, top-referenced literals included:
            // the flag is uncomputed with the literals moved the same way
            let mut fl_post = fl.clone();
            if PAGE_N && PAGE_G {
                let (hx, hy) = ((bx - d as i32) as usize, (by - d as i32) as usize);
                let mv = |q0: u32| -> u32 {
                    if let Some(i) = x.iter().position(|&a| a == q0) { if i >= hx { return x[i - 2 * d]; } }
                    if let Some(i) = y.iter().position(|&a| a == q0) { if i >= hy { return y[i - 2 * d]; } }
                    q0
                };
                fl_post = vec![];
                for l in &terms {
                    let mut l2: Vec<Lit> = l.iter().map(|&(q0, v)| (mv(q0), v)).collect();
                    if l2 != *l {
                        // only a compacted shot has X[W-1] = X[W-2] = 0 (freed lanes); an uncompacted one has a 1 there
                        // (g = F - bl(A) <= 1, proof in P1_progress.md 00:55), so a moved term cannot fire on it
                        l2.extend_from_slice(&[(x[W - 1], false), (x[W - 2], false)]);
                    }
                    fl_post.extend(self.m(&l2, x0));
                }
            }
            for j in 0..d as i32 {
                cswap(x0, va[j as usize], x[(bx + j) as usize], &mut g);
                cswap(x0, t1[j as usize], x[(bx - 1 - j) as usize], &mut g);
                cswap(x0, vb[j as usize], y[(by + j).rem_euclid(wi) as usize], &mut g);
                cswap(x0, t2[j as usize], y[(by - 1 - j).rem_euclid(wi) as usize], &mut g);
            }
            if PAGE_N && PAGE_G {
                // close the holes: everything above a hole moves down 2D (top 2D lanes of each ring become 0)
                let sx: Vec<u32> = x[(bx - d as i32) as usize..].to_vec();
                g.extend(rotate_up(x0, &sx, sx.len() - 2 * d));
                assert!(by >= d as i32 && by <= wi - d as i32);
                let sy: Vec<u32> = y[(by - d as i32) as usize..].to_vec();
                g.extend(rotate_up(x0, &sy, sy.len() - 2 * d));
            }
            g.extend_from_slice(&fl_post);
        }
        g.extend(self.erase_blk_d(x0, PAGE_DI));
        g.push(gx(x0));
        g
    }
    /// CONV: the start-side D16 -> D11 converter on the narrowed D16 state.
    /// xf, yf: the explicit W-lane lists (narrowed ring ++ its freed tops) that page_cases reads; pg16: the D16 page
    /// (VA, VB, SC, T2, F, ZB); spares: 5 lanes clean on every paged shot; k: insertion index of the 10 lanes per ring.
    /// P = VA0 or VB0 (0 exactly on an unpaged all-zero page) sits on ZB for the lift and the route, then on F as a
    /// literal of every reopen flag (ZB is free for the flags' AND). Returns (gates, ring X list, ring Y list) at D11.
    fn conv_gates(&self, tt: i32, xf: &[u32], yf: &[u32], pg16: &[u32], spares: &[u32], k: (usize, usize)) -> (GL, Vec<u32>, Vec<u32>) {
        use self::window_prims::{self as wp, Cfg};
        let (d, dl) = (PAGE_DI, PAGE_D);
        let nl = d - dl;
        assert!(spares.len() == nl && xf.len() == W && yf.len() == W && pg16.len() == 4 * d + 2);
        let (va, vb, sc) = (&pg16[0..d], &pg16[d..2 * d], &pg16[2 * d..3 * d]);
        let (f, zb) = (pg16[4 * d], pg16[4 * d + 1]);
        assert_eq!(zb, ZB_LANE);
        let pon = |t: u32| -> GL { vec![gx(va[0]), gx(vb[0]), gt(va[0], vb[0], t), gx(va[0]), gx(vb[0]), gx(t)] };
        let (pz, pf) = (pon(zb), pon(f));
        // lift: spares ^= P & h[dl..d], h the implicit word (select F = [B even], K2 half, copy, undo)
        let mut sel: GL = vec![gx(vb[0]), gc(vb[0], f), gx(vb[0])];
        for j in 0..d { cswap(f, va[j], vb[j], &mut sel); }
        let (qa, qb, qc, qp) = (Self::qs(va), Self::qs(vb), Self::qs(sc), Self::qs(&self.pas[..64]));
        let mut pb = self::prims_builder::B::new();
        let k2 = Self::pgl(wp::rec(&mut pb, |b| {
            wp::idiv(b, Cfg::PY, &qa, &qb, &qp);
            wp::invp(b, Cfg::PY, &qb, &qp, wp::P256_LO, &[]);
            wp::undo(b, |b| wp::mac(b, Cfg::PY, &qb, &qa, &qc, &qp));
        }));
        let mut g: GL = pz.clone();
        g.extend_from_slice(&sel);
        let mut lift: GL = k2.clone();
        for kk in 0..nl { lift.push(gt(zb, vb[dl + kk], spares[kk])); }
        lift.extend(rev(&k2));
        if SW1_CONV_HOP {
            // SW1 converter adapter: 450.. VA, 466.. VB, 482.. SC (D16), 498.. passengers, 758 = ZB (holding P), 760.. spares
            let pas = self.pas.clone();
            let (va2, vb2, sc2, sp2) = (va.to_vec(), vb.to_vec(), sc.to_vec(), spares.to_vec());
            let m = move |q0: u32| -> u32 {
                match q0 {
                    NONE => NONE,
                    450..=465 => va2[(q0 - 450) as usize],
                    466..=481 => vb2[(q0 - 466) as usize],
                    482..=497 => sc2[(q0 - 482) as usize],
                    498..=753 => pas[(q0 - 498) as usize],
                    758 => zb,
                    760..=764 => sp2[(q0 - 760) as usize],
                    _ => panic!("SW1: converter packet lane {q0} outside the adapter"),
                }
            };
            let pp = sw1_packet(SW1_CONV_PARENT, "2ca44e52e7cce86897622c048ed656ae0324b1fecdaf1f61f5e792a293c1469f", &m);
            eprintln!("SW1CHK native converter lift vs converter_parent_lift: {}", sw1_same(&lift, &pp));
            lift = sw1_packet(SW1_CONV_PARKED, "cd768002616acbc2fba500a891a85f680b8d205a21d83ad9e3c08dba8bbd2c47", &m);
        }
        g.extend(lift);
        g.extend(rev(&sel));
        // route: F = P and [B even]; SC tops <-> spares, so SC tops = tB bits, spares = tA bits
        let fg: GL = vec![gx(vb[0]), gt(zb, vb[0], f), gx(vb[0])];
        g.extend_from_slice(&fg);
        for kk in 0..nl { cswap(f, sc[dl + kk], spares[kk], &mut g); }
        g.extend(rev(&fg));
        g.extend_from_slice(&pf);
        g.extend(rev(&pz));
        // the D11 ring lists: 10 lanes inserted at k (ring X: tB 15..11, A 11..15; ring Y: tA 15..11, B 11..15)
        let (x16, y16) = (&xf[..WHI], &yf[..WHI]);
        let mut nx: Vec<u32> = (0..nl).map(|kk| sc[d - 1 - kk]).collect();
        nx.extend((0..nl).map(|kk| va[dl + kk]));
        let mut ny: Vec<u32> = (0..nl).map(|kk| spares[nl - 1 - kk]).collect();
        ny.extend((0..nl).map(|kk| vb[dl + kk]));
        let (kx, ky) = k;
        let xe: Vec<u32> = x16[..kx].iter().chain(nx.iter()).chain(x16[kx..].iter()).copied().collect();
        let ye: Vec<u32> = y16[..ky].iter().chain(ny.iter()).chain(y16[ky..].iter()).copied().collect();
        // reopen: per case, flag (page_in(D11)'s moved terms read on xe / ye, plus P on F) and rotate the segment
        // between k and the shot's junction so that the 10 lanes land in the hole
        let x0 = xe[0];
        assert_eq!(x0, xf[0]);
        let wi = W as i32;
        let seg = |e: &[u32], j: usize, kk: usize| -> GL {
            if j >= kk {
                let s0 = &e[kk..j + 2 * nl];
                rotate_up(x0, s0, s0.len() - 2 * nl)
            } else {
                let s0 = &e[j..kk + 2 * nl];
                rotate_up(x0, s0, 2 * nl)
            }
        };
        let posx: HashMap<u32, usize> = xf.iter().enumerate().map(|(i, &q0)| (q0, i)).collect();
        let posy: HashMap<u32, usize> = yf.iter().enumerate().map(|(i, &q0)| (q0, i)).collect();
        g.push(gx(x0));
        for (fv, terms) in self.page_cases_xy(xf, yf, tt) {
            let bx = (wi - fv) as usize;
            let by = (wi - tt + fv).rem_euclid(wi) as usize;
            let (hx, hy) = (bx - dl, by - dl);
            let mv = |q0: u32| -> u32 {
                if let Some(&i) = posx.get(&q0) { return if i >= hx { xe[i - 2 * dl] } else { xe[i] }; }
                if let Some(&i) = posy.get(&q0) { return if i >= hy { ye[i - 2 * dl] } else { ye[i] }; }
                q0
            };
            let mut fl: GL = vec![];
            for l in &terms {
                let mut l2: Vec<Lit> = l.iter().map(|&(q0, v)| (mv(q0), v)).collect();
                l2.push((f, true));
                fl.extend(self.m(&l2, x0));
            }
            g.extend_from_slice(&fl);
            g.extend(seg(&xe, bx - d, kx));
            g.extend(seg(&ye, by - d, ky));
            g.extend_from_slice(&fl);
        }
        g.push(gx(x0));
        g.extend(rev(&pf));
        (g, xe, ye)
    }
    /// CONV: after page_in(tt) and the narrowing to WHI: emit the converter, move the frame to D11 lists and page.
    fn conv_fwd(&mut self, tt: i32) {
        r7e_tag("converters");
        let (d, dl) = (PAGE_DI, PAGE_D);
        assert!(PAGE_N && PAGE_G && self.wr == WHI && self.x.len() == WHI && self.pg.len() == 4 * d + 2);
        let xf: Vec<u32> = self.x.iter().chain(self.freed[..W - WHI].iter()).copied().collect();
        let yf: Vec<u32> = self.y.iter().chain(self.freed[W - WHI..].iter()).copied().collect();
        let pg16 = self.pg.clone();
        let s0 = if (TIER_LONG > 0 && !W4HOST) || CAD4 { 1 } else { 0 };
        if DS_PAGE_EDITS {
            assert!(s0 + d - dl <= W - WHI - 2, "converter spares reach the page_cases literals x[W-2], x[W-1]");
        } else {
            assert!(s0 + d - dl <= 6, "converter spares beyond the six kept freed lanes");
        }
        let spares: Vec<u32> = self.freed[s0..s0 + d - dl].to_vec();
        let (g, xe, ye) = self.conv_gates(tt, &xf, &yf, &pg16, &spares, CONV_K_S);
        eprintln!("conv: start converter at {}: {} gates, {} CCX (pre-MAC)", tt, g.len(), g.iter().filter(|q0| q0.2 != NONE).count());
        self.b.t(&g);
        self.cv_t2 = pg16[3 * d..4 * d].to_vec();
        self.cv_freed = self.freed.clone();
        self.cv_x16 = self.x.clone();
        self.cv_y16 = self.y.clone();
        self.cv_pg16 = pg16.clone();
        let mut pg: Vec<u32> = pg16[0..dl].to_vec();
        pg.extend_from_slice(&pg16[d..d + dl]);
        pg.extend_from_slice(&pg16[2 * d..2 * d + dl]);
        pg.extend_from_slice(&pg16[3 * d..3 * d + dl]);
        pg.push(pg16[4 * d]);
        pg.push(pg16[4 * d + 1]);
        self.pg = pg;
        self.x = xe;
        self.y = ye;
        self.wr = WH;
        self.freed = self.cv_freed[..s0].to_vec();
        assert!(self.x.len() == WH && self.y.len() == WH);
    }
    /// CONV: at the boundary below slot tt + 1 (before page_out(tt) / the tail list): the inverse converter on the
    /// current D11 lists, back to the D16 narrowed lists, page and freed tops.
    fn conv_back(&mut self, tt: i32) {
        r7e_tag("converters");
        let (d, dl) = (PAGE_DI, PAGE_D);
        let nl = d - dl;
        assert!(self.wr == WH && self.x.len() == WH && self.y.len() == WH && self.pg.len() == 4 * dl + 2);
        let (kx, ky) = CONV_K_T;
        let (xe, ye) = (self.x.clone(), self.y.clone());
        let (nx, ny) = (xe[kx..kx + 2 * nl].to_vec(), ye[ky..ky + 2 * nl].to_vec());
        let x16: Vec<u32> = xe[..kx].iter().chain(xe[kx + 2 * nl..].iter()).copied().collect();
        let y16: Vec<u32> = ye[..ky].iter().chain(ye[ky + 2 * nl..].iter()).copied().collect();
        let pg = self.pg.clone();
        let mut pg16: Vec<u32> = pg[0..dl].to_vec();
        pg16.extend_from_slice(&nx[nl..]);
        pg16.extend_from_slice(&pg[dl..2 * dl]);
        pg16.extend_from_slice(&ny[nl..]);
        pg16.extend_from_slice(&pg[2 * dl..3 * dl]);
        pg16.extend((0..nl).map(|kk| nx[nl - 1 - kk]));
        pg16.extend_from_slice(&self.cv_t2);
        pg16.push(pg[4 * dl]);
        pg16.push(pg[4 * dl + 1]);
        let spares: Vec<u32> = (0..nl).map(|kk| ny[nl - 1 - kk]).collect();
        let s0 = if (TIER_LONG > 0 && !W4HOST) || CAD4 { 1 } else { 0 };
        let mut freed: Vec<u32> = self.cv_freed[..s0].to_vec();
        freed.extend_from_slice(&spares);
        freed.extend_from_slice(&self.cv_freed[s0 + nl..]);
        let xf: Vec<u32> = x16.iter().chain(freed[..W - WHI].iter()).copied().collect();
        let yf: Vec<u32> = y16.iter().chain(freed[W - WHI..].iter()).copied().collect();
        let (g, xe2, ye2) = self.conv_gates(tt, &xf, &yf, &pg16, &spares, CONV_K_T);
        assert!(xe2 == xe && ye2 == ye, "conv_back: the ring lists do not round-trip");
        eprintln!("conv: tail converter at {}: {} gates, {} CCX (pre-MAC)", tt, g.len(), g.iter().filter(|q0| q0.2 != NONE).count());
        self.b.t(&rev(&g));
        // relabel (CX swaps, no Toffoli): the start's label sets come back, ring X and ring Y as sets, page and freed
        // tops by position, so everything after the cut (page_out / tail list, F's end labels) sees the D16 labels
        let tgt_set = |cur: &[u32], orig: &[u32]| -> Vec<u32> {
            let os: std::collections::HashSet<u32> = orig.iter().copied().collect();
            let cs: std::collections::HashSet<u32> = cur.iter().copied().collect();
            let mut miss = orig.iter().copied().filter(|l| !cs.contains(l));
            let t: Vec<u32> = cur.iter().map(|&l| if os.contains(&l) { l } else { miss.next().expect("conv relabel: set sizes") }).collect();
            assert!(miss.next().is_none(), "conv relabel: set sizes");
            t
        };
        let (tx, ty) = (tgt_set(&x16, &self.cv_x16), tgt_set(&y16, &self.cv_y16));
        let (tp, tf) = (self.cv_pg16.clone(), self.cv_freed.clone());
        let mut dest: HashMap<u32, u32> = HashMap::new();
        for (c, t) in [(&x16, &tx), (&y16, &ty), (&pg16, &tp), (&freed, &tf)] {
            assert_eq!(c.len(), t.len());
            for (&a, &b) in c.iter().zip(t.iter()) { if a != b { dest.insert(a, b); } }
        }
        let vals: std::collections::HashSet<u32> = dest.values().copied().collect();
        assert!(dest.keys().all(|k| vals.contains(k)) && vals.len() == dest.len(), "conv relabel: not a permutation");
        let mut keys: Vec<u32> = dest.keys().copied().collect();
        keys.sort();
        let mut done = std::collections::HashSet::new();
        let mut sw: GL = vec![];
        for &s0 in &keys {
            if done.contains(&s0) { continue; }
            let mut c = vec![s0];
            let mut q0 = dest[&s0];
            while q0 != s0 { c.push(q0); q0 = dest[&q0]; }
            for &l in &c { done.insert(l); }
            for &sj in &c[1..] { sw.extend([G(s0, sj, NONE), G(sj, s0, NONE), G(s0, sj, NONE)]); }
        }
        eprintln!("conv: tail relabel {} labels moved, {} CX", dest.len(), sw.len());
        self.b.t(&sw);
        self.x = tx;
        self.y = ty;
        self.pg = tp;
        self.freed = tf;
        self.wr = WHI;
    }
    /// recorded window_prims gates -> frame gates
    /// as pgl, with the measurement-based AND pair kept as AND markers (fb-r7b T2C: Gidney adders on clean T2 lanes)
    fn pgl_and(rg: Vec<self::prims_builder::G>) -> GL {
        use self::prims_builder::G as PG;
        use self::gl_loader::{ANDC, ANDU};
        if !SW_T2C { return Self::pgl(rg); }
        let mut g: GL = Vec::with_capacity(rg.len());
        for e in rg {
            match e {
                PG::AndC(a, b, c) => g.push(G(a.0 as u32, b.0 as u32, c.0 as u32 | ANDC)),
                PG::AndU(a, b, c) => g.push(G(a.0 as u32, b.0 as u32, c.0 as u32 | ANDU)),
                other => g.extend(Self::pgl(vec![other])),
            }
        }
        g
    }
    /// SW1_K2_AND_ROLES: as pgl_and with the AND pair always kept as AND markers (no SW_T2C guard)
    fn pgl_roles(rg: Vec<self::prims_builder::G>) -> GL {
        use self::prims_builder::G as PG;
        use self::gl_loader::{ANDC, ANDU};
        let mut g: GL = Vec::with_capacity(rg.len());
        for e in rg {
            match e {
                PG::AndC(a, b, c) => g.push(G(a.0 as u32, b.0 as u32, c.0 as u32 | ANDC)),
                PG::AndU(a, b, c) => g.push(G(a.0 as u32, b.0 as u32, c.0 as u32 | ANDU)),
                other => g.extend(Self::pgl(vec![other])),
            }
        }
        g
    }
    fn pgl(rg: Vec<self::prims_builder::G>) -> GL {
        use self::prims_builder::G as PG;
        let mut g: GL = Vec::with_capacity(rg.len());
        for e in rg {
            match e {
                PG::X(a) => g.push(gx(a.0 as u32)),
                PG::Cx(a, b) => g.push(gc(a.0 as u32, b.0 as u32)),
                PG::Ccx(a, b, c) => g.push(gt(a.0 as u32, b.0 as u32, c.0 as u32)),
                PG::Swap(a, b) => g.extend_from_slice(&[gc(a.0 as u32, b.0 as u32), gc(b.0 as u32, a.0 as u32), gc(a.0 as u32, b.0 as u32)]),
                PG::AndC(a, b, c) | PG::AndU(a, b, c) => g.push(gt(a.0 as u32, b.0 as u32, c.0 as u32)),
                other => panic!("pgl: unexpected prims gate {other:?}"),
            }
        }
        g
    }
    fn qs(v: &[u32]) -> Vec<QubitId> { v.iter().map(|&a| q(a)).collect() }
    /// T1 = tB_low, T2 = tA_low on the page (VA, VB = A, B low) -> SC = the explicit cofactor by the parity of B and
    /// T2 = 0 (T2 = T2 * pivot + other * SC - p). z: a clean lane (0 in and out).
    fn erase_blk(&self, z: u32) -> GL {
        self.erase_blk_d(z, PAGE_D)
    }
    fn erase_blk_d(&self, z: u32, d: usize) -> GL {
        use self::window_prims::{self as wp, Cfg};
        let (va, vb, t1, t2) = (&self.pg[0..d], &self.pg[d..2 * d], &self.pg[2 * d..3 * d], &self.pg[3 * d..4 * d]);
        let mut g: GL = vec![];
        // z = [B even]
        g.extend_from_slice(&[gx(vb[0]), gc(vb[0], z), gx(vb[0])]);
        for j in 0..d {
            cswap(z, t1[j], t2[j], &mut g);
            cswap(z, va[j], vb[j], &mut g);
        }
        let (qa, qb, q1, q2, qp) = (Self::qs(va), Self::qs(vb), Self::qs(t1), Self::qs(t2), Self::qs(&self.pas[..64]));
        let mut pb = self::prims_builder::B::new();
        let kneg = (1u64 << d) - (wp::P256_LO & ((1u64 << d) - 1));
        let rg = wp::rec(&mut pb, |b| {
            wp::imul(b, Cfg::PY, &q2, &qb, &qp, 0);
            wp::mac(b, Cfg::PY, &q2, &qa, &q1, &qp);
            wp::const_add(b, Cfg::PY, &q2, kneg, &qp);
        });
        g.extend(Self::pgl(rg));
        for j in 0..d {
            cswap(z, va[j], vb[j], &mut g);
        }
        g.extend_from_slice(&[gx(vb[0]), gc(vb[0], z), gx(vb[0])]);
        g
    }
    /// erase_blk controlled by ctrl (the shots whose four low words are being put on / taken off the page).
    fn cerase(&self, ctrl: u32) -> GL {
        use self::window_prims::{self as wp, Cfg};
        let d = PAGE_D;
        let (va, vb, t1, t2) = (&self.pg[0..d], &self.pg[d..2 * d], &self.pg[2 * d..3 * d], &self.pg[3 * d..4 * d]);
        let z = self.pg[4 * d + 1];
        let zg = self.m(&[(ctrl, true), (vb[0], false)], z);
        let mut g: GL = zg.clone();
        for j in 0..d {
            cswap(z, t1[j], t2[j], &mut g);
            cswap(z, va[j], vb[j], &mut g);
        }
        let (qa, qb, q1, q2, qp) = (Self::qs(va), Self::qs(vb), Self::qs(t1), Self::qs(t2), Self::qs(&self.pas[..64]));
        let mut pb = self::prims_builder::B::new();
        let kneg = (1u64 << d) - (wp::P256_LO & ((1u64 << d) - 1));
        let qc = q(ctrl);
        let rg = wp::rec(&mut pb, |b| {
            wp::cimul(b, Cfg::PY, qc, &q2, &qb, &qp);
            for i in 0..d {
                wp::cc_add_p(b, Cfg::PY, qc, qa[i], &q1[..d - i], &q2[i..], &qp);
            }
            wp::c_const_add(b, Cfg::PY, qc, &q2, kneg, &qp);
        });
        g.extend(Self::pgl(rg));
        for j in 0..d {
            cswap(z, va[j], vb[j], &mut g);
        }
        g.extend(zg);
        g
    }
    /// the four low words of an acting shot (A at X[W-f..], tB under it, B at Y[W-l..], tA under it) <-> the page
    fn swap4(&self, ctrl: u32, l: usize, f: usize) -> GL {
        let d = PAGE_D;
        let (x, y) = (&self.x, &self.y);
        let mut g: GL = vec![];
        for j in 0..d {
            cswap(ctrl, self.pg[j], x[W - f + j], &mut g);
            cswap(ctrl, self.pg[d + j], y[W - l + j], &mut g);
            cswap(ctrl, self.pg[2 * d + j], x[W - f - 1 - j], &mut g);
            cswap(ctrl, self.pg[3 * d + j], y[W - l - 1 - j], &mut g);
        }
        g
    }
    /// at the swap of an act (ctl): the page words trade roles, and when the old B and the new B (A') are both odd the
    /// explicit cofactor changes: SC = tB -> tA' = (p - A' tB) / B = (p - VB SC) / VA after the swap.
    fn post_page(&self, ctl: u32) -> GL {
        self.post_page_k(ctl, AR_POST_AND)
    }
    /// SW2_POST_AND: keep_and = the post-page arithmetic's AND pairs (Gidney forms on the
    /// clean ZB) stay explicit AND compute / measured-uncompute markers (pgl_post); only the ordinary odd11 / even11 calls pass it.
    fn post_page_k(&self, ctl: u32, keep_and: bool) -> GL {
        use self::window_prims::{self as wp, Cfg};
        let d = PAGE_D;
        let (va, vb, sc) = (&self.pg[0..d], &self.pg[d..2 * d], &self.pg[2 * d..3 * d]);
        let f = self.pg[4 * d];
        let mut g: GL = vec![];
        for j in 0..d {
            cswap(ctl, va[j], vb[j], &mut g);
        }
        if AK_PCONV {
            // AK_PCONV: the sandwich close has converted; only the role swap here
            if CONV_PEND.with(|c| c.replace(false)) { AK_CONV_CNT[1].fetch_add(1, Ordering::Relaxed); return g; }
            if PK3_PCONV_BIG && PK3_IN_BIG_POST.with(|c| c.get()) && CONV_PEND_BIG.with(|c| c.replace(false)) {
                PK3_PB_CNT[1].fetch_add(1, Ordering::Relaxed);
                return g;
            }
            AK_CONV_CNT[2].fetch_add(1, Ordering::Relaxed);
        }
        let fg = self.m(&[(ctl, true), (va[0], true), (vb[0], true)], f);
        g.extend_from_slice(&fg);
        let (qa, qb, qc, qp) = (Self::qs(va), Self::qs(vb), Self::qs(sc), Self::qs(&self.pas[..64]));
        let mut pb = self::prims_builder::B::new();
        let k1 = (wp::P256_LO.wrapping_add(1)) & ((1u64 << d) - 1);
        let qf = q(f);
        let zb = [q(ZB_LANE)];
        let cf = if POST_ZB && ZB > 0 { Cfg { clean: &zb, fast: false } } else { Cfg::PY };
        let rg = wp::rec(&mut pb, |b| {
            wp::cimul(b, cf, qf, &qc, &qb, &qp);
            for &s_ in &qc { b.cx(qf, s_); }
            wp::c_const_add(b, cf, qf, &qc, k1, &qp);
            wp::cidiv(b, cf, qf, &qc, &qa, &qp);
        });
        g.extend(if keep_and { Self::pgl_post(rg) } else { Self::pgl(rg) });
        g.extend(fg);
        g
    }
    /// SW2_POST_AND: scoped pgl that keeps PG::AndC / AndU as explicit GL AND markers (the ordinary post_page only)
    fn pgl_post(rg: Vec<self::prims_builder::G>) -> GL {
        use self::prims_builder::G as PG;
        use self::gl_loader::{ANDC, ANDU};
        let mut g: GL = Vec::with_capacity(rg.len());
        for e in rg {
            match e {
                PG::AndC(a, b, c) => g.push(G(a.0 as u32, b.0 as u32, c.0 as u32 | ANDC)),
                PG::AndU(a, b, c) => g.push(G(a.0 as u32, b.0 as u32, c.0 as u32 | ANDU)),
                other => g.extend(Self::pgl(vec![other])),
            }
        }
        g
    }
    /// K2 step sandwich (v3/c/slot2r_q.py step()): with the quotient's low digits on q (fixed weights, 0 above the
    /// class), A' = A - qB already on VA, B on VB, SC = the explicit cofactor:
    /// select (F = [B even]; cswap VA, VB), K2 half, F = 0: VB -= q SC, F = 1: VB /= (1 + q VA). Returns (pre, post):
    /// pre ends with VB = tA_low (pre-step) when F = 0 and VB = tB_low when F = 1 (the role swap is the caller's);
    /// post = inverse of select and K2 half. act: literals of "this shot acts" (q is junk otherwise).
    fn sandwich(&self, qd: &[u32], z2: u32, acts: &[Vec<Lit>]) -> (GL, GL) {
        self.sandwich_g(qd, z2, acts, &|_j| acts.to_vec(), &|_j| vec![])
    }
    /// as sandwich, with digit j counted only for the shots of actj(j) (pre_S) and with ext(j) added to the AND of
    /// the cubic block (third_T): the classes whose quotient is shorter than j + 1 digits drop digit j (no zero fill).
    fn sandwich_g(&self, qd: &[u32], z2: u32, acts: &[Vec<Lit>], actj: &dyn Fn(usize) -> Vec<Vec<Lit>>, ext: &dyn Fn(usize) -> Vec<Lit>) -> (GL, GL) {
        self.sandwich_x(qd, z2, acts, actj, &|j| vec![ext(j)], &|_j| vec![], &|_j| vec![])
    }
    /// as sandwich_g, with the F = 1 AND gate of digit j split over the disjoint cubes extc(j) (an empty cube = no
    /// extra literal), and extra digit-j terms one0(j) (F = 0 block, act literals included) / one1(j) (F = 1 block,
    /// given z) whose cubes carry their own digit lane: a big class e < D (D > 10) has its weight-e digit on y0.
    fn sandwich_x(&self, qd: &[u32], z2: u32, acts: &[Vec<Lit>], actj: &dyn Fn(usize) -> Vec<Vec<Lit>>, extc: &dyn Fn(usize) -> Vec<Vec<Lit>>, one0: &dyn Fn(usize) -> Vec<Vec<Lit>>, one1: &dyn Fn(usize) -> Vec<Vec<Lit>>) -> (GL, GL) {
        // acts: pairwise disjoint literal sets whose union is "this shot acts" (no ACT lane); qd: the quotient digits
        let qn = qd.len();
        let mx = |me: &Self, base: &[Lit], t: u32| -> GL { let mut g: GL = vec![]; for a in acts { let mut l = base.to_vec(); l.extend_from_slice(a); g.extend(me.m(&l, t)); } g };
        use self::window_prims::{self as wp, Cfg};
        let d = PAGE_D;
        let (va, vb, sc) = (&self.pg[0..d], &self.pg[d..2 * d], &self.pg[2 * d..3 * d]);
        let (f, z) = (self.pg[4 * d], self.pg[4 * d + 1]);
        let (qa, qb, qc, qp) = (Self::qs(va), Self::qs(vb), Self::qs(sc), Self::qs(&self.pas[..64]));
        // fb-r7b HYB: R7B_HYBW = number of clean lanes handed to the sandwich adders (count probe on the T2 labels)
        let hw: usize = option_env!("R7B_HYBW").and_then(|v| v.parse().ok()).unwrap_or(d).min(d);
        let qt2 = Self::qs(&self.pg[3 * d..3 * d + hw]);
        let cfc = if SW_T2C && hw > 0 { Cfg { clean: &qt2, fast: false } } else { Cfg::PY };
        let qk2 = [q(z), q(z2)];
        assert!(!SW_K2C || (z != z2 && !va.contains(&z2) && !vb.contains(&z2) && !sc.contains(&z2) && !self.pas[..64].contains(&z2)), "K2C: z2 among the K2 operands");
        let cfk = if SW_K2C { Cfg { clean: &qk2, fast: false } } else { cfc };
        if option_env!("R7B_HYBTEST").is_some() && !HOP_SEEN.load(Ordering::Relaxed) { wp::hyb_selftest(); }
        wp::HYB.store(SW_T2C || SW_K2C, Ordering::Relaxed);
        // F = [B even] and the shot acts (a non-acting shot takes the F = 0 branch, where every q block is off)
        // NK certified call (recipes.json fallback): quotient length 2 / 4 / 10 / 11, no one0 / one1 terms, AND markers on F
        let nk_abi = (NK_F1_TRIE || NK_F0_BODY || NK_SELECT_LSB) && SW_F1Z && hmr_and() && IN_F.load(Ordering::Relaxed)
            && matches!(qn, 2 | 4 | 10 | 11) && (0..d).all(|j| one0(j).is_empty() && one1(j).is_empty());
        let mut sel: GL = mx(self, &[(vb[0], false)], f);
        for j in 0..d {
            // NK_SELECT_LSB: F = 1 implies VA[0] = 1, VB[0] = 0 (B even, A odd), so the bit-0 swap is two CX
            if j == 0 && NK_SELECT_LSB && nk_abi { sel.extend_from_slice(&[gc(f, va[0]), gc(f, vb[0])]); NK_CNT[4].fetch_add(1, Ordering::Relaxed); continue; }
            cswap(f, va[j], vb[j], &mut sel);
        }
        let mut pb = self::prims_builder::B::new();
        let k2 = if HOPA || HOPP {
            // catalyst lanes: passenger 1..d (lane 0 is read in even11), the hop's pool: passenger d..64
            let (gd, pl) = (Self::qs(&self.pas[1..d]), Self::qs(&self.pas[d..64]));
            let rgk = wp::rec(&mut pb, |b| hop2::hop(b, cfk, &qa, &qb, &qc, &gd, &pl, wp::P256_LO, HOPP));
            let rgk2 = if SW1_GROUP_K2 || SW1_K2_AND_ROLES { Some(rgk.clone()) } else { None };
            // AKK2: the native K2 half keeps its AND roles (pgl_and strips them while SW_T2C is off: 308 T instead of 258)
            let h = if SW1_K2_AND_ROLES || AKK2_K2 { Self::pgl_roles(rgk) } else { Self::pgl_and(rgk) };
            if !HOP_SEEN.swap(true, Ordering::Relaxed) {
                eprintln!("r7b lanes at the first sandwich: f {} z {} z2 {} x0 {} y0 {} y1 {} par {}", f, z, z2, self.x[0], self.y[0], self.y[1], self.par);
                eprintln!("hop2: K2 half at D = {} {}: {} CCX one way", d, if HOPP { "parked (HOPP)" } else { "catalyst (HOPA)" }, h.iter().filter(|q0| q0.2 != NONE).count());
            }
            // AKK2: any K2 switch on = the native hop (its adapter controls compare against the parent packets and would differ)
            if (SW1_GROUP_K2 || SW1_K2_AND_ROLES) && !AKK2_K2 {
                // SW1 adapter (lane table): 0 = z2, 470.. VA, 481.. VB, 492.. SC, 503.. passengers, 763 = z
                let pas = self.pas.clone();
                let (va2, vb2, sc2) = (va.to_vec(), vb.to_vec(), sc.to_vec());
                let m = move |q0: u32| -> u32 {
                    match q0 {
                        NONE => NONE,
                        0 => z2,
                        470..=480 => va2[(q0 - 470) as usize],
                        481..=491 => vb2[(q0 - 481) as usize],
                        492..=502 => sc2[(q0 - 492) as usize],
                        503..=758 => pas[(q0 - 503) as usize],
                        763 => z,
                        _ => panic!("SW1: K2 packet lane {q0} outside the adapter"),
                    }
                };
                {
                    // adapter controls at EVERY sandwich: the parent packets must equal the native K2 half
                    let first = !SW1_SEEN.swap(true, Ordering::Relaxed);
                    let lit = Self::pgl(rgk2.clone().unwrap());
                    let rol = Self::pgl_roles(rgk2.clone().unwrap());
                    let pl_ = sw1_packet(SW1_K2_PARENT_LIT, "550bbfea80b611bae6a0b99e32724f94dc34365d2235f716fe755fd339dd75f5", &m);
                    let pr_ = sw1_packet(SW1_K2_PARENT_ROLES, "f06b08510bd878720592183f51670dd4289c0aa514fdb6b140ebe2553568e46b", &m);
                    let gf = sw1_packet(SW1_K2_GROUP_FWD, "44e53adcb3b8c9cbe962f1cf4c3b80a6daf856c776d1af9ea8cfa5f1574245ec", &m);
                    let gi = sw1_packet(SW1_K2_GROUP_INV, "ac1dc7f1228ddce4612fb9a3db1d0ff59ca41992c4ea019c86bc199a351c6352", &m);
                    for (k, (a, b_)) in [(&lit, &pl_), (&rol, &pr_), (&rev_and(&gf), &gi)].into_iter().enumerate() {
                        let r = sw1_same(a, b_);
                        let eq = r.starts_with("EQUAL");
                        let n_ = SW1_CHK[2 * k + if eq { 0 } else { 1 }].fetch_add(1, Ordering::Relaxed);
                        if first || (!eq && n_ < 3) {
                            eprintln!("SW1CHK {} sandwich z {z} z2 {z2}: {r}", ["native literal vs parent_literal", "native roles vs parent_roles", "rev_and(group fwd) vs group inv"][k]);
                        }
                    }
                }
                if SW1_GROUP_K2 {
                    SW1_CHK[6].fetch_add(1, Ordering::Relaxed);
                    sw1_packet(SW1_K2_GROUP_FWD, "44e53adcb3b8c9cbe962f1cf4c3b80a6daf856c776d1af9ea8cfa5f1574245ec", &m)
                } else { h }
            } else { h }
        } else {
            Self::pgl(wp::rec(&mut pb, |b| {
                wp::idiv(b, Cfg::PY, &qa, &qb, &qp);
                wp::invp(b, Cfg::PY, &qb, &qp, wp::P256_LO, &[]);
                wp::undo(b, |b| wp::mac(b, Cfg::PY, &qb, &qa, &qc, &qp));
            }))
        };
        // AK_PCONV: k2 = k2ab ++ k2c with k2c = hop_c (the K2 MAC undo, VB: p/B -> tA); the close converts between them
        let (k2ab, k2c): (GL, GL) = if AK_PCONV && (HOPA || HOPP) {
            let pl = Self::qs(&self.pas[d..64]);
            let rc = wp::rec(&mut pb, |b| hop2::hop_c(b, cfk, &qa, &qb, &qc, &pl));
            // DS: with SW1_GROUP_K2 gated off below page 11, the AKK2 half k2 keeps its AND roles (pgl_roles above), so hop_c's
            // copy must be built the same way for the tail check below (at page 11 SW1_GROUP_K2 is on: unchanged)
            let kc = if SW1_GROUP_K2 || SW1_K2_AND_ROLES || (DS_K2_ALLW && AKK2_K2) { Self::pgl_roles(rc) } else { Self::pgl_and(rc) };
            let n = k2.len();
            assert!(n > kc.len() && sw1_same(&k2[n - kc.len()..], &kc).starts_with("EQUAL"),
                    "AK_PCONV: the K2 list does not end with hop_c: {}", sw1_same(&k2[n.saturating_sub(kc.len())..], &kc));
            (k2[..n - kc.len()].to_vec(), kc)
        } else { (vec![], vec![]) };
        let mut pre: GL = sel.clone();
        pre.extend_from_slice(&k2);
        r7a_sw("a_sel", &sel, 2); r7a_sw("b_k2", &k2, 2); r7a_sw("n_calls", &[gt(0, 1, 2)], 1);
        // F = 0: VB -= q SC
        let qm = (0..d).filter(|&j| j < qn || !one0(j).is_empty()).max().map_or(0, |j| j + 1);
        // DB_F0_SIGN: the certified lengths with digit 0 on the parent path and no one0 terms; db_k0 = K0
        let db0 = DB_F0_SIGN && matches!(qn, 4 | 10 | 11) && !(NK_F0_BODY && nk_abi && nk_f0_bracket_j(qn, 0)) && (0..d).all(|j| one0(j).is_empty());
        let mut db_k0: u64 = 0;
        // DB_F0_SIGN: the signed body of digit j >= 1 (fan(ZB -> VB[j-1..]); VB[j-1..] += SC[..d-j+1]; fan) and digit 0's
        // folded body (X ZB; VB += ZB SC; X ZB)
        let db0_body = |j: usize| -> GL {
            let mut pb0 = self::prims_builder::B::new();
            if j == 0 {
                let mut g: GL = vec![gx(z)];
                g.extend(Self::pgl_and(wp::rec(&mut pb0, |b| wp::cadd_p(b, cfc, q(z), &qc[..d], &qb[0..], &qp))));
                g.push(gx(z));
                return g;
            }
            let fan: GL = vb[j - 1..].iter().map(|&t| gc(z, t)).collect();
            let mut g: GL = fan.clone();
            g.extend(Self::pgl(wp::rec(&mut pb0, |b| wp::add(b, Cfg::PY, &qc[..d - j + 1], &qb[j - 1..], None))));
            g.extend(fan);
            g
        };
        for j in 0..qm {
            let db0j = db0 && j >= 1 && j <= DB_F0_JMAX && j < qn;
            // NK_F0_BODY (recipes.json choices.combined, F0 bracket rows): one predicate_add per disjoint act cube around its
            // subtract (decided before any flag macro is recorded)
            if NK_F0_BODY && nk_abi && j < qn && nk_f0_bracket_j(qn, j) {
                let f0b = if db0j { db0_body(j) } else { Self::pgl_and(wp::rec(&mut pb, |b| wp::undo(b, |b| wp::cadd_p(b, cfc, q(z), &qc[..d - j], &qb[j..], &qp)))) };
                let lits: Vec<Vec<Lit>> = actj(j).into_iter().map(|a| [&[(qd[j], true), (f, false)][..], &a[..]].concat()).collect();
                if let Some(g) = nk_bracket_all(&lits, z, z2, &f0b) {
                    if db0j {
                        // one signed add per emitted predicate (nk_pred_add emits nothing for a contradictory cube)
                        for l in &lits {
                            if nk_norm(l).is_some() { db_k0 = db_k0.wrapping_add(1u64 << (j - 1)); DB_CNT[1].fetch_add(1, Ordering::Relaxed); }
                        }
                    }
                    pre.extend(g);
                    continue;
                }
            }
            let mut zg: GL = vec![];
            if j < qn {
                for a in actj(j) {
                    let mut l: Vec<Lit> = vec![(qd[j], true), (f, false)];
                    l.extend_from_slice(&a);
                    zg.extend(if L3X0 { self.mclean(&l, z, z2) } else { self.m(&l, z) });
                }
            }
            for a in one0(j) {
                let mut l: Vec<Lit> = vec![(f, false)];
                l.extend_from_slice(&a);
                zg.extend(if L3X0 { self.mclean(&l, z, z2) } else { self.m(&l, z) });
            }
            // ob-ladder merge: fb-r7b K2C form (pgl_and + cfc) with fb-r7a's count-only R7E_PROF counters kept
            let f0a = if db0 && j == 0 {
                db0_body(0)
            } else if db0j && !zg.is_empty() {
                db_k0 = db_k0.wrapping_add(1u64 << (j - 1));
                DB_CNT[1].fetch_add(1, Ordering::Relaxed);
                db0_body(j)
            } else {
                Self::pgl_and(wp::rec(&mut pb, |b| wp::undo(b, |b| wp::cadd_p(b, cfc, q(z), &qc[..d - j], &qb[j..], &qp))))
            };
            pre.extend_from_slice(&zg);
            r7a_sw("c_f0_flags", &zg, 2); r7a_sw("d_f0_adds", &f0a, 1);
            pre.extend(f0a);
            pre.extend_from_slice(&zg);
        }
        if db0 {
            // VB -= (K0 + 1) SC: the + SC of digit 0's fold and the + SC 2^(j-1) of every signed add
            let (c, n) = db_comp_sc(sc, vb, db_k0.wrapping_add(1));
            DB_CNT[0].fetch_add(1, Ordering::Relaxed);
            DB_CNT[3].fetch_add(n, Ordering::Relaxed);
            r7a_sw("d_f0_adds", &c, 1);
            pre.extend(c);
        }
        // F = 1: VB /= (1 + q VA)  (inverse of the top-down multiply)
        let mut mul: GL = vec![];
        // NK_F1_TRIE contract: certified quotient lengths, no extra one1 terms, the F = 1 bit flag form, AND markers on F
        let nk_call = NK_F1_TRIE && SW_F1Z && hmr_and() && IN_F.load(Ordering::Relaxed) && matches!(qn, 4 | 10 | 11) && (0..qm).all(|j| one1(j).is_empty());
        // DB_F1_SIGN: K = sum of 2^s over the signed adds (mod 2^d), paid once by db_comp at the end of mul
        let db_sig = |s: usize| -> bool { DB_F1_SIGN && s <= DB_F1_SMAX };
        let mut db_k: u64 = 0;
        for i in (0..=(d - 2)).rev() {
            if nk_call && i <= 8 {
                let mut digits: Vec<(usize, u32, Vec<Vec<Lit>>)> = vec![];
                let mut bodies: BTreeMap<usize, GL> = BTreeMap::new();
                // DB_F1_SIGN: the signed digits of this group; db_j0 = the j = 0 term taken out of the trie (VB_i is a scaffold lane)
                let mut db_sj: BTreeSet<usize> = BTreeSet::new();
                let mut db_j0: Option<usize> = None;
                for j in 0..qn {
                    if i + j + 1 >= d { continue; }
                    let ln = d - (i + j + 1);
                    let cubes = extc(j);
                    if cubes.is_empty() { continue; }
                    if j == 0 && db_sig(i) && cubes.len() == 1 && cubes[0].is_empty() { db_j0 = Some(i); continue; }
                    if j >= 1 && db_sig(i + j) {
                        bodies.insert(j, db_sign_body(z2, va, vb, i + j));
                        db_sj.insert(j);
                    } else {
                        bodies.insert(j, Self::pgl_and(wp::rec(&mut pb, |b| wp::cadd_p(b, cfc, q(z2), &qa[1..1 + ln], &qb[i + j + 1..], &qp))));
                    }
                    digits.push((j, qd[j], cubes));
                }
                if let Some(g) = nk_trie_group(f, vb[i], z, z2, &digits, &bodies) {
                    mul.extend(g);
                    // one signed add per emitted packet (nk_trie_group skips a contradictory cube)
                    for (j, dq, cubes) in &digits {
                        if !db_sj.contains(j) { continue; }
                        for ex in cubes {
                            if nk_norm(&[&[(f, true), (vb[i], true)][..], &ex[..], &[(*dq, true)][..]].concat()).is_some() {
                                db_k = db_k.wrapping_add(1u64 << (i + j));
                                DB_CNT[1].fetch_add(1, Ordering::Relaxed);
                            }
                        }
                    }
                    if let Some(s) = db_j0 {
                        // after the group (multiply direction): F & VB_i -> ZB, ZB & q0 -> X0, signed body, release; the body
                        // flips VB_i by VA_1 (pending until the compensation), so the ZB release runs inside CX(VA_1 -> VB_i)
                        use self::gl_loader::{ANDC, ANDU};
                        mul.push(G(f, vb[i], z | ANDC));
                        mul.push(G(z, qd[0], z2 | ANDC));
                        mul.extend(db_sign_body(z2, va, vb, s));
                        mul.push(G(z, qd[0], z2 | ANDU));
                        mul.extend_from_slice(&[gc(va[1], vb[i]), G(f, vb[i], z | ANDU), gc(va[1], vb[i])]);
                        db_k = db_k.wrapping_add(1u64 << s);
                        DB_CNT[1].fetch_add(1, Ordering::Relaxed);
                        DB_CNT[2].fetch_add(1, Ordering::Relaxed);
                    }
                    continue;
                }
            }
            let zg = if SW_F1Z {
                // f = [B even] AND act (sel above; the act lanes are not written inside the sandwich), so f & vb[i] & act = f & vb[i]
                and2(f, vb[i], z)
            } else if L3X0 {
                let mut g: GL = vec![];
                for a in acts { let mut l: Vec<Lit> = vec![(f, true), (vb[i], true)]; l.extend_from_slice(a); g.extend(self.mclean(&l, z, z2)); }
                g
            } else { mx(self, &[(f, true), (vb[i], true)], z) };
            // held: the digit terms that read the bit flag on ZB; dir (SW_Z2D): the terms computed without it
            let (mut held, mut dir): (GL, GL) = (vec![], vec![]);
            // DB_F1_SIGN: a signed held j = 0 term (it is first in held) leaves VB_i flipped by VA_1
            let mut db_j0h = false;
            for j in 0..qm {
                if i + j + 1 >= d { continue; }
                let ln = d - (i + j + 1);
                let mut z2g: GL = vec![];
                let terms: Vec<(bool, Vec<Lit>)> = {
                    let mut v: Vec<(bool, Vec<Lit>)> = vec![];
                    if j < qn { for c in extc(j) { v.push((true, c)); } }
                    for c in one1(j) { v.push((false, c)); }
                    v
                };
                // DB_F1_SIGN: one add per digit (z2 = XOR of its terms); a direct j = 0 term would write the bit its flags read
                let db_dir = SW_Z2D && SW_F1Z && !terms.is_empty() && terms.iter().all(|t| t.1.len() >= 2);
                let db_s = db_sig(i + j) && !terms.is_empty() && !(j == 0 && db_dir);
                let add = if db_s {
                    db_k = db_k.wrapping_add(1u64 << (i + j));
                    DB_CNT[1].fetch_add(1, Ordering::Relaxed);
                    if j == 0 { db_j0h = true; DB_CNT[2].fetch_add(1, Ordering::Relaxed); }
                    db_sign_body(z2, va, vb, i + j)
                } else {
                    Self::pgl_and(wp::rec(&mut pb, |b| wp::cadd_p(b, cfc, q(z2), &qa[1..1 + ln], &qb[i + j + 1..], &qp)))
                };
                if SW_Z2D && SW_F1Z && !terms.is_empty() && terms.iter().all(|t| t.1.len() >= 2) {
                    // every term of this digit has two or more extra literals: z2 = f & vb[i] & (digit) & cube as a clean
                    // macro on X[0] with ZB as its inner lane (ZB is free: the bit flag is not held here). The adds of one bit
                    // commute (they write VB above bit i and read lanes none of them writes), so they are emitted after
                    // the held ones.
                    for (dig_, ex) in &terms {
                        let mut l: Vec<Lit> = vec![(f, true), (vb[i], true)];
                        if *dig_ { l.push((qd[j], true)); }
                        l.extend_from_slice(ex);
                        z2g.extend(self.m(&l, z2));
                    }
                    r7a_sw("g_f1_z2_direct", &z2g, 2); r7a_sw("h_f1_adds", &add, 1);
                    dir.extend_from_slice(&z2g);
                    dir.extend(add);
                    dir.extend_from_slice(&z2g);
                    continue;
                }
                let single = terms.len() == 1;
                for (dig_, ex) in terms {
                    if ex.is_empty() {
                        if dig_ { if single && SW_F1Z { z2g.extend(and2(z, qd[j], z2)); } else { z2g.push(gt(z, qd[j], z2)); } } else { z2g.push(gc(z, z2)); }
                    } else {
                        let mut l: Vec<Lit> = vec![(z, true)];
                        if dig_ { l.push((qd[j], true)); }
                        l.extend_from_slice(&ex);
                        ZB_BUSY.store(true, Ordering::Relaxed);
                        z2g.extend(self.m(&l, z2));
                        ZB_BUSY.store(false, Ordering::Relaxed);
                    }
                }
                r7a_sw("f_f1_z2_held", &z2g, 2); r7a_sw("h_f1_adds", &add, 1);
                held.extend_from_slice(&z2g);
                held.extend(add);
                held.extend_from_slice(&z2g);
            }
            // DB_F1_SIGN: the bit flag's release and the direct flags read VB_i: undo the pending VA_1 flip around them
            let db_corr: GL = if db_j0h { vec![gc(va[1], vb[i])] } else { vec![] };
            if !held.is_empty() || !SW_Z2D {
                r7a_sw("e_f1_bitflag", &zg, 2);
                mul.extend_from_slice(&zg);
                mul.extend(held);
                mul.extend_from_slice(&db_corr);
                mul.extend_from_slice(&zg);
                mul.extend_from_slice(&db_corr);
            }
            mul.extend_from_slice(&db_corr);
            mul.extend(dir);
            mul.extend_from_slice(&db_corr);
        }
        if DB_F1_SIGN && db_k & ((1u64 << d) - 1) != 0 {
            let (c, n) = db_comp(va, vb, db_k);
            DB_CNT[0].fetch_add(1, Ordering::Relaxed);
            DB_CNT[3].fetch_add(n, Ordering::Relaxed);
            r7a_sw("h_f1_adds", &c, 1);
            mul.extend(c);
        }
        pre.extend(rev_and(&mul));
        if r765_prof() { *SWX_LAST.lock().unwrap() = (sel.len(), k2.len()); }
        let cacts = if AK_PCONV { CONV_ACTS.with(|c| c.borrow_mut().take()) } else { None };
        let pk3_fam = PK3_PCONV_BIG && PK3_FAM.with(|c| c.replace(false));
        let mut post = if AK_PCONV && (HOPA || HOPP) && !k2c.is_empty() {
            // AK_PCONV close: undo hop_c (VB = p/B, VA = r, SC = tB); under c = act & !F & r0 (on z2): SC <- p/B - r tB = tA'
            let mut g = rev_and(&k2c);
            let cacts = cacts.unwrap_or_else(|| acts.to_vec());
            let mut cg: GL = vec![];
            for a in &cacts {
                let mut l: Vec<Lit> = vec![(f, false), (va[0], true)];
                l.extend_from_slice(a);
                cg.extend(self.m(&l, z2));
            }
            let qz2 = q(z2);
            let qzz = [q(z)];
            let cfz = Cfg { clean: &qzz, fast: false };
            // DS: the block moved verbatim into hop2::pconv_cv (unit-tested by dial_k2_pconv_cv)
            let cv_rg = wp::rec(&mut pb, |b| hop2::pconv_cv(b, cfz, qz2, &qa, &qb, &qc, &qp));
            let cv = Self::pgl_roles(cv_rg);
            g.extend_from_slice(&cg);
            g.extend(cv);
            g.extend_from_slice(&cg);
            g.extend(rev_and(&k2ab));
            assert!(!CONV_PEND.with(|c| c.get()), "AK_PCONV: two sandwiches before one post_page");
            CONV_PEND.with(|c| c.set(true));
            AK_CONV_CNT[0].fetch_add(1, Ordering::Relaxed);
            if pk3_fam {
                assert!(!CONV_PEND_BIG.with(|c| c.get()), "PK3_PCONV_BIG: two family closes before one big post");
                CONV_PEND_BIG.with(|c| c.set(true));
                PK3_PB_CNT[0].fetch_add(1, Ordering::Relaxed);
            }
            g
        } else {
            if AK_PCONV { AK_CONV_CNT[3].fetch_add(1, Ordering::Relaxed); }
            rev_and(&k2)
        };
        wp::HYB.store(false, Ordering::Relaxed);
        post.extend(rev(&sel));
        (pre, post)
    }
    /// R765_PROF: emit g as [..a) [a..a+k) [a+k..) under three part tags (big: full big:* tags), then restore the tag.
    /// The same gates as one self.b.t(g) (tags are count-only); with the profile off it IS one self.b.t(g).
    fn t3(&mut self, g: &[G], a: usize, k: usize, parts: [&str; 3], big: bool) {
        if !r765_prof() { self.b.t(g); return; }
        let save = R7E_TAG.lock().unwrap().clone();
        let a = a.min(g.len());
        let b_ = (a + k).min(g.len());
        for (lo, hi, p_) in [(0, a, parts[0]), (a, b_, parts[1]), (b_, g.len(), parts[2])] {
            if big { *R7E_TAG.lock().unwrap() = format!("big:{p_}"); } else { r7e_sub(p_); }
            self.b.t(&g[lo..hi]);
        }
        *R7E_TAG.lock().unwrap() = save;
    }
    /// R765_PROF: emit g under the sub-tag `part` of the current slot class, then restore the tag (count-only; off = one t()).
    fn tsub(&mut self, part: &str, g: &[G]) {
        if !r765_prof() { self.b.t(g); return; }
        let save = R7E_TAG.lock().unwrap().clone();
        if part.starts_with("big:") { *R7E_TAG.lock().unwrap() = part.to_string(); } else { r7e_sub(part); }
        self.b.t(g);
        *R7E_TAG.lock().unwrap() = save;
    }
    /// R765_PROF: emit g in pieces [prev..cut) under each (cut, part), the rest under the tag in force (count-only).
    fn tsplit(&mut self, g: &[G], cuts: &[(usize, &str)]) {
        if !r765_prof() { self.b.t(g); return; }
        let save = R7E_TAG.lock().unwrap().clone();
        let mut lo = 0usize;
        for &(c, part) in cuts { let c = c.min(g.len()).max(lo); if part.starts_with("big:") { *R7E_TAG.lock().unwrap() = part.to_string(); } else { r7e_sub(part); } self.b.t(&g[lo..c]); lo = c; }
        *R7E_TAG.lock().unwrap() = save;
        self.b.t(&g[lo..]);
    }
    fn slot(&mut self, t: i32) {
        r7e_tag(slot_class(t));
        if t % 2 == 1 {
            self.odd11(t);
        } else {
            self.even11(t);
        }
    }
    /// PO2: fold top waiters and LOOK16 frozen shots into the first down-turn.
    /// W1 tags only the frozen family during this post. F is clean at post_page_k.
    /// Conditional domain checked in Python.
    fn po2_odd_post(&self, t: i32) -> GL {
        let (x, y) = (&self.x, &self.y);
        let (h0, h1) = (self.e[0], self.e[1]);
        let ff = self.pg[4 * PAGE_D];
        assert!(self.wr == 235 && PAGE_D == 11 && ECAP == 17);
        let mut g: GL = vec![];
        g.extend(self.m(&[(y[234], true), (h0, false), (h1, false), (y[0], false)], x[0]));
        g.extend(self.m(&[(y[234], true), (h0, true), (h1, false)], ff));
        g.extend(self.m(&[(y[234], true), (h0, true), (h1, true)], ff));
        g.extend(self.m(&[(y[234], true), (h0, false), (h1, true), (self.w1, true)], ff));
        g.extend(self.m(&[(ff, true)], x[0]));
        // PO2 tag frozen on W1
        if l16_frz(t) { g.extend(self.m(&[(y[234], false), (y[233], true), (h0, true), (h1, true)], self.w1)); }
        // PO2 frozen shares first down-turn
        if l16_frz(t) { g.extend(self.m(&[(y[234], false), (y[233], true), (h0, true), (h1, true)], x[0])); }
        g.extend(rotate_up(x[0], y, 234));
        g.extend(self.m(&[(y[234], true), (h0, false), (h1, false)], x[0]));
        // PO2 clear shifted frozen control
        if l16_frz(t) { g.extend(self.m(&[(self.w1, true), (y[233], false)], x[0])); }
        g.extend(self.m(&[(ff, true)], x[0]));
        g.extend(self.m(&[(ff, true), (h1, false)], y[0]));
        g.extend(self.m(&[(ff, true), (y[0], true)], h1));
        g.extend(self.m(&[(ff, true), (self.w1, true)], h0));
        g.extend(self.m(&[(y[234], false), (y[233], true), (h0, true), (h1, true)], ff));
        for j in 1..self.wr { cswap(x[0], x[j], y[j], &mut g); }
        g.extend(self.m(&[(x[0], true)], self.par));
        let pp = self.post_page_k(x[0], SW2_POST_AND);
        pg_add(7, &pp);
        g.extend(pp);
        g.extend(self.m(&[(x[0], true)], y[234]));
        g.extend(self.m(&[(y[234], true), (h0, false), (h1, false)], x[0]));
        g.extend(self.m(&[(y[234], true), (h0, false), (h1, false), (x[234], false), (y[233], false)], x[0]));
        g.extend(rot1(x[0], &y[..self.wr - 1]));
        g.extend(self.m(&[(y[234], true), (h0, false), (h1, false), (x[234], false), (y[0], false)], x[0]));
        g.extend(self.m(&[(y[234], true), (x[234], true), (h0, false), (h1, false)], x[0]));
        g.extend(self.m(&[(y[234], true), (x[234], false), (y[0], true), (h0, false), (h1, false)], x[0]));
        g.extend(self.m(&[(x[0], true)], h0));
        g.extend(self.m(&[(y[234], true), (x[234], true), (y[0], true), (h0, true), (h1, false)], x[0]));
        g.extend(self.m(&[(y[234], true), (x[234], false), (y[0], true), (h0, true), (h1, false)], x[0]));
        g.extend(self.m(&[(x[234], true), (y[0], true), (h0, true), (h1, false)], y[234]));
        g.extend(self.m(&[(x[234], false), (y[0], false), (y[1], true), (h0, false), (h1, false)], y[234]));
        g.extend(self.m(&[(y[233], true), (x[234], false), (y[0], true), (h0, true), (h1, false)], y[234]));
        g.extend(self.m(&[], y[234]));
        g.extend(self.m(&[(y[234], true)], x[0]));
        g.extend(self.m(&[], y[234]));
        g.extend(self.m(&[(y[234], false), (y[233], true), (h0, true), (h1, true)], ff));
        g.extend(self.m(&[(ff, true)], x[0]));
        // PO2 suppress shifted frozen rise
        if l16_frz(t) { g.extend(self.m(&[(self.w1, true), (y[233], false)], x[0])); }
        g.extend(self.m(&[(x[0], true), (h0, false), (h1, false)], y[0]));
        g.extend(self.m(&[(x[0], true), (y[0], true), (h0, false)], h1));
        g.extend(self.m(&[(x[0], true), (h1, false)], h0));
        g.extend(self.m(&[(x[0], true), (h0, true), (x[234], true), (y[232], true)], h1));
        g.extend(self.m(&[(x[0], true), (h0, true), (x[234], false), (y[231], true)], h1));
        g.extend(self.m(&[(x[0], true), (x[234], true), (h0, true), (h1, false)], y[232]));
        g.extend(self.m(&[(x[0], true), (x[234], false), (h0, true), (h1, false)], y[231]));
        g.extend(rot_free(y, 1));
        // PO2 restore frozen control
        if l16_frz(t) { g.extend(self.m(&[(y[234], false), (y[233], true), (h0, true), (h1, true)], x[0])); }
        g.extend(self.m(&[(ff, true), (y[1], true)], h1));
        g.extend(self.m(&[(ff, true), (h1, false)], y[1]));
        g.extend(self.m(&[(ff, true), (self.w1, true)], h0));
        g.extend(self.m(&[(y[234], true), (h0, true), (h1, false)], ff));
        g.extend(self.m(&[(y[234], true), (h0, true), (h1, true)], ff));
        g.extend(self.m(&[(y[234], true), (h0, false), (h1, true), (self.w1, true)], ff));
        // PO2 release frozen W1 tag
        if l16_frz(t) { g.extend(self.m(&[(y[234], false), (y[233], true), (h0, true), (h1, true)], self.w1)); }
        g.extend(self.m(&[], x[0]));
        g.extend(self.m(&[(y[234], true), (h0, true), (h1, true)], x[0]));
        g.extend(self.m(&[(y[234], true), (h0, true), (h1, false)], x[0]));
        g.extend(self.m(&[(y[234], true), (h0, false), (h1, true), (self.w1, true)], x[0]));
        g
    }
    fn odd11(&mut self, t: i32) {
        r7e_sub("head");
        let wv = self.wr;
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        let yt = y[wv - 1];
        let (x0, y0) = (x[0], y[0]);
        let (d, ctl) = (x0, x0);
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let al: Vec<Lit> = cat(&[(yt, true)], &self.hc(0));
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        self.b.t(&[gx(x0)]);
        // a shot at the top with e odd >= 3 waits one slot: code 11
        // CAD4: a W1 waiter (code 01 at the top) keeps its code and takes no part in the slot
        let w1o: Vec<Lit> = if cad4_band(t) { vec![(self.w1, false)] } else { vec![] };
        let g = self.m(&cat(&[(yt, true), (h1, true)], &w1o), h0);
        self.b.t(&g);
        let (l, f) = ((t - 1) / 2, (t + 1) / 2);
        let pgo = PAGE_G && mid_odd(t);
        r7e_sub("rows");
        // P1: every acting shot of an odd slot has e = 1, so its page window is an uncontrolled lane permutation
        let dd = PAGE_D;
        let pd = if pgo { dd } else { 0 };
        let (va, vb, sc) = if pgo { (self.pg[..dd].to_vec(), self.pg[dd..2 * dd].to_vec(), self.pg[2 * dd..3 * dd].to_vec()) } else { (vec![], vec![], vec![]) };
        let (lu, fu) = (l as usize, f as usize);
        if pgo {
            let mut lanes = va.clone();
            lanes.push(x[wv - fu + dd]);
            self.b.t(&rot_free(&lanes, dd));
        }
        if l >= 1 && f <= N as i32 {
            let actv: Vec<Vec<Lit>> = vec![cat(&[(yt, true), (h0, false)], &w1o)];
            for k in 0..2usize {
                let alo = wv - l as usize - k + pd;
                let tv: Vec<u32> = (alo..(wv - k - 1)).map(|a| x[a]).collect();
                let sv: Vec<u32> = (alo..(wv - k - 1)).map(|a| y[a + k]).collect();
                let t1 = x[wv - 1 - k];
                let top = if k >= 1 { x[wv - k] } else { NONE };
                let g = self.row_v(&tv, &sv, t1, top, d, h1, NONE, &no_tog, &actv, None, None);
                if pgo {
                    let mut up: GL = vec![];
                    let mut dn: GL = vec![];
                    for b in 0..dd {
                        let (sq, tq) = (vb[b], va[(b + dd - k) % dd]);
                        up.extend_from_slice(&[gx(tq), gc(h1, sq), gc(h1, tq), gt(sq, tq, h1)]);
                    }
                    for b in (0..dd).rev() {
                        let (sq, tq) = (vb[b], va[(b + dd - k) % dd]);
                        dn.extend_from_slice(&[gt(sq, tq, h1), gc(h1, tq), gt(d, sq, tq), gc(h1, sq), gx(tq)]);
                    }
                    pg_add(1, &up); pg_add(1, &dn);
                    self.b.t(&up);
                    self.b.t(&g);
                    self.b.t(&dn);
                } else {
                    self.b.t(&g);
                }
                let mut g: GL = vec![];
                if k >= 1 {
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(x[wv - k], true)]), d));
                    }
                } else {
                    if SM_L2V {
                        g.push(gc(d, y0));
                    } else {
                        for li in &actv {
                            g.extend(self.m(&cat(li, &[(d, true)]), y0));
                        }
                    }
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(y0, true)]), d));
                    }
                }
                self.b.t(&g);
                if pgo && k == 0 {
                    self.b.t(&swap_free(va[dd - 1], x[wv - lu + dd - 1]));
                }
            }
            let mut sw_post: GL = vec![];
            if pgo {
                self.b.t(&rot_free(&va, 1));
                // digits: dig[0] = Y0 has weight 2, dig[1] = X[wv-1] weight 1; zeros (B's empty ring lanes) above
                // digits: dig[0] = Y0 has weight 2, dig[1] = X[wv-1] weight 1: swap them; q has 2 digits
                let rm: GL = swap_free(y0, x[wv - 1]);
                let q: Vec<u32> = vec![y0, x[wv - 1]];
                let (pre, post) = self.sandwich(&q, d, &actv);
                let fz = self.pg[4 * dd];
                let mut rs: GL = vec![];
                for j in 0..dd {
                    cswap(fz, vb[j], sc[j], &mut rs);
                }
                pg_add(5, &pre); pg_add(5, &post); pg_add(5, &rs); pg_add(5, &rs);
                r7e_sub("sw_swap");
                self.b.t(&rm);
                { let (a_, k_) = swx_last(); self.t3(&pre, a_, k_, ["sw_sel", "sw_K2", "sw_q"], false); }
                self.b.t(&rm);
                self.b.t(&rs);
                r7e_sub("rows");
                self.b.t(&rot_free(&vb, dd - 1));
                swp_note(rs.len());
                sw_post = rs;
                sw_post.extend(post);
            }
            for k in [1usize, 0] {
                let ahi = W - f as usize - 1 + k - pd;
                let wires: Vec<usize> = (k..=ahi).rev().collect();
                let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
                let sv: Vec<u32> = wires.iter().map(|&a| x[a - k]).collect();
                let nn = tv.len();
                let top = if k >= 1 { y[k - 1] } else { NONE };
                let g = self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, h1, NONE, &no_tog, &actv, None, None);
                let mut hh: GL = vec![];
                if k >= 1 {
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(x[wv - k], true)]), d));
                    }
                    hh.push(gc(d, x[wv - k]));
                    let xt = x[wv - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(y0, true)]), xt));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(xt, true)]), y0));
                    }
                    hh.push(gc(d, top));
                } else {
                    let host = x[wv - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(host, true)]), d));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(d, true)]), host));
                    }
                }
                self.b.t(&hh);
                if pgo {
                    let mut gp: GL = vec![];
                    for b in 0..dd {
                        let (sq, tq) = (sc[b], vb[(b + dd - k) % dd]);
                        gp.extend_from_slice(&[gx(tq), gc(h1, sq), gc(h1, tq), gt(sq, tq, h1)]);
                    }
                    pg_add(1, &gp);
                    gp.extend_from_slice(&g);
                    let mut dn: GL = vec![];
                    for b in (0..dd).rev() {
                        let (sq, tq) = (sc[b], vb[(b + dd - k) % dd]);
                        dn.extend_from_slice(&[gt(sq, tq, h1), gc(h1, tq), gt(d, sq, tq), gc(h1, sq), gx(tq)]);
                    }
                    pg_add(1, &dn);
                    gp.extend(dn);
                    self.b.t(&rev(&gp));
                    if k == 1 {
                        self.b.t(&swap_free(vb[dd - 1], y[W - fu - dd]));
                    }
                } else {
                    self.b.t(&rev(&g));
                }
            }
            if pgo {
                let mut lanes = vb.clone();
                lanes.push(y[W - lu - 1 - dd]);
                self.b.t(&rot_free(&lanes, 1));
                r7e_sub("sw_swap");
                { let (a_, k_) = swp_last(); self.t3(&sw_post, a_, k_, ["sw_swap", "sw_K2", "sw_sel"], false); }
                r7e_sub("rows");
            }
        }
        r7e_sub("post");
        if PO2_ODD_FREE_RISE && pgo && cad4_band(t) && (PO2_ODD_SITE < 0 || t == PO2_ODD_SITE) {
            let g = self.po2_odd_post(t);
            self.b.t(&g);
            let (xt, yt2) = (x[wv - 1], y[wv - 1]);
            self.arrive11(t - 1, &y, ctl);
            // the second state acts at the next even slot
            let g = self.m(&[(yt2, true), (xt, false), (y[0], false), (y[1], true), (h1, false)], h0);
            self.b.t(&g);
            self.b.t(&[gx(ctl)]);
            return;
        }
        let g = self.m(&cat(&al, &[(y[0], false)]), ctl);
        self.b.t(&g);
        let g = rotate_up(ctl, &y, wv - 1);
        self.b.t(&g);
        let g = self.m(&al, ctl);
        self.b.t(&g);
        let mut g = vec![];
        for w in 1..wv {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        if pgo {
            let g = self.post_page_k(ctl, SW2_POST_AND);
            pg_add(7, &g);
            self.b.t(&g);
        }
        let xt = x[wv - 1];
        self.b.t(&[gc(ctl, y[wv - 1])]);
        let g = self.m(&al, ctl);
        self.b.t(&g);
        let fl = y[wv - 1];
        let aa = cat(&[(fl, true)], &self.hc(0));
        let win: Vec<u32> = y[..wv - 1].to_vec();
        let g = self.m(&cat(&aa, &[(xt, false), (y[wv - 2], false)]), ctl);
        self.b.t(&g);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        let g = self.m(&cat(&aa, &[(xt, false), (y[0], false)]), ctl);
        self.b.t(&g);
        // acted: E'=0 and the second state take code 01 (the common rise gives 00); E'=2 stays 00 (the rise gives 10 and a marker)
        let mut g = self.m(&cat(&[(fl, true), (xt, true)], &self.hc(0)), ctl);
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hc(0)), ctl));
        g.push(gc(ctl, h0));
        g.extend(self.m(&cat(&[(fl, true), (xt, true), (y[0], true)], &self.hc(1)), ctl));
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hc(1)), ctl));
        self.b.t(&g);
        let mut g = self.m(&cat(&[(xt, true), (y[0], true)], &self.hc(1)), fl);
        g.extend(self.m(&cat(&[(xt, false), (y[0], false), (y[1], true)], &self.hc(0)), fl));
        g.extend(self.m(&cat(&[(y[wv - 2], true), (xt, false), (y[0], true)], &self.hc(1)), fl));
        self.b.t(&g);
        self.b.t(&[gx(y[wv - 1]), gc(y[wv - 1], ctl), gx(y[wv - 1])]);
        // LOOK16: a frozen shot (not at the top, code 11, flag on y[wv-2]) takes no part in the rise block or the rotation
        let frz: Vec<Lit> = if l16_frz(t) { cat(&[(y[wv - 1], false), (y[wv - 2], true)], &self.hc(3)) } else { vec![] };
        if l16_frz(t) {
            let g = self.m(&frz, ctl);
            self.tsub("l16_freeze", &g);
        }
        // one slot of rise for every shot not at the top
        let mut g = self.m(&cat(&[(ctl, true)], &self.hc(0)), y[0]);
        g.extend(self.m(&[(ctl, true), (y[0], true), (h0, false)], h1));
        g.extend(self.m(&[(ctl, true), (h1, false)], h0));
        g.extend(self.m(&[(ctl, true), (h0, true), (xt, true), (y[wv - 3], true)], h1));
        g.extend(self.m(&[(ctl, true), (h0, true), (xt, false), (y[wv - 4], true)], h1));
        g.extend(self.m(&cat(&[(ctl, true), (xt, true)], &self.hc(1)), y[wv - 3]));
        g.extend(self.m(&cat(&[(ctl, true), (xt, false)], &self.hc(1)), y[wv - 4]));
        self.b.t(&g);
        let g = rotate_up(ctl, &y, 1);
        self.b.t(&g);
        if l16_frz(t) {
            let g = self.m(&frz, ctl);
            self.tsub("l16_freeze", &g);
        }
        let yt2 = y[wv - 1];
        let mut g = vec![gx(ctl)];
        g.extend(self.m(&cat(&[(yt2, true)], &self.hc(3)), ctl));
        g.extend(self.m(&cat(&[(yt2, true)], &self.hc(1)), ctl));
        if cad4_band(t) {
            g.extend(self.m(&cat(&cat(&[(yt2, true)], &self.hc(2)), &[(self.w1, true)]), ctl));
        }
        self.b.t(&g);
        self.arrive11(t - 1, &y, ctl);
        // the second state acts at the next even slot
        let g = self.m(&[(yt2, true), (xt, false), (y[0], false), (y[1], true), (h1, false)], h0);
        self.b.t(&g);
        self.b.t(&[gx(ctl)]);
    }
    fn even11(&mut self, t: i32) {
        r7e_sub("head");
        let wv = self.wr;
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        // CAD4: c4l = this slot runs only e <= 3 (the W1 waiters step aside); c4p = the W1 waiters act here
        let (c4l, c4p) = (cad4_low(t), cad4_p4(t));
        let w1l = self.w1;
        let prs: Vec<i32> = pairs(t).into_iter().filter(|&e| e <= if c4l { 3 } else { 9 }).collect();
        let big: Vec<i32> = prs.iter().cloned().filter(|&e| e >= 2).collect();
        // CAD4: (class, wait) pairs of the generic rows; a waiter of class e has l and f one larger (slot t + 2's)
        let pr: Vec<(i32, i32)> = big.iter().flat_map(|&e| (0..(if c4p && e >= 4 { 2 } else { 1 })).map(move |w| (e, w))).collect();
        assert!(pr.iter().all(|p| { let (l, f) = lf(t, p.0); l + p.1 >= 1 && f + p.1 <= N as i32 }));
        let kk = 1 + big.iter().cloned().max().unwrap_or(0);
        let yt = y[wv - 1];
        let (x0, y0, y1) = (x[0], y[0], y[1]);
        let (d, ctl) = (x0, x0);
        let cl: Vec<Lit> = vec![(yt, true), (h1, true)];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        self.b.t(&[gx(x0)]);
        if l16_early(t) {
            r7e_sub("l16_norm");
            self.l16_norm(t);
            r7e_sub("head");
        }
        if c4l {
            // CAD4: the W1 waiters step aside before the rows (a down-rotation; the post's relabel undoes it)
            let mut g = self.m(&[(yt, true), (h1, true), (w1l, true)], ctl);
            if CAD4B {
                // the big waiters (code 10 at the top, Y[1] = 0; the gap-1 second form has Y[1] = 1) go with them
                g.extend(self.m(&cat(&cat(&[(yt, true)], &self.hc(1)), &[(y1, false)]), ctl));
            }
            let n_fz = g.len();
            if l16_frz(t) {
                // LOOK16: the frozen shots step aside too
                g.extend(self.m(&cat(&[(y[wv - 1], false), (y[wv - 2], true)], &self.hc(3)), ctl));
            }
            { let n_e = g.len(); self.tsplit(&g, &[(n_fz, "head"), (n_e, "l16_freeze")]); }
            let g = rotate_up(ctl, &y, wv - 1);
            self.b.t(&g);
            let mut g = self.m(&[(y[wv - 1], false), (y[wv - 2], true), (h1, true), (w1l, true)], ctl);
            if CAD4B {
                g.extend(self.m(&cat(&[(y[wv - 1], false), (y[wv - 2], true)], &self.hc(1)), ctl));
            }
            let n_fz2 = g.len();
            if l16_frz(t) {
                g.extend(self.m(&cat(&[(y[wv - 1], false), (y[wv - 2], false), (y[wv - 3], true)], &self.hc(3)), ctl));
            }
            { let n_e = g.len(); self.tsplit(&g, &[(n_fz2, "head"), (n_e, "l16_freeze")]); }
        }
        // CAD4 page sites: a waiter's ring lanes sit one wire lower than its class's: conjugate the site's use by a
        // W1-controlled up-rotation of the lanes [lo, hi] (the waiter's content of lane i goes to lane i + 1)
        let w1c = |lanes: &[u32]| -> GL { rotate_up(w1l, lanes, 1) };
        // EVJS swaps of one (l, f) geometry under control c; cof = C form
        let dd_ = PAGE_D;
        let pgv = self.pg.clone();
        let (xs, ys) = (x.clone(), y.clone());
        let ejs = move |l: i32, f: i32, c: u32, cof: bool| -> GL {
            let (lu, fu) = (l as usize, f as usize);
            let mut g: GL = vec![];
            for b in 0..dd_ {
                if cof {
                    cswap(c, pgv[dd_ + b], ys[wv - lu + 2 * dd_ - 1 - b], &mut g);
                    cswap(c, pgv[2 * dd_ + b], xs[wv - fu + 2 * dd_ - 1 - b], &mut g);
                } else {
                    cswap(c, pgv[dd_ + b], ys[wv - lu + b], &mut g);
                    cswap(c, pgv[b], xs[wv - fu + b], &mut g);
                }
            }
            g
        };
        // EVJS: the W1 conjugation (waiters' lanes one wire lower) over the union span of the waiter classes' swap lanes
        let ejs_cj = |cof: bool, gate: bool| -> GL {
            if !c4p { return vec![]; }
            let ws: Vec<i32> = big.iter().cloned().filter(|&e| e >= 4).collect();
            if ws.is_empty() { return vec![]; }
            let o = if cof { dd_ } else { 0 };
            let (mut g, mut sp): (GL, Vec<(usize, usize, bool)>) = (vec![], vec![]);
            let (ly, hy) = (ws.iter().map(|&e| wv - lf(t, e).0 as usize - 1 + o).min().unwrap(), ws.iter().map(|&e| wv - lf(t, e).0 as usize + dd_ - 1 + o).max().unwrap());
            let (lx, hx) = (ws.iter().map(|&e| wv - lf(t, e).1 as usize - 1 + o).min().unwrap(), ws.iter().map(|&e| wv - lf(t, e).1 as usize + dd_ - 1 + o).max().unwrap());
            sp.push((ly, hy, true)); sp.push((lx, hx, false));
            for (lo, hi, isy) in sp {
                let lanes: Vec<u32> = (lo..=hi).map(|a| if isy { y[a] } else { x[a] }).collect();
                if gate {
                    // E3V: W1 also marks the big shots (W1 & !h1): rotate only the CAD4 waiters (W1 & h1), via ZB
                    g.push(gt(w1l, h1, ZB_LANE));
                    g.extend(rotate_up(ZB_LANE, &lanes, 1));
                    g.push(gt(w1l, h1, ZB_LANE));
                } else {
                    g.extend(w1c(&lanes));
                }
            }
            g
        };
        let mut g: GL = vec![];
        for &e in &big {
            if e & 1 == 1 {
                let mut l = cl.clone();
                if c4p && e >= 4 {
                    // a waiter with e odd never took code 11
                    l.push((w1l, false));
                }
                for j in 1..(e as usize - 1) {
                    l.push((y[j], false));
                }
                l.push((y[e as usize - 1], true));
                g.extend(self.m(&l, h0));
            }
        }
        self.b.t(&g);
        let sp0: Vec<Lit> = cat(&[(yt, true)], &self.hc(0));
        self.mk(t, 1);
        let sp1: Vec<Lit> = cat(&cat(&[(yt, true)], &self.hc(1)), &[(y1, true)]);
        let sp1c: Vec<Lit> = cat(&cat(&[(yt, true)], &self.hc(1)), &[(x[wv - 1], false), (x[wv - 2], false)]);
        let merge0 = prs.contains(&0) && !big.is_empty();
        let merge1 = MERGE1 && ZB > 0 && prs.contains(&1) && !big.is_empty();
        r7e_sub("plain_gap01");
        if prs.contains(&0) && !merge0 {
            let (l, _f) = lf(t, 0);
            let lu = l as usize;
            let c1 = self.m(&sp0, d);
            self.b.t(&c1);
            let tv: Vec<u32> = ((wv - lu)..(wv - 1)).map(|a| x[a]).collect();
            let sv: Vec<u32> = ((wv - lu)..(wv - 1)).map(|a| y[a]).collect();
            let g = self.plain_v(&tv, &sv, x[wv - 1], d, h0);
            self.b.t(&g);
            self.b.t(&c1);
        }
        if prs.contains(&1) && !merge1 {
            let (l, _f) = lf(t, 1);
            let lu = l as usize;
            let c1 = self.m(&sp1, d);
            self.b.t(&c1);
            // P1: e = 1 at an even slot (q = 1, shift 0): with the global page its chain starts at B bit D
            let pg1 = PAGE_G && mid_even(t);
            let s0 = if pg1 { PAGE_D } else { 0 };
            let tv: Vec<u32> = ((wv - lu - 1 + s0)..(wv - 2)).map(|a| x[a]).collect();
            let sv: Vec<u32> = ((wv - lu - 1 + s0)..(wv - 2)).map(|a| y[a + 1]).collect();
            let g = self.plain_v(&tv, &sv, x[wv - 2], d, h1);
            if pg1 {
                let (pa, pb) = (&self.pg[..PAGE_D], &self.pg[PAGE_D..2 * PAGE_D]);
                let mut up: GL = vec![];
                let mut dn: GL = vec![];
                for b in 0..PAGE_D {
                    up.extend_from_slice(&[gx(pa[b]), gc(h1, pb[b]), gc(h1, pa[b]), gt(pb[b], pa[b], h1)]);
                }
                for b in (0..PAGE_D).rev() {
                    dn.extend_from_slice(&[gt(pb[b], pa[b], h1), gc(h1, pa[b]), gt(d, pb[b], pa[b]), gc(h1, pb[b]), gx(pa[b])]);
                }
                pg_add(1, &up); pg_add(1, &dn);
                self.b.t(&up);
                self.b.t(&g);
                self.b.t(&dn);
            } else {
                self.b.t(&g);
            }
            self.b.t(&c1);
        }
        self.mk(t, 2);
        let lik = |k: i32| -> Vec<Lit> {
            let mut l = cl.clone();
            if k >= 3 {
                for j in 1..(k as usize - 1) {
                    l.push((y[j], false));
                }
            }
            l
        };
        let pgo = PAGE_G && mid_even(t);
        assert!(!pgo || (merge0 && !big.is_empty()));
        let pv = (PAGE_V || PAGE_C || pgo) && mid_even(t) && !big.is_empty();
        let pc = (PAGE_C || pgo) && pv;
        let local = pc && !pgo;
        // EVJS: the ladder slots run the low rows at page offset 0 (junction swaps instead of windows)
        let evjs = evjs_on() && LADDER && pgo && (2..=9).all(|e| big.contains(&e));
        // E3V state (see the switch)
        let bprs: Vec<(i32, i32, i32, i32)> = if evjs && t % 8 == 0 { self.big_pairs11(t) } else { vec![] };
        let e3 = e3v_on() && togv_on() && evjs && t % 8 == 0 && !bprs.is_empty() && JSWAP && JSWAP_V && !(TIER_LONG > 0 && long16(t) && t.rem_euclid(16) == 0);
        // W4HOST: at a slot 8 mod 16 of the long region the long waiters stay (code 01, no act): mark the actors by their cubes
        let e3b8 = e3 && TIER_LONG > 0 && long16(t) && t.rem_euclid(16) == 8;
        self.e3t = e3;
        let clb: Vec<Lit> = if e3b8 { vec![(yt, true), (h1, false), (w1l, true)] } else { vec![(yt, true), (h0, true), (h1, false), (y1, false)] };
        let bes: BTreeSet<i32> = bprs.iter().map(|p| p.0).collect();
        let hb0: Vec<u32> = vec![y[2], y[3], y[7], y[8]];
        let (bw0, bw1, bw2) = (y[4], y[5], y[6]);
        let mut bpre: GL = vec![];
        let mut bcv: GL = vec![];
        if e3 {
            for &e in &bes {
                let mut li = clb.clone();
                for j in 9..(e as usize - 1) { li.push((y[j], false)); }
                li.push((y[e as usize - 1], true));
                let m_ = e >> 1;
                for i in 0..4 { if (m_ >> i) & 1 == 1 { bpre.extend(self.m(&li, hb0[i])); } }
            }
            for &e in &bes {
                let mut li = clb.clone();
                for i in 0..4 { li.push((hb0[i], ((e >> 1) >> i) & 1 == 1)); }
                li.push((bw0, e & 1 == 1));
                bpre.extend(self.m(&li, y[e as usize - 1]));
            }
            bcv = dec_ctl(&hb0, &cat(&clb, &[(bw1, true)]), &self.dirty);
            bcv.extend(dec_ctl(&hb0[1..], &cat(&clb, &[(bw2, true)]), &self.dirty));
        }
        // LOOK16 h1 hosted code at this tier: A = y2, y3, y7 (hi' = (e >> 1) - 5, then U3 = u - 2), B = y4, y5, y6, y8 (r, then
        // V4 = v - 1); the prefix writes hi' (marker -> hi'), bcv is A -> U3
        let l16 = e3 && l16h(t);
        let a3: Vec<u32> = vec![y[2], y[3], y[7]];
        let b4: Vec<u32> = vec![y[4], y[5], y[6], y[8]];
        let lanes7: Vec<u32> = vec![y[2], y[3], y[7], y[4], y[5], y[6], y[8]];
        if l16 {
            assert!(e3c_on() && e3c2_on() && evjs && pgo, "LOOK16: the h1 code needs E3C + E3C2 at the tier");
            bpre = vec![];
            for &e in &bes {
                let mut li = clb.clone();
                for j in 9..(e as usize - 1) { li.push((y[j], false)); }
                li.push((y[e as usize - 1], true));
                let hp = (e >> 1) - 5;
                for i in 0..3 { if (hp >> i) & 1 == 1 { bpre.extend(self.m(&li, a3[i])); } }
            }
            for &e in &bes {
                let mut li = clb.clone();
                let hp = (e >> 1) - 5;
                for i in 0..3 { li.push((a3[i], (hp >> i) & 1 == 1)); }
                li.push((bw0, e & 1 == 1));
                bpre.extend(self.m(&li, y[e as usize - 1]));
            }
            bcv = self.l16_cu(&a3, &b4, &clb);
        }
        let bhterm = |vals: &BTreeSet<i32>, others: &BTreeSet<i32>| -> Vec<Vec<Lit>> {
            let (mut on, mut off) = (0u128, 0u128);
            for &v in vals { on |= 1u128 << (v % 16); }
            for &v in others { off |= 1u128 << (v % 16); }
            dtree(on, off, &[0, 1, 2, 3], 0).iter().map(|c| c.iter().map(|&(v, b)| (hb0[v], b == 1)).collect()).collect()
        };
        // E3C state (see the switch): the big family literal (W1 marks the big actors, h1 = 0 parts them from the CAD4
        // waiters), the big classes' top, act cubes on (hi, w0), group terms on any 4 lanes, class flags, family moves
        let e3c = e3 && e3c_on() && TIER_LONG == 0 && !e3b8 && pgo && evjs;
        E3C_T.store(e3c, Ordering::Relaxed);
        let famb: Vec<Lit> = vec![(yt, true), (h1, false), (w1l, true)];
        let kkb: i32 = bes.iter().next_back().map(|e| e + 1).unwrap_or(0);
        let lanes_vb: Vec<u32> = vec![hb0[0], hb0[1], hb0[2], hb0[3], bw0, bw1, bw2];
        let hterm_l = |vals: &BTreeSet<i32>, others: &BTreeSet<i32>, lanes: &[u32]| -> Vec<Vec<Lit>> {
            let (mut on, mut off) = (0u128, 0u128);
            for &v in vals { on |= 1u128 << (v % 16); }
            for &v in others { off |= 1u128 << (v % 16); }
            dtree(on, off, &[0, 1, 2, 3], 0).iter().map(|c| c.iter().map(|&(v, b)| (lanes[v], b == 1)).collect()).collect()
        };
        let bexact = |k: i32, lanes: &[u32], fam: &[Lit]| -> Vec<Vec<Lit>> {
            let (mut on, mut off) = (0u128, 0u128);
            for &e in &bes {
                let p_ = (e >> 1) | ((e & 1) << 4);
                if e >= k { on |= 1u128 << p_; } else { off |= 1u128 << p_; }
            }
            dtree(on, off, &[0, 1, 2, 3, 4], 1).iter().map(|c| {
                let mut l: Vec<Lit> = c.iter().map(|&(v, b)| (lanes[v], b == 1)).collect();
                l.extend_from_slice(fam);
                l
            }).collect()
        };
        let bcflag = |me: &Self, e: i32| -> GL {
            let (mut on, mut off): (Vec<usize>, Vec<usize>) = (vec![], vec![]);
            if l16 {
                for c in &bprs { if c.0 == e { on.push(l16_pt(0, c)); } else { off.push(l16_pt(0, c)); } }
                let mut g: GL = vec![];
                for cube in l16_cubes(&on, &off, &lanes7) { g.extend(me.m(&[cube, famb.clone()].concat(), x0)); }
                return g;
            }
            for &(e2, w, _u, _v) in &bprs {
                let pt = ((e2 >> 1) | (w << 4)) as usize;
                if e2 == e { on.push(pt); } else { off.push(pt); }
            }
            let mut g: GL = vec![];
            for cube in hw_cubes(&on, &off, &lanes_vb, NONE) {
                g.extend(me.m(&[cube, famb.clone()].concat(), x0));
            }
            g
        };
        let mvf = |me: &Self, src: u32, dst: u32| -> GL {
            let mut g = me.m(&[famb.clone(), vec![(src, true)]].concat(), dst);
            g.extend(me.m(&[famb.clone(), vec![(dst, true)]].concat(), src));
            g
        };
        // E3C2: family-gated toggle of tgt by the cases whose class satisfies sel, on the converted points (h | w << 4),
        // h = u (V side, after bcv) or v mod 16 (C side, after the hoisted hi -> v)
        let e3c2 = e3c && e3c2_on();
        let e3r2 = e3c && e3c2r2_on();
        let bflag = |me: &Self, sel: &dyn Fn(i32) -> bool, cof: bool, tgt: u32| -> GL {
            let (mut on, mut off): (Vec<usize>, Vec<usize>) = (vec![], vec![]);
            if l16 {
                for c in &bprs { let pt = l16_pt(if cof { 2 } else { 1 }, c); if sel(c.0) { on.push(pt); } else { off.push(pt); } }
                let mut g: GL = vec![];
                for cube in l16_cubes(&on, &off, &lanes7) { g.extend(me.m(&[cube, famb.clone()].concat(), tgt)); }
                return g;
            }
            for &(e2, w, u, v) in &bprs {
                let h = if cof { v.rem_euclid(16) } else { u };
                let pt = (h | (w << 4)) as usize;
                if sel(e2) { on.push(pt); } else { off.push(pt); }
            }
            let mut g: GL = vec![];
            for cube in hw_cubes(&on, &off, &lanes_vb, NONE) {
                g.extend(me.m(&[cube, famb.clone()].concat(), tgt));
            }
            g
        };
        // AKB_E3C2_KEY (see the switch): the class-coded register for E3C2's toggles
        let e3k = e3c2 && l16 && AKB_E3C2_KEY;
        let e3k_cv = |me: &Self, cof: bool| -> GL {
            // V (cof false): B[1..3] += A mod 8; C (cof true): A += B[0..2] mod 8; bit i = an increment of the register's top
            // 3 - i lanes under famb & addend bit i
            let (r_, s_): (Vec<u32>, Vec<u32>) = if cof { (a3.clone(), b4[..3].to_vec()) } else { (b4[1..].to_vec(), a3.clone()) };
            let mut g: GL = vec![];
            for i in 0..3usize { g.extend(inc_ctl(&r_[i..], &cat(&famb, &[(s_[i], true)]), &me.dirty)); }
            g
        };
        let e3k_pt = |c: &(i32, i32, i32, i32), cof: bool| -> usize {
            let (_e, w, u, v) = *c;
            let (u3, r, v4) = (u - 2, w.rem_euclid(16), v - 1);
            let (a, b) = if cof { ((u3 + (v4 & 7)).rem_euclid(8), v4) } else { (u3, (2 * u3 + r).rem_euclid(16)) };
            assert!((0..8).contains(&a) && (0..16).contains(&b), "AKB_E3C2_KEY: point out of range");
            (a | (b << 3)) as usize
        };
        let e3k_flag = |me: &Self, sel: &dyn Fn(i32) -> bool, cof: bool, tgt: u32| -> GL {
            let (mut on, mut off): (Vec<usize>, Vec<usize>) = (vec![], vec![]);
            for c in &bprs { let pt = e3k_pt(c, cof); if sel(c.0) { on.push(pt); } else { off.push(pt); } }
            let mut g: GL = vec![];
            for cube in l16_cubes(&on, &off, &lanes7) { g.extend(me.m(&[cube, famb.clone()].concat(), tgt)); }
            g
        };
        // E3C: the big hosted lanes during the C rows (big_phase moves them to the consumed digit lanes before rows 9..3)
        let mut hbc: Vec<u32> = hb0.clone();
        let mut ac: [u32; 3] = [bw0, bw1, bw2];
        let sp1cs: Vec<Vec<Lit>> = if e3 { vec![cat(&sp1c, &[(w1l, false)])] } else { vec![sp1c.clone()] };
        let fm_ = self.pg[4 * PAGE_D];
        let pd0 = if pgo && !evjs { PAGE_D as i32 } else { 0 };
        let pdc = if pc && !evjs { PAGE_D as i32 } else { 0 };
        let sc: Vec<u32> = if pc { self.pg[2 * PAGE_D..3 * PAGE_D].to_vec() } else { vec![] };
        let dig: Vec<u32> = (0..(if DS_PAGE_EDITS { 10 } else { PAGE_D.min(10) })).map(|k| if k == 0 { y0 } else { x[wv - k] }).collect();
        let pd = if pv && !evjs { PAGE_D as i32 } else { 0 };
        let (va, vb): (Vec<u32>, Vec<u32>) = if pv { (self.pg[..PAGE_D].to_vec(), self.pg[PAGE_D..2 * PAGE_D].to_vec()) } else { (vec![], vec![]) };
        // flag of exactly class e (or of a set of classes sharing l): lik(lo) xor lik(hi + 1)
        let zf = if pv { self.pg[4 * PAGE_D + 1] } else { NONE };
        let lad = LADDER && pgo && (2..=9).all(|e| big.contains(&e));
        // digit remap of class e (reverse dig[0..=e]) under control c
        let rmb = |c: u32, e: i32| -> GL {
            let mut rm: GL = vec![];
            let eu = e as usize;
            let mut i = 0usize;
            while i < eu - i {
                cswap(c, dig[i], dig[eu - i], &mut rm);
                i += 1;
            }
            rm
        };
        let fl_cls = |me: &Self, lo: i32, hi: i32| -> GL {
            // exactly class e: (yt, h1), Y[1..e-2] zero, marker Y[e-1]; AND on the clean lane Z (2k - 3)
            let mut g: GL = vec![];
            for e in lo..=hi {
                let mut l = cl.clone();
                for j in 1..(e as usize - 1) {
                    l.push((y[j], false));
                }
                l.push((y[e as usize - 1], true));
                g.extend(me.mz(&l, d, zf));
            }
            g
        };
        let fl_cit = |me: &Self, kp: i32, es: &[i32]| -> GL {
            let mut g: GL = vec![];
            for &e in es {
                let mut l = lik(kp.max(0));
                l.push((x[wv - e as usize], true));
                for j in kp.max(2)..e {
                    l.push((x[wv - j as usize], false));
                }
                g.extend(me.mz(&l, d, zf));
            }
            g
        };
        r7e_sub("flags_windows");
        // P1 (b2): local gather of the four low words of every acting low-class shot, then the implicit word is erased
        let gather4 = |me: &Self, post: bool| -> GL {
            let mut g: GL = vec![];
            for &e in &big {
                let (l, f) = lf(t, e);
                let (lu, fu) = (l as usize, f as usize);
                let fl = if post { fl_cit(me, 0, &[e]) } else { fl_cls(me, e, e) };
                g.extend_from_slice(&fl);
                let mut ga: GL = vec![];
                for j in 0..PAGE_D {
                    cswap(d, va[j], x[wv - fu + j], &mut ga);
                    cswap(d, vb[j], y[wv - lu + j], &mut ga);
                    cswap(d, me.pg[2 * PAGE_D + j], x[W - fu - 1 - j], &mut ga);
                    cswap(d, me.pg[3 * PAGE_D + j], y[W - lu - 1 - j], &mut ga);
                }
                pg_add(0, &ga); pg_add(4, &fl); pg_add(4, &fl);
                g.extend(ga);
                g.extend_from_slice(&fl);
            }
            g
        };
        if local {
            let mut g = gather4(self, false);
            let er = self.erase_blk(d);
            pg_add(0, &er);
            g.extend(er);
            self.b.t(&g);
        }
        if evjs {
            // EVJS V in: the low words of every acting low-class shot into its ring wires (merged e = 0, 1 by their own flags)
            let cj = ejs_cj(false, e3);
            pg_add(2, &cj); pg_add(2, &cj);
            self.b.t(&cj);
            let g = if fw_on("V-win-in") { self.fw_ladder(t, "V-win-in", false, 0) } else { self.ladder("V-win-in", &|set, c| {
                let (l, f) = lf(t, set[0]);
                let s_ = ejs(l, f, c, false);
                pg_add(3, &s_);
                s_
            }) };
            self.b.t(&g);
            self.b.t(&rev(&cj));
            let mut g: GL = vec![];
            if fw_on("V-win-in") && prs.contains(&0) && prs.contains(&1) {
                g = self.fw_e01(t, false, &sp0, &[sp1.clone()], d, zf);
            } else {
            for (lit, e) in [(&sp0, 0i32), (&sp1, 1i32)] {
                if !prs.contains(&e) { continue; }
                let (l, f) = lf(t, e);
                let fl = self.mz(lit, d, zf);
                let s_ = ejs(l, f, d, false);
                pg_add(3, &s_); pg_add(4, &fl); pg_add(4, &fl);
                g.extend_from_slice(&fl);
                g.extend(s_);
                g.extend_from_slice(&fl);
            }
            }
            self.b.t(&g);
        } else if lad {
            // CAD4B: one W1 conjugation over the union of the waiters' window lanes
            let cjv: GL = if c4p && CAD4B {
                let ix: Vec<usize> = big.iter().filter(|&&e| e >= 4).flat_map(|&e| { let fu = lf(t, e).1 as usize; (0..=e as usize).map(move |i| wv - fu - 1 + PAGE_D + i) }).collect();
                let cj = w1c(&x[*ix.iter().min().unwrap()..=*ix.iter().max().unwrap()]);
                pg_add(2, &cj); pg_add(2, &cj);
                cj
            } else { vec![] };
            self.b.t(&cjv);
            let g = self.ladder("V-win-in", &|set, c| {
                let e = set[0];
                let fu = lf(t, e).1 as usize;
                let mut lanes = va.clone();
                lanes.extend((0..e as usize).map(|i| x[wv - fu + PAGE_D + i]));
                let n = lanes.len();
                let ro = rotate_up(c, &lanes, n - e as usize);
                pg_add(2, &ro);
                if c4p && !CAD4B && e >= 4 {
                    let cj = w1c(&(0..=e as usize).map(|i| x[wv - fu - 1 + PAGE_D + i]).collect::<Vec<u32>>());
                    pg_add(2, &cj); pg_add(2, &cj);
                    return [cj.clone(), ro, rev(&cj)].concat();
                }
                ro
            });
            self.b.t(&g);
            self.b.t(&rev(&cjv));
        } else if pv {
            let mut g: GL = vec![];
            for &e in &big {
                let (l, f) = lf(t, e);
                let (lu, fu) = (l as usize, f as usize);
                let fl = fl_cls(self, e, e);
                g.extend_from_slice(&fl);
                let mut ga: GL = vec![];
                for j in 0..(if pc { 0 } else { PAGE_D }) {
                    cswap(d, va[j], x[wv - fu + j], &mut ga);
                    cswap(d, vb[j], y[wv - lu + j], &mut ga);
                }
                let mut lanes = va.clone();
                lanes.extend((0..e as usize).map(|i| x[wv - fu + PAGE_D + i]));
                let n = lanes.len();
                let ro = rotate_up(d, &lanes, n - e as usize);
                pg_add(0, &ga); pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl);
                g.extend(ga);
                g.extend(ro);
                g.extend_from_slice(&fl);
            }
            self.b.t(&g);
        }
        if e3 {
            // E3V: mark the big actors on W1 (they all have W1 = 0: arrive11 sets it only on code-10 shots), big prefix
            // (marker -> hi, code kept 01), big junction swap in, hi -> u, big rows 0 and 1 alone
            let mut g: GL = vec![];
            if e3b8 {
                for c in self.band8_actors(t, &y) { g.extend(self.m(&cat(&c, &[(h1, false)]), w1l)); }
                // every band8 actor arrived at 8..15 mod 16: its W4 (y[8] = hi's bit-3 host) is 1; clear it before the prefix
                g.extend(self.m(&clb, y[8]));
            } else {
                g = self.m(&clb, w1l);
            }
            self.b.t(&g);
            self.b.t(&bpre);
            if l16 && L16_TRIM {
                // L16_TRIM: bcv first, then the junction swap reads U3 directly
                self.tsub("h1_conv", &bcv);
                let g = self.l16_jswap_f(t, &bprs, &a3, &b4, false, &clb, 1);
                pg_add(8, &g);
                self.tsub("h1_jswap", &g);
            } else {
            let g = if l16 { self.l16_jswap(t, &bprs, &a3, &b4, false, &clb) } else { self.jswap_f(t, &bprs, &hb0, [bw0, bw1, bw2], false, false, NONE, &clb) };
            pg_add(8, &g);
            self.b.t(&g);
            self.b.t(&bcv);
            }
            let allu: BTreeSet<i32> = bprs.iter().map(|p| p.2).collect();
            let e3n: i32 = if std::env::var("R7A_E3_LOWONLY").is_ok() { 10 } else if LR_V01 && !e3b8 { 0 } else { e3from() };
            for k in 0..e3n {
                let mut stb: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
                for p in &bprs { stb.entry(wv as i32 - (t / 2 - p.2) - k).or_default().insert(p.2); }
                let alob = *stb.keys().next().unwrap();
                assert!(alob + k >= 10);
                let (ku, au) = (k as usize, alob as usize);
                let tv: Vec<u32> = (au..(wv - ku - 1)).map(|a| x[a]).collect();
                let sv: Vec<u32> = (au..(wv - ku - 1)).map(|a| y[a + ku]).collect();
                let t1 = x[wv - 1 - ku];
                let top = if k >= 1 { x[wv - ku] } else { NONE };
                let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                for (&a, us) in &stb {
                    let rest: BTreeSet<i32> = allu.difference(us).cloned().collect();
                    tg.insert((a - alob) as usize, if l16 { l16_keys(us, &rest, &a3, 2) } else { bhterm(us, &rest) });
                }
                let actb = vec![clb.clone()];
                let g = self.row_v(&tv, &sv, t1, top, d, y[9], fm_, &tg, &actb, None, None);
                self.b.t(&g);
                let mut g: GL = vec![];
                if k >= 1 {
                    g.extend(self.m(&cat(&clb, &[(x[wv - ku], true)]), d));
                } else {
                    g.extend(self.m(&cat(&clb, &[(d, true)]), y0));
                    g.extend(self.m(&cat(&clb, &[(y0, true)]), d));
                }
                self.b.t(&g);
            }
        }
        self.mk(t, 3);
        // NR_PARK_V (see the switch): the plain full ladder slots only
        let nrp = NR_PARK_V && evjs && !e3 && togv_on() && kk == 10 && self.pg.len() == 4 * PAGE_D + 2;
        let nr_park: GL = if nrp { self.nr_park_v(t) } else { vec![] };
        for k in 0..kk {
            r7e_sub("V_rows");
            let act: Vec<(i32, i32)> = pr.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() {
                continue;
            }
            let starts: Vec<(i32, i32, i32)> = act.iter().map(|p| (p.0, p.1, wv as i32 - (lf(t, p.0).0 + p.1) - k + pd)).collect();
            let m0 = merge0 && k == 0;
            let m1 = merge1 && k == 1;
            let alo1 = starts.iter().map(|p| p.2).min().unwrap();
            let shi = starts.iter().map(|p| p.2).max().unwrap();
            let alo = if m0 { (wv as i32) - t / 2 + pd0 } else if m1 { (wv as i32) - t / 2 - 1 + pd0 } else { alo1 };
            assert!(!(m0 || m1) || alo < alo1);
            let (ku, alo_u) = (k as usize, alo as usize);
            let tv: Vec<u32> = (alo_u..(wv - ku - 1)).map(|a| x[a]).collect();
            let sv: Vec<u32> = (alo_u..(wv - ku - 1)).map(|a| y[a + ku]).collect();
            let t1 = x[wv - 1 - ku];
            let top = if k >= 1 { x[wv - ku] } else { NONE };
            let li = lik(k);
            let lr01 = LR_V01 && e3 && !e3b8;
            let e3k = e3 && ((if lr01 { 0 } else { e3from() })..=9).contains(&k);
            // LR_V01: rows 0 and 1 shared with the big family (special forms kept: low mask verbatim, family [!H1, W1])
            let lrk = lr01 && k <= 1;
            let e3lo = std::env::var("R7A_E3_LOWONLY").is_ok();
            let mut actv: Vec<Vec<Lit>> = vec![li];
            if e3k && std::env::var("R7A_E3_LOWONLY").is_err() { actv.push(vec![(yt, true), (h1, false), (w1l, true)]); }
            let mn = act.iter().map(|p| p.0).min().unwrap();
            let both = act.iter().any(|p| p.1 == 1);
            let mut il: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for i in 0..(shi - alo + 1) {
                let a = alo + i;
                let mut cu: Vec<Vec<Lit>> = vec![vec![]];
                if (m0 || m1) && a < alo1 {
                    // below every low start: only the merged class fires; one cancel cube for all of code 1x
                    cu.push(vec![(h1, true)]);
                } else {
                    // per wait value: the classes of that wait whose start is above this wire are cancelled
                    for wq in 0..2 {
                        let off = starts.iter().filter(|p| p.1 == wq && p.2 > a).map(|p| p.0).min();
                        if let Some(yy) = off {
                            // CAD4B: a waiter is a class >= 4, its Y[1], Y[2] are 0
                            let lo = if CAD4B && both && wq == 1 { 3 } else { (mn - 1).max(1) as usize };
                            let mut ch: Vec<Lit> = vec![];
                            if m0 || m1 {
                                ch.push((h1, true));
                            }
                            if both {
                                ch.push((w1l, wq == 1));
                            }
                            ch.extend((lo..((yy - 1).max(0) as usize)).map(|j| (y[j], false)));
                            cu.push(ch);
                        }
                    }
                }
                il.insert(i as usize, cu);
            }
            let (tgv, tvs, svs): (BTreeMap<usize, Vec<Vec<Lit>>>, Vec<u32>, Vec<u32>) = if e3k {
                // E3V shared row: low cubes get the family literal h1 (and are all off below the low start), the big shots
                // start off (cube !h1) and turn on at their group's start (hterm on u, & !h1); the chain starts at the lower
                // of the two families' starts
                let mut sb: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
                for p in &bprs { sb.entry(wv as i32 - (t / 2 - p.2) - k).or_default().insert(p.2); }
                if e3lo { sb.clear(); sb.insert(alo, BTreeSet::new()); }
                let allu: BTreeSet<i32> = bprs.iter().map(|p| p.2).collect();
                let bhi = *sb.keys().next_back().unwrap();
                assert!(!lrk || *sb.keys().next().unwrap() >= alo, "LR_V01: a big start below the low chain start");
                let alos = alo.min(*sb.keys().next().unwrap());
                assert!(alos + k >= 10, "E3V: shared row reaches the hosted lanes");
                let n = (shi.max(bhi) - alos + 1) as usize;
                let mut ilc: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                for i in 0..n {
                    let a = alos + i as i32;
                    let mut cu: Vec<Vec<Lit>> = vec![];
                    let low: Vec<Vec<Lit>> = if a < alo { vec![vec![], vec![(h1, true)]] } else { il.get(&((a - alo) as usize)).cloned().unwrap_or_else(|| vec![vec![]]) };
                    // LR_V01 rows 0 / 1: the special gap-0 / gap-1 actors have H1 = 0 too, so the family is [!H1, W1]
                    let famv: Vec<Lit> = if lrk { vec![(h1, false), (w1l, true)] } else { vec![(h1, false)] };
                    for c in low {
                        let mut c = c;
                        if !lrk && !c.is_empty() && !c.contains(&(h1, true)) { c.push((h1, true)); }
                        cu.push(c);
                    }
                    cu.push(famv.clone());
                    for (&sa, us) in &sb {
                        if sa <= a && !e3lo {
                            let rest: BTreeSet<i32> = allu.difference(us).cloned().collect();
                            for c in if l16 { l16_keys(us, &rest, &a3, 2) } else { bhterm(us, &rest) } {
                                // BK_D1 (see the switch): rows 4..9, a positive literal on y[1..=k-2] makes !h1 redundant
                                if BK_D1 && l16 && !lrk && ku >= 4 && c.iter().any(|&(q0, p)| p && y[1..(ku - 1)].contains(&q0)) {
                                    cu.push(c);
                                } else {
                                    cu.push(cat(&c, &famv));
                                }
                            }
                        }
                    }
                    ilc.insert(i, cu);
                }
                let au = alos as usize;
                let tvs: Vec<u32> = (au..(wv - ku - 1)).map(|a| x[a]).collect();
                let svs: Vec<u32> = (au..(wv - ku - 1)).map(|a| y[a + ku]).collect();
                (tog_of(&ilc), tvs, svs)
            } else { (tog_of(&il), tv.clone(), sv.clone()) };
            let h0t: GL = if e3k { self.m(&[(w1l, true), (h1, false)], h0) } else { vec![] };
            self.b.t(&h0t);
            let nrk = nrp && k >= 2;
            if nrk {
                let fm = self.pg[4 * PAGE_D];
                if k == 2 {
                    assert!(pd == 0 && !e3k && !ZB_BUSY.load(Ordering::Relaxed));
                    self.b.t(&nr_park);
                    ZB_BUSY.store(true, Ordering::Relaxed);
                }
                // the act cubes on the held flag: class >= 2; class >= 4 or class 3 exactly; class >= k
                actv = if k == 2 {
                    vec![cl.clone()]
                } else if k == 3 {
                    vec![vec![(fm, true)], vec![(yt, true), (h1, true), (y[1], false), (fm, false)]]
                } else {
                    let mut a: Vec<Lit> = vec![(fm, true)];
                    a.extend((3..(ku - 1)).map(|j| (y[j], false)));
                    vec![a]
                };
            }
            let g = if nrk {
                self.nr_row_plain(&tv, &sv, t1, top, d, h0, &actv)
            } else if togv_on() {
                let fm = self.pg[4 * PAGE_D];
                // BK_L3B_E3 (see the switch): E3 shared V rows 2..9 at the kept tiers
                let cut = if BK_L3B_E3 && e3k && l16 && !lrk && k >= 2 && !(m0 || m1) { bk_l3b_cut(&tgv, &actv, tvs.len()) } else { None };
                if let Some((last, tg2)) = cut {
                    BK_WCUT.store(last, Ordering::Relaxed);
                    let g = self.row_vmask(&tvs, &svs, t1, top, d, h0, fm, &tg2, &actv, m0 || m1);
                    BK_WCUT.store(usize::MAX, Ordering::Relaxed);
                    g
                } else {
                    self.row_vmask(&tvs, &svs, t1, top, d, h0, fm, &tgv, &actv, m0 || m1)
                }
            } else {
                self.row_vz(&tv, &sv, t1, top, d, h0, NONE, &no_tog, &actv, Some(&il), None, m0 || m1)
            };
            let wg: Vec<Lit> = if lrk { vec![(w1l, false)] } else { vec![] };
            let c1 = if m0 {
                self.m(&cat(&sp0, &wg), d)
            } else if m1 {
                let mut c1 = self.m(&cat(&sp1, &wg), d);
                c1.extend(self.m(&cat(&[(d, true), (h1, false)], &wg), h0));
                if pv && !evjs {
                    let z1 = ZB_LANE;
                    c1.extend_from_slice(&[gx(h1), gt(d, h1, z1), gx(h1)]);
                    let ro = rotate_up(z1, &va, PAGE_D - 1);
                    pg_add(2, &ro); pg_add(2, &ro);
                    c1.extend(ro);
                    c1.extend_from_slice(&[gx(h1), gt(d, h1, z1), gx(h1)]);
                }
                c1
            } else {
                vec![]
            };
            self.b.t(&c1);
            if pv && !evjs {
                // page cells: the bottom D cells of the row's chain, source bit b <-> window lane (b - k) mod D
                let mut up: GL = vec![];
                for b in 0..PAGE_D {
                    let (sq, tq) = (vb[b], va[(b + PAGE_D - ku % PAGE_D) % PAGE_D]);
                    up.extend_from_slice(&[gx(tq), gc(h0, sq), gc(h0, tq), gt(sq, tq, h0)]);
                }
                pg_add(1, &up);
                r7e_sub("page_cells");
                self.b.t(&up);
                r7e_sub("V_rows");
                self.b.t(&g);
                let mut dn: GL = vec![];
                for b in (0..PAGE_D).rev() {
                    let (sq, tq) = (vb[b], va[(b + PAGE_D - ku % PAGE_D) % PAGE_D]);
                    dn.extend_from_slice(&[gt(sq, tq, h0), gc(h0, tq), gt(d, sq, tq), gc(h0, sq), gx(tq)]);
                }
                pg_add(1, &dn);
                r7e_sub("page_cells");
                self.b.t(&dn);
            } else {
                self.b.t(&g);
            }
            r7e_sub("V_rows");
            let mut g: GL = vec![];
            if k >= 1 {
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(x[wv - ku], true)]), d));
                }
            } else {
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(d, true)]), y0));
                }
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(y0, true)]), d));
                }
            }
            self.b.t(&g);
            self.b.t(&h0t);
            self.b.t(&if m1 { rev(&c1) } else { c1 });
            if nrk && k == 9 {
                // NR_PARK_V: the hook above was built with ZB_BUSY set; now release ZB and undo the park
                ZB_BUSY.store(false, Ordering::Relaxed);
                self.b.t(&rev(&nr_park));
            }
            r7e_sub("flags_windows");
            if evjs {
                // EVJS: the values are whole in the rings: no window slide
            } else if lad && k <= 8 {
                let cjs: GL = if c4p && CAD4B {
                    let ps: Vec<usize> = big.iter().filter(|&&e| e >= 4 && e >= k + 1).map(|&e| wv - lf(t, e).0 as usize + PAGE_D - ku - 1).collect();
                    if ps.is_empty() { vec![] } else {
                        let cj = w1c(&x[*ps.iter().min().unwrap() - 1..=*ps.iter().max().unwrap()]);
                        pg_add(3, &cj); pg_add(3, &cj);
                        cj
                    }
                } else { vec![] };
                self.b.t(&cjs);
                let g = self.ladder(&format!("V-row{k}"), &|set, c| {
                    let es: Vec<i32> = set.iter().cloned().filter(|&e| e >= k + 1).collect();
                    let l = lf(t, es[0]).0;
                    assert!(es.iter().all(|&e| lf(t, e).0 == l));
                    let mut sw: GL = vec![];
                    let p = wv - l as usize + PAGE_D - ku - 1;
                    cswap(c, va[(PAGE_D - 1 - ku % PAGE_D) % PAGE_D], x[p], &mut sw);
                    pg_add(3, &sw);
                    if c4p && !CAD4B && es.iter().any(|&e| e >= 4) {
                        assert!(es.iter().all(|&e| e >= 4));
                        let cj = w1c(&[x[p - 1], x[p]]);
                        pg_add(3, &cj); pg_add(3, &cj);
                        return [cj.clone(), sw, rev(&cj)].concat();
                    }
                    sw
                });
                self.b.t(&g);
                self.b.t(&rev(&cjs));
            } else if pv {
                // the window slides down one bit: the lane leaving it trades with the ring wire just below the next start
                let mut g: GL = vec![];
                let mut grp: BTreeMap<i32, Vec<i32>> = BTreeMap::new();
                for &e in big.iter().filter(|&&e| e >= k + 1) {
                    grp.entry(lf(t, e).0).or_default().push(e);
                }
                for (l, es) in grp {
                    let (lo, hi) = (*es.iter().min().unwrap(), *es.iter().max().unwrap());
                    assert!(hi - lo + 1 == es.len() as i32);
                    let fl = fl_cls(self, lo, hi);
                    g.extend_from_slice(&fl);
                    let mut sw: GL = vec![];
                    cswap(d, va[(PAGE_D - 1 - ku % PAGE_D) % PAGE_D], x[wv - l as usize + PAGE_D - ku - 1], &mut sw);
                    pg_add(3, &sw); pg_add(4, &fl); pg_add(4, &fl);
                    g.extend(sw);
                    g.extend_from_slice(&fl);
                }
                self.b.t(&g);
            }
        }
        if e3c {
            r7e_sub("E3C_bigV_rows");
            // E3C: the big-only V rows 10..e here (big_phase's rows; actors clb, mask F, carry y9; row 10 in u form, the rows
            // above it in hi form with the conversion inside the row), then the big V jswap out; no park
            assert!(bes.iter().next() == Some(&10), "E3C: class 10 acts at every E3 slot");
            let mut cvv = dec_ctl(&hb0, &[(bw1, true)], &self.dirty);
            cvv.extend(dec_ctl(&hb0[1..], &[(bw2, true)], &self.dirty));
            for k in 10..kkb {
                let act: Vec<(i32, i32, i32, i32)> = bprs.iter().cloned().filter(|p| p.0 >= k).collect();
                if act.is_empty() { continue; }
                let mut stb: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
                for p in &act { stb.entry(wv as i32 - (t / 2 - p.2) - k).or_default().insert(p.2); }
                let alob = *stb.keys().next().unwrap();
                assert!(alob + k >= 10);
                let (ku, au) = (k as usize, alob as usize);
                let tv: Vec<u32> = (au..(wv - ku - 1)).map(|a| x[a]).collect();
                let sv: Vec<u32> = (au..(wv - ku - 1)).map(|a| y[a + ku]).collect();
                let t1 = x[wv - 1 - ku];
                let top = x[wv - ku];
                let allu: BTreeSet<i32> = act.iter().map(|p| p.2).collect();
                let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                for (&a, us) in &stb {
                    let rest: BTreeSet<i32> = allu.difference(us).cloned().collect();
                    tg.insert((a - alob) as usize, if l16 { l16_keys(us, &rest, &a3, 2) } else { hterm_l(us, &rest, &hb0) });
                }
                if e3c2 && k >= 11 && e3k {
                    // AKB_E3C2_KEY: B -> B' = e - 4 before the first toggle; the same toggles on (U3, B')
                    let mut g = if k == 11 { e3k_cv(self, false) } else { vec![] };
                    g.extend(if k == 11 { e3k_flag(self, &|e| e >= 11, false, y1) } else { e3k_flag(self, &|e| e == k - 1, false, y1) });
                    self.b.t(&g);
                } else if e3c2 && k >= 11 {
                    // E3C2: flag y1 = [e >= k] (u form kept): [e >= 11] before row 11, then [e == k - 1]
                    let g = if k == 11 { bflag(self, &|e| e >= 11, false, y1) } else { bflag(self, &|e| e == k - 1, false, y1) };
                    self.b.t(&g);
                }
                let actb: Vec<Vec<Lit>> = if k == 10 { vec![clb.clone()] } else if e3c2 { vec![cat(&famb, &[(y1, true)])] } else { bexact(k, &[hb0[0], hb0[1], hb0[2], hb0[3], bw0], &clb) };
                let g = self.row_big(&tv, &sv, t1, top, d, y[9], fm_, &tg, &actb, if k == 10 || e3c2 { None } else { Some(&cvv) });
                self.b.t(&g);
                let mut g: GL = vec![];
                for li in &actb {
                    g.extend(self.m(&cat(li, &[(x[wv - ku], true)]), d));
                }
                self.b.t(&g);
                if k == 10 && !e3c2 {
                    self.b.t(&rev(&bcv));
                }
            }
            if e3c2 {
                // E3C2: the flag back to 0 ([e >= emax] = [e == emax]), then the u -> hi conversion (bcv reads !y1)
                if kkb > 11 && e3k {
                    // AKB_E3C2_KEY: the last toggle, then B' -> B
                    let mut g = e3k_flag(self, &|e| e == kkb - 1, false, y1);
                    g.extend(rev(&e3k_cv(self, false)));
                    self.b.t(&g);
                } else if kkb > 11 {
                    let g = bflag(self, &|e| e == kkb - 1, false, y1);
                    self.b.t(&g);
                }
                if l16 && L16_TRIM {
                    // L16_TRIM: the V junction swap out while A is still U3, then bcv undone
                    let g = self.l16_jswap_f(t, &bprs, &a3, &b4, false, &clb, 1);
                    pg_add(8, &g);
                    self.tsub("h1_jswap", &g);
                }
                self.tsub("h1_conv", &rev(&bcv));
            }
            if !(l16 && L16_TRIM) {
            let g = if l16 { self.l16_jswap(t, &bprs, &a3, &b4, false, &clb) } else { self.jswap_f(t, &bprs, &hb0, [bw0, bw1, bw2], false, false, NONE, &clb) };
            pg_add(8, &g);
            self.b.t(&g);
            }
        } else if e3 {
            r7e_sub("E3V_park");
            // E3V: park the big shots like waiters for the low work and the low post
            self.b.t(&rev(&bcv));
            self.b.t(&rev(&bpre));
            let mut g = self.m(&cat(&clb, &[(y0, true)]), y[7]);
            g.extend(self.m(&cat(&clb, &[(y[7], true)]), y0));
            self.b.t(&g);
        }
        r7e_sub("flags_windows");
        self.mk(t, 4);
        let mut sw_post: GL = vec![];
        if pv {
            // per class: V window-out; in PAGE_C mode also the digit remap (dig[k] has weight 2^(e-k): reverse
            // dig[0..=e], park B's empty ring lanes as zeros above e). One flag bracket for both.
            let mut g: GL = vec![];
            let mut rms: Vec<GL> = vec![];
            if evjs {
                // EVJS V out (the same swaps) and the digit remap, one flag walk
                let cj = ejs_cj(false, e3);
                pg_add(2, &cj); pg_add(2, &cj);
                g = cj.clone();
                g.extend(if fw_on("V-win-out") { self.fw_ladder(t, "V-win-out", false, 1) } else { self.ladder("V-win-out", &|set, c| {
                    let e = set[0];
                    let (l, f) = lf(t, e);
                    let mut r = ejs(l, f, c, false);
                    let rm = rmb(c, e);
                    pg_add(3, &r); pg_add(5, &rm);
                    r.extend(rm);
                    r
                }) });
                g.extend(rev(&cj));
                if fw_on("V-win-out") && prs.contains(&0) && prs.contains(&1) {
                    g.extend(self.fw_e01(t, false, &sp0, &sp1cs, d, zf));
                }
                for (lits_, e) in [(vec![sp0.clone()], 0i32), (sp1cs.clone(), 1i32)] {
                    if fw_on("V-win-out") && prs.contains(&0) && prs.contains(&1) { continue; }
                    if !prs.contains(&e) { continue; }
                    let (l, f) = lf(t, e);
                    let fl: GL = lits_.iter().flat_map(|l_| self.mz(l_, d, zf)).collect();
                    let s_ = ejs(l, f, d, false);
                    pg_add(3, &s_); pg_add(4, &fl); pg_add(4, &fl);
                    g.extend_from_slice(&fl);
                    g.extend(s_);
                    g.extend_from_slice(&fl);
                }
            } else if lad {
                g = self.ladder("V-win-out", &|set, c| {
                    let e = set[0];
                    let mut r = rotate_up(c, &va, e as usize % PAGE_D);
                    let rm = rmb(c, e);
                    pg_add(2, &r); pg_add(5, &rm);
                    r.extend(rm);
                    r
                });
            }
            for &e in big.iter().filter(|_| !lad) {
                let (l, f) = lf(t, e);
                let (lu, fu) = (l as usize, f as usize);
                let fl = fl_cls(self, e, e);
                g.extend_from_slice(&fl);
                let ro = rotate_up(d, &va, e as usize % PAGE_D);
                let mut ga: GL = vec![];
                for j in 0..(if pc { 0 } else { PAGE_D }) {
                    cswap(d, va[j], x[wv - fu + j], &mut ga);
                    cswap(d, vb[j], y[wv - lu + j], &mut ga);
                }
                let mut rm: GL = vec![];
                if pc {
                    let eu = e as usize;
                    let mut i = 0usize;
                    while i < eu - i {
                        cswap(d, dig[i], dig[eu - i], &mut rm);
                        i += 1;
                    }
                }
                pg_add(0, &ga); pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl); pg_add(5, &rm); pg_add(5, &rm);
                g.extend(ro);
                g.extend(ga);
                g.extend_from_slice(&rm);
                g.extend_from_slice(&fl);
                rms.push(rm);
            }
            // e = 0 (global page only): q = 1 -> Q[0] = 1, B's empty ring lanes as zeros above it
            let mut rm0: GL = vec![];
            if pgo {
                let l0 = lf(t, 0).0 as usize;
                let fl = self.mz(&sp0, d, zf);
                rm0.extend_from_slice(&fl);
                rm0.push(gc(d, dig[0]));
                rm0.extend_from_slice(&fl);
                if prs.contains(&1) {
                    let l1 = lf(t, 1).0 as usize;
                    let fl: GL = sp1cs.iter().flat_map(|l_| self.mz(l_, d, zf)).collect();
                    rm0.extend_from_slice(&fl);
                    rm0.push(gc(d, dig[0]));
                    rm0.extend_from_slice(&fl);
                }
                pg_add(5, &rm0); pg_add(5, &rm0);
                g.extend_from_slice(&rm0);
            }
            // the acting shots of this slot's rows: low classes, and e = 0 with the global page (disjoint terms)
            let mut acts: Vec<Vec<Lit>> = if pgo { vec![cl.clone(), sp0.clone()] } else { vec![cl.clone()] };
            if pgo && prs.contains(&1) {
                acts.extend(sp1cs.iter().cloned());
            }
            self.b.t(&g);
            r7e_sub("sw_swap");
            if pc {
                // digit j counts for: j = 0 every acting shot; j = 1, 2 the low classes; j >= 3 the classes >= j
                let lowc = cl.clone();
                let ext_y: Vec<u32> = y.clone();
                let actj = |j: usize| -> Vec<Vec<Lit>> {
                    if j == 0 { return acts.clone(); }
                    let mut l = lowc.clone();
                    for i in 1..(j.max(2) - 1) { l.push((ext_y[i], false)); }
                    vec![l]
                };
                let ext = |j: usize| -> Vec<Lit> {
                    if j == 0 { return vec![]; }
                    let mut l = vec![(h1, true)];
                    for i in 1..(j.max(2) - 1) { l.push((ext_y[i], false)); }
                    l
                };
                // E3C: the big digits reversed into the low layout (weight j on y0 / x[wv - j], j = 0..e: weight 10 on
                // x[wv - 10]) by class flags on the hosted (hi, w) lanes; undone after the role swap
                let mut brm: GL = vec![];
                let brm_bar = e3c && l16 && AKB_BRM_BARREL;
                if brm_bar {
                    // AKB_BRM_BARREL: famb on x0, funnel stages on ZB = x0 & key bit, fixed reversal of Q, famb off
                    let edig = |k: usize| -> u32 { if k == 0 { y0 } else { x[wv - k] } };
                    assert!(bes.iter().next() == Some(&10) && *bes.iter().next_back().unwrap() <= 18, "AKB_BRM_BARREL: classes 10..=18");
                    let xm = (*bes.iter().next_back().unwrap() - 10) as usize;
                    let key = |b: usize| -> u32 { if b == 0 { b4[0] } else { a3[b - 1] } };
                    brm.extend(self.m(&famb, x0));
                    for b in (0..4usize).rev() {
                        let s_ = 1usize << b;
                        if s_ > xm { continue; }
                        let hi = xm.min(2 * s_ - 1) + 10;
                        brm.extend(and2(x0, key(b), ZB_LANE));
                        for p_ in s_..=hi { cswap(ZB_LANE, edig(p_ - s_), edig(p_), &mut brm); }
                        brm.extend(and2(x0, key(b), ZB_LANE));
                    }
                    for i in 0..5usize { cswap(x0, edig(i), edig(10 - i), &mut brm); }
                    brm.extend(self.m(&famb, x0));
                    self.b.t(&brm);
                } else if e3c {
                    let edig = |k: usize| -> u32 { if k == 0 { y0 } else { x[wv - k] } };
                    for &e in &bes {
                        let fl = bcflag(self, e);
                        let eu = e as usize;
                        let mut sw: GL = vec![];
                        let mut i = 0usize;
                        while i < eu - i {
                            cswap(d, edig(i), edig(eu - i), &mut sw);
                            i += 1;
                        }
                        brm.extend_from_slice(&fl);
                        brm.extend(sw);
                        brm.extend_from_slice(&fl);
                    }
                    self.b.t(&brm);
                }
                let (pre, post) = if e3c {
                    // E3C: ONE sandwich for both families (the K2 hop is unconditional): the big family joins the act set,
                    // every digit j <= 9 (pre_S) and the F = 1 digit terms as its own cube; digit 10 is the big family's only
                    let mut acts2 = acts.clone();
                    acts2.push(famb.clone());
                    let mut qd: Vec<u32> = dig.clone();
                    qd.push(x[wv - 10]);
                    let famx: Vec<Lit> = vec![(w1l, true), (h1, false)];
                    let actj2 = |j: usize| -> Vec<Vec<Lit>> {
                        if j == 0 { return acts2.clone(); }
                        if j >= 10 { return vec![famb.clone()]; }
                        let mut v = actj(j);
                        v.push(famb.clone());
                        v
                    };
                    let extc2 = |j: usize| -> Vec<Vec<Lit>> {
                        if j == 0 { return vec![vec![]]; }
                        if j >= 10 { return vec![famx.clone()]; }
                        vec![ext(j), famx.clone()]
                    };
                    // AK_PCONV: the close converts the low acts only (the big family's post_page is big_phase's, full)
                    if AK_PCONV { CONV_ACTS.with(|c| *c.borrow_mut() = Some(if PK3_PCONV_BIG { acts2.clone() } else { acts.clone() })); }
                    if AK_PCONV && PK3_PCONV_BIG { PK3_FAM.with(|c| c.set(true)); }
                    self.sandwich_x(&qd, d, &acts2, &actj2, &extc2, &|_j| vec![], &|_j| vec![])
                } else {
                    self.sandwich_g(if c4l { &dig[..kk as usize] } else { &dig[..] }, d, &acts, &actj, &ext)
                };
                let fz = self.pg[4 * PAGE_D];
                let mut rs: GL = vec![];
                for j in 0..PAGE_D {
                    cswap(fz, vb[j], sc[j], &mut rs);
                }
                pg_add(5, &pre); pg_add(5, &post); pg_add(5, &rs); pg_add(5, &rs);
                { let (a_, k_) = swx_last(); self.t3(&pre, a_, k_, ["sw_sel", "sw_K2", "sw_q"], false); }
                self.b.t(&rs);
        self.mk(t, 5);
                // per class: remap back, then the cofactor window (inverse of its window-out: rotate VB by -e)
                let mut cw: GL = vec![];
                if evjs {
                    // EVJS: remap back and the C-form swaps in (cofactors whole in the rings), one flag walk
                    let cj = ejs_cj(true, e3);
                    pg_add(2, &cj); pg_add(2, &cj);
                    cw = cj.clone();
                    cw.extend(if fw_on("cw") { self.fw_ladder(t, "cw", true, -1) } else { self.ladder("cw", &|set, c| {
                        let e = set[0];
                        let (l, f) = lf(t, e);
                        let mut r = rmb(c, e);
                        let s_ = ejs(l, f, c, true);
                        pg_add(3, &s_); pg_add(5, &r);
                        r.extend(s_);
                        r
                    }) });
                    cw.extend(rev(&cj));
                    if fw_on("cw") && prs.contains(&0) && prs.contains(&1) {
                        cw.extend(self.fw_e01(t, true, &sp0, &sp1cs, d, zf));
                    }
                    for (lits_, e) in [(vec![sp0.clone()], 0i32), (sp1cs.clone(), 1i32)] {
                        if fw_on("cw") && prs.contains(&0) && prs.contains(&1) { continue; }
                        if !prs.contains(&e) { continue; }
                        let (l, f) = lf(t, e);
                        let fl: GL = lits_.iter().flat_map(|l_| self.mz(l_, d, zf)).collect();
                        let s_ = ejs(l, f, d, true);
                        pg_add(3, &s_); pg_add(4, &fl); pg_add(4, &fl);
                        cw.extend_from_slice(&fl);
                        cw.extend(s_);
                        cw.extend_from_slice(&fl);
                    }
                } else if lad {
                    cw = self.ladder("cw", &|set, c| {
                        let e = set[0];
                        let mut r = rmb(c, e);
                        let ro = rotate_up(c, &vb, (PAGE_D - e as usize % PAGE_D) % PAGE_D);
                        pg_add(2, &ro); pg_add(5, &r);
                        r.extend(ro);
                        r
                    });
                }
                for (ie, &e) in big.iter().enumerate().filter(|_| !lad) {
                    let fl = fl_cls(self, e, e);
                    let ro = rotate_up(d, &vb, (PAGE_D - e as usize % PAGE_D) % PAGE_D);
                    pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl);
                    cw.extend_from_slice(&fl);
                    cw.extend_from_slice(&rms[ie]);
                    cw.extend(ro);
                    cw.extend_from_slice(&fl);
                }
                r7e_sub("cw_jswap");
                self.b.t(&rm0);
                self.b.t(&cw);
                if e3c {
                    r7e_sub("E3C_bigC_rows");
                    // E3C: big digits back, the big C jswap in, the big-only C rows e..10 (big_phase's form; actors by the
                    // family, mask y1, carry x[wv - k]; CVHC's hoisted hi -> v conversion before row 10)
                    if brm_bar { self.b.t(&rev(&brm)); } else { self.b.t(&brm); }
                    if !(l16 && L16_TRIM) {
                    let g = if l16 { self.l16_jswap(t, &bprs, &a3, &b4, true, &famb) } else { self.jswap_f(t, &bprs, &hb0, [bw0, bw1, bw2], true, false, NONE, &famb) };
                    pg_add(8, &g);
                    self.b.t(&g);
                    }
                    if l16 {
                        // LOOK16 h1: A -> U3, then B -> V4 (the C rows and the X-side groups read V4)
                        let mut g = self.l16_cu(&a3, &b4, &famb);
                        g.extend(self.l16_cv(&a3, &b4, &famb));
                        self.tsub("h1_conv", &g);
                        if L16_TRIM {
                            // L16_TRIM: the C junction swap in on the converted lanes
                            let g = self.l16_jswap_f(t, &bprs, &a3, &b4, true, &famb, 2);
                            pg_add(8, &g);
                            self.tsub("h1_jswap", &g);
                        }
                    } else if e3c2 {
                        // E3C2: the hoisted hi -> v conversion before the first big C row (not before row 10)
                        let mut g = inc_ctl(&hb0, &cat(&famb, &[(bw0, true)]), &self.dirty);
                        g.extend(inc_ctl(&hb0, &cat(&famb, &[(bw1, true)]), &self.dirty));
                        g.extend(inc_ctl(&hb0[1..], &cat(&famb, &[(bw2, true)]), &self.dirty));
                        self.b.t(&g);
                    }
                    for k in (10..kkb).rev() {
                        let act: Vec<(i32, i32, i32, i32)> = bprs.iter().cloned().filter(|p| p.0 >= k).collect();
                        if act.is_empty() { continue; }
                        let ku = k as usize;
                        let mut cv_c = inc_ctl(&hb0, &[(bw0, true)], &self.dirty);
                        cv_c.extend(inc_ctl(&hb0, &[(bw1, true)], &self.dirty));
                        cv_c.extend(inc_ctl(&hb0[1..], &[(bw2, true)], &self.dirty));
                        if e3c2 && e3k {
                            // AKB_E3C2_KEY: A -> A' = (e - 3) mod 8 before the first toggle (k = kkb - 1 >= 11), back after the clear
                            let mut g = if k == kkb - 1 && k >= 11 { e3k_cv(self, true) } else { vec![] };
                            g.extend(if k >= 11 { e3k_flag(self, &|e| e == k, true, y[9]) } else { e3k_flag(self, &|e| e >= 11, true, y[9]) });
                            if k == 10 && kkb > 11 { g.extend(rev(&e3k_cv(self, true))); }
                            self.b.t(&g);
                        } else if e3c2 {
                            // E3C2: flag y9 = [e >= k] going down: [e == k] before row k >= 11; cleared by [e >= 11] before row 10
                            let g = if k >= 11 { bflag(self, &|e| e == k, true, y[9]) } else { bflag(self, &|e| e >= 11, true, y[9]) };
                            self.b.t(&g);
                        }
                        if k == 10 && !e3c2 {
                            let mut g = inc_ctl(&hb0, &cat(&famb, &[(bw0, true)]), &self.dirty);
                            g.extend(inc_ctl(&hb0, &cat(&famb, &[(bw1, true)]), &self.dirty));
                            g.extend(inc_ctl(&hb0[1..], &cat(&famb, &[(bw2, true)]), &self.dirty));
                            self.b.t(&g);
                        }
                        let mut starts: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
                        for p in &act { starts.entry(W as i32 - (t / 2 + p.3) - 1 + k).or_default().insert(p.3); }
                        let ahb = *starts.keys().next_back().unwrap();
                        let wires: Vec<usize> = (ku..=(ahb as usize)).rev().collect();
                        let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
                        let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
                        let nn = tv.len();
                        let top = y[ku - 1];
                        let cc = x[wv - ku];
                        let actv: Vec<Vec<Lit>> = if k == 10 { vec![famb.clone()] } else if e3c2 { vec![cat(&famb, &[(y[9], true)])] } else { bexact(k, &[hb0[0], hb0[1], hb0[2], hb0[3], bw0], &famb) };
                        let allv: BTreeSet<i32> = act.iter().map(|p| p.3).collect();
                        let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                        for (&a, vs) in &starts {
                            let rest: BTreeSet<i32> = allv.difference(vs).cloned().collect();
                            tg.insert((ahb - a) as usize, if l16 { l16_keys(vs, &rest, &b4, 1) } else { hterm_l(vs, &rest, &hb0) });
                        }
                        let g = self.row_big(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, y1, &tg, &actv, if k == 10 || e3c2 { None } else { Some(&cv_c) });
                        let mut hh: GL = vec![];
                        for li in &actv {
                            hh.extend(self.m(&cat(li, &[(x[wv - ku], true)]), d));
                        }
                        hh.push(gc(d, x[wv - ku]));
                        hh.push(gc(d, top));
                        self.b.t(&hh);
                        self.b.t(&rev(&g));
                    }
                }
                swp_note(rs.len());
                sw_post = rs;
                sw_post.extend(post);
            }
        }
        self.mk(t, 6);
        for k in (0..kk).rev() {
            r7e_sub("C_rows");
            let act: Vec<(i32, i32)> = pr.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() {
                continue;
            }
            let ku = k as usize;
            let li = lik(k);
            // E3C: rows 9..3 are shared with the big C rows (the big family's act cube joins); big_phase's hosted-lane move
            // of row k first (to the consumed digit lane x[wv - k - 1])
            let e3s = e3c && ((3..=9).contains(&k) || (e3r2 && k == 2));
            if e3s && k >= 3 {
                let dst = x[wv - ku - 1];
                let g = match k {
                    9 => { let g = mvf(self, hbc[3], dst); hbc[3] = dst; g }
                    8 => { let g = mvf(self, hbc[2], dst); hbc[2] = dst; g }
                    7 => { let g = mvf(self, ac[2], dst); ac[2] = dst; g }
                    6 => { let g = mvf(self, ac[1], dst); ac[1] = dst; g }
                    5 => { let g = mvf(self, ac[0], dst); ac[0] = dst; g }
                    4 => { let g = mvf(self, hbc[1], dst); hbc[1] = dst; g }
                    _ => { let g = mvf(self, hbc[0], dst); hbc[0] = dst; g }
                };
                self.b.t(&g);
            }
            let actv: Vec<Vec<Lit>> = if e3s { vec![li.clone(), famb.clone()] } else { vec![li.clone()] };
            let flag = k >= 2 && big.contains(&k);
            if flag {
                let mut g = self.m(&cat(&li, &[(y[ku - 1], true)]), h0);
                g.extend(self.m(&cat(&li, &[(h0, true)]), y[ku - 1]));
                self.b.t(&g);
            }
            let starts: Vec<(i32, i32, i32)> = act.iter().map(|p| (p.0, p.1, W as i32 - (lf(t, p.0).1 + p.1) - 1 + k - pdc)).collect();
            let m0 = merge0 && k == 0;
            let m1 = merge1 && k == 1;
            let ahi1 = starts.iter().map(|p| p.2).max().unwrap();
            let slo = starts.iter().map(|p| p.2).min().unwrap();
            let mn = act.iter().map(|p| p.0).min().unwrap();
            let both = act.iter().any(|p| p.1 == 1);
            let ahi = if m0 { (W as i32) - t / 2 - 1 - pd0 } else { ahi1 };
            assert!(!m0 || ahi > ahi1);
            // LOOK16: an early case has v down to 1, so its shared C row can start above the low chain's top: the chain runs
            // from ahx (the higher of the two) and the low family is off above ahi
            let ahx = if e3s && l16 { ahi.max(bprs.iter().map(|p| W as i32 - (t / 2 + p.3) - 1 + k).max().unwrap()) } else { ahi };
            let xo = (ahx - ahi) as usize;
            let wires: Vec<usize> = (ku..=(ahx as usize)).rev().collect();
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
            let nn = tv.len();
            let top = if k >= 1 { y[ku - 1] } else { NONE };
            let c = if k >= 2 { x[wv - ku] } else { h0 };
            let mut il: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for i in 0..(ahi - slo + 1) {
                let a = ahi - i;
                let mut cu: Vec<Vec<Lit>> = vec![vec![]];
                if m0 && a > ahi1 {
                    cu.push(vec![(h1, true)]);
                } else {
                    // per wait value: the classes of that wait whose start is below this wire are cancelled
                    for wq in 0..2 {
                        let off = starts.iter().filter(|p| p.1 == wq && p.2 < a).map(|p| p.0).min();
                        if let Some(yy) = off {
                            let jlo = (k + 1).max(2);
                            let mut ch: Vec<Lit> = vec![];
                            if m0 || m1 {
                                ch.push((h1, true));
                            }
                            if both {
                                ch.push((w1l, wq == 1));
                            }
                            // classes >= yy: the lifted marker (h0 = 1) is class k itself, the digit lanes below yy are zero;
                            // with waiters, yy = the row's lowest class means every shot of this wait (no class literal)
                            if yy > mn || !both {
                                // CAD4B: a waiter is a class >= 4: it is never the class of the rows 2, 3 (h0), and its
                                // digit lanes 2, 3 above the row are consumed (0)
                                let wt = CAD4B && both && wq == 1;
                                if k >= (if wt { 4 } else { 2 }) {
                                    ch.push((h0, false));
                                }
                                for j in (if wt { jlo.max(4) } else { jlo })..yy {
                                    ch.push((x[wv - j as usize], false));
                                }
                            }
                            cu.push(ch);
                        }
                    }
                }
                il.insert(i as usize, cu);
            }
            let g = if e3s {
                // E3C shared C row, toggle form on y1 (0 on every acting shot of both families at rows >= 3): low cubes get the
                // family literal h1 ([] XOR [!h1] = h1), the big groups turn on at their starts by hterm on the moved hosted
                // lanes AND the full family, so the last wire's XOR is exactly [] ^ [!h1] ^ famb: that is the mask reset
                // around the decision (lik reads y1)
                let mut sbv: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
                for p in &bprs { sbv.entry(W as i32 - (t / 2 + p.3) - 1 + k).or_default().insert(p.3); }
                // CM_FAMB: the toggles' family literal (the act cube actv keeps famb)
                let famc: Vec<Lit> = if CM_FAMB { vec![(h1, false)] } else { famb.clone() };
                let allv: BTreeSet<i32> = bprs.iter().map(|p| p.3).collect();
                let blo = *sbv.keys().next().unwrap();
                assert!(*sbv.keys().next_back().unwrap() <= ahx && blo >= k, "E3C: big C starts outside the low chain at t {t} k {k}");
                assert!(xo == 0 || k >= 3, "LOOK16: row 2 never needs the chain extension");
                let n = (ahx - blo.min(slo) + 1) as usize;
                let mut ilc: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                for i in 0..n {
                    let a = ahx - i as i32;
                    let mut cu: Vec<Vec<Lit>> = vec![];
                    if a <= ahi {
                        let low: Vec<Vec<Lit>> = il.get(&(i - xo)).cloned().unwrap_or_else(|| vec![vec![]]);
                        for c0 in low {
                            let mut c0 = c0;
                            if !c0.is_empty() && !c0.contains(&(h1, true)) && !(CM_FAMB && c0.contains(&(w1l, false))) { c0.push((h1, true)); }
                            cu.push(c0);
                        }
                        cu.push(vec![(h1, false)]);
                    }
                    for (&sa, vs) in &sbv {
                        if sa >= a {
                            let rest: BTreeSet<i32> = allv.difference(vs).cloned().collect();
                            for c0 in if l16 { l16_keys(vs, &rest, &[ac[0], ac[1], ac[2], hbc[3]], 1) } else { hterm_l(vs, &rest, &hbc) } {
                                // BK_D1 (see the switch): rows 6..9 (k >= 3 here), a positive literal on y[2..=k-2] makes !h1 redundant
                                if BK_D1 && l16 && CM_FAMB && ku >= 3 && c0.iter().any(|&(q0, p)| p && y[2..(ku - 1)].contains(&q0)) {
                                    cu.push(c0);
                                } else {
                                    cu.push(cat(&c0, &famc));
                                }
                            }
                        }
                    }
                    ilc.insert(i, cu);
                }
                if k >= 3 {
                    let rst: Vec<Vec<Lit>> = if CM_FAMB { vec![vec![]] } else { vec![vec![], vec![(h1, false)], famb.clone()] };
                    self.row_vzr(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, y1, &tog_of(&ilc), &actv, None, None, false, NONE, &rst)
                } else {
                    // E3C2R2: row 2 inline: the low cubes as in the parent (h1 added to the non-empty ones), the big family by
                    // [!h1 & !m] on m = x[wv - 3], toggled at the big group starts by hterm & famb
                    let m3 = x[wv - 3];
                    let mut il2: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                    let mut tg2: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                    for i in 0..n {
                        let a = ahi - i as i32;
                        let low: Vec<Vec<Lit>> = il.get(&i).cloned().unwrap_or_else(|| vec![vec![]]);
                        let mut cu: Vec<Vec<Lit>> = vec![];
                        for c0 in low {
                            let mut c0 = c0;
                            if !c0.is_empty() && !c0.contains(&(h1, true)) && !(CM_FAMB && c0.contains(&(w1l, false))) { c0.push((h1, true)); }
                            cu.push(c0);
                        }
                        cu.push(vec![(h1, false), (m3, false)]);
                        il2.insert(i, cu);
                        if let Some(vs) = sbv.get(&a) {
                            let rest: BTreeSet<i32> = allv.difference(vs).cloned().collect();
                            tg2.insert(i, (if l16 { l16_keys(vs, &rest, &[ac[0], ac[1], ac[2], hbc[3]], 1) } else { hterm_l(vs, &rest, &hbc) }).into_iter().map(|c0| cat(&c0, &famc)).collect());
                        }
                    }
                    self.row_vzr(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, m3, &tg2, &actv, Some(&il2), None, false, NONE, &[])
                }
            } else if togc_on() {
                ZB_BUSY.store(true, Ordering::Relaxed);
                let g = self.row_vzx(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, ZB_LANE, &tog_of(&il), &actv, None, None, m0 || m1, if m1 { h1 } else { NONE });
                ZB_BUSY.store(false, Ordering::Relaxed);
                g
            } else if CM_HOLD && evjs && !e3 && (3..=7).contains(&k) {
                // CM_HOLD (see the switch): the yt toggle form with the table's class tests held on y[1..k-2]
                assert!(xo == 0 && il.len() < nn && ![c, top, d, tv[nn - 1]].contains(&yt) && !tv.contains(&yt) && !sv.contains(&yt));
                assert!(il.values().next_back().map(|v| v.len() == 1 && v[0].is_empty()).unwrap_or(false), "CM_HOLD: the mask above the zone is not 1 at t {t} k {k}");
                let reg = |q: u32| -> Option<i32> { if q == h0 { Some(k) } else { (1..=9).find(|&j| x[wv - j as usize] == q) } };
                let pset = |cb: &Vec<Lit>| -> Vec<i32> { let mut v: Vec<i32> = cb.iter().filter(|l| !l.1).filter_map(|l| reg(l.0)).collect(); v.sort(); v };
                let lit = |j: i32| -> Lit { (if j == k { h0 } else { x[wv - j as usize] }, false) };
                let present: BTreeSet<Vec<i32>> = il.values().flat_map(|cs| cs.iter().map(|cb| pset(cb))).filter(|p| p.len() >= 2).collect();
                let held: Vec<Vec<i32>> = cm_hold_table(k).into_iter().filter(|p| present.contains(p)).collect();
                assert!(held.len() <= (k - 2) as usize, "CM_HOLD: more held tests than lanes at t {t} k {k}");
                let mut cv: GL = vec![];
                let mut cv_nc: Vec<usize> = vec![]; // control counts, for the CMHOLD check line (no gates)
                for (i, p) in held.iter().enumerate() {
                    let lane = y[1 + i];
                    assert!(!tv.contains(&lane) && lane != top && lane != tv[nn - 1], "CM_HOLD: a hold lane is a row lane");
                    // base: the longest earlier held test that is a proper subset (its lane holds it on actors)
                    let base = (0..i).filter(|&b| held[b].len() < p.len() && held[b].iter().all(|j| p.contains(j))).max_by_key(|&b| held[b].len());
                    let mut ls: Vec<Lit> = vec![];
                    if let Some(b) = base { ls.push((y[1 + b], true)); }
                    for &j in p { if base.map(|b| !held[b].contains(&j)).unwrap_or(true) { ls.push(lit(j)); } }
                    cv_nc.push(ls.len());
                    cv.extend(self.m(&ls, lane));
                }
                let il2: BTreeMap<usize, Vec<Vec<Lit>>> = il.iter().map(|(&i, cs)| (i, cs.iter().map(|cb| {
                    let p = pset(cb);
                    match held.iter().position(|h| *h == p) {
                        Some(hi) => { let mut c2: Vec<Lit> = cb.iter().filter(|l| l.1 || reg(l.0).is_none()).cloned().collect(); c2.push((y[1 + hi], true)); c2 }
                        None => cb.clone(),
                    }
                }).collect())).collect();
                let mut tg = tog_of(&il2);
                if let Some(v) = tg.get_mut(&0) { v.retain(|c0| !c0.is_empty()); }
                if tg.get(&0).map(|v| v.is_empty()).unwrap_or(false) { tg.remove(&0); }
                // check line (stderr only): compare with the Rust-mirror table at plain slot 260
                if t == 260 { eprintln!("CMHOLD t {t} k {k} held {:?} cv MCX {} controls {:?} toggle cubes {}", held, held.len(), cv_nc, tg.values().map(|v| v.len()).sum::<usize>()); }
                self.row_vzr(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, yt, &tg, &actv, None, Some(&cv), false, NONE, &[])
            } else if NR_CTOG_Y1 && evjs && !e3 && k >= 3 {
                // NR_CTOG_Y1: the mask above the zone is the XOR of all toggles = the last wire's cube list (the empty cube:
                // every hosted class has started); that list is the reset around the decision
                assert!(!m0 && !m1 && xo == 0 && il.len() < nn && c != y1 && top != y1 && d != y1);
                let rst: Vec<Vec<Lit>> = il.values().next_back().cloned().unwrap_or_else(|| vec![vec![]]);
                assert!(rst.len() == 1 && rst[0].is_empty(), "NR_CTOG_Y1: the mask above the zone is not 1 at t {t} k {k}");
                self.row_vzr(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, y1, &tog_of(&il), &actv, None, None, false, NONE, &rst)
            } else if CM_YT && evjs && !e3s {
                // builder assert (gate of CM_YT): no e3 slot without E3C sharing reaches this branch (cm_check has none)
                assert!(e3 == e3c, "CM_YT: EVJS slot with e3 set and E3C sharing off at t {t} k {k}");
                // CM_YT: mask on yt (1 on every actor here); the toggles are tog_of(il) without the empty cube, so the mask is yt
                // xor (the inline list) and their XOR over the zone is 0 on every shot (the last wire's list is the empty cube)
                assert!(xo == 0 && il.len() < nn && ![c, top, d, tv[nn - 1]].contains(&yt) && !tv.contains(&yt) && !sv.contains(&yt));
                assert!(il.values().next_back().map(|v| v.len() == 1 && v[0].is_empty()).unwrap_or(false), "CM_YT: the mask above the zone is not 1 at t {t} k {k}");
                let mut tg = tog_of(&il);
                if let Some(v) = tg.get_mut(&0) { v.retain(|c0| !c0.is_empty()); }
                if tg.get(&0).map(|v| v.is_empty()).unwrap_or(false) { tg.remove(&0); }
                self.row_vzr(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, yt, &tg, &actv, None, None, m0 || m1, if m1 { h1 } else { NONE }, &[])
            } else {
                self.row_vzx(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, NONE, &no_tog, &actv, Some(&il), None, m0 || m1, if m1 { h1 } else { NONE })
            };
            let c1 = if m0 {
                self.m(&sp0, d)
            } else if m1 {
                let mut c1: GL = sp1cs.iter().flat_map(|l_| self.m(l_, d)).collect();
                c1.extend(self.m(&[(d, true), (h1, false)], h0));
                if pc && !evjs {
                    let z1 = ZB_LANE;
                    c1.extend_from_slice(&[gx(h1), gt(d, h1, z1), gx(h1)]);
                    let ro = rotate_up(z1, &vb, PAGE_D - 1);
                    pg_add(2, &ro); pg_add(2, &ro);
                    c1.extend(ro);
                    c1.extend_from_slice(&[gx(h1), gt(d, h1, z1), gx(h1)]);
                }
                c1
            } else {
                vec![]
            };
            let mut hh: GL = vec![];
            if k >= 1 {
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(x[wv - ku], true)]), d));
                }
                hh.push(gc(d, x[wv - ku]));
                if k == 1 {
                    let xt = x[wv - 1];
                    for l_ in &actv {
                        hh.extend(self.m(&cat(l_, &[(y0, true)]), xt));
                    }
                    for l_ in &actv {
                        hh.extend(self.m(&cat(l_, &[(xt, true)]), y0));
                    }
                }
                hh.push(gc(d, top));
            } else {
                let host = x[wv - 1];
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(host, true)]), d));
                }
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(d, true)]), host));
                }
            }
            self.b.t(&hh);
            self.b.t(&c1);
            if pc && !evjs {
                let mut gp: GL = vec![];
                for b in 0..PAGE_D {
                    let (sq, tq) = (sc[b], vb[(b + PAGE_D - ku % PAGE_D) % PAGE_D]);
                    gp.extend_from_slice(&[gx(tq), gc(c, sq), gc(c, tq), gt(sq, tq, c)]);
                }
                pg_add(1, &gp);
                gp.extend_from_slice(&g);
                let mut dn: GL = vec![];
                for b in (0..PAGE_D).rev() {
                    let (sq, tq) = (sc[b], vb[(b + PAGE_D - ku % PAGE_D) % PAGE_D]);
                    dn.extend_from_slice(&[gt(sq, tq, c), gc(c, tq), gt(d, sq, tq), gc(c, sq), gx(tq)]);
                }
                pg_add(1, &dn);
                gp.extend(dn);
                self.b.t(&rev(&gp));
            } else {
                self.b.t(&rev(&g));
            }
            self.b.t(&if m1 { rev(&c1) } else { c1 });
            if flag {
                let mut g = self.m(&cat(&li, &[(h0, true)]), x[wv - ku]);
                g.extend(self.m(&cat(&li, &[(x[wv - ku], true)]), h0));
                self.b.t(&g);
            }
            r7e_sub("flags_windows");
            if evjs {
                // EVJS: no window slide
            } else if lad && k >= 1 {
                let cjs: GL = if c4p && CAD4B {
                    let ps: Vec<usize> = big.iter().filter(|&&e| e >= 4 && e >= k).map(|&e| W - lf(t, e).1 as usize - PAGE_D + ku - 1).collect();
                    if ps.is_empty() { vec![] } else {
                        let cj = w1c(&y[*ps.iter().min().unwrap() - 1..=*ps.iter().max().unwrap()]);
                        pg_add(3, &cj); pg_add(3, &cj);
                        cj
                    }
                } else { vec![] };
                self.b.t(&cjs);
                let g = self.ladder(&format!("C-row{k}"), &|set, c| {
                    let es: Vec<i32> = set.iter().cloned().filter(|&e| e >= k).collect();
                    let f = lf(t, es[0]).1;
                    assert!(es.iter().all(|&e| lf(t, e).1 == f));
                    let mut sw: GL = vec![];
                    let p = W - f as usize - PAGE_D + ku - 1;
                    cswap(c, vb[(PAGE_D - ku % PAGE_D) % PAGE_D], y[p], &mut sw);
                    pg_add(3, &sw);
                    if c4p && !CAD4B && es.iter().any(|&e| e >= 4) {
                        // W1 is 0 on every shot of a class below 4, so a mixed set (3, 4) needs no split
                        let cj = w1c(&[y[p - 1], y[p]]);
                        pg_add(3, &cj); pg_add(3, &cj);
                        return [cj.clone(), sw, rev(&cj)].concat();
                    }
                    sw
                });
                self.b.t(&g);
                self.b.t(&rev(&cjs));
            } else if pc && k >= 1 {
                // inverse of the cofactor window's slide after V-style row k - 1 (classes e >= k, grouped by f)
                let mut g: GL = vec![];
                let mut grp: BTreeMap<i32, Vec<i32>> = BTreeMap::new();
                for &e in big.iter().filter(|&&e| e >= k) {
                    grp.entry(lf(t, e).1).or_default().push(e);
                }
                for (f, es) in grp {
                    let fl = fl_cit(self, k, &es);
                    let mut sw: GL = vec![];
                    cswap(d, vb[(PAGE_D - ku % PAGE_D) % PAGE_D], y[W - f as usize - PAGE_D + ku - 1], &mut sw);
                    pg_add(3, &sw); pg_add(4, &fl); pg_add(4, &fl);
                    g.extend_from_slice(&fl);
                    g.extend(sw);
                    g.extend_from_slice(&fl);
                }
                self.b.t(&g);
            }
        }
        if e3c {
            r7e_sub("E3C_bigC_rows");
            // E3C: big C rows 2..0 alone (big_phase's form: mask x[wv - 3], carries x[wv - 2] / x[wv - 1] at rows 1 / 0),
            // then CVHC's conversion undone and the big C jswap out (before the merged sandwich's post)
            for k in (0..(if e3r2 { 2i32 } else { 3i32 })).rev() {
                let ku = k as usize;
                let mut starts: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
                for p in &bprs { starts.entry(W as i32 - (t / 2 + p.3) - 1 + k).or_default().insert(p.3); }
                let ahb = *starts.keys().next_back().unwrap();
                let wires: Vec<usize> = (ku..=(ahb as usize)).rev().collect();
                let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
                let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
                let nn = tv.len();
                let top = if k >= 1 { y[ku - 1] } else { NONE };
                let cc = if k >= 2 { x[wv - ku] } else if k == 1 { x[wv - 2] } else { x[wv - 1] };
                let actv: Vec<Vec<Lit>> = vec![famb.clone()];
                let allv: BTreeSet<i32> = bprs.iter().map(|p| p.3).collect();
                let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
                for (&a, vs) in &starts {
                    let rest: BTreeSet<i32> = allv.difference(vs).cloned().collect();
                    tg.insert((ahb - a) as usize, if l16 { l16_keys(vs, &rest, &[ac[0], ac[1], ac[2], hbc[3]], 1) } else { hterm_l(vs, &rest, &hbc) });
                }
                let g = self.row_big(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, x[wv - 3], &tg, &actv, None);
                let mut hh: GL = vec![];
                if k >= 1 {
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(x[wv - ku], true)]), d));
                    }
                    hh.push(gc(d, x[wv - ku]));
                    if k == 1 {
                        let xt = x[wv - 1];
                        for li in &actv {
                            hh.extend(self.m(&cat(li, &[(y0, true)]), xt));
                        }
                        for li in &actv {
                            hh.extend(self.m(&cat(li, &[(xt, true)]), y0));
                        }
                    }
                    hh.push(gc(d, top));
                } else {
                    let host = x[wv - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(host, true)]), d));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(d, true)]), host));
                    }
                }
                self.b.t(&hh);
                self.b.t(&rev(&g));
            }
            if l16 {
                let (am, bm) = (vec![hbc[0], hbc[1], hbc[2]], vec![ac[0], ac[1], ac[2], hbc[3]]);
                if L16_TRIM {
                    // L16_TRIM: the C junction swap out before the conversion is undone
                    let g = self.l16_jswap_f(t, &bprs, &am, &bm, true, &famb, 2);
                    pg_add(8, &g);
                    self.tsub("h1_jswap", &g);
                }
                let mut g = self.l16_cu(&am, &bm, &famb);
                g.extend(self.l16_cv(&am, &bm, &famb));
                self.tsub("h1_conv", &rev(&g));
            } else {
            let mut g = inc_ctl(&hbc, &cat(&famb, &[(ac[0], true)]), &self.dirty);
            g.extend(inc_ctl(&hbc, &cat(&famb, &[(ac[1], true)]), &self.dirty));
            g.extend(inc_ctl(&hbc[1..], &cat(&famb, &[(ac[2], true)]), &self.dirty));
            self.b.t(&rev(&g));
            }
            if !(l16 && L16_TRIM) {
            let g = if l16 { self.l16_jswap(t, &bprs, &[hbc[0], hbc[1], hbc[2]], &[ac[0], ac[1], ac[2], hbc[3]], true, &famb) } else { self.jswap_f(t, &bprs, &hbc, ac, true, false, NONE, &famb) };
            pg_add(8, &g);
            self.b.t(&g);
            }
        }
        r7e_sub("flags_windows");
        if pc {
            let mut g: GL = vec![];
            let cjw: GL = if lad && !evjs && c4p && CAD4B {
                let ix: Vec<usize> = big.iter().filter(|&&e| e >= 4).flat_map(|&e| { let lu = lf(t, e).0 as usize; (0..=e as usize).map(move |i| W - lu - 1 - PAGE_D - e as usize + i) }).collect();
                let cj = w1c(&y[*ix.iter().min().unwrap()..=*ix.iter().max().unwrap()]);
                pg_add(2, &cj); pg_add(2, &cj);
                cj
            } else { vec![] };
            if evjs {
                // EVJS C out: the same C-form swaps
                let cj = ejs_cj(true, e3);
                pg_add(2, &cj); pg_add(2, &cj);
                g = cj.clone();
                g.extend(if fw_on("C-win-out") { self.fw_ladder(t, "C-win-out", true, 0) } else { self.ladder("C-win-out", &|set, c| {
                    let (l, f) = lf(t, set[0]);
                    let s_ = ejs(l, f, c, true);
                    pg_add(3, &s_);
                    s_
                }) });
                g.extend(rev(&cj));
                if fw_on("C-win-out") && prs.contains(&0) && prs.contains(&1) {
                    g.extend(self.fw_e01(t, true, &sp0, &sp1cs, d, zf));
                }
                for (lits_, e) in [(vec![sp0.clone()], 0i32), (sp1cs.clone(), 1i32)] {
                    if fw_on("C-win-out") && prs.contains(&0) && prs.contains(&1) { continue; }
                    if !prs.contains(&e) { continue; }
                    let (l, f) = lf(t, e);
                    let fl: GL = lits_.iter().flat_map(|l_| self.mz(l_, d, zf)).collect();
                    let s_ = ejs(l, f, d, true);
                    pg_add(3, &s_); pg_add(4, &fl); pg_add(4, &fl);
                    g.extend_from_slice(&fl);
                    g.extend(s_);
                    g.extend_from_slice(&fl);
                }
            } else if lad {
                g = self.ladder("C-win-out", &|set, c| {
                    let e = set[0];
                    let lu = lf(t, e).0 as usize;
                    let mut lanes = vb.clone();
                    lanes.extend((0..e as usize).map(|i| y[W - lu - 1 - PAGE_D - i]));
                    let ro = rotate_up(c, &lanes, e as usize);
                    pg_add(2, &ro);
                    if c4p && !CAD4B && e >= 4 {
                        let cj = w1c(&(0..=e as usize).map(|i| y[W - lu - 1 - PAGE_D - e as usize + i]).collect::<Vec<u32>>());
                        pg_add(2, &cj); pg_add(2, &cj);
                        return [cj.clone(), ro, rev(&cj)].concat();
                    }
                    ro
                });
                g = [cjw.clone(), g, rev(&cjw)].concat();
            }
            for &e in big.iter().filter(|_| !lad) {
                let lu = lf(t, e).0 as usize;
                let fl = fl_cit(self, 0, &[e]);
                let mut lanes = vb.clone();
                lanes.extend((0..e as usize).map(|i| y[W - lu - 1 - PAGE_D - i]));
                let ro = rotate_up(d, &lanes, e as usize);
                pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl);
                g.extend_from_slice(&fl);
                g.extend(ro);
                g.extend_from_slice(&fl);
            }
            self.b.t(&g);
            if !pgo {
                let (a_, k_) = swp_last(); self.t3(&sw_post, a_, k_, ["sw_swap", "sw_K2", "sw_sel"], false);
            }
            if local {
                let er = rev(&self.erase_blk(d));
                pg_add(0, &er);
                self.b.t(&er);
                let g = gather4(self, true);
                self.b.t(&g);
            }
        }
        self.mk(t, 7);
        r7e_sub("plain_gap01");
        if prs.contains(&0) && !merge0 {
            let (_l, f) = lf(t, 0);
            let mb = W - f as usize;
            let wires: Vec<usize> = (0..mb).rev().collect();
            let c1 = self.m(&sp0, d);
            self.b.t(&c1);
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a]).collect();
            let nn = tv.len();
            let g = self.plain_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], d, x[wv - 1]);
            self.b.t(&rev(&g));
            self.b.t(&c1);
        }
        if prs.contains(&1) && !merge1 {
            let (_l, f) = lf(t, 1);
            let mb = W - f as usize;
            let wires: Vec<usize> = (1..=mb).rev().collect();
            let c1 = self.m(&sp1c, d);
            self.b.t(&c1);
            let pg1 = PAGE_G && mid_even(t);
            let wires: Vec<usize> = if pg1 { (1..=(mb - PAGE_D)).rev().collect() } else { wires };
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - 1]).collect();
            let nn = tv.len();
            let g = self.plain_vt(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], y[0], d, x[wv - 1]);
            if pg1 {
                let (pb, ps) = (&self.pg[PAGE_D..2 * PAGE_D], &self.pg[2 * PAGE_D..3 * PAGE_D]);
                let c = x[wv - 1];
                let mut gp: GL = vec![];
                for b in 0..PAGE_D {
                    gp.extend_from_slice(&[gx(pb[b]), gc(c, ps[b]), gc(c, pb[b]), gt(ps[b], pb[b], c)]);
                }
                pg_add(1, &gp);
                gp.extend_from_slice(&g);
                let mut dn: GL = vec![];
                for b in (0..PAGE_D).rev() {
                    dn.extend_from_slice(&[gt(ps[b], pb[b], c), gc(c, pb[b]), gt(d, ps[b], pb[b]), gc(c, ps[b]), gx(pb[b])]);
                }
                pg_add(1, &dn);
                gp.extend(dn);
                self.b.t(&rev(&gp));
            } else {
                self.b.t(&rev(&g));
            }
            self.b.t(&c1);
        }
        self.mk(t, 8);
        if pgo {
            let (a_, k_) = swp_last(); self.t3(&sw_post, a_, k_, ["sw_swap", "sw_K2", "sw_sel"], false);
        }
        if e3c {
            // E3C: park the big shots' y0, y1, y2 (C-row results) on the consumed lanes x[wv - 1..wv - 3]: for the low post a
            // big shot then looks like E3V's parked shot (code 01, yt, W1, y0 = y1 = y2 = 0); big_phase moves them back
            let mut g = mvf(self, y0, x[wv - 1]);
            g.extend(mvf(self, y1, x[wv - 2]));
            g.extend(mvf(self, y[2], x[wv - 3]));
            self.b.t(&g);
        }
        self.mk(t, 9);
        r7e_sub("post");
        let po_merge_turn = PO_EVEN_MERGE_TURN && pgo && !(c4l && CAD4B);
        // waiters step aside: a down-rotation now, the relabel below undoes it
        if !po_merge_turn && !(c4l && CAD4B) {
            let hold1: Vec<Lit> = cat(&[(yt, true)], &self.hc(1));
            let mut g = self.m(&cat(&hold1, &[(x[wv - 1], true)]), ctl);
            g.extend(self.m(&cat(&hold1, &[(x[wv - 1], false), (x[wv - 2], true)]), ctl));
            if e3 {
                // E3V: the parked big shots (digits on the top lanes may be 0); the acted e = 1 second form has y0 | y1 = 1
                g.extend(self.m(&cat(&hold1, &[(x[wv - 1], false), (x[wv - 2], false), (w1l, true)]), ctl));
            }
            let n_fz = g.len();
            if l16_frz(t) {
                // LOOK16: the frozen shots step aside too
                g.extend(self.m(&cat(&[(y[wv - 1], false), (y[wv - 2], true)], &self.hc(3)), ctl));
            }
            { let n_e = g.len(); self.tsplit(&g, &[(n_fz, "post"), (n_e, "l16_freeze")]); }
            let g = rotate_up(ctl, &y, wv - 1);
            self.b.t(&g);
            let mut g = self.m(&cat(&[(y[wv - 1], false), (y[wv - 2], true)], &self.hc(1)), ctl);
            let n_fz = g.len();
            if l16_frz(t) {
                g.extend(self.m(&cat(&[(y[wv - 1], false), (y[wv - 2], false), (y[wv - 3], true)], &self.hc(3)), ctl));
            }
            { let n_e = g.len(); self.tsplit(&g, &[(n_fz, "post"), (n_e, "l16_freeze")]); }
        }
        self.mk(t, 10);
        // post
        let mut g = self.m(&[(yt, true), (y[0], false)], ctl);
        let n_fz = g.len();
        if po_merge_turn && l16_frz(t) {
            // LOOK16 + PO merged turn: the frozen shots (not at the top) share the post's down-turn instead of the skipped
            // step-aside block
            g.extend(self.m(&cat(&[(y[wv - 1], false), (y[wv - 2], true)], &self.hc(3)), ctl));
        }
        { let n_e = g.len(); self.tsplit(&g, &[(n_fz, "post"), (n_e, "l16_freeze")]); }
        let g = rotate_up(ctl, &y, wv - 1);
        self.b.t(&g);
        self.b.t(&[gc(y[wv - 1], ctl)]);
        if po_merge_turn {
            // A waiter had y0 = y1 = 0. An acted second form had y0 | y1 = 1.
            // Both share the down-turn; only the waiter drops out of ctl here.
            let mut g = self.m(&cat(&[(y[wv - 1], false), (y[wv - 2], true), (y[0], false)], &self.hc(1)), ctl);
            let n_fz = g.len();
            if l16_frz(t) {
                // LOOK16: the turned frozen shot (old y0 = 0 now on top, flag one wire lower) drops out too
                g.extend(self.m(&cat(&[(y[wv - 1], false), (y[wv - 2], false), (y[wv - 3], true)], &self.hc(3)), ctl));
            }
            { let n_e = g.len(); self.tsplit(&g, &[(n_fz, "post"), (n_e, "l16_freeze")]); }
        }
        let mut g = vec![];
        for w in 1..wv {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        if pgo {
            let g = self.post_page_k(ctl, SW2_POST_AND);
            pg_add(7, &g);
            self.b.t(&g);
        }
        self.mk(t, 11);
        let xt = x[wv - 1];
        self.b.t(&[gc(ctl, y[wv - 1])]);
        self.b.t(&[gc(y[wv - 1], ctl)]);
        self.mk(t, 12);
        let mut ny = vec![y[wv - 1]];
        ny.extend_from_slice(&y[..wv - 1]);
        self.y = ny.clone();
        let y = ny;
        let mut d2 = self.pas.clone();
        d2.extend_from_slice(&self.x);
        d2.extend_from_slice(&y);
        self.dirty = d2;
        let act = y[0];
        let win: Vec<u32> = y[1..].to_vec();
        if PO_EVEN_REFLECT && pgo {
            assert!(PAGE_G && PAGE_N && PAGE_D == 11 && (ECAP == 17 || ECAP == 18));
            let ff = self.pg[4 * PAGE_D];
            let zz = ZB_LANE;
            // a is the parent's parity-rise control, b = act & !xt,
            // and w = act & W1 only at a CAD4 rise. No flag crosses a row.
            let mut g = self.m(&cat(&[(act, true)], &self.hc(1)), ctl);
            for &e in &big {
                if e & 1 == 1 {
                    let eu = e as usize;
                    let mut li = cat(&[(act, true)], &self.hc(2));
                    for i in 0..(eu - 2) { li.push((y[wv - 1 - i], false)); }
                    li.push((y[wv - eu + 1], true));
                    g.extend(self.m(&li, ctl));
                }
            }
            g.extend(self.m(&[(act, true), (xt, false)], ff));
            if c4p { g.push(gt(act, w1l, zz)); }
            g.extend(po_reflect(ctl, &win, 0));
            g.push(gc(ff, ctl));
            g.extend(po_reflect(ctl, &win, 1));
            g.push(gc(ff, ctl));
            if c4p { g.push(gc(zz, ff)); }
            g.extend(po_reflect(ff, &win, 2));
            if c4p {
                g.push(gc(zz, ff));
                g.extend(po_reflect(zz, &win, 4));
                g.push(gt(act, w1l, zz));
                // ZB is clean before the following MCX calls.
                for w in [false, true] {
                    for xv in [false, true] {
                        let k = 1 + 2 * (w as usize) + ((!xv) as usize);
                        g.extend(self.m(&[(act, true), (w1l, w), (xt, xv), (y[k], false)], ctl));
                    }
                }
                for xv in [false, true] {
                    let b = (!xv) as usize;
                    g.extend(self.m(&[(act, true), (xt, xv), (y[1 + b], false), (y[2 + b], false)], w1l));
                }
            } else {
                g.extend(self.m(&[(act, true), (xt, true), (y[1], false)], ctl));
                g.extend(self.m(&[(act, true), (xt, false), (y[2], false)], ctl));
            }
            g.extend(self.m(&[(act, true), (xt, false)], ff));
            // Conjugate the parent's header edits through the moved R1(b).
            for xv in [true, false] {
                let first = if xv { y[1] } else { y[2] };
                g.extend(self.m(&[(act, true), (xt, xv), (h1, false), (first, false)], h0));
            }
            for xv in [true, false] {
                let top = if xv { y[wv - 1] } else { y[1] };
                g.extend(self.m(&[(act, true), (xt, xv), (h1, true), (top, true)], h0));
            }
            for xv in [true, false] {
                let top = if xv { y[wv - 1] } else { y[1] };
                g.extend(self.m(&cat(&[(act, true), (xt, xv)], &self.hc(3)), top));
            }
            g.extend(self.m(&[(act, true), (h0, true)], h1));
            g.extend(self.m(&[(act, true), (h1, false), (xt, false)], h0));
            g.extend(self.m(&[(act, true), (h1, true), (xt, false), (y[wv - 2], true)], h0));
            g.extend(self.m(&cat(&[(act, true), (xt, false)], &self.hc(3)), y[wv - 2]));
            g.extend(self.m(&[(act, true), (h0, true), (xt, false)], h1));
            g.extend(self.m(&[(act, true), (h1, true)], h0));
            self.b.t(&g);
        } else {
            // parity: rotate the new N by r. The marker sits at wv-e+1, everything above it is zero.
            let mut g = self.m(&cat(&[(act, true)], &self.hc(1)), ctl);
            for &e in &big {
                if e & 1 == 1 {
                    let eu = e as usize;
                    let mut l = cat(&[(act, true)], &self.hc(2));
                    for i in 0..(eu - 2) {
                        l.push((y[wv - 1 - i], false));
                    }
                    l.push((y[wv - eu + 1], true));
                    g.extend(self.m(&l, ctl));
                }
            }
            self.b.t(&g);
            let g = rot1(ctl, &win);
            self.b.t(&g);
            let g = self.m(&[(act, true), (y[1], false)], ctl);
            self.b.t(&g);
            if c4p {
                // CAD4: a waiter acted two slots late: W1 goes into two more wires of rise of its new N
                let mut g = self.m(&[(act, true), (w1l, true)], ctl);
                g.push(gc(ctl, w1l));
                self.b.t(&g);
                let g = rotate_up(ctl, &win, 2);
                self.b.t(&g);
                let g = self.m(&[(act, true), (y[1], false), (y[2], false)], ctl);
                self.b.t(&g);
            }
            // final codes; the marker of a shot that stays in 11 is already in place
            let aa: Vec<Lit> = vec![(act, true)];
            let mut g = self.m(&cat(&aa, &[(h1, false), (y[1], false)]), h0);
            g.extend(self.m(&cat(&aa, &[(h1, true), (y[wv - 1], true)]), h0));
            g.extend(self.m(&cat(&aa, &self.hc(3)), y[wv - 1]));
            g.extend(self.m(&cat(&aa, &[(h0, true)]), h1));
            g.extend(self.m(&cat(&aa, &[(h1, false), (xt, false)]), h0));
            g.extend(self.m(&cat(&aa, &[(h1, true), (xt, false), (y[wv - 3], true)]), h0));
            g.extend(self.m(&cat(&cat(&aa, &self.hc(3)), &[(xt, false)]), y[wv - 3]));
            g.extend(self.m(&cat(&aa, &[(h0, true), (xt, false)]), h1));
            g.extend(self.m(&cat(&aa, &[(h1, true)]), h0));
            self.b.t(&g);
            let g1 = self.m(&[(act, true), (xt, false)], ctl);
            self.b.t(&g1);
            let g = rot1(ctl, &win);
            self.b.t(&g);
            self.b.t(&g1);
        }
        let mut g = self.m(&[(xt, true), (y[1], true)], act);
        let mut cuts: Vec<(usize, &str)> = vec![(g.len(), "post")];
        // LOOK16 (EA freeze fix): a frozen zero-wait big state shows the two act-erasure patterns below; cancel them there
        let fzc: Vec<Lit> = vec![(y[wv - 1], false), (y[wv - 2], true), (h0, true), (h1, true)];
        if l16_frz(t) {
            g.extend(self.m(&cat(&[(xt, true), (y[1], true)], &fzc), act));
        }
        cuts.push((g.len(), "l16_freeze"));
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], true), (h1, false)], act));
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], true), (h1, true), (h0, true)], act));
        cuts.push((g.len(), "post"));
        if l16_frz(t) {
            g.extend(self.m(&cat(&[(xt, false), (y[1], false), (y[2], true)], &fzc), act));
        }
        cuts.push((g.len(), "l16_freeze"));
        g.extend(self.m(&[(xt, true), (y[1], false), (y[2], true), (h0, true)], act));
        cuts.push((g.len(), "post"));
        r7e_sub("cad4_band");
        if cad4_band(t) {
            // a waiter with e = 4 that did not act here (stepped aside, or just arrived) has this pattern
            g.extend(self.m(&[(xt, false), (y[1], false), (y[2], false), (y[3], true), (w1l, false)], act));
        } else {
            g.extend(self.m(&[(xt, false), (y[1], false), (y[2], false), (y[3], true)], act));
        }
        if c4p {
            // the acted waiters: the same patterns two wires up
            let top0: Vec<Lit> = vec![(h0, true), (y[wv - 1], false)];
            for gq in [2usize, 3] {
                let mut l: Vec<Lit> = vec![(xt, true)];
                for i in 1..=gq {
                    l.push((y[i], false));
                }
                l.push((y[gq + 1], true));
                l.extend_from_slice(&top0);
                g.extend(self.m(&l, act));
            }
            for gq in [3usize, 4] {
                let mut z: Vec<Lit> = vec![(xt, false)];
                for i in 1..=gq {
                    z.push((y[i], false));
                }
                z.push((y[gq + 1], true));
                g.extend(self.m(&cat(&z, &top0), act));
                g.extend(self.m(&cat(&z, &self.hc(0)), act));
            }
        }
        self.tsplit(&g, &cuts);
        r7e_sub("post_pi10");
        if PO_PI10_HOLD && pgo {
            let g = self.pi10_po_hold(t + 1, ctl);
            self.b.t(&g);
        } else {
            if t + 1 <= 2 * N as i32 {
                let tau = ctl;
                let gl = cat(&[(xt, true), (y[1], false), (y[2], true)], &self.hc(0));
                let tg = self.m(&gl, tau);
                self.b.t(&tg);
                let p0 = self.pas[0];
                let (p12, p3) = self.pi10(t + 1, h1, h0, y[1], p0);
                self.b.t(&p12);
                let q = self.m(&[(tau, true), (h0, false), (y[1], true), (p0, true)], act);
                self.b.t(&q);
                self.b.t(&p3);
                self.b.t(&q);
                self.b.t(&rev(&p3));
                self.b.t(&rev(&p12));
                self.b.t(&tg);
            }
        }
        if t % 8 == 0 && !self.big_pairs11(t).is_empty() {
            self.big_phase(t);
            r7e_tag(slot_class(t));
        }
        if l16_gone(t) {
            r7e_sub("l16_release");
            self.l16_release(t);
        }
        self.arrive11(t - 1, &y, ctl);
        self.b.t(&[gx(ctl)]);
    }
    /// the acting big shots at a slot 8 mod 16 of the long region (marker form, code 01 at the top): the short classes
    /// (marker on y[9..TIER_LONG-2]) and the long cases moved here from the next slot 0 mod 16 (class e, w = e - 10)
    fn band8_actors(&self, t: i32, y: &[u32]) -> Vec<Vec<Lit>> {
        let wv = self.wr;
        let (yt, h0) = (y[wv - 1], self.e[0]);
        let _ = t;
        let mut out: Vec<Vec<Lit>> = vec![];
        for j in 9..=(TIER_LONG.max(11) as usize - 2) {
            // y[1] = 0: in even11 the gap-1 second form (code 01, yt, y[1] = 1) is still at the top
            let mut l: Vec<Lit> = vec![(yt, true), (h0, true), (y[1], false)];
            for i in 9..j { l.push((y[i], false)); }
            l.push((y[j], true));
            out.push(l);
        }
        for e in (TIER_LONG.max(11))..=17 {
            let mut l: Vec<Lit> = vec![(yt, true), (h0, true), (y[1], false)];
            for i in 9..(e as usize - 1) { l.push((y[i], false)); }
            l.push((y[e as usize - 1], true));
            for i in 0..3 { l.push((y[4 + i], ((e - 10) >> i) & 1 == 1)); }
            out.push(l);
        }
        out
    }
    /// LOOK16 release (EA release kernel) at a slot T - 8 that lost big service, after the relabel and before arrive11
    /// (x0, F, ZB clean): family = the frozen cube on x0; the flag off; code 11 -> 00 so h0, h1, F take the release bits r0,
    /// r1, r2 off the ring; whole-ring turns 4, 2, 1 under ZB = family & bit, each bit erased by the turned bottom pattern
    /// (first one at y[1 + delta], delta = !xt); code 11 back; the natural marker pop the freeze skipped (delta = 1 cases);
    /// family erased by the parent's post-image cubes (wait = 8 - d) with !yt.
    fn l16_release(&mut self, t: i32) {
        let wv = self.wr;
        let (x, y) = (self.x.clone(), self.y.clone());
        let (h0, h1) = (self.e[0], self.e[1]);
        let fam = x[0];
        let xt = x[wv - 1];
        let fl = self.pg[4 * PAGE_D];
        let zb = ZB_LANE;
        let _ = t;
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let mut g = self.m(&cat(&[(y[wv - 1], false), (y[wv - 2], true)], &self.hc(3)), fam);
        g.push(gc(fam, y[wv - 2]));
        g.push(gc(fam, h0));
        g.push(gc(fam, h1));
        for (tg, src) in [(h0, y[wv - 3]), (h1, y[wv - 4]), (fl, y[wv - 5])] {
            cswap(fam, tg, src, &mut g);
        }
        self.b.t(&g);
        for (reg, k) in [(fl, 4usize), (h1, 2), (h0, 1)] {
            let mut g = vec![gt(fam, reg, zb)];
            g.extend(rotate_up(zb, &y, k));
            g.push(gt(fam, reg, zb));
            for delta in 0..2usize {
                let gq = 1 + delta;
                let base: Vec<Lit> = vec![(fam, true), (xt, delta == 0)];
                if k == 4 {
                    let mut l = base.clone();
                    for j in 0..(gq + 4) { l.push((y[j], false)); }
                    g.extend(self.m(&l, reg));
                } else {
                    let offs: &[usize] = if k == 2 { &[2, 6] } else { &[1, 3, 5, 7] };
                    for &z in offs {
                        let j = gq + z;
                        let mut l = base.clone();
                        for a in 0..j { l.push((y[a], false)); }
                        l.push((y[j], true));
                        g.extend(self.m(&l, reg));
                    }
                }
            }
            self.b.t(&g);
        }
        let mut g = vec![gc(fam, h0), gc(fam, h1)];
        g.extend(self.m(&[(fam, true), (xt, false), (h0, true), (y[wv - 2], true)], h1));
        g.extend(self.m(&[(fam, true), (xt, false), (h0, true), (h1, false)], y[wv - 2]));
        for delta in 0..2usize {
            for wait in 0..8i32 {
                let es: Vec<i32> = (10..=ECAP).filter(|e| e % 2 == wait % 2).collect();
                let gq = 1 + delta + wait as usize;
                let mut low: Vec<Lit> = vec![(y[wv - 1], false), (xt, delta == 0)];
                for j in 0..gq { low.push((y[j], false)); }
                low.push((y[gq], true));
                if es.iter().any(|&e| !(delta == 1 && (e - wait) / 2 == 2)) {
                    let mut l = cat(&low, &self.hc(3));
                    for j in (wv + gq + 1 - 10)..(wv - 1) { l.push((y[j], false)); }
                    g.extend(self.m(&l, fam));
                }
                if es.iter().any(|&e| delta == 1 && (e - wait) / 2 == 2) {
                    g.extend(self.m(&cat(&low, &self.hc(1)), fam));
                }
            }
        }
        self.b.t(&g);
    }
    /// LOOK16 detector + normaliser (head of even11 at a kept tier T >= CUT_T + 16; x0 = 0, F = 0, ZB = 0 here).
    /// Flag F: a code-10 shot not at the top whose class-e arrival is d = 1..8 slots away (top d wires 0, its top bit on
    /// y[wv-1-d], the arrival's zero wires y[0..=8-d], class e < 20 - d: the classes above wait for T - 16). The step bits of d
    /// (8, 4, 2, 1) park on y0..y3 (zero on every flagged shot when each is written) and the sub-rings above them turn up;
    /// then r = 16 - d onto B, the bits back to 0 from r, code 10 -> 01, and F back to 0 by the exact early cases (class
    /// marker, r): the shot is now a big waiter of case (e, r) like a late one (no natural shot matches a cube of this list:
    /// the late waiters of class e have r <= e - 4).
    fn l16_norm(&mut self, t: i32) {
        let wv = self.wr;
        let y = self.y.clone();
        let (h0, h1) = (self.e[0], self.e[1]);
        let fl = self.pg[4 * PAGE_D];
        let zb = ZB_LANE;
        let _ = t;
        let mut g: GL = vec![];
        for d in 1..=8usize {
            let mut c: Vec<Lit> = vec![(h0, false), (h1, true)];
            for i in 0..d { c.push((y[wv - 1 - i], false)); }
            c.push((y[wv - 1 - d], true));
            for i in 0..=(8 - d) { c.push((y[i], false)); }
            g.extend(self.m(&c, fl));
            if L16_TRIM && 20 - d as i32 > ECAP { continue; }
            let mut cx = c.clone();
            for i in (9 - d)..=(18 - 2 * d) { cx.push((y[i], false)); }
            g.extend(self.m(&cx, fl));
        }
        self.b.t(&g);
        for (j, s) in [(0usize, 8usize), (1, 4), (2, 2), (3, 1)] {
            let mut c: Vec<Lit> = vec![(fl, true)];
            for i in 0..s { c.push((y[wv - 1 - i], false)); }
            let mut g = self.m(&c, y[j]);
            g.push(gt(fl, y[j], zb));
            g.extend(rotate_up(zb, &y[j + 1..], s));
            g.push(gt(fl, y[j], zb));
            self.b.t(&g);
        }
        let (b8, b4, b2, b1) = (y[0], y[1], y[2], y[3]);
        let (r0, r1, r2, r3) = (y[4], y[5], y[6], y[8]);
        // r = 16 - d: r3 = 1, r0 = b1, r1 = b2 ^ b1, r2 = b4 ^ (b2 | b1)
        let mut g: GL = vec![gc(fl, r3), gt(fl, b1, r0), gt(fl, b2, r1), gt(fl, b1, r1), gt(fl, b4, r2), gt(fl, b2, r2), gt(fl, b1, r2)];
        g.extend(self.m(&[(fl, true), (b2, true), (b1, true)], r2));
        // the bits back to 0: b1 = r0, b2 = r1 ^ r0, b4 = r2 ^ (r1 | r0), b8 = [r low bits 0]
        g.extend_from_slice(&[gt(fl, r0, b1), gt(fl, r1, b2), gt(fl, r0, b2), gt(fl, r2, b4), gt(fl, r1, b4), gt(fl, r0, b4)]);
        g.extend(self.m(&[(fl, true), (r1, true), (r0, true)], b4));
        g.extend(self.m(&[(fl, true), (r0, false), (r1, false), (r2, false)], b8));
        // code 10 -> 01
        g.push(gc(fl, h0));
        g.push(gc(fl, h1));
        self.b.t(&g);
        // F back to 0: per class e the early r values (r = e mod 2, e - 4 < r <= 15, 16 - r <= min(8, e - 2)) against its late ones
        let mut g: GL = vec![];
        for e in 10..=ECAP {
            let (mut on, mut off) = (BTreeSet::new(), BTreeSet::new());
            for r in ((e % 2)..16).step_by(2) {
                if r <= e - 4 { off.insert(r); } else if 16 - r <= 8.min(e - 2) { on.insert(r); }
            }
            let mut base: Vec<Lit> = vec![(y[wv - 1], true), (h0, true), (h1, false), (y[0], false), (y[1], false), (y[2], false), (y[3], false), (y[7], false)];
            for j in 9..(e as usize - 1) { base.push((y[j], false)); }
            base.push((y[e as usize - 1], true));
            for c in l16_keys(&on, &off, &[r0, r1, r2, r3], 0) {
                g.extend(self.m(&[base.clone(), c].concat(), fl));
            }
        }
        self.b.t(&g);
    }
    fn big_pairs11(&self, t: i32) -> Vec<(i32, i32, i32, i32)> {
        let mut out = vec![];
        if l16_gone(t) {
            return out;
        }
        if LOOK16 && l16h(t) {
            // late first: r = tn mod 16 (r = e mod 2); r <= e - 4 waits (w = r), else early (w = -(16 - r), d <= min(8, e - 2));
            // no early case at CUT_T (its range belongs to the native tier below); no late r >= 8 at CUT_S - 16 (those
            // arrivals, CUT_S - 8 and up, act at CUT_S - 8 in the parent form)
            for e in 10..=ECAP {
                for r in ((e % 2)..16).step_by(2) {
                    let w = if r <= e - 4 { r } else { -(16 - r) };
                    if w < 0 && (-w > 8.min(e - 2) || !l16_early(t)) { continue; }
                    if w >= 8 && t == CUT_S - 16 { continue; }
                    let (u, v) = ((e - w) / 2, (e + w) / 2);
                    let (l, f) = (t / 2 - u, t / 2 + v);
                    if l >= 1 && f <= N as i32 && f >= l {
                        out.push((e, w, u, v));
                    }
                }
            }
            return out;
        }
        // L-C banded: inside [CUT_T, CUT_S - 17] the long classes act only at slots 0 mod 16 (w < 16), else w < 8
        // a long case whose wait to the slot 0 mod 16 would leave u = (e - w) / 2 = 1 ((16, 14), (17, 15)) acts at the slot
        // 8 mod 16 before it instead, as (e, w - 8) (the frame's post has no u = 1 form)
        let ok = |e: i32, w: i32| -> bool {
            if !(TIER_LONG > 0 && e >= TIER_LONG && long16(t)) {
                return w < 8;
            }
            if t.rem_euclid(16) == 0 { w < 16 && (w < 8 || e - w != 2) } else { w < 8 && e - (w + 8) == 2 }
        };
        for w in 0..16 {
            for e in 10..=ECAP {
                if !ok(e, w) {
                    continue;
                }
                if (e - w).rem_euclid(2) != 0 {
                    continue;
                }
                let (u, v) = ((e - w) / 2, (e + w) / 2);
                let (l, f) = (t / 2 - u, t / 2 + v);
                if l >= 1 && f <= N as i32 && f >= l {
                    out.push((e, w, u, v));
                }
            }
        }
        out
    }
    /// A shot that has just reached the top with e >= 10 takes code 01 and w = tn mod 8. ctl is clean.
    fn arrive11(&mut self, tn: i32, y: &[u32], ctl: u32) {
        r7e_sub("arrive_tiers");
        let wv = self.wr;
        let (h0, h1) = (self.e[0], self.e[1]);
        let w = tn.rem_euclid(8);
        let yt2 = y[wv - 1];
        let mut l: Vec<Lit> = vec![(yt2, true)];
        l.extend(self.hc(2));
        for j in 1..9 {
            l.push((y[j], false));
        }
        let mut g = self.m(&l, ctl);
        g.push(gc(ctl, h0));
        g.push(gc(ctl, h1));
        for i in 0..3 {
            if (w >> i) & 1 == 1 {
                g.push(gc(ctl, y[4 + i]));
            }
        }
        if (long16(tn) || l16_arr(tn)) && tn.rem_euclid(16) >= 8 {
            // LOOK16: r = tn mod 16, bit 3 on y8 (zero for every big arrival)
            g.push(gc(ctl, if W4HOST || l16_arr(tn) { y[8] } else { self.w4 }));
        }
        let mut l: Vec<Lit> = vec![(yt2, true)];
        l.extend(self.hc(1));
        l.push((y[1], false));
        for i in 0..3 {
            l.push((y[4 + i], (w >> i) & 1 == 1));
        }
        if long16(tn) || l16_arr(tn) {
            // a long waiter that arrived 8 slots earlier has the same 3 low wait bits: W4 tells them apart
            l.push((if W4HOST || l16_arr(tn) { y[8] } else { self.w4 }, tn.rem_euclid(16) >= 8));
        }
        g.extend(self.m(&l, ctl));
        self.b.t(&g);
        if cad4_arr(tn) {
            let w1l = self.w1;
            let mut g: GL = vec![];
            if tn.rem_euclid(4) == 3 {
                // an odd low class e >= 5 (the big classes left code 01 above): it waits for the slot 0 mod 4
                let mut l: Vec<Lit> = vec![(yt2, true)];
                l.extend(self.hc(2));
                l.extend_from_slice(&[(y[1], false), (y[2], false)]);
                g.extend(self.m(&l, w1l));
            } else {
                // the odd waiters (W1 = 1, marker on an even wire) sit at the top too: read the even classes' marker
                for e in [4usize, 6, 8] {
                    let mut l: Vec<Lit> = vec![(yt2, true)];
                    l.extend(self.hc(2));
                    for j in 1..(e - 1) {
                        l.push((y[j], false));
                    }
                    l.push((y[e - 1], true));
                    g.extend(self.m(&l, w1l));
                }
            }
            self.b.t(&g);
        }
    }
    /// r7e JSWAP: junction swap of the big phase. For the acting big shots (cl) the page's low words are swapped with the D ring
    /// wires next to the shot's junction, so that the rows run as plain ring rows from bit 0 (no page cells, windows or slides).
    /// Geometry between the cuts (narrowed rings, D = PAGE_D, SY = wv - (t/2 - u) + D, SX = wv - (t/2 + v) + D): ring Y holds
    /// B[D + j] on y[SY + j] and tA[D + i] on y[SY - 1 - i]; ring X holds A[D + j] on x[SX + j] and tB[D + i] on x[SX - 1 - i].
    /// V form (cof = false): VB[b] <-> y[SY - D + b] (by u), VA[b] <-> x[SX - D + b] (by v): the values are whole in the rings,
    /// the cofactor bits D..2D-1 are parked on the page lanes. C form (cof = true): VB[b] <-> y[SY + D - 1 - b] (by u),
    /// SC[b] <-> x[SX + D - 1 - b] (by v): the cofactors are whole, the value bits D..2D-1 are parked. Self-inverse given the
    /// same hosted bits (hb = hi, a = w0, w1, w2); the group flags are the slide's demux walk on u = hi - (w >> 1) and
    /// v = hi + w0 + (w >> 1) mod 16.
    fn jswap(&self, t: i32, prs: &[(i32, i32, i32, i32)], hb: &[u32], a: [u32; 3], cof: bool, full16: bool, w4: u32) -> GL {
        self.jswap_f(t, prs, hb, a, cof, full16, w4, &[])
    }
    /// jswap with the acting-big literal given (E3V: code 01 in even11); empty = yt & code 11
    #[allow(clippy::too_many_arguments)]
    fn jswap_f(&self, t: i32, prs: &[(i32, i32, i32, i32)], hb: &[u32], a: [u32; 3], cof: bool, full16: bool, w4: u32, fam: &[Lit]) -> GL {
        let wv = self.wr;
        let dd = PAGE_D;
        let (x, y) = (&self.x, &self.y);
        let d = x[0];
        let (va, vb, sc) = (&self.pg[..dd], &self.pg[dd..2 * dd], &self.pg[2 * dd..3 * dd]);
        let cl: Vec<Lit> = if fam.is_empty() { [vec![(y[wv - 1], true)], self.hc(3)].concat() } else { fam.to_vec() };
        let mut cu = dec_ctl(hb, &[(a[1], true)], &self.dirty);
        cu.extend(dec_ctl(&hb[1..], &[(a[2], true)], &self.dirty));
        let mut cv = inc_ctl(hb, &[(a[0], true)], &self.dirty);
        cv.extend(inc_ctl(hb, &[(a[1], true)], &self.dirty));
        cv.extend(inc_ctl(&hb[1..], &[(a[2], true)], &self.dirty));
        if full16 {
            cu.extend(dec_ctl(&hb[2..], &[(w4, true)], &self.dirty));
            cv.extend(inc_ctl(&hb[2..], &[(w4, true)], &self.dirty));
        }
        let us: BTreeSet<i32> = prs.iter().map(|p| p.2).collect();
        let vs: BTreeSet<i32> = prs.iter().map(|p| p.3).collect();
        assert!(us.len() == us.iter().map(|u| u.rem_euclid(16)).collect::<BTreeSet<i32>>().len(), "jswap: u groups collide mod 16");
        assert!(vs.len() == vs.iter().map(|v| v.rem_euclid(16)).collect::<BTreeSet<i32>>().len(), "jswap: v groups collide mod 16");
        let fa = if cof { None } else { Some(self.pg[4 * dd]) };
        let mut g: GL = vec![];
        let mut gr: Vec<(i32, Vec<Vec<Lit>>, GL)> = vec![];
        for &u in &us {
            let sy = wv as i32 - (t / 2 - u) + dd as i32;
            // V form needs the D cofactor wires below the junction clear of the hosted lanes y[0..10); C form needs the D value
            // wires above it below the top wire
            assert!(if cof { sy + dd as i32 <= wv as i32 - 1 } else { sy - dd as i32 >= 10 }, "jswap: Y wires out of range at t {t} u {u}");
            let mut sw: GL = vec![];
            for b in 0..dd {
                let w_ = if cof { sy as usize + dd - 1 - b } else { sy as usize - dd + b };
                cswap(d, vb[b], y[w_], &mut sw);
            }
            gr.push((u.rem_euclid(16), vec![vec![]], sw));
        }
        g.extend_from_slice(&cu);
        g.extend(self.demux(&cl, hb, &mut gr, d, fa));
        g.extend(rev(&cu));
        let mut gr: Vec<(i32, Vec<Vec<Lit>>, GL)> = vec![];
        for &v in &vs {
            let sx = wv as i32 - (t / 2 + v) + dd as i32;
            // C form: the D value wires above the junction must stay below the digit lanes x[wv - e..] of every class in the group
            let emax = prs.iter().filter(|p| p.3 == v).map(|p| p.0).max().unwrap();
            assert!(if cof { sx + dd as i32 <= wv as i32 - emax } else { sx - dd as i32 >= 1 }, "jswap: X wires out of range at t {t} v {v}");
            let mut sw: GL = vec![];
            for b in 0..dd {
                let w_ = if cof { sx as usize + dd - 1 - b } else { sx as usize - dd + b };
                cswap(d, if cof { sc[b] } else { va[b] }, x[w_], &mut sw);
            }
            gr.push((v.rem_euclid(16), vec![vec![]], sw));
        }
        g.extend_from_slice(&cv);
        g.extend(self.demux(&cl, hb, &mut gr, d, fa));
        g.extend(rev(&cv));
        g
    }
    /// LOOK16 h1: A (hi', 3 lanes) -> U3 = hi' + 3 - (r >> 1) mod 8 under lits (r on B, 4 lanes)
    fn l16_cu(&self, a: &[u32], b: &[u32], lits: &[Lit]) -> GL {
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let mut g = inc_ctl(a, lits, &self.dirty);
        g.extend(inc_ctl(&a[1..], lits, &self.dirty));
        g.extend(dec_ctl(a, &cat(lits, &[(b[1], true)]), &self.dirty));
        g.extend(dec_ctl(&a[1..], &cat(lits, &[(b[2], true)]), &self.dirty));
        g.extend(dec_ctl(&a[2..], &cat(lits, &[(b[3], true)]), &self.dirty));
        g
    }
    /// LOOK16 h1: B (r) -> V4 = U3 + r + 1 mod 16 under lits (U3 on A)
    fn l16_cv(&self, a: &[u32], b: &[u32], lits: &[Lit]) -> GL {
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let mut g = inc_ctl(b, lits, &self.dirty);
        for i in 0..3 {
            g.extend(inc_ctl(&b[i..], &cat(lits, &[(a[i], true)]), &self.dirty));
        }
        g
    }
    /// LOOK16 h1 junction swap (jswap_f's geometry and demux): the Y-side groups by U3 = u - 2 on A (demux's fourth key lane
    /// is h1, which the family cube holds at 0), the X-side groups by V4 = v - 1 on B; conversions unconditional and undone.
    /// The hosted lanes come in and go out in the hi form (hi', r).
    fn l16_jswap(&self, t: i32, prs: &[(i32, i32, i32, i32)], a: &[u32], b: &[u32], cof: bool, fam: &[Lit]) -> GL {
        self.l16_jswap_f(t, prs, a, b, cof, fam, 0)
    }
    /// form: 0 = hosted lanes in (hi', r); 1 = (U3, r) on the family (only B -> V4 inside); 2 = (U3, V4) (no conversion)
    #[allow(clippy::too_many_arguments)]
    fn l16_jswap_f(&self, t: i32, prs: &[(i32, i32, i32, i32)], a: &[u32], b: &[u32], cof: bool, fam: &[Lit], form: u8) -> GL {
        let wv = self.wr;
        let dd = PAGE_D;
        let (x, y) = (&self.x, &self.y);
        let d = x[0];
        let h1 = self.e[1];
        let (va, vb, sc) = (&self.pg[..dd], &self.pg[dd..2 * dd], &self.pg[2 * dd..3 * dd]);
        assert!(fam.contains(&(h1, false)), "LOOK16 jswap: the family cube must hold h1 = 0");
        let cl: Vec<Lit> = fam.to_vec();
        let cu = if form == 0 { self.l16_cu(a, b, &[]) } else { vec![] };
        let cv = if form <= 1 { self.l16_cv(a, b, &[]) } else { vec![] };
        let us: BTreeSet<i32> = prs.iter().map(|p| p.2).collect();
        let vs: BTreeSet<i32> = prs.iter().map(|p| p.3).collect();
        assert!(us.iter().all(|&u| (2..=9).contains(&u)) && vs.iter().all(|&v| (1..=16).contains(&v)), "LOOK16 jswap: u or v out of the h1 range");
        let fa = if cof { None } else { Some(self.pg[4 * dd]) };
        let ua: Vec<u32> = vec![a[0], a[1], a[2], h1];
        let mut g: GL = vec![];
        if LT_JSWAP_FUNNEL && form >= 1 {
            // LT_JSWAP_FUNNEL (see the switch): the same windows as below, by ring index
            let mut yw: BTreeMap<i32, Vec<(u32, usize)>> = BTreeMap::new();
            for &u in &us {
                let sy = wv as i32 - (t / 2 - u) + dd as i32;
                assert!(if cof { sy + dd as i32 <= wv as i32 - 1 } else { sy - dd as i32 >= 10 }, "jswap: Y wires out of range at t {t} u {u}");
                yw.insert(u - 2, (0..dd).map(|bq| (vb[bq], if cof { sy as usize + dd - 1 - bq } else { sy as usize - dd + bq })).collect());
            }
            let mut xw: BTreeMap<i32, Vec<(u32, usize)>> = BTreeMap::new();
            for &v in &vs {
                let sx = wv as i32 - (t / 2 + v) + dd as i32;
                let emax = prs.iter().filter(|p| p.3 == v).map(|p| p.0).max().unwrap();
                assert!(if cof { sx + dd as i32 <= wv as i32 - emax } else { sx - dd as i32 >= 1 }, "jswap: X wires out of range at t {t} v {v}");
                xw.insert(v - 1, (0..dd).map(|bq| (if cof { sc[bq] } else { va[bq] }, if cof { sx as usize + dd - 1 - bq } else { sx as usize - dd + bq })).collect());
            }
            let mut g = self.m(&cl, d);
            let (gy, hy) = lt_funnel_side(&yw, &y[..wv], &a[..3], d);
            let (gxs, hx) = lt_funnel_side(&xw, &x[..wv], b, d);
            for q in hy.iter().chain(hx.iter()) {
                assert!(!a.contains(q) && !b.contains(q) && !cl.iter().any(|l| l.0 == *q) && *q != d && *q != ZB_LANE && *q != h1,
                    "LT funnel: the hull meets a key, family or clean lane at t {t}");
            }
            g.extend(gy);
            g.extend_from_slice(&cv);
            g.extend(gxs);
            g.extend(rev(&cv));
            g.extend(self.m(&cl, d));
            return g;
        }
        let mut gr: Vec<(i32, Vec<Vec<Lit>>, GL)> = vec![];
        for &u in &us {
            let sy = wv as i32 - (t / 2 - u) + dd as i32;
            assert!(if cof { sy + dd as i32 <= wv as i32 - 1 } else { sy - dd as i32 >= 10 }, "jswap: Y wires out of range at t {t} u {u}");
            let mut sw: GL = vec![];
            for bq in 0..dd {
                let w_ = if cof { sy as usize + dd - 1 - bq } else { sy as usize - dd + bq };
                cswap(d, vb[bq], y[w_], &mut sw);
            }
            gr.push((u - 2, vec![vec![]], sw));
        }
        g.extend_from_slice(&cu);
        // demux's A-level AND (fa = None: cc_core / mac_aux) does not merge repeated literals, so the Y side's cube leaves out
        // the family's h1 = 0: the fourth key lane (h1, every key < 8) supplies it
        let cly: Vec<Lit> = cl.iter().cloned().filter(|l| *l != (h1, false)).collect();
        g.extend(self.demux(&cly, &ua, &mut gr, d, fa));
        let mut gr: Vec<(i32, Vec<Vec<Lit>>, GL)> = vec![];
        for &v in &vs {
            let sx = wv as i32 - (t / 2 + v) + dd as i32;
            let emax = prs.iter().filter(|p| p.3 == v).map(|p| p.0).max().unwrap();
            assert!(if cof { sx + dd as i32 <= wv as i32 - emax } else { sx - dd as i32 >= 1 }, "jswap: X wires out of range at t {t} v {v}");
            let mut sw: GL = vec![];
            for bq in 0..dd {
                let w_ = if cof { sx as usize + dd - 1 - bq } else { sx as usize - dd + bq };
                cswap(d, if cof { sc[bq] } else { va[bq] }, x[w_], &mut sw);
            }
            gr.push((v - 1, vec![vec![]], sw));
        }
        g.extend_from_slice(&cv);
        g.extend(self.demux(&cl, b, &mut gr, d, fa));
        g.extend(rev(&cv));
        g.extend(rev(&cu));
        g
    }
    /// Rows, marker and post of the waiting big shots (code 01) at a tier slot, after the slot's own low work.
    fn big_phase(&mut self, t: i32) {
        let wv = self.wr;
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        let prs = self.big_pairs11(t);
        r7e_tag("big:a_prefix"); r7e_keys(&[format!("T{:03}", t)]);
        let es: BTreeSet<i32> = prs.iter().map(|p| p.0).collect();
        let kk = *es.iter().next_back().unwrap() + 1;
        let yt = y[wv - 1];
        let (d, ctl) = (x[0], x[0]);
        let (y0, y1) = (y[0], y[1]);
        let (w0, w1, w2) = (y[4], y[5], y[6]);
        let hb0: Vec<u32> = vec![y[2], y[3], y[7], y[8]];
        let cv9 = y[9];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        // L-C: at a slot 8 mod 16 of the long region only the short classes (marker in Y[9..TIER_LONG-2]) act; the long
        // waiters keep code 10. Every short actor there arrived at tn = 8..15 mod 16, so its W4 is 1: clear it.
        let band8 = TIER_LONG > 0 && long16(t) && t.rem_euclid(16) == 8;
        let full16 = TIER_LONG > 0 && long16(t) && t.rem_euclid(16) == 0;
        let w4h = W4HOST && full16;
        // the W4 lane while waiting (w4w) and during the phase of a slot 0 mod 16 (w4p; W4HOST: CAD4's lane W1, 0 on every shot
        // during a phase at a slot 0 mod 4)
        let w4w = if W4HOST { y[8] } else { self.w4 };
        let w4p = if W4HOST { self.w1 } else { self.w4 };
        // E3C: even11 already ran this phase's rows and sandwich; only the marker, the post and the wait rotation are left
        let e3c = E3C_T.load(Ordering::Relaxed) && self.e3t;
        if self.e3t && !e3c {
            // E3V: the row-0 digit back from its parking lane (the big shots are still code 01 here; at a slot 8 mod 16 of the
            // long region the not-acting long waiters are code 01 too: W1 tells the actors)
            let clb: Vec<Lit> = if band8 { vec![(yt, true), (h1, false), (self.w1, true)] } else { vec![(yt, true), (h0, true), (h1, false), (y1, false)] };
            let mut g = self.m(&cat(&clb, &[(y[7], true)]), y0);
            g.extend(self.m(&cat(&clb, &[(y0, true)]), y[7]));
            // and the big mark off W1 (0 again for every shot before arrive11), by a predicate that does not read W1
            if band8 {
                for c in self.band8_actors(t, &y) { g.extend(self.m(&cat(&c, &[(h1, false)]), self.w1)); }
            } else {
                g.extend(self.m(&clb, self.w1));
            }
            self.b.t(&g);
        }
        let g = if band8 {
            let mut g: GL = vec![];
            for j in 9..=(TIER_LONG.max(11) as usize - 2) {
                let mut l: Vec<Lit> = vec![(yt, true), (h0, true)];
                for i in 9..j { l.push((y[i], false)); }
                l.push((y[j], true));
                g.extend(self.m(&l, h1));
            }
            // the long cases moved here from the next slot 0 mod 16 (u would be 1): class e with w = e - 10
            for e in (TIER_LONG.max(11))..=17 {
                let mut l: Vec<Lit> = vec![(yt, true), (h0, true)];
                for i in 9..(e as usize - 1) { l.push((y[i], false)); }
                l.push((y[e as usize - 1], true));
                for i in 0..3 { l.push((y[4 + i], ((e - 10) >> i) & 1 == 1)); }
                g.extend(self.m(&l, h1));
            }
            g
        } else {
            self.m(&[(yt, true), (h0, true)], h1)
        };
        self.b.t(&g);
        let cl: Vec<Lit> = cat(&[(yt, true)], &self.hc(3));
        if e3c {
            // E3C: y0, y1, y2 back from x[wv - 1..wv - 3], and the big mark off W1 (cl is code 11 now; every actor has W1 = 1)
            let mut g: GL = vec![];
            for (src, dst) in [(x[wv - 1], y0), (x[wv - 2], y1), (x[wv - 3], y[2])] {
                g.extend(self.m(&cat(&cl, &[(src, true)]), dst));
                g.extend(self.m(&cat(&cl, &[(dst, true)]), src));
            }
            g.extend(self.m(&cl, self.w1));
            self.b.t(&g);
        }
        // LOOK16 h1 (the hosted lanes where even11's C rows left them: A = x[wv-4], x[wv-5], x[wv-9]; B = x[wv-6], x[wv-7],
        // x[wv-8], x[wv-10]): r3 leaves x[wv-10] (class 10's marker lane) for W1 (0 on every actor here; the late shots' rotation
        // by 8 reads it there), and the early flag E (from (hi', r)) goes to x[wv-1] (free again: y0 is back)
        let l16 = e3c && l16h(t);
        let l16e = l16 && prs.iter().any(|p_| p_.1 < 0);
        let l16w8 = l16 && prs.iter().any(|p_| p_.1 >= 8);
        if l16 {
            let src = x[wv - 10];
            let mut g = self.m(&cat(&cl, &[(src, true)]), self.w1);
            g.extend(self.m(&cat(&cl, &[(self.w1, true)]), src));
            if l16e {
                let l7: Vec<u32> = vec![x[wv - 4], x[wv - 5], x[wv - 9], x[wv - 6], x[wv - 7], x[wv - 8], self.w1];
                let (mut on, mut off): (Vec<usize>, Vec<usize>) = (vec![], vec![]);
                for c in &prs { if c.1 < 0 { on.push(l16_pt(0, c)); } else { off.push(l16_pt(0, c)); } }
                for cube in l16_cubes(&on, &off, &l7) { g.extend(self.m(&cat(&cl, &cube), x[wv - 1])); }
            }
            self.tsub("big:l16_prefix", &g);
        }
        if band8 && !self.e3t {
            let g = self.m(&cl, w4w);
            self.b.t(&g);
        }
        let pgo = PAGE_G && mid_even(t);
        let case_st = |e: i32, w: i32| -> Vec<Lit> {
            let mut l = cl.clone();
            for i in 0..3 {
                l.push((y[4 + i], (w >> i) & 1 == 1));
            }
            for j in 9..(e as usize - 1) {
                l.push((y[j], false));
            }
            l.push((y[e as usize - 1], true));
            l
        };
        let case_end = |e: i32, w: i32| -> Vec<Lit> {
            let mut l = cl.clone();
            for i in 0..3 {
                l.push((x[wv - 2 - i], (w >> i) & 1 == 1));
            }
            l.push((x[wv - e as usize], true));
            for j in 10..(e as usize) {
                l.push((x[wv - j], false));
            }
            l
        };
        let mut g: GL = vec![];
        if w4h {
            // W4HOST: the actors' W4 leaves y[8] (hi's bit 3 below) for the lane W1 (0 on every shot here)
            g.extend(self.m(&cat(&cl, &[(y[8], true)]), w4p));
            g.extend(self.m(&cat(&cl, &[(w4p, true)]), y[8]));
        }
        for &e in &es {
            let mut li = cl.clone();
            for j in 9..(e as usize - 1) {
                li.push((y[j], false));
            }
            li.push((y[e as usize - 1], true));
            let m = e >> 1;
            for i in 0..4 {
                if (m >> i) & 1 == 1 {
                    g.extend(self.m(&li, hb0[i]));
                }
            }
        }
        for &e in &es {
            let mut li = cl.clone();
            for i in 0..4 {
                li.push((hb0[i], ((e >> 1) >> i) & 1 == 1));
            }
            li.push((w0, e & 1 == 1));
            g.extend(self.m(&li, y[e as usize - 1]));
        }
        if !e3c {
            self.b.t(&g);
        }
        let lits = |cubes: &Cubes, lanes: &[u32]| -> Vec<Vec<Lit>> { cubes.iter().map(|x_| x_.iter().map(|&(v, bt)| (lanes[v], bt == 1)).collect()).collect() };
        let exact = |k: i32, lanes: &[u32]| -> Vec<Vec<Lit>> {
            let (mut on, mut off) = (0u128, 0u128);
            for &e in &es {
                let p_ = (e >> 1) | ((e & 1) << 4);
                if e >= k {
                    on |= 1u128 << p_;
                } else {
                    off |= 1u128 << p_;
                }
            }
            lits(&dtree(on, off, &[0, 1, 2, 3, 4], 1), lanes).into_iter().map(|x_| cat(&x_, &cl)).collect()
        };
        let hterm = |vals: &BTreeSet<i32>, others: &BTreeSet<i32>, lanes: &[u32]| -> Vec<Vec<Lit>> {
            let (mut on, mut off) = (0u128, 0u128);
            for &x_ in vals {
                on |= 1u128 << (x_ % 16);
            }
            for &x_ in others {
                off |= 1u128 << (x_ % 16);
            }
            lits(&dtree(on, off, &[0, 1, 2, 3], 0), lanes)
        };
        // P1 big classes through the page: case flags on (hi, w) by decision trees (7 vars: hi bits 0..3, w bits 4..6)
        let dd = PAGE_D;
        let (va, vb, sc) = if pgo { (self.pg[..dd].to_vec(), self.pg[dd..2 * dd].to_vec(), self.pg[2 * dd..3 * dd].to_vec()) } else { (vec![], vec![], vec![]) };
        // JSWAP halves (JSWAP_V: the V rows, JSWAP_C: the C rows; separately switchable for bisecting a failed grade)
        let jsv = pgo && JSWAP && JSWAP_V;
        let jsc = pgo && JSWAP && JSWAP_C;
        let pdv = if pgo && !jsv { dd as i32 } else { 0 };
        let pdc = if pgo && !jsc { dd as i32 } else { 0 };
        let cpt = |e: i32, w: i32| -> usize { ((e >> 1) | (w << 4)) as usize };
        // hsel: 0 -> the hosted lanes hold hi = e >> 1, 1 -> u (after cv_v), 2 -> v mod 16 (after cv_c)
        let cflagh = |me: &Machine, on_set: &[(i32, i32)], lanes: &[u32], hsel: u8| -> GL {
            let (mut on, mut off): (Vec<usize>, Vec<usize>) = (vec![], vec![]);
            for &(e, w, u, v) in &prs {
                let h = match hsel { 0 => e >> 1, 1 => u, _ => v % 16 };
                let pt = (h | (w << 4)) as usize;
                if on_set.contains(&(e, w)) { on.push(pt); } else { off.push(pt); }
            }
            let mut g: GL = vec![];
            for cube in hw_cubes(&on, &off, lanes, w4p) {
                g.extend(me.m(&cat(&cube, &cl), d));
            }
            g
        };
        let cflag = |me: &Machine, on_set: &[(i32, i32)], lanes: &[u32]| -> GL { cflagh(me, on_set, lanes, 0) };
        let lanes_v: Vec<u32> = vec![hb0[0], hb0[1], hb0[2], hb0[3], w0, w1, w2];
        r7e_tag("big:b_Vwin_in");
        if jsv && !self.e3t {
            let g = self.jswap(t, &prs, &hb0, [w0, w1, w2], false, full16, w4p);
            pg_add(8, &g);
            self.b.t(&g);
        }
        if pgo && !jsv {
            BIG_SITE.store(1, Ordering::Relaxed);
            let mut g: GL = vec![];
            for &(e, w, _u, v) in &prs {
                let fu = (t / 2 + v) as usize;
                let fl = cflag(self, &[(e, w)], &lanes_v);
                let mut lanes = va.clone();
                lanes.extend((0..e as usize).map(|i| x[wv - fu + dd + i]));
                let n = lanes.len();
                let ro = rotate_up(d, &lanes, n - e as usize);
                pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl);
                g.extend_from_slice(&fl);
                g.extend(ro);
                g.extend_from_slice(&fl);
            }
            self.b.t(&g);
        }
        let mut cv_v = dec_ctl(&hb0, &[(w1, true)], &self.dirty);
        cv_v.extend(dec_ctl(&hb0[1..], &[(w2, true)], &self.dirty));
        if full16 {
            cv_v.extend(dec_ctl(&hb0[2..], &[(w4p, true)], &self.dirty));
        }
        let kh = *es.iter().next().unwrap();
        let cvh = cvhv_on() && jsv;
        if cvh && !e3c {
            self.b.t(&cv_v);
        }
        for k in 0..kk {
            r7e_keys(&[format!("T{:03}", t), format!("K{:02}", k)]);
            let act: Vec<(i32, i32, i32, i32)> = prs.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() || (self.e3t && k < 10) || e3c {
                continue;
            }
            let mut starts: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
            for &(_e, _w, u, _v) in &act {
                starts.entry(wv as i32 - (t / 2 - u) - k + pdv).or_default().insert(u);
            }
            let alo = *starts.keys().next().unwrap();
            assert!(alo + k >= 10);
            let (ku, alo_u) = (k as usize, alo as usize);
            let tv: Vec<u32> = (alo_u..(wv - ku - 1)).map(|a| x[a]).collect();
            let sv: Vec<u32> = (alo_u..(wv - ku - 1)).map(|a| y[a + ku]).collect();
            let t1 = x[wv - 1 - ku];
            let top = if k >= 1 { x[wv - ku] } else { NONE };
            let actv = exact(k, &[hb0[0], hb0[1], hb0[2], hb0[3], w0]);
            let allu: BTreeSet<i32> = act.iter().map(|p| p.2).collect();
            let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for (&a, us) in &starts {
                let rest: BTreeSet<i32> = allu.difference(us).cloned().collect();
                tg.insert((a - alo) as usize, hterm(us, &rest, &hb0));
            }
            let hz = cvh && k <= kh;
            assert!(!hz || actv == vec![cl.clone()], "CVHV: act cube of row {k} reads the hosted lanes");
            let g = self.row_v(&tv, &sv, t1, top, d, cv9, y1, &tg, &actv, None, if hz { None } else { Some(&cv_v) });
            if pgo && !jsv {
                let mut up: GL = vec![];
                let mut dn: GL = vec![];
                for b in 0..dd {
                    let (sq, tq) = (vb[b], va[(b + 3 * dd - ku) % dd]);
                    up.extend_from_slice(&[gx(tq), gc(cv9, sq), gc(cv9, tq), gt(sq, tq, cv9)]);
                }
                for b in (0..dd).rev() {
                    let (sq, tq) = (vb[b], va[(b + 3 * dd - ku) % dd]);
                    dn.extend_from_slice(&[gt(sq, tq, cv9), gc(cv9, tq), gt(d, sq, tq), gc(cv9, sq), gx(tq)]);
                }
                pg_add(1, &up); pg_add(1, &dn);
                r7e_tag("big:c_Vcells");
                self.b.t(&up);
                r7e_tag("big:c_Vrow");
                self.b.t(&g);
                r7e_tag("big:c_Vcells");
                self.b.t(&dn);
            } else {
                r7e_tag("big:c_Vrow");
                self.b.t(&g);
            }
            r7e_tag("big:c_Vdigit");
            let mut g: GL = vec![];
            if k >= 1 {
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(x[wv - ku], true)]), d));
                }
            } else {
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(d, true)]), y0));
                }
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(y0, true)]), d));
                }
            }
            self.b.t(&g);
            if cvh && k == kh {
                self.b.t(&rev(&cv_v));
            }
            if pgo && !jsv {
                // window slide for the cases with e > k, one swap per u (same ring wire)
                r7e_tag("big:c_Vslide");
                BIG_SITE.store(2, Ordering::Relaxed);
                let mut grp: BTreeMap<i32, Vec<(i32, i32)>> = BTreeMap::new();
                for &(e, w, u, _v) in prs.iter().filter(|p| p.0 >= k + 1) {
                    grp.entry(u).or_default().push((e, w));
                }
                let mut g: GL = cv_v.clone();
                pg_add(4, &cv_v); pg_add(4, &cv_v);
                if SLIDE_LAD {
                    let mut gr: Vec<(i32, Vec<Vec<Lit>>, GL)> = vec![];
                    for (u, cs) in &grp {
                        let on: Vec<usize> = cs.iter().map(|&(_e, w)| (w << 4) as usize).collect();
                        let off: Vec<usize> = prs.iter().filter(|p| p.2 == *u && p.0 < k + 1).map(|p| (p.1 << 4) as usize).collect();
                        let ex = if off.is_empty() { vec![vec![]] } else { hw_cubes(&on, &off, &lanes_v, w4p) };
                        let mut sw: GL = vec![];
                        cswap(d, va[(3 * dd - 1 - ku) % dd], x[wv - (t / 2 - u) as usize + dd - ku - 1], &mut sw);
                        pg_add(3, &sw);
                        gr.push((*u, ex, sw));
                    }
                    g.extend(self.demux(&cl, &hb0, &mut gr, d, Some(self.pg[4 * dd])));
                    grp.clear();
                }
                for (u, cs) in grp {
                    let fl = cflagh(self, &cs, &lanes_v, 1);
                    let mut sw: GL = vec![];
                    cswap(d, va[(3 * dd - 1 - ku) % dd], x[wv - (t / 2 - u) as usize + dd - ku - 1], &mut sw);
                    pg_add(3, &sw); pg_add(4, &fl); pg_add(4, &fl);
                    g.extend_from_slice(&fl);
                    g.extend(sw);
                    g.extend_from_slice(&fl);
                }
                g.extend(rev(&cv_v));
                self.b.t(&g);
            }
        }
        // P1: window out + digit remap (weights 0..9 of class e sit on X[wv-e..wv-e+9] -> Q = X[wv-10..wv-1]), sandwich,
        // remap back, role swap, cofactor window out (inverse)
        if jsv && !e3c {
            r7e_keys(&[format!("T{:03}", t)]);
            r7e_tag("big:c_Vjswap_out");
            let g = self.jswap(t, &prs, &hb0, [w0, w1, w2], false, full16, w4p);
            pg_add(8, &g);
            self.b.t(&g);
        }
        let mut sw_post: GL = vec![];
        r7e_keys(&[format!("T{:03}", t)]);
        r7e_tag("big:d1_Vwinout_remap");
        BIG_SITE.store(3, Ordering::Relaxed);
        if pgo && !e3c {
            let es_l: Vec<i32> = es.iter().cloned().collect();
            let cls_cases = |e: i32| -> Vec<(i32, i32)> { prs.iter().filter(|p| p.0 == e).map(|p| (p.0, p.1)).collect() };
            let mut g: GL = vec![];
            let mut rms: Vec<GL> = vec![];
            for &e in &es_l {
                let fl = cflag(self, &cls_cases(e), &lanes_v);
                let ro = rotate_up(d, &va, e as usize % dd);
                // class e >= D: weights 0..D-1 of its digits (X[wv-e+j]) -> Q = X[wv-D..wv-1]; class e < D (D > 10): the
                // D top lanes rotate up by e (weight j -> Q[j]); Q[e..D) then hold non-digits: weight e is row 0's digit
                // on y0, weights above it are 0 (both by the class gating of the sandwich)
                let eu = e as usize;
                let rm = if eu >= dd {
                    let lanes: Vec<u32> = (0..eu).map(|i| x[wv - eu + i]).collect();
                    if eu > dd { rotate_up(d, &lanes, eu - dd) } else { vec![] }
                } else {
                    let lanes: Vec<u32> = (0..dd).map(|i| x[wv - dd + i]).collect();
                    rotate_up(d, &lanes, eu)
                };
                if !jsv { pg_add(2, &ro); } pg_add(4, &fl); pg_add(4, &fl); pg_add(5, &rm); pg_add(5, &rm);
                g.extend_from_slice(&fl);
                if !jsv { g.extend(ro); }
                g.extend_from_slice(&rm);
                g.extend_from_slice(&fl);
                rms.push(rm);
            }
            self.b.t(&g);
            let q: Vec<u32> = (0..dd).map(|j| x[wv - dd + j]).collect();
            let (pre, post) = if es_l.iter().all(|&e| e as usize >= dd) {
                self.sandwich(&q, d, &[cl.clone()])
            } else {
                // cubes over the hosted (hi, w) lanes of the acting classes that satisfy p (given cl)
                let cubes = |p: &dyn Fn(i32) -> bool| -> Vec<Vec<Lit>> {
                    let (mut on, mut off): (Vec<usize>, Vec<usize>) = (vec![], vec![]);
                    for &(e, w, _u, _v) in &prs {
                        let pt = ((e >> 1) | (w << 4)) as usize;
                        if p(e) { on.push(pt); } else { off.push(pt); }
                    }
                    if on.is_empty() { return vec![]; }
                    if off.is_empty() { return vec![vec![]]; }
                    hw_cubes(&on, &off, &lanes_v, w4p)
                };
                let withcl = |v: Vec<Vec<Lit>>| -> Vec<Vec<Lit>> { v.into_iter().map(|c| cat(&c, &cl)).collect() };
                // weight e of class e is row 0's digit, on y0 (not an implicit 1: q of class e can be below 2^e)
                let ony0 = |v: Vec<Vec<Lit>>| -> Vec<Vec<Lit>> { v.into_iter().map(|c| cat(&c, &[(y0, true)])).collect() };
                self.sandwich_x(&q, d, &[cl.clone()], &|j| withcl(cubes(&|e| e as usize > j)), &|j| cubes(&|e| e as usize > j),
                    &|j| ony0(withcl(cubes(&|e| e as usize == j))), &|j| ony0(cubes(&|e| e as usize == j)))
            };
            let fz = self.pg[4 * dd];
            let mut rs: GL = vec![];
            for j in 0..dd {
                cswap(fz, vb[j], sc[j], &mut rs);
            }
            pg_add(5, &pre); pg_add(5, &post); pg_add(5, &rs); pg_add(5, &rs);
            r7e_tag("big:d2_sandwich_pre");
            { let (a_, k_) = swx_last(); self.t3(&pre, a_, k_, ["d2_sw_sel", "d2_sw_K2", "d2_sandwich_pre"], true); }
            r7e_tag("big:d3_roleswap");
            self.b.t(&rs);
            r7e_tag("big:d4_Cwin");
            BIG_SITE.store(4, Ordering::Relaxed);
            let mut g: GL = vec![];
            for (ie, &e) in es_l.iter().enumerate() {
                let fl = cflag(self, &cls_cases(e), &lanes_v);
                let ro = rotate_up(d, &vb, (dd - e as usize % dd) % dd);
                if !jsc { pg_add(2, &ro); } pg_add(4, &fl); pg_add(4, &fl);
                g.extend_from_slice(&fl);
                g.extend(rev(&rms[ie]));
                if !jsc { g.extend(ro); }
                g.extend_from_slice(&fl);
            }
            self.b.t(&g);
            swp_note(rs.len());
            sw_post = rs;
            sw_post.extend(post);
        }
        let mv = |me: &Machine, src: u32, dst: u32| -> GL {
            let mut g = me.m(&cat(&cl, &[(src, true)]), dst);
            g.extend(me.m(&cat(&cl, &[(dst, true)]), src));
            g
        };
        // E3C: the hosted lanes where even11's C rows left them (big_phase's moves of rows 9..3)
        let mut hb = if e3c { vec![x[wv - 4], x[wv - 5], x[wv - 9], x[wv - 10]] } else { hb0.clone() };
        let (mut a0, mut a1, mut a2) = if e3c { (x[wv - 6], x[wv - 7], x[wv - 8]) } else { (w0, w1, w2) };
        // the W4 lane during the C half
        let w4c = w4p;
        if jsc && !e3c {
            r7e_tag("big:d5_Cjswap_in");
            let g = self.jswap(t, &prs, &hb, [a0, a1, a2], true, full16, w4c);
            pg_add(8, &g);
            self.b.t(&g);
        }
        for k in (0..kk).rev() {
            r7e_keys(&[format!("T{:03}", t), format!("K{:02}", k)]);
            r7e_tag("big:e_Cmv");
            let act: Vec<(i32, i32, i32, i32)> = prs.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() || e3c {
                continue;
            }
            let ku = k as usize;
            if k == 9 {
                let g = mv(self, hb[3], x[wv - 10]);
                self.b.t(&g);
                hb[3] = x[wv - 10];
            }
            if k == 8 {
                let g = mv(self, hb[2], x[wv - 9]);
                self.b.t(&g);
                hb[2] = x[wv - 9];
            }
            if k == 7 {
                let g = mv(self, a2, x[wv - 8]);
                self.b.t(&g);
                a2 = x[wv - 8];
            }
            if k == 6 {
                let g = mv(self, a1, x[wv - 7]);
                self.b.t(&g);
                a1 = x[wv - 7];
            }
            if k == 5 {
                let g = mv(self, a0, x[wv - 6]);
                self.b.t(&g);
                a0 = x[wv - 6];
            }
            if k == 4 {
                let g = mv(self, hb[1], x[wv - 5]);
                self.b.t(&g);
                hb[1] = x[wv - 5];
            }
            if k == 3 {
                let g = mv(self, hb[0], x[wv - 4]);
                self.b.t(&g);
                hb[0] = x[wv - 4];
            }
            let mut cv_c = inc_ctl(&hb, &[(a0, true)], &self.dirty);
            cv_c.extend(inc_ctl(&hb, &[(a1, true)], &self.dirty));
            cv_c.extend(inc_ctl(&hb[1..], &[(a2, true)], &self.dirty));
            if full16 {
                cv_c.extend(inc_ctl(&hb[2..], &[(w4c, true)], &self.dirty));
            }
            // W4HOST v2: W4 sits on W1 for the whole phase (no move), so the slots 0 mod 16 hoist too, with cv_c's W4 term
            let cvhc = cvhc_on() && jsc;
            let hzc = cvhc && k <= kh;
            if cvhc && k == kh {
                let mut g = inc_ctl(&hb, &cat(&cl, &[(a0, true)]), &self.dirty);
                g.extend(inc_ctl(&hb, &cat(&cl, &[(a1, true)]), &self.dirty));
                g.extend(inc_ctl(&hb[1..], &cat(&cl, &[(a2, true)]), &self.dirty));
                if full16 {
                    g.extend(inc_ctl(&hb[2..], &cat(&cl, &[(w4c, true)]), &self.dirty));
                }
                self.b.t(&g);
            }
            let mut starts: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
            for &(_e, _w, _u, v) in &act {
                starts.entry(W as i32 - (t / 2 + v) - 1 + k - pdc).or_default().insert(v);
            }
            let ahi = *starts.keys().next_back().unwrap();
            let wires: Vec<usize> = (ku..=(ahi as usize)).rev().collect();
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
            let nn = tv.len();
            let top = if k >= 1 { y[ku - 1] } else { NONE };
            let cc = if k >= 2 {
                x[wv - ku]
            } else if k == 1 {
                x[wv - 2]
            } else {
                x[wv - 1]
            };
            let mask = if k >= 3 { y1 } else { x[wv - 3] };
            let actv = exact(k, &[hb[0], hb[1], hb[2], hb[3], a0]);
            let allv: BTreeSet<i32> = act.iter().map(|p| p.3).collect();
            let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for (&a, vs) in &starts {
                let rest: BTreeSet<i32> = allv.difference(vs).cloned().collect();
                tg.insert((ahi - a) as usize, hterm(vs, &rest, &hb));
            }
            assert!(!hzc || actv == vec![cl.clone()], "CVHC: act cube of C row {k} reads the hosted lanes");
            let g = self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, mask, &tg, &actv, None, if hzc { None } else { Some(&cv_c) });
            let mut hh: GL = vec![];
            if k >= 1 {
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(x[wv - ku], true)]), d));
                }
                hh.push(gc(d, x[wv - ku]));
                if k == 1 {
                    let xt = x[wv - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(y0, true)]), xt));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(xt, true)]), y0));
                    }
                }
                hh.push(gc(d, top));
            } else {
                let host = x[wv - 1];
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(host, true)]), d));
                }
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(d, true)]), host));
                }
            }
            r7e_tag("big:e_Chh");
            self.b.t(&hh);
            if pgo && !jsc {
                let mut gp: GL = vec![];
                for b in 0..dd {
                    let (sq, tq) = (sc[b], vb[(b + 3 * dd - ku) % dd]);
                    gp.extend_from_slice(&[gx(tq), gc(cc, sq), gc(cc, tq), gt(sq, tq, cc)]);
                }
                pg_add(1, &gp);
                let r7e_n1 = gp.len();
                gp.extend_from_slice(&g);
                let r7e_n2 = gp.len();
                let mut dn: GL = vec![];
                for b in (0..dd).rev() {
                    let (sq, tq) = (sc[b], vb[(b + 3 * dd - ku) % dd]);
                    dn.extend_from_slice(&[gt(sq, tq, cc), gc(cc, tq), gt(d, sq, tq), gc(cc, sq), gx(tq)]);
                }
                pg_add(1, &dn);
                gp.extend(dn);
                let r7e_rg = rev(&gp);
                let (r7e_l1, r7e_l2) = (gp.len() - r7e_n2, gp.len() - r7e_n1);
                r7e_tag("big:e_Ccells");
                self.b.t(&r7e_rg[..r7e_l1]);
                r7e_tag("big:e_Crow");
                self.b.t(&r7e_rg[r7e_l1..r7e_l2]);
                r7e_tag("big:e_Ccells");
                self.b.t(&r7e_rg[r7e_l2..]);
                if k >= 1 {
                    // inverse of the cofactor window's slide after V-style row k - 1 (cases e >= k, one swap per f)
                    r7e_tag("big:e_Cslide");
                    BIG_SITE.store(5, Ordering::Relaxed);
                    let lanes_c: Vec<u32> = vec![hb[0], hb[1], hb[2], hb[3], a0, a1, a2];
                    let mut grp: BTreeMap<i32, Vec<(i32, i32)>> = BTreeMap::new();
                    for &(e, w, _u, v) in prs.iter().filter(|p| p.0 >= k) {
                        grp.entry(t / 2 + v).or_default().push((e, w));
                    }
                    let mut g: GL = cv_c.clone();
                    pg_add(4, &cv_c); pg_add(4, &cv_c);
                    if SLIDE_LAD {
                        let mut gr: Vec<(i32, Vec<Vec<Lit>>, GL)> = vec![];
                        for (f, cs) in &grp {
                            let v = *f - t / 2;
                            let on: Vec<usize> = cs.iter().map(|&(_e, w)| (w << 4) as usize).collect();
                            let off: Vec<usize> = prs.iter().filter(|p| p.3 == v && p.0 < k).map(|p| (p.1 << 4) as usize).collect();
                            let ex = if off.is_empty() { vec![vec![]] } else { hw_cubes(&on, &off, &lanes_c, w4c) };
                            let mut sw: GL = vec![];
                            cswap(d, vb[(3 * dd - ku) % dd], y[W - *f as usize - dd + ku - 1], &mut sw);
                            pg_add(3, &sw);
                            gr.push((v % 16, ex, sw));
                        }
                        g.extend(self.demux(&cl, &hb, &mut gr, d, None));
                        grp.clear();
                    }
                    for (f, cs) in grp {
                        let fl = cflagh(self, &cs, &lanes_c, 2);
                        let mut sw: GL = vec![];
                        cswap(d, vb[(3 * dd - ku) % dd], y[W - f as usize - dd + ku - 1], &mut sw);
                        pg_add(3, &sw); pg_add(4, &fl); pg_add(4, &fl);
                        g.extend_from_slice(&fl);
                        g.extend(sw);
                        g.extend_from_slice(&fl);
                    }
                    g.extend(rev(&cv_c));
                    self.b.t(&g);
                }
            } else {
                r7e_tag("big:e_Crow");
                self.b.t(&rev(&g));
            }
        }
        if cvhc_on() && jsc && !e3c {
            let mut g = inc_ctl(&hb, &cat(&cl, &[(a0, true)]), &self.dirty);
            g.extend(inc_ctl(&hb, &cat(&cl, &[(a1, true)]), &self.dirty));
            g.extend(inc_ctl(&hb[1..], &cat(&cl, &[(a2, true)]), &self.dirty));
            if full16 {
                g.extend(inc_ctl(&hb[2..], &cat(&cl, &[(w4c, true)]), &self.dirty));
            }
            self.b.t(&rev(&g));
        }
        r7e_keys(&[format!("T{:03}", t)]);
        r7e_tag("big:f1_Cwin_out");
        if jsc && !e3c {
            let g = self.jswap(t, &prs, &hb, [a0, a1, a2], true, full16, w4c);
            pg_add(8, &g);
            self.b.t(&g);
            r7e_tag("big:f2_roleswap_sandwich_post");
            { let (a_, k_) = swp_last(); self.t3(&sw_post, a_, k_, ["f2_roleswap_sandwich_post", "f2_sw_K2", "f2_sw_sel"], true); }
        }
        if pgo && !jsc {
            // inverse of the cofactor window-in, then the sandwich's post
            BIG_SITE.store(6, Ordering::Relaxed);
            let lanes_c: Vec<u32> = vec![hb[0], hb[1], hb[2], hb[3], a0, a1, a2];
            let mut g: GL = vec![];
            for &(e, w, u, _v) in &prs {
                let lu = (t / 2 - u) as usize;
                let fl = cflag(self, &[(e, w)], &lanes_c);
                let mut lanes = vb.clone();
                lanes.extend((0..e as usize).map(|i| y[W - lu - 1 - dd - i]));
                let ro = rotate_up(d, &lanes, e as usize);
                pg_add(2, &ro); pg_add(4, &fl); pg_add(4, &fl);
                g.extend_from_slice(&fl);
                g.extend(ro);
                g.extend_from_slice(&fl);
            }
            self.b.t(&g);
            r7e_tag("big:f2_roleswap_sandwich_post");
            { let (a_, k_) = swp_last(); self.t3(&sw_post, a_, k_, ["f2_roleswap_sandwich_post", "f2_sw_K2", "f2_sw_sel"], true); }
        }
        r7e_tag("big:g_marker");
        BIG_SITE.store(0, Ordering::Relaxed);
        // hi -> marker on X[wv-e], largest e first
        let mut g: GL = vec![];
        if l16 {
            // LOOK16 h1: hi = hi' + 5 on the parent's four hi lanes (A + x[wv-10], which r3 has left), so the parent's write-back
            // below runs as is: with hi' its "all hi lanes 0" cube would also match the unwritten classes 10 and 11 (hi' = 0)
            let mut cg = inc_ctl(&hb, &cl, &self.dirty);
            cg.extend(inc_ctl(&hb[2..], &cl, &self.dirty));
            g.extend(cg);
        }
        let n_l16c = g.len();
        for &e in es.iter().rev() {
            let m = e >> 1;
            let mk = x[wv - e as usize];
            let mut li = cl.clone();
            for i in 0..4 {
                li.push((hb[i], (m >> i) & 1 == 1));
            }
            li.push((a0, e & 1 == 1));
            g.extend(self.m(&li, ctl));
            for i in 0..4 {
                if (m >> i) & 1 == 1 {
                    g.push(gc(ctl, hb[i]));
                }
            }
            g.push(gc(ctl, mk));
            let mut li = cl.clone();
            for i in 0..4 {
                if hb[i] != mk {
                    li.push((hb[i], false));
                }
            }
            li.push((mk, true));
            g.extend(self.m(&li, ctl));
        }
        self.tsplit(&g, &[(n_l16c, "big:l16_hi5")]);
        if l16e {
            // LOOK16: E to x[wv-5] (hi'1's lane, 0 now); the late shots' r0..r2 to x[wv-2..wv-4] (the barrel's lanes); an early
            // shot keeps r0..r2 (its release amount 8 - d) on x[wv-6..wv-8] and has 0 on the barrel's lanes
            let e5 = x[wv - 5];
            let mut g = self.m(&cat(&cl, &[(x[wv - 1], true)]), e5);
            g.extend(self.m(&cat(&cl, &[(e5, true)]), x[wv - 1]));
            for (src, dst) in [(a0, x[wv - 2]), (a1, x[wv - 3]), (a2, x[wv - 4])] {
                g.extend(self.m(&cat(&cl, &[(e5, false), (src, true)]), dst));
                g.extend(self.m(&cat(&cl, &[(e5, false), (dst, true)]), src));
            }
            self.tsub("big:l16_move", &g);
        } else {
        let g = mv(self, a0, x[wv - 2]);
        self.b.t(&g);
        let g = mv(self, a1, x[wv - 3]);
        self.b.t(&g);
        let g = mv(self, a2, x[wv - 4]);
        self.b.t(&g);
        }
        // its own post
        r7e_tag("big:h1_post_rot_swap");
        let g = self.m(&cat(&cl, &[(y[0], false)]), ctl);
        self.b.t(&g);
        let g = rotate_up(ctl, &y, wv - 1);
        self.b.t(&g);
        let g = self.m(&cl, ctl);
        self.b.t(&g);
        let mut g = vec![];
        for w in 1..wv {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        if pgo {
            r7e_tag("big:h2_post_page");
            if PK3_PCONV_BIG { PK3_IN_BIG_POST.with(|c| c.set(true)); }
            let g = self.post_page(ctl);
            if PK3_PCONV_BIG { PK3_IN_BIG_POST.with(|c| c.set(false)); }
            pg_add(7, &g);
            self.b.t(&g);
        }
        r7e_tag("big:i_wait_rot");
        let xt = x[wv - 1];
        self.b.t(&[gc(ctl, y[wv - 1])]);
        let g = self.m(&cl, ctl);
        self.b.t(&g);
        let fl = y[wv - 1];
        let aa: Vec<Lit> = cat(&[(fl, true)], &self.hc(3));
        for &(idx, rot) in &[(wv - 4, 4usize), (wv - 3, 2), (wv - 2, 1)] {
            let mut g = self.m(&cat(&aa, &[(y[idx], true)]), ctl);
            g.extend(self.m(&cat(&aa, &[(ctl, true)]), y[idx]));
            self.b.t(&g);
            let g = rotate_up(ctl, &y[0..=idx], rot);
            self.b.t(&g);
            let mut g: GL = vec![];
            if rot == 4 {
                g.extend(self.m(&cat(&aa, &[(y[0], false)]), ctl));
            } else if rot == 2 {
                g.extend(self.m(&cat(&aa, &[(y[0], false), (y[2], true)]), ctl));
                g.extend(self.m(&cat(&aa, &[(y[0], false), (y[2], false), (y[4], false)]), ctl));
            } else {
                for &p_ in &[1usize, 3, 5, 7] {
                    let mut l = aa.clone();
                    for i in 0..p_ {
                        l.push((y[i], false));
                    }
                    l.push((y[p_], true));
                    g.extend(self.m(&l, ctl));
                }
            }
            self.b.t(&g);
        }
        // L-C: the 4th wait bit: rotate by 8 under W4 (last: the shots rotated by w & 7 have their first one at y[w & 7]),
        // W4 moved into ctl and back out by the 8 zeros a rotated shot has at the bottom
        if full16 && prs.iter().any(|p_| p_.1 >= 8) {
            let mut g = self.m(&cat(&aa, &[(w4c, true)]), ctl);
            g.extend(self.m(&cat(&aa, &[(ctl, true)]), w4c));
            self.b.t(&g);
            let g = rotate_up(ctl, &y[0..=wv - 2], 8);
            self.b.t(&g);
            let mut l = aa.clone();
            for i in 0..8 { l.push((y[i], false)); }
            let g = self.m(&l, ctl);
            self.b.t(&g);
        }
        if l16w8 {
            // LOOK16: the late shots' r3 (on W1) turns them up by 8; an early shot (W1 = 1 too) has its flag on y[wv-5], which
            // every late shot with r3 = 1 has 0 here (at least 10 zero wires below the top after the turn by r & 7)
            let w1 = self.w1;
            let mut g = self.m(&cat(&aa, &[(w1, true), (y[wv - 5], false)]), ctl);
            g.extend(self.m(&cat(&aa, &[(ctl, true)]), w1));
            self.tsub("big:l16_turn8", &g);
            let g = rotate_up(ctl, &y[0..=wv - 2], 8);
            self.tsub("big:l16_turn8", &g);
            let mut l = aa.clone();
            for i in 0..8 { l.push((y[i], false)); }
            let g = self.m(&l, ctl);
            self.tsub("big:l16_turn8", &g);
        }
        r7e_tag("big:j_end_rot1");
        // u=2, g=1 ends with E'=-1: no marker, code 01
        // L-C: at a slot 8 mod 16 the long waiters (code 10, yt = 1) are still here and are not acting; they all have W4 = 1
        // there and the actors W4 = 0 (cleared above), so the terms below that are not gated by code 11 also read W4 = 0
        // W4HOST: the long waiters (fl, code 01, y[8] = W4 = 1) are memoed on F here, where every acted shot still has code 11;
        // the same gate clears F after the act flags are erased (acted shots then have fl = 0)
        let memo: GL = if band8 && W4HOST { self.m(&cat(&cat(&[(fl, true)], &self.hc(1)), &[(y[8], true)]), self.pg[4 * PAGE_D]) } else { vec![] };
        self.b.t(&memo);
        let nw4: Vec<Lit> = if band8 { vec![(if W4HOST { self.pg[4 * PAGE_D] } else { self.w4 }, false)] } else { vec![] };
        let fc1 = cat(&cat(&[(fl, true), (xt, false)], &self.hc(1)), &nw4);
        let mut g = self.m(&cat(&aa, &[(xt, false), (y[wv - 4], true)]), ctl);
        g.push(gc(ctl, h1));
        g.extend(self.m(&fc1, ctl));
        self.b.t(&g);
        let g = self.m(&fc1, y[wv - 4]);
        self.b.t(&g);
        let ab: Vec<Lit> = cat(&[(fl, true), (h0, true)], &nw4);
        let win: Vec<u32> = y[..wv - 1].to_vec();
        let g1 = self.m(&cat(&ab, &[(xt, false)]), ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        let g1 = self.m(&ab, ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        if l16e {
            // LOOK16: the end rotations turned the early shots up by k = 2 - xt: flag on y[wv-5+k], release bits on
            // y[wv-6+k..wv-8+k]; move them to the freeze layout (flag y[wv-2], release r0..r2 on y[wv-3..wv-5])
            let mut g: GL = vec![];
            let ce: Vec<Lit> = vec![(fl, true), (h0, true), (h1, true), (self.w1, true)];
            for (xv, k) in [(true, 1usize), (false, 2usize)] {
                let c = cat(&ce, &[(xt, xv)]);
                for i in 0..4usize {
                    let (src, dst) = (y[wv - 5 + k - i], y[wv - 2 - i]);
                    g.extend(self.m(&cat(&c, &[(src, true)]), dst));
                    g.extend(self.m(&cat(&c, &[(dst, true)]), src));
                }
            }
            self.tsub("big:l16_place", &g);
        }
        // erase the act flag
        r7e_tag("big:k_erase");
        let mut g: GL = vec![];
        if l16e {
            // LOOK16: an early shot acted with no wait (bottom pattern of w = 0), freeze bits on top, W1 = 1
            for gg in 0..2usize {
                let gq = 1 + gg;
                let mut l: Vec<Lit> = vec![(xt, gg == 0)];
                for i in 0..gq { l.push((y[i], false)); }
                l.push((y[gq], true));
                l.extend(self.hc(3));
                l.push((self.w1, true));
                g.extend(self.m(&l, fl));
            }
        }
        let n_l16k = g.len();
        for gg in 0..2usize {
            // AKB_KERASE_HOLD: the group's common literals on ctl (x0) around its code-11 cubes
            let kh = AKB_KERASE_HOLD && l16;
            let (mut held, mut extra): (GL, GL) = (vec![], vec![]);
            for w in 0..(if full16 || l16 { 16 } else { 8 }) {
                let sub: Vec<&(i32, i32, i32, i32)> = prs.iter().filter(|p| p.1 == w).collect();
                if sub.is_empty() {
                    continue;
                }
                let gq = 1 + gg + w as usize;
                let mut li: Vec<Lit> = vec![(xt, gg == 0)];
                for i in 0..gq {
                    li.push((y[i], false));
                }
                li.push((y[gq], true));
                if sub.iter().any(|p| !(gg == 1 && p.2 == 2)) {
                    let mut l = cat(&li, &self.hc(3));
                    // an acted shot of class e has zeros from y[wv-2] down to y[wv-(e-1)] before its rotation by w: the
                    // top literals cover what is left above it (e_min = 10 for w < 8, as before; L-C long cases: their e_min)
                    let emin = if w >= 8 { sub.iter().map(|p| p.0).min().unwrap() as usize } else { 10 };
                    for j in (wv + gq + 1 - emin)..(wv - 1) {
                        l.push((y[j], false));
                    }
                    if kh {
                        let r_: Vec<Lit> = std::iter::once((ctl, true)).chain(l.iter().cloned().filter(|x_| x_.0 != xt && x_.0 != y[0] && x_.0 != h0 && x_.0 != h1)).collect();
                        held.extend(self.m(&r_, fl));
                    } else {
                        g.extend(self.m(&l, fl));
                    }
                }
                if sub.iter().any(|p| gg == 1 && p.2 == 2) {
                    let g2 = self.m(&cat(&cat(&li, &self.hc(1)), &nw4), fl);
                    if kh { extra.extend(g2); } else { g.extend(g2); }
                }
            }
            if kh && !held.is_empty() {
                let hc_ = self.m(&cat(&cat(&[(xt, gg == 0)], &self.hc(3)), &[(y[0], false)]), ctl);
                g.extend_from_slice(&hc_);
                g.extend(held);
                g.extend(hc_);
            }
            g.extend(extra);
        }
        self.tsplit(&g, &[(n_l16k, "big:l16_kerase")]);
        self.b.t(&memo);
        if l16e {
            // LOOK16: W1 back to 0 on the frozen shots (not at the top, code 11, flag on y[wv-2]: no natural shot, M5 kill 3)
            let g = self.m(&[(y[wv - 1], false), (y[wv - 2], true), (h0, true), (h1, true)], self.w1);
            self.tsub("big:l16_w1", &g);
        }
    }
    fn pi10_po_hold(&self, t: i32, tau: u32) -> GL {
        assert!(PAGE_G && PAGE_N && PAGE_D == 11 && (ECAP == 17 || ECAP == 18));
        let wv = self.wr;
        let l = ((t - 1).div_euclid(2)) as usize;
        let x = &self.x;
        let y = &self.y;
        let (h0, h1) = (self.e[0], self.e[1]);
        let ff = self.pg[4 * PAGE_D];
        let mut yy = y[1..].to_vec();
        yy.push(y[0]);
        let hs = if wv < W { PAGE_D } else { 0 };
        let mut li = vec![(x[wv - 1], true), (y[1], false), (y[2], true)];
        li.extend(self.hc(0));
        let tg = self.m(&li, tau);
        let mut hi: GL = vec![];
        let all: Vec<usize> = ((wv - l + hs)..(wv - 1)).collect();
        let at = all.len().saturating_sub(PIW - 1);
        for &w in &all[at..] {
            hi.extend_from_slice(&[gc(ff, x[w]), gc(ff, yy[w]), gt(x[w], yy[w], ff)]);
        }
        let all: Vec<usize> = (2..(wv - l + hs)).rev().collect();
        let at = all.len().saturating_sub(PIW);
        let idx = &all[at..];
        let mut fw: GL = idx.iter().map(|&w| gx(x[w])).collect();
        for &w in idx {
            fw.extend_from_slice(&[gc(h1, x[w]), gc(h1, yy[w]), gt(x[w], yy[w], h1)]);
        }
        let mut mid = fw.clone();
        mid.extend_from_slice(&[gc(h1, y[1]), gc(x[1], y[1]), gc(yy[1], y[1])]);
        mid.extend(rev(&fw));
        let mut lo: GL = idx.iter().map(|&w| gx(x[w - 1])).collect();
        for &w in idx {
            lo.extend_from_slice(&[gc(h1, yy[w]), gc(h1, x[w - 1]), gt(yy[w], x[w - 1], h1)]);
        }
        let mut g = tg.clone();
        g.extend_from_slice(&hi);
        g.extend_from_slice(&mid);
        g.extend_from_slice(&lo);
        g.extend(self.m(&[(tau, true), (ff, false), (y[1], true), (h1, true)], y[0]));
        g.extend(rev(&lo));
        g.extend(rev(&mid));
        g.extend(rev(&hi));
        g.extend(tg);
        g
    }
    fn pi10(&self, t: i32, cc: u32, f1: u32, f2: u32, f3: u32) -> (GL, GL) {
        let wv = self.wr;
        let l = ((t - 1).div_euclid(2)) as usize;
        let x = &self.x;
        let mut y: Vec<u32> = self.y[1..].to_vec();
        y.push(self.y[0]);
        let last = |v: Vec<usize>| -> Vec<usize> {
            let k = v.len().saturating_sub(PIW);
            v[k..].to_vec()
        };
        let mut g = vec![];
        // the top lane of this frame is a known zero (it holds the act bit): only its carry-out matters
        // narrowed rings (PAGE_N): for the tau shots the X and y' holes sit at native lanes [W-l-D, W-l+D) (bX = W - l),
        // at the carry-in end of all three chains. Drop them exactly (op-layout's DROP model, NARROW.md s3 L3 / s6): the
        // top chain starts at narrowed lane wv - l + D, the bottom chains (C lanes, native indices) end at W - l - D.
        let hs = if wv < W { PAGE_D } else { 0 };
        let idx = {
            let v: Vec<usize> = ((wv - l + hs)..(wv - 1)).collect();
            let k = v.len().saturating_sub(PIW - 1);
            v[k..].to_vec()
        };
        let mut fw = vec![];
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.push(gt(cc, x[wv - 1], f1));
        g.extend(rev(&fw));
        let idx = last((2..(wv - l + hs)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.extend_from_slice(&[gc(cc, f2), gc(x[1], f2), gc(y[1], f2)]);
        g.extend(rev(&fw));
        let idx = last((2..(wv - l + hs)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w - 1])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, y[w]), gc(cc, x[w - 1]), gt(y[w], x[w - 1], cc)]);
        }
        let mut h = fw.clone();
        h.push(gt(cc, y[1], f3));
        h.extend(rev(&fw));
        (g, h)
    }
}

/// F on virtual lanes: 0..255 x, 256..511 borrowed passenger, 512.. the rest.
struct FCirc {
    gates: Vec<G>,
    next: u32,
    y0: u32,
    y1: u32,
    par: u32,
    xtop: u32,
    ar: Vec<u32>,
    last: GL,
    /// ob-hmr: per gate of `gates`, 0 plain, 1 AND compute, 2 AND measured uncompute (empty when HMR_AND is off)
    role: Vec<u8>,
    /// R765_PROF: section of each gate of `gates` (empty when off)
    tags: Vec<u16>,
    /// AKEND MBU: the forward measured-erase blocks in `gates`, ascending and disjoint (empty = off)
    mbu: Vec<MbuBlk>,
}
fn f_circuit() -> FCirc {
    IN_F.store(true, Ordering::Relaxed);
    let mut b = B { free: vec![], next: 512, gates: Vec::with_capacity(48_000_000) };
    for _ in 0..ZB {
        b.alloc();
    }
    let xl: Vec<u32> = (0..256).collect();
    let pas: Vec<u32> = (256..512).collect();
    let y0 = b.alloc();
    let par = xl[N - 1];
    let y1 = b.alloc();
    let mut y = vec![y0, y1];
    y.extend_from_slice(&xl[..N - 1]);
    let x: Vec<u32> = (0..W).map(|_| b.alloc()).collect();
    let e: Vec<u32> = (0..EB).map(|_| b.alloc()).collect();
    let mut dirty = pas.clone();
    dirty.extend_from_slice(&x);
    dirty.extend_from_slice(&y);
    let mut mc = Machine { b, dirty, pas, x, y, e, par, pg: vec![], wr: W, freed: vec![], w4: NONE, w1: NONE, cv_t2: vec![], cv_freed: vec![], cv_x16: vec![], cv_y16: vec![], cv_pg16: vec![], e3t: false };
    mc.page_alloc();
    gl_loader::splice(gl_loader::At::FBegin, &mut mc.b);
    let g_start = mc.b.gates.len();
    let y_init = mc.y.clone();
    mc.init();
    let (mut y_tail, mut g_tail) = (vec![], 0usize);
    let mut asm_a = 0usize;
    let (mut tab765, mut g765): (Vec<u32>, usize) = (vec![], 0usize);
    for t in (3..=(2 * N as i32 - 1)).rev() {
        if CONV && t == CUT_T - 1 {
            mc.conv_back(CUT_T - 1);
        }
        if (TAIL765 > 0 || TAIL_SWAP765) && t == CUT_T - 1 {
            tab765 = mc.phys765(mc.b.next);
            g765 = mc.b.gates.len();
        }
        if t == gl_loader::TAIL_CUT {
            // the cut's format switch (PAGE_G: page_out at 63, PAGE_N: rings re-widened) belongs to the frame, not to
            // the tail region a Tail splice replaces: run it first, then take the tail's labels and gate index.
            gl_loader::splice(gl_loader::At::BeforeTick(t), &mut mc.b);
            let g_pre = mc.b.gates.len();
            if ASM_DUMP {
                let l = |v: &[u32]| v.iter().map(|q| q.to_string()).collect::<Vec<_>>().join(",");
                eprintln!("ASMDUMP 79 y[{}] {}", mc.y.len(), l(&mc.y));
                eprintln!("ASMDUMP 79 x[{}] {}", mc.x.len(), l(&mc.x));
                let mut used: Vec<u32> = mc.b.gates[asm_a..g_pre].iter().flat_map(|g| [g.0, g.1, g.2]).filter(|&q| q != NONE && q < MAC).collect();
                let nmac = mc.b.gates[asm_a..g_pre].iter().filter(|g| g.0 == MAC).count();
                used.sort(); used.dedup();
                eprintln!("ASMDUMP used between cuts: {} labels (gates {}, MAC macros {} not expanded here) {}", used.len(), g_pre - asm_a, nmac, l(&used));
                eprintln!("ASMDUMP b.next {}", mc.b.next);
            }
            mc.cut(t);
            y_tail = mc.y.clone();
            g_tail = if ASM_TAIL_UNPACK && gl_loader::has(gl_loader::At::Tail) { g_pre } else { mc.b.gates.len() };
            mc.slot(t);
            continue;
        }
        if t == gl_loader::START_CUT - 1 {
            // boundary 447: the native init + ticks 511..448 have run (their software state, e.g. the ring-Y relabels,
            // is kept); with a Start splice their gates are replaced by the module's (frame input -> boundary 447).
            let native = &mc.b.gates[g_start..];
            let ccx = native.iter().filter(|g| g.2 != NONE).count();
            eprintln!("gl_loader: native start region (init + ticks 511..{}): {} gates, {} CCX (pre-MAC)", gl_loader::START_CUT, native.len(), ccx);
            if gl_loader::SPLICE_START765 {
                assert!(ASM_START_PAGED && PAGE_G && PAGE_N && PAGE_DI == 16 && CUT_S == 432, "start765 needs the D16 / 432 paged frame");
                mc.b.gates.truncate(g_start);
                sec_trunc(g_start);
                r7e_tag("start_list");
                start765(&mut mc);
            } else if gl_loader::has(gl_loader::At::Start) {
                mc.b.gates.truncate(g_start);
                gl_loader::splice(gl_loader::At::Start, &mut mc.b);
                // the module writes ring Y's logical lane i on the INITIAL label y[i] (trace2048 is in logical order,
                // and the native slots relabel y one wire per slot): continue the frame on those labels.
                mc.y = y_init.clone();
            }
        }
        gl_loader::splice(gl_loader::At::BeforeTick(t), &mut mc.b);
        if ASM_DUMP && t == CUT_S - 1 {
            mc.cut(t);
            asm_a = mc.b.gates.len();
            let l = |v: &[u32]| v.iter().map(|q| q.to_string()).collect::<Vec<_>>().join(",");
            eprintln!("ASMDUMP 431 y[{}] {}", mc.y.len(), l(&mc.y));
            eprintln!("ASMDUMP 431 x[{}] {}", mc.x.len(), l(&mc.x));
            eprintln!("ASMDUMP 431 pg[{}] {}", mc.pg.len(), l(&mc.pg));
            eprintln!("ASMDUMP 431 e {} par {} w4 {} freed[{}] {}", l(&mc.e), mc.par, mc.w4, mc.freed.len(), l(&mc.freed));
            mc.slot(t);
            continue;
        }
        mc.tick(t);
    }
    {
        let native = &mc.b.gates[g_tail..];
        let ccx = native.iter().filter(|g| g.2 != NONE).count();
        eprintln!("gl_loader: native tail region (ticks {}..3): {} gates, {} CCX (pre-MAC)", gl_loader::TAIL_CUT, native.len(), ccx);
        if gl_loader::has(gl_loader::At::Tail) {
            // ring-Y lanes of the list follow the initial labels y_init (logical order); the frame holds y_tail at tick
            // TAIL_CUT: map y_init[i] -> y_tail[i], and continue (exit, FCirc fields) on y_tail.
            mc.b.gates.truncate(g_tail);
            let pos: HashMap<u32, usize> = y_init.iter().enumerate().map(|(i, &q)| (q, i)).collect();
            let yt = y_tail.clone();
            gl_loader::splice_mapped(gl_loader::At::Tail, &mut mc.b, &|q| pos.get(&q).map(|&i| yt[i]).unwrap_or(q));
            mc.y = y_tail.clone();
        }
    }
    let mut keep_last = true;
    if TAIL_SWAP765 {
        assert!(TAIL765 == 0 && gl_loader::SPLICE_START765 && !START765_SWAP, "TAIL_SWAP765: native tail after a re-pointed start765");
        let y773: Vec<usize> = [512usize, 513].into_iter().chain(0..255).collect();
        let tgt: Vec<u32> = y773.iter().map(|&p| tab765[p]).collect();
        assert_eq!(mc.y.len(), W);
        let xs: std::collections::HashSet<u32> = mc.x.iter().copied().collect();
        let src: std::collections::HashSet<u32> = mc.y.iter().copied().collect();
        let dst: std::collections::HashSet<u32> = tgt.iter().copied().collect();
        assert!(src.iter().chain(dst.iter()).all(|l| !xs.contains(l)) && !src.contains(&mc.par) && !dst.contains(&mc.par), "tail swap: ring X / par involved");
        let mut dest: HashMap<u32, u32> = mc.y.iter().copied().zip(tgt.iter().copied()).collect();
        let mut a: Vec<u32> = dst.iter().copied().filter(|l| !src.contains(l)).collect();
        let mut bz: Vec<u32> = src.iter().copied().filter(|l| !dst.contains(l)).collect();
        a.sort();
        bz.sort();
        for (s0, d0) in a.into_iter().zip(bz) { dest.insert(s0, d0); }
        let mut keys: Vec<u32> = dest.keys().copied().collect();
        keys.sort();
        let mut done = std::collections::HashSet::new();
        let mut g: GL = vec![];
        for &s0 in &keys {
            if done.contains(&s0) || dest[&s0] == s0 { done.insert(s0); continue; }
            let mut c = vec![s0];
            let mut q = dest[&s0];
            while q != s0 { c.push(q); q = dest[&q]; }
            for &l in &c { done.insert(l); }
            for &sj in &c[1..] { g.extend([G(s0, sj, NONE), G(sj, s0, NONE), G(s0, sj, NONE)]); }
        }
        eprintln!("tail swap765: ring Y moved onto the Y773 labels: {} CX", g.len());
        mc.b.t(&g);
        mc.y = tgt;
    }
    if TAIL765 > 0 {
        let inv: HashMap<u32, u32> = tab765.iter().enumerate().map(|(p, &q)| (q, p as u32)).collect();
        let lay = format!("{}.lay", if TAIL765 == 1 { TAIL765_DUMP } else { TAIL765_LIST });
        if TAIL765 == 1 {
            assert!(!MAC_ON, "TAIL765 = 1 dumps plain gates: macro pass off");
            let ph = |q: u32| -> u32 { if q == NONE { NONE } else { *inv.get(&q).expect("tail765 dump: lane outside the table") } };
            let reg: GL = mc.b.gates[g765..].iter().map(|g| G(ph(g.0), ph(g.1), ph(g.2))).collect();
            let top = reg.iter().flat_map(|g| [g.0, g.1, g.2]).filter(|&q| q != NONE).max().unwrap_or(0) + 1;
            std::fs::write(TAIL765_DUMP, gl_loader::encode(&reg, top)).expect("tail765 dump write");
            let ys: Vec<String> = mc.y.iter().map(|&q| ph(q).to_string()).collect();
            let xs: Vec<String> = mc.x.iter().map(|&q| ph(q).to_string()).collect();
            std::fs::write(&lay, format!("Y {}\nX {}\n", ys.join(" "), xs.join(" "))).expect("tail765 lay write");
            eprintln!("tail765: dumped {} gates, {} CCX, phys lanes {} -> {}", reg.len(), reg.iter().filter(|g| g.2 != NONE).count(), top, TAIL765_DUMP);
        } else {
            let z: Vec<u8> = if TAIL765 == 3 { (if TAIL765_CL { TAIL765C_DATA } else { TAIL765_DATA }).to_vec() } else { std::fs::read(TAIL765_LIST).expect("tail765 list read") };
            if TAIL765 == 3 { assert_eq!(gl_loader::sha3_hex(&z), if TAIL765_CL { TAIL765C_SHA3 } else { TAIL765_SHA3 }, "tail765: registered list sha3"); }
            eprintln!("tail765: list {} sha3 {}", TAIL765_LIST, gl_loader::sha3_hex(&z));
            let f = gl_loader::decode(&z);
            let rl = |p: u32| -> u32 { if p == NONE { NONE } else { tab765[p as usize] } };
            let native = mc.b.gates.len() - g765;
            mc.b.gates.truncate(g765);
            sec_trunc(g765);
            r7e_tag("tail_list");
            let g: GL = f.gates.iter().map(|g| gl_loader::relabel(g, &rl)).collect();
            if (AK_T1 || AK_GAD || AK_M3E) && TAIL765 == 3 && TAIL765_CL {
                // AKEND MBU: the list lands at mc.b.gates[g765..] (truncated above, appended below)
                ak_fix_pins();
                assert_eq!(g.len(), AK_TAIL.0, "AKEND MBU: tail list length");
                assert!(!AK_GAD || AK_M3E, "AKEND: AK_GAD needs AK_M3E (B is dead only with M3E's FIX)");
                if AK_T1 { mbu_register("tail-caf", &g, g765, AK_TAIL.1, mbu_lanes(AK_CAF_MEAS), 189, AK_CAF_FIX, false, vec![], None, &rl); }
                // HMR first: the FIX (A 619..670 -> 620..671) writes lane 671, which is measured
                if AK_GAD { mbu_register("tail-gadget", &g, g765, AK_TAIL.2, mbu_lanes(AK_GAD_MEAS), 144, AK_GAD_FIX, false, (620u32..659).collect(), None, &rl); }
                // TB / TA (tail lanes 567..660); FIX (PAR ^= f(a)) before the HMR; PAR (tail lane 255) for the anchor check
                if AK_M3E { mbu_register("m3e", &g, g765, AK_TAIL.3, (567u32..661).collect(), 94, AK_M3E_FIX, true, vec![], Some(255), &rl); }
            }
            eprintln!("tail765: native region {} gates replaced by the list: {} gates, {} CCX, phys lanes {}", native, g.len(), f.n_ccx, f.n_lanes);
            mc.b.t(&g);
            let txt = if TAIL765 == 3 { TAIL765_LAY.to_string() } else { std::fs::read_to_string(&lay).expect("tail765 lay read") };
            // a 765 tail list leaves ring X zero (SHELL.md s3d): without an X line the X-ring constant clear (fc.last) is dropped
            keep_last = txt.lines().any(|l| l.starts_with("X "));
            for ln in txt.lines() {
                let mut it = ln.split_whitespace();
                let k = it.next().unwrap_or("");
                let v: Vec<u32> = it.map(|w| rl(w.parse().unwrap())).collect();
                if k == "Y" { mc.y = v; } else if k == "X" { mc.x = v; }
            }
        }
    }
    gl_loader::splice(gl_loader::At::FEnd, &mut mc.b);
    IN_F.store(false, Ordering::Relaxed);
    if std::env::var("R7B_FAIL").is_ok() { r7b_fail::run(&mc.b.gates, mc.b.next as usize); std::process::exit(0); }
    if PAGE || PAGE_V || PAGE_C || PAGE_G {
        let c: Vec<u64> = PG_CNT.iter().map(|a| a.load(Ordering::Relaxed)).collect();
        eprintln!("P1 page CCX per pass: gather(test) {} cells {} rotations {} swaps {} flags {} sandwich+remap {} unpage/repage(e=1 even) {} (e=1 odd) {} (big) {} post swap+format {}", c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[8], c[9], c[7]);
        eprintln!("P1 big-phase flags per pass: win-in {} V-slides {} V-win-out {} cw {} C-slides {} C-win-out {}", c[11], c[12], c[13], c[14], c[15], c[16]);
    }
    if SW1_GROUP_K2 || SW1_K2_AND_ROLES || SW2_LADDER_SEM {
        let c: Vec<usize> = SW1_CHK.iter().map(|a| a.load(Ordering::Relaxed)).collect();
        eprintln!("SW1CHK SUMMARY literal eq {} diff {} | roles eq {} diff {} | group inv eq {} diff {} | group packets emitted {} || SW2 certified tables emitted {}",
            c[0], c[1], c[2], c[3], c[4], c[5], c[6], SW2_CNT.load(Ordering::Relaxed));
    }
    if NK_F1_TRIE || NK_F0_BODY || NK_SELECT_LSB {
        let c: Vec<usize> = NK_CNT.iter().map(|a| a.load(Ordering::Relaxed)).collect();
        eprintln!("NKCHK SUMMARY trie groups {} | kept (cubes not disjoint) {} | kept (lane contract) {} || F0 brackets {} kept {} || select CX pairs {}", c[0], c[1], c[2], c[3], c[5], c[4]);
    }
    if DB_F1_SIGN || DB_F0_SIGN {
        let c: Vec<usize> = DB_CNT.iter().map(|a| a.load(Ordering::Relaxed)).collect();
        eprintln!("DBCHK SUMMARY (F1 + F0) blocks with a compensation {} | signed adds {} | F1 j = 0 terms {} | compensation CCX {}", c[0], c[1], c[2], c[3]);
    }
    let pre_tags = if r765_prof() { sec_tags(mc.b.gates.len()) } else { vec![] };
    if MAC_ON { let g = std::mem::take(&mut mc.b.gates); mc.b.gates = mac_finish(g); }
    let mut ftags: Vec<u16> = if r765_prof() {
        if MAC_ON { MAC_SRC.lock().unwrap().iter().map(|&i| pre_tags[i as usize]).collect() } else { pre_tags }
    } else { vec![] };
    let mut last: GL = vec![gx(mc.x[W - 1])];
    for i in 0..N {
        if pbit(i) {
            last.push(gx(mc.x[W - 2 - i]));
        }
    }
    if !keep_last {
        last.clear();
    }
    r7e_print();
    // with start765 re-pointed, the sign ends on the re-pointed par (= y0's label), not on xl[255]
    let par = if gl_loader::SPLICE_START765 && !START765_SWAP { mc.par } else { par };
    let mut fc = FCirc {
        gates: mc.b.gates,
        next: mc.b.next,
        y0,
        y1,
        par,
        xtop: mc.y[W - 1],
        ar: (0..N).map(|i| mc.y[W - 2 - i]).collect(),
        last,
        role: vec![],
        tags: vec![],
        mbu: vec![],
    };
    if ASM765_COMPACT {
        let mut used = vec![false; fc.next as usize];
        for g in fc.gates.iter().chain(fc.last.iter()) {
            for q in [g.0, g.1, g.2] { if q != NONE { used[gl_loader::lane_of(q) as usize] = true; } }
        }
        for q in [fc.y0, fc.y1, fc.par, fc.xtop].into_iter().chain(fc.ar.iter().copied()) { used[q as usize] = true; }
        let mut rn = vec![NONE; fc.next as usize];
        for q in 0..512 { rn[q] = q as u32; }
        let mut nx = 512u32;
        for q in 512..fc.next as usize { if used[q] { rn[q] = nx; nx += 1; } }
        let r = |q: u32| if q == NONE { NONE } else { rn[q as usize] };
        for g in fc.gates.iter_mut().chain(fc.last.iter_mut()) { *g = gl_loader::relabel(g, &r); }
        fc.y0 = r(fc.y0);
        fc.y1 = r(fc.y1);
        fc.par = r(fc.par);
        fc.xtop = r(fc.xtop);
        for q in fc.ar.iter_mut() { *q = r(*q); }
        for p in MBU_PEND.lock().unwrap().iter_mut() {
            for g in p.pat.iter_mut().chain(p.fix.iter_mut()) { *g = gl_loader::relabel(g, &r); }
            for q in p.meas.iter_mut().chain(p.skip.iter_mut()) { *q = r(*q); }
            p.par = p.par.map(r);
        }
        eprintln!("asm765 compaction: labels >= 512 used {} of {} -> fc.next {} (width {})", nx - 512, fc.next - 512, nx, nx);
        fc.next = nx;
    }
    // p10 M3E / MBU: locate every registered block on the uncancelled list (before the AND pre-cancel): the unique exact lane
    // sequence match of the block as spliced (MAC expansion shifts the index from the splice's), with the list's CCX
    let mut blk: Vec<MbuBlk> = vec![];
    {
        let pend = std::mem::take(&mut *MBU_PEND.lock().unwrap());
        let key = |g: &G| (gl_loader::lane_of(g.0), gl_loader::lane_of(g.1), gl_loader::lane_of(g.2));
        for p in pend {
            let n = p.pat.len();
            assert!(n > 0 && fc.gates.len() >= n);
            let k0 = key(&p.pat[0]);
            let hits: Vec<usize> = (0..=fc.gates.len() - n)
                .filter(|&i| key(&fc.gates[i]) == k0 && fc.gates[i..i + n].iter().zip(p.pat.iter()).all(|(x, y)| key(x) == key(y)))
                .collect();
            assert!(hits.len() == 1, "p10 MBU {}: {} exact matches of the block on the uncancelled list (want 1), at {:?}", p.name, hits.len(), &hits[..hits.len().min(8)]);
            let (b0, b1) = (hits[0], hits[0] + n);
            let nccx = fc.gates[b0..b1].iter().filter(|g| g.2 != NONE).count();
            eprintln!("p10 MBU {}: block on the uncancelled list [{b0}, {b1}) (splice index {}, shift {}): {n} gates, {nccx} CCX (list {})",
                      p.name, p.base, b0 as i64 - p.base as i64, p.ccx);
            assert_eq!(nccx, p.ccx, "p10 MBU {}: block CCX differs from the list", p.name);
            if let Some(par) = p.par {
                // M3E cross-check: the exit-pattern anchor (X(PAR) X(PAR) CX(PAR, a0) ..., the last one in the list)
                let isx = |g: &G| g.0 == par && g.1 == NONE && g.2 == NONE;
                let xs: Vec<usize> = fc.gates.iter().enumerate().filter(|(_, g)| isx(g)).map(|(i, _)| i).collect();
                let k = (1..xs.len()).rev().find(|&k| xs[k] == xs[k - 1] + 1 && fc.gates[xs[k] + 1].0 == par && fc.gates[xs[k] + 1].1 != NONE && fc.gates[xs[k] + 1].2 == NONE)
                    .expect("p10 M3E: exit X(PAR) X(PAR) CX(PAR, .) not found");
                assert!(k >= 2);
                assert_eq!((xs[k - 2] + 1, xs[k - 1]), (b0, b1), "p10 M3E: the exit anchor and the exact match disagree");
            }
            blk.push(MbuBlk { name: p.name, b0, b1, meas: p.meas, fix: p.fix, fix_first: p.fix_first, skip: p.skip });
        }
        blk.sort_by_key(|x| x.b0);
        for w in blk.windows(2) { assert!(w[0].b1 <= w[1].b0, "p10 MBU: blocks {} and {} overlap", w[0].name, w[1].name); }
        // skip lanes of a block apply to the blocks after it in walk order
        let mut off: std::collections::HashSet<u32> = std::collections::HashSet::new();
        for x in blk.iter_mut() {
            let n0 = x.meas.len();
            x.meas.retain(|q| !off.contains(q));
            if x.meas.len() != n0 { eprintln!("p10 MBU {}: {} of {} measured lanes skipped (left un-created by an earlier block)", x.name, n0 - x.meas.len(), n0); }
            off.extend(x.skip.iter().copied());
        }
    }
    if hmr_and() {
        assert!(MAC_ON, "ob-hmr: the AND positions come from mac_finish");
        let idx = std::mem::take(&mut *AND_IDX.lock().unwrap());
        let mut fl = vec![false; fc.gates.len()];
        for &i in &idx { assert!(fc.gates[i].2 != NONE && !fl[i]); fl[i] = true; }
        let ccx0 = fc.gates.iter().filter(|g| g.2 != NONE).count();
        let (g2, f2, canc, mixed) = if !blk.is_empty() {
            // pre-cancel with a barrier at every block edge: no pair may straddle one (= segment-local pre-cancel)
            let n = fc.gates.len();
            let mut bar = vec![false; n];
            for x in &blk { for e in [x.b0, x.b1] { if e < n { bar[e] = true; } } }
            let (g2, f2, canc, mixed, pos) = hmr_precancel(&fc.gates, &fl, &bar);
            let bi: Vec<usize> = (0..n).filter(|&i| bar[i]).collect();
            let map = |e: usize| if e >= n { g2.len() } else { pos[bi.binary_search(&e).unwrap()] };
            for x in blk.iter_mut() { x.b0 = map(x.b0); x.b1 = map(x.b1); assert!(x.b0 < x.b1, "p10 MBU {}: empty block after the pre-cancel", x.name); }
            (g2, f2, canc, mixed)
        } else { let r = hmr_precancel(&fc.gates, &fl, &[]); (r.0, r.1, r.2, r.3) };
        let role = hmr_roles(&g2, &f2);
        let nu = role.iter().filter(|&&r| r == 2).count();
        let ccx1 = g2.iter().filter(|g| g.2 != NONE).count();
        eprintln!("ob-hmr: cc_core AND gates {} ({} calls), pre-cancel pairs {} (mixed kept {}), F list CCX {} -> {}, measured uncomputes {} (CCX after {}), neg {}",
                  idx.len(), idx.len() / 2, canc, mixed, ccx0, ccx1, nu, ccx1 - nu, hmr_negctl());
        fc.gates = g2;
        fc.role = role;
        if r765_prof() {
            let al = PRE_ALIVE.lock().unwrap();
            ftags = ftags.iter().zip(al.iter()).filter(|(_, &a)| a).map(|(&t, _)| t).collect();
        }
    }
    if r765_prof() {
        assert_eq!(ftags.len(), fc.gates.len(), "profile tags");
        let names = SECNAMES.lock().unwrap().clone();
        for (i, n) in names.iter().enumerate() { eprintln!("R765PROF TAGNAME {i} {n}"); }
        let mut c: BTreeMap<u16, (u64, u64)> = BTreeMap::new();
        for (g, &tg) in fc.gates.iter().zip(ftags.iter()) { let e = c.entry(tg).or_default(); e.0 += 1; if g.2 != NONE { e.1 += 1; } }
        for (tg, (n, ccx)) in c { eprintln!("R765PROF FLIST tag {tg} {} gates {n} ccx {ccx}", names.get(tg as usize).map(|s| s.as_str()).unwrap_or("?")); }
        fc.tags = ftags;
    }
    for x in blk.iter() {
        let (b0, b1) = (x.b0, x.b1);
        let nccx = fc.gates[b0..b1].iter().filter(|g| g.2 != NONE).count();
        eprintln!("p10 MBU {}: walk block [{b0}, {b1}) of {} ({} gates after the segment-local pre-cancel): {nccx} CCX, {} measured labels, FIX {} gates ({})",
                  x.name, fc.gates.len(), b1 - b0, x.meas.len(), x.fix.len(), if x.fix_first { "before the HMR" } else { "after the HMR" });
        assert!(fc.role.is_empty() || fc.role[b0..b1].iter().all(|&r| r == 0 || r >= 3), "p10 MBU {}: cc_core roles inside the block", x.name);
    }
    assert!(blk.is_empty() || (!r765_prof() && hmr_and()), "AKEND MBU: needs ob-hmr, not with the profile (barrier pre-cancel and walk tags)");
    fc.mbu = blk;
    if AK_PCONV {
        let c: Vec<usize> = AK_CONV_CNT.iter().map(|a| a.load(Ordering::Relaxed)).collect();
        eprintln!("AKCONV SUMMARY closes converted {} | post_pages role swap only {} | post_pages full {} | closes plain {} | pending at end {}",
                  c[0], c[1], c[2], c[3], CONV_PEND.with(|p| p.get()));
        assert!(c[0] == c[1] && c[0] > 0 && !CONV_PEND.with(|p| p.get()), "AK_PCONV: closes and skipped posts do not pair");
    }
    if PK3_PCONV_BIG {
        let (c0, c1) = (PK3_PB_CNT[0].load(Ordering::Relaxed), PK3_PB_CNT[1].load(Ordering::Relaxed));
        eprintln!("PK3 PCONV_BIG SUMMARY family closes converted {} | big posts role swap only {} | pending at end {}",
                  c0, c1, CONV_PEND_BIG.with(|p| p.get()));
        assert!(c0 == c1 && c0 > 0 && !CONV_PEND_BIG.with(|p| p.get()), "PK3_PCONV_BIG: family closes and skipped big posts do not pair");
    }
    if PK3_SW3B || PK3_L3BS {
        eprintln!("PK3 SUMMARY big rows with the shared down cell {} | big V rows cut by L3B-S {}",
                  PK3_CNT[0].load(Ordering::Relaxed), PK3_CNT[1].load(Ordering::Relaxed));
    }
    fc
}

/// op-p5b (SPLICE765.md): replay a start list written on MAP765_v2 PHYSICAL lanes (x0 on WALK508 -> the paged D16 frame at label 1431)
/// in place of the native start region, then re-point the frame's software labels at the list's output layout. Table phys -> label:
/// the lanes holding F's input keep their input labels (x0 bit i on WALK508[i] -> label i, PAS -> pas), ZB (763) -> ZB_LANE, every
/// other (clean) lane -> a frame label that is clean at F's input (its own role label where that is free). After the list the ring /
/// page / code / parity roles are read off the table; the ring tops (freed by page_in's narrowing) and T2 get labels outside the
/// table (clean, unused by the list). page_in(431) then emits no gates (ASM_START_PAGED) but narrows the rings as usual.
fn start765(mc: &mut Machine) {
    const NP: usize = 765;
    let walk: Vec<u32> = (0..255).chain(512..765).collect();
    let yh: Vec<u32> = (0..225).collect();
    let va: Vec<u32> = (225..241).collect();
    let vb: Vec<u32> = (241..255).chain([512, 513]).collect();
    let xh: Vec<u32> = (514..739).collect();
    let sc: Vec<u32> = (739..755).collect();
    let (h, w4s, zbp, fp, parp) = ([755u32, 756], 757u32..763, 763u32, 764u32, 255u32);
    assert_eq!(mc.x.len(), W);
    assert_eq!(mc.y.len(), W);
    assert_eq!(mc.e.len(), 2);
    assert_eq!(mc.pg.len(), 4 * PAGE_DI + 2);
    assert_eq!(mc.pg[4 * PAGE_DI + 1], ZB_LANE);
    let mut t = vec![NONE; NP];
    let mut used = vec![false; mc.b.next as usize];
    let mut set = |t: &mut Vec<u32>, used: &mut Vec<bool>, p: u32, l: u32| {
        assert!(t[p as usize] == NONE && !used[l as usize], "start765 table: phys {p} label {l}");
        t[p as usize] = l;
        used[l as usize] = true;
    };
    for i in 0..256 { set(&mut t, &mut used, walk[i], i as u32); }
    for k in 0..256 { set(&mut t, &mut used, 256 + k as u32, mc.pas[k]); }
    set(&mut t, &mut used, zbp, ZB_LANE);
    if !START765_SWAP {
        // F's end data must sit on labels 0..511 + y0, y1 (the emitters free every other label >= 512 after F): ring Y ends on
        // phys Y773 = [512, 513, 0..254] -> labels {255, t[513], 0..254 via the table at 79}, PAR on t[255]: so t[255], t[513] = y0, y1.
        set(&mut t, &mut used, parp, Y0_LABEL);
        set(&mut t, &mut used, 513, Y1_LABEL);
    }
    // preferred role labels for the clean lanes (labels >= 513 are clean at F's input)
    let mut pref: Vec<(u32, u32)> = vec![];
    for i in 0..225 { pref.push((xh[i], mc.x[i])); }
    for j in 0..PAGE_DI { pref.push((sc[j], mc.pg[2 * PAGE_DI + j])); }
    pref.push((vb[15], mc.pg[PAGE_DI + 15]));
    pref.push((h[0], mc.e[0]));
    pref.push((h[1], mc.e[1]));
    pref.push((fp, mc.pg[4 * PAGE_DI]));
    for (k, p) in w4s.clone().enumerate() { pref.push((p, mc.x[WHI + k])); }
    for (p, l) in pref {
        if l >= 513 && (l as usize) < used.len() && !used[l as usize] && t[p as usize] == NONE { set(&mut t, &mut used, p, l); }
    }
    let mut pool = (513..mc.b.next).filter(|&l| !used[l as usize]).collect::<Vec<u32>>().into_iter();
    for p in 0..NP as u32 {
        if t[p as usize] == NONE {
            let l = pool.next().expect("start765: label pool exhausted");
            set(&mut t, &mut used, p, l);
        }
    }
    let _ = parp;
    let base = mc.b.gates.len();
    gl_loader::splice_mapped(gl_loader::At::Start, &mut mc.b, &|q| {
        assert!((q as usize) < NP, "start765 list lane {q} >= 765");
        t[q as usize]
    });
    if AK_M2C && gl_loader::START765_D4 && !gl_loader::START765_OLD {
        // AKEND MBU: M2c of the D4 splice's list (mc.b.gates[base..], relabelled by t)
        ak_fix_pins();
        assert_eq!(mc.b.gates.len() - base, AK_START.0, "AKEND MBU: start list length");
        mbu_register("start-m2c", &mc.b.gates[base..], base, AK_START.1, mbu_lanes(AK_M2C_MEAS), 53, AK_M2C_FIX, true,
                     vec![], None, &|q: u32| t[q as usize]);
    }
    if PK_HX && gl_loader::START765_D4 && !gl_loader::START765_OLD {
        // PK HX: the hand-over counter block of the D4-family splice (mc.b.gates[base..], relabelled by t)
        assert_eq!(gl_loader::sha3_hex(PK_HX_FIX), "c7328067f0658a55edab0a6a0d9f6df605d408748c2a0444a13e662d4d732dbd", "PK HX: hx_fix sha3");
        assert_eq!(mc.b.gates.len() - base, AK_START.0, "PK HX: start list length");
        mbu_register("start-hx", &mc.b.gates[base..], base, PK_HX_BLK, mbu_lanes(PK_HX_MEAS), 6, PK_HX_FIX, true,
                     vec![], None, &|q: u32| t[q as usize]);
    }
    if START765_SWAP {
        // native role labels at 1431 (cut(431) keeps the prefix [0, WHI) of each ring and frees the tops; W4 = freed[0] = x[WHI])
        let mut n = vec![NONE; NP];
        for i in 0..225 { n[yh[i] as usize] = mc.y[i]; n[xh[i] as usize] = mc.x[i]; }
        for j in 0..PAGE_DI { n[va[j] as usize] = mc.pg[j]; n[vb[j] as usize] = mc.pg[PAGE_DI + j]; n[sc[j] as usize] = mc.pg[2 * PAGE_DI + j]; }
        n[h[0] as usize] = mc.e[0];
        n[h[1] as usize] = mc.e[1];
        n[parp as usize] = mc.par;
        for k in 0..256 { n[256 + k] = mc.pas[k]; }
        for (k, p) in w4s.clone().enumerate() { n[p as usize] = mc.x[WHI + k]; }
        n[zbp as usize] = mc.pg[4 * PAGE_DI + 1];
        n[fp as usize] = mc.pg[4 * PAGE_DI];
        assert!(n.iter().all(|&l| l != NONE));
        let mut seen = std::collections::HashSet::new();
        assert!(n.iter().all(|&l| seen.insert(l)), "start765: native role labels not distinct");
        // permutation: data on t[p] goes to n[p]; labels in n not in t (zero) fill the labels in t not in n
        let ti: std::collections::HashSet<u32> = t.iter().copied().collect();
        let ni: std::collections::HashSet<u32> = n.iter().copied().collect();
        let mut dest: HashMap<u32, u32> = (0..NP).map(|p| (t[p], n[p])).collect();
        let mut a: Vec<u32> = ni.iter().copied().filter(|l| !ti.contains(l)).collect();
        let mut bz: Vec<u32> = ti.iter().copied().filter(|l| !ni.contains(l)).collect();
        a.sort();
        bz.sort();
        assert_eq!(a.len(), bz.len());
        for (s0, d0) in a.into_iter().zip(bz) { dest.insert(s0, d0); }
        let mut keys: Vec<u32> = dest.keys().copied().collect();
        keys.sort();
        let mut done = std::collections::HashSet::new();
        let (mut nsw, mut ncyc) = (0usize, 0usize);
        let mut g: GL = vec![];
        for &s0 in &keys {
            if done.contains(&s0) || dest[&s0] == s0 { done.insert(s0); continue; }
            ncyc += 1;
            let mut c = vec![s0];
            let mut q = dest[&s0];
            while q != s0 { c.push(q); q = dest[&q]; }
            for &l in &c { done.insert(l); }
            for &sj in &c[1..] {
                g.extend([G(s0, sj, NONE), G(sj, s0, NONE), G(s0, sj, NONE)]);
                nsw += 1;
            }
        }
        mc.b.t(&g);
        eprintln!("start765 (swap mode): data moved onto the native labels at 1431: {} cycles, {} swaps, {} CX, 0 CCX", ncyc, nsw, g.len());
        return;
    }
    let mut extra = move |b: &mut B| -> u32 { pool.next().unwrap_or_else(|| b.alloc()) };
    let tm = |v: &[u32]| -> Vec<u32> { v.iter().map(|&p| t[p as usize]).collect() };
    let mut x = tm(&xh);
    x.extend(tm(&w4s.clone().collect::<Vec<u32>>()));
    while x.len() < W { x.push(extra(&mut mc.b)); }
    let mut y = tm(&yh);
    while y.len() < W { y.push(extra(&mut mc.b)); }
    let mut pg = tm(&va);
    pg.extend(tm(&vb));
    pg.extend(tm(&sc));
    for _ in 0..PAGE_DI { pg.push(extra(&mut mc.b)); }
    pg.push(t[fp as usize]);
    pg.push(t[zbp as usize]);
    mc.x = x;
    mc.y = y;
    mc.pg = pg;
    mc.e = tm(&h);
    mc.par = t[parp as usize];
    // stale software state of the dropped native start: its free list and dirty pool name labels the list now uses
    let live: std::collections::HashSet<u32> = t.iter().copied().chain(mc.x.iter().copied()).chain(mc.y.iter().copied()).chain(mc.pg.iter().copied()).collect();
    mc.b.free.retain(|l| !live.contains(l));
    let mut dirty = mc.pas.clone();
    dirty.extend_from_slice(&mc.x);
    dirty.extend_from_slice(&mc.y);
    mc.dirty = dirty;
    eprintln!("start765: table built (765 phys lanes), par label {}, W4 label {}, b.next {}", mc.par, mc.x[WHI], mc.b.next);
}

/// physical emitter
struct P {
    ops: Vec<Op>,
    free: Vec<u32>,
    next: u32,
    bits: u64,
}
const fn q(i: u32) -> QubitId {
    QubitId(i as u64)
}
impl P {
    fn alloc(&mut self) -> u32 {
        if let Some(a) = self.free.pop() {
            a
        } else {
            self.next += 1;
            self.next - 1
        }
    }
    fn allocn(&mut self, k: usize) -> Vec<u32> {
        (0..k).map(|_| self.alloc()).collect()
    }
    fn rel(&mut self, a: u32) {
        self.free.push(a);
        self.free.sort_by(|x, y| y.cmp(x));
    }
    #[inline]
    fn gate(&mut self, g: G) {
        let mut o = Op::empty();
        if g.2 != NONE {
            o.kind = OperationType::CCX;
            o.q_control1 = q(g.0);
            o.q_control2 = q(g.1);
            o.q_target = q(g.2);
        } else if g.1 != NONE {
            o.kind = OperationType::CX;
            o.q_control1 = q(g.0);
            o.q_target = q(g.1);
        } else {
            o.kind = OperationType::X;
            o.q_target = q(g.0);
        }
        self.ops.push(o);
    }
    fn g(&mut self, l: &[G]) {
        for &x in l {
            self.gate(x);
        }
    }
    fn xc(&mut self, a: u32, b: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::X;
        o.q_target = q(a);
        o.c_condition = BitId(b);
        self.ops.push(o);
    }
    fn zc(&mut self, a: u32, b: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::Z;
        o.q_target = q(a);
        o.c_condition = BitId(b);
        self.ops.push(o);
    }
    /// LEAN_SQ: CZ(a, b) under the classical bit (Gidney's AND uncompute correction).
    fn czc(&mut self, a: u32, b: u32, bit: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::CZ;
        o.q_control1 = q(a);
        o.q_target = q(b);
        o.c_condition = BitId(bit);
        self.ops.push(o);
    }
    fn hmr(&mut self, a: u32) -> u64 {
        let b = self.bits;
        self.bits += 1;
        let mut o = Op::empty();
        o.kind = OperationType::Hmr;
        o.q_target = q(a);
        o.c_target = BitId(b);
        self.ops.push(o);
        b
    }
}

fn add_gl(t: &[u32], s: &[u32], c: u32) -> GL {
    let mut g = Vec::with_capacity(3 * t.len());
    for i in 0..t.len() {
        g.push(gc(c, s[i]));
        g.push(gc(c, t[i]));
        g.push(gt(s[i], t[i], c));
    }
    g
}
fn add_back(t: &[u32], s: &[u32], c: u32) -> GL {
    let mut g = Vec::with_capacity(4 * t.len());
    for i in (0..t.len()).rev() {
        g.push(gt(s[i], t[i], c));
        g.push(gc(c, t[i]));
        g.push(gc(s[i], t[i]));
        g.push(gc(c, s[i]));
    }
    g
}

/// The shell. No spare lane for the doubling: it is a rotation, the top bit is already the LSB of its multiple of c0.
/// The carry lane doubles as the fold's clean lane. a has 255 bits, its top lane and N's top lane are free after F.
/// x is squared into in place and classical offsets load 128 bits at a time. The top CAPW multiplier bits can move into the
/// product's top lanes with a descending seed, an idea from the public frogdrop 765 note 153caee.
/// LEAN_SQ: Gidney halved adder (arXiv:1709.06648): tgt += add mod 2^w (w = tgt.len() = add.len()); the carries
/// c_1..c_(w-1) live on anc[0..w-1) (clean in, clean out) and are uncomputed by measurement (Hmr, then CZ under the
/// bit). With cout = Some(s) the carry-out c_w is computed onto s and kept. w-1 Toffoli (w with cout).
fn gid_add(p: &mut P, tgt: &[u32], add: &[u32], anc: &[u32], cout: Option<u32>) {
    let w = tgt.len();
    assert!(w >= 1 && add.len() == w);
    let kmax = if cout.is_some() { w } else { w - 1 };
    assert!(anc.len() + 1 >= kmax, "gid_add: {} ancillae for {} carries", anc.len(), kmax);
    for k in 0..kmax {
        let ck = if k == 0 { NONE } else { anc[k - 1] };
        let tc = if k == w - 1 { cout.unwrap() } else { anc[k] };
        if ck != NONE {
            p.g(&[gc(ck, add[k]), gc(ck, tgt[k])]);
        }
        p.g(&[gt(add[k], tgt[k], tc)]);
        if ck != NONE {
            p.g(&[gc(ck, tc)]);
        }
    }
    for k in (0..w).rev() {
        let ck = if k == 0 { NONE } else { anc[k - 1] };
        let processed = k < kmax;
        if processed && k < w - 1 {
            if ck != NONE {
                p.g(&[gc(ck, anc[k])]);
            }
            let m = p.hmr(anc[k]);
            p.czc(add[k], tgt[k], m);
        }
        if processed {
            if ck != NONE {
                p.g(&[gc(ck, add[k])]);
            }
            p.g(&[gc(add[k], tgt[k])]);
        } else {
            p.g(&[gc(add[k], tgt[k])]);
            if ck != NONE {
                p.g(&[gc(ck, tgt[k])]);
            }
        }
    }
}
/// LEAN_SQ: tgt -= add mod 2^w as not(not tgt + add).
fn gid_sub(p: &mut P, tgt: &[u32], add: &[u32], anc: &[u32]) {
    let x: GL = tgt.iter().map(|&q0| gx(q0)).collect();
    p.g(&x);
    gid_add(p, tgt, add, anc, None);
    p.g(&x);
}
/// LEAN_SQ: Haener's squarer, LSB first: z (2n or more wires, zero) += v^2. v^2 = -v + sum_i (2 v_i - 1) 2^(2i+1) (h_i + v_i),
/// h_i = v >> (i + 1). Step 0: z[0..n+1) -= v. Step i: sign-extend z[n+i] -> z[n+i+1]; window z[2i+1 .. n+i+2) -= u, u = h_i
/// padded to the window and inverted under v_i. Last: z[2n-1] ^= v_(n-1). AND ancillae: z above the window, then xa.
fn sq_fwd(p: &mut P, v: &[u32], z: &[u32], pad: [u32; 2], xa: [u32; 2]) {
    let n = v.len();
    let zb = z.len();
    assert!(zb >= 2 * n);
    {
        let w = n + 1;
        let mut add: Vec<u32> = v.to_vec();
        add.push(pad[0]);
        let mut anc: Vec<u32> = z[w..].to_vec();
        anc.extend_from_slice(&xa);
        gid_sub(p, &z[0..w], &add, &anc);
    }
    for i in 0..n - 1 {
        let (lo, top) = (2 * i + 1, n + i + 2);
        let w = top - lo;
        p.g(&[gc(z[n + i], z[n + i + 1])]);
        let mut add: Vec<u32> = v[i + 1..].to_vec();
        add.push(pad[0]);
        add.push(pad[1]);
        assert!(add.len() == w);
        let inv: GL = add.iter().map(|&q0| gc(v[i], q0)).collect();
        let mut anc: Vec<u32> = z[top..].to_vec();
        anc.extend_from_slice(&xa);
        p.g(&inv);
        gid_sub(p, &z[lo..top], &add, &anc);
        p.g(&inv);
    }
    p.g(&[gc(v[n - 1], z[2 * n - 1])]);
}
/// LEAN_SQ: the exact reverse of sq_fwd (z -= v^2 back to zero).
fn sq_rev(p: &mut P, v: &[u32], z: &[u32], pad: [u32; 2], xa: [u32; 2]) {
    let n = v.len();
    p.g(&[gc(v[n - 1], z[2 * n - 1])]);
    for i in (0..n - 1).rev() {
        let (lo, top) = (2 * i + 1, n + i + 2);
        let w = top - lo;
        let mut add: Vec<u32> = v[i + 1..].to_vec();
        add.push(pad[0]);
        add.push(pad[1]);
        assert!(add.len() == w);
        let inv: GL = add.iter().map(|&q0| gc(v[i], q0)).collect();
        let mut anc: Vec<u32> = z[top..].to_vec();
        anc.extend_from_slice(&xa);
        p.g(&inv);
        gid_add(p, &z[lo..top], &add, &anc, None);
        p.g(&inv);
        p.g(&[gc(z[n + i], z[n + i + 1])]);
    }
    {
        let w = n + 1;
        let mut add: Vec<u32> = v.to_vec();
        add.push(pad[0]);
        let mut anc: Vec<u32> = z[w..].to_vec();
        anc.extend_from_slice(&xa);
        gid_add(p, &z[0..w], &add, &anc, None);
    }
}
/// LEAN_SB: z[0..2n) += v * h by controlled window adds z[i..i+n+1) += v_i * h (h padded with one zero lane); 3 T per wire.
/// Partial sums stay below 2^(i+n+1), so no window overflows and the carry lane returns clean.
fn cross_fwd(p: &mut P, v: &[u32], h: &[u32], z: &[u32], pad: u32, c: u32) {
    let n = v.len();
    let mut u: Vec<u32> = h.to_vec();
    u.push(pad);
    for i in 0..n {
        let w = n + 1;
        let tgt = &z[i..i + w];
        let mut g = add_gl(tgt, &u, c);
        for j in (0..w).rev() {
            g.extend_from_slice(&[gt(u[j], tgt[j], c), gc(c, tgt[j]), gt(v[i], u[j], tgt[j]), gc(c, u[j])]);
        }
        p.g(&g);
    }
}
fn cross_rev(p: &mut P, v: &[u32], h: &[u32], z: &[u32], pad: u32, c: u32) {
    let n = v.len();
    let mut u: Vec<u32> = h.to_vec();
    u.push(pad);
    for i in (0..n).rev() {
        let w = n + 1;
        let tgt = &z[i..i + w];
        let mut g = add_gl(tgt, &u, c);
        for j in (0..w).rev() {
            g.extend_from_slice(&[gt(u[j], tgt[j], c), gc(c, tgt[j]), gt(v[i], u[j], tgt[j]), gc(c, u[j])]);
        }
        p.g(&rev(&g));
    }
}

struct S3 {
    dirty: Vec<u32>,
    zl: Vec<u32>,
}
impl S3 {
    fn m(&self, l: &[Lit], t: u32) -> GL {
        mcx(l, t, &self.dirty)
    }
    /// reg += f at its LSB, plus sign*f*2^pos for (pos,sign,z) in terms, z clean. One two-pass chain: a clean lane z in place of
    /// the borrowed bit takes f on one pass. f's wire reads f^d0 between the passes; the corrections are CNOTs.
    fn merged(&self, reg: &[u32], f: u32, terms: &[(usize, i32, u32)], c: u32) -> GL {
        let mut r = vec![f];
        r.extend_from_slice(reg);
        let mut d: Vec<u32> = Vec::with_capacity(r.len());
        let mut u = 0;
        for i in 0..r.len() {
            if let Some(t) = terms.iter().find(|t| t.0 + 1 == i) {
                d.push(t.2);
            } else {
                loop {
                    let q0 = self.dirty[u];
                    u += 1;
                    if q0 != c && !r.contains(&q0) && !terms.iter().any(|t| t.2 == q0) {
                        d.push(q0);
                        break;
                    }
                }
            }
        }
        let sub = rev(&add_chain(&r, &d, c));
        let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
        let d0 = d[0];
        let mut g: GL = vec![];
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
        }
        g.extend_from_slice(&nots);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&nots);
        g.push(gx(f));
        g
    }
    /// ZFOR-wait signed digits: `merged` whose extra terms (pos, sign, lane) add sign * (W - c) * 2^pos, W and c wires.
    /// Lane values across the two passes: positive (not W, c), negative (W, not c) (tools/chain_signed.py, exhaustive).
    fn merged_s(&self, reg: &[u32], f: u32, terms: &[(usize, i32, u32)], wt: u32, cc: u32, dterms: &[(usize, i32, u32)], c: u32) -> GL {
        let mut r = vec![f];
        r.extend_from_slice(reg);
        let mut d: Vec<u32> = Vec::with_capacity(r.len());
        let mut u = 0;
        for i in 0..r.len() {
            if let Some(t) = terms.iter().chain(dterms.iter()).find(|t| t.0 + 1 == i) {
                d.push(t.2);
            } else {
                loop {
                    let q0 = self.dirty[u];
                    u += 1;
                    if q0 != c && q0 != wt && q0 != cc && !r.contains(&q0) && !terms.iter().chain(dterms.iter()).any(|t| t.2 == q0) {
                        d.push(q0);
                        break;
                    }
                }
            }
        }
        let sub = rev(&add_chain(&r, &d, c));
        let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
        let d0 = d[0];
        let mut g: GL = vec![];
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
        }
        for t in dterms.iter() {
            g.push(gc(wt, t.2));
            if t.1 > 0 {
                g.push(gx(t.2));
            }
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
        }
        for t in dterms.iter() {
            g.push(gc(wt, t.2));
            g.push(gc(cc, t.2));
        }
        g.extend_from_slice(&nots);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gx(t.2));
        }
        for t in dterms.iter() {
            g.push(gc(cc, t.2));
            if t.1 > 0 {
                g.push(gx(t.2));
            }
        }
        g.extend_from_slice(&nots);
        g.push(gx(f));
        g
    }
    /// ZFOR-wait: acc += a with no control, carry-out on ov (zuiris's add_ctl with the control removed: 2 T per wire).
    fn add_plain(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g: GL;
        if a.len() == 256 {
            g = add_gl(acc, a, c);
            g.push(gc(c, ov));
            for j in (0..256).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gc(a[j], acc[j]), gc(c, a[j])]);
            }
        } else {
            g = add_gl(&acc[..255], a, c);
            g.push(gt(c, acc[255], ov));
            g.push(gc(c, acc[255]));
            for j in (0..255).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gc(a[j], acc[j]), gc(c, a[j])]);
            }
        }
        g
    }
    /// ZFOR-wait: zuiris's clear_ov with the control removed.
    fn clear_ov_plain(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        let mut h: GL = acc[k..].iter().map(|&q0| gx(q0)).collect();
        let mut g;
        if a.len() == 256 {
            h.extend(add_gl(&acc[k..], &a[k..], c));
            g = h.clone();
            g.push(gc(c, ov));
        } else {
            h.extend(add_gl(&acc[k..255], &a[k..], c));
            g = h.clone();
            g.push(gt(c, acc[255], ov));
        }
        g.extend(rev(&h));
        g
    }
    /// ZFOR-wait signed round: acc = acc + a (bit = 1) or acc - a (bit = 0), the subtraction as ~(~acc + a). The bit wire
    /// holds c = not bit inside the bracket; the next doubling's fold rides the ov chain as (K/2)(W255 - c).
    fn round3(&self, acc: &[u32], a: &[u32], bit: u32, c: u32, ov: u32, nxt: bool) -> GL {
        let mut g: GL = vec![gx(bit)];
        for &q0 in acc {
            g.push(gc(bit, q0));
        }
        g.extend(self.add_plain(acc, a, c, ov));
        if nxt {
            let z = &self.zl;
            g.extend(self.merged_s(&acc[0..RW], ov, &[(4, 1, z[3]), (6, -1, z[0]), (10, 1, z[1]), (32, 1, z[2])], acc[255], bit, &[(3, 1, z[4]), (5, -1, z[5]), (9, 1, z[6]), (31, 1, z[7])], c));
        } else {
            g.extend(self.lean(acc, ov, RW, c));
        }
        g.extend(self.clear_ov_plain(acc, a, c, ov));
        for &q0 in acc {
            g.push(gc(bit, q0));
        }
        g.push(gx(bit));
        g
    }
    /// ZFOR-wait: acc += a, no control (one plain round).
    fn add_round(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g = self.add_plain(acc, a, c, ov);
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov_plain(acc, a, c, ov));
        g
    }
    /// ZFOR-wait: acc -= a (fixed subtraction round, no doubling term).
    fn sub_round(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g: GL = acc.iter().map(|&q0| gx(q0)).collect();
        g.extend(self.add_plain(acc, a, c, ov));
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov_plain(acc, a, c, ov));
        g.extend(acc.iter().map(|&q0| gx(q0)));
        g
    }
    /// ZFOR-wait: acc := acc / 2 mod p (inverse of zuiris's doubling), returns the new labeling.
    fn halve(&self, acc: &[u32], c: u32) -> (Vec<u32>, GL) {
        let mut prev: Vec<u32> = acc[1..].to_vec();
        prev.push(acc[0]);
        let (t2, h) = self.dbl(&prev, c);
        assert!(t2 == acc);
        (prev, rev(&h))
    }
    fn lean(&self, t: &[u32], f: u32, _window: usize, c2: u32) -> GL {
        let z = &self.zl;
        if ZL >= 4 {
            return self.merged(&t[0..RW], f, &[(4, 1, z[3]), (6, -1, z[0]), (10, 1, z[1]), (32, 1, z[2])], c2);
        }
        let mut g = inc_long(&t[0..CHW], f, &self.dirty, c2);
        g.extend(self.merged(&t[4..RW], f, &[(2, -1, z[0]), (6, 1, z[1]), (28, 1, z[2])], c2));
        g
    }
    fn dbl(&self, t: &[u32], c2: u32) -> (Vec<u32>, GL) {
        let mut t2 = vec![t[255]];
        t2.extend_from_slice(&t[..255]);
        let f = t2[0];
        let z = &self.zl;
        let g = self.merged(&t2[4..RW], f, &[(2, -1, z[0]), (6, 1, z[1]), (28, 1, z[2])], c2);
        (t2, g)
    }
    fn add_ctl(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let mut g: GL;
        if a.len() == 256 {
            g = add_gl(acc, a, c);
            g.push(gt(ctl, c, ov));
            for j in (0..256).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gt(ctl, a[j], acc[j]), gc(c, a[j])]);
            }
        } else {
            g = add_gl(&acc[..255], a, c);
            g.extend(self.m(&[(ctl, true), (c, true), (acc[255], true)], ov));
            g.push(gt(ctl, c, acc[255]));
            for j in (0..255).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gt(ctl, a[j], acc[j]), gc(c, a[j])]);
            }
        }
        g
    }
    /// ov = ctl & (T < a), read on the top CMPW wires. An equal window reads as T >= a, so T = a (the first add) is right.
    fn clear_ov(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        let mut h: GL = acc[k..].iter().map(|&q0| gx(q0)).collect();
        let mut g;
        if a.len() == 256 {
            h.extend(add_gl(&acc[k..], &a[k..], c));
            g = h.clone();
            g.push(gt(ctl, c, ov));
        } else {
            h.extend(add_gl(&acc[k..255], &a[k..], c));
            g = h.clone();
            g.extend(self.m(&[(ctl, true), (c, true), (acc[255], true)], ov));
        }
        g.extend(rev(&h));
        g
    }
    fn round(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let mut g = self.add_ctl(acc, a, ctl, c, ov);
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov(acc, a, ctl, c, ov));
        g
    }
    /// acc = a * sum bits[i] 2^i mod p; the top w bits move into acc's top lanes. Returns acc, the fresh lanes, the gates.
    fn product(&self, p: &mut P, a: &[u32], bits: &[u32], c: u32, ov: u32, w: usize) -> (Vec<u32>, Vec<u32>, GL) {
        let nb = bits.len();
        let j_: Vec<u32> = bits[nb - w..].to_vec();
        let low = p.allocn(256 - w);
        let mut acc = low.clone();
        acc.extend_from_slice(&j_);
        let mut g: GL = vec![];
        let mut al = NONE;
        if w > 0 {
            al = p.alloc();
            let zl: Vec<Lit> = (0..ZW).map(|r| (acc[r], false)).collect();
            for k in (1..(1usize << w)).rev() {
                let mut l: Vec<Lit> = vec![(al, false)];
                for i in 0..w {
                    l.push((j_[i], (k >> i) & 1 == 1));
                }
                g.extend(self.m(&l, c));
                for i in 0..w {
                    if (k >> i) & 1 == 1 {
                        g.push(gc(c, j_[i]));
                    }
                }
                g.push(gc(c, al));
                let mut l2: Vec<Lit> = vec![(al, true)];
                l2.extend_from_slice(&zl);
                g.extend(self.m(&l2, c));
                g.extend(self.round(&acc, a, al, c, ov));
            }
            g.push(gx(al));
            g.extend(self.m(&zl, al));
        }
        // ZFOR-wait signed digits. With CAPW = w > 0, zuiris's seed loop above leaves acc = S a (S = the top w bits).
        // Then acc := 2 acc + a (one plain round), m = nb - w signed rounds on the low bits give 2ab + a; subtract a, halve.
        if w == 0 {
            for j in 0..a.len() {
                g.push(gc(a[j], acc[j]));
            }
        } else {
            let (t2, h) = self.dbl(&acc, c);
            acc = t2;
            g.extend(h);
            g.extend(self.add_round(&acc, a, c, ov));
        }
        let idx: Vec<usize> = (0..(nb - w)).rev().collect();
        for (j, &i) in idx.iter().enumerate() {
            if j == 0 && w == 0 && a.len() < 256 {
                // acc = a with a 255-bit a: top wire 0, so this doubling's fold is dead
                let mut t2 = vec![acc[255]];
                t2.extend_from_slice(&acc[..255]);
                acc = t2;
            } else {
                let (t2, h) = self.dbl(&acc, c);
                acc = t2;
                g.extend(h);
            }
            g.extend(self.round3(&acc, a, bits[i], c, ov, false));
        }
        g.extend(self.sub_round(&acc, a, c, ov));
        let (t2, h) = self.halve(&acc, c);
        acc = t2;
        g.extend(h);
        if w > 0 {
            p.rel(al);
        }
        (acc, low, g)
    }
    fn neg(&self, p: &mut P, t: &[u32], c2: u32) {
        let u = p.alloc();
        p.g(&[gx(u)]);
        let mut g: GL = t.iter().map(|&q0| gx(q0)).collect();
        for &b in &C0M1 {
            g.extend(rev(&inc_long(&t[b..], u, &self.dirty, c2)));
        }
        g.push(gx(u));
        p.g(&g);
        p.rel(u);
    }
    fn cneg_list(&self, t: &[u32], ctl: u32, neg_when: bool, c2: u32) -> GL {
        let pre: GL = if neg_when { vec![] } else { vec![gx(ctl)] };
        let mut g = pre.clone();
        for &q0 in t {
            g.push(gc(ctl, q0));
        }
        for &b in &C0M1 {
            g.extend(rev(&inc_long(&t[b..], ctl, &self.dirty, c2)));
        }
        g.extend_from_slice(&pre);
        g
    }
    /// t += classical s mod p (t -= s when sub), 128 lanes at a time.
    fn cl_add(&mut self, p: &mut P, t: &[u32], bits: u64, sub: bool) {
        const K: usize = 128;
        let l = p.allocn(K);
        let (k, c, o) = (p.alloc(), p.alloc(), p.alloc());
        self.zl = p.allocn(ZL);
        let keep = self.dirty.clone();
        self.dirty.extend_from_slice(&l);
        let (lo, hi) = (&t[..K], &t[K..]);
        let flip = |r: &[u32]| -> GL { r.iter().map(|&q0| gx(q0)).collect() };
        enum It {
            Load(u64),
            Gs(GL),
        }
        let mut seq: Vec<It> = vec![];
        let a1 = {
            let mut g = add_gl(lo, &l, c);
            g.push(gc(c, k));
            g.extend(add_back(lo, &l, c));
            g
        };
        let a2 = {
            let mut g = add_gl(hi, &l, k);
            g.push(gc(k, o));
            g.extend(add_back(hi, &l, k));
            g
        };
        let h = {
            let mut h0 = flip(lo);
            h0.extend(add_gl(lo, &l, c));
            let mut g = h0.clone();
            g.push(gc(c, k));
            g.extend(rev(&h0));
            g
        };
        let h2 = {
            let mut h0 = flip(hi);
            h0.extend(add_gl(hi, &l, k));
            let mut g = h0.clone();
            g.push(gc(k, o));
            g.extend(rev(&h0));
            g
        };
        seq.push(It::Load(0));
        seq.push(It::Gs(a1));
        seq.push(It::Load(0));
        seq.push(It::Load(K as u64));
        seq.push(It::Gs(a2));
        seq.push(It::Load(K as u64));
        seq.push(It::Load(0));
        seq.push(It::Gs(h.clone()));
        seq.push(It::Load(0));
        seq.push(It::Gs(self.lean(t, o, 256, c)));
        seq.push(It::Load(0));
        seq.push(It::Gs(h.clone()));
        seq.push(It::Load(0));
        seq.push(It::Load(K as u64));
        seq.push(It::Gs(h2));
        seq.push(It::Load(K as u64));
        seq.push(It::Load(0));
        seq.push(It::Gs(h));
        seq.push(It::Load(0));
        if sub {
            seq.reverse();
        }
        for it in &seq {
            match it {
                It::Load(off) => {
                    for i in 0..K {
                        p.xc(l[i], bits + off + i as u64);
                    }
                }
                It::Gs(g) => {
                    if sub {
                        p.g(&rev(g));
                    } else {
                        p.g(g);
                    }
                }
            }
        }
        self.dirty = keep;
        for &q0 in &l {
            p.rel(q0);
        }
        p.rel(k);
        p.rel(c);
        p.rel(o);
        for i in 0..ZL {
            p.rel(self.zl[i]);
        }
    }
    /// x += lam^2 in place: halve 256 times, then Horner on x.
    /// LEAN_SQ: ov ^= [x_top < atop] on the top CMPW wires (the parent's compare with the addend's top wires given).
    fn clear_ov_top(&self, x: &[u32], atop: &[u32], c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        assert!(atop.len() == CMPW);
        let mut h: GL = x[k..].iter().map(|&q0| gx(q0)).collect();
        h.extend(add_gl(&x[k..], atop, c));
        let mut g = h.clone();
        g.push(gc(c, ov));
        g.extend(rev(&h));
        g
    }
    /// LEAN_SQ: x[j..256) += a (a.len() = 256 - j), carry-out on ov, fold ov c0 (the parent's chain), erase ov by the
    /// top-window compare against (a << j)'s top wires. The parent's add_plain + lean + clear_ov_plain, shifted.
    fn fold_shift(&self, x: &[u32], a: &[u32], j: usize, c: u32, ov: u32) -> GL {
        let w = 256 - j;
        assert!(a.len() == w && w >= CMPW);
        let mut g = add_gl(&x[j..], a, c);
        g.push(gc(c, ov));
        g.extend(add_back(&x[j..], a, c));
        if LEAN_ZL >= 4 {
            g.extend(self.lean(x, ov, RW, c));
        } else {
            let z = &self.zl;
            g.extend(inc_long(&x[0..CHW], ov, &self.dirty, c));
            g.extend(self.merged(&x[4..RW], ov, &[(2, -1, z[0]), (6, 1, z[1]), (28, 1, z[2])], c));
        }
        g.extend(self.clear_ov_top(x, &a[w - CMPW..], c, ov));
        g
    }
    /// LEAN_SQ: x[o..o+wv) += v, the carry-out carried on through the next SPILL_W wires by the borrowed-lane increment,
    /// then erased by the window compare (t = [x_window < v]). Exact unless the carry runs past the window (2^-64).
    fn spill_add(&self, x: &[u32], v: &[u32], o: usize, c: u32, t: u32) -> GL {
        let wv = v.len();
        let hi = o + wv;
        assert!(hi <= 256);
        let mut g = add_gl(&x[o..hi], v, c);
        g.push(gc(c, t));
        g.extend(add_back(&x[o..hi], v, c));
        let top = (hi + SPILL_W).min(256);
        if top > hi {
            g.extend(inc_long(&x[hi..top], t, &self.dirty, c));
        }
        let mut h: GL = x[o..hi].iter().map(|&q0| gx(q0)).collect();
        h.extend(add_gl(&x[o..hi], v, c));
        g.extend(h.clone());
        g.push(gc(c, t));
        g.extend(rev(&h));
        g
    }
    /// LEAN_SQ: x += (Z << sh) mod p (pos) or x -= (Z << sh) mod p, Z = z[0..zw) an integer below 2^zw. The low 256 - sh
    /// wires shift into x; the top zw - 256 + sh wires are the spill, added times c0 = 2^32 + 2^10 - 2^6 + 2^4 + 1.
    fn weighted(&self, x: &[u32], z: &[u32], zw: usize, sh: usize, pos: bool, c: u32, ov: u32) -> GL {
        let flip: GL = x.iter().map(|&q0| gx(q0)).collect();
        let mut g: GL = vec![];
        if !pos {
            g.extend(flip.clone());
        }
        let wlo = 256 - sh;
        g.extend(self.fold_shift(x, &z[..wlo], sh, c, ov));
        if zw > wlo {
            let hi = &z[wlo..zw];
            for (o, sg) in [(32usize, true), (10, true), (6, false), (4, true), (0, true)] {
                if !sg {
                    g.extend(flip.clone());
                }
                g.extend(self.spill_add(x, hi, o, c, ov));
                if !sg {
                    g.extend(flip.clone());
                }
            }
        }
        if !pos {
            g.extend(flip);
        }
        g
    }
    /// LEAN_SQ: x += lam^2 mod p. lam = L + 2^128 H, S = L + H: lam^2 = L^2 (1 - 2^128) + H^2 (c0 - 2^128) + 2^128 S^2.
    fn sq_into_lean(&mut self, p: &mut P, x: &[u32], lam: &[u32]) {
        let next0 = p.next;
        let (c, ov) = (p.alloc(), p.alloc());
        self.zl = p.allocn(LEAN_ZL);
        let (l, h) = (&lam[..128], &lam[128..]);
        let xa = [self.zl[0], self.zl[1]];
        if LEAN_SB {
            // 256-wire variant: lam^2 = L^2 + 2^129 L H + c0 H^2; pads = zl[2] and ov (ov idle during the squarers).
            let z = p.allocn(256);
            assert!(p.next == next0, "LEAN_SQ raised the peak: {} -> {}", next0, p.next);
            let pad = [self.zl[2], ov];
            sq_fwd(p, l, &z, pad, xa);
            p.g(&self.weighted(x, &z, 256, 0, true, c, ov));
            sq_rev(p, l, &z, pad, xa);
            sq_fwd(p, h, &z, pad, xa);
            for (sh, pos) in [(32usize, true), (10, true), (6, false), (4, true), (0, true)] {
                p.g(&self.weighted(x, &z, 256, sh, pos, c, ov));
            }
            if !LEAN_NEGCTL {
                sq_rev(p, h, &z, pad, xa);
            }
            cross_fwd(p, l, h, &z, self.zl[2], c);
            p.g(&self.weighted(x, &z, 256, 129, true, c, ov));
            cross_rev(p, l, h, &z, self.zl[2], c);
            for &q0 in z.iter().rev() {
                p.rel(q0);
            }
            for i in 0..LEAN_ZL {
                p.rel(self.zl[i]);
            }
            p.rel(ov);
            p.rel(c);
            assert!(p.next == next0);
            return;
        }
        let z = p.allocn(258);
        let s = p.alloc();
        assert!(p.next == next0, "LEAN_SQ raised the peak: {} -> {}", next0, p.next);
        let pad = [self.zl[2], self.zl[3]];
        sq_fwd(p, l, &z, pad, xa);
        p.g(&self.weighted(x, &z, 256, 0, true, c, ov));
        p.g(&self.weighted(x, &z, 256, 128, false, c, ov));
        sq_rev(p, l, &z, pad, xa);
        sq_fwd(p, h, &z, pad, xa);
        for (sh, pos) in [(32usize, true), (10, true), (6, false), (4, true), (0, true), (128, false)] {
            p.g(&self.weighted(x, &z, 256, sh, pos, c, ov));
        }
        sq_rev(p, h, &z, pad, xa);
        gid_add(p, l, h, &z[..128], Some(s));
        let sv: Vec<u32> = [l, &[s][..]].concat();
        sq_fwd(p, &sv, &z, pad, xa);
        p.g(&self.weighted(x, &z, 258, 128, true, c, ov));
        sq_rev(p, &sv, &z, pad, xa);
        if !LEAN_NEGCTL {
            let mut hp: Vec<u32> = h.to_vec();
            hp.push(pad[0]);
            let fl: GL = sv.iter().map(|&q0| gx(q0)).collect();
            p.g(&fl);
            gid_add(p, &sv, &hp, &z[..128], None);
            p.g(&fl);
        }
        p.rel(s);
        for &q0 in z.iter().rev() {
            p.rel(q0);
        }
        for i in 0..LEAN_ZL {
            p.rel(self.zl[i]);
        }
        p.rel(ov);
        p.rel(c);
        assert!(p.next == next0);
    }
    fn sq_into(&mut self, p: &mut P, x: &[u32], lam: &[u32]) {
        if LEAN_SQ {
            self.sq_into_lean(p, x, lam);
            return;
        }
        let (c, ov, d) = (p.alloc(), p.alloc(), p.alloc());
        self.zl = p.allocn(ZL);
        let mut cur = x.to_vec();
        for _ in 0..256 {
            let mut prev: Vec<u32> = cur[1..].to_vec();
            prev.push(cur[0]);
            let (t2, h) = self.dbl(&prev, c);
            assert!(t2 == cur);
            p.g(&rev(&h));
            cur = prev;
        }
        // ZFOR-wait signed digits: cur = x / 2^256. One plain round (2 cur + lam), 256 signed rounds on lam's bits
        // (2 cur + s_i lam), subtract lam, halve: x + lam^2.
        {
            let (t2, h) = self.dbl(&cur, c);
            cur = t2;
            p.g(&h);
            p.g(&[gx(d)]);
            p.g(&self.round3(&cur, lam, d, c, ov, false));
            p.g(&[gx(d)]);
        }
        for i in (0..256).rev() {
            let (t2, h) = self.dbl(&cur, c);
            cur = t2;
            p.g(&h);
            p.g(&[gc(lam[i], d)]);
            p.g(&self.round3(&cur, lam, d, c, ov, false));
            p.g(&[gc(lam[i], d)]);
        }
        p.g(&self.sub_round(&cur, lam, c, ov));
        let (t2, h) = self.halve(&cur, c);
        cur = t2;
        p.g(&h);
        assert!(cur == x);
        p.rel(c);
        p.rel(ov);
        p.rel(d);
        for i in 0..ZL {
            p.rel(self.zl[i]);
        }
    }
}
struct Kept {
    y0: u32,
    y1: u32,
    par: u32,
    xtop: u32,
}
fn map_lanes(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32], kept: Option<&Kept>) -> Vec<u32> {
    let mut m = vec![NONE; fc.next as usize];
    for i in 0..256 {
        m[i] = x[i];
        m[256 + i] = pas[i];
    }
    if let Some(k) = kept {
        m[fc.y0 as usize] = k.y0;
        m[fc.y1 as usize] = k.y1;
    }
    for v in 0..fc.next as usize {
        if m[v] == NONE {
            m[v] = p.alloc();
        }
    }
    m
}
fn mapg(m: &[u32], g: G) -> G {
    if g.2 != NONE {
        // AND markers: a plain CCX here (exact; the measured uncompute is the P5SHELL / MarkerWalk path's)
        G(m[g.0 as usize], m[g.1 as usize], m[gl_loader::lane_of(g.2) as usize])
    } else if g.1 != NONE {
        G(m[g.0 as usize], m[g.1 as usize], NONE)
    } else {
        G(m[g.0 as usize], NONE, NONE)
    }
}
fn emit_f(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32]) -> (Vec<u32>, Kept) {
    let m = map_lanes(p, fc, x, pas, None);
    for &g in &fc.gates {
        p.gate(mapg(&m, g));
    }
    for &g in &fc.last {
        p.gate(mapg(&m, g));
    }
    let a: Vec<u32> = fc.ar.iter().map(|&v| m[v as usize]).collect();
    let kept = Kept { y0: m[fc.y0 as usize], y1: m[fc.y1 as usize], par: m[fc.par as usize], xtop: m[fc.xtop as usize] };
    for v in 512..fc.next {
        if v != fc.y0 && v != fc.y1 {
            p.rel(m[v as usize]);
        }
    }
    (a, kept)
}
fn emit_finv(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32], k: &Kept) {
    let m = map_lanes(p, fc, x, pas, Some(k));
    for &g in fc.last.iter().rev() {
        p.gate(mapg(&m, g));
    }
    for &g in fc.gates.iter().rev() {
        p.gate(mapg(&m, g));
    }
    for v in 512..fc.next {
        p.rel(m[v as usize]);
    }
}

/// P5 shell: this tree's walk F (`f_circuit`) as the division walk of the frogdrop product stage, emitted through the
/// Track 2 builder. Lanes as in `emit_f` / `emit_finv` (map_lanes), with B allocating. After `forward` the 2 lanes known
/// to be 0 (ring positions 0 and W-1 after F: inv bit 255 = a[255], and xtop; the ring is rotated, so these are
/// whatever lanes sit there) are freed, so the products see 255 inv + sign + 256 passenger
/// = 512 live, the ledger of the count of record; `inverse` takes them back (acquire) before the reversed gate list.
struct MarkerWalk {
    fc: FCirc,
    kept: Vec<(u64, u64, u64, u64)>, // (y0, y1, z255, ztop) physical lanes of each open division
    /// R765_PROF: forward / inverse traversals emitted so far
    nf: u32,
    ni: u32,
    /// per open forward walk: the measurement bits of each block of fc.mbu
    mbu_bits: Vec<Vec<Vec<crate::circuit::BitId>>>,
}
/// R765_PROF: the raw-dump tag of gate i of traversal `base` (fc.last = 999)
fn wtag(fc: &FCirc, base: u32, i: usize) -> u32 { base + if i < fc.tags.len() { fc.tags[i] as u32 } else { 999 } }
impl MarkerWalk {
    /// ob-hmr: an AND gate of F's list; `compute` = it is the first of its pair in emission order
    fn emit_and(b: &mut fd2::builder::B, m: &[u64], g: G, compute: bool) {
        let l = |v: u32| QubitId(m[v as usize]);
        let t = l(gl_loader::lane_of(g.2));
        if compute {
            b.and_c(l(g.0), l(g.1), t);
        } else if hmr_negctl() {
            b.hmr_to(t, BitId(0));
        } else {
            b.and_u(l(g.0), l(g.1), t);
        }
    }
    /// role 3 / 4 (ob-tail AND marker: compute / uncompute in forward order) -> AND compute? in this direction
    fn marker_compute(r: u8, inverse: bool) -> bool { (r == 3) != inverse }
    /// aris-eng T1: an MBU FIX gate: ANDC -> AND compute, ANDU -> measured uncompute (0 T), else emit (list body keeps emit's assert)
    fn emit_fix(b: &mut fd2::builder::B, m: &[u64], g: G) {
        match if g.2 == NONE { 0 } else { gl_loader::flag_of(g.2) } {
            gl_loader::ANDC => Self::emit_and(b, m, g, true),
            gl_loader::ANDU => Self::emit_and(b, m, g, false),
            _ => Self::emit(b, m, g),
        }
    }
    fn emit(b: &mut fd2::builder::B, m: &[u64], g: G) {
        let l = |v: u32| QubitId(m[v as usize]);
        assert!(g.2 == NONE || gl_loader::flag_of(g.2) == 0, "ob-tail: AND marker outside the role path (HMR_AND off?)");
        if g.2 != NONE {
            b.ccx(l(g.0), l(g.1), l(g.2));
        } else if g.1 != NONE {
            b.cx(l(g.0), l(g.1));
        } else {
            b.x(l(g.0));
        }
    }
}
impl fd2::pointadd_frogdrop::Walk for MarkerWalk {
    fn forward(&mut self, b: &mut fd2::builder::B, x: &[QubitId], pas: &[QubitId]) -> (Vec<QubitId>, (QubitId, bool)) {
        let fc = &self.fc;
        let mut m = vec![u64::MAX; fc.next as usize];
        for i in 0..256 {
            m[i] = x[i].0;
            m[256 + i] = pas[i].0;
        }
        for v in 512..fc.next as usize {
            m[v] = b.alloc().0;
        }
        let (tof0, (_, c0, e0)) = (b.tof, b.census());
        let prof = r765_prof();
        self.nf += 1;
        let (save, base) = (fd2::builder::ptag_get(), if self.nf == 1 { 1000 } else { 3000 });
        let ng = fc.gates.len();
        if fc.role.is_empty() {
            for (i, &g) in fc.gates.iter().chain(fc.last.iter()).enumerate() {
                if prof { fd2::builder::ptag(wtag(fc, base, if i < ng { i } else { usize::MAX })); }
                Self::emit(b, &m, g);
            }
        } else {
            let mut bits: Vec<Vec<crate::circuit::BitId>> = vec![];
            let (mut i, mut k) = (0usize, 0usize);
            while i < fc.gates.len() {
                if k < fc.mbu.len() && i == fc.mbu[k].b0 {
                    // p10 M3E / MBU: X-measure the lanes the block erases (functions of the lanes it keeps) instead of running it, with
                    // its FIX (the block's other net effect); the inverse walk, which runs the block, pays the debt
                    let x = &fc.mbu[k];
                    if x.fix_first { for &gf in x.fix.iter() { Self::emit_fix(b, &m, gf); } }
                    let bv = b.fresh_bits(x.meas.len());
                    for (j, &v) in x.meas.iter().enumerate() { b.hmr_to(QubitId(m[v as usize]), bv[j]); }
                    if !x.fix_first { for &gf in x.fix.iter() { Self::emit_fix(b, &m, gf); } }
                    bits.push(bv);
                    i = x.b1;
                    k += 1;
                    continue;
                }
                let g = fc.gates[i];
                if prof { fd2::builder::ptag(wtag(fc, base, i)); }
                match fc.role[i] { 0 => Self::emit(b, &m, g), r @ (3 | 4) => Self::emit_and(b, &m, g, Self::marker_compute(r, false)), r => Self::emit_and(b, &m, g, r == 1) }
                i += 1;
            }
            assert_eq!(k, fc.mbu.len(), "p10 MBU: forward walk missed a block");
            if !fc.mbu.is_empty() { self.mbu_bits.push(bits); }
            if prof { fd2::builder::ptag(base + 999); }
            for &g in fc.last.iter() {
                Self::emit(b, &m, g);
            }
        }
        if prof { fd2::builder::ptag(save); }
        let (_, c1, e1) = b.census();
        eprintln!("P5WALK fwd list_ccx {} B_tof_delta {} census_ccx_delta {} census_exp_delta {:.1}",
                  fc.gates.iter().chain(fc.last.iter()).filter(|g| g.2 != NONE).count(), b.tof - tof0, c1 - c0, e1 - e0);
        let a: Vec<QubitId> = fc.ar.iter().map(|&v| QubitId(m[v as usize])).collect();
        let (y0, y1) = (m[fc.y0 as usize], m[fc.y1 as usize]);
        let (z255, ztop) = (a[255].0, m[fc.xtop as usize]);
        assert!(z255 != ztop && !pas.iter().any(|q| q.0 == z255 || q.0 == ztop), "zero lanes are ring lanes");
        for v in 512..fc.next {
            if v != fc.y0 && v != fc.y1 {
                b.free(QubitId(m[v as usize]));
            }
        }
        b.free(QubitId(z255)); // inv < 2^255: bit 255 is 0 (J6, team40/shell/SHELL.md)
        b.free(QubitId(ztop)); // ring position W-1 = 0 at the end of F
        self.kept.push((y0, y1, z255, ztop));
        (a[..255].to_vec(), (QubitId(m[fc.par as usize]), true))
    }
    fn inverse(&mut self, b: &mut fd2::builder::B, x: &[QubitId], pas: &[QubitId]) {
        let (y0, y1, z255, ztop) = self.kept.pop().expect("inverse without forward");
        b.acquire(QubitId(ztop));
        b.acquire(QubitId(z255));
        let fc = &self.fc;
        let mut m = vec![u64::MAX; fc.next as usize];
        for i in 0..256 {
            m[i] = x[i].0;
            m[256 + i] = pas[i].0;
        }
        m[fc.y0 as usize] = y0;
        m[fc.y1 as usize] = y1;
        for v in 512..fc.next as usize {
            if m[v] == u64::MAX {
                m[v] = b.alloc().0;
            }
        }
        let (tof0, (_, c0, e0)) = (b.tof, b.census());
        let prof = r765_prof();
        self.ni += 1;
        let (save, base) = (fd2::builder::ptag_get(), if self.ni == 1 { 2000 } else { 4000 });
        if fc.role.is_empty() {
            let (ng, nl) = (fc.gates.len(), fc.last.len());
            for (i, &g) in fc.last.iter().rev().chain(fc.gates.iter().rev()).enumerate() {
                if prof { fd2::builder::ptag(wtag(fc, base, if i < nl { usize::MAX } else { ng - 1 - (i - nl) })); }
                Self::emit(b, &m, g);
            }
        } else {
            if prof { fd2::builder::ptag(base + 999); }
            for &g in fc.last.iter().rev() {
                Self::emit(b, &m, g);
            }
            let bits = if fc.mbu.is_empty() { vec![] } else { self.mbu_bits.pop().expect("p10 MBU: inverse without forward bits") };
            assert_eq!(bits.len(), fc.mbu.len());
            let mut k = fc.mbu.len();
            for (i, &g) in fc.gates.iter().enumerate().rev() {
                if prof { fd2::builder::ptag(wtag(fc, base, i)); }
                match fc.role[i] { 0 => Self::emit(b, &m, g), r @ (3 | 4) => Self::emit_and(b, &m, g, Self::marker_compute(r, true)), r => Self::emit_and(b, &m, g, r == 2) }
                if k > 0 && i == fc.mbu[k - 1].b0 {
                    // p10 M3E / MBU: the block has run in reverse back to its input, recomputing the measured lanes: pay the forward debt
                    let (x, bv) = (&fc.mbu[k - 1], &bits[k - 1]);
                    assert_eq!(bv.len(), x.meas.len());
                    if !AK_MBU_NEG { for (j, &v) in x.meas.iter().enumerate() { b.z_if(QubitId(m[v as usize]), bv[j]); } }
                    k -= 1;
                }
            }
            assert_eq!(k, 0, "p10 MBU: inverse walk missed a block");
        }
        if prof { fd2::builder::ptag(save); }
        let (_, c1, e1) = b.census();
        eprintln!("P5WALK inv list_ccx {} B_tof_delta {} census_ccx_delta {} census_exp_delta {:.1}",
                  fc.gates.iter().chain(fc.last.iter()).filter(|g| g.2 != NONE).count(), b.tof - tof0, c1 - c0, e1 - e0);
        for v in 512..fc.next as usize {
            b.free(QubitId(m[v]));
        }
    }
}
fn build_fd2() -> Vec<Op> {
    let fc = f_circuit();
    let mut b = fd2::builder::B::new();
    let mut w = MarkerWalk { fc, kept: vec![], nf: 0, ni: 0, mbu_bits: vec![] };
    fd2::pointadd_frogdrop::point_add_walk(&mut b, &mut w);
    assert!(w.kept.is_empty());
    let ops = fd2::finish(b);
    eprintln!("point_add: ops {} (P5SHELL: fd2 product stage around F)", ops.len());
    ops
}

// shadow: the exact Toffoli-pair folds and relocating product holds of the low-qubit lane (gate_fold.rs as in this
// tree, gate_fold2.rs and hold_idle.rs copied unchanged from odinfree's c0bcef05), applied to the finished stream.
mod gate_fold;
mod gate_fold2;
mod hold_idle;
/// RA_HP2 (port of 562e4e9's DEV_HP2, default off): after hold_idle, run hold_pass.rs's
/// flat-product + late-copy hold engine with its direct-CX rule (hold_pass.rs is 562e4e9's file; ours was byte-identical
/// to its parent 8396ec91 and never compiled). Clifford-only edits (X / CX / SWAP); relocation is fail-closed.
#[allow(dead_code)]
mod hold_pass;
const RA_HP2: bool = true;
#[allow(dead_code)]
mod peephole;
#[allow(dead_code)]
mod peephole_hook;
#[allow(dead_code)]
mod affine_simplify;
#[allow(dead_code)]
mod cond_pass;
#[allow(dead_code)]
mod quadratic_simplify;
#[allow(dead_code)]
mod truth_simplify;

fn r7d_counts(ops: &[Op]) -> (usize, u64, f64) {
    let (mut w, mut st, mut ccx, mut exp) = (1.0f64, Vec::<f64>::new(), 0u64, 0.0f64);
    for op in ops {
        match op.kind {
            OperationType::PushCondition => { st.push(w); w *= 0.5; }
            OperationType::PopCondition => { w = st.pop().expect("balanced condition stack"); }
            OperationType::CCX | OperationType::CCZ => {
                ccx += 1;
                exp += w * if op.c_condition == crate::circuit::NO_BIT { 1.0 } else { 0.5 };
            }
            _ => {}
        }
    }
    assert!(st.is_empty());
    (ops.len(), ccx, exp)
}

fn r7d_simp_round(mut ops: Vec<Op>, tag: &str) -> Vec<Op> {
    ops = affine_simplify::simplify(ops);
    eprintln!("R7D {tag} affine: {:?}", r7d_counts(&ops));
    ops = truth_simplify::simplify_products(ops);
    eprintln!("R7D {tag} truth: {:?}", r7d_counts(&ops));
    for r in 1..=3 {
        let (_, c0, _) = r7d_counts(&ops);
        ops = cond_pass::final_cap_cleanup(ops);
        let st = r7d_counts(&ops);
        eprintln!("R7D {tag} cond_cap_{r}: {:?}", st);
        if st.1 == c0 { break; }
    }
    ops
}

fn post_folds(ops: Vec<Op>) -> Vec<Op> {
    if r7d("HANDOFF_POSTPASS") {
        let mut ops = ops;
        eprintln!("R7D start: {:?}", r7d_counts(&ops));
        ops = if r7d("DEEP_FOLD") { peephole_hook::apply_deep(ops, 4) } else { peephole_hook::apply(ops) };
        eprintln!("R7D after_peep0: {:?}", r7d_counts(&ops));
        if r7d("SIMP_PRE") {
            ops = r7d_simp_round(ops, "pre");
        } else {
            ops = truth_simplify::simplify_products(ops);
            eprintln!("R7D pre truth_only: {:?}", r7d_counts(&ops));
        }
        ops = gate_fold::apply(ops);
        eprintln!("R7D after_gate_fold: {:?}", r7d_counts(&ops));
        if r7d("SIMP_MID") {
            ops = r7d_simp_round(ops, "mid");
        }
        ops = if r7d("DEEP_FOLD") { gate_fold2::apply_deep(ops, 4, 64) } else { gate_fold2::apply(ops, 3) };
        eprintln!("R7D after_gate_fold2: {:?}", r7d_counts(&ops));
        if r7d("SIMP_POST") {
            ops = r7d_simp_round(ops, "post");
        }
        if r7d("DEEP_FOLD") {
            ops = peephole_hook::apply_deep(ops, 3);
            eprintln!("R7D after_deep_peep: {:?}", r7d_counts(&ops));
            ops = gate_fold2::apply_deep(ops, 4, 64);
            eprintln!("R7D after_deep_gf2: {:?}", r7d_counts(&ops));
            ops = r7d_simp_round(ops, "deep_post");
        }
        if r7d("COND_US") {
            ops = cond_pass::run_levers(ops, "mufsr");
            eprintln!("R7D after_cond_mufsr: {:?}", r7d_counts(&ops));
            ops = peephole_hook::apply_deep(ops, 2);
            ops = gate_fold2::apply_deep(ops, 2, 64);
            eprintln!("R7D after_cond_refold: {:?}", r7d_counts(&ops));
        }
        let (ops, h) = hold_idle::apply_reloc(ops);
        eprintln!("R7D after_hold_idle holds={h}: {:?}", r7d_counts(&ops));
        if RA_HP2 {
            let (ops2, nh) = hold_pass::hold_pass_flat(ops, true);
            eprintln!("RA_HP2 flat+late holds={nh}: {:?}", r7d_counts(&ops2));
            return ops2;
        }
        return ops;
    }
    let ccx = |o: &Vec<Op>| o.iter().filter(|x| x.kind == OperationType::CCX).count();
    eprintln!("SHADOW start ccx={}", ccx(&ops));
    let ops = gate_fold::apply(ops);
    eprintln!("SHADOW gate_fold ccx={}", ccx(&ops));
    let ops = gate_fold2::apply(ops, 3);
    eprintln!("SHADOW gate_fold2 ccx={}", ccx(&ops));
    let (ops, h) = hold_idle::apply_reloc(ops);
    eprintln!("SHADOW hold_idle holds={h} ccx={}", ccx(&ops));
    ops
}
/// Fiat-Shamir tail: one identity X X pair per entry, on that qubit, appended after every pass. The op count does not
/// depend on the qubits, so a nonce search re-hashes only these ops. Empty = no tail (the parent's stream).
const TAIL_NONCE: &[u64] = &[1, 166, 492];
fn tail_nonce(mut ops: Vec<Op>) -> Vec<Op> {
    for &q in TAIL_NONCE {
        let mut x = Op::empty();
        x.kind = OperationType::X;
        x.q_target = QubitId(q);
        ops.push(x);
        ops.push(x);
    }
    ops
}
fn build_rowhunter_parent()->Vec<Op>{
    if P5SHELL {
        return tail_nonce(post_folds(build_fd2()));
    }
    let fc = f_circuit();
    let mut p = P { ops: Vec::with_capacity(190_000_000), free: vec![], next: 0, bits: 0 };
    let x = p.allocn(256);
    let y = p.allocn(256);
    let (ox, oy) = (0u64, 256u64);
    p.bits = 512;
    for r in 0..4u64 {
        let mut o = Op::empty();
        o.kind = OperationType::Register;
        o.r_target = RegisterId(r);
        p.ops.push(o);
    }
    for (r, lanes) in [(0u64, &x), (1u64, &y)] {
        for &a in lanes.iter() {
            let mut o = Op::empty();
            o.kind = OperationType::AppendToRegister;
            o.q_target = q(a);
            o.r_target = RegisterId(r);
            p.ops.push(o);
        }
    }
    for (r, base) in [(2u64, ox), (3u64, oy)] {
        for i in 0..256u64 {
            let mut o = Op::empty();
            o.kind = OperationType::AppendToRegister;
            o.c_target = BitId(base + i);
            o.r_target = RegisterId(r);
            p.ops.push(o);
        }
    }
    let w = CAPW;
    let mut a = S3 { dirty: y.clone(), zl: vec![] };
    a.cl_add(&mut p, &x, ox, true);
    a.dirty = x.clone();
    a.cl_add(&mut p, &y, oy, true);
    // division 1
    let (a1, k1) = emit_f(&mut p, &fc, &x, &y);
    a.dirty = [&a1[..255], &y[..256 - w]].concat();
    a.zl = p.allocn(ZL);
    let (lam, _low1, g) = a.product(&mut p, &a1[..255], &y, k1.xtop, a1[255], w);
    p.g(&g);
    drop(g);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    a.dirty = [&a1[..255], &y[..256 - w]].concat();
    let cg = a.cneg_list(&lam, k1.par, false, k1.xtop);
    p.g(&cg);
    let m1: Vec<u64> = y[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
    for &q0 in &y[..256 - w] {
        p.rel(q0);
    }
    emit_finv(&mut p, &fc, &x, &lam, &k1);
    // dy recompute
    let (c, ov) = (p.alloc(), p.alloc());
    a.zl = p.allocn(ZL);
    a.dirty = [&lam[..], &x[..256 - w]].concat();
    let (dy2, low2, g) = a.product(&mut p, &lam, &x, c, ov, w);
    p.g(&g);
    for i in 0..(256 - w) {
        p.zc(dy2[i], m1[i]);
    }
    p.g(&rev(&g));
    drop(g);
    for &q0 in &low2 {
        p.rel(q0);
    }
    p.rel(c);
    p.rel(ov);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    // x: dx' = lam^2 - dx - 3 ox
    let c2 = p.alloc();
    a.dirty = lam.clone();
    a.neg(&mut p, &x, c2);
    p.rel(c2);
    a.dirty = lam.clone();
    a.sq_into(&mut p, &x, &lam);
    for _ in 0..3 {
        a.dirty = lam.clone();
        a.cl_add(&mut p, &x, ox, true);
    }
    // y: ndy = -lam dx'; lam's top bits go on living inside it
    let (c, ov) = (p.alloc(), p.alloc());
    a.zl = p.allocn(ZL);
    a.dirty = [&x[..], &lam[..256 - w]].concat();
    let (ndy, _low4, g) = a.product(&mut p, &x, &lam, c, ov, w);
    p.g(&g);
    drop(g);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    p.rel(ov);
    a.neg(&mut p, &ndy, c);
    p.rel(c);
    let m2: Vec<u64> = lam[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
    for &q0 in &lam[..256 - w] {
        p.rel(q0);
    }
    // division 2
    let (a2, k2) = emit_f(&mut p, &fc, &x, &ndy);
    a.dirty = [&a2[..255 - w], &ndy[..]].concat();
    a.zl = p.allocn(ZL);
    let (l2, low5, g) = a.product(&mut p, &ndy, &a2[..255], k2.xtop, a2[255], w);
    p.g(&g);
    let cg = a.cneg_list(&l2, k2.par, true, k2.xtop);
    p.g(&cg);
    for i in 0..(256 - w) {
        p.zc(l2[i], m2[i]);
    }
    p.g(&rev(&cg));
    p.g(&rev(&g));
    drop(g);
    for &q0 in &low5 {
        p.rel(q0);
    }
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    emit_finv(&mut p, &fc, &x, &ndy, &k2);
    a.dirty = ndy.clone();
    a.cl_add(&mut p, &x, ox, false);
    a.dirty = x.clone();
    a.cl_add(&mut p, &ndy, oy, true);
    // move ndy onto the y register
    let mut cur = ndy.clone();
    for i in 0..256 {
        if cur[i] == y[i] {
            continue;
        }
        for j in (i + 1)..256 {
            if cur[j] == y[i] {
                cur[j] = cur[i];
                break;
            }
        }
        p.g(&[gc(cur[i], y[i]), gc(y[i], cur[i]), gc(cur[i], y[i])]);
        cur[i] = y[i];
    }
    eprintln!("point_add: ops {} peak qubits {}", p.ops.len(), p.next);
    p.ops
}

// v3 KT7 step 3: KT8 start machine (wide experiment)
#[allow(dead_code, unused)]
pub mod kt8;
// P5 shell (op-p5): the transplanted Track 2 builder + frogdrop product stage, used only when P5SHELL = true.
#[allow(dead_code, unused)]
pub mod fd2;

// v3 G2: window primitives (INV4 port from wt-q765-prims f5deab0, builder shim from wt-q765-v3-s1), not called by build(); tests only.
#[allow(dead_code, unused_imports)]
mod prims_builder;
#[allow(dead_code, unused_imports)]
mod window_prims;

/// Catalyst-swap hop for the K2 half (gate lists checked in a gate-level model).
mod hop2 {
    use super::prims_builder::{B, G};
    use super::window_prims::{self as wp, Cfg};
    use crate::circuit::QubitId as Q;
    /// R *= x for odd R and odd x; rb, xb = lanes of bits 1.. of each (bit 0 of both a known 1, never touched).
    pub fn imul_odd(b: &mut B, cf: Cfg, rb: &[Q], xb: &[Q], pool: &[Q]) {
        let n = rb.len() + 1;
        assert!(n >= 3 && xb.len() == n - 1);
        for i in (1..=n - 2).rev() {
            wp::cadd_p(b, cf, rb[i - 1], &xb[..n - i - 1], &rb[i..], pool);
        }
        wp::add_p(b, cf, &xb[..n - 1], rb, pool, None);
    }
    fn ccx(g: &[G]) -> usize { g.iter().filter(|e| matches!(e, G::Ccx(..))).count() }
    /// R *= K (K = 1 mod 4) as a product of (1 + 2^j)^(+-1) factors, cheapest signed plan by search (r2_inv.kmul).
    pub fn kmul(b: &mut B, cf: Cfg, r: &[Q], k: u64, pool: &[Q]) {
        let m = r.len();
        let mk: u64 = if m >= 64 { u64::MAX } else { (1u64 << m) - 1 };
        let k = k & mk;
        assert!(m < 2 || k % 4 == 1, "kmul needs K = 1 mod 4");
        let cost: Vec<usize> = (0..m).map(|j| if j >= 2 { ccx(&wp::rec(b, |b| wp::mul1p(b, cf, r, j, pool))) } else { 0 }).collect();
        let mulm = |a: u64, c: u64| -> u64 { ((a as u128 * c as u128) as u64) & mk };
        fn dfs(j0: usize, k: u64, m: usize, cost: &[usize], mulm: &dyn Fn(u64, u64) -> u64, plan: &mut Vec<(usize, bool)>, c: usize, best: &mut (Vec<(usize, bool)>, usize)) {
            if c >= best.1 { return; }
            let mut j = j0;
            while j < m && (k >> j) & 1 == 0 { j += 1; }
            if j >= m { *best = (plan.clone(), c); return; }
            let f = 1u64.wrapping_add(1u64 << j);
            plan.push((j, true));
            dfs(j + 1, mulm(k, wp::inv2k(f, m)), m, cost, mulm, plan, c + cost[j], best);
            plan.pop();
            plan.push((j, false));
            dfs(j + 1, mulm(k, f), m, cost, mulm, plan, c + cost[j], best);
            plan.pop();
        }
        let mut best: (Vec<(usize, bool)>, usize) = (vec![], usize::MAX);
        dfs(2, k, m, &cost, &mulm, &mut vec![], 0, &mut best);
        for &(j, fwd) in &best.0 {
            if fwd { wp::mul1p(b, cf, r, j, pool); } else { wp::undo(b, |b| wp::mul1p(b, cf, r, j, pool)); }
        }
    }
    /// x -> p / x in place (x odd), catalyst gd (len(x) - 1 dirty lanes). park: the third multiply is skipped, gd is
    /// left holding x g (the reversed gates give it back if x is the same word on the way out).
    pub fn cat_invp(b: &mut B, cf: Cfg, x: &[Q], gd: &[Q], pool: &[Q], p: u64, park: bool) {
        let xb = &x[1..];
        assert_eq!(gd.len(), xb.len());
        imul_odd(b, cf, xb, gd, pool);
        wp::undo(b, |b| imul_odd(b, cf, gd, xb, pool));
        if !park { imul_odd(b, cf, xb, gd, pool); }
        for (&a, &c) in xb.iter().zip(gd.iter()) { b.cx(a, c); b.cx(c, a); b.cx(a, c); }
        for &q in xb { b.x(q); }
        kmul(b, cf, x, p.wrapping_neg(), pool);
    }
    // ---------------- AKK2: 8396ec91 kernels (mod.rs hop2 of that row, verbatim; checked in Python)
    #[inline]
    fn cinc_2(b: &mut B, ctrl: Q, r0: Q, r1: Q) {
        b.ccx(ctrl, r0, r1);
        b.cx(ctrl, r0);
    }
    #[inline]
    fn ccinc_2(b: &mut B, c0: Q, c1: Q, r0: Q, r1: Q, z_clean: Q) {
        b.and_c(c0, c1, z_clean);
        b.ccx(z_clean, r0, r1);
        b.cx(z_clean, r0);
        b.and_u(c0, c1, z_clean);
    }
    /// AKK2_H1 (8396ec91 H1): Hensel 4+6 in-place invp11: x[0..11] -> (P256_LO * x^-1) mod 2048 for odd x (47 T one way).
    /// Requires 2 clean lanes cl = [z0, z1] (|0> in and out) and 1 dirty pool lane pool[0] (restored). x[0] is untouched.
    pub fn invp11(b: &mut B, cl: &[Q], x: &[Q], pool: &[Q]) {
        assert!(x.len() == 11 && cl.len() >= 2 && !pool.is_empty());
        let (a0, a1, a2, a3) = (x[1], x[2], x[3], x[4]);
        let t = &x[5..11];
        let (z0, z1) = (cl[0], cl[1]);
        let p0 = pool[0];

        // Stage 1 (9 T): t <- (M4(a) * t + 32 * t[0]) mod 64
        b.cx(a0, a1);
        wp::cadd_gidney(b, a1, &t[0..3], &t[3..6], &[z0, z1]);
        b.cx(a0, a1);

        b.cx(a0, a2); b.x(a2);
        wp::cadd_gidney(b, a2, &t[0..2], &t[4..6], &[z0]);
        b.x(a2); b.cx(a0, a2);

        b.cx(a1, a3); b.x(a3);
        b.ccx(a3, t[0], t[5]);
        b.x(a3); b.cx(a1, a3);

        // Stage 2 (18 T): t += C4_0(a0, a1, a2) mod 64
        b.and_c(a0, a1, z0);
        b.cx(a0, a1); b.and_c(a1, a2, z1); b.cx(a0, a1);

        cinc_2(b, z1, t[4], t[5]);
        b.x(t[5]); b.cx(a0, t[5]); b.cx(a2, t[5]); b.ccx(a2, z0, t[5]);

        let map_w = |b: &mut B| {
            b.cx(z1, a1);
            b.cx(a0, z1); b.cx(a2, z1); b.cx(z0, z1);
            b.cx(a1, a0);
            b.ccx(a2, z0, a0);
            b.ccx(a2, a0, z0); b.x(z0);
        };
        map_w(b);
        wp::add_ttk(b, &[z0, z1, a1, a0, p0], &t[0..5], Some(t[5]));
        wp::undo(b, |b| cinc_2(b, p0, t[4], t[5]));
        wp::undo(b, map_w);

        b.cx(a0, a1); b.and_u(a1, a2, z1); b.cx(a0, a1);
        b.and_u(a0, a1, z0);

        // Stage 3 (20 T, -2 precancelled -> 47 T total): t += a3 * D4(a0, a1, a2) mod 64 and a <- Y0_4(a)
        b.x(a1); b.ccx(a3, a1, t[5]); b.x(a1);

        b.cx(a2, a0); b.cx(a2, a1);
        b.and_c(a0, a1, z0);

        ccinc_2(b, a3, a1, t[4], t[5], z1);

        b.and_c(z0, t[0], z1);
        b.and_u(a0, a1, z0);
        b.cx(a0, a1);
        b.and_c(z1, t[1], z0);
        b.cx(a1, t[2]); b.cx(a1, z0); b.ccx(z0, t[2], a1);
        b.cx(a0, t[3]); b.cx(a0, a1); b.ccx(a1, t[3], a0);
        wp::cccx_dirty(b, a3, a0, t[4], t[5], a2);
        b.ccx(a3, a0, t[4]);
        b.ccx(a1, t[3], a0); b.cx(a0, t[3]); b.ccx(a3, a1, t[3]); b.cx(a0, a1);
        b.ccx(z0, t[2], a1); b.cx(a1, t[2]); b.ccx(a3, z0, t[2]); b.cx(a1, z0);
        b.and_u(z1, t[1], z0); b.ccx(a3, z1, t[1]);
        b.cx(a0, a1);
        b.and_c(a0, a1, z0);
        b.and_u(z0, t[0], z1); b.ccx(a3, z0, t[0]);

        b.cx(z0, a3);
        b.and_u(a0, a1, z0);
        b.cx(a2, a0);
        b.cx(a2, a1);
        b.cx(a0, a2); b.cx(a1, a2); b.x(a2);
        b.x(a0);
        b.x(a1);
    }
    /// AKK2_S2 (8396ec91 S2): R += a * y mod 2^n (= wp::mac without a pool) by the sign trick, a any parity:
    /// a y = sum_{i=0}^{n-2} 2^i (2 a_{i+1} - 1) y + 2^(n-1) y0 - (1 - a0) y (mod 2^n). Signed add i: negate R[i..] iff
    /// a_{i+1} = 0 (X, CX), uncontrolled add of y[..n-i], negate again; top: CX(y0 -> R[n-1]); parity: R -= (1 - a0) y by one
    /// cadd under X(a0). a and y read only. n = 11 with clean [z, z2], HYB: 91 + 29 = 120 T (mac 157).
    pub fn mac_sgn(b: &mut B, cf: Cfg, r: &[Q], a: &[Q], y: &[Q]) {
        let n = r.len();
        assert!(n >= 2 && a.len() >= n && y.len() >= n);
        fn neg(b: &mut B, c: Q, t: &[Q]) { for &q in t { b.x(q); b.cx(c, q); } }
        for i in 0..n - 1 {
            neg(b, a[i + 1], &r[i..]);
            wp::add(b, cf, &y[..n - i], &r[i..], None);
            neg(b, a[i + 1], &r[i..]);
        }
        b.cx(y[0], r[n - 1]);
        b.x(a[0]);
        wp::undo(b, |b| wp::cadd(b, cf, a[0], &y[..n], r));
        b.x(a[0]);
    }
    /// DS (dial768 piece 3): out ^= c0 c1 c2 c3 with two DIRTY lanes v1, v2 (restored): 10 CCX.
    fn c4x_dirty(b: &mut B, c0: Q, c1: Q, c2: Q, c3: Q, out: Q, v1: Q, v2: Q) {
        for _ in 0..2 {
            b.ccx(c3, v2, out);
            wp::cccx_dirty(b, c0, c1, c2, v2, v1);
        }
    }
    /// DS (dial768 piece 3): the 12-bit Hensel inverse x[0..12] -> (P256_LO * x^-1) mod 4096 for odd x, in place, derived from
    /// invp11 (model and derivation: lanes/dial768/h1/invp12_model.py). x = x0 + 32 b, x0 = 1 + 2a (a = x[1..5]), b = t = x[5..12]
    /// (7 bits): P / x = (K mod 32) + 32 [M(a) b + 32 (K mod 4) b0 + floor(K / 32)] mod 4096 with K = P / x0 mod 4096,
    /// M = -P x0^-2 mod 128 (the (32 b)^2 term survives as 1024 (c^2 mod 4) = 1024 c0, inside the 32 (K mod 4) b0 term).
    /// Stage 0: t6 ^= kappa'(a) = !a0 !a1 !a3 + a2 + a0 a1 a2 (bit 6 of the table, corrected for the 64-weight j(a) that
    /// his stages 2, 3 add). Stage 1: t *= (1+8)^(a0+a1) (1+16)^(1+a0+a2) (1+32)^(a1+a3) (1+64)^mu6 mod 128 and + 32 (K mod 4) b0
    /// (the mu6 and 64-weight terms fused: t6 ^= t0 (a2+a3)(1+a0+a1)). Stages 2, 3: his, with every increment of (t4, t5)
    /// carried on into t6 = x[11]. cl = [z0, z1] clean, pool >= 4 dirty lanes (restored). Exhaustive: dial_h1_12.
    pub fn invp12(b: &mut B, cl: &[Q], x: &[Q], pool: &[Q]) {
        assert!(x.len() == 12 && cl.len() >= 2 && pool.len() >= 4);
        let (a0, a1, a2, a3) = (x[1], x[2], x[3], x[4]);
        let t = &x[5..12];
        let t6 = t[6];
        let (z0, z1) = (cl[0], cl[1]);
        let (p0, d1, v1, v2) = (pool[0], pool[1], pool[2], pool[3]);
        let cf = Cfg { clean: &cl[..2], fast: false };
        // stage 0 (4 T): t6 ^= kappa'(a) from the original a
        b.x(a0); b.x(a1); b.and_c(a0, a1, z0); b.x(a1); b.x(a0);
        b.x(a3); b.ccx(z0, a3, t6); b.x(a3);
        b.x(a0); b.x(a1); b.and_u(a0, a1, z0); b.x(a1); b.x(a0);
        b.cx(a2, t6);
        b.and_c(a0, a1, z0); b.ccx(z0, a2, t6); b.and_u(a0, a1, z0);
        // stage 1: t *= M(a) mod 128, + 32 (K mod 4) t0
        b.cx(a0, a1);
        b.ccx(a1, t[3], t6);
        wp::cadd_p(b, cf, a1, &t[0..3], &t[3..7], pool);
        b.cx(a0, a1);
        b.cx(a0, a2); b.x(a2);
        wp::cadd(b, cf, a2, &t[0..3], &t[4..7]);
        b.x(a2); b.cx(a0, a2);
        b.cx(a1, a3);
        wp::cadd(b, cf, a3, &t[0..2], &t[5..7]);
        b.cx(a1, a3);
        b.ccx(t[0], t[5], t6); b.cx(t[0], t[5]);
        b.cx(a0, a1); b.x(a1); b.cx(a2, a3);
        b.and_c(a1, a3, z0); b.ccx(z0, t[0], t6); b.and_u(a1, a3, z0);
        b.cx(a2, a3); b.x(a1); b.cx(a0, a1);
        // stage 2 (his), top increments extended into t6
        b.and_c(a0, a1, z0);
        b.cx(a0, a1); b.and_c(a1, a2, z1); b.cx(a0, a1);
        wp::cccx_dirty(b, z1, t[4], t[5], t6, v1);
        cinc_2(b, z1, t[4], t[5]);
        b.cx(t[5], t6); b.x(t[5]);
        b.ccx(a0, t[5], t6); b.cx(a0, t[5]);
        b.ccx(a2, t[5], t6); b.cx(a2, t[5]);
        wp::cccx_dirty(b, a2, z0, t[5], t6, v1); b.ccx(a2, z0, t[5]);
        let map_w = |b: &mut B| {
            b.cx(z1, a1);
            b.cx(a0, z1); b.cx(a2, z1); b.cx(z0, z1);
            b.cx(a1, a0);
            b.ccx(a2, z0, a0);
            b.ccx(a2, a0, z0); b.x(z0);
        };
        map_w(b);
        wp::add_ttk(b, &[z0, z1, a1, a0, p0, d1], &t[0..6], Some(t6));
        wp::undo(b, |b| cinc_2(b, d1, t[5], t6));
        // his undo(cinc_2(p0, t4, t5)), one bit longer: (t4, t5, t6) -= p0
        b.cx(p0, t[4]); b.ccx(p0, t[4], t[5]); wp::cccx_dirty(b, p0, t[4], t[5], t6, v1);
        wp::undo(b, map_w);
        b.cx(a0, a1); b.and_u(a1, a2, z1); b.cx(a0, a1);
        b.and_u(a0, a1, z0);
        // stage 3 (his), top increments extended
        b.x(a1); b.and_c(a3, a1, z0); b.ccx(z0, t[5], t6); b.cx(z0, t[5]); b.and_u(a3, a1, z0); b.x(a1);
        b.cx(a2, a0); b.cx(a2, a1);
        b.and_c(a0, a1, z0);
        b.and_c(a3, a1, z1); wp::cccx_dirty(b, z1, t[4], t[5], t6, v1); b.ccx(z1, t[4], t[5]); b.cx(z1, t[4]); b.and_u(a3, a1, z1);
        b.and_c(z0, t[0], z1);
        b.and_u(a0, a1, z0);
        b.cx(a0, a1);
        b.and_c(z1, t[1], z0);
        b.cx(a1, t[2]); b.cx(a1, z0); b.ccx(z0, t[2], a1);
        b.cx(a0, t[3]); b.cx(a0, a1); b.ccx(a1, t[3], a0);
        c4x_dirty(b, a3, a0, t[4], t[5], t6, v1, v2);
        wp::cccx_dirty(b, a3, a0, t[4], t[5], a2);
        b.ccx(a3, a0, t[4]);
        b.ccx(a1, t[3], a0); b.cx(a0, t[3]); b.ccx(a3, a1, t[3]); b.cx(a0, a1);
        b.ccx(z0, t[2], a1); b.cx(a1, t[2]); b.ccx(a3, z0, t[2]); b.cx(a1, z0);
        b.and_u(z1, t[1], z0); b.ccx(a3, z1, t[1]);
        b.cx(a0, a1);
        b.and_c(a0, a1, z0);
        b.and_u(z0, t[0], z1); b.ccx(a3, z0, t[0]);
        b.cx(z0, a3);
        b.and_u(a0, a1, z0);
        b.cx(a2, a0);
        b.cx(a2, a1);
        b.cx(a0, a2); b.cx(a1, a2); b.x(a2);
        b.x(a0);
        b.x(a1);
    }
    /// DS (dial768 piece 4): H1 at D = 6..10, x[0..D] -> (P256_LO * x^-1) mod 2^D for odd x, in place: his invp11 restricted to
    /// the low D bits (model: lanes/dial768/h1/invp_lo_model.py). For D <= 10 the (32 b)^2 term vanishes and P / x mod 2^D is
    /// the low D bits of the 11-bit map. t = x[5..D] (k = D - 5 bits): every invp11 gate on a t lane >= k (control or target) is
    /// dropped; the adders run at their truncated widths ((1+8)^mu3 on k >= 4, (1+16)^mu4 on k = 5, no (1+32) / +32 b0 step;
    /// stage 2's add_ttk on k bits without carry-out). 11, 15, 20, 26, 32 T at D = 6..10. cl = [z0, z1] clean, pool[0] dirty.
    /// Exhaustive: dial_h1_lo.
    pub fn invp_lo(b: &mut B, cl: &[Q], x: &[Q], pool: &[Q]) {
        let d = x.len();
        assert!((6..=10).contains(&d) && cl.len() >= 2 && !pool.is_empty());
        let k = d - 5;
        let (a0, a1, a2, a3) = (x[1], x[2], x[3], x[4]);
        let tk = &x[5..d];
        let t: Vec<Option<Q>> = (0..6).map(|j| if j < k { Some(x[5 + j]) } else { None }).collect();
        let (z0, z1, p0) = (cl[0], cl[1], pool[0]);
        let cf = Cfg { clean: &cl[..2], fast: false };
        // gates on optional lanes: a gate with an absent (t >= k) lane is dropped
        let s = |q: Q| Some(q);
        fn x1(b: &mut B, a: Option<Q>) { if let Some(a) = a { b.x(a); } }
        fn cx1(b: &mut B, c: Option<Q>, t: Option<Q>) { if let (Some(c), Some(t)) = (c, t) { b.cx(c, t); } }
        fn ccx1(b: &mut B, c0: Option<Q>, c1: Option<Q>, t: Option<Q>) { if let (Some(c0), Some(c1), Some(t)) = (c0, c1, t) { b.ccx(c0, c1, t); } }
        fn andc1(b: &mut B, c0: Option<Q>, c1: Option<Q>, t: Option<Q>) { if let (Some(c0), Some(c1), Some(t)) = (c0, c1, t) { b.and_c(c0, c1, t); } }
        fn andu1(b: &mut B, c0: Option<Q>, c1: Option<Q>, t: Option<Q>) { if let (Some(c0), Some(c1), Some(t)) = (c0, c1, t) { b.and_u(c0, c1, t); } }
        // stage 1 (truncated)
        if k >= 4 {
            b.cx(a0, a1); wp::cadd(b, cf, a1, &tk[0..k - 3], &tk[3..k]); b.cx(a0, a1);
        }
        if k >= 5 {
            b.cx(a0, a2); b.x(a2); wp::cadd(b, cf, a2, &tk[0..k - 4], &tk[4..k]); b.x(a2); b.cx(a0, a2);
        }
        // stage 2 (his, restricted)
        b.and_c(a0, a1, z0);
        b.cx(a0, a1); b.and_c(a1, a2, z1); b.cx(a0, a1);
        ccx1(b, s(z1), t[4], t[5]); cx1(b, s(z1), t[4]);
        x1(b, t[5]); cx1(b, s(a0), t[5]); cx1(b, s(a2), t[5]); ccx1(b, s(a2), s(z0), t[5]);
        let map_w = |b: &mut B| {
            b.cx(z1, a1);
            b.cx(a0, z1); b.cx(a2, z1); b.cx(z0, z1);
            b.cx(a1, a0);
            b.ccx(a2, z0, a0);
            b.ccx(a2, a0, z0); b.x(z0);
        };
        map_w(b);
        let kw = k.min(5);
        let w5 = [z0, z1, a1, a0, p0];
        wp::add_ttk(b, &w5[..kw], &tk[..kw], t[5]);
        cx1(b, s(p0), t[4]); ccx1(b, s(p0), t[4], t[5]);
        wp::undo(b, map_w);
        b.cx(a0, a1); b.and_u(a1, a2, z1); b.cx(a0, a1);
        b.and_u(a0, a1, z0);
        // stage 3 (his, restricted)
        b.x(a1); ccx1(b, s(a3), s(a1), t[5]); b.x(a1);
        b.cx(a2, a0); b.cx(a2, a1);
        b.and_c(a0, a1, z0);
        b.and_c(a3, a1, z1); ccx1(b, s(z1), t[4], t[5]); cx1(b, s(z1), t[4]); b.and_u(a3, a1, z1);
        andc1(b, s(z0), t[0], s(z1));
        b.and_u(a0, a1, z0);
        b.cx(a0, a1);
        andc1(b, s(z1), t[1], s(z0));
        cx1(b, s(a1), t[2]); cx1(b, s(a1), s(z0)); ccx1(b, s(z0), t[2], s(a1));
        cx1(b, s(a0), t[3]); cx1(b, s(a0), s(a1)); ccx1(b, s(a1), t[3], s(a0));
        if let (Some(t4), Some(t5)) = (t[4], t[5]) { wp::cccx_dirty(b, a3, a0, t4, t5, a2); }
        ccx1(b, s(a3), s(a0), t[4]);
        ccx1(b, s(a1), t[3], s(a0)); cx1(b, s(a0), t[3]); ccx1(b, s(a3), s(a1), t[3]); cx1(b, s(a0), s(a1));
        ccx1(b, s(z0), t[2], s(a1)); cx1(b, s(a1), t[2]); ccx1(b, s(a3), s(z0), t[2]); cx1(b, s(a1), s(z0));
        andu1(b, s(z1), t[1], s(z0)); ccx1(b, s(a3), s(z1), t[1]);
        b.cx(a0, a1);
        b.and_c(a0, a1, z0);
        andu1(b, s(z0), t[0], s(z1)); ccx1(b, s(a3), s(z0), t[0]);
        b.cx(z0, a3);
        b.and_u(a0, a1, z0);
        b.cx(a2, a0);
        b.cx(a2, a1);
        b.cx(a0, a2); b.cx(a1, a2); b.x(a2);
        b.x(a0);
        b.x(a1);
    }
    /// DS: the PCONV close's cv as it stood inline in sandwich_x (moved verbatim): under c (r = VA odd whenever c = 1)
    /// SC <- VB - r SC, VA / VB read only; cfz = [z] clean. S3's cv_conj at 11 bits (at every width >= 3 with DS_K2_ALLW),
    /// else the cimul form.
    pub fn pconv_cv(b: &mut B, cfz: Cfg, qz2: Q, qa: &[Q], qb: &[Q], qc: &[Q], qp: &[Q]) {
        let wok = if super::DS_K2_ALLW { qb.len() >= 3 } else { qb.len() == 11 };
        if super::AK_PCONV_S3 && wok && qa.len() == qb.len() && qc.len() == qb.len() {
            cv_conj(b, cfz, cfz, qz2, qa, qb, qc, qp);
        } else {
            wp::cimul(b, cfz, qz2, qc, qa, qp);
            for &v in qb { b.x(v); }
            wp::cadd(b, cfz, qz2, qb, qc);
            for &v in qb { b.x(v); }
            for &s_ in qc { b.cx(qz2, s_); }
        }
    }
    /// the two parts of `hop`: (A, B) -> (A / B, p / B), then VB -= VA SC. Switches off: idiv; cat_invp; undo(mac), the parent.
    pub fn hop_ab(b: &mut B, cf: Cfg, va: &[Q], vb: &[Q], gd: &[Q], pool: &[Q], p: u64, park: bool) {
        if super::AKK2_X1 && cf.clean.len() >= 2 && va.len() >= 3 && vb.len() >= va.len() {
            wp::idiv_sgn2(b, cf, va, vb);
        } else {
            wp::idiv(b, cf, va, vb, pool);
        }
        if super::AKK2_H1 && vb.len() == 11 && p == wp::P256_LO && cf.clean.len() >= 2 && !pool.is_empty() {
            invp11(b, cf.clean, vb, pool);
        } else if super::AKK2_H1 && super::DS_K2_ALLW && vb.len() == 12 && p == wp::P256_LO && cf.clean.len() >= 2 && pool.len() >= 4 {
            invp12(b, cf.clean, vb, pool);
        } else if super::AKK2_H1 && super::DS_K2_ALLW && (6..=10).contains(&vb.len()) && p == wp::P256_LO && cf.clean.len() >= 2 && !pool.is_empty() {
            invp_lo(b, cf.clean, vb, pool);
        } else {
            cat_invp(b, cf, vb, gd, pool, p, park);
        }
    }
    pub fn hop_c(b: &mut B, cf: Cfg, va: &[Q], vb: &[Q], sc: &[Q], pool: &[Q]) {
        let wok = if super::DS_K2_ALLW { vb.len() >= 3 } else { vb.len() == 11 };
        if super::AKK2_S2 && wok && va.len() == vb.len() && sc.len() == vb.len() && cf.clean.len() >= 2 {
            wp::undo(b, |b| mac_sgn(b, cf, vb, va, sc));
        } else {
            wp::undo(b, |b| wp::mac(b, cf, vb, va, sc, pool));
        }
    }
    /// (A, B, tB) -> (A / B, tA, tB): the map of window_prims::k2_fwd with invp replaced by the catalyst swap.
    pub fn hop(b: &mut B, cf: Cfg, va: &[Q], vb: &[Q], sc: &[Q], gd: &[Q], pool: &[Q], p: u64, park: bool) {
        hop_ab(b, cf, va, vb, gd, pool, p, park);
        hop_c(b, cf, va, vb, sc, pool);
    }
    /// AK_PCONV_S3 (8396ec91 S3, verbatim): PCONV cv, under c (lane c; r = VA odd whenever c = 1): SC <- VB - r SC,
    /// VA / VB read only (restored). x~ = r1 ? -r : r = 1 mod 4 (CX(r1 -> VA[2..])); SC *= x~ under c top-down, step i adds
    /// (c & SC_i) (x~ >> 2) at SC[i+2..] (cc_add_p, AND on cf's clean lane z); then VB - r SC = r1 ? VB + W : ~(W + ~VB):
    /// X / CX(r1) on VB around the cadd and SC ^= ones iff c & !r1 (one AND on z). 157 T at n = 11 (cimul form 185).
    pub fn cv_conj(b: &mut B, cf: Cfg, cf_add: Cfg, c: Q, va: &[Q], vb: &[Q], sc: &[Q], pool: &[Q]) {
        let n = sc.len();
        assert!(n >= 3 && va.len() >= n && vb.len() == n && !cf.clean.is_empty());
        let z = cf.clean[0];
        let r1 = va[1];
        for k in 2..n { b.cx(r1, va[k]); }
        for i in (0..=n - 3).rev() {
            let k = n - 2 - i;
            wp::cc_add_p(b, cf, c, sc[i], &va[2..2 + k], &sc[i + 2..], pool);
        }
        for &v in vb { b.x(v); b.cx(r1, v); }
        wp::cadd(b, cf_add, c, vb, sc);
        for &v in vb { b.cx(r1, v); b.x(v); }
        b.x(r1); b.and_c(c, r1, z);
        for &s in sc { b.cx(z, s); }
        b.and_u(c, r1, z); b.x(r1);
        for k in 2..n { b.cx(r1, va[k]); }
    }
}

// S-D' P5: gate-list loader (Python lists replayed at fixed points of F; gl/gldump.py packs them).
mod gl_loader;
/// DS: unit tests of the dial code (cargo test --release --bin build_circuit -- dial_)
#[cfg(test)]
#[path = "ds_tests.rs"]
mod ds_tests;

mod ctx_hook;
pub fn build()->Vec<Op>{let parent=build_rowhunter_parent();ctx_hook::apply(parent,771)}
