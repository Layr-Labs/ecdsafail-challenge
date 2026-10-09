//! y15: the "one-fold" payload tick, forward and reverse. On in this entry; each step keeps its own switch below.
//!
//! Today a payload tick is three add-halve steps, each with its own fold. Here the three adds run with no fold
//! between them, X = T + S'0 + 2 S'1 + 4 S'2 as a 259-bit integer (S'i = the source or its 256-bit complement by
//! sign letter i), and one fold follows: bits [0, MW) of W = low(X) + E + (E - Nm - m)(f - 1), E = X >> 256,
//! Nm = s0 + 2 s1 + 4 s2, m = the quotient digit of 3 + e bits. The fold is the netlist of
//! experiments/y14-core/folds.py (`onefold_fwd`), gate for gate. The rotation by 3 + e is unchanged.
//!
//! The three top wires are erased from the three adds' own top carries (0 Toffoli): the last add's top ripple stays
//! open through the fold, and three carries of the first two adds are held (m0 = the carry into bit 255 of add 0,
//! m1 and h1 = the carries into the top two positions of add 1). m1 is erased with the cells' chunk compare on add 1's
//! sum bits (in the clear under the last add's open ripple); m0 needs add 0's sum bits, so add 1's carries are built
//! again on its window (Y15_GUARD bits below it) before the same compare.
//!
//! The reverse tick rotates up by 3 + e, flips the three letters and runs the same three adds and erases with the
//! reverse fold (folds.py `onefold_rev`). It is never used on tick 0 (see [`rev_on`]).
//!
//! y15-pack: this file holds the switches of both later studies, y15-core (smaller cores, kept low carries, joint
//! erase of m0 and m1) and y15-room (copies of W, measured clear, two lean wires, fused ticks); see Y15_KEEP_ROOM for
//! how a reverse tick-pass chooses between the kept carries and the copies, and for the builder counts.
use super::*;

/// Ticks [FROM, TO) of the payload-only forward passes run the one-fold tick. FROM = TO = 0: off.
/// Builder counts on candidate C1 (base 786219.5 x 1236), 9 October 2026:
///   FROM = 30, TO = 31 (one tick-pass):               expected=786170.5 peak=1236
///   FROM = 0,  TO = 76 (all 77 forward tick-passes):  expected=782360.5 peak=1236
///   the same with Y15_REV_FROM = 1, Y15_REV_TO = 76 (75 reverse tick-passes): expected=779916.5 peak=1236
/// y15-room: TO = 999 makes the range follow the boundary (pay_fwd_tick / pay_rev_tick are only reached by the
/// payload-only ticks). With LF_REORDER_DIV = 86 and LF_REORDER_MUL = 79: expected=779287.8 peak=1236 with
/// Y15_REV_COPY = false, expected=779014.8 peak=1236 with it true (same outputs on 270,720 shots). With
/// LF_REORDER_MUL = 81 and the copies: expected=778937.0; with Y15_REV_COPY_MBU as well: expected=778717.0 peak=1236.
pub(super) const Y15_FWD_FROM: usize = 0;
pub(super) const Y15_FWD_TO: usize = 999;
/// Ticks [FROM, TO) of the payload-only reverse passes run the reverse one-fold tick. FROM = TO = 0: off.
pub(super) const Y15_REV_FROM: usize = 1;
pub(super) const Y15_REV_TO: usize = 999;
/// Fold window (bits [0, MW) of the payload).
const Y15_WIN: usize = 56;
/// Bits below the compare window of m0 on which add 1's carries are built again.
const Y15_GUARD: usize = 0;
/// Research knob: bits added to every chunk-boundary compare of the tick (the cells' own shift is kept). 0 = as the cells.
const Y15_CMP_EXTRA: isize = 0;
/// y15-core (9 October 2026): three switches, all on. Builder counts at peak 1236, each on top of the one before:
///   all off (the folds and erases of y15-build, gate list 5a11e21c):          expected=779916.5
///   Y15_CORE_V2 (forward core 22 ANDs, reverse core 23, for 29 and 29):       expected=778436.5
///   Y15_KEEP_LOW = [5, 4, 3] (the reverse adds keep their low carries):       expected=777536.5
///   Y15_JOINT_M (the held carries m0 and m1 erased together):                 expected=776909.8
/// The first two give the same output as the base on every input; the third gives the same outputs and moves one
/// phase fix to a longer rebuilt chain on half the shots. Notes: experiments/y15-core in the Pensieve repo.
/// Y15_CORE_V2: the folds with the smaller cores (same window on every input); false = the folds of y15-build.
const Y15_CORE_V2: bool = true;
/// y16-core (9 October 2026): the addend's fields from k (forward) or n (reverse) by a searched XOR-AND program:
/// 14 ANDs for [`addend_from_k`]'s 15 and 12 for [`addend_from_n_rev`]'s 14, so the cores are 21 and 21 for 22 and 23.
/// Same forms on every reachable k and n (78 values each), hence the same window on every input of the fixed part
/// (netlist model, 262,144 forward and 1,048,576 reverse inputs, 0 wrong, 0 unclean). Needs Y15_CORE_V2.
/// false = the cores of y15-core. Notes: experiments/y16-core in the Pensieve repo (closure.c found the programs).
const Y16_CORE: bool = true;

/// y15-core, reverse tick only (needs Y15_CORE_V2): add i leaves its carries into its positions 1..=KEEP[i] on their
/// own wires and the reverse fold uses them as the borrows of its quotient recompute (the borrow into a bit of
/// `sum - S'` is the carry into that bit of `pre + S'`), so those ANDs are not built twice. [5, 4, 3] = all twelve;
/// [0, 0, 0] = off. The adds' chunk plans and boundary compares do not move (equal split while the room is 86 or
/// more for adds 0 and 1, 77 or more for add 2).
const Y15_KEEP_LOW: [usize; 3] = [5, 4, 3];
/// y15-core: erase the held carries m0 and m1 together. m0's fix already builds add 1's carries again on its window;
/// one step more gives m1's own value, so m1's chunk compare runs on a quarter of the shots and not a half. Same
/// outputs; m1's phase fix reads a 23-bit rebuilt chain in place of its 19-bit window on the shots where m0's branch
/// runs (not the same approximation as the base: see experiments/y15-core). false = each erased on its own.
const Y15_JOINT_M: bool = true;
/// Print one line a tick (costs by part, room, plans) to the build log. No effect on the gates.
const Y15_TRACE: bool = false;
/// y18 research price knob (0 = no effect on the gates): inside the body of every one-fold tick-pass the walk cap is
/// read this many wires higher. A non-zero value is a PRICE, never a build: the peak goes over 1236.
const Y18_PRICE: isize = 0;
/// y18-next (9 October 2026), "late tops": the three wires at the top of adds 0 and 1 (x256 = add 0's carry out of bit
/// 255; h1 and x257 = add 1's carries out of bits 255 and 256) are built after add 2's chunked part, just before its
/// open ripple, and not at the end of their own adds. Nothing between reads them: add 1's chunked part ends at bit 254
/// and add 2's below bit 232, and bit 255's two sums are written with them. The gates are the same (3 Toffoli, read
/// through forms of the source complemented by s2); add 1 sees 1 wire more and add 2 sees 3 more. Not on reverse tick
/// 0 (room 207). false: as entry U.
const Y18_LATE_TOPS: bool = true;
/// Research knob: with Y18_LATE_TOPS, idle wires held through adds 1 and 2 (1 and 3) so that they see the room they
/// have in U. The outputs must then be U's on every shot (the test that the move itself is an identity).
const Y18_LATE_PAD: bool = false;
/// y18-next: around the compare of m0's erase, up to Y15_GUARD - 1 "guard carries" of its rebuilt chain (the carries of
/// add 1 into the guard positions below the compare window; the window's forms do not read them, only the next carry's
/// erase does) are erased by measurement before the compare and built again after it: 1 Toffoli each on the half of
/// the shots where m0's branch runs. They are taken before cq(N - 3) (Y17_C3M, 1 Toffoli on every shot) and in place
/// of block carries where only m0's erase is short. The erase and rebuild are exact. false: off (as entry U).
const Y18_GSHED: bool = true;
/// Research knob: shed at least this many guard carries on every one-fold pass but reverse tick 0 (at most
/// Y15_GUARD - 1). With it set the outputs must not change.
const Y18_GSHED_MIN: usize = 0;
/// y18-next: where the fold is still short after the block and the three top wires, wires of its own that its ladder
/// does not read are erased by measurement before the ladder and built again after it (1 Toffoli each), in this order:
/// c2 and c1 (the carries into bits 2 and 1 of the low section acc[0..4) += E: only c3's build and the low section's
/// undo read them), then, forward only, the AND of the shift letter (only the erases of y3 and y5 read it). Up to
/// 3 forward and 2 in the reverse. false: off.
const Y18_FIN: bool = true;
/// Research knob: shed at least this many of the fold's own wires on every one-fold pass but reverse tick 0 (at most 3
/// forward, 2 reverse). With it set the outputs must not change.
const Y18_FIN_MIN: usize = 0;
/// y18-next, forward only: past those three (fin 4 to 6) the three top wires themselves leave for the ladder. The
/// forward fold reads E = (x256, x257, x258) only to build c1, c2, c3 and in its undo, so before the ladder the whole
/// erase of the top wires is run (measurements only: x258, the two top carries, x257, h1, x256; m0 and m1 stay), and
/// after the ladder all six are built again in the opposite order (6 Toffoli: 3 as the top carries cost today and 3
/// more). The top carries are then not shed before the fold. Wires of the state: fresh ids after [`esh_in`].
struct ESh {
    x256: QubitId,
    x257: QubitId,
    x258: QubitId,
    h1: QubitId,
    m0: QubitId,
    m1: QubitId,
    /// cq(N - 1), cq(N - 2), cq(N - 3)
    cq1: QubitId,
    cq2: QubitId,
    cq3: QubitId,
    /// tg[N - 1] (holds X1[255]) and the source's top three wires b[N - 1], b[N - 2], b[N - 3] (complemented by s2)
    t255: QubitId,
    b1: QubitId,
    b2: QubitId,
    b3: QubitId,
    s: [QubitId; 3],
}
impl ESh {
    /// (F1, F2): x257 = AND(F1, F2) ^ h1; (H1, H2): h1 = AND(H1, H2) ^ m1; (G1, G2): x256 = AND(G1, G2) ^ m0
    fn f(&self) -> (Lin, Lin) {
        (Lin::of(&[self.x256, self.b1, self.s[2], self.s[1]]), Lin::of(&[self.b1, self.s[2], self.s[1], self.h1]))
    }
    fn h(&self) -> (Lin, Lin) {
        (Lin::of(&[self.t255, self.b2, self.s[2], self.s[1]]), Lin::of(&[self.b2, self.s[2], self.s[1], self.m1]))
    }
    fn g(&self) -> (Lin, Lin) {
        (Lin::of(&[self.t255, self.b2, self.s[2], self.s[1], self.m1, self.b1, self.s[2], self.s[0]]), Lin::of(&[self.b1, self.s[2], self.s[0], self.m0]))
    }
}
/// Erase the six wires (the steps of the erase after the fold, in its order).
fn esh_out(c: &mut Builder, st: &ESh) {
    c.cx(st.cq1, st.x257);
    c.cx(st.b1, st.x257);
    c.cx(st.cq2, st.x256);
    c.cx(st.b2, st.x256);
    m_carry_erase(c, st.x258, st.x257, &l(st.b1), st.cq1);
    m_carry_erase(c, st.cq1, st.x256, &l(st.b2), st.cq2);
    m_carry_erase(c, st.cq2, st.t255, &l(st.b3), st.cq3);
    let (f1, f2) = st.f();
    c.cx(st.h1, st.x257);
    lin_and_erase(c, st.x257, &f1, &f2);
    lin_xor_into(c, &f2, st.x256); // x256 = X0[256]
    let (h1, h2) = st.h();
    c.cx(st.m1, st.h1);
    lin_and_erase(c, st.h1, &h1, &h2);
    let (g1, g2) = st.g();
    c.cx(st.m0, st.x256);
    lin_and_erase(c, st.x256, &g1, &g2);
}
/// Build the six wires again, in the opposite order (fresh wires).
fn esh_in(c: &mut Builder, st: &mut ESh) {
    let (g1, g2) = st.g();
    st.x256 = lin_and(c, &g1, &g2);
    c.cx(st.m0, st.x256);
    let (h1, h2) = st.h();
    st.h1 = lin_and(c, &h1, &h2);
    c.cx(st.m1, st.h1);
    let (_, f2) = st.f();
    lin_xor_into(c, &f2, st.x256); // x256 = X1[256]
    let (f1, f2) = st.f();
    st.x257 = lin_and(c, &f1, &f2);
    c.cx(st.h1, st.x257);
    st.cq2 = m_carry(c, st.t255, &l(st.b3), st.cq3);
    st.cq1 = m_carry(c, st.x256, &l(st.b2), st.cq2);
    st.x258 = m_carry(c, st.x257, &l(st.b1), st.cq1);
    c.cx(st.b2, st.x256);
    c.cx(st.cq2, st.x256);
    c.cx(st.b1, st.x257);
    c.cx(st.cq1, st.x257);
}
/// y18-next, trace only: the indices of the undo list's wires that no form of the addend reads (idle through the
/// ladder), with the indices of the records whose forms read each.
fn y18_idle(recs: &[Rec], add: &[Lin]) -> Vec<(usize, Vec<usize>)> {
    let read: Vec<QubitId> = add.iter().flat_map(|f| f.w.iter().copied()).collect();
    let wire = |r: &Rec| match r {
        Rec::And(q, _, _) | Rec::Maj(q, _, _, _) => Some(*q),
        _ => None,
    };
    let reads = |r: &Rec, q: QubitId| match r {
        Rec::And(_, a, b) => a.w.contains(&q) || b.w.contains(&q),
        Rec::Maj(_, a, b, ci) => a.w.contains(&q) || b.w.contains(&q) || ci.w.contains(&q),
        _ => false,
    };
    recs.iter()
        .enumerate()
        .filter_map(|(i, r)| wire(r).filter(|q| !read.contains(q)).map(|q| (i, recs.iter().enumerate().filter(|(_, o)| reads(o, q)).map(|(j, _)| j).collect())))
        .collect()
}
/// Replace wire `old` by `new` in every record of an undo list (a wire erased and built again is a fresh wire).
fn y18_subst(recs: &mut [Rec], old: QubitId, new: QubitId) {
    let fix = |f: &mut Lin| {
        for q in f.w.iter_mut() {
            if *q == old {
                *q = new;
            }
        }
    };
    for r in recs.iter_mut() {
        match r {
            Rec::And(q, a, b) => {
                if *q == old {
                    *q = new;
                }
                fix(a);
                fix(b);
            }
            Rec::Maj(q, a, b, ci) => {
                if *q == old {
                    *q = new;
                }
                fix(a);
                fix(b);
                fix(ci);
            }
            _ => {}
        }
    }
}
/// y18 trace: the detail lines the adds and compares left since the last call (chunk plans, each compare's cost).
fn y18_log() -> String {
    super::Y17_LOG.with(|l| l.borrow_mut().drain(..).collect::<Vec<_>>().join(" "))
}
pub(super) fn trace() -> bool {
    Y15_TRACE
}
/// y15-room: the reverse fold reads bits 2..5 of W from four copies taken before the three adds (W is in the clear
/// there) and builds its borrow chains only after the ladder, to clear the copies: the same 11 ANDs, 7 wires fewer
/// at the fold's peak, 4 more through the adds. false: the chains are built before the ladder (as y15-build).
const Y15_REV_COPY: bool = true;
/// y15-room: the copies are cleared by measurement, top bit first: a copy that measures 1 pays for the chains up to
/// its bit (and the lower copies are then cleared from the chains' forms); one that measures 0 pays nothing and the
/// next lower copy is measured. Expected ANDs 11/2 + 8/4 + 5/8 + 2/16 = 8.25 in place of 11. false: all 11, no
/// measurement.
const Y15_REV_COPY_MBU: bool = true;
/// y15-room: where the fold's ladder does not fit its room, the carries into bits 4 and 5 are erased before the ladder
/// (measured, 0 Toffoli) and built again after it: 2 ANDs for 2 wires, paid only on those ticks.
const Y15_LEAN45: bool = true;
/// y15-pack: with Y15_CORE_V2, Y15_KEEP_LOW and Y15_REV_COPY all on, the way a reverse tick-pass gets W's low bits is
/// chosen by its room (the walk cap less the wires live when the tick's body starts): the adds' kept carries (no AND,
/// 12 wires at the fold) where the room is Y15_KEEP_ROOM or more, the four CX copies (9.25 ANDs with the first
/// borrow, 5 wires) below it. 0 = kept carries on every tick; 9999 = copies on every tick.
/// 97 is the least room at which the kept form builds: the kept carries are live through the later adds, add 1 then
/// sees the room less 11 and holds its equal three-chunk split (and so a first chunk that takes the carry-in) only
/// at 86 or more. Room 97 is every payload-only reverse tick-pass and fused tick 76; fused ticks 77..86 take copies.
/// Builder counts at peak 1236, boundary 76 / 76, every switch of y15-core and y15-room on (9 October 2026):
///   Y15_KEEP_ROOM = 9999 (copies on every reverse tick-pass), window 56:  expected=775583.2
///   Y15_KEEP_ROOM = 97, window 56:                                        expected=775146.2 (gate list 0a4ac454;
///     same outputs as the y15-room head on 270,720 shots and on both stress files)
///   Y15_KEEP_ROOM = 97, window 57:                                        expected=775414.2 (gate list 1a6eef4a)
///   Y15_KEEP_ROOM = 87 or 0: does not build (the carry-in assert at room 88, the fold's ladder at room 86).
/// Known answers of the merge: all new switches off expected=779916.5 (5a11e21c); only y15-core's on
/// expected=776909.8 (17814295); only y15-room's on expected=778076.0 (32616b2f).
/// y18-next: with Y18_LATE_TOPS add 1 sees one wire more, so the kept form builds at room 96 (tick 77, 5.4 cheaper
/// than gate wires there); 92 to 95 do not build (add 1's own four kept carries count against its first chunk).
const Y15_KEEP_ROOM: usize = 96;

/// y15-room: fused ticks [FROM, TO) (above the boundary, rails and payload in one pass) whose three payload ops run
/// as one one-fold tick at the merged op's place. FROM = TO = 0: off. FROM = 0 follows the boundary. As built the
/// forward body fits down to room 82 (tick 89) and the reverse to room 88 (tick 85); with Y15_LEAN45 two wires
/// less (forward ticks 90 and 91, reverse tick 86).
/// With forward TO = 90, reverse TO = 86, LF_REORDER_DIV = 82, LF_REORDER_MUL = 79: expected=778177.0 peak=1236
/// (86 / 81: 778246.2; 84 / 81: 778186.8; 82 / 81: 778179.8; 80 / 81: 778184.2; 78 / 81: 778198.2; 82 / 77: 778182.5).
/// With the boundary left at the base's 76 / 76: expected=778228.8 peak=1236 (on the denominator stress file no
/// output differs from the base; a moved boundary changes the wrong answers of shots that are wrong on both sides).
/// With Y15_LEAN45, forward TO = 92 and reverse TO = 87: 76 / 76 expected=778076.0 peak=1236; 82 / 79
/// expected=778024.2 peak=1236.
/// y15-pack (every switch on, window 57, 76 / 76): the smaller cores free 7 wires forward and 6 reverse, so the body
/// fits on more fused ticks. Forward TO = 99 and reverse TO = 92 are the last that build (the ladder is at its least
/// budget at forward tick 98, room 73, and reverse tick 91, room 80; reverse TO = 93 does not fit):
///   forward TO = 92, reverse TO = 87 (the package, same ticks as y15-room): expected=775414.2 peak=1236 (1a6eef4a)
///   forward TO = 98, reverse TO = 91:                                       expected=774891.8 peak=1236
///   forward TO = 99, reverse TO = 92:                                       expected=774802.8 peak=1236 (e8b77f79)
/// The wider ranges do not give the same outputs as the package (12 more one-fold passes): on 30 draws 6 outputs
/// differ, 5 wrong only in the package and 1 wrong only at 99 / 92.
/// y16-late (9 October 2026, base = entry S, 774589.2 x 1236 with 99 / 92): with Y16_SHED the body fits further up.
/// Builder counts at peak 1236, window 57:
///   forward TO = 100, reverse TO = 92 (one pass more, 1 carry shed):          expected=774540.0 (gate list f83a4c61)
///   forward TO = 120, reverse TO = 92 (forward ticks 99..119, 1 to 24 shed):  expected=773521.8 (0f86ed19)
///   forward TO = 120, reverse TO = 109 (reverse ticks 92..108, 1 to 17 shed): expected=772961.0 (30c90c5f)
///   forward TO = 121, reverse TO = 109 (tick 120: block of 25 and the top carry): expected=772922.8 (bb2cedd9)
///   forward TO = 120, reverse TO = 114: expected=772876.0, but reverse ticks 109..113 save only 14 to 19.5 a pass.
/// A pass saves 36 to 65 forward and 21 to 40 reverse (the three-fold pass's chunk compares rise faster with less room
/// than the shed does). Forward TO = 122 does not build: at tick 121 (room 48) the fold lacks 27 wires and m0's erase
/// 26, against a block of 25 and the top carry. Reverse TO = 115 and beyond were not tried. Tick 137 has no forced
/// steps and cannot take the tick.
/// The new passes do not give the same outputs as 99 / 92: on 30 draws 9 outputs differ, 6 wrong only at 99 / 92 and
/// 3 wrong only here. The shed itself is an identity (forced on every pass: 0 outputs differ on 30 draws and on both
/// stress files).
/// y17-edge (9 October 2026, base = candidate T, 772220.8 x 1236 with 121 / 117). Builder counts at peak 1236, each on
/// top of the one before:
///   forward TO = 122 (tick 121: block 25, the top carry, and cq(N - 3) around the erases, Y17_C3M): expected=772178.5
///     (gate list 0cc0e6c7; same outputs as T on 270,720 shots)
///   reverse TO = 120 with Y17_LEAN on ticks 86..90, 104..109 and 114 up (no copies through the adds; ticks
///     117..119 fit with block 25 and 0, 1, 2 top wires):                                             expected=772020.1 (c1af7a1a)
///   Y17_REV0 (reverse tick 0, first two adds swapped):                                               expected=771952.9 (0a956ff8)
///   Y17_YGATE on the other copy ticks, Y17_LEAN on 86..89, 105..109, 115 up (the cheaper per tick): expected=771891.6 (ad88bda0)
/// Reverse ticks 117..119 with the copies would save +2, -3.5 and -5 (the three-fold pass falls at tick 117 while each
/// add of the one-fold body rises 2.5 a tick); without them the adds cost 298.0 flat from tick 110 to 117.
/// Forward tick 122 on and reverse tick 120 on belong to the three-fold passes (not tried here).
/// y18-next (10 October 2026, base = entry U, 771799.6 x 1236 with 122 / 120). The cells' compare window falls from 22
/// bits to 18 at tick 122 (17 at forward tick 129), so the one-fold body is cheap again past the old ranges while
/// the three-fold pass stays near 1500. Builder counts at peak 1236, each on top of the one before:
///   Y18_LATE_TOPS (ranges as U):                                                        expected=771640.1 (32fbd885)
///   Y18_GSHED, forward TO = 124, reverse TO = 122 (reverse 121 on gate wires):           expected=771495.9 (6edbc771)
///   Y18_FIN (fin 1 to 3), forward TO = 127, reverse TO = 124 (gate wires):               expected=771294.4
///   fin 4 to 6 (the top wires leave for the ladder), forward TO = 130:                   expected=771142.4
///   reverse form table refreshed (Y15_KEEP_ROOM 96, Y17_LEAN as below):                  expected=771131.0 (30288ff9)
/// A pass saves 46.8 to 64.7 forward (ticks 122..129) and 14.6 to 27.4 reverse (120..123). Forward TO = 131 needs a
/// seventh wire inside the fold and reverse TO = 125 a third (none found at about 1 Toffoli).
/// The new passes do not give U's outputs: on 30 draws 8 outputs differ, 6 wrong only in U, 1 wrong only here, 1 wrong
/// in both. The sheds are identities (forced on every pass: 0 outputs differ on 30 draws and on both stress files).
pub(super) const Y15_FUSED_FWD_FROM: usize = 0;
pub(super) const Y15_FUSED_FWD_TO: usize = 130;
pub(super) const Y15_FUSED_REV_FROM: usize = 0;
pub(super) const Y15_FUSED_REV_TO: usize = 124;
/// y16-late: where the fold does not fit the room left, a block of carries of add 2's open ripple (the carries into
/// its positions N - 3 - shed .. N - 4, just under the three the top wires are erased from) is erased before the fold
/// and built again only before the ripple is closed. The erase is measured (0 Toffoli: each carry is the majority of
/// wires that are all still live, taken top down), the rebuild is 1 Toffoli a carry, and nothing between reads them:
/// the fold reads the three top wires, the erase of the top wires reads the carries into the top three positions, and
/// the erases of m0 and m1 read add 1's sum bits (in the clear as long as add 2's sums are not written) and build
/// their own chains. The same shed block also makes room for m0's rebuilt chain and compare, which has no cap check
/// of its own and needs 3 k0 + 8 wires of room (68 at k0 = 20). As many are shed as the fold's ladder needs for its least
/// budget (10 at window 57, with the two wires of Y15_LEAN45) or m0's erase needs, no more: a wire for the ladder is worth 0.5
/// Toffoli, a shed carry costs 1. false: off (the ranges below must then end at 99 / 92).
/// Where the block is all shed and the fold still lacks one wire, the carry into the top position (cq(N - 1)) is shed
/// around the fold alone: erased before it, built again right after it (the erase of the top wires reads it).
const Y16_SHED: bool = true;
/// Research knob: shed at least this many carries on every one-fold tick-pass (0 = only where needed). With it set,
/// the outputs must not change (the test of the shed and rebuild).
const Y16_SHED_MIN: usize = 0;
/// Research knob: shed the top carry around the fold on every one-fold tick-pass that sheds at all (same test).
const Y16_TOP_ALWAYS: bool = false;
/// Wires the fold holds beside its ladder's carries (Y15_CORE_V2): forward 6 low carries, 4 gate wires, 22 core ANDs;
/// reverse with copies 6 low carries, 4 gate wires, the first borrow, 23 core ANDs.
/// With the searched cores of Y16_CORE (21 and 21 ANDs) the fold holds 1 wire less forward and 2 less in the reverse.
const Y16_FIXED_FWD: usize = if Y16_CORE { 31 } else { 32 };
const Y16_FIXED_REV_COPY: usize = if Y16_CORE { 32 } else { 34 };
/// y17-edge (9 October 2026): wires beyond the block, each erased by measurement and built again for 1 Toffoli.
/// Around the fold alone (`tops`, in this order): the carry into the top position cq(N - 1) (y16-late), the carry
/// below it cq(N - 2), and add 1's held top carry h1. None is read by the fold; each is built again right after it,
/// before the erase of the top wires reads it. Y17_TOPS_MAX = 1: as y16-late.
const Y17_TOPS_MAX: usize = 3;
/// y17-edge: around the erases of m0 and m1 alone, the last ripple carry left, cq(N - 3). The erase of the top wires
/// has read it by then, and its own inputs are shed, so it is measured with the phase fix put off: the bit is kept,
/// and when the block is built again the carry is built again (1 Toffoli) and takes a Z under the bit. false: off.
const Y17_C3M: bool = true;
/// Research knobs: on every one-fold tick-pass that may shed (forward, and reverse with copies or lean chains), shed
/// at least this many top wires around the fold, and cq(N - 3) around the erases. With them set the outputs must not
/// change.
const Y17_TOPS_MIN: usize = 0;
const Y17_C3M_ALWAYS: bool = false;
/// y17-edge: reverse fused ticks in these ranges [from, to) take W's bits 2..5 with no copy held through the adds
/// (the "lean chains" of [`fold_rev_v2`]): the three borrow chains are built inside the fold before its ladder
/// (11 ANDs past the first borrow), the three gate wires y3, y4, y5 read them, and the nine borrows above bit 2 are
/// erased again by measurement before the ladder; only the two borrows into bit 2 stay (W's bit 2 is read through
/// the ladder). After the ladder y5, y4, y3 are cleared by measurement, top first: one that measures 1 pays for the
/// chains up to its bit (9, 6, 3 ANDs), one that measures 0 pays nothing: 6.375 expected. In all 18.375 expected ANDs
/// with the first borrow against the copies' 9.25, two wires fewer at the fold's peak, and four wires more for each
/// of the three adds. Empty: off (copies on every tick below Y15_KEEP_ROOM).
/// Measured against the copies, a pass (builder, 9 October 2026): 8.1 dearer at ticks 77..81 and 7.2 dearer at
/// 96..100; cheaper by 3.4, 5.3, 5.4, 3.9, 1.4 at ticks 86..90, by 2.4, 7.3, 10.9, 11.9, 11.9, 8.4 at 104..109 and by
/// 1.9, 9.4, 15.4 at 114..116. The ranges below are where it also beats (or ties) Y17_YGATE.
/// Identity test (Y17_LEAN_PAD = 4 on ticks 77..116): 0 outputs differ from the copies on 270,720 shots.
/// y18-next: priced again per tick on Y18_LATE_TOPS (three traces): gate wires are now cheaper than lean at ticks 89,
/// 105, 115, 116 (0.5, 1.5, 3.5, 0.5); lean stays on 117..120 (gate wires are 5.5, 5.5, 4.0, 2.0 dearer); from tick 121
/// the reverse pass takes gate wires (lean lacks 1 wire at the fold at tick 121).
const Y17_LEAN: &[(usize, usize)] = &[(86, 89), (106, 110), (117, 121)];
/// Research knob: idle wires held through the three adds of a lean tick-pass (4 = the adds see the room they have
/// with the copies; the outputs must then be those of the copies).
const Y17_LEAN_PAD: usize = 0;
fn lean_on(t: usize) -> bool {
    Y17_LEAN.iter().any(|&(a, b)| t >= a && t < b)
}
/// y17-edge: reverse fused ticks in these ranges [from, to) hold the three gate wires y3, y4, y5 through the adds in
/// place of the four copies ("gate wires first"): they are ANDs of the shift letter with W's bits 3..5, built while W
/// is in the clear (the fold builds the same three ANDs from the copies today). The fold then needs no copy and no
/// chain above bit 2 before its ladder: only the two borrows into bit 2. After the ladder the gate wires are cleared
/// as in the lean form. 14.375 expected ANDs for the copies' 13.25 (gate wires counted on both sides), three wires
/// fewer at the fold's peak, one wire more for each add. A tick in Y17_LEAN takes the lean form. Empty: off.
/// Measured against the copies, a pass (builder): 0.3 to 4.9 cheaper on every tick 77..113 tried. Against the lean
/// form: cheaper by 0.5, 3.5, 5.0 at ticks 90, 104, 114; equal at 86, 105, 115; dearer by 1.5 to 10 elsewhere.
const Y17_YGATE: &[(usize, usize)] = &[(77, 999)];
/// Research knob: idle wires held through the three adds of a gate-wires-first tick-pass (1 = the adds see the room
/// they have with the copies).
const Y17_YGATE_PAD: usize = 0;
fn ygate_on(t: usize) -> bool {
    Y17_YGATE.iter().any(|&(a, b)| t >= a && t < b)
}
/// Wires the reverse fold holds beside its ladder's carries with the gate wires built first: no AND of the shift
/// letter and no gate wire of its own (4 fewer), the two borrows into bit 2.
const Y17_FIXED_REV_YGATE: usize = Y16_FIXED_REV_COPY - 2;
/// Wires the reverse fold holds beside its ladder's carries in the lean form: those of the copies' form and the two
/// borrows into bit 2 (and no copies outside the fold).
const Y17_FIXED_REV_LEAN: usize = Y16_FIXED_REV_COPY + 2;
/// The number of carries to shed before the fold: (the block, the top wires around the fold alone: 0 to 3, cq(N - 3)
/// around the erases of m0 and m1: 0 or 1).
/// `room_fold`: the room now (add 2's ripple open, the sums of the two lower top wires written); `room_m`: the room
/// m0's erase will have with nothing shed; `need_m`: what it takes (its rebuilt chain and its compare); `pool`: the
/// carries of the block; `fixed`: the wires the fold holds beside its ladder's carries.
#[allow(clippy::too_many_arguments)]
fn y16_shed(on: bool, fixed: usize, room_fold: usize, room_m: usize, need_m: usize, pool: usize, fmax: usize) -> (usize, usize, usize, usize, usize) {
    if !Y16_SHED || !Y15_CORE_V2 || !Y15_JOINT_M || !on {
        return (0, 0, 0, 0, 0);
    }
    // the ladder's least budget on bits [6, MW): 10 at window 57 (as [`fold_plan`] finds it)
    let nbits = Y15_WIN - 6;
    let min_budget = (1..=nbits).find(|&b| merged_plan(nbits - 1, b).is_some() || merged_plan(nbits, b).is_some()).expect("y16: a ladder budget");
    let need = fixed + min_budget - 2 * usize::from(Y15_LEAN45);
    let (short_f, short_m) = (need.saturating_sub(room_fold), need_m.saturating_sub(room_m));
    // y18-next: the guard carries of m0's rebuilt chain come first for its erase (see Y18_GSHED)
    let gmax = if Y18_GSHED { Y15_GUARD.saturating_sub(1) } else { 0 };
    let block = short_f.max(short_m.saturating_sub(gmax)).max(Y16_SHED_MIN).min(pool);
    // y18-next: past the three top wires the fold sheds wires of its own (see Y18_FIN)
    let fmax = if Y18_FIN { fmax } else { 0 };
    let rest_f = short_f - short_f.min(block);
    let fin = rest_f - rest_f.min(Y17_TOPS_MAX);
    let tops = (rest_f - fin).max(usize::from(Y16_TOP_ALWAYS && block > 0)).max(Y17_TOPS_MIN);
    let rest = short_m - short_m.min(block);
    let gsh = rest.min(gmax);
    let c3m = (rest - gsh).max(usize::from(Y17_C3M_ALWAYS));
    assert!(
        rest - gsh <= usize::from(Y17_C3M) && fin <= fmax && tops <= 3 && c3m <= 1,
        "y16: the room is too small: fold short of {short_f} (room {room_fold}, need {need}), m0's erase short of {short_m} (room {room_m}, need {need_m}), block {pool} + {Y17_TOPS_MAX} + {fmax} for the fold, + {gmax} + {} for the erase",
        usize::from(Y17_C3M)
    );
    (block, tops, c3m, gsh, fin)
}

pub(super) fn fused_fwd_on(t: usize) -> bool {
    t >= Y15_FUSED_FWD_FROM && t < Y15_FUSED_FWD_TO
}
pub(super) fn fused_rev_on(t: usize) -> bool {
    t >= Y15_FUSED_REV_FROM.max(1) && t < Y15_FUSED_REV_TO
}

pub(super) fn fwd_on(t: usize) -> bool {
    t >= Y15_FWD_FROM && t < Y15_FWD_TO
}
/// Tick 0 is never run in the reverse one-fold form with the adds in the order 1, 2, 4: there the payload registers
/// hold P0 = 2 P1 (mod p), and the register before the second add is (2 + 2 a + 4 b) P1 with a, b = +-1, which is
/// 0 (mod p) for one sign pair in four. That add's windowed compares then tie and fall back on their seed bits
/// (measured by y15-build: phase errors on 13% of shots).
/// y17-edge: with Y17_REV0 the reverse tick runs on tick 0 with its first two adds in the other order (2, 1, 4): the
/// registers before the second and third add are then (7, 5, -1, -3) P1 and (6, -2) P1, never 0 (mod p).
pub(super) fn rev_on(t: usize) -> bool {
    (t >= Y15_REV_FROM.max(1) && t < Y15_REV_TO) || (t == 0 && Y17_REV0)
}
/// y17-edge: the reverse one-fold tick on tick 0, its first two adds swapped (see [`rev_on`] and `swap01` in
/// [`body`]). false: tick 0 keeps today's three-fold reverse pass.
const Y17_REV0: bool = true;

/// Trace of a tick on today's ops (for the per-tick comparison).
pub(super) fn trace_old(c: &Builder, t: usize, e0: f64, a0: u32) {
    if Y15_TRACE {
        eprintln!("Y15_OLD fwd t={t} active={a0} room={} cost={:.1}", cells::cap().saturating_sub(a0 as usize), c.expected_total() - e0);
    }
}
pub(super) fn trace_old_rev(c: &Builder, t: usize, e0: f64, a0: u32) {
    if Y15_TRACE {
        eprintln!("Y15_OLD rev t={t} active={a0} room={} cost={:.1}", cells::cap().saturating_sub(a0 as usize), c.expected_total() - e0);
    }
}

fn l(q: QubitId) -> Lin {
    Lin::of(&[q])
}

/// MAJ(x, y, ci) = AND(x ^ ci, y ^ ci) ^ ci on a fresh wire (one Toffoli), and its measured erase.
fn maj_wire(c: &mut Builder, x: &Lin, y: &Lin, ci: &Lin) -> QubitId {
    let (a, b) = (x.x(ci), y.x(ci));
    let q = lin_and(c, &a, &b);
    lin_xor_into(c, ci, q);
    q
}
fn maj_wire_erase(c: &mut Builder, q: QubitId, x: &Lin, y: &Lin, ci: &Lin) {
    let (a, b) = (x.x(ci), y.x(ci));
    lin_xor_into(c, ci, q);
    lin_and_erase(c, q, &a, &b);
}

/// Undo list of the fold's helper wires (erased in reverse order).
enum Rec {
    /// wire, and the two forms whose AND it holds at the erase point
    And(QubitId, Lin, Lin),
    /// wire = AND(a, b) ^ ci
    Maj(QubitId, Lin, Lin, Lin),
    /// erase the carry into bit 5 and write bit 4
    UndoC5,
    /// erase the carry into bit 6 and write bit 5
    UndoC6,
}
fn r_and(c: &mut Builder, recs: &mut Vec<Rec>, a: Lin, b: Lin) -> Lin {
    let q = lin_and(c, &a, &b);
    recs.push(Rec::And(q, a, b));
    l(q)
}
fn r_and_e(c: &mut Builder, recs: &mut Vec<Rec>, a: Lin, b: Lin, ea: Lin, eb: Lin) -> Lin {
    let q = lin_and(c, &a, &b);
    recs.push(Rec::And(q, ea, eb));
    l(q)
}
fn r_maj(c: &mut Builder, recs: &mut Vec<Rec>, x: Lin, y: Lin, ci: Lin) -> Lin {
    let (a, b) = (x.x(&ci), y.x(&ci));
    let q = lin_and(c, &a, &b);
    lin_xor_into(c, &ci, q);
    recs.push(Rec::Maj(q, a, b, ci));
    l(q)
}

/// Forms of bits [0, mw) of (f - 1) n mod 2^mw from n's 8 bits (two's complement, n in [-70, 7]); 19 ANDs.
/// 61 n = Q + 64 n with Q = n - 4 n; bits 4..9 = Q0..Q5; bits 10..16 = U = n + (Q >> 6); bits 17..31 = s = n7;
/// bits 32..38 = n - s; bits 39.. = s. (folds.py `addend_from_n`.)
fn addend_from_n(c: &mut Builder, recs: &mut Vec<Rec>, n: &[Lin], mw: usize) -> Vec<Lin> {
    let one = Lin::k(true);
    let s = n[7].clone();
    let mut q = vec![n[0].clone(), n[1].clone(), n[2].x(&n[0])];
    let mut d = r_and(c, recs, n[2].x(&one), n[0].clone());
    for i in 3..9 {
        let ni = if i < 8 { n[i].clone() } else { n[7].clone() };
        q.push(ni.x(&n[i - 2]).x(&d));
        d = r_maj(c, recs, ni.x(&one), n[i - 2].clone(), d);
    }
    q.push(d);
    let j = [q[6].clone(), q[7].clone(), q[8].clone(), q[9].clone()];
    let mut u = vec![n[0].x(&j[0])];
    let mut e = r_and(c, recs, n[0].clone(), j[0].clone());
    for i in 1..7 {
        let ji = if i < 4 { j[i].clone() } else { j[3].clone() };
        u.push(n[i].x(&ji).x(&e));
        if i < 6 {
            e = r_maj(c, recs, n[i].clone(), ji, e);
        }
    }
    let mut h = vec![n[0].x(&s)];
    let mut z = r_and(c, recs, n[0].x(&one), s.clone());
    for i in 1..7 {
        h.push(n[i].x(&z));
        if i < 6 {
            z = r_and(c, recs, n[i].x(&one), z);
        }
    }
    (0..mw)
        .map(|b| match b {
            0..=3 => Lin::k(false),
            4..=9 => q[b - 4].clone(),
            10..=16 => u[b - 10].clone(),
            17..=31 => s.clone(),
            32..=38 => h[b - 32].clone(),
            _ => s.clone(),
        })
        .collect()
}

/// The upper ladder of [`m_fold`] from bit `lo0` with carry-in `cin0`: acc[lo0..) += add[lo0..) + cin0 (mod 2^len),
/// in chunks; a non-final chunk keeps its carry-out, erased at the end by an exact compare on half the shots.
fn ladder(c: &mut Builder, acc: &[QubitId], add: &[Lin], lo0: usize, cin0: QubitId, plan: &[usize]) {
    let mw = acc.len();
    assert_eq!(plan.iter().sum::<usize>(), mw - lo0, "y15 fold plan covers bits [lo, MW)");
    let mut kept: Vec<(usize, usize, QubitId, QubitId)> = Vec::new();
    let (mut lo, mut cin) = (lo0, cin0);
    for (j, &w) in plan.iter().enumerate() {
        let hi = lo + w;
        let last = j + 1 == plan.len();
        let direct = last && w >= 2;
        let mut cc = vec![cin];
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
        assert!(c.active_qubits() as usize <= cells::cap(), "y15 fold over the walk cap: {} > {}", c.active_qubits(), cells::cap());
        for i in (lo..hi).rev() {
            lin_xor_into(c, &add[i], acc[i]);
            if direct && i == hi - 1 {
                continue;
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
}

/// The fold of the forward one-fold tick (folds.py `onefold_fwd`): acc = bits [0, MW) of low(X), e = the three top
/// wires, nm = the three sign letters (1 = that add took the complemented source), k1, k2 the shift letter.
/// 39 fixed wires (6 low carries, 4 gate wires, 29 core ANDs) plus the ladder's carries. Returns the ladder's plan.
fn fold_fwd(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], nm: [QubitId; 3], k1: QubitId, k2: QubitId) -> Vec<usize> {
    let mw = acc.len();
    let one = Lin::k(true);
    // low section: acc[0..4) += E, sums left pending
    let c1 = lin_and(c, &l(acc[0]), &l(e[0]));
    let c2 = maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1));
    let c3 = maj_wire(c, &l(acc[2]), &l(e[2]), &l(c2));
    let c4 = lin_and(c, &l(acc[3]), &l(c3));
    let v = [Lin::of(&[acc[0], e[0]]), Lin::of(&[acc[1], e[1], c1]), Lin::of(&[acc[2], e[2], c2]), Lin::of(&[acc[3], c3])];
    let mut recs: Vec<Rec> = Vec::new();
    let tt = r_and(c, &mut recs, l(k1), l(k2));
    let g1 = Lin::of(&[k1, k2]).x(&tt);
    // D = E - Nm, 4 bits two's complement
    let mut bw = r_and(c, &mut recs, l(e[0]).x(&one), l(nm[0]));
    let mut d = vec![Lin::of(&[e[0], nm[0]]), Lin::of(&[e[1], nm[1]]).x(&bw)];
    bw = r_maj(c, &mut recs, l(e[1]).x(&one), l(nm[1]), bw);
    d.push(Lin::of(&[e[2], nm[2]]).x(&bw));
    bw = r_maj(c, &mut recs, l(e[2]).x(&one), l(nm[2]), bw);
    d.push(bw);
    let y3 = r_and(c, &mut recs, g1, v[3].clone());
    let y = [v[0].clone(), v[1].clone(), v[2].clone(), y3];
    // n = D - y, bits 0..3
    let mut n = vec![d[0].x(&y[0])];
    let mut g = r_and(c, &mut recs, d[0].x(&one), y[0].clone());
    for i in 1..4 {
        n.push(d[i].x(&y[i]).x(&g));
        g = r_maj(c, &mut recs, d[i].x(&one), y[i].clone(), g);
    }
    // bits 4 and 5 of the ladder first: their sums are the quotient's bits 4 and 5
    let (a4, a5) = (n[0].clone(), n[1].clone());
    let sum4 = Lin::of(&[acc[4], c4]).x(&a4);
    let y4 = r_and_e(c, &mut recs, l(k2), sum4, l(k2), l(acc[4]));
    let c5 = maj_wire(c, &l(acc[4]), &a4, &l(c4));
    recs.push(Rec::UndoC5);
    let sum5 = Lin::of(&[acc[5], c5]).x(&a5);
    let y5 = r_and_e(c, &mut recs, tt.clone(), sum5, tt.clone(), l(acc[5]));
    let c6 = maj_wire(c, &l(acc[5]), &a5, &l(c5));
    recs.push(Rec::UndoC6);
    for yi in [y4, y5] {
        n.push(d[3].x(&yi).x(&g));
        g = r_maj(c, &mut recs, d[3].x(&one), yi, g);
    }
    n.push(d[3].x(&g));
    let g7 = r_and(c, &mut recs, d[3].x(&one), g);
    n.push(d[3].x(&g7));
    let add = addend_from_n(c, &mut recs, &n, mw);
    // the ladder on bits [6, MW), split to the room left
    let budget = cells::cap().saturating_sub(c.active_qubits() as usize);
    let nbits = mw - 6;
    let lean45 = Y15_LEAN45 && merged_plan(nbits - 1, budget).is_none() && merged_plan(nbits, budget).is_none();
    if lean45 {
        maj_wire_erase(c, c5, &l(acc[4]), &a4, &l(c4));
        lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    }
    let budget = budget + 2 * usize::from(lean45);
    let plan = match merged_plan(nbits - 1, budget) {
        Some(mut p) => {
            *p.last_mut().unwrap() += 1;
            p
        }
        None => merged_plan(nbits, budget).unwrap_or_else(|| panic!("y15: the fold's ladder does not fit: budget {budget}, active {}, cap {}", c.active_qubits(), cells::cap())),
    };
    ladder(c, acc, &add, 6, c6, &plan);
    let (c4, c5) = if lean45 {
        let c4 = lin_and(c, &l(acc[3]), &l(c3));
        let c5 = maj_wire(c, &l(acc[4]), &a4, &l(c4));
        (c4, c5)
    } else {
        (c4, c5)
    };
    while let Some(r) = recs.pop() {
        match r {
            Rec::And(q, a, b) => lin_and_erase(c, q, &a, &b),
            Rec::Maj(q, a, b, ci) => {
                lin_xor_into(c, &ci, q);
                lin_and_erase(c, q, &a, &b);
            }
            Rec::UndoC6 => {
                maj_wire_erase(c, c6, &l(acc[5]), &a5, &l(c5));
                lin_xor_into(c, &a5, acc[5]);
                c.cx(c5, acc[5]);
            }
            Rec::UndoC5 => {
                maj_wire_erase(c, c5, &l(acc[4]), &a4, &l(c4));
                lin_xor_into(c, &a4, acc[4]);
                c.cx(c4, acc[4]);
            }
        }
    }
    // low section undo
    lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    c.cx(c3, acc[3]);
    maj_wire_erase(c, c3, &l(acc[2]), &l(e[2]), &l(c2));
    c.cx(e[2], acc[2]);
    c.cx(c2, acc[2]);
    maj_wire_erase(c, c2, &l(acc[1]), &l(e[1]), &l(c1));
    c.cx(e[1], acc[1]);
    c.cx(c1, acc[1]);
    lin_and_erase(c, c1, &l(acc[0]), &l(e[0]));
    c.cx(e[0], acc[0]);
    plan
}

/// Forms of W mod 64 = (low(X_r) - 4 S2' - 2 S1' - S0') mod 64 by three borrow chains (11 ANDs past the shared
/// first borrow `b01` for `top` = 5); acc[0..6) must hold low(X_r) unsummed and `src` the source's low 6 bits as they
/// are. Only the borrows into bits <= `top` are built (8, 5, 2 ANDs for top = 4, 3, 2): the forms above `top` are not
/// valid.
fn w_mod64(c: &mut Builder, recs: &mut Vec<Rec>, acc: &[QubitId], src: &[QubitId], nm: [QubitId; 3], b01: &Lin, top: usize) -> Vec<Lin> {
    let one = Lin::k(true);
    let sb = |j: usize, sh: usize| Lin::of(&[src[j], nm[sh]]);
    let mut w: Vec<Lin> = (0..6).map(|i| l(acc[i])).collect();
    for sh in [2usize, 1, 0] {
        let mut bo: Option<Lin> = None;
        let mut nw = w.clone();
        for i in sh..6 {
            match bo.clone() {
                None => {
                    nw[i] = w[i].x(&sb(i - sh, sh));
                    if i < top {
                        bo = Some(if (sh, i) == (0, 0) { b01.clone() } else { r_and(c, recs, w[i].x(&one), sb(i - sh, sh)) });
                    }
                }
                Some(bb) => {
                    nw[i] = w[i].x(&sb(i - sh, sh)).x(&bb);
                    if i < top {
                        bo = Some(r_maj(c, recs, w[i].x(&one), sb(i - sh, sh), bb));
                    }
                }
            }
        }
        w = nw;
    }
    w
}

/// y17-edge: [`w_mod64`] with the two borrows into bit 2 (chain 1's first and chain 0's second) returned, and taken
/// from `pre` in place of their ANDs where it is given. Needs top >= 2.
#[allow(clippy::too_many_arguments)]
fn w_mod64_pre(c: &mut Builder, recs: &mut Vec<Rec>, acc: &[QubitId], src: &[QubitId], nm: [QubitId; 3], b01: &Lin, top: usize, pre: Option<&[Lin; 2]>) -> (Vec<Lin>, [Lin; 2]) {
    assert!((2..=5).contains(&top));
    let one = Lin::k(true);
    let sb = |j: usize, sh: usize| Lin::of(&[src[j], nm[sh]]);
    let mut w: Vec<Lin> = (0..6).map(|i| l(acc[i])).collect();
    let mut got: [Option<Lin>; 2] = [None, None];
    for sh in [2usize, 1, 0] {
        let mut bo: Option<Lin> = None;
        let mut nw = w.clone();
        for i in sh..6 {
            match bo.clone() {
                None => {
                    nw[i] = w[i].x(&sb(i - sh, sh));
                    if i < top {
                        bo = Some(if (sh, i) == (0, 0) {
                            b01.clone()
                        } else if (sh, i) == (1, 1) {
                            let v = match pre {
                                Some(p) => p[0].clone(),
                                None => r_and(c, recs, w[i].x(&one), sb(i - sh, sh)),
                            };
                            got[0] = Some(v.clone());
                            v
                        } else {
                            r_and(c, recs, w[i].x(&one), sb(i - sh, sh))
                        });
                    }
                }
                Some(bb) => {
                    nw[i] = w[i].x(&sb(i - sh, sh)).x(&bb);
                    if i < top {
                        bo = Some(if (sh, i) == (0, 1) {
                            let v = match pre {
                                Some(p) => p[1].clone(),
                                None => r_maj(c, recs, w[i].x(&one), sb(i - sh, sh), bb),
                            };
                            got[1] = Some(v.clone());
                            v
                        } else {
                            r_maj(c, recs, w[i].x(&one), sb(i - sh, sh), bb)
                        });
                    }
                }
            }
        }
        w = nw;
    }
    let [g0, g1] = got;
    (w, [g0.expect("y17: the borrow of chain 1"), g1.expect("y17: the borrow of chain 0")])
}

/// y17-edge: clear the gate wires yq[i - 3] = AND(gates[i - 3], W's bit i), i = 3..=top, by measurement, top first
/// (the lean form of [`fold_rev_v2`]). A wire that measures 1 pays for the chains up to its bit (past the two borrows
/// `pre`, still live), and the wires below it are then erased from the chains' forms; one that measures 0 pays nothing
/// and the next lower wire is measured. The wires are left clear, not released. Every condition is one fresh
/// measurement bit or its complement.
#[allow(clippy::too_many_arguments)]
fn lean_clear_y(c: &mut Builder, acc: &[QubitId], src: &[QubitId], nm: [QubitId; 3], b01: &Lin, pre: &[Lin; 2], yq: &[QubitId; 3], gates: &[Lin; 3], top: usize) {
    let m = c.alloc_bit();
    c.hmr(yq[top - 3], m);
    c.push_condition(m);
    {
        let mut r2: Vec<Rec> = Vec::new();
        let (w, _) = w_mod64_pre(c, &mut r2, acc, src, nm, b01, top, Some(pre));
        lin_cz(c, &gates[top - 3], &w[top]); // the phase the measurement left
        for i in (3..top).rev() {
            let mi = c.alloc_bit();
            c.hmr(yq[i - 3], mi);
            c.push_condition(mi);
            lin_cz(c, &gates[i - 3], &w[i]);
            c.pop_condition();
            c.free_bit(mi);
        }
        pop_chain(c, &mut r2);
    }
    c.pop_condition();
    if top > 3 {
        let not_m = c.alloc_bit();
        c.bit_store1(not_m);
        c.bit_xor_into(not_m, m);
        c.push_condition(not_m);
        lean_clear_y(c, acc, src, nm, b01, pre, yq, gates, top - 1);
        c.pop_condition();
        c.free_bit(not_m);
    }
    c.free_bit(m);
}

fn pop_chain(c: &mut Builder, r2: &mut Vec<Rec>) {
    while let Some(r) = r2.pop() {
        match r {
            Rec::And(q, a, b) => lin_and_erase(c, q, &a, &b),
            Rec::Maj(q, a, b, ci) => {
                lin_xor_into(c, &ci, q);
                lin_and_erase(c, q, &a, &b);
            }
            _ => unreachable!(),
        }
    }
}

/// Clear the copies of W's bits 2..=top (wc[i - 2] holds bit i) by measurement, top bit first (see
/// [`Y15_REV_COPY_MBU`]). Every condition is one fresh measurement bit or its complement, so the builder's
/// 2^-depth weight is the true probability.
fn clear_copies(c: &mut Builder, acc: &[QubitId], src: &[QubitId], nm: [QubitId; 3], b01: &Lin, wc: &[QubitId], top: usize) {
    let m = c.alloc_bit();
    c.hmr(wc[top - 2], m);
    c.push_condition(m);
    {
        let mut r2: Vec<Rec> = Vec::new();
        let w = w_mod64(c, &mut r2, acc, src, nm, b01, top);
        lin_cz(c, &Lin::k(true), &w[top]); // the phase the measurement left: (-1)^(W's bit `top`)
        for i in 2..top {
            lin_xor_into(c, &w[i], wc[i - 2]);
        }
        pop_chain(c, &mut r2);
    }
    c.pop_condition();
    if top > 2 {
        let not_m = c.alloc_bit();
        c.bit_store1(not_m);
        c.bit_xor_into(not_m, m);
        c.push_condition(not_m);
        clear_copies(c, acc, src, nm, b01, wc, top - 1);
        c.pop_condition();
        c.free_bit(not_m);
    }
    c.free_bit(m);
}

/// The fold of the reverse one-fold tick (folds.py `onefold_rev`): acc = bits [0, MW) of low(X_r), X_r = W + K_r
/// (W = the register rotated up by 3 + e, K_r = the three unfolded adds of the sign-flipped source), e = the three top
/// wires, nm = the letters of the flipped signs, src = the source's low 6 bits (not complemented). Writes
/// T = low(X_r) + E + (E - Nm + m)(f - 1), m = W mod 2^(3 + e), which it recovers as (low(X_r) - K_r) mod 64 by three
/// borrow chains inside the fold. 51 fixed wires (6 low carries, 12 borrows, 4 gate wires, 29 core ANDs).
/// `wc`: empty, or four wires holding bits 2..5 of W (copies taken before the adds); they are read in place of the
/// borrow chains and returned clear (the chains are built after the ladder for that, 40 fixed wires plus the 4 copies).
fn fold_rev(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], nm: [QubitId; 3], k1: QubitId, k2: QubitId, src: &[QubitId], wc: &[QubitId]) -> Vec<usize> {
    let mw = acc.len();
    let one = Lin::k(true);
    let c1 = lin_and(c, &l(acc[0]), &l(e[0]));
    let c2 = maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1));
    let c3 = maj_wire(c, &l(acc[2]), &l(e[2]), &l(c2));
    let c4 = lin_and(c, &l(acc[3]), &l(c3));
    let mut recs: Vec<Rec> = Vec::new();
    let sb = |j: usize, sh: usize| Lin::of(&[src[j], nm[sh]]);
    // early part: what bits 4 and 5 of the addend (n0, n1) need
    let b01 = r_and(c, &mut recs, l(acc[0]).x(&one), sb(0, 0));
    let w0 = l(acc[0]).x(&sb(0, 0));
    let w1 = l(acc[1]).x(&sb(0, 1)).x(&sb(1, 0)).x(&b01);
    // D = E - Nm, 4 bits two's complement
    let mut bw = r_and(c, &mut recs, l(e[0]).x(&one), l(nm[0]));
    let mut d = vec![Lin::of(&[e[0], nm[0]]), Lin::of(&[e[1], nm[1]]).x(&bw)];
    bw = r_maj(c, &mut recs, l(e[1]).x(&one), l(nm[1]), bw);
    d.push(Lin::of(&[e[2], nm[2]]).x(&bw));
    bw = r_maj(c, &mut recs, l(e[2]).x(&one), l(nm[2]), bw);
    d.push(bw);
    let n0 = d[0].x(&w0);
    let g1 = r_and(c, &mut recs, d[0].clone(), w0.clone());
    let n1 = d[1].x(&w1).x(&g1);
    let c5 = maj_wire(c, &l(acc[4]), &n0, &l(c4));
    recs.push(Rec::UndoC5);
    let c6 = maj_wire(c, &l(acc[5]), &n1, &l(c5));
    recs.push(Rec::UndoC6);
    // W mod 64 = (low(X_r) - 4 S2' - 2 S1' - S0') mod 64: by the borrow chains, or bits 2..5 from the copies
    let mark = recs.len();
    let w: Vec<Lin> = if wc.is_empty() {
        w_mod64(c, &mut recs, acc, src, nm, &b01, 5)
    } else {
        assert_eq!(wc.len(), 4);
        vec![w0.clone(), w1.clone(), l(wc[0]), l(wc[1]), l(wc[2]), l(wc[3])]
    };
    let tt = r_and(c, &mut recs, l(k1), l(k2));
    let g1g = Lin::of(&[k1, k2]).x(&tt);
    let y3 = r_and(c, &mut recs, g1g, w[3].clone());
    let y4 = r_and(c, &mut recs, l(k2), w[4].clone());
    let y5 = r_and(c, &mut recs, tt.clone(), w[5].clone());
    let y = [w[0].clone(), w[1].clone(), w[2].clone(), y3, y4, y5];
    // n = D + y (8 bits, in [-7, 70])
    let mut n = vec![n0.clone(), n1.clone()];
    let mut g = r_maj(c, &mut recs, d[1].clone(), y[1].clone(), g1);
    for i in 2..6 {
        let di = if i < 4 { d[i].clone() } else { d[3].clone() };
        n.push(di.x(&y[i]).x(&g));
        g = r_maj(c, &mut recs, di, y[i].clone(), g);
    }
    n.push(d[3].x(&g));
    let g7 = r_and(c, &mut recs, d[3].clone(), g);
    n.push(d[3].x(&g7));
    let add = addend_from_n(c, &mut recs, &n, mw);
    let budget = cells::cap().saturating_sub(c.active_qubits() as usize);
    let nbits = mw - 6;
    let lean45 = Y15_LEAN45 && merged_plan(nbits - 1, budget).is_none() && merged_plan(nbits, budget).is_none();
    if lean45 {
        maj_wire_erase(c, c5, &l(acc[4]), &n0, &l(c4));
        lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    }
    let budget = budget + 2 * usize::from(lean45);
    let plan = match merged_plan(nbits - 1, budget) {
        Some(mut p) => {
            *p.last_mut().unwrap() += 1;
            p
        }
        None => merged_plan(nbits, budget).unwrap_or_else(|| panic!("y15: the reverse fold's ladder does not fit: budget {budget}, active {}, cap {}", c.active_qubits(), cells::cap())),
    };
    ladder(c, acc, &add, 6, c6, &plan);
    let (c4, c5) = if lean45 {
        let c4 = lin_and(c, &l(acc[3]), &l(c3));
        let c5 = maj_wire(c, &l(acc[4]), &n0, &l(c4));
        (c4, c5)
    } else {
        (c4, c5)
    };
    let mut copies_left = !wc.is_empty();
    loop {
        if copies_left && recs.len() == mark {
            // every wire that read the copies is gone and acc[0..6) still holds low(X_r): clear the copies
            if Y15_REV_COPY_MBU {
                clear_copies(c, acc, src, nm, &b01, wc, 5);
            } else {
                let mut r2: Vec<Rec> = Vec::new();
                let w = w_mod64(c, &mut r2, acc, src, nm, &b01, 5);
                for i in 2..6 {
                    lin_xor_into(c, &w[i], wc[i - 2]);
                }
                pop_chain(c, &mut r2);
            }
            copies_left = false;
        }
        let Some(r) = recs.pop() else { break };
        match r {
            Rec::And(q, a, b) => lin_and_erase(c, q, &a, &b),
            Rec::Maj(q, a, b, ci) => {
                lin_xor_into(c, &ci, q);
                lin_and_erase(c, q, &a, &b);
            }
            Rec::UndoC6 => {
                maj_wire_erase(c, c6, &l(acc[5]), &n1, &l(c5));
                lin_xor_into(c, &n1, acc[5]);
                c.cx(c5, acc[5]);
            }
            Rec::UndoC5 => {
                maj_wire_erase(c, c5, &l(acc[4]), &n0, &l(c4));
                lin_xor_into(c, &n0, acc[4]);
                c.cx(c4, acc[4]);
            }
        }
    }
    lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    c.cx(c3, acc[3]);
    maj_wire_erase(c, c3, &l(acc[2]), &l(e[2]), &l(c2));
    c.cx(e[2], acc[2]);
    c.cx(c2, acc[2]);
    maj_wire_erase(c, c2, &l(acc[1]), &l(e[1]), &l(c1));
    c.cx(e[1], acc[1]);
    c.cx(c1, acc[1]);
    lin_and_erase(c, c1, &l(acc[0]), &l(e[0]));
    c.cx(e[0], acc[0]);
    plan
}

/// The addend's fields as forms of bits [0, mw): bits 4..9 = q, 10..16 = u, 17..31 = s, 32..38 = h, above = s.
fn field_map(q: &[Lin], u: &[Lin], s: &Lin, h: &[Lin], mw: usize) -> Vec<Lin> {
    (0..mw)
        .map(|b| match b {
            0..=3 => Lin::k(false),
            4..=9 => q[b - 4].clone(),
            10..=16 => u[b - 10].clone(),
            17..=31 => s.clone(),
            32..=38 => h[b - 32].clone(),
            _ => s.clone(),
        })
        .collect()
}

/// y15-core, forward: forms of bits [0, mw) of -(f - 1) k mod 2^mw from k's 8 bits (two's complement, k = -n in
/// [-7, 70]); 15 ANDs. Q = 3k = k + 2k (6; its sign is k's); U = J - k with J = Q >> 6 (6), and the borrow out of its
/// top bit is s = [k > 0] (1); H = n - s = ~k + [k <= 0], whose carry stays in the low three bits (2) unless k = 0,
/// and [k = 0] is the form 1 ^ k7 ^ s.
/// (experiments/y15-core/folds2.py `addend_from_k`.)
fn addend_from_k(c: &mut Builder, recs: &mut Vec<Rec>, k: &[Lin], mw: usize) -> Vec<Lin> {
    let one = Lin::k(true);
    let mut q = vec![k[0].clone(), k[1].x(&k[0])];
    let mut cy = r_and(c, recs, k[1].clone(), k[0].clone());
    for i in 2..8 {
        q.push(k[i].x(&k[i - 1]).x(&cy));
        if i < 7 {
            cy = r_maj(c, recs, k[i].clone(), k[i - 1].clone(), cy);
        }
    }
    let j = [q[6].clone(), q[7].clone(), k[7].clone()];
    let mut u = vec![j[0].x(&k[0])];
    let mut b = r_and(c, recs, j[0].x(&one), k[0].clone());
    for i in 1..7 {
        let ji = if i < 3 { j[i].clone() } else { j[2].clone() };
        u.push(ji.x(&k[i]).x(&b));
        b = r_maj(c, recs, ji.x(&one), k[i].clone(), b);
    }
    let s = b;
    let mut h = vec![k[0].x(&s)];
    let mut z = r_and(c, recs, k[0].x(&one), s.x(&one));
    h.push(k[1].x(&one).x(&z));
    z = r_and(c, recs, k[1].x(&one), z);
    h.push(k[2].x(&one).x(&z));
    // [k = 0] = not ([k < 0] xor [k > 0]): a form, no AND
    let z = k[7].x(&s).x(&one);
    for i in 3..7 {
        h.push(k[i].x(&one).x(&z));
    }
    field_map(&q, &u, &s, &h, mw)
}

/// y15-core, reverse: forms of bits [0, mw) of (f - 1) n mod 2^mw from n's 8 bits (two's complement, n in [-7, 70]);
/// 14 ANDs. Q = n - 4n without its top borrow (6); U = n + (Q >> 6) (6); s = n7; H = n - s, whose borrow stays in the
/// low three bits because n < 0 means n in [-7, -1] (2). (folds2.py `addend_from_n_rev`.)
fn addend_from_n_rev(c: &mut Builder, recs: &mut Vec<Rec>, n: &[Lin], mw: usize) -> Vec<Lin> {
    let one = Lin::k(true);
    let s = n[7].clone();
    let mut q = vec![n[0].clone(), n[1].clone(), n[2].x(&n[0])];
    let mut d = r_and(c, recs, n[2].x(&one), n[0].clone());
    for i in 3..9 {
        let ni = if i < 8 { n[i].clone() } else { n[7].clone() };
        q.push(ni.x(&n[i - 2]).x(&d));
        if i < 8 {
            d = r_maj(c, recs, ni.x(&one), n[i - 2].clone(), d);
        }
    }
    let j = [q[6].clone(), q[7].clone(), q[8].clone()];
    let mut u = vec![n[0].x(&j[0])];
    let mut e = r_and(c, recs, n[0].clone(), j[0].clone());
    for i in 1..7 {
        let ji = if i < 3 { j[i].clone() } else { j[2].clone() };
        u.push(n[i].x(&ji).x(&e));
        if i < 6 {
            e = r_maj(c, recs, n[i].clone(), ji, e);
        }
    }
    let mut h = vec![n[0].x(&s)];
    let mut z = r_and(c, recs, n[0].x(&one), s.clone());
    h.push(n[1].x(&z));
    z = r_and(c, recs, n[1].x(&one), z);
    h.push(n[2].x(&z));
    for i in 3..7 {
        h.push(n[i].clone());
    }
    field_map(&q, &u, &s, &h, mw)
}

/// y16-core: gate and output tables of the searched programs. A mask is an XOR over the basis: bit 0 = the constant 1,
/// bits 1..=8 = x0..x7 (k's bits forward, n's bits reverse), bit 9 + j = the wire of gate j. Gate j = AND of its two
/// forms. `OUT` = the forms of Q0..Q5, U0..U6, s, H0..H6 (the addend's fields, see [`field_map`]).
/// (experiments/y16-core: gen_rust.py from run/prog_fwd_k.json and run/prog_rev_n.json.)
const Y16_FWD_GATES: [(u32, u32); 14] = [
    (0x2, 0x4),
    (0x2, 0x100),
    (0x8, 0x180),
    (0x6, 0x500),
    (0xe, 0x204),
    (0x200c, 0x14),
    (0x2024, 0x4030),
    (0x50, 0xc000),
    (0x22, 0x1c0c2),
    (0x86, 0x3c004),
    (0x4000c, 0x108),
    (0x2014, 0xc0d88),
    (0xa004, 0xc2404),
    (0x4c, 0x3ced94),
];
const Y16_FWD_OUT: [u32; 21] = [
    0x2, 0x6, 0x20c, 0x201c, 0x6034, 0xc040,
    0x1c0e2, 0x3c084, 0x40308, 0xc3114, 0x1c4430, 0x3cf154, 0x7cf1d8,
    0x7cf9d8, 0x7cf9da, 0x7cfddc, 0x7cedd0, 0x7cf8c8, 0x7cf8f8, 0x7cf898, 0x7cf858,
];
const Y16_REV_GATES: [(u32, u32); 12] = [
    (0x2, 0x8),
    (0x2, 0x100),
    (0x8a, 0x108),
    (0x6, 0x500),
    (0x206, 0x14),
    (0x2802, 0x528),
    (0x50, 0x6212),
    (0xa2, 0xe808),
    (0x44, 0x1e82c),
    (0x8, 0x3e0e4),
    (0x200c, 0x7c170),
    (0x4018, 0x7a0cc),
];
const Y16_REV_OUT: [u32; 21] = [
    0x2, 0x4, 0xa, 0x216, 0x222a, 0x6d5a,
    0xeda8, 0x1ed6c, 0x3f8e4, 0x7e0f4, 0xfcfd8, 0x17a08c, 0xe08,
    0x100, 0x102, 0x504, 0x1508, 0x10, 0x20, 0x40, 0x80,
];

/// y16-core: the addend's fields by one of the programs above. Every AND goes on the fold's undo list with its two
/// forms and is erased there by measurement, as the ANDs it replaces.
fn addend_prog(c: &mut Builder, recs: &mut Vec<Rec>, x: &[Lin], gates: &[(u32, u32)], out: &[u32; 21], mw: usize) -> Vec<Lin> {
    assert!(x.len() == 8);
    let mut vals: Vec<Lin> = vec![Lin::k(true)];
    vals.extend(x.iter().cloned());
    fn comb(vals: &[Lin], m: u32) -> Lin {
        let mut a = Lin::k(false);
        for (i, v) in vals.iter().enumerate() {
            if m >> i & 1 == 1 {
                a = a.x(v);
            }
        }
        a
    }
    for &(a, b) in gates {
        let g = r_and(c, recs, comb(&vals, a), comb(&vals, b));
        vals.push(g);
    }
    let o: Vec<Lin> = out.iter().map(|&m| comb(&vals, m)).collect();
    field_map(&o[0..6], &o[6..13], &o[13], &o[14..21], mw)
}

/// The ladder's plan on bits [6, MW) for the room left now, and whether it needs the two wires of [`Y15_LEAN45`]
/// (the caller then erases the carries into bits 4 and 5 before the ladder and builds them again after it).
fn fold_plan(c: &Builder, mw: usize, what: &str) -> (Vec<usize>, bool) {
    let budget = cells::cap().saturating_sub(c.active_qubits() as usize);
    let nbits = mw - 6;
    let lean45 = Y15_LEAN45 && merged_plan(nbits - 1, budget).is_none() && merged_plan(nbits, budget).is_none();
    let budget = budget + 2 * usize::from(lean45);
    let plan = match merged_plan(nbits - 1, budget) {
        Some(mut p) => {
            *p.last_mut().unwrap() += 1;
            p
        }
        None => merged_plan(nbits, budget).unwrap_or_else(|| panic!("y15: the {what} fold's ladder does not fit: budget {budget}, active {}, cap {}", c.active_qubits(), cells::cap())),
    };
    (plan, lean45)
}

/// Erase the fold's helper wires in reverse order, then the low section (the tail of both folds).
#[allow(clippy::too_many_arguments)]
fn fold_undo(c: &mut Builder, recs: Vec<Rec>, acc: &[QubitId], e: [QubitId; 3], a4: &Lin, a5: &Lin, cw: [QubitId; 6]) {
    let [c1, c2, c3, c4, c5, c6] = cw;
    fold_undo_recs(c, recs, acc, a4, a5, [c4, c5, c6]);
    fold_undo_low(c, acc, e, [c1, c2, c3, c4]);
}
/// The first part of [`fold_undo`]: the helper wires, last built first (none of their forms reads E, c1 or c2 in the
/// forward fold).
fn fold_undo_recs(c: &mut Builder, mut recs: Vec<Rec>, acc: &[QubitId], a4: &Lin, a5: &Lin, cw: [QubitId; 3]) {
    let [c4, c5, c6] = cw;
    while let Some(r) = recs.pop() {
        match r {
            Rec::And(q, a, b) => lin_and_erase(c, q, &a, &b),
            Rec::Maj(q, a, b, ci) => {
                lin_xor_into(c, &ci, q);
                lin_and_erase(c, q, &a, &b);
            }
            Rec::UndoC6 => {
                maj_wire_erase(c, c6, &l(acc[5]), a5, &l(c5));
                lin_xor_into(c, a5, acc[5]);
                c.cx(c5, acc[5]);
            }
            Rec::UndoC5 => {
                maj_wire_erase(c, c5, &l(acc[4]), a4, &l(c4));
                lin_xor_into(c, a4, acc[4]);
                c.cx(c4, acc[4]);
            }
        }
    }
}
/// The second part of [`fold_undo`]: the low section acc[0..4) += E.
fn fold_undo_low(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], cw: [QubitId; 4]) {
    let [c1, c2, c3, c4] = cw;
    lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    c.cx(c3, acc[3]);
    maj_wire_erase(c, c3, &l(acc[2]), &l(e[2]), &l(c2));
    c.cx(e[2], acc[2]);
    c.cx(c2, acc[2]);
    maj_wire_erase(c, c2, &l(acc[1]), &l(e[1]), &l(c1));
    c.cx(e[1], acc[1]);
    c.cx(c1, acc[1]);
    lin_and_erase(c, c1, &l(acc[0]), &l(e[0]));
    c.cx(e[0], acc[0]);
}

/// y15-core: the forward fold with a 22-AND core (folds2.py `onefold_fwd_v2`); the same window as [`fold_fwd`] on
/// every input. Works with k = -n = Nm + m - E. E cancels in the low three bits (m mod 8 = acc + E - 8 c3), so
/// k = (Nm + acc[0..3)) + 8 (y3 + 2 y4 + 4 y5 + r3 - c3): 3 ANDs for the sum, 3 for the chain that moves the upper
/// part by one either way, 1 for its sign. 32 fixed wires (6 low carries, 4 gate wires, 22 core ANDs).
#[allow(clippy::too_many_arguments)]
fn fold_fwd_v2(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], nm: [QubitId; 3], k1: QubitId, k2: QubitId, fin: usize, mut esh: Option<&mut ESh>) -> Vec<usize> {
    let mw = acc.len();
    let c1 = lin_and(c, &l(acc[0]), &l(e[0]));
    let c2 = maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1));
    let c3 = maj_wire(c, &l(acc[2]), &l(e[2]), &l(c2));
    let c4 = lin_and(c, &l(acc[3]), &l(c3));
    // y18-next: c2, c1 and the top wires leave here (see Y18_FIN and [`ESh`]): nothing below reads them before the undo
    assert!(fin <= 6 && (fin >= 4) == esh.is_some());
    if fin >= 1 {
        maj_wire_erase(c, c2, &l(acc[1]), &l(e[1]), &l(c1));
    }
    if fin >= 2 {
        lin_and_erase(c, c1, &l(acc[0]), &l(e[0]));
    }
    if let Some(st) = esh.as_deref() {
        esh_out(c, st);
    }
    let v3 = Lin::of(&[acc[3], c3]);
    let mut recs: Vec<Rec> = Vec::new();
    let tt = r_and(c, &mut recs, l(k1), l(k2));
    let g1 = Lin::of(&[k1, k2]).x(&tt);
    // r = Nm + acc[0..3) (the register's own low bits, before E is added)
    let r1 = r_and(c, &mut recs, l(nm[0]), l(acc[0]));
    let mut k = vec![Lin::of(&[nm[0], acc[0]]), Lin::of(&[nm[1], acc[1]]).x(&r1)];
    let r2 = r_maj(c, &mut recs, l(nm[1]), l(acc[1]), r1);
    k.push(Lin::of(&[nm[2], acc[2]]).x(&r2));
    let r3 = r_maj(c, &mut recs, l(nm[2]), l(acc[2]), r2);
    // bits 4 and 5 of the addend are n0 = k0 and n1 = k1 ^ k0; the sums there are the quotient's bits 4 and 5
    let (a4, a5) = (k[0].clone(), k[1].x(&k[0]));
    let y3 = r_and(c, &mut recs, g1, v3);
    let sum4 = Lin::of(&[acc[4], c4]).x(&a4);
    let y4 = r_and_e(c, &mut recs, l(k2), sum4, l(k2), l(acc[4]));
    let c5 = maj_wire(c, &l(acc[4]), &a4, &l(c4));
    recs.push(Rec::UndoC5);
    let sum5 = Lin::of(&[acc[5], c5]).x(&a5);
    let y5 = r_and_e(c, &mut recs, tt.clone(), sum5, tt.clone(), l(acc[5]));
    let c6 = maj_wire(c, &l(acc[5]), &a5, &l(c5));
    recs.push(Rec::UndoC6);
    // k's upper bits: y_hi + (r3 - c3); p = it moves, c3 = it moves down
    let fc3 = l(c3);
    let p = r3.x(&fc3);
    k.push(y3.x(&p));
    let mut t = r_and(c, &mut recs, p, y3.x(&fc3));
    k.push(y4.x(&t));
    t = r_and(c, &mut recs, t, y4.x(&fc3));
    k.push(y5.x(&t));
    t = r_and(c, &mut recs, t, y5.x(&fc3));
    k.push(t.clone());
    let k7 = r_and(c, &mut recs, t, fc3);
    k.push(k7);
    let add = if Y16_CORE { addend_prog(c, &mut recs, &k, &Y16_FWD_GATES, &Y16_FWD_OUT, mw) } else { addend_from_k(c, &mut recs, &k, mw) };
    if Y15_TRACE {
        eprintln!("Y18_IDLE fwd recs={} idle={:?}", recs.len(), y18_idle(&recs, &add));
    }
    // y18-next: the AND of the shift letter leaves for the ladder (see Y18_FIN)
    let tt_q = tt.w[0];
    if fin >= 3 {
        lin_and_erase(c, tt_q, &l(k1), &l(k2));
    }
    let (plan, lean45) = fold_plan(c, mw, "forward");
    if lean45 {
        maj_wire_erase(c, c5, &l(acc[4]), &a4, &l(c4));
        lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    }
    ladder(c, acc, &add, 6, c6, &plan);
    let (c4, c5) = if lean45 {
        let c4 = lin_and(c, &l(acc[3]), &l(c3));
        let c5 = maj_wire(c, &l(acc[4]), &a4, &l(c4));
        (c4, c5)
    } else {
        (c4, c5)
    };
    if fin >= 3 {
        let q = lin_and(c, &l(k1), &l(k2));
        y18_subst(&mut recs, tt_q, q);
    }
    fold_undo_recs(c, recs, acc, &a4, &a5, [c4, c5, c6]);
    // the top wires again, once the helper wires are gone (fresh wires: the low section's undo reads the new ones)
    let e = match esh.as_deref_mut() {
        Some(st) => {
            esh_in(c, st);
            [st.x256, st.x257, st.x258]
        }
        None => e,
    };
    let c1 = if fin >= 2 { lin_and(c, &l(acc[0]), &l(e[0])) } else { c1 };
    let c2 = if fin >= 1 { maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1)) } else { c2 };
    fold_undo_low(c, acc, e, [c1, c2, c3, c4]);
    plan
}

/// The borrow into bit i + 1 of the reverse fold's chain `sh`: add sh's kept carry if there is one (only its erase is
/// recorded), else an AND built here.
fn borrow_first(c: &mut Builder, recs: &mut Vec<Rec>, kept: &[Vec<QubitId>; 3], sh: usize, i: usize, a: Lin, b: Lin) -> Lin {
    match kept[sh].get(i - sh) {
        Some(&q) => {
            recs.push(Rec::And(q, a, b));
            l(q)
        }
        None => r_and(c, recs, a, b),
    }
}
#[allow(clippy::too_many_arguments)]
fn borrow_next(c: &mut Builder, recs: &mut Vec<Rec>, kept: &[Vec<QubitId>; 3], sh: usize, i: usize, x: Lin, y: Lin, ci: Lin) -> Lin {
    match kept[sh].get(i - sh) {
        Some(&q) => {
            let (a, b) = (x.x(&ci), y.x(&ci));
            recs.push(Rec::Maj(q, a, b, ci));
            l(q)
        }
        None => r_maj(c, recs, x, y, ci),
    }
}

/// y15-core: `acc += addend` as the cells' chunked add, with the carries into positions 1..=keep left on their own
/// wires (returned; the reverse fold erases them). keep = 0: the plain chunked add. The first `keep` positions are a
/// ripple built here; the chunked add runs its first chunk from position `keep` with the last of them as carry-in.
fn low_keep_add(c: &mut Builder, b: &[QubitId], acc: &[QubitId], proxy: usize, rev: bool, keep: usize) -> (QubitId, Vec<QubitId>) {
    if keep == 0 {
        return (cells::chunked_add(c, b, acc, proxy, rev), Vec::new());
    }
    let mut q: Vec<QubitId> = vec![lin_and(c, &l(acc[0]), &l(b[0]))]; // q[j] = the carry into position j + 1
    for j in 1..keep {
        let t = maj_wire(c, &l(acc[j]), &l(b[j]), &l(q[j - 1]));
        q.push(t);
    }
    for j in (0..keep).rev() {
        c.cx(b[j], acc[j]);
        if j > 0 {
            c.cx(q[j - 1], acc[j]);
        }
    }
    let m = cells::y15_chunked_add_cin(c, b, acc, proxy, rev, keep, q[keep - 1]);
    (m, q)
}

/// y15-core: the reverse fold with a 23-AND core (folds2.py `onefold_rev_v2`); the same window as [`fold_rev`] on
/// every input. n = E + ~Nm + y + 1 - 8 by one carry-save row on bits 0..2 (3 ANDs) and one ripple (6 ANDs).
/// 45 fixed wires (6 low carries, 12 borrows, 4 gate wires, 23 core ANDs).
/// `kept[sh][j]` = add sh's own carry into bit sh + 1 + j, left live by the add: used as the borrow there and erased
/// in this fold's undo (measured, no Toffoli). A borrow not in `kept` is built as before.
/// `wc` (y15-pack): empty, or four wires holding bits 2..5 of W (the copies of [`Y15_REV_COPY`]); they are read in
/// place of the borrow chains and returned clear, as in [`fold_rev`]. `kept` may then hold only add 0's first carry.
#[allow(clippy::too_many_arguments)]
fn fold_rev_v2(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], nm: [QubitId; 3], k1: QubitId, k2: QubitId, src: &[QubitId], kept: &[Vec<QubitId>; 3], wc: &[QubitId], lean: bool, order: [usize; 3], yg: &[QubitId], fin: usize) -> Vec<usize> {
    let mw = acc.len();
    let one = Lin::k(true);
    let c1 = lin_and(c, &l(acc[0]), &l(e[0]));
    let c2 = maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1));
    let c3 = maj_wire(c, &l(acc[2]), &l(e[2]), &l(c2));
    let c4 = lin_and(c, &l(acc[3]), &l(c3));
    let mut recs: Vec<Rec> = Vec::new();
    let sb = |j: usize, sh: usize| Lin::of(&[src[j], nm[sh]]);
    let nn = |i: usize| l(nm[i]).x(&one);
    // early part: n0 and n1 (bits 4 and 5 of the addend)
    let b01 = borrow_first(c, &mut recs, kept, 0, 0, l(acc[0]).x(&one), sb(0, 0));
    let w0 = l(acc[0]).x(&sb(0, 0));
    let w1 = l(acc[1]).x(&sb(0, 1)).x(&sb(1, 0)).x(&b01);
    let sg0 = l(e[0]).x(&nn(0)).x(&w0);
    let kp1 = r_maj(c, &mut recs, l(e[0]), nn(0), w0.clone());
    let sg1 = l(e[1]).x(&nn(1)).x(&w1);
    let n0 = sg0.x(&one);
    let n1 = sg1.x(&kp1).x(&sg0);
    let c5 = maj_wire(c, &l(acc[4]), &n0, &l(c4));
    recs.push(Rec::UndoC5);
    let c6 = maj_wire(c, &l(acc[5]), &n1, &l(c5));
    recs.push(Rec::UndoC6);
    // W mod 64 = (low(X_r) - 4 S2' - 2 S1' - S0') mod 64: bits 2..5 from the copies, or by the borrow chains
    let mark = recs.len();
    let mut w: Vec<Lin> = (0..6).map(|i| l(acc[i])).collect();
    // y17-edge, the lean form: (the gate wires, their gate forms, the two borrows into bit 2, the undo list's length
    // once the gate wires exist)
    let mut lean_y: Option<([QubitId; 3], [Lin; 3], [Lin; 2], usize)> = None;
    // y17-edge, gate wires first: (the gate wires, built by the caller before the adds; the two borrows into bit 2;
    // the undo list's length)
    let mut ygate: Option<([QubitId; 3], [Lin; 2], usize)> = None;
    let (y3, y4, y5);
    if !yg.is_empty() {
        assert!(yg.len() == 3 && !lean && wc.is_empty() && kept.iter().all(|k| k.is_empty()), "y17: gate wires first with another form");
        let (wl, pre) = w_mod64_pre(c, &mut recs, acc, src, nm, &b01, 2, None);
        w = wl;
        (y3, y4, y5) = (l(yg[0]), l(yg[1]), l(yg[2]));
        ygate = Some(([yg[0], yg[1], yg[2]], pre, recs.len()));
    } else if lean {
        assert!(wc.is_empty() && kept.iter().all(|k| k.is_empty()), "y17: lean chains with copies or kept carries");
        // the two borrows into bit 2 stay through the ladder (on the undo list); the nine above them only until the
        // gate wires are built
        let (wl, pre) = w_mod64_pre(c, &mut recs, acc, src, nm, &b01, 2, None);
        let mut r2: Vec<Rec> = Vec::new();
        let (wf, _) = w_mod64_pre(c, &mut r2, acc, src, nm, &b01, 5, Some(&pre));
        let tt = r_and(c, &mut recs, l(k1), l(k2));
        let gates = [Lin::of(&[k1, k2]).x(&tt), l(k2), tt];
        let yq = [lin_and(c, &gates[0], &wf[3]), lin_and(c, &gates[1], &wf[4]), lin_and(c, &gates[2], &wf[5])];
        pop_chain(c, &mut r2);
        w = wl;
        (y3, y4, y5) = (l(yq[0]), l(yq[1]), l(yq[2]));
        lean_y = Some((yq, gates, pre, recs.len()));
    } else {
        if wc.is_empty() {
            // the chains undo the adds last to first (`order`), so that a kept carry is the borrow at its bit
            for sh in order {
                let mut bo: Option<Lin> = None;
                let mut nw = w.clone();
                for i in sh..6 {
                    match bo.clone() {
                        None => {
                            nw[i] = w[i].x(&sb(i - sh, sh));
                            if i < 5 {
                                bo = Some(if (sh, i) == (0, 0) { b01.clone() } else { borrow_first(c, &mut recs, kept, sh, i, w[i].x(&one), sb(i - sh, sh)) });
                            }
                        }
                        Some(bb) => {
                            nw[i] = w[i].x(&sb(i - sh, sh)).x(&bb);
                            if i < 5 {
                                bo = Some(borrow_next(c, &mut recs, kept, sh, i, w[i].x(&one), sb(i - sh, sh), bb));
                            }
                        }
                    }
                }
                w = nw;
            }
        } else {
            assert!(wc.len() == 4 && kept[0].len() <= 1 && kept[1].is_empty() && kept[2].is_empty(), "y15: copies and kept carries on one tick");
            w = vec![w0.clone(), w1.clone(), l(wc[0]), l(wc[1]), l(wc[2]), l(wc[3])];
        }
        let tt = r_and(c, &mut recs, l(k1), l(k2));
        let g1g = Lin::of(&[k1, k2]).x(&tt);
        y3 = r_and(c, &mut recs, g1g, w[3].clone());
        y4 = r_and(c, &mut recs, l(k2), w[4].clone());
        y5 = r_and(c, &mut recs, tt.clone(), w[5].clone());
    }
    // the rest of the carry-save row, then the ripple with carry-in 1 (its bit 0 is n0, its first carry sg0)
    let kp2 = r_maj(c, &mut recs, l(e[1]), nn(1), w1.clone());
    let sg2 = l(e[2]).x(&nn(2)).x(&w[2]);
    let kp3 = r_maj(c, &mut recs, l(e[2]), nn(2), w[2].clone());
    let mut n = vec![n0.clone(), n1.clone()];
    let mut r = r_maj(c, &mut recs, sg1, kp1, sg0);
    n.push(sg2.x(&kp2).x(&r));
    r = r_maj(c, &mut recs, sg2, kp2, r);
    n.push(y3.x(&one).x(&kp3).x(&r));
    r = r_maj(c, &mut recs, y3.x(&one), kp3, r);
    n.push(y4.x(&one).x(&y3).x(&r));
    r = r_maj(c, &mut recs, y4.x(&one), y3, r);
    n.push(y5.x(&one).x(&y4).x(&r));
    r = r_maj(c, &mut recs, y5.x(&one), y4, r);
    n.push(y5.x(&r).x(&one));
    let n7 = r_and(c, &mut recs, y5.x(&one), r.x(&one));
    n.push(n7);
    let add = if Y16_CORE { addend_prog(c, &mut recs, &n, &Y16_REV_GATES, &Y16_REV_OUT, mw) } else { addend_from_n_rev(c, &mut recs, &n, mw) };
    if Y15_TRACE {
        eprintln!("Y18_IDLE rev recs={} idle={:?}", recs.len(), y18_idle(&recs, &add));
    }
    // y18-next: c2 and c1 leave for the ladder (see Y18_FIN)
    assert!(fin <= 2);
    if fin >= 1 {
        maj_wire_erase(c, c2, &l(acc[1]), &l(e[1]), &l(c1));
    }
    if fin >= 2 {
        lin_and_erase(c, c1, &l(acc[0]), &l(e[0]));
    }
    let (plan, lean45) = fold_plan(c, mw, "reverse");
    if lean45 {
        maj_wire_erase(c, c5, &l(acc[4]), &n0, &l(c4));
        lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    }
    ladder(c, acc, &add, 6, c6, &plan);
    let (c4, c5) = if lean45 {
        let c4 = lin_and(c, &l(acc[3]), &l(c3));
        let c5 = maj_wire(c, &l(acc[4]), &n0, &l(c4));
        (c4, c5)
    } else {
        (c4, c5)
    };
    let c1 = if fin >= 2 { lin_and(c, &l(acc[0]), &l(e[0])) } else { c1 };
    let c2 = if fin >= 1 { maj_wire(c, &l(acc[1]), &l(e[1]), &l(c1)) } else { c2 };
    if !wc.is_empty() {
        // erase every wire that read the copies (all built after `mark`); acc[0..6) still holds low(X_r): clear the
        // copies as [`fold_rev`] does
        let mut tail = recs.split_off(mark);
        pop_chain(c, &mut tail);
        if Y15_REV_COPY_MBU {
            clear_copies(c, acc, src, nm, &b01, wc, 5);
        } else {
            let mut r2: Vec<Rec> = Vec::new();
            let w = w_mod64(c, &mut r2, acc, src, nm, &b01, 5);
            for i in 2..6 {
                lin_xor_into(c, &w[i], wc[i - 2]);
            }
            pop_chain(c, &mut r2);
        }
    }
    if let Some((yq, pre, mark2)) = ygate {
        // as the lean form below; the AND of the shift letter is built here only for the gate forms
        let mut tail = recs.split_off(mark2);
        pop_chain(c, &mut tail);
        let tt = lin_and(c, &l(k1), &l(k2));
        let gates = [Lin::of(&[k1, k2, tt]), l(k2), l(tt)];
        lean_clear_y(c, acc, src, nm, &b01, &pre, &yq, &gates, 5);
        lin_and_erase(c, tt, &l(k1), &l(k2));
        for q in yq {
            c.release_clean(q);
        }
    }
    if let Some((yq, gates, pre, mark2)) = lean_y {
        // erase every wire built after the gate wires (they read them and W's bit 2), then the gate wires themselves;
        // acc[0..6) still holds low(X_r) and the two borrows into bit 2 are live
        let mut tail = recs.split_off(mark2);
        pop_chain(c, &mut tail);
        lean_clear_y(c, acc, src, nm, &b01, &pre, &yq, &gates, 5);
        for q in yq {
            c.release_clean(q);
        }
    }
    fold_undo(c, recs, acc, e, &n0, &n1, [c1, c2, c3, c4, c5, c6]);
    plan
}

/// The three unfolded adds, the fold and the erase of every wire they left (see the module text). `rev`: the reverse
/// tick (the letters already flipped by the caller, the multiply direction's compare rules, the reverse fold).
fn body(c: &mut Builder, t: usize, s: [QubitId; 3], k1: QubitId, k2: QubitId, b: &[QubitId], tg: &[QubitId], proxy: usize, rev: bool) {
    let (e_start, a_start) = (c.expected_total(), c.active_qubits());
    if Y15_TRACE {
        eprintln!("Y15_ROOM {} t={t} active={a_start} room={}", if rev { "rev" } else { "fwd" }, cells::cap().saturating_sub(a_start as usize));
    }
    // y15-pack: the reverse fold gets W's low bits from the adds' kept carries (Y15_CORE_V2 with Y15_KEEP_LOW) or from
    // copies (Y15_REV_COPY); with both switched on, by the room of this tick-pass
    let keep_on = rev && Y15_CORE_V2 && Y15_KEEP_LOW != [0, 0, 0];
    let copy_here = rev && Y15_REV_COPY && !(keep_on && cells::cap().saturating_sub(a_start as usize) >= Y15_KEEP_ROOM);
    // reverse: W (the rotated register) is in the clear here; its bits 2..5 are copied for the fold
    // y17-edge: on the ticks of Y17_LEAN no copy is taken; the fold builds its chains itself
    let lean_here = copy_here && lean_on(t);
    // y17-edge: on the ticks of Y17_YGATE the three gate wires are built here (W in the clear) and held in place of
    // the copies
    let yg_here = copy_here && !lean_here && ygate_on(t);
    let yg: Vec<QubitId> = if yg_here {
        let tt = lin_and(c, &l(k1), &l(k2));
        let q = vec![lin_and(c, &Lin::of(&[k1, k2, tt]), &l(tg[3])), lin_and(c, &l(k2), &l(tg[4])), lin_and(c, &l(tt), &l(tg[5]))];
        lin_and_erase(c, tt, &l(k1), &l(k2));
        q
    } else {
        Vec::new()
    };
    let pad: Vec<QubitId> = if lean_here {
        c.alloc_qubits(Y17_LEAN_PAD)
    } else if yg_here {
        c.alloc_qubits(Y17_YGATE_PAD)
    } else {
        Vec::new()
    };
    let wc: Vec<QubitId> = if copy_here && !lean_here && !yg_here {
        let q = c.alloc_qubits(4);
        for i in 0..4 {
            c.cx(tg[2 + i], q[i]);
        }
        q
    } else {
        Vec::new()
    };
    let keep = if keep_on && !copy_here { Y15_KEEP_LOW } else { [0, 0, 0] };
    assert!(keep[0] <= 5 && keep[1] <= 4 && keep[2] <= 3);
    // y17-edge: on reverse tick 0 the first two adds run in the other order (see [`rev_on`])
    let swap01 = rev && t == 0;
    assert!(!swap01 || (Y17_REV0 && Y15_CORE_V2 && Y15_JOINT_M));
    let (m0, kept0, m1, kept1, e_add0, e_add1);
    // (x256, h1, x257) once built: at the end of adds 0 and 1, or after add 2's chunked part (Y18_LATE_TOPS)
    let mut top3: Option<(QubitId, QubitId, QubitId)> = None;
    let late = Y18_LATE_TOPS && !swap01;
    let mut pads18: Vec<QubitId> = Vec::new();
    let _ = y18_log();
    let a_pre0 = c.active_qubits();
    let (a_pre1, log0, log1);
    if swap01 {
        // first: X0' = T + 2 S'1 on bits [1, 257) (T has no bit 256); held: m1 = the carry into bit 255, h1 = the
        // carry into bit 256
        c.cx_all(s[1], b);
        (m1, kept1) = low_keep_add(c, &b[..N - 2], &tg[1..N - 1], proxy, rev, keep[1]);
        let h1 = m_carry(c, tg[N - 1], &l(b[N - 2]), m1);
        c.cx(b[N - 2], tg[N - 1]);
        c.cx(m1, tg[N - 1]);
        c.cx_all(s[1], b);
        e_add0 = c.expected_total();
        log0 = y18_log();
        a_pre1 = c.active_qubits();
        // second: X1' = X0' + S'0 on bits [0, 256); held: m0 = the carry into bit 255; g = its carry out
        c.cx_all(s[0], b);
        (m0, kept0) = low_keep_add(c, &b[..N - 1], &tg[..N - 1], proxy, rev, keep[0]);
        let g = m_carry(c, tg[N - 1], &l(b[N - 1]), m0);
        c.cx(b[N - 1], tg[N - 1]);
        c.cx(m0, tg[N - 1]);
        c.cx_all(s[0], b);
        // bits 256 and 257 of X1' are the sum and the carry of S'1[255], h1 and g (b holds the source as it is here)
        let s1top = Lin::of(&[b[N - 1], s[1]]);
        let x257 = maj_wire(c, &l(g), &s1top, &l(h1));
        c.cx(h1, g);
        lin_xor_into(c, &s1top, g);
        top3 = Some((g, h1, x257));
        e_add1 = c.expected_total();
        log1 = y18_log();
    } else {
        // add 0: X0 = T + S'0; held: m0 = the carry into bit 255
        c.cx_all(s[0], b);
        (m0, kept0) = low_keep_add(c, &b[..N - 1], &tg[..N - 1], proxy, rev, keep[0]);
        let x256e = if late {
            None
        } else {
            let q = m_carry(c, tg[N - 1], &l(b[N - 1]), m0);
            c.cx(b[N - 1], tg[N - 1]);
            c.cx(m0, tg[N - 1]);
            Some(q)
        };
        c.cx_all(s[0], b);
        e_add0 = c.expected_total();
        log0 = y18_log();
        if late && Y18_LATE_PAD {
            pads18.push(c.alloc_qubit());
        }
        a_pre1 = c.active_qubits();
        // add 1: X1 = X0 + 2 S'1 on bits [1, 257); held: m1, h1 = the carries into its top two positions
        c.cx_all(s[1], b);
        (m1, kept1) = low_keep_add(c, &b[..N - 2], &tg[1..N - 1], proxy, rev, keep[1]);
        if let Some(x256) = x256e {
            let h1 = m_carry(c, tg[N - 1], &l(b[N - 2]), m1);
            let x257 = m_carry(c, x256, &l(b[N - 1]), h1);
            c.cx(b[N - 1], x256);
            c.cx(h1, x256);
            c.cx(b[N - 2], tg[N - 1]);
            c.cx(m1, tg[N - 1]);
            top3 = Some((x256, h1, x257));
        }
        c.cx_all(s[1], b);
        e_add1 = c.expected_total();
        log1 = y18_log();
    }
    if late && Y18_LATE_PAD {
        pads18.extend(c.alloc_qubits(2));
    }
    let a_pre2 = c.active_qubits();
    // add 2: X = X1 + 4 S'2 on bits [2, 258); its top ripple [sp2, 256) stays open (register, source and carries
    // each on their own wires, sums not written) through the fold and the erases
    c.cx_all(s[2], b);
    let (k0, seed0) = cells::y15_split_spec(proxy, rev, N - 1);
    let (kk1, seed1) = cells::y15_split_spec(proxy, rev, N - 2);
    // (swap01: it is the first add's carry m1 whose erase builds a chain again, on its window and the guard)
    let sp2 = N - 3 - if swap01 { (kk1 + Y15_GUARD).max(k0) } else { (k0 + Y15_GUARD).max(kk1) };
    let (m2, kept2) = low_keep_add(c, &b[..sp2], &tg[2..2 + sp2], proxy, rev, keep[2]);
    for &q in &pads18 {
        c.release_clean(q); // never written
    }
    let (x256, h1, x257) = match top3 {
        Some(t) => t,
        None => {
            // y18-next: the tops of adds 0 and 1 now (b holds the source complemented by s2: S'i[j] = b[j] ^ s2 ^ si)
            let s0f = |i: usize| Lin::of(&[b[i], s[2], s[0]]);
            let s1f = |i: usize| Lin::of(&[b[i], s[2], s[1]]);
            let x256 = m_carry(c, tg[N - 1], &s0f(N - 1), m0);
            lin_xor_into(c, &s0f(N - 1), tg[N - 1]);
            c.cx(m0, tg[N - 1]);
            let h1 = m_carry(c, tg[N - 1], &s1f(N - 2), m1);
            let x257 = m_carry(c, x256, &s1f(N - 1), h1);
            lin_xor_into(c, &s1f(N - 1), x256);
            c.cx(h1, x256);
            lin_xor_into(c, &s1f(N - 2), tg[N - 1]);
            c.cx(m1, tg[N - 1]);
            (x256, h1, x257)
        }
    };
    let mut acc1: Vec<QubitId> = tg[1..].to_vec();
    acc1.push(x256);
    let mut acc2: Vec<QubitId> = tg[2..].to_vec();
    acc2.push(x256);
    acc2.push(x257);
    let kept = [kept0, kept1, kept2];
    let mut cc = vec![m2]; // cc[i - sp2] = the carry into index i of add 2
    for i in sp2..N {
        let q = m_carry(c, acc2[i], &l(b[i]), cc[i - sp2]);
        cc.push(q);
    }
    let cq = |i: usize| cc[i - sp2];
    let x258 = cq(N);
    for &q in &pad {
        c.release_clean(q); // never written
    }
    let e_add2 = c.expected_total();
    let a_fold = c.active_qubits();
    let log2 = y18_log();
    // the two lower top wires hold their sums while the fold reads them
    c.cx(b[N - 2], x256);
    c.cx(cq(N - 2), x256);
    c.cx(b[N - 1], x257);
    c.cx(cq(N - 1), x257);
    // y16-late: shed a block of add 2's ripple carries (see Y16_SHED): cq(i) = MAJ(acc2[i - 1], S'2[i - 1], cq(i - 1))
    // for i in [N - 3 - shed, N - 3), top down. They stay shed through the fold and the erases of the top wires, m0
    // and m1; m0's erase holds m2, the ripple's carries up to cq(N - 3), its chain of k0 + Y15_GUARD and k0 - 1 compare
    // carries.
    let room_now = cells::cap().saturating_sub(c.active_qubits() as usize);
    let live_m = 1 + (N - 3 - sp2);
    let shed_on = !kept.iter().any(|k| !k.is_empty()) && (!rev || !wc.is_empty() || lean_here || yg_here);
    let fmax = if rev { 2 } else { 6 };
    let (shed, tops, c3m, gsh, fin) = y16_shed(
        shed_on,
        if !rev {
            Y16_FIXED_FWD
        } else if lean_here {
            Y17_FIXED_REV_LEAN
        } else if yg_here {
            Y17_FIXED_REV_YGATE
        } else {
            Y16_FIXED_REV_COPY
        },
        room_now,
        cells::cap().saturating_sub(a_start as usize + live_m),
        if swap01 { kk1 + Y15_GUARD + kk1 - 1 } else { k0 + Y15_GUARD + k0 - 1 },
        N - 4 - sp2,
        fmax,
    );
    // the top carry: cq(N - 1) = MAJ(x256', S'2[N - 2], cq(N - 2)), and x256 holds its sum x256' ^ S'2[N - 2] ^ cq(N - 2)
    // y18-next: with the top wires leaving inside the forward fold (fin 4 to 6) the top carries are not shed here
    let esh_on = !rev && !swap01 && Y15_CORE_V2 && fin.max(Y18_FIN_MIN.min(fmax)) >= 4;
    let tops_pre = if esh_on { 0 } else { tops };
    if tops_pre >= 1 {
        c.cx(cq(N - 2), cq(N - 1));
        lin_and_erase(c, cq(N - 1), &Lin::of(&[x256, b[N - 2]]), &Lin::of(&[b[N - 2], cq(N - 2)]));
    }
    // y17-edge: the carry below it, cq(N - 2) = MAJ(X1[255], S'2[N - 3], cq(N - 3)) (tg[N - 1] holds X1[255]: add 2's
    // sum is not written there)
    if tops_pre >= 2 {
        m_carry_erase(c, cq(N - 2), tg[N - 1], &l(b[N - 3]), cq(N - 3));
    }
    // y17-edge: add 1's held top carry, h1 = MAJ(S'1[254], X0[255], m1), by the forms of its erase below
    let h1_forms = (Lin::of(&[tg[N - 1], b[N - 2], s[2], s[1]]), Lin::of(&[b[N - 2], s[2], s[1], m1]));
    if tops_pre >= 3 {
        c.cx(m1, h1);
        lin_and_erase(c, h1, &h1_forms.0, &h1_forms.1);
    }
    assert!(!swap01 || (shed, tops, c3m, gsh, fin) == (0, 0, 0, 0, 0), "y17: reverse tick 0 has no shed");
    let fin = if swap01 || !Y15_CORE_V2 { 0 } else { fin.max(Y18_FIN_MIN.min(fmax)) };
    let gsh = if swap01 { 0 } else { gsh.max(Y18_GSHED_MIN.min(Y15_GUARD.saturating_sub(1))) };
    let (sh_lo, sh_hi) = (N - 3 - shed, N - 3);
    for i in (sh_lo..sh_hi).rev() {
        m_carry_erase(c, cq(i), acc2[i - 1], &l(b[i - 1]), cq(i - 1));
    }
    let mut esh: Option<ESh> = esh_on.then(|| ESh { x256, x257, x258, h1, m0, m1, cq1: cq(N - 1), cq2: cq(N - 2), cq3: cq(N - 3), t255: tg[N - 1], b1: b[N - 1], b2: b[N - 2], b3: b[N - 3], s });
    let plan = if rev {
        // the reverse fold reads the source's low 6 bits as they are (b holds the source complemented by s[2])
        for j in 0..6 {
            c.cx(s[2], b[j]);
        }
        let plan = if Y15_CORE_V2 {
            fold_rev_v2(c, &tg[..Y15_WIN], [x256, x257, x258], s, k1, k2, &b[..6], &kept, &wc, lean_here, if swap01 { [2, 0, 1] } else { [2, 1, 0] }, &yg, fin)
        } else {
            fold_rev(c, &tg[..Y15_WIN], [x256, x257, x258], s, k1, k2, &b[..6], &wc)
        };
        for j in 0..6 {
            c.cx(s[2], b[j]);
        }
        for &q in &wc {
            c.release_clean(q); // cleared inside the fold (no reset: a copy left dirty would show in the checker)
        }
        plan
    } else if Y15_CORE_V2 {
        fold_fwd_v2(c, &tg[..Y15_WIN], [x256, x257, x258], s, k1, k2, fin, esh.as_mut())
    } else {
        fold_fwd(c, &tg[..Y15_WIN], [x256, x257, x258], s, k1, k2)
    };
    // y17-edge: h1 and cq(N - 2) again
    let h1 = if tops_pre >= 3 {
        let q = lin_and(c, &h1_forms.0, &h1_forms.1);
        c.cx(m1, q);
        q
    } else {
        h1
    };
    if tops_pre >= 2 {
        cc[N - 2 - sp2] = m_carry(c, tg[N - 1], &l(b[N - 3]), cc[N - 3 - sp2]);
    }
    // y18-next: the wires the forward fold built again
    let (x256, x257, x258, h1) = match &esh {
        Some(st) => {
            cc[N - 1 - sp2] = st.cq1;
            cc[N - 2 - sp2] = st.cq2;
            cc[N - sp2] = st.x258;
            (st.x256, st.x257, st.x258, st.h1)
        }
        None => (x256, x257, x258, h1),
    };
    // y16-late: the top carry again (x256 still holds its sum)
    if tops_pre >= 1 {
        let ci = cc[N - 2 - sp2];
        let q = lin_and(c, &Lin::of(&[x256, b[N - 2]]), &Lin::of(&[b[N - 2], ci]));
        c.cx(ci, q);
        cc[N - 1 - sp2] = q;
    }
    let cq = |i: usize| cc[i - sp2];
    let e_shed = c.expected_total();
    let logf = y18_log();
    c.cx(cq(N - 1), x257);
    c.cx(b[N - 1], x257);
    c.cx(cq(N - 2), x256);
    c.cx(b[N - 2], x256);
    let e_fold = e_shed;
    // the three top wires and the carries next to them (measurements and Clifford gates only)
    m_carry_erase(c, x258, x257, &l(b[N - 1]), cq(N - 1));
    m_carry_erase(c, cq(N - 1), x256, &l(b[N - 2]), cq(N - 2));
    m_carry_erase(c, cq(N - 2), tg[N - 1], &l(b[N - 3]), cq(N - 3));
    // x257 = MAJ(S'1[255], X0[256], h1), with X0[256] ^ h1 = X1[256] ^ S'1[255] and S'1 = b ^ s2 ^ s1
    // (swap01: x257 = MAJ(S'1[255], g, h1) and x256 holds g ^ h1 ^ S'1[255]: the same forms; x256 is then g)
    c.cx(h1, x257);
    lin_and_erase(c, x257, &Lin::of(&[x256, b[N - 1], s[2], s[1]]), &Lin::of(&[b[N - 1], s[2], s[1], h1]));
    lin_xor_into(c, &Lin::of(&[b[N - 1], s[2], s[1], h1]), x256); // x256 = X0[256]
    if swap01 {
        // h1 = MAJ(S'1[254], T[255], m1), with T[255] ^ m1 = X0'[255] ^ S'1[254] and X0'[255] = X1'[255] ^ S'0[255] ^ m0
        c.cx(m1, h1);
        lin_and_erase(
            c,
            h1,
            &Lin::of(&[tg[N - 1], b[N - 1], s[2], s[0], m0, b[N - 2], s[2], s[1]]),
            &Lin::of(&[b[N - 2], s[2], s[1], m1]),
        );
        // g = MAJ(S'0[255], X0'[255], m0), with X0'[255] ^ m0 = X1'[255] ^ S'0[255]
        c.cx(m0, x256);
        lin_and_erase(c, x256, &Lin::of(&[tg[N - 1], b[N - 1], s[2], s[0]]), &Lin::of(&[b[N - 1], s[2], s[0], m0]));
    } else {
        // h1 = MAJ(S'1[254], X0[255], m1), with X0[255] ^ m1 = X1[255] ^ S'1[254]
        c.cx(m1, h1);
        lin_and_erase(c, h1, &Lin::of(&[tg[N - 1], b[N - 2], s[2], s[1]]), &Lin::of(&[b[N - 2], s[2], s[1], m1]));
        // x256 = MAJ(S'0[255], T[255], m0), with T[255] ^ m0 = X0[255] ^ S'0[255] = X1[255] ^ S'1[254] ^ m1 ^ S'0[255]
        c.cx(m0, x256);
        lin_and_erase(
            c,
            x256,
            &Lin::of(&[tg[N - 1], b[N - 2], s[2], s[1], m1, b[N - 1], s[2], s[0]]),
            &Lin::of(&[b[N - 1], s[2], s[0], m0]),
        );
    }
    let e_tops = c.expected_total();
    // y17-edge: cq(N - 3) is idle until the ripple is closed; its inputs are shed, so it is measured now and its phase
    // fixed when it is built again
    let c3_bit = (c3m == 1).then(|| {
        let m = c.alloc_bit();
        c.hmr(cc[N - 3 - sp2], m);
        c.release_clean(cc[N - 3 - sp2]);
        m
    });
    let e_m0;
    if swap01 {
        // y17-edge: the mirror of the joint erase below. m1 (the first add's held carry, into its position N - 2) needs
        // X0' on its window, which lies under the second add: X0'[j] = X1'[j] ^ S'0[j] ^ C0[j]. The second add's carries
        // C0 are built again from Y15_GUARD bits below the window; one step more gives C0[N - 1], m0's own value.
        let s0f = |i: usize| Lin::of(&[b[i], s[2], s[0]]);
        let split1 = N - 2;
        let lo1 = split1 - kk1;
        let jmin = lo1 + 1;
        let i0 = jmin - Y15_GUARD;
        assert!(sp2 + 2 <= i0 && i0 >= 1);
        let bit_o = c.alloc_bit();
        c.hmr(m1, bit_o);
        c.release_clean(m1);
        let bit_i = c.alloc_bit();
        c.hmr(m0, bit_i);
        c.free(m0);
        c.push_condition(bit_o);
        let mut r: Vec<Lin> = vec![s0f(i0 - 1)]; // r[j - i0] = C0[j]
        let mut rr: Vec<(QubitId, Lin, Lin, Lin)> = Vec::new();
        for j in i0..N - 1 {
            let ci = r[j - i0].clone();
            let (fa, fb) = (s0f(j).x(&ci), l(tg[j]).x(&s0f(j)));
            let q = lin_and(c, &fa, &fb);
            lin_xor_into(c, &ci, q);
            rr.push((q, fa, fb, ci));
            r.push(l(q));
        }
        let top = rr.last().expect("y17: the rebuilt chain is not empty").0; // C0[N - 1] = m0
        c.push_condition(bit_i);
        c.cz(top, top);
        c.pop_condition();
        for j in jmin..N - 1 {
            lin_xor_into(c, &s0f(j).x(&r[j - i0]), tg[j]);
        }
        let blo = seed1.map_or(lo1, |sd| sd.min(lo1));
        for i in blo..split1 {
            c.cx(s[2], b[i]);
            c.cx(s[1], b[i]);
        }
        super::super::compare::cmp_lt_phase(c, &tg[lo1 + 1..split1 + 1], &b[lo1..split1], seed1.map(|sd| b[sd]));
        for i in blo..split1 {
            c.cx(s[1], b[i]);
            c.cx(s[2], b[i]);
        }
        for j in (jmin..N - 1).rev() {
            lin_xor_into(c, &s0f(j).x(&r[j - i0]), tg[j]);
        }
        while let Some((q, fa, fb, ci)) = rr.pop() {
            lin_xor_into(c, &ci, q);
            lin_and_erase(c, q, &fa, &fb);
        }
        c.pop_condition();
        e_m0 = c.expected_total();
        // m0: the cells' chunk compare at index 255 of the second add, on its own sum bits, only when its bit is set
        // and m1's is not
        let nb = c.alloc_bit();
        c.bit_store1(nb);
        c.bit_xor_into(nb, bit_o);
        let split0 = N - 1;
        let lo0 = split0 - k0;
        assert!(sp2 + 2 <= lo0);
        let blo = seed0.map_or(lo0, |sd| sd.min(lo0));
        for i in blo..split0 {
            c.cx(s[2], b[i]);
            c.cx(s[0], b[i]);
        }
        c.push_condition(bit_i);
        c.push_condition(nb);
        super::super::compare::cmp_lt_phase(c, &tg[lo0..split0], &b[lo0..split0], seed0.map(|sd| b[sd]));
        c.pop_condition();
        c.pop_condition();
        for i in blo..split0 {
            c.cx(s[0], b[i]);
            c.cx(s[2], b[i]);
        }
        c.free_bit(nb);
        c.free_bit(bit_i);
        c.free_bit(bit_o);
    } else if Y15_JOINT_M {
        // m0 and m1 are measured together. m0's fix builds add 1's carries again on its window; one step more and the
        // chain's top wire is the carry into bit 255 of add 1, which is m1's own value: m1's fix is then a Z on it.
        // m1's own chunk compare runs only when m0's branch did not (a quarter of the shots, not a half).
        let split = N - 1;
        let lo = split - k0;
        let i0 = lo - 1 - Y15_GUARD;
        assert!(sp2 + 2 <= i0 + 1 && i0 >= 1);
        let s1f = |i: usize| Lin::of(&[b[i], s[2], s[1]]);
        let bit0 = c.alloc_bit();
        c.hmr(m0, bit0);
        c.release_clean(m0);
        let bit1 = c.alloc_bit();
        c.hmr(m1, bit1);
        c.free(m1);
        c.push_condition(bit0);
        let mut r: Vec<Lin> = vec![s1f(i0 - 1)]; // r[j] = C1[i0 + j]
        let mut rr: Vec<(QubitId, Lin, Lin, Lin)> = Vec::new();
        for i in i0..split - 1 {
            let ci = r[i - i0].clone();
            let (fa, fb) = (s1f(i).x(&ci), l(tg[i + 1]).x(&s1f(i)));
            let q = lin_and(c, &fa, &fb);
            lin_xor_into(c, &ci, q);
            rr.push((q, fa, fb, ci));
            r.push(l(q));
        }
        let top = rr.last().expect("y15: the rebuilt chain is not empty").0; // C1[split - 1] = m1
        c.push_condition(bit1);
        c.cz(top, top);
        c.pop_condition();
        for j in lo..split {
            lin_xor_into(c, &s1f(j - 1).x(&r[j - 1 - i0]), tg[j]);
        }
        // y18-next: the guard carries rr[0..gsh) (C1[i0 + 1 ..= i0 + gsh]) are idle through the compare and no window
        // form reads them (those read r[Y15_GUARD..]); their own forms read tg below the window, which is as it was
        assert!(gsh == 0 || (gsh < Y15_GUARD && gsh < rr.len()));
        for m in (0..gsh).rev() {
            let (q, fa, fb, ci) = rr[m].clone();
            lin_xor_into(c, &ci, q);
            lin_and_erase(c, q, &fa, &fb);
        }
        let blo = seed0.map_or(lo, |sd| sd.min(lo));
        for i in blo..split {
            c.cx(s[2], b[i]);
            c.cx(s[0], b[i]);
        }
        super::super::compare::cmp_lt_phase(c, &tg[lo..split], &b[lo..split], seed0.map(|sd| b[sd]));
        for i in blo..split {
            c.cx(s[0], b[i]);
            c.cx(s[2], b[i]);
        }
        // the guard carries again, bottom up (fresh wires: the forms of each and of the first carry above them are
        // made again on the new wires)
        for m in 0..gsh {
            let i = i0 + m;
            let ci = if m == 0 { s1f(i0 - 1) } else { l(rr[m - 1].0) };
            let (fa, fb) = (s1f(i).x(&ci), l(tg[i + 1]).x(&s1f(i)));
            let q = lin_and(c, &fa, &fb);
            lin_xor_into(c, &ci, q);
            rr[m] = (q, fa, fb, ci);
        }
        if gsh > 0 {
            let ci = l(rr[gsh - 1].0);
            let fa = s1f(i0 + gsh).x(&ci);
            let (q, _, fb, _) = rr[gsh].clone();
            rr[gsh] = (q, fa, fb, ci);
        }
        for j in (lo..split).rev() {
            lin_xor_into(c, &s1f(j - 1).x(&r[j - 1 - i0]), tg[j]);
        }
        while let Some((q, fa, fb, ci)) = rr.pop() {
            lin_xor_into(c, &ci, q);
            lin_and_erase(c, q, &fa, &fb);
        }
        c.pop_condition();
        e_m0 = c.expected_total();
        // m1: the cells' chunk compare at index 254 of add 1, only when bit1 is set and bit0 is not
        let nb = c.alloc_bit();
        c.bit_store1(nb);
        c.bit_xor_into(nb, bit0);
        let split = N - 2;
        let lo = split - kk1;
        assert!(sp2 + 2 <= lo + 1);
        let blo = seed1.map_or(lo, |sd| sd.min(lo));
        for i in blo..split {
            c.cx(s[2], b[i]);
            c.cx(s[1], b[i]);
        }
        c.push_condition(bit1);
        c.push_condition(nb);
        super::super::compare::cmp_lt_phase(c, &acc1[lo..split], &b[lo..split], seed1.map(|sd| b[sd]));
        c.pop_condition();
        c.pop_condition();
        for i in blo..split {
            c.cx(s[1], b[i]);
            c.cx(s[2], b[i]);
        }
        c.free_bit(nb);
        c.free_bit(bit1);
        c.free_bit(bit0);
    } else {
        // m0: the compare [X0 < S'0] on bits [lo, 255); X0[j] = X1[j] ^ S'1[j - 1] ^ C1[j - 1], add 1's carries built
        // again from Y15_GUARD bits below the window (seeded with the source bit below), all on the measured half
        {
            let split = N - 1;
            let lo = split - k0;
            let i0 = lo - 1 - Y15_GUARD;
            assert!(sp2 + 2 <= i0 + 1 && i0 >= 1);
            let s1f = |i: usize| Lin::of(&[b[i], s[2], s[1]]);
            let bit = c.alloc_bit();
            c.hmr(m0, bit);
            c.release_clean(m0);
            c.push_condition(bit);
            let mut r: Vec<Lin> = vec![s1f(i0 - 1)]; // r[j] = C1[i0 + j]
            let mut rr: Vec<(QubitId, Lin, Lin, Lin)> = Vec::new();
            for i in i0..split - 2 {
                let ci = r[i - i0].clone();
                let (fa, fb) = (s1f(i).x(&ci), l(tg[i + 1]).x(&s1f(i)));
                let q = lin_and(c, &fa, &fb);
                lin_xor_into(c, &ci, q);
                rr.push((q, fa, fb, ci));
                r.push(l(q));
            }
            for j in lo..split {
                lin_xor_into(c, &s1f(j - 1).x(&r[j - 1 - i0]), tg[j]);
            }
            let blo = seed0.map_or(lo, |sd| sd.min(lo));
            for i in blo..split {
                c.cx(s[2], b[i]);
                c.cx(s[0], b[i]);
            }
            super::super::compare::cmp_lt_phase(c, &tg[lo..split], &b[lo..split], seed0.map(|sd| b[sd]));
            for i in blo..split {
                c.cx(s[0], b[i]);
                c.cx(s[2], b[i]);
            }
            for j in (lo..split).rev() {
                lin_xor_into(c, &s1f(j - 1).x(&r[j - 1 - i0]), tg[j]);
            }
            while let Some((q, fa, fb, ci)) = rr.pop() {
                lin_xor_into(c, &ci, q);
                lin_and_erase(c, q, &fa, &fb);
            }
            c.pop_condition();
            c.free_bit(bit);
        }
        e_m0 = c.expected_total();
        // m1: the cells' chunk compare at index 254 of add 1 (sum bits tg[255 - k, 255), source as S'1)
        {
            let split = N - 2;
            let lo = split - kk1;
            assert!(sp2 + 2 <= lo + 1);
            let blo = seed1.map_or(lo, |sd| sd.min(lo));
            for i in blo..split {
                c.cx(s[2], b[i]);
                c.cx(s[1], b[i]);
            }
            cells::y15_erase_cmp(c, m1, &acc1[lo..split], &b[lo..split], seed1.map(|sd| b[sd]));
            c.free(m1);
            for i in blo..split {
                c.cx(s[1], b[i]);
                c.cx(s[2], b[i]);
            }
        }
    }
    let e_m1 = c.expected_total();
    let logm = y18_log();
    // y16-late: the shed carries again, bottom up
    for i in sh_lo..sh_hi {
        cc[i - sp2] = m_carry(c, acc2[i - 1], &l(b[i - 1]), cc[i - 1 - sp2]);
    }
    if let Some(m) = c3_bit {
        let q = m_carry(c, acc2[N - 4], &l(b[N - 4]), cc[N - 4 - sp2]);
        c.z_if(q, m);
        c.free_bit(m);
        cc[N - 3 - sp2] = q;
    }
    let cq = |i: usize| cc[i - sp2];
    // close add 2's top ripple, then its split carry with the cells' chunk compare
    for i in (sp2..N - 2).rev() {
        c.cx(b[i], acc2[i]);
        c.cx(cq(i), acc2[i]);
        if i > sp2 {
            m_carry_erase(c, cq(i), acc2[i - 1], &l(b[i - 1]), cq(i - 1));
        }
    }
    let (kk2, seed2) = cells::y15_split_spec(proxy, rev, sp2);
    cells::y15_erase_cmp(c, m2, &acc2[sp2 - kk2..sp2], &b[sp2 - kk2..sp2], seed2.map(|sd| b[sd]));
    c.free(m2);
    c.cx_all(s[2], b);
    let e_end = c.expected_total();
    assert_eq!(c.active_qubits(), a_start, "y15: a wire was left behind");
    if Y15_TRACE {
        eprintln!(
            "Y15_NEW {} t={t} active={a_start} room={} low={} at_fold={a_fold} sp2={sp2} k0={k0} k1={kk1} k2={kk2} seeds={:?} plan={plan:?} shed={shed} top={tops} c3m={c3m} gsh={gsh} fin={fin} \
             add0={:.1} add1={:.1} add2={:.1} fold={:.1} tops={:.1} m0={:.1} m1={:.1} close={:.1} body={:.1}",
            if rev { "rev" } else { "fwd" },
            cells::cap().saturating_sub(a_start as usize),
            if !rev { "-" } else if lean_here { "lean" } else if yg_here { "ygate" } else if copy_here { "copy" } else if keep_on { "keep" } else { "chains" },
            (seed0, seed1, seed2),
            e_add0 - e_start,
            e_add1 - e_add0,
            e_add2 - e_add1,
            e_fold - e_add2,
            e_tops - e_shed,
            e_m0 - e_tops,
            e_m1 - e_m0,
            e_end - e_m1,
            e_end - e_start
        );
        let cap = cells::cap();
        let logc = y18_log();
        eprintln!(
            "Y18_ADDS {} t={t} proxy={proxy} rooms=[{},{},{},{}] held=[{},{},{},{}] kk=[{k0},{kk1},{kk2}] A0:: {log0} A1:: {log1} A2:: {log2} F:: {logf} M:: {logm} C:: {logc}",
            if rev { "rev" } else { "fwd" },
            cap.saturating_sub(a_pre0 as usize),
            cap.saturating_sub(a_pre1 as usize),
            cap.saturating_sub(a_pre2 as usize),
            cap.saturating_sub(a_fold as usize),
            a_pre0 - a_start,
            a_pre1 - a_start,
            a_pre2 - a_start,
            a_fold - a_start
        );
    }
}

/// y16-late: [`body`] with its peak live count checked against the walk cap (m0's erase has no check of its own).
#[allow(clippy::too_many_arguments)]
fn body_capped(c: &mut Builder, t: usize, s: [QubitId; 3], k1: QubitId, k2: QubitId, b: &[QubitId], tg: &[QubitId], proxy: usize, rev: bool) {
    super::super::pingpong::Y17_EXTRA.with(|e| e.set(Y18_PRICE));
    let ((), peak) = c.r3_peak(|c| body(c, t, s, k1, k2, b, tg, proxy, rev));
    let dir = if rev { "rev" } else { "fwd" };
    if Y15_TRACE {
        eprintln!("Y16_PEAK {dir} t={t} peak={peak} cap={}", cells::cap());
    }
    assert!(peak as usize <= cells::cap(), "y16: the one-fold tick {dir} t={t} peaks at {peak}, over the walk cap {}", cells::cap());
    super::super::pingpong::Y17_EXTRA.with(|e| e.set(0));
}

/// Forward one-fold payload tick: `tgt <- (tgt + (-1)^s0 src + 2 (-1)^s1 src + 4 (-1)^s2 src) 2^-(3 + e) (mod p)`,
/// e = k1 + 2 k2: the map of two `add_halve` cells and the merged op.
pub(super) fn fwd_tick(c: &mut Builder, t: usize, letter: &[QubitId], p: &mut [Vec<QubitId>; 2]) {
    let [w, ..] = steps()[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let (_, proxy) = proxy_fold(w, false);
    let (s, k1, k2) = ([letter[0], letter[1], letter[2]], letter[3], letter[4]);
    let (tg, b) = (p[ti].clone(), p[si].clone());
    let (e0, a0) = (c.expected_total(), c.active_qubits());
    let shift = cmp_shift_at(t);
    cells::with_tie(None, || cells::with_cmp_shift((shift.0 + Y15_CMP_EXTRA, shift.1), || cells::with_bridge(proxy, false, || body_capped(c, t, s, k1, k2, &b, &tg, proxy, false))));
    for _ in 0..3 {
        rot1(c, &tg, true);
    }
    rot4(c, k1, k2, &tg, false);
    if Y15_TRACE {
        eprintln!("Y15_TICK fwd t={t} active={a0} cost={:.1}", c.expected_total() - e0);
    }
}

/// Reverse one-fold payload tick (the inverse map of [`fwd_tick`]): `tgt <- 2^(3 + e) tgt - ((-1)^s0 + 2 (-1)^s1 +
/// 4 (-1)^s2) src (mod p)`: the map of the reverse merged op and two `double_add` cells.
pub(super) fn rev_tick(c: &mut Builder, t: usize, letter: &[QubitId], p: &mut [Vec<QubitId>; 2]) {
    let [w, ..] = steps()[t];
    let (ti, si) = (t % 2, 1 - t % 2);
    let (_, proxy) = proxy_fold(w, true);
    let (s, k1, k2) = ([letter[0], letter[1], letter[2]], letter[3], letter[4]);
    let (tg, b) = (p[ti].clone(), p[si].clone());
    let (e0, a0) = (c.expected_total(), c.active_qubits());
    rot4(c, k1, k2, &tg, true);
    for _ in 0..3 {
        rot1(c, &tg, false);
    }
    for q in s {
        c.x(q);
    }
    let shift = cmp_shift_at(t);
    cells::with_tie(None, || cells::with_cmp_shift((shift.0 + Y15_CMP_EXTRA, shift.1), || cells::with_bridge(proxy, true, || body_capped(c, t, s, k1, k2, &b, &tg, proxy, true))));
    for q in s {
        c.x(q);
    }
    if Y15_TRACE {
        eprintln!("Y15_TICK rev t={t} active={a0} cost={:.1}", c.expected_total() - e0);
    }
}
