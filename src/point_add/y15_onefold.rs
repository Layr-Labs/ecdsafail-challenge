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
/// y19 research price knob (0 = no effect on the gates): from the end of the three adds to the end of the erases of
/// m0 and m1 (the shed decision, the fold and both erases) the walk cap is read this many wires higher still. It
/// prices wires that a change would free from the fold on (for example the three held wires m0, m1, h1). A non-zero
/// value is a PRICE, never a build: the peak goes over 1236.
const Y19_PRICE_FOLD: isize = 0;
/// y20-ripple (10 October 2026), "direct cuts": the chunked parts of adds 0 and 1 run one bit higher (256 and 255
/// bits), so the wire each leaves is its carry into bit 256: g0 = X0[256], which becomes the top wire x256, and h1.
/// The carries into bit 255 (m0, m1) are then inner carries of the last chunks and no wire is held for them. The two
/// compares that erase the held carries move up one bit (windows tg[N - k, N) for tg[N - 1 - k, N - 1)), and add 2's
/// open ripple starts one bit higher. Same Toffoli; 3 wires fewer from the end of the adds to the end of the erases.
/// h1 has no exact erase any more, so at most 2 top carries are shed around the fold, and the forward fold's own shed
/// of the top wires (fin 4, 5) leaves x256 and h1 in place. Not on reverse tick 0. false: as candidate V.
/// Builder counts at peak 1236 on candidate V (768640.2, gate list e957530d; both y20 switches off give it byte for
/// byte), 10 October 2026:
///   Y20_CUT, ranges 130 / 124:            expected=768229.2 (5bc60bb1; against V 0 outputs differ on 30 draws and on
///     both stress files, phase shots 345 / 337)
///   and reverse TO = 125 (tick 124 fits):  expected=768197.9 (303b7654; 0 differ on 30 draws; slope file 710 differ,
///     13 wrong only in V and 4 only here; denominator file 0)
/// Reverse TO = 126 and forward TO = 131 are each one wire short: the cuts free 3 wires and take 2 (reverse) or 3
/// (forward) places from the shed.
const Y20_CUT: bool = true;
/// y20-ripple, "closed ripple": on these ticks ([from, to)) add 2's chunked part runs to the top (its held carry m2
/// is the carry into the top wire x256, or into bit 255 without Y20_CUT) and no ripple stays open over the windows of
/// the two held carries. Their erases then read the register through add 2: its carries are built again on the window
/// (k + Y20_G2 Toffoli, on the 3/4 of the shots where either measures 1), and that chain's top wire is m2's own
/// value, so m2's compare runs on 1/8 of the shots. k wires fewer from the fold to the end of the erases, for
/// (3k + 3)/8 Toffoli a pass. Needs the room for two rebuilt chains and a compare (3k + 1). Empty: off.
/// It also puts k more bits into add 2's chunked part, which takes one more chunk on most passes. Builder counts:
///   alone on V, forward [80, 109) and reverse [1, 108):                         expected=768686.6 (46.4 over V)
///   on the head, every pass where it fits (forward [1, 109), reverse [1, 108)):  expected=768598.6 (400.7 over)
///   on the head, forward [(83, 87), (96, 107)], reverse [(81, 84), (86, 87), (93, 104), (106, 108)]:
///                                                                                expected=768146.8 (51.1 under; 7e219890)
///   the same without reverse 106, 107, Y20_G2 = 0 / 2 / 4:                       768150.8 / 768195.8 / 768240.8
/// Off at the head: under the round's bar, and 116 more phase shots than the head on the slope stress file.
const Y20_CLOSE_FWD: &[(usize, usize)] = &[];
const Y20_CLOSE_REV: &[(usize, usize)] = &[];
/// Bits below the window on which the closed ripple's rebuilt chain of add 2 starts (0: seeded just under the window).
const Y20_G2: usize = 0;
fn y20_close_on(t: usize, rev: bool) -> bool {
    (if rev { Y20_CLOSE_REV } else { Y20_CLOSE_FWD }).iter().any(|&(a, b)| t >= a && t < b)
}
/// y21-shed (10 October 2026), "top cut": on these ticks ([from, to)) add 1's chunked part runs to the top (256 bits;
/// its top target bit is the wire that holds add 0's cut carry g0), so the wire it leaves is its carry out x257 and
/// h1 (its carry into bit 256) is never held: one wire fewer from the end of add 2 to the joint erase. x257 has no
/// exact erase without h1, so it stays through the fold and the erase of the top wires and is measured first in the
/// joint erase. Its fix needs h1: when its bit is set, add 1's chain is built (the chain of g0's erase, the same
/// window and seed), one step more gives x257's value (Z), and the chain's top turns the wire x256 (g0 ^ h1) into g0
/// before that is measured; g0's compare then runs on the chain as today. When x257's bit is clear, x256 is measured
/// as g0 ^ h1 and the chain runs only when its bit is set, with a Z on its top for h1. By count at k = 20:
/// 24.5 expected Toffoli for 24.25 (chain 20 on 1/2, compare 19 on 1/4; chain and compare on 1/4; x257's own fix
/// is a CZ and a Z once h1 is on a wire).
/// Add 1's own compare is not run. The forward fold's own shed of the top wires then takes x258 alone (fin 4).
/// Needs Y20_CUT; not with the closed ripple. Empty: off (candidate W byte for byte).
const Y21_TOP_FWD: &[(usize, usize)] = &[(1, 86), (91, 106), (107, 999)];
const Y21_TOP_REV: &[(usize, usize)] = &[(1, 84), (89, 103), (104, 999)];
fn y21_top_on(t: usize, rev: bool) -> bool {
    (if rev { Y21_TOP_REV } else { Y21_TOP_FWD }).iter().any(|&(a, b)| t >= a && t < b)
}
/// y21-shed, "deep shed": on these ticks the last ripple carry cq(N - 3) leaves around the fold as well (one more
/// place). The erase of the top wires right after the fold reads it, and its own erase reads the carry below, so the
/// whole block is built again after the fold (forward: after the ladder, inside the fold's own shed of the top wires;
/// reverse: right after the fold), the top wires are erased, and the block is shed again for the erases of the held
/// carries. Exact (measured erases and rebuilds only); block + 1 Toffoli more on the pass. Needs the whole block shed
/// there. Empty: off.
const Y21_DEEP_FWD: &[(usize, usize)] = &[(130, 131)];
const Y21_DEEP_REV: &[(usize, usize)] = &[(126, 127)];
fn y21_deep_on(t: usize, rev: bool) -> bool {
    (if rev { Y21_DEEP_REV } else { Y21_DEEP_FWD }).iter().any(|&(a, b)| t >= a && t < b)
}
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
    /// y20 (Y20_CUT): x256 and h1 are the adds' cut carries and stay; only x258, the two top carries and x257 leave
    direct: bool,
    /// y21 (top cut): there is no h1 and x257 stays too; only x258 and the two top carries leave
    top1: bool,
    /// y21 (deep shed): the ripple's carries from m2 (index 0, stays) up to cq(N - 3) (the last, = cq3), with the
    /// register and source wires each is the majority of; empty: off
    deep_c: Vec<QubitId>,
    deep_a: Vec<QubitId>,
    deep_b: Vec<QubitId>,
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
    for j in (1..st.deep_c.len()).rev() {
        m_carry_erase(c, st.deep_c[j], st.deep_a[j - 1], &l(st.deep_b[j - 1]), st.deep_c[j - 1]);
    }
    if st.top1 {
        return; // x256 holds X1[256] and x257 its own value, both without add 2's sums
    }
    let (f1, f2) = st.f();
    c.cx(st.h1, st.x257);
    lin_and_erase(c, st.x257, &f1, &f2);
    lin_xor_into(c, &f2, st.x256); // x256 = X0[256]
    if st.direct {
        return;
    }
    let (h1, h2) = st.h();
    c.cx(st.m1, st.h1);
    lin_and_erase(c, st.h1, &h1, &h2);
    let (g1, g2) = st.g();
    c.cx(st.m0, st.x256);
    lin_and_erase(c, st.x256, &g1, &g2);
}
/// Build the six wires again, in the opposite order (fresh wires).
fn esh_in(c: &mut Builder, st: &mut ESh) {
    if !st.direct {
        let (g1, g2) = st.g();
        st.x256 = lin_and(c, &g1, &g2);
        c.cx(st.m0, st.x256);
        let (h1, h2) = st.h();
        st.h1 = lin_and(c, &h1, &h2);
        c.cx(st.m1, st.h1);
    }
    if !st.top1 {
        let (_, f2) = st.f();
        lin_xor_into(c, &f2, st.x256); // x256 = X1[256]
        let (f1, f2) = st.f();
        st.x257 = lin_and(c, &f1, &f2);
        c.cx(st.h1, st.x257);
    }
    for j in 1..st.deep_c.len() {
        st.deep_c[j] = m_carry(c, st.deep_a[j - 1], &l(st.deep_b[j - 1]), st.deep_c[j - 1]);
    }
    if st.deep_c.len() > 1 {
        st.cq3 = st.deep_c[st.deep_c.len() - 1];
    }
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
/// y28-loop (card s2-2), forward fold on the ticks where [`Y15_LEAN45`] fires: sums 4 and 5 are written before the
/// ladder (the carries into bits 4 and 5 are still measured away there, with today's forms), and after the ladder
/// nothing reads those two carries as values but the erase of the carry into bit 6. That carry is X-measured and the
/// two are built again only under its bit: c4 = AND(acc[3], c3), c5 = AND(acc[4] ^ a4, a4 ^ c4) ^ c4 on the written
/// sum, the phase is CZ(acc[5] ^ a5, a5 ^ c5) and Z(c5), and both are measured away again under the same bit at the
/// places today's undo measures them (the gate list keeps the head's measurements in the head's order).
/// 1 expected Toffoli for 2 on each such pass. false = the head, gate for gate.
const Y28_LEAN_FWD: bool = true;
/// y28-loop (card s2-4, step 1), reverse fold with the gate wires built first: the AND of the shift letter is read
/// only by the clearing of y5 (its gate form is that AND) and of y3 (k1 ^ k2 ^ the AND), each under that wire's
/// measured bit. It is built into a wire that holds 0 only where one of those bits is set (y5's, or with y5's clear
/// y3's: 3/4 of the shots) and measured away at the head's place under the OR of the two. 0.75 expected Toffoli for 1
/// on each such pass; the gate list keeps the head's measurements in the head's order. false = the head, gate for gate.
const Y28_TT_REV: bool = true;
/// y28-loop (card s2-4, step 2), forward fold: the same for the AND of the shift letter where it leaves for the
/// ladder. After the ladder only the erases of y5 (forms: the AND, sum 5) and y3 (k1 ^ k2 ^ the AND, sum 3) read it,
/// each under its own measured bit: it is built under y5's bit, or with that clear under y3's (0.75 expected Toffoli
/// for the 1 of [`Y18_FIN`]'s third wire), and measured away at the head's place under the OR of the two.
/// At that price it is the first wire to leave on a pass that sheds for the fold: one carry fewer in the block (or
/// one top wire fewer), 0.75 for 1. false = the head, gate for gate.
const Y28_TT_FWD: bool = true;
/// y28-loop (card s2-5), reverse fold on the passes where [`Y15_LEAN45`] fires (gate wires first or lean chains): as
/// [`Y28_LEAN_FWD`], sums 4 and 5 are written before the ladder. After it the register's old bits 4 and 5 are the
/// forms acc[4] ^ n0 ^ c4 and acc[5] ^ n1 ^ c5, read by the clearing of the gate wires (y5's branch reads both, y4's
/// reads bit 4, y3's neither) and by the erase of the carry into bit 6. The two carries are built into wires that
/// hold 0 only on the branches that read them: c4 where y5's bit, y4's or c6's is set (7/8 of the shots), c5 where
/// y5's or c6's is (3/4); each is measured away at the head's place under the OR of those bits. 1.625 expected
/// Toffoli for 2 on each such pass. false = the head, gate for gate.
const Y28_LEAN_REV: bool = true;
/// y28-loop (card s2-1): on these ticks ([from, to), wires) the fold's ladder runs on 1 or 2 wires fewer than
/// [`merged_plan`]'s least budget of 10. A kept carry named in the plan's drop list is X-measured as soon as the next
/// chunk has read it (its exact compare on its own chunk, the carry below still live: the cost it has at the end
/// today). At the end the erase of the kept carry above it lacks its carry-in: under that carry's measured bit the
/// dropped one is built again as a value (its chunk's carry chain on the written sums, one AND a bit; the chain's
/// lower carries are measured away at once), the compare runs, and the rebuilt carry is X-measured again with its own
/// compare under its bit. One wire for 2.75 expected Toffoli, two for 10.0 (netlist model: 0 wrong windows, 0 unclean
/// wires on 262,144 forward and 1,048,576 reverse inputs). On such a tick the deep shed ([`Y21_DEEP_FWD`]) is off.
/// Empty: off (the head, gate for gate).
/// Kept: one wire on the last one-fold tick of each direction (card s2-1). NOT kept: card s2-3, the one-fold range
/// one tick wider with two wires dropped there ([`Y15_FUSED_FWD_TO`] = 132 and [`Y15_FUSED_REV_TO`] = 128 with
/// (131, 132, 2) and (127, 128, 2) added here). It builds at peak 1,236 and is 73.75 Toffoli cheaper, but a one-fold
/// pass in place of a three-fold pass fails on other inputs: on 90 draws 3 shots pass in entry Y and fail there, 8
/// the other way, 1 output differs. An error trade, not an exact change.
const Y28_DROP_FWD: &[(usize, usize, usize)] = &[(130, 131, 1)];
const Y28_DROP_REV: &[(usize, usize, usize)] = &[(126, 127, 1)];
fn y28_drop(t: usize, rev: bool) -> usize {
    (if rev { Y28_DROP_REV } else { Y28_DROP_FWD }).iter().find(|&&(a, b, _)| t >= a && t < b).map_or(0, |&(_, _, n)| n)
}
/// y28 DIAGNOSTIC, used only with leapfrog.rs's `Y28_ALIGNED` (the aligned copy, never an entry): (tick, n) = n idle
/// measurements (of a wire that holds 0) on that one-fold pass, between the erase of the top wires and the erases of
/// the held carries. A pass that runs the dropped-carry ladder in place of the deep shed has fewer measurements than
/// the head's (the deep shed measures its block three times); with the difference put back the gate list draws the
/// head's number of random words from there on, and a paired run compares phase flags shot by shot. Every measurement
/// between the adds and this point is an exact erase in both gate lists, so which random word each one draws does
/// not matter.
const Y28_PADS_FWD: &[(usize, usize)] = &[(130, 9)];
const Y28_PADS_REV: &[(usize, usize)] = &[(126, 10)];
fn y28_pads(t: usize, rev: bool) -> usize {
    if !Y28_ALIGNED {
        return 0;
    }
    (if rev { Y28_PADS_REV } else { Y28_PADS_FWD }).iter().find(|&&(a, _)| a == t).map_or(0, |&(_, n)| n)
}
/// The ladder's plans on bits [6, 56) for budgets 9 and 8 with the 0-based chunks whose kept carry is dropped
/// (experiments/y28-loop/s2/ladder_drop.py: the cheapest of each kind).
const Y28_PLAN9: ([usize; 10], [usize; 1]) = ([4, 8, 8, 7, 6, 5, 4, 3, 2, 3], [0]);
const Y28_PLAN8: ([usize; 10], [usize; 2]) = ([7, 7, 7, 6, 6, 5, 4, 3, 2, 3], [0, 2]);
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
/// y20-ripple (10 October 2026, base = candidate V, 768640.2 x 1236 with 130 / 124): with Y20_CUT reverse TO = 125
/// (expected=768197.9); see Y20_CUT for the counts and for why 131 / 126 do not fit.
pub(super) const Y15_FUSED_FWD_FROM: usize = 0;
pub(super) const Y15_FUSED_FWD_TO: usize = 131;
pub(super) const Y15_FUSED_REV_FROM: usize = 0;
pub(super) const Y15_FUSED_REV_TO: usize = 127;
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
fn y16_shed(on: bool, fixed: usize, room_fold: usize, room_m: usize, need_m: usize, pool: usize, fmax: usize, tops_max: usize, at: (bool, usize), drop: usize) -> (usize, usize, usize, usize, usize) {
    if !Y16_SHED || !Y15_CORE_V2 || !Y15_JOINT_M || !on {
        return (0, 0, 0, 0, 0);
    }
    // the ladder's least budget on bits [6, MW): 10 at window 57 (as [`fold_plan`] finds it)
    let nbits = Y15_WIN - 6;
    let min_budget = (1..=nbits).find(|&b| merged_plan(nbits - 1, b).is_some() || merged_plan(nbits, b).is_some()).expect("y16: a ladder budget");
    // y28: the ladder with `drop` kept carries dropped early runs on that many wires fewer
    let need = fixed + min_budget - drop - 2 * usize::from(Y15_LEAN45);
    let (short_f, short_m) = (need.saturating_sub(room_fold), need_m.saturating_sub(room_m));
    // y18-next: the guard carries of m0's rebuilt chain come first for its erase (see Y18_GSHED)
    let gmax = if Y18_GSHED { Y15_GUARD.saturating_sub(1) } else { 0 };
    let block = short_f.max(short_m.saturating_sub(gmax)).max(Y16_SHED_MIN).min(pool);
    // y18-next: past the three top wires the fold sheds wires of its own (see Y18_FIN)
    let fmax = if Y18_FIN { fmax } else { 0 };
    let rest_f = short_f - short_f.min(block);
    let fin = rest_f - rest_f.min(tops_max);
    let tops = (rest_f - fin).max(usize::from(Y16_TOP_ALWAYS && block > 0)).max(Y17_TOPS_MIN);
    let rest = short_m - short_m.min(block);
    let gsh = rest.min(gmax);
    let c3m = (rest - gsh).max(usize::from(Y17_C3M_ALWAYS));
    assert!(
        rest - gsh <= usize::from(Y17_C3M) && fin <= fmax && tops <= 3 && c3m <= 1,
        "y16 at {} t={}: the room is too small: fold short of {short_f} (room {room_fold}, need {need}), m0's erase short of {short_m} (room {room_m}, need {need_m}), block {pool} + {tops_max} + {fmax} for the fold, + {gmax} + {} for the erase",
        if at.0 { "rev" } else { "fwd" },
        at.1,
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
    ladder_d(c, acc, add, lo0, cin0, plan, &[]);
}
/// [`ladder`]; `drops` (y28, card s2-1) = the 0-based chunks whose kept carry is measured away as soon as the next
/// chunk has read it and built again under the measured bit of the kept carry above it (see [`Y28_DROP_FWD`]).
fn ladder_d(c: &mut Builder, acc: &[QubitId], add: &[Lin], lo0: usize, cin0: QubitId, plan: &[usize], drops: &[usize]) {
    if !drops.is_empty() {
        return ladder_drop(c, acc, add, lo0, cin0, plan, drops);
    }
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

/// One chunk of the fold's ladder, as [`ladder`] runs it: carries, sums written back, the carries erased. Returns the
/// chunk's carry-out wire (a non-final chunk keeps it).
fn ladder_chunk(c: &mut Builder, acc: &[QubitId], add: &[Lin], lo: usize, w: usize, cin: QubitId, last: bool) -> Option<QubitId> {
    let hi = lo + w;
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
    (!last).then(|| cc[w])
}
/// X-measure a kept carry of the ladder and fix its phase by the exact compare on its chunk [lo, hi) (carry-in `cin`),
/// under the measured bit.
fn kept_erase(c: &mut Builder, acc: &[QubitId], add: &[Lin], lo: usize, hi: usize, cin: QubitId, out: QubitId) {
    let m = c.alloc_bit();
    c.hmr(out, m);
    c.release_clean(out);
    c.push_condition(m);
    lin_lt_phase(c, &acc[lo..hi], &add[lo..hi], cin);
    c.pop_condition();
    c.free_bit(m);
}
/// y28 (card s2-1): [`ladder`] with the kept carries of the chunks in `drops` dropped early.
fn ladder_drop(c: &mut Builder, acc: &[QubitId], add: &[Lin], lo0: usize, cin0: QubitId, plan: &[usize], drops: &[usize]) {
    let mw = acc.len();
    assert_eq!(plan.iter().sum::<usize>(), mw - lo0, "y15 fold plan covers bits [lo, MW)");
    // (lo, hi, carry-in wire, carry-out wire, still live)
    let mut kept: Vec<(usize, usize, QubitId, QubitId, bool)> = Vec::new();
    let (mut lo, mut cin) = (lo0, cin0);
    for (j, &w) in plan.iter().enumerate() {
        let last = j + 1 == plan.len();
        if let Some(out) = ladder_chunk(c, acc, add, lo, w, cin, last) {
            kept.push((lo, lo + w, cin, out, true));
            cin = out;
        }
        // the carry below the one this chunk read: nothing reads it as a value any more
        if j >= 1 && drops.contains(&(j - 1)) {
            assert!(!last && (j < 2 || kept[j - 2].4), "y28: a dropped carry needs the next kept carry and its own carry-in live");
            let (l0, h0, c0, o0, _) = kept[j - 1];
            kept_erase(c, acc, add, l0, h0, c0, o0);
            kept[j - 1].4 = false;
        }
        lo += w;
    }
    for idx in (0..kept.len()).rev() {
        let (lo, hi, cin, out, live) = kept[idx];
        if !live {
            continue;
        }
        if idx == 0 || kept[idx - 1].4 {
            kept_erase(c, acc, add, lo, hi, cin, out);
            continue;
        }
        // its carry-in was dropped: under this carry's measured bit, build it again on the written sums
        let (l0, h0, c0, _, _) = kept[idx - 1];
        let m = c.alloc_bit();
        c.hmr(out, m);
        c.release_clean(out);
        c.push_condition(m);
        // the carry out of bit i is MAJ(X_i, add_i, d_i) with X_i ^ d_i = acc_i ^ add_i (acc holds the sum)
        let forms = |i: usize, di: QubitId| (l(acc[i]).x(&add[i]), add[i].x(&l(di)));
        let mut d = vec![c0];
        for i in l0..h0 {
            let di = d[i - l0];
            let (a, b) = forms(i, di);
            let q = lin_and(c, &a, &b);
            c.cx(di, q);
            d.push(q);
        }
        // the chain's lower carries leave at once (measured, each from the carry below it)
        for i in (l0 + 1..h0).rev() {
            let (q, di) = (d[i - l0], d[i - l0 - 1]);
            let (a, b) = forms(i - 1, di);
            c.cx(di, q);
            lin_and_erase(c, q, &a, &b);
        }
        let back = d[h0 - l0];
        lin_lt_phase(c, &acc[lo..hi], &add[lo..hi], back);
        kept_erase(c, acc, add, l0, h0, c0, back);
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
    w_mod64_pre_x(c, recs, acc, src, nm, b01, top, pre, None)
}
/// `x45` (y28, card s2-5): the forms of low(X_r)'s bits 4 and 5 where acc[4] and acc[5] already hold their sums.
#[allow(clippy::too_many_arguments)]
fn w_mod64_pre_x(c: &mut Builder, recs: &mut Vec<Rec>, acc: &[QubitId], src: &[QubitId], nm: [QubitId; 3], b01: &Lin, top: usize, pre: Option<&[Lin; 2]>, x45: Option<[Lin; 2]>) -> (Vec<Lin>, [Lin; 2]) {
    assert!((2..=5).contains(&top));
    let one = Lin::k(true);
    let sb = |j: usize, sh: usize| Lin::of(&[src[j], nm[sh]]);
    let mut w: Vec<Lin> = (0..6).map(|i| l(acc[i])).collect();
    if let Some([x4, x5]) = x45 {
        w[4] = x4;
        w[5] = x5;
    }
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
    lean_clear_y_t(c, acc, src, nm, b01, pre, yq, gates, top, None, &mut None);
}
/// y28 (card s2-5): the reverse fold's carries into bits 4 and 5 built late (see [`Y28_LEAN_REV`]). `c4`, `c5`: wires
/// that hold 0 until built; `need4`, `need5`: bits that hold 0 until then; `n5`, `n4`: the complements of y5's measured
/// bit and (where that is clear) of y4's, kept from the clearing of the gate wires for c6's erase.
struct Late45 {
    acc3: QubitId,
    acc4: QubitId,
    acc5: QubitId,
    c3: QubitId,
    c4: QubitId,
    c5: QubitId,
    n0: Lin,
    n1: Lin,
    need4: crate::circuit::BitId,
    need5: crate::circuit::BitId,
    n5: Option<crate::circuit::BitId>,
    n4: Option<crate::circuit::BitId>,
}
impl Late45 {
    fn build4(&self, c: &mut Builder) {
        lin_and_into(c, self.c4, &l(self.acc3), &l(self.c3));
        c.bit_store1(self.need4);
    }
    /// c5 = MAJ(X[4], n0, c4) with X[4] ^ c4 = acc[4] ^ n0 (acc[4] holds the sum); needs c4
    fn build5(&self, c: &mut Builder) {
        lin_and_into(c, self.c5, &l(self.acc4).x(&self.n0), &self.n0.x(&l(self.c4)));
        c.cx(self.c4, self.c5);
        c.bit_store1(self.need5);
    }
    fn erase5(&self, c: &mut Builder) {
        c.push_condition(self.need5);
        c.cx(self.c4, self.c5);
        lin_and_erase(c, self.c5, &l(self.acc4).x(&self.n0), &self.n0.x(&l(self.c4)));
        c.pop_condition();
    }
    /// low(X_r)'s bits 4 and 5 from the written sums
    fn x45(&self) -> [Lin; 2] {
        [l(self.acc4).x(&self.n0).x(&l(self.c4)), l(self.acc5).x(&self.n1).x(&l(self.c5))]
    }
}
/// The AND of the shift letter built late (y28, card s2-4): into `q` (a wire that holds 0) under the conditions in
/// force, and `need` (a bit that holds 0 until then) is set: the wire is measured away under it.
#[derive(Clone, Copy)]
struct TtLate {
    k1: QubitId,
    k2: QubitId,
    q: QubitId,
    need: crate::circuit::BitId,
}
impl TtLate {
    fn build(&self, c: &mut Builder) {
        lin_and_into(c, self.q, &l(self.k1), &l(self.k2));
        c.bit_store1(self.need);
    }
}
/// [`lean_clear_y`]; with `late` the AND of the shift letter (the wire in gates[2] and gates[0]) is not built yet: it
/// is built here on the branches that read it (y5's bit set; y5's clear and y3's set), once on any shot.
#[allow(clippy::too_many_arguments)]
/// With `l45` (y28, card s2-5) acc[4] and acc[5] hold their sums: y5's branch builds both carries and y4's the lower
/// one, the chains read the old bits through them, and the complements of y5's and y4's bits are kept in `l45`.
#[allow(clippy::too_many_arguments)]
fn lean_clear_y_t(c: &mut Builder, acc: &[QubitId], src: &[QubitId], nm: [QubitId; 3], b01: &Lin, pre: &[Lin; 2], yq: &[QubitId; 3], gates: &[Lin; 3], top: usize, late: Option<TtLate>, l45: &mut Option<Late45>) {
    let m = c.alloc_bit();
    c.hmr(yq[top - 3], m);
    c.push_condition(m);
    {
        if let Some(s) = l45.as_ref() {
            if top >= 4 {
                s.build4(c);
            }
            if top == 5 {
                s.build5(c);
            }
        }
        // top = 5: y5's own fix reads the AND; top = 3: y3's does (and nothing built it on this branch)
        if let (Some(t), true) = (late, top != 4) {
            t.build(c);
        }
        let mut r2: Vec<Rec> = Vec::new();
        let (w, _) = w_mod64_pre_x(c, &mut r2, acc, src, nm, b01, top, Some(pre), l45.as_ref().map(|s| s.x45()));
        lin_cz(c, &gates[top - 3], &w[top]); // the phase the measurement left
        for i in (3..top).rev() {
            let mi = c.alloc_bit();
            c.hmr(yq[i - 3], mi);
            c.push_condition(mi);
            // top = 4: y5's bit is clear and y4's fix read k2 alone; y3's fix is the first to read the AND
            if let (Some(t), true) = (late, top == 4 && i == 3) {
                t.build(c);
            }
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
        lean_clear_y_t(c, acc, src, nm, b01, pre, yq, gates, top - 1, late, l45);
        c.pop_condition();
        match l45.as_mut() {
            // kept for c6's erase (the caller frees them)
            Some(s) if top == 5 => s.n5 = Some(not_m),
            Some(s) if top == 4 => s.n4 = Some(not_m),
            _ => c.free_bit(not_m),
        }
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
    let (plan, lean45, drops) = fold_plan_d(c, mw, what, 0);
    assert!(drops.is_empty());
    (plan, lean45)
}
/// [`fold_plan`] with up to `drop` kept carries dropped early (see [`Y28_DROP_FWD`]): the third value is the 0-based
/// chunks whose kept carry leaves when the next chunk has read it (empty where a plan of [`merged_plan`] fits).
fn fold_plan_d(c: &Builder, mw: usize, what: &str, drop: usize) -> (Vec<usize>, bool, Vec<usize>) {
    let budget = cells::cap().saturating_sub(c.active_qubits() as usize);
    let nbits = mw - 6;
    let lean45 = Y15_LEAN45 && merged_plan(nbits - 1, budget).is_none() && merged_plan(nbits, budget).is_none();
    let budget = budget + 2 * usize::from(lean45);
    if drop > 0 && merged_plan(nbits - 1, budget).is_none() && merged_plan(nbits, budget).is_none() {
        assert!(nbits == 50 && budget + drop >= 10 && (8..=9).contains(&budget), "y28: the {what} fold's ladder with {drop} dropped carries does not fit: budget {budget}, active {}, cap {}", c.active_qubits(), cells::cap());
        return if budget == 9 { (Y28_PLAN9.0.to_vec(), lean45, Y28_PLAN9.1.to_vec()) } else { (Y28_PLAN8.0.to_vec(), lean45, Y28_PLAN8.1.to_vec()) };
    }
    let (plan, lean45) = fold_plan_0(c, mw, what, budget, lean45);
    (plan, lean45, Vec::new())
}
fn fold_plan_0(c: &Builder, mw: usize, what: &str, budget: usize, lean45: bool) -> (Vec<usize>, bool) {
    let nbits = mw - 6;
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
fn fold_undo_recs(c: &mut Builder, recs: Vec<Rec>, acc: &[QubitId], a4: &Lin, a5: &Lin, cw: [QubitId; 3]) {
    fold_undo_recs_t(c, recs, acc, a4, a5, cw, &mut None);
}
/// y28 (s2-4, step 2): the state of the forward fold's undo when the AND of the shift letter is built late: the
/// wires of y5 and y3 (their erases read it) and, once y5 is measured, the complement of its bit.
struct TtUndo {
    t: TtLate,
    y5: QubitId,
    y3: QubitId,
    n5: Option<crate::circuit::BitId>,
}
/// Erase one AND record of the forward fold's undo list. With `late`, y5 and y3 are measured here and the AND of the
/// shift letter is built under the bit that reads it; its own record is erased under the OR of the two bits.
fn tt_and_erase(c: &mut Builder, late: &mut Option<TtUndo>, q: QubitId, a: &Lin, b: &Lin) {
    let Some(u) = late.as_mut() else {
        lin_and_erase(c, q, a, b);
        return;
    };
    if q == u.y5 {
        let m = c.alloc_bit();
        c.hmr(q, m);
        c.push_condition(m);
        u.t.build(c);
        lin_cz(c, a, b);
        c.pop_condition();
        let n = c.alloc_bit();
        c.bit_store1(n);
        c.bit_xor_into(n, m);
        u.n5 = Some(n);
        c.free_bit(m);
        c.release_clean(q);
    } else if q == u.y3 {
        let n = u.n5.take().expect("y28: y5 is erased before y3");
        let m = c.alloc_bit();
        c.hmr(q, m);
        c.push_condition(m);
        c.push_condition(n);
        u.t.build(c);
        c.pop_condition();
        lin_cz(c, a, b);
        c.pop_condition();
        c.free_bit(m);
        c.free_bit(n);
        c.release_clean(q);
    } else if q == u.t.q {
        c.push_condition(u.t.need);
        lin_and_erase(c, q, a, b);
        c.pop_condition();
        c.free_bit(u.t.need);
    } else {
        lin_and_erase(c, q, a, b);
    }
}
fn fold_undo_recs_t(c: &mut Builder, mut recs: Vec<Rec>, acc: &[QubitId], a4: &Lin, a5: &Lin, cw: [QubitId; 3], late: &mut Option<TtUndo>) {
    let [c4, c5, c6] = cw;
    while let Some(r) = recs.pop() {
        match r {
            Rec::And(q, a, b) => tt_and_erase(c, late, q, &a, &b),
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
/// y28 (s2-2): [`fold_undo_recs`] for the forward fold whose sums 4 and 5 were written before the ladder and whose
/// carries into bits 4 and 5 are gone (see [`Y28_LEAN_FWD`]); `cw` = two wires that hold 0 for them (taken where the
/// head builds the two carries again, so every later wire keeps the head's id) and c6. Returns c6's measured bit: c4
/// is built under it and still to be erased under it by the low section's undo.
fn fold_undo_recs_m(c: &mut Builder, mut recs: Vec<Rec>, acc: &[QubitId], a4: &Lin, a5: &Lin, c3: QubitId, cw: [QubitId; 3], late: &mut Option<TtUndo>) -> crate::circuit::BitId {
    let [c4, c5, c6] = cw;
    let mut st: Option<crate::circuit::BitId> = None;
    while let Some(r) = recs.pop() {
        match r {
            Rec::And(q, a, b) => tt_and_erase(c, late, q, &a, &b),
            Rec::Maj(q, a, b, ci) => {
                lin_xor_into(c, &ci, q);
                lin_and_erase(c, q, &a, &b);
            }
            Rec::UndoC6 => {
                let m = c.alloc_bit();
                c.hmr(c6, m);
                c.release_clean(c6);
                c.push_condition(m);
                lin_and_into(c, c4, &l(acc[3]), &l(c3));
                // c5 = MAJ(X[4], a4, c4) with X[4] ^ c4 = acc[4] ^ a4 (acc[4] holds the sum)
                lin_and_into(c, c5, &l(acc[4]).x(a4), &a4.x(&l(c4)));
                c.cx(c4, c5);
                // c6 = MAJ(X[5], a5, c5) = AND(acc[5] ^ a5, a5 ^ c5) ^ c5
                lin_cz(c, &l(acc[5]).x(a5), &a5.x(&l(c5)));
                lin_cz(c, &Lin::k(true), &l(c5));
                c.pop_condition();
                st = Some(m);
            }
            Rec::UndoC5 => {
                let m = st.expect("y28: c6 is erased before c5");
                c.push_condition(m);
                c.cx(c4, c5);
                lin_and_erase(c, c5, &l(acc[4]).x(a4), &a4.x(&l(c4)));
                c.pop_condition();
            }
        }
    }
    st.expect("y28: the fold's undo list holds c6")
}
/// AND of two linear forms into a wire that holds 0 (one Toffoli): [`lin_and`] without its allocation.
fn lin_and_into(c: &mut Builder, q: QubitId, a: &Lin, b: &Lin) {
    let (ha, hb) = lin_pair_on(c, a, b);
    c.ccx(ha, hb, q);
    lin_pair_off(c, a, b);
}
/// The second part of [`fold_undo`]: the low section acc[0..4) += E.
fn fold_undo_low(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], cw: [QubitId; 4]) {
    fold_undo_low_c(c, acc, e, cw, None);
}
/// `c4m` (y28): c4 exists only under this bit (and is erased under it).
fn fold_undo_low_c(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], cw: [QubitId; 4], c4m: Option<crate::circuit::BitId>) {
    let [c1, c2, c3, c4] = cw;
    if let Some(m) = c4m {
        c.push_condition(m);
    }
    lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    if c4m.is_some() {
        c.pop_condition();
    }
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
fn fold_fwd_v2(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], nm: [QubitId; 3], k1: QubitId, k2: QubitId, fin: usize, mut esh: Option<&mut ESh>, ttm: bool, drop: usize) -> Vec<usize> {
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
    // y18-next: the AND of the shift letter leaves for the ladder (see Y18_FIN); y28: also with `ttm` ([`Y28_TT_FWD`]),
    // and then it comes back only under the measured bits of y5 and y3
    let tt_q = tt.w[0];
    let (y5_q, y3_q) = (y5.w[0], y3.w[0]);
    if fin >= 3 || ttm {
        lin_and_erase(c, tt_q, &l(k1), &l(k2));
    }
    let (plan, lean45, drops) = fold_plan_d(c, mw, "forward", drop);
    // y28 (s2-2): sums 4 and 5 are written here and the two carries come back only under c6's measured bit
    let lean_m = lean45 && Y28_LEAN_FWD;
    if lean45 {
        if lean_m {
            lin_xor_into(c, &a5, acc[5]);
            c.cx(c5, acc[5]);
        }
        maj_wire_erase(c, c5, &l(acc[4]), &a4, &l(c4));
        if lean_m {
            lin_xor_into(c, &a4, acc[4]);
            c.cx(c4, acc[4]);
        }
        lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    }
    ladder_d(c, acc, &add, 6, c6, &plan, &drops);
    let (c4, c5) = if lean_m {
        (c.alloc_qubit(), c.alloc_qubit())
    } else if lean45 {
        let c4 = lin_and(c, &l(acc[3]), &l(c3));
        let c5 = maj_wire(c, &l(acc[4]), &a4, &l(c4));
        (c4, c5)
    } else {
        (c4, c5)
    };
    let mut late: Option<TtUndo> = None;
    if ttm {
        let q = c.alloc_qubit();
        let need = c.alloc_bit();
        c.bit_store0(need);
        y18_subst(&mut recs, tt_q, q);
        late = Some(TtUndo { t: TtLate { k1, k2, q, need }, y5: y5_q, y3: y3_q, n5: None });
    } else if fin >= 3 {
        let q = lin_and(c, &l(k1), &l(k2));
        y18_subst(&mut recs, tt_q, q);
    }
    let c4m = if lean_m {
        Some(fold_undo_recs_m(c, recs, acc, &a4, &a5, c3, [c4, c5, c6], &mut late))
    } else {
        fold_undo_recs_t(c, recs, acc, &a4, &a5, [c4, c5, c6], &mut late);
        None
    };
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
    fold_undo_low_c(c, acc, e, [c1, c2, c3, c4], c4m);
    if let Some(m) = c4m {
        c.free_bit(m);
    }
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
fn fold_rev_v2(c: &mut Builder, acc: &[QubitId], e: [QubitId; 3], nm: [QubitId; 3], k1: QubitId, k2: QubitId, src: &[QubitId], kept: &[Vec<QubitId>; 3], wc: &[QubitId], lean: bool, order: [usize; 3], yg: &[QubitId], fin: usize, drop: usize) -> Vec<usize> {
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
    let (plan, lean45, drops) = fold_plan_d(c, mw, "reverse", drop);
    // y28 (s2-5): sums 4 and 5 are written here; the two carries come back only on the branches that read them
    let lean_r = lean45 && Y28_LEAN_REV && (ygate.is_some() || lean_y.is_some());
    if lean45 {
        if lean_r {
            lin_xor_into(c, &n1, acc[5]);
            c.cx(c5, acc[5]);
        }
        maj_wire_erase(c, c5, &l(acc[4]), &n0, &l(c4));
        if lean_r {
            lin_xor_into(c, &n0, acc[4]);
            c.cx(c4, acc[4]);
        }
        lin_and_erase(c, c4, &l(acc[3]), &l(c3));
    }
    ladder_d(c, acc, &add, 6, c6, &plan, &drops);
    let mut l45: Option<Late45> = None;
    let (c4, c5) = if lean_r {
        let (c4, c5) = (c.alloc_qubit(), c.alloc_qubit());
        let (need4, need5) = (c.alloc_bit(), c.alloc_bit());
        c.bit_store0(need4);
        c.bit_store0(need5);
        l45 = Some(Late45 { acc3: acc[3], acc4: acc[4], acc5: acc[5], c3, c4, c5, n0: n0.clone(), n1: n1.clone(), need4, need5, n5: None, n4: None });
        (c4, c5)
    } else if lean45 {
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
        if Y28_TT_REV {
            // y28 (s2-4): the AND comes only where y5's or y3's measured bit reads it
            let tt = c.alloc_qubit();
            let need = c.alloc_bit();
            c.bit_store0(need);
            let gates = [Lin::of(&[k1, k2, tt]), l(k2), l(tt)];
            lean_clear_y_t(c, acc, src, nm, &b01, &pre, &yq, &gates, 5, Some(TtLate { k1, k2, q: tt, need }), &mut l45);
            c.push_condition(need);
            lin_and_erase(c, tt, &l(k1), &l(k2));
            c.pop_condition();
            c.free_bit(need);
        } else {
            let tt = lin_and(c, &l(k1), &l(k2));
            let gates = [Lin::of(&[k1, k2, tt]), l(k2), l(tt)];
            lean_clear_y_t(c, acc, src, nm, &b01, &pre, &yq, &gates, 5, None, &mut l45);
            lin_and_erase(c, tt, &l(k1), &l(k2));
        }
        for q in yq {
            c.release_clean(q);
        }
    }
    if let Some((yq, gates, pre, mark2)) = lean_y {
        // erase every wire built after the gate wires (they read them and W's bit 2), then the gate wires themselves;
        // acc[0..6) still holds low(X_r) and the two borrows into bit 2 are live
        let mut tail = recs.split_off(mark2);
        pop_chain(c, &mut tail);
        lean_clear_y_t(c, acc, src, nm, &b01, &pre, &yq, &gates, 5, None, &mut l45);
        for q in yq {
            c.release_clean(q);
        }
    }
    if let Some(s) = l45 {
        // y28 (s2-5): [`fold_undo`] with c6 measured as it is and the two carries where they were built
        let (n5, n4) = (s.n5.expect("y28: y5's bit is kept"), s.n4.expect("y28: y4's bit is kept"));
        let mut recs = recs;
        while let Some(r) = recs.pop() {
            match r {
                Rec::And(q, a, b) => lin_and_erase(c, q, &a, &b),
                Rec::Maj(q, a, b, ci) => {
                    lin_xor_into(c, &ci, q);
                    lin_and_erase(c, q, &a, &b);
                }
                Rec::UndoC6 => {
                    let m = c.alloc_bit();
                    c.hmr(c6, m);
                    c.release_clean(c6);
                    c.push_condition(m);
                    // c5 is still to build where y5's bit was clear, and c4 under it where y4's was clear too
                    c.push_condition(n5);
                    c.push_condition(n4);
                    s.build4(c);
                    c.pop_condition();
                    s.build5(c);
                    c.pop_condition();
                    // c6 = MAJ(X[5], n1, c5) = AND(acc[5] ^ n1, n1 ^ c5) ^ c5
                    lin_cz(c, &l(acc[5]).x(&n1), &n1.x(&l(c5)));
                    lin_cz(c, &Lin::k(true), &l(c5));
                    c.pop_condition();
                    c.free_bit(m);
                }
                Rec::UndoC5 => s.erase5(c),
            }
        }
        fold_undo_low_c(c, acc, e, [c1, c2, c3, c4], Some(s.need4));
        for b in [s.need4, s.need5, n5, n4] {
            c.free_bit(b);
        }
    } else {
        fold_undo(c, recs, acc, e, &n0, &n1, [c1, c2, c3, c4, c5, c6]);
    }
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
    // y20: direct cuts (the chunked parts of adds 0 and 1 one bit longer) and the closed ripple on this pass
    let cut = Y20_CUT && late && Y15_JOINT_M;
    let dcut = usize::from(cut);
    let close = !swap01 && late && Y15_JOINT_M && y20_close_on(t, rev);
    // y21: add 1's chunked part to the top on this pass (no h1; m1 is then x257)
    let top1 = cut && !close && y21_top_on(t, rev);
    // y28 (s2-1): the ladder's dropped carries on this pass (then no deep shed)
    let drop_n = if cut && !close && !swap01 && Y15_CORE_V2 { y28_drop(t, rev) } else { 0 };
    let deep = cut && !close && y21_deep_on(t, rev) && drop_n == 0;
    let mut pads18: Vec<QubitId> = Vec::new();
    let _ = y18_log();
    let a_pre0 = c.active_qubits();
    let (a_pre1, log0, log1);
    if swap01 {
        // first: X0' = T + 2 S'1 on bits [1, 257) (T has no bit 256); held: m1 = the carry into bit 255, h1 = the
        // carry into bit 256
        c.cx_all(s[1], b);
        (m1, kept1) = low_keep_add(c, &b[..N - 2 + dcut], &tg[1..N - 1 + dcut], proxy, rev, keep[1]);
        let h1 = m_carry(c, tg[N - 1], &l(b[N - 2]), m1);
        c.cx(b[N - 2], tg[N - 1]);
        c.cx(m1, tg[N - 1]);
        c.cx_all(s[1], b);
        e_add0 = c.expected_total();
        log0 = y18_log();
        a_pre1 = c.active_qubits();
        // second: X1' = X0' + S'0 on bits [0, 256); held: m0 = the carry into bit 255; g = its carry out
        c.cx_all(s[0], b);
        (m0, kept0) = low_keep_add(c, &b[..N - 1 + dcut], &tg[..N - 1 + dcut], proxy, rev, keep[0]);
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
        (m0, kept0) = low_keep_add(c, &b[..N - 1 + dcut], &tg[..N - 1 + dcut], proxy, rev, keep[0]);
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
        (m1, kept1) = if top1 {
            // y21: all 256 bits; the top target bit is m0 (g0 = X0[256]), which then holds X1[256]
            let mut a1: Vec<QubitId> = tg[1..].to_vec();
            a1.push(m0);
            low_keep_add(c, &b[..N], &a1, proxy, rev, keep[1])
        } else {
            low_keep_add(c, &b[..N - 2 + dcut], &tg[1..N - 1 + dcut], proxy, rev, keep[1])
        };
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
    let (k0, seed0) = cells::y15_split_spec(proxy, rev, N - 1 + dcut);
    let (kk1, seed1) = cells::y15_split_spec(proxy, rev, N - 2 + dcut);
    // (swap01: it is the first add's carry m1 whose erase builds a chain again, on its window and the guard)
    let kwin = if swap01 { (kk1 + Y15_GUARD).max(k0) } else { (k0 + Y15_GUARD).max(kk1) };
    // y20: the closed ripple leaves only the steps into the top wires open (and bit 255's without the direct cuts)
    let sp2 = if close { N - 3 + dcut } else { N - 3 + dcut - kwin };
    let (m2, kept2) = low_keep_add(c, &b[..sp2], &tg[2..2 + sp2], proxy, rev, keep[2]);
    for &q in &pads18 {
        c.release_clean(q); // never written
    }
    let (x256, h1, x257) = match top3 {
        Some(t) => t,
        // y21: m0 holds X1[256] and m1 is x257 (the middle entry, h1, is not a wire of its own: never read)
        None if top1 => (m0, m1, m1),
        None if cut => {
            // y20: m0 is g0 = X0[256] and m1 is h1; the chunked parts wrote bit 255, so only x257 is built here
            let s1f = |i: usize| Lin::of(&[b[i], s[2], s[1]]);
            let x257 = m_carry(c, m0, &s1f(N - 1), m1);
            lin_xor_into(c, &s1f(N - 1), m0);
            c.cx(m1, m0);
            (m0, m1, x257)
        }
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
    super::super::pingpong::Y17_EXTRA.with(|e| e.set(Y18_PRICE + Y19_PRICE_FOLD));
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
    let live_m = 1 + (N - 3).saturating_sub(sp2);
    let shed_on = !kept.iter().any(|k| !k.is_empty()) && (!rev || !wc.is_empty() || lean_here || yg_here);
    // y20: with the direct cuts h1 and x256 stay through the fold (2 top carries to shed, 2 more wires in the fold's
    // own shed); with the closed ripple as well the carry under the top one is m2 itself
    let fmax = (if rev { 2 } else if top1 { 4 } else if cut { 5 } else { 6 }) + usize::from(deep);
    let tops_max = if cut { if close { 1 } else { 2 } } else { Y17_TOPS_MAX };
    let shed_fixed = if !rev {
        Y16_FIXED_FWD
    } else if lean_here {
        Y17_FIXED_REV_LEAN
    } else if yg_here {
        Y17_FIXED_REV_YGATE
    } else {
        Y16_FIXED_REV_COPY
    };
    let shed_for = |fixed: usize, fmax: usize| {
        y16_shed(
            shed_on,
            fixed,
            room_now,
            cells::cap().saturating_sub(a_start as usize + live_m),
            if swap01 { kk1 + Y15_GUARD + kk1 - 1 } else { k0 + Y15_GUARD + k0 - 1 + if close { kwin + Y20_G2 } else { 0 } },
            (N - 4).saturating_sub(sp2),
            fmax,
            tops_max,
            (rev, t),
            drop_n,
        )
    };
    let shed0 = shed_for(shed_fixed, fmax);
    // y28 (s2-4, step 2): forward, the AND of the shift letter leaves first where the fold sheds at all and that takes
    // one wire off the shed (`fin` then counts c2, c1 and the top wires: the head's numbering skips its third)
    let (ttm, (shed, tops, c3m, gsh, fin)) = if Y28_TT_FWD && !rev && !swap01 && Y15_CORE_V2 && Y18_FIN {
        if shed0.4 >= 3 {
            (true, shed0)
        } else if shed0.0 + shed0.1 + shed0.4 > 0 {
            let r = shed_for(shed_fixed - 1, fmax - 1);
            if r.0 + r.1 + r.4 < shed0.0 + shed0.1 + shed0.4 {
                (true, (r.0, r.1, r.2, r.3, if r.4 >= 3 { r.4 + 1 } else { r.4 }))
            } else {
                (false, shed0)
            }
        } else {
            (false, shed0)
        }
    } else {
        (false, shed0)
    };
    assert!(!close || ((shed, c3m, gsh) == (0, 0, 0) && fin <= 3), "y20: the closed ripple on {} t={t} needs a shed it does not have: {:?}", if rev { "rev" } else { "fwd" }, (shed, tops, c3m, gsh, fin));
    // the top carry: cq(N - 1) = MAJ(x256', S'2[N - 2], cq(N - 2)), and x256 holds its sum x256' ^ S'2[N - 2] ^ cq(N - 2)
    // y18-next: with the top wires leaving inside the forward fold (fin 4 to 6) the top carries are not shed here
    let esh_on = !rev && !swap01 && Y15_CORE_V2 && fin.max(Y18_FIN_MIN.min(fmax)) >= 4;
    let tops_pre = if esh_on { 0 } else { tops };
    assert!(
        !deep || (shed == (N - 4).saturating_sub(sp2) && shed >= 1 && if rev { tops_pre == 2 } else { esh_on }),
        "y21: the deep shed on {} t={t} needs the whole block shed and the top carries gone: {:?}",
        if rev { "rev" } else { "fwd" },
        (shed, tops, c3m, gsh, fin)
    );
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
    // y21, deep shed: reverse, cq(N - 3) first (the top carries are gone); forward, the fold sheds all of them itself
    if deep && rev {
        m_carry_erase(c, cq(N - 3), acc2[N - 4], &l(b[N - 4]), cq(N - 4));
    }
    if !(deep && !rev) {
        for i in (sh_lo..sh_hi).rev() {
            m_carry_erase(c, cq(i), acc2[i - 1], &l(b[i - 1]), cq(i - 1));
        }
    }
    assert!(!cut || tops_pre <= 2);
    let mut esh: Option<ESh> = esh_on.then(|| ESh { x256, x257, x258, h1, m0, m1, cq1: cq(N - 1), cq2: cq(N - 2), cq3: cq(N - 3), t255: tg[N - 1], b1: b[N - 1], b2: b[N - 2], b3: b[N - 3], s, direct: cut, top1,
        deep_c: if deep { cc[..=N - 3 - sp2].to_vec() } else { Vec::new() },
        deep_a: if deep { acc2[sp2..N - 3].to_vec() } else { Vec::new() },
        deep_b: if deep { b[sp2..N - 3].to_vec() } else { Vec::new() },
    });
    let plan = if rev {
        // the reverse fold reads the source's low 6 bits as they are (b holds the source complemented by s[2])
        for j in 0..6 {
            c.cx(s[2], b[j]);
        }
        let plan = if Y15_CORE_V2 {
            fold_rev_v2(c, &tg[..Y15_WIN], [x256, x257, x258], s, k1, k2, &b[..6], &kept, &wc, lean_here, if swap01 { [2, 0, 1] } else { [2, 1, 0] }, &yg, fin.min(2), drop_n)
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
        // y26, stage b (a test): the fold as carries only under the Z layer, then the written fold as today
        if Y26_T0 == 2 && t == 0 {
            if let Some(bits) = Y26_BITS.with(|p| p.borrow_mut().take()) {
                assert!(shed == 0 && tops_pre == 0 && esh.is_none() && fin == 0);
                let mut ph = T0Phase::new(c, k1, k2, N, bits);
                // X's bits: written below add 2's open ripple, a form of register, source and carry in it
                let xf: Vec<Lin> = (0..N).map(|i| if i < sp2 + 2 { l(tg[i]) } else { Lin::of(&[tg[i], b[i - 2], cc[i - 2 - sp2]]) }).collect();
                let (w, mut recs) = fold_fwd_forms(c, &xf[..Y15_WIN], &[l(x256), l(x257), l(x258)], s, k1, k2);
                for i in 0..N {
                    ph.z(c, (i + N - 3) % N, if i < Y15_WIN { &w[i] } else { &xf[i] });
                }
                pop_chain(c, &mut recs);
                ph.finish(c);
            }
        }
        fold_fwd_v2(c, &tg[..Y15_WIN], [x256, x257, x258], s, k1, k2, fin, esh.as_mut(), ttm, drop_n)
    } else {
        fold_fwd(c, &tg[..Y15_WIN], [x256, x257, x258], s, k1, k2)
    };
    // y21, deep shed, reverse: the block and cq(N - 3) again, bottom up
    if deep && rev {
        for i in sh_lo..=sh_hi {
            cc[i - sp2] = m_carry(c, acc2[i - 1], &l(b[i - 1]), cc[i - 1 - sp2]);
        }
    }
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
            for j in 1..st.deep_c.len() {
                cc[j] = st.deep_c[j];
            }
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
    // (y20, closed ripple with the direct cuts: cq(N - 2) is m2 itself)
    if sp2 <= N - 3 {
        m_carry_erase(c, cq(N - 2), tg[N - 1], &l(b[N - 3]), cq(N - 3));
    }
    // x257 = MAJ(S'1[255], X0[256], h1), with X0[256] ^ h1 = X1[256] ^ S'1[255] and S'1 = b ^ s2 ^ s1
    // (swap01: x257 = MAJ(S'1[255], g, h1) and x256 holds g ^ h1 ^ S'1[255]: the same forms; x256 is then g)
    if !top1 {
        c.cx(h1, x257);
        lin_and_erase(c, x257, &Lin::of(&[x256, b[N - 1], s[2], s[1]]), &Lin::of(&[b[N - 1], s[2], s[1], h1]));
        lin_xor_into(c, &Lin::of(&[b[N - 1], s[2], s[1], h1]), x256); // x256 = X0[256]
    }
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
    } else if !cut {
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
    // y21, deep shed: the block was built again for the erase of the top wires; shed again for the erases below
    if deep {
        for i in (sh_lo..sh_hi).rev() {
            m_carry_erase(c, cc[i - sp2], acc2[i - 1], &l(b[i - 1]), cc[i - 1 - sp2]);
        }
    }
    // y28 DIAGNOSTIC, never for an entry (see [`Y28_PADS_FWD`]): the aligned copy's idle measurements
    for _ in 0..y28_pads(t, rev) {
        let q = c.alloc_qubit();
        let m = c.alloc_bit();
        c.hmr(q, m);
        c.free_bit(m);
        c.release_clean(q);
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
    } else if top1 {
        // y21, top cut: x257 (on m1) is measured first; x256 (on m0) holds X1[256]
        assert!(cut && !close && gsh == 0 && Y15_GUARD == 0);
        let split = N;
        let lo = split - k0;
        let i0 = lo - 1 - Y15_GUARD;
        assert!(sp2 + 2 <= i0 + 1 && i0 >= 1);
        let s1f = |i: usize| Lin::of(&[b[i], s[2], s[1]]);
        lin_xor_into(c, &s1f(N - 1), m0); // m0 = g0 ^ h1
        let bitx = c.alloc_bit();
        c.hmr(m1, bitx);
        c.free(m1);
        let nbx = c.alloc_bit();
        c.bit_store1(nbx);
        c.bit_xor_into(nbx, bitx);
        // add 1's carries on the window, built again: r[j] = C1[i0 + j]; the top wire is C1[N - 1] = h1
        let chain = |c: &mut Builder| -> (Vec<Lin>, Vec<(QubitId, Lin, Lin, Lin)>) {
            let mut r: Vec<Lin> = vec![s1f(i0 - 1)];
            let mut rr: Vec<(QubitId, Lin, Lin, Lin)> = Vec::new();
            for i in i0..split - 1 {
                let ci = r[i - i0].clone();
                let (fa, fb) = (s1f(i).x(&ci), l(tg[i + 1]).x(&s1f(i)));
                let q = lin_and(c, &fa, &fb);
                lin_xor_into(c, &ci, q);
                rr.push((q, fa, fb, ci));
                r.push(l(q));
            }
            (r, rr)
        };
        let unchain = |c: &mut Builder, mut rr: Vec<(QubitId, Lin, Lin, Lin)>| {
            while let Some((q, fa, fb, ci)) = rr.pop() {
                lin_xor_into(c, &ci, q);
                lin_and_erase(c, q, &fa, &fb);
            }
        };
        // g0's fix: the compare [X0 < S'0] on bits [lo, 256), X0[j] = X1[j] ^ S'1[j - 1] ^ C1[j - 1]
        let cmp0 = |c: &mut Builder, r: &[Lin]| {
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
        };
        // x257's bit set: the chain now. x257 = AND(S'1[255] ^ h1, g0 ^ h1) ^ h1, so its fix is a CZ of the two forms
        // (the second is the wire m0) and a Z on h1: no Toffoli. Then m0 = g0
        c.push_condition(bitx);
        let (ra, rra) = chain(c);
        let ha = rra.last().expect("y21: the rebuilt chain is not empty").0;
        for w in [b[N - 1], s[2], s[1], ha] {
            c.cz(w, m0);
        }
        c.cz(ha, ha);
        c.cx(ha, m0);
        c.pop_condition();
        let bit0 = c.alloc_bit();
        c.hmr(m0, bit0);
        c.release_clean(m0);
        c.push_condition(bitx);
        c.push_condition(bit0);
        cmp0(c, &ra);
        c.pop_condition();
        unchain(c, rra);
        c.pop_condition();
        // x257's bit clear: m0 was measured as g0 ^ h1; with its bit set the chain, a Z on its top (h1), g0's compare
        c.push_condition(nbx);
        c.push_condition(bit0);
        let (rb, rrb) = chain(c);
        let hb = rrb.last().expect("y21: the rebuilt chain is not empty").0;
        c.cz(hb, hb);
        cmp0(c, &rb);
        unchain(c, rrb);
        c.pop_condition();
        c.pop_condition();
        e_m0 = c.expected_total();
        c.free_bit(nbx);
        c.free_bit(bitx);
        c.free_bit(bit0);
    } else if Y15_JOINT_M {
        // m0 and m1 are measured together. m0's fix builds add 1's carries again on its window; one step more and the
        // chain's top wire is the carry into bit 255 of add 1, which is m1's own value: m1's fix is then a Z on it.
        // m1's own chunk compare runs only when m0's branch did not (a quarter of the shots, not a half).
        let split = N - 1 + dcut;
        let lo = split - k0;
        let i0 = lo - 1 - Y15_GUARD;
        assert!((close || sp2 + 2 <= i0 + 1) && i0 >= 1);
        let s1f = |i: usize| Lin::of(&[b[i], s[2], s[1]]);
        // y20, closed ripple: add 2's last sum bit (without the direct cuts) is written now, and m2 is measured with
        // the other two
        if close {
            for i in (sp2..N - 2).rev() {
                c.cx(b[i], acc2[i]);
                c.cx(cc[i - sp2], acc2[i]);
                assert!(i == sp2);
            }
        }
        let bit0 = c.alloc_bit();
        c.hmr(m0, bit0);
        c.release_clean(m0);
        let bit1 = c.alloc_bit();
        c.hmr(m1, bit1);
        c.free(m1);
        let bit2 = close.then(|| {
            let m = c.alloc_bit();
            c.hmr(m2, m);
            c.free(m2);
            m
        });
        // y20: the register under add 2 on the windows, tg[wlo, split): X1[j] = X[j] ^ S'2[j - 2] ^ C2[j - 2], add 2's
        // carries built again from Y20_G2 bits below (seeded with the source bit below; b holds S'2). The top of the
        // chain is the carry into index sp2, m2's own value. Returns the chain for [`y20_unpeel`].
        let wlo = split - kwin;
        let i2 = (wlo - 2).saturating_sub(Y20_G2);
        let peel = |c: &mut Builder| -> Vec<(QubitId, Lin, Lin, Lin)> {
            assert!(i2 >= 1 && sp2 == split - 2);
            let mut r2: Vec<Lin> = vec![l(b[i2 - 1])]; // r2[j] = C2[i2 + j]
            let mut rr2: Vec<(QubitId, Lin, Lin, Lin)> = Vec::new();
            for i in i2..sp2 {
                let ci = r2[i - i2].clone();
                let (fa, fb) = (l(b[i]).x(&ci), Lin::of(&[tg[i + 2], b[i]]));
                let q = lin_and(c, &fa, &fb);
                lin_xor_into(c, &ci, q);
                rr2.push((q, fa, fb, ci));
                r2.push(l(q));
            }
            let top2 = rr2.last().expect("y20: the rebuilt chain is not empty").0; // C2[sp2] = m2
            c.push_condition(bit2.expect("y20: m2 is measured"));
            c.cz(top2, top2);
            c.pop_condition();
            for j in wlo..split {
                lin_xor_into(c, &l(b[j - 2]).x(&r2[j - 2 - i2]), tg[j]);
            }
            rr2
        };
        let unpeel = |c: &mut Builder, mut rr2: Vec<(QubitId, Lin, Lin, Lin)>| {
            for j in (wlo..split).rev() {
                let ci = if j - 2 == i2 { l(b[i2 - 1]) } else { l(rr2[j - 3 - i2].0) };
                lin_xor_into(c, &l(b[j - 2]).x(&ci), tg[j]);
            }
            while let Some((q, fa, fb, ci)) = rr2.pop() {
                lin_xor_into(c, &ci, q);
                lin_and_erase(c, q, &fa, &fb);
            }
        };
        c.push_condition(bit0);
        let peeled = close.then(|| peel(c));
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
        if let Some(rr2) = peeled {
            unpeel(c, rr2);
        }
        c.pop_condition();
        e_m0 = c.expected_total();
        // m1: the cells' chunk compare at index 254 of add 1, only when bit1 is set and bit0 is not
        let nb = c.alloc_bit();
        c.bit_store1(nb);
        c.bit_xor_into(nb, bit0);
        let split = N - 2 + dcut;
        let lo = split - kk1;
        assert!(close || sp2 + 2 <= lo + 1);
        let blo = seed1.map_or(lo, |sd| sd.min(lo));
        let peeled = close.then(|| {
            c.push_condition(bit1);
            c.push_condition(nb);
            let rr2 = peel(c);
            c.pop_condition();
            c.pop_condition();
            rr2
        });
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
        if let Some(rr2) = peeled {
            c.push_condition(bit1);
            c.push_condition(nb);
            unpeel(c, rr2);
            c.pop_condition();
            c.pop_condition();
        }
        // y20, closed ripple: m2's own compare (the cells' chunk compare at index sp2 of add 2, on its own sum),
        // only when its bit is set and neither peel ran
        if let Some(b2) = bit2 {
            let nb1 = c.alloc_bit();
            c.bit_store1(nb1);
            c.bit_xor_into(nb1, bit1);
            let (kk2, seed2) = cells::y15_split_spec(proxy, rev, sp2);
            c.push_condition(b2);
            c.push_condition(nb);
            c.push_condition(nb1);
            super::super::compare::cmp_lt_phase(c, &acc2[sp2 - kk2..sp2], &b[sp2 - kk2..sp2], seed2.map(|sd| b[sd]));
            c.pop_condition();
            c.pop_condition();
            c.pop_condition();
            c.free_bit(nb1);
            c.free_bit(b2);
        }
        c.free_bit(nb);
        c.free_bit(bit1);
        c.free_bit(bit0);
    } else {
        assert!(!cut && !close);
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
    super::super::pingpong::Y17_EXTRA.with(|e| e.set(Y18_PRICE));
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
    let (kk2, _) = cells::y15_split_spec(proxy, rev, sp2);
    if !close {
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
    }
    c.cx_all(s[2], b);
    let e_end = c.expected_total();
    assert_eq!(c.active_qubits(), a_start, "y15: a wire was left behind");
    if Y15_TRACE {
        eprintln!(
            "Y15_NEW {} t={t} active={a_start} room={} low={} at_fold={a_fold} sp2={sp2} k0={k0} k1={kk1} k2={kk2} cut={dcut} closed={} top1={} seeds={:?} plan={plan:?} shed={shed} top={tops} c3m={c3m} gsh={gsh} fin={fin} \
             add0={:.1} add1={:.1} add2={:.1} fold={:.1} tops={:.1} m0={:.1} m1={:.1} close={:.1} body={:.1}",
            if rev { "rev" } else { "fwd" },
            cells::cap().saturating_sub(a_start as usize),
            if !rev { "-" } else if lean_here { "lean" } else if yg_here { "ygate" } else if copy_here { "copy" } else if keep_on { "keep" } else { "chains" },
            usize::from(close),
            usize::from(top1),
            (seed0, seed1),
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
    super::super::pingpong::Y17_EXTRA.with(|e| e.set(Y18_PRICE + Y19_PRICE_FOLD));
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

/// y26-loop (10 October 2026), measure-1: the multiply's tick-0 phase block (payload tick 0 forward on (P, P/2), the
/// Z layer of [`rot4_phase`], the tick back) in one call. The block only applies a phase, so what the forward tick
/// writes and the reverse tick unwrites can be evaluated as carries only: each AND built once on a fresh wire, the Z
/// layer put on XOR forms of live wires, every AND erased by measurement with its build forms.
///   0: off (the head byte for byte).
///   1: the same gates by explicit calls (stage a).
///   2: a test: the forward fold as carries only under the Z layer, inside the forward tick's body just before its
///      written fold; the tick then goes on and the reverse tick runs as today (stage b; 80 Toffoli more).
///   5: the form (m3): all three adds as forms over the one register P/2 (carry-save: two local AND layers and one
///      ripple chain), T = 2 (P/2) as forms through the doubling's window carries, the fold as carries only.
///      Nothing is written: no copy of P/2, no reverse tick, one mod_double fewer. See [`t0_phase_forms`].
/// Builder counts at peak 1236 on the head (767599.9, gate list 26775814), 10 October 2026:
///   1: expected=767599.9 (26775814, the head's bytes)
///   2: expected=767679.9 (bffe61d1; against the head 0 outputs differ on 30 draws, phase shots 339 / 349)
///   5, Y26_FUSE_DBL off: expected=766850.1 (8b18b6bb; 0 differ on 30 draws, phase shots 339 / 330)
///   5, Y26_FUSE_DBL on:  expected=766802.1 (954104ba; 0 differ on 30 draws, phase shots 339 / 369, of them on a
///      right output 116 / 114; on the denominator stress file 1 output differs, wrong only in the head)
/// The block at 5: window 48 + 1, the three AND layers 768, the fold 80, two boundaries 219.5, in all 1117.5 for the
/// head's 907.0 + 910.2 + 2 and two doublings of 48.
pub(super) const Y26_T0: u8 = 5;
pub(super) fn t0_carries_on(phrot: bool) -> bool {
    (Y26_T0 == 1 || Y26_T0 == 2) && phrot && fwd_on(0) && rev_on(0)
}
/// Research knob, a control of the paired test: the Z layer's positions 100 and 101 swapped (a wrong phase function).
/// false in every build that is kept.
const Y26_FAULT: bool = false;
/// y26, with the larger form: the product's doubling (P/2 -> P, [`cells::mod_double`]'s map) is written at the end
/// of the block from the window's carries, which the block holds anyway: the register is rotated up, the window's sum
/// bits are written top down and each carry is erased by measurement as it is passed. 0 Toffoli for the doubling's
/// own carry ladder. Same value on every input (the same truncated sum). false: [`cells::mod_double`] after the block.
pub(super) const Y26_FUSE_DBL: bool = true;
/// Research knob, a diagnostic of the paired test (0 in every build that is kept): this many idle X measurements on
/// a clean wire at the end of the block. The checker hands one random word to every measurement and reset in the
/// order of the gate list, so a block with another number of them moves the outcomes of every later measurement.
/// 2767 = the head's block's count less this block's (917,134 against 914,367 random words): with it the outcomes
/// outside the block are the head's, and a phase flag that moves is the block's own. Measured with 2767 (gate list
/// a7a0a4b9, expected=766802.1): on 90 draws 1 output differs (wrong only in the head) and the phase shots are the
/// head's less 4 (339 / 339 and 705 / 701), none new; slope stress file 7176 / 7176; denominator 4451 / 4450.
const Y26_PAD_RNG: usize = 0;
pub(super) fn t0_forms_on(phrot: bool) -> bool {
    Y26_T0 == 5 && phrot && fwd_on(0) && Y15_CORE_V2 && Y16_CORE
}
thread_local! {
    /// y26, stage b: the kept bits of the phase block, taken by the hook in the forward tick 0's [`body`].
    static Y26_BITS: std::cell::RefCell<Option<Vec<crate::circuit::BitId>>> = const { std::cell::RefCell::new(None) };
}
/// y26: the Z layer of [`rot4_phase`] (forward side), one position at a time and on forms.
struct T0Phase {
    k1: QubitId,
    k2: QubitId,
    t: QubitId,
    /// per position j of the register the layer is on: (monomial, kept bit)
    at: Vec<Vec<(usize, crate::circuit::BitId)>>,
    done: Vec<bool>,
    bits: Vec<crate::circuit::BitId>,
}
impl T0Phase {
    /// The plan of [`rot4_phase`] (`inv` = false) for an n-wire register; builds the AND of the shift letter.
    fn new(c: &mut Builder, k1: QubitId, k2: QubitId, n: usize, bits: Vec<crate::circuit::BitId>) -> T0Phase {
        assert_eq!(bits.len(), n);
        let maps: Vec<Vec<usize>> = (0..4).map(|e| rot4_map(n, e)).collect();
        let anf: [&[usize]; 4] = [&[0, 1, 2, 3], &[1, 3], &[2, 3], &[3]];
        let mut acc: std::collections::BTreeMap<(usize, usize), Vec<usize>> = std::collections::BTreeMap::new();
        for i in 0..n {
            for val in 0..4 {
                let (j, bi) = (maps[val][i], i);
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
        let mut at: Vec<Vec<(usize, crate::circuit::BitId)>> = vec![Vec::new(); n];
        for (&(j, mono), l) in acc.iter() {
            for &i in l {
                at[j].push((mono, bits[i]));
            }
        }
        T0Phase { k1, k2, t, at, done: vec![false; n], bits }
    }
    /// Position j of the register holds the value of the form `f`.
    fn z(&mut self, c: &mut Builder, j: usize, f: &Lin) {
        assert!(!self.done[j], "y26: position {j} twice");
        self.done[j] = true;
        for &(mono, bit) in &self.at[j] {
            let ctl = match mono {
                0 => None,
                1 => Some(self.k1),
                2 => Some(self.k2),
                _ => Some(self.t),
            };
            for &q in &f.w {
                match ctl {
                    None => c.z_if(q, bit),
                    Some(k) => c.cz_if(k, q, bit),
                }
            }
            if f.one {
                match ctl {
                    // -1 under the bit: Z X Z X on any wire
                    None => {
                        c.z_if(self.k1, bit);
                        c.x(self.k1);
                        c.z_if(self.k1, bit);
                        c.x(self.k1);
                    }
                    Some(k) => c.z_if(k, bit),
                }
            }
        }
    }
    /// Clear the AND of the shift letter as [`rot4_phase`] does and free the bits.
    fn finish(self, c: &mut Builder) {
        assert!(self.done.iter().all(|&d| d), "y26: a position of the Z layer was left out");
        if std::env::var("LF_PHROT_TOF").is_ok_and(|v| v == "1") {
            c.ccx(self.k1, self.k2, self.t);
            c.release_clean(self.t);
        } else {
            and_erase(c, self.t, self.k1, self.k2);
        }
        for b in self.bits {
            c.free_bit(b);
        }
    }
}
/// y26: the forward fold of [`fold_fwd_v2`] over forms, nothing written. `x`: forms of X's bits [0, MW); `e`: forms of
/// its three top bits. The same ANDs (4 low carries, 27 of the core, and the ladder's carries into bits 7..MW - 1,
/// the last on a wire of its own here). Returns the forms of W's bits [0, MW) and the undo list: every wire is erased
/// by measurement with its build forms, last built first ([`pop_chain`]).
fn fold_fwd_forms(c: &mut Builder, x: &[Lin], e: &[Lin; 3], nm: [QubitId; 3], k1: QubitId, k2: QubitId) -> (Vec<Lin>, Vec<Rec>) {
    assert!(Y15_CORE_V2 && Y16_CORE);
    let mw = x.len();
    let mut recs: Vec<Rec> = Vec::new();
    // low section: X[0..4) + E, carries only
    let c1 = r_and(c, &mut recs, x[0].clone(), e[0].clone());
    let c2 = r_maj(c, &mut recs, x[1].clone(), e[1].clone(), c1.clone());
    let c3 = r_maj(c, &mut recs, x[2].clone(), e[2].clone(), c2.clone());
    let c4 = r_and(c, &mut recs, x[3].clone(), c3.clone());
    let v3 = x[3].x(&c3);
    let tt = r_and(c, &mut recs, l(k1), l(k2));
    let g1 = Lin::of(&[k1, k2]).x(&tt);
    // r = Nm + X[0..3)
    let r1 = r_and(c, &mut recs, l(nm[0]), x[0].clone());
    let mut k = vec![l(nm[0]).x(&x[0]), l(nm[1]).x(&x[1]).x(&r1)];
    let r2 = r_maj(c, &mut recs, l(nm[1]), x[1].clone(), r1);
    k.push(l(nm[2]).x(&x[2]).x(&r2));
    let r3 = r_maj(c, &mut recs, l(nm[2]), x[2].clone(), r2);
    let (a4, a5) = (k[0].clone(), k[1].x(&k[0]));
    let y3 = r_and(c, &mut recs, g1, v3);
    let sum4 = x[4].x(&c4).x(&a4);
    let y4 = r_and(c, &mut recs, l(k2), sum4.clone());
    let c5 = r_maj(c, &mut recs, x[4].clone(), a4, c4);
    let sum5 = x[5].x(&c5).x(&a5);
    let y5 = r_and(c, &mut recs, tt.clone(), sum5.clone());
    let c6 = r_maj(c, &mut recs, x[5].clone(), a5, c5);
    let fc3 = c3.clone();
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
    let add = addend_prog(c, &mut recs, &k, &Y16_FWD_GATES, &Y16_FWD_OUT, mw);
    let mut w = vec![x[0].x(&e[0]), x[1].x(&e[1]).x(&c1), x[2].x(&e[2]).x(&c2), x[3].x(&c3), sum4, sum5];
    let mut f = c6;
    for i in 6..mw {
        w.push(x[i].x(&add[i]).x(&f));
        if i + 1 < mw {
            f = r_maj(c, &mut recs, x[i].clone(), add[i].clone(), f);
        }
    }
    (w, recs)
}
/// The phase (-1)^(m . y R2) on (P, P/2) = (`p[0]`, `p[1]`), both restored; frees `bits`.
pub(super) fn t0_phase(c: &mut Builder, letter: &[QubitId], p: &[Vec<QubitId>; 2], bits: Vec<crate::circuit::BitId>) {
    let t = 0usize;
    let [w, ..] = steps()[t];
    let (s, k1, k2) = ([letter[0], letter[1], letter[2]], letter[3], letter[4]);
    let (tg, b) = (p[0].clone(), p[1].clone());
    let shift = cmp_shift_at(t);
    let shift = (shift.0 + Y15_CMP_EXTRA, shift.1);
    let (_, proxy_f) = proxy_fold(w, false);
    let (_, proxy_r) = proxy_fold(w, true);
    // stages a and b: the forward tick without its 4-way rotation, the Z layer, the reverse tick without its rotation
    let (e0, a0) = (c.expected_total(), c.active_qubits());
    let mut bits = Some(bits);
    if Y26_T0 == 2 {
        Y26_BITS.with(|p| *p.borrow_mut() = bits.take());
    }
    cells::with_tie(None, || cells::with_cmp_shift(shift, || cells::with_bridge(proxy_f, false, || body_capped(c, t, s, k1, k2, &b, &tg, proxy_f, false))));
    assert!(Y26_BITS.with(|p| p.borrow().is_none()), "y26: the forward tick did not take the kept bits");
    for _ in 0..3 {
        rot1(c, &tg, true);
    }
    if Y15_TRACE {
        eprintln!("Y15_TICK fwd t={t} active={a0} cost={:.1}", c.expected_total() - e0);
    }
    if let Some(bits) = bits.take() {
        rot4_phase(c, k1, k2, &tg, bits, false);
    }
    let (e0, a0) = (c.expected_total(), c.active_qubits());
    for _ in 0..3 {
        rot1(c, &tg, false);
    }
    for q in s {
        c.x(q);
    }
    cells::with_tie(None, || cells::with_cmp_shift(shift, || cells::with_bridge(proxy_r, true, || body_capped(c, t, s, k1, k2, &b, &tg, proxy_r, true))));
    for q in s {
        c.x(q);
    }
    if Y15_TRACE {
        eprintln!("Y15_TICK rev t={t} active={a0} cost={:.1}", c.expected_total() - e0);
    }
}

/// y26: the forms (a, b, ci) with MAJ(x, y, z) = AND(a, b) ^ ci; None where two of the three are identically 0 (the
/// majority is then 0). One of them 0: the AND of the other two.
fn maj_forms(x: &Lin, y: &Lin, z: &Lin) -> Option<(Lin, Lin, Lin)> {
    let zero = |f: &Lin| f.w.is_empty() && !f.one;
    let zs = [zero(x), zero(y), zero(z)];
    if zs.iter().filter(|&&b| b).count() >= 2 {
        return None;
    }
    Some(if zs[2] {
        (x.clone(), y.clone(), Lin::k(false))
    } else if zs[0] {
        (y.clone(), z.clone(), Lin::k(false))
    } else if zs[1] {
        (x.clone(), z.clone(), Lin::k(false))
    } else {
        (x.x(z), y.x(z), z.clone())
    })
}
/// A wire holding AND(a, b) ^ ci.
#[derive(Clone)]
struct MRec {
    q: QubitId,
    a: Lin,
    b: Lin,
    ci: Lin,
}
/// y26: MAJ(x, y, z) over forms, on a fresh wire where it needs one (1 Toffoli), with its erase record.
fn f_maj(c: &mut Builder, x: &Lin, y: &Lin, z: &Lin) -> (Lin, Option<MRec>) {
    match maj_forms(x, y, z) {
        None => (Lin::k(false), None),
        Some((a, b, ci)) => {
            let q = lin_and(c, &a, &b);
            lin_xor_into(c, &ci, q);
            (l(q), Some(MRec { q, a, b, ci }))
        }
    }
}
/// Erase by measurement with the build forms (0 Toffoli).
fn f_erase(c: &mut Builder, r: Option<MRec>) {
    if let Some(r) = r {
        lin_xor_into(c, &r.ci, r.q);
        lin_and_erase(c, r.q, &r.a, &r.b);
    }
}
/// y26, the larger form: X = T + S'0 + 2 S'1 + 4 S'2 as forms over the one register H = P/2 (S'k = H ^ s_k, 256 bits).
/// T = 2 H mod p as [`cells::mod_double`] computes it: H rotated up, plus f under H's top bit on the low `wf` bits
/// (the carry off the window dropped): forms through the window's carries g. Carry-save, three wires a position p:
///   k1[p] = MAJ(T[p - 1], S'0[p - 1], S'1[p - 2])        (register only)
///   k2[p] = MAJ(s1[p - 1], k1[p - 1], S'2[p - 3])        s1[i] = T[i] ^ S'0[i] ^ S'1[i - 1]
///   r[p]  = MAJ(s2[p - 1], k2[p - 1], r[p - 1])          s2[i] = s1[i] ^ k1[i] ^ S'2[i - 2]; the one ripple chain
///   X[i]  = s2[i] ^ k2[i] ^ r[i],  i in [0, 259)
struct CsForms<'a> {
    h: &'a [QubitId],
    s: [QubitId; 3],
    wf: usize,
    fbit: Vec<bool>,
    g: Vec<Lin>,
    k1: Vec<Lin>,
    k2: Vec<Lin>,
    r: Vec<Lin>,
    rec: Vec<[Option<MRec>; 3]>,
    live: Vec<bool>,
}
const CS_TOP: usize = N + 2;
impl CsForms<'_> {
    fn hf(&self, i: isize) -> Lin {
        if i >= 0 && (i as usize) < N { l(self.h[i as usize]) } else { Lin::k(false) }
    }
    fn sf(&self, k: usize, j: isize) -> Lin {
        if j >= 0 && (j as usize) < N { Lin::of(&[self.h[j as usize], self.s[k]]) } else { Lin::k(false) }
    }
    fn tf(&self, i: isize) -> Lin {
        if i < 0 || i as usize >= N {
            Lin::k(false)
        } else if i as usize >= self.wf {
            self.hf(i - 1)
        } else {
            let t = self.hf(i - 1).x(&self.g[i as usize]);
            if self.fbit[i as usize] { t.x(&l(self.h[N - 1])) } else { t }
        }
    }
    fn at(&self, v: &[Lin], p: isize) -> Lin {
        if p < 1 || p as usize > CS_TOP {
            return Lin::k(false);
        }
        assert!(self.live[p as usize], "y26: position {p} is read while its wires are gone");
        v[p as usize].clone()
    }
    fn s1f(&self, i: isize) -> Lin {
        self.tf(i).x(&self.sf(0, i)).x(&self.sf(1, i - 1))
    }
    fn s2f(&self, i: isize) -> Lin {
        self.s1f(i).x(&self.at(&self.k1, i)).x(&self.sf(2, i - 2))
    }
    fn xf(&self, i: usize) -> Lin {
        let i = i as isize;
        self.s2f(i).x(&self.at(&self.k2, i)).x(&self.at(&self.r, i))
    }
    fn build(&mut self, c: &mut Builder, p: usize) {
        assert!(p >= 1 && p <= CS_TOP && !self.live[p]);
        let q = p as isize;
        let (a, ra) = f_maj(c, &self.tf(q - 1), &self.sf(0, q - 1), &self.sf(1, q - 2));
        let (b, rb) = f_maj(c, &self.s1f(q - 1), &self.at(&self.k1, q - 1), &self.sf(2, q - 3));
        let (d, rd) = f_maj(c, &self.s2f(q - 1), &self.at(&self.k2, q - 1), &self.at(&self.r, q - 1));
        self.k1[p] = a;
        self.k2[p] = b;
        self.r[p] = d;
        self.rec[p] = [ra, rb, rd];
        self.live[p] = true;
    }
    /// Erase position p's wires with their build forms (position p - 1 must be as it was at the build).
    fn erase(&mut self, c: &mut Builder, p: usize) {
        assert!(self.live[p]);
        let [ra, rb, rd] = std::mem::take(&mut self.rec[p]);
        f_erase(c, rd);
        f_erase(c, rb);
        f_erase(c, ra);
        self.live[p] = false;
    }
    /// Erase the boundary position `hi` of the chunk (lo, hi], whose positions lo + 1 .. hi - 1 are gone. k1[hi] is
    /// register only. k2[hi] reads k1[hi - 1]: built again (1 Toffoli). r[hi] is measured; with its bit set the
    /// chunk's positions below it are built again (3 Toffoli a position on half the shots), the measurement's phase
    /// is fixed on the forms of r[hi], and they are erased again. Exact.
    fn close_boundary(&mut self, c: &mut Builder, lo: usize, hi: usize) {
        assert!(self.live[hi] && self.live[lo] && hi > lo);
        let [ra, rb, rd] = std::mem::take(&mut self.rec[hi]);
        if hi - 1 == lo {
            f_erase(c, rd);
            f_erase(c, rb);
            f_erase(c, ra);
            self.live[hi] = false;
            return;
        }
        let q = hi as isize;
        if let Some(rb) = rb {
            let (k1m, r1) = f_maj(c, &self.tf(q - 2), &self.sf(0, q - 2), &self.sf(1, q - 3));
            let (a, b, ci) = maj_forms(&self.s1f(q - 1), &k1m, &self.sf(2, q - 3)).expect("y26: k2 of a boundary");
            lin_xor_into(c, &ci, rb.q);
            lin_and_erase(c, rb.q, &a, &b);
            f_erase(c, r1);
        }
        if let Some(rd) = rd {
            let m = c.alloc_bit();
            c.hmr(rd.q, m);
            c.release_clean(rd.q);
            c.push_condition(m);
            for p in lo + 1..hi {
                self.build(c, p);
            }
            let (a, b, ci) = maj_forms(&self.s2f(q - 1), &self.at(&self.k2, q - 1), &self.at(&self.r, q - 1)).expect("y26: r of a boundary");
            lin_cz(c, &a, &b);
            assert!(!ci.one);
            for &w in &ci.w {
                c.cz(w, w);
            }
            for p in (lo + 1..hi).rev() {
                self.erase(c, p);
            }
            c.pop_condition();
            c.free_bit(m);
        }
        f_erase(c, ra);
        self.live[hi] = false;
    }
}
/// y26, the larger form of the multiply's tick-0 phase block: the phase (-1)^(m . y R2) with `h` = P/2 on the wires
/// (before the product is doubled), nothing written, `h` left as found; frees `bits`. The Z layer goes on forms, a
/// chunk at a time: the low chunk (positions 1..55, what the fold's window reads) is kept to the end, the middle chunks
/// are erased once the layer has read them (each leaves its top position, a boundary: [`CsForms::close_boundary`]),
/// the top chunk is open through the fold ([`fold_fwd_forms`]). The chunk plan is taken from the room.
pub(super) fn t0_phase_forms(c: &mut Builder, letter: &[QubitId], h: &[QubitId], bits: Vec<crate::circuit::BitId>) {
    let (s, k1, k2) = ([letter[0], letter[1], letter[2]], letter[3], letter[4]);
    let ((), peak) = c.r3_peak(|c| t0_forms_body(c, s, k1, k2, h, bits));
    assert!(peak as usize <= cells::cap(), "y26: the phase block on forms peaks at {peak}, over the walk cap {}", cells::cap());
}
fn t0_forms_body(c: &mut Builder, s: [QubitId; 3], k1: QubitId, k2: QubitId, h: &[QubitId], bits: Vec<crate::circuit::BitId>) {
    assert_eq!(h.len(), N);
    let (e_start, a_start) = (c.expected_total(), c.active_qubits());
    let mut ph = T0Phase::new(c, k1, k2, N, bits);
    let vpos = |i: usize| (i + N - 3) % N; // W[i] is the layer's position (i - 3) mod N (the three rot1)
    let wf = go_fs("GO_FG_P");
    let fc = f();
    let zero = Lin::k(false);
    let mut st = CsForms {
        h,
        s,
        wf,
        fbit: (0..wf).map(|i| fc.bit(i)).collect(),
        g: vec![zero.clone(); wf],
        k1: vec![zero.clone(); CS_TOP + 1],
        k2: vec![zero.clone(); CS_TOP + 1],
        r: vec![zero.clone(); CS_TOP + 1],
        rec: (0..=CS_TOP).map(|_| [None, None, None]).collect(),
        live: vec![false; CS_TOP + 1],
    };
    assert!((0..N).all(|i| i < wf || !fc.bit(i)) && wf < Y15_WIN);
    // the doubling's window: g[i] = the carry into bit i of (2 H) + ov f, ov = H's top bit; bit 0 of 2 H is 0
    let mut grec: Vec<Option<MRec>> = vec![None; wf];
    for i in 0..wf - 1 {
        let add = if st.fbit[i] { l(h[N - 1]) } else { zero.clone() };
        let (gf, gr) = f_maj(c, &st.hf(i as isize - 1), &add, &st.g[i].clone());
        st.g[i + 1] = gf;
        grec[i + 1] = gr;
    }
    let e_g = c.expected_total();
    // the low chunk: every position the fold's window reads
    const B0: usize = Y15_WIN - 1;
    for p in 1..=B0 {
        st.build(c, p);
    }
    // the chunk plan: the top chunk (open through the fold) as long as the room allows, the rest in the fewest
    // middle chunks
    let fold_wires = 31 + (Y15_WIN - 7);
    let room = cells::cap().saturating_sub(c.active_qubits() as usize);
    let (mut nb, mut top_len) = (0usize, 0usize);
    let mut mids: Vec<usize> = Vec::new();
    loop {
        // the top chunk's positions hold 3 wires each, less the three that are identically 0
        let avail = room.checked_sub(3 * nb + fold_wires).unwrap_or_else(|| panic!("y26: no room for the fold: {room}"));
        top_len = ((avail + 3) / 3).min(CS_TOP - B0);
        let rest = CS_TOP - B0 - top_len;
        // middle chunk j is built over j boundaries
        let caps: Vec<usize> = (0..nb).map(|j| (room - 3 * j) / 3).collect();
        if caps.iter().sum::<usize>() >= rest && (rest == 0) == (nb == 0) {
            let mut left = rest;
            mids = (0..nb)
                .map(|j| {
                    let take = left.div_ceil(nb - j).min(caps[j]);
                    left -= take;
                    take
                })
                .collect();
            assert_eq!(left, 0, "y26: the middle chunks do not cover the register");
            break;
        }
        nb += 1;
        assert!(nb < 40, "y26: no chunk plan at room {room}");
    }
    let mut edges = vec![B0];
    for &w in &mids {
        edges.push(edges.last().unwrap() + w);
    }
    assert_eq!(edges.last().unwrap() + top_len, CS_TOP);
    let mut a_mid = 0;
    for j in 1..edges.len() {
        let (lo, hi) = (edges[j - 1], edges[j]);
        for p in lo + 1..=hi {
            st.build(c, p);
        }
        a_mid = a_mid.max(c.active_qubits());
        for i in (lo + 1..=hi).filter(|&i| i >= Y15_WIN && i < N) {
            // Y26_FAULT (a control of the test, never a build): two positions of the layer swapped
            let at = if Y26_FAULT && (i == 100 || i == 101) { i ^ 1 } else { i };
            ph.z(c, vpos(at), &st.xf(i));
        }
        for p in (lo + 1..hi).rev() {
            st.erase(c, p);
        }
    }
    let lo_top = *edges.last().unwrap();
    for p in lo_top + 1..=CS_TOP {
        st.build(c, p);
    }
    for i in (lo_top + 1..N).filter(|&i| i >= Y15_WIN) {
        ph.z(c, vpos(i), &st.xf(i));
    }
    let e_adds = c.expected_total();
    // the fold on forms
    let x: Vec<Lin> = (0..Y15_WIN).map(|i| st.xf(i)).collect();
    let e = [st.xf(N), st.xf(N + 1), st.xf(N + 2)];
    let (w, mut recs) = fold_fwd_forms(c, &x, &e, s, k1, k2);
    let a_fold = c.active_qubits();
    assert!(a_fold as usize <= cells::cap(), "y26: the fold on forms is over the walk cap: {a_fold} > {}", cells::cap());
    for (i, f) in w.iter().enumerate() {
        ph.z(c, vpos(i), f);
    }
    pop_chain(c, &mut recs);
    let e_fold = c.expected_total();
    for p in (lo_top + 1..=CS_TOP).rev() {
        st.erase(c, p);
    }
    for j in (1..edges.len()).rev() {
        st.close_boundary(c, edges[j - 1], edges[j]);
    }
    let e_bound = c.expected_total();
    for p in (1..=B0).rev() {
        st.erase(c, p);
    }
    if Y26_FUSE_DBL {
        // as start_doubling: the top bit out onto a wire of its own, the register rotated up (h[0] is then clear)
        assert!(st.fbit[0] && wf <= N);
        let out = c.alloc_qubit();
        c.swap(h[N - 1], out);
        for i in (0..N - 1).rev() {
            c.swap(h[i], h[i + 1]);
        }
        // h[i] now holds (2 H)[i] and `out` the bit ov. Bit i of the window's sum is (2 H)[i] ^ f[i] ov ^ g[i];
        // g[i] = MAJ((2 H)[i - 1], f[i - 1] ov, g[i - 1]) is erased while bit i - 1 is still unsummed
        for i in (1..wf).rev() {
            if st.fbit[i] {
                c.cx(out, h[i]);
            }
            lin_xor_into(c, &st.g[i], h[i]);
            if let Some(r) = grec[i].take() {
                let d = if i >= 2 { l(h[i - 1]) } else { zero.clone() };
                let add = if st.fbit[i - 1] { l(out) } else { zero.clone() };
                let (a, b, ci) = maj_forms(&d, &add, &st.g[i - 1]).expect("y26: a window carry");
                lin_xor_into(c, &ci, r.q);
                lin_and_erase(c, r.q, &a, &b);
            }
        }
        c.cx(out, h[0]);
        // as mod_double_pm: bit 0 of the sum is ov itself
        c.cx(h[0], out);
        c.free(out);
    } else {
        for i in (1..wf).rev() {
            f_erase(c, grec[i].take());
        }
    }
    assert!(grec.iter().all(|r| r.is_none()));
    ph.finish(c);
    if Y26_PAD_RNG > 0 {
        let q = c.alloc_qubit();
        for _ in 0..Y26_PAD_RNG {
            let m = c.alloc_bit();
            c.hmr(q, m);
            c.free_bit(m);
        }
        c.release_clean(q);
    }
    assert_eq!(c.active_qubits(), a_start, "y26: a wire was left behind");
    if Y15_TRACE {
    eprintln!(
        "Y26_FORMS active={a_start} cap={} room_after_low={room} wf={wf} edges={edges:?} top={top_len} mid_active={a_mid} fold_active={a_fold} window={:.1} adds={:.1} fold={:.1} boundaries={:.1} all={:.1}",
        cells::cap(),
        e_g - e_start,
        e_adds - e_g,
        e_fold - e_adds,
        e_bound - e_fold,
        c.expected_total() - e_start
    );
    }
}
