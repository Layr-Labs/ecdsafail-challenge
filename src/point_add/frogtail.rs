//! frogtail: a tape-free Stehle-Zimmermann 2-adic Euclid walk in micro-ticks, used as an in-place inverter.
//!
//! Two shelves hold (value | cofactor) with A.v A.c + B.v B.c = p. A is the active shelf. Each tick halves A.v and
//! doubles A.c in one go by relabeling A's ring (frame offset = tick); B is fixed. Inside a ring the value sits
//! ascending from frame 0 and the cofactor descending from the top frame (significance s at frame W - 1 - s), so the
//! relabel moves A.v's emptied low lane to A.c's new low lane. The value | cofactor boundary c(t) is classical:
//! shared by both shelves and every shot. When it moves, the lanes that change owner get the new owner's sign
//! (CNOTs only, valid while both quantities fit).
//!
//! Forward tick t (the inverter's first walk):
//!   step end (t >= 2, e = [j < 0] & A.v odd): j <- -j, parity ^= e, swap A <-> B, e = the new A.c's low bit.
//!   digit: a = A.v[0] & [j >= 0]; A.v += (-1)^[j = 0] a B.v; B.c -= (-1)^[j = 0] a A.c; a is X-measured (bit m_t,
//!     phase (-1)^(m_t a)): the digit record is never stored.
//!   halve: relabel A, boundary sign fixes, j -= 1.
//! Counter: j = g - i (i = ticks since the step started, g = the step's 2-adic gap); at a step end g_new = j_new = -j.
//!
//! The inverse walk replays the "regenerating" tick backwards. That tick keeps the step's digits in Q (a shift
//! register: on ticks with j >= 0 Q moves down one lane and a enters lane QB - 1, so at the step end digit k sits in
//! lane k + QB - g - 1, top-aligned) and erases them at the step end through
//! Q b + L = 0 mod 2^(g+1) (b = A.c >> s', s' = nu(A.c) from a normalizer, L = B.c's low bits, g = j + s'):
//! Q <- -(Q b), rotate up by g, XOR L_k into lane k - 1 for k <= g. Played backwards it recomputes every digit just
//! before the digit is undone; Z^(m_t) on the recomputed a cancels the forward measurement's phase. The last step
//! never ends, so its digits are recomputed once (a 7-bit normalizer) before the inverse walk starts.

use super::arith::{and_lits, dec, inc, ttk_add};
use super::builder::{B, G};
use super::frogdrop::crot_up;
use super::mask::{ge_const, mc_xor, onehot_scan, Dec};
use super::modp_ft::ctrl_add_pool;
use crate::circuit::{BitId, QubitId};

/// digit register (g cap QB - 1)
pub const QB: usize = 23;
/// j = g - i, two's complement (finished shots keep counting down; 8 bits keep them negative to the end)
pub const JB: usize = 8;
/// gap bits
pub const GB: usize = 5;
/// per-tick normalizer shift bits (steps up to 31 ticks)
pub const SB: usize = 5;
/// final-step normalizer shift bits (the last step runs to the end of the walk)
pub const SBF: usize = 7;
/// clean temps used by a tick
pub const NTMP: usize = 8;

/// Classical schedule: ring widths, tick count, boundary c[t] for t in 1..=T+1 (c[0] unused).
#[derive(Clone, Debug)]
pub struct Sched {
    pub wa: usize,
    pub wb: usize,
    pub t: usize,
    pub c: Vec<usize>,
}

impl Sched {
    pub fn from_text(s: &str) -> Sched {
        let mut it = s.lines().filter(|l| !l.trim_start().starts_with('#')).flat_map(|l| l.split_whitespace())
            .map(|w| w.parse::<usize>().unwrap());
        let wa = it.next().unwrap();
        let wb = it.next().unwrap();
        let t = it.next().unwrap();
        let mut c = vec![0];
        c.extend(it);
        assert_eq!(c.len(), t + 2, "schedule needs c[1..=T+1]");
        Sched { wa, wb, t, c }
    }
}

/// Walk registers. `a` = A ring (physical lanes), `bb` = B ring, `q` = digit register (inverse walk only).
pub struct Walk {
    pub a: Vec<QubitId>,
    pub bb: Vec<QubitId>,
    pub q: Vec<QubitId>,
    pub j: Vec<QubitId>,
    pub par: QubitId,
}

impl Walk {
    /// A ring lane at frame f during tick t (frame offset t - 1; the halve of tick t moves it to t).
    pub fn af(&self, t: usize, f: usize) -> QubitId {
        let w = self.a.len();
        self.a[(f + t - 1) % w]
    }
    /// A cofactor lane of significance s during tick t.
    pub fn asig(&self, t: usize, s: usize) -> QubitId {
        self.af(t, self.a.len() - 1 - s)
    }
    pub fn bf(&self, f: usize) -> QubitId {
        self.bb[f]
    }
    pub fn bsig(&self, s: usize) -> QubitId {
        self.bb[self.bb.len() - 1 - s]
    }
}

/// Tick scratch: clean e, a, eq, one, temps (NTMP); s' (SB lanes) = a, eq, one and SB - 3 more (a, eq, one are clean
/// during a step end); `pool` = clean lanes for the digit adds' carries (the room under the circuit peak in the
/// forward walk); `dirty` borrowed (>= QB + 1 lanes, restored). The final-step normalizer's two extra shift bits
/// borrow A's value lanes (|0> once the walk is done).
pub struct Scr {
    pub e: QubitId,
    pub sp: Vec<QubitId>,
    pub a: QubitId,
    pub eq: QubitId,
    pub one: QubitId,
    pub tmp: Vec<QubitId>,
    /// s' lanes beyond a, eq, one (inverse walk only)
    pub xs: Vec<QubitId>,
    pub pool: Vec<QubitId>,
    pub dirty: Vec<QubitId>,
}

impl Scr {
    /// Scratch of the forward walk (no s'), with `room` pool lanes.
    pub fn alloc_fwd(b: &mut B, dirty: &[QubitId], room: usize) -> Scr {
        Scr { e: b.alloc(), sp: vec![], a: b.alloc(), eq: b.alloc(), one: b.alloc(), tmp: b.alloc_n(NTMP), xs: vec![],
              pool: b.alloc_n(room), dirty: dirty.to_vec() }
    }
    pub fn alloc(b: &mut B, dirty: &[QubitId]) -> Scr {
        let (e, a, eq, one) = (b.alloc(), b.alloc(), b.alloc(), b.alloc());
        let xs = b.alloc_n(SB - 3);
        let mut sp = vec![a, eq, one];
        sp.extend(&xs);
        Scr { e, sp, a, eq, one, tmp: b.alloc_n(NTMP), xs, pool: vec![], dirty: dirty.to_vec() }
    }
    pub fn release(self, b: &mut B) {
        b.free(self.e);
        b.free(self.a);
        b.free(self.eq);
        b.free(self.one);
        b.free_n(&self.tmp);
        b.free_n(&self.xs);
        b.free_n(&self.pool);
    }
    /// Lanes |0> during a digit's adds: the pool, e, one, the temps the j = 0 test leaves free, s' beyond a and eq.
    fn add_pool(&self) -> Vec<QubitId> {
        let mut pl = self.pool.clone();
        pl.extend([self.e, self.one]);
        pl.extend(&self.tmp[JB - 2..]);
        pl.extend(&self.xs);
        pl
    }
}

/// Initial state: A = (p, 1), j = 1 (g = 1, i = 0) (B = (x', 0) is the caller's: x' odd in bb[0..256), rest |0>).
pub fn init(b: &mut B, w: &Walk) {
    let p = super::frogdrop_sched::p();
    for f in 0..256 {
        if p.bit(f) {
            b.x(w.af(1, f));
        }
    }
    b.x(w.asig(1, 0));
    b.x(w.j[0]);
}

/// target ^= AND(lits) with clean `tmp`: as mc_xor while the chain fits; otherwise the AND of the first half is held in
/// one temp while the second half's chain reuses the others, and the first half is recomputed to uncompute it.
fn and_xor(b: &mut B, lits: &[(QubitId, bool)], target: QubitId, tmp: &[QubitId], dirty: &[QubitId]) {
    let n = lits.len();
    let t = tmp.len();
    if n < 3 || n - 2 <= t || n > 2 * t {
        mc_xor(b, lits, target, tmp, dirty);
        return;
    }
    // halves: na - 1 temps for A's chain, then (nb - 1) temps + A's result for B's
    let nb = n / 2;
    let na = n - nb;
    assert!(na - 1 <= t && nb <= t);
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
    let la: Vec<QubitId> = lits[..na].iter().map(|l| l.0).collect();
    let lb: Vec<QubitId> = lits[na..].iter().map(|l| l.0).collect();
    let ra = tmp[na - 2];
    // chain over `ls` into temps `ts` (len ls.len() - 1); returns the gates
    let chain = |b: &mut B, ls: &[QubitId], ts: &[QubitId]| -> Vec<G> {
        b.begin();
        let mut acc = ls[0];
        for i in 1..ls.len() {
            b.and_c(acc, ls[i], ts[i - 1]);
            acc = ts[i - 1];
        }
        b.end()
    };
    let ca = chain(b, &la, &tmp[..na - 1]);
    b.play(&ca, false);
    // keep A's result (last gate), uncompute A's intermediates
    b.play(&ca[..ca.len() - 1], true);
    let mut tb: Vec<QubitId> = tmp[..na - 2].to_vec();
    tb.extend(tmp[na - 1..].iter().cloned());
    let cb = chain(b, &lb, &tb[..nb - 1]);
    b.play(&cb[..cb.len() - 1], false);
    let rb_src = if nb >= 2 { if nb == 2 { lb[0] } else { tb[nb - 3] } } else { lb[0] };
    // target ^= ra & (B chain's last AND), as one 3-control step through a temp
    let tl = tb[nb - 2];
    b.and_c(rb_src, lb[nb - 1], tl);
    b.ccx(ra, tl, target);
    b.and_u(rb_src, lb[nb - 1], tl);
    b.play(&cb[..cb.len() - 1], true);
    // uncompute A's result: recompute its intermediates, measure it away, drop them again
    b.play(&ca[..ca.len() - 1], false);
    b.play(&ca[ca.len() - 1..], true);
    b.play(&ca[..ca.len() - 1], true);
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
}

/// Normalizer (recorded, not emitted) with `levels` shift bits: for k = levels-1..0, sp[k] ^= [window lanes 0..2^k
/// all zero], then where sp[k] = 1 the window's lanes [2^k, 2^(k+1) - 1 + QB) move down by 2^k (chains of swaps
/// x <-> x + 2^k, ascending: the zero lanes [0, 2^k) end at the top of their chains). For a window value with
/// nu < 2^levels this gives sp = nu and leaves value >> nu in the low QB lanes; any other value is permuted reversibly.
fn normalize(b: &mut B, win: &[QubitId], sp: &[QubitId], levels: usize, tmp: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    b.begin();
    for k in (0..levels).rev() {
        let s = 1usize << k;
        let lits: Vec<(QubitId, bool)> = win[..s].iter().map(|&q| (q, true)).collect();
        and_xor(b, &lits, sp[k], tmp, dirty);
        let l = 2 * s - 1 + QB;
        for x in 0..l - s {
            b.cswap(sp[k], win[x], win[x + s]);
        }
    }
    b.end()
}

/// Digit erase where `e` = 1 (others untouched). b = win[0..QB) (odd), L = B.c's low lanes, Q top-aligned with
/// m = g + 1 digits: Q <- -(Q b) mod 2^QB = L mod 2^m in the top m lanes; rotating up by g puts L_k in lane
/// (k - 1) mod QB; XOR L_k there for k <= g.
fn digit_erase(b: &mut B, w: &Walk, g: &[QubitId], win: &[QubitId], sc: &Scr, e: QubitId) {
    let q = &w.q;
    let gt = sc.tmp[0];
    // Q <- Q (-b) mod 2^QB: -b = ~b with bit 0 set (b odd), so (-b) >> 1 is b's lanes 1.. complemented. Top-down,
    // bit i (never touched by later rows) controls Q[i+1..) += ((-b) >> 1) << (i + 1); rows add with logical-AND
    // carries on the temps the erase leaves free.
    let pool = &sc.tmp[1..];
    for &x in &win[1..QB] {
        b.x(x);
    }
    for i in (0..QB - 1).rev() {
        let nm = QB - 1 - i;
        b.and_c(q[i], e, gt);
        if nm == 1 {
            b.ccx(gt, win[1], q[QB - 1]);
        } else {
            ctrl_add_pool(b, &win[1..1 + nm], &q[i + 1..QB], gt, pool);
        }
        b.and_u(q[i], e, gt);
    }
    for &x in &win[1..QB] {
        b.x(x);
    }
    // rotate up by g
    for k in 0..GB {
        b.and_c(g[k], e, gt);
        crot_up(b, gt, q, 1 << k);
        b.and_u(g[k], e, gt);
    }
    // XOR L_k into lane (k - 1) mod QB for k <= g (k = 0 always)
    b.ccx(e, w.bsig(0), q[QB - 1]);
    let (f, t2, tw) = (sc.tmp[1], sc.tmp[2], sc.tmp[3]);
    let pre = &sc.tmp[4..4 + GB - 1];
    // f = [l < g] for l < QB - 1 (lane k = l + 1 live iff k <= g); g = j + s' is arbitrary where e = 0, so f is
    // cleared with a comparator after the last live lane
    ge_const(b, g, 1, f, pre);
    let mut dec = Dec::new(g, pre);
    for l in 0..QB - 1 {
        if l > 0 {
            let c = dec.ctrls(b, l);
            mc_xor(b, &c, f, &[tw], &sc.dirty);
        }
        let k = l + 1;
        b.and_c(e, f, t2);
        b.ccx(t2, w.bsig(k), q[k - 1]);
        b.and_u(e, f, t2);
    }
    dec.clear(b);
    ge_const(b, g, (QB - 1) as isize, f, pre);
}

/// s' <- s' + j (mod 2^GB) = g in place (recorded).
fn gap_of(b: &mut B, sp: &[QubitId], j: &[QubitId]) -> Vec<G> {
    b.begin();
    ttk_add(b, &j[..GB], &sp[..GB], None, None);
    b.end()
}

/// Controlled role swap of the shelves. A's cofactor region is wider than B's (finished shots keep doubling A.c):
/// its extra lanes hold the old A.c's sign and take the new one.
fn swap_shelves(b: &mut B, w: &Walk, t: usize, c: usize, e: QubitId) {
    let (wa, wb) = (w.a.len(), w.bb.len());
    for f in 0..c {
        b.cswap(e, w.af(t, f), w.bf(f));
    }
    for s in 0..wb - c {
        b.cswap(e, w.asig(t, s), w.bsig(s));
    }
    let (at, bt) = (w.asig(t, wb - c - 1), w.bsig(wb - c - 1));
    b.cx(at, bt);
    for s in wb - c..wa - c {
        b.ccx(e, bt, w.asig(t, s));
    }
    b.cx(at, bt);
}

/// Step-end tail shared by both walks (e = 1 shots): j <- -j, parity, swap, then e erased (= new A.c odd).
fn step_end_tail(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) {
    let e = sc.e;
    for &x in &w.j {
        b.cx(e, x);
    }
    inc(b, e, &w.j, &sc.tmp[..JB - 1]);
    b.cx(e, w.par);
    swap_shelves(b, w, t, sch.c[t], e);
    b.cx(w.asig(t, 0), e);
}

/// Forward step end of tick t (t >= 2).
fn step_end_fwd(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) {
    b.and_c(w.j[JB - 1], w.af(t, 0), sc.e);
    step_end_tail(b, w, t, sch, sc);
}

/// Regenerating step end of tick t (t >= 2): erases the finished step's digits from Q, then the shared tail.
fn step_end_regen(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) {
    let e = sc.e;
    b.and_c(w.j[JB - 1], w.af(t, 0), e);
    let win: Vec<QubitId> = (0..(1 << SB) - 1 + QB).map(|k| w.asig(t, k)).collect();
    let nr = normalize(b, &win, &sc.sp[..SB], SB, &sc.tmp, &sc.dirty);
    b.play(&nr, false);
    let gr = gap_of(b, &sc.sp, &w.j);
    b.play(&gr, false);
    digit_erase(b, w, &sc.sp[..GB], &win, sc, e);
    b.play(&gr, true);
    b.play(&nr, true);
    step_end_tail(b, w, t, sch, sc);
}

/// Digit of tick t up to (not including) the record of a: a = A.v[0] & [j >= 0] and the two controlled adds.
fn digit_core(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) {
    let c = sch.c[t];
    let wb = w.bb.len();
    let (a, eq) = (sc.a, sc.eq);
    let lits: Vec<(QubitId, bool)> = w.j.iter().map(|&q| (q, true)).collect();
    let req = and_lits(b, &lits, eq, &sc.tmp[..JB - 2]);
    b.play(&req, false);
    let js = w.j[JB - 1];
    b.x(js);
    b.and_c(w.af(t, 0), js, a);
    b.x(js);
    // A.v += (-1)^eq a B.v on the value lanes
    let av: Vec<QubitId> = (0..c).map(|f| w.af(t, f)).collect();
    let bv: Vec<QubitId> = (0..c).map(|f| w.bf(f)).collect();
    for &x in &av {
        b.cx(eq, x);
    }
    let pl = sc.add_pool();
    ctrl_add_pool(b, &bv, &av, a, &pl);
    for &x in &av {
        b.cx(eq, x);
    }
    // B.c -= (-1)^eq a A.c on B's cofactor lanes
    let ac: Vec<QubitId> = (0..wb - c).map(|k| w.asig(t, k)).collect();
    let bc: Vec<QubitId> = (0..wb - c).map(|k| w.bsig(k)).collect();
    b.x(eq);
    for &x in &bc {
        b.cx(eq, x);
    }
    ctrl_add_pool(b, &ac, &bc, a, &pl);
    for &x in &bc {
        b.cx(eq, x);
    }
    b.x(eq);
    b.play(&req, true);
}

/// Digit store as a shift register: on ticks with j >= 0 Q moves down one lane (lane 0, |0> while the step holds
/// fewer than QB digits, wraps to the top) and a enters lane QB - 1. At a step end (all digits stored, j < 0) the
/// digit of counter j sits in lane QB - 1 - j (top-aligned); mid-step the layout is that one shifted up by j.
fn digit_store(b: &mut B, w: &Walk, sc: &Scr) {
    let js = w.j[JB - 1];
    b.x(js);
    for i in 0..QB - 1 {
        b.cswap(js, w.q[i], w.q[i + 1]);
    }
    b.cswap(js, sc.a, w.q[QB - 1]);
    b.x(js);
}

/// A ring boundary moves from c0 to c1 (value = [0, c), cofactor = [c, W)): reassigned lanes take the new owner's
/// sign (the value's at lane c - 1, the cofactor's at lane c).
fn fix_boundary(b: &mut B, lane: &dyn Fn(usize) -> QubitId, c0: usize, c1: usize) {
    if c1 > c0 {
        for l in c0..c1 {
            b.cx(lane(c1), lane(l));
            b.cx(lane(l - 1), lane(l));
        }
    } else if c1 < c0 {
        for l in (c1..c0).rev() {
            b.cx(lane(c1 - 1), lane(l));
            b.cx(lane(c0), lane(l));
        }
    }
}

/// Halve of tick t: relabel (implicit in the frame offset), boundary fixes, j -= 1.
pub fn halve(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) {
    fix_boundary(b, &|f| w.af(t + 1, f), sch.c[t] - 1, sch.c[t + 1]);
    fix_boundary(b, &|f| w.bf(f), sch.c[t], sch.c[t + 1]);
    b.x(sc.one);
    dec(b, sc.one, &w.j, &sc.tmp[..JB - 1]);
    b.x(sc.one);
}

/// Forward tick t (emitted): the digit's record a is X-measured into `m`.
pub fn fwd_tick(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr, m: BitId) {
    // t = 2 never ends a step: j = 0 on every shot (j = 1 at the start, one decrement)
    if t >= 3 {
        step_end_fwd(b, w, t, sch, sc);
    }
    digit_core(b, w, t, sch, sc);
    b.hmr_to(sc.a, m);
    halve(b, w, t, sch, sc);
}

/// Regenerating tick t as three recordings: (step end + digit core, digit store, halve).
pub fn rec_regen_tick(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) -> (Vec<G>, Vec<G>, Vec<G>) {
    b.begin();
    if t >= 3 {
        step_end_regen(b, w, t, sch, sc);
    }
    digit_core(b, w, t, sch, sc);
    let p1 = b.end();
    b.begin();
    digit_store(b, w, sc);
    let p2 = b.end();
    b.begin();
    halve(b, w, t, sch, sc);
    let p3 = b.end();
    (p1, p2, p3)
}

/// Erase of the last (unfinished) step's digits after tick T on every shot (recorded): a 7-bit normalizer (the last
/// step runs to the end; its top two shift bits on A's value lanes, |0> with A.v = 0 and outside the window), g = j + s',
/// then the digit erase with e = 1.
pub(crate) fn final_erase(b: &mut B, w: &Walk, sch: &Sched, sc: &Scr) -> Vec<G> {
    let t = sch.t + 1;
    b.begin();
    // shift-register layout -> top-aligned: a step still in its digit phase at the end (j = J >= 0) holds its digits
    // shifted up by J + 1; rotate Q down by J + 1 (its low lanes are |0>), i.e. by the bits of j + 1 where j + 1 > 0
    let al = {
        b.begin();
        b.x(sc.one);
        inc(b, sc.one, &w.j, &sc.tmp[..JB - 1]);
        b.x(sc.one);
        let js = w.j[JB - 1];
        let gt = sc.tmp[0];
        b.x(js);
        for k in 0..GB {
            b.and_c(w.j[k], js, gt);
            crot_up(b, gt, &w.q, QB - (1 << k));
            b.and_u(w.j[k], js, gt);
        }
        b.x(js);
        b.x(sc.one);
        dec(b, sc.one, &w.j, &sc.tmp[..JB - 1]);
        b.x(sc.one);
        b.end()
    };
    b.play(&al, false);
    let win: Vec<QubitId> = (0..(1 << SBF) - 1 + QB).map(|k| w.asig(t, k)).collect();
    assert!(sch.c[t] >= SBF - SB);
    let mut sp = sc.sp.clone();
    sp.extend((0..SBF - SB).map(|f| w.af(t, f)));
    let nr = normalize(b, &win, &sp, SBF, &sc.tmp, &sc.dirty);
    b.play(&nr, false);
    let gr = gap_of(b, &sp, &w.j);
    b.play(&gr, false);
    b.x(sc.e);
    digit_erase(b, w, &sp[..GB], &win, sc, sc.e);
    b.x(sc.e);
    b.play(&gr, true);
    b.play(&nr, true);
    b.play(&al, true);
    b.end()
}

/// Forward walk: init, then ticks 1..=T. Returns the digit measurement bits m[t] (index t, m[0] unused). The inverse
/// lives in A's cofactor lanes `out_lanes` afterwards.
pub fn walk_forward(b: &mut B, w: &Walk, sch: &Sched, sc: &Scr) -> Vec<BitId> {
    init(b, w);
    let m = b.fresh_bits(sch.t + 1);
    for t in 1..=sch.t {
        fwd_tick(b, w, t, sch, sc, m[t]);
    }
    m
}

/// Inverse of walk_forward (Q, clean, must be allocated in `w.q`; it is |0> again afterwards): recompute the last
/// step's digits, then replay the regenerating ticks backwards, cancelling each digit measurement's phase.
pub fn walk_inverse(b: &mut B, w: &Walk, sch: &Sched, sc: &Scr, m: &[BitId]) {
    let fe = final_erase(b, w, sch, sc);
    b.play(&fe, true);
    for t in (1..=sch.t).rev() {
        let (p1, p2, p3) = rec_regen_tick(b, w, t, sch, sc);
        b.play(&p3, true);
        b.play(&p2, true);
        b.z_if(sc.a, m[t]);
        b.play(&p1, true);
    }
    init(b, w);
}

/// After the walk: x'^-1 = (-1)^S C 2^-T mod p, C = two's complement value of these lanes (LSB first) and
/// S = [B.v = -1] ^ parity ^ [x was negated].
pub fn out_lanes(w: &Walk, sch: &Sched) -> Vec<QubitId> {
    let t = sch.t + 1;
    (0..sch.wa - sch.c[t]).map(|s| w.asig(t, s)).collect()
}

/// End state of B is (+-1, +-p) (same sign): fold it into one qubit holding [B.v = -1] (returned); every other B
/// lane is |0> afterwards. Recorded so it can be undone.
pub fn collapse_b(b: &mut B, w: &Walk, sch: &Sched) -> (QubitId, Vec<G>) {
    let c = sch.c[sch.t + 1];
    let cl = sch.wb - c;
    let p = super::frogdrop_sched::p();
    // patterns for B = (1, p) and (-1, -p) over the value lanes [0, c) and cofactor lanes [0, cl)
    let mut plus: Vec<(QubitId, bool)> = vec![];
    let mut minus: Vec<(QubitId, bool)> = vec![];
    for f in 0..c {
        plus.push((w.bf(f), f == 0));
        minus.push((w.bf(f), true));
    }
    let mp = (!p).wrapping_add(super::frogdrop_sched::N::from(1u64)); // -p in 384-bit two's complement
    for s in 0..cl {
        plus.push((w.bsig(s), s < 384 && p.bit(s)));
        minus.push((w.bsig(s), if s < 384 { mp.bit(s) } else { true }));
    }
    let key = w.bf(1); // 0 for +, 1 for -
    b.begin();
    for &(q, v) in &plus {
        if v {
            b.x(q);
        }
    }
    for (&(q, vp), &(_, vm)) in plus.iter().zip(&minus) {
        if q != key && vp != vm {
            b.cx(key, q);
        }
    }
    let r = b.end();
    b.play(&r, false);
    (key, r)
}

/// z = y * C * 2^-tt mod p into a zero register z (relabeled in place by the halvings), C = two's complement value of
/// `c` (LSB first, top lane weighs -2^(M-1)), y in [0, p) restored. Bottom-up halving Horner over C's lanes, then
/// tt - M more halvings.
pub fn product_tail(b: &mut B, ms: &super::modp_frogdrop::Ms, z: &mut Vec<QubitId>, c: &[QubitId], y: &[QubitId],
                    tt: usize) {
    use super::modp_frogdrop::{ctrl_modadd, mod_halve};
    let m = c.len();
    assert!(tt >= m);
    for k in 0..m {
        let d = c[(k + 1) % m];
        if k + 1 < m {
            ctrl_modadd(b, ms, z, y, c[k], d);
        } else {
            b.begin();
            ctrl_modadd(b, ms, z, y, c[k], d);
            let r = b.end();
            b.play(&r, true);
        }
        mod_halve(b, ms, z, y);
    }
    for _ in m..tt {
        mod_halve(b, ms, z, y);
    }
}
