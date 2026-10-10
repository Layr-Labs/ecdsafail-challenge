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
//!   step end (t >= 3, e = [j < 0] & A.v odd): j <- -j, parity ^= e, swap A <-> B, e = the new A.c's low bit.
//!   digit: a = A.v[0] & [j >= 0]; A.v += (-1)^[j = 0] a B.v; B.c -= (-1)^[j = 0] a A.c; a is X-measured (bit m_t,
//!     phase (-1)^(m_t a)): the digit record is never stored.
//!   halve: relabel A, boundary sign fixes, j -= 1.
//! Counter: j = g - i (i = ticks since the step started, g = the step's 2-adic gap); at a step end g_new = j_new = -j.
//!
//! The inverse walk replays the "regenerating" tick backwards. That tick keeps the step's digits in Q (a shift
//! register: on ticks with j >= 0 Q moves down one lane and a enters lane QB - 1, so at the step end digit k sits in
//! lane k + QB - g - 1, top-aligned) and erases them at digit completion through
//! Q b + L = 0 mod 2^(g+1) (b = A.c >> s', s' = nu(A.c) from a normalizer, L = B.c's low bits, g = j + s'):
//! Q <- -(Q b), rotate up by g, XOR L_k into lane k - 1 for k <= g. Played backwards it recomputes every digit just
//! before the digit is undone; Z^(m_t) on the recomputed a cancels the forward measurement's phase.
//! The eraser runs only after even ticks with j=-1; Q is already clean during the idle tail and absorption.
//!
//! Absorption of finished shots (from tick TABS on): a shot whose A.v is 0 runs one more step end at its first tick
//! with j < 0 (e ^= [j < 0] & B.v odd & [A.v's low min(ZL, c) lanes zero]; no shot inside the envelope has those
//! lanes zero with j < 0 unless A.v = 0). The step end erases the last step's digits as usual, swaps the shelves
//! (B = (0, C), A = (+-1, +-p)) and is followed by a clear: A = (0, 1), B.v = -2s (s = [the old B.v = -1]). After
//! that the shot is frozen: B.v is even, so j (decremented under B.v's low bit) stays at +1, a = 0, and A.c = 2^m
//! counts the ticks since the absorption. Ring A therefore needs no room for a finished shot's growing cofactor
//! (W_A = W_B), and the final-step erase is gone. At the end (`unabsorb`) C_T = C 2^m is rebuilt by a barrel shift.
//! Frozen j = +1 for absorbed shots: Q is all zero and a = 0 there, so anything gated on j >= 0 only moves zeros.

use super::arith::{and_lits, dec, inc, rot4_up, ttk_add};
use super::builder::{B, G};
use super::frogdrop::crot_up;
use super::mask::{ge_const, mc_xor, onehot_scan, Dec};
use super::modp_ft::ctrl_add_pool;
use crate::circuit::{BitId, QubitId};

/// Lever switch (every lever is on in this build).
pub(crate) fn lv(name: &str) -> bool {
    let _ = name;
    true
}

/// digit register (g cap QB - 1)
pub const QB: usize = 23;
/// j = g - i (in [-22, 22] inside the envelope) has the parity of t at the start of tick t (a halve decrements it,
/// a step end negates it), so the register holds h = (j - (t mod 2)) / 2, two's complement: a step end on an odd tick
/// is a complement (j -> -j is h -> -h - 1), the halve of an odd tick leaves h, [j = 0] is [h = 0] on even ticks and
/// never on odd ones, [j < 0] = [h < 0]. Absorbed shots hold h = 0 (j = 1 on odd ticks, 0 on even ones).
pub const JB: usize = 5;
/// first tick with the absorption logic (finished shots appear from tick ~494 on)
pub const TABS: usize = 485;
/// zero-test lanes of A.v for the absorption flag
pub const ZL: usize = 22;
/// bits of m (ticks since the absorption, m < 2^MB)
pub const MB: usize = 6;
/// lanes of the rebuilt C_T register (B's cofactor lanes plus RLEN - (W_B - c[T+1]) lanes of A)
pub const RLEN: usize = 318;
/// gap bits
pub const GB: usize = 5;
/// per-tick normalizer shift bits (steps up to 31 ticks)
pub const SB: usize = 5;
/// clean temps used by a tick
pub const NTMP: usize = 8;

/// Classical schedule: ring widths, tick count, boundary c[t] for t in 1..=T+1 (c[0] unused).
#[derive(Clone, Debug)]
pub struct Sched {
    pub wa: usize,
    pub wb: usize,
    pub t: usize,
    pub c: Vec<usize>,
    /// compressed widths of tick t (`lsc`): values fit kv[t] lanes, cofactors kc[t] (kv <= c, kc <= W_B - c)
    pub kv: Vec<usize>,
    pub kc: Vec<usize>,
}

/// kv kc per tick for the schedule's T (`lsc`)
const LSC: &str = include_str!("lsc_frogtail.txt");

impl Sched {
    pub fn from_text(s: &str) -> Sched {
        let mut it = s
            .lines()
            .filter(|l| !l.trim_start().starts_with('#'))
            .flat_map(|l| l.split_whitespace())
            .map(|w| w.parse::<usize>().unwrap());
        let wa = it.next().unwrap();
        let wb = it.next().unwrap();
        let t = it.next().unwrap();
        let mut c = vec![0];
        c.extend(it);
        assert_eq!(c.len(), t + 2, "schedule needs c[1..=T+1]");
        let kv = c.clone();
        let kc = c.iter().map(|&x| wb.saturating_sub(x)).collect();
        let mut sch = Sched { wa, wb, t, c, kv, kc };
        sch.load_lsc(LSC);
        sch
    }
    /// Compressed widths from `s` (T, then kv kc for t = 1..T) when its T is the schedule's.
    pub fn load_lsc(&mut self, s: &str) {
        let v: Vec<usize> = s
            .lines()
            .filter(|l| !l.trim_start().starts_with('#'))
            .flat_map(|l| l.split_whitespace())
            .map(|w| w.parse::<usize>().unwrap())
            .collect();
        if v[0] != self.t {
            return;
        }
        for t in 1..=self.t {
            let (kv, kc) = (v[2 * t - 1], v[2 * t]);
            assert!(2 <= kv && kv <= self.c[t] && 2 <= kc && kc <= self.wb - self.c[t]);
            self.kv[t] = kv;
            self.kc[t] = kc;
        }
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
    /// Q's frame lanes during tick t. Ring layout ("ringq"): frame lane f is q[(f + t) mod QB], so the digit of tick
    /// t lands in frame lane QB - 1 and moves down one frame lane per tick for free (the old shift register).
    pub fn qfr(&self, t: usize) -> Vec<QubitId> {
        if lv("ringq") {
            (0..QB).map(|f| self.q[(f + t) % QB]).collect()
        } else {
            self.q.clone()
        }
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
        Scr {
            e: b.alloc(),
            sp: vec![],
            a: b.alloc(),
            eq: b.alloc(),
            one: b.alloc(),
            tmp: b.alloc_n(NTMP),
            xs: vec![],
            pool: b.alloc_n(room),
            dirty: dirty.to_vec(),
        }
    }
    pub fn alloc(b: &mut B, dirty: &[QubitId]) -> Scr {
        let (e, a, eq, one) = (b.alloc(), b.alloc(), b.alloc(), b.alloc());
        let xs = b.alloc_n(SB - 3);
        let mut sp = vec![a, eq, one];
        sp.extend(&xs);
        Scr {
            e,
            sp,
            a,
            eq,
            one,
            tmp: b.alloc_n(NTMP),
            xs,
            pool: vec![],
            dirty: dirty.to_vec(),
        }
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
        if lv("eqmbu") {
            // [j = 0] is held without its AND chain (measured erase), so the chain temps are free
            pl.extend(&self.tmp[..JB - 2]);
        }
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
}

/// target ^= AND(lits) with clean `tmp`: as mc_xor while the chain fits; otherwise the AND of the first half is held in
/// one temp while the second half's chain reuses the others, and the first half is recomputed to uncompute it.
fn and_xor(
    b: &mut B,
    lits: &[(QubitId, bool)],
    target: QubitId,
    tmp: &[QubitId],
    dirty: &[QubitId],
) {
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
    let rb_src = if nb >= 2 {
        if nb == 2 {
            lb[0]
        } else {
            tb[nb - 3]
        }
    } else {
        lb[0]
    };
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
fn normalize(
    b: &mut B,
    win: &[QubitId],
    sp: &[QubitId],
    levels: usize,
    tmp: &[QubitId],
    dirty: &[QubitId],
) -> Vec<G> {
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
fn digit_erase(
    b: &mut B,
    w: &Walk,
    g: &[QubitId],
    win: &[QubitId],
    sc: &Scr,
    e: QubitId,
    zl: &[QubitId],
    q: &[QubitId],
) {
    let gt = sc.tmp[0];
    // Q <- Q (-b) mod 2^QB: -b = ~b with bit 0 set (b odd), so (-b) >> 1 is b's lanes 1.. complemented. Top-down,
    // bit i (never touched by later rows) controls Q[i+1..) += ((-b) >> 1) << (i + 1); rows add with logical-AND
    // carries on the temps the erase leaves free and the shelves' cleared sign-extension lanes `zl`.
    let mut pool = sc.tmp[1..].to_vec();
    pool.extend(&sc.pool);
    pool.extend(zl);
    let pool = &pool[..];
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

/// Local sign compression of tick t: inside the envelope the lanes [kv, c) of both values and [kc, W_B - c) of both
/// cofactors hold the sign of lane kv - 1 (kc - 1); XORing it in clears them, and the same gates extend the (new)
/// sign again afterwards. Returns the cleared lanes (|0> in between).
fn lsc(b: &mut B, w: &Walk, t: usize, c: usize, kv: usize, kc: usize) -> Vec<QubitId> {
    lsc_from(b, w, t, c, kv, kc, 0, 0)
}

/// `lsc` that leaves A's cofactor lanes below `a_lo` and B's below `b_lo` extended.
#[allow(clippy::too_many_arguments)]
fn lsc_from(
    b: &mut B,
    w: &Walk,
    t: usize,
    c: usize,
    kv: usize,
    kc: usize,
    a_lo: usize,
    b_lo: usize,
) -> Vec<QubitId> {
    let wb = w.bb.len();
    let mut z = vec![];
    for f in kv..c {
        b.cx(w.af(t, kv - 1), w.af(t, f));
        b.cx(w.bf(kv - 1), w.bf(f));
        z.extend([w.af(t, f), w.bf(f)]);
    }
    for s in kc.max(a_lo)..wb - c {
        b.cx(w.asig(t, kc - 1), w.asig(t, s));
        z.push(w.asig(t, s));
    }
    for s in kc.max(b_lo)..wb - c {
        b.cx(w.bsig(kc - 1), w.bsig(s));
        z.push(w.bsig(s));
    }
    z
}

/// Controlled role swap of the shelves, over the compressed widths (the cleared lanes match). A's cofactor region is
/// wider than B's (finished shots keep doubling A.c): its extra lanes hold the old A.c's sign and take the new one.
fn swap_shelves(b: &mut B, w: &Walk, t: usize, sch: &Sched, e: QubitId) {
    let (wa, wb) = (w.a.len(), w.bb.len());
    let c = sch.c[t];
    let (kv, kc) = if wa == wb { (sch.kv[t], sch.kc[t]) } else { (c, wb - c) };
    lsc(b, w, t, c, kv, kc);
    for f in 0..kv {
        b.cswap(e, w.af(t, f), w.bf(f));
    }
    for s in 0..kc {
        b.cswap(e, w.asig(t, s), w.bsig(s));
    }
    lsc(b, w, t, c, kv, kc);
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
    if t % 2 == 0 {
        inc(b, e, &w.j, &sc.tmp[..JB - 1]);
    }
    b.cx(e, w.par);
    swap_shelves(b, w, t, sch, e);
    b.cx(w.asig(t, 0), e);
}

/// Absorption flag (t >= TABS): e ^= [j < 0] & B.v odd & [A.v lanes 0..min(ZL, c) all zero]. Exclusive with the
/// ordinary step-end condition (A.v odd). `temps` clean.
fn absorb_flag(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr, temps: &[QubitId]) {
    let mut lits = vec![(w.j[JB - 1], false), (w.bf(0), false)];
    lits.extend((0..sch.c[t].min(ZL)).map(|f| (w.af(t, f), true)));
    if lv("absorb13") {
        let mut tt = temps.to_vec();
        for &x in &sc.xs {
            if !tt.contains(&x) {
                tt.push(x);
            }
        }
        and_xor(b, &lits, sc.e, &tt, &sc.dirty);
    } else {
        mc_xor(b, &lits, sc.e, temps, &sc.dirty);
    }
}

/// Clear after an absorbing step end (t >= TABS): A = (+-1, +-p) -> (0, 1), B.v = 0 -> -2s with s = [A.v = -1].
/// f = !B.v[0] & A.v[0] identifies these shots (in e, clean again after the tail; fs in a).
fn absorb_clear(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) {
    let c = sch.c[t];
    let cl = w.a.len() - c;
    let (f, fs, b0) = (sc.e, sc.a, w.bf(0));
    b.x(b0);
    b.and_c(b0, w.af(t, 0), f);
    b.x(b0);
    b.and_c(f, w.af(t, 1), fs);
    for l in 1..c {
        b.cx(fs, w.bf(l));
    }
    for l in 2..c {
        b.cx(fs, w.af(t, l));
    }
    let p = super::frogdrop_sched::p();
    let mp = (!p).wrapping_add(super::frogdrop_sched::N::from(1u64));
    for s in 1..cl {
        let pb = s < 384 && p.bit(s);
        let mb = if s < 384 { mp.bit(s) } else { true };
        if pb {
            b.cx(f, w.asig(t, s));
        }
        if pb != mb {
            b.cx(fs, w.asig(t, s));
        }
    }
    b.and_u(f, w.af(t, 1), fs);
    b.ccx(f, w.bf(1), w.af(t, 1));
    b.cx(f, w.af(t, 0));
    b.x(b0);
    b.and_u(b0, w.asig(t, 0), f);
    b.x(b0);
}

/// Forward step end of tick t (t >= 2; t = T + 1 is the closing absorption step).
fn step_end_fwd(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) {
    b.and_c(w.j[JB - 1], w.af(t, 0), sc.e);
    if t >= TABS {
        let mut temps = sc.tmp.clone();
        temps.extend([sc.a, sc.eq, sc.one]);
        temps.extend(&sc.pool);
        absorb_flag(b, w, t, sch, sc, &temps);
    }
    step_end_tail(b, w, t, sch, sc);
    if t >= TABS {
        absorb_clear(b, w, t, sch, sc);
    }
}

/// Regenerating step end of tick t (t >= 2): erases the finished step's digits from Q, then the shared tail.
fn step_end_regen(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) {
    // Q was erased at the end of its digit phase, before the idle tail.
    step_end_fwd(b, w, t, sch, sc);
}

/// Erase a completed digit word immediately after its final digit and halve.
/// Active j has parity 1-t after tick t, so j=-1 can occur only on even ticks.
/// On the subsequent idle tail, nu(A.c) increases and j decreases equally;
/// normalized b, g=nu(A.c)+j, B.c and the completed digit word are invariant.
fn finish_digits(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) {
    if t % 2 != 0 {
        return;
    }
    if lv("erase2") {
        finish_digits2(b, w, t, sch, sc);
        return;
    }
    // the shelves' sign-extension lanes at tick t + 1, cleared outside the normalizer window and B.c's low QB lanes
    let nw = (1 << SB) - 1 + QB;
    let tz = (t + 1).min(sch.t);
    let (cz, kv, kc) = if t < sch.t && w.a.len() == w.bb.len() {
        (sch.c[t + 1], sch.kv[t + 1], sch.kc[t + 1])
    } else {
        (sch.c[tz + 1], sch.c[tz + 1], w.bb.len() - sch.c[tz + 1])
    };
    let zl = lsc_from(b, w, t + 1, cz, kv, kc, nw, QB);
    let lits: Vec<(QubitId, bool)> = w.j.iter().map(|&q| (q, false)).collect();
    and_xor(b, &lits, sc.e, &sc.tmp, &sc.dirty);
    let win: Vec<QubitId> = (0..nw).map(|k| w.asig(t + 1, k)).collect();
    let nr = normalize(b, &win, &sc.sp[..SB], SB, &sc.tmp, &sc.dirty);
    b.play(&nr, false);
    // On selected inputs j=-1; other inputs never use the erased word.
    b.begin();
    dec(b, sc.e, &sc.sp[..GB], &sc.tmp[..GB - 1]);
    let gr = b.end();
    b.play(&gr, false);
    let qf = w.qfr(t);
    digit_erase(b, w, &sc.sp[..GB], &win, sc, sc.e, &zl, &qf);
    b.play(&gr, true);
    b.play(&nr, true);
    and_xor(b, &lits, sc.e, &sc.tmp, &sc.dirty);
    lsc_from(b, w, t + 1, cz, kv, kc, nw, QB);
}

/// Lanes of the erase window (A.c significance 1..): g <= QB - 1 shifts plus b's QB lanes.
const WIN2: usize = 2 * QB - 1;

/// Content of the ring `t` moves up by u (k1 + 2 k2): rot4 on each residue class mod gcd(u, n), reindexed so the
/// class's step u / gcd is one position.
fn rot4_unit(b: &mut B, k1: QubitId, k2: QubitId, t: &[QubitId], u: usize) {
    let n = t.len();
    let gcd = |mut x: usize, mut y: usize| {
        while y != 0 {
            let r = x % y;
            x = y;
            y = r;
        }
        x
    };
    let g = gcd(u % n, n).max(1);
    let m = n / g;
    let st = (u / g) % m;
    for r in 0..g {
        let sub: Vec<QubitId> = (0..m).map(|i| t[r + g * ((st * i) % m)]).collect();
        rot4_up(b, k1, k2, &sub);
    }
}

/// Max shift left after normalizer level k is applied, over gaps g <= QB - 1.
fn norm_rest(k: usize) -> usize {
    (0..QB).filter(|g| (g >> k) & 1 == 1).map(|g| g & ((1 << k) - 1)).max().unwrap_or(0)
}

/// The even-tick erase, version 2. After tick t's halve A.c's significance-0 lane is |0> on every shot, so the
/// normalizer runs on A.c >> 1 and yields g = nu(A.c) - 1 directly (no gap decrement), and that lane joins the
/// temps. Zero tests are computed coherently and erased by X measurement (phase oracle on outcome 1). e = [j = -1]
/// is computed after the normalizer and erased before its undo, so it is a temp for the zero tests too.
fn finish_digits2(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) {
    if t == 2 && lv("t2") {
        // every shot completes its first step here: g = 1, b = A.c / 4 = 1, digits (1, a_2) with L = 2 a_2 - 1
        // mod 4, so a_2 = !L_1
        let q = w.qfr(t);
        b.x(q[QB - 2]);
        b.cx(w.bsig(1), q[QB - 1]);
        b.x(q[QB - 1]);
        return;
    }
    // the shelves' sign-extension lanes at tick t + 1, cleared outside A.c's low 1 + WIN2 lanes and B.c's low QB
    let tz = (t + 1).min(sch.t);
    let (cz, kv, kc) = if t < sch.t && w.a.len() == w.bb.len() {
        (sch.c[t + 1], sch.kv[t + 1], sch.kc[t + 1])
    } else {
        (sch.c[tz + 1], sch.c[tz + 1], w.bb.len() - sch.c[tz + 1])
    };
    let zl = lsc_from(b, w, t + 1, cz, kv, kc, 1 + WIN2, QB);
    let a0 = w.asig(t + 1, 0);
    let win: Vec<QubitId> = (0..WIN2).map(|k| w.asig(t + 1, 1 + k)).collect();
    let q = w.qfr(t);
    let g = &sc.sp[..GB];
    // normalizer: level k tests the window's low 2^k lanes and moves the next rest_k + QB lanes down by 2^k
    let pair = lv("nrot4");
    b.begin();
    for k in (0..SB).rev() {
        let s = 1usize << k;
        if pair && k == 0 {
            break;
        }
        let lits: Vec<(QubitId, bool)> = win[..s].iter().map(|&x| (x, true)).collect();
        let mut temps = sc.tmp.clone();
        temps.extend([sc.e, a0]);
        temps.extend(&sc.sp[..k]);
        b.mbu_compute(sc.sp[k], &lits, &temps);
        if pair && k == 1 {
            // g0 = [the window after the g1 shift has its lane 0 zero] = !w0 & !(g1 & w2); then one rotation of
            // the low 3 + QB lanes down by g0 + 2 g1 (rot4, content moves down)
            let tt = sc.tmp[0];
            b.and_c(sc.sp[1], win[2], tt);
            b.mbu_compute(sc.sp[0], &[(win[0], true), (tt, true)], &[]);
            b.and_u(sc.sp[1], win[2], tt);
            let rv: Vec<QubitId> = win[..3 + QB].iter().rev().cloned().collect();
            rot4_up(b, sc.sp[0], sc.sp[1], &rv);
            break;
        }
        // lane 0 is never read after the last level (b's bit 0 is 1)
        let lo = if k == 0 { 1 } else { 0 };
        for x in lo..norm_rest(k) + QB {
            b.cswap(sc.sp[k], win[x], win[x + s]);
        }
    }
    let nr = b.end();
    b.play(&nr, false);
    let jl: Vec<(QubitId, bool)> = w.j.iter().map(|&x| (x, false)).collect();
    b.begin();
    b.mbu_compute(sc.e, &jl, &sc.tmp);
    let er = b.end();
    b.play(&er, false);
    let e = sc.e;
    // Q <- Q (-b) mod 2^QB (rows as digit_erase), carries on tmp[1..] and A.c's significance-0 lane
    let gt = sc.tmp[0];
    let mut pool: Vec<QubitId> = sc.tmp[1..].to_vec();
    pool.push(a0);
    pool.extend(&sc.pool);
    pool.extend(&zl);
    for &x in &win[1..QB] {
        b.x(x);
    }
    for i in (0..QB - 1).rev() {
        let nm = QB - 1 - i;
        b.and_c(q[i], e, gt);
        if nm == 1 {
            b.ccx(gt, win[1], q[QB - 1]);
        } else {
            ctrl_add_pool(b, &win[1..1 + nm], &q[i + 1..QB], gt, &pool);
        }
        b.and_u(q[i], e, gt);
    }
    for &x in &win[1..QB] {
        b.x(x);
    }
    // rotate Q up by g where e
    if lv("rot4") {
        let (c1, c2) = (sc.tmp[0], sc.tmp[1]);
        for k in [0usize, 2] {
            b.and_c(g[k], e, c1);
            b.and_c(g[k + 1], e, c2);
            rot4_unit(b, c1, c2, &q, 1 << k);
            b.and_u(g[k + 1], e, c2);
            b.and_u(g[k], e, c1);
        }
        b.and_c(g[4], e, c1);
        crot_up(b, c1, &q, 16);
        b.and_u(g[4], e, c1);
    } else {
        for k in 0..GB {
            b.and_c(g[k], e, gt);
            crot_up(b, gt, &q, 1 << k);
            b.and_u(g[k], e, gt);
        }
    }
    // XOR L_k into lane (k - 1) mod QB for k <= g where e; L_0 = 1 (b and the digit word are odd)
    b.cx(e, q[QB - 1]);
    if lv("mask6") {
        // f = e & [l < g], toggled by a full decoder over (g, e) at the values 32 + l
        let f = sc.tmp[0];
        let mut v: Vec<QubitId> = g.to_vec();
        v.push(e);
        let pre = &sc.tmp[1..1 + GB];
        let mut dd = Dec::new(&v, pre);
        b.cx(e, f);
        for l in 0..QB {
            let c = dd.ctrls(b, (1 << GB) + l);
            mc_xor(b, &c, f, &[], &sc.dirty);
            if l + 1 < QB {
                b.ccx(f, w.bsig(l + 1), q[l]);
            }
        }
        dd.clear(b);
    } else {
        let (f, t2, tw) = (sc.tmp[1], sc.tmp[2], sc.tmp[3]);
        let pre = &sc.tmp[4..4 + GB - 1];
        ge_const(b, g, 1, f, pre);
        let mut dec = Dec::new(g, pre);
        for l in 0..QB - 1 {
            if l > 0 {
                let c = dec.ctrls(b, l);
                mc_xor(b, &c, f, &[tw], &sc.dirty);
            }
            b.and_c(e, f, t2);
            b.ccx(t2, w.bsig(l + 1), q[l]);
            b.and_u(e, f, t2);
        }
        dec.clear(b);
        ge_const(b, g, (QB - 1) as isize, f, pre);
    }
    b.play(&er, true);
    b.play(&nr, true);
    lsc_from(b, w, t + 1, cz, kv, kc, 1 + WIN2, QB);
}

/// Digit of tick t up to (not including) the record of a: a = A.v[0] & [j >= 0] and the two controlled adds.
fn digit_core(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr, a: QubitId) {
    let c = sch.c[t];
    let wb = w.bb.len();
    let eq = sc.eq;
    let lits: Vec<(QubitId, bool)> = w.j.iter().map(|&q| (q, true)).collect();
    let eqm = lv("eqmbu");
    // [j = 0] only on even ticks
    let even = t % 2 == 0;
    let req = if !even {
        vec![]
    } else if eqm {
        b.mbu_compute(eq, &lits, &sc.tmp[..JB - 2]);
        vec![]
    } else {
        let r = and_lits(b, &lits, eq, &sc.tmp[..JB - 2]);
        b.play(&r, false);
        r
    };
    let js = w.j[JB - 1];
    b.x(js);
    b.and_c(w.af(t, 0), js, a);
    b.x(js);
    // compressed widths (the shelves' cleared sign-extension lanes join the carry pool)
    let (kv, kc) = if w.a.len() == wb { (sch.kv[t], sch.kc[t]) } else { (c, wb - c) };
    let mut pl = lsc(b, w, t, c, kv, kc);
    pl.extend(sc.add_pool());
    if !even && !eqm {
        // add_pool holds the [j = 0] chain temps already when that test is measured away
        pl.extend(&sc.tmp[..JB - 2]);
    }
    if a != sc.a {
        // the digit lives in Q: the tick's `a` qubit is free
        pl.push(sc.a);
    }
    // A.v += (-1)^eq a B.v on the value lanes
    let av: Vec<QubitId> = (0..kv).map(|f| w.af(t, f)).collect();
    let bv: Vec<QubitId> = (0..kv).map(|f| w.bf(f)).collect();
    for &x in &av {
        b.cx(eq, x);
    }
    ctrl_add_pool(b, &bv, &av, a, &pl);
    for &x in &av {
        b.cx(eq, x);
    }
    // B.c -= (-1)^eq a A.c on B's cofactor lanes
    let ac: Vec<QubitId> = (0..kc).map(|k| w.asig(t, k)).collect();
    let bc: Vec<QubitId> = (0..kc).map(|k| w.bsig(k)).collect();
    b.x(eq);
    for &x in &bc {
        b.cx(eq, x);
    }
    ctrl_add_pool(b, &ac, &bc, a, &pl);
    for &x in &bc {
        b.cx(eq, x);
    }
    b.x(eq);
    lsc(b, w, t, c, kv, kc);
    if even {
        if eqm {
            b.mbu_erase(eq, &lits, &sc.tmp[..JB - 2]);
        } else {
            b.play(&req, true);
        }
    }
}

/// Digit store as a shift register: on ticks with j >= 0 Q moves down one lane (lane 0, |0> while the step holds
/// fewer than QB digits, wraps to the top) and a enters lane QB - 1. At a step end (all digits stored, j < 0) the
/// digit of counter j sits in lane QB - 1 - j (top-aligned); mid-step the layout is that one shifted up by j.
fn digit_store(b: &mut B, w: &Walk, sc: &Scr) {
    if lv("ringq") {
        // the digit was computed straight into its ring lane
        return;
    }
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

/// Halve of tick t: relabel (implicit in the frame offset), boundary fixes, j -= 1 where B.v is odd (every shot but
/// an absorbed one).
pub fn halve(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr) {
    fix_boundary(b, &|f| w.af(t + 1, f), sch.c[t] - 1, sch.c[t + 1]);
    fix_boundary(b, &|f| w.bf(f), sch.c[t], sch.c[t + 1]);
    if t % 2 == 0 {
        dec(b, w.bf(0), &w.j, &sc.tmp[..JB - 1]);
    }
}

/// Forward tick t (emitted): the digit's record a is X-measured into `m`.
pub fn fwd_tick(b: &mut B, w: &Walk, t: usize, sch: &Sched, sc: &Scr, m: BitId) {
    // t = 2 never ends a step: j = 0 on every shot (j = 1 at the start, one decrement)
    if t >= 3 {
        step_end_fwd(b, w, t, sch, sc);
    }
    digit_core(b, w, t, sch, sc, sc.a);
    b.hmr_to(sc.a, m);
    halve(b, w, t, sch, sc);
}

/// Regenerating tick t as three recordings: (step end + digit core, digit store, halve).
pub fn rec_regen_tick(
    b: &mut B,
    w: &Walk,
    t: usize,
    sch: &Sched,
    sc: &Scr,
) -> (Vec<G>, Vec<G>, Vec<G>) {
    b.begin();
    if t >= 3 {
        step_end_regen(b, w, t, sch, sc);
    }
    digit_core(b, w, t, sch, sc, regen_digit(w, t, sc));
    let p1 = b.end();
    b.begin();
    digit_store(b, w, sc);
    let p2 = b.end();
    b.begin();
    halve(b, w, t, sch, sc);
    finish_digits(b, w, t, sch, sc);
    let p3 = b.end();
    (p1, p2, p3)
}

/// The qubit holding tick t's digit in the regenerating tick: its ring lane of Q, or the tick's `a`.
pub(crate) fn regen_digit(w: &Walk, t: usize, sc: &Scr) -> QubitId {
    if lv("ringq") {
        w.qfr(t)[QB - 1]
    } else {
        sc.a
    }
}

/// Forward walk: init, ticks 1..=T, then the closing absorption step at T + 1 (every finished shot absorbed). Returns
/// the digit measurement bits m[t] (index t, m[0] unused).
pub fn walk_forward(b: &mut B, w: &Walk, sch: &Sched, sc: &Scr) -> Vec<BitId> {
    init(b, w);
    let m = b.fresh_bits(sch.t + 1);
    for t in 1..=sch.t {
        fwd_tick(b, w, t, sch, sc, m[t]);
    }
    close_fwd(b, w, sch, sc);
    m
}

/// The closing absorption step at T + 1 (forward).
pub fn close_fwd(b: &mut B, w: &Walk, sch: &Sched, sc: &Scr) {
    step_end_fwd(b, w, sch.t + 1, sch, sc);
}

/// The regenerating closing step (T + 1), recorded.
pub(crate) fn rec_regen_close(b: &mut B, w: &Walk, sch: &Sched, sc: &Scr) -> Vec<G> {
    b.begin();
    step_end_regen(b, w, sch.t + 1, sch, sc);
    b.end()
}

/// Inverse of walk_forward (Q, clean, must be allocated in `w.q`; it is |0> again afterwards): the regenerating
/// closing step and ticks played backwards, cancelling each digit measurement's phase.
pub fn walk_inverse(b: &mut B, w: &Walk, sch: &Sched, sc: &Scr, m: &[BitId]) {
    let ce = rec_regen_close(b, w, sch, sc);
    b.play(&ce, true);
    for t in (1..=sch.t).rev() {
        let (p1, p2, p3) = rec_regen_tick(b, w, t, sch, sc);
        b.play(&p3, true);
        b.play(&p2, true);
        b.z_if(regen_digit(w, t, sc), m[t]);
        b.play(&p1, true);
    }
    init(b, w);
}

/// After walk_forward every finished shot is absorbed: A = (0, 2^m) with m = T + 1 - (absorption tick) < 2^MB,
/// B = (-2s, C), j = +1. Rebuilds C_T = C 2^m (the cofactor the walk would have reached by doubling C up to T + 1, so
/// x'^-1 = (-1)^S C_T 2^-T with S = s ^ parity ^ 1 ^ [x was negated]) in R = B's cofactor lanes followed by lanes of
/// A, two's complement over RLEN lanes; m goes to `mr` (|0> before), A and j are cleared. `tm` = 1 + (MB - 1) clean
/// qubits (|0> again afterwards). Recorded; returns (R, key qubit holding s, recording).
pub fn unabsorb(
    b: &mut B,
    w: &Walk,
    sch: &Sched,
    mr: &[QubitId],
    tm: &[QubitId],
    dirty: &[QubitId],
) -> (Vec<QubitId>, QubitId, Vec<G>) {
    let t = sch.t + 1;
    let nm = 1usize << MB;
    let oh: Vec<QubitId> = (0..nm).map(|k| w.asig(t, k)).collect();
    let cl = sch.wb - sch.c[t];
    let mut r: Vec<QubitId> = (0..cl).map(|s| w.bsig(s)).collect();
    let ext: Vec<QubitId> = (0..RLEN - cl).map(|f| w.af(t, f)).collect();
    assert!(
        sch.wa - sch.c[t] - (RLEN - cl) >= nm,
        "one-hot lanes overlap the C_T extension"
    );
    r.extend(&ext);
    let sg = tm[0];
    b.begin();
    // m from the one-hot, then the one-hot becomes a thermometer oh[k] = [m >= k]
    for k in 0..nm {
        for i in 0..MB {
            if (k >> i) & 1 == 1 {
                b.cx(oh[k], mr[i]);
            }
        }
    }
    for k in (0..nm - 1).rev() {
        b.cx(oh[k + 1], oh[k]);
    }
    // sign-extend C over R, clear the m top lanes (they wrap to the bottom), rotate up by m
    b.cx(r[cl - 1], sg);
    for &q in &ext {
        b.cx(sg, q);
    }
    for k in 0..nm - 1 {
        b.ccx(sg, oh[k + 1], r[RLEN - 1 - k]);
    }
    for i in 0..MB {
        crot_up(b, mr[i], &r, 1 << i);
    }
    b.cx(r[RLEN - 1], sg);
    // thermometer back to the one-hot, erased against m
    for k in 0..nm - 1 {
        b.cx(oh[k + 1], oh[k]);
    }
    onehot_scan(b, mr, &tm[1..MB], 0, nm, 0, |b, v, ctrls| {
        mc_xor(b, ctrls, oh[v], &[], dirty);
    });
    let rec = b.end();
    b.play(&rec, false);
    (r, w.bf(1), rec)
}

/// z = y * C * 2^-tt mod p into a zero register z (relabeled in place by the halvings), C = two's complement value of
/// `c` (LSB first, top lane weighs -2^(M-1)), y in [0, p) restored. Bottom-up halving Horner over C's lanes, then
/// tt - M more halvings.
pub fn product_tail(
    b: &mut B,
    ms: &super::modp_frogdrop::Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
) {
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
