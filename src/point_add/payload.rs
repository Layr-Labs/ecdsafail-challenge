//! Payload division: dy -> lambda = dy / dx in place, carried by the frogdrop Euclid walk itself (no product
//! register). Per Euclid level j: e = floor(d / r_j); d -= e r_j; L += e t_j. At the end d = 0 and L = dy / dx.
//!
//! Payload register p[0..NP): d (bit i at p[i]) and W (two's complement, bit i at p[NP-1-i]), where
//! W = V - [j odd] and V = sigma_j L - |t_{j-1}| + |t_j| (offset form after agent sub700; the [j odd] shift makes
//! every digit erase a non-strict compare and every level transition W -> q|t_j| + ~W).
//! Between columns W lives in the "pre" region [NP-1-bl(t_j), NP) and d < r_{j-1} below it.
//!
//! Per stepping column (phase HR: r_j = Z in the ring bottom, |t_j| = Y in Q; HT: r_j = Y in Q, |t_j| = Z):
//!   digit (before P): restoring long division of d by r_j into e; W += e|t_j| erasing e bit by bit
//!     (W >= 2^k |t_j|); W sign-extended to the post region [bl(r_j), NP); complement of (bl(r_j), NP) = offset
//!     form of ~W.
//!   transition (while P holds q0): U += q0 |t_j|, U -= bq |t_j| (q = q0 - bq): W_{j+1} = q|t_j| + ~W_post.
//!   narrow (HR after the middle, HT at the next column start): offset form -> two's complement in the next pre
//!     region [NP-1-bl(t_{j+1}), NP).
//! Ring-bottom sources carry the ring-top value above every shot's 31-lane gap; that garbage only reaches target
//! positions far outside each shot's region, so writes there are suppressed by coarse masks (16-lane steps of a size
//! register). Comparisons read the carry per shot at the source lane just above the source's MSB.

use super::builder::B;
use super::frogdrop::Cut;
use super::mask::{ge_const, mc_xor, Dec};
use crate::circuit::QubitId;

thread_local! { pub static PCNT: std::cell::RefCell<[u64; 4]> = std::cell::RefCell::new([0; 4]); }
fn pcnt(i: usize, v: u64) { PCNT.with(|c| c.borrow_mut()[i] += v); }
pub const NP: usize = 259;
thread_local! { static LOAN_PEND: std::cell::RefCell<Option<(usize, usize)>> = std::cell::RefCell::new(None); }
thread_local! { static TCLEAN: std::cell::RefCell<(Vec<QubitId>, u32)> = std::cell::RefCell::new((vec![], 0)); }
/// s17 A11: clean wires + call-site id for the next trans_* ripples (set by the caller, cleared by `with_tclean`)
fn with_tclean<R>(clean: Vec<QubitId>, site: u32, f: impl FnOnce() -> R) -> R {
    TCLEAN.with(|c| *c.borrow_mut() = (clean, site));
    let r = f();
    TCLEAN.with(|c| *c.borrow_mut() = (vec![], 0));
    r
}

/// s6-cuts: cuts 1..7 are always ON (the FD_CUT1..FD_CUT7 environment switches were removed; default was ON).
pub fn cut(_n: usize) -> bool { true }
/// digit / quotient bits
pub const KD: usize = 26;
/// digit register lanes: every digit e_j <= q_j, and every quotient of a model-clean shot is below 2^QB (the
/// predicted q0 cap, the last level's q = R included)
pub const KE0: usize = super::pointadd_frogdrop::QB;
/// walk-bundle: digit register length override (WB_KE), default QB
pub fn ke() -> usize { 22 }
thread_local! { pub static KES: std::cell::Cell<usize> = std::cell::Cell::new(22); }
pub fn kes() -> usize { KES.with(|k| k.get()) }
thread_local! { pub static SKIPDIV: std::cell::Cell<bool> = std::cell::Cell::new(false); }
// s16 (B_top P2-F3): SPARE = a clean lane that is sa's ninth lane (None in wide-sz columns); HELD_SB = the loop in
// progress holds s = sz + sy in sb9 = sy ++ [SPARE] (sz untouched) instead of in sa
thread_local! { pub static SPARE: std::cell::Cell<Option<QubitId>> = std::cell::Cell::new(None); pub static HELD_SB: std::cell::Cell<bool> = std::cell::Cell::new(false); }
fn don(n: &str) -> bool { super::devsw_b::on(n) }
fn dbrk(n: &str) -> u32 { super::devsw_b::brk(n) }
/// sb9 = sy ++ [spare] when the sum can be held there
fn sb9_of(sc: &DigScr) -> Option<Vec<QubitId>> {
    let sp = SPARE.with(|c| c.get())?;
    if sc.sb.len() != 8 || sc.sa.len() != 9 || sc.sa[8] != sp { return None; }
    let mut v = sc.sb.clone();
    v.push(sp);
    Some(v)
}
/// sb9 += sa[..8] (undo: -=)
fn s_add_sb(b: &mut B, sc: &DigScr, undo: bool) {
    let sb9 = sb9_of(sc).unwrap();
    b.begin();
    super::frogdrop::reg_add_into(b, &sb9, &sc.sa[..8], &sc.zeros, sc.c0);
    let r = b.end();
    b.play(&r, undo);
}

/// lane of W's bit `pos`
#[inline]
pub fn wl(p: &[QubitId], pos: usize) -> QubitId {
    p[NP - 1 - pos]
}

/// Cuccaro ripple over (t, s) (equal length) with carry-in c0 (clean). `cmpl`: complement t around the passes
/// (subtract / compare form). After the up pass `mid(b)` runs: s[i] then holds the carry into lane i + 1. Down pass:
/// before lane i's cell gate(b, Some(i)) returns the write control (None = restore only); gate(b, None) at the end.
pub fn ripple(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, cmpl: bool, mid: &mut dyn FnMut(&mut B),
              gate: &mut dyn FnMut(&mut B, Option<usize>) -> Option<QubitId>) {
    ripple_c(b, t, s, c0, cmpl, mid, gate, &[], 0)
}

/// s17 A11: `clean` = wires proven |0> through the whole ripple (disjoint from t, s, c0 and from everything `mid` and
/// `gate` touch). Lane i < clean.len() keeps its Cuccaro carry on s[i] but computes x & t into clean[i] with a measured
/// AND (and_c: 1 Toffoli) and takes it back out of s[i] on the down pass with a free measured uncompute (and_u): the
/// two Cuccaro ccx of that lane (2 charged) become 1 charged. `site` names the call site (census markers, tallies).
pub fn ripple_c(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, cmpl: bool, mid: &mut dyn FnMut(&mut B),
                gate: &mut dyn FnMut(&mut B, Option<usize>) -> Option<QubitId>, clean: &[QubitId], site: u32) {
    assert_eq!(t.len(), s.len());
    let l = t.len();
    // the top lane is never laddered: with an empty `mid` and `gate` its two Cuccaro ccx are adjacent and the builder's
    // peephole already cancels them (cost 0), and the ladder would cost 1
    let nl = if super::devsw_c::lvl(11) >= 1 { clean.len().min(l.saturating_sub(1)) } else { 0 };
    let w = &clean[..nl];
    if nl > 0 {
        for (j, &q) in w.iter().enumerate() {
            assert!(!t.contains(&q) && !s.contains(&q) && q != c0 && !w[..j].contains(&q), "ripple_c: bad clean wire");
        }
        super::devsw_c::tally(site, nl as u64, l as u64);
    } else if clean.is_empty() && site != 0 {
        super::devsw_c::tally(site, 0, l as u64);
    }
    // numbered breakage of the clean-wire obligation: 1 = every ladder wire holds |1> around the block, 2 = only the
    // first one, 3 = only the second
    let brk = if nl > 0 { super::devsw_c::brk(11) } else { 0 };
    let hit = |j: usize| brk == 1 || (brk == 2 && j == 0) || (brk == 3 && j == 1);
    for (j, &q) in w.iter().enumerate() { if hit(j) { b.x(q); } }
    for &q in w { b.mark(q, 11000 + site); }
    if cmpl {
        for &q in t {
            b.x(q);
        }
    }
    for i in 0..l {
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        if i < nl {
            b.and_c(x, t[i], w[i]);
            b.cx(w[i], s[i]);
        } else {
            b.ccx(x, t[i], s[i]);
        }
    }
    mid(b);
    for i in (0..l).rev() {
        let x = if i == 0 { c0 } else { s[i - 1] };
        let g = gate(b, Some(i));
        if i < nl {
            b.cx(w[i], s[i]);
            b.and_u(x, t[i], w[i]);
        } else {
            b.ccx(x, t[i], s[i]);
        }
        b.cx(s[i], x);
        b.cx(s[i], t[i]);
        if let Some(gq) = g {
            b.cx(s[i], x);
            b.ccx(gq, x, t[i]);
            b.cx(s[i], x);
        }
    }
    gate(b, None);
    if cmpl {
        for &q in t {
            b.x(q);
        }
    }
    for &q in w { b.mark(q, 41000 + site); }
    for (j, &q) in w.iter().enumerate() { if hit(j) { b.x(q); } }
}


/// s17 A12: msb probe of v[lo..hi) into out (|0> on entry) by the priority probe on a clean bank (instead of the quadratic
/// `msb_probe_range` with its 8 decoder prefixes rebuilt per lane). `cands`: lanes that are |0> at BOTH ends of the probe
/// (forward and inverse play); `excl`: lanes live across it. Falls back to the old probe when off or no layout fits.
fn probe12(b: &mut B, v: &[QubitId], lo: usize, hi: usize, out: &[QubitId], cands: &[QubitId], excl: &[&[QubitId]],
           old: &dyn Fn(&mut B), site: u32) {
    let n = hi.saturating_sub(lo);
    if !super::devsw_c::on(12) || n == 0 {
        if n == 0 && super::devsw_c::on(12) { return; }
        return old(b);
    }
    let mut ex: Vec<&[QubitId]> = excl.to_vec();
    ex.push(v);
    ex.push(out);
    let bank = spare(cands, &ex);
    let Some(chunk) = super::priority_probe::choose(n, bank.len()) else { return old(b) };
    let used = super::priority_probe::need(n, chunk);
    super::devsw_c::tally(12000 + site, used as u64, n as u64);
    let brk = super::devsw_c::brk(12);
    if brk == 1 { b.x(bank[0]); }
    if brk == 2 { b.x(bank[used - 1]); }
    for &w in &bank[..used] { b.mark(w, 12000 + site); }
    super::priority_probe::emit(b, v, lo, hi, out, &bank);
    for &w in &bank[..used] { b.mark(w, 42000 + site); }
    if brk == 1 { b.x(bank[0]); }
    if brk == 2 { b.x(bank[used - 1]); }
}


/// s17 A15: extra clean AND temps for a Mask's toggles: a toggle is an mc_xor of `lits` literals and needs lits - 2 temps for an
/// all-and_c chain (1 Toffoli per literal) instead of the dirty Barenco tail; `have` temps are already given.
fn mask_extra(lits: usize, have: usize, avail: usize) -> usize {
    if !super::devsw_c::on(15) { return 0; }
    lits.saturating_sub(2).saturating_sub(have).min(avail)
}

/// candidates minus everything in `excl` (and duplicates), order kept
fn spare(cands: &[QubitId], excl: &[&[QubitId]]) -> Vec<QubitId> {
    let mut bad = vec![false; 4096];
    for e in excl { for q in e.iter() { bad[q.0 as usize] = true; } }
    let mut out: Vec<QubitId> = vec![];
    for &q in cands {
        if bad[q.0 as usize] { continue; }
        bad[q.0 as usize] = true;
        out.push(q);
    }
    out
}

/// Coarse write mask tracked on one qubit `g` during a ripple's down pass: g = AND(base) & allowed(i), where
/// allowed(i) = [a < lim(i)] (`below`) or [a >= lim(i)] (!below), a = value of `bits`, and lim(i) monotone so that
/// the allowed set only grows as i decreases. `amax` bounds a over every shot. Toggles are multi-controlled XORs of
/// base & [a == v].
pub struct Mask<'a> {
    pub bits: &'a [QubitId],
    pub amax: usize,
    pub below: bool,
    pub base: Vec<(QubitId, bool)>,
    pub g: QubitId,
    pub temps: &'a [QubitId],
    pub dirty: &'a [QubitId],
    cur: Option<isize>,
    /// s6-cuts: smallest value `a` can take on a shot where the mask matters; skip_empty: report an empty allowed set
    pub amin: usize,
    pub skip_empty: bool,
}

impl<'a> Mask<'a> {
    pub fn new(bits: &'a [QubitId], amax: usize, below: bool, base: Vec<(QubitId, bool)>, g: QubitId,
               temps: &'a [QubitId], dirty: &'a [QubitId]) -> Mask<'a> {
        Mask { bits, amax, below, base, g, temps, dirty, cur: None, amin: 0, skip_empty: false }
    }
    pub fn with_cut(mut self, amin: usize, skip_empty: bool) -> Mask<'a> {
        self.amin = amin;
        self.skip_empty = skip_empty;
        self
    }
    /// the write control to hand to the ripple after `goto(Some(..))`: None when g is statically |0>
    pub fn ctl(&self) -> Option<QubitId> {
        if self.skip_empty {
            let (lo, hi) = self.cur.map(|l| self.set(l)).unwrap_or((1, 0));
            if lo > hi { return None; }
        }
        Some(self.g)
    }
    fn toggle(&self, b: &mut B, v: usize) {
        if v >= (1usize << self.bits.len()) {
            return;
        }
        let mut lits = self.base.clone();
        for (i, &q) in self.bits.iter().enumerate() {
            lits.push((q, (v >> i) & 1 == 0));
        }
        mc_xor(b, &lits, self.g, self.temps, self.dirty);
    }
    /// allowed values for limit `lim`: the v in [0, amax] with v < lim (below) or v >= lim
    fn set(&self, lim: isize) -> (usize, usize) {
        let am = self.amax as isize;
        let an = self.amin as isize;
        let (lo, hi) = if self.below { (an, (lim - 1).min(am)) } else { (lim.max(an), am) };
        if lo > hi { (1, 0) } else { (lo as usize, hi as usize) }
    }
    /// move g to limit `lim` (None: clear)
    pub fn goto(&mut self, b: &mut B, lim: Option<isize>) {
        let mg0 = b.tof;
        let old = self.cur.map(|l| self.set(l)).unwrap_or((1, 0));
        let new = lim.map(|l| self.set(l)).unwrap_or((1, 0));
        // toggle the symmetric difference of the two value intervals
        let inr = |r: (usize, usize), v: usize| r.0 <= r.1 && v >= r.0 && v <= r.1;
        for v in 0..=self.amax {
            if inr(old, v) != inr(new, v) {
                self.toggle(b, v);
            }
        }
        self.cur = lim;
        pcnt(1, b.tof - mg0);
    }
}

/// target ^= AND(extra) & (lane(v) ^ neg) for the shot's value v of `reg` in [lo, hi] (lane(v) = None: skip).
/// Full decoder prefixes `pre` (>= reg.len() - 1), temps for the AND.
pub fn read_lane(b: &mut B, reg: &[QubitId], lo: usize, hi: usize, lane: &dyn Fn(usize) -> Option<QubitId>, neg: bool,
                 extra: &[(QubitId, bool)], target: QubitId, pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) {
    read_lane_x(b, reg, lo, hi, lane, neg, extra, target, pre, temps, dirty, &[])
}

/// number of extra clean wires `read_lane_x` wants beyond the bank `pre_len` to fold `ne` literals into its decoder
pub fn read_lane_need(reg_len: usize, ne: usize, pre_len: usize) -> usize {
    if ne == 0 || ne > 2 || !super::devsw_c::on(10) { return 0; }
    (reg_len + ne - 1).saturating_sub(pre_len)
}

/// s17 A10: read_lane with the `extra` literals folded into the decoder as extra top bits of the register (match value
/// fixed by their polarity): the decoder then holds reg.len() + extra.len() - 1 prefix levels (`pre` plus `spare`, which must
/// be |0> through the call) and every lane is ONE ccx (prefix, lane qubit -> target) instead of a 2-3 Toffoli and_c chain.
/// Falls back to the plain form when `pre` + `spare` is too short.
pub fn read_lane_x(b: &mut B, reg: &[QubitId], lo: usize, hi: usize, lane: &dyn Fn(usize) -> Option<QubitId>, neg: bool,
                   extra: &[(QubitId, bool)], target: QubitId, pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId],
                   spare: &[QubitId]) {
    let rl0 = b.tof;
    let ne = extra.len();
    let need = (reg.len() + ne).saturating_sub(1);
    let ext_ok = ne > 0 && ne <= 2 && super::devsw_c::on(10) && pre.len() + spare.len() >= need
        && extra.iter().all(|l| !reg.contains(&l.0) && l.0 != target);
    if ext_ok {
        let mut ext: Vec<QubitId> = reg.to_vec();
        let mut ebits = 0usize;
        for (i, l) in extra.iter().enumerate() {
            ext.push(l.0);
            if !l.1 { ebits |= 1 << i; } // (q, false) = q must be 1: bit 1; (q, true) = q must be 0: bit 0
        }
        let mut pre_e: Vec<QubitId> = pre.to_vec();
        pre_e.extend_from_slice(spare);
        // wires the base decoder did not use: everything past its own reg.len()-1 prefix levels (bank wires the base never touched
        // count too: the census must show them |0>)
        let borrowed: Vec<QubitId> = pre_e[pre.len().min(reg.len().saturating_sub(1)).min(need)..need].to_vec();
        let brk = super::devsw_c::brk(10);
        if brk == 1 { for &w in &borrowed { b.x(w); } }
        for &w in &borrowed { b.mark(w, 10000 + ne as u32); }
        let mut dec = Dec::new(&ext, &pre_e);
        for v in lo..=hi {
            if v >= (1usize << reg.len()) {
                break;
            }
            if let Some(q) = lane(v) {
                let mut c = dec.ctrls(b, v | (ebits << reg.len()));
                c.push((q, neg));
                mc_xor(b, &c, target, temps, dirty);
            }
        }
        dec.clear(b);
        for &w in &borrowed { b.mark(w, 40000 + ne as u32); }
        if brk == 1 { for &w in &borrowed { b.x(w); } }
        pcnt(0, b.tof - rl0);
        return;
    }
    let mut dec = Dec::new(reg, pre);
    for v in lo..=hi {
        if v >= (1usize << reg.len()) {
            break;
        }
        if let Some(q) = lane(v) {
            let mut c = dec.ctrls(b, v);
            c.push((q, neg));
            c.extend_from_slice(extra);
            mc_xor(b, &c, target, temps, dirty);
        }
    }
    dec.clear(b);
    pcnt(0, b.tof - rl0);
}

/// Walk lanes l in [lo, hi) with f1 = [l < c1] and f2 = [l < c2] live (cuts any value; comparators clean up),
/// per(b, l) runs per lane. f1, f2 clean before and after. pre1 / pre2 >= register lengths (decoders + chains).
pub fn walk2(b: &mut B, c1: &Cut, c2: &Cut, lo: usize, hi: usize, f1: QubitId, f2: QubitId, pre1: &[QubitId],
             pre2: &[QubitId], tmp: QubitId, dirty: &[QubitId], per: &mut dyn FnMut(&mut B, usize)) {
    walk2x(b, c1, c2, lo, hi, hi, lo, f1, f2, pre1, pre2, tmp, dirty, per)
}

/// walk2 with s6-cut 6 bounds: f1 is live only on lanes [lo, hi1) (c1 never exceeds hi1 - 1 on a shot of the
/// envelope, so [l < c1] = 0 and the (f1, true) control is true for l >= hi1), f2 only on lanes [lo2, hi) (c2 >= lo2,
/// so [l < c2] = 1 below lo2). `per` must drop the dead literal itself (l >= hi1: no f1; l < lo2: no f2).
/// hi1 = hi, lo2 = lo reproduces walk2 gate for gate.
pub fn walk2x(b: &mut B, c1: &Cut, c2: &Cut, lo: usize, hi: usize, hi1: usize, lo2: usize, f1: QubitId, f2: QubitId,
              pre1: &[QubitId], pre2: &[QubitId], tmp: QubitId, dirty: &[QubitId], per: &mut dyn FnMut(&mut B, usize)) {
    if lo >= hi {
        return;
    }
    let hi1 = hi1.min(hi).max(lo + 1);
    let lo2 = lo2.max(lo).min(hi - 1);
    let ch: Vec<QubitId> = pre1.iter().chain(pre2.iter()).copied().collect();
    c1.ge(b, lo as isize + 1, f1, &ch);
    c2.ge(b, lo2 as isize + 1, f2, &ch);
    let mut d1 = Dec::new(&c1.v, pre1);
    let mut d2 = Dec::new(&c2.v, pre2);
    for l in lo..hi {
        if l > lo && l < hi1 {
            if let Some(v) = c1.val_at(l as isize) {
                let c = d1.ctrls(b, v);
                mc_xor(b, &c, f1, &[tmp], dirty);
            }
        }
        if l > lo2 {
            if let Some(v) = c2.val_at(l as isize) {
                let c = d2.ctrls(b, v);
                mc_xor(b, &c, f2, &[tmp], dirty);
            }
        }
        per(b, l);
    }
    d1.clear(b);
    d2.clear(b);
    c1.ge(b, hi1 as isize, f1, &ch);
    c2.ge(b, hi as isize, f2, &ch);
}

/// D1 C9c: t ^= sv & [v >= k] (`ge_const` with its final CX turned into a CCX with sv)
fn ge_const_and(b: &mut B, v: &[QubitId], k: isize, sv: QubitId, t: QubitId, chain: &[QubitId]) {
    let n = v.len();
    if k <= 0 {
        b.cx(sv, t);
        return;
    }
    if k >= (1isize << n) {
        return;
    }
    #[derive(Clone, Copy)]
    enum C { K(bool), Q(QubitId, bool) }
    let addend = (1usize << n) - k as usize;
    b.begin();
    let mut c = C::K(false);
    let mut used = 0usize;
    for i in 0..n {
        let a = (addend >> i) & 1 == 1;
        let vi = C::Q(v[i], false);
        c = match (a, c) {
            (true, C::K(true)) => C::K(true),
            (true, C::K(false)) => vi,
            (false, C::K(true)) => vi,
            (false, C::K(false)) => C::K(false),
            (_, C::Q(q, ng)) => {
                let out = chain[used];
                used += 1;
                let (nv, nc) = if a { (true, !ng) } else { (false, ng) };
                if nv { b.x(v[i]); }
                if nc { b.x(q); }
                b.and_c(v[i], q, out);
                if nc { b.x(q); }
                if nv { b.x(v[i]); }
                C::Q(out, a)
            }
        };
    }
    let rec = b.end();
    b.play(&rec, false);
    match c {
        C::K(true) => b.cx(sv, t),
        C::K(false) => {}
        C::Q(q, ng) => {
            b.ccx(sv, q, t);
            if ng {
                b.cx(sv, t);
            }
        }
    }
    b.play(&rec, true);
}

/// `Cut::ge` gated by sv: t ^= sv & [cut >= k]
fn cut_ge_and(c: &Cut, b: &mut B, k: isize, sv: QubitId, t: QubitId, chain: &[QubitId]) {
    if c.neg {
        ge_const_and(b, &c.v, c.a - k + 1, sv, t, chain);
        b.cx(sv, t);
    } else {
        ge_const_and(b, &c.v, k - c.a, sv, t, chain);
    }
}

/// D1 C9c: `walk2x` with f2 held as sv & [l < c2] (sv constant through the walk): the toggles of f2 fold sv in as an extra top
/// bit of c2's decoder (needs pre2.len() >= c2.v.len()), the comparators are AND-gated by sv, and `per` then takes lanes
/// l >= lo2 without the sv literal. f1 is untouched, f2 is clean (0) before and after on every shot, as for walk2x.
pub fn walk2x_sv(b: &mut B, c1: &Cut, c2: &Cut, lo: usize, hi: usize, hi1: usize, lo2: usize, f1: QubitId, f2: QubitId,
                 sv: QubitId, pre1: &[QubitId], pre2: &[QubitId], tmp: QubitId, dirty: &[QubitId],
                 per: &mut dyn FnMut(&mut B, usize)) {
    if lo >= hi {
        return;
    }
    let hi1 = hi1.min(hi).max(lo + 1);
    let lo2 = lo2.max(lo).min(hi - 1);
    let ch: Vec<QubitId> = pre1.iter().chain(pre2.iter()).copied().collect();
    let brk = super::devsw_d1::brk(10);
    c1.ge(b, lo as isize + 1, f1, &ch);
    if brk == 1 { c2.ge(b, lo2 as isize + 1, f2, &ch); } else { cut_ge_and(c2, b, lo2 as isize + 1, sv, f2, &ch); }
    let mut ext2: Vec<QubitId> = c2.v.clone();
    ext2.push(sv);
    let mut d1 = Dec::new(&c1.v, pre1);
    let mut d2 = Dec::new(&ext2, pre2);
    for l in lo..hi {
        if l > lo && l < hi1 {
            if let Some(v) = c1.val_at(l as isize) {
                let c = d1.ctrls(b, v);
                mc_xor(b, &c, f1, &[tmp], dirty);
            }
        }
        if l > lo2 {
            if let Some(v) = c2.val_at(l as isize) {
                let c = d2.ctrls(b, v | if brk == 2 { 0 } else { 1usize << c2.v.len() });
                mc_xor(b, &c, f2, &[tmp], dirty);
            }
        }
        per(b, l);
    }
    d1.clear(b);
    d2.clear(b);
    c1.ge(b, hi1 as isize, f1, &ch);
    if brk == 1 { c2.ge(b, hi as isize, f2, &ch); } else { cut_ge_and(c2, b, hi as isize, sv, f2, &ch); }
}

/// One phase's view of a column for the payload.
pub struct Ph {
    pub ht: bool,
    /// bl(r_j) register and range
    pub rv: Vec<QubitId>,
    pub rr: (usize, usize),
    /// bl(t_j) register and range
    pub tv: Vec<QubitId>,
    pub tr: (usize, usize),
    /// divisor r_j lanes (LSB first) and |t_j| lanes, each long enough for every window (zero-padded)
    pub src_r: Vec<QubitId>,
    pub src_t: Vec<QubitId>,
}

/// Scratch of the digit stage (all |0> on entry and exit).
pub struct DigScr {
    pub e: Vec<QubitId>,
    /// s = bl(r) + bl(t) = sz + sy is formed in place (sa += sb) around each size gate
    pub sa: Vec<QubitId>,
    pub sb: Vec<QubitId>,
    pub sv: QubitId,
    pub fa: QubitId,
    pub g: QubitId,
    pub c0: QubitId,
    pub tmp: Vec<QubitId>,
    pub pre1: Vec<QubitId>,
    pub pre2: Vec<QubitId>,
    pub zeros: Vec<QubitId>,
    /// borrowed lanes for the size gates' comparator when its clean chain is short
    pub dirty: Vec<QubitId>,
    /// s17: further lanes that are |0> throughout the digit stage (pool lanes past the two decoder banks, loan-bank lanes of Q);
    /// only the A11 carry ladder uses them
    pub more: Vec<QubitId>,
}

/// fa = act & [s <= lim] (s register value range sr); returns the control to use (act itself when always true) and
/// whether a flag was computed. None: never true. `extra`: lanes clean at this step beyond the scratch's own.
fn gate_le(b: &mut B, sc: &DigScr, act: QubitId, sr: (usize, usize), lim: isize, extra: &[QubitId])
           -> Option<(QubitId, bool)> {
    gate_le_h(b, sc, act, sr, lim, extra, false)
}
/// `hold`: sa already holds s = sz + sy (s6-cut 2: the caller's loop brackets the in-place add once)
fn gate_le_h(b: &mut B, sc: &DigScr, act: QubitId, sr: (usize, usize), lim: isize, extra: &[QubitId], hold: bool)
           -> Option<(QubitId, bool)> {
    let g0 = b.tof;
    let r = gate_le_i(b, sc, act, sr, lim, extra, hold);
    pcnt(2, b.tof - g0);
    r
}
fn gate_le_i(b: &mut B, sc: &DigScr, act: QubitId, sr: (usize, usize), lim: isize, extra: &[QubitId], hold: bool)
             -> Option<(QubitId, bool)> {
    if (sr.0 as isize) > lim {
        return None;
    }
    if (sr.1 as isize) <= lim {
        return Some((act, false));
    }
    // c = [s >= lim + 1] on tmp[1]; fa = act & !c
    let chain = gate_chain(sc, extra);
    if !hold { s_add(b, sc, false); }
    if super::devsw_c::on(19) && { let (r19, k19) = gate_operand(sc, lim + 1); super::mask::ge_const_need(r19.len(), k19) <= chain.len() } {
        // s17 A19: build the comparator's carry chain once, use its top wire as the control of fa = act & !c, erase the chain
        // for free (the base computes the whole chain twice around one and_c)
        gate_fa_hold(b, sc, act, lim + 1, &chain, false);
    } else {
        gate_cmp(b, sc, lim + 1, &chain);
        b.x(sc.tmp[1]);
        b.and_c(act, sc.tmp[1], sc.fa);
        b.x(sc.tmp[1]);
        gate_cmp(b, sc, lim + 1, &chain);
    }
    if !hold { s_add(b, sc, true); }
    Some((sc.fa, true))
}

fn gate_le_undo(b: &mut B, sc: &DigScr, act: QubitId, lim: isize, extra: &[QubitId]) {
    gate_le_undo_h(b, sc, act, lim, extra, false)
}
fn gate_le_undo_h(b: &mut B, sc: &DigScr, act: QubitId, lim: isize, extra: &[QubitId], hold: bool) {
    let g0 = b.tof;
    gate_le_undo_i(b, sc, act, lim, extra, hold);
    pcnt(2, b.tof - g0);
}
fn gate_le_undo_i(b: &mut B, sc: &DigScr, act: QubitId, lim: isize, extra: &[QubitId], hold: bool) {
    let chain = gate_chain(sc, extra);
    if !hold { s_add(b, sc, false); }
    if super::devsw_c::on(19) && { let (r19, k19) = gate_operand(sc, lim + 1); super::mask::ge_const_need(r19.len(), k19) <= chain.len() } {
        gate_fa_hold(b, sc, act, lim + 1, &chain, true);
    } else {
        gate_cmp(b, sc, lim + 1, &chain);
        b.x(sc.tmp[1]);
        b.and_u(act, sc.tmp[1], sc.fa);
        b.x(sc.tmp[1]);
        gate_cmp(b, sc, lim + 1, &chain);
    }
    if !hold { s_add(b, sc, true); }
}

/// s17 A19: fa ^= act & ![sa >= k] (compute, or uncompute by measurement when `undo`) with the comparator chain held only while
/// fa's AND is formed. All chain wires are |0> before and after.
fn gate_fa_hold(b: &mut B, sc: &DigScr, act: QubitId, k: isize, chain: &[QubitId], undo: bool) {
    use super::mask::GeLit;
    let (reg19, k19) = gate_operand(sc, k);
    let (rec, lit) = super::mask::ge_const_hold(b, &reg19, k19, chain);
    b.play(&rec, false);
    // wanted control: [sa < k] = !c
    match lit {
        GeLit::K(true) => {}            // c = 1: fa = 0, nothing to do
        GeLit::K(false) => b.cx(act, sc.fa), // c = 0: fa = act (a CX is its own inverse)
        GeLit::Q(q, ng) => {
            // c = q ^ ng, !c = q ^ !ng: a literal "q == ng"
            if !ng { b.x(q); }
            if undo { b.and_u(act, q, sc.fa); } else { b.and_c(act, q, sc.fa); }
            if !ng { b.x(q); }
        }
    }
    b.play(&rec, true);
}

/// s16 P2-F3 part C: s lies in [224, 258] (documented envelope 228..257), so a 9-bit s equals a 6-bit value
/// u = s mod 32 + 32 * bit8 - the bits 5..7 are all one for s in [224, 255] and zero for s in [256, 258].
/// Returns the narrowed (register, constant) of the comparison [reg >= k], or None when P2F3D does not apply.
/// BREAK 1: the 5-bit slice also in columns with kes() == ke(); BREAK 2: the 6-bit slice's constant off by one;
/// BREAK 3: the 6-bit slice loses bit 4. (s20: moved out of gate_cmp unchanged.)
fn p2f3d_operand(reg: &[QubitId], k: isize) -> Option<(Vec<QubitId>, isize)> {
    if don("P2F3D") && reg.len() == 9 {
        let brk = dbrk("P2F3D");
        if (kes() < ke() || brk == 1) && (241..=258).contains(&k) {
            return Some((vec![reg[0], reg[1], reg[2], reg[3], reg[8]], k - 240));
        }
        if (225..=258).contains(&k) {
            if brk == 3 {
                return Some((vec![reg[0], reg[1], reg[2], reg[3], reg[8]], (k - 224).min(31)));
            }
            return Some((vec![reg[0], reg[1], reg[2], reg[3], reg[4], reg[8]], if brk == 2 { k - 223 } else { k - 224 }));
        }
    }
    None
}
/// the register gate_cmp compares: s lives in sb9 while the P2-F3 hold is on, else in sa
fn gate_reg(sc: &DigScr) -> Vec<QubitId> { if HELD_SB.with(|c| c.get()) { sb9_of(sc).unwrap() } else { sc.sa.clone() } }
/// the (register, constant) a comparison [s >= k] actually reads (s20 merge of s16 P2F3A/D with s17 A19)
fn gate_operand(sc: &DigScr, k: isize) -> (Vec<QubitId>, isize) {
    let reg = gate_reg(sc);
    p2f3d_operand(&reg, k).unwrap_or((reg, k))
}

/// tmp[1] ^= [sa >= k]: the carry-chain comparator when the chain holds its carries, else the exact compact
/// comparator (clean temps = chain, borrowed dirty lanes)
fn gate_cmp(b: &mut B, sc: &DigScr, k: isize, chain: &[QubitId]) {
    let reg: Vec<QubitId> = gate_reg(sc);
    // s16 P2-F3 part C (factored into p2f3d_operand by s20 so that s17 A19's gate_fa_hold uses the same operand)
    if let Some((r, kk)) = p2f3d_operand(&reg, k) {
        ge_const(b, &r, kk, sc.tmp[1], chain);
        return;
    }
    if super::mask::ge_const_need(reg.len(), k) <= chain.len() {
        ge_const(b, &reg, k, sc.tmp[1], chain);
    } else {
        super::frogdrop_col::ge_const_compact(b, &reg, k, sc.tmp[1], chain, &sc.dirty);
    }
}

/// does gate_le_i with these arguments compute the flag (rather than return a constant)?
fn gate_made(sr: (usize, usize), lim: isize) -> bool {
    !((sr.0 as isize) > lim) && !((sr.1 as isize) <= lim)
}

/// carries of the size gate's comparator: both decoder banks, tmp[0], and the zero pad, c0 and g (idle while a
/// comparator runs between the in-place adds), then the step's `extra` clean lanes
fn gate_chain(sc: &DigScr, extra: &[QubitId]) -> Vec<QubitId> {
    let mut chain = sc.pre2.clone();
    chain.push(sc.tmp[0]);
    chain.extend_from_slice(&sc.pre1);
    chain.extend_from_slice(&sc.zeros);
    chain.extend([sc.c0, sc.g]);
    for &x in extra {
        if !chain.contains(&x) {
            chain.push(x);
        }
    }
    chain
}

/// sa += sb (undo: -=): the digit's s = sz + sy in the sz register while a size gate is formed
fn s_add(b: &mut B, sc: &DigScr, undo: bool) {
    b.begin();
    super::frogdrop::reg_add_into(b, &sc.sa, &sc.sb, &sc.zeros, sc.c0);
    let r = b.end();
    b.play(&r, undo);
}

/// The digit stage of one phase (stage 2.5: after the middle swap, before P). `act` = this phase's stepping flag.
/// `top_bits`: (register slice, max value) of the coarse mask register for the ring-sourced writes.
pub fn digit(b: &mut B, p: &[QubitId], ph: &Ph, act: QubitId, sc: &DigScr, dirty: &[QubitId]) {
    let (rlo, rhi) = ph.rr;
    let (tlo, thi) = ph.tr;
    let mtmp = &sc.tmp[..];
    // s = bl(r) + bl(t) (formed in place by the size gates)
    // s16 P2-F3 part B: bl(r) + bl(t) <= 257 on every shot of the envelope (BREAK 1: 256)
    let scap = if don("P2F3C") { if dbrk("P2F3C") == 1 { 256 } else { 257 } } else { usize::MAX };
    let srange = (rlo + tlo, (rhi + thi).min(scap));
    let pt0 = b.tof;
    let mut ptk = [0u64; 6];
    // ---- long division: e_k = [d >= 2^k r_j] with d < 2^(k+1) r_j; window positions [k, k + bl(r) + 1)
    // s6-cut 2: HT's D reads neither sz (= sa) nor writes sy (= sb): hold s = sz + sy over the whole loop
    let hold_d = cut(2) && ph.ht && (0..kes()).any(|k| gate_made(srange, 257 - k as isize));
    if hold_d { s_add(b, sc, false); }
    for k in (0..kes()).rev() {
        if SKIPDIV.with(|x| x.get()) { break; }
        // clean at this step: e[0..k] (not yet written) and sv (formed after the division)
        let mut lde = vec![sc.sv];
        lde.extend_from_slice(&sc.e[0..k]);
        let Some((fa, made)) = gate_le_h(b, sc, act, srange, 257 - k as isize, &lde, hold_d) else { continue };
        let top = (k + rhi + 1).min(NP);
        let t: Vec<QubitId> = (k..top).map(|i| p[i]).collect();
        let s: Vec<QubitId> = ph.src_r[..top - k].to_vec();
        let ek = sc.e[k];
        let rv = ph.rv.clone();
        let src = s.clone();
        // e[0..k] are still clean: from k = 8 on they are the decoder bank (below: topped up with sv, g and e[0..k];
        // g is the HR mask flag, clean until the down pass)
        let mut ldb = vec![sc.sv, sc.g];
        ldb.extend_from_slice(&sc.e[0..k]);
        let bank: &[QubitId] = &if k >= 8 { sc.e[0..8].to_vec() } else { bank_of(&sc.pre1, &ldb) };
        // s17 A11: clean wires through this ripple: e[0..k] and e[kes..], sv (formed after the division), pre1/pre2 and
        // the zero pad (all outside the decoder bank / read_lane temps / the HR mask flag g), sc.fa when the size gate
        // returned a constant. Provenance: DigScr doc ("all |0> on entry and exit") and the step-k notes above.
        let mut cd: Vec<QubitId> = sc.e[0..k].to_vec();
        cd.extend_from_slice(&sc.e[kes()..]);
        cd.push(sc.sv);
        cd.extend_from_slice(&sc.pre1);
        cd.extend_from_slice(&sc.pre2);
        cd.extend_from_slice(&sc.zeros);
        if ph.ht { cd.push(sc.g); }
        if !made { cd.push(sc.fa); }
        if super::devsw_c::lvl(11) >= 2 { cd.extend_from_slice(&sc.more); }
        let fav = [fa];
        let cl_all = spare(&cd, &[&t, &s, bank, mtmp, &[sc.c0, ek, act], &fav[..usize::from(made)], &[sc.g][..usize::from(!ph.ht)], dirty, &sc.sa, &sc.sb]);
        // s17 A10: the first wires of the spare list go to read_lane's decoder (it folds `fa` into the prefix chain); the rest
        // is the A11 ladder
        let nr = read_lane_need(rv.len(), 1, bank.len()).min(cl_all.len());
        let (rl_sp, cl) = (cl_all[..nr].to_vec(), cl_all[nr..].to_vec());
        let mut mid = |b: &mut B| {
            let lane = |v: usize| if v < src.len() { Some(src[v]) } else { None };
            read_lane_x(b, &rv, rlo, rhi, &lane, true, &[(fa, false)], ek, bank, mtmp, dirty, &rl_sp);
        };
        if ph.ht {
            let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| ek);
            ripple_c(b, &t, &s, sc.c0, true, &mut mid, &mut gate, &cl, 1);
        } else {
            // HR: ring-sourced divisor; writes allowed at d positions P < 266 - 16 (bl(t) >> 4)
            let bits = &ph.tv[4..];
            // s17 A15: the next spare wires are extra AND temps of the mask toggles
            let nm = mask_extra(1 + bits.len(), 1, cl.len());
            let mut mk_t: Vec<QubitId> = vec![mtmp[0]];
            mk_t.extend_from_slice(&cl[..nm]);
            let cl = cl[nm..].to_vec();
            let brk15 = matches!(super::devsw_c::brk(15), 1 | 9) && nm > 0;
            if brk15 { b.x(mk_t[1]); }
            for &w in &mk_t[1..] { b.mark(w, 15001); }
            let mut mk = Mask::new(bits, thi >> 4, true, vec![(ek, false)], sc.g, &mk_t, dirty)
                .with_cut(if cut(1) { tlo >> 4 } else { 0 }, cut(1));
            let mut gate = |b: &mut B, i: Option<usize>| match i {
                Some(i) => {
                    let pos = (k + i) as isize;
                    mk.goto(b, Some((265 - pos).div_euclid(16) + 1));
                    mk.ctl()
                }
                None => {
                    mk.goto(b, None);
                    None
                }
            };
            ripple_c(b, &t, &s, sc.c0, true, &mut mid, &mut gate, &cl, 2);
            for &w in &mk_t[1..] { b.mark(w, 45001); }
            if brk15 { b.x(mk_t[1]); }
        }
        if made {
            gate_le_undo_h(b, sc, act, 257 - k as isize, &lde, hold_d);
        }
    }
    if hold_d { s_add(b, sc, true); }
    ptk[0] = b.tof - pt0;
    // ---- sv = sign of W (lane of bit bl(t))
    {
        let lane = |v: usize| if v <= NP - 1 { Some(p[NP - 1 - v]) } else { None };
        let bank = bank_of(&sc.pre1, &[sc.fa, sc.g, sc.c0, sc.zeros[0]]);
        // s17 A10: spare decoder wires (pre2, more, e[kes..])
        // (e[0..kes] holds the digits here and is NOT clean; e[kes..] was never written)
        let mut cd: Vec<QubitId> = sc.pre2.clone();
        cd.extend_from_slice(&sc.e[kes()..]);
        cd.extend_from_slice(&sc.more);
        let rl_sp = spare(&cd, &[&bank, mtmp, &[sc.sv, act, sc.c0], dirty, &sc.sa, &sc.sb, &ph.tv, &ph.rv]);
        read_lane_x(b, &ph.tv, tlo, thi, &lane, false, &[(act, false)], sc.sv, &bank, mtmp, dirty, &rl_sp);
    }
    ptk[1] = b.tof - pt0;
    // ---- D^-1: W += e_k 2^k |t|; e_k ^= act & !sv & [s <= 258 - k] & [W >= 2^k |t|]
    // s6-cut 2: HR's D^-1 reads neither sz (= sa) nor writes sy (= sb): hold s = sz + sy over the whole loop
    // s16 P2-F3 part A: HT's D^-1 reads sz (tv) but not sy: hold s in sb9 = sy ++ [spare] (sb += sz) instead
    let hold_sb = ph.ht && don("P2F3A") && sb9_of(sc).is_some();
    // BREAK 1: HT holds in sa like HR (sz is read inside the loop)
    let hold_sa_ht = ph.ht && don("P2F3A") && dbrk("P2F3A") == 1;
    let hold_i = cut(2) && (!ph.ht || hold_sb || hold_sa_ht) && (0..kes()).any(|k| {
        let top = (k + thi + 1).min(NP);
        top > k && gate_made(srange, 258 - k as isize)
    });
    let use_sb = hold_i && hold_sb && !hold_sa_ht;
    if hold_i { if use_sb { HELD_SB.with(|c| c.set(true)); s_add_sb(b, sc, false); } else { s_add(b, sc, false); } }
    for k in 0..kes() {
        let top = (k + thi + 1).min(NP);
        if top <= k {
            break;
        }
        let t: Vec<QubitId> = (k..top).map(|pos| wl(p, pos)).collect();
        let s: Vec<QubitId> = ph.src_t[..top - k].to_vec();
        let ek = sc.e[k];
        // add (writes gated by e_k; HT ring source masked: allowed positions P < k + 24 + 16 (bl(t) >> 4))
        {
            let mut mid = |_b: &mut B| {};
            // s17 A11: clean through the add: e[0..k] (erased already) and e[kes..], pre1/pre2/zeros, fa and tmp[1] (the
            // previous step's size gate was undone), g unless HT's mask flag; sv holds the sign, e[k] is the write control
            let mut cd: Vec<QubitId> = sc.e[0..k].to_vec();
            cd.extend_from_slice(&sc.e[kes()..]);
            cd.extend_from_slice(&sc.pre1);
            cd.extend_from_slice(&sc.pre2);
            cd.extend_from_slice(&sc.zeros);
            cd.push(sc.fa);
            cd.push(sc.tmp[1]);
            if !ph.ht { cd.push(sc.g); }
            if super::devsw_c::lvl(11) >= 2 { cd.extend_from_slice(&sc.more); }
            let cl = spare(&cd, &[&t, &s, &[sc.c0, ek, sc.sv, act], &mtmp[..1], &[sc.g][..usize::from(ph.ht)], dirty, &sc.sa, &sc.sb]);
            if ph.ht {
                let bits = &ph.tv[4..];
                // s17 A15: the first spare wires are extra AND temps of the mask toggles
                let nm = mask_extra(1 + bits.len(), 1, cl.len());
                let mut mk_t: Vec<QubitId> = vec![mtmp[0]];
                mk_t.extend_from_slice(&cl[..nm]);
                let cl = cl[nm..].to_vec();
                let brk15 = matches!(super::devsw_c::brk(15), 2 | 9) && nm > 0;
                if brk15 { b.x(mk_t[1]); }
                for &w in &mk_t[1..] { b.mark(w, 15002); }
                let mut mk = Mask::new(bits, thi >> 4, false, vec![(ek, false)], sc.g, &mk_t, dirty)
                    .with_cut(if cut(1) { tlo >> 4 } else { 0 }, cut(1));
                let mut gate = |b: &mut B, i: Option<usize>| match i {
                    Some(i) => {
                        let pos = (k + i) as isize;
                        let x = pos - k as isize - 24;
                        mk.goto(b, Some(if x < 0 { 0 } else { x.div_euclid(16) + 1 }));
                        mk.ctl()
                    }
                    None => {
                        mk.goto(b, None);
                        None
                    }
                };
                ripple_c(b, &t, &s, sc.c0, false, &mut mid, &mut gate, &cl, 3);
                for &w in &mk_t[1..] { b.mark(w, 45002); }
                if brk15 { b.x(mk_t[1]); }
            } else {
                let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| ek);
                ripple_c(b, &t, &s, sc.c0, false, &mut mid, &mut gate, &cl, 4);
            }
        }
        // compare-erase
        let Some((fa, made)) = gate_le_h(b, sc, act, srange, 258 - k as isize, &sc.e[0..k], hold_i) else { continue };
        {
            let tv = ph.tv.clone();
            let src = s.clone();
            // e[0..k] are erased already: from k = 8 on they are the decoder bank (below: topped up with g and
            // e[0..k])
            let mut deb = vec![sc.g];
            deb.extend_from_slice(&sc.e[0..k]);
            let bank: &[QubitId] = &if k >= 8 { sc.e[0..8].to_vec() } else { bank_of(&sc.pre1, &deb) };
            let mut gate = |_b: &mut B, _i: Option<usize>| None;
            // s17 A11: e[0..k] (erased) and e[kes..], pre1/pre2/zeros, g, fa when the size gate returned a constant;
            // outside the decoder bank, read_lane temps and its literals (fa, sv)
            let mut cd: Vec<QubitId> = sc.e[0..k].to_vec();
            cd.extend_from_slice(&sc.e[kes()..]);
            cd.extend_from_slice(&sc.pre1);
            cd.extend_from_slice(&sc.pre2);
            cd.extend_from_slice(&sc.zeros);
            cd.push(sc.g);
            if !made { cd.push(sc.fa); }
            if super::devsw_c::lvl(11) >= 2 { cd.extend_from_slice(&sc.more); }
            let fav = [fa];
            let cl_all = spare(&cd, &[&t, &s, bank, mtmp, &[sc.c0, ek, sc.sv, act], &fav[..usize::from(made)], dirty, &sc.sa, &sc.sb]);
            let nr = read_lane_need(tv.len(), 2, bank.len()).min(cl_all.len());
            let (rl_sp, cl) = (cl_all[..nr].to_vec(), cl_all[nr..].to_vec());
            let mut mid = |b: &mut B| {
                let lane = |v: usize| if v < src.len() { Some(src[v]) } else { None };
                read_lane_x(b, &tv, tlo, thi, &lane, true, &[(fa, false), (sc.sv, true)], ek, bank, mtmp, dirty, &rl_sp);
            };
            ripple_c(b, &t, &s, sc.c0, true, &mut mid, &mut gate, &cl, 5);
        }
        if made {
            gate_le_undo_h(b, sc, act, 258 - k as isize, &sc.e[0..k], hold_i);
        }
    }
    if hold_i { if use_sb { s_add_sb(b, sc, true); HELD_SB.with(|c| c.set(false)); } else { s_add(b, sc, true); } }
    ptk[2] = b.tof - pt0;
    // ---- widen: lanes [bl(r), NP-1-bl(t)) ^= sv
    {
        let c1 = Cut { v: ph.rv.clone(), a: 0, neg: false }; // l < bl(r)
        let c2 = Cut { v: ph.tv.clone(), a: (NP - 1) as isize, neg: true }; // l < NP-1-bl(t)
        let lo = rlo;
        let hi = (NP - 1).saturating_sub(tlo);
        let (f1, f2) = (sc.fa, sc.g);
        // s6-cut 6: c1 = bl(r) <= rhi (f1 = [l < c1] = 0 from lane rhi), c2 = 258 - bl(t) >= 258 - thi (f2 = 1 below)
        let (hi1, lo2) = if cut(6) { (rhi.min(hi), (NP - 1).saturating_sub(thi)) } else { (hi, lo) };
        // e is erased: its lanes serve as decoder banks from here on
        walk2x(b, &c1, &c2, lo, hi, hi1, lo2, f1, f2, &sc.e[0..8], &sc.e[8..16], mtmp[0], dirty, &mut |b, l| {
            let mut lits: Vec<(QubitId, bool)> = Vec::with_capacity(3);
            if l < hi1 { lits.push((f1, true)); }
            if l >= lo2 { lits.push((f2, false)); }
            lits.push((sc.sv, false));
            mc_xor(b, &lits, p[l], &mtmp[1..], dirty);
        });
    }
    ptk[3] = b.tof - pt0;
    // ---- complement lanes (bl(r), NP) on active shots
    {
        for l in (rhi + 1)..NP {
            b.cx(act, p[l]);
        }
        let cut = Cut { v: ph.rv.clone(), a: 1, neg: false }; // f = [l < bl(r) + 1] = [l <= bl(r)]
        let lo = rlo + 1;
        let hi = rhi + 1;
        if lo < hi {
            super::frogdrop::walk_cutf_capped(b, &cut, lo, hi, sc.fa, &sc.e[0..16], mtmp[0], dirty, |b, l, f| {
                b.x(f);
                b.ccx(f, act, p[l]);
                b.x(f);
            });
        }
    }
    ptk[4] = b.tof - pt0;
    // ---- erase sv: sv = lane bl(r) (sign-extended W, not complemented)
    {
        let lane = |v: usize| if v < NP { Some(p[v]) } else { None };
        let mut cd: Vec<QubitId> = sc.pre1.clone();
        cd.extend_from_slice(&sc.pre2);
        cd.extend_from_slice(&sc.e[8..]);
        cd.extend_from_slice(&sc.more);
        let rl_sp = spare(&cd, &[&sc.e[0..8], mtmp, &[sc.sv, act, sc.c0], dirty, &sc.sa, &sc.sb, &ph.tv, &ph.rv]);
        read_lane_x(b, &ph.rv, rlo, rhi, &lane, false, &[(act, false)], sc.sv, &sc.e[0..8], mtmp, dirty, &rl_sp);
    }
    ptk[5] = b.tof - pt0;
    if std::env::var("FROGDROP_PROF2").is_ok() { let pc = PCNT.with(|c| { let v = *c.borrow(); *c.borrow_mut() = [0; 4]; v }); eprintln!("digprof ht {} rr {:?} tr {:?} cum {:?} readlane/mask/gate {:?}", ph.ht, ph.rr, ph.tr, ptk, pc); }
}

/// Transition adds U += g * 2^k * src (k = 0..q0.len()) on the post region, where g = q0[k] & AND(act) (& the coarse
/// mask for ring sources: allowed positions P < 266 - 16 (bl(r) >> 4)). Window positions [k, wtop).
pub fn trans_q0(b: &mut B, p: &[QubitId], q0: &[QubitId], sel: Option<&[bool]>, act: &[(QubitId, bool)],
                src: &[QubitId], wtop: usize, mask: Option<(&[QubitId], usize)>, g: QubitId, c0: QubitId,
                temps: &[QubitId], dirty: &[QubitId]) {
    trans_q0x(b, p, q0, sel, act, src, wtop, mask, 0, g, c0, temps, dirty)
}
/// trans_q0 with `amin`: smallest value of the mask register on any shot that writes (s6-cut 5)
pub fn trans_q0x(b: &mut B, p: &[QubitId], q0: &[QubitId], sel: Option<&[bool]>, act: &[(QubitId, bool)],
                 src: &[QubitId], wtop: usize, mask: Option<(&[QubitId], usize)>, amin: usize, g: QubitId, c0: QubitId,
                 temps: &[QubitId], dirty: &[QubitId]) {
    for (k, &qk) in q0.iter().enumerate() {
        if let Some(sel) = sel {
            if !sel[k] {
                continue;
            }
        }
        let top = wtop.min(NP);
        if top <= k {
            break;
        }
        let t: Vec<QubitId> = (k..top).map(|pos| wl(p, pos)).collect();
        let s: Vec<QubitId> = src[..top - k].to_vec();
        let mut base = vec![(qk, false)];
        base.extend_from_slice(act);
        trans_one_x(b, &t, &s, k, false, base, mask, amin, g, c0, temps, dirty);
    }
}

/// one masked or plain add/sub of s into t (positions k.. of the post region), write control AND(base) (& mask).
pub fn trans_one(b: &mut B, t: &[QubitId], s: &[QubitId], k: usize, sub: bool, base: Vec<(QubitId, bool)>,
                 mask: Option<(&[QubitId], usize)>, g: QubitId, c0: QubitId, temps: &[QubitId], dirty: &[QubitId]) {
    trans_one_x(b, t, s, k, sub, base, mask, 0, g, c0, temps, dirty)
}
pub fn trans_one_x(b: &mut B, t: &[QubitId], s: &[QubitId], k: usize, sub: bool, base: Vec<(QubitId, bool)>,
                   mask: Option<(&[QubitId], usize)>, amin: usize, g: QubitId, c0: QubitId, temps: &[QubitId],
                   dirty: &[QubitId]) {
    let mut mid = |_b: &mut B| {};
    let (tcl, tsite) = TCLEAN.with(|c| c.borrow().clone());
    match mask {
        Some((bits, amax)) => {
            // s17 A15: extra AND temps for the mask toggles from the clean list (the ladder keeps the rest)
            let nm = if tsite != 0 { mask_extra(base.len() + bits.len(), temps.len(), tcl.len()) } else { 0 };
            let mut mk_t: Vec<QubitId> = temps.to_vec();
            mk_t.extend_from_slice(&tcl[..nm]);
            let tcl = tcl[nm..].to_vec();
            let brk15 = matches!(super::devsw_c::brk(15), 3 | 9) && nm > 0;
            if brk15 { b.x(mk_t[temps.len()]); }
            for &w in &mk_t[temps.len()..] { b.mark(w, 15000 + tsite); }
            let mut mk = Mask::new(bits, amax, true, base, g, &mk_t, dirty).with_cut(amin, false);
            let mut gate = |b: &mut B, i: Option<usize>| match i {
                Some(i) => {
                    let pos = (k + i) as isize;
                    mk.goto(b, Some((265 - pos).div_euclid(16) + 1));
                    Some(g)
                }
                None => {
                    mk.goto(b, None);
                    None
                }
            };
            ripple_c(b, t, s, c0, sub, &mut mid, &mut gate, &tcl, tsite);
            for &w in &mk_t[temps.len()..] { b.mark(w, 45000 + tsite); }
            if brk15 { b.x(mk_t[temps.len()]); }
        }
        None => {
            // plain: g = AND(base) for the whole down pass
            let lits = base.clone();
            let mut set = false;
            let mut gate = |b: &mut B, i: Option<usize>| match i {
                Some(_) => {
                    if !set {
                        mc_xor(b, &lits, g, temps, dirty);
                        set = true;
                    }
                    Some(g)
                }
                None => {
                    if set {
                        mc_xor(b, &lits, g, temps, dirty);
                    }
                    None
                }
            };
            ripple_c(b, t, s, c0, sub, &mut mid, &mut gate, &tcl, tsite);
        }
    }
}

/// Narrow: offset form U at width NP - B (offset bit at lane B = bl(r_j)) -> two's complement W in the region
/// [NP-1-bl(t'), NP), t' = t_{j+1}, on shots with gn. `bv` = bl(r_j) register / range, `tv` = bl(t') register / range.
pub fn narrow(b: &mut B, p: &[QubitId], bv: &[QubitId], br: (usize, usize), tv: &[QubitId], tr: (usize, usize),
              gn: QubitId, sv: QubitId, f1: QubitId, f2: QubitId, pre1: &[QubitId], pre2: &[QubitId], temps: &[QubitId],
              dirty: &[QubitId]) {
    let sign_lane = |v: usize| if v <= NP - 1 { Some(p[NP - 1 - v]) } else { None };
    // s17 A10: pre2 is |0> around both sign reads (it is the walk's second decoder bank in between): spare decoder wires
    read_lane_x(b, tv, tr.0, tr.1, &sign_lane, false, &[(gn, false)], sv, pre1, temps, dirty, pre2);
    // lanes (B, NP-1-bl(t')) ^= sv
    {
        let c1 = Cut { v: bv.to_vec(), a: 1, neg: false }; // f1 = [l <= B]
        let c2 = Cut { v: tv.to_vec(), a: (NP - 1) as isize, neg: true }; // f2 = [l < NP-1-bl(t')]
        let lo = br.0 + 1;
        let hi = (NP - 1).saturating_sub(tr.0);
        // s6-cut 6: c1 = B + 1 <= br.1 + 1, c2 = 258 - bl(t') >= 258 - tr.1
        let (hi1, lo2) = if cut(6) { ((br.1 + 1).min(hi), (NP - 1).saturating_sub(tr.1)) } else { (hi, lo) };
        // D1 C9c: f2 held as sv & [l < c2] when pre2 can carry c2's decoder plus sv as an extra top bit
        let fold = super::devsw_d1::on(10) && pre2.len() >= tv.len();
        let mut per = |b: &mut B, l: usize| {
            let mut lits: Vec<(QubitId, bool)> = Vec::with_capacity(3);
            if l < hi1 { lits.push((f1, true)); }
            if l >= lo2 { lits.push((f2, false)); }
            if !(fold && l >= lo2) { lits.push((sv, false)); }
            mc_xor(b, &lits, p[l], &temps[1..], dirty);
        };
        if fold {
            walk2x_sv(b, &c1, &c2, lo, hi, hi1, lo2, f1, f2, sv, pre1, pre2, temps[0], dirty, &mut per);
        } else {
            walk2x(b, &c1, &c2, lo, hi, hi1, lo2, f1, f2, pre1, pre2, temps[0], dirty, &mut per);
        }
    }
    // lane B ^= gn & !sv
    // D1 C9: gn and !sv fold into the decoder as two extra top bits of the register (match value gn = 1, sv = 0), so each lane
    // is one CX from the last prefix level instead of a 2-Toffoli chain; the extra levels live on pre2[..] (|0> here: the walk's
    // second decoder bank, cleared by walk2x) and are cleared by Dec::clear.
    let need9 = bv.len() + 1;
    if super::devsw_d1::on(9) && pre1.len() + pre2.len() >= need9 && pre1.len() <= need9 {
        let brk = super::devsw_d1::brk(9);
        let mut ext: Vec<QubitId> = bv.to_vec();
        ext.push(gn);
        ext.push(sv);
        let mut pre_e: Vec<QubitId> = pre1.to_vec();
        pre_e.extend_from_slice(&pre2[..need9 - pre1.len()]);
        if brk == 1 { b.x(pre_e[pre_e.len() - 1]); }
        let mut dec = Dec::new(&ext, &pre_e);
        for v in br.0..=br.1 {
            if v >= NP || v >= (1usize << bv.len()) {
                break;
            }
            let c = dec.ctrls(b, v | (if brk == 2 { 0 } else { 1usize << bv.len() }));
            mc_xor(b, &c, p[v], temps, dirty);
        }
        dec.clear(b);
        if brk == 1 { b.x(pre_e[pre_e.len() - 1]); }
    } else {
        let mut dec = Dec::new(bv, pre1);
        for v in br.0..=br.1 {
            if v >= NP || v >= (1usize << bv.len()) {
                break;
            }
            let mut c = dec.ctrls(b, v);
            c.push((gn, false));
            c.push((sv, true));
            mc_xor(b, &c, p[v], temps, dirty);
        }
        dec.clear(b);
    }
    read_lane_x(b, tv, tr.0, tr.1, &sign_lane, false, &[(gn, false)], sv, pre1, temps, dirty, pre2);
}

// ---------------------------------------------------------------------------------------------------------------
// Column hooks

use super::frogdrop_col::{ColPar, ColScr, Fd};

/// Payload context of a traversal column.
pub struct PlCol {
    /// the NP payload lanes
    pub p: Vec<QubitId>,
    /// lanes clean outside P and outside stages 1-2 / 9's own temps (pool[10..64] in the point add): stage 1.5 and
    /// 9 narrowing scratch, plus (with the spare size register appended) the digit scratch of stage 2.5
    pub free: Vec<QubitId>,
    /// clean from the end of P through stage 5's correction: act, zero, zero, g, c0 (pool[10..15])
    pub mid_hr: Vec<QubitId>,
    /// clean at stage 7's insertion: temp, act, g, c0 (pool[11..15])
    pub mid_ht: Vec<QubitId>,
    /// borrowed lanes never used as payload operands (ring top lanes)
    pub dirty: Vec<QubitId>,
    /// debug observers (empty in production)
    pub obs: Vec<QubitId>,
}


pub const L0P: usize = super::frogdrop_sched::L0;

/// Digit scratch on `free` (pool[10..] + sx): e (KE lanes), sv, fa, g, c0, tmp (2), one zero lane, then two decoder
/// prefix banks of m = min(8, (len - KE - 7) / 2) lanes (the stepping flag lives outside: the sw lane). sa / sb: the
/// sz / sy registers (s = sz + sy in place). Short banks are topped up by the lanes each step knows to be clean.
fn dig_scr(free: &[QubitId], sa: &[QubitId], sb: &[QubitId], dirty: &[QubitId]) -> DigScr {
    let n0 = ke() + 7;
    assert!(free.len() >= n0, "payload digit scratch: {} lanes", free.len());
    let m = ((free.len() - n0) / 2).min(8);
    DigScr { e: free[0..ke()].to_vec(), sa: sa.to_vec(), sb: sb.to_vec(), sv: free[ke()], fa: free[ke() + 1],
             g: free[ke() + 2], c0: free[ke() + 3], tmp: free[ke() + 4..ke() + 6].to_vec(), zeros: free[ke() + 6..n0].to_vec(),
             pre1: free[n0..n0 + m].to_vec(), pre2: free[n0 + m..n0 + 2 * m].to_vec(), dirty: dirty.to_vec(),
             more: free[n0 + 2 * m..].to_vec() }
}

/// `base` topped up with `more` (distinct lanes, at most 8: a decoder holds at most 8 prefix levels)
fn bank_of(base: &[QubitId], more: &[QubitId]) -> Vec<QubitId> {
    let mut v = base.to_vec();
    for &x in more {
        if v.len() >= 8 {
            break;
        }
        if !v.contains(&x) {
            v.push(x);
        }
    }
    v
}

fn pad(v: &[QubitId], zeros: &[QubitId], len: usize) -> Vec<QubitId> {
    let mut out: Vec<QubitId> = v.iter().copied().take(len).collect();
    let mut zi = 0;
    while out.len() < len {
        out.push(zeros[zi]);
        zi += 1;
    }
    out
}

/// stepping flag of a phase: HR = !ph & !sw, HT = ph & cnt == 0 (when some shot may be done)
fn act_lits(fd: &Fd, cp: &ColPar, sc: &ColScr, ht: bool) -> Vec<(QubitId, bool)> {
    let mut l = if cp.fz && !ht { vec![] } else { vec![(fd.ph, !ht)] };
    if !ht && cp.sw {
        l.push((sc.sw, true));
    }
    if cp.wait {
        l.push((super::frogdrop_col::wx(), true));
    }
    l
}

/// act ^= the phase's stepping flag (HT: ph & not done, done derived)
fn set_act(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, ht: bool, act: QubitId, temps: &[QubitId], dirty: &[QubitId]) {
    let lits = act_lits(fd, cp, sc, ht);
    if ht && cp.dn {
        if don("P1R2B") {
            // s16 P1-R2: the W1 bounds the Stage 5 caller of the same flag already uses (bl(Q) of non-done shots, counter bits)
            let qb_y = if cp.sy.1 == 0 || cp.m == 0 { usize::MAX } else { cp.sy.1.min(cp.m) };
            let cw = if dbrk("P1R2B") == 1 { cp.cntw.saturating_sub(1) } else { cp.cntw };
            super::frogdrop_col::mc_xor_dnx(b, &lits, act, temps, dirty, fd, false, qb_y, cw);
        } else {
            super::frogdrop_col::mc_xor_dn(b, &lits, act, temps, dirty, fd, cp.l0, false);
        }
    } else {
        mc_xor(b, &lits, act, temps, dirty);
    }
}

/// Stage 2.5 (after the middle swap: Q = Y): digit + offset prep of both phases.
pub fn col_digit(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    if super::devsw_c::dbg() { eprintln!("DBGLIVE col_digit live {} peak {} free {} nq {} sy.1 {} dn {}", b.live, b.peak, pl.free.len(), fd.q.len(), cp.sy.1, cp.dn); }
    KES.with(|k| k.set(if cp.qb == super::pointadd_frogdrop::QB { ke() } else { cp.qb - 1 }));
    let mut free = pl.free.clone();
    free.extend_from_slice(&fd.sx);
    // one lane beyond the digit scratch: s = sz + sy needs nine bits (sz's ninth lane), except in a wide-sz column,
    // whose sz already holds the sw lane and whose stepping flag takes this lane instead
    let extra = free.pop().unwrap();
    // s16 P2-F8: HT's stepping flag on its own clean lane (the next spare size lane) instead of borrowing sw, which saves
    // the two sw_toggle erase/recompute pairs per column (BREAK 1: the flag lane is the digit scratch's fa lane)
    let ht_own = don("P2F8");
    let ht_act: Option<QubitId> = if ht_own {
        if dbrk("P2F8") == 1 { Some(free[ke() + 1]) } else { Some(free.pop().unwrap()) }
    } else { None };
    let wide = sc.sz.len() > super::frogdrop_col::SZB;
    assert!(!wide || !cp.sw);
    let mut sa = sc.sz.clone();
    if !wide { sa.push(extra); }
    let mut ds = dig_scr(&free, &sa, &fd.sy, &pl.dirty);
    SPARE.with(|c| c.set(if wide { None } else { Some(extra) }));
    if super::devsw_c::lvl(11) >= 2 {
        // loan-bank lanes of Q: |0> outside P's pipeline (Y < 2^sy; done shots hold R < 2^26 in <= 28 low lanes and the counter
        // in the top lanes): the lanes the later stages' ring_cadd2_loan borrows (ripple_c drops the ones a source uses)
        let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
        let loan_end = fd.q.len() - if cp.dn { fd.cnt.len() } else { 0 };
        if lsb < loan_end {
            // census line for the Q loan-bank invariant at stage 2.5 (marker 19000 before, 49000 after the digit); BREAK=4 flips one loan lane
            if super::devsw_c::brk(11) == 4 { b.x(fd.q[lsb]); }
            for &w in &fd.q[lsb..loan_end] { b.mark(w, 19000); }
            ds.more.extend_from_slice(&fd.q[lsb..loan_end]);
            LOAN_PEND.with(|c| *c.borrow_mut() = Some((lsb, loan_end)));
        }
    }
    // The stepping flag lives on the sw lane. sw = !ph & [sz <= l0] (stage 1b) is a function of ph and sz, both
    // unchanged through stage 2.5 and zero on ph shots: HR's flag !ph & !sw is sw ^ !ph in place; HT erases sw,
    // holds its own flag there and recomputes sw.
    let act_hr = if wide { extra } else { sc.sw };
    let mut atemps = ds.tmp.clone();
    // s17 A18: set_act's derived-done test is mc_xor_dn: up to ~70 literals (ph, wx, Q[RA..ctop), cnt) with only ds.tmp (2) as AND
    // temps, so the rest runs through the dirty Barenco tail (4 Toffoli per literal). Before the digit / after ht_exact_trans every
    // DigScr lane is |0> (DigScr doc, payload.rs:235): give set_act all of them as an and_c chain (1 Toffoli per literal).
    let a18_n = atemps.len();
    if super::devsw_c::on(18) {
        let mut cd: Vec<QubitId> = ds.pre1.clone();
        cd.extend_from_slice(&ds.pre2);
        cd.extend_from_slice(&ds.e);
        cd.extend_from_slice(&ds.more);
        cd.extend_from_slice(&ds.zeros);
        cd.push(ds.sv);
        cd.push(ds.fa);
        let ex = spare(&cd, &[&ds.tmp, &[act_hr, ht_act.unwrap_or(act_hr), ds.c0, ds.g], &pl.p, &pl.dirty, &fd.q, &fd.cnt, &fd.ring, &fd.sy, &sc.sz, &[fd.ph, sc.sw]]);
        atemps.extend_from_slice(&ex);
    }
    let a18 = |b: &mut B, tag: u32| {
        if !super::devsw_c::on(18) { return; }
        if tag == 18000 && super::devsw_c::brk(18) == 1 && atemps.len() > a18_n { b.x(atemps[a18_n]); }
        for &w in &atemps[a18_n..] { b.mark(w, tag); }
        if tag == 48000 && super::devsw_c::brk(18) == 1 && atemps.len() > a18_n { b.x(atemps[a18_n]); }
    };
    let dirty = &pl.dirty;
    let hr_flag = |b: &mut B| {
        b.x(fd.ph);
        b.cx(fd.ph, act_hr);
        if cp.wait { b.ccx(fd.ph, super::frogdrop_col::wx(), act_hr); }
        b.x(fd.ph);
    };
    // sw ^= !ph & [sz <= l0] on the clean digit scratch (fa the compare, e[0..8] its carries)
    let sw_toggle = |b: &mut B| {
        if !cp.sw {
            return;
        }
        ge_const(b, &sc.sz, cp.l0 as isize + 1, ds.fa, &ds.e[0..8]);
        if cp.wait { mc_xor(b, &[(ds.fa, true), (fd.ph, true), (super::frogdrop_col::wx(), true)], sc.sw, &ds.e[8..9], dirty); }
        else { mc_xor(b, &[(ds.fa, true), (fd.ph, true)], sc.sw, &[], dirty); }
        ge_const(b, &sc.sz, cp.l0 as isize + 1, ds.fa, &ds.e[0..8]);
    };
    for ht in [false, true] {
        if (!ht && !cp.hr) || (ht && !cp.ht) {
            continue;
        }
        let ph = if !ht {
            let rr = (cp.sz.0.max(L0P + 1), cp.sz.1.min(256));
            let tr = (cp.sy.0.max(1), cp.sy.1.min(257 - (L0P + 1)));
            if rr.0 > rr.1 || tr.0 > tr.1 {
                continue;
            }
            Ph { ht, rv: sc.sz.clone(), rr, tv: fd.sy.clone(), tr, src_r: fd.ring.clone(),
                 src_t: pad(&fd.q, &ds.zeros, tr.1 + 1) }
        } else {
            let rr = (cp.sy.0.max(1), cp.sy.1.min(L0P));
            let tr = (cp.sz.0.max(1), cp.sz.1.min(256));
            if rr.0 > rr.1 || tr.0 > tr.1 {
                continue;
            }
            Ph { ht, rv: fd.sy.clone(), rr, tv: sc.sz.clone(), tr, src_r: pad(&fd.q, &ds.zeros, rr.1 + 1),
                 src_t: fd.ring.clone() }
        };
        let act = if ht { ht_act.unwrap_or(act_hr) } else { act_hr };
        // the stepping flag's long derived-done test borrows the payload lanes (no operand of it)
        if ht {
            if !ht_own { sw_toggle(b); }
            a18(b, 18000);
            set_act(b, fd, cp, sc, ht, act, &atemps, &pl.p);
            a18(b, 48000);
        } else {
            hr_flag(b);
        }
        digit(b, &pl.p, &ph, act, &ds, dirty);
        if ht {
            ht_exact_trans(b, fd, cp, &sc.sz, &pl.p, act, &ds, dirty);
        }
        if ht {
            a18(b, 18001);
            set_act(b, fd, cp, sc, ht, act, &atemps, &pl.p);
            a18(b, 48001);
            if !ht_own { sw_toggle(b); }
        } else {
            hr_flag(b);
        }
    }
    if let Some((lsb, loan_end)) = LOAN_PEND.with(|c| c.borrow_mut().take()) {
        for &w in &fd.q[lsb..loan_end] { b.mark(w, 49000); }
        if super::devsw_c::brk(11) == 4 { b.x(fd.q[lsb]); }
    }
}

/// Stage 3.5 (after P): HR transition U += q0 |t_j| (|t_j| = Y in Q, no garbage, offset form keeps every carry in
/// the region; HR regions lie in positions < 140).
pub fn col_trans_hr_q0(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol, set: &[bool]) {
    if !cp.hr {
        return;
    }
    let m = &pl.mid_hr;
    let (act, z1, z2, g, c0) = (m[0], m[1], m[2], m[3], m[4]);
    let lits = act_lits(fd, cp, sc, false);
    mc_xor(b, &lits, act, &[], &pl.dirty);
    let wtop = if cut(4) { 259usize.saturating_sub(cp.sz.0.max(L0P + 1)) } else { 259 - (L0P + 1) };
    let src = pad(&fd.q, &[z1, z2], wtop);
    trans_q0(b, &pl.p, &sc.ps.q0, Some(set), &[(act, false)], &src, wtop, None, g, c0, &[], &pl.dirty);
    mc_xor(b, &lits, act, &[], &pl.dirty);
}

/// Stage 5 (HR correction, bq = HR correction bit still live): U -= bq |t_j|.
pub fn col_trans_hr_bq(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    if !cp.hr {
        return;
    }
    let m = &pl.mid_hr;
    let (z1, z2, g, c0) = (m[1], m[2], m[3], m[4]);
    let wtop = if cut(4) { 259usize.saturating_sub(cp.sz.0.max(L0P + 1)) } else { 259 - (L0P + 1) };
    let t: Vec<QubitId> = (0..wtop).map(|pos| wl(&pl.p, pos)).collect();
    let src = pad(&fd.q, &[z1, z2], wtop);
    trans_one(b, &t, &src, 0, true, vec![(sc.bq, false)], None, g, c0, &[], &pl.dirty);
}

/// Stage 7 hook: unused (the HT transition runs before P with the exact quotient, see `ht_exact_trans`; during P
/// the ring gap above Z holds the pipeline remainder).
pub fn col_trans_ht(_b: &mut B, _fd: &Fd, _cp: &ColPar, _sc: &ColScr, _pl: &PlCol) {}

/// Stage 9 (Q = X_new = t_{j+1}, sz = bl(r_j) still live): HR narrowing; sx probes bl(X_new).
pub fn col_narrow_hr(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    if !cp.hr {
        return;
    }
    let f = &pl.free;
    let (gn, sv, f1, f2) = (f[0], f[1], f[2], f[3]);
    let temps = [f[4], f[5]];
    let pre1 = f[6..14].to_vec();
    let pre2 = f[14..22].to_vec();
    // s6-cut 3: bl(X_new) = max(bl X_new, bl Y) in [smax.0, smax.1 = m] on a stepping shot (t_{j+1} >= t_j >= 1)
    let tlo = if cut(3) { cp.smax.0.max(1).min(cp.m) } else { 1 };
    b.begin();
    {
        // s17 A12 bank: every pl.free lane (|0> at stage 9, before gn / the narrowing scratch is formed and again after it
        // is erased) and the old probe's own helpers opre / tmp
        let mut cd = pl.free.clone(); cd.extend_from_slice(&sc.opre); cd.push(sc.tmp);
        probe12(b, &fd.q, tlo - 1, cp.m, &fd.sx, &cd, &[&sc.dirty, &pl.dirty],
                &|b| super::frogdrop::msb_probe_range(b, &fd.q, tlo - 1, cp.m, &fd.sx, &sc.opre, sc.tmp, &sc.dirty), 1);
    }
    let probe = b.end();
    b.play(&probe, false);
    let lits = act_lits(fd, cp, sc, false);
    mc_xor(b, &lits, gn, &temps, &pl.dirty);
    let br = (cp.sz.0.max(L0P + 1), cp.sz.1.min(256));
    narrow(b, &pl.p, &sc.sz, br, &fd.sx, (tlo, cp.m), gn, sv, f1, f2, &pre1, &pre2, &temps, &pl.dirty);
    mc_xor(b, &lits, gn, &temps, &pl.dirty);
    b.play(&probe, true);
}

// ---------------------------------------------------------------------------------------------------------------
// floor-form NICF fused HR columns (see golden-walk/pareto-drop/BUILD.md S3)

/// t <- s - t = ~(t + ~s) on lanes l < bound where `ctl`; writes past the bound suppressed by a Mask on `bits`
/// (below = false: bound = a, lim(l) = l + 1; below = true: bound = 258 - a, lim(l) = 258 - l), the final complement
/// walk-masked by `cut` from `lo` (every shot's bound >= lo).
#[allow(clippy::too_many_arguments)]
pub(crate) fn reflect_masked(b: &mut B, t: &[QubitId], s: &[QubitId], ctl: QubitId, bits: &[QubitId], amax: usize, below: bool,
                  cut: &Cut, lo: usize, g: QubitId, c0: QubitId, f: QubitId, pre: &[QubitId], tmp: QubitId,
                  temps: &[QubitId], dirty: &[QubitId]) {
    let w = t.len();
    for &x in s { b.x(x); }
    {
        let mut mk = Mask::new(bits, amax, below, vec![(ctl, false)], g, temps, dirty);
        let mut mid = |_b: &mut B| {};
        let mut gate = |b: &mut B, i: Option<usize>| match i {
            Some(i) => {
                let lim = if below { 258 - i as isize } else { i as isize + 1 };
                mk.goto(b, Some(lim));
                Some(g)
            }
            None => { mk.goto(b, None); None }
        };
        ripple(b, t, s, c0, false, &mut mid, &mut gate);
    }
    for &x in s { b.x(x); }
    for l in 0..lo.min(w) { b.cx(ctl, t[l]); }
    if lo < w {
        // capped walk: a shot whose bound exceeds w (e.g. 258 - bl(T) = 257 > 256) must still leave f clean
        super::frogdrop::walk_cutf_capped(b, cut, lo, w, f, pre, tmp, dirty, |b, l, f| b.ccx(f, ctl, t[l]));
    }
}

/// Stage 9 of a fused column (after col_narrow_hr; sz = bl(r'_k) live, Z = r'_k): d <- r'_k - d where e'.
/// Scratch: pl.free (clean after the narrowing); borrowed: Q lanes.
pub fn col_fused_pre(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol, ep: QubitId) {
    let f = &pl.free;
    let w = cp.sz.1.min(256);
    let cut = Cut { v: sc.sz.clone(), a: 0, neg: false };
    reflect_masked(b, &pl.p[..w], &fd.ring[..w], ep, &sc.sz, cp.sz.1, false, &cut, cp.sz.0.min(w), f[0], f[1], f[2],
                   &f[3..11], f[11], &f[3..15], &fd.q[..28]);
}

/// Post-map of a fused column (after qfix: Q = t'_{k+1} on fused shots, Z = r'_{k+2}, fd.sy = bl(T)): d <- r'_{k+2} - d
/// where e'; then RCF level k+1 on W with the known digit e' (digit tail: add, erase, widen, complement), the q = 1
/// transition U += |t'_{k+1}| and the narrowing to bl(T). `gate` = HR-active literals; act = o & gate.
/// `bank`: the post-map scratch (>= 51 clean lanes): ac | rvq (9) | 41 shared.
#[allow(clippy::too_many_arguments)]
pub fn col_fused_post(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol, gate: &[(QubitId, bool)], o: QubitId,
                      ep: QubitId, bank: &[QubitId]) {
    let _ = sc;
    assert!(bank.len() >= 10 + 23 + 4, "fused post bank: {} lanes", bank.len());
    let ac = bank[0];
    let rvq: Vec<QubitId> = bank[1..10].to_vec();
    let r = &bank[10..];
    let (sy_lo, sy_hi) = (cp.sy.0.max(1), cp.smax.1.min(128));
    let temps: Vec<QubitId> = r[3..15].to_vec();
    // (a) d <- Z - d on lanes l < 258 - bl(T)
    let w = (258 - sy_lo).min(256);
    let cut = Cut { v: fd.sy.clone(), a: 258, neg: true };
    reflect_masked(b, &pl.p[..w], &fd.ring[..w], ep, &fd.sy, sy_hi, true, &cut, (258 - sy_hi).min(w), r[0], r[1], r[2],
                   &r[3..11], r[11], &temps, &fd.q[..28]);
    // (b) act = o & gate
    let mut al = vec![(o, false)];
    al.extend_from_slice(gate);
    mc_xor(b, &al, ac, &temps, &pl.dirty);
    // (c) rvq = 257 - bl(T) (9 lanes): copy, complement, + 258 mod 512 (the constant on 9 transient lanes)
    let c258 = &r[0..9];
    b.begin();
    for i in 0..fd.sy.len() { b.cx(fd.sy[i], rvq[i]); }
    for &x in &rvq { b.x(x); }
    b.x(c258[1]); b.x(c258[8]);
    super::arith::ttk_add(b, c258, &rvq, None, None);
    b.x(c258[1]); b.x(c258[8]);
    let rvrec = b.end();
    b.play(&rvrec, false);
    let rr = (257 - sy_hi, 257 - sy_lo);
    let tr = (sy_lo, sy_hi);
    // digit scratch (e[0] = e'; e[1..16] clean decoder banks); the two prefix banks take what the bank leaves
    let dm = ((r.len() - 23) / 2).min(8);
    let mut e = vec![ep];
    e.extend_from_slice(&r[0..15]);
    let ds = DigScr { e, sa: rvq.clone(), sb: fd.sy.clone(), sv: r[15], fa: r[16], g: r[17], c0: r[18],
                      tmp: r[19..21].to_vec(), zeros: r[21..22].to_vec(), pre1: r[22..22 + dm].to_vec(), pre2: r[22 + dm..22 + 2 * dm].to_vec(),
                      dirty: pl.dirty.clone(), more: vec![] };
    let zeros_t: Vec<QubitId> = r[22 + 2 * dm..23 + 2 * dm].to_vec();
    let ph = Ph { ht: false, rv: rvq.clone(), rr, tv: fd.sy.clone(), tr, src_r: vec![], src_t: pad(&fd.q, &zeros_t, tr.1 + 1) };
    let kes0 = KES.with(|k| k.get());
    KES.with(|k| k.set(1));
    SKIPDIV.with(|x| x.set(true));
    digit(b, &pl.p, &ph, ac, &ds, &pl.dirty);
    SKIPDIV.with(|x| x.set(false));
    KES.with(|k| k.set(kes0));
    // (e) transition U += act |t'_{k+1}|
    let wtop = 259 - (L0P + 1);
    let tt: Vec<QubitId> = (0..wtop).map(|pos| wl(&pl.p, pos)).collect();
    let src = pad(&fd.q, &[r[0], r[1]], wtop);
    trans_one(b, &tt, &src, 0, false, vec![(ac, false)], None, r[2], r[3], &r[4..16], &pl.dirty);
    // (f) narrowing: offset form at width NP - rv' -> W_{k+2} in [NP-1-bl(T), NP)
    narrow(b, &pl.p, &rvq, rr, &fd.sy, tr, ac, r[0], r[1], r[2], &r[3..11], &r[11..19], &[r[19], r[20]], &pl.dirty);
    b.play(&rvrec, true);
    mc_xor(b, &al, ac, &temps, &pl.dirty);
}

/// Stage 9 narrowing of a FUSED column: like col_narrow_hr, but shots with bl(r_k) + bl(X_new) = 258 (fused: X_new =
/// t'_{k+2}) narrow into a region one lane smaller (W_{k+1} fits: bl(t'_{k+1}) <= 257 - bl(r_k)) and then sign-extend W by
/// that lane (free there: d < 2^bl(r_k)), so every shot ends with W in the region of bl(X_new).
/// Extra scratch: pl.free[22..35]. f258 from the in-place sum sz += sx: every HR shot of a fusing column has
/// 130 <= sz + sx <= 258, so (8-lane sz) [sum = 258] = !bit7 & bit1, (9-lane sz, column 0) = bit8 & bit1.
pub fn col_narrow_hr_fz(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    if !cp.hr {
        return;
    }
    let f = &pl.free;
    let (gn, sv, f1, f2) = (f[0], f[1], f[2], f[3]);
    let temps = [f[4], f[5]];
    let pre1 = f[6..14].to_vec();
    let pre2 = f[14..22].to_vec();
    let x = &f[22..];
    assert!(!x.is_empty(), "fused narrowing scratch: {} lanes", f.len());
    b.begin();
    super::frogdrop::msb_probe_range(b, &fd.q, 0, cp.m, &fd.sx, &sc.opre, sc.tmp, &sc.dirty);
    let probe = b.end();
    b.play(&probe, false);
    let (f258, c0) = (x[0], f[5]);
    let flag = |b: &mut B| {
        b.begin();
        super::frogdrop::reg_add_into(b, &sc.sz, &fd.sx, &f[4..5], c0);
        let add = b.end();
        b.play(&add, false);
        if sc.sz.len() > 8 { b.ccx(sc.sz[8], sc.sz[1], f258); }
        else { b.x(sc.sz[7]); b.ccx(sc.sz[7], sc.sz[1], f258); b.x(sc.sz[7]); }
        b.play(&add, true);
    };
    flag(b);
    // sx -= f258 (controlled decrement)
    let anc: Vec<QubitId> = f[6..13].to_vec();
    super::arith::dec(b, f258, &fd.sx, &anc);
    let lits = act_lits(fd, cp, sc, false);
    mc_xor(b, &lits, gn, &temps, &pl.dirty);
    let br = (cp.sz.0.max(L0P + 1), cp.sz.1.min(256));
    let tr = (1usize, cp.m);
    narrow(b, &pl.p, &sc.sz, br, &fd.sx, tr, gn, sv, f1, f2, &pre1, &pre2, &temps, &pl.dirty);
    mc_xor(b, &lits, gn, &temps, &pl.dirty);
    // sign-extend by one lane where f258: p[NP-1-(v+1)] ^= p[NP-1-v] for the (decremented) sx value v
    {
        let mut dec = Dec::new(&fd.sx, &f[6..13]);
        for v in 0..cp.m.min(NP - 2) {
            if v >= (1usize << fd.sx.len()) { break; }
            let mut c = dec.ctrls(b, v);
            c.push((f258, false));
            c.push((pl.p[NP - 1 - v], false));
            mc_xor(b, &c, pl.p[NP - 2 - v], &f[14..18], &pl.dirty);
        }
        dec.clear(b);
    }
    super::arith::inc(b, f258, &fd.sx, &anc);
    flag(b);
    b.play(&probe, true);
}

/// Stage 1.5 (sz = bl(Z) probed, Q = X): HT narrowing of the shots that stepped HT in the previous column
/// (ph & bl(Q) <= l0 & cnt <= 1): B = bl(Q) = bl(r_j) probed into sx, bl(t_{j+1}) = sz.
pub fn col_narrow_ht(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    if !cp.pht {
        return;
    }
    // Runs before stage 1b: the sw lane is clean and joins the free lanes. gn and the parked counter (pd, park)
    // stay live across the bl(Q) probe, so they avoid its helpers (opre, tmp); the narrowing lanes and the gate's
    // helpers may share them.
    let mut nf = vec![sc.sw];
    nf.extend_from_slice(&pl.free);
    let ph_lanes: Vec<QubitId> = sc.opre.iter().copied().chain([sc.tmp]).collect();
    let np: Vec<QubitId> = nf.iter().copied().filter(|x| !ph_lanes.contains(x)).collect();
    let gn = np[0];
    // done shots exist only in dn columns (elsewhere the parking is the identity)
    // s16 P1-R6: the counter lanes are Q[ctop..); a probe that reads only Q[..bhi] with bhi <= ctop never sees them, so
    // the parking (and unparking) of the done shots' counter around it is the identity and is dropped
    let ctop0 = fd.q.len() - fd.cnt.len();
    let bhi0 = cp.psy.1.min(L0P);
    let need_park = cp.dn && (!don("P1R6A") || (bhi0 > ctop0 + if dbrk("P1R6A") == 1 { 1 } else { 0 } && dbrk("P1R6A") != 2));
    let (pd, park): (Option<QubitId>, Vec<QubitId>) =
        if need_park { (Some(np[1]), np[2..2 + cp.cntw.min(fd.cnt.len())].to_vec()) } else { (None, vec![]) };
    let rest: Vec<QubitId> = nf.iter().copied().filter(|&x| x != gn && Some(x) != pd && !park.contains(&x)).collect();
    let (sv, f1, f2) = (rest[0], rest[1], rest[2]);
    let temps = [rest[3], rest[4]];
    let pb = &rest[5..];
    let m1 = pb.len().div_ceil(2).min(8);
    let pre1 = pb[..m1].to_vec();
    let pre2 = pb[m1..(m1 + 8).min(pb.len())].to_vec();
    let blo = cp.psy.0.max(1);
    let bhi = cp.psy.1.min(L0P);
    if blo > bhi {
        return;
    }
    b.begin();
    {
        // s17 A12 bank: the narrowing lanes nf (sw is |0> before stage 1b) and opre / tmp, minus gn and the parked
        // counter (pd, park), which are live across the probe at both ends
        let mut cd = nf.clone(); cd.extend_from_slice(&sc.opre); cd.push(sc.tmp);
        let pk: Vec<QubitId> = std::iter::once(gn).chain(pd).chain(park.iter().copied()).collect();
        probe12(b, &fd.q, blo - 1, bhi, &fd.sx, &cd, &[&sc.dirty, &pl.dirty, &pk],
                &|b| super::frogdrop::msb_probe_range(b, &fd.q, blo - 1, bhi, &fd.sx, &sc.opre, sc.tmp, &sc.dirty), 2);
    }
    let probe = b.end();
    // stepped HT last column (not done; switched-layout shots have sy > l0) or just finished (done, cnt == 1)
    let nq = fd.q.len();
    let ctop = nq - fd.cnt.len();
    // gate helpers (all clean around it): big, its compare chain, and AND temps past the chain
    let big = sv;
    let chain = &rest[1..8];
    let mut gtl: Vec<QubitId> = rest[8..].to_vec();
    gtl.extend(pd);
    gtl.extend_from_slice(&park);
    gtl.truncate(11);
    let gt: &[QubitId] = &gtl;
    // parking's AND temps: everything but gn and pd is clean then
    let pt: Vec<QubitId> = rest.iter().copied().take(11).collect();
    // s16 P1-R6 / P2-F5: big = [sy >= l0 + 1] is dead (zero) when cp.sy.1 <= l0 (P1-R6) and in columns without switched
    // first-HT shots (P2-F5: psw false), where sy <= l0 on every shot; P2-F5 also slices the comparator
    let big_live = (!don("P1R6B") || cp.sy.1 == 0 || cp.sy.1 > L0P + if dbrk("P1R6B") == 1 { 1 } else { 0 }) && (!don("P2F5A") || (cp.psw && dbrk("P2F5A") != 1)) && !(don("P1R6B") && dbrk("P1R6B") == 2);
    let mut l1 = vec![(fd.ph, false)];
    if big_live { l1.push((big, true)); }
    if cp.wait { l1.push((super::frogdrop_col::wx(), true)); }
    let sy_cmp = |b: &mut B| {
        if !big_live { return; }
        if don("P2F5B") {
            let (hi, brk) = (cp.sy.1, dbrk("P2F5B"));
            if hi != 0 && hi <= 143 + if brk == 1 { 16 } else { 0 } {
                ge_const(b, &[fd.sy[0], fd.sy[1], fd.sy[2], fd.sy[3], fd.sy[7]], 17, big, chain);
                return;
            }
            if hi != 0 && hi <= 159 {
                ge_const(b, &[fd.sy[0], fd.sy[1], fd.sy[2], fd.sy[3], fd.sy[4], fd.sy[7]], 33, big, chain);
                return;
            }
        }
        ge_const(b, &fd.sy, L0P as isize + 1, big, chain);
    };
    let p1r2 = don("P1R2B");
    // s16 P1-R2 / P2-F2: W1 bounds in this column's gate: bl(Q) of non-done shots <= xw, counter <= cntw bits; the
    // done-with-cnt==1 flag l2 exists only in done columns (the counter is zero elsewhere)
    let qb_x = if cp.xw == 0 { usize::MAX } else if p1r2 && dbrk("P1R2B") == 2 { cp.xw.min(ctop) } else { cp.xw };
    let nc = if p1r2 { cp.cntw.min(fd.cnt.len()) } else { fd.cnt.len() };
    let mut l2 = vec![(fd.ph, false)];
    if !p1r2 || qb_x > ctop { l2.extend((super::frogdrop_col::RA..ctop).map(|l| (fd.q[l], true))); }
    if nc > 0 {
        l2.push((fd.cnt[0], false));
        l2.extend(fd.cnt[1..nc].iter().map(|&x| (x, true)));
    }
    let l2_live = !p1r2 || (cp.dn && nc > 0 && dbrk("P1R2B") != 3);
    // the payload lanes are no operand of these gates: borrow them
    let gate = |b: &mut B| {
        sy_cmp(b);
        if p1r2 {
            super::frogdrop_col::mc_xor_dnx(b, &l1, gn, gt, &pl.p, fd, false, qb_x, cp.cntw);
        } else {
            super::frogdrop_col::mc_xor_dn(b, &l1, gn, gt, &pl.p, fd, cp.l0, false);
        }
        if l2_live { mc_xor(b, &l2, gn, gt, &pl.p); }
        sy_cmp(b);
    };
    // the gate first (it reads the counter); then done shots' counter is parked (pd, park: clean and outside the
    // narrowing / probe helpers) while
    // bl(Q) is probed: a probe bound above nq - cnt would read it (B = bl(R) for the just-finished shots)
    gate(b);
    let parking = |b: &mut B| {
        let Some(pd) = pd else { return };
        if p1r2 { super::frogdrop_col::mc_xor_dnx(b, &[], pd, &pt, &pl.p, fd, true, qb_x, cp.cntw); }
        else { super::frogdrop_col::mc_xor_dn(b, &[], pd, &pt, &pl.p, fd, cp.l0, true); }
        for (i, &x) in park.iter().enumerate() { b.cswap(pd, fd.cnt[i], x); }
    };
    let unparking = |b: &mut B| {
        let Some(pd) = pd else { return };
        for (i, &x) in park.iter().enumerate() { b.cswap(pd, fd.cnt[i], x); }
        if p1r2 { super::frogdrop_col::mc_xor_dnx(b, &[], pd, &pt, &pl.p, fd, true, qb_x, cp.cntw); }
        else { super::frogdrop_col::mc_xor_dn(b, &[], pd, &pt, &pl.p, fd, cp.l0, true); }
    };
    parking(b);
    b.play(&probe, false);
    let tr = (cp.sz.0.max(1), cp.sz.1.min(256));
    narrow(b, &pl.p, &fd.sx, (blo, bhi), &sc.sz, tr, gn, sv, f1, f2, &pre1, &pre2, &temps, &pl.dirty);
    b.play(&probe, true);
    unparking(b);
    gate(b);
}

/// HT transition before P (stage 2.5, ring gap clean): q = floor(X / Y) by restoring division in place on the ring-top
/// ladder X = r_{j-1} (Y = r_j in Q): X -= 2^k Y, q_k = !sign (read per shot at the buffer lane below the region),
/// add back where negative; then U += q |t_j| (|t_j| = Z, coarse-masked against the ring-top value r_{j+1}) and the
/// division is undone (X restored, q erased). Only shots with [bl(Z) + bl(Y) + k <= 257] (2^k Y within the region)
/// take bit k. q uses the digit lanes.
pub fn ht_exact_trans(b: &mut B, fd: &Fd, cp: &ColPar, sz: &[QubitId], p: &[QubitId], act: QubitId, sc: &DigScr,
                      dirty: &[QubitId]) {
    let n = fd.ring.len();
    let nq = fd.q.len();
    let mt = (n - (cp.sz.0 + cp.h) + 1).min(nq.max(cp.xw) + 1);
    let q = &sc.e;
    let (szlo, szhi) = (cp.sz.0.max(1), cp.sz.1.min(256));
    let (sylo, syhi) = (cp.sy.0.max(1), cp.sy.1.min(L0P));
    let srange = (szlo + sylo, (szhi + syhi).min(257));
    let h = cp.h;
    // s16 P2-F3 part A': div reads sz (read_lane) and never sy: hold s in sb9 = sy ++ [spare] over the loop
    let hold_dv = don("P2F3B") && sb9_of(sc).is_some()
        && (0..kes()).any(|k| k < mt && gate_made(srange, 257 - k as isize));
    let div = {
        b.begin();
        // BREAK 1: the naive hold in sa (sz is read by read_lane inside the loop)
        let naive = hold_dv && dbrk("P2F3B") == 1;
        if naive { s_add(b, sc, false); } else if hold_dv { HELD_SB.with(|c| c.set(true)); s_add_sb(b, sc, false); }
        for k in (0..kes()).rev() {
            if k >= mt {
                continue;
            }
            // clean at this step: q[0..k] (not yet written) and sv (a pad lane, zero outside the ripple)
            let mut hxe = vec![sc.sv];
            hxe.extend_from_slice(&q[0..k]);
            let Some((fa, made)) = gate_le_h(b, sc, act, srange, 257 - k as isize, &hxe, hold_dv) else { continue };
            let qk = q[k];
            // one compare-and-conditional-subtract ripple: the borrow into the shot's gap lane sz + h - 1 (window
            // position n - h - k - sz) is read after the up pass, and the down pass writes X -= 2^k Y only where
            // q_k = fa & !borrow (lanes past the shot's top then see 0 - 0 - 0). Y's lanes are padded with clean lanes.
            let span = mt - k;
            let mut pads: Vec<QubitId> = sc.pre2.clone();
            pads.extend_from_slice(&sc.zeros);
            pads.extend([sc.sv, sc.g]);
            if k > 8 { pads.extend_from_slice(&q[8..k]); }
            // below 8 the bank is topped up with the pads the ripple leaves clean and q[0..k]
            let mut hxb: Vec<QubitId> = pads[span.saturating_sub(fd.q.len()).min(pads.len())..].to_vec();
            hxb.extend_from_slice(&q[0..k]);
            let bank: &[QubitId] = &if k >= 8 { q[0..8].to_vec() } else { bank_of(&sc.pre1, &hxb) };
            if std::env::var("PL_OLDHTX").is_err() && span <= fd.q.len() + pads.len() {
                let t: Vec<QubitId> = (k..k + span).map(|m| fd.ring[n - 1 - m]).collect();
                let src: Vec<QubitId> = fd.q.iter().chain(pads.iter()).copied().take(span).collect();
                let base = (n - h) as isize - k as isize - 1;
                let rd = src.clone();
                let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| qk);
                // s17 A11: clean through this ripple: the pads the source did not take (pre2, zeros, sv, g, q[8..k]),
                // q[0..k] (not yet written), q[kes..], pre1; outside the bank, sc.tmp, the write control qk, fa (if made)
                let mut cd: Vec<QubitId> = pads.clone();
                cd.extend_from_slice(&q[0..k]);
                cd.extend_from_slice(&q[kes()..]);
                cd.extend_from_slice(&sc.pre1);
                if !made { cd.push(sc.fa); }
                if super::devsw_c::lvl(11) >= 2 { cd.extend_from_slice(&sc.more); }
                let fav = [fa];
                let cl_all = spare(&cd, &[&t, &src, bank, &sc.tmp, &[sc.c0, qk, act], &fav[..usize::from(made)], p, &sc.sa, &sc.sb]);
                let nr = read_lane_need(sz.len(), 1, bank.len()).min(cl_all.len());
                let (rl_sp, cl) = (cl_all[..nr].to_vec(), cl_all[nr..].to_vec());
                let mut mid = |b: &mut B| {
                    let lane = |v: usize| {
                        let i = base - v as isize;
                        if i >= 0 && (i as usize) < rd.len() { Some(rd[i as usize]) } else { None }
                    };
                    read_lane_x(b, sz, szlo, szhi, &lane, true, &[(fa, false)], qk, bank, &sc.tmp, p, &rl_sp);
                };
                ripple_c(b, &t, &src, sc.c0, true, &mut mid, &mut gate, &cl, 6);
                if made {
                    gate_le_undo_h(b, sc, act, 257 - k as isize, &hxe, hold_dv);
                }
                continue;
            }
            super::frogdrop_col::ring_cadd2(b, &fd.ring, &fd.q, k, mt - k, fa, true, &sc.zeros, sc.c0, sc.g, p);
            let lane = |v: usize| if v + h >= 1 && v + h - 1 < n { Some(fd.ring[v + h - 1]) } else { None };
            // the buffer lanes reach the ring top: borrow the payload lanes (no operand here) instead
            let mut hxo = sc.pre2.clone();
            hxo.extend([sc.sv, sc.g]);
            hxo.extend_from_slice(&q[0..k]);
            let bank: &[QubitId] = &if k >= 8 { q[0..8].to_vec() } else { bank_of(&sc.pre1, &hxo) };
            read_lane(b, sz, szlo, szhi, &lane, true, &[(fa, false)], qk, bank, &sc.tmp, p);
            // add back where the subtraction went negative (fa & !q_k)
            b.x(qk);
            b.and_c(fa, qk, sc.sv);
            b.x(qk);
            super::frogdrop_col::ring_cadd2(b, &fd.ring, &fd.q, k, mt - k, sc.sv, false, &sc.zeros, sc.c0, sc.g, p);
            b.x(qk);
            b.and_u(fa, qk, sc.sv);
            b.x(qk);
            if made {
                gate_le_undo_h(b, sc, act, 257 - k as isize, &hxe, hold_dv);
            }
        }
        if naive { s_add(b, sc, true); } else if hold_dv { s_add_sb(b, sc, true); HELD_SB.with(|c| c.set(false)); }
        b.end()
    };
    b.play(&div, false);
    let amax = syhi >> 4;
    // s6-cut 5: writes need pos < 266 - 16 (sy >> 4) <= 266 - 16 (sylo >> 4) and sy >> 4 >= sylo >> 4
    let (amin5, wtop5) = if cut(5) { (sylo >> 4, (266 - 16 * (sylo >> 4)).min(NP)) } else { (0, NP) };
    // B1: `div` only writes q[..kes()]; the lanes above stay zero, so their transition steps are dead
    {
        // s17 A11 (site 7): after `div` the quotient q[..kes] is live and every other digit-scratch lane is |0>: pre1, pre2, zeros,
        // sv (pad lane), fa (size gate undone), q[kes..], more; g / c0 / tmp are the transition's own write control, carry and temps
        let mut cd: Vec<QubitId> = sc.pre1.clone();
        cd.extend_from_slice(&sc.pre2);
        cd.extend_from_slice(&sc.zeros);
        cd.push(sc.sv);
        cd.push(sc.fa);
        cd.extend_from_slice(&q[kes()..]);
        if super::devsw_c::lvl(11) >= 2 { cd.extend_from_slice(&sc.more); }
        let cl = spare(&cd, &[&q[..kes()], &[sc.g, sc.c0, act], &sc.tmp, &fd.ring, dirty, p, &fd.sy, &sc.sa, &sc.sb]);
        with_tclean(cl, 7, || trans_q0x(b, p, &q[..kes()], None, &[(act, false)], &fd.ring, wtop5, Some((&fd.sy[4..], amax)), amin5, sc.g, sc.c0, &sc.tmp, dirty));
    }
    b.play(&div, true);
}

/// End of a payload traversal (every shot A0 = (t_last, R, 1) after the B0 fix; R stays in Q's low lanes):
/// deferred narrowing of the shots that finished in the last column (cnt == 1), the last digit (divisor 1 = the
/// ring-top lane, |t| = Z) and the final transition U += R |t_last| (q = R exact). Leaves U in offset form with its
/// offset bit at lane 1 (bl(r_last) = 1).
pub fn pl_end(b: &mut B, fd: &Fd, cpl: &ColPar, sc: &ColScr, pl: &PlCol) {
    KES.with(|k| k.set(ke()));
    let n = fd.ring.len();
    let dirty = &pl.dirty;
    let (szlo, szhi) = (cpl.sz.0.max(1), cpl.sz.1.min(256));
    // sz = bl(Z): Y = 1 holds lane n - 1, Z the region below it
    let probe_z = {
        b.begin();
        {
            let mut cd = pl.free.clone(); cd.extend_from_slice(&sc.opre); cd.push(sc.tmp);
            probe12(b, &fd.ring, szlo - 1, szhi, &sc.sz, &cd, &[&sc.dirty, &pl.dirty],
                    &|b| super::frogdrop::msb_probe_range(b, &fd.ring, szlo - 1, szhi, &sc.sz, &sc.opre, sc.tmp, &sc.dirty), 3);
        }
        b.end()
    };
    b.play(&probe_z, false);
    let f = &pl.free;
    // narrowing of the last column's finishers: B = bl(R) (Q < 2^26), t' = t_last
    {
        let (gn, sv, f1, f2) = (f[0], f[1], f[2], f[3]);
        let temps = [f[4], f[5]];
        let pre1 = f[6..14].to_vec();
        let pre2 = f[14..22].to_vec();
        let probe = {
            b.begin();
            {
                let mut cd = pl.free.clone(); cd.extend_from_slice(&sc.opre); cd.push(sc.tmp);
                probe12(b, &fd.q, 0, KD, &fd.sx, &cd, &[&sc.dirty, &pl.dirty],
                        &|b| super::frogdrop::msb_probe_range(b, &fd.q, 0, KD, &fd.sx, &sc.opre, sc.tmp, &sc.dirty), 4);
            }
            b.end()
        };
        b.play(&probe, false);
        let mut lits = vec![(fd.cnt[0], false)];
        lits.extend(fd.cnt[1..].iter().map(|&x| (x, true)));
        mc_xor(b, &lits, gn, &f[1..9], dirty);
        narrow(b, &pl.p, &fd.sx, (1, KD), &sc.sz, (szlo, szhi), gn, sv, f1, f2, &pre1, &pre2, &temps, dirty);
        mc_xor(b, &lits, gn, &f[1..9], dirty);
        b.play(&probe, true);
    }
    // last digit and the final transition
    let mut free = pl.free.clone();
    free.extend_from_slice(&fd.sx);
    // s = 1 + bl(t_last) may reach 256: the sw lane (clean at the end) is sz's ninth bit
    let mut sa = sc.sz.clone();
    sa.push(sc.sw);
    let ds = dig_scr(&free, &sa, &fd.sy, &pl.dirty);
    SPARE.with(|c| c.set(Some(sc.sw)));
    let act = fd.ph; // 1 on every shot
    // s6-cut 7: every shot has bl(r_last) = fd.sy = 1, a one-bit register
    let ph = Ph { ht: true, rv: if cut(7) { fd.sy[..1].to_vec() } else { fd.sy.clone() }, rr: (1, 1), tv: sc.sz.clone(), tr: (szlo, szhi),
                  src_r: vec![fd.ring[n - 1], ds.zeros[0]], src_t: fd.ring.clone() };
    digit(b, &pl.p, &ph, act, &ds, dirty);
    if cut(7) {
        // act = ph = 1 and fd.sy >> 4 = 0 on every shot: no mask, no act literal
        // s17 A11 (site 8): after digit() every DigScr lane is |0> (e erased, sv erased, fa / zeros / banks restored)
        let mut cd: Vec<QubitId> = ds.e.clone();
        cd.push(ds.sv);
        cd.push(ds.fa);
        cd.extend_from_slice(&ds.zeros);
        cd.extend_from_slice(&ds.pre1);
        cd.extend_from_slice(&ds.pre2);
        if super::devsw_c::lvl(11) >= 2 { cd.extend_from_slice(&ds.more); }
        let cl = spare(&cd, &[&[ds.g, ds.c0], &ds.tmp, &fd.ring, dirty, &pl.p, &fd.q]);
        with_tclean(cl, 8, || trans_q0(b, &pl.p, &fd.q[..KD], None, &[], &fd.ring, NP, None, ds.g, ds.c0, &ds.tmp, dirty));
    } else {
        trans_q0(b, &pl.p, &fd.q[..KD], None, &[(act, false)], &fd.ring, NP, Some((&fd.sy[4..], 0)), ds.g, ds.c0, &ds.tmp, dirty);
    }
    b.play(&probe_z, true);
}
