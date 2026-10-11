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
/// digit / quotient bits
pub const KD: usize = 26;

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
    assert_eq!(t.len(), s.len());
    let l = t.len();
    if cmpl {
        for &q in t {
            b.x(q);
        }
    }
    for i in 0..l {
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(x, t[i], s[i]);
    }
    mid(b);
    for i in (0..l).rev() {
        let x = if i == 0 { c0 } else { s[i - 1] };
        let g = gate(b, Some(i));
        b.ccx(x, t[i], s[i]);
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
}

impl<'a> Mask<'a> {
    pub fn new(bits: &'a [QubitId], amax: usize, below: bool, base: Vec<(QubitId, bool)>, g: QubitId,
               temps: &'a [QubitId], dirty: &'a [QubitId]) -> Mask<'a> {
        Mask { bits, amax, below, base, g, temps, dirty, cur: None }
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
        let (lo, hi) = if self.below { (0, (lim - 1).min(am)) } else { (lim.max(0), am) };
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
    let rl0 = b.tof;
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
    if lo >= hi {
        return;
    }
    let ch: Vec<QubitId> = pre1.iter().chain(pre2.iter()).copied().collect();
    c1.ge(b, lo as isize + 1, f1, &ch);
    c2.ge(b, lo as isize + 1, f2, &ch);
    let mut d1 = Dec::new(&c1.v, pre1);
    let mut d2 = Dec::new(&c2.v, pre2);
    for l in lo..hi {
        if l > lo {
            if let Some(v) = c1.val_at(l as isize) {
                let c = d1.ctrls(b, v);
                mc_xor(b, &c, f1, &[tmp], dirty);
            }
            if let Some(v) = c2.val_at(l as isize) {
                let c = d2.ctrls(b, v);
                mc_xor(b, &c, f2, &[tmp], dirty);
            }
        }
        per(b, l);
    }
    d1.clear(b);
    d2.clear(b);
    c1.ge(b, hi as isize, f1, &ch);
    c2.ge(b, hi as isize, f2, &ch);
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
}

/// fa = act & [s <= lim] (s register value range sr); returns the control to use (act itself when always true) and
/// whether a flag was computed. None: never true.
fn gate_le(b: &mut B, sc: &DigScr, act: QubitId, sr: (usize, usize), lim: isize) -> Option<(QubitId, bool)> {
    let g0 = b.tof;
    let r = gate_le_i(b, sc, act, sr, lim);
    pcnt(2, b.tof - g0);
    r
}
fn gate_le_i(b: &mut B, sc: &DigScr, act: QubitId, sr: (usize, usize), lim: isize) -> Option<(QubitId, bool)> {
    if (sr.0 as isize) > lim {
        return None;
    }
    if (sr.1 as isize) <= lim {
        return Some((act, false));
    }
    // c = [s >= lim + 1] on tmp[1]; fa = act & !c
    let chain = gate_chain(sc);
    s_add(b, sc, false);
    ge_const(b, &sc.sa, lim + 1, sc.tmp[1], &chain);
    b.x(sc.tmp[1]);
    b.and_c(act, sc.tmp[1], sc.fa);
    b.x(sc.tmp[1]);
    ge_const(b, &sc.sa, lim + 1, sc.tmp[1], &chain);
    s_add(b, sc, true);
    Some((sc.fa, true))
}

fn gate_le_undo(b: &mut B, sc: &DigScr, act: QubitId, lim: isize) {
    let g0 = b.tof;
    gate_le_undo_i(b, sc, act, lim);
    pcnt(2, b.tof - g0);
}
fn gate_le_undo_i(b: &mut B, sc: &DigScr, act: QubitId, lim: isize) {
    let chain = gate_chain(sc);
    s_add(b, sc, false);
    ge_const(b, &sc.sa, lim + 1, sc.tmp[1], &chain);
    b.x(sc.tmp[1]);
    b.and_u(act, sc.tmp[1], sc.fa);
    b.x(sc.tmp[1]);
    ge_const(b, &sc.sa, lim + 1, sc.tmp[1], &chain);
    s_add(b, sc, true);
}

/// carries of the size gate's comparator: both decoder banks, tmp[0], and the zero pad, c0 and g (idle while a
/// comparator runs between the in-place adds)
fn gate_chain(sc: &DigScr) -> Vec<QubitId> {
    let mut chain = sc.pre2.clone();
    chain.push(sc.tmp[0]);
    chain.extend_from_slice(&sc.pre1);
    chain.extend_from_slice(&sc.zeros);
    chain.extend([sc.c0, sc.g]);
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
    let srange = (rlo + tlo, rhi + thi);
    let pt0 = b.tof;
    let mut ptk = [0u64; 6];
    // ---- long division: e_k = [d >= 2^k r_j] with d < 2^(k+1) r_j; window positions [k, k + bl(r) + 1)
    for k in (0..KD).rev() {
        let Some((fa, made)) = gate_le(b, sc, act, srange, 257 - k as isize) else { continue };
        let top = (k + rhi + 1).min(NP);
        let t: Vec<QubitId> = (k..top).map(|i| p[i]).collect();
        let s: Vec<QubitId> = ph.src_r[..top - k].to_vec();
        let ek = sc.e[k];
        let rv = ph.rv.clone();
        let src = s.clone();
        // e[0..k] are still clean: from k = 8 on they are the decoder bank
        let bank: &[QubitId] = if k >= 8 { &sc.e[0..8] } else { &sc.pre1 };
        let mut mid = |b: &mut B| {
            let lane = |v: usize| if v < src.len() { Some(src[v]) } else { None };
            read_lane(b, &rv, rlo, rhi, &lane, true, &[(fa, false)], ek, bank, mtmp, dirty);
        };
        if ph.ht {
            let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| ek);
            ripple(b, &t, &s, sc.c0, true, &mut mid, &mut gate);
        } else {
            // HR: ring-sourced divisor; writes allowed at d positions P < 266 - 16 (bl(t) >> 4)
            let bits = &ph.tv[4..];
            let mut mk = Mask::new(bits, thi >> 4, true, vec![(ek, false)], sc.g, &mtmp[..1], dirty);
            let mut gate = |b: &mut B, i: Option<usize>| match i {
                Some(i) => {
                    let pos = (k + i) as isize;
                    mk.goto(b, Some((265 - pos).div_euclid(16) + 1));
                    Some(sc.g)
                }
                None => {
                    mk.goto(b, None);
                    None
                }
            };
            ripple(b, &t, &s, sc.c0, true, &mut mid, &mut gate);
        }
        if made {
            gate_le_undo(b, sc, act, 257 - k as isize);
        }
    }
    ptk[0] = b.tof - pt0;
    // ---- sv = sign of W (lane of bit bl(t))
    {
        let lane = |v: usize| if v <= NP - 1 { Some(p[NP - 1 - v]) } else { None };
        read_lane(b, &ph.tv, tlo, thi, &lane, false, &[(act, false)], sc.sv, &sc.pre1, mtmp, dirty);
    }
    ptk[1] = b.tof - pt0;
    // ---- D^-1: W += e_k 2^k |t|; e_k ^= act & !sv & [s <= 258 - k] & [W >= 2^k |t|]
    for k in 0..KD {
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
            if ph.ht {
                let bits = &ph.tv[4..];
                let mut mk = Mask::new(bits, thi >> 4, false, vec![(ek, false)], sc.g, &mtmp[..1], dirty);
                let mut gate = |b: &mut B, i: Option<usize>| match i {
                    Some(i) => {
                        let pos = (k + i) as isize;
                        let x = pos - k as isize - 24;
                        mk.goto(b, Some(if x < 0 { 0 } else { x.div_euclid(16) + 1 }));
                        Some(sc.g)
                    }
                    None => {
                        mk.goto(b, None);
                        None
                    }
                };
                ripple(b, &t, &s, sc.c0, false, &mut mid, &mut gate);
            } else {
                let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| ek);
                ripple(b, &t, &s, sc.c0, false, &mut mid, &mut gate);
            }
        }
        // compare-erase
        let Some((fa, made)) = gate_le(b, sc, act, srange, 258 - k as isize) else { continue };
        {
            let tv = ph.tv.clone();
            let src = s.clone();
            // e[0..k] are erased already: from k = 8 on they are the decoder bank
            let bank: &[QubitId] = if k >= 8 { &sc.e[0..8] } else { &sc.pre1 };
            let mut mid = |b: &mut B| {
                let lane = |v: usize| if v < src.len() { Some(src[v]) } else { None };
                read_lane(b, &tv, tlo, thi, &lane, true, &[(fa, false), (sc.sv, true)], ek, bank, mtmp, dirty);
            };
            let mut gate = |_b: &mut B, _i: Option<usize>| None;
            ripple(b, &t, &s, sc.c0, true, &mut mid, &mut gate);
        }
        if made {
            gate_le_undo(b, sc, act, 258 - k as isize);
        }
    }
    ptk[2] = b.tof - pt0;
    // ---- widen: lanes [bl(r), NP-1-bl(t)) ^= sv
    {
        let c1 = Cut { v: ph.rv.clone(), a: 0, neg: false }; // l < bl(r)
        let c2 = Cut { v: ph.tv.clone(), a: (NP - 1) as isize, neg: true }; // l < NP-1-bl(t)
        let lo = rlo;
        let hi = (NP - 1).saturating_sub(tlo);
        let (f1, f2) = (sc.fa, sc.g);
        // e is erased: its lanes serve as decoder banks from here on
        walk2(b, &c1, &c2, lo, hi, f1, f2, &sc.e[0..8], &sc.e[8..16], mtmp[0], dirty, &mut |b, l| {
            mc_xor(b, &[(f1, true), (f2, false), (sc.sv, false)], p[l], &mtmp[1..], dirty);
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
        read_lane(b, &ph.rv, rlo, rhi, &lane, false, &[(act, false)], sc.sv, &sc.e[0..8], mtmp, dirty);
    }
    ptk[5] = b.tof - pt0;
    if std::env::var("FROGDROP_PROF2").is_ok() { let pc = PCNT.with(|c| { let v = *c.borrow(); *c.borrow_mut() = [0; 4]; v }); eprintln!("digprof ht {} rr {:?} tr {:?} cum {:?} readlane/mask/gate {:?}", ph.ht, ph.rr, ph.tr, ptk, pc); }
}

/// Transition adds U += g * 2^k * src (k = 0..q0.len()) on the post region, where g = q0[k] & AND(act) (& the coarse
/// mask for ring sources: allowed positions P < 266 - 16 (bl(r) >> 4)). Window positions [k, wtop).
pub fn trans_q0(b: &mut B, p: &[QubitId], q0: &[QubitId], sel: Option<&[bool]>, act: &[(QubitId, bool)],
                src: &[QubitId], wtop: usize, mask: Option<(&[QubitId], usize)>, g: QubitId, c0: QubitId,
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
        trans_one(b, &t, &s, k, false, base, mask, g, c0, temps, dirty);
    }
}

/// one masked or plain add/sub of s into t (positions k.. of the post region), write control AND(base) (& mask).
pub fn trans_one(b: &mut B, t: &[QubitId], s: &[QubitId], k: usize, sub: bool, base: Vec<(QubitId, bool)>,
                 mask: Option<(&[QubitId], usize)>, g: QubitId, c0: QubitId, temps: &[QubitId], dirty: &[QubitId]) {
    let mut mid = |_b: &mut B| {};
    match mask {
        Some((bits, amax)) => {
            let mut mk = Mask::new(bits, amax, true, base, g, temps, dirty);
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
            ripple(b, t, s, c0, sub, &mut mid, &mut gate);
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
            ripple(b, t, s, c0, sub, &mut mid, &mut gate);
        }
    }
}

/// Narrow: offset form U at width NP - B (offset bit at lane B = bl(r_j)) -> two's complement W in the region
/// [NP-1-bl(t'), NP), t' = t_{j+1}, on shots with gn. `bv` = bl(r_j) register / range, `tv` = bl(t') register / range.
pub fn narrow(b: &mut B, p: &[QubitId], bv: &[QubitId], br: (usize, usize), tv: &[QubitId], tr: (usize, usize),
              gn: QubitId, sv: QubitId, f1: QubitId, f2: QubitId, pre1: &[QubitId], pre2: &[QubitId], temps: &[QubitId],
              dirty: &[QubitId]) {
    let sign_lane = |v: usize| if v <= NP - 1 { Some(p[NP - 1 - v]) } else { None };
    read_lane(b, tv, tr.0, tr.1, &sign_lane, false, &[(gn, false)], sv, pre1, temps, dirty);
    // lanes (B, NP-1-bl(t')) ^= sv
    {
        let c1 = Cut { v: bv.to_vec(), a: 1, neg: false }; // f1 = [l <= B]
        let c2 = Cut { v: tv.to_vec(), a: (NP - 1) as isize, neg: true }; // f2 = [l < NP-1-bl(t')]
        let lo = br.0 + 1;
        let hi = (NP - 1).saturating_sub(tr.0);
        walk2(b, &c1, &c2, lo, hi, f1, f2, pre1, pre2, temps[0], dirty, &mut |b, l| {
            mc_xor(b, &[(f1, true), (f2, false), (sv, false)], p[l], &temps[1..], dirty);
        });
    }
    // lane B ^= gn & !sv
    {
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
    read_lane(b, tv, tr.0, tr.1, &sign_lane, false, &[(gn, false)], sv, pre1, temps, dirty);
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

/// Digit scratch on `free` (pool[10..] + sx): e 0..26, sv, fa, g, c0, tmp 30..32, then two decoder prefix banks of
/// m = min(8, (len - 34) / 2) lanes and one zero lane (the last lane is the caller's stepping flag). sa / sb: the
/// sz / sy registers (s = sz + sy in place).
fn dig_scr(free: &[QubitId], sa: &[QubitId], sb: &[QubitId]) -> DigScr {
    assert!(free.len() >= 38, "payload digit scratch: {} lanes", free.len());
    let m = ((free.len() - 34) / 2).min(8);
    DigScr { e: free[0..26].to_vec(), sa: sa.to_vec(), sb: sb.to_vec(), sv: free[26], fa: free[27], g: free[28],
             c0: free[29], tmp: free[30..32].to_vec(), pre1: free[32..32 + m].to_vec(),
             pre2: free[32 + m..32 + 2 * m].to_vec(), zeros: free[32 + 2 * m..33 + 2 * m].to_vec() }
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
    let mut l = vec![(fd.ph, !ht)];
    if !ht && cp.sw {
        l.push((sc.sw, true));
    }
    l
}

/// act ^= the phase's stepping flag (HT: ph & not done, done derived)
fn set_act(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, ht: bool, act: QubitId, temps: &[QubitId], dirty: &[QubitId]) {
    let lits = act_lits(fd, cp, sc, ht);
    if ht && cp.dn {
        super::frogdrop_col::mc_xor_dn(b, &lits, act, temps, dirty, fd, cp.l0, false);
    } else {
        mc_xor(b, &lits, act, temps, dirty);
    }
}

/// Stage 2.5 (after the middle swap: Q = Y): digit + offset prep of both phases.
pub fn col_digit(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    let mut free = pl.free.clone();
    free.extend_from_slice(&fd.sx);
    let ds = dig_scr(&free, &sc.sz, &fd.sy);
    let act = *free.last().unwrap();
    let atemps = [free[30], free[31]];
    let dirty = &pl.dirty;
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
        // the stepping flag's long derived-done test borrows the payload lanes (no operand of it)
        set_act(b, fd, cp, sc, ht, act, &atemps, &pl.p);
        digit(b, &pl.p, &ph, act, &ds, dirty);
        if ht {
            ht_exact_trans(b, fd, cp, &sc.sz, &pl.p, act, &ds, dirty);
        }
        set_act(b, fd, cp, sc, ht, act, &atemps, &pl.p);
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
    let wtop = 259 - (L0P + 1);
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
    let wtop = 259 - (L0P + 1);
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
    b.begin();
    super::frogdrop::msb_probe_range(b, &fd.q, 0, cp.m, &fd.sx, &sc.opre, sc.tmp, &sc.dirty);
    let probe = b.end();
    b.play(&probe, false);
    let lits = act_lits(fd, cp, sc, false);
    mc_xor(b, &lits, gn, &temps, &pl.dirty);
    let br = (cp.sz.0.max(L0P + 1), cp.sz.1.min(256));
    narrow(b, &pl.p, &sc.sz, br, &fd.sx, (1, cp.m), gn, sv, f1, f2, &pre1, &pre2, &temps, &pl.dirty);
    mc_xor(b, &lits, gn, &temps, &pl.dirty);
    b.play(&probe, true);
}

/// Stage 1.5 (sz = bl(Z) probed, Q = X): HT narrowing of the shots that stepped HT in the previous column
/// (ph & bl(Q) <= l0 & cnt <= 1): B = bl(Q) = bl(r_j) probed into sx, bl(t_{j+1}) = sz.
pub fn col_narrow_ht(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    if !cp.pht {
        return;
    }
    let f = &pl.free;
    let (gn, sv, f1, f2) = (f[0], f[1], f[2], f[3]);
    let temps = [f[4], f[5]];
    let pre1 = f[6..14].to_vec();
    let pre2 = f[14..22].to_vec();
    // the gate's helpers (clean around the narrowing) share the narrowing lanes
    let blo = cp.psy.0.max(1);
    let bhi = cp.psy.1.min(L0P);
    if blo > bhi {
        return;
    }
    b.begin();
    super::frogdrop::msb_probe_range(b, &fd.q, blo - 1, bhi, &fd.sx, &sc.opre, sc.tmp, &sc.dirty);
    let probe = b.end();
    // stepped HT last column (not done; switched-layout shots have sy > l0) or just finished (done, cnt == 1)
    let nq = fd.q.len();
    let ctop = nq - fd.cnt.len();
    let big = f[1];
    let chain = &f[2..11];
    let gt = &f[2..22];
    let l1 = vec![(fd.ph, false), (big, true)];
    let mut l2 = vec![(fd.ph, false)];
    l2.extend((super::frogdrop_col::RA..ctop).map(|l| (fd.q[l], true)));
    l2.push((fd.cnt[0], false));
    l2.extend(fd.cnt[1..].iter().map(|&x| (x, true)));
    // the payload lanes are no operand of these gates: borrow them
    let gate = |b: &mut B| {
        ge_const(b, &fd.sy, L0P as isize + 1, big, chain);
        super::frogdrop_col::mc_xor_dn(b, &l1, gn, &gt[9..20], &pl.p, fd, cp.l0, false);
        mc_xor(b, &l2, gn, &gt[9..20], &pl.p);
        ge_const(b, &fd.sy, L0P as isize + 1, big, chain);
    };
    // the gate first (it reads the counter); then done shots' counter is parked (free[22..30] = pool[32..40], clean
    // and outside the gate / narrowing / probe helpers) while
    // bl(Q) is probed: a probe bound above nq - cnt would read it (B = bl(R) for the just-finished shots)
    gate(b);
    let pd = f[22];
    let park: Vec<QubitId> = f[23..23 + fd.cnt.len()].to_vec();
    let parking = |b: &mut B| {
        super::frogdrop_col::mc_xor_dn(b, &[], pd, &gt[9..20], &pl.p, fd, cp.l0, true);
        for (i, &x) in park.iter().enumerate() { b.cswap(pd, fd.cnt[i], x); }
    };
    let unparking = |b: &mut B| {
        for (i, &x) in park.iter().enumerate() { b.cswap(pd, fd.cnt[i], x); }
        super::frogdrop_col::mc_xor_dn(b, &[], pd, &gt[9..20], &pl.p, fd, cp.l0, true);
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
    let div = {
        b.begin();
        for k in (0..KD).rev() {
            if k >= mt {
                continue;
            }
            let Some((fa, made)) = gate_le(b, sc, act, srange, 257 - k as isize) else { continue };
            let qk = q[k];
            // one compare-and-conditional-subtract ripple: the borrow into the shot's gap lane sz + h - 1 (window
            // position n - h - k - sz) is read after the up pass, and the down pass writes X -= 2^k Y only where
            // q_k = fa & !borrow (lanes past the shot's top then see 0 - 0 - 0). Y's lanes are padded with clean lanes.
            let span = mt - k;
            let bank: &[QubitId] = if k >= 8 { &q[0..8] } else { &sc.pre1 };
            let mut pads: Vec<QubitId> = sc.pre2.clone();
            pads.extend_from_slice(&sc.zeros);
            pads.extend([sc.sv, sc.g]);
            if k > 8 { pads.extend_from_slice(&q[8..k]); }
            if std::env::var("PL_OLDHTX").is_err() && span <= fd.q.len() + pads.len() {
                let t: Vec<QubitId> = (k..k + span).map(|m| fd.ring[n - 1 - m]).collect();
                let src: Vec<QubitId> = fd.q.iter().chain(pads.iter()).copied().take(span).collect();
                let base = (n - h) as isize - k as isize - 1;
                let rd = src.clone();
                let mut mid = |b: &mut B| {
                    let lane = |v: usize| {
                        let i = base - v as isize;
                        if i >= 0 && (i as usize) < rd.len() { Some(rd[i as usize]) } else { None }
                    };
                    read_lane(b, sz, szlo, szhi, &lane, true, &[(fa, false)], qk, bank, &sc.tmp, p);
                };
                let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| qk);
                ripple(b, &t, &src, sc.c0, true, &mut mid, &mut gate);
                if made {
                    gate_le_undo(b, sc, act, 257 - k as isize);
                }
                continue;
            }
            super::frogdrop_col::ring_cadd2(b, &fd.ring, &fd.q, k, mt - k, fa, true, &sc.zeros, sc.c0, sc.g, p);
            let lane = |v: usize| if v + h >= 1 && v + h - 1 < n { Some(fd.ring[v + h - 1]) } else { None };
            // the buffer lanes reach the ring top: borrow the payload lanes (no operand here) instead
            let bank: &[QubitId] = if k >= 8 { &q[0..8] } else { &sc.pre1 };
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
                gate_le_undo(b, sc, act, 257 - k as isize);
            }
        }
        b.end()
    };
    b.play(&div, false);
    let amax = syhi >> 4;
    trans_q0(b, p, q, None, &[(act, false)], &fd.ring, NP, Some((&fd.sy[4..], amax)), sc.g, sc.c0, &sc.tmp, dirty);
    b.play(&div, true);
}

/// End of a payload traversal (every shot A0 = (t_last, R, 1) after the B0 fix; R stays in Q's low lanes):
/// deferred narrowing of the shots that finished in the last column (cnt == 1), the last digit (divisor 1 = the
/// ring-top lane, |t| = Z) and the final transition U += R |t_last| (q = R exact). Leaves U in offset form with its
/// offset bit at lane 1 (bl(r_last) = 1).
pub fn pl_end(b: &mut B, fd: &Fd, cpl: &ColPar, sc: &ColScr, pl: &PlCol) {
    let n = fd.ring.len();
    let dirty = &pl.dirty;
    let (szlo, szhi) = (cpl.sz.0.max(1), cpl.sz.1.min(256));
    // sz = bl(Z): Y = 1 holds lane n - 1, Z the region below it
    let probe_z = {
        b.begin();
        super::frogdrop::msb_probe_range(b, &fd.ring, szlo - 1, szhi, &sc.sz, &sc.opre, sc.tmp, &sc.dirty);
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
            super::frogdrop::msb_probe_range(b, &fd.q, 0, KD, &fd.sx, &sc.opre, sc.tmp, &sc.dirty);
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
    let ds = dig_scr(&free, &sc.sz, &fd.sy);
    let act = fd.ph; // 1 on every shot
    let ph = Ph { ht: true, rv: fd.sy.clone(), rr: (1, 1), tv: sc.sz.clone(), tr: (szlo, szhi),
                  src_r: vec![fd.ring[n - 1], ds.zeros[0]], src_t: fd.ring.clone() };
    digit(b, &pl.p, &ph, act, &ds, dirty);
    trans_q0(b, &pl.p, &fd.q[..KD], None, &[(act, false)], &fd.ring, NP, Some((&fd.sy[4..], 0)), ds.g, ds.c0, &ds.tmp, dirty);
    b.play(&probe_z, true);
}
