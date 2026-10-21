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
/// digit register lanes: every digit e_j <= q_j, and every quotient of a model-clean shot is below 2^QB (the
/// predicted q0 cap, the last level's q = R included)
pub const KE: usize = super::pointadd_frogdrop::QB;
thread_local! {
    static D2_DIGIT_COL: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static D2_DIGIT_TARGET: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
mod prefix_cover_tests;
mod read_lane_tree;
#[cfg(test)]
mod read_lane_tree_tests;
#[cfg(test)]
mod c48_tests;
#[cfg(test)]
mod c51c_tests;
mod erase_ripple;
mod minimal3;
mod shared_size_digit;
#[cfg(test)]
mod erase_ripple_tests;

/// Largest power-of-two mask granule no larger than the physical margin.
/// With margin1, granule2 omits the source carry position for odd bit lengths.
fn ht_mask_shift(margin: isize) -> usize {
    assert!(margin >= 0, "HT source requires a nonnegative ring margin");
    if margin >= 16 { 4 } else if margin >= 8 { 3 }
    else if margin >= 4 { 2 } else if margin >= 2 { 1 } else { 0 }
}

/// The final divisor-one sentinel is not part of the arithmetic source.
/// Returned digit scratch supplies distinct zero roles at and beyond it.
fn final_transition_source(ring: &[QubitId], zeros: &[QubitId],
                           forbidden: &[QubitId]) -> Vec<QubitId> {
    assert!(ring.len() >= 257);
    let mut out = ring.to_vec();
    if ring.len() <= NP {
        let needed = NP - ring.len() + 1;
        assert!(zeros.len() >= needed);
        for (i, &z) in zeros[..needed].iter().enumerate() {
            assert!(!ring.contains(&z) && !forbidden.contains(&z));
            assert!(!zeros[..i].contains(&z));
        }
        out[ring.len() - 1] = zeros[0];
        out.extend_from_slice(&zeros[1..needed]);
    }
    out
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
    let f1 = b.tof;
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
    super::f1_profile("payload.ripple", f1, b.tof);
}

/// Query !carry after the full MAJ sweep, using two reversible gathers.
/// On extra-active shots the caller exposes original_s[v] = 0: then the
/// completed sweep holds carry(v+1) = t[v] & s[v-1]. The following source
/// bit may be arbitrary. At v=0 the clean carry-in instead gives carry=0.
/// This record preserves the exact address interval and every extra guard.
/// All off-guard data may be arbitrary; both gathers and the clean witness
/// are returned before the unchanged down sweep.
#[allow(clippy::too_many_arguments)]
fn true_carry_pair_record(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId,
    reg: &[QubitId], lo: usize, hi: usize, extra: &[(QubitId, bool)],
    e: QubitId, witness: QubitId, pre: &[QubitId], temps: &[QubitId],
    dirty: &[QubitId]) -> Option<Vec<super::builder::G>> {
    use std::collections::BTreeSet;
    if reg.is_empty() || reg.len() >= usize::BITS as usize || extra.is_empty()
        || t.len() != s.len() || t.is_empty() || lo > hi || hi > 256 {
        return None;
    }
    let end = hi.min((1usize << reg.len()) - 1).min(t.len() - 1);
    if lo > end { return None; }
    let mut ports = BTreeSet::new();
    for q in t.iter().chain(s).chain(reg).chain(extra.iter().map(|(q, _)| q))
        .chain([&c0, &e, &witness]) {
        if !ports.insert(q.0) { return None; }
    }
    // Only clean roles already used by the original decoder/AND ABI may
    // participate. A candidate with stronger geometry simply falls back.
    let h = pre.len().min(reg.len() - 1);
    let nt = temps.len().min((reg.len() - h + extra.len() + 1).saturating_sub(2));
    let mut clean = Vec::new();
    for &q in pre[..h].iter().chain(&temps[..nt]) {
        if ports.contains(&q.0) || clean.contains(&q) { return None; }
        clean.push(q);
    }
    let first = lo.max(1);
    let mut tswaps = Vec::new();
    let mut sswaps = Vec::new();
    let roots = if first <= end {
        let tl: Vec<_> = (first..=end).map(|v| (v, t[v])).collect();
        let sl: Vec<_> = (first..=end).map(|v| (v, s[v - 1])).collect();
        Some((read_lane_tree::collect_tree(reg, &tl, reg.len(), &mut tswaps),
              read_lane_tree::collect_tree(reg, &sl, reg.len(), &mut sswaps)))
    } else { None };
    // Non-root data may be borrowed while gathered, but every query control,
    // target and clean role is excluded. mc_xor's no-clean path does not
    // filter dirty donors itself. Deduplicate the supplied donor bank too.
    let mut protected: BTreeSet<_> = reg.iter().chain(extra.iter().map(|(q, _)| q))
        .chain([&c0, &e, &witness]).chain(&clean).map(|q| q.0).collect();
    if let Some((rt, rs)) = roots { protected.extend([rt.0, rs.0]); }
    let mut seen = BTreeSet::new();
    let donors: Vec<_> = dirty.iter().copied()
        .filter(|q| !protected.contains(&q.0) && seen.insert(q.0)).collect();
    if donors.len() < reg.len() + extra.len() { return None; }
    b.begin();
    if lo == 0 {
        let mut zero = Mask::new(reg, (1usize << reg.len()) - 1, true,
            extra.to_vec(), e, &clean, &donors);
        zero.toggle_range(b, 0, 0);
    }
    if let Some((rt, rs)) = roots {
        for &(c, a, d) in &tswaps { b.cswap(c, a, d); }
        for &(c, a, d) in &sswaps { b.cswap(c, a, d); }
        b.and_c(rt, rs, witness);
        let mut base = extra.to_vec();
        base.push((witness, true));
        let mut selected = Mask::new(reg, (1usize << reg.len()) - 1, true,
            base, e, &clean, &donors);
        selected.toggle_range(b, first, end);
        b.and_u(rt, rs, witness);
        for &(c, a, d) in sswaps.iter().rev() { b.cswap(c, a, d); }
        for &(c, a, d) in tswaps.iter().rev() { b.cswap(c, a, d); }
    }
    Some(b.end())
}

/// Exact carry query with a possibly live following source bit. The legacy
/// path saves original_s[v+1], since MAJ leaves s[v]=carry(v+1)^original_s[v+1].
/// At the two ring-source digit call sites upper_records exposes s[v]=0 on
/// act shots. At wide HR SZ=256, instead SY=1, the previous coefficient is
/// zero, and the sole q=1 bit parks at ring255, leaving ring256 zero too.
/// Prefer the two-gather identity there only when its complete
/// primitive Toffoli price does not increase in either playback direction.
/// The ripple and its stateful down-mask callback are generated exactly once.
#[allow(clippy::too_many_arguments)]
pub(crate) fn ripple_true_carry(b:&mut B,t:&[QubitId],s:&[QubitId],c0:QubitId,
 reg:&[QubitId],lo:usize,hi:usize,extra:&[(QubitId,bool)],e:QubitId,witness:QubitId,
 pre:&[QubitId],temps:&[QubitId],dirty:&[QubitId],gate:&mut dyn FnMut(&mut B,Option<usize>)->Option<QubitId>){
 let mut selected_gate=|b:&mut B,i:Option<usize>,_pair:bool|gate(b,i);
 ripple_true_carry_select(b,t,s,c0,reg,lo,hi,extra,e,witness,pre,temps,dirty,&mut selected_gate);
}

/// The same exact selection, exposing its public selected route to the down
/// callback. Only pair=true returns witness before the first down cell; the
/// legacy route keeps witness live until the entire ripple has returned.
#[allow(clippy::too_many_arguments)]
pub(crate) fn ripple_true_carry_select(b:&mut B,t:&[QubitId],s:&[QubitId],c0:QubitId,
 reg:&[QubitId],lo:usize,hi:usize,extra:&[(QubitId,bool)],e:QubitId,witness:QubitId,
 pre:&[QubitId],temps:&[QubitId],dirty:&[QubitId],gate:&mut dyn FnMut(&mut B,Option<usize>,bool)->Option<QubitId>){
 let bank:Vec<_>=pre.iter().copied().filter(|&q|q!=witness).collect();
 assert!(!t.contains(&witness)&&!s.contains(&witness)&&!reg.contains(&witness));
 assert!(!extra.iter().any(|&(q,_)|q==witness));assert!(witness!=c0&&witness!=e);
 assert!(!temps.contains(&witness)&&!dirty.contains(&witness));
 let next=|v:usize|s.get(v+1).copied();
 b.begin();
 read_lane(b,reg,lo,hi,&next,false,extra,witness,&bank,temps,dirty);
 let legacy_next=b.end();
 b.begin();
 let lane=|v:usize|s.get(v).copied();
 read_lane(b,reg,lo,hi,&lane,true,extra,e,&bank,temps,dirty);b.cx(witness,e);
 let legacy_mid=b.end();
 let pair=true_carry_pair_record(b,t,s,c0,reg,lo,hi,extra,e,witness,&bank,temps,dirty)
  .filter(|candidate| {
   match (read_lane_tree::prices(&legacy_next),read_lane_tree::prices(&legacy_mid),
          read_lane_tree::prices(candidate)) {
    (Some((nf,ni)),Some((mf,mi)),Some((pf,pi))) =>
     pf<=2*nf+mf && pi<=2*ni+mi && (pf<2*nf+mf || pi<2*ni+mi),
    _=>false,
   }
  });
 if let Some(pair)=pair {
  let mut mid=|b:&mut B|b.play(&pair,false);
  let mut down=|b:&mut B,i|gate(b,i,true);
  ripple(b,t,s,c0,true,&mut mid,&mut down);
 } else {
  b.play(&legacy_next,false);
  let mut mid=|b:&mut B|b.play(&legacy_mid,false);
  let mut down=|b:&mut B,i|gate(b,i,false);
  ripple(b,t,s,c0,true,&mut mid,&mut down);
  b.play(&legacy_next,false);
 }
}

/// Coarse write mask tracked on one qubit `g` during a ripple's down pass: g = AND(base) & allowed(i), where
/// allowed(i) = [a < lim(i)] (`below`) or [a >= lim(i)] (!below), a = value of `bits`, and lim(i) monotone so that
/// the allowed set only grows as i decreases. `amax` bounds a over every shot. Toggles are multi-controlled XORs of
/// base & [a == v].
#[derive(Clone)]
pub struct Mask<'a> {
    pub bits: &'a [QubitId],
    pub amax: usize,
    pub below: bool,
    pub base: Vec<(QubitId, bool)>,
    pub g: QubitId,
    pub temps: &'a [QubitId],
    pub dirty: &'a [QubitId],
    cur: Option<isize>,
    lo: usize,
    dec: Option<Dec<'a>>,
}

impl<'a> Mask<'a> {
    pub fn new(bits: &'a [QubitId], amax: usize, below: bool, base: Vec<(QubitId, bool)>, g: QubitId,
               temps: &'a [QubitId], dirty: &'a [QubitId]) -> Mask<'a> {
        Mask { bits, amax, below, base, g, temps, dirty, cur: None, lo: 0, dec: None }
    }
    pub fn with_lo(mut self, lo: usize) -> Self {
        self.lo = lo.min(self.amax);
        self
    }
    /// Decode consecutive address values with returned clean prefix cells.
    pub fn with_pre(mut self, pre: &'a [QubitId]) -> Self {
        if !pre.is_empty() {
            let h = pre.len().min(self.bits.len().saturating_sub(1));
            let used = &pre[..h];
            assert!(used.iter().all(|q| !self.bits.contains(q) && *q != self.g
                && !self.base.iter().any(|(p, _)| p == q) && !self.temps.contains(q)
                && !self.dirty.contains(q)));
            assert_eq!(used.iter().map(|q| q.0).collect::<std::collections::BTreeSet<_>>().len(), used.len());
            self.dec = Some(Dec::new(self.bits, pre));
        }
        self
    }
    fn toggle(&mut self, b: &mut B, v: usize) {
        if v >= (1usize << self.bits.len()) {
            return;
        }
        let mut lits = self.base.clone();
        if let Some(d) = &mut self.dec {
            lits.extend(d.ctrls(b, v));
            mc_xor(b, &lits, self.g, self.temps, self.dirty);
            return;
        }
        for (i, &q) in self.bits.iter().enumerate() {
            lits.push((q, (v >> i) & 1 == 0));
        }
        mc_xor(b, &lits, self.g, self.temps, self.dirty);
    }
    /// Toggle a public interval as disjoint binary-prefix matches. An aligned
    /// block of 2^k values reads only bits k..: its lower k bits are unrestricted.
    /// This is the same XOR as the original one-hot sweep on every raw value,
    /// including values above amax, and uses the same clean/dirty scratch.
    fn toggle_range(&mut self, b: &mut B, mut lo: usize, hi: usize) {
        let end = 1usize << self.bits.len();
        if lo > hi || lo >= end { return; }
        let hi = hi.min(end - 1);
        if self.dec.is_some() { for v in lo..=hi { self.toggle(b, v); } return; }
        while lo <= hi {
            let remaining = hi - lo + 1;
            let fit = (usize::BITS - 1 - remaining.leading_zeros()) as usize;
            let aligned = (lo.trailing_zeros() as usize).min(self.bits.len());
            let skip = fit.min(aligned);
            if skip == 0 {
                self.toggle(b, lo);
            } else {
                let mut lits = self.base.clone();
                for (i, &q) in self.bits.iter().enumerate().skip(skip) {
                    lits.push((q, (lo >> i) & 1 == 0));
                }
                mc_xor(b, &lits, self.g, self.temps, self.dirty);
            }
            lo += 1usize << skip;
        }
    }
    /// allowed values for limit `lim`: the v in [0, amax] with v < lim (below) or v >= lim
    fn set(&self, lim: isize) -> (usize, usize) {
        let am = self.amax as isize;
        let (lo, hi) = if self.below { (0, (lim - 1).min(am)) } else { (lim.max(0), am) };
        if lo > hi { (1, 0) } else { (lo as usize, hi as usize) }
    }
    /// End a complete prefix walk by restoring the live decoder first,
    /// then clearing its current interval with the exact binary cover.
    /// Detach Dec for the entire cover, including singleton blocks, so no
    /// prefix is silently recreated. The returned decoder is empty.
    pub(crate) fn clear_compact(&mut self, b: &mut B) {
        let mg0=b.tof;
        let old=self.cur.map(|l|self.set(l)).unwrap_or((1,0));
        if let Some(d)=&mut self.dec { d.clear(b); }
        let empty=self.dec.take();
        let lo=old.0.max(self.lo);
        if lo<=old.1 { self.toggle_range(b,lo,old.1); }
        self.dec=empty;
        self.cur=None;
        pcnt(1,b.tof-mg0);
    }
    /// move g to limit `lim` (None: clear)
    pub fn goto(&mut self, b: &mut B, lim: Option<isize>) {
        if super::frogdrop_col::c665_pool4() && lim.is_none() && self.dec.is_some() {
            // Both complete endings restore every live decoder prefix and
            // XOR the same base-gated interval into g. Price both literal
            // directions: a singleton can favor the already-held decoder.
            let mg0 = b.tof;
            let mut walked = self.clone();
            b.begin();
            walked.goto_walk(b, None);
            let walk_record = b.end();
            let mut compact = self.clone();
            b.begin();
            compact.clear_compact(b);
            let compact_record = b.end();
            let use_compact = match (read_lane_tree::prices(&walk_record),
                                     read_lane_tree::prices(&compact_record)) {
                (Some((wf, wi)), Some((cf, ci))) =>
                    cf <= wf && ci <= wi && (cf < wf || ci < wi),
                _ => false,
            };
            if use_compact {
                *self = compact;
                b.play(&compact_record, false);
            } else {
                *self = walked;
                b.play(&walk_record, false);
            }
            pcnt(1, b.tof - mg0);
            return;
        }
        self.goto_walk(b, lim);
    }
    fn goto_walk(&mut self, b: &mut B, lim: Option<isize>) {
        let mg0 = b.tof;
        let old = self.cur.map(|l| self.set(l)).unwrap_or((1, 0));
        let new = lim.map(|l| self.set(l)).unwrap_or((1, 0));
        // toggle the symmetric difference of the two value intervals
        let inr = |r: (usize, usize), v: usize| r.0 <= r.1 && v >= r.0 && v <= r.1;
        let mut start = None;
        for v in self.lo..=self.amax {
            if inr(old, v) != inr(new, v) {
                if start.is_none() { start = Some(v); }
            } else if let Some(lo) = start.take() {
                self.toggle_range(b, lo, v - 1);
            }
        }
        if let Some(lo) = start { self.toggle_range(b, lo, self.amax); }
        if lim.is_none() { if let Some(d) = &mut self.dec { d.clear(b); } }
        self.cur = lim;
        pcnt(1, b.tof - mg0);
    }
}

/// target ^= AND(extra) & (lane(v) ^ neg) for the shot's value v of `reg` in [lo, hi] (lane(v) = None: skip).
/// Full decoder prefixes `pre` (>= reg.len() - 1), temps for the AND.
fn read_lane_decoder(b: &mut B, reg: &[QubitId], lo: usize, hi: usize, lane: &dyn Fn(usize) -> Option<QubitId>, neg: bool,
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

/// Public-layout optimization of the unchanged one-hot decoder. The pruned
/// swap tree is used only when its ports satisfy the stronger disjointness
/// contract and its complete F and literal-I Toffoli prices do not increase.
/// The lane callback is a public wire map; collect it once, in original order.
pub fn read_lane(b: &mut B, reg: &[QubitId], lo: usize, hi: usize, lane: &dyn Fn(usize) -> Option<QubitId>, neg: bool,
                 extra: &[(QubitId, bool)], target: QubitId, pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) {
    read_lane_impl(b, reg, lo, hi, lane, neg, extra, target, pre, temps, dirty, false);
}

/// Use only when the public extra predicate implies an address in the full
/// contiguous lane range. Out-of-range extra-off shots keep arbitrary data.
#[allow(clippy::too_many_arguments)]
pub fn read_lane_gated(b: &mut B, reg: &[QubitId], lo: usize, hi: usize, lane: &dyn Fn(usize) -> Option<QubitId>, neg: bool,
                       extra: &[(QubitId, bool)], target: QubitId, pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) {
    assert!(!extra.is_empty());
    read_lane_impl(b, reg, lo, hi, lane, neg, extra, target, pre, temps, dirty, true);
}

#[allow(clippy::too_many_arguments)]
fn read_lane_impl(b: &mut B, reg: &[QubitId], lo: usize, hi: usize, lane: &dyn Fn(usize) -> Option<QubitId>, neg: bool,
                  extra: &[(QubitId, bool)], target: QubitId, pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId], gated: bool) {
    let rl0 = b.tof;
    let leaves: Vec<_> = (lo..=hi).take_while(|&v| v < (1usize << reg.len()))
        .filter_map(|v| lane(v).map(|q| (v, q))).collect();
    // With no clean AND prefix mc_xor dispatches directly to dirty MCX.
    // Its donor must not be a queried leaf, even on an extra-off shot.
    // The five-role digit supplies ring+Q, so filtering the complete leaf
    // set leaves a returned donor bank and keeps the same tree eligibility.
    let clean_donors: Vec<_> = if super::frogdrop_col::c665_pool4() && temps.is_empty() {
        let mut seen = std::collections::BTreeSet::new();
        dirty.iter().copied().filter(|q| *q != target && !reg.contains(q)
            && !pre.contains(q) && !extra.iter().any(|(c, _)| c == q)
            && !leaves.iter().any(|(_, l)| l == q) && seen.insert(q.0)).collect()
    } else { dirty.to_vec() };
    let dirty = &clean_donors[..];
    let cached_lane = |v: usize| leaves.binary_search_by_key(&v, |&(value, _)| value)
        .ok().map(|i| leaves[i].1);
    b.begin();
    read_lane_decoder(b, reg, lo, hi, &cached_lane, neg, extra, target, pre, temps, dirty);
    let reference = b.end();
    let full_range = gated && hi >= lo && reg.len() < usize::BITS as usize
        && hi < (1usize << reg.len()) && leaves.len() == hi - lo + 1
        && leaves.first().map(|x| x.0) == Some(lo)
        && leaves.last().map(|x| x.0) == Some(hi)
        && leaves.windows(2).all(|w| w[1].0 == w[0].0 + 1);
    let selected = if full_range {
        read_lane_tree::choose_record_gated(b, reg, &leaves, neg, extra, target, pre, temps, dirty, reference)
    } else {
        read_lane_tree::choose_record(b, reg, &leaves, neg, extra, target, pre, temps, dirty, reference)
    };
    b.play(&selected, false);
    pcnt(0, b.tof - rl0);
    super::f1_profile("payload.read_lane", rl0, b.tof);
}

/// On the N258 HT support, original s[v] is zero at the queried source
/// boundary. After the Cuccaro up pass the true carry is t[v] & s[v-1],
/// even when original s[v+1] is live. Query both lanes under the size decoder.
#[allow(clippy::too_many_arguments)]
pub(crate) fn read_lane_and2(b: &mut B, reg: &[QubitId], lo: usize, hi: usize,
    t: &[QubitId], s: &[QubitId], extra: &[(QubitId, bool)], target: QubitId,
    pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) {
    let mut dec = Dec::new(reg, pre);
    for v in lo..=hi {
        if v >= (1usize << reg.len()) { break; }
        if v >= t.len() { continue; }
        let mut controls = dec.ctrls(b, v);
        controls.extend_from_slice(extra);
        // The compare toggles for !carry, including the clean-c0 v=0 case.
        mc_xor(b, &controls, target, temps, dirty);
        if v > 0 {
            controls.extend_from_slice(&[(t[v], false), (s[v - 1], false)]);
            mc_xor(b, &controls, target, temps, dirty);
        }
    }
    dec.clear(b);
}

/// Walk lanes l in [lo, hi) with f1 = [l < c1] and f2 = [l < c2] live (cuts any value; comparators clean up),
/// per(b, l) runs per lane. f1, f2 clean before and after. pre1 / pre2 >= register lengths (decoders + chains).
pub fn walk2(b: &mut B, c1: &Cut, c2: &Cut, lo: usize, hi: usize, f1: QubitId, f2: QubitId, pre1: &[QubitId],
             pre2: &[QubitId], tmp: QubitId, dirty: &[QubitId], per: &mut dyn FnMut(&mut B, usize)) {
    walk2t(b, c1, c2, lo, hi, f1, f2, pre1, pre2, &[tmp], dirty, per)
}

/// walk2 with the decoders' AND temps `tmp` (may be empty: dirty toggles)
#[allow(clippy::too_many_arguments)]
pub fn walk2t(b: &mut B, c1: &Cut, c2: &Cut, lo: usize, hi: usize, f1: QubitId, f2: QubitId, pre1: &[QubitId],
              pre2: &[QubitId], tmp: &[QubitId], dirty: &[QubitId], per: &mut dyn FnMut(&mut B, usize)) {
    if lo >= hi {
        return;
    }
    let ch: Vec<QubitId> = pre1.iter().chain(pre2.iter()).copied().collect();
    c1.ge_dirty(b, lo as isize + 1, f1, &ch, dirty);
    c2.ge_dirty(b, lo as isize + 1, f2, &ch, dirty);
    let mut d1 = Dec::new(&c1.v, pre1);
    let mut d2 = Dec::new(&c2.v, pre2);
    for l in lo..hi {
        if l > lo {
            if let Some(v) = c1.val_at(l as isize) {
                let c = d1.ctrls(b, v);
                mc_xor(b, &c, f1, tmp, dirty);
            }
            if let Some(v) = c2.val_at(l as isize) {
                let c = d2.ctrls(b, v);
                mc_xor(b, &c, f2, tmp, dirty);
            }
        }
        per(b, l);
    }
    d1.clear(b);
    d2.clear(b);
    c1.ge_dirty(b, hi as isize, f1, &ch, dirty);
    c2.ge_dirty(b, hi as isize, f2, &ch, dirty);
}

/// One phase's view of a column for the payload.
pub struct Ph {
    pub ht: bool,
    /// The N257 relocated HR divisor has dirty passenger lanes above sz.
    pub sz_mask: bool,
    /// N257 HT presents a virtual zero adjacent to its divisor (WP-D).
    pub virt_m1: bool,
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
    /// s is formed as s - smin (every shot's s in [smin, smin + 2^|sa|)): no extra top lane for s
    pub smin: usize,
}

/// fa = act & [s <= lim] (s register value range sr); returns the control to use (act itself when always true) and
/// whether a flag was computed. None: never true. `extra`: lanes clean at this step beyond the scratch's own.
pub(crate) fn gate_le(b: &mut B, sc: &DigScr, act: QubitId, sr: (usize, usize), lim: isize, extra: &[QubitId])
           -> Option<(QubitId, bool)> {
    let g0 = b.tof;
    let r = gate_le_i(b, sc, act, sr, lim, extra);
    pcnt(2, b.tof - g0);
    r
}
fn gate_le_i(b: &mut B, sc: &DigScr, act: QubitId, sr: (usize, usize), lim: isize, extra: &[QubitId])
             -> Option<(QubitId, bool)> {
    if (sr.0 as isize) > lim {
        return None;
    }
    if (sr.1 as isize) <= lim {
        return Some((act, false));
    }
    // c = [s >= lim + 1] on the compare lane; fa = act & !c
    let (cl, chain) = gate_lanes(sc, extra);
    let k = lim + 1 - sc.smin as isize;
    s_add(b, sc, false);
    gate_cmp(b, sc, k, cl, &chain);
    b.x(cl);
    b.and_c(act, cl, sc.fa);
    b.x(cl);
    gate_cmp(b, sc, k, cl, &chain);
    s_add(b, sc, true);
    Some((sc.fa, true))
}

pub(crate) fn gate_le_undo(b: &mut B, sc: &DigScr, act: QubitId, lim: isize, extra: &[QubitId]) {
    let g0 = b.tof;
    gate_le_undo_i(b, sc, act, lim, extra);
    pcnt(2, b.tof - g0);
}
fn gate_le_undo_i(b: &mut B, sc: &DigScr, act: QubitId, lim: isize, extra: &[QubitId]) {
    let (cl, chain) = gate_lanes(sc, extra);
    let k = lim + 1 - sc.smin as isize;
    s_add(b, sc, false);
    gate_cmp(b, sc, k, cl, &chain);
    b.x(cl);
    b.and_u(act, cl, sc.fa);
    b.x(cl);
    gate_cmp(b, sc, k, cl, &chain);
    s_add(b, sc, true);
}

/// The size gate's compare lane (tmp[1], or with one temp the step's first clean extra lane, else tmp[0]) and its
/// comparator chain (the other clean lanes).
fn gate_lanes(sc: &DigScr, extra: &[QubitId]) -> (QubitId, Vec<QubitId>) {
    let cl = if sc.tmp.len() >= 2 { sc.tmp[1] } else if let Some(&x) = extra.first() { x } else { *sc.tmp.first().expect("size gate needs a clean extra or temp") };
    let chain: Vec<QubitId> = gate_chain(sc, extra).into_iter().filter(|&x| x != cl).collect();
    (cl, chain)
}

/// cl ^= [sa >= k]: the carry-chain comparator when the chain holds its carries, else the exact compact
fn gate_cmp(b: &mut B, sc: &DigScr, k: isize, cl: QubitId, chain: &[QubitId]) {
    let sa = if sc.smin == 232 { &sc.sa[..5] } else { &sc.sa[..] };
    if super::mask::ge_const_need(sa.len(), k) <= chain.len() {
        ge_const(b, sa, k, cl, chain);
    } else {
        super::frogdrop_col::ge_const_compact(b, sa, k, cl, chain, &sc.dirty);
    }
}

/// carries of the size gate's comparator: both decoder banks, tmp[0], and the zero pad, c0 and g (idle while a
/// comparator runs between the in-place adds), then the step's `extra` clean lanes
fn gate_chain(sc: &DigScr, extra: &[QubitId]) -> Vec<QubitId> {
    let mut chain = sc.pre2.clone();
    if let Some(&tmp) = sc.tmp.first() { chain.push(tmp); }
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
    if sc.smin == 232 { return; }
    b.begin();
    super::frogdrop::reg_add_into(b, &sc.sa, &sc.sb, &sc.zeros, sc.c0);
    if sc.smin > 0 {
        let a = super::frogdrop_col::rec(b, |b| super::frogdrop::add_const_dirty_exact(b, &sc.sa, sc.smin, &sc.dirty));
        b.play(&a, true);
    }
    let r = b.end();
    b.play(&r, undo);
}

fn original_size<R>(b: &mut B, offset: Option<&[super::builder::G]>, sz: &[QubitId],
                    body: impl FnOnce(&mut B) -> R) -> R {
    if let Some(r) = offset {
        super::mask::R11O11_DECCC.with(|c| c.borrow_mut().clear());
        b.play(r, true);
    }
    let result = body(b);
    if let Some(r) = offset {
        b.play(r, false);
        super::mask::R11O11_DECCC.with(|c| *c.borrow_mut() = sz[5..8].to_vec());
    }
    result
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
    // in-place digit (sc.e = [c, bank (8)] shorter than KE): e_k leaves the division at d-index bl(r) + k (zero
    // once d < 2^k r); one reflection of [bl(r), 257 - bl(t)] moves it to W-index bl(t) + 1 + k, above everything
    // the D^-1 writes up to bit k (W < 2^(bl(t) + k + 2), s + bl(e) <= 258); c holds the bit being processed
    let ip = sc.e.len() < KE;
    let ecl = |k: usize| if ip { sc.e[0] } else { sc.e[k] };
    let clean_e = |k: usize| -> Vec<QubitId> { if ip { sc.e[1..].to_vec() } else { sc.e[0..k].to_vec() } };
    let ipb: Vec<QubitId> = if ip { sc.e[1..sc.e.len().min(8)].to_vec() } else { vec![] };
    // C51C isolated S3 probe: hold the five-bit size code during gates. The
    // upper three size lanes are decoder prefixes only on act shots.
    let offset: Option<Vec<super::builder::G>> = if sc.smin == 232 {
        let r = super::frogdrop_col::rec(b, |b| {
            super::frogdrop::reg_add_into(b, &sc.sa, &sc.sb, &sc.zeros, sc.c0);
            let bias = super::frogdrop_col::rec(b, |b| super::frogdrop::add_const_dirty_exact(b, &sc.sa, 232, dirty));
            b.play(&bias, true);
        });
        b.play(&r, false);
        super::mask::R11O11_DECCC.with(|c| *c.borrow_mut() = sc.sa[5..8].to_vec());
        Some(r)
    } else { None };
    let safe_bank = |bank: Vec<QubitId>| -> Vec<QubitId> {
        if sc.smin == 232 { bank.into_iter().filter(|q| !sc.sa[5..8].contains(q)).collect() } else { bank }
    };
    // ---- long division: e_k = [d >= 2^k r_j] with d < 2^(k+1) r_j; window positions [k, k + bl(r) + 1)
    for k in (0..KE).rev() {
        // clean at this step: e[0..k] (not yet written) and sv (formed after the division)
        let mut lde = vec![sc.sv];
        lde.extend(clean_e(k));
        let Some((fa, made)) = gate_le(b, sc, act, srange, 257 - k as isize, &lde) else { continue };
        let top = (k + rhi + 1).min(NP);
        let t: Vec<QubitId> = (k..top).map(|i| p[i]).collect();
        let s: Vec<QubitId> = ph.src_r[..top - k].to_vec();
        let ek = ecl(k);
        let rv = ph.rv.clone();
        let src = s.clone();
        // e[0..k] are still clean: from k = 8 on they are the decoder bank (below: topped up with sv, g and e[0..k];
        // g is the HR mask flag, clean until the down pass)
        let mut ldb = vec![sc.sv, sc.g];
        ldb.extend_from_slice(&sc.e[0..k.min(sc.e.len())]);
        // (in place: sv tops the bank up, clean until the division's sign read)
        let bank0 = if ip { bank_of(&ipb, &[sc.sv]) } else if k >= 8 { sc.e[0..8].to_vec() }
                                else { bank_of(&sc.pre1, &ldb) };
        let bank = safe_bank(bank0);
        let mut mid = |b: &mut B| {
            let lane = |v: usize| if v < src.len() { Some(src[v]) } else { None };
            read_lane_gated(b, &rv, rlo, rhi, &lane, true, &[(fa, false)], ek, &bank, mtmp, dirty);
        };
        if ph.ht {
            let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| ek);
            original_size(b, offset.as_deref(), &sc.sa, |b|
                ripple(b, &t, &s, sc.c0, true, &mut mid, &mut gate));
        } else {
            // HR: ring-sourced divisor; the coarse boundary follows physical
            // ring length (N280 has one fewer guaranteed zero lane than N281).
            // agent_lowq_quot: with granule g = 2^gsh the guard G must satisfy 256 <= G (a live step's Z lanes pass:
            // k + i <= 256 - bl(t)) and G <= N - g (Y's lanes, ring index >= N - bl(t), are masked): G = N - 16 needs
            // ring >= 272; below it the 8-lane granule (G = N - 8, ring >= 264)
            // (agent_lowq_lane: 4-lane granule at ring 263, G = N - 4 >= 256)
            let gsh: usize = if ph.src_r.len() >= 256 + 16 { 4 } else if ph.src_r.len() >= 256 + 8 { 3 }
                              else if ph.src_r.len() >= 260 { 2 } else if ph.src_r.len() >= 258 { 1 } else { 0 };
            let bits = &ph.tv[gsh..];
            let hr_guard = ph.src_r.len() as isize - (1 << gsh);
            let mpre_hr: Vec<QubitId> = if ip { safe_bank(ipb.clone()) } else { vec![] };
            let mut mk = if ph.sz_mask {
                Mask::new(&ph.rv, rhi, false, vec![(ek, false)], sc.g, &mtmp[..1], dirty)
                    .with_lo(rlo).with_pre(&mpre_hr)
            } else {
                Mask::new(bits, thi >> gsh, true, vec![(ek, false)], sc.g, &mtmp[..1], dirty)
                    .with_lo(tlo >> gsh).with_pre(&mpre_hr)
            };
            let mut gate = |b: &mut B, i: Option<usize>| match i {
                Some(i) => {
                    let pos = (k + i) as isize;
                    mk.goto(b, Some(if ph.sz_mask { i as isize }
                        else { (hr_guard - pos).div_euclid(1 << gsh) + 1 }));
                    Some(sc.g)
                }
                None => {
                    mk.goto(b, None);
                    None
                }
            };
            original_size(b, offset.as_deref(), &sc.sa, |b| {
                if ph.src_r.len()<=258 {
                    ripple_true_carry(b,&t,&s,sc.c0,&rv,rlo,rhi,&[(fa,false)],ek,sc.sv,&bank,mtmp,dirty,&mut gate);
                } else { ripple(b, &t, &s, sc.c0, true, &mut mid, &mut gate); }
            });
        }
        if ip {
            // e_k to d-index bl(r) + k
            let lane = |v: usize| if v + k < NP { Some(p[v + k]) } else { None };
            original_size(b, offset.as_deref(), &sc.sa, |b|
                super::mid2::dec_swap(b, &ph.rv, rlo, rhi, &lane, ek, &[(fa, false)],
                                      &safe_bank(bank_of(&ipb, &[sc.sv])), mtmp, dirty));
        }
        if made {
            gate_le_undo(b, sc, act, 257 - k as isize, &lde);
        }
    }
    #[cfg(test)] super::frogdrop_col::mark(b, 30000 + 1000 * usize::from(ph.ht));
    ptk[0] = b.tof - pt0;
    if std::env::var("D2_DIGIT_STOP").ok().as_deref() == Some("divide")
        && D2_DIGIT_TARGET.with(|t| t.get()) {
        if let Some(r) = &offset { super::mask::R11O11_DECCC.with(|c| c.borrow_mut().clear()); b.play(r, true); }
        return;
    }
    // ---- sv = sign of W (lane of bit bl(t))
    {
        let lane = |v: usize| if v <= NP - 1 { Some(p[NP - 1 - v]) } else { None };
        let more: Vec<QubitId> = [sc.fa, sc.g, sc.c0].into_iter().chain(sc.zeros.iter().copied()).collect();
        let bank = if ip { bank_of(&ipb, &more) } else { bank_of(&sc.pre1, &more) };
        original_size(b, offset.as_deref(), &sc.sa, |b|
            read_lane_gated(b, &ph.tv, tlo, thi, &lane, false, &[(act, false)], sc.sv,
                            &safe_bank(bank), mtmp, dirty));
    }
    if ip {
        // e: d-index bl(r) + k -> W-index bl(t) + 1 + k, the segment [bl(r), 257 - bl(t)] reversed on act shots (in
        // the payload frame down by bl(r) it is [0, 258 - s))
        // Pool4's paid QB30 domain includes S=226/227. The column-zero
        // raw-size fallback must retain the same full reflection support
        // as the shared-size digit; the legacy layouts keep their bound.
        let paid30 = super::frogdrop_col::c665_pool4();
        let care_len = if paid30 { 32 } else { 31 };
        let dest: std::collections::BTreeSet<usize> = (0..care_len).collect();
        let rot = super::frogdrop_col::rec(b, |b| {
            super::frogdrop::rot_by_range_care(b, p, &ph.rv, rlo, rhi, true, dirty, &dest)
        });
        original_size(b, offset.as_deref(), &sc.sa, |b| b.play(&rot, false));
        s_add(b, sc, false);
        let (slo, shi) = (srange.0.max(if paid30 { 226 } else { 228 }), srange.1.min(257));
        let rb = bank_of(&ipb, &[sc.c0, sc.fa]);
        let size_bits = if sc.smin == 232 { &sc.sa[..5] } else { &sc.sa[..] };
        let mut dec = Dec::new(size_bits, &rb);
        for sv_ in slo..=shi {
            let l = 258 - sv_;
            if l < 2 { continue; }
            let mut ct = dec.ctrls(b, sv_ - sc.smin);
            ct.push((act, false));
            for i in 0..l / 2 { super::mid2::mc_swap(b, &ct, p[i], p[l - 1 - i], mtmp, dirty); }
        }
        dec.clear(b);
        s_add(b, sc, true);
        original_size(b, offset.as_deref(), &sc.sa, |b| b.play(&rot, true));
    }
    #[cfg(test)] super::frogdrop_col::mark(b, 30001 + 1000 * usize::from(ph.ht));
    ptk[1] = b.tof - pt0;
    if std::env::var("D2_DIGIT_STOP").ok().as_deref() == Some("relocate")
        && D2_DIGIT_TARGET.with(|t| t.get()) {
        if let Some(r) = &offset { super::mask::R11O11_DECCC.with(|c| c.borrow_mut().clear()); b.play(r, true); }
        return;
    }
    // ---- D^-1: W += e_k 2^k |t|; e_k ^= act & !sv & [s <= 258 - k] & [W >= 2^k |t|]
    for k in 0..KE {
        #[cfg(test)] super::frogdrop_col::mark(b, 30200 + 1000 * usize::from(ph.ht) + k);
        let top = (k + thi + 1).min(NP);
        if top <= k {
            break;
        }
        let t: Vec<QubitId> = (k..top).map(|pos| wl(p, pos)).collect();
        let s: Vec<QubitId> = ph.src_t[..top - k].to_vec();
        let ek = ecl(k);
        if ip {
            // e_k from W-index bl(t) + 1 + k on shots with s <= 257 - k (elsewhere that lane is d's or W's)
            let cle = clean_e(k);
            let Some((fr, mr)) = gate_le(b, sc, act, srange, 257 - k as isize, &cle) else { continue };
            let lane = |v: usize| if v + 1 + k < NP { Some(wl(p, v + 1 + k)) } else { None };
            original_size(b, if ph.ht { offset.as_deref() } else { None }, &sc.sa, |b|
                super::mid2::dec_swap(b, &ph.tv, tlo, thi, &lane, ek, &[(fr, false)],
                                      &if ph.ht { safe_bank(bank_of(&ipb, &[sc.c0, sc.g])) }
                                       else { bank_of(&ipb, &[sc.c0, sc.g]) }, mtmp, dirty));
            if mr { gate_le_undo(b, sc, act, 257 - k as isize, &cle); }
        }
        // Fuse only the exact ADD;compare pair. A missing size guard retains
        // the old ADD-before-continue behavior. The returned size query runs
        // before either arithmetic only when fa cannot alias their data/pads.
        let cle = clean_e(k);
        let mut deb = vec![sc.g];
        deb.extend_from_slice(&sc.e[0..k.min(sc.e.len())]);
        let pair_bank0 = if ip { if ph.ht { bank_of(&ipb, &[sc.g]) } else { ipb.clone() } }
                        else if k >= 8 { sc.e[0..8].to_vec() } else { bank_of(&sc.pre1, &deb) };
        let pair_bank = if ph.ht { safe_bank(pair_bank0) } else { pair_bank0 };
        let lim = 258 - k as isize;
        let pair_fa = if (srange.1 as isize) <= lim { act } else { sc.fa };
        let pair_extra = [(pair_fa, false), (sc.sv, true)];
        let ht_margin = if ph.virt_m1 { 1 } else { ph.src_t.len() as isize - 257 };
        // agent_lowq_quot: the 16-lane granule needs a ring margin n - 257 >= 16 (ring 273); below it the granule is
        // 8 lanes (margin >= 8, ring >= 265); agent_lowq_lane: 4 lanes at ring 264 (margin 7)
        // N260 has only three guard lanes. A four-lane prefix can admit a
        // write past that margin, so use a two-lane granule there.
        let gsh = if ph.ht { ht_mask_shift(ht_margin) } else { 1 };
        let mask_pre = if ph.ht { safe_bank(ipb.clone()) } else { ipb.clone() };
        let pair_mask = if ph.ht { Some(erase_ripple::PrefixMask {
            bits: &ph.tv[gsh..], amax: thi >> gsh, flag: sc.g, margin: ht_margin, shift: gsh,
            lo: tlo >> gsh, pre: &mask_pre,
        }) } else { None };
        let pair_eligible = (srange.0 as isize) <= lim && erase_ripple::geometry(&t, &s, sc.c0, ek,
            &ph.tv, &pair_extra, &pair_bank, mtmp, dirty, pair_mask);
        let margin1_fused = ph.ht && (ph.src_t.len() == 258 || ph.virt_m1)
            && std::env::var("R9_DIGIT_FUSED").as_deref() == Ok("1");
        if pair_eligible && (!ph.ht || ph.src_t.len() > 258 || margin1_fused) {
            let f1 = b.tof;
            let (fa, made) = gate_le(b, sc, act, srange, lim, &cle).expect("public eligible size gate");
            assert_eq!(fa, pair_fa);
            let selected = if margin1_fused {
                erase_ripple::fused_record_margin1(b, &t, &s, sc.c0, ek, &ph.tv,
                    tlo, thi, &pair_extra, &pair_bank, mtmp, dirty, pair_mask)
                    .expect("eligible N258 fused geometry")
            } else {
                erase_ripple::choose_record(b, &t, &s, sc.c0, ek, &ph.tv,
                    tlo, thi, &pair_extra, &pair_bank, mtmp, dirty, pair_mask)
            };
            #[cfg(test)] let diag=std::env::var("Q675_DIGIT_FINE").is_ok();
            #[cfg(not(test))] let diag=false;
            #[cfg(test)] if diag { erase_ripple::diagnostic_reference_play(b,&t,&s,sc.c0,ek,&ph.tv,tlo,thi,&pair_extra,&pair_bank,mtmp,dirty,pair_mask,40000+1000*usize::from(ph.ht)+10*k); }
            if !diag {
                original_size(b, if ph.ht { offset.as_deref() } else { None }, &sc.sa,
                              |b| b.play(&selected, false));
            }
            if made { gate_le_undo(b, sc, act, lim, &cle); }
            super::f1_profile("digit.inverse_fused", f1, b.tof);
            continue;
        }
        super::f1_profile(if (srange.0 as isize) > lim { "digit.inverse_missing_guard" } else { "digit.inverse_geometry_fallback" }, 0, 0);
        let f1 = b.tof;
        // Fallback add: HT ring-source writes stop before the physical
        // headroom margin plus 16 (bl(t) >> 4), preventing overlap with Z.
        {
            let mut mid = |_b: &mut B| {};
            if ph.ht {
                let bits = &ph.tv[gsh..];
                let mpre_ht: Vec<QubitId> = if ip { safe_bank(ipb.clone()) } else if k >= 8 { safe_bank(sc.e[0..8].to_vec()) } else { vec![] };
                let mut mk = Mask::new(bits, thi >> gsh, false, vec![(ek, false)], sc.g, &mtmp[..1], dirty)
                    .with_lo(tlo >> gsh).with_pre(&mpre_ht);
                let mut gate = |b: &mut B, i: Option<usize>| match i {
                    Some(i) => {
                        let pos = (k + i) as isize;
                        let x = pos - k as isize - ht_margin;
                        mk.goto(b, Some(if x < 0 { 0 } else { x.div_euclid(1 << gsh) + 1 }));
                        Some(sc.g)
                    }
                    None => {
                        mk.goto(b, None);
                        None
                    }
                };
                original_size(b, offset.as_deref(), &sc.sa,
                              |b| ripple(b, &t, &s, sc.c0, false, &mut mid, &mut gate));
            } else {
                let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| ek);
                ripple(b, &t, &s, sc.c0, false, &mut mid, &mut gate);
            }
        }
        // compare-erase
        let cle = clean_e(k);
        let Some((fa, made)) = gate_le(b, sc, act, srange, 258 - k as isize, &cle) else {
            super::f1_profile("digit.inverse_fallback", f1, b.tof);
            continue
        };
        {
            let tv = ph.tv.clone();
            let src = s.clone();
            // e[0..k] are erased already: from k = 8 on they are the decoder bank (below: topped up with g and
            // e[0..k])
            let mut deb = vec![sc.g];
            deb.extend_from_slice(&sc.e[0..k.min(sc.e.len())]);
            // (in place, HT: g tops the bank up; HR's padded source holds g)
            let bank0 = if ip { if ph.ht { bank_of(&ipb, &[sc.g]) } else { ipb.clone() } }
                                    else if k >= 8 { sc.e[0..8].to_vec() } else { bank_of(&sc.pre1, &deb) };
            let bank = if ph.ht { safe_bank(bank0) } else { bank0 };
            let mut mid = |b: &mut B| {
                let lane = |v: usize| if v < src.len() { Some(src[v]) } else { None };
                read_lane_gated(b, &tv, tlo, thi, &lane, true, &[(fa, false), (sc.sv, true)], ek, &bank, mtmp, dirty);
            };
            let mut gate = |_b: &mut B, _i: Option<usize>| None;
            original_size(b, if ph.ht { offset.as_deref() } else { None }, &sc.sa, |b| {
                if ph.ht && ph.src_t.len()<=258 {
                    ripple_true_carry(b,&t,&s,sc.c0,&tv,tlo,thi,&[(fa,false),(sc.sv,true)],ek,sc.g,&bank,mtmp,dirty,&mut gate);
                } else { ripple(b, &t, &s, sc.c0, true, &mut mid, &mut gate); }
            });
        }
        if made {
            gate_le_undo(b, sc, act, 258 - k as isize, &cle);
        }
        super::f1_profile("digit.inverse_fallback", f1, b.tof);
    }
    #[cfg(test)] super::frogdrop_col::mark(b, 30002 + 1000 * usize::from(ph.ht));
    ptk[2] = b.tof - pt0;
    if std::env::var("D2_DIGIT_STOP").ok().as_deref() == Some("inverse")
        && D2_DIGIT_TARGET.with(|t| t.get()) {
        if let Some(r) = &offset { super::mask::R11O11_DECCC.with(|c| c.borrow_mut().clear()); b.play(r, true); }
        return;
    }
    // ---- widen: lanes [bl(r), NP-1-bl(t)) ^= sv
    {
        let c1 = Cut { v: ph.rv.clone(), a: 0, neg: false }; // l < bl(r)
        let c2 = Cut { v: ph.tv.clone(), a: (NP - 1) as isize, neg: true }; // l < NP-1-bl(t)
        let lo = rlo;
        let hi = (NP - 1).saturating_sub(tlo);
        let (f1, f2) = (sc.fa, sc.g);
        // e is erased: its lanes serve as decoder banks from here on
        let eh = 1 + (sc.e.len() - 1).div_ceil(2);
        let (wb1, wb2) = if ip { (&sc.e[1..eh], &sc.e[eh..]) } else { (&sc.e[0..8], &sc.e[8..16]) };
        let wb1 = safe_bank(wb1.to_vec());
        let wb2 = safe_bank(wb2.to_vec());
        original_size(b, offset.as_deref(), &sc.sa, |b| {
            walk2(b, &c1, &c2, lo, hi, f1, f2, &wb1, &wb2, mtmp[0], dirty, &mut |b, l| {
                mc_xor(b, &[(f1, true), (f2, false), (sc.sv, false)], p[l], &mtmp[1..], dirty);
            });
        });
    }
    #[cfg(test)] super::frogdrop_col::mark(b, 30003 + 1000 * usize::from(ph.ht));
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
            let cb = if ip { &sc.e[1..] } else { &sc.e[0..16] };
            let cb = safe_bank(cb.to_vec());
            original_size(b, offset.as_deref(), &sc.sa, |b| {
                super::frogdrop::walk_cutf_capped(b, &cut, lo, hi, sc.fa, &cb, mtmp[0], dirty, |b, l, f| {
                    b.x(f);
                    b.ccx(f, act, p[l]);
                    b.x(f);
                });
            });
        }
    }
    #[cfg(test)] super::frogdrop_col::mark(b, 30004 + 1000 * usize::from(ph.ht));
    ptk[4] = b.tof - pt0;
    // ---- erase sv: sv = lane bl(r) (sign-extended W, not complemented)
    {
        let lane = |v: usize| if v < NP { Some(p[v]) } else { None };
        original_size(b, offset.as_deref(), &sc.sa, |b|
            read_lane_gated(b, &ph.rv, rlo, rhi, &lane, false, &[(act, false)], sc.sv,
                            &safe_bank(sc.e[0..sc.e.len().min(8)].to_vec()), mtmp, dirty));
    }
    #[cfg(test)] super::frogdrop_col::mark(b, 30005 + 1000 * usize::from(ph.ht));
    ptk[5] = b.tof - pt0;
    let names = ["digit.divide", "digit.sign_relocate", "digit.inverse", "digit.widen", "digit.complement", "digit.erase_sign"];
    for i in 0..6 {
        super::f1_profile(names[i], 0, ptk[i] - if i == 0 { 0 } else { ptk[i - 1] });
    }
    if std::env::var("FROGDROP_PROF2").is_ok() { let pc = PCNT.with(|c| { let v = *c.borrow(); *c.borrow_mut() = [0; 4]; v }); eprintln!("digprof ht {} rr {:?} tr {:?} cum {:?} readlane/mask/gate {:?}", ph.ht, ph.rr, ph.tr, ptk, pc); }
    if let Some(r) = &offset {
        super::mask::R11O11_DECCC.with(|c| c.borrow_mut().clear());
        b.play(r, true);
    }
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
/// A source shorter than t (plain adds only): the ripple runs on its lanes and the carry out of them (s's last lane
/// between the passes) is added into t's rest by an increment under AND(base).
pub fn trans_one(b: &mut B, t: &[QubitId], s: &[QubitId], k: usize, sub: bool, base: Vec<(QubitId, bool)>,
                 mask: Option<(&[QubitId], usize)>, g: QubitId, c0: QubitId, temps: &[QubitId], dirty: &[QubitId]) {
    trans_one_guard(b, t, s, k, sub, base, mask, g, c0, temps, dirty, 265);
}

/// The HT ring-source mask's coarse boundary follows the physical ring size.
/// The 280-lane layout has one fewer guaranteed zero lane before the top operand.
pub fn trans_one_guard(b: &mut B, t: &[QubitId], s: &[QubitId], k: usize, sub: bool, base: Vec<(QubitId, bool)>,
                       mask: Option<(&[QubitId], usize)>, g: QubitId, c0: QubitId, temps: &[QubitId],
                       dirty: &[QubitId], guard: isize) {
    let f1 = b.tof;
    let ls = s.len().min(t.len());
    let (t, th) = t.split_at(ls);
    let s = &s[..ls];
    assert!(th.is_empty() || (!sub && mask.is_none()));
    let inc: Vec<(QubitId, bool)> = base.iter().copied().chain(s.last().map(|&x| (x, false))).collect();
    let mut mid = |b: &mut B| {
        for i in (0..th.len()).rev() {
            let mut l = inc.clone();
            l.extend(th[..i].iter().map(|&x| (x, false)));
            mc_xor(b, &l, th[i], temps, dirty);
        }
    };
    match mask {
        Some((bits, amax)) => {
            let mut mk = Mask::new(bits, amax, true, base, g, temps, dirty);
            let mut gate = |b: &mut B, i: Option<usize>| match i {
                Some(i) => {
                    let pos = (k + i) as isize;
                    mk.goto(b, Some((guard - pos).div_euclid(16) + 1));
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
    super::f1_profile(if mask.is_some() { "payload.transition_masked" } else { "payload.transition_plain" }, f1, b.tof);
}

/// Narrow: offset form U at width NP - B (offset bit at lane B = bl(r_j)) -> two's complement W in the region
/// [NP-1-bl(t'), NP), t' = t_{j+1}, on shots with gn. `bv` = bl(r_j) register / range, `tv` = bl(t') register / range.
pub fn narrow(b: &mut B, p: &[QubitId], bv: &[QubitId], br: (usize, usize), tv: &[QubitId], tr: (usize, usize),
              gn: QubitId, sv: QubitId, f1: QubitId, f2: QubitId, pre1: &[QubitId], pre2: &[QubitId], temps: &[QubitId],
              dirty: &[QubitId]) {
    let sign_lane = |v: usize| if v <= NP - 1 { Some(p[NP - 1 - v]) } else { None };
    read_lane_gated(b, tv, tr.0, tr.1, &sign_lane, false, &[(gn, false)], sv, pre1, temps, dirty);
    // lanes (B, NP-1-bl(t')) ^= sv
    {
        let c1 = Cut { v: bv.to_vec(), a: 1, neg: false }; // f1 = [l <= B]
        let c2 = Cut { v: tv.to_vec(), a: (NP - 1) as isize, neg: true }; // f2 = [l < NP-1-bl(t')]
        let lo = br.0 + 1;
        let hi = (NP - 1).saturating_sub(tr.0);
        let (wt, rt) = temps.split_at(temps.len().min(1));
        walk2t(b, &c1, &c2, lo, hi, f1, f2, pre1, pre2, wt, dirty, &mut |b, l| {
            mc_xor(b, &[(f1, true), (f2, false), (sv, false)], p[l], rt, dirty);
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
    read_lane_gated(b, tv, tr.0, tr.1, &sign_lane, false, &[(gn, false)], sv, pre1, temps, dirty);
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
    dig_scr_z(free, sa, sb, dirty, false)
}

/// short in-place digit scratch: no zero lane (the caller pads with g; s = sz + sy needs no pad: sa, sb 8 lanes)
fn dig_zpad() -> bool {
    std::env::var("FD_DIG_ZPAD").map(|v| v == "1").unwrap_or(DIG_ZPAD)
}
pub const DIG_ZPAD: bool = true;

fn dig_scr_z(free: &[QubitId], sa: &[QubitId], sb: &[QubitId], dirty: &[QubitId], zpad: bool) -> DigScr {
    // e in the pool when it fits (two temps when the pool allows, else one: the size gates then compare on a
    // clean step lane), else the in-place digit: e = [c, bank (8)]
    let ip = std::env::var("FD_DIGIT_IP").is_ok() || free.len() < KE + 6;
    let short = ip && free.len() < 15;
    let zpad = zpad && short;
    let nz = if zpad { 0 } else { 1 };
    // (a 12-lane scratch, Scheme G's 13-lane pool: e = [c, five prefixes]; FD_DIG_NE overrides)
    let mut ne = if ip { 9.min(free.len().saturating_sub(5 + nz)) } else { KE };
    if short { if let Some(v) = std::env::var("FD_DIG_NE").ok().and_then(|v| v.parse::<usize>().ok()) {
        if v + 5 + nz <= free.len() { ne = v; } } }
    assert!(ne >= 4 || (std::env::var("FD_DIG_FREE").is_ok() && ne >= 2), "payload digit scratch: {} lanes", free.len());
    let nt = if short { free.len() - ne - 4 - nz } else if free.len() >= ne + 7 { 2 } else { 1 };
    let n0 = ne + 4 + nt + nz;
    assert!(free.len() >= n0, "payload digit scratch: {} lanes", free.len());
    let m = ((free.len() - n0) / 2).min(8);
    assert!(nt >= 1 && free.len() >= n0, "payload digit scratch: {} lanes", free.len());
    DigScr { e: free[0..ne].to_vec(), sa: sa.to_vec(), sb: sb.to_vec(), sv: free[ne], fa: free[ne + 1],
             g: free[ne + 2], c0: free[ne + 3], tmp: free[ne + 4..ne + 4 + nt].to_vec(),
             zeros: free[ne + 4 + nt..n0].to_vec(),
             pre1: free[n0..n0 + m].to_vec(), pre2: free[n0 + m..n0 + 2 * m].to_vec(), dirty: dirty.to_vec(),
             smin: 0 }
}

/// `base` topped up with `more` (distinct lanes, at most 8: a decoder holds at most 8 prefix levels)
pub(crate) fn bank_of(base: &[QubitId], more: &[QubitId]) -> Vec<QubitId> {
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

pub(crate) fn pad(v: &[QubitId], zeros: &[QubitId], len: usize) -> Vec<QubitId> {
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

/// act ^= the phase's stepping flag (HT: ph & not done, done derived; dq columns: & !(sz < sy), the delayed shots'
/// no-step column, with the in-place compare on `c0`)
fn set_act(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, ht: bool, act: QubitId, temps: &[QubitId], dirty: &[QubitId],
           c0: QubitId) {
    let mut lits = act_lits(fd, cp, sc, ht);
    let lt = if ht && cp.dq {
        let lt = super::arith::up_m(b, &sc.sz, &fd.sy, c0, true);
        b.play(&lt, false);
        lits.push((fd.sy[fd.sy.len() - 1], true));
        Some(lt)
    } else { None };
    if ht && cp.dn {
        super::frogdrop_col::mc_xor_dn(b, &lits, act, temps, dirty, fd, cp.l0, false);
    } else {
        mc_xor(b, &lits, act, temps, dirty);
    }
    if let Some(lt) = lt { b.play(&lt, true); }
}

/// Stage 2.5 (after the middle swap: Q = Y): digit + offset prep of both phases.
pub fn col_digit(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    col_digit_phase(b, fd, cp, sc, pl, None);
}

/// At margin zero HR keeps the pre-digit payload until its V plays have
/// finished. The HT pass still runs at the original stage-2.5 boundary.
pub fn col_digit_phase(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol,
                       only_ht: Option<bool>) {
    col_digit_phase_hr(b, fd, cp, sc, pl, only_ht, HrDigit::None);
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum HrDigit { None, Fixed, Cross { act_freed: bool } }

/// Exact scatter under a public raw-address interval. Reversible gather
/// brings lane(value) to root, the binary interval predicate toggles root,
/// and the inverse gather returns every other lane. No extra clean owner is
/// needed; existing globally clean AND temps and arbitrary-restored dirty
/// donors keep their original contracts on every address, including invalid.
#[allow(clippy::too_many_arguments)]
fn scatter_range_record(b: &mut B, reg: &[QubitId], leaves: &[(usize, QubitId)],
    extra: &[(QubitId, bool)], temps: &[QubitId], dirty: &[QubitId])
    -> Option<Vec<super::builder::G>> {
    use std::collections::BTreeSet;
    if reg.is_empty() || reg.len() >= usize::BITS as usize || leaves.is_empty()
        || leaves.last()?.0 >= 1usize << reg.len()
        || leaves.windows(2).any(|p| p[0].0 + 1 != p[1].0) { return None; }
    let mut ports = BTreeSet::new();
    if !reg.iter().chain(leaves.iter().map(|(_, q)| q))
        .chain(extra.iter().map(|(q, _)| q)).chain(temps)
        .all(|q| ports.insert(q.0)) { return None; }
    let mut seen = BTreeSet::new();
    let donors: Vec<_> = dirty.iter().copied()
        .filter(|q| !ports.contains(&q.0) && seen.insert(q.0)).collect();
    if donors.len() < reg.len() + extra.len() { return None; }
    let mut swaps = Vec::new();
    let root = super::midg::swap_tree(reg, leaves, reg.len(), &mut swaps);
    Some(super::frogdrop_col::rec(b, |b| {
        for &(c, x, y) in &swaps { b.cswap(c, x, y); }
        let mut range = Mask::new(reg, leaves.last().unwrap().0, true,
            extra.to_vec(), root, temps, &donors);
        range.toggle_range(b, leaves[0].0, leaves.last().unwrap().0);
        for &(c, x, y) in swaps.iter().rev() { b.cswap(c, x, y); }
    }))
}

fn choose_outer_record(reference: Vec<super::builder::G>, candidate: Vec<super::builder::G>)
    -> Vec<super::builder::G> {
    match (read_lane_tree::prices(&reference), read_lane_tree::prices(&candidate)) {
        (Some((of, oi)), Some((nf, ni)))
            if nf <= of && ni <= oi && (nf < of || ni < oi) => candidate,
        _ => reference,
    }
}

/// Exact raw-size virtual-leading-one shuttle. The inherited two decoder
/// sweeps implement save ^= !selected; selected ^= save. Gather that same
/// selected lane once, apply the two gates under the exact address interval,
/// and undo every swap. Even an invalid address or an arbitrary incoming save
/// has the same permutation. Both clean helpers are returned before the digit.
#[allow(clippy::too_many_arguments)]
fn top_shuttle_record(b: &mut B, reg: &[QubitId], ring: &[QubitId],
    lo: usize, hi: usize, save: QubitId, clean: &[QubitId], dirty: &[QubitId],
    reference: Vec<super::builder::G>) -> Vec<super::builder::G> {
    use std::collections::BTreeSet;
    if clean.len() < 2 || reg.is_empty() || reg.len() >= usize::BITS as usize
        || lo == 0 || lo > hi || hi > ring.len() { return reference; }
    let hi = hi.min((1usize << reg.len()) - 1);
    if lo > hi { return reference; }
    let (flag, tmp) = (clean[0], clean[1]);
    let mut ports = BTreeSet::new();
    if !reg.iter().chain(ring).chain([&save, &flag, &tmp])
        .all(|q| ports.insert(q.0)) { return reference; }
    // Mask only reads the address. Dirty operands can be arbitrary, but its
    // target, clean temp, address and saved value are never borrowed.
    let mut seen = BTreeSet::new();
    let donors: Vec<_> = dirty.iter().copied().filter(|q|
        !reg.contains(q) && *q != flag && *q != tmp && *q != save
        && seen.insert(q.0)).collect();
    if donors.len() < reg.len() { return reference; }
    let leaves: Vec<_> = (lo..=hi).map(|v| (v, ring[v - 1])).collect();
    let mut swaps = Vec::new();
    let root = super::midg::swap_tree(reg, &leaves, reg.len(), &mut swaps);
    let guard = super::frogdrop_col::rec(b, |b| {
        let temp = [tmp];
        let mut range = Mask::new(reg, hi, true, vec![], flag, &temp, &donors);
        range.toggle_range(b, lo, hi);
    });
    let candidate = super::frogdrop_col::rec(b, |b| {
        b.play(&guard, false);
        for &(c, x, y) in &swaps { b.cswap(c, x, y); }
        b.x(root); b.ccx(flag, root, save); b.x(root);
        b.ccx(flag, save, root);
        for &(c, x, y) in swaps.iter().rev() { b.cswap(c, x, y); }
        b.play(&guard, true);
    });
    choose_outer_record(reference, candidate)
}

/// The outer digit wrapper has already established act and completed the
/// original top/adjacent shuttles with both size words raw. Its returned
/// ordinary owners are in raw_free; raw SZ high lanes are not yet scratch.
/// Restore that exact raw layout before any of those outer records is undone.
#[allow(clippy::too_many_arguments)]
fn pool5_shared_digit(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr,
    pl: &PlCol, ph: &Ph, act: QubitId, raw_free: &[QubitId], hr_mode: HrDigit) {
    assert_eq!(fd.ring.len(), 257);
    assert_eq!(fd.sy.len(), 8);
    assert!((8..=9).contains(&sc.sz.len()));
    assert!(!sc.sz.contains(&act) && !fd.sy.contains(&act));
    assert!(ph.ht || hr_mode != HrDigit::None,
        "N257 HR shared digit requires its delayed top/adjacent shuttles");
    let mut raw_bank = Vec::new();
    for &q in raw_free {
        assert!(q != act && !sc.sz.contains(&q) && !fd.sy.contains(&q));
        if !raw_bank.contains(&q) { raw_bank.push(q); }
    }
    let with_sources = |zview: Vec<QubitId>, zero: QubitId| -> Ph {
        if ph.ht {
            Ph { ht: true, sz_mask: ph.sz_mask, virt_m1: ph.virt_m1,
                rv: fd.sy.clone(), rr: ph.rr, tv: zview, tr: ph.tr,
                src_r: pad(&fd.q, &[zero], ph.rr.1 + 1), src_t: fd.ring.clone() }
        } else {
            Ph { ht: false, sz_mask: ph.sz_mask, virt_m1: ph.virt_m1,
                rv: zview, rr: ph.rr, tv: fd.sy.clone(), tr: ph.tr,
                src_r: fd.ring.clone(), src_t: pad(&fd.q, &[zero], ph.tr.1 + 1) }
        }
    };
    if sc.sz.len() == 9 {
        // Only the public column-zero endpoint needs the ninth raw size bit.
        // Its Q[SYhi+1..121) bank is ample after Q118/119/120 exclusions.
        // Keep the original raw digit, including its real ninth-size pad.
        assert_eq!(cp.col, 0);
        assert!(raw_bank.len() >= 10, "wide raw digit lacks public Q funding");
        let raw = dig_scr_z(&raw_bank, &sc.sz, &fd.sy, &pl.dirty, false);
        assert!(!raw.zeros.is_empty());
        let raw_ph = with_sources(sc.sz.clone(), raw.zeros[0]);
        digit(b, &pl.p, &raw_ph, act, &raw, &pl.dirty);
        return;
    }
    let mut inner_bank = raw_bank;
    for &q in &sc.sz[5..8] {
        // Fixed HR moved act to raw.sw and returned the flight before
        // decoding raw SZ. Thus its SX5/SX7 are ordinary size owners here;
        // the encoder returns both globally, just like the third high bit.
        let reserved = matches!(hr_mode, HrDigit::Cross { act_freed: false }) && q == fd.sx[5];
        if !reserved && !inner_bank.contains(&q) { inner_bank.push(q); }
    }
    // Preserve all six roles whenever the existing public bank funds them.
    // The five-role lowering is needed only at the hard crossing columns.
    let five = super::frogdrop_col::c665_pool4() && inner_bank.len() < 6;
    let nroles = if five { 5 } else { 6 };
    assert!(inner_bank.len() >= nroles, "shared-size digit needs {} returned owners at col {}", nroles, cp.col);
    // Beyond the ordinary roles, keep at most seven returned owners as
    // in-place decoder prefixes. They never hold quotient bits: e[0] is
    // still the sole quotient flight and e.len() remains strictly below KE.
    let npre = if super::frogdrop_col::c665_pool4() && !five {
        (inner_bank.len() - nroles).min(7)
    } else { 0 };
    inner_bank.truncate(nroles + npre);
    for (i, q) in inner_bank.iter().enumerate() {
        assert!(!inner_bank[..i].contains(q) && *q != act
            && !sc.sz[..5].contains(q) && !fd.sy.contains(q));
    }
    let mut donors = pl.dirty.clone();
    if five { donors.extend(&fd.ring); donors.extend(&fd.q); }
    let mut seen = std::collections::BTreeSet::new();
    let dirty: Vec<_> = donors.into_iter().filter(|q|
        !inner_bank.contains(q) && *q != act && (!five || *q != fd.ph)
        && !sc.sz.contains(q) && !fd.sy.contains(q) && seen.insert(q.0)).collect();
    assert!(dirty.len() >= 2);
    // The inherited post-stage-2 domain includes inactive classes and done:
    // 226<=SZ+SY<=257. Therefore all three encoded high owners are globally
    // zero here, not merely conditionally zero under this phase's act.
    let encode = super::shared_size::encode_record(b, &sc.sz, &fd.sy, &dirty);
    b.play(&encode, false);
    let e: Vec<_> = std::iter::once(inner_bank[0])
        .chain(inner_bank[nroles..].iter().copied()).collect();
    assert!(e.len() <= 8 && e.len() < KE);
    let inner = DigScr { e, sa: sc.sz[..5].to_vec(), sb: fd.sy.clone(),
        sv: inner_bank[1], fa: inner_bank[2], g: inner_bank[3], c0: inner_bank[4],
        tmp: if five { vec![] } else { vec![inner_bank[5]] }, pre1: vec![], pre2: vec![], zeros: vec![],
        dirty: dirty.clone(), smin: 0 };
    let zview: Vec<_> = sc.sz[..5].iter().chain(fd.sy[5..8].iter()).copied().collect();
    let inner_ph = with_sources(zview, inner.g);
    // Public Q loans start strictly above Y's padded source. The sole
    // permitted source/helper alias is the inherited virtual zero pad g.
    assert!(inner_bank.iter().all(|q| !pl.p.contains(q)
        && (*q == inner.g || (!inner_ph.src_r.contains(q) && !inner_ph.src_t.contains(q)))));
    let flip = if five {
        super::shared_size::view_record_two_clean(b, &sc.sz[..5], &fd.sy[..5],
            &fd.sy[5..8], inner.c0, inner.g, &dirty)
    } else {
        super::shared_size::view_record(b, &sc.sz[..5], &fd.sy[..5],
            &fd.sy[5..8], inner.tmp[0], &[inner.g, inner.c0], &dirty)
    };
    let mut is_z = false;
    let mut view = |b: &mut B, want_z: bool| {
        if is_z != want_z { b.play(&flip, false); is_z = want_z; }
    };
    shared_size_digit::digit(b, &pl.p, &inner_ph, act, fd.ph, &inner, &dirty, &mut view);
    drop(view);
    assert!(!is_z, "shared digit must return the full raw Y-size view");
    // Every inner role, including each loaned SZ-high lane, is returned.
    b.play(&encode, true);
}

/// The N257 delayed HR digit uses one saved Z top and one saved adjacent bit.
/// The mode fixes lane ownership at the digit boundary, while Q scratch starts
/// at the same clean Y bound used by B11A D1.
pub fn col_digit_phase_hr(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol,
                          only_ht: Option<bool>, hr_mode: HrDigit) {
    let minimal = super::frogdrop_col::c666_pool5();
    if minimal {
        assert_eq!(fd.ring.len(), 257);
        assert!(super::mid2::enabled(), "shared-size digit requires the Scheme G middle");
    }
    let col = D2_DIGIT_COL.with(|c| {
        if only_ht == Some(false) { c.get().checked_sub(1).expect("HR digit requires stage-2 column") }
        else { let v = c.get(); c.set(v + 1); v }
    });
    let target = std::env::var("D2_DIGIT_STOP_COL").ok().and_then(|s| s.parse::<usize>().ok()) == Some(col);
    D2_DIGIT_TARGET.with(|t| t.set(target));
    let mut free = pl.free.clone();
    free.extend_from_slice(&fd.sx);
    // (lowq-672 pool9: the Q lanes above the column's largest Y, below the done counter, are clean at stage 2.5)
    if (super::frogdrop_col::pool9() || minimal) && !cp.dn {
        let top = fd.q.len() - fd.cnt.len();
        let lo = (cp.sy.1 + 1).min(top);
        free.extend(&fd.q[lo..top]);
    }
    // Done-column Q above both the Y bound and the counter is clean during digit.
    // Put at most nine such lanes first so dig_scr_z binds them to e.
    if (super::frogdrop_col::pool9() || minimal) && cp.dn {
        let top = fd.q.len() - fd.cnt.len();
        let lo = (cp.sy.1 + 1).max(super::frogdrop_col::RB).min(top);
        let ql: Vec<QubitId> = fd.q[lo..top].to_vec();
        let k = ql.len().min(9);
        let mut ordered: Vec<QubitId> = ql[..k].to_vec();
        ordered.extend(&free);
        ordered.extend(&ql[k..]);
        free = ordered;
    }
    let seven = std::env::var("FD_DIG_FREE").ok().and_then(|v| v.parse::<usize>().ok()) == Some(7);
    // The derived-done flag reads Q[64..120], so a seven-lane digit may not
    // borrow those Q lanes as its set_act temp, even when their value is zero.
    if seven && !minimal && sc.sz.len() == super::frogdrop_col::SZB && cp.sz.1 > 255 { free = fd.sx[..7].to_vec(); }
    if minimal { free.retain(|q| !sc.sz.contains(q)); }
    let ht_adj_save = if fd.ring.len() == 257 && cp.ht && only_ht != Some(false) {
        let top = fd.q.len() - fd.cnt.len();
        let lo = (cp.sy.1 + 1).min(top);
        let save = if top > lo { fd.q[120] } else { fd.sx[0] };
        free.retain(|&q| q != save);
        Some(save)
    } else { None };
    // At N257 the fixed/parked HR stage may store its top in-place quotient
    // bit over Z's leading one. Save the quotient value in a clean digit lane,
    // expose the virtual leading one for the digit, then undo both operations.
    // Keep the saved bit out of dig_scr_z's pool for the whole digit lifetime.
    let top_save = if fd.ring.len() == 257 && only_ht == Some(false) {
        assert!(hr_mode != HrDigit::None, "N257 HR digit requires an owner mode");
        let top = fd.q.len() - fd.cnt.len();
        let lo = (cp.sy.1 + 1).min(top);
        if hr_mode == HrDigit::Fixed { free.retain(|&q| q != fd.sx[5] && q != fd.sx[7]); }
        if let HrDigit::Cross { act_freed: false } = hr_mode {
            free.retain(|&q| q != fd.sx[5]);
        }
        let save = if top - lo >= 2 { fd.q[120] } else { fd.sx[0] };
        free.retain(|&q| q != save);
        Some(save)
    } else { None };
    let upper_saves: Vec<(usize, QubitId)> = if fd.ring.len() == 257 && only_ht == Some(false) {
        let top = fd.q.len() - fd.cnt.len();
        let lo = (cp.sy.1 + 1).min(top);
        let save = if top - lo >= 2 { fd.q[119] } else { fd.ph };
        free.retain(|&q| q != save);
        vec![(0, save)]
    } else { vec![] };
    // s = sz + sy is formed as s - 2 on sz's own eight lanes; a wide-sz
    // column (sz holds the sw lane) takes its stepping flag from the last free lane
    let wide = sc.sz.len() > super::frogdrop_col::SZB;
    if wide && super::frogdrop_col::c55_pool8() {
        free.retain(|q| !sc.sz.contains(q));
    }
    assert!(!wide || !cp.sw);
    #[cfg(test)]
    let offset_test = std::env::var("C51_OFFSET_COL").ok()
        .and_then(|v| v.parse::<usize>().ok()) == Some(cp.col);
    #[cfg(not(test))]
    let offset_test = false;
    let offset_mode = !minimal && fd.ring.len() == 257 && !wide
        && (super::frogdrop_col::c55_pool8() || !super::frogdrop_col::pool9() || offset_test);
    // a ninth lane for s when the pool allows it; else s - 2 (every shot's s lies in [228, 257]) on sz's eight
    // The seven-lane form uses the eight-bit s-2 representation and its
    // zero-pad fallback even when the pre-truncation Q bank could fund a ninth.
    let ninth = !minimal && !offset_mode && (wide || (!seven && free.len() >= KE + 8));
    let extra = if ninth { Some(free.pop().unwrap()) } else { None };
    // FD_DIG_FREE: a lane budget for the digit scratch (the rest of the free lanes stay |0>)
    let mut raw_free = Vec::new();
    if minimal {
        let qtop = fd.q.len() - fd.cnt.len();
        free.retain(|&lane| lane != sc.sw);
        let mut seen = std::collections::BTreeSet::new();
        free.retain(|q| seen.insert(q.0));
        // Q above the public Y+padding bound and below the counter is
        // globally zero. Done detection reads that zero prefix, so it must
        // not supply an OUTER predicate helper. The inner digit starts only
        // after set_act and both adjacent/top shuttles have returned their
        // helpers, and returns this entire bank before they are undone.
        if super::frogdrop_col::c665_pool4() { raw_free = free.clone(); }
        free.retain(|&lane| !(cp.dn && fd.q[super::frogdrop_col::RA..qtop].contains(&lane)));
        // Keep this entire public raw-clean bank for the inner digit. The
        // outer predicates/shuttles use up to the original three clean roles;
        // with pool4 their two live roles suffice and the decoder uses two prefixes.
        if !super::frogdrop_col::c665_pool4() { raw_free = free.clone(); }
        let outer_roles = if super::frogdrop_col::c665_pool4() && free.len() < 3 { 2 } else { 3 };
        assert!(free.len() >= outer_roles, "raw digit needs {} clean owners at col {}", outer_roles, cp.col);
        free.truncate(outer_roles);
    } else if offset_mode {
        // At pool8 sc.sw may be one of fd.sx. The guarded digit uses it as
        // act throughout its lifetime, so it cannot also occupy a bank role.
        // A done-column act test reads all of Q[RA..top); its accumulator
        // cannot be a borrowed digit helper from that same control prefix.
        let qtop = fd.q.len() - fd.cnt.len();
        free.retain(|&lane| lane != sc.sw && !(cp.dn && fd.q[super::frogdrop_col::RA..qtop].contains(&lane)));
        assert!(free.len() >= 6, "guarded offset needs six ordinary free lanes at col {}", cp.col);
        free.truncate(6);
    } else if !wide {
        if let Some(k) = std::env::var("FD_DIG_FREE").ok().and_then(|v| v.parse::<usize>().ok()) { free.truncate(k); }
    }
    #[cfg(test)] if only_ht == Some(false) && free.len() < 10 {
        eprintln!("C42_HR_DIGSCR col={} free={} qlo={} sy={:?} sz={:?} sx={:?} save={:?}",
                  cp.col, free.len(), cp.sy.1 + 1, cp.sy, cp.sz, fd.sx, top_save);
    }
    let mut sa = sc.sz.clone();
    if !wide { if let Some(x) = extra { sa.push(x); } }
    let bank: Vec<QubitId> = if offset_mode {
        std::iter::once(free[0]).chain(sc.sz[5..8].iter().copied())
            .chain(free[1..].iter().copied()).collect()
    } else { free.clone() };
    let mut ds = if minimal {
        // Raw outer predicates/shuttles use fa and c0; sv is never read here.
        // Two owners suffice in pool4 (sv aliases c0), and a third owner
        // remains an optional decoder prefix. Bind inner roles after encoding.
        DigScr { e: vec![free[0]], sa: sa.clone(), sb: fd.sy.clone(), sv: free[1],
            fa: free[0], g: free[0], c0: free[if free.len() == 2 { 1 } else { 2 }],
            tmp: vec![], pre1: vec![], pre2: vec![],
            zeros: vec![], dirty: pl.dirty.clone(), smin: 0 }
    } else { dig_scr_z(&bank, &sa, &fd.sy, &pl.dirty, !ninth && dig_zpad()) };
    // (no zero lane: Q's pad past lane 127 is g, idle in the ripples that read the padded source: HR's D^-1 and
    // compare-erase, HT's division)
    let zl: Vec<QubitId> = if ds.zeros.is_empty() { vec![ds.g] } else { ds.zeros.clone() };
    if offset_mode { ds.smin = 232; }
    else if !ninth { ds.smin = 2; }
    // The stepping flag lives on the sw lane. sw = !ph & [sz <= l0] (stage 1b) is a function of ph and sz, both
    // unchanged through stage 2.5 and zero on ph shots: HR's flag !ph & !sw is sw ^ !ph in place; HT erases sw,
    // holds its own flag there and recomputes sw.
    let act = if !minimal && wide && !(super::frogdrop_col::c55_pool8() && cp.col == 0 && hr_mode == HrDigit::Fixed) {
        extra.unwrap()
    } else { sc.sw };
    assert!(!bank.contains(&act), "digit act must stay outside the guarded bank at col {}", cp.col);
    let atemps = ds.tmp.clone();
    let dirty = &pl.dirty;
    let hr_flag = |b: &mut B| {
        b.x(fd.ph);
        b.cx(fd.ph, act);
        b.x(fd.ph);
    };
    // sw ^= !ph & [sz <= l0] (dl columns: & [sz <= sy], the in-place compare on c0) on the clean digit scratch (fa
    // the compare, e[0..8] its carries)
    let sw_toggle = |b: &mut B| {
        if !cp.sw {
            return;
        }
        let sw_chain: &[QubitId] = if minimal || offset_mode { &[] } else { &ds.e[0..ds.e.len().min(8)] };
        super::frogdrop_col::ge_cd(b, &sc.sz, cp.l0 as isize + 1, ds.fa, sw_chain, dirty);
        if cp.dl {
            let gt = super::arith::up_m(b, &fd.sy, &sc.sz, ds.c0, true);
            b.play(&gt, false);
            mc_xor(b, &[(ds.fa, true), (fd.ph, true), (sc.sz[sc.sz.len() - 1], true)], sc.sw, &[], dirty);
            b.play(&gt, true);
        } else {
            mc_xor(b, &[(ds.fa, true), (fd.ph, true)], sc.sw, &[], dirty);
        }
        super::frogdrop_col::ge_cd(b, &sc.sz, cp.l0 as isize + 1, ds.fa, sw_chain, dirty);
    };
    for ht in [false, true] {
        if only_ht.is_some() && only_ht != Some(ht) { continue; }
        if (!ht && !cp.hr) || (ht && !cp.ht) {
            continue;
        }
        let ph = if !ht {
            let rr = (cp.sz.0.max(if cp.dl { cp.dlr } else { L0P + 1 }), cp.sz.1.min(256));
            let tr = (cp.sy.0.max(1), cp.sy.1.min(257 - (L0P + 1)));
            if rr.0 > rr.1 || tr.0 > tr.1 {
                continue;
            }
            Ph { ht, sz_mask: fd.ring.len() == 257, virt_m1: false,
                 rv: sc.sz.clone(), rr, tv: fd.sy.clone(), tr, src_r: fd.ring.clone(),
                 src_t: if minimal { fd.q[..(tr.1 + 1).min(fd.q.len())].to_vec() }
                        else { pad(&fd.q, &zl, tr.1 + 1) } }
        } else {
            let rr = (cp.sy.0.max(1), cp.sy.1.min(L0P));
            let tr = (cp.sz.0.max(1), cp.sz.1.min(256));
            if rr.0 > rr.1 || tr.0 > tr.1 {
                continue;
            }
            Ph { ht, sz_mask: false, virt_m1: ht_adj_save.is_some(),
                 rv: fd.sy.clone(), rr, tv: sc.sz.clone(), tr,
                 src_r: if minimal { fd.q[..(rr.1 + 1).min(fd.q.len())].to_vec() }
                        else { pad(&fd.q, &zl, rr.1 + 1) },
                 src_t: fd.ring.clone() }
        };
        // the stepping flag's long derived-done test borrows the payload lanes (no operand of it)
        if ht {
            sw_toggle(b);
            set_act(b, fd, cp, sc, ht, act, &atemps, &pl.p, ds.c0);
        } else if !(super::frogdrop_col::c55_pool8() && hr_mode == HrDigit::Fixed) {
            // In pool8 the fixed middle's sx5 already holds the HR act.
            hr_flag(b);
        }
        #[cfg(test)] if !ht { super::frogdrop_col::mark(b, 39905); }
        let top_record = if !ht {
            top_save.map(|save| {
                let np = sc.sz.len() - 1;
                assert!(free.len() >= np || offset_mode || minimal, "N257 HR top decoder needs {} clean lanes", np);
                let bank = &free[..np.min(free.len())];
                let reference = super::frogdrop_col::rec(b, |b| {
                    let mut dec = Dec::new(&sc.sz, bank);
                    for v in cp.sz.0.max(1)..=cp.sz.1.min(257) {
                        if v >= (1usize << sc.sz.len()) { break; }
                        let mut c = dec.ctrls(b, v);
                        c.push((fd.ring[v - 1], true));
                        let helpers: Vec<QubitId> = if offset_mode || minimal { dirty.iter().copied()
                            .filter(|q| *q != save && !c.iter().any(|&(w, _)| w == *q)).collect() }
                            else { vec![] };
                        mc_xor(b, &c, save, &[], &helpers);
                    }
                    dec.clear(b);
                    let mut dec = Dec::new(&sc.sz, bank);
                    for v in cp.sz.0.max(1)..=cp.sz.1.min(257) {
                        if v >= (1usize << sc.sz.len()) { break; }
                        let mut c = dec.ctrls(b, v);
                        c.push((save, false));
                        let target = fd.ring[v - 1];
                        let helpers: Vec<QubitId> = if offset_mode || minimal { dirty.iter().copied()
                            .filter(|q| *q != target && !c.iter().any(|&(w, _)| w == *q)).collect() }
                            else { vec![] };
                        mc_xor(b, &c, target, &[], &helpers);
                    }
                    dec.clear(b);
                });
                if minimal && super::frogdrop_col::c665_pool4() {
                    top_shuttle_record(b, &sc.sz, &fd.ring, cp.sz.0.max(1),
                        cp.sz.1.min(257), save, &free, dirty, reference)
                } else { reference }
            })
        } else { None };
        if let Some(r) = &top_record { b.play(r, false); }
        #[cfg(test)] if !ht { super::frogdrop_col::mark(b, 39902); }
        let adjacent_saves: Vec<(usize, QubitId)> = if ht {
            ht_adj_save.map(|save| vec![(0, save)]).unwrap_or_default()
        } else { upper_saves.clone() };
        let upper_records: Vec<_> = adjacent_saves.iter().map(|&(off, save)| {
            let leaves: Vec<(usize, QubitId)> = (cp.sz.0.max(1)..=cp.sz.1.min(256 - off))
                .map(|v| (v, fd.ring[v + off])).collect();
            assert!(!leaves.is_empty());
            let mut swaps = vec![];
            let root = super::midg::swap_tree(&sc.sz, &leaves, sc.sz.len(), &mut swaps);
            super::frogdrop_col::rec(b, |b| {
                for &(bit, left, right) in &swaps { b.cswap(bit, left, right); }
                let mut controls = vec![(act, false)];
                if !ht && sc.sz.len() == 9 { controls.push((sc.sz[8], true)); }
                let helpers: Vec<QubitId> = dirty.iter().copied()
                    .filter(|&q| q != root && q != save && !controls.iter().any(|&(w, _)| w == q)).collect();
                super::mid2::mc_swap(b, &controls, root, save, &[], &helpers);
                for &(bit, left, right) in swaps.iter().rev() { b.cswap(bit, left, right); }
            })
        }).collect();
        for r in &upper_records { b.play(r, false); }
        if minimal { pool5_shared_digit(b, fd, cp, sc, pl, &ph, act, &raw_free, hr_mode); }
        else { digit(b, &pl.p, &ph, act, &ds, dirty); }
        #[cfg(test)] if !ht { super::frogdrop_col::mark(b, 39904); }
        for r in upper_records.iter().rev() { b.play(r, true); }
        #[cfg(test)] if !ht { super::frogdrop_col::mark(b, 39903); }
        if let Some(r) = &top_record { b.play(r, true); }
        if ht && !super::mid2::enabled() {
            ht_exact_trans(b, fd, cp, &sc.sz, &pl.p, act, &ds, dirty);
        }
        if ht {
            set_act(b, fd, cp, sc, ht, act, &atemps, &pl.p, ds.c0);
            sw_toggle(b);
        } else if !(super::frogdrop_col::c55_pool8() && hr_mode == HrDigit::Fixed) {
            hr_flag(b);
        }
    }
    D2_DIGIT_TARGET.with(|t| t.set(false));
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

/// Narrowing lanes (gn, sv, f1, f2, temps, pre1, pre2) and the preceding bl probe's prefixes / temp: the slim lanes
/// (SLIM), else the free lanes (decoder banks of up to eight lanes each from what the pool leaves) and the column's
/// opre / tmp
#[allow(clippy::type_complexity)]
fn slim_narrow_lanes(sc: &ColScr, pl: &PlCol) -> (QubitId, QubitId, QubitId, QubitId, Vec<QubitId>, Vec<QubitId>,
                                                  Vec<QubitId>, Vec<QubitId>, QubitId) {
    if super::frogdrop_col::SLIM {
        let s = &sc.slim;
        (s[0], s[1], s[2], s[3], vec![], vec![], vec![], s[1..4].to_vec(), s[0])
    } else {
        let f = &pl.free;
        let m = ((f.len() - 6) / 2).min(8);
        (f[0], f[1], f[2], f[3], vec![f[4], f[5]], f[6..6 + m].to_vec(), f[6 + m..6 + 2 * m].to_vec(), sc.opre.clone(),
         sc.tmp)
    }
}

/// Stage 9 (Q = X_new = t_{j+1}, sz = bl(r_j) still live): HR narrowing; sx probes bl(X_new).
pub fn col_narrow_hr(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    if !cp.hr {
        return;
    }
    if narrow_delta() {
        col_narrow_hr_delta(b, fd, cp, sc, pl);
        return;
    }
    // SLIM: the slim lanes are the flags; sy (bl of the ring-top Y, which lies in [bl(Z) + h, n) after the wide
    // swap) is erased by the masked probe stage 2 uses for T and restored afterwards, so its lanes hold the probe's
    // and the narrowing's decoder prefixes and temps (sx is clean around the erase and the restore)
    let (gn, sv, f1, f2, mut temps, mut pre1, mut pre2, mut popre, ptmp) = slim_narrow_lanes(sc, pl);
    let sy_rec = if super::frogdrop_col::SLIM {
        let s = &sc.slim;
        let n = fd.ring.len();
        let rev: Vec<QubitId> = fd.ring.iter().rev().copied().collect();
        let cutr = super::frogdrop::Cut { v: sc.sz.clone(), a: (n - cp.h) as isize, neg: true };
        let opre = vec![s[3]];
        b.begin();
        super::frogdrop::msb_probe_cut_range(b, &rev, &cutr, n - cp.h - cp.sz.1, n - cp.h - cp.sz.0, 0,
                                             cp.sy.1.min(n), &fd.sy, s[2], &fd.sx[..4], &opre, s[0], s[1], &sc.dirty);
        let r = b.end();
        b.play(&r, true);
        if std::env::var_os("D3_TRACE_PHASE").is_some() { super::frogdrop_col::mark(b, 811); }
        let y = &fd.sy;
        popre = y[..y.len() - 1].to_vec();
        temps = y[0..2].to_vec();
        pre1 = y[2..5].to_vec();
        pre2 = y[5..8].to_vec();
        Some(r)
    } else { None };
    b.begin();
    super::frogdrop::msb_probe_range(b, &fd.q, 0, cp.m, &fd.sx, &popre, ptmp, &sc.dirty);
    let probe = b.end();
    b.play(&probe, false);
    if std::env::var_os("D3_TRACE_PHASE").is_some() { super::frogdrop_col::mark(b, 812); }
    let lits = act_lits(fd, cp, sc, false);
    mc_xor(b, &lits, gn, &temps, &pl.dirty);
    if std::env::var_os("D3_TRACE_PHASE").is_some() { super::frogdrop_col::mark(b, 813); }
    let br = (cp.sz.0.max(L0P + 1), cp.sz.1.min(256));
    narrow(b, &pl.p, &sc.sz, br, &fd.sx, (1, cp.m), gn, sv, f1, f2, &pre1, &pre2, &temps, &pl.dirty);
    if std::env::var_os("D3_TRACE_PHASE").is_some() { super::frogdrop_col::mark(b, 814); }
    mc_xor(b, &lits, gn, &temps, &pl.dirty);
    if std::env::var_os("D3_TRACE_PHASE").is_some() { super::frogdrop_col::mark(b, 815); }
    b.play(&probe, true);
    if std::env::var_os("D3_TRACE_PHASE").is_some() { super::frogdrop_col::mark(b, 816); }
    if let Some(r) = sy_rec { b.play(&r, false); }
    if std::env::var_os("D3_TRACE_PHASE").is_some() { super::frogdrop_col::mark(b, 817); }
}

/// col_narrow_hr by the size identity: an HR stepping shot holds Q = X_new = t_{j+1} with sz = bl(r_j), so
/// bl(t_{j+1}) = 257 - sz - d, d in {0, 1}, d = 1 iff Q's bit 256 - sz is clear. narrow()'s sign lane is then
/// NP-1-bl(t_{j+1}) = sz + 1 + d, its walk region (sz, sz + 1 + d) is lane sz + 1 alone (d = 1) and lane B is sz:
/// no bl(X_new) probe into sx, no sy erase. Lanes: gn (s[0]), sv (s[1]), d' = gn & Q[256 - sz] (s[2]), FD_NHT_TMP
/// temps (s[3]), FD_NHT_PRE decoder prefixes (sx).
fn col_narrow_hr_delta(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    let s = &sc.slim;
    let (gn, sv, dl) = (s[0], s[1], s[2]);
    let nt = if super::frogdrop_col::c665_pool4() { 0 } else { nht_param("FD_NHT_TMP", 1).min(1) };
    let np = if super::frogdrop_col::c666_pool5() { 0 }
             else { nht_param("FD_NHT_PRE", 7).min(fd.sx.len()).min(sc.sz.len() - 1) };
    let temps: Vec<QubitId> = s[3..3 + nt].to_vec();
    let pre: Vec<QubitId> = fd.sx[..np].to_vec();
    let nq = fd.q.len();
    // HR stepping shots have bl(r_j) > l0
    let vlo = cp.sz.0.max(L0P + 1);
    let vhi = cp.sz.1.min(256);
    let lits = act_lits(fd, cp, sc, false);
    mc_xor(b, &lits, gn, &temps, &pl.dirty);
    if vlo <= vhi {
        let qlane = |v: usize| if 256 - v < nq { Some(fd.q[256 - v]) } else { None };
        // d' = gn & Q[256 - sz]
        read_lane_gated(b, &sc.sz, vlo, vhi, &qlane, false, &[(gn, false)], dl, &pre, &temps, &pl.p);
        // sv = gn & W's sign: lane sz + 1 + d (d = 0 <=> d' = 1 on gn shots)
        let lane_d0 = |v: usize| if v + 1 <= NP - 1 { Some(pl.p[v + 1]) } else { None };
        let lane_d1 = |v: usize| if v + 2 <= NP - 1 { Some(pl.p[v + 2]) } else { None };
        let sv_rd = |b: &mut B| {
            read_lane_gated(b, &sc.sz, vlo, vhi, &lane_d0, false, &[(dl, false)], sv, &pre, &temps, &pl.dirty);
            read_lane_gated(b, &sc.sz, vlo, vhi, &lane_d1, false, &[(gn, false), (dl, true)], sv, &pre, &temps, &pl.dirty);
        };
        sv_rd(b);
        // lane sz + 1 ^= sv on d = 1 shots (sv already carries gn); lane sz ^= gn & !sv
        let reference = super::frogdrop_col::rec(b, |b| {
            let mut dec = Dec::new(&sc.sz, &pre);
            for v in vlo..=vhi {
                let c = dec.ctrls(b, v);
                if v + 1 <= NP - 1 {
                    let mut c1 = c.clone();
                    c1.extend([(dl, true), (sv, false)]);
                    mc_xor(b, &c1, pl.p[v + 1], &temps, &pl.dirty);
                }
                let mut c2 = c.clone();
                c2.extend([(gn, false), (sv, true)]);
                mc_xor(b, &c2, pl.p[v], &temps, &pl.dirty);
            }
            dec.clear(b);
        });
        let selected = if super::frogdrop_col::c665_pool4() {
            let l1: Vec<_> = (vlo..=vhi).filter(|&v| v + 1 < NP)
                .map(|v| (v, pl.p[v + 1])).collect();
            let l2: Vec<_> = (vlo..=vhi).map(|v| (v, pl.p[v])).collect();
            match (scatter_range_record(b, &sc.sz, &l1, &[(dl, true), (sv, false)], &temps, &pl.dirty),
                   scatter_range_record(b, &sc.sz, &l2, &[(gn, false), (sv, true)], &temps, &pl.dirty)) {
                (Some(a), Some(c)) => {
                    // Controls are unchanged and the two selected targets
                    // differ, so the inherited interleaved writes commute.
                    let candidate = super::frogdrop_col::rec(b, |b| {
                        b.play(&a, false); b.play(&c, false);
                    });
                    choose_outer_record(reference, candidate)
                }
                _ => reference,
            }
        } else { reference };
        b.play(&selected, false);
        sv_rd(b);
        read_lane_gated(b, &sc.sz, vlo, vhi, &qlane, false, &[(gn, false)], dl, &pre, &temps, &pl.p);
    }
    mc_xor(b, &lits, gn, &temps, &pl.dirty);
}

/// Stage 1.5 (sz = bl(Z) probed, Q = X): HT narrowing of the shots that stepped HT in the previous column
/// (ph & bl(Q) <= l0 & cnt <= 1): B = bl(Q) = bl(r_j) probed into sx, bl(t_{j+1}) = sz.
pub fn col_narrow_ht(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    if !cp.pht {
        return;
    }
    if narrow_delta() {
        col_narrow_ht_delta(b, fd, cp, sc, pl);
        return;
    }
    if super::frogdrop_col::SLIM {
        col_narrow_ht_slim(b, fd, cp, sc, pl);
        return;
    }
    // Runs before stage 1b: the sw lane is clean and joins the free lanes. gn and the parked counter (pd, park)
    // stay live across the bl(Q) probe, so they avoid its helpers (opre, tmp); the narrowing lanes and the gate's
    // helpers may share them.
    let slim = super::frogdrop_col::SLIM;
    let mut nf = vec![sc.sw];
    nf.extend_from_slice(if slim { &sc.slim } else { &pl.free });
    let ph_lanes: Vec<QubitId> = if slim { vec![] } else { sc.opre.iter().copied().chain([sc.tmp]).collect() };
    let np: Vec<QubitId> = nf.iter().copied().filter(|x| !ph_lanes.contains(x)).collect();
    let gn = np[0];
    let nq = fd.q.len();
    let ctop = nq - fd.cnt.len();
    // done shots exist only in dn columns (elsewhere the parking is the identity). SLIM: only a probe that reaches
    // the counter lanes parks, each bit swapped under the done test A = ph & Q[RA..ctop) == 0 (no flag lane)
    let bhi0 = cp.psy.1.min(L0P);
    let slim_park = slim && cp.dn && bhi0 > ctop;
    let (pd, park): (Option<QubitId>, Vec<QubitId>) =
        if slim { (None, if slim_park { np[1..1 + cp.cntw.min(fd.cnt.len())].to_vec() } else { vec![] }) }
        else if cp.dn { (Some(np[1]), np[2..2 + cp.cntw.min(fd.cnt.len())].to_vec()) } else { (None, vec![]) };
    let rest: Vec<QubitId> = nf.iter().copied().filter(|&x| x != gn && Some(x) != pd && !park.contains(&x)).collect();
    let (sv, f1, f2) = (rest[0], rest[1], rest[2]);
    let temps: Vec<QubitId> = if slim { vec![rest[3]] } else { vec![rest[3], rest[4]] };
    let pb = &rest[temps.len() + 3..];
    let m1 = pb.len().div_ceil(2).min(8);
    let pre1 = pb[..m1].to_vec();
    let pre2 = pb[m1..(m1 + 8).min(pb.len())].to_vec();
    let blo = cp.psy.0.max(1);
    let bhi = cp.psy.1.min(L0P);
    if blo > bhi {
        return;
    }
    // the probe runs while gn and the parked counter are live (SLIM: on the remaining lanes)
    let (popre, ptmp) = if slim { (rest[1..].to_vec(), rest[0]) } else { (sc.opre.clone(), sc.tmp) };
    b.begin();
    super::frogdrop::msb_probe_range(b, &fd.q, blo - 1, bhi, &fd.sx, &popre, ptmp, &sc.dirty);
    let probe = b.end();
    // stepped HT last column (not done; switched-layout shots have sy > l0) or just finished (done, cnt == 1)
    // gate helpers (all clean around it): big, its compare chain, and AND temps past the chain
    let big = sv;
    let gchain: Vec<QubitId> = if slim { nf.iter().copied().filter(|&x| x != gn && x != big).take(7).collect() }
                               else { rest[1..8].to_vec() };
    let chain = &gchain[..];
    let mut gtl: Vec<QubitId> = if slim { nf.iter().copied().filter(|&x| x != gn && x != big).skip(7).collect() }
                                else { rest[8..].to_vec() };
    gtl.extend(pd);
    gtl.extend_from_slice(&park);
    gtl.truncate(11);
    let gt: &[QubitId] = &gtl;
    // parking's AND temps: everything but gn and pd is clean then
    let pt: Vec<QubitId> = rest.iter().copied().take(11).collect();
    let mut l1 = vec![(fd.ph, false), (big, true)];
    if cp.dq { l1.push((sc.sz[sc.sz.len() - 1], false)); }
    let mut l2 = vec![(fd.ph, false)];
    l2.extend((super::frogdrop_col::RA..ctop).map(|l| (fd.q[l], true)));
    l2.push((fd.cnt[0], false));
    l2.extend(fd.cnt[1..].iter().map(|&x| (x, true)));
    // the payload lanes are no operand of these gates: borrow them
    let gate = |b: &mut B| {
        ge_const(b, &fd.sy, L0P as isize + 1, big, chain);
        super::frogdrop_col::mc_xor_dn(b, &l1, gn, gt, &pl.p, fd, cp.l0, false);
        mc_xor(b, &l2, gn, gt, &pl.p);
        ge_const(b, &fd.sy, L0P as isize + 1, big, chain);
    };
    // the gate first (it reads the counter); then done shots' counter is parked (pd, park: clean and outside the
    // narrowing / probe helpers) while
    // bl(Q) is probed: a probe bound above nq - cnt would read it (B = bl(R) for the just-finished shots)
    gate(b);
    let a_lits: Vec<(QubitId, bool)> = std::iter::once((fd.ph, false))
        .chain((super::frogdrop_col::RA..ctop).map(|l| (fd.q[l], true))).collect();
    let aswap = |b: &mut B, i: usize, x: QubitId, inverse: bool| {
        let mut l1 = a_lits.clone(); l1.push((fd.cnt[i], false));
        let mut l2 = a_lits.clone(); l2.push((x, false));
        if !inverse { mc_xor(b, &l1, x, &[], &pl.p); mc_xor(b, &l2, fd.cnt[i], &[], &pl.p); }
        else { mc_xor(b, &l2, fd.cnt[i], &[], &pl.p); mc_xor(b, &l1, x, &[], &pl.p); }
    };
    let parking = |b: &mut B| {
        if slim_park { for (i, &x) in park.iter().enumerate() { aswap(b, i, x, false); } return; }
        let Some(pd) = pd else { return };
        super::frogdrop_col::mc_xor_dn(b, &[], pd, &pt, &pl.p, fd, cp.l0, true);
        for (i, &x) in park.iter().enumerate() { b.cswap(pd, fd.cnt[i], x); }
    };
    let unparking = |b: &mut B| {
        if slim_park { for (i, &x) in park.iter().enumerate().rev() { aswap(b, i, x, true); } return; }
        let Some(pd) = pd else { return };
        for (i, &x) in park.iter().enumerate() { b.cswap(pd, fd.cnt[i], x); }
        super::frogdrop_col::mc_xor_dn(b, &[], pd, &pt, &pl.p, fd, cp.l0, true);
    };
    parking(b);
    b.play(&probe, false);
    let tr = (cp.sz.0.max(1), cp.sz.1.min(256));
    narrow(b, &pl.p, &fd.sx, (blo, bhi), &sc.sz, tr, gn, sv, f1, f2, &pre1, &pre2, &temps, &pl.dirty);
    b.play(&probe, true);
    unparking(b);
    gate(b);
}

/// col_narrow_ht on the sw lane (gn; clean before stage 1b) and the four slim lanes (sv, f1, f2 and a temp). A bl(Q)
/// probe that reaches the counter lanes reads them only on shots with A = ph & Q[RA..ctop) == 0 clear (A held in the
/// temp's lane; done shots have A set and Q < 2^RB): no parking. The gate's compare chain and AND temps are in sx,
/// clean before the probe and after its inverse.
/// The size identity form of the HT narrowing (FD_NARROW_DELTA / NARROW_DELTA): every narrowing shot stepped HT, so
/// Q = r_j and Z = t_{j+1} (just-finished shots: Q = R = r_{N-2}, Z = t_{N-1}) with r_j |t_{j+1}| in (p/2, p), hence
/// B = bl(r_j) = 257 - sz - d, d in {0, 1}, d = 1 iff Q's bit 256 - sz is clear. narrow()'s walk region
/// (B, NP-1-sz) is then lane 257 - sz alone (d = 1) and its lane B is 257 - sz - d: no B register, no bl(Q) probe,
/// no sy erase. Lanes: gn (sw), d' = gn & Q[256 - sz] (s[0]), sv (s[1]), FD_NHT_TMP AND temps (s[2..]),
/// FD_NHT_PRE decoder prefixes (sx); every other sx / slim lane stays |0>.
pub const NARROW_DELTA: bool = false;
pub fn narrow_delta() -> bool {
    std::env::var("FD_NARROW_DELTA").map(|v| v == "1").unwrap_or(NARROW_DELTA)
}
fn nht_param(name: &str, dflt: usize) -> usize {
    std::env::var(name).ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(dflt)
}
fn col_narrow_ht_delta(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    use super::frogdrop_col::{ge_cd, mc_xor_dn, RA};
    let s = &sc.slim;
    let gn = sc.sw;
    let (dl, sv) = (s[0], s[1]);
    let nt = nht_param("FD_NHT_TMP", 2).min(if super::frogdrop_col::c665_pool4() { 1 } else { 2 });
    let np = if super::frogdrop_col::c666_pool5() { 0 }
             else { nht_param("FD_NHT_PRE", 7).min(fd.sx.len()).min(sc.sz.len() - 1) };
    let temps: Vec<QubitId> = s[2..2 + nt].to_vec();
    let pre: Vec<QubitId> = fd.sx[..np].to_vec();
    let ctop = fd.q.len() - fd.cnt.len();
    let nq = fd.q.len();
    let blo = cp.psy.0.max(1);
    let bhi = cp.psy.1.min(L0P);
    if blo > bhi {
        return;
    }
    // sz on the narrowing shots: 257 - bhi - 1 ..= 257 - blo
    let vlo = cp.sz.0.max(1).max(256 - bhi);
    let vhi = cp.sz.1.min(256).min(257 - blo);
    // the gate: ph & sy <= l0 & (not done or cnt == 1) (& sz <= 127 is excluded in dq columns), on gn
    let big = sv;
    let mut l1 = vec![(fd.ph, false), (big, true)];
    if cp.dq { l1.push((sc.sz[sc.sz.len() - 1], false)); }
    let mut l2 = vec![(fd.ph, false)];
    l2.extend((RA..ctop).map(|l| (fd.q[l], true)));
    l2.push((fd.cnt[0], false));
    l2.extend(fd.cnt[1..].iter().map(|&x| (x, true)));
    let gate = |b: &mut B| {
        ge_cd(b, &fd.sy, L0P as isize + 1, big, &pre, &pl.p);
        mc_xor_dn(b, &l1, gn, &temps, &pl.p, fd, cp.l0, false);
        mc_xor(b, &l2, gn, &temps, &pl.p);
        ge_cd(b, &fd.sy, L0P as isize + 1, big, &pre, &pl.p);
    };
    gate(b);
    super::frogdrop_col::mark(b, 2004);
    if vlo <= vhi {
        let qlane = |v: usize| if 256 - v < nq { Some(fd.q[256 - v]) } else { None };
        let sign_lane = |v: usize| if v <= NP - 1 { Some(pl.p[NP - 1 - v]) } else { None };
        // d' = gn & Q[256 - sz] (d = !d' on gn shots); sv = gn & W's sign at position sz
        read_lane_gated(b, &sc.sz, vlo, vhi, &qlane, false, &[(gn, false)], dl, &pre, &temps, &pl.p);
        read_lane_gated(b, &sc.sz, vlo, vhi, &sign_lane, false, &[(gn, false)], sv, &pre, &temps, &pl.dirty);
        // lane 257 - sz ^= sv ^ d' (d = 1: the walk's lane gets sv; d = 0: it is lane B, gets !sv);
        // lane 256 - sz ^= gn & !d' & !sv (d = 1: lane B)
        let reference = super::frogdrop_col::rec(b, |b| {
            let mut dec = Dec::new(&sc.sz, &pre);
            for v in vlo..=vhi {
                let c = dec.ctrls(b, v);
                if v <= 256 {
                    let mut c1 = c.clone();
                    c1.extend([(gn, false), (dl, true), (sv, true)]);
                    mc_xor(b, &c1, pl.p[256 - v], &temps, &pl.dirty);
                }
                if v <= 257 {
                    b.cx(dl, sv);
                    let mut c2 = c.clone();
                    c2.push((sv, false));
                    mc_xor(b, &c2, pl.p[257 - v], &temps, &pl.dirty);
                    b.cx(dl, sv);
                }
            }
            dec.clear(b);
        });
        let selected = if super::frogdrop_col::c665_pool4() {
            let l1: Vec<_> = (vlo..=vhi).filter(|&v| v <= 256)
                .map(|v| (v, pl.p[256 - v])).collect();
            let l2: Vec<_> = (vlo..=vhi).filter(|&v| v <= 257)
                .map(|v| (v, pl.p[257 - v])).collect();
            match (scatter_range_record(b, &sc.sz, &l1, &[(gn, false), (dl, true), (sv, true)], &temps, &pl.dirty),
                   scatter_range_record(b, &sc.sz, &l2, &[(sv, false)], &temps, &pl.dirty)) {
                (Some(a), Some(c)) => {
                    // Per-value CX(dl,sv) pairs cancel between orthogonal
                    // address writes. One pair conjugates their full sum.
                    let candidate = super::frogdrop_col::rec(b, |b| {
                        b.play(&a, false);
                        b.cx(dl, sv); b.play(&c, false); b.cx(dl, sv);
                    });
                    choose_outer_record(reference, candidate)
                }
                _ => reference,
            }
        } else { reference };
        b.play(&selected, false);
        read_lane_gated(b, &sc.sz, vlo, vhi, &sign_lane, false, &[(gn, false)], sv, &pre, &temps, &pl.dirty);
        read_lane_gated(b, &sc.sz, vlo, vhi, &qlane, false, &[(gn, false)], dl, &pre, &temps, &pl.p);
    }
    super::frogdrop_col::mark(b, 2005);
    gate(b);
}

fn col_narrow_ht_slim(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: &PlCol) {
    use super::frogdrop_col::{probe_gated, RA};
    let s = &sc.slim;
    let gn = sc.sw;
    let (af, sv, f1, f2) = (s[0], s[1], s[2], s[3]);
    let ctop = fd.q.len() - fd.cnt.len();
    let blo = cp.psy.0.max(1);
    let bhi = cp.psy.1.min(L0P);
    if blo > bhi {
        return;
    }
    let gate_a = cp.dn && bhi > ctop;
    // sy (bl of the ring top, which lies in [bl(Z) + h, n): stage 2's swap and T probe rely on the same region) is
    // read only by the gate: erased by the masked probe after it and restored before its inverse, its lanes hold the
    // probe's and the narrowing's decoder prefixes and temps
    let n = fd.ring.len();
    let rev: Vec<QubitId> = fd.ring.iter().rev().copied().collect();
    let cutr = super::frogdrop::Cut { v: sc.sz.clone(), a: (n - cp.h) as isize, neg: true };
    let mut eopre = vec![af];
    eopre.extend(&fd.sx[4..]);
    b.begin();
    super::frogdrop::msb_probe_cut_range(b, &rev, &cutr, n - cp.h - cp.sz.1, n - cp.h - cp.sz.0, 0,
                                         (cp.xw.max(cp.sy.1) + 1).min(n), &fd.sy, f1, &fd.sx[..4], &eopre, sv, f2,
                                         &sc.dirty);
    let sy_rec = b.end();
    let y = &fd.sy;
    let mut temps: Vec<QubitId> = y[0..2].to_vec();
    if !gate_a { temps.push(af); }
    let (pre1, pre2) = (y[2..5].to_vec(), y[5..8].to_vec());
    let popre: Vec<QubitId> = y[..y.len() - 1].to_vec();
    b.begin();
    if gate_a {
        probe_gated(b, &fd.q, ctop.max(blo - 1), bhi, &fd.sx, &[(af, true)], &popre, sv, &[], &sc.dirty);
        if blo - 1 < ctop { super::frogdrop::msb_probe_range(b, &fd.q, blo - 1, ctop, &fd.sx, &popre, sv, &sc.dirty); }
    } else {
        super::frogdrop::msb_probe_range(b, &fd.q, blo - 1, bhi, &fd.sx, &popre, sv, &sc.dirty);
    }
    let probe = b.end();
    let big = sv;
    let chain: Vec<QubitId> = fd.sx[..fd.sx.len() - 1].to_vec();
    let gt: Vec<QubitId> = vec![fd.sx[fd.sx.len() - 1], af, f1, f2];
    // (dq columns: a delayed shot's no-step column, sz <= 127, narrows at the column after it)
    let mut l1 = vec![(fd.ph, false), (big, true)];
    if cp.dq { l1.push((sc.sz[sc.sz.len() - 1], false)); }
    let mut l2 = vec![(fd.ph, false)];
    l2.extend((RA..ctop).map(|l| (fd.q[l], true)));
    l2.push((fd.cnt[0], false));
    l2.extend(fd.cnt[1..].iter().map(|&x| (x, true)));
    // the payload lanes are no operand of these gates: borrow them
    let gate = |b: &mut B| {
        ge_const(b, &fd.sy, L0P as isize + 1, big, &chain);
        super::frogdrop_col::mc_xor_dn(b, &l1, gn, &gt, &pl.p, fd, cp.l0, false);
        mc_xor(b, &l2, gn, &gt, &pl.p);
        ge_const(b, &fd.sy, L0P as isize + 1, big, &chain);
    };
    let a_lits: Vec<(QubitId, bool)> = std::iter::once((fd.ph, false)).chain((RA..ctop).map(|l| (fd.q[l], true))).collect();
    gate(b);
    b.play(&sy_rec, true);
    if gate_a { mc_xor(b, &a_lits, af, &fd.sx, &pl.p); }
    b.play(&probe, false);
    let tr = (cp.sz.0.max(1), cp.sz.1.min(256));
    narrow(b, &pl.p, &fd.sx, (blo, bhi), &sc.sz, tr, gn, sv, f1, f2, &pre1, &pre2, &temps, &pl.dirty);
    b.play(&probe, true);
    if gate_a { mc_xor(b, &a_lits, af, &fd.sx, &pl.p); }
    b.play(&sy_rec, false);
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
    let div = ht_div_rec(b, fd, cp, sz, p, act, sc);
    b.play(&div, false);
    let amax = syhi >> 4;
    trans_q0(b, p, q, None, &[(act, false)], &fd.ring, NP, Some((&fd.sy[4..], amax)), sc.g, sc.c0, &sc.tmp, dirty);
    b.play(&div, true);
}

/// The restoring division of ht_exact_trans (recorded, not played): q (in sc.e) = floor(X / Y) on act & room shots,
/// X = r_{j+1} after it.
pub(crate) fn ht_div_rec(b: &mut B, fd: &Fd, cp: &ColPar, sz: &[QubitId], p: &[QubitId], act: QubitId, sc: &DigScr)
                         -> Vec<super::builder::G> {
    let n = fd.ring.len();
    let mt = (n - (cp.sz.0 + cp.h) + 1).min(fd.q.len().max(cp.xw) + 1);
    let q = &sc.e;
    let (szlo, szhi) = (cp.sz.0.max(1), cp.sz.1.min(256));
    let (sylo, syhi) = (cp.sy.0.max(1), cp.sy.1.min(L0P));
    let srange = (szlo + sylo, (szhi + syhi).min(257));
    let h = cp.h;
    let divstop: usize = std::env::var("FD_DIVSTOP").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    {
        b.begin();
        for k in (0..KE).rev() {
            if k < divstop { break; }
            if k >= mt {
                continue;
            }
            // clean at this step: q[0..k] (not yet written) and sv (a pad lane, zero outside the ripple)
            let mut hxe = vec![sc.sv];
            hxe.extend_from_slice(&q[0..k]);
            let Some((fa, made)) = gate_le(b, sc, act, srange, 257 - k as isize, &hxe) else { continue };
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
                    gate_le_undo(b, sc, act, 257 - k as isize, &hxe);
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
                gate_le_undo(b, sc, act, 257 - k as isize, &hxe);
            }
        }
        b.end()
    }
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
    // Select the existing endpoint Q bank before evaluating the legacy
    // four-slim-owner binding. Pool4 has only three raw ordinary owners,
    // but this endpoint never uses them: R<KD26 and Q100..108 is clean.
    let (gn, sv, f1, f2, temps, pre1, pre2, popre, ptmp) = if super::frogdrop_col::pool9() {
        let q = &fd.q;
        (q[100], q[101], q[102], q[103], vec![], vec![], vec![], q[104..107].to_vec(), q[107])
    } else { slim_narrow_lanes(sc, pl) };
    // (SLIM: the sw lane is clean here and serves as the narrowing's temp)
    let temps = if super::frogdrop_col::c55_pool8() { vec![fd.q[108]] }
                else if super::frogdrop_col::SLIM { vec![sc.sw] } else { temps };
    let probe_z = {
        b.begin();
        super::frogdrop::msb_probe_range(b, &fd.ring, szlo - 1, szhi, &sc.sz, &popre, ptmp, &sc.dirty);
        b.end()
    };
    b.play(&probe_z, false);
    // narrowing of the last column's finishers: B = bl(R) (Q < 2^26), t' = t_last
    {
        let probe = {
            b.begin();
            super::frogdrop::msb_probe_range(b, &fd.q, 0, KD, &fd.sx, &popre, ptmp, &sc.dirty);
            b.end()
        };
        b.play(&probe, false);
        let mut lits = vec![(fd.cnt[0], false)];
        lits.extend(fd.cnt[1..].iter().map(|&x| (x, true)));
        // the gate's AND temps: the narrowing lanes besides gn (clean around it)
        let gt: Vec<QubitId> = [sv, f1, f2].iter().chain(&temps).chain(&pre1).chain(&pre2).copied().take(8).collect();
        mc_xor(b, &lits, gn, &gt, dirty);
        narrow(b, &pl.p, &fd.sx, (1, KD), &sc.sz, (szlo, szhi), gn, sv, f1, f2, &pre1, &pre2, &temps, dirty);
        mc_xor(b, &lits, gn, &gt, dirty);
        b.play(&probe, true);
    }
    // last digit and the final transition
    let mut free = pl.free.clone();
    // (lowq-672 pool9: no pool lanes past sw; Q[KD..KD + 4) above R take their place, as the old 12-lane layout)
    if super::frogdrop_col::pool9() { free.extend(&fd.q[KD..KD + 4]); }
    free.extend_from_slice(&fd.sx);
    // s = 1 + bl(t_last) may reach 256. Q[120] is a returned zero owner
    // after the B0 map, above the final R (<2^26) and below the counter.
    let mut sa = sc.sz.clone();
    sa.push(fd.q[120]);
    let ds = dig_scr(&free, &sa, &fd.sy, &pl.dirty);
    let act = fd.ph; // 1 on every shot
    let ph = Ph { ht: true, sz_mask: false, virt_m1: n == 257,
                  rv: fd.sy.clone(), rr: (1, 1), tv: sc.sz.clone(), tr: (szlo, szhi),
                  src_r: vec![fd.ring[n - 1], ds.zeros[0]], src_t: fd.ring.clone() };
    #[cfg(test)] super::frogdrop_col::mark(b, 8100);
    digit(b, &pl.p, &ph, act, &ds, dirty);
    #[cfg(test)] super::frogdrop_col::mark(b, 8101);
    // At N=NP the ring's last lane is the sentinel one for divisor 1.
    // Replace it with a returned clean zero when forming the payload source;
    // at wider N that sentinel lies beyond the NP-lane transition already.
    let mut forbidden = pl.p.clone();
    forbidden.extend_from_slice(&fd.q[..KD]);
    forbidden.extend([act, ds.g, ds.c0]);
    forbidden.extend_from_slice(&ds.tmp);
    // DigScr's contract returns e and zeros clean; borrow e0 only after digit.
    let final_src = final_transition_source(&fd.ring, &[ds.zeros[0], ds.e[0], ds.e[1]], &forbidden);
    trans_q0(b, &pl.p, &fd.q[..KD], None, &[(act, false)], &final_src, NP, Some((&fd.sy[4..], 0)), ds.g, ds.c0, &ds.tmp, dirty);
    #[cfg(test)] super::frogdrop_col::mark(b, 8102);
    b.play(&probe_z, true);
}
