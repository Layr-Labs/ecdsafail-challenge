//! Exact ADD;compare-erase fusion. No quantum-value or case-dependent choice.
use super::{B, Mask, QubitId, read_lane, ripple, mc_xor};
use crate::point_add::builder::G;
use std::collections::BTreeSet;

#[derive(Clone, Copy)]
pub(super) struct PrefixMask<'a> {
    pub bits: &'a [QubitId], pub amax: usize, pub flag: QubitId, pub margin: isize,
    /// agent_lowq_quot: mask granule 2^shift lanes (bits = the size register from bit `shift`)
    pub shift: usize,
    pub lo: usize,
    pub pre: &'a [QubitId],
}

// The new ordering holds the already-paid size guard during both passes.
// Every mutable data/carry port is separated from that guard, the address,
// decoder and clean AND cells. Data may be arbitrary-state dirty donors.
#[allow(clippy::too_many_arguments)]
pub(super) fn geometry(t: &[QubitId], s: &[QubitId], c0: QubitId, e: QubitId,
    reg: &[QubitId], extra: &[(QubitId, bool)], pre: &[QubitId], temps: &[QubitId],
    dirty: &[QubitId], mask: Option<PrefixMask<'_>>) -> bool {
    if t.is_empty() || t.len() != s.len() || reg.is_empty()
        || reg.len() >= usize::BITS as usize { return false; }
    let h = pre.len().min(reg.len() - 1);
    let used = temps.len().min((reg.len() - h + 1 + extra.len()).saturating_sub(2));
    if used == 0 && reg.len() - h + 1 + extra.len() > 2 { return false; }
    if mask.is_some() && temps.is_empty() { return false; }
    let mut ports = BTreeSet::new();
    for q in t.iter().chain(s).chain([&c0, &e]).chain(reg)
        .chain(extra.iter().map(|(q, _)| q)).chain(pre[..h].iter())
        .chain(temps[..used.max(usize::from(mask.is_some()))].iter()) {
        if !ports.insert(q.0) { return false; }
    }
    if let Some(m) = mask {
        // The query returns all decoder cells before the masked write starts.
        // HT already lends its mask flag as a decoder cell at that exact cut.
        if (ports.contains(&m.flag.0) && !pre[..h].contains(&m.flag)) || m.bits.is_empty()
            || !m.bits.iter().all(|q| reg.contains(q)) { return false; }
    }
    let forbidden: BTreeSet<_> = reg.iter().chain(extra.iter().map(|(q, _)| q))
        .chain([&c0, &e]).chain(pre[..h].iter())
        .chain(temps[..used.max(usize::from(mask.is_some()))].iter())
        .map(|q| q.0).chain(mask.map(|m| m.flag.0)).collect();
    let mut donors = BTreeSet::new();
    dirty.iter().all(|q| !forbidden.contains(&q.0) && donors.insert(q.0))
        && dirty.len() >= reg.len() + extra.len() + 4
}

fn query(b: &mut B, s: &[QubitId], reg: &[QubitId], lo: usize, hi: usize,
    extra: &[(QubitId, bool)], e: QubitId, pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) {
    let lane = |v: usize| s.get(v).copied();
    read_lane(b, reg, lo, hi, &lane, true, extra, e, pre, temps, dirty);
}

// Paired reversible trees read t[v] and s[v-1] under one public address.
// The extra guard is asserted to imply an address in [lo, hi] at the caller;
// out-of-range extra-off states remain untouched. Every swap is restored.
#[allow(clippy::too_many_arguments)]
pub(super) fn paired_mid_record(b: &mut B, t: &[QubitId], s: &[QubitId], reg: &[QubitId],
    lo: usize, hi: usize, extra: &[(QubitId, bool)], e: QubitId,
    bank: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) -> Option<Vec<G>> {
    if lo == 0 || lo > hi || hi >= t.len() || hi > s.len() || extra.is_empty() { return None; }
    let lt: Vec<_> = (lo..=hi).map(|v| (v, t[v])).collect();
    let ls: Vec<_> = (lo..=hi).map(|v| (v, s[v - 1])).collect();
    let mut protected = BTreeSet::new();
    for q in reg.iter().chain(lt.iter().map(|(_, q)| q)).chain(ls.iter().map(|(_, q)| q))
        .chain(extra.iter().map(|(q, _)| q)).chain(std::iter::once(&e))
        .chain(bank.iter()).chain(temps.iter()) {
        if !protected.insert(q.0) { return None; }
    }
    let mut tswaps = Vec::new();
    let mut sswaps = Vec::new();
    let tr = super::read_lane_tree::collect_tree(reg, &lt, reg.len(), &mut tswaps);
    let sr = super::read_lane_tree::collect_tree(reg, &ls, reg.len(), &mut sswaps);
    let donors: Vec<_> = dirty.iter().copied().filter(|q| *q != tr && *q != sr
        && !reg.contains(q) && !extra.iter().any(|(c, _)| c == q)
        && *q != e && !bank.contains(q) && !temps.contains(q)).collect();
    let controls = extra.iter().copied().chain([(tr, false), (sr, false)]).collect::<Vec<_>>();
    b.begin();
    for &(c, x, y) in &tswaps { b.cswap(c, x, y); }
    for &(c, x, y) in &sswaps { b.cswap(c, x, y); }
    mc_xor(b, &controls, e, temps, &donors);
    for &(c, x, y) in sswaps.iter().rev() { b.cswap(c, x, y); }
    for &(c, x, y) in tswaps.iter().rev() { b.cswap(c, x, y); }
    Some(b.end())
}

// Write sets are prefixes for every raw mask code, including codes above
// amax (empty prefix). This is essential: an arbitrary hole mask is invalid.
fn arithmetic(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, e: QubitId,
    subtract: bool, mask: Option<PrefixMask<'_>>, temps: &[QubitId], dirty: &[QubitId],
    mid: &mut dyn FnMut(&mut B)) {
    if let Some(m) = mask {
        let mut mk = Mask::new(m.bits, m.amax, false, vec![(e, false)], m.flag, &temps[..1], dirty)
            .with_lo(m.lo).with_pre(m.pre);
        let mut gate = |b: &mut B, i: Option<usize>| match i {
            Some(i) => {
                let x = i as isize - m.margin;
                mk.goto(b, Some(if x < 0 { 0 } else { x.div_euclid(1 << m.shift) + 1 }));
                Some(m.flag)
            }
            None => { mk.goto(b, None); None }
        };
        ripple(b, t, s, c0, subtract, mid, &mut gate);
    } else {
        let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| e);
        ripple(b, t, s, c0, subtract, mid, &mut gate);
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn reference_record(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, e: QubitId,
    reg: &[QubitId], lo: usize, hi: usize, extra: &[(QubitId, bool)], pre: &[QubitId],
    temps: &[QubitId], dirty: &[QubitId], mask: Option<PrefixMask<'_>>) -> Vec<G> {
    b.begin();
    arithmetic(b, t, s, c0, e, false, mask, temps, dirty, &mut |_b| {});
    let mut mid = |b: &mut B| query(b, s, reg, lo, hi, extra, e, pre, temps, dirty);
    let mut gate = |_b: &mut B, _i: Option<usize>| None;
    ripple(b, t, s, c0, true, &mut mid, &mut gate);
    b.end()
}

#[allow(clippy::too_many_arguments)]
pub(super) fn fused_record(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, e: QubitId,
    reg: &[QubitId], lo: usize, hi: usize, extra: &[(QubitId, bool)], pre: &[QubitId],
    temps: &[QubitId], dirty: &[QubitId], mask: Option<PrefixMask<'_>>) -> Option<Vec<G>> {
    if !geometry(t, s, c0, e, reg, extra, pre, temps, dirty, mask) { return None; }
    b.begin();
    let mut mid = |b: &mut B| query(b, s, reg, lo, hi, extra, e, pre, temps, dirty);
    arithmetic(b, t, s, c0, e, true, mask, temps, dirty, &mut mid);
    let restoring = b.end();
    b.begin(); b.play(&restoring, true); Some(b.end())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn fused_record_margin1(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, e: QubitId,
    reg: &[QubitId], lo: usize, hi: usize, extra: &[(QubitId, bool)], pre: &[QubitId],
    temps: &[QubitId], dirty: &[QubitId], mask: Option<PrefixMask<'_>>) -> Option<Vec<G>> {
    if !geometry(t, s, c0, e, reg, extra, pre, temps, dirty, mask) { return None; }
    let witness = mask?.flag;
    if t.contains(&witness) || s.contains(&witness)
        || temps.contains(&witness) || reg.contains(&witness) || witness == c0
        || witness == e || extra.iter().any(|&(q, _)| q == witness) { return None; }
    let bank: Vec<QubitId> = pre.iter().copied().filter(|&q| q != witness).collect();
    let last = hi.min(t.len() - 1);
    b.begin();
    if lo <= last {
        let mut range = Mask::new(reg, last, true, extra.to_vec(), e, &bank, dirty);
        range.toggle_range(b, lo, last);
        let tv = |v: usize| t.get(v).copied();
        super::read_lane(b, reg, lo, last, &tv, false, &[], witness, &bank, temps, dirty);
        let sv = |v: usize| v.checked_sub(1).and_then(|i| s.get(i).copied());
        let mut guarded = extra.to_vec();
        guarded.push((witness, false));
        super::read_lane(b, reg, lo, last, &sv, false, &guarded, e, &bank, temps, dirty);
        super::read_lane(b, reg, lo, last, &tv, false, &[], witness, &bank, temps, dirty);
    }
    let old_mid = b.end();
    let mut chosen = old_mid.clone();
    if let Some(pair) = paired_mid_record(b, t, s, reg, lo, last, extra, e, &bank, temps, dirty) {
        b.begin();
        if lo <= last {
            let mut range = Mask::new(reg, last, true, extra.to_vec(), e, &bank, dirty);
            range.toggle_range(b, lo, last);
        }
        b.play(&pair, false);
        let candidate = b.end();
        if let (Some((of, oi)), Some((nf, ni))) =
            (super::read_lane_tree::prices(&old_mid), super::read_lane_tree::prices(&candidate)) {
            if nf <= of && ni <= oi && (nf < of || ni < oi) { chosen = candidate; }
        }
    }
    b.begin();
    let mut mid = |b: &mut B| b.play(&chosen, false);
    arithmetic(b, t, s, c0, e, true, mask, temps, dirty, &mut mid);
    let restoring = b.end();
    b.begin(); b.play(&restoring, true); Some(b.end())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn choose_record(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, e: QubitId,
    reg: &[QubitId], lo: usize, hi: usize, extra: &[(QubitId, bool)], pre: &[QubitId],
    temps: &[QubitId], dirty: &[QubitId], mask: Option<PrefixMask<'_>>) -> Vec<G> {
    let old = reference_record(b, t, s, c0, e, reg, lo, hi, extra, pre, temps, dirty, mask);
    #[cfg(test)] if std::env::var("Q675_DIGIT_REFERENCE").is_ok() { return old; }
    if let Some(new) = fused_record(b, t, s, c0, e, reg, lo, hi, extra, pre, temps, dirty, mask) {
        if let (Some((of, oi)), Some((nf, ni))) =
            (super::read_lane_tree::prices(&old), super::read_lane_tree::prices(&new)) {
            if nf <= of && ni <= oi && (nf < of || ni < oi) { return new; }
        }
    }
    old
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(super) fn diagnostic_reference_play(b:&mut B,t:&[QubitId],s:&[QubitId],c0:QubitId,e:QubitId,
 reg:&[QubitId],lo:usize,hi:usize,extra:&[(QubitId,bool)],pre:&[QubitId],temps:&[QubitId],dirty:&[QubitId],mask:Option<PrefixMask<'_>>,tag:usize){
 arithmetic(b,t,s,c0,e,false,mask,temps,dirty,&mut |_b|{});
 crate::point_add::frogdrop_col::mark(b,tag);
 let mut mid=|b:&mut B|{crate::point_add::frogdrop_col::mark(b,tag+1);query(b,s,reg,lo,hi,extra,e,pre,temps,dirty);crate::point_add::frogdrop_col::mark(b,tag+2);};
 let mut gate=|_b:&mut B,_i:Option<usize>|None;ripple(b,t,s,c0,true,&mut mid,&mut gate);
 crate::point_add::frogdrop_col::mark(b,tag+3);
}
