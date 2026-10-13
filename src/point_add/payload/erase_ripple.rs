//! Exact ADD;compare-erase fusion. No quantum-value or case-dependent choice.
use super::{B, Mask, QubitId, read_lane, ripple};
use crate::point_add::builder::G;
use std::collections::BTreeSet;

#[derive(Clone, Copy)]
pub(super) struct PrefixMask<'a> {
    pub bits: &'a [QubitId], pub amax: usize, pub flag: QubitId,
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

// Write sets are prefixes for every raw mask code, including codes above
// amax (empty prefix). This is essential: an arbitrary hole mask is invalid.
fn arithmetic(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, e: QubitId,
    subtract: bool, mask: Option<PrefixMask<'_>>, temps: &[QubitId], dirty: &[QubitId],
    mid: &mut dyn FnMut(&mut B)) {
    if let Some(m) = mask {
        let mut mk = Mask::new(m.bits, m.amax, false, vec![(e, false)], m.flag, &temps[..1], dirty);
        let mut gate = |b: &mut B, i: Option<usize>| match i {
            Some(i) => {
                let x = i as isize - 24;
                mk.goto(b, Some(if x < 0 { 0 } else { x.div_euclid(16) + 1 }));
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
pub(super) fn choose_record(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, e: QubitId,
    reg: &[QubitId], lo: usize, hi: usize, extra: &[(QubitId, bool)], pre: &[QubitId],
    temps: &[QubitId], dirty: &[QubitId], mask: Option<PrefixMask<'_>>) -> Vec<G> {
    let old = reference_record(b, t, s, c0, e, reg, lo, hi, extra, pre, temps, dirty, mask);
    if let Some(new) = fused_record(b, t, s, c0, e, reg, lo, hi, extra, pre, temps, dirty, mask) {
        if let (Some((of, oi)), Some((nf, ni))) =
            (super::read_lane_tree::prices(&old), super::read_lane_tree::prices(&new)) {
            if nf <= of && ni <= oi && (nf < of || ni < oi) { return new; }
        }
    }
    old
}
