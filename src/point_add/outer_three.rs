//! Three-role direct-size outer queries. No dedicated clean MCX prefix.
//!
//! Ports: E[7]=Y-1, S[5]=Z+Y-226, plus exactly three scalar owners.
//! Q and ring remain ordinary physical data; no joint packet is imported.
//! The two-query priority probes have an explicit ZERO-DESTINATION care
//! contract. They are not claimed to return their toggle for arbitrary S.
//! Their complete captured inverses are used for erasure. Off-extra branches
//! are literal identities, including arbitrary destination contents.
//!
//! Supported ordinary states retain the qualified parent's existing
//! post-refill sum-frame care 226<=Z+Y<=257. First-HT/DQ uses the separately
//! tagged bottom-size protocol. All inner middle/digit owner gaps remain open.

use super::builder::{B, G};
use super::mask::mc_xor;
use super::sum_size::SumSize;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[derive(Clone, Copy)]
pub(crate) struct Roles {
    /// Input C=W|D, then incoming-tag zero, new W, D, and outgoing C.
    pub tag: QubitId,
    /// Returned window/cut predicate.
    pub cut: QubitId,
    /// Returned two-query priority toggle.
    pub work: QubitId,
}

/// Complete boundary exchange. The former decoder-prefix owner is not
/// retained: seven-bit equalities use restored dirty donors directly.
pub(crate) fn swap_top_record(b:&mut B,size:&SumSize,roles:Roles,
    ring:&[QubitId],q:&[QubitId],extra:&[(QubitId,bool)],dirty:&[QubitId])->Vec<G>{
    assert_eq!((ring.len(),q.len()),(257,128));
    assert!(extra.len()<=1&&extra.iter().all(|p|p.0==roles.tag));
    let address=super::direct_frame::z_byte_record(b,size,roles.work,dirty);
    record(b,|b|{
        b.play(&address,false);
        mc_xor(b,extra,roles.cut,&[],dirty);
        for lane in(129..257).rev(){
            if lane<256{
                let mut c=eq(&size.y,lane&127);
                c.push((roles.work,false));c.extend_from_slice(extra);
                mc_xor(b,&c,roles.cut,&[],dirty);
            }
            b.cswap(roles.cut,ring[lane],q[256-lane]);
        }
        mc_xor(b,extra,roles.cut,&[],dirty);
        let mut high=extra.to_vec();high.push((roles.work,false));
        mc_xor(b,&high,roles.cut,&[],dirty);
        let mut last=eq(&size.y,0);last.extend(high);
        mc_xor(b,&last,roles.cut,&[],dirty);
        b.play(&address,true);
    })
}

fn record(b: &mut B, f: impl FnOnce(&mut B)) -> Vec<G> {
    b.begin(); f(b); b.end()
}
fn eq(word: &[QubitId], value: usize) -> Vec<(QubitId, bool)> {
    word.iter().enumerate().map(|(i, &q)| (q, value >> i & 1 == 0)).collect()
}
fn intervals(word: &[QubitId], mut lo: usize, hi: usize) -> Vec<Vec<(QubitId, bool)>> {
    assert!(lo <= hi && hi <= 1usize << word.len());
    let mut out = vec![];
    while lo < hi {
        let mut free = if lo == 0 { word.len() } else { lo.trailing_zeros() as usize };
        free = free.min(word.len());
        while lo + (1usize << free) > hi { free -= 1; }
        out.push((free..word.len()).map(|i| (word[i], lo >> i & 1 == 0)).collect());
        lo += 1usize << free;
    }
    out
}
fn bank(size: &SumSize, roles: Roles, source: &[QubitId], extra: &[(QubitId, bool)],
        dirty: &[QubitId]) -> Vec<QubitId> {
    let ports: Vec<_> = size.y.iter().chain(&size.sum).copied()
        .chain([roles.tag, roles.cut, roles.work]).collect();
    assert_eq!(ports.iter().copied().collect::<BTreeSet<_>>().len(), 15);
    assert_eq!(source.iter().copied().collect::<BTreeSet<_>>().len(), source.len());
    assert!(!source.iter().any(|q| ports.contains(q)));
    assert!(extra.len() <= 2);
    assert!(!extra.iter().any(|p| size.y.contains(&p.0) || size.sum.contains(&p.0) || source.contains(&p.0)));
    assert!(!extra.iter().any(|p| p.0 == roles.cut || p.0 == roles.work));
    let mut excluded: BTreeSet<_> = ports.into_iter().chain(source.iter().copied())
        .chain(extra.iter().map(|p| p.0)).collect();
    let out: Vec<_> = dirty.iter().copied().filter(|q| excluded.insert(*q)).collect();
    // Probe toggles have at most nine controls; general Z equalities can
    // have fourteen. Twelve donors cover even their plain dirty lowering.
    // No metadata, role, source lane or external control is borrowed.
    assert!(out.len() >= 12, "outer-size helpers require twelve external restored dirty donors");
    out
}
fn xor_interval(b: &mut B, word: &[QubitId], lo: usize, hi: usize,
                target: QubitId, extra: &[(QubitId, bool)], clean: &[QubitId], dirty: &[QubitId]) {
    assert!(!word.contains(&target) && !extra.iter().any(|p| p.0 == target));
    for mut term in intervals(word, lo, hi) {
        term.extend_from_slice(extra);
        mc_xor(b, &term, target, clean, dirty);
    }
}

/// Capture S=0 -> S=bl(source below257-Y)+Y-226, controlled by `extra`.
///
/// For each candidate bit l, E+l lies224..255, so V=E+l-224 lies0..31.
/// Candidates are scanned descending and have DISTINCT V within this window.
/// The zero code V=0 is the LAST eligible candidate. Thus the ordinary
/// two-query priority construction can safely use S=0 as its sentinel.
/// A selected higher candidate never equals a subsequent V, even when the
/// global public interval is wider than32 positions.
///
/// Care: when extra is true, S starts0 and the highest valid source bit lies
/// in both `bits` and the 32-lane window. If the window is empty, output0 is
/// also well-defined. When extra is false, arbitrary S is unchanged. cut,
/// work starts/ends globally0 on these contracts. E/source and
/// every dirty donor are restored. The inverse is this COMPLETE literal tape.
pub(crate) fn sum_probe_record(b: &mut B, size: &SumSize, roles: Roles,
    source: &[QubitId], bits: (usize, usize), extra: &[(QubitId, bool)], dirty: &[QubitId]) -> Vec<G> {
    assert!(bits.0 <= bits.1 && bits.1 <= source.len());
    let d = bank(size, roles, source, extra, dirty);
    record(b, |b| {
        for l in (bits.0..bits.1).rev() {
            // 224 <= E+l <=255. Endpoints are clamped to physical E0..127.
            let low = 224isize - l as isize;
            let high = 256isize - l as isize;
            let lo = low.max(0).min(128) as usize;
            let hi = high.max(0).min(128) as usize;
            if lo >= hi { continue; }
            xor_interval(b, &size.y, lo, hi, roles.cut, &[], &[roles.work], &d);
            let mut c = eq(&size.sum, 0);
            c.extend([(source[l], false), (roles.cut, false)]);
            c.extend_from_slice(extra);
            mc_xor(b, &c, roles.work, &[], &d);

            // Since224 is divisible by32, V=(E.low5+l) mod32. The cut
            // flag was computed BEFORE this temporary E-low permutation.
            let v = record(b, |b| super::frogdrop::add_const_dirty_exact(b, &size.y[..5], l & 31, &d));
            b.play(&v, false);
            for i in 0..5 { b.ccx(roles.work, size.y[i], size.sum[i]); }
            for i in 0..5 { b.cx(size.y[i], size.sum[i]); }
            mc_xor(b, &c, roles.work, &[], &d);
            for i in 0..5 { b.cx(size.y[i], size.sum[i]); }
            b.play(&v, true);
            xor_interval(b, &size.y, lo, hi, roles.cut, &[], &[roles.work], &d);
        }
    })
}

/// Complete ordinary window only. Partial DL probes deliberately keep the
/// original public bit cut: their upper cells may contain the new value.
fn complete_sum_probe_record(b:&mut B,size:&SumSize,roles:Roles,
    ring:&[QubitId],bits:(usize,usize),extra:&[(QubitId,bool)],dirty:&[QubitId])->Vec<G>{
    assert!(extra.len()<=1 && bits.0<=bits.1 && bits.1<=ring.len());
    if super::aligned_sum_probe::preferred(bits,!extra.is_empty()){
        let d=bank(size,roles,ring,extra,dirty);
        super::aligned_sum_probe::record(b,size,ring,extra.first().copied(),&d)
    }else{sum_probe_record(b,size,roles,ring,bits,extra,dirty)}
}

/// Positive source of width<=128 -> (bit length)-1 on seven output lanes.
/// Offset0 (source bit0) is the last candidate, so no aliased zero sentinel.
/// Care and helper-return contract is identical to sum_probe_record.
fn offset_probe_record(b: &mut B, size: &SumSize, roles: Roles,
    source: &[QubitId], extra: &[(QubitId, bool)], dirty: &[QubitId]) -> Vec<G> {
    assert!(source.len() <= 128);
    let d = bank(size, roles, source, extra, dirty);
    record(b, |b| {
        for l in (0..source.len()).rev() {
            let mut c = eq(&size.y, 0);
            c.push((source[l], false)); c.extend_from_slice(extra);
            mc_xor(b, &c, roles.work, &[roles.cut], &d);
            for i in 0..7 { if l >> i & 1 != 0 { b.cx(roles.work, size.y[i]); } }
            let mut c = eq(&size.y, l);
            c.push((source[l], false)); c.extend_from_slice(extra);
            mc_xor(b, &c, roles.work, &[roles.cut], &d);
        }
    })
}

/// Entry: all S bits0. Ordinary (!C): E=Y-1, supported sum care.
/// Tagged C: E=M-1, bottom M98..128; S temporarily holds (M-1) mod32.
/// HT narrowing must exclude C until tagged_refill has completed.
pub(crate) fn stage1_record(b: &mut B, size: &SumSize, roles: Roles,
    ring: &[QubitId], bits: (usize, usize), dirty: &[QubitId]) -> Vec<G> {
    let probe = complete_sum_probe_record(b, size, roles, ring, bits, &[(roles.tag, true)], dirty);
    record(b, |b| {
        b.play(&probe, false);
        for i in 0..5 { b.ccx(roles.tag, size.y[i], size.sum[i]); }
    })
}

/// Tagged first-HT/DQ only. Entry C1: E=M-1 (97..127), S=E mod32.
/// Ordinary C0 is an exact identity for arbitrary metadata.
/// Exit C1: E=bl(Q)-1, S=M+bl(Q)-226 mod32. Q is positive and<=128 bits.
/// All three ordinary roles are returned; C remains held until erase_tag.
pub(crate) fn tagged_refill_record(b: &mut B, size: &SumSize, roles: Roles,
    q: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    let probe = offset_probe_record(b, size, roles, q, &[(roles.tag, false)], dirty);
    record(b, |b| {
        for i in 0..5 { b.ccx(roles.tag, size.sum[i], size.y[i]); }
        b.cx(roles.tag, size.y[5]); b.cx(roles.tag, size.y[6]);
        b.play(&probe, false);
        // M-1 + (Y-1) = M+Y-226 modulo32. 3*5-2=13CCX.
        super::arith::ttk_add(b, &size.y[..5], &size.sum, Some(roles.tag), None);
    })
}

/// XOR an existing supported raw-Z equality while E is in its z_epoch.
fn xor_z(b: &mut B, size: &SumSize, value: usize, target: QubitId,
         extra: &[(QubitId, bool)], dirty: &[QubitId]) {
    size.xor_terms(b, size.z_terms(value), target, extra, dirty);
}

/// Clear the incoming C only AFTER refill has made the sum/size pair valid.
/// The old first-HT/DQ characterization is PH & (Z<=127 | Z128&topbit128).
/// Ordinary/data-inactive states still satisfy this inherited characterization.
pub(crate) fn erase_tag_record(b: &mut B, size: &SumSize, roles: Roles,
    phase: QubitId, old_top_bit128: QubitId, dirty: &[QubitId]) -> Vec<G> {
    let extra = [(phase, false), (old_top_bit128, false)];
    let d = bank(size, roles, &[], &extra, dirty);
    let z = size.z_epoch(b, &d);
    record(b, |b| {
        b.play(&z, false);
        for v in 98..=127 { xor_z(b, size, v, roles.tag, &[(phase, false)], &d); }
        xor_z(b, size, 128, roles.tag, &extra, &d);
        b.play(&z, true);
    })
}

/// New W=!PH & Z<=Y, or total crossing C=!PH & Z<=128.
/// The exact S-specific thresholds use no raw-Z register or clean comparator.
/// Target normally is roles.tag; no predicate reads that owner.
fn xor_cross_predicate(b: &mut B, size: &SumSize, roles: Roles, phase: QubitId,
    switch_only: bool, dirty: &[QubitId]) {
    let d = bank(size, roles, &[], &[(phase, true)], dirty);
    if switch_only{
        super::direct_size_predicates::xor_switch(b,size,phase,roles.tag,&d);
    }else{
        super::direct_size_predicates::xor_crossing(b,size,phase,roles.tag,roles.cut,&d);
    }
}
pub(crate) fn xor_new_switch(b: &mut B, size: &SumSize, roles: Roles,
    phase: QubitId, dirty: &[QubitId]) {
    xor_cross_predicate(b, size, roles, phase, true, dirty);
}

/// Exact257-ring delayed upper-data relocation, retaining the original cut.
/// Entry tag=W; exit tag=C=W|D. No payload or narrow call is hidden here.
/// The caller performs HR narrowing after this record, before delayed_reprobe.
pub(crate) fn delayed_move_record(b: &mut B, size: &SumSize, roles: Roles,
    phase: QubitId, ring: &[QubitId], xw: usize, dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(ring.len(), 257); assert!(xw <= 257);
    let d = bank(size, roles, ring, &[(phase, true)], dirty);
    let z = size.z_epoch(b, &d);
    record(b, |b| {
        xor_cross_predicate(b, size, roles, phase, false, &d); // W xor C =D.
        if xw > 129 {
            let lo = 257 - xw;
            b.play(&z, false);
            for v in 98..=127 { xor_z(b, size, v, roles.cut, &[(roles.tag, false)], &d); }
            for a in (lo..128).rev() {
                if a < 127 { xor_z(b, size, a + 1, roles.cut, &[(roles.tag, false)], &d); }
                b.cswap(roles.cut, ring[a], ring[256 - a]);
            }
            for a in lo + 1..128 { xor_z(b, size, a, roles.cut, &[(roles.tag, false)], &d); }
            for v in 98..=127 { xor_z(b, size, v, roles.cut, &[(roles.tag, false)], &d); }
            b.play(&z, true);
        }
        xor_new_switch(b, size, roles, phase, &d); // D xor W =C.
    })
}

/// Entry/exit tag=C. After delayed_move and narrow, replace old Z by the
/// bottom probe's max(Z,bl(t_next)) on D only. Old lower128 still contains r_j.
/// The new sum is226..256 by the exact DL identity documented in the receipt.
pub(crate) fn delayed_reprobe_record(b: &mut B, size: &SumSize, roles: Roles,
    phase: QubitId, ring: &[QubitId], bitlo: usize, xw: usize, dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(ring.len(), 257); assert!(bitlo < 128 && (128..=257).contains(&xw));
    let old = sum_probe_record(b, size, roles, ring, (bitlo, 128), &[(roles.tag, false)], dirty);
    let new = sum_probe_record(b, size, roles, ring, (bitlo, xw), &[(roles.tag, false)], dirty);
    record(b, |b| {
        xor_new_switch(b, size, roles, phase, dirty); // C xor W =D.
        b.play(&old, true); b.play(&new, false);
        xor_new_switch(b, size, roles, phase, dirty); // W unchanged on D.
    })
}

/// Final S erasure is a FRESH unconditional output-layout probe inverse.
/// Do not reuse the stage1 tape: old input C and outgoing C differ.
pub(crate) fn erase_output_sum(b: &mut B, size: &SumSize, roles: Roles,
    ring: &[QubitId], bits: (usize, usize), dirty: &[QubitId]) {
    let probe = complete_sum_probe_record(b, size, roles, ring, bits, &[], dirty);
    b.play(&probe, true);
}
