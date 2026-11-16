//! Source-only one-hole payload representation.
//!
//! The arithmetic payload remains LOGICAL_NP=259.  A compact register has
//! PHYSICAL_NP=258 lanes, in the same order with one known-zero lane omitted.
//! PRE omits h=257-bl(t). POST first changes P[B] ^= P[B+1] ^ 1,
//! B=bl(r), then omits P[B]. Mixed inactive branches retain their old format:
//! every splice below is controlled by the same complete phase enable.
//!
//! These are literal, reversible permutations; none allocates a qubit. The
//! extra raw owner is data from expansion until compression. It MUST NOT be
//! counted as a returned digit, size, reciprocal, decoder or carry owner.
//! Integration is deliberately blocked until the whole owner timeline exists.

use super::{Mask, PlCol};
use super::super::builder::{B, G};
use super::super::frogdrop_col::rec;
use super::super::mask::{mc_xor, Dec};
use crate::circuit::QubitId;
use std::collections::BTreeSet;

pub(crate) const LOGICAL_NP: usize = 259;
pub(crate) const PHYSICAL_NP: usize = 258;
// The PH-only bridge, compact narrowing, endpoint and sixth fixed-R loan
// are wired in this source draft. This is not a circuit qualification.
pub(crate) const INTEGRATED: bool = true;

/// The raw digit has returned every helper and both raw sizes, but PH is
/// still logical P258. `act` is the original complete activity, retained.
pub(crate) struct DigitExit { pub act: QubitId, pub ht: bool }

/// Production bridge: PH remains the extra raw payload cell through the
/// complete phase transition. Every metadata/phase reader lies outside it.
pub(crate) struct PhaseTransition {
    pub raw: PlCol,
    pub act: QubitId,
    pub phase: QubitId,
    pub ht: bool,
}

/// Caller has encoded raw SZ and returned middle_act to zero. On every
/// branch the two-CX transfer leaves the old raw act owner zero.
pub(crate) fn retain_phase_digit(b:&mut B,
    fd:&super::super::frogdrop_col::Fd,pl:&PlCol,exit:DigitExit,
    middle_act:QubitId)->PhaseTransition {
    assert!(!fd.sy.contains(&middle_act) && middle_act!=fd.ph);
    if exit.act!=middle_act {b.cx(exit.act,middle_act);b.cx(middle_act,exit.act);}
    PhaseTransition{raw:raw_context(pl,fd.ph),act:middle_act,phase:fd.ph,ht:exit.ht}
}

/// Metadata sizes and retained act have returned unchanged after the
/// exact quotient transition. Compress the POST hole, then restore PH.
pub(crate) fn finish_phase(b:&mut B,session:&PhaseTransition,
    remainder_bits:&[QubitId],range:(usize,usize),flag:QubitId,
    pre:&[QubitId],temps:&[QubitId],dirty:&[QubitId]) {
    assert!(!remainder_bits.contains(&session.phase));
    let gates=compress_post_record(b,&session.raw.p,remainder_bits,range,
        &[(session.act,false)],flag,pre,temps,dirty);
    b.play(&gates,false);
    if session.ht {b.cx(session.act,session.phase);}
}

/// During the exact payload transition SY7 is the missing raw P cell.
/// Caller must finish compression and restore size before erasing act.
pub(crate) struct Transition {
    pub raw: PlCol,
    pub act: QubitId,
    pub normalize: Vec<G>,
}

/// Call only after the raw-size frame was encoded and returned `middle_act`
/// globally zero. The act move uses two CX because the destination is zero.
/// PH is restored before the function returns, including all inactive shots.
pub(crate) fn handoff_digit(b: &mut B,
    fd: &super::super::frogdrop_col::Fd, pl: &PlCol, exit: DigitExit,
    middle_act: QubitId, temps: &[QubitId], dirty: &[QubitId]) -> Transition {
    assert!(!fd.sy.contains(&middle_act) && middle_act!=fd.ph);
    if exit.act!=middle_act { b.cx(exit.act,middle_act); b.cx(middle_act,exit.act); }
    let normalize=sy_normalize_record(b,&fd.sy,middle_act,fd.ph,temps,dirty);
    handoff_to_sy7(b,&fd.sy,fd.ph,middle_act,&normalize);
    if exit.ht {b.cx(middle_act,fd.ph);}
    Transition {raw:raw_context(pl,fd.sy[7]),act:middle_act,normalize}
}

/// `xor_eq` must include this transition's retained act. The raw remainder
/// size must be unchanged since the digit; the original low7 SY view must
/// have been returned by every temporary transition frame.
pub(crate) fn finish_transition(b: &mut B, session: Transition,
    range:(usize,usize), flag:QubitId,
    xor_eq:&mut dyn FnMut(&mut B,usize,QubitId)) {
    assert_ne!(flag,session.act);
    let r=compress_post_by_query_record(b,&session.raw.p,range,flag,xor_eq);
    b.play(&r,false);
    restore_sy_after_compress(b,&session.normalize);
}

pub(crate) fn enabled() -> bool {
    std::env::var("C660_PAYLOAD258").as_deref() == Ok("1")
}

pub(crate) fn physical_width() -> usize {
    if enabled() { PHYSICAL_NP } else { LOGICAL_NP }
}

pub(crate) fn check_context(p: &[QubitId]) {
    assert_eq!(p.len(), physical_width(), "payload physical/layout width mismatch");
}

/// The compact terminal form omits normalized lane 1. Its first two
/// physical lanes are zero and its 256-bit W word ends at physical lane257.
pub(crate) fn terminal_word(p: &[QubitId]) -> Vec<QubitId> {
    check_context(p);
    (0..256).map(|i| p[p.len()-1-i]).collect()
}

pub(crate) fn terminal_offset(b: &mut B, p: &[QubitId]) {
    check_context(p);
    if !enabled() { b.x(p[1]); }
}

pub(crate) fn require_integrated() {
    assert!(!enabled() || INTEGRATED,
        "P258 splice integration is disabled");
}

/// Append the supplied physical owner as the logical last lane. No state
/// transfer occurs here; expand_pre_record supplies the missing zero.
pub(crate) fn raw_view(compact: &[QubitId], extra: QubitId) -> Vec<QubitId> {
    assert_eq!(compact.len(), PHYSICAL_NP);
    assert!(!compact.contains(&extra));
    assert_eq!(compact.iter().copied().collect::<BTreeSet<_>>().len(), PHYSICAL_NP);
    compact.iter().copied().chain([extra]).collect()
}

/// Give the unchanged logical-259 arithmetic a phase-local context. Its
/// caller owns expansion, handoff, compression, and exclusion of extra from
/// every concurrently live scratch bank.
pub(crate) fn raw_context(compact: &PlCol, extra: QubitId) -> PlCol {
    assert!(!compact.free.contains(&extra) && !compact.mid_hr.contains(&extra)
        && !compact.mid_ht.contains(&extra) && !compact.dirty.contains(&extra));
    PlCol { p: raw_view(&compact.p, extra), free: compact.free.clone(),
        mid_hr: compact.mid_hr.clone(), mid_ht: compact.mid_ht.clone(),
        dirty: compact.dirty.clone(), obs: compact.obs.clone() }
}

/// A single owner cannot be the omitted raw cell and an arithmetic role.
/// In particular the four-role digit's freed SX7 is unavailable if SX7 was
/// already physically removed by the independent fixed-bank architecture.
pub(crate) fn assert_extra_disjoint(extra: QubitId, roles: &[QubitId]) {
    assert!(!roles.contains(&extra), "P258 raw extra overlaps a live owner");
}

/// Normalize SY7 only on the retained active branch. Active raw SY is in
/// 1..=128, so SY7 XOR [SYlow7==0] is exactly zero. Inactive SY may exceed128
/// and remains bit-for-bit unchanged. This record is captured before the
/// handoff and inverted only after the transition has returned SYlow7.
pub(crate) fn sy_normalize_record(b: &mut B, sy: &[QubitId], act: QubitId,
    extra: QubitId, temps: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(sy.len(),8);
    assert!(!sy.contains(&act) && !sy.contains(&extra) && act!=extra);
    let mut ports:BTreeSet<_>=sy.iter().copied().collect();
    assert_eq!(ports.len(),8);
    ports.extend([act,extra]);
    for &q in temps { assert!(ports.insert(q)); }
    let mut seen=BTreeSet::new();
    let donors:Vec<_>=dirty.iter().copied()
        .filter(|q|!ports.contains(q)&&seen.insert(*q)).collect();
    assert!(donors.len()>=8);
    let mut lits=vec![(act,false)];
    lits.extend(sy[..7].iter().map(|&q|(q,true)));
    rec(b,|b|mc_xor(b,&lits,sy[7],temps,&donors))
}

/// After the digit has returned the shared-size frame to Y view, this
/// handoff moves its raw extra cell to normalized SY7 and returns `extra`.
/// Caller must have removed extra from every live scratch bank first.
/// `act` remains live, unchanged, through the complete transition. On act0,
/// both the size register and the mixed compact payload are untouched.
pub(crate) fn handoff_to_sy7(b: &mut B, sy: &[QubitId], extra: QubitId,
    act: QubitId, normalize: &[G]) {
    assert_eq!(sy.len(),8);
    assert!(!sy.contains(&extra) && !sy.contains(&act) && extra!=act);
    b.play(normalize,false);
    b.cswap(act,extra,sy[7]);
}

/// Compression has put the selected zero back into SY7 on act1. Restoring
/// the original high size bit now ends the payload loan. No high-bit reader
/// is allowed between handoff_to_sy7 and this call; all transition size
/// queries need an explicit low7/zero-means128 view during that interval.
pub(crate) fn restore_sy_after_compress(b: &mut B, normalize: &[G]) {
    b.play(normalize,true);
}

fn bank(raw: &[QubitId], addr: &[QubitId], controls: &[(QubitId,bool)],
        flag: QubitId, pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) -> Vec<QubitId> {
    assert_eq!(raw.len(), LOGICAL_NP);
    assert!(!addr.is_empty() && addr.len() <= 9);
    let mut ports = BTreeSet::new();
    for q in raw.iter().chain(addr).chain(controls.iter().map(|(q,_)|q))
        .chain([&flag]).chain(pre).chain(temps) {
        assert!(ports.insert(*q), "P258 splice aliases an operand or clean owner");
    }
    let mut seen = BTreeSet::new();
    let out: Vec<_> = dirty.iter().copied()
        .filter(|q| !ports.contains(q) && seen.insert(*q)).collect();
    assert!(out.len() >= addr.len() + controls.len(), "P258 splice lacks dirty donors");
    out
}

/// Insert extra=0 at h=257-value(tbits) on enabled shots, shifting the
/// suffix right by one. After this record all 259 logical lanes are raw.
/// Other shots are exactly unchanged, even when their extra is arbitrary.
/// tbits is the complete raw coefficient bit length, including 256 via a
/// ninth size bit. The live range is never inferred from low-seven bits.
#[allow(clippy::too_many_arguments)]
pub(crate) fn expand_pre_record(b: &mut B, raw: &[QubitId], tbits: &[QubitId],
    range: (usize,usize), enable: &[(QubitId,bool)], flag: QubitId,
    pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    assert!(1 <= range.0 && range.0 <= range.1 && range.1 <= 256);
    assert!(range.1 < (1usize << tbits.len()));
    let donors = bank(raw,tbits,enable,flag,pre,temps,dirty);
    rec(b, |b| {
        let mut mask = Mask::new(tbits,range.1,false,enable.to_vec(),flag,temps,&donors)
            .with_lo(range.0).with_pre(pre);
        // Right-rotate suffix h..259: the predicate for adjacent swap i
        // is h<i, equivalently t>=258-i. Address and enable stay unchanged.
        let hmin=257-range.1;
        for i in (hmin+1..LOGICAL_NP).rev() {
            mask.goto(b,Some((258-i) as isize));
            b.cswap(flag,raw[i],raw[i-1]);
        }
        mask.goto(b,None);
    })
}

/// The same insertion permutation for a POST hole at B=value(rbits).
/// Playing its inverse moves the selected zero to extra and returns extra.
#[allow(clippy::too_many_arguments)]
pub(crate) fn expand_post_record(b: &mut B, raw: &[QubitId], rbits: &[QubitId],
    range: (usize,usize), enable: &[(QubitId,bool)], flag: QubitId,
    pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    assert!(1 <= range.0 && range.0 <= range.1 && range.1 <= 256);
    assert!(range.1 < (1usize << rbits.len()));
    let donors = bank(raw,rbits,enable,flag,pre,temps,dirty);
    rec(b, |b| {
        let mut mask = Mask::new(rbits,range.1,true,enable.to_vec(),flag,temps,&donors)
            .with_lo(range.0).with_pre(pre);
        for i in (range.0+1..LOGICAL_NP).rev() {
            mask.goto(b,Some(i as isize));
            b.cswap(flag,raw[i],raw[i-1]);
        }
        mask.goto(b,None);
    })
}

/// P[B] ^= P[B+1] ^ 1 under the complete enable. On a completed exact
/// transition |W_next|<2^(257-B), so this exposes the POST zero. This does
/// NOT hold merely after digit; a caller must finish every q/bq correction.
#[allow(clippy::too_many_arguments)]
pub(crate) fn normalize_post_record(b: &mut B, raw: &[QubitId], rbits: &[QubitId],
    range: (usize,usize), enable: &[(QubitId,bool)], flag: QubitId,
    pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    assert!(1 <= range.0 && range.0 <= range.1 && range.1 <= 256);
    assert!(range.1 < (1usize << rbits.len()));
    let donors = bank(raw,rbits,enable,flag,pre,temps,dirty);
    rec(b, |b| {
        let mut dec=Dec::new(rbits,pre);
        for v in range.0..=range.1 {
            let mut lits=dec.ctrls(b,v); lits.extend_from_slice(enable);
            mc_xor(b,&lits,flag,temps,&donors);
            b.ccx(flag,raw[v+1],raw[v]); b.cx(flag,raw[v]);
            mc_xor(b,&lits,flag,temps,&donors);
        }
        dec.clear(b);
    })
}

/// Complete raw POST -> compact POST, returning the supplied extra owner.
#[allow(clippy::too_many_arguments)]
pub(crate) fn compress_post_record(b: &mut B, raw: &[QubitId], rbits: &[QubitId],
    range: (usize,usize), enable: &[(QubitId,bool)], flag: QubitId,
    pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    let n=normalize_post_record(b,raw,rbits,range,enable,flag,pre,temps,dirty);
    let e=expand_post_record(b,raw,rbits,range,enable,flag,pre,temps,dirty);
    rec(b,|b| { b.play(&n,false); b.play(&e,true); })
}

/// POST compression when the remainder size exists only as an affine
/// sum-frame query. `xor_eq` must XOR the COMPLETE phase-gated predicate
/// [B==v] into flag, preserve all size/phase ports, and return its scratch
/// on every call. Thus HR can use the existing sumframe::xor_raw_eq while
/// SY7 is payload data; HT can compare SYlow7 with128 represented by zero.
/// Neither query may read SY7 or any raw payload lane as metadata.
///
/// Four exact equality toggles per public value (two for normalization,
/// two for the swap walk) return flag even outside the public interval.
/// The conservative closure ABI deliberately keeps no live prefix across
/// a payload write. It may be funded later by an exact captured prefix walk.
pub(crate) fn compress_post_by_query_record(b: &mut B, raw: &[QubitId],
    range: (usize,usize), flag: QubitId,
    xor_eq: &mut dyn FnMut(&mut B,usize,QubitId)) -> Vec<G> {
    assert_eq!(raw.len(),LOGICAL_NP);
    assert_eq!(raw.iter().copied().collect::<BTreeSet<_>>().len(),LOGICAL_NP);
    assert!(!raw.contains(&flag));
    assert!(1<=range.0 && range.0<=range.1 && range.1<=256);
    rec(b,|b| {
        for v in range.0..=range.1 {
            xor_eq(b,v,flag);
            b.ccx(flag,raw[v+1],raw[v]); b.cx(flag,raw[v]);
            xor_eq(b,v,flag);
        }
        // Left-rotate the suffix B..259. Before swap i, flag is exactly
        // the XOR of the mutually exclusive matches B in[lo,i-1].
        for i in range.0+1..LOGICAL_NP {
            if i-1<=range.1 { xor_eq(b,i-1,flag); }
            b.cswap(flag,raw[i],raw[i-1]);
        }
        for v in range.0..=range.1 { xor_eq(b,v,flag); }
    })
}

/// Adjacent-hole narrowing without materializing a 259th payload lane.
/// The caller's `move_enable` includes phase and delta=[257-bl(t_next)=B+1].
/// When delta=0 the old and new omitted holes coincide and nothing is done.
/// When delta=1, compact[B] and compact[B+1] are equal sign bits; XORing
/// the latter into the former creates the PRE zero. The omission moves
/// from B to B+1 across this zero, so no physical permutation is needed.
#[allow(clippy::too_many_arguments)]
pub(crate) fn narrow_adjacent_record(b: &mut B, compact: &[QubitId],
    rbits: &[QubitId], range: (usize,usize), move_enable: &[(QubitId,bool)],
    flag: QubitId, pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(compact.len(),PHYSICAL_NP);
    assert!(1 <= range.0 && range.0 <= range.1 && range.1 <= 256);
    assert!(range.1 < (1usize << rbits.len()));
    let mut ports=BTreeSet::new();
    for q in compact.iter().chain(rbits).chain(move_enable.iter().map(|(q,_)|q))
        .chain([&flag]).chain(pre).chain(temps) {
        assert!(ports.insert(*q),"compact narrow aliases a live owner");
    }
    let mut seen=BTreeSet::new();
    let donors:Vec<_>=dirty.iter().copied()
        .filter(|q|!ports.contains(q)&&seen.insert(*q)).collect();
    assert!(donors.len()>=rbits.len()+move_enable.len());
    rec(b,|b| {
        let mut dec=Dec::new(rbits,pre);
        for v in range.0..=range.1 {
            let mut lits=dec.ctrls(b,v); lits.extend_from_slice(move_enable);
            mc_xor(b,&lits,flag,temps,&donors);
            b.ccx(flag,compact[v+1],compact[v]);
            mc_xor(b,&lits,flag,temps,&donors);
        }
        dec.clear(b);
    })
}

/// The same compact narrowing, addressed by the new coefficient size T.
/// With h=257-T, delta=1 iff Q[256-T]=0, and B=h-delta. Only delta=1
/// changes a physical lane: compact[256-T] ^= compact[257-T]. This avoids
/// probing B into another size register and also handles the final cnt=1
/// deferred narrowing before the divisor-one endpoint.
#[allow(clippy::too_many_arguments)]
pub(crate) fn narrow_from_t_record(b: &mut B, compact: &[QubitId],
    tbits: &[QubitId], range: (usize,usize), q: &[QubitId],
    enable: &[(QubitId,bool)], flag: QubitId, pre: &[QubitId],
    temps: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(compact.len(), PHYSICAL_NP);
    assert!(1 <= range.0 && range.0 <= range.1 && range.1 <= 256);
    assert!(range.1 < (1usize << tbits.len()));
    let mut ports=BTreeSet::new();
    for p in compact.iter().chain(tbits).chain(q)
        .chain(enable.iter().map(|(p,_)|p)).chain([&flag]).chain(pre).chain(temps) {
        assert!(ports.insert(*p),"compact T narrow aliases a live owner");
    }
    let mut seen=BTreeSet::new();
    let donors:Vec<_>=dirty.iter().copied()
        .filter(|p|!ports.contains(p)&&seen.insert(*p)).collect();
    assert!(donors.len()>=tbits.len()+enable.len()+1);
    rec(b,|b| {
        let mut dec=Dec::new(tbits,pre);
        for v in range.0..=range.1 {
            let bit=256-v;
            let mut lits=dec.ctrls(b,v); lits.extend_from_slice(enable);
            // Outside the physical Q width the bit is the known zero
            // above the whole remainder; no zero qubit is materialized.
            if let Some(&qb)=q.get(bit) { lits.push((qb,true)); }
            mc_xor(b,&lits,flag,temps,&donors);
            b.ccx(flag,compact[bit+1],compact[bit]);
            mc_xor(b,&lits,flag,temps,&donors);
        }
        dec.clear(b);
    })
}

/// Endpoint-only integration. Q113 is returned before the caller resumes;
/// unlike a traversal-wide raw-extra loan it is available on every endpoint
/// shot (R<2^KD, counter starts at121). The old final digit and transition
/// run on their original259-lane operands without changing arithmetic.
pub(crate) fn end_compact(b: &mut B,
    fd: &super::super::frogdrop_col::Fd,
    cp: &super::super::frogdrop_col::ColPar,
    sc: &super::super::frogdrop_col::ColScr, pl: &PlCol) {
    assert!(super::super::frogdrop_col::c665_pool4());
    assert_eq!(pl.p.len(),PHYSICAL_NP);
    assert_eq!(fd.q.len(),128,"endpoint Q113 loan needs the parent Q128 layout");
    let extra=fd.q[113];
    let raw=raw_context(pl,extra);
    let range=(cp.sz.0.max(1),cp.sz.1.min(256));
    let (flag,pre,temp)=(fd.q[100],&fd.q[104..107],fd.q[108]);
    let probe=rec(b,|b| {
        super::super::frogdrop::msb_probe_range(b,&fd.ring,range.0-1,range.1,
            &sc.sz,&fd.q[104..107],fd.q[107],&sc.dirty);
    });
    b.play(&probe,false);
    let mut finish=vec![(fd.cnt[0],false)];
    finish.extend(fd.cnt[1..].iter().map(|&p|(p,true)));
    // The counter overlaps fd.q, so pass only the arithmetic remainder
    // lanes to the direct query. Its relevant tested bit is below KD.
    let narrow=narrow_from_t_record(b,&pl.p,&sc.sz,range,&fd.q[..super::KD],
        &finish,flag,pre,&[temp],&pl.dirty);
    b.play(&narrow,false);
    let expand=expand_pre_record(b,&raw.p,&sc.sz,range,&[(fd.ph,false)],
        flag,pre,&[temp],&pl.dirty);
    b.play(&expand,false);
    b.play(&probe,true);
    // Deferred narrowing is already done in compact representation.
    super::pl_end_raw(b,fd,cp,sc,&raw,true);
    // All shots now have B=1, P0=0, P2=0 and offset P1=1. Expose and
    // delete P1; the unchanged 256-bit terminal W shifts down one lane.
    b.ccx(fd.ph,raw.p[2],raw.p[1]); b.cx(fd.ph,raw.p[1]);
    for i in 2..LOGICAL_NP { b.cswap(fd.ph,raw.p[i],raw.p[i-1]); }
}
