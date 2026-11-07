//! Final HR payload transition in one complete Q/ring/P coordinate.
//!
//! The raw post word is U=2^(L-1)-1-Wpost, L=259-bitlen(r). With
//! Rt+rT=p, q=floor(R/r), PRE W in[-T,t), every intermediate partial
//! natural quotient a in[0,q] obeys 0<=U+a*t<2^L. Thus the carry at
//! the true W/d boundary is zero, even though d above it is arbitrary.
//! After Q128 UP delta and P259 DOWN delta (delta=128-Y), this true
//! boundary is at reverse-word position160-S, S=bitlen(r)+Y-226.
//! A fixed161-k target therefore preserves every d passenger above it.

use super::builder::{B,G};
use super::cross_four::Cross;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// Software-only view of an already-open PH-as-payload session. No new
/// quantum owner or callback is introduced into no-payload traversals.
pub(crate) trait PayloadPorts{
    fn hr_payload_word(&self)->&[QubitId];
}

fn check(c:&Cross<'_>,raw:&[QubitId]){
    assert_eq!((raw.len(),c.q.len(),c.ring.len(),c.size.y.len()),(259,128,257,7));
    assert_eq!(raw[258],c.phase);let r=c.roles;let mut seen=BTreeSet::new();
    assert!(raw.iter().chain(c.q).chain(c.ring).chain(&c.size.y).chain(&c.size.sum)
        .copied().chain([r.activity,r.flight,r.mask,r.x128])
        .chain(c.clean_external.iter().copied()).all(|q|seen.insert(q)));
}

/// Enter only after raw payload digit and after both Q park families have
/// returned. The same E/S must survive through the exact inverse record.
/// PH belongs to `raw`, never to phase/activity logic in this lifetime.
pub(crate) fn frame_record(b:&mut B,c:&Cross<'_>,raw:&[QubitId])->Vec<G>{
    check(c,raw);let qr=super::normalized_cross_unparked_frame::record(b,c);
    b.begin();b.play(&qr,false);
    for &e in &c.size.y{b.x(e);}
    for(k,&e)in c.size.y.iter().enumerate(){
        super::frogdrop::crot_up(b,e,raw,259-(1usize<<k));
    }
    for &e in &c.size.y{b.x(e);}
    b.end()
}

/// Add e*2^k*t to the complete offset W word. Caller supplies the actual
/// natural q bits in ascending k: accumulated partial a never exceeds q.
/// e=>original activity; e0 makes this entire ripple identity on arbitrary
/// inactive data/carry. Return activity, mask and x128; retain flight e.
pub(crate) fn tick(b:&mut B,c:&Cross<'_>,raw:&[QubitId],k:usize){
    check(c,raw);assert!(k<30);let r=c.roles;
    let target:Vec<_>=(k..161).map(|i|raw[258-i]).collect();
    let(low,tail)=target.split_at(128);assert_eq!(tail.len(),33-k);
    let mut held:BTreeSet<_>=raw.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum)
        .copied().chain([r.activity,r.flight,r.mask,r.x128])
        .chain(c.clean_external.iter().copied()).collect();
    let bank:Vec<_>=c.dirty.iter().chain(c.ring).copied().filter(|q|held.insert(*q)).collect();
    assert!(bank.len()>=tail.len()+1);
    // On e1 original A is one, so X(A) is zero carry. On e0 the
    // unconditional up/down pass restores arbitrary carry and all cells.
    b.x(r.activity);
    let mut mid=|b:&mut B|{
        b.ccx(r.flight,c.q[127],r.mask);
        super::frogdrop::inc_mixed(b,r.mask,tail,&[],&bank);
        b.ccx(r.flight,c.q[127],r.mask);
    };
    let mut gate=|_b:&mut B,i:Option<usize>|i.map(|_|r.flight);
    // Normalization places all active source ones in the upper Y cells.
    // Below the public Y maximum the source and incoming carry are zero,
    // so the omitted prefix is an identity on the complete target word.
    // Off flight, MAJ/restore cancels even with arbitrary inactive data.
    let first=128-c.y_bounds.1;
    super::payload::ripple(b,&low[first..],&c.q[first..],r.activity,false,&mut mid,&mut gate);
    b.x(r.activity);
}

pub(crate) const PAYLOAD_FRAME_PAIR_TOFFOLI:usize=3612;
pub(crate) const COMPLETE_FRAME_PAIR_TOFFOLI:usize=8734;
