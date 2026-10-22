//! Three-owner no-parks coordinate for the final HR payload loop.
//!
//! Raw Q is the positive Y operand on activity; Q[Y..128] is zero and
//! x128 is globally returned. Unlike the parked frame, the cycle is Q128
//! alone. Rotate Q UP delta and ring257 DOWN delta, delta=127-E=128-Y.
//! On activity Q has no wrapped ONE, so Q'[0..128] is identical to the
//! parked Q129 frame's data portion. x128 stays globally zero.
//! Off activity both records are exact permutations; no zero assumption
//! is made about Q, ring or metadata. All inactive arithmetic is identity.

use super::builder::{B,G};
use super::cross_three::Cross;
use std::collections::BTreeSet;

fn check(c:&Cross<'_>){
    assert_eq!((c.q.len(),c.ring.len(),c.size.y.len()),(128,257,7));
    let r=c.roles;let mut seen=BTreeSet::new();
    assert!(c.q.iter().chain(c.ring).chain(&c.size.y).chain(&c.size.sum)
        .copied().chain([c.phase,r.activity,r.flight,r.work])
        .chain(c.clean_external.iter().copied()).all(|q|seen.insert(q)));
}

/// Raw Q -> normalized Q. Its inverse temporarily exposes raw Q to the
/// unchanged payload tick. E, S, PH, ring, all three scalars are untouched.
pub(crate) fn q_record(b:&mut B,c:&Cross<'_>)->Vec<G>{
    check(c);b.begin();
    for &e in &c.size.y{b.x(e);}
    for(k,&e)in c.size.y.iter().enumerate(){
        super::frogdrop::crot_up(b,e,c.q,1usize<<k);
    }
    for &e in &c.size.y{b.x(e);}
    b.end()
}

/// Enter only AFTER raw hr_payload_open and leave BEFORE finish_phase.
/// No Q parks may be introduced while this coordinate is live.
pub(crate) fn record(b:&mut B,c:&Cross<'_>)->Vec<G>{
    check(c);b.begin();
    for &e in &c.size.y{b.x(e);}
    for(k,&e)in c.size.y.iter().enumerate(){
        super::frogdrop::crot_up(b,e,c.q,1usize<<k);
        super::frogdrop::crot_up(b,e,c.ring,257-(1usize<<k));
    }
    for &e in &c.size.y{b.x(e);}
    b.end()
}

/// Q128 rotations have 2^k cycles, hence 128-2^k CSWAPs. The ring is
/// prime-length257, hence256 CSWAPs at each of the same seven stages.
pub(crate) const Q_ONE_DIRECTION_TOFFOLI:usize=769;
pub(crate) const ONE_DIRECTION_TOFFOLI:usize=2561;
