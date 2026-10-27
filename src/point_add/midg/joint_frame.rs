//! Short raw-address epochs around a complete P1 V boundary.
//!
//! Three returned owners temporarily hold raw SY5..7. A fourth is the
//! codec's single clean flag and subsequently the raw-Z address flag.
//! All four return before entering the reciprocal core. No metadata owner
//! is lent across that core, and the phase/q0 port is never touched here.

use super::joint_size::View;
use super::super::builder::B;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn raw_epoch(b:&mut B,view:&View,helpers:[QubitId;4],dirty:&[QubitId],
             body:impl FnOnce(&mut B,&[QubitId],QubitId,&[QubitId])) {
    assert!(view.normalized);
    let mut ports:BTreeSet<_>=view.ports().into_iter().collect();
    for q in helpers {assert!(ports.insert(q),"joint raw-address helper alias");}
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied()
        .filter(|q|!ports.contains(q)&&seen.insert(*q)).collect();
    let sy:Vec<_>=view.low.iter().copied().chain(helpers[..3].iter().copied()).collect();
    let codec=super::super::joint_prefix::normalized_one_flag_record(
        b,&sy,&view.high[..5],helpers[3],&bank);
    b.play(&codec,true);
    body(b,&sy,helpers[3],&bank);
    b.play(&codec,false);
}

/// Same inherited support-only raw-Z rotation, with the address bridge
/// restored before return. `code` is the original five-bit sum code.
#[allow(clippy::too_many_arguments)]
pub(super) fn rotate(b:&mut B,cycle:&[QubitId],code:&[QubitId],view:&View,
    helpers:[QubitId;4],inverse:bool,range:(usize,usize),
    dest:&BTreeSet<usize>,dirty:&[QubitId]) {
    assert!(helpers.iter().all(|q|!cycle.contains(q)&&!code.contains(q)));
    raw_epoch(b,view,helpers,dirty,|b,sy,flag,bank| {
        super::sumframe::rot_raw_clean_care(b,cycle,code,sy,inverse,bank,
            flag,range.0,range.1,dest);
    });
}

/// Exact inherited singleton raw-Z lane query in one complete address epoch.
pub(super) fn rotate_full(b:&mut B,cycle:&[QubitId],code:&[QubitId],view:&View,
    helpers:[QubitId;4],inverse:bool,dirty:&[QubitId]) {
    assert!(helpers.iter().all(|q|!cycle.contains(q)&&!code.contains(q)));
    raw_epoch(b,view,helpers,dirty,|b,sy,flag,bank| {
        super::sumframe::rot_raw_clean(b,cycle,code,sy,inverse,bank,flag);
    });
}

/// Exact inherited singleton raw-Z lane query in one complete address epoch.
#[allow(clippy::too_many_arguments)]
pub(super) fn lane_query(b:&mut B,cycle:&[QubitId],code:&[QubitId],view:&View,
    helpers:[QubitId;4],range:(usize,usize),destination:usize,
    query:Option<(QubitId,QubitId)>,dirty:&[QubitId]) {
    assert!(helpers.iter().all(|q|!cycle.contains(q)&&!code.contains(q)));
    if let Some((a,z))=query {assert!(!helpers.contains(&a)&&!helpers.contains(&z));}
    raw_epoch(b,view,helpers,dirty,|b,sy,flag,bank| {
        super::sumframe::raw_lane_query(b,cycle,code,sy,flag,range.0,range.1,
            destination,query,bank);
    });
}
