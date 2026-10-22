//! Three-owner HR payload transition. No new owner and no PH phase read.
//! All quotient parks have returned before entry. The chosen natural
//! quotient bit e implies retained HR activity A. PH is raw payload258.
//! The full inherited target/carry tail is preserved, including DL width.

use super::builder::B;
use super::payload_three::{Context,Roles,Session};
use super::frogdrop_col::ColPar;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// Add 2^bit * Y to the reverse W word under the selected flight e.
/// Preserve e and return work globally0; original A returns intact.
/// Thus Cross can use work=x128 as its following inverse-division carry.
pub(crate) fn tick(b:&mut B,ctx:&Context<'_>,session:&Session,roles:Roles,
    cp:&ColPar,bit:usize,dirty:&[QubitId]){
    assert!(!session.ht&&session.activity==roles.activity);
    assert_eq!((session.raw.len(),ctx.q.len(),ctx.ring.len()),(259,128,257));
    assert!(bit<30&&session.phase==ctx.phase);
    assert_eq!(session.raw[..258],ctx.compact[..]);
    assert_eq!(session.raw[258],ctx.phase);
    let low=if cp.dl{cp.dlr.min(super::payload::L0P+1)}else{super::payload::L0P+1};
    let wtop=259-low;assert!(bit<wtop);
    let target:Vec<_>=(bit..wtop).map(|i|session.raw[258-i]).collect();
    let n=target.len().min(ctx.q.len());assert!(n>0);
    let source=&ctx.q[..n];let(low_word,tail)=target.split_at(n);
    let mut held:BTreeSet<_>=session.raw.iter().chain(ctx.q).chain(&ctx.meta.y)
        .chain(&ctx.meta.sum).copied().chain([roles.activity,roles.flight,roles.work]).collect();
    let bank:Vec<_>=dirty.iter().chain(ctx.ring).copied().filter(|q|held.insert(*q)).collect();
    assert!(bank.len()>=tail.len()+1);
    assert!(source.iter().all(|q|!target.contains(q)));
    // e=>A, so X(A) is zero on every enabled addition. A may be arbitrary
    // on e0 shots: the complete ripple with all writes disabled returns it.
    b.x(roles.activity);
    let mut mid=|b:&mut B|{
        if tail.is_empty(){return;}
        // The full MAJ sweep leaves its carry out in the last source cell.
        super::three_control::inc(b,tail,&[(roles.flight,false),(source[n-1],false)],&bank);
    };
    let mut gate=|_b:&mut B,i:Option<usize>|i.map(|_|roles.flight);
    super::payload::ripple(b,low_word,source,roles.activity,false,&mut mid,&mut gate);
    b.x(roles.activity);
}
