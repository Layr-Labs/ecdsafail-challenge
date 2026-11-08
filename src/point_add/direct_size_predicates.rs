//! Exact affine-size predicates using one four/five-cell MAJ carry.
//! Source-only: all4096 E7/S5 states, no public/input-dependent cutoff.
use super::builder::{B,G};
use super::sum_size::SumSize;
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// Captures complement(source) followed by MAJ(source,target,carry).
/// The exposed last source bit is carry(target + !source + carry_in).
/// No helper is allocated; the complete literal inverse restores all ports.
fn carry_record(b:&mut B,source:&[QubitId],target:&[QubitId],cin:QubitId,
    invert_cin:bool)->Vec<G>{
    assert_eq!(source.len(),target.len());assert!(!source.is_empty());
    let ports:Vec<_>=source.iter().chain(target).copied().chain([cin]).collect();
    assert_eq!(ports.len(),ports.iter().collect::<BTreeSet<_>>().len());
    b.begin();for &q in source{b.x(q);}if invert_cin{b.x(cin);}
    for i in 0..source.len(){let c=if i==0{cin}else{source[i-1]};
        b.cx(source[i],target[i]);b.cx(source[i],c);b.ccx(c,target[i],source[i]);}
    b.end()
}
fn query(b:&mut B,meta:&SumSize,ctl:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    assert!(!ctl.iter().any(|p|p.0==target));
    let mut held:BTreeSet<_>=meta.y.iter().chain(&meta.sum).copied().chain([target]).collect();
    held.extend(ctl.iter().map(|p|p.0));
    let d:Vec<_>=dirty.iter().copied().filter(|q|held.insert(*q)).collect();
    mc_xor(b,ctl,target,&[],&d);
}

/// W=!PH & Z<=Y iff !PH & E.high3=111 & E.low4>=ceil(S/2).
/// carry(E.low4 + !S.high4 + !S0) is exactly that low-word comparison.
/// S0 is data, not an assumed-zero carry, and returns by the literal inverse.
/// Cost20 raw CCX: 4+4 MAJ plus one five-control dirty query12.
pub(crate) fn xor_switch(b:&mut B,meta:&SumSize,phase:QubitId,target:QubitId,dirty:&[QubitId]){
    let tape=carry_record(b,&meta.sum[1..5],&meta.y[..4],meta.sum[0],true);
    b.play(&tape,false);
    query(b,meta,&[(phase,true),(meta.y[4],false),(meta.y[5],false),
        (meta.y[6],false),(meta.sum[4],false)],target,dirty);
    b.play(&tape,true);
}

/// C=!PH & Z<=128 iff !PH & E.high2=11 & E.low5>S.
/// `zero_carry` is a returned scalar initially0. Cost18 raw CCX.
pub(crate) fn xor_crossing(b:&mut B,meta:&SumSize,phase:QubitId,target:QubitId,
    zero_carry:QubitId,dirty:&[QubitId]){
    assert_ne!(zero_carry,target);
    let tape=carry_record(b,&meta.sum,&meta.y[..5],zero_carry,false);
    b.play(&tape,false);
    query(b,meta,&[(phase,true),(meta.y[5],false),(meta.y[6],false),
        (meta.sum[4],false)],target,dirty);
    b.play(&tape,true);
}

/// HT DQ skips Z<Y iff E.high3=111 and E.low4>floor(S/2).
/// While this tape is played, S4 is the low-word excess bit; E4..E6
/// stay untouched. Caller gates its query by PH and original !DONE,
/// then plays the exact inverse BEFORE reading any other E/S predicate.
pub(crate) fn ht_excess_record(b:&mut B,meta:&SumSize,zero_carry:QubitId)->Vec<G>{
    carry_record(b,&meta.sum[1..5],&meta.y[..4],zero_carry,false)
}
