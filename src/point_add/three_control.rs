//! Ancilla-free predicates for the three-owner schedule.
//!
//! Every dirty donor is restored by the literal MCX implementation.  No
//! predicate result is retained across a data operation.
use super::builder::{B,G};
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;
pub(crate) type Term=Vec<(QubitId,bool)>;
pub(crate) fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
pub(crate) fn range(w:&[QubitId],mut lo:usize,hi:usize)->Vec<Term>{
    assert!(lo<=hi&&hi<=1usize<<w.len());let mut out=vec![];
    while lo<hi{let mut n=if lo==0{w.len()}else{lo.trailing_zeros()as usize};
        n=n.min(w.len());while lo+(1usize<<n)>hi{n-=1;}
        out.push((n..w.len()).map(|i|(w[i],lo>>i&1==0)).collect());lo+=1usize<<n;
    }out
}
pub(crate) fn merged(a:&[(QubitId,bool)],z:&[(QubitId,bool)])->Option<Term>{
    let mut t=a.to_vec();for &(q,n) in z{if let Some(p)=t.iter().find(|p|p.0==q){
        if p.1!=n{return None;}
    }else{t.push((q,n));}}Some(t)
}
pub(crate) fn literal(b:&mut B,c:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    assert!(!c.iter().any(|p|p.0==target));let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied().filter(|q|*q!=target&&!c.iter().any(|p|p.0==*q)&&seen.insert(*q)).collect();
    mc_xor(b,c,target,&[],&bank);
}
pub(crate) fn xor_terms(b:&mut B,terms:&[Term],extra:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    for t in terms{if let Some(t)=merged(t,extra){literal(b,&t,target,dirty);}}
}
pub(crate) fn swap_terms(b:&mut B,terms:&[Term],extra:&[(QubitId,bool)],a:QubitId,z:QubitId,dirty:&[QubitId]){
    if a==z{return;}for t in terms{if let Some(mut t)=merged(t,extra){
        assert!(!t.iter().any(|p|p.0==a||p.0==z));b.cx(a,z);t.push((z,false));literal(b,&t,a,dirty);b.cx(a,z);
    }}
}
pub(crate) fn inc(b:&mut B,word:&[QubitId],control:&[(QubitId,bool)],dirty:&[QubitId]){
    for i in (0..word.len()).rev(){let mut c=control.to_vec();c.extend(word[..i].iter().map(|&q|(q,false)));literal(b,&c,word[i],dirty);}
}
