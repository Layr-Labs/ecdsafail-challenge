//! SOURCE-ONLY E7/S5 frames. No allocation, registration or execution.
//!
//! A single globally-zero returned flag extends E into the exact unsigned
//! byte Z-1. The temporary byte is ~(E:0)+S-31 = 224+S-E.
//! This covers ALL 4096 E/S words, including Z=256, without a ninth bit.
//! Frame boundaries always return ORIGINAL E/S; the top frame does not
//! leave S complemented. A, x128 and PH are retained external passengers.

use super::builder::{B,G};
use super::sum_size::SumSize;
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn bank(meta:&SumSize,flag:QubitId,dirty:&[QubitId])->Vec<QubitId>{
    let mut used:BTreeSet<_>=meta.y.iter().chain(&meta.sum).copied().collect();
    assert!(used.insert(flag));
    let out:Vec<_>=dirty.iter().copied().filter(|q|used.insert(*q)).collect();
    assert!(out.len()>=8);out
}
fn zero_extend_add(b:&mut B,s:&[QubitId],t:&[QubitId],dirty:&[QubitId]){
    assert!(s.len()<=t.len());let count=t.len()-s.len();
    let mut used:BTreeSet<_>=s.iter().chain(t).copied().collect();
    assert_eq!(used.len(),s.len()+t.len());
    let pad:Vec<_>=dirty.iter().copied().filter(|q|used.insert(*q)).take(count).collect();
    assert_eq!(pad.len(),count);
    let source:Vec<_>=s.iter().chain(&pad).copied().collect();
    super::arith::ttk_add(b,&source,t,None,None);
    if count==1{b.cx(pad[0],t[s.len()]);}
    else if count>1{
        let undo=rec(b,|b|super::arith::ttk_add(b,&pad,&t[s.len()..],None,None));
        b.play(&undo,true);
    }
}
pub(crate) fn z_byte_record(b:&mut B,meta:&SumSize,flag:QubitId,dirty:&[QubitId])->Vec<G>{
    let d=bank(meta,flag,dirty);
    let byte:Vec<_>=meta.y.iter().copied().chain([flag]).collect();
    rec(b,|b|{
        for &q in &byte{b.x(q);}
        zero_extend_add(b,&meta.sum,&byte,&d);
        super::frogdrop::add_const_dirty_exact(b,&byte,225,&d); // -31 modulo256
    })
}

/// Rotation direction agrees with frogdrop::rot_by: inverse moves DOWN.
/// A support is allowed only for an intervening body that touches it and
/// returns every arbitrary donor. The captured opposite frame is exact.
pub(crate) fn rotate_z_record(b:&mut B,meta:&SumSize,cycle:&[QubitId],flag:QubitId,
    range:(usize,usize),support:Option<&BTreeSet<usize>>,inverse:bool,dirty:&[QubitId])->Vec<G>{
    assert!(98<=range.0&&range.0<=range.1&&range.1<=256);
    assert!(!cycle.iter().any(|q|meta.y.contains(q)||meta.sum.contains(q)||*q==flag));
    let d=bank(meta,flag,dirty);
    let byte:Vec<_>=meta.y.iter().copied().chain([flag]).collect();
    let address=z_byte_record(b,meta,flag,&d);
    let up=rec(b,|b|{
        b.play(&address,false);
        for i in(1..cycle.len()).rev(){b.swap(cycle[i],cycle[i-1]);}
        if let Some(s)=support{
            assert!(s.iter().all(|i|*i<cycle.len()));
            let shifted=s.iter().map(|i|(i+1)%cycle.len()).collect();
            super::frogdrop::rot_by_range_care(b,cycle,&byte,range.0-1,range.1-1,
                false,&d,&shifted);
        }else{super::frogdrop::rot_by(b,cycle,&byte,false);}
        b.play(&address,true);
    });
    rec(b,|b|b.play(&up,inverse))
}

/// Exact selected raw lane on the complete public Z care; every other
/// cycle cell is restored. Partial-tree extension outside that care is a
/// permutation, not an additional metadata-domain assertion.
pub(crate) fn z_lane_record(b:&mut B,meta:&SumSize,cycle:&[QubitId],flag:QubitId,
    range:(usize,usize),destination:usize,query:Option<(QubitId,QubitId)>,dirty:&[QubitId])->Vec<G>{
    assert!(98<=range.0&&range.0<=range.1&&range.1<=256&&destination<cycle.len());
    let mut d=bank(meta,flag,dirty);
    assert!(!cycle.iter().any(|q|meta.y.contains(q)||meta.sum.contains(q)||*q==flag));
    if let Some((a,t))=query{
        assert!(a!=t&&!cycle.contains(&a)&&!cycle.contains(&t));
        assert!(!meta.y.contains(&a)&&!meta.sum.contains(&a)&&a!=flag);
        assert!(!meta.y.contains(&t)&&!meta.sum.contains(&t)&&t!=flag);
        d.retain(|q|*q!=a&&*q!=t);
    }
    assert!(d.len()>=8);
    let byte:Vec<_>=meta.y.iter().copied().chain([flag]).collect();
    let address=z_byte_record(b,meta,flag,&d);
    let leaves:Vec<_>=(range.0..=range.1).map(|z|(z-1,cycle[(destination+z)%cycle.len()])).collect();
    let mut swaps=vec![];let root=super::midg::swap_tree(&byte,&leaves,8,&mut swaps);
    rec(b,|b|{
        b.play(&address,false);
        for &(c,a,z) in &swaps{b.cswap(c,a,z);}
        if let Some((a,t))=query{b.x(root);b.ccx(a,root,t);b.x(root);}else{b.x(root);}
        for &(c,a,z) in swaps.iter().rev(){b.cswap(c,a,z);}
        b.play(&address,true);
    })
}

/// UP by min(29,31-S), with S restored before the arithmetic callback.
pub(crate) fn top_record(b:&mut B,meta:&SumSize,ring:&[QubitId],flag:QubitId,dirty:&[QubitId])->Vec<G>{
    assert_eq!(ring.len(),257);let d=bank(meta,flag,dirty);
    assert!(!ring.iter().any(|q|meta.y.contains(q)||meta.sum.contains(q)||*q==flag));
    rec(b,|b|{
        for &q in &meta.sum{b.x(q);}
        super::frogdrop::rot_by(b,ring,&meta.sum,false);
        for bit in 0..2{
            let prep=rec(b,|b|for g in 30..32{
                if ((g-29)>>bit)&1==0{continue;}
                let c:Vec<_>=meta.sum.iter().enumerate().map(|(i,&q)|(q,g>>i&1==0)).collect();
                mc_xor(b,&c,flag,&[],&d);
            });
            b.play(&prep,false);super::frogdrop::crot_up(b,flag,ring,257-(1<<bit));b.play(&prep,true);
        }
        for &q in &meta.sum{b.x(q);}
    })
}

/// Normalized Cross top bodies touch exactly ring[128..257] and ring[0..14].
/// Construct DOWN min(29,31-S) on that complete support and invert it.
/// Every other lane is a restored donor of the intervening body.
pub(crate) fn normalized_top_record(b:&mut B,meta:&SumSize,ring:&[QubitId],flag:QubitId,dirty:&[QubitId])->Vec<G>{
    use std::collections::BTreeMap;
    assert_eq!(ring.len(),257);let d=bank(meta,flag,dirty);
    assert!(!ring.iter().any(|q|meta.y.contains(q)||meta.sum.contains(q)||*q==flag));
    let mut support:BTreeSet<_>=(0..14).chain(128..257).collect();
    b.begin();for &s in &meta.sum{b.x(s);}
    for bit in 0..5{
        // Clamp30/31 to29 by changing only the lowest two control bits.
        let control=if bit<2{flag}else{meta.sum[bit]};
        let prep=rec(b,|b|if bit<2{
            b.cx(meta.sum[bit],flag);
            let terms:Vec<_>=if bit==0{(0..5).map(|i|(meta.sum[i],i==0)).collect()}
                else{(1..5).map(|i|(meta.sum[i],false)).collect()};
            mc_xor(b,&terms,flag,&[],&d);
        });
        b.play(&prep,false);
        let shift=257-(1usize<<bit);
        let mut next:BTreeMap<_,_>=support.iter().map(|&i|(i,(i+shift)%257)).collect();
        let destinations:BTreeSet<_>=next.values().copied().collect();
        for &start in support.difference(&destinations){
            let mut end=start;while support.contains(&end){end=next[&end];}
            next.insert(end,start);
        }
        let mut seen=BTreeSet::new();
        for &start in next.keys(){if seen.contains(&start){continue;}
            let(mut cycle,mut i)=(vec![],start);
            while seen.insert(i){cycle.push(i);i=next[&i];}assert_eq!(i,start);
            for k in(1..cycle.len()).rev(){b.cswap(control,ring[cycle[k]],ring[cycle[k-1]]);}
        }
        b.play(&prep,true);
        let shifted:Vec<_>=support.iter().map(|&i|(i+shift)%257).collect();support.extend(shifted);
    }
    for &s in &meta.sum{b.x(s);}let down=b.end();
    rec(b,|b|b.play(&down,true))
}

/// Used only INSIDE a P1 reciprocal gap epoch, S now stores g=31-Sold.
/// The threshold is Z>=257-j iff E+g<j. For j<=32 it implies E<32;
/// E5/E6 therefore gate a six-bit E.low5+g sum with one returned flag.
/// No phase/activity or parked quotient owner is read or changed.
pub(crate) fn v_gate(b:&mut B,meta:&SumSize,j:usize,target:QubitId,carry:QubitId,dirty:&[QubitId]){
    let d:Vec<_>=dirty.iter().copied().filter(|q|*q!=target).collect();
    let add=v_gate_prepare_record(b,meta,carry,&d);
    b.play(&add,false);
    v_gate_latched(b,meta,j,target,carry,dirty);
    b.play(&add,true);
}

/// The exact six-bit E.low5+gap coordinate may span the entire reciprocal
/// core: that body reads metadata only through v_gate_latched. Original
/// E5/E6 remain separate high-class controls; carry starts/returns zero.
pub(crate) fn v_gate_prepare_record(b:&mut B,meta:&SumSize,carry:QubitId,dirty:&[QubitId])->Vec<G>{
    let d=bank(meta,carry,dirty);
    let word:Vec<_>=meta.y[..5].iter().copied().chain([carry]).collect();
    rec(b,|b|zero_extend_add(b,&meta.sum,&word,&d))
}

/// Same threshold on the prepared coordinate, without recomputing its sum.
pub(crate) fn v_gate_latched(b:&mut B,meta:&SumSize,j:usize,target:QubitId,carry:QubitId,dirty:&[QubitId]){
    assert!(j<=32&&target!=carry);
    let mut d=bank(meta,carry,dirty);d.retain(|q|*q!=target);assert!(d.len()>=8);
    assert!(!meta.y.contains(&target)&&!meta.sum.contains(&target));
    let word:Vec<_>=meta.y[..5].iter().copied().chain([carry]).collect();
    for i in(0..6).rev(){
        if j>>i&1==0{continue;}
        let mut c:Vec<_>=((i+1)..6).map(|h|(word[h],j>>h&1==0)).collect();
        c.extend([(word[i],true),(meta.y[5],true),(meta.y[6],true)]);
        mc_xor(b,&c,target,&[],&d);
    }
}


/// Seven-bit (Z-1) residue on E. This is exact on all 4096 E/S words;
/// the caller supplies any box premise needed to select a physical lane.
pub(crate) fn z_byte7_record(b:&mut B,meta:&SumSize,dirty:&[QubitId])->Vec<G>{
    let d=bank7(meta,dirty);
    rec(b,|b|{
        for &q in &meta.y{b.x(q);}
        zero_extend_add(b,&meta.sum,&meta.y,&d);
        super::frogdrop::add_const_dirty_exact(b,&meta.y,97,&d);
    })
}

fn bank7(meta:&SumSize,dirty:&[QubitId])->Vec<QubitId>{
    let mut used:BTreeSet<_>=meta.y.iter().chain(&meta.sum).copied().collect();
    let out:Vec<_>=dirty.iter().copied().filter(|q|used.insert(*q)).collect();
    assert!(out.len()>=8);out
}

/// The low seven Z bits select the first 128 values from `floor`. For each
/// overflow value, an exact z_epoch query cancels that alias and selects
/// the true lane. `overflow` is the number of values beyond floor+127.
pub(crate) fn z_lane7_record(b:&mut B,meta:&SumSize,cycle:&[QubitId],
    floor:usize,overflow:usize,destination:usize,query:Option<(QubitId,QubitId)>,
    dirty:&[QubitId])->Vec<G>{
    assert!((98..=256).contains(&floor)&&overflow<=16);
    assert!(destination<cycle.len());
    let cap=(floor+127).min(256);
    if overflow>0{assert!(floor+127+overflow<=256);}
    assert!(!cycle.iter().any(|q|meta.y.contains(q)||meta.sum.contains(q)));
    let mut d=bank7(meta,dirty);
    if let Some((a,t))=query{
        assert!(a!=t&&!cycle.contains(&a)&&!cycle.contains(&t));
        d.retain(|q|*q!=a&&*q!=t);
    }
    assert!(d.len()>=8);
    let view=meta.z_epoch(b,&d);
    let mut leaves:Vec<_>=(floor..=cap)
        .map(|z|(z%128,cycle[(destination+z)%cycle.len()])).collect();
    leaves.sort_unstable_by_key(|x|x.0);
    let mut swaps=vec![];let root=super::midg::swap_tree(&meta.y,&leaves,7,&mut swaps);
    rec(b,|b|{
        b.play(&view,false);
        for &(c,a,z) in &swaps{b.cswap(c,a,z);}
        if let Some((a,t))=query{b.x(root);b.ccx(a,root,t);b.x(root);}else{b.x(root);}
        for &(c,a,z) in swaps.iter().rev(){b.cswap(c,a,z);}
        for z in cap+1..=cap+overflow{
            let low=cycle[(destination+z-128)%cycle.len()];
            let high=cycle[(destination+z)%cycle.len()];
            let terms=meta.z_terms(z);
            if let Some((a,t))=query{
                meta.xor_terms(b,terms.clone(),t,&[(a,false),(low,true)],&d);
                meta.xor_terms(b,terms,t,&[(a,false),(high,true)],&d);
            }else{
                meta.xor_terms(b,terms.clone(),low,&[],&d);
                meta.xor_terms(b,terms,high,&[],&d);
            }
        }
        b.play(&view,true);
    })
}

fn shifted_swaps(n:usize,shift:usize)->Vec<(usize,usize)>{
    let shift=shift%n;if shift==0{return vec![];}
    let mut seen=vec![false;n];let mut out=vec![];
    for s in 0..n{if seen[s]{continue;}
        let(mut cycle,mut i)=(vec![],s);
        while !seen[i]{seen[i]=true;cycle.push(i);i=(i+shift)%n;}
        assert_eq!(i,s);
        for k in (1..cycle.len()).rev(){out.push((cycle[k],cycle[k-1]));}
    }
    out
}

/// UP by Z using a seven-bit offset from `floor`. In a span above 128,
/// the eighth stage is folded into exact per-Z controls, without a flag.
/// The inverse is the exact inverse of this whole permutation on every word.
pub(crate) fn rotate_z7_record(b:&mut B,meta:&SumSize,cycle:&[QubitId],
    floor:usize,overflow:usize,inverse:bool,dirty:&[QubitId])->Vec<G>{
    assert!((98..=256).contains(&floor)&&overflow<=16);
    if overflow>0{assert!(floor+127+overflow<=256);}
    assert!(!cycle.iter().any(|q|meta.y.contains(q)||meta.sum.contains(q)));
    let d=bank7(meta,dirty);
    let view=meta.z_epoch(b,&d);
    let up=rec(b,|b|{
        b.play(&view,false);
        // All terms are exact and disjoint in the z_epoch view. Each swap
        // uses the CSWAP conjugation with its control distributed by term.
        let mut terms=vec![];
        for z in floor+128..=floor+127+overflow{terms.extend(meta.z_terms(z));}
        if !terms.is_empty(){for (i,j) in shifted_swaps(cycle.len(),128){
            let (a,t)=(cycle[i],cycle[j]);b.cx(t,a);
            for term in &terms{let mut c=term.clone();c.push((a,false));
                mc_xor(b,&c,t,&[],&d);}
            b.cx(t,a);
        }}
        let offset=rec(b,|b|super::frogdrop::add_const_dirty_exact(
            b,&meta.y,(128-floor%128)%128,&d));
        b.play(&offset,false);
        for (i,j) in shifted_swaps(cycle.len(),floor){b.swap(cycle[i],cycle[j]);}
        super::frogdrop::rot_by(b,cycle,&meta.y,false);
        b.play(&offset,true);
        b.play(&view,true);
    });
    rec(b,|b|b.play(&up,inverse))
}

/// The top frame's flag is the complement of the unchanged leading ONE.
pub(crate) fn normalized_top_head_record(b:&mut B,meta:&SumSize,ring:&[QubitId],
    q127:QubitId,dirty:&[QubitId])->Vec<G>{
    assert!(!ring.contains(&q127));
    rec(b,|b|{b.x(q127);
        let frame=normalized_top_record(b,meta,ring,q127,dirty);
        b.play(&frame,false);b.x(q127);
    })
}

/// Threshold on the prepared V coordinate when its sixth bit is structural 0.
pub(crate) fn v_gate_latched_const0(b:&mut B,meta:&SumSize,j:usize,
    target:QubitId,dirty:&[QubitId]){
    assert!(j<=32&&!meta.y.contains(&target)&&!meta.sum.contains(&target));
    let mut d=bank7(meta,dirty);d.retain(|q|*q!=target);assert!(d.len()>=8);
    if j==32{mc_xor(b,&[(meta.y[5],true),(meta.y[6],true)],target,&[],&d);return;}
    for i in (0..5).rev(){if j>>i&1==0{continue;}
        let mut c:Vec<_>=((i+1)..5).map(|h|(meta.y[h],j>>h&1==0)).collect();
        c.extend([(meta.y[i],true),(meta.y[5],true),(meta.y[6],true)]);
        mc_xor(b,&c,target,&[],&d);
    }
}

#[cfg(test)]
#[path="r14_k5_fixture.rs"]
mod r14_k5_fixture;
