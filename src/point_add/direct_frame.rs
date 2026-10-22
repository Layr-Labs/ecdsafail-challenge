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

/// Used only INSIDE a P1 reciprocal gap epoch, S now stores g=31-Sold.
/// The threshold is Z>=257-j iff E+g<j. For j<=32 it implies E<32;
/// E5/E6 therefore gate a six-bit E.low5+g sum with one returned flag.
/// No phase/activity or parked quotient owner is read or changed.
pub(crate) fn v_gate(b:&mut B,meta:&SumSize,j:usize,target:QubitId,carry:QubitId,dirty:&[QubitId]){
    assert!(j<=32&&target!=carry);
    let mut d=bank(meta,carry,dirty);d.retain(|q|*q!=target);assert!(d.len()>=8);
    assert!(!meta.y.contains(&target)&&!meta.sum.contains(&target));
    let word:Vec<_>=meta.y[..5].iter().copied().chain([carry]).collect();
    let add=rec(b,|b|zero_extend_add(b,&meta.sum,&word,&d));
    b.play(&add,false);
    for i in(0..6).rev(){
        if j>>i&1==0{continue;}
        let mut c:Vec<_>=((i+1)..6).map(|h|(word[h],j>>h&1==0)).collect();
        c.extend([(word[i],true),(meta.y[5],true),(meta.y[6],true)]);
        mc_xor(b,&c,target,&[],&d);
    }
    b.play(&add,true);
}
