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

/// Same E+gap<j predicate without a clean threshold carry, exact on all
/// 4096 E7/gap5 words and arbitrary target/donors. Let r=(E.low5+gap)%32.
/// On E5=E6=0, overflow is C=[gap>r], so the answer is [r<j] & !C.
/// Two toggles controlled by an arbitrary donor d, on opposite sides of
/// d^=!C, give [r<j]&!C while canceling d's unknown original value.
/// All arithmetic is literally reversed before returning; no metadata,
/// phase, activity, or parked quotient passenger is left in a new view.
pub(crate) fn v_gate_no_carry(b:&mut B,meta:&SumSize,j:usize,target:QubitId,dirty:&[QubitId]){
    assert!(j<=32);
    let d=bank(meta,target,dirty);
    if j==0{return;}
    let overflow=d[0];
    let word=&meta.y[..5];
    let add=rec(b,|b|super::arith::ttk_add(b,&meta.sum,word,None,None));
    let no_overflow=rec(b,|b|{
        for &q in word{b.x(q);}
        // carry(gap + !r) is [gap>r], with carry-in zero. Both
        // arguments and the distinct borrowed helper d[1] are restored.
        super::arith::ttk_carry_u(b,&meta.sum,word,overflow,d[1]);
        for &q in word{b.x(q);}
        b.x(overflow);
    });
    let mut terms=vec![];
    let high=vec![(meta.y[5],true),(meta.y[6],true)];
    if j==32{terms.push(high);}else{
        for i in(0..5).rev(){
            if j>>i&1==0{continue;}
            let mut c:Vec<_>=((i+1)..5).map(|h|(word[h],j>>h&1==0)).collect();
            c.push((word[i],true));c.extend_from_slice(&high);terms.push(c);
        }
    }
    let echoed=rec(b,|b|for c in &terms{
        let mut c=c.clone();c.push((overflow,false));mc_xor(b,&c,target,&[],&d[2..]);
    });
    b.play(&add,false);
    b.play(&echoed,false);b.play(&no_overflow,false);
    b.play(&echoed,false);b.play(&no_overflow,true);
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

#[cfg(test)]
mod no_carry_tests{
    use super::*;

    /// Bitslice 64 independent basis states. Reject phase, measurement,
    /// classical, or opaque operations rather than silently simulating
    /// them as Boolean gates; equality then proves coherent equivalence.
    fn play(tape:&[G],state:&mut [u64]){
        for gate in tape{match *gate{
            G::X(t)=>state[t.0 as usize]^=u64::MAX,
            G::Cx(c,t)=>{let bit=state[c.0 as usize];state[t.0 as usize]^=bit;},
            G::Ccx(a,c,t)=>{let bit=state[a.0 as usize]&state[c.0 as usize];state[t.0 as usize]^=bit;},
            G::Swap(a,c)=>state.swap(a.0 as usize,c.0 as usize),
            _=>panic!("unexpected non-permutation gate in no-carry threshold"),
        }}
    }

    #[test]
    fn reciprocal_threshold_no_clean_carry_exhaustive(){
        let mut b=B::new();let q=b.alloc_n(21);
        let meta=SumSize{y:q[..7].try_into().unwrap(),sum:q[7..12].try_into().unwrap()};
        let target=q[12];let dirty=&q[13..21];
        // Nine free input bits: arbitrary target plus all eight donors.
        // Eight batches cover all 512 assignments, not random samples.
        let patterns:Vec<Vec<u64>>=(0..8usize).map(|batch|(0..9usize).map(|bit|
            (0..64usize).fold(0u64,|word,lane|
                word|((((64*batch+lane)>>bit)&1)as u64)<<lane)).collect()).collect();
        for j in 0..=32{
            let tape=rec(&mut b,|b|v_gate_no_carry(b,&meta,j,target,dirty));
            assert_eq!(b.width(),21,"threshold allocated a hidden clean owner");
            for e in 0..128usize{for gap in 0..32usize{for pattern in &patterns{
                let mut original=[0u64;21];
                for i in 0..7{if e>>i&1!=0{original[i]=u64::MAX;}}
                for i in 0..5{if gap>>i&1!=0{original[7+i]=u64::MAX;}}
                original[12..].copy_from_slice(pattern);
                let mut actual=original;play(&tape,&mut actual);
                let mut expected=original;
                if e+gap<j{expected[12]^=u64::MAX;}
                assert_eq!(actual,expected,"E={e}, gap={gap}, j={j}");
                play(&tape,&mut actual);
                assert_eq!(actual,original,"threshold query is not an involution");
            }}}
        }
    }
}
