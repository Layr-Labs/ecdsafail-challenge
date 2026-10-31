//! Exact wrapped addition with measured block-carry erasure. No truncated
//! comparison: each outgoing carry is reconstructed from every post-sum bit,
//! the entire source block, and the still-live incoming carry.
use super::{Builder,modular,compare};
use crate::circuit::QubitId;

fn and_phase(c:&mut Builder,bits:&[QubitId]){
    assert!(bits.len()>=2);if bits.len()==2{c.cz(bits[0],bits[1]);return;}
    let work=c.alloc_qubits(bits.len()-2);c.ccx(bits[0],bits[1],work[0]);
    for i in 1..work.len(){c.ccx(work[i-1],bits[i+1],work[i]);}c.cz(work[work.len()-1],bits[bits.len()-1]);
    for i in(0..work.len()).rev(){let m=c.alloc_bit();c.hmr(work[i],m);let a=if i==0{bits[0]}else{work[i-1]};c.cz_if(a,bits[i+1],m);c.free_bit(m);c.release_clean(work[i]);}
}
fn erase(c:&mut Builder,flag:QubitId,source:&[QubitId],sum:&[QubitId],incoming:Option<QubitId>){
    if !source.is_empty()&&sum.len()>1{assert_eq!(source.len(),sum.len());compare::erase_with_compare(c,flag,sum,source,incoming);return;}
    let m=c.alloc_bit();c.hmr(flag,m);c.push_condition(m);c.x_all(sum);
    if source.is_empty(){let mut controls=sum.to_vec();controls.push(incoming.expect("zero source block has incoming carry"));and_phase(c,&controls);}
    else{assert_eq!(sum.len(),1);c.cz(source[0],sum[0]);if let Some(q)=incoming{c.cz(source[0],q);c.cz(sum[0],q);}}
    c.x_all(sum);c.pop_condition();c.free_bit(m);
}
pub(crate) fn add(c:&mut Builder,a:&[QubitId],b:&[QubitId],incoming:Option<QubitId>,negative:bool,chunk:usize){
    assert!(!a.is_empty()&&a.len()<=b.len()&&chunk>=1);if negative{c.x_all(b);}
    if b.len()<=chunk{modular::ripple_add(c,a,b,incoming,None);if negative{c.x_all(b);}return;}
    // End a source block exactly at a.len(); no repeated zero aliases enter a
    // comparison. Above it, one clean zero is reused by the native ripple.
    let zero=if a.len()<b.len(){Some(c.alloc_qubit())}else{None};let mut stages=Vec::new();let mut at=0;let mut previous=incoming;
    while at<b.len(){let end=(at+chunk).min(if at<a.len(){a.len()}else{b.len()});let flag=if end<b.len(){Some(c.alloc_qubit())}else{None};
        let zeros:Vec<_>=zero.into_iter().collect();let source=if at<a.len(){&a[at..end]}else{&zeros};modular::ripple_add(c,source,&b[at..end],previous,flag);
        if let Some(q)=flag{stages.push((at,end,previous,q));}previous=flag;at=end;
    }
    // Descending order preserves each incoming boundary until its successor's
    // measurement phase is repaired. Then its own exact predicate is erased.
    for(at,end,prev,q)in stages.into_iter().rev(){let source=if at<a.len(){&a[at..end]}else{&[]};erase(c,q,source,&b[at..end],prev);c.release_clean(q);}
    if let Some(q)=zero{c.release_clean(q);}if negative{c.x_all(b);}
}
