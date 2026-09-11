//! Exact all32 folded-rank C-high/S-high zero predicates.
//! Default-OFF experimental bank; no reachable-only or clean-rail premise.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::point_add::trailmix_port::inversion::length_recompute::mixed_mcx;
const C_ZERO:&[(usize,usize)]=&[(0,0),(4,4),(8,8),(14,12),(31,29)];
const S_ZERO:&[(usize,usize)]=&[(16,0),(26,10),(31,10)];
pub(super) fn enabled()->bool{std::env::var("Q794_SIGN_PREDICATES").ok().as_deref()==Some("1")}
fn rank_zero(circ:&mut Circuit,rank:&[QReg],target:&QReg,dirty:&[QReg]){
    for &(mask,value) in C_ZERO {
        let cs:Vec<_>=(0..5).filter(|&i|mask>>i&1!=0).map(|i|(&rank[i],value>>i&1!=0)).collect();
        mixed_mcx(circ,&cs,target,dirty);
    }
}
pub(super) fn c1(circ:&mut Circuit,rank:&[QReg],low:&[QReg],guard:&QReg,out:&QReg,dirty:&[QReg]){
    assert_eq!(rank.len(),5);assert_eq!(low.len(),6);assert!(dirty.len()>=8);
    let mut ids:Vec<_>=rank.iter().chain(low).chain(dirty).map(QReg::id).collect();ids.extend([guard.id(),out.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]));
    let flag=&dirty[0];let rest=&dirty[1..];
    let mut cs=vec![(guard,true),(flag,true)];cs.extend(low.iter().enumerate().map(|(i,q)|(q,i==0)));
    // Dirty echo: [d XOR highzero]*base XOR d*base = highzero*base.
    // All metadata controls remain unchanged and the borrowed flag returns.
    rank_zero(circ,rank,flag,rest);mixed_mcx(circ,&cs,out,rest);
    rank_zero(circ,rank,flag,rest);mixed_mcx(circ,&cs,out,rest);
}
pub(super) fn szero_swap(circ:&mut Circuit,rank:&[QReg],sm:&[QReg],guard:&QReg,cache:&QReg,left:&QReg,right:&QReg,dirty:&[QReg]){
    assert_eq!(rank.len(),5);assert_eq!(sm.len(),4);assert!(dirty.len()>=8);
    let mut ids:Vec<_>=rank.iter().chain(sm).chain(dirty).map(QReg::id).collect();ids.extend([guard.id(),cache.id(),left.id(),right.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]));
    for &(mask,value) in S_ZERO {
        let mut cs=vec![(guard,true),(cache,true)];cs.extend(sm.iter().map(|q|(q,false)));
        cs.extend((0..5).filter(|&i|mask>>i&1!=0).map(|i|(&rank[i],value>>i&1!=0)));
        circ.cx(right,left);cs.push((left,true));mixed_mcx(circ,&cs,right,dirty);circ.cx(right,left);
    }
}
