//! Exact standard-chart C1 factor and active-g T10 parity factoring.
//! Source-only bank. Install as a public(super) child of q794_t10.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::point_add::trailmix_port::inversion::length_recompute::mixed_mcx;
const C_ZERO:&[(usize,usize)]=&[(8,8),(20,0),(18,18),(30,18),(21,20),(27,16),(31,12)];
pub(crate) fn enabled()->bool{std::env::var("Q794_T10_POLISH").ok().as_deref()==Some("1")}
fn high_zero(circ:&mut Circuit,rank:&[QReg],out:&QReg,dirty:&[QReg]){
    for &(m,v) in C_ZERO {
        let cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)).collect();
        mixed_mcx(circ,&cs,out,dirty);
    }
}
pub(super) fn c1_guard(circ:&mut Circuit,rank:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]){
    assert_eq!(rank.len(),5);assert_eq!(c.len(),6);assert!(dirty.len()>=8);
    let mut ids:Vec<_>=rank.iter().chain(c).chain(dirty).map(QReg::id).collect();ids.extend([p1.id(),p2.id(),g.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]));
    let flag=&dirty[0];let rest=&dirty[1..];
    let mut cs=vec![(p1,true),(p2,false),(flag,true)];cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));
    high_zero(circ,rank,flag,rest);mixed_mcx(circ,&cs,g,rest);
    high_zero(circ,rank,flag,rest);mixed_mcx(circ,&cs,g,rest);
}
pub(crate) fn threshold(circ:&mut Circuit,g:&QReg,carry:&QReg,source:&QReg,target:&QReg,decision:&QReg,dirty:&[QReg]){
    assert_ne!(source.id(),target.id());
    circ.cx(source,target);
    mixed_mcx(circ,&[(g,true),(carry,true),(target,true)],decision,dirty);
    circ.cx(source,target);
}
