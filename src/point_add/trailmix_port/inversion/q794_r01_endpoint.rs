//! Exact all-state A_high+C_high=3 predicate, compact rank chart.
//! Dirty echo replaces eight13-control minterms; all lenders restored.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::point_add::trailmix_port::inversion::length_recompute::mixed_mcx;
const TERMS:&[(usize,usize)]=&[(4,4),(6,6),(10,10),(13,12),(14,14),(20,4),(22,6),(27,10)];
pub(super) fn enabled()->bool{std::env::var("Q794_R01_ENDPOINT_FACTOR").ok().as_deref()==Some("1")}
fn rank_predicate(circ:&mut Circuit,rank:&[QReg],out:&QReg,dirty:&[QReg]){
    for &(mask,value) in TERMS {
        let cs:Vec<_>=(0..5).filter(|&b|mask>>b&1!=0).map(|b|(&rank[b],value>>b&1!=0)).collect();
        mixed_mcx(circ,&cs,out,dirty);
    }
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,out:&QReg,dirty:&[QReg]){
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert!(dirty.len()>=9);
    let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(dirty).map(QReg::id).collect();ids.extend([p1.id(),p2.id(),out.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]));
    let flag=&dirty[0];let rest=&dirty[1..];
    for i in 0..6{circ.cx(&a[i],&c[i]);}
    let mut cs=vec![(p1,false),(p2,true),(flag,true)];cs.extend(c.iter().map(|q|(q,true)));
    rank_predicate(circ,rank,flag,rest);mixed_mcx(circ,&cs,out,rest);
    rank_predicate(circ,rank,flag,rest);mixed_mcx(circ,&cs,out,rest);
    for i in (0..6).rev(){circ.cx(&a[i],&c[i]);}
}
