//! Exact grouped rank reflections. Full rank/flag map, no clean-rail premise.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::super::length_recompute::mixed_mcx;
pub(super) fn enabled()->bool{std::env::var("Q794_COUNTER_REFLECTION").ok().as_deref()==Some("1")}
// Group: XOR displacement, pivot, predicate on other rank bits in index order.
type Group=(usize,usize,&'static[(usize,usize)]);
const C0:&[Group]=&[(15,0,&[(15,2)]),(9,0,&[(15,6)]),(12,2,&[(15,6)]),(7,0,&[(13,9)]),(6,1,&[(15,14)])];
const C1:&[Group]=&[(4,2,&[(12,0)]),(3,0,&[(7,4)]),(5,0,&[(15,6)]),(28,2,&[(15,8),(12,8)]),(2,1,&[(14,14),(11,10)]),(13,0,&[(15,13)])];
const S0:&[Group]=&[(2,1,&[(13,1)]),(3,0,&[(15,5)]),(30,1,&[(15,8)]),(1,0,&[(14,8),(11,8)])];
const S1:&[Group]=&[(1,0,&[(15,11),(7,4),(10,8),(4,0)]),(7,0,&[(15,6)]),(3,0,&[(15,9),(7,7)]),(31,0,&[(15,8)]),(15,0,&[(15,12)])];
pub(super) fn emit(c:&mut Circuit,rank:&[QReg],flag:&QReg,dirty:&[QReg],axis:usize,offset:usize){
 assert_eq!(rank.len(),5);assert!(dirty.len()>=3);let owned=c.b.next_qubit;
 let mut ids:Vec<_>=rank.iter().chain(dirty).map(QReg::id).collect();ids.push(flag.id());ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]));
 let groups=match(axis,offset){(1,0)=>C0,(1,1)=>C1,(2,0)=>S0,(2,1)=>S1,_=>panic!("counter reflection selector")};
 for &(delta,pivot,terms) in groups{
  let others:Vec<_>=(0..5).filter(|&i|i!=pivot).collect();
  for i in 0..5{if i!=pivot&&delta>>i&1!=0{c.cx(&rank[pivot],&rank[i]);}}
  for &(mask,value) in terms{let mut cs=vec![(flag,true)];cs.extend(others.iter().enumerate().filter(|&(i,_)|mask>>i&1!=0).map(|(i,&b)|(&rank[b],value>>i&1!=0)));mixed_mcx(c,&cs,&rank[pivot],dirty);}
  for i in (0..5).rev(){if i!=pivot&&delta>>i&1!=0{c.cx(&rank[pivot],&rank[i]);}}
 }assert_eq!(c.b.next_qubit,owned);
}
