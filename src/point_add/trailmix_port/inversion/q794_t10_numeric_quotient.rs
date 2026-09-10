//! Closed operational M=A+C chart for the two general-T10 quotient windows.
//! No fused-walk changes, new rail, measurement, or offguard clean premise.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::super::metadata_arithmetic5_encoded::add;
#[path="q794_r01_numeric_partial.rs"] mod chart;
pub(super) fn enabled()->bool{std::env::var("Q794_T10_NUMERIC_QUOTIENT").ok().as_deref()==Some("1")}

fn window(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,cache:&QReg,passengers:&[&QReg],w1:&[QReg],w2:&[QReg],dirty:&[QReg],body:impl FnOnce(&mut Circuit,&[QReg])){
 assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(w1.len(),259);assert_eq!(w2.len(),259);assert!(dirty.len()>=18);
 let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(w1).chain(w2).chain(dirty).map(QReg::id).collect();ids.extend([g.id(),cache.id()]);ids.extend(passengers.iter().map(|p|p.id()));ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"numeric quotient aliases");
 let owned=circ.b.next_qubit;let word:Vec<_>=rank.iter().chain(std::iter::once(cache)).map(QReg::borrowed_alias).collect();let aa:Vec<_>=a.iter().chain(word[..2].iter()).map(QReg::borrowed_alias).collect();let mm:Vec<_>=c.iter().chain(word[2..4].iter()).map(QReg::borrowed_alias).collect();
 // On g1, cache=P2 is zero: the existing partial86 map exposes numeric
 // Ahi/Chi/Shi. On g0 its total permutation and literal inverse still close.
 let start=circ.b.ops.len();chart::emit(circ,&word,dirty);let converter=circ.b.ops[start..].to_vec();add(circ,&aa,&mm,None,false);
 body(circ,&mm);
 // The body changes no metadata. Subtract A before undoing the chart: its
 // temporary sum-coordinate word need not belong to the rank image.
 add(circ,&aa,&mm,None,true);circ.b.ops.extend(converter.into_iter().rev());assert_eq!(circ.b.next_qubit,owned);
}
fn endpoint(circ:&mut Circuit,m:&[QReg],g:&QReg,extra:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
 let mut cs=vec![(g,true)];cs.extend(m.iter().map(|q|(q,false)));cs.extend_from_slice(extra);super::gate(circ,&cs,out,dirty);
}
fn normal(circ:&mut Circuit,m:&[QReg],g:&QReg,passengers:&[&QReg],w1:&[QReg],dirty:&[QReg]){
 let start=circ.b.ops.len();let mut nodes:Vec<_>=(0..256).map(|i|if i==0{None}else{Some(&w1[i+1])}).collect();
 for bit in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
  (Some(left),Some(right))=>{circ.cswap(&m[bit],left,right);Some(left)},
  (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
 });}nodes=next;}
 let root=nodes[0].unwrap();let route=circ.b.ops[start..].to_vec();
 for &p in passengers{
  circ.cx(p,root);circ.ccx(g,root,p);
  // M=0 is the full quotient/residual endpoint on the active general lane.
  // Cancel normal exchange there; no omitted W1[257/258] is ever emitted.
  endpoint(circ,m,g,&[(root,true)],p,dirty);circ.cx(p,root);
 }
 circ.b.ops.extend(route.into_iter().rev());
}
pub(super) fn pop_and_mask(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,p:&QReg,mask:&QReg,cache:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
 window(circ,rank,a,c,g,cache,&[p,mask],w1,w2,dirty,|circ,m|{
  normal(circ,m,g,&[p,mask],w1,dirty);
  circ.cx(p,&w2[1]);endpoint(circ,m,g,&[(&w1[0],false),(&w2[1],true)],p,dirty);circ.cx(p,&w2[1]);
  endpoint(circ,m,g,&[(&w1[0],true),(&w2[0],false)],p,dirty);
  endpoint(circ,m,g,&[],&w2[258],dirty);
  circ.cx(mask,&w2[258]);endpoint(circ,m,g,&[(&w2[258],true)],mask,dirty);circ.cx(mask,&w2[258]);
 });
}
pub(super) fn mask_return(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,mask:&QReg,cache:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
 window(circ,rank,a,c,g,cache,&[mask],w1,w2,dirty,|circ,m|{
  normal(circ,m,g,&[mask],w1,dirty);
  circ.cx(mask,&w2[258]);endpoint(circ,m,g,&[(&w2[258],true)],mask,dirty);circ.cx(mask,&w2[258]);
  endpoint(circ,m,g,&[],&w2[258],dirty);
 });
}
