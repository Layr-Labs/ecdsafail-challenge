//! Closed numeric M=A+C routing on the existing rank5+P2 chart.
//! Quotient windows and original-chart seed roots; no extra quantum rail.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::arithmetic;
#[path="q794_r01_numeric_partial.rs"] mod chart;
fn mode()->usize{let n=std::env::var("Q794_R01_NUMERIC_ROUTE").ok().map(|s|s.parse().unwrap()).unwrap_or(0);assert!(n<=2);n}
pub(super) fn quotient_enabled()->bool{mode()>=1}
pub(super) fn seed_enabled()->bool{mode()>=2}
fn check(rank:&[QReg],a:&[QReg],c:&[QReg],cache:&QReg,word:&[QReg],dirty:&[QReg]){
 assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(c.len(),6);assert_eq!(word.len(),259);assert!(dirty.len()>=3);
 let mut ids:Vec<_>=rank.iter().chain(a).chain(c).chain(word).chain(dirty).map(QReg::id).collect();ids.push(cache.id());ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"numeric R01 route aliases");
}
fn route<'a>(circ:&mut Circuit,m:&[QReg],word:&'a[QReg],offset:usize)->&'a QReg{
 assert_eq!(m.len(),8);assert!(offset==1||offset==2);
 let mut nodes:Vec<_>=(0..256).map(|v|if v<=254&&v+offset>=2{Some(&word[v+offset])}else{None}).collect();
 for bit in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
  (Some(left),Some(right))=>{circ.cswap(&m[bit],left,right);Some(left)},
  (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
 });}nodes=next;}nodes[0].unwrap()
}
pub(super) fn quotient(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,decision:&QReg,cache:&QReg,w1:&[QReg],dirty:&[QReg]){
 check(rank,a,c,cache,w1,dirty);assert_ne!(g.id(),decision.id());
 assert!(rank.iter().chain(a).chain(c).chain(w1).chain(dirty).chain(std::iter::once(cache)).all(|q|q.id()!=g.id()&&q.id()!=decision.id()));
 let owned=circ.b.next_qubit;let word:Vec<_>=rank.iter().chain(std::iter::once(cache)).map(QReg::borrowed_alias).collect();let aa:Vec<_>=a.iter().chain(word[..2].iter()).map(QReg::borrowed_alias).collect();let mm:Vec<_>=c.iter().chain(word[2..4].iter()).map(QReg::borrowed_alias).collect();
 let start=circ.b.ops.len();chart::emit(circ,&word,dirty);arithmetic::add(circ,&aa,&mm,None,false);let root=route(circ,&mm,w1,2);let preparation=circ.b.ops[start..].to_vec();
 circ.cswap(g,root,decision);circ.b.ops.extend(preparation.into_iter().rev());assert_eq!(circ.b.next_qubit,owned);
}
/// Return original rank/cache and prepared LOW C, exactly the old gather
/// interface. Only data routing persists across the seed's metadata reads.
pub(super) fn gather_seed<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],cache:&QReg,w1:&'a[QReg],dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
 check(rank,a,c,cache,w1,dirty);let owned=circ.b.next_qubit;let word:Vec<_>=rank.iter().chain(std::iter::once(cache)).map(QReg::borrowed_alias).collect();let aa:Vec<_>=a.iter().chain(word[..2].iter()).map(QReg::borrowed_alias).collect();let mm:Vec<_>=c.iter().chain(word[2..4].iter()).map(QReg::borrowed_alias).collect();
 let start=circ.b.ops.len();chart::emit(circ,&word,dirty);let converter=circ.b.ops[start..].to_vec();arithmetic::add(circ,&aa,&mm,None,false);let root=route(circ,&mm,w1,1);
 arithmetic::add(circ,&aa,&mm,None,true);circ.b.ops.extend(converter.into_iter().rev());arithmetic::add(circ,a,c,None,false);assert_eq!(circ.b.next_qubit,owned);
 (root,circ.b.ops[start..].to_vec())
}
