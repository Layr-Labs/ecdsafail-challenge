//! C-high=0-specific closed routing. No rank mutation or new qubits.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
const A: [&[(u16,u16)];2]=[&[(20,0),(8,8),(4,0)],&[(12,8),(20,20)]];
const S: [&[(u16,u16)];4]=[
 &[(17,17),(3,0),(6,2),(18,0),(4,0)],
 &[(5,4),(3,1),(10,8)],
 &[(9,9),(5,0),(3,1),(6,0)],
 &[(20,0),(5,0),(3,1),(10,8)],
];
fn toggle(c:&mut Circuit,rank:&[QReg],terms:&[(u16,u16)],out:&QReg,extra:Option<&QReg>,dirty:&[QReg]) {
 for &(m,v) in terms {
  let mut cs:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)).collect();
  if let Some(q)=extra{cs.push((q,true));}
  mixed_mcx(c,&cs,out,dirty);
 }
}
pub(super) fn s_equal(c:&mut Circuit,rank:&[QReg],h:usize,out:&QReg,dirty:&[QReg]) {toggle(c,rank,S[h],out,None,dirty);}
pub(super) fn mode()->usize {let n=std::env::var("Q794_R00_ENDPOINTS").ok().map(|v|v.parse().unwrap()).unwrap_or(0);assert!(n<=2);n}
/// mode1: C1/C4 temporary numeric A-high. mode2: direct formula swaps.
/// Active caller must prove C=0 and both caches zero. Offguard use requires
/// either an inactive history center or the COMPLETE paired-loan conjugation
/// L W center W^-1 L; an individual upper loan need not be identity there.
pub(super) fn gather<'a>(c:&mut Circuit,rank:&[QReg],a:&[QReg],word:&'a[QReg],offset:usize,cache:[&QReg;2],dirty:&[QReg],mode:usize)->(&'a QReg,Vec<crate::circuit::Op>) {
 assert!((1..=2).contains(&mode));assert!((1..=2).contains(&offset));
 for q in cache {assert!(!rank.iter().chain(a).chain(word).chain(dirty).any(|p|p.id()==q.id()));}
 assert_ne!(cache[0].id(),cache[1].id());
 let start=c.b.ops.len();let(lo,hi)=c.q797_a_support.unwrap_or((0,256));
 let mut nodes:Vec<_>=(0..256).map(|v|if (lo..hi).contains(&v)||v==255{Some(&word[v+offset])}else{None}).collect();
 for level in 0..8 {
  if level>=6&&mode==1&&nodes.chunks_exact(2).any(|p|p[0].is_some()&&p[1].is_some()) {toggle(c,rank,A[level-6],cache[level-6],None,dirty);}
  let mut next=Vec::new();
  for p in nodes.chunks_exact(2){next.push(match(p[0],p[1]){
   (Some(left),Some(right))=>{
    if level<6{c.cswap(&a[level],left,right);}
    else if mode==1{c.cswap(cache[level-6],left,right);}
    else{c.cx(right,left);toggle(c,rank,A[level-6],right,Some(left),dirty);c.cx(right,left);}
    Some(left)
   },(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
  });}
  nodes=next;
 }
 (nodes[0].unwrap(),c.b.ops[start..].to_vec())
}
