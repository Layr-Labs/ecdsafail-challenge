//! Local folded-binary rank chart, exact dirty-helper routing. No allocation.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
const MAP:[usize;32]=[0,16,31,15,4,20,27,11,8,24,23,12,28,1,17,30,14,5,21,26,9,25,13,2,18,29,6,22,10,3,19,7];
pub(super) fn triples()->Vec<[usize;3]>{
 let old:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
 let mut ts=vec![[0;3];32];for(i,t)in old.into_iter().enumerate(){ts[MAP[i]]=t;}ts
}
fn transposition(circ:&mut Circuit,rank:&[QReg],left:usize,right:usize,dirty:&[QReg]){
 let delta=left^right;assert_ne!(delta,0);let pivot=delta.trailing_zeros()as usize;
 for b in 0..5{if b!=pivot&&delta>>b&1!=0{circ.cx(&rank[pivot],&rank[b]);}}
 let framed=if left>>pivot&1!=0{left^(delta^(1<<pivot))}else{left};
 let cs:Vec<_>=(0..5).filter(|&b|b!=pivot).map(|b|(&rank[b],framed>>b&1!=0)).collect();mixed_mcx(circ,&cs,&rank[pivot],dirty);
 for b in (0..5).rev(){if b!=pivot&&delta>>b&1!=0{circ.cx(&rank[pivot],&rank[b]);}}
}
pub(super) fn convert(circ:&mut Circuit,rank:&[QReg],dirty:&[QReg],inverse:bool){
 assert_eq!(rank.len(),5);let start=circ.b.ops.len();let mut seen=[false;32];
 for first in 0..32{if seen[first]{continue;}let mut cycle=Vec::new();let mut x=first;while !seen[x]{seen[x]=true;cycle.push(x);x=MAP[x];}
  for &next in cycle.iter().skip(1){transposition(circ,rank,first,next,dirty);}
 }if inverse{circ.b.ops[start..].reverse();}
}
fn orientation(circ:&mut Circuit,y:&[QReg],out:&QReg,dirty:&[QReg]){
 // bc XOR (b XOR c)ade XOR bc*!a*!d*!e. Cost21CCX with dirty ladders.
 circ.ccx(&y[1],&y[3],out);
 circ.cx(&y[1],&y[3]);mixed_mcx(circ,&[(&y[3],true),(&y[0],true),(&y[2],true),(&y[4],true)],out,dirty);circ.cx(&y[1],&y[3]);
 mixed_mcx(circ,&[(&y[1],true),(&y[3],true),(&y[0],false),(&y[2],false),(&y[4],false)],out,dirty);
}
/// Exact high-axis XOR translation. Missing roots are completed with
/// existing nonroot DATA, never omitted markers or new quantum allocation.
pub(super) fn gather_axis<'a>(circ:&mut Circuit,rank:&[QReg],low:&[QReg],axis:usize,mut nodes:Vec<Option<&'a QReg>>,physical:&'a[QReg],dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
 assert_eq!(nodes.len(),256);assert!(axis<3&&dirty.len()>=4);let start=circ.b.ops.len();
 for control in &low[..6]{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
  (Some(a),Some(b))=>{circ.cswap(control,a,b);Some(a)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
 });}nodes=next;}
 assert_eq!(nodes.len(),4);let present=nodes.iter().filter(|x|x.is_some()).count();assert!(present>0);
 if present==1{return(nodes.into_iter().flatten().next().unwrap(),circ.b.ops[start..].to_vec());}
 for i in 0..4{if nodes[i].is_none(){let q=physical.iter().find(|q|q.id()!=u32::MAX&&!nodes.iter().flatten().any(|p|p.id()==q.id())).expect("existing physical completion root");nodes[i]=Some(q);}}
 let roots:Vec<_>=nodes.into_iter().map(Option::unwrap).collect();
 let mut ids:Vec<_>=rank.iter().chain(low).chain(dirty).map(QReg::id).collect();ids.extend(roots.iter().map(|q|q.id()));ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"fold route aliases");
 for bit in 0..2{if axis==2&&bit==1{continue;}let control=&rank[2*axis+bit];for i in 0..4{let j=i^(1<<bit);if i<j{circ.cswap(control,roots[i],roots[j]);}}}
 let d=&dirty[0];let rest=&dirty[1..];
 for _ in 0..2{orientation(circ,rank,d,rest);circ.cswap(d,roots[0],roots[3]);circ.cswap(d,roots[1],roots[2]);}
 (roots[0],circ.b.ops[start..].to_vec())
}

pub mod verification{
 use super::*;use crate::{sim::Simulator,circuit::OperationType as K};use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
 fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
 fn put(w:&mut[u64],q:&QReg,l:usize,b:bool){w[q.id()as usize]=(w[q.id()as usize]&!(1u64<<l))|((b as u64)<<l);}
 pub fn run(){
  let mut primitive=0;let mut gather_cases=0;
  for orient in [false,true]{let mut c=Circuit::new();let rank=c.alloc_qreg_bits("rank",5);let out=c.alloc_qreg("out");let help=c.alloc_qreg_bits("dirty",8);let owned=c.b.next_qubit;
   if orient{orientation(&mut c,&rank,&out,&help);}else{convert(&mut c,&rank,&help,false);}let ops=c.b.ops;let nt=ops.iter().filter(|o|o.kind==K::CCX).count();assert_eq!(nt,if orient{21}else{216});
   for batch in 0..16{let mut rng=0xf014789u64^batch as u64;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut rng)).collect();let mut want=before.clone();
    for lane in 0..64{let x=(64*batch+lane)&31;let ov=(64*batch+lane)>>5&1!=0;for w in [&mut before,&mut want]{for i in 0..5{put(w,&rank[i],lane,x>>i&1!=0);}put(w,&out,lane,ov);}
     if orient{let sum=[1,2,1,2,1].iter().enumerate().map(|(i,v)|v*(x>>i&1)).sum::<usize>();put(&mut want,&out,lane,ov^(sum>4));}else{for i in 0..5{put(&mut want,&rank[i],lane,MAP[x]>>i&1!=0);}}
    }let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits=before.clone();sim.apply_iter(ops.iter());assert_eq!(sim.qubits,want);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);primitive+=64;
   }
  }
  for block in 0..26{let(lo,hi)=super::super::metadata_entry_head5::A_SUPPORTS[block];for family in 0..3{
   let mut c=Circuit::new();let rank=c.alloc_qreg_bits("rank",5);let low=c.alloc_qreg_bits("low",6);let word=c.alloc_qreg_bits("word",259);let help=c.alloc_qreg_bits("helpers",22);let passenger=c.alloc_qreg("passenger");let owned=c.b.next_qubit;
   let axis=if family==2{1}else{0};let values:Vec<_>=(0..256).filter(|&v|match family{0=>(lo..hi).contains(&v)||v==255,1=>v<255&&(lo..hi).contains(&v),_=>v>=2}).collect();
   let physical=|v:usize|if family==2{258-v}else{v+family+1};
   let nodes=(0..256).map(|v|values.contains(&v).then(||&word[physical(v)])).collect();
   let(root,route)=gather_axis(&mut c,&rank,&low,axis,nodes,&word[..257],&help);c.cx(root,&passenger);c.cx(&passenger,root);c.cx(root,&passenger);c.b.ops.extend(route.into_iter().rev());assert_eq!(c.b.next_qubit,owned);let ops=c.b.ops;
   for op in &ops{assert!(matches!(op.kind,K::X|K::CX|K::CCX));for h in [257,258]{let id=word[h].id()as u64;assert!(op.q_target.0!=id&&op.q_control1.0!=id&&op.q_control2.0!=id);}}
   let cases:Vec<_>=triples().iter().enumerate().flat_map(|(r,t)|(0..64).filter_map(move|l|{let v=64*t[axis]+l;values_contains(family,lo,hi,v).then_some((r,l,v))})).collect();assert!(!cases.is_empty());
   for pattern in 0..4{for batch in 0..cases.len().div_ceil(64){let mut rng=0x5f014u64^((block as u64)<<32)^((pattern as u64)<<24)^batch as u64;let mut before:Vec<_>=(0..owned).map(|_|rnd(&mut rng)).collect();let mut want=before.clone();
    for lane in 0..64{let(r,l,v)=cases[(batch*64+lane)%cases.len()];for w in [&mut before,&mut want]{for i in 0..5{put(w,&rank[i],lane,r>>i&1!=0);}for i in 0..6{put(w,&low[i],lane,l>>i&1!=0);}}
     let qi=&word[physical(v)];let a=before[qi.id()as usize]>>lane&1!=0;let b=before[passenger.id()as usize]>>lane&1!=0;put(&mut want,qi,lane,b);put(&mut want,&passenger,lane,a);
    }let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits=before.clone();sim.apply_iter(ops.iter());assert_eq!(sim.qubits,want,"fold gather block{block} family{family} pattern{pattern} batch{batch}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);gather_cases+=64;
   }}eprintln!("FOLD_GATHER block={block} family={family} PASS");
  }}eprintln!("FOLD_HELPER_PASS primitive={primitive} gather_lanes={gather_cases}; actual converter216T orientation21T, all32labels, arbitrary dirty helpers/DATA, every26support/A1/A2/C2 geometry, bothholes untouched, noallocation, phase/inverse");
 }
 fn values_contains(f:usize,lo:usize,hi:usize,v:usize)->bool{match f{0=>(lo..hi).contains(&v)||v==255,1=>v<255&&(lo..hi).contains(&v),_=>v>=2}}
}
