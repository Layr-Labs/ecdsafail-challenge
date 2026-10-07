//! Exact indexed incremental substitutions. Each index entry is bound to an
//! unconditional full-state Boolean proof; hashes only prefilter exact matching.
use crate::circuit::{Op,OperationType as K,QubitId,NO_BIT,NO_QUBIT};
use std::collections::HashMap;
use std::sync::OnceLock;
struct Pattern{n:usize,sig:u64,code:&'static [[u16;4]],patch:&'static [[u16;4]]}
include!("q792_incremental_patterns_r01.rs");
const HASH_BASE:u64=0x9e3779b185ebca87;
type Bank=HashMap<(usize,u64),Vec<usize>>;
fn banks()->&'static Vec<Bank>{static B:OnceLock<Vec<Bank>>=OnceLock::new();B.get_or_init(||BANKS.iter().map(|bank|{let mut map:Bank=HashMap::new();for &ix in *bank{let p=&PATTERNS[ix];map.entry((p.code.len(),p.sig)).or_default().push(ix);}map}).collect())}
fn kind(o:&Op)->u16{match o.kind{K::X=>0,K::CX=>1,K::CCX=>2,_=>unreachable!()}}
fn matched(ops:&[Op],p:&Pattern)->Option<Vec<u64>>{
 if ops.len()!=p.code.len(){return None;}let mut ids=vec![u64::MAX;p.n];let mut n=0;let mut reverse=HashMap::with_capacity(p.n);
 for(o,row)in ops.iter().zip(p.code){let k=kind(o);if k!=row[0]||o.c_condition!=NO_BIT{return None;}
  for(z,q)in [o.q_target,o.q_control1,o.q_control2].into_iter().take(k as usize+1).enumerate(){assert_ne!(q,NO_QUBIT);let expected=row[z+1]as usize;if expected>=p.n{return None;}
   if expected==n{if reverse.insert(q.0,n).is_some(){return None;}ids[n]=q.0;n+=1;}
   else if expected>=n||ids[expected]!=q.0{return None;}
  }
 }if n==p.n{Some(ids)}else{None}
}
fn emit(row:&[u16;4],ids:&[u64])->Op{let mut o=Op::empty();o.kind=[K::X,K::CX,K::CCX][row[0]as usize];o.q_target=QubitId(ids[row[1]as usize]);if row[0]>=1{o.q_control1=QubitId(ids[row[2]as usize]);}if row[0]==2{o.q_control2=QubitId(ids[row[3]as usize]);}o.validate();o}
struct Hit{first:usize,last:usize,pattern:usize,ids:Vec<u64>,saving:usize,extra:i64}
fn pass(ops:&mut Vec<Op>,bank:&Bank)->(usize,usize){
 let n=ops.len();if n<2{return(0,0);}let mut prefix=Vec::with_capacity(n+1);prefix.push(0u64);for o in ops.iter(){prefix.push(prefix.last().unwrap().wrapping_mul(HASH_BASE).wrapping_add(kind(o)as u64+1));}
 let mut powers=vec![1u64;8194];for i in 1..powers.len(){powers[i]=powers[i-1].wrapping_mul(HASH_BASE);}
 let mut recent:HashMap<u64,Vec<usize>>=HashMap::new();let mut hits=Vec::new();
 for(i,o)in ops.iter().enumerate(){if o.kind!=K::CCX{continue;}let prior=recent.entry(o.q_target.0).or_default();prior.retain(|&p|i-p<=8192);if prior.len()>9{prior.drain(..prior.len()-9);}
  for &first in prior.iter(){let len=i-first+1;let sig=prefix[i+1].wrapping_sub(prefix[first].wrapping_mul(powers[len]));if let Some(indices)=bank.get(&(len,sig)){
    for &pattern in indices{let p=&PATTERNS[pattern];if let Some(ids)=matched(&ops[first..=i],p){let nt=p.patch.iter().filter(|r|r[0]==2).count();assert!(nt<2);hits.push(Hit{first,last:i,pattern,ids,saving:2-nt,extra:p.patch.len()as i64-2});break;}}
   }
  }prior.push(i);
 }
 if hits.is_empty(){return(0,0);}let ends:Vec<_>=hits.iter().map(|h|h.last+1).collect();let mut dp=vec![(0usize,0i64)];let mut choices=Vec::new();
 for(i,h)in hits.iter().enumerate(){let prev=ends[..i].partition_point(|&end|end<=h.first);let yes=(dp[prev].0+h.saving,dp[prev].1-h.extra);let take=yes>*dp.last().unwrap();choices.push((take,prev));dp.push(if take{yes}else{*dp.last().unwrap()});}
 let mut picked=Vec::new();let mut i=hits.len();while i>0{let(take,prev)=choices[i-1];if take{picked.push(i-1);i=prev;}else{i-=1;}}picked.reverse();let mut out=Vec::with_capacity(n);let mut at=0;
 for &ix in &picked{let h=&hits[ix];assert!(at<=h.first);out.extend_from_slice(&ops[at..h.first]);out.extend_from_slice(&ops[h.first+1..h.last]);for row in PATTERNS[h.pattern].patch{out.push(emit(row,&h.ids));}at=h.last+1;}out.extend_from_slice(&ops[at..]);
 let saved=ops.iter().filter(|o|o.kind==K::CCX).count()-out.iter().filter(|o|o.kind==K::CCX).count();assert_eq!(saved,dp.last().unwrap().0);assert_eq!(n as i64-out.len()as i64,dp.last().unwrap().1);*ops=out;(saved,picked.len())
}
pub(super) fn apply(ops:&mut Vec<Op>)->(usize,usize){
 assert!(ops.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX)&&o.c_condition==NO_BIT));let mut saved=0;let mut count=0;
 for bank in banks(){let(s,n)=pass(ops,bank);saved+=s;count+=n;}(saved,count)
}
pub fn check(){
 use crate::sim::Simulator;use sha3::digest::XofReader;struct F;impl XofReader for F{fn read(&mut self,b:&mut[u8]){b.fill(0x62)}}
 let mut seed=0x7922026091301u64;let mut cases=0;let mut long=0;
 for p in PATTERNS{assert_eq!(p.code[0][0],2);assert_eq!(p.code.last().unwrap()[0],2);let ids:Vec<_>=(0..p.n as u64).collect();let original:Vec<_>=p.code.iter().map(|r|emit(r,&ids)).collect();assert_eq!(matched(&original,p),Some(ids.clone()));
  let mut candidate=original[1..original.len()-1].to_vec();candidate.extend(p.patch.iter().map(|r|emit(r,&ids)));
  assert!(candidate.iter().filter(|o|o.kind==K::CCX).count()<original.iter().filter(|o|o.kind==K::CCX).count());
  let exhaustive=p.n<=10;let batches=if exhaustive{(1usize<<p.n).div_ceil(64)}else{long+=1;4};
  for batch in 0..batches{let state:Vec<_>=(0..p.n).map(|q|{if exhaustive{(0..64).fold(0u64,|v,l|v|(((((64*batch+l)% (1<<p.n))>>q)&1)as u64)<<l)}else{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed}}).collect();let mut f=F;let mut g=F;let mut a=Simulator::new(p.n,0,&mut f);let mut b=Simulator::new(p.n,0,&mut g);a.qubits.copy_from_slice(&state);b.qubits.copy_from_slice(&state);a.apply_iter(original.iter());b.apply_iter(candidate.iter());assert_eq!(a.qubits,b.qubits,"incremental pattern span={} n={}",p.code.len(),p.n);assert_eq!(a.phase,b.phase);b.apply_iter(candidate.iter().rev());assert_eq!(b.qubits,state);assert_eq!(b.phase,0);cases+=64;}
 }
 // End-to-end matching/selection, arbitrary wire permutations and guard rejection.
 for case in 0..128{let p=&PATTERNS[case*PATTERNS.len()/128];let ids:Vec<_>=(0..p.n as u64).rev().map(|q|q+11).collect();let original:Vec<_>=p.code.iter().map(|r|emit(r,&ids)).collect();assert_eq!(matched(&original,p),Some(ids));let mut candidate=original.clone();let(s,_)=apply(&mut candidate);assert!(s>0);let n=p.n+11;let state:Vec<_>=(0..n).map(|_|{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed}).collect();let mut f=F;let mut g=F;let mut a=Simulator::new(n,0,&mut f);let mut b=Simulator::new(n,0,&mut g);a.qubits.copy_from_slice(&state);b.qubits.copy_from_slice(&state);a.apply_iter(original.iter());b.apply_iter(candidate.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);b.apply_iter(candidate.iter().rev());assert_eq!(b.qubits,state);}
 eprintln!("INCREMENTAL_LIBRARY_NATIVE_PASS patterns={} banks={} cases={cases} long_patterns_random={long} source_symbolic_proofs=true all_wires=true inverse=true contract=unconditional",PATTERNS.len(),BANKS.len());
}
