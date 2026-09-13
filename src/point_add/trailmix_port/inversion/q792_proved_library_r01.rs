//! Function-keyed unconditional library. CPU exhaustive truth and bothB50 proofs.
//! The sequence index is a fast path to complete normalized function certificates;
//! all roles are arbitrary in/out, contract=true, no prefix or clean assumption.
use crate::circuit::{Op,OperationType as K,QubitId,NO_QUBIT};
struct Pattern{n:usize,code:[u8;32],key:&'static str,replacement:&'static [[u8;4]]}
const PATTERNS:&[Pattern]=&[
Pattern{n:8,code:[1, 0, 1, 0, 2, 1, 2, 3, 1, 0, 1, 0, 1, 4, 5, 0, 2, 5, 2, 3, 1, 4, 5, 0, 1, 6, 7, 0, 2, 7, 2, 3],key:"6f956236ce1d82a131f9f4623bb16ceffe2fe1623a2e7ca7353d0a6cc30920ef",replacement:&[[1, 1, 0, 0], [1, 4, 0, 0], [1, 5, 0, 0], [1, 6, 0, 0], [1, 7, 0, 0], [2, 0, 2, 3], [1, 7, 0, 0], [1, 6, 0, 0], [1, 5, 0, 0], [1, 4, 0, 0], [1, 1, 0, 0], [1, 6, 7, 0]] },
Pattern{n:8,code:[2, 0, 1, 2, 1, 3, 0, 0, 1, 4, 5, 0, 2, 5, 1, 2, 1, 4, 5, 0, 1, 6, 7, 0, 2, 7, 1, 2, 1, 6, 7, 0],key:"20fda0d2ecb9a1b6503538afe500524ceefe090134caeff69218d55dc57f3173",replacement:&[[1, 4, 0, 0], [1, 5, 0, 0], [1, 6, 0, 0], [1, 7, 0, 0], [2, 0, 1, 2], [1, 7, 0, 0], [1, 6, 0, 0], [1, 5, 0, 0], [1, 4, 0, 0], [1, 3, 0, 0]] },
Pattern{n:7,code:[2, 0, 1, 2, 1, 1, 3, 0, 1, 2, 4, 0, 0, 5, 0, 0, 2, 0, 5, 2, 1, 2, 4, 0, 1, 6, 5, 0, 2, 0, 6, 4],key:"aba537d10500a8051885f62ce4de70c9c554164f51c644123b99ef42d7788cb8",replacement:&[[1, 1, 5, 0], [2, 0, 1, 2], [1, 1, 5, 0], [2, 0, 4, 6], [1, 6, 5, 0], [1, 1, 3, 0], [1, 0, 2, 0], [0, 5, 0, 0], [0, 6, 0, 0]] },
Pattern{n:6,code:[1, 0, 1, 0, 0, 2, 0, 0, 2, 3, 2, 0, 1, 0, 1, 0, 1, 4, 2, 0, 2, 3, 4, 1, 1, 4, 2, 0, 2, 3, 5, 0],key:"31bb84e048e32da643984e6a0b4a86dfe8b7f906c1e62a6b8d0961425ad1a5fa",replacement:&[[1, 2, 5, 0], [2, 3, 0, 2], [1, 2, 5, 0], [2, 3, 1, 4], [1, 3, 0, 0], [0, 2, 0, 0]] },
Pattern{n:7,code:[0, 0, 0, 0, 2, 1, 0, 2, 1, 2, 3, 0, 1, 4, 0, 0, 2, 1, 4, 3, 1, 4, 0, 0, 2, 1, 5, 2, 0, 6, 0, 0],key:"9baf843a444a316cc95cdf2e2651d43f896bde464614fdb11314e1193c703380",replacement:&[[1, 0, 5, 0], [1, 2, 3, 0], [2, 1, 0, 2], [1, 2, 3, 0], [1, 0, 5, 0], [2, 1, 3, 4], [1, 2, 3, 0], [1, 1, 2, 0], [0, 0, 0, 0], [0, 6, 0, 0]] },
Pattern{n:7,code:[2, 0, 1, 2, 1, 1, 3, 0, 1, 2, 4, 0, 0, 5, 0, 0, 2, 0, 5, 2, 1, 2, 4, 0, 1, 6, 5, 0, 2, 0, 4, 6],key:"aba537d10500a8051885f62ce4de70c9c554164f51c644123b99ef42d7788cb8",replacement:&[[1, 1, 5, 0], [2, 0, 1, 2], [1, 1, 5, 0], [2, 0, 4, 6], [1, 6, 5, 0], [1, 1, 3, 0], [1, 0, 2, 0], [0, 5, 0, 0], [0, 6, 0, 0]] },
Pattern{n:6,code:[1, 0, 1, 0, 0, 2, 0, 0, 2, 3, 2, 0, 1, 0, 1, 0, 1, 4, 2, 0, 2, 3, 1, 4, 1, 4, 2, 0, 2, 3, 5, 0],key:"31bb84e048e32da643984e6a0b4a86dfe8b7f906c1e62a6b8d0961425ad1a5fa",replacement:&[[1, 2, 5, 0], [2, 3, 0, 2], [1, 2, 5, 0], [2, 3, 1, 4], [1, 3, 0, 0], [0, 2, 0, 0]] },
Pattern{n:6,code:[2, 0, 1, 2, 2, 2, 3, 4, 0, 3, 0, 0, 0, 4, 0, 0, 2, 2, 3, 4, 0, 1, 0, 0, 2, 0, 1, 2, 0, 5, 0, 0],key:"e0aa90119a6ea54980d4207b6839d33eac5f5e79ae4513725d48ea61b946046e",replacement:&[[1, 3, 4, 0], [2, 0, 1, 3], [1, 3, 4, 0], [1, 2, 4, 0], [1, 2, 3, 0], [1, 0, 2, 0], [1, 0, 1, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 2, 0, 0], [0, 3, 0, 0], [0, 4, 0, 0], [0, 5, 0, 0]] },
Pattern{n:6,code:[1, 0, 1, 0, 2, 0, 1, 2, 2, 3, 0, 4, 1, 0, 1, 0, 1, 3, 0, 0, 2, 3, 0, 4, 2, 0, 1, 2, 0, 5, 0, 0],key:"ac9bf22346b073eb4a3951f9dd48b3751b4feed6dc52eea7e54f91bbc9846107",replacement:&[[1, 2, 4, 0], [2, 3, 1, 2], [1, 2, 4, 0], [1, 3, 0, 0], [0, 5, 0, 0]] },
 ];
fn emit(row:&[u8;4],ids:&[u64])->Op{let mut o=Op::empty();o.kind=[K::X,K::CX,K::CCX][row[0]as usize];o.q_target=QubitId(ids[row[1]as usize]);if row[0]>=1{o.q_control1=QubitId(ids[row[2]as usize]);}if row[0]==2{o.q_control2=QubitId(ids[row[3]as usize]);}o.validate();o}
#[derive(Clone)]struct Hit{at:usize,pattern:usize,ids:[u64;8],saving:usize,extra:i64}
fn signature(ops:&[Op])->u32{ops.iter().enumerate().fold(0,|s,(i,o)|s|((match o.kind{K::X=>0,K::CX=>1,K::CCX=>2,_=>3})<<(2*i)))}
pub(super) fn apply(ops:&mut Vec<Op>)->(usize,usize){
 if ops.len()<8{return(0,0);}let signatures:Vec<_>=PATTERNS.iter().map(|p|(0..8).fold(0u32,|s,i|s|((p.code[4*i]as u32)<<(2*i)))).collect();let mut hits=Vec::new();
 for at in 0..=ops.len()-8{let chunk=&ops[at..at+8];let sig=signature(chunk);if !signatures.contains(&sig){continue;}
  let mut ids=[u64::MAX;8];let mut n=0;let mut code=[0u8;32];let mut valid=true;
  for(i,o)in chunk.iter().enumerate(){let k=match o.kind{K::X=>0,K::CX=>1,K::CCX=>2,_=>{valid=false;break;}};code[4*i]=k;
   for(z,q)in [o.q_target,o.q_control1,o.q_control2].into_iter().take(k as usize+1).enumerate(){assert_ne!(q,NO_QUBIT);let pos=if let Some(p)=ids[..n].iter().position(|&v|v==q.0){p}else{if n==8{valid=false;break;}ids[n]=q.0;n+=1;n-1};code[4*i+1+z]=pos as u8;}if !valid{break;}
  }if !valid{continue;}
  if let Some(pattern)=PATTERNS.iter().position(|p|p.n==n&&p.code==code){let p=&PATTERNS[pattern];let old=chunk.iter().filter(|o|o.kind==K::CCX).count();let new=p.replacement.iter().filter(|r|r[0]==2).count();assert!(new<old);hits.push(Hit{at,pattern,ids,saving:old-new,extra:p.replacement.len()as i64-8});}
 }
 if hits.is_empty(){return(0,0);}let mut dp=vec![(0usize,0i64)];let mut choices=Vec::new();
 for(i,h)in hits.iter().enumerate(){let prev=hits[..i].partition_point(|v|v.at+8<=h.at);let yes=(dp[prev].0+h.saving,dp[prev].1-h.extra);let take=yes>*dp.last().unwrap();choices.push((take,prev));dp.push(if take{yes}else{*dp.last().unwrap()});}
 let mut picked=Vec::new();let mut i=hits.len();while i>0{let(take,prev)=choices[i-1];if take{picked.push(hits[i-1].clone());i=prev;}else{i-=1;}}picked.reverse();let mut out=Vec::with_capacity(ops.len());let mut at=0;
 for h in &picked{assert!(at<=h.at);out.extend_from_slice(&ops[at..h.at]);let p=&PATTERNS[h.pattern];assert_eq!(p.key.len(),64);for row in p.replacement{out.push(emit(row,&h.ids));}at=h.at+8;}out.extend_from_slice(&ops[at..]);let saved=ops.iter().filter(|o|o.kind==K::CCX).count()-out.iter().filter(|o|o.kind==K::CCX).count();assert_eq!(saved,dp.last().unwrap().0);*ops=out;(saved,picked.len())
}
pub fn check(){use crate::sim::Simulator;use sha3::digest::XofReader;struct F;impl XofReader for F{fn read(&mut self,b:&mut[u8]){b.fill(0x57)}}let mut cases=0;
 for p in PATTERNS{let ids:Vec<_>=(0..p.n as u64).collect();let original:Vec<_>=p.code.chunks_exact(4).map(|r|emit(r.try_into().unwrap(),&ids)).collect();let mut candidate=original.clone();let(saved,count)=apply(&mut candidate);assert!(saved>0&&count==1);
  for first in(0..1usize<<p.n).step_by(64){let state:Vec<_>=(0..p.n).map(|q|(0..64).fold(0u64,|v,l|v|(((((first+l)% (1<<p.n))>>q)&1)as u64)<<l)).collect();let mut f=F;let mut a=Simulator::new(p.n,0,&mut f);let mut g=F;let mut b=Simulator::new(p.n,0,&mut g);a.qubits.copy_from_slice(&state);b.qubits.copy_from_slice(&state);a.apply_iter(original.iter());b.apply_iter(candidate.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);b.apply_iter(candidate.iter().rev());assert_eq!(b.qubits,state);assert_eq!(b.phase,0);cases+=64;}
 }eprintln!("PROVED_LIBRARY_NATIVE_PASS functions=7 patterns=9 cases={cases} all_states=true all_wires=true inverse=true contract=unconditional");}
