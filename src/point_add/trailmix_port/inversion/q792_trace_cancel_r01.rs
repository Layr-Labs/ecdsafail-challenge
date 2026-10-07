//! Exact NCT cancellation with rollback of live read/write dependencies.
//! Inspired by welttowelt Q833 commit247621aafc3cb0581a66e4ae7c9fef6cbd91bf75.
//! Q792 already uses commuting cancellation; this removes its 2048-live-op bound.
//! Physical template interfaces are finalized before this pass. No measurements,
//! allocations, reset, classical conditions, or phase gates are admitted.
use crate::circuit::{Op,OperationType as K,NO_BIT,NO_QUBIT};
use std::collections::HashMap;
type Key=(u8,u64,u64,u64);
fn controls(op:&Op)->[u64;2]{let mut cs=[op.q_control1.0,op.q_control2.0];cs.sort_unstable();cs}
fn key(op:&Op)->Key{let cs=controls(op);(op.kind as u8,op.q_target.0,cs[0],cs[1])}
fn last(stack:&mut Vec<usize>,alive:&[bool])->Option<usize>{while stack.last().is_some_and(|&i|!alive[i]){stack.pop();}stack.last().copied()}
pub(super) fn reduce(ops:&mut Vec<Op>)->usize{
 assert!(ops.iter().all(|op|matches!(op.kind,K::X|K::CX|K::CCX)&&op.c_condition==NO_BIT&&op.c_target==NO_BIT));
 let n=ops.iter().flat_map(|op|[op.q_target,op.q_control1,op.q_control2]).filter(|&q|q!=NO_QUBIT).map(|q|q.0 as usize+1).max().unwrap_or(0);assert!(n<=2048);
 let mut readers=vec![Vec::<usize>::new();n];let mut writers=vec![Vec::<usize>::new();n];let mut same=HashMap::<Key,Vec<usize>>::new();let mut alive=vec![true;ops.len()];let mut removed=0;
 for(i,op)in ops.iter().enumerate(){let target=op.q_target.0 as usize;let cs=controls(op);assert!(cs.iter().all(|&q|q==u64::MAX||q!=target as u64));
  let previous=last(same.entry(key(op)).or_default(),&alive);
  let can=previous.is_some_and(|p|{
   last(&mut readers[target],&alive).is_none_or(|x|x<p)&&cs.iter().filter(|&&q|q!=u64::MAX).all(|&q|last(&mut writers[q as usize],&alive).is_none_or(|x|x<p))
  });
  if can{alive[previous.unwrap()]=false;alive[i]=false;removed+=2;}
  else{same.get_mut(&key(op)).unwrap().push(i);writers[target].push(i);for &q in &cs{if q!=u64::MAX{readers[q as usize].push(i);}}}
 }
 let mut at=0;ops.retain(|_|{let keep=alive[at];at+=1;keep});removed
}
pub fn run(){
 use crate::circuit::QubitId;use crate::sim::Simulator;use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x79);}}
 fn gate(kind:K,t:u64,c1:u64,c2:u64)->Op{let mut op=Op::empty();op.kind=kind;op.q_target=QubitId(t);if kind!=K::X{op.q_control1=QubitId(c1);}if kind==K::CCX{op.q_control2=QubitId(c2);}op}
 fn check(ops:Vec<Op>)->usize{let mut reduced=ops.clone();let count=reduce(&mut reduced);assert_eq!(reduced.len()+count,ops.len());let mut fixed=Fixed;let mut a=Simulator::new(8,0,&mut fixed);let mut fixed2=Fixed;let mut b=Simulator::new(8,0,&mut fixed2);
  for offset in [0usize,64,128,192]{for q in 0..8{let v=(0..64).fold(0u64,|v,l|v|((((offset+l)>>q)&1)as u64)<<l);a.qubits[q]=v;b.qubits[q]=v;}a.apply_iter(ops.iter());b.apply_iter(reduced.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);b.apply_iter(reduced.iter().rev());for q in 0..8{assert_eq!(b.qubits[q],(0..64).fold(0u64,|v,l|v|((((offset+l)>>q)&1)as u64)<<l));}}
  let mut again=reduced.clone();assert_eq!(reduce(&mut again),0);count
 }
 let x=gate(K::X,0,0,0);let cx=gate(K::CX,1,0,0);assert_eq!(check(vec![x,cx,x]),0);assert_eq!(check(vec![x,cx,cx,x]),4);
 let mut long=vec![gate(K::CCX,0,1,2)];for i in 0..4097{long.push(gate(K::CX,3+(i%3),6,0));}long.push(gate(K::CCX,0,2,1));assert!(check(long)>=2);
 let mut seed=0x83379220260912u64;let mut removed=0;for case in 0..4000{let mut ops=Vec::new();for _ in 0..16+case%64{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;let t=seed%8;let a=(t+1+(seed>>8)%7)%8;let mut b=(t+1+(seed>>16)%7)%8;if b==a{b=(b+1)%8;if b==t{b=(b+1)%8;}}let k=match(seed>>24)%3{0=>K::X,1=>K::CX,_=>K::CCX};ops.push(gate(k,t,a,b));if case%4==0&&ops.len()%3==0{ops.push(*ops.last().unwrap());}}removed+=check(ops);}
 eprintln!("Q792_TRACE_CANCEL_PASS random_programs=4000 exhaustive_inputs_per_program=256 directed_long_gap=true phase=0 inverse=true fixed_point=true removed={removed}");
}
