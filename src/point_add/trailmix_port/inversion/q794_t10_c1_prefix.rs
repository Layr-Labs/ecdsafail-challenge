//! Three existing C-high rails, borrowed only inside fused C1 T10.
//! No allocation. Dirty offguard extension is closed by exact per-cell inverses.
use crate::{circuit::Op,point_add::trailmix_port::circuit::{Circuit,QReg}};
use std::cell::{Cell,RefCell};
thread_local!{static DISABLED:Cell<bool>=const{Cell::new(false)};static PACKET:RefCell<Option<Packet>>=const{RefCell::new(None)};}
pub(super) fn enabled()->bool{!DISABLED.with(Cell::get)&&super::super::metadata_muxlease::active("Q794_T10_C1_PREFIX")}
pub(crate) fn checking()->bool{std::env::var_os("Q794_T10_C1_PREFIX_CHECK").is_some()}
pub(super) fn without<T>(f:impl FnOnce()->T)->T{
 struct Restore;impl Drop for Restore{fn drop(&mut self){DISABLED.with(|d|d.set(false));}}
 DISABLED.with(|d|assert!(!d.replace(true)));let _restore=Restore;f()
}
pub(super) struct Cache{bank:Vec<QReg>,keys:Vec<Vec<(u32,bool)>>,history:Vec<Vec<Op>>}
impl Cache{
 pub(super) fn new(bank:&[QReg])->Self{assert_eq!(bank.len(),3);Self{bank:bank.iter().map(QReg::borrowed_alias).collect(),keys:Vec::new(),history:Vec::new()}}
 pub(super) fn clear(&mut self,circ:&mut Circuit){for p in self.history.iter().rev(){circ.b.ops.extend(p.iter().rev().copied());}self.keys.clear();self.history.clear();}
 pub(super) fn equality(&mut self,circ:&mut Circuit,ordered:&[(&QReg,bool)],mask:&QReg,g:&QReg){
  let mut ids:Vec<_>=ordered.iter().map(|(q,_)|q.id()).chain(self.bank.iter().map(QReg::id)).collect();ids.extend([mask.id(),g.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"C1 prefix aliases");
  let n=ordered.len();let depth=if n<4{0}else{3.min(n-3)};let first=if n==4{2}else{3};
  let next:Vec<Vec<_>>=(0..depth).map(|i|ordered[..first+i].iter().map(|(q,p)|(q.id(),*p)).collect()).collect();
  let mut keep=0;while keep<self.keys.len()&&keep<next.len()&&self.keys[keep]==next[keep]{keep+=1;}
  for i in (keep..self.history.len()).rev(){circ.b.ops.extend(self.history[i].iter().rev().copied());}self.history.truncate(keep);
  for i in keep..depth{let start=circ.b.ops.len();if i==0{
   circ.x(g);super::super::paired_clean_mcx::toggle(circ,&ordered[..first],&self.bank[0],g);circ.x(g);
  }else{let(q,p)=ordered[first+i-1];if !p{circ.x(q);}circ.ccx(&self.bank[i-1],q,&self.bank[i]);if !p{circ.x(q);}}
   self.history.push(circ.b.ops[start..].to_vec());
  }self.keys=next;
  let mut leaf=Vec::new();if depth==0{leaf.extend_from_slice(ordered);}else{leaf.push((&self.bank[depth-1],true));leaf.extend_from_slice(&ordered[first+depth-1..]);}
  circ.x(g);super::super::paired_clean_mcx::toggle(circ,&leaf,mask,g);circ.x(g);
 }
}
struct Packet{start:usize,end:usize,g:usize,decision:usize,bank:[usize;3],reference:Vec<Op>}
pub(super) fn capture(start:usize,end:usize,g:&QReg,decision:&QReg,bank:&[QReg],reference:Vec<Op>){
 assert_eq!(bank.len(),3);PACKET.with(|p|*p.borrow_mut()=Some(Packet{start,end,g:g.id()as usize,decision:decision.id()as usize,bank:std::array::from_fn(|i|bank[i].id()as usize),reference}));
}
pub(crate) fn check(before:&[u64],actual:&[Op])->usize{
 use crate::sim::Simulator;use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
 PACKET.with(|p|{let p=p.borrow();let p=p.as_ref().expect("C1 packet captured before T10 cancellation");let mut f=Fixed;let mut sim=Simulator::new(before.len(),0,&mut f);
  sim.qubits.copy_from_slice(before);sim.apply_iter(actual[..p.start].iter());assert_eq!(sim.phase,0);let incoming=sim.qubits.clone();let active=incoming[p.g];
  for &q in &p.bank{assert_eq!(incoming[q]&active,0,"actual caller C1 bank not clean");}
  for flip in [false,true]{for dirty in [false,true]{let mut input=incoming.clone();if flip{input[p.decision]^=u64::MAX;}if dirty{for(i,&q)in p.bank.iter().enumerate(){let pattern=[0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0][i];input[q]=(input[q]&active)|(pattern&!active);}}
   sim.qubits.copy_from_slice(&input);sim.apply_iter(p.reference.iter());assert_eq!(sim.phase,0);let want=sim.qubits.clone();
   sim.qubits.copy_from_slice(&input);sim.apply_iter(actual[p.start..p.end].iter());assert_eq!(sim.qubits,want,"fused C1 prefix/reference decision flip={flip} dirty={dirty}");assert_eq!(sim.phase,0);
   for &q in &p.bank{assert_eq!(sim.qubits[q],input[q],"C1 bank return");}
   sim.apply_iter(actual[p.start..p.end].iter().rev());assert_eq!(sim.qubits,input);assert_eq!(sim.phase,0);
  }}active.count_ones()as usize
 })
}
