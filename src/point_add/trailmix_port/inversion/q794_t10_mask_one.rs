//! Known-one mask on current inherited support: before cell i, i<=lo<=A.
//! Both C1 and general T10. No new scratch, allocation or measurements.
use crate::{circuit::Op,point_add::trailmix_port::circuit::{Circuit,QReg}};
use std::cell::{Cell,RefCell};
thread_local!{static DISABLED:Cell<bool>=const{Cell::new(false)};static PACKETS:RefCell<Vec<Packet>>=const{RefCell::new(Vec::new())};}
pub(super) fn enabled()->bool{!DISABLED.with(Cell::get)&&super::super::metadata_muxlease::active("Q794_T10_KNOWN_MASK")}
pub(crate) fn checking()->bool{std::env::var_os("Q794_T10_KNOWN_MASK_CHECK").is_some()}
pub(crate) fn clear(){PACKETS.with(|p|p.borrow_mut().clear());}
pub(super) fn without<T>(f:impl FnOnce()->T)->T{struct Reset;impl Drop for Reset{fn drop(&mut self){DISABLED.with(|d|d.set(false));}}DISABLED.with(|d|assert!(!d.replace(true)));let _reset=Reset;f()}
pub(super) fn cell(circ:&mut Circuit,s:&QReg,t:&QReg,k:&QReg,inverse:bool){if !inverse{circ.cx(s,t);circ.cx(k,s);}circ.ccx(t,s,k);if inverse{circ.cx(k,s);circ.cx(s,t);}}
struct Packet{start:usize,end:usize,g:usize,decision:usize,mask:usize,rank:[usize;5],a:[usize;6],lo:usize,c1:bool,reference:Vec<Op>}
pub(super) fn capture(start:usize,end:usize,g:&QReg,decision:&QReg,mask:&QReg,rank:&[QReg],a:&[QReg],lo:usize,c1:bool,reference:Vec<Op>){
 PACKETS.with(|p|p.borrow_mut().push(Packet{start,end,g:g.id()as usize,decision:decision.id()as usize,mask:mask.id()as usize,rank:std::array::from_fn(|i|rank[i].id()as usize),a:std::array::from_fn(|i|a[i].id()as usize),lo,c1,reference}));
}
pub(crate) fn check(before:&[u64],actual:&[Op])->[usize;2]{
 use crate::sim::Simulator;use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
 let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
 PACKETS.with(|ps|{let ps=ps.borrow();assert_eq!(ps.len(),2,"both actual T10 call families required");let mut counts=[0usize;2];
  for p in ps.iter(){let mut f=Fixed;let mut sim=Simulator::new(before.len(),0,&mut f);sim.qubits.copy_from_slice(before);sim.apply_iter(actual[..p.start].iter());assert_eq!(sim.phase,0);let incoming=sim.qubits.clone();let active=incoming[p.g];
   assert_eq!(incoming[p.mask]&active,0,"actual fused entry mask is zero on guard");
   for lane in 0..64{if active>>lane&1==0{continue;}let rank=p.rank.iter().enumerate().map(|(i,&q)|(((incoming[q]>>lane)&1)as usize)<<i).sum::<usize>();let low=p.a.iter().enumerate().map(|(i,&q)|(((incoming[q]>>lane)&1)as usize)<<i).sum::<usize>();assert!(64*ts[rank][0]+low>=p.lo,"actual A violates inherited support");}
   for flip in [false,true]{let mut input=incoming.clone();if flip{input[p.decision]^=u64::MAX;}sim.qubits.copy_from_slice(&input);sim.apply_iter(p.reference.iter());assert_eq!(sim.phase,0);let want=sim.qubits.clone();sim.qubits.copy_from_slice(&input);sim.apply_iter(actual[p.start..p.end].iter());assert_eq!(sim.qubits,want,"known-mask fused reference c1={} flip={flip}",p.c1);assert_eq!(sim.phase,0);sim.apply_iter(actual[p.start..p.end].iter().rev());assert_eq!(sim.qubits,input);assert_eq!(sim.phase,0);}
   counts[usize::from(!p.c1)]+=active.count_ones()as usize;
  }counts
 })
}
