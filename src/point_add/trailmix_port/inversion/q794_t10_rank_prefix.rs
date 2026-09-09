//! General T10 only: conditional rank banks and an address-bit child bank.
//! Full-space target-XOR prefixes; retain high selector. No allocation/HMR.
use crate::{circuit::Op,point_add::trailmix_port::circuit::{Circuit,QReg}};
use std::cell::{Cell,RefCell};
thread_local!{static DISABLED:Cell<bool>=const{Cell::new(false)};static PACKET:RefCell<Option<Packet>>=const{RefCell::new(None)};}
pub(super) fn enabled()->bool{!DISABLED.with(Cell::get)&&super::super::metadata_muxlease::active("Q794_T10_RANK_PREFIX")}
pub(crate) fn checking()->bool{let on=std::env::var_os("Q794_T10_RANK_PREFIX_CHECK").is_some();if on{assert!(std::env::var_os("Q794_T10_C1_PREFIX_CHECK").is_none()&&std::env::var_os("Q794_T10_KNOWN_MASK_CHECK").is_none(),"run rank-prefix checkpoint independently of other nested CHECK diagnostics");}on}
pub(super) fn without<T>(f:impl FnOnce()->T)->T{struct Reset;impl Drop for Reset{fn drop(&mut self){DISABLED.with(|d|d.set(false));}}DISABLED.with(|d|assert!(!d.replace(true)));let _r=Reset;f()}
fn exact_t(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*n-8}}
fn clean_t(n:usize)->usize{if n<2{0}else{2*n-3}}
fn key(v:usize,bits:&[usize])->usize{bits.iter().enumerate().map(|(i,&b)|((v>>b)&1)<<i).sum()}

struct Plan{high:usize,root:Vec<usize>,low:[usize;2],second_rank:bool,selector:bool}
impl Plan{
 fn choose(high:usize,lo:usize,hi:usize,n:usize)->Option<Self>{
  if std::env::var("Q796_PREFIX_FACTORS").ok().as_deref()==Some("0"){return None;}
  let left=lo.max(high*64);let right=hi.min((high+1)*64);if left>=right{return None;}
  let bits:Vec<_>=(0..6).rev().filter(|&i|(left>>i)!=((right-1)>>i)).collect();
  if bits.len()<4{return None;}
  let values:Vec<_>=(left.max(1)..right.min(n-1)).collect();if values.is_empty(){return None;}
  let selector=lo/64!=(hi-1)/64;let root=bits[..bits.len()-2].to_vec();let low=[bits[bits.len()-2],bits[bits.len()-1]];
  let changes=values.windows(2).filter(|p|key(p[0],&root)!=key(p[1],&root)).count();
  let root_t=2*exact_t(root.len())+changes*exact_t(root.len()-1);
  let original=values.len()*clean_t(usize::from(selector)+bits.len());
  let mut best=None;let mut best_t=original;
  for second_rank in [false,true]{if second_rank&&high<2{continue;}
   let chart=match(high,second_rank){(1,_)=>10,(2,true)=>8,_=>0};
   let child=if second_rank{2}else{2*(changes+1)};
   let total=values.len()*clean_t(usize::from(selector)+2)+root_t+child+chart;
   if total<best_t{best_t=total;best=Some(Self{high,root:root.clone(),low,second_rank,selector});}
  }best
 }
}
fn minterm(c:&mut Circuit,a:&[QReg],bits:&[usize],value:usize,out:&QReg,dirty:&[QReg]){
 let cs:Vec<_>=bits.iter().enumerate().map(|(i,&b)|(&a[b],value>>i&1!=0)).collect();super::super::length_recompute::mixed_mcx(c,&cs,out,dirty);
}
fn transition(c:&mut Circuit,a:&[QReg],bits:&[usize],old:usize,new:usize,out:&QReg,dirty:&[QReg]){
 if old==new{return;}let delta=old^new;let pivot=delta.trailing_zeros()as usize;
 for i in 0..bits.len(){if i!=pivot&&delta>>i&1!=0{c.cx(&a[bits[pivot]],&a[bits[i]]);}}
 let cs:Vec<_>=bits.iter().enumerate().filter(|&(i,_)|i!=pivot).map(|(i,&b)|{let v=(old>>i&1)^if delta>>i&1!=0{old>>pivot&1}else{0};(&a[b],v!=0)}).collect();
 super::super::length_recompute::mixed_mcx(c,&cs,out,dirty);
 for i in (0..bits.len()).rev(){if i!=pivot&&delta>>i&1!=0{c.cx(&a[bits[pivot]],&a[bits[i]]);}}
}
fn chart(c:&mut Circuit,rank:&[QReg],g:&QReg,high:usize,second:bool){
 let term=|c:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg|{c.x(g);super::super::paired_clean_mcx::toggle(c,cs,out,g);c.x(g);};
 match high{
  0=>{},
  1=>{c.x(&rank[3]);c.cx(&rank[3],&rank[4]);c.x(&rank[3]);term(c,&[(&rank[3],false),(&rank[2],true),(&rank[1],true),(&rank[0],true)],&rank[4]);},
  2=>{c.x(&rank[4]);if second{
   c.x(&rank[2]);c.cx(&rank[2],&rank[3]);c.x(&rank[2]);
   c.x(&rank[1]);c.x(&rank[0]);c.ccx(&rank[1],&rank[0],&rank[3]);c.x(&rank[0]);c.x(&rank[1]);
   term(c,&[(&rank[2],false),(&rank[1],false),(&rank[0],false)],&rank[3]);
  }},
  3=>{for i in 2..5{c.x(&rank[i]);}},_=>unreachable!()
 }
}
pub(super) struct Cache<'a>{plan:Plan,rank:&'a[QReg],a:&'a[QReg],g:&'a QReg,selector:&'a QReg,mask:&'a QReg,dirty:&'a[QReg],parent:Option<usize>,child:Option<usize>,chart:Vec<Op>}
impl<'a> Cache<'a>{
 pub(super) fn open(c:&mut Circuit,high:usize,lo:usize,hi:usize,n:usize,rank:&'a[QReg],a:&'a[QReg],g:&'a QReg,selector:&'a QReg,mask:&'a QReg,dirty:&'a[QReg])->Option<Self>{
  let plan=Plan::choose(high,lo,hi,n)?;
  let mut ids:Vec<_>=rank.iter().chain(a).chain(dirty).map(QReg::id).collect();ids.extend([g.id(),selector.id(),mask.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"rank prefix aliases");
  let start=c.b.ops.len();chart(c,rank,g,high,plan.second_rank);let chart=c.b.ops[start..].to_vec();
  Some(Self{plan,rank,a,g,selector,mask,dirty,parent:None,child:None,chart})
 }
 pub(super) fn high(&self)->usize{self.plan.high}
 fn child_target(&self)->&QReg{if self.plan.second_rank{&self.rank[3]}else{&self.a[self.plan.root[0]]}}
 fn normalize_child(&self,c:&mut Circuit,parent:usize){if !self.plan.second_rank&&parent&1!=0{c.x(self.child_target());}}
 fn clear_child(&self,c:&mut Circuit){if let Some(v)=self.child{minterm(c,self.a,&self.plan.low,v,self.child_target(),self.dirty);if !self.plan.second_rank{self.normalize_child(c,self.parent.unwrap());}}}
 pub(super) fn advance(&mut self,c:&mut Circuit,value:usize){
  assert_eq!(value/64,self.plan.high);let parent=key(value,&self.plan.root);let child=key(value,&self.plan.low);
  if self.parent!=Some(parent){
   if !self.plan.second_rank{self.clear_child(c);self.child=None;}
   if let Some(old)=self.parent{transition(c,self.a,&self.plan.root,old,parent,&self.rank[4],self.dirty);}else{minterm(c,self.a,&self.plan.root,parent,&self.rank[4],self.dirty);}
   self.parent=Some(parent);
  }
  if let Some(old)=self.child{transition(c,self.a,&self.plan.low,old,child,self.child_target(),self.dirty);}else{
   self.normalize_child(c,parent);minterm(c,self.a,&self.plan.low,child,self.child_target(),self.dirty);
  }self.child=Some(child);
  let mut cs=Vec::new();if self.plan.selector{cs.push((self.selector,true));}cs.extend([(&self.rank[4],true),(self.child_target(),true)]);
  c.x(self.g);super::super::paired_clean_mcx::toggle(c,&cs,self.mask,self.g);c.x(self.g);
 }
 /// Does not mutate emission state: inverse of emitted close can re-enter it.
 pub(super) fn suspend(&self,c:&mut Circuit){
  self.clear_child(c);if let Some(v)=self.parent{minterm(c,self.a,&self.plan.root,v,&self.rank[4],self.dirty);}c.b.ops.extend(self.chart.iter().rev().copied());
 }
}

struct Packet{start:usize,end:usize,g:usize,decision:usize,mask:usize,selector:usize,reference:Vec<Op>}
pub(super) fn capture(start:usize,end:usize,g:&QReg,decision:&QReg,mask:&QReg,selector:&QReg,reference:Vec<Op>){PACKET.with(|p|*p.borrow_mut()=Some(Packet{start,end,g:g.id()as usize,decision:decision.id()as usize,mask:mask.id()as usize,selector:selector.id()as usize,reference}));}
pub(crate) fn check(before:&[u64],ops:&[Op])->usize{
 use crate::sim::Simulator;use sha3::digest::XofReader;struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69);}}
 PACKET.with(|p|{let p=p.borrow();let p=p.as_ref().expect("general rank-prefix packet");let mut f=Fixed;let mut sim=Simulator::new(before.len(),0,&mut f);sim.qubits.copy_from_slice(before);sim.apply_iter(ops[..p.start].iter());assert_eq!(sim.phase,0);let input=sim.qubits.clone();let count=input[p.g].count_ones()as usize;assert_eq!(input[p.mask]&input[p.g],0,"actual general entry mask0");assert_eq!(input[p.selector]&input[p.g],0,"actual high cache entry0");
  for flip in [false,true]{let mut incoming=input.clone();if flip{incoming[p.decision]^=u64::MAX;}sim.qubits.copy_from_slice(&incoming);sim.apply_iter(p.reference.iter());assert_eq!(sim.phase,0);let want=sim.qubits.clone();sim.qubits.copy_from_slice(&incoming);sim.apply_iter(ops[p.start..p.end].iter());assert_eq!(sim.qubits,want,"rank-prefix general allwire flip={flip}");assert_eq!(sim.phase,0);sim.apply_iter(ops[p.start..p.end].iter().rev());assert_eq!(sim.qubits,incoming);assert_eq!(sim.phase,0);}
  count
 })
}
