//! Exact dirty-echo factoring of target-XOR banks. One existing dirty memo.
//! Scratch is zero on the caller's admitted domain; arbitrary elsewhere still
//! gives a pure target-XOR extension with every control and lender restored.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
fn cost(n:usize)->usize{if n<2{0}else{2*n-3}}
pub(super) fn emit(c:&mut Circuit,terms:&[Vec<(&QReg,bool)>],target:&QReg,dirty:&[QReg],scratch:&QReg)->bool{
 if terms.len()<3{return false;}let mut wires:Vec<_>=terms.iter().flatten().map(|(q,_)|*q).collect();wires.sort_by_key(|q|q.id());wires.dedup_by_key(|q|q.id());if wires.len()>32||wires.iter().any(|q|q.id()==target.id()||q.id()==scratch.id()){return false;}
 let Some(memo)=dirty.iter().find(|q|q.id()!=target.id()&&q.id()!=scratch.id()&&!wires.iter().any(|x|x.id()==q.id()))else{return false;};
 let mut cubes=Vec::<(u64,u64)>::new();for term in terms{let(mut m,mut v)=(0u64,0u64);for &(q,b)in term{let bit=1u64<<wires.iter().position(|x|x.id()==q.id()).unwrap();if m&bit!=0{return false;}m|=bit;if b{v|=bit;}}cubes.push((m,v));}
 use std::collections::{BTreeSet,HashMap};use std::sync::{Mutex,OnceLock};static CACHE:OnceLock<Mutex<HashMap<Vec<(u64,u64)>,Option<(u64,u64)>>>>=OnceLock::new();let mut cache=CACHE.get_or_init(||Mutex::new(HashMap::new())).lock().unwrap();let plan=if let Some(p)=cache.get(&cubes){*p}else{let mut candidates=BTreeSet::new();for i in 0..cubes.len(){for j in i+1..cubes.len(){let(a,av)=cubes[i];let(b,bv)=cubes[j];let m=a&b&!(av^bv);if m.count_ones()>=2{candidates.insert((m,av&m));}}}let mut best=(0usize,None);for(m,v)in candidates{let members:Vec<_>=cubes.iter().filter(|&&(a,av)|a&m==m&&av&m==v).collect();if members.len()<3{continue;}let base=members.iter().map(|(a,_)|cost(a.count_ones()as usize)).sum::<usize>();let next=2*cost(m.count_ones()as usize)+2*members.iter().map(|(a,_)|cost(1+(a&!m).count_ones()as usize)).sum::<usize>();let gain=base.saturating_sub(next);if gain>best.0{best=(gain,Some((m,v)));}}cache.insert(cubes.clone(),best.1);best.1};drop(cache);let Some((mask,value))=plan else{return false;};
 let members:Vec<_>=cubes.iter().map(|&(m,v)|m&mask==mask&&v&mask==value).collect();for(i,term)in terms.iter().enumerate(){if !members[i]{super::paired_clean_mcx::toggle(c,term,target,scratch);}}
 let factor:Vec<_>=wires.iter().enumerate().filter(|(i,_)|mask>>i&1!=0).map(|(i,q)|(*q,value>>i&1!=0)).collect();
 for _ in 0..2{super::paired_clean_mcx::toggle(c,&factor,memo,scratch);for(i,&(m,v))in cubes.iter().enumerate(){if !members[i]{continue;}let mut cs=vec![(memo,true)];cs.extend(wires.iter().enumerate().filter(|(i,_)|(m&!mask)>>i&1!=0).map(|(i,q)|(*q,v>>i&1!=0)));super::paired_clean_mcx::toggle(c,&cs,target,scratch);}}
 true
}

pub fn check(){
 use crate::{circuit::OperationType as K,sim::Simulator};use sha3::digest::XofReader;
 struct F;impl XofReader for F{fn read(&mut self,b:&mut[u8]){b.fill(0x43)}}
 let mut cases=0;
 for polarity in 0..32usize{
  let mut c=Circuit::new();let w=c.alloc_qreg_bits("bank.variables",8);let target=c.alloc_qreg("bank.target");let scratch=c.alloc_qreg("bank.scratch");let dirty=c.alloc_qreg_bits("bank.dirty",2);
  let terms:Vec<_>=(5..8).map(|j|{let mut t:Vec<_>=(0..5).map(|i|(&w[i],polarity>>i&1!=0)).collect();t.push((&w[j],true));t}).collect();
  assert!(emit(&mut c,&terms,&target,&dirty,&scratch));let ops=c.into_builder().ops;assert!(ops.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX)));
  for clean in 0..2{for first in(0..2048usize).step_by(64){
   let mut before=vec![0u64;12];let mut expected=before.clone();
   for l in 0..64{let x=first+l;for i in 0..9{before[i]|=(((x>>i)&1)as u64)<<l;}before[9]|=(clean as u64)<<l;before[10]|=(((x>>9)&1)as u64)<<l;before[11]|=(((x>>10)&1)as u64)<<l;}
   expected.clone_from(&before);for l in 0..64{let x=first+l;if x&31==polarity&&((x>>5)&7).count_ones()%2==1{expected[8]^=1u64<<l;}}
   let mut f=F;let mut sim=Simulator::new(12,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());
   if clean==0{assert_eq!(sim.qubits,expected,"bank clean contract");}else{for i in 0..12{if i!=8{assert_eq!(sim.qubits[i],before[i],"bank arbitrary scratch restoration");}}}
   assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);cases+=64;
  }}
 }eprintln!("BANK_FACTOR_NATIVE_PASS cases={cases} clean_truth=true arbitrary_scratch_controls_restored=true inverse=true phase=0");
}
