use crate::{circuit::{Op,QubitId},sim::Simulator};
use sha3::digest::XofReader;
#[path="r00_inverse_phase.rs"] mod r00;
struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x69)}}
pub struct Packet { before_loan:usize, after_loan:usize, after_r00:usize, before_sign:usize, after_sign:usize, r00_inverse:Vec<Op>, r00_phase:Vec<Op>, pub sign_phase:Vec<Op> }
impl Packet {
 pub fn new(ops:&[Op],marks:&[(&str,usize)],sign_phase:Vec<Op>)->Self {
  let at=|s:&str|marks.iter().find(|(name,_)|*name==s).expect("missing exact raw MBU mark").1;
  let before_loan=at("mbu_before_loan");let after_loan=at("mbu_after_loan");let after_r00=at("mbu_after_r00");let before_sign=at("before_sign");let after_sign=at("mbu_after_sign");
  let producer=&ops[after_loan..after_r00];
  Self{before_loan,after_loan,after_r00,before_sign,after_sign,r00_inverse:producer.iter().rev().copied().collect(),r00_phase:r00::body(producer,QubitId(542)),sign_phase}
 }
 pub fn check(&self,ops:&[Op],before:&[u64]) {
  assert_eq!(before.len(),565);
  let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
  let mut f=Fixed;let mut sim=Simulator::new(565,0,&mut f);sim.qubits.copy_from_slice(before);
  sim.apply_iter(ops[..self.before_loan].iter());let before_loan=sim.qubits.clone();
  for lane in 0..64 {let val=|start:usize,n:usize|->usize{(0..n).map(|i|(((before_loan[start+i]>>lane)&1)as usize)<<i).sum()};let rk=val(0,5);let av=64*ts[rk][0]+val(5,6);assert_eq!(before_loan[24+av+1]>>lane&1,0,"preloan selected gap is not zero");}
  sim.apply_iter(ops[self.before_loan..self.after_loan].iter());assert_eq!(sim.qubits[542],0,"Sign was not clean after passenger loan");
  sim.apply_iter(ops[self.after_loan..self.after_r00].iter());let produced=sim.qubits.clone();
  super::q794_mbu_native::check(&produced,&self.r00_inverse,&self.r00_phase,QubitId(542));
  let mut f=Fixed;let mut back=Simulator::new(565,0,&mut f);back.qubits.copy_from_slice(&produced);back.apply_iter(self.r00_inverse.iter());back.apply_iter(ops[self.before_loan..self.after_loan].iter().rev());assert_eq!(back.qubits,before_loan,"inverse R00 failed to return external passenger");assert_eq!(back.phase,0);
  sim.apply_iter(ops[self.after_r00..self.before_sign].iter());
  super::q794_mbu_native::check(&sim.qubits,&ops[self.before_sign..self.after_sign],&self.sign_phase,QubitId(542));
 }
}
