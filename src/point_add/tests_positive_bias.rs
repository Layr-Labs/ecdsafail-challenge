use super::*;
use crate::circuit::{analyze_ops,QubitOrBit};
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Tape {seed:u64,at:u64}
impl XofReader for Tape {
 fn read(&mut self,out:&mut[u8]) {
  assert_eq!(out.len(),8);let at=self.at;self.at+=1;
  let mut z=self.seed.wrapping_add(at.wrapping_mul(0x9e3779b97f4a7c15));
  z=(z^(z>>30)).wrapping_mul(0xbf58476d1ce4e5b9);z=(z^(z>>27)).wrapping_mul(0x94d049bb133111eb);z^=z>>31;
  if self.seed==0{z=0;}if self.seed==1{z=u64::MAX;}out.copy_from_slice(&z.to_le_bytes());
 }
}
fn prepare(){
 super::super::clear_process_env();super::super::install_skywalk_submission_recipe();
 std::env::set_var("EXACT_PAIR_CARRY","1");super::super::leapfrog::install_recipe();
 assert!(row0_copy());assert_eq!(super::super::optional_env::<usize>("SQ_LEND_RETAINED_CROSS2").unwrap_or(0),0);
}
fn reg(ids:&[QubitId])->Vec<QubitOrBit>{ids.iter().map(|&q|QubitOrBit::Qubit(q)).collect()}
fn circuit(m:usize,node:bool,cap:Option<usize>)->(Vec<crate::circuit::Op>,usize,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>){
 let mut c=Builder::new();let x=c.alloc_qubits(m);let product=c.alloc_qubits(2*m);let output=c.alloc_qubits(2*m);let _sentinel=c.alloc_bits(2);
 let mut cut=0;
 super::super::pingpong::with_phase_cap(cap,||{
  if node {
   let retained=tri_square_k2r(&mut c,&x,&product);cut=c.op_count();
   for (&a,&b)in product.iter().zip(&output){c.cx(a,b);}
   tri_square_k2r_inv(&mut c,&x,&product,retained);
  }else{
   tri_square(&mut c,&x,&product,false);cut=c.op_count();
   for (&a,&b)in product.iter().zip(&output){c.cx(a,b);}
   tri_square(&mut c,&x,&product,true);
  }
 });
 c.declare_qubit_register(&x);c.declare_qubit_register(&product);c.declare_qubit_register(&output);
 (c.take_ops(),cut,x,product,output)
}
fn exhaustive(node:bool,range:std::ops::RangeInclusive<usize>){
 prepare();let mut cases=0;
 for m in range {for limited in [false,true]{
  let cap=limited.then_some(5*m+4);let(ops,cut,x,product,output)=circuit(m,node,cap);
  let(nq,nb,_,_)=analyze_ops(ops.iter());let rx=reg(&x);let rp=reg(&product);let ro=reg(&output);
  let mask=(1u64<<(2*m))-1;
  for pattern in 0..32u64 {for start in (0..1usize<<m).step_by(64){
   let count=64.min((1<<m)-start);let mut tape=Tape{seed:pattern,at:0};let mut sim=Simulator::new(nq as usize,nb as usize,&mut tape);
   let mut expected=vec![0u64;nq as usize];let mut sentinel=[0u64;2];
   for lane in 0..count{
    let value=(start+lane)as u64;let dirty=value.wrapping_mul(0x9e37).wrapping_add(pattern)&mask;
    sim.set_register(&rx,U256::from(value),lane);sim.set_register(&ro,U256::from(dirty),lane);
    let out=dirty^(value*value+2);
    for(i,&q)in x.iter().enumerate(){expected[q.0 as usize]|=((value>>i)&1)<<lane;}
    for(i,&q)in output.iter().enumerate(){expected[q.0 as usize]|=((out>>i)&1)<<lane;}
    sentinel[0]|=(value&1)<<lane;sentinel[1]|=((value>>1)&1)<<lane;
   }
   sim.bits[0]=sentinel[0];sim.bits[1]=sentinel[1];
   sim.apply_iter(ops[..cut].iter());
   for lane in 0..count{let v=(start+lane)as u64;assert_eq!(sim.get_register(&rp,lane),U256::from(v*v+2),"forward m={m} node={node} cap={cap:?} pattern={pattern} input={v}");}
   sim.apply_iter(ops[cut..].iter());
   let active=if count==64{u64::MAX}else{(1u64<<count)-1};
   for(q,(&got,&want))in sim.qubits.iter().zip(&expected).enumerate(){assert_eq!(got&active,want,"all-q m={m} node={node} cap={cap:?} pattern={pattern} start={start} q={q}");}
   assert_eq!(sim.phase&active,0,"phase m={m} node={node} cap={cap:?} pattern={pattern} start={start}");
   assert_eq!(sim.bits[0]&active,sentinel[0]);assert_eq!(sim.bits[1]&active,sentinel[1]);cases+=count;
  }}
  eprintln!("POSITIVE_BIAS_COMPONENT m={m} node={node} cap={cap:?} ops={} touched_q={nq} measurement_patterns=32 all_basis_inputs={} scored=false",ops.len(),1usize<<m);
 }}
 eprintln!("POSITIVE_BIAS_SUITE node={node} native_cases={cases} phase_scope=32_fixed_measurement_patterns classical_inputs_preserved=2 score=NONE");
}
#[test]fn uniform_positive_leaf_exhaustive(){exhaustive(false,3..=8);}
#[test]fn uniform_positive_node_exhaustive(){exhaustive(true,6..=10);}
#[test]fn uniform_positive_bias_fault_detection(){
 prepare();let(ops,cut,x,product,_)=circuit(6,true,None);let(nq,nb,_,_)=analyze_ops(ops.iter());
 let mut tape=Tape{seed:0,at:0};let mut sim=Simulator::new(nq as usize,nb as usize,&mut tape);
 sim.set_register(&reg(&x),U256::ZERO,0);sim.apply_iter(ops[..cut].iter());assert_eq!(sim.get_register(&reg(&product),0),U256::from(2));
 // A deliberate failure to preserve the declared +2 output bias is observable at input0.
 let mut faulty=ops[..cut].to_vec();let mut flip=crate::circuit::Op::empty();flip.kind=crate::circuit::OperationType::X;flip.q_target=product[1];faulty.push(flip);
 let mut tape=Tape{seed:0,at:0};let mut sim=Simulator::new(nq as usize,nb as usize,&mut tape);sim.apply_iter(faulty.iter());assert_ne!(sim.get_register(&reg(&product),0),U256::from(2));
}

#[path="tests_positive_large.rs"]
mod production_sized;
