use super::*;use crate::circuit::{BitId,QubitId,RegisterId};use crate::sim::Simulator;
struct Fixed(u8);impl sha3::digest::XofReader for Fixed{fn read(&mut self,out:&mut[u8]){out.fill(self.0);}}
fn ann(q:bool,id:u64,r:u64)->Op{let mut o=Op::empty();o.kind=OperationType::AppendToRegister;o.r_target=RegisterId(r);if q{o.q_target=QubitId(id)}else{o.c_target=BitId(id)}o}
fn copy(bit:u64,q:u64)->[Op;3]{let mut p=Op::empty();p.kind=OperationType::PushCondition;p.c_condition=BitId(bit);let mut x=Op::empty();x.kind=OperationType::X;x.q_target=QubitId(q);let mut pop=Op::empty();pop.kind=OperationType::PopCondition;[p,x,pop]}
fn ccx()->Op{let mut o=Op::empty();o.kind=OperationType::CCX;o.q_control1=QubitId(0);o.q_control2=QubitId(1);o.q_target=QubitId(2);o}
fn fixture()->Vec<Op>{vec![ann(true,0,0),ann(false,0,1),ann(false,1,1)]}
fn paired(ops:&[Op],out:&[Op]){for pattern in [0u8,255,0xa5,0x5a]{for input in 0..8{let mut ra=Fixed(pattern);let mut rb=Fixed(pattern);let mut a=Simulator::new(4,3,&mut ra);let mut b=Simulator::new(4,3,&mut rb);a.qubits[0]=input&1;a.bits[0]=input>>1&1;a.bits[1]=input>>2&1;b.qubits.clone_from(&a.qubits);b.bits.clone_from(&a.bits);a.apply_iter(ops.iter());b.apply_iter(out.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.bits,b.bits);assert_eq!(a.phase,b.phase);}}}
#[test]fn copied_classical_controls_preserve_all_values_and_conditions(){let mut ops=fixture();ops.extend(copy(0,1));let mut o=ccx();o.c_condition=BitId(1);ops.push(o);let out=simplify_classical(ops.clone());assert_eq!(out.iter().filter(|o|o.kind==OperationType::CCX).count(),0);paired(&ops,&out);
 // Nested condition snapshot then mutate a bit other than the witness.
 let mut ops=fixture();ops.extend(copy(0,1));let mut p=Op::empty();p.kind=OperationType::PushCondition;p.c_condition=BitId(1);let mut inv=Op::empty();inv.kind=OperationType::BitInvert;inv.c_target=BitId(1);let mut pop=Op::empty();pop.kind=OperationType::PopCondition;ops.extend([p,inv,ccx(),pop]);let out=simplify_classical(ops.clone());paired(&ops,&out);
}
#[test]fn mutable_witness_slots_and_measurement_atoms_do_not_alias(){let mut ops=fixture();ops.extend(copy(0,1));let mut inv=Op::empty();inv.kind=OperationType::BitInvert;inv.c_target=BitId(0);ops.extend([inv,ccx()]);let out=simplify_classical(ops.clone());assert_eq!(out.iter().filter(|o|o.kind==OperationType::CCX).count(),0);paired(&ops,&out);
 let mut ops=fixture();let mut h=Op::empty();h.kind=OperationType::Hmr;h.q_target=QubitId(3);h.c_target=BitId(0);ops.push(h);ops.extend(copy(0,1));ops.push(ccx());let out=simplify_classical(ops.clone());assert_eq!(out.iter().filter(|o|o.kind==OperationType::CCX).count(),0);paired(&ops,&out);
 // Negative control: stale witness after inversion changes target at a=1,b=0.
 let mut ops=fixture();ops.extend(copy(0,1));ops.extend([inv,ccx()]);let mut ra=Fixed(0);let mut rb=Fixed(0);let mut a=Simulator::new(4,3,&mut ra);let mut b=Simulator::new(4,3,&mut rb);a.qubits[0]=1;b.qubits[0]=1;a.apply_iter(ops.iter());let mut faulty=ops.clone();faulty.pop();let mut x=Op::empty();x.kind=OperationType::CX;x.q_control1=QubitId(0);x.q_target=QubitId(2);x.c_condition=BitId(0);faulty.push(x);b.apply_iter(faulty.iter());assert_ne!(a.qubits,b.qubits);
}

#[test]fn quantum_control_product_has_a_classical_factor(){
 for complement in [false,true]{for same_condition in [false,true]{
  let mut ops=fixture();ops.extend(copy(0,1));
  let mut cx=Op::empty();cx.kind=OperationType::CX;cx.q_control1=QubitId(0);cx.q_target=QubitId(1);ops.push(cx);
  if !complement{let mut x=Op::empty();x.kind=OperationType::X;x.q_target=QubitId(1);ops.push(x);}
  let mut gate=ccx();if same_condition{gate.c_condition=BitId(0);}ops.push(gate);
  let out=simplify_classical(ops.clone());assert_eq!(out.iter().filter(|o|o.kind==OperationType::CCX).count(),0);
  paired(&ops,&out);
 }}
}
