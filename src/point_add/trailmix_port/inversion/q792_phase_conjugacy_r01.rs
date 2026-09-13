//! Diagnostic exact phase-normalization prototype. No production integration.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::OperationType as K;
/// J_x(q,r)=(x-1-(q*2^n+r)) mod2^(n+1). Source x is restored.
/// A full-width complement followed by carry-XOR addition implements J.
fn reflection(c:&mut Circuit,x:&[QReg],r:&[QReg],q:&QReg,phase:Option<&QReg>,dirty:&QReg){
 let owned=c.b.next_qubit;let at=c.b.ops.len();for b in r.iter().chain(std::iter::once(q)){c.x(b);}super::metadata_arithmetic5::add(c,x,r,Some(q),false);
 if let Some(p)=phase{
  let ops=c.b.ops.split_off(at);let refs:Vec<_>=x.iter().chain(r).chain(std::iter::once(q)).collect();let find=|id:u64|*refs.iter().find(|r|r.id()as u64==id).unwrap();
  for op in ops{match op.kind{
   K::X=>c.cx(p,find(op.q_target.0)),
   K::CX=>c.ccx(p,find(op.q_control1.0),find(op.q_target.0)),
   K::CCX=>crate::point_add::trailmix_port::arith::mcx::mcx_dirty_ladder(c,&[p,find(op.q_control1.0),find(op.q_control2.0)],find(op.q_target.0),&[dirty]),
   _=>unreachable!(),
  }}
 }assert_eq!(owned,c.b.next_qubit);
}
pub fn run(){
 use crate::sim::Simulator;use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x26)}}
 let mut cases=0;
 for n in 2..=8{
  let mut c=Circuit::new();let x=c.alloc_qreg_bits("x",n);let r=c.alloc_qreg_bits("r",n);let q=c.alloc_qreg("decision");let p=c.alloc_qreg("phase-selector");let d=c.alloc_qreg("existing-dirty");let owned=c.b.next_qubit;
  reflection(&mut c,&x,&r,&q,Some(&p),&d);let ops=c.into_builder().ops;for o in &ops{o.validate();}
  let size=1usize<<(2*n+3);let mask=(1usize<<n)-1;
  for first in (0..size).step_by(64){let before:Vec<_>=(0..owned).map(|bit|(0..64).fold(0u64,|v,l|v|((((first+l)>>bit&1)as u64)<<l))).collect();let mut after=before.clone();
   for l in 0..64{let z=first+l;let xx=z&mask;let rr=z>>n&mask;let qq=z>>(2*n)&1;let phase=z>>(2*n+1)&1;let out=if phase==0{rr|(qq<<n)}else{xx.wrapping_sub(1).wrapping_sub(rr|(qq<<n))&((2<<n)-1)};for bit in 0..=n{let id=n+bit;after[id]=(after[id]&!(1<<l))|(((out>>bit&1)as u64)<<l);}}
   let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after,"reflection n={n} first={first}");assert_eq!(sim.phase,0);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,before,"involution");sim.apply_iter(ops.iter());sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,before,"literal inverse");assert_eq!(sim.phase,0);cases+=64;
  }
  assert_eq!(ops.iter().filter(|o|o.kind==K::CCX).count(),13*n-7);
 }
 for controlled in [false,true]{
  let n=256;let mut c=Circuit::new();let x=c.alloc_qreg_bits("x",n);let r=c.alloc_qreg_bits("r",n);let q=c.alloc_qreg("decision");let p=c.alloc_qreg("phase-selector");let d=c.alloc_qreg("existing-dirty");let owned=c.b.next_qubit;reflection(&mut c,&x,&r,&q,controlled.then_some(&p),&d);let ops=c.into_builder().ops;for o in &ops{o.validate();}
  for batch in 0..32{let mut seed=0x792fa5ecafeu64^batch;let before:Vec<_>=(0..owned).map(|_|{seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;seed}).collect();let mut after=before.clone();
   for l in 0..64{if controlled&&before[p.id()as usize]>>l&1==0{continue;}let mut carry=false;for bit in 0..=n{let id=if bit==n{q.id()as usize}else{r[bit].id()as usize};let a=bit<n&&before[x[bit].id()as usize]>>l&1!=0;let b=before[id]>>l&1==0;let sum=a^b^carry;carry=(a&&b)||(a&&carry)||(b&&carry);after[id]=(after[id]&!(1<<l))|((sum as u64)<<l);}}
   let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&before);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,after);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);cases+=64;
  }
  let t=ops.iter().filter(|o|o.kind==K::CCX).count();assert_eq!(t,if controlled{3321}else{511});eprintln!("PHASE_REFLECTION_NATIVE_WIDTH256 controlled={controlled} T={t} ops={} allocated_by_reflection=0 dirty_restored=true",ops.len());
 }
 eprintln!("PHASE_CONJUGACY_NATIVE_PASS lanes={cases} exhaustive_widths=2..8 width256_lanes=4096 phase=0 inverse=true source_and_dirty_restored=true production_changed=false whole_gain=unmeasured");
}
