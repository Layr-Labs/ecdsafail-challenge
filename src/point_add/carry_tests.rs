use super::*;use crate::sim::Simulator;use sha3::digest::XofReader;
struct Outcomes([u8;2],usize);impl XofReader for Outcomes{fn read(&mut self,b:&mut[u8]){b.fill(self.0[self.1.min(1)]);self.1+=1;}}
fn gate(k:OperationType,a:usize,b:usize,t:usize)->Op{let mut o=Op::empty();o.kind=k;o.q_target=QubitId(t as u64);if matches!(k,OperationType::CX|OperationType::CCX){o.q_control1=QubitId(a as u64);}if k==OperationType::CCX{o.q_control2=QubitId(b as u64);}o}
#[test]fn full_predicate_source_capture_phase_conditions_and_original_trace(){
 let data=include_bytes!("predicate_comparator_test.hir");let mut cases=0;
 for context in 0..4{for dirty in [false,true]{
  let build=|enabled,retain|{let mut inputs:Vec<_>=(0..513).chain([514]).collect();if dirty{inputs.push(513);}let mut s=State::new(518,256,&inputs,&[0],retain,0);s.carry_enabled=enabled;
   if context==1||context==2{s.raw(if context==1{OperationType::BitStore1}else{OperationType::BitStore0}).c_target=BitId(0);}if context!=0{s.raw(OperationType::PushCondition).c_condition=BitId(0);}
   let mut r=Reader{data,at:0};assert_eq!(predicate_cleanup(&mut r,&mut s,2267,0,0),2053);if context!=0{s.raw(OperationType::PopCondition);}s.flush_raw();s.assert_accounting(2053+usize::from(context==1||context==2)+2*usize::from(context!=0),0);s};
  let old=build(false,true);let new=build(true,true);let count=build(true,false);assert_eq!(new.carry_selected,usize::from(!dirty));assert_eq!(old.trace,new.trace);assert_eq!(old.proof.diagnostic_fingerprint(),new.proof.diagnostic_fingerprint());assert_eq!(new.output_hist,count.output_hist);assert_eq!(new.output_ops,count.output_ops);
  for sample in 0..64u64{for m in [0,255]{for local in [0,255]{for active in 0..2u64{
   let mut ra=Outcomes([m,local],0);let mut rb=Outcomes([m,local],0);let mut a=Simulator::new(518,258,&mut ra);let mut b=Simulator::new(518,258,&mut rb);for q in 0..513{a.qubits[q]=sample.rotate_left((q%64)as u32)&1;}a.qubits[513]=u64::from(dirty);a.qubits[514]=(sample>>3)&1;a.bits[0]=active;a.bits[256]=sample&1;b.qubits=a.qubits.clone();b.bits=a.bits.clone();a.apply_iter(old.out.iter());b.apply_iter(new.out.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);for c in 0..258{if c!=256{assert_eq!(a.bits[c],b.bits[c]);}}cases+=1;
  }}}}
 }}assert_eq!(cases,4096);
}
fn small(n:usize,rewrite:bool)->Vec<Op>{use OperationType::*;let carry=2*n+1;let mut v=Vec::new();for i in 0..n{v.push(gate(X,0,0,n+1+i));}v.push(gate(X,0,0,carry));for i in 0..n{let(a,b,c)=(i+1,n+1+i,if i==0{carry}else{i});v.extend([gate(CX,a,0,b),gate(CX,a,0,c),gate(CCX,c,b,a)]);}for i in (0..n).rev(){let(a,b,c)=(i+1,n+1+i,if i==0{carry}else{i});let o=gate(CCX,c,b,a);if i==0&&rewrite{ // Match source q_control2=carry, q_control1=b.
 let mut o=o;o.q_control2=QubitId(c as u64);o.q_control1=QubitId(b as u64);v.extend(carry_replacement(&o,BitId(0)));}else{v.push(o);}v.extend([gate(CX,a,0,c),gate(CX,a,0,b)]);}v.push(gate(X,0,0,carry));for i in 0..n{v.push(gate(X,0,0,n+1+i));}v}
#[test]fn exhaustive_small_clean_carry_and_dirty_falsifier(){let mut cases=0;for n in 1..=5{let old=small(n,false);let new=small(n,true);for bits in 0..1usize<<(2*n){for m in [0,255]{let mut ra=Outcomes([m,m],0);let mut rb=Outcomes([m,m],0);let mut a=Simulator::new(2*n+2,1,&mut ra);let mut b=Simulator::new(2*n+2,1,&mut rb);for q in 1..=2*n{a.qubits[q]=((bits>>(q-1))&1)as u64;}b.qubits=a.qubits.clone();a.apply_iter(old.iter());b.apply_iter(new.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);cases+=1;}}}assert_eq!(cases,2728);
let mut ra=Outcomes([0,0],0);let mut rb=Outcomes([0,0],0);let mut a=Simulator::new(4,1,&mut ra);let mut b=Simulator::new(4,1,&mut rb);a.qubits[3]=1;b.qubits=a.qubits.clone();a.apply_iter(small(1,false).iter());b.apply_iter(small(1,true).iter());assert_ne!(a.qubits,b.qubits,"dirty carry must falsify forced replacement");}
#[test]fn pending_entry_fact_and_existing_capture_are_respected(){
 let data=include_bytes!("predicate_comparator_test.hir");for toggles in 0..=2{for capture in [false,true]{let inputs:Vec<_>=(0..513).chain([514]).collect();let mut s=State::new(518,256,&inputs,&[],true,0);s.carry_enabled=true;
 for _ in 0..toggles{s.raw(OperationType::X).q_target=QubitId(513);}if capture{s.flush_raw();s.capture=Some(Vec::new());}
 let mut r=Reader{data,at:0};predicate_cleanup(&mut r,&mut s,2267,0,0);s.flush_raw();assert_eq!(s.carry_zero,usize::from(toggles%2==0));assert_eq!(s.carry_selected,usize::from(toggles%2==0&&!capture));if capture{let v=s.capture.take().unwrap();assert!(!v.is_empty());}
 }}
}
#[test]fn local_outcome_dies_at_next_private_cleanup(){
 struct Triple([u8;3],usize);impl XofReader for Triple{fn read(&mut self,b:&mut[u8]){b.fill(self.0[self.1.min(2)]);self.1+=1;}}
 let data=include_bytes!("predicate_comparator_test.hir");let build=|enabled|{let inputs:Vec<_>=(0..513).chain([514]).collect();let mut s=State::new(518,256,&inputs,&[],true,0);s.carry_enabled=true;s.carry_enabled=enabled;let mut r=Reader{data,at:0};predicate_cleanup(&mut r,&mut s,2267,0,0);for _ in 0..2{*s.raw(OperationType::CCX)=gate(OperationType::CCX,1,2,515);}s.flush_raw();assert_eq!(s.proof.rewrites,1);s};let old=build(false);let new=build(true);assert_eq!(old.trace,new.trace);assert_eq!(old.proof.diagnostic_fingerprint(),new.proof.diagnostic_fingerprint());
 for sample in 0..16u64{for pred in [0,255]{for local in [0,255]{for next in [0,255]{for stale in 0..2u64{let mut ra=Triple([pred,next,next],0);let mut rb=Triple([pred,local,next],0);let mut a=Simulator::new(518,258,&mut ra);let mut b=Simulator::new(518,258,&mut rb);for q in 0..513{a.qubits[q]=sample.rotate_left((q%64)as u32)&1;}a.qubits[514]=(sample>>2)&1;a.bits[256]=stale;b.qubits=a.qubits.clone();b.bits=a.bits.clone();a.apply_iter(old.out.iter());b.apply_iter(new.out.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);assert_eq!(a.bits,b.bits);}}}}}
}
