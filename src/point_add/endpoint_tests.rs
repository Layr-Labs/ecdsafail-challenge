use super::*;
use crate::sim::Simulator;
use sha3::digest::XofReader;
struct Outcome(u8);impl XofReader for Outcome{fn read(&mut self,b:&mut[u8]){b.fill(self.0)}}
fn op(k:OperationType,a:usize,b:usize,c:usize)->Op{
 let mut o=Op::empty();o.kind=k;o.q_target=QubitId(c as u64);
 if matches!(k,OperationType::CX|OperationType::CZ|OperationType::CCX|OperationType::CCZ){o.q_control1=QubitId(b as u64);}
 if matches!(k,OperationType::CCX|OperationType::CCZ){o.q_control2=QubitId(a as u64);}o
}
#[test]fn endpoint_identity_all_basis_and_inherited_conditions(){
 use OperationType::*;
 let before=vec![op(CCX,2,3,1),op(X,0,0,1),op(CZ,0,0,1),op(X,0,0,1),op(CCX,2,3,1)];
 let after=vec![op(Z,0,0,0),op(CZ,0,0,1),op(CCZ,0,2,3)];
 for bits in 0..16 {for cond in 0..4 {
  let mut a=Outcome(0);let mut b=Outcome(0);let mut x=Simulator::new(4,2,&mut a);let mut y=Simulator::new(4,2,&mut b);
  for i in 0..4{x.qubits[i]=(bits>>i)&1;y.qubits[i]=x.qubits[i];}
  x.bits[0]=cond&1;x.bits[1]=cond>>1;y.bits=x.bits.clone();
  for seq in [&before,&after]{let sim=if std::ptr::eq(seq,&before){&mut x}else{&mut y};
   let mut stream=vec![];for bit in 0..2{let mut o=Op::empty();o.kind=PushCondition;o.c_condition=BitId(bit);stream.push(o);}
   for o in seq{o.validate();stream.push(*o);}
   let mut o=Op::empty();o.kind=PopCondition;stream.push(o);stream.push(o);sim.apply_iter(stream.iter());
  }
  assert_eq!(x.qubits,y.qubits);assert_eq!(x.bits,y.bits);assert_eq!(x.phase,y.phase);
 }}
}
fn var(out:&mut Vec<u8>,mut v:usize){loop{let b=(v&127)as u8;v>>=7;out.push(b|if v>0{128}else{0});if v==0{break}}}
pub(super)fn fixture(n:usize)->Vec<u8>{
 let mut out=vec![];let mut gate=|tag:u8,qs:&[usize]|{out.push(tag);var(&mut out,0);var(&mut out,1);var(&mut out,qs.len());for q in qs{var(&mut out,*q)}var(&mut out,0);};
 for i in 0..n{gate(1,&[1+i]);}gate(1,&[513]);
 for i in 0..n{let(a,b,c)=(257+i,1+i,if i==0{513}else{256+i});gate(3,&[a,b]);gate(3,&[a,c]);gate(5,&[c,b,a]);}
 gate(1,&[256+n]);gate(5,&[0,256+n,514]);gate(1,&[256+n]);
 for i in(0..n).rev(){let(a,b,c)=(257+i,1+i,if i==0{513}else{256+i});gate(5,&[c,b,a]);gate(3,&[a,c]);gate(3,&[a,b]);}
 gate(1,&[513]);for i in 0..n{gate(1,&[1+i]);}out
}
#[test]fn small_actual_comparator_exhaustive(){
 for n in 1..=4{
  let data=fixture(n);let mut state=State::new(518,256,&(0..513).collect::<Vec<_>>(),&[0],true,0);state.endpoint_enabled=true;
  state.raw(OperationType::PushCondition).c_condition=BitId(0);
  let mut r=Reader{data:&data,at:0};assert_eq!(predicate_cleanup_n(&mut r,&mut state,2267,0,0,n),8*n+5);assert_eq!(r.at,data.len());
  state.raw(OperationType::PopCondition);state.flush_raw();assert_eq!(state.endpoint_blocks,1);assert!(state.proof.balanced());
  for o in &state.out{o.validate();}
  for left in 0..1usize<<n{for right in 0..1usize<<n{for ctrl in 0..2u64{for inherited in 0..2u64{for m in[0,255]{
   let mut rng=Outcome(m);let mut sim=Simulator::new(518,258,&mut rng);sim.qubits[0]=ctrl;sim.bits[0]=inherited;
   for i in 0..n{sim.qubits[257+i]=((left>>i)&1)as u64;sim.qubits[1+i]=((right>>i)&1)as u64;}
   sim.qubits[514]=ctrl*u64::from(left<right);let mut expected=sim.qubits.clone();if inherited==1{expected[514]=0;}
   sim.apply_iter(state.out.iter());for(got,want)in sim.qubits.iter().zip(expected){assert_eq!(got&1,want,"n={n} left={left} right={right} ctrl={ctrl} inherited={inherited} m={m}");}
   assert_eq!(sim.phase&1,0);assert_eq!(sim.bits[0]&1,inherited);
   assert_eq!(sim.bits[257]&1,if inherited==1{u64::from(m!=0)}else{0});
  }}}}}
 }
}
#[test]fn endpoint_q0_specialization_preserves_conditional_phase(){
 use OperationType::*;
 let mut stream=vec![op(X,0,0,0)];let mut push=Op::empty();push.kind=PushCondition;push.c_condition=BitId(0);stream.push(push);
 for mut o in [op(Z,0,0,0),op(CZ,0,0,1),op(CCZ,0,2,3)]{o.c_condition=BitId(1);stream.push(o);}
 let mut pop=Op::empty();pop.kind=PopCondition;stream.push(pop);stream.push(op(X,0,0,0));
 let mut lowered=stream.clone();eliminate_constant_outer_control(&mut lowered,QubitId(0));
 assert_eq!(lowered[1].kind,Neg);assert_eq!(lowered[1].q_target,NO_QUBIT);assert_eq!(lowered[1].c_condition,BitId(1));
 for o in &lowered{o.validate();}
 for bits in 0..8 {for cond in 0..4 {
  let mut ra=Outcome(0);let mut rb=Outcome(0);let mut a=Simulator::new(4,2,&mut ra);let mut b=Simulator::new(3,2,&mut rb);
  for i in 0..3{a.qubits[i+1]=(bits>>i)&1;b.qubits[i]=a.qubits[i+1];}a.bits[0]=cond&1;a.bits[1]=cond>>1;b.bits=a.bits.clone();
  a.apply_iter(stream.iter());b.apply_iter(lowered.iter());assert_eq!(a.qubits[0],0);assert_eq!(&a.qubits[1..],&b.qubits);assert_eq!(a.bits,b.bits);assert_eq!(a.phase,b.phase);
 }}
}
#[test]fn endpoint_global_alias_uses_original_phase_path(){
 let data=fixture(2);let mut state=State::new(518,256,&(0..513).collect::<Vec<_>>(),&[],true,0);
 state.endpoint_enabled=true;state.qmap[0]=QubitId(257); // ctrl aliases final MAJ carry, but not the comparator's phase target.
 let mut r=Reader{data:&data,at:0};predicate_cleanup_n(&mut r,&mut state,2267,0,0,2);state.flush_raw();
 assert_eq!(state.endpoint_blocks,0);assert_eq!(state.endpoint_outer,0);assert_eq!(state.out.len(),24);for o in &state.out{o.validate();}
}

#[test]
fn endpoint_original_proof_and_retained_count_boundary_equivalence() {
 for n in 1..=4 {for shifted in [false,true] {
  let data=fixture(n);
  let build=|enabled,retain| {
   let mut state=State::new(518,256,&(0..513).chain([515]).collect::<Vec<_>>(),&[0],retain,0);
   state.endpoint_enabled=enabled;
   if shifted {state.qmap[0]=QubitId(515);}
   state.raw(OperationType::X).q_target=QubitId(516);
   state.raw(OperationType::PushCondition).c_condition=BitId(0);
   let mut r=Reader{data:&data,at:0};predicate_cleanup_n(&mut r,&mut state,2267,0,0,n);
   state.raw(OperationType::PopCondition);
   state.raw(OperationType::X).q_target=QubitId(516);
   state.flush_raw();assert!(state.proof.balanced());assert!(state.capture.is_none());
   state.assert_accounting(8*n+5+4,0);
   state
  };
  let old=build(false,true);let new=build(true,true);let counted=build(true,false);
  assert_eq!(old.trace,new.trace);assert_eq!(old.proof.diagnostic_fingerprint(),new.proof.diagnostic_fingerprint());
  assert_eq!(old.input_hist,new.input_hist);assert_eq!(old.input_ops,new.input_ops);
  assert_eq!(new.trace,counted.trace);assert_eq!(new.proof.diagnostic_fingerprint(),counted.proof.diagnostic_fingerprint());
  assert_eq!(new.input_hist,counted.input_hist);assert_eq!(new.output_hist,counted.output_hist);
  assert_eq!(new.selected_delta,counted.selected_delta);assert_eq!(new.outer_lowered,counted.outer_lowered);
  assert_eq!(new.endpoint_blocks,1);assert_eq!(new.endpoint_outer,usize::from(!shifted));
  assert_eq!(new.selected_delta,-2);assert_eq!(new.output_ops+2,old.output_ops);assert!(counted.out.is_empty());
  for left in 0..1usize<<n {for right in 0..1usize<<n {for ctrl in 0..2u64 {for active in 0..2u64 {for stale in 0..2u64 {for m in [0,255] {
   let mut ra=Outcome(m);let mut rb=Outcome(m);let mut a=Simulator::new(518,258,&mut ra);let mut b=Simulator::new(518,258,&mut rb);
   a.qubits[if shifted{515}else{0}]=ctrl;a.bits[0]=active;a.bits[257]=stale;
   for i in 0..n {a.qubits[257+i]=((left>>i)&1)as u64;a.qubits[1+i]=((right>>i)&1)as u64;}
   a.qubits[514]=ctrl*u64::from(left<right);b.qubits=a.qubits.clone();b.bits=a.bits.clone();
   a.apply_iter(old.out.iter());b.apply_iter(new.out.iter());
   assert_eq!(a.qubits,b.qubits);assert_eq!(a.bits,b.bits);assert_eq!(a.phase,b.phase);
  }}}}}}
 }}
}
