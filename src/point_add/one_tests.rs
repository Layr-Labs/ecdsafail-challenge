use super::*;
use crate::sim::Simulator;
use sha3::digest::XofReader;
struct Outcome(u8);impl XofReader for Outcome{fn read(&mut self,b:&mut[u8]){b.fill(self.0);}}
fn gate(k:OperationType,a:usize,b:usize,t:usize)->Op{
 let mut o=Op::empty();o.kind=k;o.q_target=QubitId(t as u64);
 if matches!(k,OperationType::CX|OperationType::CCX){o.q_control1=QubitId(a as u64);}
 if k==OperationType::CCX{o.q_control2=QubitId(b as u64);}o
}
fn emit(s:&mut State,ops:&[Op]){for o in ops{*s.raw(o.kind)=*o;}s.flush_raw();}
#[test]
fn one_cleanup_actual_phase_conditions_and_original_proof(){
 use OperationType::*;
 let mut selected=0;let mut cases=0;
 for condition in 0..7 {for allowed in [false,true] {
  let mut base=vec![gate(CCX,1,2,3),gate(X,0,0,3)];
  if [1,2,3,4].contains(&condition){let mut o=Op::empty();o.kind=if condition<=2{BitStore1}else{BitStore0};o.c_target=BitId(0);base.push(o);}
  let stacked=[2,4,6].contains(&condition);
  if stacked{let mut o=Op::empty();o.kind=PushCondition;o.c_condition=BitId(0);base.push(o);}
  let mut cleanup=gate(CCX,1,2,3);if [1,3,5].contains(&condition){cleanup.c_condition=BitId(0);}base.push(cleanup);
  if stacked{let mut o=Op::empty();o.kind=PopCondition;base.push(o);}
  base.push(gate(X,0,0,4));base.push(gate(X,0,0,4));
  let build=|enabled,retain|{let mut s=State::new(5,1,&[1,2],&[0],retain,0);s.one_enabled=enabled;s.one_allowed=allowed;emit(&mut s,&base);s.assert_accounting(base.len(),0);s};
  let old=build(false,true);let new=build(true,true);let counted=build(true,false);
  let expected=usize::from(allowed&&[0,2].contains(&condition));assert_eq!(new.one_cleanups,expected);selected+=expected;
  assert_eq!(new.proof.diagnostic_fingerprint(),old.proof.diagnostic_fingerprint());assert_eq!(new.trace,old.trace);
  assert_eq!(new.input_hist,counted.input_hist);assert_eq!(new.output_hist,counted.output_hist);assert_eq!(new.output_ops,counted.output_ops);assert_eq!(new.one_cleanups,counted.one_cleanups);assert!(counted.out.is_empty());
  assert_eq!(new.output_ops,old.output_ops+3*expected);
  if expected==1 {assert_eq!(new.out.iter().filter(|o|o.kind==Neg).count(),1);}
  for bits in 0..4 {for active in 0..2u64 {for stale in 0..2u64 {for m in [0,255] {
   let mut ra=Outcome(m);let mut rb=Outcome(m);let mut a=Simulator::new(5,3,&mut ra);let mut b=Simulator::new(5,3,&mut rb);
   a.qubits[1]=bits&1;a.qubits[2]=bits>>1;a.bits[0]=active;a.bits[1]=stale;b.qubits=a.qubits.clone();b.bits=a.bits.clone();
   a.apply_iter(base.iter());b.apply_iter(new.out.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);assert_eq!(a.bits[0],b.bits[0]);cases+=1;
  }}}}
 }}
 assert_eq!(selected,2);assert_eq!(cases,448);
}
#[test]
fn one_cleanup_requires_exact_support_and_respects_old_priority(){
 use OperationType::*;
 for input_target in [false,true]{for invert in [false,true]{
  let inputs=if input_target{vec![1,2,3]}else{vec![1,2]};let mut s=State::new(5,1,&inputs,&[],true,0);
  let mut ops=vec![gate(CCX,1,2,3)];if invert{ops.push(gate(X,0,0,3));}ops.push(gate(CCX,1,2,3));emit(&mut s,&ops);
  assert_eq!(s.one_cleanups,usize::from(!input_target&&invert));assert_eq!(s.proof.rewrites,u64::from(!input_target&&!invert));
 }}
 let mut s=State::new(5,1,&[],&[],true,0);emit(&mut s,&[gate(X,0,0,1),gate(X,0,0,2),gate(CCX,1,2,3)]);
 assert_eq!(s.proof.support_x,1);assert_eq!(s.one_cleanups,0);
}
#[test]
fn one_cleanup_followed_by_private_overwrite_preserves_phase(){
 use OperationType::*;
 let base=vec![gate(CCX,1,2,3),gate(X,0,0,3),gate(CCX,1,2,3),gate(CCX,1,2,4),gate(CCX,1,2,4)];
 let mut s=State::new(5,1,&[1,2],&[],true,0);emit(&mut s,&base);assert_eq!(s.one_cleanups,1);assert_eq!(s.proof.rewrites,1);
 for bits in 0..4{for m in[0,255]{let mut ra=Outcome(m);let mut rb=Outcome(m);let mut a=Simulator::new(5,3,&mut ra);let mut b=Simulator::new(5,3,&mut rb);a.qubits[1]=bits&1;a.qubits[2]=bits>>1;b.qubits=a.qubits.clone();b.bits[1]=1;a.apply_iter(base.iter());b.apply_iter(s.out.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);}}
}
#[test]
fn one_query_rejects_outer_wire_and_stale_nonccx_actions(){
 use OperationType::*;
 for (a,b,t) in [(0,2,3),(1,0,3),(1,2,0)] {
  let inputs=vec![a,b];let mut p=super::super::clean_and::Proof::new(5,1,&inputs,&[]);
  let ccx=gate(CCX,a,b,t);p.step(&ccx);p.step(&gate(X,0,0,t));p.step(&ccx);assert!(!p.ccx_result_is_one(&ccx));
 }
 let mut p=super::super::clean_and::Proof::new(5,1,&[1,2],&[]);let ccx=gate(CCX,1,2,3);p.step(&ccx);p.step(&gate(X,0,0,3));p.step(&ccx);assert!(p.ccx_result_is_one(&ccx));
 let x=gate(X,0,0,4);p.step(&x);assert!(!p.ccx_result_is_one(&x));
 let bad=gate(CCX,1,1,3);assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||p.step(&bad))).is_err());
}
#[test]
fn selected_motif_accounts_for_omitted_one_cleanup_once(){
 use OperationType::*;
 let data=include_bytes!("motif_fixture_6.hir");let mut r=Reader{data,at:0};let mut locals=Vec::new();let mut source=Vec::new();
 while r.at<data.len(){let tag=r.byte();assert_eq!(r.uvar(),0);assert_eq!(r.uvar(),1);let n=r.uvar();let mut q=Vec::new();for _ in 0..n{let v=r.uvar();if !locals.contains(&v){locals.push(v);}q.push(v);}assert_eq!(r.uvar(),0);source.push((tag,q));}
 assert_eq!(locals.len(),3);let prepare=[gate(X,0,0,1),gate(CCX,1,2,3),gate(X,0,0,1),gate(X,0,0,3)];
 let build=|retain|{let mut s=State::new(5,1,&[1,2],&[],retain,0);s.qmap=vec![QubitId(0);580];for (i,&q) in locals.iter().enumerate(){s.qmap[q]=QubitId((i+1)as u64);}s.motif_exclusions=vec![vec![]];emit(&mut s,&prepare);let mut r=Reader{data,at:0};assert_eq!(motif::try_apply(&mut s,&mut r,0,0,6,0,580,usize::MAX),Some(6));s.flush_raw();s.assert_accounting(10,0);s};
 let s=build(true);let c=build(false);assert_eq!(s.one_cleanups,1);assert_eq!(s.skipped_one,1);assert_eq!(s.selected_counts,[0,0,1]);assert_eq!(s.selected_delta,-6);assert_eq!(s.output_ops,7);assert_eq!(s.output_hist,c.output_hist);assert_eq!(s.output_ops,c.output_ops);assert_eq!(s.proof.diagnostic_fingerprint(),c.proof.diagnostic_fingerprint());
 let mut base=prepare.to_vec();for (tag,qs) in source{let q:Vec<_>=qs.iter().map(|x|locals.iter().position(|v|v==x).unwrap()+1).collect();base.push(match tag{1=>gate(X,0,0,q[0]),3=>gate(CX,q[0],0,q[1]),5=>gate(CCX,q[0],q[1],q[2]),_=>panic!()});}
 for bits in 0..4 {for m in [0,255] {for stale in 0..2u64 {let mut ra=Outcome(m);let mut rb=Outcome(m);let mut a=Simulator::new(5,3,&mut ra);let mut b=Simulator::new(5,3,&mut rb);a.qubits[1]=bits&1;a.qubits[2]=bits>>1;a.bits[1]=stale;b.qubits=a.qubits.clone();b.bits=a.bits.clone();a.apply_iter(base.iter());b.apply_iter(s.out.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);assert_eq!(a.bits,b.bits);}}}
}
