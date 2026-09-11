use super::*;use crate::sim::Simulator;use sha3::digest::XofReader;
struct Outcome(u8);impl XofReader for Outcome{fn read(&mut self,b:&mut[u8]){b.fill(self.0);}}
fn gate(k:OperationType,a:usize,b:usize,t:usize)->Op{let mut o=Op::empty();o.kind=k;o.q_target=QubitId(t as u64);if matches!(k,OperationType::CX|OperationType::CCX){o.q_control1=QubitId(a as u64);}if k==OperationType::CCX{o.q_control2=QubitId(b as u64);}o}
#[test]fn wire_actual_emitter_aliases_conditions_phase_and_count(){use OperationType::*;let mut cases=0;let mut admitted=0;
for wire in 1..=3{for parity in [false,true]{for condition in 0..7{
 let mut ops=vec![gate(CCX,1,2,4),gate(CX,wire,0,4)];if parity{ops.push(gate(X,0,0,4));}
 if [1,2,4,5].contains(&condition){let mut o=Op::empty();o.kind=if [1,4].contains(&condition){BitStore1}else{BitStore0};o.c_target=BitId(0);ops.push(o);}
 if condition>=4{let mut o=Op::empty();o.kind=PushCondition;o.c_condition=BitId(0);ops.push(o);}
 let mut cleanup=gate(CCX,1,2,4);if (1..=3).contains(&condition){cleanup.c_condition=BitId(0);}ops.push(cleanup);
 if condition>=4{let mut o=Op::empty();o.kind=PopCondition;ops.push(o);}ops.push(gate(X,0,0,5));ops.push(gate(X,0,0,5));
 let build=|enable,retain|{let mut s=State::new(6,1,&[1,2,3],&[0],retain,0);s.residual_enabled=enable;for o in &ops{*s.raw(o.kind)=*o;}s.flush_raw();s.assert_accounting(ops.len(),0);s};
 let a=build(false,true);let b=build(true,true);let count=build(true,false);let expect=usize::from(condition==0||condition==4);assert_eq!(b.residual_counts[parity as usize],expect,"wire={wire} parity={parity} condition={condition}");assert_eq!(b.residual_counts[(!parity)as usize],0);admitted+=expect;
 assert_eq!(a.trace,b.trace);assert_eq!(a.proof.diagnostic_fingerprint(),b.proof.diagnostic_fingerprint());assert_eq!(b.output_hist,count.output_hist);assert_eq!(b.output_ops,count.output_ops);assert_eq!(b.proof.residual_action,None);
 for mask in 0..8{for active in 0..2{for stale in 0..2{for m in [0,255]{let mut ra=Outcome(m);let mut rb=Outcome(m);let mut sa=Simulator::new(6,3,&mut ra);let mut sb=Simulator::new(6,3,&mut rb);for q in 1..=3{sa.qubits[q]=(mask>>(q-1))&1;}sa.bits[0]=active;sa.bits[1]=stale;sb.qubits=sa.qubits.clone();sb.bits=sa.bits.clone();sa.apply_iter(a.out.iter());sb.apply_iter(b.out.iter());assert_eq!(sa.qubits,sb.qubits);assert_eq!(sa.phase,sb.phase);assert_eq!(sa.bits[0],sb.bits[0]);cases+=1;}}}}
}}}assert_eq!(admitted,12);assert_eq!(cases,2688);}
#[test]
fn selected_motif_accounts_for_omitted_residual_once(){
 use OperationType::*;
 let data=include_bytes!("motif_fixture_6.hir");let mut r=Reader{data,at:0};let mut locals=Vec::new();let mut source=Vec::new();
 while r.at<data.len(){let tag=r.byte();assert_eq!(r.uvar(),0);assert_eq!(r.uvar(),1);let n=r.uvar();let mut q=Vec::new();for _ in 0..n{let v=r.uvar();if !locals.contains(&v){locals.push(v);}q.push(v);}assert_eq!(r.uvar(),0);source.push((tag,q));}
 assert_eq!(locals.len(),3);let prepare=[gate(X,0,0,1),gate(CCX,1,2,3),gate(X,0,0,1),gate(CX,4,0,3)];
 let build=|retain|{let mut s=State::new(6,1,&[1,2,4],&[],retain,0);s.qmap=vec![QubitId(0);580];for (i,&q) in locals.iter().enumerate(){s.qmap[q]=QubitId((i+1)as u64);}s.motif_exclusions=vec![vec![]];for o in &prepare{*s.raw(o.kind)=*o;}s.flush_raw();let mut r=Reader{data,at:0};assert_eq!(motif::try_apply(&mut s,&mut r,0,0,6,0,580,usize::MAX),Some(6));s.flush_raw();s.assert_accounting(10,0);s};
 let s=build(true);let c=build(false);assert_eq!(s.residual_counts,[1,0]);assert_eq!(s.skipped_residual,[1,0]);assert_eq!(s.selected_counts,[0,0,1]);assert_eq!(s.selected_delta,-6);assert_eq!(s.output_ops,7);assert_eq!(s.output_hist,c.output_hist);assert_eq!(s.output_ops,c.output_ops);assert_eq!(s.proof.diagnostic_fingerprint(),c.proof.diagnostic_fingerprint());
 let mut base=prepare.to_vec();for (tag,qs) in source{let q:Vec<_>=qs.iter().map(|x|locals.iter().position(|v|v==x).unwrap()+1).collect();base.push(match tag{1=>gate(X,0,0,q[0]),3=>gate(CX,q[0],0,q[1]),5=>gate(CCX,q[0],q[1],q[2]),_=>panic!()});}
 for bits in 0..8 {for m in [0,255] {for stale in 0..2u64 {let mut ra=Outcome(m);let mut rb=Outcome(m);let mut a=Simulator::new(6,3,&mut ra);let mut b=Simulator::new(6,3,&mut rb);a.qubits[1]=bits&1;a.qubits[2]=(bits>>1)&1;a.qubits[4]=(bits>>2)&1;a.bits[1]=stale;b.qubits=a.qubits.clone();b.bits=a.bits.clone();a.apply_iter(base.iter());b.apply_iter(s.out.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);assert_eq!(a.bits,b.bits);}}}
}
#[test]fn residual_motif_no_gain_fallback_keeps_emitted_cleanup(){use OperationType::*;
 let data=include_bytes!("motif_fixture_0.hir");let prepare=[gate(CX,5,0,3),gate(X,0,0,5),gate(X,0,0,5)];
 let build=|retain|{let mut s=State::new(6,1,&[1,2,4,5],&[],retain,0);s.qmap=vec![QubitId(0);580];for (local,q) in [(268,1),(278,2),(279,3),(269,4)]{s.qmap[local]=QubitId(q);}s.motif_exclusions=vec![vec![]];for o in prepare{*s.raw(o.kind)=o;}s.flush_raw();let mut r=Reader{data,at:0};assert_eq!(motif::try_apply(&mut s,&mut r,0,0,3,0,580,usize::MAX),Some(3));s.flush_raw();s.assert_accounting(6,0);s};
 let a=build(true);let b=build(false);assert_eq!(a.residual_counts,[1,0]);assert_eq!(a.skipped_residual,[0,0]);assert_eq!(a.selected_counts,[0;3]);assert_eq!(a.output_hist,b.output_hist);assert_eq!(a.output_ops,9);
 let mut old=prepare.to_vec();old.extend([gate(CCX,1,2,3),gate(CX,3,0,4),gate(CCX,1,2,3)]);
 for mask in 0..16{for m in [0,255]{for stale in 0..2{let mut ra=Outcome(m);let mut rb=Outcome(m);let mut sa=Simulator::new(6,3,&mut ra);let mut sb=Simulator::new(6,3,&mut rb);for (j,q)in [1,2,4,5].into_iter().enumerate(){sa.qubits[q]=(mask>>j)&1;}sa.bits[1]=stale;sb.qubits=sa.qubits.clone();sb.bits=sa.bits.clone();sa.apply_iter(old.iter());sb.apply_iter(a.out.iter());assert_eq!(sa.qubits,sb.qubits);assert_eq!(sa.phase,sb.phase);}}}
}
