fn fixture()->Vec<u8>{let gates:&[(u8,&[u8])]=&[(5,&[0,1,2]),(3,&[2,3]),(3,&[4,2]),(5,&[2,3,4]),(3,&[4,5]),(3,&[6,4]),(5,&[4,5,6]),(3,&[6,7]),(3,&[8,7]),(5,&[4,5,6])];let mut b=vec![];for(t,q)in gates{b.extend([*t,0,1,q.len()as u8]);b.extend(*q);b.push(0);}b}
#[test]fn family63_tiny(){use super::{OperationType as K,BitId};use crate::sim::Simulator;use sha3::digest::XofReader;
struct R(u64,usize);impl XofReader for R{fn read(&mut self,b:&mut[u8]){assert!(self.1<12);b.fill(if self.0>>self.1&1==1{255}else{0});self.1+=1;}}
let data=fixture();let mut rr=Reader{data:&data,at:0};let v:Vec<_>=(0..10).map(|_|read(&mut rr)).collect();let(mut selected,mut fallback,mut cases,mut sawzero,mut sawone,mut sawresidual)=(0,0,0,false,false,false);
for known in [0,1,2,4,8,16,32,64,128,256,85,170,341,511,512,513] {for cond in 0..4 {
 let inputs:Vec<_>=(1..=9).filter(|j|if known<512{known>>(j-1)&1==0}else{*j!=7}).collect();
 let build=|enabled,retain,outer|{let mut s=State::new(11,1,&inputs,&[0],retain,0);s.endpoint_enabled=true;s.carry_enabled=true;s.family63_locations=vec![vec![0]];s.qmap=(1..=9).map(QubitId).collect();
 if known==512{s.raw(K::X).q_target=QubitId(7);}if known==513{let o=s.raw(K::CX);o.q_control1=QubitId(9);o.q_target=QubitId(7);}
 if cond>0{if cond<3{s.raw(if cond==1{K::BitStore1}else{K::BitStore0}).c_target=BitId(0);}s.raw(K::PushCondition).c_condition=BitId(0);}
 s.flush_raw();if outer{s.comparator_capture=Some(vec![]);}
 if enabled{let mut r=Reader{data:&data,at:0};assert_eq!(try_apply(&mut s,&mut r,0,0,10,0,9,usize::MAX),Some(10));assert_eq!(r.at,data.len());}else{for o in &v{let mut q=[NO_QUBIT;3];for j in 0..o.nq{q[j]=s.qmap[o.q[j]];}s.emit_leaf(o.t,&q,o.nq,NO_BIT,0);}s.flush_raw();}
 if outer{let cap=s.comparator_capture.take().unwrap();assert!(!cap.is_empty()||cond==2);for o in cap{s.deliver(o);}}
 if cond>0{s.raw(K::PopCondition);}
 // Unchanged suffix kills the private result before its next read.
 for _ in 0..2{let o=s.raw(K::CCX);o.q_control1=QubitId(1);o.q_control2=QubitId(2);o.q_target=QubitId(10);}s.flush_raw();s.assert_accounting(s.input_ops,0);assert!(s.proof.balanced());s};
 let old=build(false,true,false);let new=build(true,true,false);let counted=build(true,false,false);let outer=build(true,true,true);
 assert_eq!(old.trace,new.trace);assert_eq!(old.input_hist,new.input_hist);assert_eq!(old.proof.diagnostic_fingerprint(),new.proof.diagnostic_fingerprint());assert_eq!(new.output_hist,counted.output_hist);assert_eq!(new.output_hist,outer.output_hist);assert_eq!(new.final_private_hmr,counted.final_private_hmr);assert_eq!(new.final_private_hmr,outer.final_private_hmr);assert_eq!(new.final_private_neg,counted.final_private_neg);assert_eq!(new.selected_delta,counted.selected_delta);assert_eq!(new.family63_counts,counted.family63_counts);assert_eq!(new.residual_counts,old.residual_counts);assert_eq!(new.skipped_residual,old.skipped_residual);assert_eq!(new.one_cleanups,old.one_cleanups);assert_eq!(new.proof.rewrites,old.proof.rewrites);assert!(counted.out.is_empty());
 if new.family63_counts[1]>0{selected+=1;assert_eq!(new.selected_delta,-1);assert_eq!(new.skipped_cleanups,0);assert_eq!(new.skipped_one,0);assert_eq!(new.skipped_support,[0;3]);}else{fallback+=1;assert_eq!(new.output_hist,old.output_hist);}
 sawzero|=old.proof.rewrites>0;sawone|=old.one_cleanups>0;sawresidual|=old.residual_counts.iter().sum::<usize>()>0;
 let nh=old.out.iter().filter(|o|matches!(o.kind,K::Hmr|K::R)).count();assert!(nh<12);
 for x in 0..512u64 {if(1..=9).any(|j|!inputs.contains(&j)&&x>>(j-1)&1!=0){continue;}for active in 0..2{for outcome in 0..(1<<nh){for stale in 0..2{
 let mut ra=R(outcome,0);let mut rb=R(outcome,0);let mut a=Simulator::new(11,3,&mut ra);let mut b=Simulator::new(11,3,&mut rb);for j in 0..9{a.qubits[j+1]=x>>j&1;}a.bits[0]=active;a.bits[1]=stale;b.qubits=a.qubits.clone();b.bits=a.bits.clone();a.apply_iter(old.out.iter());b.apply_iter(new.out.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);assert_eq!(a.bits,b.bits);cases+=1;
 }}}}
}}
println!("coverage selected={selected} fallback={fallback} zero={sawzero} one={sawone} residual={sawresidual}");assert!(selected>0&&fallback>0&&sawzero&&sawone);println!("PASS family63 cases={cases} selected={selected} fallback={fallback} 14knownpatterns+one/copy contexts fourconditions outercapture retain/count phase/classical/Proof/accounting");
}
#[test]fn family63_rejections(){let data=fixture();let make=||{let mut s=State::new(11,1,&[1,2,3,4,5,6,7,8,9],&[],true,0);s.endpoint_enabled=true;s.carry_enabled=true;s.family63_locations=vec![vec![0]];s.qmap=(1..=9).map(QubitId).collect();s};
for i in 0..9{for j in i+1..9{let mut s=make();s.qmap[j]=s.qmap[i];let mut r=Reader{data:&data,at:0};assert_eq!(try_apply(&mut s,&mut r,0,0,10,0,9,usize::MAX),None);assert_eq!(s.input_ops,0);assert_eq!(r.at,0);}}
for i in 0..9{let mut s=make();s.qmap[i]=QubitId(0);let mut r=Reader{data:&data,at:0};assert_eq!(try_apply(&mut s,&mut r,0,0,10,0,9,usize::MAX),None);assert_eq!(s.input_ops,0);}
for kind in 0..4{let mut s=make();let mut bad=data.clone();if kind==0{s.family63_locations[0].clear();}if kind==1{bad[1]=1;bad.insert(3,0);}let mut r=Reader{data:&bad,at:0};assert_eq!(try_apply(&mut s,&mut r,0,0,if kind==2{9}else{10},0,9,if kind==3{0}else{usize::MAX}),None);assert_eq!(s.input_ops,0);assert_eq!(r.at,0);}}

#[test]fn family63_native_full_inverse(){use super::{Op,OperationType as K};use crate::sim::Simulator;use sha3::digest::XofReader;struct R;impl XofReader for R{fn read(&mut self,_:&mut[u8]){panic!("native circuit has no measurements")}}
let data=fixture();let mut r=Reader{data:&data,at:0};let v:Vec<_>=(0..10).map(|_|read(&mut r)).collect();let mut old=vec![];for o in &v{let mut op=Op::empty();op.kind=if o.t==3{K::CX}else{K::CCX};if o.t==3{op.q_control1=QubitId(o.q[0]as u64+1);op.q_target=QubitId(o.q[1]as u64+1);}else{op.q_control2=QubitId(o.q[0]as u64+1);op.q_control1=QubitId(o.q[1]as u64+1);op.q_target=QubitId(o.q[2]as u64+1);}old.push(op);}
let mut new=old[..6].to_vec();new.push(old[7]);new.push(old[8]);let mut p=old[6];p.q_target=QubitId(8);new.push(p);
for x in 0..512{let mut rng=R;let mut sim=Simulator::new(10,1,&mut rng);for j in 0..9{sim.qubits[j+1]=(x>>j)&1;}let before=sim.qubits.clone();sim.apply_iter(new.iter());sim.apply_iter(old.iter().rev());assert_eq!(sim.qubits,before);assert_eq!(sim.phase,0);}}
