use super::*;

pub(super)struct Tracker{pub root:usize,pub eligible:usize,pub selected:usize,pub saving:usize,pub delta:isize,pub skipped_private_hmr:usize,pub skipped_private_neg:usize,sites:Vec<(usize,usize)>,allowed:Vec<(usize,usize)>,native:Vec<Op>,active:Option<(usize,Vec<Op>)>}
fn read_native()->Vec<Op>{read_ops("new")}
fn read_ops(name:&str)->Vec<Op>{(if name=="new"{include_str!("comparator_fixtures/new.ops")}else{assert_eq!(name,"old");include_str!("comparator_fixtures/old.ops")}).lines().map(|l|{let v:Vec<i64>=l.split_whitespace().map(|x|x.parse().unwrap()).collect();assert_eq!(v.len(),6);let mut o=Op::empty();o.kind=match v[0]{6=>OperationType::X,7=>OperationType::Z,8=>OperationType::CX,9=>OperationType::CZ,10=>OperationType::Swap,12=>OperationType::Hmr,13=>OperationType::CCX,_=>panic!()};o.q_control2=QubitId(v[1]as u64);o.q_control1=QubitId(v[2]as u64);o.q_target=QubitId(v[3]as u64);o.c_target=BitId(v[4]as u64);o.c_condition=BitId(v[5]as u64);o.validate();o}).collect()}
impl Tracker{pub fn new()->Self{let sites=include_str!("comparator_fixtures/match-offsets.txt").lines().map(|l|{let v:Vec<_>=l.split_whitespace().collect();(v[0].parse().unwrap(),if v[1]=="add"{0}else{1})}).collect();let allowed=include_str!("comparator_eligible.txt").lines().map(|l|{let v:Vec<_>=l.split_whitespace().collect();(v[0].parse().unwrap(),v[1].parse().unwrap())}).collect();Self{root:0,eligible:0,selected:0,saving:0,delta:0,skipped_private_hmr:0,skipped_private_neg:0,sites,allowed,native:read_native(),active:None}}}
fn cost(v:&[Op])->usize{v.iter().filter(|o|matches!(o.kind,OperationType::CCX|OperationType::CCZ)).count()}
fn finish(s:&mut State,new:Vec<Op>){assert!(s.capture.is_none());let old=s.comparator_capture.take().unwrap();let a=cost(&old);let b=cost(&new);if b<a{
 let mut written=std::collections::BTreeSet::new();let mut depth=0usize;for o in &old{
 if o.c_condition!=NO_BIT{assert!(written.contains(&o.c_condition.0),"capture reads stale classical work");}
 if o.kind==OperationType::PushCondition{depth+=1;}else if o.kind==OperationType::PopCondition{assert!(depth>0);depth-=1;}
 if o.c_target!=NO_BIT{assert!((1024..1280).contains(&o.c_target.0)||o.c_target==s.measurement_bit||cfg!(test)&&o.c_target.0<256);assert!(matches!(o.kind,OperationType::Hmr|OperationType::BitStore0|OperationType::BitStore1));assert_eq!(depth,0);assert_eq!(o.c_condition,NO_BIT);written.insert(o.c_target.0);}
 }assert_eq!(depth,0);
 s.comparator.skipped_private_hmr+=old.iter().filter(|o|o.kind==OperationType::Hmr&&o.c_target==s.measurement_bit).count();s.comparator.skipped_private_neg+=old.iter().filter(|o|o.kind==OperationType::Neg).count();s.comparator.selected+=1;s.comparator.saving+=a-b;s.comparator.delta+=new.len()as isize-old.len()as isize;s.output_ops-=old.len();for o in old{s.output_hist[o.kind as usize]-=1;}for o in new{s.write(o);}}else{for o in old{s.deliver(o);}}}
pub(super)fn boundary(s:&mut State,r:&Reader<'_>,record:usize,qstart:usize,cstart:usize){
 if let Some((end,_))=&s.comparator.active{assert!(r.at<=*end);if r.at==*end{assert!(s.proof.balanced());let (_,new)=s.comparator.active.take().unwrap();finish(s,new);}}
 let Some((_,family))=s.comparator.sites.iter().find(|(at,_)|*at==r.at).copied()else{return;};
 let fixture:&[u8]=if family==0{include_bytes!("comparator_fixtures/source-old-comparator.hir")}else{include_bytes!("comparator_fixtures/source-old-double-comparator.hir")};assert_eq!(&r.data[r.at..r.at+fixture.len()],fixture);
 if !s.comparator.allowed.contains(&(s.comparator.root,record)){return;}
 assert!((0..256).all(|j|s.cmap[cstart+j]==BitId(1024+j as u64)));
 let clean=if family==0{[768,770,771,772]}else{[769,770,771,772]};assert!(clean.iter().all(|&q|s.proof.qubit_is_zero(s.qmap[qstart+q].0 as usize)));assert!(s.proof.balanced());assert!(matches!(s.pending_hmr,PendingHmr::None));
 let mut map=vec![NO_QUBIT;518];for j in 0..256{map[j+1]=s.qmap[qstart+512+j];map[j+257]=s.qmap[qstart+256+j];}for j in 0..4{map[513+j]=s.qmap[qstart+clean[j]];}map[517]=s.qmap[qstart+if family==0{769}else{768}];let mut ids:Vec<_>=map[1..].iter().map(|q|q.0).collect();ids.sort();ids.dedup();assert_eq!(ids.len(),517);assert!(!ids.contains(&0));
 let new=s.comparator.native.iter().map(|o|{let mut o=*o;for q in [&mut o.q_control2,&mut o.q_control1,&mut o.q_target]{if *q!=NO_QUBIT{*q=map[q.0 as usize];}}for c in [&mut o.c_target,&mut o.c_condition]{if *c!=NO_BIT{assert!(c.0<34);*c=s.cmap[cstart+c.0 as usize];}}o.validate();o}).collect();assert!(s.comparator_capture.is_none());assert!(s.capture.is_none());s.comparator_capture=Some(Vec::new());s.comparator.active=Some((r.at+fixture.len(),new));s.comparator.eligible+=1;
}
#[cfg(test)]mod tests{use super::*;fn op(k:OperationType)->Op{let mut o=Op::empty();o.kind=k;o.q_target=QubitId(3);if k==OperationType::CCX{o.q_control1=QubitId(1);o.q_control2=QubitId(2);}o}
#[test]fn nested_delivery_and_accounting(){for retain in [false,true]{for gain in [false,true]{let mut s=State::new(6,2,&[1,2,3],&[],retain,0);s.comparator_capture=Some(vec![]);s.capture=Some(vec![]);s.write(op(OperationType::CCX));s.write(op(OperationType::CCX));let inner=s.capture.take().unwrap();for o in inner{s.deliver(o);}assert_eq!(s.comparator_capture.as_ref().unwrap().len(),2);let replacement=vec![op(OperationType::CCX);if gain{1}else{2}];finish(&mut s,replacement);assert_eq!(s.output_ops,if gain{1}else{2});assert_eq!(s.comparator.selected,usize::from(gain));assert_eq!(s.output_ops as isize,2+s.comparator.delta);assert_eq!(s.out.len(),if retain{s.output_ops}else{0});}}}
}

#[cfg(test)]mod native_tests{
use super::*;use crate::sim::Simulator;use sha3::digest::XofReader;
struct R(u8);impl XofReader for R{fn read(&mut self,b:&mut[u8]){b.fill(self.0);}}
fn hexbit(h:&str,j:usize)->u64{h.as_bytes().get(h.len().wrapping_sub(1+j/4)).map(|b|((*b as char).to_digit(16).unwrap()as u64>>(j%4))&1).unwrap_or(0)}
#[test]fn complete_native_capture_phase_and_count_parity(){
 let old=read_ops("old");let new=read_native();assert_eq!(cost(&new),640);
 let build=|retain,select|{let inputs:Vec<_>=(1..=512).chain([517]).collect();let mut s=State::new(518,256,&inputs,&[],retain,0);if select{s.comparator_capture=Some(vec![]);}for o in &old{*s.raw(o.kind)=*o;}s.flush_raw();if select{finish(&mut s,new.clone());}s.assert_accounting(old.len(),0);s};
 let baseline=build(true,false);let selected=build(true,true);let counted=build(false,true);for s in [&baseline,&selected]{assert_eq!(s.final_private_hmr,s.out.iter().filter(|o|o.kind==OperationType::Hmr&&o.c_target==s.measurement_bit).count());assert_eq!(s.final_private_neg,s.out.iter().filter(|o|o.kind==OperationType::Neg&&o.c_condition==s.measurement_bit).count());}assert_eq!(selected.final_private_hmr,counted.final_private_hmr);assert_eq!(selected.comparator.selected,1);assert_eq!(selected.input_hist,baseline.input_hist);assert_eq!(selected.trace,baseline.trace);assert_eq!(selected.proof.diagnostic_fingerprint(),baseline.proof.diagnostic_fingerprint());assert_eq!(selected.output_hist,counted.output_hist);assert_eq!(selected.output_ops,counted.output_ops);
 let mut cases=0;for line in include_str!("comparator_fixtures/cases256.txt").lines(){let v:Vec<_>=line.split_whitespace().collect();for m in [0,255]{let mut ra=R(m);let mut rb=R(m);let mut a=Simulator::new(518,258,&mut ra);let mut b=Simulator::new(518,258,&mut rb);for j in 0..256{a.qubits[j+1]=hexbit(v[0],j);a.qubits[j+257]=hexbit(v[1],j);}a.qubits[517]=v[2].parse().unwrap();a.bits.fill(1);b.qubits=a.qubits.clone();b.bits=a.bits.clone();a.apply_iter(baseline.out.iter());b.apply_iter(selected.out.iter());assert_eq!(a.qubits,b.qubits);assert_eq!(a.phase,b.phase);assert_eq!(b.phase,0);cases+=1;}}
 assert!(cases>100);eprintln!("COMPARATOR_NATIVE_CAPTURE cases={cases} old_t={} new_t={} saving={}",cost(&baseline.out),cost(&selected.out),selected.comparator.saving);
}
}

#[cfg(test)]mod boundary_tests{use super::*;
fn setup()->(State,Vec<u8>,usize){let mut s=State::new(834,1280,&[],&[],true,0);s.comparator.root=1028;for j in 0..256{s.cmap[j]=BitId(1024+j as u64);}let (at,_)=s.comparator.sites.iter().find(|(_,f)|*f==1).copied().unwrap();let fixture=include_bytes!("comparator_fixtures/source-old-double-comparator.hir");let mut bytes=vec![0;at];bytes.extend(fixture);(s,bytes,at)}
#[test]fn exact_mapping_and_rejections(){
 let(mut s,b,at)=setup();boundary(&mut s,&Reader{data:&b,at},12153,0,0);assert_eq!(s.comparator.eligible,1);let (_,v)=s.comparator.active.take().unwrap();assert_eq!(cost(&v),640);assert!(v.iter().all(|o|o.c_target==NO_BIT||(1024..=1057).contains(&o.c_target.0)));assert!(v.iter().all(|o|o.q_target!=QubitId(0)));
 let(mut s,b,at)=setup();s.comparator.root=2830;boundary(&mut s,&Reader{data:&b,at},12153,0,0);assert!(s.comparator_capture.is_none());
 for mode in 0..4{let(mut s,mut b,at)=setup();match mode{0=>b[at]^=1,1=>s.cmap[0]=BitId(7),2=>s.qmap[772]=s.qmap[770],_=>{let mut o=Op::empty();o.kind=OperationType::X;o.q_target=s.qmap[772];s.proof.step(&o);}}assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(||boundary(&mut s,&Reader{data:&b,at},12153,0,0))).is_err());}
}
}

pub(super)fn validate_helper(g:&Graph<'_>){let n=g.nodes[2257];assert_eq!(&g.data[n.start..n.end],&[1,1,1,2,0,1,1,0,0],"comparator phase helper changed");}
#[cfg(test)]#[test]fn phase_helper_exact_bytes_reject_mutations(){
 let check=|data:&[u8]|{let g=Graph{data,nodes:vec![Node{start:0,end:data.len()};2258],root:2257,root_qubits:1,root_bits:1,summaries:vec![]};validate_helper(&g);};
 let good=[1,1,1,2,0,1,1,0,0];check(&good);for i in 0..good.len(){let mut bad=good;bad[i]^=1;assert!(std::panic::catch_unwind(||check(&bad)).is_err());}assert!(std::panic::catch_unwind(||check(&good[..8])).is_err());
}
