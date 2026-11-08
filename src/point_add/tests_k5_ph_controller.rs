//! Fixed local PH-frame/record gate. Full caller controller images are a
//! separate mandatory integration gate, not synthesized by this harness.
use super::*;
use super::super::{k5_ph_ports::{Context,Roles,Traversal},sum_size::SumSize};
use super::super::normalized_cross_arithmetic::{ph_controller as arithmetic,ph_reference_record};
use crate::circuit::{Op as NativeOp,OperationType as K,NO_BIT};
use crate::sim::Simulator;
use sha3::{Digest,digest::{ExtendableOutput,Update}};
const SEED:u64=0x4b355f5048313239;
const BATCHES:usize=32;
fn next(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn bit(w:&[u64],q:QubitId,k:usize)->bool{(w[q.0 as usize]>>k)&1!=0}
fn put(w:&mut[u64],q:QubitId,k:usize,v:bool){let mask=1u64<<k;if v{w[q.0 as usize]|=mask;}else{w[q.0 as usize]&=!mask;}}
fn word(w:&mut[u64],q:&[QubitId],k:usize,v:usize){for(i,&q)in q.iter().enumerate(){put(w,q,k,(v>>i)&1!=0);}}
fn read(w:&[u64],q:&[QubitId],k:usize)->usize{q.iter().enumerate().fold(0,|a,(i,&q)|a|(usize::from(bit(w,q,k))<<i))}
fn hash(ops:&[NativeOp])->String{let mut h=sha3::Keccak256::new();for o in ops{Digest::update(&mut h,(o.kind as u32).to_le_bytes());for x in [o.q_control1.0,o.q_control2.0,o.q_target.0,o.c_condition.0,o.c_target.0,o.r_target.0]{Digest::update(&mut h,x.to_le_bytes());}}format!("{:x}",h.finalize())}
fn emit(b:&mut B,t:&[G],inverse:bool)->Vec<NativeOp>{b.ops.clear();b.tof=0;b.global_cancel=false;b.play(t,inverse);b.flush_global();assert!(b.ops.len()<100_000&&b.c162_audit.is_empty());b.ops.clone()}
fn run(ops:&[NativeOp],w:&[u64],sign:u64)->(Vec<u64>,u64){let mut h=sha3::Shake256::default();Update::update(&mut h,b"k5-ph-controller-fixed-local-v1");let mut rng=h.finalize_xof();let mut s=Simulator::new(660,10002,&mut rng);s.qubits.clone_from_slice(w);s.phase=sign;s.apply_iter(ops.iter());(s.qubits,s.phase)}
fn diff(a:&[u64],b:&[u64])->u64{a.iter().zip(b).fold(0,|m,(a,b)|m|(a^b))}
fn uses(o:&NativeOp,q:QubitId)->bool{[o.q_control1,o.q_control2,o.q_target].contains(&q)}
fn pure(ops:&[NativeOp]){assert!(ops.iter().all(|o|matches!(o.kind,K::X|K::CX|K::CCX)&&o.c_condition==NO_BIT));}
#[derive(Clone,Copy,Debug)]
struct Profile{traversal:Traversal,ht:bool,parked:bool,kind:usize}
fn profiles()->Vec<Profile>{let mut p=vec![];for traversal in [Traversal::T1,Traversal::T2,Traversal::T3,Traversal::T4]{for ht in [false,true]{for parked in [false,true]{for kind in 0..if ht{3}else{2}{p.push(Profile{traversal,ht,parked,kind});}}}}assert_eq!(p.len(),40);p}
struct Rig{b:B,ring:Vec<QubitId>,q:Vec<QubitId>,p:Vec<QubitId>,meta:SumSize,ph:QubitId,r:Roles,spectator:QubitId}
impl Rig{
 fn new()->Self{let mut b=B::new();b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;b.global_cancel=false;let ring=b.alloc_n(257);let q=b.alloc_n(128);let p=b.alloc_n(258);let meta=SumSize{y:b.alloc_n(7).try_into().unwrap(),sum:b.alloc_n(5).try_into().unwrap()};let ph=b.alloc();let r=Roles{activity:b.alloc(),flight:b.alloc(),mask:b.alloc()};let spectator=b.alloc();assert_eq!((b.width(),spectator.0),(660,659));Self{b,ring,q,p,meta,ph,r,spectator}}
 fn context(&self,p:Profile)->Context<'_>{Context{size:&self.meta,ring:&self.ring,q:&self.q,ph:self.ph,roles:self.r,dirty:&self.p,y_bounds:(1,128),qb:30,clean_external:if p.traversal.has_payload(){&[]}else{&self.p[..2]},excluded:std::slice::from_ref(&self.spectator),traversal:p.traversal}}
 fn capture(&mut self,p:Profile,candidate:bool,fault:usize)->Vec<G>{
 let c=Context{size:&self.meta,ring:&self.ring,q:&self.q,ph:self.ph,roles:self.r,dirty:&self.p,y_bounds:(1,128),qb:30,clean_external:if p.traversal.has_payload(){&[]}else{&self.p[..2]},excluded:std::slice::from_ref(&self.spectator),traversal:p.traversal};
 let t=frame::natural_target(&c,0);self.b.begin();
 if p.ht&&!p.parked&&fault!=2{self.b.cx(self.r.activity,self.ph);}
 if candidate{
 let mut controller=Controller::new(&c,p.traversal.has_payload());controller.enter(&mut self.b);
 if fault==4{self.b.cx(self.ph,self.r.flight);} // prohibited PH metadata query
 let tape=arithmetic::diagnostic(&mut self.b,&c,&t,p.ht,if p.parked{Source::Parked}else{Source::EmptyQ},p.kind,if fault==1{1}else{0});
 // The arithmetic record has no PH port except explicit close/park, which
 // this probe does not request. PH is data solely in the frame permutation.
 assert!(tape.iter().all(|g|match g{G::X(q)=>*q!=self.ph,G::Cx(a,z)=>*a!=self.ph&&*z!=self.ph,G::Ccx(a,z,t)=>*a!=self.ph&&*z!=self.ph&&*t!=self.ph,_=>false}));
 self.b.play(&tape,false);controller.leave(&mut self.b);assert!(controller.is_raw());
 }else{
 // Old parent reference uses PH as its x128 data and the reserved original
 // prefix spectator as its PH carry. Only this reference owns four roles.
 let old=super::super::cross_four::Cross{size:&self.meta,ring:&self.ring,q:&self.q,phase:self.spectator,roles:super::super::cross_four::Roles{activity:self.r.activity,flight:self.r.flight,mask:self.r.mask,x128:self.ph},dirty:&self.p,y_bounds:(1,128),qb:30,clean_external:c.clean_external};
 let frame=super::super::normalized_cross_frame::record(&mut self.b,&old);self.b.play(&frame,false);
 let record=ph_reference_record(&mut self.b,&old,&t,p.ht,p.parked,p.kind);self.b.play(&record,false);self.b.play(&frame,true);
 }
 if p.ht&&!p.parked&&fault!=3{self.b.cx(self.r.activity,self.ph);}
 let out=self.b.end();assert!(out.len()<100_000);out
 }
 /// EmptyQ probes begin at a raw phase boundary with the outer HT pair.
 /// Parked probes begin inside the retained epoch: raw PH is park data,
 /// so they neither impose PH phase care nor repeat HT conjugation.
 /// Independent index permutation, used for fixed fixture coordinates and
 /// oracle expectations. This does not invoke the builder or candidate code.
 fn rotate(&self,w:&[u64],forward:bool)->Vec<u64>{let mut out=w.to_vec();let cycle:Vec<_>=self.q.iter().copied().chain([self.ph]).collect();for k in 0..64{let delta=127-read(w,&self.meta.y,k);for i in 0..129{let j=(i+delta)%129;if forward{put(&mut out,cycle[j],k,bit(w,cycle[i],k));}else{put(&mut out,cycle[i],k,bit(w,cycle[j],k));}}for i in 0..257{let j=(i+257-delta)%257;if forward{put(&mut out,self.ring[j],k,bit(w,self.ring[i],k));}else{put(&mut out,self.ring[i],k,bit(w,self.ring[j],k));}}}out}
 fn fixture(&self,p:Profile,batch:usize)->Vec<u64>{let mut seed=SEED^(batch as u64)<<32^(p.kind as u64)<<16^u64::from(p.ht)^u64::from(p.parked)<<8;let mut w:Vec<_>=(0..660).map(|_|next(&mut seed)).collect();w[self.r.mask.0 as usize]=0;
 for k in 0..64{let delta=batch*4+k/16;let e=127-delta;let sum=(k*7+batch)%32;let gate=sum<17usize.max(e.saturating_sub(96));let active=k%4!=0;let flight=if p.kind==2{active&&gate&&k&2!=0}else{!active&&gate&&k&2!=0};word(&mut w,&self.meta.y,k,e);word(&mut w,&self.meta.sum,k,sum);put(&mut w,self.r.activity,k,active);put(&mut w,self.r.flight,k,flight);
 if active||flight{put(&mut w,self.q[127],k,true);}
 if active{if !p.parked{put(&mut w,self.ph,k,false);}for i in 0..delta{if !p.parked||i>=14{put(&mut w,self.q[i],k,false);}}if !p.parked{put(&mut w,if delta==0{self.ph}else{self.q[delta-1]},k,false);}put(&mut w,self.spectator,k,p.ht);}
 }
 if !p.traversal.has_payload(){w[self.p[0].0 as usize]=0;w[self.p[1].0 as usize]=0;}
 let mut raw=self.rotate(&w,false);if p.ht&&!p.parked{raw[self.ph.0 as usize]^=raw[self.r.activity.0 as usize];}for k in 0..64{if !p.parked&&bit(&raw,self.r.activity,k){assert_eq!(bit(&raw,self.ph,k),p.ht);}}raw
 }
 fn oracle(&self,p:Profile,w:&[u64])->Vec<u64>{let mut raw=w.to_vec();if p.ht&&!p.parked{raw[self.ph.0 as usize]^=raw[self.r.activity.0 as usize];}let mut n=self.rotate(&raw,true);let entry=n.clone();let target:Vec<_>=(0..129).map(|j|self.ring[256-j]).collect();
 for k in 0..64{let e=read(&entry,&self.meta.y,k);let sum=read(&entry,&self.meta.sum,k);if !bit(&entry,self.r.activity,k)||sum>=17usize.max(e.saturating_sub(96)){continue;}
 let delta=127-e;let q:Vec<_>=(0..129).map(|i|i<128&&i>=delta&&bit(&entry,self.q[i],k)).collect();let t:Vec<_>=target.iter().map(|&q|bit(&entry,q,k)).collect();let flight=bit(&entry,self.r.flight,k);
 let greater=t.iter().rev().cmp(q.iter().rev())!=std::cmp::Ordering::Less;
 let mut added=vec![false;129];let mut carry=false;for i in 0..129{let sum=u8::from(t[i])+u8::from(q[i])+u8::from(carry);added[i]=sum&1!=0;carry=sum>=2;}
 let mut sub=vec![false;129];let mut borrow=false;for i in 0..129{let v=(t[i] as i8)-(q[i] as i8)-(borrow as i8);sub[i]=(v&1)!=0;borrow=v<0;}
 let (value,decision)=match p.kind{0=>(if greater{sub}else{t},greater),1=>(if !carry{added}else{t},!carry),2=>(if flight{added}else{t},flight),_=>unreachable!()};
 for(i,&q)in target.iter().enumerate(){put(&mut n,q,k,value[i]);}put(&mut n,self.r.flight,k,decision);
 }
 let mut out=self.rotate(&n,false);if p.ht&&!p.parked{out[self.ph.0 as usize]^=out[self.r.activity.0 as usize];}out
 }
}
fn guards()->usize {
 let r=Rig::new();let p=Profile{traversal:Traversal::T1,ht:false,parked:true,kind:0};
 for which in 0..4 {let excluded=[r.q[0]];let mut c=r.context(p);
 match which {0=>c.ph=c.roles.activity,1=>c.excluded=&excluded,2=>c.clean_external=&r.p[..2],_=>{}}
 let caught=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||{if which==3{let _=Controller::new(&c,false);}else{c.check();}}));
 let expected=match which{0|1=>"K5_PH_PORT_ALIAS",2=>"K5_PH_LOANS",_=>"K5_PH_TRAVERSAL"};
 match caught {Ok(_)=>panic!("accepted wrong PH binding"),Err(e)=>{let msg=e.downcast_ref::<String>().map(|x|x.as_str()).or_else(||e.downcast_ref::<&str>().copied());if !msg.is_some_and(|s|s.contains(expected)){std::panic::resume_unwind(e);}}}
 }4
}
#[test]
fn k5_ph_controller_local_native(){
 assert!(std::mem::size_of::<G>()<=128&&std::mem::size_of::<NativeOp>()<=64);
 assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());assert!(std::env::var_os("LS_NO_BAKE").is_none());
 for key in include_str!("c162_consulted_env.txt").lines(){if let Some(v)=std::env::var_os(key){let expected=super::super::BAKED_KNOBS.iter().find(|(k,_)|*k==key).map(|(_,v)|*v);assert!(expected.is_some_and(|s|v==std::ffi::OsStr::new(s)),"K5 PH inherited override {key}");}}
 let profiles=profiles();let mut baselines=vec![];let(mut baseline_rows,mut good_rows,mut applications,mut mutations)=(0usize,0usize,0usize,0usize);
 // Complete all original-parent forward/oracle/inverse baselines FIRST.
 for(id,&p)in profiles.iter().enumerate(){let mut r=Rig::new();let tape=r.capture(p,false,0);let f=emit(&mut r.b,&tape,false);let inv=emit(&mut r.b,&tape,true);pure(&f);pure(&inv);for batch in 0..BATCHES{let w=r.fixture(p,batch);let expected=r.oracle(p,&w);let sign=SEED^batch as u64;let(out,phase)=run(&f,&w,sign);assert_eq!((&out,phase),(&expected,sign),"parent baseline {id}/{batch} input={w:?}");assert_eq!(run(&inv,&out,phase),(w,sign));baseline_rows+=64;applications+=128;}baselines.push((hash(&f),hash(&inv)));println!("K5_PH_BASELINE id={id} profile={p:?} rows=2048 forward_hash={} inverse_hash={}",hash(&f),hash(&inv));}
 assert_eq!(baseline_rows,81920);let guards=guards();assert_eq!(guards,4);
 for(id,&p)in profiles.iter().enumerate(){let mut r=Rig::new();let parent=r.capture(p,false,0);let pf=emit(&mut r.b,&parent,false);let pi=emit(&mut r.b,&parent,true);assert_eq!((hash(&pf),hash(&pi)),baselines[id]);drop(pf);drop(pi);drop(parent);
 let tape=r.capture(p,true,0);let f=emit(&mut r.b,&tape,false);let inv=emit(&mut r.b,&tape,true);pure(&f);pure(&inv);assert!(!f.iter().chain(&inv).any(|o|uses(o,r.spectator)));
 let mut seen=[false;128];for batch in 0..BATCHES{let w=r.fixture(p,batch);let sign=SEED^batch as u64;let expected=r.oracle(p,&w);let(out,phase)=run(&f,&w,sign);assert_eq!((&out,phase),(&expected,sign),"candidate {id}/{batch} input={w:?}");assert_eq!(run(&inv,&out,phase),(w.clone(),sign));for k in 0..64{seen[127-read(&w,&r.meta.y,k)]=true;}good_rows+=64;applications+=128;}
 assert!(seen.into_iter().all(|v|v));
 let w=r.fixture(p,0);let sign=SEED;let expected=r.oracle(p,&w);
 for fault in if p.ht&&!p.parked{vec![2,3,4]}else{vec![4]}{let bad=r.capture(p,true,fault);let ops=emit(&mut r.b,&bad,false);let(out,phase)=run(&ops,&w,sign);assert_ne!(diff(&out,&expected)|(phase^sign),0,"ineffective PH fault {id}/{fault}");println!("K5_PH_MUTANT profile={id} fault={fault} mask={:016x} hash={}",diff(&out,&expected)|(phase^sign),hash(&ops));mutations+=1;applications+=64;}
 if p.parked&&p.kind==0{let bad=r.capture(p,true,1);let ops=emit(&mut r.b,&bad,false);let mut caught=0;for batch in 0..BATCHES{let w=r.fixture(p,batch);let(out,phase)=run(&ops,&w,SEED);caught|=diff(&out,&r.oracle(p,&w))|(phase^SEED);applications+=64;}assert_ne!(caught,0,"ineffective wrong-root {id}");mutations+=1;println!("K5_PH_ROOT_MUTANT profile={id} mask={caught:016x} hash={}",hash(&ops));}
 for control in 0..3{let mut bad=tape.clone();bad.push(match control{0=>G::Cz(r.r.activity,r.meta.y[0]),1=>G::X(r.p[2]),_=>G::X(r.spectator)});let ops=emit(&mut r.b,&bad,false);let(out,phase)=run(&ops,&w,sign);if control==0{assert_eq!(out,expected);assert_ne!(phase,sign);}else{assert_eq!(phase,sign);assert_ne!(out,expected);}applications+=64;mutations+=1;println!("K5_PH_OBSERVER_CONTROL profile={id} kind={control} mask={:016x} phase_delta={:016x}",diff(&out,&expected),phase^sign);}
 println!("K5_PH_PROFILE id={id} rows=2048 all128separators=true signed=true all660wires=true fourth_spectator=true candidate_hash={} inverse_hash={} Q=660",hash(&f),hash(&inv));
 }
 assert_eq!((good_rows,mutations,applications),(81920,192,355840));
 println!("K5_PH_LOCAL_COMPLETE tests=1 profiles=40 baseline_rows={baseline_rows} candidate_rows={good_rows} native_row_applications={applications} effective_controls={mutations} selector_guards={guards} every_separator=true actual_caller_images=false complete_controller_runtime=false payload_bridge_runtime=false S5_composition=false Q659=false submit=CLOSED");
}
