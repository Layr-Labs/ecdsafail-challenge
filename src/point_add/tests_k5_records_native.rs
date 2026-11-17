//! Frozen source-only K5 harness. No execution accompanies preparation.
//! Forward ABI probes and their own inverse images; no caller reachability claim.
use super::*;
use super::k5_records::{self as k5,Fault};
use super::super::{cross_four::Roles,sum_size::SumSize};
use crate::circuit::{Op as NativeOp,OperationType as K,NO_BIT};
use crate::sim::Simulator;
use sha3::{Digest,digest::{ExtendableOutput,Update}};
const SEED:u64=0x4b355f5245432026;
const BATCHES:usize=31;
const DELTAS:[usize;19]=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,40,100,127];
fn rng(s:&mut u64)->u64 {*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:QubitId,k:usize,v:bool){let bit=1u64<<k;let a=&mut w[q.0 as usize];if v {*a|=bit}else{*a&=!bit}}
fn word(w:&mut[u64],q:&[QubitId],k:usize,v:usize){for(i,&q)in q.iter().enumerate(){put(w,q,k,(v>>i)&1!=0);}}
fn read(w:&[u64],q:&[QubitId],k:usize)->usize{q.iter().enumerate().fold(0,|v,(i,q)|v|((((w[q.0 as usize]>>k)&1)as usize)<<i))}
fn digest(ops:&[NativeOp])->String{
 let mut h=sha3::Keccak256::new();for o in ops{Digest::update(&mut h,(o.kind as u32).to_le_bytes());
 for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{Digest::update(&mut h,v.to_le_bytes());}}
 format!("{:x}",h.finalize())
}
fn words_hash(w:&[u64])->String{let mut h=sha3::Keccak256::new();for v in w{Digest::update(&mut h,v.to_le_bytes());}format!("{:x}",h.finalize())}
fn counts(ops:&[NativeOp])->(usize,usize){(ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len())}
fn uses(o:&NativeOp,q:QubitId)->bool{[o.q_control1,o.q_control2,o.q_target].contains(&q)}
fn emit(b:&mut B,t:&[G],inverse:bool)->Vec<NativeOp>{
 b.ops.clear();b.tof=0;b.global_cancel=false;b.play(t,inverse);b.flush_global();
 assert!(b.ops.len()<100_000&&b.c162_audit.is_empty());b.ops.clone()
}
fn source_counts(t:&[G])->(usize,usize){
 let(mut ccx,mut ops)=(0,0);for g in t{match g{G::X(_)|G::Cx(..)=>ops+=1,G::Ccx(..)=>{ccx+=1;ops+=1},_=>panic!("K5 unexpected raw source primitive {g:?}")}}(ccx,ops)
}
fn pure(ops:&[NativeOp]){for o in ops{assert!(matches!(o.kind,K::X|K::CX|K::CCX));assert_eq!(o.c_condition,NO_BIT);}}
fn play(ops:&[NativeOp],w:&[u64],sign:u64)->(Vec<u64>,u64){
 let mut h=sha3::Shake256::default();Update::update(&mut h,b"k5-signed-native-fixed-v1");let mut xof=h.finalize_xof();
 let mut s=Simulator::new(w.len(),10002,&mut xof);s.qubits.clone_from_slice(w);s.phase=sign;s.apply_iter(ops.iter());(s.qubits,s.phase)
}
fn difference(a:&[u64],b:&[u64])->u64{a.iter().zip(b).fold(0,|m,(a,b)|m|(a^b))}
fn require(got:&[u64],phase:u64,want:&[u64],sign:u64,label:&str,profile:usize,batch:usize,input:&[u64]){
 if got!=want||phase!=sign{println!("K5_FAILURE label={label} profile={profile} batch={batch} difference={:016x} phase_delta={:016x} input_hash={} input={input:?} actual={got:?} expected={want:?}",difference(got,want),phase^sign,words_hash(input));}
 assert_eq!((got,phase),(want,sign),"K5 fixed fixture retained; no replacement");
}

// The reference is the original Cuccaro record arithmetic, generalized only
// in operand/prefix lengths for finite tests. Full tests call parent_record.
fn small_parent_prefix(b:&mut B,t:&[QubitId],q:&[QubitId],meta:&[QubitId],a:QubitId,e:QubitId,m:QubitId,carry:QubitId,pn:usize,add:bool,down:bool,d:&[QubitId]){
 let mut p=Prefix{e:meta,root:q[q.len()-1],cur:None};p.enter(b,d);
 if down{p.goto(b,16-pn);k5::parity(b,&mut p,m,pn);b.cswap(m,carry,q[pn-1]);}
 let order:Vec<_>=if down{(0..pn).rev().collect()}else{(0..pn).collect()};
 for i in order{p.goto(b,15-i);let x=if i==0{carry}else{q[i-1]};
  if down{controlled_cell(b,q[i],t[i],x,m,true,d);b.cx(q[i],x);
   let mut ctl=vec![(m,false),(e,false),(x,false)];if !add{ctl.push((a,false));}lit(b,&ctl,t[i],d);b.cx(q[i],x);
   if i>0{first_swap(b,&p,carry,q[i-1],d);}p.xor_eq(b,m);
  }else{p.xor_eq(b,m);if i>0{first_swap(b,&p,carry,q[i-1],d);}controlled_cell(b,q[i],t[i],x,m,false,d);}
 }
 if !down{b.cswap(m,carry,q[pn-1]);k5::parity(b,&mut p,m,pn);}p.leave(b,d);
}
fn small_parent(b:&mut B,t:&[QubitId],q:&[QubitId],meta:&[QubitId],sum:&[QubitId],a:QubitId,e:QubitId,m:QubitId,carry:QubitId,pn:usize,op:Op,d:&[QubitId]){
 let n=q.len();let add=matches!(op,Op::Add);let split=matches!(op,Op::VBit(VTop::Frame(0)));
 if pn>0{small_parent_prefix(b,t,q,meta,a,e,m,carry,pn,add,false,d);}
 for i in pn..n{cell(b,q[i],t[i],if i==pn{carry}else{q[i-1]},false);}
 let query=|b:&mut B,high:bool|xor_terms(b,&if high{cover(sum,2,32)}else{cover(sum,0,2)},m,&[(a,false)],d);
 if !add{if split{query(b,false);normal_decision(b,m,e,t[n],q[n-1],d);query(b,false);}else{normal_decision(b,a,e,t[n],q[n-1],d);}}
 if add{b.cx(e,m);}else{b.ccx(a,e,m);}b.ccx(m,q[n-1],t[n]);
 for i in (pn..n).rev(){let x=if i==pn{carry}else{q[i-1]};cell(b,q[i],t[i],x,true);
  if split&&i==n-1{b.ccx(a,e,m);query(b,true);lit(b,&[(m,false),(t[i],true),(x,true)],e,d);query(b,true);b.ccx(a,e,m);}
  b.cx(q[i],x);b.ccx(m,x,t[i]);b.cx(q[i],x);
 }
 if add{b.cx(e,m);}else{b.ccx(a,e,m);}
 if pn>0{small_parent_prefix(b,t,q,meta,a,e,m,carry,pn,add,true,d);}
}
fn operation(id:usize)->Op{match id{0=>Op::Divide,1=>Op::VBit(VTop::Zero),2=>Op::VBit(VTop::Frame(0)),3=>Op::Add,_=>unreachable!()}}
struct Small{b:B,q:Vec<QubitId>,t:Vec<QubitId>,meta:Vec<QubitId>,sum:Vec<QubitId>,a:QubitId,e:QubitId,m:QubitId,carry:QubitId,dirty:Vec<QubitId>}
impl Small{
 fn new(n:usize)->Self{let mut b=B::new();b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
  let q=b.alloc_n(n);let t=b.alloc_n(n+1);let meta=b.alloc_n(7);let sum=b.alloc_n(5);let a=b.alloc();let e=b.alloc();let m=b.alloc();let carry=b.alloc();let dirty=b.alloc_n(6);
  Self{b,q,t,meta,sum,a,e,m,carry,dirty}}
 fn tapes(&mut self,pn:usize,id:usize)->Vec<Vec<NativeOp>>{
  let mut out=vec![];for candidate in [false,true]{self.b.begin();if id==0{for &q in &self.t{self.b.x(q);}}
   if !candidate{small_parent(&mut self.b,&self.t,&self.q,&self.meta,&self.sum,self.a,self.e,self.m,self.carry,pn,operation(id),&self.dirty);}
   else if pn==0{k5::form_n(&mut self.b,&self.t,&self.q,self.a,self.e,self.m,&self.sum,operation(id),&self.dirty,Fault::None);}
   else{k5::form_p(&mut self.b,&self.t,&self.q,&self.meta,&self.sum,self.a,self.e,self.m,pn,operation(id),&self.dirty,Fault::None);}
   if id==0{for &q in &self.t{self.b.x(q);}}let tape=self.b.end();let forward=emit(&mut self.b,&tape,false);assert_eq!(source_counts(&tape),counts(&forward));
   out.push(forward);out.push(emit(&mut self.b,&tape,true));
  }for ops in &out{pure(ops);}out
 }
 fn oracle(&self,w:&[u64],valid:u64,pn:usize,id:usize)->Vec<u64>{
  // Independent integer semantics, not a carry-gate transcription. Prefix
  // parks are virtual zero operands; the held physical Q cells are returned.
  let n=self.q.len();let low_mask=(1usize<<n)-1;let full_mask=(1usize<<(n+1))-1;let mut out=w.to_vec();
  for k in 0..64{if (valid>>k)&1==0||(w[self.a.0 as usize]>>k)&1==0{continue;}
   let mut q=read(w,&self.q,k);if pn>0{let delta=127-read(w,&self.meta,k);q&=!((1usize<<delta.min(pn))-1);}
   let t=read(w,&self.t,k);let e=(w[self.e.0 as usize]>>k)&1!=0;let s=read(w,&self.sum,k);
   let (value,decision)=match id{
    0=>{let dec=t>=q;(if dec{t-q}else{t},dec)},
    1=>{let dec=t+q<=full_mask;(if dec{t+q}else{t},dec)},
    2=>{let carry=(t&low_mask)+q>low_mask;let first=s<2&&!(t>>n!=0&&carry);let dec=first^(s>=2&&!carry);
      let top=(t>>n)^usize::from(first&&carry);let low=((t&low_mask)+if dec{q}else{0})&low_mask;((top<<n)|low,dec)},
    3=>((t+if e{q}else{0})&full_mask,e),_=>unreachable!(),
   };
   word(&mut out,&self.t,k,value);put(&mut out,self.e,k,decision);
  }out
 }
 fn check(&self,ops:&[Vec<NativeOp>],w:&[u64],valid:u64,pn:usize,id:usize,tag:&str){
  let sign=SEED^valid;let(p,ps)=play(&ops[0],w,sign);let(c,cs)=play(&ops[2],w,sign);
  let expected=self.oracle(w,valid,pn,id);
  assert_eq!((difference(&p,&expected)&valid,difference(&c,&expected)&valid,(ps^sign)&valid,(cs^sign)&valid),(0,0,0,0),"small {tag} input={w:?} parent={p:?} candidate={c:?} independent={expected:?}");
  let(pi,pis)=play(&ops[1],&p,ps);let(ci,cis)=play(&ops[3],&c,cs);
  assert_eq!((difference(&pi,w)&valid,difference(&ci,w)&valid,(pis^sign)&valid,(cis^sign)&valid),(0,0,0,0));
 }
}
fn small_tests()->usize{
 let mut total=0;
 // Form N: full q/t, two dirty bits, every allowed A/e/carry combination.
 // Split tests both S classes. Mask=0 is the retained original contract.
 for n in 2..=6{let mut r=Small::new(n);let mut count=0;
  for id in 0..4{let ops=r.tapes(0,id);for sum in if id==2{vec![0,2]}else{vec![0]}{
   let mut w=vec![0;r.b.width()as usize];let mut k=0;
   for av in 0..2{for ev in 0..2{
    if (id==3&&ev==1&&av==0)||(id!=3&&ev==1&&av==1){continue;}
    for cv in 0..if av==0{2}else{1}{for qv in if av==0{0}else{1usize<<(n-1)}..1usize<<n{for tv in 0..1usize<<(n+1){for dv in 0..4{
     word(&mut w,&r.q,k,qv);word(&mut w,&r.t,k,tv);word(&mut w,&r.dirty,k,dv);word(&mut w,&r.sum,k,sum);
     put(&mut w,r.a,k,av!=0);put(&mut w,r.e,k,ev!=0);put(&mut w,r.carry,k,cv!=0);k+=1;count+=1;
     if k==64{r.check(&ops,&w,u64::MAX,0,id,"N exhaustive");w.fill(0);k=0;}
    }}}}
   }}if k>0{r.check(&ops,&w,(1u64<<k)-1,0,id,"N final batch");}
  }}println!("K5_SMALL_N width={n} rows={count} operand_and_two_donor_exhaustive=true");total+=count;
 }
 assert_eq!(total,916608);
 let mut ptotal=0;
 // Form P: active operand basis exhaustive at widths2..4; fixed 64-row
 // operand probes at widths5..6. Every width also has 64 dirty inactive
 // probes per separator/op/S class; these are explicitly not exhaustive.
 for n in 2..=6{let mut r=Small::new(n);let pn=n-1;let mut count=0;
  for id in 0..4{let ops=r.tapes(pn,id);for sum in if id==2{vec![0,2]}else{vec![0]}{for delta in 0..=n{
   let active_rows=if n<=4{1usize<<(2*n)}else{64};let mut state=SEED^((n as u64)<<40)^((id as u64)<<32)^delta as u64;
   let mut w=vec![0;r.b.width()as usize];let mut k=0;
   for row in 0..active_rows+64{
    let active=row<active_rows;
    let(qv,tv)=if active&&n<=4{((1usize<<(n-1))+(row>>(n+1)),row&((1usize<<(n+1))-1))}else{(rng(&mut state)as usize&((1usize<<n)-1),rng(&mut state)as usize&((1usize<<(n+1))-1))};
    word(&mut w,&r.q,k,if active{qv|(1usize<<(n-1))}else{qv});word(&mut w,&r.t,k,tv);word(&mut w,&r.meta,k,127-delta);word(&mut w,&r.sum,k,sum);
    put(&mut w,r.a,k,active);put(&mut w,r.e,k,if id==3{active}else{!active&&row&1!=0});put(&mut w,r.carry,k,!active&&row&2!=0);
    word(&mut w,&r.dirty,k,if active{0}else{row&63});k+=1;count+=1;
    if k==64{r.check(&ops,&w,u64::MAX,pn,id,"P fixed contract");w.fill(0);k=0;}
   }if k>0{r.check(&ops,&w,(1u64<<k)-1,pn,id,"P final batch");}
  }}}println!("K5_SMALL_P width={n} prefix={pn} rows={count} active_operand_exhaustive={} dirty_inactive_fixed=true",n<=4);ptotal+=count;
 }
 assert_eq!(ptotal,20080);assert_eq!(total+ptotal,936688);total+ptotal
}

#[derive(Clone,Copy,Debug)]
struct Profile{optimized:bool,ht:bool,first:usize,delta:Option<usize>,kind:usize}
impl Profile{
 fn policy(self)->SourcePolicy{if self.delta.is_some()||self.first>=14{SourcePolicy::Parked}else{SourcePolicy::EmptyQ}}
 fn legacy_unparked(self)->bool{self.policy()==SourcePolicy::EmptyQ&&(if let Gate::Top(j)=self.gate(){self.hi().min(128-j)}else{self.hi()})>=115}
 fn hi(self)->usize{if self.delta.is_some(){128}else{128-self.first}}
 fn gate(self)->Gate{match self.kind{0|6|7|10=>Gate::Top(0),1|8|9=>Gate::Top(13),2|3|5=>Gate::Bottom(13),4=>Gate::Bottom(0),_=>unreachable!()}}
 fn op(self)->Op{match self.kind{0..=2|10=>Op::Divide,3=>Op::Add,4|5=>Op::VBit(VTop::Zero),6|7=>Op::VBit(VTop::Frame(0)),8|9=>Op::VBit(VTop::Frame(13)),_=>unreachable!()}}
 fn prefix(self)->bool{let hi=if let Gate::Top(j)=self.gate(){self.hi().min(128-j)}else{self.hi()};hi>=115&&self.policy()==SourcePolicy::Parked}
 fn actual_first(self)->usize{if self.prefix(){14}else{128-if let Gate::Top(j)=self.gate(){self.hi().min(128-j)}else{self.hi()}}}
 fn has_acted_rows(self)->bool{!matches!((self.delta,self.gate()),(Some(delta),Gate::Top(j)) if delta<j)}
 // E=112/113 has clean high-prefix cells and low nibble0/1, outside leaves2..15.
 fn root_fault_zero_support(self)->bool{matches!(self.delta,Some(14|15))}
 fn close(self,r:&Rig)->Close{match self.kind{1=>Close::Inplace,2=>Close::EraseInplace(r.q[12]),10=>Close::EraseInplace(r.r.x128),5=>Close::Store(VTop::Zero),7=>Close::Store(VTop::Frame(0)),9=>Close::Store(VTop::Frame(13)),_=>Close::None}}
}
fn profiles()->Vec<Profile>{
 let mut out=vec![];for optimized in [false,true]{
  for first in [0,1,13,14,95]{for ht in [false,true]{for kind in 0..11{
   if (kind==3&&!ht)||(matches!(kind,2|10)&&first<14){continue;}out.push(Profile{optimized,ht,first,delta:None,kind});
  }}}
  for delta in DELTAS{for ht in [false,true]{for kind in 0..11{if kind==3&&!ht{continue;}out.push(Profile{optimized,ht,first:14,delta:Some(delta),kind});}}}
 }assert_eq!(out.len(),984);out
}
struct Rig{b:B,ring:Vec<QubitId>,q:Vec<QubitId>,p:Vec<QubitId>,meta:SumSize,ph:QubitId,r:Roles}
impl Rig{
 fn new()->Self{let mut b=B::new();let ring=b.alloc_n(257);let q=b.alloc_n(128);let p=b.alloc_n(258);let meta=SumSize{y:b.alloc_n(7).try_into().unwrap(),sum:b.alloc_n(5).try_into().unwrap()};let ph=b.alloc();let r=Roles{activity:b.alloc(),flight:b.alloc(),mask:b.alloc(),x128:b.alloc()};assert_eq!(b.width(),660);Self{b,ring,q,p,meta,ph,r}}
 fn target(&self,p:Profile)->Vec<QubitId>{match p.gate(){Gate::Top(j)=>(0..129).map(|i|self.ring[(256+j-i)%257]).collect(),Gate::Bottom(k)=>(0..129).map(|i|self.ring[256-k-i]).collect(),_=>unreachable!()}}
 fn capture(&mut self,p:Profile,candidate:bool,original:bool,fault:Fault)->Vec<G>{
  self.b.cancel_simple_pairs=p.optimized;self.b.cancel_commuting_pairs=p.optimized;self.b.global_cancel=false;
  let t=self.target(p);let close=p.close(self);
  let c=Cross{size:&self.meta,ring:&self.ring,q:&self.q,phase:self.ph,roles:self.r,dirty:&self.p,y_bounds:(1,p.hi()),qb:30,clean_external:&[]};
  let d=if candidate{D::k5_records(p.ht,p.policy(),&c,p.gate())}else{D::parent(p.ht,p.legacy_unparked())};
  let tape=if original{d.parent_record(&mut self.b,&c,&t,p.gate(),p.op(),close)}else if fault!=Fault::None{k5::record(&d,&mut self.b,&c,&t,p.gate(),p.op(),close,fault)}else{d.record(&mut self.b,&c,&t,p.gate(),p.op(),close)};
  assert!(tape.len()<100_000);tape
 }
 fn fixture(&self,p:Profile,batch:usize)->(Vec<u64>,[usize;4]){
  let mut seed=SEED^((p.first as u64)<<48)^((p.delta.unwrap_or(255)as u64)<<40)^((p.kind as u64)<<32)^(batch as u64+1);
  let mut w:Vec<_>=(0..660).map(|_|rng(&mut seed)).collect();let mut sectors=[0;4];w[self.r.mask.0 as usize]=0;
  for k in 0..64{
   let e=p.delta.map(|d|127-d).unwrap_or_else(||(batch*64+k)%p.hi());let sum=(batch*7+k)%32;
   let passed=match p.gate(){Gate::Top(j)=>e<128-j&&sum<32-j,Gate::Bottom(j)=>sum<17usize.max(e.saturating_sub(96))-j,_=>unreachable!()};
   let av=k&1!=0;let ev=if p.kind==3{av&&passed&&k&2!=0}else{!av&&passed&&k&2!=0};
   word(&mut w,&self.meta.y,k,e);word(&mut w,&self.meta.sum,k,sum);put(&mut w,self.r.activity,k,av);put(&mut w,self.r.flight,k,ev);
   sectors[if av{if passed{0}else{1}}else if passed{2}else{3}]+=1;
   // Bottom's unchanged witness needs its leading-one decoder on A OR e,
   // even when the resulting arithmetic activity is zero.
   if av||ev{put(&mut w,self.q[127],k,true);}
   if av{
    let delta=127-e;for i in 0..delta{if p.policy()==SourcePolicy::EmptyQ||i>=14{put(&mut w,self.q[i],k,false);}}
    put(&mut w,self.q[127],k,true);put(&mut w,self.ph,k,p.ht);
    if p.legacy_unparked(){put(&mut w,self.r.x128,k,false);}
   }
  }(w,sectors)
 }
 fn assert_abi(&self,p:Profile,w:&[u64]){
  assert_eq!(w[self.r.mask.0 as usize],0);
  for k in 0..64{let av=(w[self.r.activity.0 as usize]>>k)&1!=0;let ev=(w[self.r.flight.0 as usize]>>k)&1!=0;let e=read(w,&self.meta.y,k);let sum=read(w,&self.meta.sum,k);
   let gate=match p.gate(){Gate::Top(j)=>e<128-j&&sum<32-j,Gate::Bottom(j)=>sum<17usize.max(e.saturating_sub(96))-j,_=>unreachable!()};
   if p.kind==3{assert!(!ev||(av&&gate));}else{assert!(!ev||(!av&&gate));}
   if av||ev{assert_eq!((w[self.q[127].0 as usize]>>k)&1,1);assert!(e<p.hi());}
  }
 }
}

fn selector_controls()->usize{
 let mut n=0;
 for ht in [false,true]{for unparked in [false,true]{assert_eq!(D::parent(ht,unparked).contract.body,ArithmeticBody::ParentCuccaro);n+=1;}}
 for site in [HrSite::PayloadTick,HrSite::NoPayloadTwin]{let d=D::hr(K3Diagnostic::OptionB,site);assert_eq!(d.contract.body,ArithmeticBody::K3NaturalTtk);assert_eq!(d.contract.source,SourcePolicy::Unparked);n+=1;}
 for ht in [false,true]{for policy in [SourcePolicy::Parked,SourcePolicy::EmptyQ]{for hi in [114,115,128]{for gate in [Gate::Top(0),Gate::Top(14)]{
  let r=Rig::new();let c=Cross{size:&r.meta,ring:&r.ring,q:&r.q,phase:r.ph,roles:r.r,dirty:&r.p,y_bounds:(1,hi),qb:30,clean_external:&[]};
  let d=D::k5_records(ht,policy,&c,gate);let acted=if let Gate::Top(j)=gate{hi.min(128-j)}else{unreachable!()};
  assert_eq!(d.payload_open,policy==SourcePolicy::EmptyQ&&acted>=115);assert_eq!(d.contract.body,if policy==SourcePolicy::Parked&&acted>=115{ArithmeticBody::K5FormP}else{ArithmeticBody::K5FormN});n+=1;
 }}}}
 let messages=["K5_SELECTOR_CALLER","K5_SELECTOR_FRAME","K5_SELECTOR_CARRY","K5_SELECTOR_SOURCE","K5_SELECTOR_NATURAL","K5_SELECTOR_INDEX","K5_SELECTOR_ADD_HR","K5_SELECTOR_CLOSE","K5_SELECTOR_ERASE_SLOT","K5_SELECTOR_ERASE_POLICY","K5_SELECTOR_BODY","K5_SELECTOR_LEGACY_POLICY","K5_SELECTOR_PORTS"];
 for (which,expected) in messages.iter().enumerate(){
  let mut r=Rig::new();let p=Profile{optimized:false,ht:false,first:14,delta:Some(0),kind:0};let t=r.target(p);
  let mut c=Cross{size:&r.meta,ring:&r.ring,q:&r.q,phase:r.ph,roles:r.r,dirty:&r.p,y_bounds:(1,128),qb:30,clean_external:&[]};
  let mut d=D::k5_records(false,SourcePolicy::Parked,&c,Gate::Top(0));let mut gate=Gate::Top(0);let mut op=Op::Divide;let mut close=Close::None;
  match which{
   0=>d.contract.caller=ArithmeticCaller::Parent,1=>d.contract.frame=ArithmeticFrame::NativeHrQ128Ring257P259,2=>d.contract.carry=CarrySource::ParentDefined,3=>d.contract.source=SourcePolicy::Unparked,
   4=>gate=Gate::Natural(0),5=>gate=Gate::Top(15),6=>op=Op::Add,7=>{op=Op::VBit(VTop::Frame(0));close=Close::Inplace},8=>close=Close::EraseInplace(r.q[0]),9=>{d.contract.source=SourcePolicy::EmptyQ;close=Close::EraseInplace(r.r.x128)},10=>d.contract.body=ArithmeticBody::K5FormN,11=>d.payload_open=true,12=>c.phase=r.q[0],_=>unreachable!(),
  }
  let caught=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||d.record(&mut r.b,&c,&t,gate,op,close)));
  match caught{Ok(_)=>panic!("K5 incompatible selector accepted {which}"),Err(payload)=>{
   let message=payload.downcast_ref::<String>().map(|s|s.as_str()).or_else(||payload.downcast_ref::<&str>().copied());
   if !message.is_some_and(|s|s.contains(expected)){std::panic::resume_unwind(payload);}
  }}assert!(r.b.ops.is_empty());n+=1;
 }
 assert_eq!(n,43);println!("K5_SELECTORS controls={n} parent_choices=4 K3_sites=2 prefix_boundary_choices=24 rejected_exact=13 unrelated_panics_propagate=true");n
}

#[test]
fn k5_records_native_component(){
 assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());assert!(std::env::var_os("LS_NO_BAKE").is_none());
 for key in include_str!("c162_consulted_env.txt").lines(){if let Some(v)=std::env::var_os(key){let expected=super::super::BAKED_KNOBS.iter().find(|(k,_)|*k==key).map(|(_,v)|*v);assert!(expected.is_some_and(|s|v==std::ffi::OsStr::new(s)),"K5 inherited override key {key}");}}
 let profiles=profiles();let mut baseline_hashes=vec![];let mut all_sectors=[0usize;4];let mut baseline_rows=0usize;
 // Every fixed parent fixture and own-image inverse completes before the
 // first candidate is constructed. Retain fingerprints, never entire tapes.
 for (id,&p) in profiles.iter().enumerate(){let mut r=Rig::new();let parent=r.capture(p,false,true,Fault::None);let disabled=r.capture(p,false,false,Fault::None);assert_eq!(parent,disabled);
  let pf=emit(&mut r.b,&parent,false);let pi=emit(&mut r.b,&parent,true);let df=emit(&mut r.b,&disabled,false);let di=emit(&mut r.b,&disabled,true);assert_eq!((&pf,&pi),(&df,&di));pure(&pf);pure(&pi);
  if !p.optimized{assert_eq!(source_counts(&parent),counts(&pf));}
  let mut sector_counts=[0usize;4];for batch in 0..BATCHES{let(w,sectors)=r.fixture(p,batch);r.assert_abi(p,&w);let sign=SEED^batch as u64;
   let(f,phase)=play(&pf,&w,sign);assert_eq!(phase,sign);let(inv,iphase)=play(&pi,&f,phase);require(&inv,iphase,&w,sign,"parent own-image inverse",id,batch,&w);
   for i in 0..4{sector_counts[i]+=sectors[i];all_sectors[i]+=sectors[i];}baseline_rows+=64;
  }
  baseline_hashes.push((digest(&pf),digest(&pi)));
  println!("K5_BASELINE id={id} profile={p:?} actual_first={} prefix={} rows={} sectors={sector_counts:?} T={} N={} forward_hash={} inverse_hash={} disabled_all_fields=true signed_own_image=true",p.actual_first(),p.prefix(),BATCHES*64,counts(&pf).0,counts(&pf).1,digest(&pf),digest(&pi));
 }
 assert_eq!(baseline_rows,1_952_256);assert!(all_sectors.iter().all(|&n|n>0));
 let selectors=selector_controls();let small=small_tests();let(mut full_rows,mut mutations,mut phase_controls,mut dirty_controls,mut root_zero_controls)=(0usize,0usize,0usize,0usize,0usize);
 for (id,&p) in profiles.iter().enumerate(){let mut r=Rig::new();let parent=r.capture(p,false,true,Fault::None);let candidate=r.capture(p,true,false,Fault::None);
  let pf=emit(&mut r.b,&parent,false);let pi=emit(&mut r.b,&parent,true);let cf=emit(&mut r.b,&candidate,false);let ci=emit(&mut r.b,&candidate,true);pure(&cf);pure(&ci);
  assert_eq!((digest(&pf),digest(&pi)),baseline_hashes[id]);assert!(!cf.iter().chain(&ci).any(|o|uses(o,r.ph)));
  if !p.optimized{assert_eq!(source_counts(&candidate),counts(&cf));let delta=counts(&cf).0 as isize-counts(&pf).0 as isize;
   assert_eq!(delta,if p.prefix(){if p.kind==3{-14}else if matches!(p.kind,6|7){-46}else{-65}}else if p.kind==3{0}else if matches!(p.kind,6|7){-9}else{3},"raw T delta profile {id}");
  }
  let mut fault_tapes=vec![(Fault::DroppedS2,r.capture(p,true,false,Fault::DroppedS2))];
  if p.prefix()&&p.kind!=3&&p.has_acted_rows(){fault_tapes.push((Fault::RootOnQ127,r.capture(p,true,false,Fault::RootOnQ127)));fault_tapes.push((Fault::MissingParityConjugation,r.capture(p,true,false,Fault::MissingParityConjugation)));}
  let fault_ops:Vec<_>=fault_tapes.iter().map(|(f,t)|(*f,emit(&mut r.b,t,false))).collect();let mut caught=vec![0u64;fault_ops.len()];let mut leading_mask=0u64;
  let mut witnesses:Vec<Option<(usize,u64,String)>>=vec![None;fault_ops.len()];let mut leading_witness=None;
  for batch in 0..BATCHES{let(w,_)=r.fixture(p,batch);let sign=SEED^batch as u64;
   let(pfout,pp)=play(&pf,&w,sign);let(cfout,cp)=play(&cf,&w,sign);require(&cfout,cp,&pfout,pp,"candidate all-wire forward",id,batch,&w);assert_eq!(pp,sign);
   let(pback,pbp)=play(&pi,&pfout,pp);let(cback,cbp)=play(&ci,&cfout,cp);require(&pback,pbp,&w,sign,"parent inverse",id,batch,&w);require(&cback,cbp,&w,sign,"candidate own-image inverse",id,batch,&w);
   for (j,(_,ops)) in fault_ops.iter().enumerate(){let(bad,phase)=play(ops,&w,sign);let mask=difference(&bad,&pfout)|(phase^sign);caught[j]|=mask;if mask!=0&&witnesses[j].is_none(){witnesses[j]=Some((batch,mask,words_hash(&w)));}}
   let mut broken=w.clone();broken[r.q[127].0 as usize]=0;let(a,ap)=play(&pf,&broken,sign);let(z,zp)=play(&cf,&broken,sign);let mask=difference(&a,&z)|(ap^zp);leading_mask|=mask;
   if mask!=0&&leading_witness.is_none(){leading_witness=Some((batch,mask,words_hash(&broken)));}
   full_rows+=64;
  }
  for (((fault,ops),mask),witness) in fault_ops.iter().zip(&caught).zip(&witnesses){
   assert_ne!(digest(ops),digest(&cf));
   if *fault==Fault::RootOnQ127&&p.root_fault_zero_support(){
    assert_eq!(*mask,0,"source-proved empty root support profile {id}");assert!(witness.is_none());
    println!("K5_ZERO_SUPPORT_CONTROL profile={id} fault={fault:?} mask=0000000000000000 replayed=true unchanged_fixed_rows=true hash={}",digest(ops));root_zero_controls+=1;
   }else{assert_ne!(*mask,0,"required K5 mutation {fault:?} profile {id}");assert!(witness.is_some());println!("K5_MUTANT profile={id} fault={fault:?} mask={mask:016x} replayed=true first_batch_mask_input_hash={witness:?} hash={}",digest(ops));mutations+=1;}
  }
  if p.has_acted_rows(){assert_ne!(leading_mask,0,"leading-one premise mutation profile {id}");assert!(leading_witness.is_some());mutations+=1;println!("K5_MUTANT profile={id} fault=BrokenLeadingOne mask={leading_mask:016x} premise_violation=true replayed=true first_batch_mask_input_hash={leading_witness:?}");}
  else{assert_eq!(leading_mask,0);println!("K5_NO_ACTED_CONTROL profile={id} leading_mask=0 root_parity_catch_not_claimed=true complete_fixed_rows_retained=true");}
  let(w,_)=r.fixture(p,0);let sign=SEED;let(expected,_)=play(&cf,&w,sign);
  let mut phase_bad=candidate.clone();phase_bad.push(G::Cz(r.r.activity,r.q[127]));let bad=emit(&mut r.b,&phase_bad,false);let(same,phase)=play(&bad,&w,sign);assert_eq!(same,expected);assert_ne!(phase,sign);let phase_delta=phase^sign;let phase_hash=digest(&bad);phase_controls+=1;
  let mut dirty_bad=candidate.clone();dirty_bad.push(G::X(r.p[2]));let bad=emit(&mut r.b,&dirty_bad,false);let(wrong,phase)=play(&bad,&w,sign);assert_eq!(phase,sign);assert_ne!(difference(&wrong,&expected),0);dirty_controls+=1;
  println!("K5_HARNESS_CONTROLS profile={id} phase_delta={phase_delta:016x} dirty_mask={:016x} phase_hash={phase_hash} dirty_hash={} input_hash={} actual_replays=true",difference(&wrong,&expected),digest(&bad),words_hash(&w));
  println!("K5_PROFILE id={id} profile={p:?} actual_first={} prefix={} rows={} Q=660 parent_T={} parent_N={} candidate_T={} candidate_N={} parent_hash={} candidate_hash={} inverse_hash={} signed=true all_wires=true PH_spectator=true",p.actual_first(),p.prefix(),BATCHES*64,counts(&pf).0,counts(&pf).1,counts(&cf).0,counts(&cf).1,digest(&pf),digest(&cf),digest(&ci));
 }
 assert_eq!((full_rows,phase_controls,dirty_controls),(1_952_256,984,984));assert_eq!((mutations,root_zero_controls),(2940,80));
 println!("K5_NATIVE_COMPLETE tests=1 profiles=984 small_rows={small} full_rows={full_rows} baseline_rows={baseline_rows} forward_inverse_pairs={} selector_controls={selectors} mutations={mutations} root_zero_support_controls={root_zero_controls} phase_controls={phase_controls} dirty_controls={dirty_controls} raw_and_optimized=true PH_controller_integration=false caller_reachability=false whole_cost=false Q659=false submit=CLOSED",2*full_rows);
}
