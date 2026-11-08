//! One isolated, source-bound component experiment. Never a whole traversal.
use super::{builder::{B,G},direct_column::Column,outer_size::Roles,sum_size::SumSize};
use super::frogdrop_sched::{self,N,Kind};
use super::frogdrop_col::ColPar;
use crate::circuit::{BitId,QubitId,Op,OperationType as K,NO_BIT};
use super::c162_audit::{Simulator,C162Audit,C162Relation,C162Counts,C162Witness,c162_validate_shape};
use sha3::{Digest,digest::{ExtendableOutput,Update}};
use std::collections::BTreeMap;

#[derive(Clone,Copy,Debug)]
enum Route {Parent,Disabled,Candidate}
struct Rig{b:B,ring:Vec<QubitId>,q:Vec<QubitId>,p:Vec<QubitId>,meta:SumSize,roles:Roles,ph:QubitId}
impl Rig{
 fn new()->Self{
  assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
  let mut b=B::new();b.c162_audit_enabled=true;
  let ring=b.alloc_n(257);let q=b.alloc_n(128);let p=b.alloc_n(258);
  let meta=SumSize{y:b.alloc_n(7).try_into().unwrap(),sum:b.alloc_n(5).try_into().unwrap()};
  let roles=Roles{tag:b.alloc(),cut:b.alloc(),toggle:b.alloc(),prefix:b.alloc()};let ph=b.alloc();
  assert_eq!(b.width(),660);Self{b,ring,q,p,meta,roles,ph}
 }
 fn tape(&mut self,cp:&ColPar,payload:bool,route:Route)->Vec<G>{
  assert_eq!(cp.col,162);assert_eq!(cp.sy.1,62);assert!(cp.ht&&!cp.hr);
  let c=Column{meta:&self.meta,roles:self.roles,ring:&self.ring,q:&self.q,phase:self.ph,
    compact:if payload{Some(&self.p)}else{None},dirty:&self.p,clean_external:&[]};
  println!("C162_PORTS route={:?} ring={:?} Q={:?} payload={:?} E={:?} S={:?} roles={:?} PH={:?} H={:?} A={:?}",
    route,self.ring,self.q,self.p,self.meta.y,self.meta.sum,
    [self.roles.tag,self.roles.cut,self.roles.toggle,self.roles.prefix],self.ph,self.q[62],self.q[74]);
  self.b.begin();
  match route {
   Route::Parent=>super::midg::direct_fixed_middle::run(&mut self.b,&c,cp),
   Route::Disabled=>super::midg::direct_fixed_middle::run_c162(&mut self.b,&c,cp,false),
   Route::Candidate=>super::midg::direct_fixed_middle::run_c162(&mut self.b,&c,cp,true),
  }
  self.b.end()
 }
 fn emit(&mut self,tape:&[G],inverse:bool){
  self.b.ops.clear();self.b.c162_audit.clear();self.b.tof=0;
  self.b.play(tape,inverse);self.b.flush_global();
  c162_validate_shape(&self.b.ops,&self.b.c162_audit).expect("C162_UNKNOWN final operation binding");
 }
}
struct Fixture{x:N,z:N,y:N,top:N,p:Vec<bool>,done:bool,counter:usize,kind:&'static str,supported:bool}
fn euclid(x:N)->(Vec<N>,Vec<N>){
 let(mut r,mut t)=(vec![frogdrop_sched::p(),x],vec![N::ZERO,N::from(1u64)]);
 while !r.last().unwrap().is_zero(){let n=r.len();let q=r[n-2]/r[n-1];r.push(r[n-2]-q*r[n-1]);t.push(t[n-2]+q*t[n-1]);}(r,t)
}
fn digest(bytes:&[u8])->String{format!("{:x}",sha3::Keccak256::digest(bytes))}
fn words_hash(words:&[u64],mask:u64)->String{
 let mut h=sha3::Keccak256::new();for w in words{Digest::update(&mut h,(w&mask).to_le_bytes());}format!("{:x}",h.finalize())
}
fn profile()->(frogdrop_sched::Sched,ColPar,Vec<usize>){
 // Reject every literal environment key consulted by this frozen source unless
 // it is a baked knob with the exact baked value. Never print unexpected values.
 assert!(std::env::var_os("LS_NO_BAKE").is_none());
 for key in include_str!("c162_consulted_env.txt").lines(){
  if let Some(value)=std::env::var_os(key){
   let expected=super::BAKED_KNOBS.iter().find(|(k,_)|*k==key).map(|(_,v)|*v);
   assert!(expected.is_some_and(|v|value==std::ffi::OsStr::new(v)),"C162_UNKNOWN inherited override key {}",key);
  }
 }
 super::bake_knobs();
 for &(k,v) in super::BAKED_KNOBS{assert_eq!(std::env::var(k).as_deref(),Ok(v));}
 let sc=frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
 let(cols,_,_)=super::pointadd_frogdrop::col_pars(&sc);
 let maps=super::frogdrop_col::MAP_CTRL_S.with(|m|m.borrow().clone());
 assert_eq!(maps.1,cols.len());
 let cp=cols[162].clone();
 println!("C162_PROFILE baked={:?} map_control={:?} schedule_keccak={} known_env_keccak={} cp={:?} predictor= predict_n_geometry k=24 kp=24 qb=30 tot=83 nq=128 emax=31 nring=257 reserve={} ordinary_extra=0",
  super::BAKED_KNOBS,maps,digest(super::pointadd_frogdrop::SCHED_FROGDROP.as_bytes()),
  digest(include_bytes!("c162_consulted_env.txt")),cp,super::midg::park_reserve());
 (sc,cp,maps.0)
}
fn fixtures(sc:&frogdrop_sched::Sched,cp:&ColPar,maps:&[usize])->Vec<Fixture>{
 let mut out=vec![];let(mut active,mut done)=(0,0);
 let get=|line:&str,key:&str|->String{line.split_whitespace().find_map(|s|s.strip_prefix(&format!("{}=",key))).unwrap().to_string()};
 println!("C162_FIXTURE_LOG keccak={} count=40 seed_search=0",digest(include_bytes!("c162_logged_fixtures.txt")));
 for line in include_str!("c162_logged_fixtures.txt").lines(){
  let i=out.len();assert_eq!(get(line,"shot").parse::<usize>().unwrap(),i);
  let hex=|k|N::from_str_radix(&get(line,k),16).unwrap();
  let x=hex("x");let sh=frogdrop_sched::shot(x,128);assert!(frogdrop_sched::check(&sh,sc).is_none());
  let(r,t)=euclid(x);let kind=sh.rec(162).kind;
  let(z,y,top,p,counter,is_done,label)=if kind==Kind::Ht {
   let j=1+sh.recs[..162].iter().filter(|r|matches!(r.kind,Kind::Hr|Kind::Ht|Kind::Dq)).count();
   let(z,y,top)=(t[j],r[j],r[j-1]);
   assert_eq!(z*top+t[j-1]*y,frogdrop_sched::p());
   let mut w=N::ZERO;for k in 1..j {w=(r[k-1]/r[k]).wrapping_mul(t[k]).wrapping_add(!w);}
   let hole=257-z.bit_len();let bound=258-z.bit_len();
   let raw:Vec<bool>=(0..259).map(|l|if l<bound {false}else{w.bit(258-l)}).collect();
   assert!(!raw[hole]);
   let p:Vec<bool>=raw.into_iter().enumerate().filter_map(|(i,v)|(i!=hole).then_some(v)).collect();
   active+=1;(z,y,top,p,0,false,"active_euclid_dy0")
  }else{
   assert_eq!(kind,Kind::Idle);assert!(sh.recs.len()>114);
   let n=r.len()-1;let idle=162-sh.recs.len();
   let skip=maps.iter().filter(|&&c|c>sh.recs.len()-1&&c<=161).count();
   let parity=(idle-skip)%2;
   let(z,y,top)=if parity==0 {(t[n-1],N::from(1u64),r[n-2])}else{(t[n-2],r[n-2],N::from(1u64))};
   let p:Vec<bool>=(0..258).map(|l|((l*17+done*11)%23)<11).collect();
   done+=1;(z,y,top,p,idle+1,true,"done_euclid_arbitrary_payload")
  };
  assert_eq!((z,y,top),(hex("z"),hex("y"),hex("top")));
  assert_eq!(counter,get(line,"counter").parse::<usize>().unwrap());assert_eq!(label,get(line,"kind"));
  let(zb,yb)=(z.bit_len(),y.bit_len());
  assert_eq!((zb,yb),(get(line,"zbits").parse().unwrap(),get(line,"ybits").parse().unwrap()));
  // Direct middle entry, AFTER stage2 exchange: E=bl(Y)-1, S=bl(Z)+bl(Y)-226,
  // disjoint bottom/top, Q suffix H/A and metadata roles clean, PH=1.
  assert!((226..=257).contains(&(zb+yb))&&yb>0&&yb<=cp.sy.1&&zb<=255);
  assert!(zb+top.bit_len()<=257&&counter<=cp.cntmax&&counter<128);
  assert!((cp.sz.0..=cp.sz.1).contains(&zb));
  let local_q=if is_done{N::ZERO}else{top/y};
  // Fixed division retains its existing public cap. The exact predictor also
  // checks source-specific approximation/correction, window and map premises.
  let local_supported=is_done||frogdrop_sched::c162_fixed_ht_predict(z,y,top);
  let exclusion=frogdrop_sched::predict_n_geometry(x,sc,24,24,30,83,128,31,257,super::midg::park_reserve(),0);
  let supported=exclusion.is_none()&&local_supported;
  let pbytes:Vec<u8>=p.iter().map(|&v|u8::from(v)).collect();
  println!("C162_FIXTURE shot={} kind={} x={:x} z={:x} y={:x} top={:x} counter={} dy=0 x_keccak={} counter_keccak={} dy_keccak={} P_keccak={} E={} S={} PH=1 H=0 A=0 roles=0 determinant_or_done_parity=true ring_disjoint=true local_q={:x} local_fixed_head=25 local_fixed_qb=23 local_supported={} predictor_exclusion={:?} supported={} classification=algebraic_boundary_probe traversal_image_proven=false carry_tail_global=UNCHECKED",
   i,label,x,z,y,top,counter,digest(format!("{:096x}",x).as_bytes()),digest(&(counter as u64).to_le_bytes()),
   digest(&[0u8;48]),digest(&pbytes),yb-1,zb+yb-226,local_q,local_supported,exclusion,supported);
  out.push(Fixture{x,z,y,top,p,done:is_done,counter,kind:label,supported});
 }
 assert_eq!((out.len(),active,done),(40,8,32));
 println!("C162_COVERAGE active={} done={} supported_active={} supported_done={} inactive_non_done=0 accepted_failure=0 nonzero_dy_active=0",active,done,
  out.iter().filter(|f|!f.done&&f.supported).count(),out.iter().filter(|f|f.done&&f.supported).count());out
}
fn put(w:&mut[u64],q:&[QubitId],shot:usize,v:N){for(i,q)in q.iter().enumerate(){if v.bit(i){w[q.0 as usize]|=1<<shot;}}}
fn input(r:&Rig,fs:&[Fixture],payload:bool)->Vec<u64>{
 let mut w=vec![0;r.b.width() as usize];
 for (i,f) in fs.iter().enumerate(){
  put(&mut w,&r.ring,i,f.z);for k in 0..f.top.bit_len(){if f.top.bit(k){w[r.ring[256-k].0 as usize]|=1<<i;}}
  put(&mut w,&r.q,i,f.y);put(&mut w,&r.q[121..128],i,N::from(f.counter as u64));
  put(&mut w,&r.meta.y,i,N::from((f.y.bit_len()-1)as u64));
  put(&mut w,&r.meta.sum,i,N::from((f.z.bit_len()+f.y.bit_len()-226)as u64));
  w[r.ph.0 as usize]|=1<<i;
  for(l,q)in r.p.iter().enumerate(){if if payload{f.p[l]}else{((l*13+i*7)%19)<9}{w[q.0 as usize]|=1<<i;}}
 }
 // Padding remains excluded by valid_mask before every count and witness cap.
 for i in fs.len()..64{for v in &mut w{*v|=(*v&1)<<i;}}
 assert_eq!(w[r.q[62].0 as usize],0);assert_eq!(w[r.q[74].0 as usize],0);w
}
fn fingerprint(ops:&[Op])->String{
 let mut h=sha3::Keccak256::new();for o in ops{Digest::update(&mut h,(o.kind as u32).to_le_bytes());
 for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{Digest::update(&mut h,v.to_le_bytes());}}
 format!("{:x}",h.finalize())
}
struct Replay {w:Vec<u64>,phase:u64,counts:BTreeMap<&'static str,C162Counts>,witnesses:Vec<C162Witness>,first_product:Option<(usize,u64)>}
impl Replay{
 fn bad(&self)->usize{self.counts.values().map(|c|c.bad_operations).sum()}
 fn bad_mask(&self)->u64{self.counts.values().fold(0,|v,c|v|c.bad_lane_mask)}
}
fn replay(r:&Rig,w:&[u64],fs:&[Fixture],label:&'static str,mask:u64)->Replay{
 c162_validate_shape(&r.b.ops,&r.b.c162_audit).expect("C162_UNKNOWN audit shape");
 let mut h=sha3::Shake256::default();Update::update(&mut h,b"c162-signed-native");let mut xof=h.finalize_xof();
 let mut s=Simulator::new(r.b.width()as usize,r.b.bits_end()as usize,&mut xof);s.qubits.clone_from_slice(w);
 s.c162_audit=r.b.c162_audit.clone();s.c162_valid_mask=mask;s.c162_direction=label;
 s.c162_select_mask=fs.iter().enumerate().fold(0,|m,(i,f)|m|if f.supported{1u64<<i}else{0});
 s.c162_fixture_ids=fs.iter().map(|f|format!("x={:x},kind={},counter={}",f.x,f.kind,f.counter)).collect();
 s.apply_iter(r.b.ops.iter());assert_eq!(s.c162_checked,r.b.c162_audit.len());
 println!("C162_REPLAY label={} ops={} T={} width={} op_hash={} metadata_hash={} input_hash={} output_hash={} checked={} families={:?} bad_witnesses={:?} phase={:#x} A={:#x} H={:#x} PH={:#x} spectator={:#x} measurement_stream=c162-signed-native sampled_sign_only=true",
  label,r.b.ops.len(),r.b.tof,r.b.width(),fingerprint(&r.b.ops),digest(format!("{:?}",r.b.c162_audit).as_bytes()),
  words_hash(w,mask),words_hash(&s.qubits,mask),s.c162_checked,s.c162_counts,s.c162_bad,s.phase&mask,
  s.qubits[r.q[74].0 as usize]&mask,s.qubits[r.q[62].0 as usize]&mask,s.qubits[r.ph.0 as usize]&mask,s.qubits[r.roles.prefix.0 as usize]&mask);
 Replay{w:s.qubits,phase:s.phase&mask,counts:s.c162_counts,witnesses:s.c162_bad,first_product:s.c162_first_product}
}
fn mismatch(a:&[u64],b:&[u64],mask:u64)->Vec<(usize,u64)>{
 a.iter().zip(b).enumerate().filter_map(|(i,(a,b))|{let d=(a^b)&mask;(d!=0).then_some((i,d))}).collect()
}
fn exits(r:&Rig,before:&[u64],after:&[u64],payload:bool,mask:u64)->Vec<(u64,u64)>{
 let mut ports:Vec<_>=r.meta.y.iter().chain(&r.meta.sum).chain(&r.q).copied().collect();
 ports.extend([r.roles.tag,r.roles.cut,r.roles.toggle,r.roles.prefix,r.ph]);
 if !payload {ports.extend(&r.p);}
 ports.into_iter().filter_map(|q|{let d=(after[q.0 as usize]^before[q.0 as usize])&mask;(d!=0).then_some((q.0,d))}).collect()
}
fn require_clean(result:&Replay,baseline:bool,label:&str,support:u64){
 if result.bad()!=0||result.phase!=0{
  println!("C162_STOP label={} candidate_status={} bad_operations={} phase={:#x} retained_bad_supported={:#x} first_witness={:?}",
   label,if baseline{"UNKNOWN_BASELINE_FAILURE"}else if (result.bad_mask()|result.phase)&support!=0{"SUPPORTED_COMPONENT_FAILURE"}else{"UNKNOWN_UNSUPPORTED_PROBE"},
   result.bad(),result.phase,result.bad_mask()&support,result.witnesses.first());
  panic!("C162 qualification stopped; see typed stop receipt");
 }
}

fn audit_controls(){
 // Same production checker/simulator, tiny operation lists. No caught panics.
 let hmr=Op{kind:K::Hmr,q_target:QubitId(2),c_target:BitId(3),c_condition:BitId(2),..Op::empty()};
 let cz=Op{kind:K::CZ,q_control1:QubitId(0),q_target:QubitId(1),c_condition:BitId(3),..Op::empty()};
 let ops=vec![Op{kind:K::PushCondition,c_condition:BitId(0),..Op::empty()},
  Op{kind:K::PushCondition,c_condition:BitId(1),..Op::empty()},hmr,cz,
  Op{kind:K::PopCondition,..Op::empty()},Op{kind:K::PopCondition,..Op::empty()}];
 let entries=vec![C162Audit{at:2,family:"AND_U_image",operation:hmr,
  relation:C162Relation::Product(QubitId(0),QubitId(1)),correction:vec![cz]}];
 c162_validate_shape(&ops,&entries).unwrap();
 let mut mask_cases=0;
 for (base0,base1,explicit,valid,held,want) in [
  (1u64,1u64,1u64,1u64,1u64,1usize),
  (0,1,1,1,1,0),(1,0,1,1,1,0),(1,1,0,1,1,0),(1,1,1,0,1,0),
  (1,1,1,1,0,0),(3,3,3,1,2,0),(3,3,3,1,3,1)] {
  let mut h=sha3::Shake256::default();Update::update(&mut h,b"c162-controls");let mut xof=h.finalize_xof();
  let mut sim=Simulator::new(3,4,&mut xof);sim.bits[0]=base0;sim.bits[1]=base1;sim.bits[2]=explicit;
  sim.qubits[2]=held;sim.c162_audit=entries.clone();sim.c162_valid_mask=valid;
  sim.apply_iter(ops.iter());let count=&sim.c162_counts["AND_U_image"];
  assert_eq!(count.bad_operations,want);assert_eq!(count.bad_lanes,want as u64);
  assert_eq!(sim.c162_checked,1);mask_cases+=1;
 }
 let mut shape_cases=0;
 for defect in 0..7{
  let mut es=entries.clone();let mut os=ops.clone();
  match defect {
   0=>es[0].at=1,
   1=>es.push(es[0].clone()),
   2=>os[2].kind=K::X,
   3=>os[2].q_target=QubitId(1),
   4=>os[2].c_target=BitId(0),
   5=>os[3].q_control1=QubitId(1),
   6=>es[0].correction.clear(),
   _=>unreachable!(),
  }
  assert!(c162_validate_shape(&os,&es).is_err());shape_cases+=1;
 }
 // AND_C target must be clean only on the live classical and fixture mask.
 let op=Op{kind:K::CCX,q_target:QubitId(2),q_control1:QubitId(0),q_control2:QubitId(1),c_condition:BitId(0),..Op::empty()};
 let entry=C162Audit{at:0,family:"AND_C_entry",operation:op,relation:C162Relation::Clean,correction:vec![]};
 let mut entry_cases=0;
 for (enable,valid,want) in [(1u64,1u64,1usize),(0,1,0),(1,0,0)]{
  let mut h=sha3::Shake256::default();let mut xof=h.finalize_xof();let mut sim=Simulator::new(3,1,&mut xof);
  sim.bits[0]=enable;sim.qubits[2]=1;sim.c162_valid_mask=valid;sim.c162_audit=vec![entry.clone()];
  c162_validate_shape(&[op],&sim.c162_audit).unwrap();sim.apply_iter([op].iter());
  assert_eq!(sim.c162_counts["AND_C_entry"].bad_operations,want);entry_cases+=1;
 }
 // Sixteen invalid-lane residuals must not consume the diagnostic buffer.
 // Then twenty real failures prove totals continue beyond the first16 witnesses.
 let mut b=B::new();b.c162_audit_enabled=true;let q=b.alloc_n(38);
 for &t in &q[2..]{b.and_u(q[0],q[1],t);}
 c162_validate_shape(&b.ops,&b.c162_audit).unwrap();
 let mut h=sha3::Shake256::default();let mut xof=h.finalize_xof();let mut sim=Simulator::new(38,10002,&mut xof);
 for w in &mut sim.qubits[2..18]{*w=2;}for w in &mut sim.qubits[18..]{*w=1;}
 sim.c162_audit=b.c162_audit.clone();sim.c162_valid_mask=1;sim.apply_iter(b.ops.iter());
 assert_eq!(sim.c162_counts["AND_U_image"].bad_operations,20);assert_eq!(sim.c162_counts["AND_U_image"].bad_lanes,20);
 assert_eq!(sim.c162_bad.len(),16);assert_eq!(sim.c162_bad[0].index,32);
 assert!(sim.c162_bad.iter().all(|w|w.executed_residual==1));
 println!("C162_CONTROLS mask_cases={} entry_cases={} index_negative_cases={} buffer_cases=2 status=PASS",mask_cases,entry_cases,shape_cases);
}

fn discriminator_controls(cp:&ColPar){
 use super::midg::direct_fixed_middle::c162_unpark_guard::{self as guard,Site,Reasons,Offender,C162EarlyAUnparkAlias as Witness};
 use std::any::Any;
 fn rejected(id:u8,payload:Box<dyn Any+Send>)->Box<dyn Any+Send>{
  match std::panic::catch_unwind(std::panic::AssertUnwindSafe(||guard::dispatch(id,payload))){
   Err(payload)=>payload,
   Ok(_)=>panic!("C162_UNKNOWN invalid discriminator control accepted"),
  }
 }
 let a=QubitId(257+74);let h=QubitId(257+62);
 let good=Witness {
  site:Site::UnparkBankDisjoint,profile:cp.clone(),audit_enabled:true,loan:true,mutant:1,
  observed:a,required:h,a_owner:a,sx2:a,x128:a,
  offenders:vec![Offender{owner:a,reasons:Reasons {
   dirty:false,reciprocal_r:true,ring:false,sx_indices:vec![2],raw_size:false,
   act:false,c0:false,x128:true,pzero:false,ph:false,sw:false,
  }}],
  unpark_bank:(63..=85).chain(96..=119).map(|i|QubitId(257+i)).collect(),
  comparator_bank:(96..=119).map(|i|QubitId(257+i)).collect(),
  recorded_gates:1,emitted_ops:0,
 };
 let accepted=guard::dispatch(1,Box::new(good.clone()));
 assert_eq!(accepted.site,Site::UnparkBankDisjoint);assert_eq!(accepted.offenders,good.offenders);
 assert_eq!((accepted.recorded_gates,accepted.emitted_ops),(1,0));
 let defects:Vec<(&str,fn(&mut Witness))>=vec![
  ("audit_disabled",|e|e.audit_enabled=false),
  ("loan_disabled",|e|e.loan=false),
  ("wrong_mutant",|e|e.mutant=2),
  ("wrong_column",|e|e.profile.col=161),
  ("wrong_k",|e|e.profile.k=1),
  ("wrong_sy",|e|e.profile.sy.1=63),
  ("wrong_profile_tail",|e|e.profile.tail=41),
  ("wrong_site",|e|e.site=Site::PayloadAlias),
  ("wrong_observed",|e|e.observed=QubitId(319)),
  ("wrong_required",|e|e.required=QubitId(320)),
  ("wrong_A",|e|e.a_owner=QubitId(330)),
  ("wrong_SX2",|e|e.sx2=QubitId(319)),
  ("wrong_x128",|e|e.x128=QubitId(319)),
  ("no_collision",|e|e.offenders.clear()),
  ("normal_H",|e|{e.observed=QubitId(319);e.sx2=QubitId(319);e.x128=QubitId(319);e.offenders[0].owner=QubitId(319);}),
  ("wrong_offender",|e|e.offenders[0].owner=QubitId(332)),
  ("extra_offender",|e|{let mut extra=e.offenders[0].clone();extra.owner=QubitId(332);e.offenders.push(extra);}),
  ("missing_R",|e|e.offenders[0].reasons.reciprocal_r=false),
  ("missing_SX",|e|e.offenders[0].reasons.sx_indices.clear()),
  ("extra_SX",|e|e.offenders[0].reasons.sx_indices.push(3)),
  ("missing_x128",|e|e.offenders[0].reasons.x128=false),
  ("extra_dirty",|e|e.offenders[0].reasons.dirty=true),
  ("extra_ring",|e|e.offenders[0].reasons.ring=true),
  ("extra_raw_size",|e|e.offenders[0].reasons.raw_size=true),
  ("extra_act",|e|e.offenders[0].reasons.act=true),
  ("extra_c0",|e|e.offenders[0].reasons.c0=true),
  ("extra_pzero",|e|e.offenders[0].reasons.pzero=true),
  ("extra_PH",|e|e.offenders[0].reasons.ph=true),
  ("extra_SW",|e|e.offenders[0].reasons.sw=true),
  ("wrong_unpark_size",|e|{e.unpark_bank.pop();}),
  ("wrong_comparator_size",|e|{e.comparator_bank.pop();}),
  ("H_in_unpark",|e|e.unpark_bank[0]=QubitId(319)),
  ("A_not_in_unpark",|e|{for q in &mut e.unpark_bank{if *q==QubitId(331){*q=QubitId(400);}}}),
  ("zero_recorded",|e|e.recorded_gates=0),
 ];
 let mut negative=0;
 for (name,alter) in defects {
  let mut bad=good.clone();alter(&mut bad);
  let payload=rejected(1,Box::new(bad));
  assert!(payload.is::<Witness>(),"discriminator changed rejected payload: {}",name);
  negative+=1;
 }
 for id in [0,2]{assert!(rejected(id,Box::new(good.clone())).is::<Witness>());negative+=1;}
 // The later payload alias type is a distinct, unaccepted site for this gate.
 let old=super::midg::direct_fixed_middle::C162EarlyAAlias {
  observed:a,required:h,recorded_gates:1,emitted_ops:0,
 };
 assert!(rejected(1,Box::new(old)).is::<super::midg::direct_fixed_middle::C162EarlyAAlias>());negative+=1;
 assert_eq!(*rejected(1,Box::new("unrelated panic")).downcast::<&str>().unwrap(),"unrelated panic");negative+=1;
 assert_eq!(*rejected(1,Box::new(String::from("unrelated owned panic"))).downcast::<String>().unwrap(),"unrelated owned panic");negative+=1;
 // This goes through the actual dispatcher and is observed by its outer catcher.
 #[derive(Debug)] struct Sentinel(u64);
 let sentinel=rejected(1,Box::new(Sentinel(0xc162_47_24)));
 assert_eq!(sentinel.downcast_ref::<Sentinel>().unwrap().0,0xc162_47_24);negative+=1;
 println!("C162_DISCRIMINATOR_CONTROLS positive_cases=1 negative_cases={} sentinel_propagation=PASS actual_dispatcher=true status=PASS",negative);
}

#[test]
fn component_contract(){
 println!("C162_START exact_target=point_add::tests_c162_native::component_contract candidate_status=UNKNOWN paired_checks=0");
 let(sc,cp,maps)=profile();audit_controls();discriminator_controls(&cp);let fs=fixtures(&sc,&cp,&maps);
 let mask=(1u64<<fs.len())-1;
 let support=fs.iter().enumerate().fold(0,|m,(i,f)|m|if f.supported{1u64<<i}else{0});
 let mut pairs=0usize;let mut costs=vec![];let mut payload_reference=None;let mut selected_offimage=None;
 let mut baseline_modes=Vec::new();
 // Fresh direct-parent forward and inverse are completed for BOTH payload
 // modes before emitting any candidate. Each inverse consumes its own image.
 for payload in [false,true]{
  let mut r=Rig::new();let before=input(&r,&fs,payload);let tape=r.tape(&cp,payload,Route::Parent);r.emit(&tape,false);
  let hash=fingerprint(&r.b.ops);let fcost=(r.b.tof,r.b.ops.len());
  println!("C162_BASELINE payload={} hash={} T={} N={} source_identity=preserved_run_direct separate_pristine_compile=false",payload,hash,fcost.0,fcost.1);
  if !payload{assert_eq!(hash,"daf903ce244e7b1f5376b3ce68911a4d3b354db5c992b016b50cf7523fd8f835","C162_UNKNOWN baseline operation drift");}
  let forward=replay(&r,&before,&fs,"parent_forward",mask);require_clean(&forward,true,"parent_forward",support);
  let exit_bad=exits(&r,&before,&forward.w,payload,mask);
  if !exit_bad.is_empty(){println!("C162_STOP candidate_status=UNKNOWN_BASELINE_EXIT payload={} wire_differences={:?}",payload,exit_bad);panic!("baseline exit");}
  // Independent DISABLED dispatch on identical ports; compare every operation
  // and audit record, rather than assigning the already computed parent hash.
  let mut disabled=Rig::new();let disabled_tape=disabled.tape(&cp,payload,Route::Disabled);disabled.emit(&disabled_tape,false);
  assert_eq!(r.b.ops,disabled.b.ops,"C162_UNKNOWN disabled dispatch operation identity");
  assert_eq!(r.b.c162_audit,disabled.b.c162_audit,"C162_UNKNOWN disabled audit identity");
  println!("C162_DISABLED_IDENTITY payload={} direct_parent_hash={} disabled_hash={} ops={} compared_all_fields=true",payload,hash,fingerprint(&disabled.b.ops),disabled.b.ops.len());
  r.emit(&tape,true);let inverse=replay(&r,&forward.w,&fs,"parent_inverse_on_forward_image",mask);
  require_clean(&inverse,true,"parent_inverse",support);
  let back_bad=mismatch(&inverse.w,&before,mask);
  if !back_bad.is_empty(){println!("C162_STOP candidate_status=UNKNOWN_BASELINE_INVERSE differences={:?}",back_bad);panic!("parent inverse");}
  costs.push((payload,"parent",fcost.0,fcost.1,r.b.tof,r.b.ops.len()));
  baseline_modes.push((payload,before,forward.w,inverse.w));
 }
 if !fs.iter().any(|f|f.supported&&!f.done)||!fs.iter().any(|f|f.supported&&f.done){
  println!("C162_STOP candidate_status=UNKNOWN_INSUFFICIENT_SUPPORTED_CASES paired_checks=0 support_mask={:#x}",support);
  panic!("nonzero supported active and DONE required");
 }
 for (payload,before,parent_forward,parent_inverse) in baseline_modes {
  let mut r=Rig::new();let tape=r.tape(&cp,payload,Route::Candidate);r.emit(&tape,false);
  let fcost=(r.b.tof,r.b.ops.len());let forward=replay(&r,&before,&fs,"candidate_forward",mask);
  require_clean(&forward,false,"candidate_forward",support);
  let bad=mismatch(&forward.w,&parent_forward,mask);let exit_bad=exits(&r,&before,&forward.w,payload,mask);
  if !bad.is_empty()||!exit_bad.is_empty(){
   let failed=bad.iter().fold(0,|m,(_,v)|m|v)|exit_bad.iter().fold(0,|m,(_,v)|m|v);
   println!("C162_STOP candidate_status={} payload={} direction=forward all_wire={:?} exit={:?}",if failed&support!=0{"SUPPORTED_COMPONENT_FAILURE"}else{"UNKNOWN_UNSUPPORTED_PROBE"},payload,bad,exit_bad);
   panic!("paired forward failure");
  }
  pairs+=fs.len();
  println!("C162_PAIR payload={} direction=forward checks={} supported_checks={} all_wires=660 signed_phase=0 metadata_counter_A_H_PH_spectator=PASS dirty_payload_checked={}",payload,fs.len(),support.count_ones(),!payload);
  if payload {payload_reference=Some(forward.w.clone());selected_offimage=forward.first_product;}
  r.emit(&tape,true);let inverse=replay(&r,&forward.w,&fs,"candidate_inverse_on_forward_image",mask);
  require_clean(&inverse,false,"candidate_inverse",support);
  let bad=mismatch(&inverse.w,&parent_inverse,mask);let back_bad=mismatch(&inverse.w,&before,mask);
  if !bad.is_empty()||!back_bad.is_empty(){
   let failed=bad.iter().chain(&back_bad).fold(0,|m,(_,v)|m|v);
   println!("C162_STOP candidate_status={} payload={} direction=inverse paired={:?} return={:?}",if failed&support!=0{"SUPPORTED_COMPONENT_FAILURE"}else{"UNKNOWN_UNSUPPORTED_PROBE"},payload,bad,back_bad);
   panic!("paired inverse failure");
  }
  pairs+=fs.len();assert!(pairs<=160);
  println!("C162_PAIR payload={} direction=inverse_on_own_forward_image checks={} supported_checks={} all_wires=660 signed_phase=0",payload,fs.len(),support.count_ones());
  costs.push((payload,"candidate",fcost.0,fcost.1,r.b.tof,r.b.ops.len()));
 }
 let expected=payload_reference.unwrap();let mut structural=0;let mut dynamic=0;
 for id in 1..=4u8{
  let name=match id{1=>"early_A",2=>"omitted_CX_sandwich",3=>"early_PH_compression",4=>"executed_offimage_AND_U",_=>unreachable!()};
  let trial=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||{
   super::midg::direct_fixed_middle::with_c162_mutant(id,||{
    let mut r=Rig::new();let before=input(&r,&fs,true);let tape=r.tape(&cp,true,Route::Candidate);r.emit(&tape,false);
    assert!(!r.b.ops.is_empty());let mut injected=None;
    if id==4{
     let (at,executing)=selected_offimage.expect("C162_UNKNOWN no executed AND_U for mutant");
     let entry=r.b.c162_audit.iter().find(|e|e.at==at).expect("selected product index").clone();
     assert!(matches!(&entry.relation,C162Relation::Product(..))&&executing&mask!=0);
     // This first selected product must be outside another correction recipe.
     // Otherwise an X there also alters that recipe; never silently rebind it.
     assert!(!r.b.c162_audit.iter().any(|e|e.at<at&&e.at+e.correction.len()>=at),"C162_UNKNOWN offimage index nested in another correction");
     r.b.ops.insert(at,Op{kind:K::X,q_target:entry.operation.q_target,c_condition:entry.operation.c_condition,..Op::empty()});
     for e in &mut r.b.c162_audit {if e.at>=at{e.at+=1;}}
     c162_validate_shape(&r.b.ops,&r.b.c162_audit).expect("C162_UNKNOWN transformed index shape");
     assert_ne!(executing&support,0,"C162_UNKNOWN no supported executed injection lane");
     injected=Some((at+1,executing&support));
    }
    // Unsupported probes never count as a caught dynamic mutation.
    let result=replay(&r,&before,&fs,"mutant_forward",support);
    let difference=mismatch(&result.w,&expected,support);
    let image_catch=result.bad()!=0;
    let wire_catch=!difference.is_empty();let sign_catch=result.phase!=0;
    if let Some((at,executing))=injected {
     let witness=result.witnesses.iter().find(|w|w.index==at&&w.family=="AND_U_image")
      .expect("C162_UNKNOWN injected executed-image witness absent");
     assert_ne!(witness.executed_residual&executing,0);
     println!("C162_MUTANT_INJECTION index={} original_executing={:#x} witness={:?}",at,executing,witness);
    }
    let reason=if image_catch{"AUDIT_PREMISE"}else if sign_catch{"SIGNED_PHASE"}else if wire_catch{"FULL_WIRE_PARITY"}else{"NOT_DETECTED"};
    println!("C162_MUTANT id={} name={} type=DYNAMIC reason={} replay_ops={} supported_fixtures={} bad_operations={} phase={:#x} differing_wires={} differences={:?} caught={}",
     id,name,reason,r.b.ops.len(),support.count_ones(),result.bad(),result.phase,difference.len(),difference,image_catch||sign_catch||wire_catch);
    assert!(image_catch||sign_catch||wire_catch,"C162_UNKNOWN mutant not discriminated");
   })
  }));
  match trial{
   Ok(())=>{assert_ne!(id,1,"early-A should reach its specific existing alias guard");dynamic+=1;},
   Err(payload)=>{
    use super::midg::direct_fixed_middle::c162_unpark_guard;
    if c162_unpark_guard::recognize(id,payload.as_ref()).is_none() {
     println!("C162_MUTANT id={} name={} type=UNEXPECTED_PANIC caught=false coverage=UNKNOWN",id,name);
    }
    let e=c162_unpark_guard::dispatch(id,payload);
    println!("C162_MUTANT id=1 name={} type=STRUCTURAL reason=UNPARK_BANK_DISJOINT witness={:?} recorded_gates={} emitted_ops={} replay_ops=0 fixtures=0 caught=true dynamic_detection=false",name,e,e.recorded_gates,e.emitted_ops);
    structural+=1;continue;
   }
  }
 }
 assert_eq!((pairs,structural,dynamic),(160,1,3));
 println!("C162_RESULT status=QUALIFIED_FOR_INDEPENDENT_COMPONENT_REVIEW paired_checks={} supported_paired_checks={} fixtures={} costs={:?} mutants_structural={} mutants_dynamic={} mutation_receipts=4 all_measurement_outcomes=OPEN global_carry_tail=OPEN non_done_inactive=0 active_nonzero_dy=0 accepted_failure=0 all65=OPEN Q659=OPEN submit=CLOSED",pairs,4*support.count_ones(),fs.len(),costs,structural,dynamic);
}
