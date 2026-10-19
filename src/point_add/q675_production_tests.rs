//! Bounded production-call census: one middle at a time, never a full operation Vec.
use super::{builder::B,frogdrop_col::ColScr};

#[derive(Clone,Debug,PartialEq,Eq)]
struct Tape { mode:usize, state:u64, bytes:usize }
impl sha3::digest::XofReader for Tape { fn read(&mut self,out:&mut[u8]) { for x in out {
 self.state^=self.state<<13;self.state^=self.state>>7;self.state^=self.state<<17;
 *x=match self.mode {0=>0,1=>255,_=>self.state as u8};self.bytes+=1;
}}}
// General finite instrument replay. Unlike the earlier adjacent-AND oracle, this
// accepts captured classical scopes; it is not an all-outcome support theorem.
fn instrument(ops:&[crate::circuit::Op],input:&[u64],mode:usize)->super::tests_frogdrop::Sim {
 use crate::circuit::{OperationType as K,NO_BIT};use sha3::digest::XofReader;
 let(_,nb,_,_)=crate::circuit::analyze_ops(ops.iter());let mut tape=Tape{mode,state:0x9e3779b97f4a7c15,bytes:0};let mut rng=tape.clone();
 let mut trusted=crate::sim::Simulator::new(input.len(),(nb as usize).max(1),&mut tape);
 trusted.qubits.copy_from_slice(input);
 for(i,v)in trusted.bits.iter_mut().enumerate(){*v=0xd1b54a32d192ed03u64.rotate_left(i as u32);}
 let mut bits=trusted.bits.clone();trusted.apply_iter(ops.iter());
 let mut q=input.to_vec();let mut phase=0;let mut t=0;let mut cliff=0;let mut frames=vec![u64::MAX];
 let trace=std::env::var("Q675_TRACE_FILE").ok();let marks=super::frogdrop_col::MARKS.with(|m|m.borrow().clone());let mut snapshots=Vec::new();
 for(i,o)in ops.iter().enumerate(){
  let outer=*frames.last().unwrap();let mask=outer & if o.c_condition==NO_BIT {u64::MAX}else{bits[o.c_condition.0 as usize]};
  let a=o.q_control1.0 as usize;let b=o.q_control2.0 as usize;let z=o.q_target.0 as usize;
  match o.kind {
   K::CCX|K::CCZ=>t+=mask.count_ones()as u64,
   K::CX|K::CZ|K::Swap|K::R|K::Hmr=>cliff+=mask.count_ones()as u64,_=>{}
  }
  match o.kind {
   K::X=>q[z]^=mask,K::CX=>q[z]^=mask&q[a],K::CCX=>q[z]^=mask&q[a]&q[b],
   K::Swap=>{let delta=mask&(q[a]^q[z]);q[a]^=delta;q[z]^=delta;},
   K::Z=>phase^=mask&q[z],K::CZ=>phase^=mask&q[a]&q[z],K::CCZ=>phase^=mask&q[a]&q[b]&q[z],K::Neg=>phase^=mask,
   K::Hmr|K::R=>{let mut buf=[0u8;8];rng.read(&mut buf);let m=u64::from_le_bytes(buf);phase^=mask&q[z]&m;q[z]&=!mask;
    if o.kind==K::Hmr {let c=&mut bits[o.c_target.0 as usize];*c=(*c&!mask)|(m&mask);}
   },
   K::BitInvert=>bits[o.c_target.0 as usize]^=mask,
   K::BitStore0=>bits[o.c_target.0 as usize]&=!mask,
   K::BitStore1=>bits[o.c_target.0 as usize]|=mask,
   K::PushCondition=>{assert_ne!(o.c_condition,NO_BIT);frames.push(mask);},
   K::PopCondition=>{assert!(frames.len()>1,"POP underflow at {i}");frames.pop();},
   K::Register|K::AppendToRegister|K::DebugPrint=>{}
  }
  if trace.is_some(){for &(_,stage)in marks.iter().filter(|&&(at,_)|at==i+1){snapshots.push(format!("{{\"op\":{},\"stage\":{stage},\"q\":{q:?},\"phase\":{phase},\"bit0\":{},\"captured_masks\":{frames:?}}}",i+1,bits[0]));}}
 }
 if let Some(path)=trace{use std::io::Write;let mut f=std::fs::OpenOptions::new().create_new(true).write(true).open(path).unwrap();write!(f,"[{}]",snapshots.join(",")).unwrap();}
 assert_eq!(frames.len(),1,"unbalanced instrument call");
 assert_eq!(trusted.qubits,q);assert_eq!(trusted.bits,bits);assert_eq!(trusted.phase,phase);
 assert_eq!((trusted.stats.toffoli_gates,trusted.stats.clifford_gates),(t,cliff));
 let result=super::tests_frogdrop::Sim{q:trusted.qubits,phase,tof:t};assert_eq!(tape,rng);result
}
// Execute the same balanced helper under two immutable captured frames whose
// source bits are then changed. Inactive quantum state is deliberately arbitrary.
fn guarded_kernel(ops:&[crate::circuit::Op],input:&[u64],want:&[u64],mode:usize){
 use crate::circuit::{Op,OperationType as K,BitId};
 let push=|id|{let mut o=Op::empty();o.kind=K::PushCondition;o.c_condition=BitId(id);o};
 let flip=|id|{let mut o=Op::empty();o.kind=K::BitInvert;o.c_target=BitId(id);o};
 let mut pop=Op::empty();pop.kind=K::PopCondition;
 let mut wrapped=vec![push(0),flip(0),push(1),flip(1)];wrapped.extend_from_slice(ops);wrapped.extend([pop,pop]);
 let a=0xd1b54a32d192ed03u64;let mask=a&a.rotate_left(1);
 let mut q=input.to_vec();let mut expected=want.to_vec();
 for(i,x)in q.iter_mut().enumerate(){let inactive=0x9e3779b97f4a7c15u64.rotate_left((i*7)as u32)&!mask;*x=(*x&mask)|inactive;expected[i]=(expected[i]&mask)|inactive;}
 let sim=instrument(&wrapped,&q,mode);assert_eq!(sim.q,expected,"captured helper mode={mode}");assert_eq!(sim.phase,0);
}

#[test]
fn q675_production_middle_bounded_census(){
 use std::io::Write;super::bake_knobs();
 let path=std::env::var("Q675_PRODUCTION_CENSUS").expect("fresh bounded census output");
 let mut f=std::fs::OpenOptions::new().create_new(true).write(true).open(path).unwrap();
 let mut rows=0;let mut maxops=0;
 for n in[259,258]{for payload in[false,true]{
  let(mut b,mut fd,pool,dirty)=super::q675_layout_tests::ports(n);
  let(mut cols,_,_)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
  for cp in &mut cols {cp.n=n;cp.h=n-257;
   let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
   let pl=super::pointadd_frogdrop::pl_col(&dirty,&fd,&pool);let mut stage=2;let mut last_ops=0;let mut last_t=0;
   super::midg::middle(&mut b,&fd,cp,&sc,payload.then_some(&pl),&[],&mut |b|{
    stage+=1;assert!(b.ops.len()<8_000_000,"bounded one-column operation cap");
    writeln!(f,"{{\"n\":{n},\"col\":{},\"payload\":{payload},\"stage\":{stage},\"ops\":{},\"T\":{},\"Q\":{},\"hr\":{},\"ht\":{},\"tt\":{},\"dl\":{},\"dq\":{},\"sw\":{},\"dn\":{}}}",cp.col,b.ops.len()-last_ops,b.tof-last_t,b.width(),cp.hr,cp.ht,cp.tt,cp.dl,cp.dq,cp.sw,cp.dn).unwrap();
    last_ops=b.ops.len();last_t=b.tof;true
   });
   assert_eq!(b.width(),(n+417)as u64);maxops=maxops.max(b.ops.len());
   eprintln!("Q675_PRODUCTION_COL n={n} payload={payload} col={} ops={} T={} Q={}",cp.col,b.ops.len(),b.tof,b.width());
   b.ops.clear();b.tof=0;std::mem::swap(&mut fd.sy,&mut fd.sx);rows+=1;
  }
 }}
 assert_eq!(rows,812);eprintln!("Q675_PRODUCTION_MIDDLE_CENSUS rows={rows} max_column_ops={maxops} all_structural_assertions=true arithmetic_unvalidated=true");
}

#[test]
fn q675_production_full_column_bounded_census(){
 use std::io::Write;super::bake_knobs();
 let path=std::env::var("Q675_FULL_COLUMN_CENSUS").expect("fresh full-column census output");
 let mut f=std::fs::OpenOptions::new().create_new(true).write(true).open(path).unwrap();
 let mut rows=0;let mut maxops=0;
 let active_only=std::env::var("Q675_CENSUS_RING").ok().map(|s|{assert_eq!(s,"258");true}).unwrap_or(false);
 for n in [259,258].into_iter().filter(|&n|!active_only||n==258) {for payload in [false,true] {
  let(mut b,mut fd,pool,dirty)=super::q675_layout_tests::ports(n);
  let(mut cols,mut b0,mut last)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
  for cp in &mut cols {cp.n=n;cp.h=n-257;
   let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
   let pl=super::pointadd_frogdrop::pl_col(&dirty,&fd,&pool);
   super::frogdrop_col::column_pl(&mut b,&mut fd,cp,&sc,payload.then_some(&pl));
   assert!(b.ops.len()<12_000_000,"bounded full-column operation cap");
   for o in &b.ops {o.validate();}
   assert_eq!(b.width(),(n+417)as u64);maxops=maxops.max(b.ops.len());
   writeln!(f,"{{\"n\":{n},\"col\":{},\"payload\":{payload},\"ops\":{},\"T\":{},\"Q\":{}}}",cp.col,b.ops.len(),b.tof,b.width()).unwrap();
   eprintln!("Q675_FULL_COLUMN n={n} payload={payload} col={} ops={} T={} Q={}",cp.col,b.ops.len(),b.tof,b.width());
   b.ops.clear();b.tof=0;rows+=1;
  }
  for cp in b0.iter_mut().chain(std::iter::once(&mut last)){cp.n=n;cp.h=n-257;}
  let pl=super::pointadd_frogdrop::pl_col(&dirty,&fd,&pool);
  let carve=|sx:&[crate::circuit::QubitId]|ColScr::carve(&pool,sx,&dirty,last.kp,last.qb,last.tail);
  super::frogdrop_col::traversal_end_pl(&mut b,&mut fd,b0.as_ref(),&last,&carve,payload.then_some(&pl));
  assert!(b.ops.len()<12_000_000,"bounded endpoint operation cap");for o in &b.ops{o.validate();}
  assert_eq!(b.width(),(n+417)as u64);maxops=maxops.max(b.ops.len());
  writeln!(f,"{{\"n\":{n},\"col\":\"endpoint\",\"payload\":{payload},\"ops\":{},\"T\":{},\"Q\":{}}}",b.ops.len(),b.tof,b.width()).unwrap();
  eprintln!("Q675_FULL_COLUMN_ENDPOINT n={n} payload={payload} ops={} T={} Q={}",b.ops.len(),b.tof,b.width());rows+=1;
 }}
 assert_eq!(rows,if active_only{408}else{816});eprintln!("Q675_FULL_COLUMN_CENSUS rows={rows} max_segment_ops={maxops} arithmetic_unvalidated=true deferred_pairing_not_exercised=true");
}

#[test]
fn q675_production_instrument_captured_guards(){
 use crate::circuit::{Op,OperationType as K,BitId,QubitId};
 let op=|kind|{let mut o=Op::empty();o.kind=kind;o};
 let mut push=op(K::PushCondition);push.c_condition=BitId(0);
 let mut flip=op(K::BitInvert);flip.c_target=BitId(0);
 let mut x=op(K::X);x.q_target=QubitId(0);
 let mut h=op(K::Hmr);h.q_target=QubitId(1);h.c_target=BitId(0);
 let mut repair=op(K::Z);repair.q_target=QubitId(0);repair.c_condition=BitId(0);
 let ops=[push,flip,x,op(K::PopCondition),h,repair];
 let g=0xd1b54a32d192ed03;let input=[0,g];
 for mode in 0..3 {let result=instrument(&ops,&input,mode);assert_eq!(result.q,[g,0]);assert_eq!(result.phase,0);}
 let bad=instrument(&ops[..ops.len()-1],&input,1);assert_eq!(bad.q,[g,0]);assert_eq!(bad.phase,g);
 // A dynamic reread after the classical invert would suppress the X entirely.
 assert_ne!(g,0);eprintln!("Q675_GENERAL_INSTRUMENT_GUARDS_PASS tapes=3 stale_bit0=true immutable_capture=true missing_repair_detected=true dynamic_reread_negative=true");
}

#[test]
fn q675_production_full_columns_fixed_trajectories(){
 use super::frogdrop_sched::{N,Kind,p,shot,L0};
 fn put(q:&mut[u64],bits:&[crate::circuit::QubitId],lane:usize,v:N){assert!(v.bit_len()<=bits.len());for(i,b)in bits.iter().enumerate(){if v.bit(i){q[b.0 as usize]|=1<<lane;}}}
 super::bake_knobs();
 let xs=["49176424196341559882282835066500465739964486710944627237969621863740844055600","7801068174888942215453276072244625408945163364090463797248400728130351100631","3221298318250477569130864633716084673551962514470203759046027749693133723655","26519862389053564010481439055492936948247804999014740043933127691834765424534","22209487291262036614423068735401345736403532185831517457072025085196704704075","4108011952227412774928094428100183838836827860897645614755958029386194827498","19916315704823571356936714846135094793442177208650530057314963199793923003014","48993842489728369977411078580230959863956286310235992247568368632942001659173"];
 let mut data=vec![];
 let xs:Vec<_>=xs.iter().flat_map(|x|{let x=N::from_str_radix(x,10).unwrap();[x,p()-x]}).collect();
 for x in xs {let mut r=vec![p(),x];let mut t=vec![N::ZERO,N::from(1)];while !r.last().unwrap().is_zero(){let n=r.len();let q=r[n-2]/r[n-1];r.push(r[n-2]-q*r[n-1]);t.push(t[n-2]+q*t[n-1]);}data.push((r,t,shot(x,L0)));}
 let(mut b,mut fd,pool,dirty)=super::q675_layout_tests::ports(258);
 let(mut cols,mut b0,mut last)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
 let mut states=vec![vec![0u64;675];3];for(mode,state)in states.iter_mut().enumerate(){for(i,&d)in dirty.iter().enumerate(){state[d.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left((i+mode*7)as u32);}for lane in 0..64{put(state,&fd.ring,lane,data[lane%data.len()].0[1]);state[fd.ring[257].0 as usize]|=1<<lane;state[fd.sy[0].0 as usize]|=1<<lane;}}
 let mut j=vec![1usize;data.len()];let mut ph=vec![false;data.len()];let mut checked=0;
 for cp in &mut cols {cp.n=258;cp.h=1;let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
  super::frogdrop_col::column_pl(&mut b,&mut fd,cp,&sc,None);assert!(b.ops.len()<12_000_000);for o in &b.ops{o.validate();}
  let mut logical=vec![];
  for(f,(r,t,sh))in data.iter().enumerate(){let c=cp.col;let nn=r.len()-1;
   let (bot,qv,top,cnt)=if c<sh.recs.len(){match sh.recs[c].kind{
    Kind::Hr=>{j[f]+=1;(r[j[f]],t[j[f]-1],t[j[f]],0)},
    Kind::Ht=>{j[f]+=1;(t[j[f]],r[j[f]-1],r[j[f]],if j[f]==nn-1{1}else{0})},
    Kind::Sw=>{ph[f]=true;(t[j[f]],r[j[f]],r[j[f]-1],0)},
    Kind::Dl=>{ph[f]=true;(t[j[f]],r[j[f]],r[j[f]+1],0)},
    Kind::Dq=>{j[f]+=1;(t[j[f]],r[j[f]-1],r[j[f]],if j[f]==nn-1{1}else{0})},Kind::Idle=>unreachable!()
   }}else{let idle=c+1-sh.recs.len();let skipped=super::frogdrop_col::map_ctrl_skipped_by(sh.recs.len()-1,c);if(idle-skipped)%2==0{(t[nn-1],r[nn-2],N::from(1),idle+1)}else{(t[nn-2],N::from(1),r[nn-2],idle+1)}};
   logical.push((bot,qv,top,cnt));
  }
  for mode in 0..3{let sim=instrument(&b.ops,&states[mode],mode);let mut want=vec![0u64;675];for &d in &dirty{want[d.0 as usize]=states[mode][d.0 as usize];}
   let top_ports:Vec<_>=fd.ring.iter().rev().copied().collect();for lane in 0..64{let f=lane%data.len();let(bot,qv,top,cnt)=logical[f];assert!(bot.bit_len()+top.bit_len()<=258);put(&mut want,&fd.ring,lane,bot);put(&mut want,&top_ports,lane,top);put(&mut want,&fd.q,lane,qv);put(&mut want,&fd.cnt,lane,N::from(cnt));put(&mut want,&fd.sy,lane,N::from(top.bit_len()));if ph[f]{want[fd.ph.0 as usize]|=1<<lane;}if cp.col<data[f].2.recs.len()&&data[f].2.recs[cp.col].kind==Kind::Dl{want[sc.sw.0 as usize]|=1<<lane;}}
   let diff:Vec<_>=sim.q.iter().zip(&want).enumerate().filter(|(_, (a,b))|a!=b).map(|(i,(a,b))|(i,a^b)).collect();
   assert!(diff.is_empty()&&sim.phase==0,"full column {} tape={mode} logical={logical:?} diff={diff:?} phase={:x}",cp.col,sim.phase);states[mode]=sim.q;checked+=data.len();
  }
  eprintln!("Q675_FULL_FIXED_COL col={} ops={} full_quantum_phase=true stale_receipts=true",cp.col,b.ops.len());b.ops.clear();b.tof=0;
 }
 for cp in b0.iter_mut().chain(std::iter::once(&mut last)){cp.n=258;cp.h=1;}
 let carve=|sx:&[crate::circuit::QubitId]|ColScr::carve(&pool,sx,&dirty,last.kp,last.qb,last.tail);
 super::frogdrop_col::traversal_end_pl(&mut b,&mut fd,b0.as_ref(),&last,&carve,None);assert!(b.ops.len()<12_000_000);
 for mode in 0..3 {let sim=instrument(&b.ops,&states[mode],mode);let mut want=vec![0u64;675];for &d in &dirty{want[d.0 as usize]=states[mode][d.0 as usize];}
  for lane in 0..64{let(r,t,sh)=&data[lane%data.len()];let nn=r.len()-1;put(&mut want,&fd.ring,lane,t[nn-1]);want[fd.ring[257].0 as usize]|=1<<lane;put(&mut want,&fd.q[..26],lane,r[nn-2]);put(&mut want,&fd.cnt,lane,N::from(204-sh.recs.len()));want[fd.sy[0].0 as usize]|=1<<lane;want[fd.ph.0 as usize]|=1<<lane;}
  assert_eq!(sim.q,want,"endpoint mode={mode}");assert_eq!(sim.phase,0);checked+=data.len();
 }
 eprintln!("Q675_FULL_FIXED_PASS meaningful_lanes={checked} columns=203 endpoint=true fixed_inputs=16 deterministic_complements=true tapes=3 no_payload=true column_private_bits_reinitialized=true deferred_pairing_not_exercised=true");
}

#[test]
fn q675_production_middle_exact_euclid_states(){
 use super::frogdrop_sched::{N,Kind,p,shot,L0};
 fn put(q:&mut[u64],bits:&[crate::circuit::QubitId],lane:usize,v:N){assert!(v.bit_len()<=bits.len());for(i,b)in bits.iter().enumerate(){if v.bit(i){q[b.0 as usize]|=1<<lane;}}}
 super::bake_knobs();
 let xs=["49176424196341559882282835066500465739964486710944627237969621863740844055600","7801068174888942215453276072244625408945163364090463797248400728130351100631","3221298318250477569130864633716084673551962514470203759046027749693133723655","26519862389053564010481439055492936948247804999014740043933127691834765424534","22209487291262036614423068735401345736403532185831517457072025085196704704075","4108011952227412774928094428100183838836827860897645614755958029386194827498","19916315704823571356936714846135094793442177208650530057314963199793923003014","48993842489728369977411078580230959863956286310235992247568368632942001659173"];
 let mut rows:Vec<Vec<(N,N,N,N,bool,bool,usize)>>=vec![vec![];203];let mut excluded=0;
 for (fixture,hx) in xs.iter().enumerate(){let xr=N::from_str_radix(hx,10).unwrap();let mut r=vec![p(),xr];let mut t=vec![N::ZERO,N::from(1)];
  while !r.last().unwrap().is_zero(){let n=r.len();let q=r[n-2]/r[n-1];r.push(r[n-2]-q*r[n-1]);t.push(t[n-2]+q*t[n-1]);}
  let sh=shot(xr,L0);let mut j=1;
  for (col,rr) in sh.recs.iter().enumerate(){if col>=203{break;}
   let (z,y,x,want,ph,sw,step)=match rr.kind{
    Kind::Hr|Kind::Dl=>(r[j],t[j],t[j-1],t[j+1],false,false,true),
    Kind::Ht=>(t[j],r[j],r[j-1],r[j+1],true,false,true),
    Kind::Sw=>(r[j],t[j],t[j-1],t[j-1],false,true,false),
    Kind::Dq=>(t[j],r[j],r[j+1],r[j+1],true,false,false),
    Kind::Idle=>unreachable!()};
   if matches!(rr.kind,Kind::Hr|Kind::Ht|Kind::Dq){j+=1;}
   // Independently classify the inherited reciprocal interval, never search new fixtures.
   if step {let sz=z.bit_len();assert!(sz>=24);let s=sz-24;let h=(z>>s)|N::from(1);let f=((N::from(1)<<(256-s))-N::from(1))/h;
    let u=257usize.saturating_sub(sz+26);let theta=((f>>u)<<u)|((N::from(1)<<u)-N::from(1));let image=if ph{x}else{want};
    if image>theta||image+y<=theta{eprintln!("Q675_INHERITED_INTERVAL_EXCLUDED fixture={fixture} col={col} ph={ph}");excluded+=1;continue;}
   }
   rows[col].push((z,y,x,want,ph,sw,fixture));
  }
 }
 let(mut b,mut fd,pool,dirty)=super::q675_layout_tests::ports(258);
 let(mut cols,_,_)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
 let mut checked=0;let mut colcount=0;
 for cp in &mut cols {cp.n=258;cp.h=1;
  if rows[cp.col].is_empty(){std::mem::swap(&mut fd.sy,&mut fd.sx);continue;}
  let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
  super::midg::middle(&mut b,&fd,cp,&sc,None,&[],&mut |b|{assert!(b.ops.len()<8_000_000);true});
  let top:Vec<_>=fd.ring.iter().rev().copied().collect();
  for tape in 0..3 {let mut input=vec![0u64;675];let mut want=vec![0u64;675];
   for(i,&q)in dirty.iter().enumerate(){input[q.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left((i+tape*7)as u32);}
   want.clone_from(&input);
   for(lane,&(z,y,x,w,ph,sw,_))in rows[cp.col].iter().enumerate(){assert!(z.bit_len()+x.bit_len()<=258);assert!(z.bit_len()+w.bit_len()<=258);
    assert!((cp.sz.0..=cp.sz.1).contains(&z.bit_len()));assert!((cp.sy.0..=cp.sy.1).contains(&y.bit_len()));
    for a in [&mut input,&mut want]{put(a,&fd.ring,lane,z);put(a,&fd.q,lane,y);put(a,&fd.sy,lane,N::from(y.bit_len()));put(a,&sc.sz,lane,N::from(z.bit_len()));if ph{a[fd.ph.0 as usize]|=1<<lane;}if sw{a[sc.sw.0 as usize]|=1<<lane;}}
    put(&mut input,&top,lane,x);put(&mut want,&top,lane,w);
   }
   // Repeat named fixtures through all64 packed lanes; no unsupported zero-size padding shots.
   let n=rows[cp.col].len();for a in [&mut input,&mut want]{for word in a {*word &= (1u64<<n)-1;for lane in n..64{*word|=((*word>>(lane%n))&1)<<lane;}}}
   let sim=instrument(&b.ops,&input,tape);
   assert_eq!(sim.phase,0,"middle phase col={} tape={tape}",cp.col);
   let diff:Vec<_>=sim.q.iter().zip(&want).enumerate().filter(|(_, (a,b))|a!=b).map(|(i,(a,b))|(i,a^b)).collect();
   assert!(diff.is_empty(),"middle col={} tape={tape} rows={:?} diff={diff:?}",cp.col,rows[cp.col]);checked+=n;
  }
  eprintln!("Q675_MIDDLE_EUCLID_COL col={} rows={} ops={} Q={} full_instrument=true",cp.col,rows[cp.col].len(),b.ops.len(),b.width());
  b.ops.clear();b.tof=0;std::mem::swap(&mut fd.sy,&mut fd.sx);colcount+=1;
 }
 eprintln!("Q675_MIDDLE_EUCLID_PASS columns={colcount} meaningful_lanes={checked} inherited_interval_exclusions={excluded} fixed_inputs=8 full_traversal_not_executed=true");
}

#[test]
fn q675_production_middle_exact_euclid_payload_states(){
 use super::frogdrop_sched::{N,Kind,p,shot,L0};
 fn put(q:&mut[u64],bits:&[crate::circuit::QubitId],lane:usize,v:N){assert!(v.bit_len()<=bits.len());for(i,b)in bits.iter().enumerate(){if v.bit(i){q[b.0 as usize]|=1<<lane;}}}
 super::bake_knobs();
 let xs=["49176424196341559882282835066500465739964486710944627237969621863740844055600","7801068174888942215453276072244625408945163364090463797248400728130351100631","3221298318250477569130864633716084673551962514470203759046027749693133723655","26519862389053564010481439055492936948247804999014740043933127691834765424534","22209487291262036614423068735401345736403532185831517457072025085196704704075","4108011952227412774928094428100183838836827860897645614755958029386194827498","19916315704823571356936714846135094793442177208650530057314963199793923003014","48993842489728369977411078580230959863956286310235992247568368632942001659173"];
 let mut rows:Vec<Vec<(N,N,N,N,bool,bool,usize)>>=vec![vec![];203];let mut excluded=0;
 for (fixture,hx) in xs.iter().enumerate(){let xr=N::from_str_radix(hx,10).unwrap();let mut r=vec![p(),xr];let mut t=vec![N::ZERO,N::from(1)];
  while !r.last().unwrap().is_zero(){let n=r.len();let q=r[n-2]/r[n-1];r.push(r[n-2]-q*r[n-1]);t.push(t[n-2]+q*t[n-1]);}
  let sh=shot(xr,L0);let mut j=1;
  for (col,rr) in sh.recs.iter().enumerate(){if col>=203{break;}
   let (z,y,x,want,ph,sw,step)=match rr.kind{
    Kind::Hr|Kind::Dl=>(r[j],t[j],t[j-1],t[j+1],false,false,true),
    Kind::Ht=>(t[j],r[j],r[j-1],r[j+1],true,false,true),
    Kind::Sw=>(r[j],t[j],t[j-1],t[j-1],false,true,false),
    Kind::Dq=>(t[j],r[j],r[j+1],r[j+1],true,false,false),
    Kind::Idle=>unreachable!()};
   if matches!(rr.kind,Kind::Hr|Kind::Ht|Kind::Dq){j+=1;}
   // Independently classify the inherited reciprocal interval, never search new fixtures.
   if step {let sz=z.bit_len();assert!(sz>=24);let s=sz-24;let h=(z>>s)|N::from(1);let f=((N::from(1)<<(256-s))-N::from(1))/h;
    let u=257usize.saturating_sub(sz+26);let theta=((f>>u)<<u)|((N::from(1)<<u)-N::from(1));let image=if ph{x}else{want};
    if image>theta||image+y<=theta{eprintln!("Q675_INHERITED_INTERVAL_EXCLUDED fixture={fixture} col={col} ph={ph}");excluded+=1;continue;}
   }
   rows[col].push((z,y,x,want,ph,sw,fixture));
  }
 }
 let(mut b,mut fd,pool,dirty)=super::q675_layout_tests::ports(258);
 let(mut cols,_,_)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
 let mut checked=0;let mut colcount=0;
 for cp in &mut cols {cp.n=258;cp.h=1;
  if rows[cp.col].is_empty(){std::mem::swap(&mut fd.sy,&mut fd.sx);continue;}
  let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
  let pl=super::pointadd_frogdrop::pl_col(&dirty,&fd,&pool);
  super::midg::middle(&mut b,&fd,cp,&sc,Some(&pl),&[],&mut |b|{assert!(b.ops.len()<8_000_000);true});
  let top:Vec<_>=fd.ring.iter().rev().copied().collect();
  for tape in 0..3 {let mut input=vec![0u64;675];let mut want=vec![0u64;675];
   for(i,&q)in dirty.iter().enumerate(){input[q.0 as usize]=0x9e3779b97f4a7c15u64.rotate_left((i+tape*7)as u32);}
   want.clone_from(&input);
   for(lane,&(z,y,x,w,ph,sw,_))in rows[cp.col].iter().enumerate(){assert!(z.bit_len()+x.bit_len()<=258);assert!(z.bit_len()+w.bit_len()<=258);
    assert!((cp.sz.0..=cp.sz.1).contains(&z.bit_len()));assert!((cp.sy.0..=cp.sy.1).contains(&y.bit_len()));
    for a in [&mut input,&mut want]{put(a,&fd.ring,lane,z);put(a,&fd.q,lane,y);put(a,&fd.sy,lane,N::from(y.bit_len()));put(a,&sc.sz,lane,N::from(z.bit_len()));if ph{a[fd.ph.0 as usize]|=1<<lane;}if sw{a[sc.sw.0 as usize]|=1<<lane;}}
    put(&mut input,&top,lane,x);put(&mut want,&top,lane,w);
   }
   let fullw:Vec<_>=pl.p.iter().rev().copied().collect();
   for(lane,&(z,y,x,w,ph,_sw,_))in rows[cp.col].iter().enumerate(){
    let oldw=fullw.iter().enumerate().fold(N::ZERO,|v,(i,q)|v|(N::from((input[q.0 as usize]>>lane)&1)<<i));let mut result=oldw;
    if !ph&&w>x {let q=(w-x)/y;let width=259-if cp.dl{cp.dlr.min(129)}else{129};let m=(N::from(1)<<width)-N::from(1);result=(oldw&!m)|((oldw+q*y)&m);}
    if ph&&x>w {let q=(x-w)/y;for kb in 0..23{if q.bit(kb){assert!(z.bit_len()+y.bit_len()+kb<=257);let sh=((usize::BITS-1-(kb+1).leading_zeros())as usize).min(4);let width=259-(y.bit_len()>>sh)*(1<<sh);let m=(N::from(1)<<width)-N::from(1);result=(result&!m)|((result+(z<<kb))&m);}}}
    for(i,q)in fullw.iter().enumerate(){let m=1u64<<lane;want[q.0 as usize]=(want[q.0 as usize]&!m)|((result.bit(i)as u64)<<lane);}
   }
   // Repeat named fixtures through all64 packed lanes; no unsupported zero-size padding shots.
   let n=rows[cp.col].len();for a in [&mut input,&mut want]{for word in a {*word &= (1u64<<n)-1;for lane in n..64{*word|=((*word>>(lane%n))&1)<<lane;}}}
   let sim=instrument(&b.ops,&input,tape);
   assert_eq!(sim.phase,0,"middle phase col={} tape={tape}",cp.col);
   let diff:Vec<_>=sim.q.iter().zip(&want).enumerate().filter(|(_, (a,b))|a!=b).map(|(i,(a,b))|(i,a^b)).collect();
   assert!(diff.is_empty(),"middle col={} tape={tape} rows={:?} diff={diff:?}",cp.col,rows[cp.col]);checked+=n;
  }
  eprintln!("Q675_MIDDLE_PAYLOAD_EUCLID_COL col={} rows={} ops={} Q={} full_instrument=true",cp.col,rows[cp.col].len(),b.ops.len(),b.width());
  b.ops.clear();b.tof=0;std::mem::swap(&mut fd.sy,&mut fd.sx);colcount+=1;
 }
 eprintln!("Q675_MIDDLE_PAYLOAD_EUCLID_PASS columns={colcount} meaningful_lanes={checked} inherited_interval_exclusions={excluded} fixed_inputs=8 full_traversal_not_executed=true");
}

#[test]
fn q675_production_full_columns_payload_trajectories(){
 use super::frogdrop_sched::{N,Kind,p,shot,L0};
 fn put(q:&mut[u64],bits:&[crate::circuit::QubitId],lane:usize,v:N){assert!(v.bit_len()<=bits.len());for(i,b)in bits.iter().enumerate(){if v.bit(i){q[b.0 as usize]|=1<<lane;}}}
 super::bake_knobs();
 let xs=["49176424196341559882282835066500465739964486710944627237969621863740844055600","7801068174888942215453276072244625408945163364090463797248400728130351100631","3221298318250477569130864633716084673551962514470203759046027749693133723655","26519862389053564010481439055492936948247804999014740043933127691834765424534","22209487291262036614423068735401345736403532185831517457072025085196704704075","4108011952227412774928094428100183838836827860897645614755958029386194827498","19916315704823571356936714846135094793442177208650530057314963199793923003014","48993842489728369977411078580230959863956286310235992247568368632942001659173"];
 let mut data=vec![];
 let xs:Vec<_>=xs.iter().flat_map(|x|{let x=N::from_str_radix(x,10).unwrap();[x,p()-x]}).collect();
 for x in xs {let mut r=vec![p(),x];let mut t=vec![N::ZERO,N::from(1)];while !r.last().unwrap().is_zero(){let n=r.len();let q=r[n-2]/r[n-1];r.push(r[n-2]-q*r[n-1]);t.push(t[n-2]+q*t[n-1]);}data.push((r,t,shot(x,L0)));}
 let n:usize=std::env::var("Q675_TEST_RING").ok().map(|x|x.parse().unwrap()).unwrap_or(258);assert!([258,259].contains(&n));
 let(mut b,mut fd,pool,dirty)=super::q675_layout_tests::ports(n);
 let(mut cols,mut b0,mut last)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
 let mut states=vec![vec![0u64;n+417];3];for(mode,state)in states.iter_mut().enumerate(){let _=mode;for lane in 0..64{put(state,&dirty[..256],lane,(data[lane%data.len()].0[1]*N::from(7)+N::from(13))%p());put(state,&fd.ring,lane,data[lane%data.len()].0[1]);state[fd.ring[n-1].0 as usize]|=1<<lane;state[fd.sy[0].0 as usize]|=1<<lane;}}
 let mut j=vec![1usize;data.len()];let mut ph=vec![false;data.len()];let mut checked=0;
 for cp in &mut cols {cp.n=n;cp.h=n-257;let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
  super::frogdrop_col::MARKS.with(|m|m.borrow_mut().clear());
  let plc=super::pointadd_frogdrop::pl_col(&dirty,&fd,&pool);super::frogdrop_col::column_pl(&mut b,&mut fd,cp,&sc,Some(&plc));assert!(b.ops.len()<12_000_000);for o in &b.ops{o.validate();}
  let mut logical=vec![];
  for(f,(r,t,sh))in data.iter().enumerate(){let c=cp.col;let nn=r.len()-1;
   let (bot,qv,top,cnt)=if c<sh.recs.len(){match sh.recs[c].kind{
    Kind::Hr=>{j[f]+=1;(r[j[f]],t[j[f]-1],t[j[f]],0)},
    Kind::Ht=>{j[f]+=1;(t[j[f]],r[j[f]-1],r[j[f]],if j[f]==nn-1{1}else{0})},
    Kind::Sw=>{ph[f]=true;(t[j[f]],r[j[f]],r[j[f]-1],0)},
    Kind::Dl=>{ph[f]=true;(t[j[f]],r[j[f]],r[j[f]+1],0)},
    Kind::Dq=>{j[f]+=1;(t[j[f]],r[j[f]-1],r[j[f]],if j[f]==nn-1{1}else{0})},Kind::Idle=>unreachable!()
   }}else{let idle=c+1-sh.recs.len();let skipped=super::frogdrop_col::map_ctrl_skipped_by(sh.recs.len()-1,c);if(idle-skipped)%2==0{(t[nn-1],r[nn-2],N::from(1),idle+1)}else{(t[nn-2],N::from(1),r[nn-2],idle+1)}};
   logical.push((bot,qv,top,cnt));
  }
  for mode in 0..3{let trace_mode=std::env::var("Q675_TRACE_MODE").ok().map(|s|s.parse::<usize>().unwrap()).unwrap_or(0);let trace_lo=std::env::var("Q675_TRACE_LO").ok().map(|s|s.parse::<usize>().unwrap()).unwrap_or(60);let trace_hi=std::env::var("Q675_TRACE_HI").ok().map(|s|s.parse::<usize>().unwrap()).unwrap_or(64);if mode==trace_mode&&(trace_lo..=trace_hi).contains(&cp.col){if let Ok(dir)=std::env::var("Q675_BOUNDARY_DIR"){
    use std::io::Write;let path=std::path::Path::new(&dir);std::fs::create_dir_all(path).unwrap();
    let ids=|v:&[crate::circuit::QubitId]|v.iter().map(|q|q.0).collect::<Vec<_>>();
    let mut out=std::fs::OpenOptions::new().create_new(true).write(true).open(path.join(format!("n{n}-col{}-boundary.json",cp.col))).unwrap();
    write!(out,"{{\"n\":{n},\"col\":{},\"input\":{:?},\"ring\":{:?},\"qports\":{:?},\"sy_after_names\":{:?},\"sx_after_names\":{:?},\"pool\":{:?},\"payload\":{:?},\"marks\":{:?}}}",cp.col,states[mode],ids(&fd.ring),ids(&fd.q),ids(&fd.sy),ids(&fd.sx),ids(&pool),ids(&dirty),super::frogdrop_col::MARKS.with(|m|m.borrow().iter().map(|&(a,b)|[a,b]).collect::<Vec<_>>())).unwrap();
    std::env::set_var("Q675_TRACE_FILE",path.join(format!("n{n}-col{}-trace.json",cp.col)));
   }}let sim=instrument(&b.ops,&states[mode],mode);std::env::remove_var("Q675_TRACE_FILE");let mut want=vec![0u64;n+417];for &d in &dirty{want[d.0 as usize]=sim.q[d.0 as usize];}
   let top_ports:Vec<_>=fd.ring.iter().rev().copied().collect();for lane in 0..64{let f=lane%data.len();let(bot,qv,top,cnt)=logical[f];assert!(bot.bit_len()+top.bit_len()<=n);put(&mut want,&fd.ring,lane,bot);put(&mut want,&top_ports,lane,top);put(&mut want,&fd.q,lane,qv);put(&mut want,&fd.cnt,lane,N::from(cnt));put(&mut want,&fd.sy,lane,N::from(top.bit_len()));if ph[f]{want[fd.ph.0 as usize]|=1<<lane;}if cp.col<data[f].2.recs.len()&&data[f].2.recs[cp.col].kind==Kind::Dl{want[sc.sw.0 as usize]|=1<<lane;}}
   let diff:Vec<_>=sim.q.iter().zip(&want).enumerate().filter(|(_, (a,b))|a!=b).map(|(i,(a,b))|(i,a^b)).collect();
   assert!(diff.is_empty()&&sim.phase==0,"full column {} tape={mode} logical={logical:?} diff={diff:?} phase={:x}",cp.col,sim.phase);states[mode]=sim.q;checked+=data.len();
  }
  eprintln!("Q675_FULL_PAYLOAD_COL col={} ops={} walk_scratch_phase=true intermediate_payload_unchecked=true stale_receipts=true",cp.col,b.ops.len());b.ops.clear();b.tof=0;
 }
 for cp in b0.iter_mut().chain(std::iter::once(&mut last)){cp.n=n;cp.h=n-257;}
 let carve=|sx:&[crate::circuit::QubitId]|ColScr::carve(&pool,sx,&dirty,last.kp,last.qb,last.tail);
 let plc=super::pointadd_frogdrop::pl_col(&dirty,&fd,&pool);super::frogdrop_col::traversal_end_pl(&mut b,&mut fd,b0.as_ref(),&last,&carve,Some(&plc));assert!(b.ops.len()<12_000_000);
 for mode in 0..3 {let sim=instrument(&b.ops,&states[mode],mode);let mut want=vec![0u64;n+417];for &d in &dirty{want[d.0 as usize]=sim.q[d.0 as usize];}
  for lane in 0..64{let(r,t,sh)=&data[lane%data.len()];let nn=r.len()-1;let mut d=(r[1]*N::from(7)+N::from(13))%p();let mut w=N::ZERO;for j in 1..nn {let e=d/r[j];d-=e*r[j];let post=w.wrapping_add(e*t[j]);w=(r[j-1]/r[j]*t[j]).wrapping_add(!post);}assert_eq!(d,N::ZERO);let u=w.wrapping_add(N::from(1)<<257);for(l,q)in dirty.iter().enumerate(){let v=l>=1&&u.bit(258-l);let bit=1u64<<lane;want[q.0 as usize]=(want[q.0 as usize]&!bit)|((v as u64)<<lane);}put(&mut want,&fd.ring,lane,t[nn-1]);want[fd.ring[n-1].0 as usize]|=1<<lane;put(&mut want,&fd.q[..26],lane,r[nn-2]);put(&mut want,&fd.cnt,lane,N::from(204-sh.recs.len()));want[fd.sy[0].0 as usize]|=1<<lane;want[fd.ph.0 as usize]|=1<<lane;}
  assert_eq!(sim.q,want,"endpoint mode={mode}");assert_eq!(sim.phase,0);checked+=data.len();
 }
 eprintln!("Q675_FULL_PAYLOAD_PASS meaningful_lanes={checked} columns=203 endpoint=true fixed_inputs=16 deterministic_complements=true tapes=3 payload_endpoint_integer_oracle=true payload_intermediate_not_asserted=true column_private_bits_reinitialized=true deferred_pairing_not_exercised=true");
}


#[test]
fn q675_digit_boundary_probe(){
 super::bake_knobs();let n:usize=std::env::var("Q675_TEST_RING").unwrap().parse().unwrap();assert!([258,259].contains(&n));
 let text=std::fs::read_to_string(std::env::var("Q675_DIGIT_INPUT").unwrap()).unwrap();
 let input:Vec<u64>=text.split(',').map(|s|s.trim().parse().unwrap()).collect();assert_eq!(input.len(),n+417);
 let(mut b,fd,pool,dirty)=super::q675_layout_tests::ports(n);
 let(mut cols,_,_)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
 let cp=&mut cols[64];cp.n=n;cp.h=n-257;
 let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
 let pl=super::pointadd_frogdrop::pl_col(&dirty,&fd,&pool);
 super::frogdrop_col::MARKS.with(|m|m.borrow_mut().clear());super::payload::col_digit(&mut b,&fd,cp,&sc,&pl);
 for o in &b.ops{o.validate();}let sim=instrument(&b.ops,&input,0);
 eprintln!("Q675_DIGIT_PROBE n={n} ops={} Q={} phase={} oracle_all_channels=true q={:?}",b.ops.len(),b.width(),sim.phase,sim.q);
}

#[test]
fn q675_true_carry_witness_all_channels(){
 use crate::circuit::QubitId;
 let mut cases=0usize;
 for len in 1..=5 {for controlled in [false,true]{
  let mut b=B::new();let q=b.alloc_n(48);let t=&q[0..len];let s=&q[5..5+len];let reg=&q[10..13];
  let (e,w,c0,act,sign)=(q[13],q[14],q[15],q[16],q[17]);let pre=&q[18..20];let tmp=&q[20..21];let dirty=&q[21..];
  let mut gate=|_b:&mut B,i:Option<usize>|if controlled{i.map(|_|e)}else{None};
  super::payload::ripple_true_carry(&mut b,t,s,c0,reg,0,len-1,&[(act,false),(sign,true)],e,w,pre,tmp,dirty,&mut gate);
  for o in &b.ops{o.validate();}
  let count=(1usize<<(2*len+3))*len;
  for start in (0..count).step_by(64){let mut input=vec![0u64;48];let mut want=input.clone();
   for lane in 0..64{let code=(start+lane)%count;let v=code%len;let data=code/len;let mask=(1usize<<len)-1;
    let a=data&mask;let z=(data>>len)&mask;let ein=(data>>(2*len))&1;let active=(data>>(2*len+1))&1;let sg=(data>>(2*len+2))&1;
    let upto=(1usize<<(v+1))-1;let carry=(((upto-(a&upto))+(z&upto))>>(v+1))&1;
    let eo=ein^(active&(1-sg)&(1-carry));let ao=if controlled&&eo==1{a.wrapping_sub(z)&mask}else{a};
    let mut put=|ids:&[QubitId],value:usize|{for(i,p)in ids.iter().enumerate(){input[p.0 as usize]|=(((value>>i)&1)as u64)<<lane;}};
    put(t,a);put(s,z);put(reg,v);put(&[e],ein);put(&[act],active);put(&[sign],sg);
    for &d in dirty{input[d.0 as usize]|=(((code.wrapping_mul(0x9e3779b1)>>(d.0 as usize%29))&1)as u64)<<lane;}
    for i in 0..48{want[i]|=input[i]&(1u64<<lane);}
    for(i,p)in t.iter().enumerate(){want[p.0 as usize]=(want[p.0 as usize]&!(1u64<<lane))|((((ao>>i)&1)as u64)<<lane);}
    want[e.0 as usize]=(want[e.0 as usize]&!(1u64<<lane))|((eo as u64)<<lane);
   }
   for mode in 0..3{let sim=instrument(&b.ops,&input,mode);assert_eq!(sim.q,want,"len={len} ctrl={controlled} start={start} mode={mode}");assert_eq!(sim.phase,0);guarded_kernel(&b.ops,&input,&want,mode);cases+=count.saturating_sub(start).min(64);}
  }
 }}eprintln!("Q675_TRUE_CARRY_PASS meaningful_lanes={cases} lengths=1..5 modes=3 source_target_arbitrary=true witness_zero_restored=true");
}

#[test]
fn q675_boundary_carry_all_channels(){
 let mut cases=0usize;
 for len in 2..=6{for stride in [1,2,4]{let choices=(len-1)/stride+1;let mut b=B::new();let q=b.alloc_n(48);let t=&q[..len];let s=&q[6..6+len];let sy=&q[12..15];let(c,g,c0)=(q[15],q[16],q[17]);
  super::midg::trans_carry_boundary(&mut b,t,s,len-1,stride,c,sy,0,choices-1,g,c0,&q[18..20],&q[20..21],&q[21..]);
  for o in &b.ops{o.validate();}let count=(1usize<<(2*len+1))*choices;
  for start in (0..count).step_by(64){let mut input=vec![0u64;48];let mut want=input.clone();
   for lane in 0..64{let code=(start+lane)%count;let v=code%choices;let z=code/choices;let mask=(1usize<<len)-1;let a=z&mask;let src=(z>>len)&mask;let active=(z>>(2*len))&1;let boundary=len-1-stride*v;let low=(1usize<<boundary)-1;let win=(1usize<<(boundary+1))-1;let out=if active==1{(a&!win)|((a+(src&low))&win)}else{a};
    for(i,&p)in t.iter().enumerate(){input[p.0 as usize]|=(((a>>i)&1)as u64)<<lane;want[p.0 as usize]|=(((out>>i)&1)as u64)<<lane;}
    for(i,&p)in s.iter().enumerate(){input[p.0 as usize]|=(((src>>i)&1)as u64)<<lane;want[p.0 as usize]|=(((src>>i)&1)as u64)<<lane;}
    for(i,&p)in sy.iter().enumerate(){input[p.0 as usize]|=(((v>>i)&1)as u64)<<lane;want[p.0 as usize]|=(((v>>i)&1)as u64)<<lane;}
    input[c.0 as usize]|=(active as u64)<<lane;want[c.0 as usize]|=(active as u64)<<lane;
    for p in &q[21..]{let bit=(((code.wrapping_mul(0x9e3779b1)>>(p.0 as usize%29))&1)as u64)<<lane;input[p.0 as usize]|=bit;want[p.0 as usize]|=bit;}
   }
   for mode in 0..3{let sim=instrument(&b.ops,&input,mode);assert_eq!(sim.q,want,"len={len} start={start} mode={mode}");assert_eq!(sim.phase,0);guarded_kernel(&b.ops,&input,&want,mode);cases+=count.saturating_sub(start).min(64);}
  }
 }}eprintln!("Q675_BOUNDARY_CARRY_PASS meaningful_lanes={cases} lengths=2..6 modes=3 arbitrary_foreign_source=true source_and_clean_scratch_restored=true");
}

#[test]
fn q675_carry_repairs_negative_controls(){
 let mut b=B::new();let q=b.alloc_n(48);let(t,s)=(&q[..3],&q[5..8]);let reg=&q[10..13];let(e,w,c0,act,sign)=(q[13],q[14],q[15],q[16],q[17]);
 let mut gate=|_b:&mut B,_i:Option<usize>|None;
 super::payload::ripple_true_carry(&mut b,t,s,c0,reg,0,2,&[(act,false),(sign,true)],e,w,&q[18..20],&q[20..21],&q[21..],&mut gate);
 let mut input=vec![0u64;48];input[s[2].0 as usize]=u64::MAX;input[reg[0].0 as usize]=u64::MAX;input[act.0 as usize]=u64::MAX;
 let good=instrument(&b.ops,&input,1);assert_eq!(good.q[e.0 as usize],u64::MAX);assert_eq!(good.q[w.0 as usize],0);assert_eq!(good.phase,0);
 let mut dirty=input.clone();dirty[w.0 as usize]=u64::MAX;let bad=instrument(&b.ops,&dirty,1);assert_eq!(bad.q[e.0 as usize],0);assert_ne!(bad.q,good.q);
 let mut old=B::new();old.alloc_n(48);let mut mid=|b:&mut B|{b.x(e);b.cx(s[1],e);};
 super::payload::ripple(&mut old,t,s,c0,true,&mut mid,&mut gate);let contaminated=instrument(&old.ops,&input,1);assert_eq!(contaminated.q[e.0 as usize],0);
 let mut cut=B::new();cut.alloc_n(48);let mut no_mid=|_b:&mut B|{};let mut short=|_b:&mut B,i:Option<usize>|i.filter(|&i|i<2).map(|_|act);
 super::payload::ripple(&mut cut,t,s,c0,false,&mut no_mid,&mut short);
 let mut a=vec![0u64;48];a[t[0].0 as usize]=u64::MAX;a[t[1].0 as usize]=u64::MAX;a[s[0].0 as usize]=u64::MAX;a[act.0 as usize]=u64::MAX;
 let omitted=instrument(&cut.ops,&a,1);assert_eq!(omitted.q[t[2].0 as usize],0);assert_eq!(omitted.q[s[0].0 as usize],u64::MAX);
 eprintln!("Q675_REPAIR_NEGATIVES_PASS dirty_witness=64 omitted_next_source_correction=64 omitted_boundary_carry=64");
}
