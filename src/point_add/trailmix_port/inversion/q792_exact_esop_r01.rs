//! Exact ESOP candidates, with a measured T-primary acceptance guard.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::{Op,OperationType as K};
struct Plan{n:usize,k:usize,truth:u64,cubes:&'static[(usize,usize)]}
include!("q792_exact_esop_plans_r01.rs");
thread_local!{
 static DISABLED:std::cell::Cell<bool>=const{std::cell::Cell::new(false)};
 static CONTEXT:std::cell::Cell<Option<(usize,usize)>>=const{std::cell::Cell::new(None)};
}
pub(super) fn without<T>(f:impl FnOnce()->T)->T{DISABLED.with(|d|{let old=d.replace(true);let result=f();d.set(old);result})}
pub(super) fn context(value:Option<(usize,usize)>){CONTEXT.with(|c|c.set(value));}
pub(super) fn capture_calls()->bool{std::env::var_os("FOLD20_EXACT_ESOP_CALL_CENSUS").is_some()&&!DISABLED.with(|d|d.get())}
pub(super) fn record_call(n:usize,k:usize,truth:&[bool],old:&[Op],new:&[Op]){
 let before=scored(old);let after=scored(new);if before==after{return;}
 let t=truth.iter().enumerate().fold(0u64,|a,(i,&v)|a|((v as u64)<<i));let(block,j)=CONTEXT.with(|c|c.get()).unwrap_or((usize::MAX,usize::MAX));
 eprintln!("EXACT_ESOP_FINAL_CALL block={block} j={j} n={n} k={k} truth={t:016x} old_T={} old_ops={} new_T={} new_ops={}",before.0,before.1,after.0,after.1);
}
fn scored(ops:&[Op])->(usize,usize){(ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len())}
fn emit(c:&mut Circuit,word:&[&QReg],prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg],p:&Plan){
 let mut cubes=p.cubes.to_vec();let mut frame=0usize;
 for &(q,v)in prefix{if !v{c.x(q);}}
 while !cubes.is_empty(){
  let pick=(0..cubes.len()).min_by_key(|&i|{let(m,v)=cubes[i];((frame^(m^v))&m).count_ones()}).unwrap();
  let(m,v)=cubes.remove(pick);let toggles=(frame^(m^v))&m;for(i,q)in word.iter().enumerate(){if toggles>>i&1!=0{c.x(q);}}frame^=toggles;
  let mut cs:Vec<_>=prefix.iter().map(|&(q,_)|(q,true)).collect();cs.extend(word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(_,q)|(*q,true)));
  super::length_recompute::mixed_mcx(c,&cs,out,dirty);
 }
 for(i,q)in word.iter().enumerate(){if frame>>i&1!=0{c.x(q);}}
 for &(q,v)in prefix.iter().rev(){if !v{c.x(q);}}
}
pub(super) fn improve(c:&mut Circuit,word:&[&QReg],truth:&[bool],prefix:&[(&QReg,bool)],out:&QReg,dirty:&[QReg],at:usize){
 if word.len()!=5||!prefix.is_empty()||dirty.len()<3||super::q792_passive_r01::active()||super::q792_rank4_lower_r01::capture_active(){return;}
 if DISABLED.with(|d|d.get())||std::env::var_os("FOLD20_EXACT_ESOP_DISABLED").is_some(){return;}
 let t=truth.iter().enumerate().fold(0u64,|a,(i,&v)|a|((v as u64)<<i));
 if ![0x080f0c0f,0x30003000,0x80f0c0f0].contains(&t){return;}
 let mut ids:Vec<_>=word.iter().map(|q|q.id()).chain(std::iter::once(out.id())).chain(dirty.iter().map(QReg::id)).collect();ids.sort_unstable();if ids.windows(2).any(|p|p[0]==p[1]){return;}
 let p=PLANS.iter().find(|p|p.n==5&&p.k==0&&p.truth==t).unwrap();
 for x in 0..32{assert_eq!(p.cubes.iter().fold(false,|a,&(m,v)|a^(x&m==v)),truth[x]);}
 let old=c.b.ops.split_off(at);let before=scored(&old);let owned=c.b.next_qubit;
 emit(c,word,prefix,out,dirty,p);assert_eq!(owned,c.b.next_qubit);let after=scored(&c.b.ops[at..]);
 // These three prequalified functions use at most two extra op records for
 // each removed Toffoli. The whole-count diagnostic enforces the independent
 // 125 GB (56-byte records) payload cap before qualification.
 if after.0>=before.0||after.1>before.1+2{c.b.ops.truncate(at);c.b.ops.extend(old);return;}
 if std::env::var_os("FOLD20_EXACT_ESOP_CAPTURE").is_some(){
  use sha3::{Digest,Sha3_256};
  static COUNTS:std::sync::OnceLock<std::sync::Mutex<std::collections::BTreeMap<u64,u64>>>=std::sync::OnceLock::new();
  let mut counts=COUNTS.get_or_init(||std::sync::Mutex::new(std::collections::BTreeMap::new())).lock().unwrap();let count=counts.entry(t).or_default();*count+=1;
  if *count==1{
   let wire:Vec<_>=word.iter().copied().chain(std::iter::once(out)).chain(dirty.iter()).map(QReg::id).collect();
   let encode=|ops:&[Op]|ops.iter().map(|op|{let q=|id:u64|wire.iter().position(|&w|w as u64==id).map(|i|i as i32).unwrap_or(-1);format!("{}:{},{},{}",op.kind as u32,q(op.q_control2.0),q(op.q_control1.0),q(op.q_target.0))}).collect::<Vec<_>>().join(";");
   let hash=format!("{:x}",Sha3_256::digest(truth.iter().map(|&v|u8::from(v)).collect::<Vec<_>>()));
   eprintln!("EXACT_ESOP_BIND truth={t:016x} truth_vector_sha3_256={hash} old={} new={}",encode(&old),encode(&c.b.ops[at..]));
  }
  eprintln!("EXACT_ESOP_ACCEPT truth={t:016x} occurrence={count} old_T={} old_ops={} new_T={} new_ops={}",before.0,before.1,after.0,after.1);
 }
}
pub fn run(){
 use crate::sim::Simulator;use sha3::digest::XofReader;
 struct Fixed;impl XofReader for Fixed{fn read(&mut self,b:&mut[u8]){b.fill(0x5b);}}
 fn rnd(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
 let mut wins=0;let mut lanes=0usize;
 for p in PLANS{
  for x in 0..1usize<<p.n{assert_eq!(p.cubes.iter().fold(false,|a,&(m,v)|a^(x&m==v)),p.truth>>x&1!=0);}
  let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;
  let w=c.alloc_qreg_bits("exact.word",p.n);let pre=c.alloc_qreg_bits("exact.prefix",p.k);let out=c.alloc_qreg("exact.target");let dirty=c.alloc_qreg_bits("exact.dirty",p.n+p.k+2);let owned=c.b.next_qubit;
  let word:Vec<_>=w.iter().collect();let prefix:Vec<_>=pre.iter().enumerate().map(|(i,q)|(q,i%3!=1)).collect();
  std::env::set_var("FOLD20_EXACT_ESOP_DISABLED","1");super::q792_fold20_r01::table(&mut c,&word,(0..1<<p.n).map(|x|p.truth>>x&1!=0).collect(),&prefix,&out,&dirty);std::env::remove_var("FOLD20_EXACT_ESOP_DISABLED");let baseline=c.b.ops.split_off(0);
  emit(&mut c,&word,&prefix,&out,&dirty,p);assert_eq!(c.b.next_qubit,owned);let ops=c.into_builder().ops;
  let before=scored(&baseline);let after=scored(&ops);let win=after.0<before.0&&after.1<=before.1+2;wins+=usize::from(win);
  eprintln!("EXACT_ESOP_COMPARE n={} k={} truth={:016x} old_T={} old_ops={} new_T={} new_ops={} win={win}",p.n,p.k,p.truth,before.0,before.1,after.0,after.1);
  assert!(ops.iter().all(|op|matches!(op.kind,K::X|K::CX|K::CCX)));
  let full_dirty=p.n==5&&p.k==0&&[0x080f0c0f,0x30003000,0x80f0c0f0].contains(&p.truth);
  for pattern in 0..2{for first in (0..1usize<<(p.n+p.k+1+if full_dirty{dirty.len()}else{0})).step_by(64){
   let mut seed=0xe79220260912u64^p.truth^(first as u64)^((pattern as u64)<<32);
   let mut initial:Vec<_>=(0..owned).map(|_|rnd(&mut seed)).collect();for(i,q)in w.iter().chain(&pre).chain(std::iter::once(&out)).chain(dirty.iter().take(if full_dirty{dirty.len()}else{0})).enumerate(){initial[q.id()as usize]=(0..64).fold(0,|a,l|a|((((first+l)>>i&1)as u64)<<l));}
   let mut expected=initial.clone();for l in 0..64{if p.truth>>((first+l)%(1<<p.n))&1!=0&&prefix.iter().all(|&(q,v)|(initial[q.id()as usize]>>l&1!=0)==v){expected[out.id()as usize]^=1u64<<l;}}
   let mut f=Fixed;let mut sim=Simulator::new(owned as usize,0,&mut f);sim.qubits.copy_from_slice(&initial);sim.apply_iter(ops.iter());assert_eq!(sim.qubits,expected);assert_eq!(sim.phase,0);sim.apply_iter(ops.iter().rev());assert_eq!(sim.qubits,initial);assert_eq!(sim.phase,0);lanes+=64;
  }}
 }
 eprintln!("EXACT_ESOP_NATIVE_PASS plans={} lanes={lanes} wins={wins} all_word_prefix_targets=true arbitrary_dirty=true winners_all_dirty_states=true phase=0 inverse=true no_extra_qubits=true",PLANS.len());
}
