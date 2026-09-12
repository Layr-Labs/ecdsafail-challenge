//! Per-builder lossless template storage; the public operation ABI is unchanged.
use crate::circuit::{Op,OperationType as K,QubitId,NO_QUBIT,NO_BIT,NO_REG};
use std::collections::HashMap;
#[derive(Default)]
pub(crate) struct Cache {
 environment:Vec<(std::ffi::OsString,std::ffi::OsString)>,
 blocks:HashMap<(usize,usize),(usize,Vec<u8>)>,
 pub(crate) hits:usize,
 pub(crate) misses:usize,
}
impl Cache {
 pub(crate) fn synchronize(&mut self){let mut now:Vec<_>=std::env::vars_os().collect();now.sort();if now!=self.environment{self.blocks.clear();self.environment=now;}}
 pub(crate) fn get(&mut self,key:(usize,usize))->Option<Vec<Op>>{
  match self.blocks.get(&key){Some((n,bytes))=>{self.hits+=1;Some(decode(*n,bytes))},None=>{self.misses+=1;None}}
 }
 pub(crate) fn insert(&mut self,key:(usize,usize),ops:&[Op]){assert!(self.blocks.insert(key,(ops.len(),encode(ops))).is_none());}
 pub(crate) fn bytes(&self)->usize{self.blocks.values().map(|(_,v)|v.len()).sum()}
}
fn encode(ops:&[Op])->Vec<u8>{
 let mut raw=Vec::with_capacity(ops.len()*7);
 for o in ops{
  o.validate();assert!(matches!(o.kind,K::X|K::CX|K::CCX));assert_eq!(o.c_condition,NO_BIT);assert_eq!(o.c_target,NO_BIT);assert_eq!(o.r_target,NO_REG);
  raw.push(o.kind as u8);
  for q in [o.q_control2,o.q_control1,o.q_target]{let id=if q==NO_QUBIT{u16::MAX}else{let id=u16::try_from(q.0).unwrap();assert_ne!(id,u16::MAX);id};raw.extend_from_slice(&id.to_le_bytes());}
 }
 zstd::bulk::compress(&raw,1).unwrap()
}
fn decode(n:usize,bytes:&[u8])->Vec<Op>{
 let raw=zstd::bulk::decompress(bytes,n.checked_mul(7).unwrap()).unwrap();assert_eq!(raw.len(),n*7);let mut out=Vec::with_capacity(n);
 for r in raw.chunks_exact(7){
  let mut o=Op::empty();o.kind=match r[0]{6=>K::X,8=>K::CX,13=>K::CCX,_=>panic!("bad internal NCT template")};
  for(i,q)in[&mut o.q_control2,&mut o.q_control1,&mut o.q_target].into_iter().enumerate(){let id=u16::from_le_bytes(r[1+2*i..3+2*i].try_into().unwrap());*q=if id==u16::MAX{NO_QUBIT}else{QubitId(id as u64)};}
  o.validate();out.push(o);
 }
 out
}
pub(crate) fn check(){
 let mut ops=Vec::new();for t in 0..565{for n in 0..3{let mut o=Op::empty();o.kind=[K::X,K::CX,K::CCX][n];o.q_target=QubitId(t);if n>0{o.q_control1=QubitId((t+1)%565);}if n>1{o.q_control2=QubitId((t+257)%565);}o.validate();ops.push(o);}}
 let bytes=encode(&ops);assert_eq!(decode(ops.len(),&bytes),ops);
 let mut cache=Cache::default();cache.synchronize();assert!(cache.get((3,2)).is_none());cache.insert((3,2),&ops);assert_eq!(cache.get((3,2)).unwrap(),ops);
 cache.synchronize();assert_eq!(cache.get((3,2)).unwrap(),ops);std::env::set_var("Q793_RUNTIME_TEST_CACHE_KEY","changed");cache.synchronize();assert!(cache.get((3,2)).is_none());std::env::remove_var("Q793_RUNTIME_TEST_CACHE_KEY");
 let mut kinds=[0;18];for o in &ops{kinds[o.kind as usize]+=1;}
 for count_only in [false,true]{for capture in [false,true]{for hashed in [false,true]{
  let mut a=super::B::new();let mut b=super::B::new();a.count_only=count_only;b.count_only=count_only;
  if capture{a.count_only_capture_stack.push(Vec::new());b.count_only_capture_stack.push(Vec::new());}
  if hashed{a.fiat_hash=Some(Default::default());b.fiat_hash=Some(Default::default());}
  for _ in 0..7{for &o in &ops{a.push_op(o);}b.append_nct_template(&ops,&kinds);}
  assert_eq!(a.ops,b.ops);assert_eq!(a.counted_ops,b.counted_ops);assert_eq!(a.counted_kind_ops,b.counted_kind_ops);assert_eq!(a.counted_phase_kind_ops,b.counted_phase_kind_ops);assert_eq!(a.count_only_capture_stack,b.count_only_capture_stack);
  if hashed{use sha3::digest::{ExtendableOutput,XofReader};let mut ax=[0;64];let mut bx=[0;64];a.fiat_hash.take().unwrap().finalize_xof().read(&mut ax);b.fiat_hash.take().unwrap().finalize_xof().read(&mut bx);assert_eq!(ax,bx);}
 }}}
 eprintln!("Q793_RUNTIME_R01_PASS codec_ops={} codec_bytes={} builder_cases=8 copies=7 fields/counters/capture/hash_equal=true cache_invalidation=true",ops.len(),bytes.len());
}
