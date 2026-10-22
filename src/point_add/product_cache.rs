// Generated from the fixed product-cache plan. Do not edit.
// Retained-AND caching idea credited to MonitSharma.
use crate::circuit::{Op,OperationType as K};
use sha3::{Digest,Sha3_256};
const TABLE:&str=include_str!("product_cache.txt");
fn row(v:&[u64])->Op{
 assert_eq!(v.len(),7);let mut o=Op::empty();
 o.kind=match v[0]{0=>K::Neg,1=>K::Register,2=>K::AppendToRegister,3=>K::BitInvert,4=>K::BitStore0,5=>K::BitStore1,6=>K::X,7=>K::Z,8=>K::CX,9=>K::CZ,10=>K::Swap,11=>K::R,12=>K::Hmr,13=>K::CCX,14=>K::CCZ,15=>K::PushCondition,16=>K::PopCondition,17=>K::DebugPrint,_=>panic!("product-cache row kind")};
 o.q_control2.0=v[1];o.q_control1.0=v[2];o.q_target.0=v[3];o.c_target.0=v[4];o.c_condition.0=v[5];o.r_target.0=v[6];o
}
fn same(o:&Op,v:&[u64])->bool{(o.kind as u64)==v[0]&&o.q_control2.0==v[1]&&o.q_control1.0==v[2]&&o.q_target.0==v[3]&&o.c_target.0==v[4]&&o.c_condition.0==v[5]&&o.r_target.0==v[6]}
#[allow(unused)]
pub(super) fn run(ops:Vec<Op>)->Vec<Op>{
 let mut lines=TABLE.lines();let header:Vec<&str>=lines.next().unwrap().split_whitespace().collect();assert_eq!(header[0],"PRODUCT_CACHE");
 assert_eq!(ops.len(),header[1].parse::<usize>().unwrap(),"product-cache source count");let mut h=Sha3_256::new();
 for o in &ops{h.update((o.kind as u32).to_le_bytes());h.update([0u8;4]);for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{h.update(v.to_le_bytes());}}
 assert_eq!(format!("{:x}",h.finalize()),header[2],"product-cache source hash");
 let mut edits=lines.map(|l|l.split_whitespace().map(|s|s.parse::<u64>().unwrap()).collect::<Vec<u64>>());
 let mut next=edits.next();let mut out=Vec::with_capacity(ops.len()+4096);let mut activated=0;
 for (i,o) in ops.into_iter().enumerate(){
  if next.as_ref().map_or(false,|v|v[0]==i as u64){
   let v=next.take().unwrap();assert!(same(&o,&v[6..13]),"product-cache expected source row");
   let (n,m)=(v[4] as usize,v[5] as usize);assert_eq!(v.len(),13+7*(n+m));
   let start=13;let len=n;
   for p in v[start..start+7*len].chunks(7){out.push(row(p));}
   activated+=1;next=edits.next();
  }else{out.push(o);}
 }
 assert!(next.is_none(),"product-cache inactive edits");
 out
}
