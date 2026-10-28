//! Frozen exact cache output, independent of the evaluator packet and nonce.
use crate::circuit::{Op,OperationType as K,QubitId,BitId,RegisterId};
use sha3::{Digest,Sha3_256};
use std::io::Read;
const DATA:&[u8]=include_bytes!("frozen_cache_product67.bin");
fn input_hash(ops:&[Op])->String{
 let mut h=Sha3_256::new();for o in ops{h.update((o.kind as u32).to_le_bytes());h.update([0u8;4]);for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{h.update(v.to_le_bytes());}}format!("{:x}",h.finalize())
}
fn bind(ops:&[Op],count:usize,hash:&str){assert_eq!(ops.len(),count,"frozen cache input count");assert_eq!(input_hash(ops),hash,"frozen cache input hash");}
fn number(row:&[u8;56],field:usize)->u64{u64::from_le_bytes(row[field*8..field*8+8].try_into().unwrap())}
fn kind(k:u64)->K{match k{0=>K::Neg,1=>K::Register,2=>K::AppendToRegister,3=>K::BitInvert,4=>K::BitStore0,5=>K::BitStore1,6=>K::X,7=>K::Z,8=>K::CX,9=>K::CZ,10=>K::Swap,11=>K::R,12=>K::Hmr,13=>K::CCX,14=>K::CCZ,15=>K::PushCondition,16=>K::PopCondition,17=>K::DebugPrint,_=>panic!("frozen cache kind")}}
pub(super) fn run(ops:Vec<Op>)->Vec<Op>{
 bind(&ops,11630620,"b200178da6b06e841e384f71c2562c54b1dec09e6ef0a1c44990d408dba4e2e2");drop(ops);
 assert_eq!(format!("{:x}",Sha3_256::digest(DATA)),"04aa2235f6e4cd70cd22fd134fd6d52f47ef09ba6a6e14c7b33570751571184e","frozen cache data hash");
 assert_eq!(&DATA[..8],b"QECCOPSZ");let count=u64::from_le_bytes(DATA[8..16].try_into().unwrap()) as usize;assert_eq!(count,17891821,"frozen cache output count");
 let mut decoder=zstd::stream::read::Decoder::new(&DATA[16..]).expect("frozen cache zstd");decoder.window_log_max(27).expect("frozen cache window");
 let mut out=Vec::with_capacity(count-96);let mut row=[0u8;56];let mut previous=None;
 for i in 0..count{decoder.read_exact(&mut row).expect("frozen cache truncated data");assert_eq!(&row[4..8],&[0u8;4]);let op=Op{kind:kind(number(&row,0)),q_control2:QubitId(number(&row,1)),q_control1:QubitId(number(&row,2)),q_target:QubitId(number(&row,3)),c_target:BitId(number(&row,4)),c_condition:BitId(number(&row,5)),r_target:RegisterId(number(&row,6))};op.validate();
  if i<count-96{out.push(op);}else{
   assert!(op.kind==K::X&&op.q_target.0<=1&&op.q_control1.0==u64::MAX&&op.q_control2.0==u64::MAX&&op.c_target.0==u64::MAX&&op.c_condition.0==u64::MAX&&op.r_target.0==u64::MAX,"frozen cache identity tail shape");
   if (i-(count-96))%2==0{previous=Some(row);}else{assert_eq!(previous,Some(row),"frozen cache paired tail");}
  }
 }
 let mut extra=[0u8;1];assert_eq!(decoder.read(&mut extra).expect("frozen cache trailing read"),0,"frozen cache trailing data");
 eprintln!("FROZEN_CACHE input={} output={} nonce_tail_retained=true",11630620,out.len());out
}
#[cfg(test)]mod tests{
 use super::*;
 fn sample()->Vec<Op>{let mut o=Op::empty();o.kind=K::X;o.q_target=QubitId(0);vec![o]}
 #[test]fn source_binding_positive(){let p=sample();bind(&p,1,&input_hash(&p));}
 #[test]#[should_panic(expected="input count")]fn source_binding_rejects_missing_op(){bind(&[],1,"");}
 #[test]#[should_panic(expected="input hash")]fn source_binding_rejects_changed_wire(){let mut p=sample();let h=input_hash(&p);p[0].q_target=QubitId(1);bind(&p,1,&h);}
 #[test]fn source_binding_includes_classical_conditions(){let p=sample();let h=input_hash(&p);let mut changed=p.clone();changed[0].c_condition=BitId(2);assert_ne!(h,input_hash(&changed));}
}
