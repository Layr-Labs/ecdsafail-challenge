use crate::circuit::{Op,OperationType,QubitId};
use sha3::{Digest,Sha3_256};
const RAW_COUNT:usize=10543037;
const RAW_SHA3:&str="18f7fc00af40daeda201761064a6ce33a6ac74da78054df3464bdce6a4f0bcb9";
pub(super)const IDENTITY_NONCE:u64=8;
pub(super)fn run(ops:Vec<Op>)->Vec<Op>{
 assert_eq!(ops.len(),RAW_COUNT,"Frozen square1408 raw operation count");let mut hash=Sha3_256::new();
 for o in &ops{for v in[o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{hash.update(v.to_le_bytes());}}
 assert_eq!(format!("{:x}",hash.finalize()),RAW_SHA3,"Frozen square1408 raw records");
 let mut ops=super::breakthrough_generic::run(super::square_lease_cache::run(super::breakthrough_generic::run(ops)));assert!(IDENTITY_NONCE<(1u64<<48));
 for bit in 0..48{let mut o=Op::empty();o.kind=OperationType::X;o.q_target=QubitId((IDENTITY_NONCE>>bit)&1);o.validate();ops.extend([o,o]);}ops
}
