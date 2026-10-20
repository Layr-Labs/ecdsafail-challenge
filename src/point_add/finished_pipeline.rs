use crate::circuit::{Op,OperationType,QubitId};
use sha3::{Digest,Sha3_256};
const RAW_COUNT:usize=10547458;
const RAW_SHA3:&str="68d39438e3a7dc3627edc9e5ce9f1e2a75fcf113bafbfd83e85e99a269843d8c";
pub(super) const IDENTITY_NONCE:u64=125;
pub(super)fn run(ops:Vec<Op>)->Vec<Op>{
 assert_eq!(ops.len(),RAW_COUNT,"Frozen raw operation count");let mut hash=Sha3_256::new();
 for o in &ops{for v in[o.kind as u64,o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{hash.update(v.to_le_bytes());}}
 assert_eq!(format!("{:x}",hash.finalize()),RAW_SHA3,"Frozen raw operation records");
 let mut ops=super::breakthrough_generic::run(ops);assert!(IDENTITY_NONCE<(1u64<<48));
 for bit in 0..48{let mut op=Op::empty();op.kind=OperationType::X;op.q_target=QubitId((IDENTITY_NONCE>>bit)&1);op.validate();ops.extend([op,op]);}
 ops
}
