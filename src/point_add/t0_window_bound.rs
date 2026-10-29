use crate::circuit::Op;
use sha3::{Digest,Sha3_256};
pub(super) fn run(ops:Vec<Op>)->Vec<Op>{
 assert_eq!(ops.len(),PREFIX_LEN,"t0-fullv2-stack-E251 complete parent length");
 let mut h=Sha3_256::new();let mut buf=[0u8;56*256];
 for batch in ops.chunks(256){for(i,o)in batch.iter().enumerate(){let r=&mut buf[i*56..(i+1)*56];r[..4].copy_from_slice(&(o.kind as u32).to_le_bytes());r[4..8].fill(0);for(j,x)in[o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0].into_iter().enumerate(){r[8+j*8..16+j*8].copy_from_slice(&x.to_le_bytes());}}h.update(&buf[..batch.len()*56]);}
 assert_eq!(format!("{:x}",h.finalize()),PREFIX_SHA3,"t0-fullv2-stack-E251 complete parent SHA3");
 super::t0_window::run_minimal(ops,4,3)
}
const PREFIX_LEN:usize=10216164;
const PREFIX_SHA3:&str="7cb59127e6e55b8b24b6ad2b9eaaede31c8f1f8b3d0459eab1edbc4d13387baa";
