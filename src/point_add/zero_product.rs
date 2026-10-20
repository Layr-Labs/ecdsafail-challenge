// Content-bound zero-product row removal.
use crate::circuit::Op;
use sha3::{Digest,Sha3_256};
fn hash(ops:&[Op])->String{let mut h=Sha3_256::new();for o in ops{h.update((o.kind as u32).to_le_bytes());h.update([0u8;4]);for x in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{h.update(x.to_le_bytes());}}format!("{:x}",h.finalize())}
pub(super) fn run(mut ops:Vec<Op>)->Vec<Op>{
 assert_eq!(ops.len(),17891806,"row input length");
 assert_eq!(hash(&ops),"468e86dd1628976643d42b4bb50bdb8c43211f4d29bfbc3df60b11f7342ac619","row input content");
 let i=17876252;
 assert_eq!(hash(&ops[i..i+1]),"167c7dad3201c7b11743b8d6bdd1949fa61952ac7201f71692a3a369be305823","row content");
 assert_eq!(hash(&ops[i-32..i+32+1]),"fa0026c261299431b6a9ce51f74d695f0ddde18e0b67c1b6f8021fe1957e9dd6","row context");
 ops.remove(i);
 ops
}
