//! Exact compare/subtract by a divisor whose low bit is a virtual constant one.
use super::builder::B;
use super::arith::{up_m,down_m,Dm};
use crate::circuit::QubitId;
/// t has n bits; zh has n-1 bits and zh[0] is ignored. zero=0, out initially0
/// for arithmetic care. t0 is a borrowed carry-in, not a clean helper.
/// All gates are unitary; zero and zh are restored even for arbitrary out.
pub fn cmp_csub_virtual_odd(b:&mut B,t:&[QubitId],zh:&[QubitId],zero:QubitId,out:QubitId){
 assert!(t.len()>=3 && zh.len()+1==t.len());
 let mut upper=zh[1..].to_vec();upper.push(zero);
 b.x(t[0]);
 let up=up_m(b,&t[1..],&upper,t[0],true);
 let dn=down_m(b,&t[1..],&upper,t[0],Dm::Cond(out),true);
 b.play(&up,false);
 b.x(zero);b.cx(zero,out);b.x(zero);
 b.play(&dn,false);
 b.x(t[0]);b.cx(out,t[0]);
}
