//! Full Sign erasure on twenty metadata wires; phase P2 funds general rank5.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
fn triples()->Vec<[usize;3]>{super::q792_fold20_rank_r01::triples()}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],j:usize,_n:usize){
    assert_eq!(m.len(),20);assert!(h.len()>=22);let owned=c.b.next_qubit;let start=c.b.ops.len();
    super::q798_sign_erase::code(c,p1,p2,sign,h,false);
    super::q792_sign_small_r01::compare(c,m,p1,p2,sign,w1,w2,h,j);super::q792_sign_small_r01::flag(c,m,p1,p2,h,j);super::q795_t11::park_c1(c,p1,p2,sign,h);
    super::q792_unfold_lease_r01::emit(c,m,p2,p1,h,false);let rank:Vec<_>=m[..4].iter().chain(std::iter::once(p2)).map(QReg::borrowed_alias).collect();
    super::q792_sign_nop2_r01::general(c,&rank,&m[4..10],&m[10..16],&m[16..20],p1,p2,sign,w1,w2,h,j);
    super::q792_unfold_lease_r01::emit(c,m,p2,p1,h,true);
    super::q795_t11::park_c1(c,p1,p2,sign,h);super::q792_sign_small_r01::flag(c,m,p1,p2,h,j);super::q798_sign_erase::code(c,p1,p2,sign,h,true);
    assert_eq!(c.b.next_qubit,owned);for op in &c.b.ops[start..]{for h in [256,257,258]{let q=w1[h].id()as u64;assert!([op.q_target.0,op.q_control1.0,op.q_control2.0].iter().all(|&x|x!=q),"Sign20 touched hole{h}");}}
}
#[path="q792_sign_phaselease_check_r01.rs"]pub mod verification;
