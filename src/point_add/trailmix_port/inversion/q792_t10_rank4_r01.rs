//! Branch-local numeric four-bit high metadata; the restored fifth bit funds P2.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::NO_QUBIT;
pub(super) fn branch(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],n:usize,j:usize,last:bool,low:bool){
 assert!(last||low);let class=if last{4}else{3};let ts=super::q792_fold20_rank_r01::triples();let pairs:Vec<_>=ts.iter().enumerate().filter(|(_,t)|t[if last{1}else{2}]==0).map(|(r,t)|(r,t[0]+4*t[if last{2}else{1}])).collect();
 let rank:Vec<_>=m[..4].iter().chain(std::iter::once(p2)).collect();let at=c.b.ops.len();super::q792_unfold_lease_r01::permutation(c,&rank,&h[0],&h[1..],&pairs);let chart=c.b.ops[at..].to_vec();
 let mut v=Circuit::new();v.b.count_only=false;v.b.fiat_hash=None;v.q797_a_support=c.q797_a_support;let r=v.alloc_qreg_bits("rank",5);let a=v.alloc_qreg_bits("a",6);let cc=v.alloc_qreg_bits("c",6);let sm=v.alloc_qreg_bits("sm",4);let vp1=v.alloc_qreg("p1");let vp2=v.alloc_qreg("p2");let vw1=v.alloc_qreg_bits("w1",259);let vw2=v.alloc_qreg_bits("w2",259);let vh=v.alloc_qreg_bits("helpers",23);let owned=v.b.next_qubit as usize;
 super::q792_rank4_lower_r01::begin_capture();super::q793_t10_full_v13::branch(&mut v,&r,&a,&cc,&sm,&vp1,&vp2,&vw1,&vw2,&vh,n,j,last,low);super::q792_rank4_lower_r01::end_capture();
 let pool:Vec<_>=vh[1..].iter().map(|q|q.id()as usize).collect();let source=v.into_builder().ops;let ops=super::q792_rank4_lower_r01::lower_clean(&source,owned,&pool,class);let refs:Vec<_>=m.iter().chain([p1,p2]).chain(w1).chain(w2).chain(h).collect();assert_eq!(refs.len(),owned-1);
 eprintln!("FOLD20_T10_RANK4 j={j} last={last} low={low} old_ops={} ops={}",source.len(),ops.len());
 for mut op in ops{for wire in [&mut op.q_target,&mut op.q_control1,&mut op.q_control2]{if *wire!=NO_QUBIT{wire.0=refs[wire.0 as usize].id()as u64;assert_ne!(wire.0,u32::MAX as u64);}}c.b.ops.push(op);}c.b.ops.extend(chart.into_iter().rev());
}
