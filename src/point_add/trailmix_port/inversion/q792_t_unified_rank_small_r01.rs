//! Unified T metadata chart AFTER low unpack, no shifted S token.
//! Input rank6 is [original rank5, held SMALL=(Squarter==0)]. SM0..2
//! may hold arbitrary parked payload iff SMALL; SM3 then remains zero.
//! Output rank[0..2] is literal A_high2 for every A0..252 and C>=1,
//! including raw C0 as C256/A0/S0. Remaining rank and SM are payload.
//! A_low6 and C_low6 are untouched. All dirty helpers are restored.
//! A physical lease must fund held SMALL; this does NOT provide H mask.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
const P:[usize;64]=[0, 52, 48, 16, 4, 28, 20, 7, 8, 56, 60, 24, 12, 13, 5, 9, 1, 17, 33, 25, 29, 21, 22, 6, 18, 10, 26, 2, 30, 23, 15, 31, 32, 3, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44, 43, 45, 46, 47, 19, 49, 50, 51, 61, 55, 53, 54, 27, 57, 58, 59, 14, 11, 62, 63];
fn trans(c:&mut Circuit,r:&[QReg],sm:&[QReg],g:&QReg,d:&[QReg],left:usize,right:usize,sm_zero:bool){
 let delta=left^right;let pivot=delta.trailing_zeros()as usize;let base=if left>>pivot&1==0{left}else{right};
 let frame:Vec<_>=(0..6).filter(|&i|i!=pivot&&delta>>i&1!=0).collect();
 for &i in &frame{c.cx(&r[pivot],&r[i]);}
 let mut cs=vec![(g,true)];cs.extend((0..6).filter(|&i|i!=pivot).map(|i|(&r[i],base>>i&1!=0)));
 if sm_zero{cs.extend(sm.iter().map(|q|(q,false)));}mixed_mcx(c,&cs,&r[pivot],d);
 for &i in frame.iter().rev(){c.cx(&r[pivot],&r[i]);}
}
pub(super) fn emit(c:&mut Circuit,r:&[QReg],sm:&[QReg],g:&QReg,d:&[QReg],inverse:bool){
 assert_eq!(r.len(),6);assert_eq!(sm.len(),4);assert!(d.len()>=8);
 let mut ids:Vec<_>=r.iter().chain(sm).chain(std::iter::once(g)).chain(d).map(QReg::id).collect();ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]));
 let at=c.b.ops.len();let owned=c.b.next_qubit;
 // Only one rank input needs a different A label between the two SM banks:
 // original rank7=(Ah0,Ch1,Sh3), SMALL0 swaps with rank0,SMALL0.
 trans(c,r,sm,g,d,7,0,true);
 let mut seen=[false;64];for a in 0..64{if seen[a]{continue;}seen[a]=true;let mut b=P[a];while b!=a{trans(c,r,sm,g,d,a,b,false);seen[b]=true;b=P[b];}}
 if inverse{c.b.ops[at..].reverse();}assert_eq!(c.b.next_qubit,owned);
}
