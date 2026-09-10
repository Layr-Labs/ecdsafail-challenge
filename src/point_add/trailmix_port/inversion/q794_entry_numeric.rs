//! Closed numeric entry chart; active empty-C -> final valid high triple.
//! Offguard every arithmetic output is inactive and the chart pair restores.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::super::length_recompute::mixed_mcx;
#[path="q794_r01_numeric_partial.rs"] mod chart;
pub(super) fn enabled()->bool{std::env::var("Q794_ENTRY_NUMERIC").ok().as_deref()==Some("1")}

fn convert(circ:&mut Circuit,word:&[QReg],dirty:&[QReg],inverse:bool){let start=circ.b.ops.len();chart::emit(circ,word,dirty);if inverse{circ.b.ops[start..].reverse();}}
/// Guard every gate of the existing no-carry-register ripple adder.
/// Its initial duplicate a0->b0 CNOTs commute with the other first fanouts
/// and cancel. No other gate ordering or source-restoration rule changes.
fn ripple(circ:&mut Circuit,a:&[QReg],b:&[QReg],g:&QReg,dirty:&[QReg],inverse:bool){
 let n=a.len();assert_eq!(n,b.len());assert!(n>=2);let start=circ.b.ops.len();
 for i in 1..n{circ.ccx(g,&a[i],&b[i]);}
 for i in(1..n).rev(){if i+1<n{circ.ccx(g,&a[i],&a[i+1]);}}
 for i in 0..n-1{mixed_mcx(circ,&[(g,true),(&a[i],true),(&b[i],true)],&a[i+1],dirty);}
 for i in(1..n).rev(){circ.ccx(g,&a[i],&b[i]);mixed_mcx(circ,&[(g,true),(&a[i-1],true),(&b[i-1],true)],&a[i],dirty);}
 for i in 1..n-1{circ.ccx(g,&a[i],&a[i+1]);}for i in 0..n{circ.ccx(g,&a[i],&b[i]);}
 if inverse{circ.b.ops[start..].reverse();}
}

pub(super) fn transfer(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,source:&[QReg],_prefix:&[QReg],dirty:&[QReg],j:usize,inverse:bool,lo:usize,hi:usize){
 let start=circ.b.ops.len();let owned=circ.b.next_qubit;assert!(j<4);circ.cx(g,p1);circ.cx(g,p2);
 let chartword:Vec<_>=rank.iter().chain(std::iter::once(p1)).map(QReg::borrowed_alias).collect();
 convert(circ,&chartword,dirty,false);
 // On entry g1: rank2/3 are numeric Chi=0, p2 remains0. On g0 their
 // arbitrary values are safe because all middle target operations retain g.
 let aa:Vec<_>=a.iter().chain(&rank[..2]).map(QReg::borrowed_alias).collect();
 let cc:Vec<_>=c.iter().chain(&rank[2..4]).map(QReg::borrowed_alias).collect();
 let ss:Vec<_>=sm.iter().chain(std::iter::once(&rank[4])).chain(std::iter::once(p1)).map(QReg::borrowed_alias).collect();
 super::head_delta(circ,rank,a,source,c,g,dirty,lo,hi);
 // Complement delta and add2, exactly as in the old destination C8 word.
 for q in&cc{circ.cx(g,q);}for k in(1..8).rev(){let cs:Vec<_>=cc[1..k].iter().map(|q|(q,true)).collect();super::clean(circ,g,p2,dirty,&cs,&cc[k]);}
 ripple(circ,&aa,&cc,g,dirty,true);
 ripple(circ,&ss,&cc[2..],g,dirty,true);
 // The compile-time virtual low S bits are subtracted after high S.
 // Both translations commute on C8; every source and scratch is restored.
 let low=(4-j)%4;for i in(0..2).rev(){if low>>i&1==0{continue;}for k in i..8{let cs:Vec<_>=cc[i..k].iter().map(|q|(q,true)).collect();super::clean(circ,g,p2,dirty,&cs,&cc[k]);}}
 // The proved final high triple belongs to the SAME partial chart image.
 // Thus its inverse restores rank5 plus p1=0, with p2 still zero on g1.
 convert(circ,&chartword,dirty,true);circ.cx(g,p2);circ.cx(g,p1);
 if inverse{circ.b.ops[start..].reverse();}let mut ops=circ.b.ops.split_off(start);super::super::shared_optimize::cancel_nct(&mut ops,256,8);super::super::shared_optimize::cancel_nct_live(&mut ops,256);circ.b.ops.extend(ops);assert_eq!(circ.b.next_qubit,owned);
}
