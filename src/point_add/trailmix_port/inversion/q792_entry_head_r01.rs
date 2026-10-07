//! Fold20 C0 -> Cnew using phase11's two temporary zeros, no extra rank wire.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
pub(super) fn transfer_with_support(circ:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,guard:&QReg,source:&[QReg],_prefix:&[QReg],helpers:&[QReg],j:usize,inverse:bool,lo:usize,hi:usize){
    assert_eq!(m.len(),20);assert!(helpers.len()>=20);let start=circ.b.ops.len();let owned=circ.b.next_qubit;
    super::q792_czero_guarded_r01::emit(circ,m,guard,helpers,false);circ.cx(guard,p1);circ.cx(guard,p2);
    let rank=&m[..4];let a=&m[4..10];let c=&m[10..16];let sm=&m[16..20];let word:Vec<_>=c.iter().chain([p1,p2]).collect();
    super::metadata_entry_head5::head_delta(circ,rank,a,source,c,guard,helpers,lo,hi);
    // C starts at the one-hot head offset delta; compute 257-delta-A-S mod256.
    for &q in &word{circ.cx(guard,q);}for k in (1..8).rev(){let mut cs=vec![(guard,true)];cs.extend(word[1..k].iter().map(|&q|(q,true)));mixed_mcx(circ,&cs,word[k],helpers);}
    let addstart=circ.b.ops.len();for i in 0..8{for k in (i..8).rev(){let mut cs=vec![(guard,true),(if i<6{&a[i]}else{&rank[i-6]},true)];cs.extend(word[i..k].iter().map(|&q|(q,true)));mixed_mcx(circ,&cs,word[k],helpers);}}circ.b.ops[addstart..].reverse();
    let addstart=circ.b.ops.len();let low=(4-j)%4;for i in 0..8{if i<2&&low>>i&1==0{continue;}for k in (i..8).rev(){let mut cs=vec![(guard,true)];if i>=2{cs.push((if i<6{&sm[i-2]}else{&rank[i-4]},true));}cs.extend(word[i..k].iter().map(|&q|(q,true)));mixed_mcx(circ,&cs,word[k],helpers);}}circ.b.ops[addstart..].reverse();
    // Six numeric high bits -> rank5 plus zero, then inverse folded decode
    // returns the remaining phase bit to zero on the admitted simplex.
    let high:Vec<_>=rank.iter().chain([p1,p2]).collect();let ts=super::q792_fold20_rank_r01::triples();let pairs:Vec<_>=ts.iter().enumerate().map(|(r,t)|(t[0]|t[2]<<2|t[1]<<4,r)).collect();
    super::q792_unfold_lease_r01::permutation(circ,&high,guard,helpers,&pairs);super::q792_unfold_lease_r01::emit(circ,m,p1,guard,helpers,true);circ.cx(guard,p2);circ.cx(guard,p1);
    if inverse{circ.b.ops[start..].reverse();}assert_eq!(circ.b.next_qubit,owned);
}
#[path="q792_entry_head_check_r01.rs"]mod check;
pub fn run(){check::run();}
