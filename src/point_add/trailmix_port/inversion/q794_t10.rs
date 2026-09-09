//! Scheduled dual-cargo T10 on the two-hole mod4 chart. Experimental.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="metadata_phase115_programs.rs"] mod programs;
fn c1_guard(circ:&mut Circuit,rank:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]){
    for &(m,v)in programs::C_EQUAL[0]{let mut cs=vec![(p1,true),(p2,false)];cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,g,dirty);}
}
fn other_guard(circ:&mut Circuit,rank:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]){
    mixed_mcx(circ,&[(p1,true),(p2,false)],g,dirty);c1_guard(circ,rank,c,p1,p2,g,dirty);
}
fn last(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],n:usize,j:usize){
    let g=&helpers[0];let dirty=&helpers[1..];
    super::q798_step::loan(circ,rank,a,w1,g,dirty);c1_guard(circ,rank,c,p1,p2,g,dirty);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);
    // C=1 supplies cacheC2=0, maskC1=0 and decisionC0=1. The complete
    // fused forward consumes the last quotient1, producing decision0;
    // restore C0 afterward. Its S0 predicate never reads this mutable C0.
    super::q794_t10_fused::add_and_clear(circ,rank,w1,w2,a,g,&c[2],&c[1],&c[0],dirty,n,c,sm,j,true);
    circ.cx(g,&c[0]);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);
    c1_guard(circ,rank,c,p1,p2,g,dirty);super::q798_step::loan(circ,rank,a,w1,g,dirty);
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],n:usize,j:usize){
    if super::q794_t10_fused::mask_one::checking(){super::q794_t10_fused::mask_one::clear();}
    assert_eq!(helpers.len(),23);assert!(j<4);let owned=circ.b.next_qubit;let start=circ.b.ops.len();
    last(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,n,j);
    let g=&helpers[0];let dirty=&helpers[1..];let mask=&dirty[0];let rest=&dirty[1..];
    super::q798_step::loan(circ,rank,a,w1,g,dirty);other_guard(circ,rank,c,p1,p2,g,dirty);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);
    circ.cx(g,p1);
    if super::metadata_muxlease::active("Q794_T10_ENDPOINT_CACHE"){
        super::q794_t10_quotient::pop_and_mask_cached(circ,rank,a,c,g,p1,mask,p2,w1,w2,rest);
    }else if super::metadata_muxlease::active("Q794_T10_COMBINED_LOAN"){
        super::q794_t10_quotient::pop_and_mask_loan(circ,rank,a,c,g,p1,mask,w1,w2,rest);
    }else{
        super::q794_t10_quotient::pop(circ,rank,a,c,g,p1,w1,w2,rest);
        super::q794_t10_quotient::mask_loan(circ,rank,a,c,g,mask,w1,w2,rest,false);
    }
    super::q794_t10_fused::add_and_clear(circ,rank,w1,w2,a,g,p2,mask,p1,rest,n,c,sm,j,false);
    if super::metadata_muxlease::active("Q794_T10_ENDPOINT_CACHE"){
        super::q794_t10_quotient::mask_return_cached(circ,rank,a,c,g,mask,p2,w1,w2,rest);
    }else{super::q794_t10_quotient::mask_loan(circ,rank,a,c,g,mask,w1,w2,rest,true);}
    circ.cx(g,p1);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);
    other_guard(circ,rank,c,p1,p2,g,dirty);super::q798_step::loan(circ,rank,a,w1,g,dirty);
    assert_eq!(circ.b.next_qubit,owned);
    if !super::q794_t10_fused::c1_prefix::checking()&&!super::q794_t10_fused::mask_one::checking()&&!super::q794_t10_fused::rank_prefix::checking(){let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,2048,8);super::shared_optimize::cancel_nct_live(&mut tail,2048);circ.b.ops.extend(tail);}
}
