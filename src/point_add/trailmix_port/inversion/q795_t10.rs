//! T10 with two passenger cargos: existing P2 head plus a second safe gap.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="metadata_phase115_programs.rs"] mod programs;
fn enable_other(circ:&mut Circuit,rank:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]){
    mixed_mcx(circ,&[(p1,true),(p2,false)],g,dirty);
    for &(m,v)in programs::C_EQUAL[0]{
        let mut cs=vec![(p1,true),(p2,false)];cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));
        cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,g,dirty);
    }
}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],n:usize){
    assert!(helpers.len()>=23);
    let start=circ.b.ops.len();
    // C1's last digit is known one. Its existing specialized adder leaves
    // arbitrary cargo in that digit while returning all other scratch.
    super::q797_t10_c1::emit(circ,rank,a,c,p1,p2,w1,w2,helpers,n);
    let g=&helpers[0];let dirty=&helpers[1..];let mask=&dirty[0];let rest=&dirty[1..];
    super::q798_step::loan(circ,rank,a,w1,g,dirty);enable_other(circ,rank,c,p1,p2,g,dirty);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);
    // P1 is one on this stable aggregate enable, and may serve as the
    // temporary quotient/Sign bit while g guards the arithmetic.
    circ.cx(g,p1);
    if super::metadata_muxlease::active("Q795_T10_QUOTIENT_PAIR") {
        super::metadata_muxlease::quotient_sequence(circ,rank,a,c,&[(g,true)],&[p1,mask],w1,rest,false);
    }else{
        super::metadata_muxlease::quotient(circ,rank,a,c,&[(g,true)],p1,w1,dirty,false);
        super::metadata_muxlease::quotient(circ,rank,a,c,&[(g,true)],mask,w1,rest,false);
    }
    if super::metadata_muxlease::active("Q795_T10_FUSED") {
        super::q795_t10_fused::add_and_clear(circ,rank,w1,w2,a,g,p2,mask,p1,rest,n);
    } else {
    if super::metadata_muxlease::active("Q795_T10_TOP_TWO_PASS") {
        super::q795_t10_two_pass::prefix(circ,rank,w1,w2,a,g,p2,mask,None,Some(p1),rest,true,n);
    } else {super::metadata_prefix_tree::prefix(circ,rank,w1,w2,a,g,p2,mask,None,Some(p1),rest,true,n);}
    circ.cx(g,p1);
    if super::metadata_muxlease::active("Q795_T10_TOP_TWO_PASS") {
        super::q795_t10_two_pass::prefix(circ,rank,w1,w2,a,g,p2,mask,Some(p1),None,rest,false,n);
    } else {super::metadata_prefix_tree::prefix(circ,rank,w1,w2,a,g,p2,mask,Some(p1),None,rest,false,n);}
    }
    super::metadata_muxlease::quotient(circ,rank,a,c,&[(g,true)],mask,w1,rest,false);
    // On reachable T10 states the comparison/carry result is zero.
    circ.cx(g,p1);
    super::q798_handoffs::move_t10(circ,rank,a,p1,p2,w1,w2,dirty);
    enable_other(circ,rank,c,p1,p2,g,dirty);super::q798_step::loan(circ,rank,a,w1,g,dirty);
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,2048,8);super::shared_optimize::cancel_nct_live(&mut tail,2048);circ.b.ops.extend(tail);
}
