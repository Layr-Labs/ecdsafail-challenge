//! Scheduled dual-cargo T10 on the two-hole mod4 chart. Experimental.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="metadata_phase115_programs.rs"] mod programs;
fn c1_guard(circ:&mut Circuit,rank:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg]){
    if c1_guard_factored(circ,rank,c,p1,p2,g,dirty){return;}
    for &(m,v)in programs::C_EQUAL[0]{let mut cs=vec![(p1,true),(p2,false)];cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));mixed_mcx(circ,&cs,g,dirty);}
}

/// The C1 guard is `H(rank) * B` with `B = p1 * !p2 * c[0] * !c[1..6]` shared by
/// every `C_EQUAL[0]` cube, so the direct expansion pays the same 8-control
/// conjunction once per cube. Factor it with the tree's exact dirty echo (same
/// identity as `q794_r01_factor`): `D_B H_d D_B^-1 H_d` toggles `H*B` into `g`
/// and restores the borrowed `d`. `H` is a function of the 5 rank bits alone,
/// so each cube costs only its own popcount.
///
/// Cost-compared against the direct form with the tree's own `4n-8` dirty-ladder
/// model and declined when the echo is not strictly cheaper, so it cannot
/// regress. Cubes are `(mask,value)` pairs, i.e. mixed-polarity products, which
/// the echo handles unchanged -- only the SHARED factor is hoisted.
fn c1_guard_factored(circ:&mut Circuit,rank:&[QReg],c:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg])->bool{
    if !super::metadata_muxlease::active("Q794_T10_C1_GUARD_FACTOR")||dirty.len()<2{return false;}
    fn cost(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*n-8}}
    let shared=2+c.len();
    let direct:usize=programs::C_EQUAL[0].iter().map(|&(m,_)|cost(shared+m.count_ones()as usize)).sum();
    let chart:usize=programs::C_EQUAL[0].iter().map(|&(m,_)|cost(m.count_ones()as usize)).sum();
    let echo=2*chart+2*cost(shared+1);
    if direct<=echo{return false;}
    let d=&dirty[0];let rest=&dirty[1..];
    let compute=|circ:&mut Circuit|{
        for &(m,v)in programs::C_EQUAL[0]{
            let cs:Vec<(&QReg,bool)>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)).collect();
            match cs.len(){
                0=>circ.x(d),
                1=>{if !cs[0].1{circ.x(cs[0].0);}circ.cx(cs[0].0,d);if !cs[0].1{circ.x(cs[0].0);}}
                _=>mixed_mcx(circ,&cs,d,rest),
            }
        }
    };
    let consume=|circ:&mut Circuit|{
        let mut cs=vec![(d,true),(p1,true),(p2,false)];
        cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));
        mixed_mcx(circ,&cs,g,rest);
    };
    consume(circ);compute(circ);consume(circ);compute(circ);
    true
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
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,2048,8);super::shared_optimize::cancel_nct_live(&mut tail,2048);circ.b.ops.extend(tail);
}
