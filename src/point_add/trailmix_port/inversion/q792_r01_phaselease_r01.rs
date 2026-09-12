//! Fold20 R01: P2 funds the unfolded rank; the arithmetic has no HS cache.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::NO_QUBIT;
use super::{q792_class_chart_r01 as chart,q792_r01_r01 as local};
fn end_guard(c:&mut Circuit,a:&[QReg],cl:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,d:&[QReg],value:usize){
    let mut cs=vec![(p1,false),(p2,true)];cs.extend(sm.iter().map(|q|(q,false)));cs.extend(cl.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));super::length_recompute::mixed_mcx(c,&cs,g,d);cs.extend(a.iter().map(|q|(q,true)));super::length_recompute::mixed_mcx(c,&cs,g,d);
}
fn normal(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,d:&[QReg]){
    c.x(p1);c.ccx(p1,p2,g);c.x(p1);let mut cs=vec![(p1,false),(p2,true),(&m[5],true)];cs.extend(m[..4].iter().map(|q|(q,true)));super::length_recompute::mixed_mcx(c,&cs,g,d);
    super::q792_ssmall_unconditional_r01::emit(c,m,d,false);let a=super::q792_ssmall_unconditional_r01::aa(m);let cl=super::q792_ssmall_unconditional_r01::cc(m);super::metadata_arithmetic5::add(c,&a,&cl,None,false);
    for v in [254,255]{end_guard(c,&a,&cl,&m[16..20],p1,p2,g,d,v);}super::metadata_arithmetic5::add(c,&a,&cl,None,true);super::q792_ssmall_unconditional_r01::emit(c,m,d,true);
}
fn endpoints(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,w1:&[QReg],w2:&[QReg],d:&[QReg],j:usize){
    use super::length_recompute::mixed_mcx;
    super::q792_ssmall_unconditional_r01::emit(c,m,d,false);let a=super::q792_ssmall_unconditional_r01::aa(m);let cl=super::q792_ssmall_unconditional_r01::cc(m);super::metadata_arithmetic5::add(c,&a,&cl,None,false);
    let zero=|c:&mut Circuit|{let mut cs=vec![(g,true)];cs.extend(a.iter().map(|q|(q,false)));mixed_mcx(c,&cs,p1,d);};
    for value in [254,255]{end_guard(c,&a,&cl,&m[16..20],p1,p2,g,d,value);zero(c);
        if value==254{let shift=if j&1!=0{0}else{1};let b=[&w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259]];let base=[(g,true),(p1,false),(&w1[0],false)];if shift==0{for x in 1..4{let mut cs=base.to_vec();cs.extend([(&w2[258],x&1!=0),(&w2[257],x&2!=0)]);super::q793_r01_dynamic_timefix_r01::short_permutation(c,b,&cs,x,d);}}else{super::q793_r01_dynamic_timefix_r01::short_permutation(c,b,&base,2,d);}}
        else{c.cx(&w2[1],&w2[0]);mixed_mcx(c,&[(g,true),(p1,false),(&w1[0],false),(&w2[0],true)],&w2[1],d);c.cx(&w2[1],&w2[0]);}
        zero(c);end_guard(c,&a,&cl,&m[16..20],p1,p2,g,d,value);
    }super::metadata_arithmetic5::add(c,&a,&cl,None,true);super::q792_ssmall_unconditional_r01::emit(c,m,d,true);
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],j:usize,end:usize){emit_with_loan(c,m,p1,p2,w1,w2,h,j,end,false);}
pub(super) fn emit_with_loan(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],j:usize,end:usize,held:bool){
    assert_eq!(m.len(),20);assert_eq!(h.len(),23);let n=c.b.next_qubit;let g=&h[0];let ha=&h[1];let decision=&h[2];let d=&h[3..];
    let bank:Vec<_>=(0..256).map(|a|if a==255{&w2[258]}else{&w1[a+1]}).collect();if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);}
    normal(c,m,p1,p2,g,d);c.cx(g,p2);super::q792_unfold_lease_r01::emit(c,m,p2,g,d,false);
    let rank:Vec<_>=m[..4].iter().chain(std::iter::once(p2)).map(QReg::borrowed_alias).collect();let a=&m[4..10];let cl=&m[10..16];let sm=&m[16..20];
    super::q793_r01_a1normalize_timefix_r01::normalize(c,&rank,a,cl,sm,g,p1,w1,w2,d,j,false);
    super::q793_r01_dynamic_timefix_r01::borrow_ha(c,&rank,a,g,ha,w2,d);
    super::q793_r01_routes_v1::quotient(c,&rank,a,cl,w1,g,p1,decision);
    let omitted=QReg::omitted_lane_marker();
    super::q792_r01_nohs_normal_r01::emit(c,&rank,a,cl,sm,g,p1,&omitted,ha,decision,w1,w2,d,j,end,false);
    super::q793_r01_routes_v1::quotient(c,&rank,a,cl,w1,g,p1,decision);
    super::q793_r01_dynamic_timefix_r01::borrow_ha(c,&rank,a,g,ha,w2,d);
    super::q793_r01_a1normalize_timefix_r01::normalize(c,&rank,a,cl,sm,g,p1,w1,w2,d,j,true);
    super::q792_unfold_lease_r01::emit(c,m,p2,g,d,true);c.cx(g,p2);normal(c,m,p1,p2,g,d);
    endpoints(c,m,p1,p2,g,w1,w2,d,j);
    if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);}assert_eq!(n,c.b.next_qubit);
}
#[path="q792_r01_phaselease_check_r01.rs"]mod check;
pub fn run(){check::run();}
