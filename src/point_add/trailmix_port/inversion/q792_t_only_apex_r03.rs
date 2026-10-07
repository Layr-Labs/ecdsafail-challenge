//! Exact finite apex T geometry. Every admitted A253/254 state has S<=2.
//! Public clock removes impossible branches; folded metadata predicates are
//! exact constants, including all endpoint cases, not sampled width caps.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};

const GEOMETRY:[(usize,usize,usize);9]=[
    (253,1,0),(253,1,1),(253,1,2),(253,2,0),(253,2,1),
    (253,3,0),(254,1,0),(254,1,1),(254,2,0),
];
fn guard(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,d:&[QReg],j:usize,f:u8){
    let ts=super::q792_fold20_rank_r01::triples();
    let rank=ts.iter().position(|&v|v==[3,0,0]).unwrap();
    let(lo,hi)=c.q797_a_support.unwrap_or((0,256));
    for(a,cv,s)in GEOMETRY{
        if a<lo||a>=hi||f&(if cv==1{1}else{2})==0{continue;}
        let clock_s=(j&1)+2*((j>>1)^(j&1)^(cv&1));
        if s!=clock_s{continue;}
        let code=super::q792_fold20_rank_r01::encode(rank,a&63,cv,0,&ts);
        let mut cs=vec![(p1,true),(p2,false)];
        cs.extend(m.iter().enumerate().map(|(i,q)|(q,code>>i&1!=0)));
        super::length_recompute::mixed_mcx(c,&cs,g,d);
    }
}
pub(super)fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],n:usize,j:usize){emit_with_loan(c,m,p1,p2,w1,w2,h,n,j,false);}
pub(super)fn emit_with_loan(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],n:usize,j:usize,held:bool){
    assert_eq!(m.len(),20);assert_eq!(h.len(),23);assert!(j<4);
    if c.q797_a_support.is_some_and(|(lo,hi)|lo>=255||hi<=253){return;}
    let owned=c.b.next_qubit;let g=&h[0];let d=&h[1..];
    let bank:Vec<_>=(0..256).map(|a|if a==255{&w2[258]}else{&w1[a+1]}).collect();
    if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);}
    let original=c.q797_a_support;
    // On this exact branch M=A+C>=254, so retaining M>=253 is conservative.
    // Keep the original upper calendar bound; only the proven lower bound changes.
    let quotient_support=Some(original.map_or((253,256),|(lo,hi)|(lo.max(253),hi)));
    let _quotient_scope=super::q792_t_narrow_support_r01::enter(quotient_support);
    let(lo,hi)=original.unwrap_or((0,256));c.q797_a_support=Some((lo.max(253),hi.min(255)));
    let mut previous=0;
    for(last,f)in[(true,1),(false,2)]{
        if last&&j==3||!last&&j==1{continue;}
        guard(c,m,p1,p2,g,d,j,f^previous);previous=f;
        super::q792_unfold_lease_r01::emit(c,m,p2,g,d,false);
        if last{super::q792_t10_rank4_r01::unified(c,m,p1,p2,w1,w2,h,n,j);}
        else{super::q792_t10_rank4_r01::branch(c,m,p1,p2,w1,w2,h,n,j,false,true);}
        super::q792_unfold_lease_r01::emit(c,m,p2,g,d,true);
    }
    guard(c,m,p1,p2,g,d,j,previous);c.q797_a_support=original;
    if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);}
    assert_eq!(c.b.next_qubit,owned);
}
#[path="q792_t_only_apex_check_r03.rs"]mod check;
pub fn run(){check::run();}
