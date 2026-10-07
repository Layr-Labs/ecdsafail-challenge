//! Numeric low-dimensional routing charts and phase-funded final transport.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
fn a(m:&[QReg])->Vec<QReg>{m[4..10].iter().chain(&m[..2]).map(QReg::borrowed_alias).collect()}
fn terminal(c:&mut Circuit,m:&[QReg],out:&QReg,d:&[QReg]){let mut cs:Vec<_>=m[..4].iter().map(|q|(q,true)).collect();cs.push((&m[5],true));mixed_mcx(c,&cs,out,d);}
pub(super) fn r00(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w2:&[QReg],d:&[QReg]){
    terminal(c,m,p1,d);super::q792_czero_chart_r01::emit(c,m,d,false);let a=a(m);super::q792_numeric_moves_r01::adjacent_a_terms(c,&a,w2,1,2,&[vec![(p1,false),(p2,false)]],d);super::q792_czero_chart_r01::emit(c,m,d,true);terminal(c,m,p1,d);
}
pub(super) fn c1_inbound(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],d:&[QReg]){
    let flag=|c:&mut Circuit|super::q792_fold20_predicate_r01::rank_low(c,m,0x6381e00f,63<<6,1<<6,&[(p1,true),(p2,false)],sign,d);
    flag(c);c.x(&m[10]);super::q792_czero_chart_r01::emit(c,m,d,false);let a=a(m);super::q792_numeric_cargo_r01::inbound(c,&a,w1,w2,2,&vec![vec![(p1,true),(p2,false),(sign,true)]],d);super::q792_czero_chart_r01::emit(c,m,d,true);c.x(&m[10]);flag(c);
}
pub(super) fn r_to_t(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],d:&[QReg],j:usize){
    if j&1!=0{return;}
    let c1=|c:&mut Circuit|{if j==2{let truth=[0,13,23,29].iter().fold(0u32,|v,&r|v|(1<<r));super::q792_fold20_predicate_r01::rank_low(c,m,truth,(63<<6)|(15<<12),1<<6,&[(p1,false),(p2,true)],sign,d);}};
    let flag=|c:&mut Circuit|{super::q792_fold20_predicate_r01::rank_low(c,m,0xb4d22911,(1<<6)|(15<<12),usize::from(j==2)<<6,&[(p1,false),(p2,true)],sign,d);c1(c);if j==0{let mut cs=vec![(p1,false),(p2,true),(&w2[258],false)];cs.extend(m.iter().map(|q|(q,false)));mixed_mcx(c,&cs,sign,d);}};
    let controls=vec![vec![(p1,false),(sign,true)]];
    if j==2{c1(c);super::q792_ssmall_unconditional_r01::emit(c,m,d,false);let a=a(m);super::q792_numeric_cargo_r01::inbound(c,&a,w1,w2,0,&controls,d);super::q792_ssmall_unconditional_r01::emit(c,m,d,true);c1(c);}
    flag(c);super::q792_ssmall_unconditional_r01::emit(c,m,d,false);let a=a(m);super::q792_numeric_cargo_r01::head_to_two(c,&a,&m[10..16],w1,w2,&controls,d);super::q792_ssmall_unconditional_r01::emit(c,m,d,true);flag(c);
}
pub(super) fn final_cargo(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,it:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],held:bool){
    let pool:Vec<_>=h.iter().chain(std::iter::once(it)).map(QReg::borrowed_alias).collect();let g=&pool[0];let d=&pool[1..];let bank:Vec<_>=(0..256).map(|a|if a==255{&w2[258]}else{&w1[a+1]}).collect();if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);}
    // P1 xor P2 marks both active transport cases. The held A-pad zero
    // supplies the missing rank bit, while P2 retains the case distinction.
    c.cx(p2,p1);
    super::q792_unfold_lease_r01::emit(c,m,g,p1,d,false);
    let rank:Vec<_>=m[..4].iter().chain(std::iter::once(g)).map(QReg::borrowed_alias).collect();
    super::q793_step_r03::final20_mux_provided(c,&rank,&m[4..10],&m[10..16],p1,p2,w1,w2,d);
    super::q792_unfold_lease_r01::emit(c,m,g,p1,d,true);
    c.cx(p2,p1);
    if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);}
}
