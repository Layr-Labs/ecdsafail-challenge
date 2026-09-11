//! Complete folded20 T10; P2 leases the missing rank bit in each branch.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
fn guard(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,d:&[QReg],j:usize,f:u8){
    if f&1!=0{c.x(p2);c.ccx(p1,p2,g);c.x(p2);}
    for(bit,kind)in[(2,0),(4,1),(8,2)]{if f&bit==0||kind==2&&j==3{continue;}let truth=match kind{0=>0x6381e00f,1=>0xb4d22911,_=>0x20802001};let mut mask=0;let mut value=0;
        if kind!=1{mask|=63<<6;value|=1<<6;}if kind!=0{mask|=15<<12;if j&1!=0{mask|=1<<6;if j==1{value|=1<<6;}}}super::q792_fold20_predicate_r01::rank_low(c,m,truth,mask,value,&[(p1,true),(p2,false)],g,d);
    }
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],n:usize,j:usize){emit_with_loan(c,m,p1,p2,w1,w2,h,n,j,false);}
pub(super) fn emit_with_loan(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],n:usize,j:usize,held:bool){
    assert_eq!(m.len(),20);assert_eq!(h.len(),23);let owned=c.b.next_qubit;let g=&h[0];let d=&h[1..];let bank:Vec<_>=(0..256).map(|a|if a==255{&w2[258]}else{&w1[a+1]}).collect();if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);}
    let mut previous=0u8;for(last,low,f)in[(true,false,2|8),(false,false,1|2|4|8),(true,true,8),(false,true,4|8)]{
        if last&&low&&j==3{continue;}guard(c,m,p1,p2,g,d,j,f^previous);previous=f;super::q792_unfold_lease_r01::emit(c,m,p2,g,d,false);
        let rank:Vec<_>=m[..4].iter().chain(std::iter::once(p2)).map(QReg::borrowed_alias).collect();
        if last||low{super::q792_t10_rank4_r01::branch(c,m,p1,p2,w1,w2,h,n,j,last,low);}else{super::q792_t10_nop2_r01::branch(c,&rank,&m[4..10],&m[10..16],&m[16..20],p1,p2,w1,w2,h,n,j,last,low);}
        super::q792_unfold_lease_r01::emit(c,m,p2,g,d,true);
    }guard(c,m,p1,p2,g,d,j,previous);if !held{super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);}assert_eq!(c.b.next_qubit,owned);
}
#[path="q792_t10_phaselease_check_r01.rs"]mod check;
pub fn run(){check::run();}
