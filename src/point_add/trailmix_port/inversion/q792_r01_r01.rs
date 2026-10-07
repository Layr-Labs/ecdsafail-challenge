//! Full R01 with three local rank4 charts and literal temporary counters.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::circuit::{Op,NO_QUBIT};
use super::{q792_rank4_lower_r01 as lower,q792_class_chart_r01 as chart,q792_fold20_r01::table,length_recompute::mixed_mcx};
fn project(r:usize,k:usize)->usize{let ker=[24usize,16,29][k];let p=ker.trailing_zeros()as usize;let f=r^if r>>p&1!=0{ker}else{0};(f&((1<<p)-1))|((f>>(p+1))<<p)}
fn rankflag(c:&mut Circuit,m:&[QReg],class:usize,cs:&[(&QReg,bool)],g:&QReg,d:&[QReg],f:impl Fn([usize;3])->bool){
    let ts=super::q792_fold20_rank_r01::triples();let map=lower::chart(class);
    table(c,&m[..4].iter().collect::<Vec<_>>(),(0..16).map(|i|project(map[i],class)==i&&f(ts[map[i]])).collect(),cs,g,d);
}
fn endpoint(c:&mut Circuit,m:&[QReg],class:usize,p1:&QReg,p2:&QReg,g:&QReg,d:&[QReg],value:usize){
    let mut cs=vec![(p1,false),(p2,true)];cs.extend(m[16..20].iter().map(|q|(q,false)));
    if class==0{
        if value!=254{return;}cs.extend(m[4..16].iter().map(|q|(q,true)));rankflag(c,m,class,&cs,g,d,|t|t[0]+t[1]==2&&t[2]==0);
    }else if class==1{
        super::metadata_arithmetic5::add(c,&m[4..10],&m[10..16],None,false);
        cs.extend(m[10..16].iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));
        rankflag(c,m,class,&cs,g,d,|t|t[2]==0);
        if value==254{cs.extend(m[4..10].iter().map(|q|(q,true)));rankflag(c,m,class,&cs,g,d,|t|t[2]==0);}
        super::metadata_arithmetic5::add(c,&m[4..10],&m[10..16],None,true);
        // A255/C0 is the forbidden phase01 terminal extension.
        if value==255{let mut cs=vec![(p1,false),(p2,true)];cs.extend(m[4..10].iter().map(|q|(q,true)));cs.extend(m[10..20].iter().map(|q|(q,false)));rankflag(c,m,class,&cs,g,d,|t|t==[3,0,0]);}
    }
}
pub(super) fn guard(c:&mut Circuit,m:&[QReg],class:usize,p1:&QReg,p2:&QReg,g:&QReg,d:&[QReg],mode:usize){
    if mode!=0{endpoint(c,m,class,p1,p2,g,d,253+mode);return;}
    let base=[(p1,false),(p2,true)];
    if class==0{rankflag(c,m,class,&base,g,d,|_|true);}
    else if class==1{
        rankflag(c,m,class,&base,g,d,|_|true);
        let bit=&d[0];let rest=&d[1..];let word=[&m[8],&m[9],&m[14],&m[15],&m[18],&m[19]];
        let calc=|c:&mut Circuit|table(c,&word,(0..64).map(|x|(x&3)+(x>>2&3)+(x>>4&3)>=5).collect(),&[],bit,rest);
        let useit=|c:&mut Circuit|rankflag(c,m,class,&[(p1,false),(p2,true),(bit,true)],g,rest,|_|true);
        useit(c);calc(c);useit(c);calc(c);
    }else{let mut cs=base.to_vec();cs.extend(m[4..20].iter().map(|q|(q,false)));rankflag(c,m,class,&cs,g,d,|t|t[2]!=0);return;}
    endpoint(c,m,class,p1,p2,g,d,254);endpoint(c,m,class,p1,p2,g,d,255);
}
pub(super) fn template(class:usize,j:usize,end:usize,mode:usize)->Vec<Op>{
    let mut c=Circuit::new();c.b.count_only=false;c.b.fiat_hash=None;let r=c.alloc_qreg_bits("r",5);let a=c.alloc_qreg_bits("a",6);let cl=c.alloc_qreg_bits("c",6);let sm=c.alloc_qreg_bits("sm",4);let p1=c.alloc_qreg("p1");let p2=c.alloc_qreg("p2");let w1=c.alloc_qreg_bits("w1",259);let w2=c.alloc_qreg_bits("w2",259);let h=c.alloc_qreg_bits("helpers",23);let n=c.b.next_qubit;
    let old=std::env::var_os("Q793_R01_NUMERIC_SEED");std::env::set_var("Q793_R01_NUMERIC_SEED","0");lower::begin_capture();
    if mode==0{super::q793_r01_dynamic_timefix_r01::provided_normal(&mut c,&r,&a,&cl,&sm,&p1,&p2,&w1,&w2,&h,j,end);}
    else{super::q793_r01_dynamic_timefix_r01::provided_endpoint(&mut c,&r,&a,&p1,&h[0],&w1,&w2,&h[3..],j,253+mode);}
    lower::end_capture();match old{Some(v)=>std::env::set_var("Q793_R01_NUMERIC_SEED",v),None=>std::env::remove_var("Q793_R01_NUMERIC_SEED")};assert_eq!(c.b.next_qubit,n);
    lower::lower_clean(&c.b.ops,n as usize,&h[3..].iter().map(|q|q.id()as usize).collect::<Vec<_>>(),class)
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],h:&[QReg],j:usize,end:usize){
    assert_eq!(m.len(),20);assert_eq!(h.len(),23);let n=c.b.next_qubit;let g=&h[0];let d=&h[3..];
    let bank:Vec<_>=(0..256).map(|a|if a==255{&w2[258]}else{&w1[a+1]}).collect();super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);
    let ids:Vec<_>=m.iter().chain([p1,p2]).chain(w1).chain(w2).chain(h).map(|q|q.id()as u64).collect();
    for class in 0..3{chart::emit(c,m,d,class,false);for mode in 0..3{if class==2&&mode!=0{continue;}
        guard(c,m,class,p1,p2,g,d,mode);let ops=template(class,j,end,mode);for mut op in ops{for q in [&mut op.q_target,&mut op.q_control1,&mut op.q_control2]{if *q!=NO_QUBIT{q.0=ids[q.0 as usize];}}c.b.ops.push(op);}guard(c,m,class,p1,p2,g,d,mode);
    }chart::emit(c,m,d,class,true);}
    super::q792_fold20_address_r01::exchange(c,m,g,&bank,d);assert_eq!(n,c.b.next_qubit);
}
#[path="q792_r01_check_r01.rs"]mod check;
pub fn run(){check::run();}
