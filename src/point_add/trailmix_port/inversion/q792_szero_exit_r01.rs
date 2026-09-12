//! Entire twenty-bit S0 cycle exit, including both data-dependent length maps.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{q792_fold20_predicate_r01 as folded,q792_szero_chart_r01 as chart};
fn fold_swap(c:&mut Circuit,m:&[QReg],bit:usize,l:&QReg,r:&QReg,d:&[QReg]){
    c.cx(r,l);folded::toggle(c,m,1<<bit,1<<bit,&[(l,true)],r,d);c.cx(r,l);
}
fn folded_loan(c:&mut Circuit,m:&[QReg],pass:&QReg,w1:&[QReg],w2:&[QReg],d:&[QReg]){
    let bank:Vec<_>=(0..256).map(|a|if a==255{&w2[258]}else{&w1[a+1]}).collect();
    super::q792_fold20_address_r01::exchange(c,m,pass,&bank,d);
}
fn guard(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,d:&[QReg]){
    folded::rank_low(c,m,0xb4d22911,15<<12,0,&[(p1,true),(p2,true)],g,d);
    folded::toggle(c,m,(1<<21)-1,0,&[(p1,true),(p2,true)],g,d);
}
fn exchange(c:&mut Circuit,address:&[QReg],bank:Vec<Option<&QReg>>,g:&QReg,pass:&QReg,one:bool){
    let at=c.b.ops.len();let mut nodes=bank;assert_eq!(nodes.len(),1<<address.len());
    for q in address{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(l),Some(r))=>{c.cswap(q,l,r);Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None});}nodes=next;}
    let route=c.b.ops[at..].to_vec();let root=nodes[0].unwrap();c.cswap(g,root,pass);if one{c.cx(g,root);}c.b.ops.extend(route.into_iter().rev());
}
fn loan(c:&mut Circuit,a:&[QReg],g:&QReg,pass:&QReg,w1:&[QReg],w2:&[QReg]){
    exchange(c,a,(0..256).map(|v|Some(if v==255{&w2[258]}else{&w1[v+1]})).collect(),g,pass,false);
}
pub(super) fn emit(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,it:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize){emit_with_loan(c,m,p1,p2,it,w1,w2,helpers,lo,hi,false);}
pub(super) fn emit_with_loan(c:&mut Circuit,m:&[QReg],p1:&QReg,p2:&QReg,it:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],lo:usize,hi:usize,held:bool){
    let at=c.b.ops.len();let n=c.b.next_qubit;assert_eq!(m.len(),20);assert!(helpers.len()>=23);
    let g=&helpers[0];let d=&helpers[2..];if !held{folded_loan(c,m,g,w1,w2,d);}guard(c,m,p1,p2,g,d);
    chart::emit(c,m,g,d,false);let a=chart::aa(m);let cl=chart::cc(m);let sm=&m[16..20];
    exchange(c,&a,(0..256).map(|v|match v{0..=253=>Some(&w1[v+2]),254=>Some(&w2[256]),_=>None}).collect(),g,&sm[2],false);
    exchange(c,&cl,(0..256).map(|v|if v==0{None}else{Some(&w2[259-v])}).collect(),g,&sm[0],true);
    loan(c,&a,g,&sm[3],w1,w2);
    for(i,(x,y))in w1.iter().zip(w2).enumerate(){if ![0,1,2,256,257,258].contains(&i){c.cswap(g,x,y);}}
    super::q793_mod8::cycle_swap(c,[&w1[0],&w1[1],&w1[2],&w2[0],&w2[1],&w2[2],&w2[258],&w2[257],&w2[256]],g,d);
    c.cswap(g,&sm[0],&sm[1]);c.cx(g,p1);
    super::q793_Aupdate::update_numeric(c,&a,&cl,sm,p1,g,w1,w2,d,lo,hi);
    c.cx(g,p1);
    exchange(c,&a,(0..256).map(|v|Some(&w1[v])).collect(),g,&sm[1],false);c.cx(g,&sm[1]);
    exchange(c,&a,(0..256).map(|v|Some(&w2[v+2])).collect(),g,&sm[2],false);
    loan(c,&a,g,&sm[3],w1,w2);
    c.cx(g,p1);super::q793_transfer::erase_c_numeric(c,&a,&cl,sm,p1,g,w1,w2,d);c.cx(g,p1);
    c.cx(g,it);chart::emit(c,m,g,d,true);guard(c,m,p1,p2,g,d);if !held{folded_loan(c,m,g,w1,w2,d);}
    assert_eq!(n,c.b.next_qubit);for op in &c.b.ops[at..]{for h in [256usize,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q);}}
}
#[path="q792_szero_exit_check_r01.rs"]mod check;
pub fn run(){check::run();}
