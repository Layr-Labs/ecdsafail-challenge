//! Complete candidate T10 via a funded single-rail chart expansion.
//! Active coefficient A<=254 follows the exact start-cycle t<=p/2 bound.
//! Active A0/Craw0/S0 represents the full C256 quotient; A255 is terminal.
//! This file still requires new complete physical native qualification.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
#[path="metadata_phase115_programs.rs"] mod phases;
use super::q793_t10_expand_v11::ceq;
fn guard(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg],j:usize,last:bool,low:bool){
    let _=a;let cc=if last{ceq(rank,c,1)}else{let mut cc=vec![vec![]];cc.extend(ceq(rank,c,1));cc};
    let mut small=Vec::new();for&(m,v)in phases::S_ZERO[0]{let mut cs:Vec<_>=sm.iter().map(|q|(q,false)).collect();if j&1!=0{cs.push((&c[0],j==1));}cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));small.push(cs);}
    let ss=if low{small}else{let mut x=vec![vec![]];x.extend(small);x};
    for x in &cc{for y in &ss{let mut cs=vec![(p1,true),(p2,false)];cs.extend(x);cs.extend(y);super::q794_t10_quotient::gate(circ,&cs,g,dirty);}}
}
fn move_g(circ:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    let(left,l)=super::q794_handoffs::gather_a(circ,rank,a,w1,1,dirty);let(right,r)=super::q794_handoffs::gather_a(circ,rank,a,w2,2,dirty);circ.cswap(g,left,right);circ.b.ops.extend(r.into_iter().rev());circ.b.ops.extend(l.into_iter().rev());
}
fn branch(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],n:usize,j:usize,last:bool,low:bool){
    let g=&helpers[0];let dirty=&helpers[1..];let mut cost_at=circ.b.ops.len();
    guard(circ,rank,a,c,sm,p1,p2,g,dirty,j,last,low);
    if low{super::q793_t10_expand_v11::flags(circ,rank,a,c,g,&sm[1],&sm[2],dirty);super::q793_t10_expand_v11::emit(circ,rank,a,c,sm,p1,p2,g,w1,w2,dirty,j,false,last);}
    cost(circ,&mut cost_at,last,low,"guard+decode");
    let mut source:Vec<_>=w1[..256].iter().map(QReg::borrowed_alias).collect();if low{source.push(sm[3].borrowed_alias());}
    move_g(circ,rank,a,g,&source,w2,dirty);
    if last{
        super::q793_t10_fused_v3::add_and_clear(circ,rank,&source,w2,a,g,&c[2],&c[1],&c[0],dirty,n,c,sm,j,true,low);circ.cx(g,&c[0]);
    }else{
        let mask=&dirty[0];let rest=&dirty[1..];circ.cx(g,p1);
        if low{super::q794_t10_quotient::pop_and_mask_cached(circ,rank,a,c,g,p1,mask,p2,&source,w2,rest);}
        else{super::q793_t10_routes_v4::exchanges(circ,rank,a,c,g,&[p1,mask],&source,rest);}
        super::q793_t10_fused_v3::add_and_clear(circ,rank,&source,w2,a,g,p2,mask,p1,rest,n,c,sm,j,false,low);
        if low{super::q794_t10_quotient::mask_return_cached(circ,rank,a,c,g,mask,p2,&source,w2,rest);}
        else{super::q793_t10_routes_v4::exchanges(circ,rank,a,c,g,&[mask],&source,rest);}
        circ.cx(g,p1);
    }
    move_g(circ,rank,a,g,&source,w2,dirty);
    cost(circ,&mut cost_at,last,low,"arithmetic");
    if low{super::q793_t10_expand_v11::emit(circ,rank,a,c,sm,p1,p2,g,w1,w2,dirty,j,true,last);super::q793_t10_expand_v11::flags(circ,rank,a,c,g,&sm[1],&sm[2],dirty);}
    guard(circ,rank,a,c,sm,p1,p2,g,dirty,j,last,low);
    cost(circ,&mut cost_at,last,low,"encode+return");
}
fn cost(circ:&Circuit,at:&mut usize,last:bool,low:bool,part:&str){if std::env::var("Q793_T10_COST").ok().as_deref()==Some("1"){let ops=&circ.b.ops[*at..];let t=ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count();eprintln!("Q793_T10_V11_COST last={last} low={low} part={part} ops={} T={t}",ops.len());}*at=circ.b.ops.len();}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],n:usize,j:usize){
    assert_eq!(helpers.len(),23);assert!(j<4);let owned=circ.b.next_qubit;let start=circ.b.ops.len();
    // Every branch restores g=0 and its original passenger at the same
    // A-addressed source top. Hold this one loan across all four branches.
    super::q793_loans::global_a(circ,rank,a,&helpers[0],w1,&w2[258],None,&helpers[1..]);
    for low in [false,true]{for last in [true,false]{branch(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,n,j,last,low);}}
    super::q793_loans::global_a(circ,rank,a,&helpers[0],w1,&w2[258],None,&helpers[1..]);
    assert_eq!(circ.b.next_qubit,owned);
    for op in &circ.b.ops[start..]{for h in [256,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"T10 V11 touched omitted W1[{h}]");}}
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,2048,8);super::shared_optimize::cancel_nct_live(&mut tail,2048);circ.b.ops.extend(tail);
}
