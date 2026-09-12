//! Complete candidate T10 via a funded single-rail chart expansion.
//! Active coefficient A<=254 follows the exact start-cycle t<=p/2 bound.
//! Active A0/Craw0/S0 represents the full C256 quotient; A255 is terminal.
//! This file still requires new complete physical native qualification.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
// Exact disjoint covers on all32 encoded rank triples. No restricted
// care domain. These three predicates are also used by qualified Sign r05.
fn rank_terms(rank:&[QReg],kind:usize)->Vec<Vec<(&QReg,bool)>>{
    let cubes:&[(usize,usize)]=match kind{
        0=>&[(28,0),(29,13),(15,14),(23,16),(31,23),(27,25)], // C_high0
        1=>&[(23,0),(15,4),(31,11),(15,13),(31,17),(30,22),(31,26),(31,28),(31,31)], // S_high0
        2=>&[(31,0),(15,13),(31,23)], // C_high0 AND S_high0
        _=>unreachable!(),
    };
    cubes.iter().map(|&(m,v)|(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)).collect()).collect()
}
// XOR selected factors into g: bit0=phase10, bit1=phase10*C1,
// bit2=phase10*Ssmall, bit3=phase10*C1*Ssmall.
fn guard_delta(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,g:&QReg,dirty:&[QReg],j:usize,factors:u8){
    let phase=vec![(p1,true),(p2,false)];
    if factors&1!=0{super::q794_t10_quotient::gate(circ,&phase,g,dirty);}
    for (bit,kind)in[(2,0),(4,1),(8,2)]{
        if factors&bit==0 || kind==2&&j==3{continue;}
        let mut gates=Vec::new();for term in rank_terms(rank,kind){let mut cs=phase.clone();cs.extend(term);
            if kind!=1{cs.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));}
            if kind!=0{cs.extend(sm.iter().map(|q|(q,false)));if j&1!=0{cs.push((&c[0],j==1));}}
            gates.push(cs);
        }super::q793_r01_dynamic_timefix_r01::grouped_with_flag(circ,&gates,rank,g,dirty,"Q793_T10_GUARD_FACTOR");
    }
}
fn move_g(circ:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    let(left,l)=super::q794_handoffs::gather_a(circ,rank,a,w1,1,dirty);let(right,r)=super::q794_handoffs::gather_a(circ,rank,a,w2,2,dirty);circ.cswap(g,left,right);circ.b.ops.extend(r.into_iter().rev());circ.b.ops.extend(l.into_iter().rev());
}
pub(super) fn branch(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],n:usize,j:usize,last:bool,low:bool){
    let g=&helpers[0];let dirty=&helpers[1..];let mut cost_at=circ.b.ops.len();
    if low{super::q793_t10_expand_v11::flags(circ,rank,a,c,g,&sm[1],&sm[2],dirty);super::q792_t10_dirtyq1_r01::emit(circ,rank,a,c,sm,p1,p2,g,w1,w2,dirty,j,false,last);}
    cost(circ,&mut cost_at,last,low,"guard+decode");
    let mut source:Vec<_>=w1[..256].iter().map(QReg::borrowed_alias).collect();if low{source.push(sm[3].borrowed_alias());}
    move_g(circ,rank,a,g,&source,w2,dirty);
    if last{
        super::q792_t10_nocache_r01::add_and_clear(circ,rank,&source,w2,a,g,&c[2],&c[1],&c[0],dirty,n,c,sm,j,true,low);circ.cx(g,&c[0]);
    }else{
        let mask=&dirty[0];let rest=&dirty[1..];circ.cx(g,p1);
        if low{super::q793_t10_routes_v12::pop_and_mask(circ,rank,a,c,g,p1,mask,&sm[2],&sm[0],&source,w2,rest);}
        else{let carry=&rest[0];let tail=&rest[1..];top_lease(circ,rank,a,g,carry,&source,tail);super::q793_t10_routes_v12::exchanges(circ,rank,a,c,g,&[p1,mask],&source,tail,carry,None);top_lease(circ,rank,a,g,carry,&source,tail);}
        super::q792_t10_nocache_r01::add_and_clear(circ,rank,&source,w2,a,g,p2,mask,p1,rest,n,c,sm,j,false,low);
        if low{super::q793_t10_routes_v12::mask_return(circ,rank,a,c,g,mask,&sm[2],&sm[0],&source,w2,rest);}
        else{let carry=&rest[0];let tail=&rest[1..];top_lease(circ,rank,a,g,carry,&source,tail);super::q793_t10_routes_v12::exchanges(circ,rank,a,c,g,&[mask],&source,tail,carry,None);top_lease(circ,rank,a,g,carry,&source,tail);}
        circ.cx(g,p1);
    }
    move_g(circ,rank,a,g,&source,w2,dirty);
    cost(circ,&mut cost_at,last,low,"arithmetic");
    if low{super::q792_t10_dirtyq1_r01::emit(circ,rank,a,c,sm,p1,p2,g,w1,w2,dirty,j,true,last);super::q793_t10_expand_v11::flags(circ,rank,a,c,g,&sm[1],&sm[2],dirty);}
    cost(circ,&mut cost_at,last,low,"encode+return");
}
fn cost(circ:&Circuit,at:&mut usize,last:bool,low:bool,part:&str){if std::env::var("Q793_T10_COST").ok().as_deref()==Some("1"){let ops=&circ.b.ops[*at..];let t=ops.iter().filter(|o|o.kind==crate::circuit::OperationType::CCX).count();eprintln!("Q793_T10_V13_COST last={last} low={low} part={part} ops={} T={t}",ops.len());}*at=circ.b.ops.len();}
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],helpers:&[QReg],n:usize,j:usize){
    assert_eq!(helpers.len(),23);assert!(j<4);let owned=circ.b.next_qubit;let start=circ.b.ops.len();
    // Every branch restores g=0 and its original passenger at the same
    // A-addressed source top. Hold this one loan across all four branches.
    super::q793_loans::global_a(circ,rank,a,&helpers[0],w1,&w2[258],None,&helpers[1..]);
    let g=&helpers[0];let dirty=&helpers[1..];
    // Every body restores phase/rank/A/C/SM and keeps its held g. Therefore
    // adjacent erase/recompute guards may be replaced by their Boolean XOR.
    // Let C=[C1], L=[Ssmall], H=1+L, under phase10.
    guard_delta(circ,rank,c,sm,p1,p2,g,dirty,j,2|8); // HC=C+LC
    branch(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,n,j,true,false);
    guard_delta(circ,rank,c,sm,p1,p2,g,dirty,j,1|4); // HC -> H(1+C)
    branch(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,n,j,false,false);
    if j==3{
        // C1 implies S mod4=3 at clock3, so LC is identically zero.
        guard_delta(circ,rank,c,sm,p1,p2,g,dirty,j,1|2); // H(1+C) -> L
    }else{
        guard_delta(circ,rank,c,sm,p1,p2,g,dirty,j,1|2|4); // H(1+C) -> LC
        branch(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,n,j,true,true);
        guard_delta(circ,rank,c,sm,p1,p2,g,dirty,j,4); // LC -> L(1+C)
    }
    branch(circ,rank,a,c,sm,p1,p2,w1,w2,helpers,n,j,false,true);
    guard_delta(circ,rank,c,sm,p1,p2,g,dirty,j,4|8); // L(1+C) ->0

    super::q793_loans::global_a(circ,rank,a,&helpers[0],w1,&w2[258],None,&helpers[1..]);
    assert_eq!(circ.b.next_qubit,owned);
    for op in &circ.b.ops[start..]{for h in [256,257,258]{let q=w1[h].id()as u64;assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"T10 V13 touched omitted W1[{h}]");}}
    let mut tail=circ.b.ops.split_off(start);super::shared_optimize::cancel_nct(&mut tail,2048,8);super::shared_optimize::cancel_nct_live(&mut tail,2048);circ.b.ops.extend(tail);
}

fn top_lease(circ:&mut Circuit,rank:&[QReg],a:&[QReg],g:&QReg,carry:&QReg,source:&[QReg],d:&[QReg]){let(root,ops)=super::q794_handoffs::gather_a(circ,rank,a,source,1,d);circ.cswap(g,root,carry);circ.b.ops.extend(ops.into_iter().rev());}
