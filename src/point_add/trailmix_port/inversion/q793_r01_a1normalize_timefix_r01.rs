//! A1/S1 normalizes its b2 donor so all R01 states share one carry scan.
//! At t2,u1: v2=1 XOR r1 XOR qstored0 before and after the decision;
//! erase v2 and park r2 there. At t3, u<3 already makes the b2 donor zero.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
fn gate(circ:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let mut unique:Vec<(&QReg,bool)>=Vec::new();for &(q,v) in cs{assert_ne!(q.id(),out.id());
        if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){if old!=v{return;}}else{unique.push((q,v));}}
    mixed_mcx(circ,&unique,out,dirty);
}
/// Base implies A1/S1. Its possible rank codes are 0,4,8,11, where
/// C_high bit0 = rank2 XOR rank0, bit1 = rank3. Off base U cancels.
pub(super) fn q0_xor(circ:&mut Circuit,rank:&[QReg],c:&[QReg],w1:&[QReg],base:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]){
    let start=circ.b.ops.len();let mut nodes:Vec<_>=(0..256).map(|cv|if cv<=252{Some(&w1[cv+2])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&c[level],left,right);}else if level==6{circ.cswap(&rank[2],left,right);circ.cswap(&rank[0],left,right);}else{circ.cswap(&rank[3],left,right);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let route=circ.b.ops[start..].to_vec();let mut cs=base.to_vec();cs.push((nodes[0].unwrap(),true));gate(circ,&cs,out,dirty);
    cs.extend([(&rank[2],false),(&rank[3],false)]);cs.extend(c.iter().map(|q|(q,false)));gate(circ,&cs,out,dirty);
    circ.b.ops.extend(route.into_iter().rev());
}
fn flag(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,t0:&QReg,j:usize,dirty:&[QReg]){
    // Exact disjoint cover of {0,4,8,11}; the complete active selector
    // implies A1/S1/t2 and therefore normal C<=252 from the held guard.
    for (m,v) in [(27usize,0usize),(31,8),(31,11)]{
        let mut cs=vec![(g,true),(t0,false),(&c[0],j>>1!=0)];
        cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)));
        cs.extend(a.iter().enumerate().map(|(i,q)|(q,i==0)));cs.extend(sm.iter().map(|q|(q,false)));gate(circ,&cs,mask,dirty);
    }
}
/// mask and carry are still the two zero phase loans under g. No carry is
/// needed here. Every action retains g so an arbitrary off-g mask is safe.
pub(super) fn normalize(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,mask:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize,inverse:bool){
    if j&1==0||circ.q797_a_support.is_some_and(|(lo,hi)|!(lo<=1&&1<hi)){return;}
    let start=circ.b.ops.len();flag(circ,rank,a,c,sm,g,mask,&w1[0],j,dirty);
    let base=[(g,true),(mask,true)];gate(circ,&base,&w2[256],dirty);
    gate(circ,&[(g,true),(mask,true),(&w2[1],true)],&w2[256],dirty);
    q0_xor(circ,rank,c,w1,&base,&w2[256],dirty);
    circ.cx(&w2[256],&w2[2]);gate(circ,&[(g,true),(mask,true),(&w2[2],true)],&w2[256],dirty);circ.cx(&w2[256],&w2[2]);
    flag(circ,rank,a,c,sm,g,mask,&w1[0],j,dirty);
    if inverse{circ.b.ops[start..].reverse();}
}
