//! Exact prepared folded-rank high-sum swaps. Every64-state input is supported.
//! Temporary MAJ transforms three existing input bits and restores them.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::point_add::trailmix_port::inversion::length_recompute::mixed_mcx;

fn controlled_swap(circ:&mut Circuit,controls:&[(&QReg,bool)],left:&QReg,right:&QReg,dirty:&[QReg]){
    circ.cx(right,left);let mut cs=controls.to_vec();cs.push((left,true));mixed_mcx(circ,&cs,right,dirty);circ.cx(right,left);
}


fn majority(circ:&mut Circuit,a:&QReg,b:&QReg,c:&QReg,body:impl FnOnce(&mut Circuit,&QReg)){
    let start=circ.b.ops.len();circ.cx(a,b);circ.cx(a,c);circ.ccx(b,c,a);let compute=circ.b.ops[start..].to_vec();body(circ,a);circ.b.ops.extend(compute.into_iter().rev());
}
pub(crate) fn swap(circ:&mut Circuit,rank:&[QReg],carry:&QReg,bit:usize,left:&QReg,right:&QReg,dirty:&[QReg]){
    assert_eq!(rank.len(),5);assert!(bit<3&&dirty.len()>=4);
    let mut ids:Vec<_>=rank.iter().chain(dirty).map(QReg::id).collect();ids.extend([carry.id(),left.id(),right.id()]);ids.sort_unstable();assert!(ids.windows(2).all(|p|p[0]!=p[1]),"folded sum swap aliases");
    let(a,b,c,d,e)=(&rank[0],&rank[1],&rank[2],&rank[3],&rank[4]);
    match bit{
        0=>{
            if std::env::var("Q794_SIGN_SUM_PARITY").ok().as_deref()==Some("1"){
                circ.cx(c,carry);circ.cx(e,carry);circ.cswap(carry,left,right);circ.cx(e,carry);circ.cx(c,carry);
            }else{circ.cswap(c,left,right);circ.cswap(e,left,right);circ.cswap(carry,left,right);}
        },
        1=>{
            circ.cswap(d,left,right);
            circ.cx(c,e);controlled_swap(circ,&[(carry,true),(e,true)],left,right,dirty);circ.cx(c,e);
            controlled_swap(circ,&[(a,true),(b,true),(d,true),(c,false),(e,false)],left,right,dirty);
            majority(circ,a,b,d,|circ,m|controlled_swap(circ,&[(c,true),(e,true),(m,false)],left,right,dirty));
        },
        2=>{
            controlled_swap(circ,&[(a,true),(b,true),(d,true),(c,false),(e,false)],left,right,dirty);
            majority(circ,a,b,d,|circ,m|controlled_swap(circ,&[(c,true),(e,true),(m,true)],left,right,dirty));
            majority(circ,c,e,carry,|circ,m|controlled_swap(circ,&[(d,true),(m,true)],left,right,dirty));
        },_=>unreachable!(),
    }
}
