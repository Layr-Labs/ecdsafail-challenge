//! Normal-domain quotient routes: 2<=A<=252, 1<=C, A+C<=254.
//! No statement is made about active inputs outside that domain. Offguard
//! maps are exact identity. All emitted W1 leaves are physical indices<=255.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_arithmetic5_encoded::add,metadata_muxlease as mux};
fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
fn route<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],w1:&'a[QReg],helpers:&[QReg],offset:usize)->(&'a QReg,Vec<crate::circuit::Op>){
    assert!(helpers.len()>=18&&offset<=1);let start=circ.b.ops.len();add(circ,a,c,None,false);let d=&helpers[0];let dirty=&helpers[1..];
    // For offset0 these leaves deliberately exclude source low t[0..3).
    // Low-borrow predicates may read t while the higher quotient route is live.
    let mut nodes:Vec<_>=(0..256).map(|s|if(3..=254).contains(&s){Some(&w1[s+offset])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{
            if level<6{circ.cswap(&c[level],left,right);}else{
                let bit=level-6;let ts=triples();let controls:Vec<_>=rank.iter().chain(std::iter::once(d)).collect();
                let truth:Vec<_>=(0..64).map(|r|((ts[r&31][0]+ts[r&31][1]+(r>>5))>>bit)&1!=0).collect();
                add(circ,a,c,None,true);add(circ,a,c,Some(d),false);mux::truth_swap(circ,&controls,truth.clone(),left,right,dirty);
                add(circ,a,c,None,true);add(circ,a,c,Some(d),false);mux::truth_swap(circ,&controls,truth,left,right,dirty);
                let zero:Vec<_>=ts.iter().map(|t|((t[0]+t[1])>>bit)&1!=0).collect();mux::truth_swap(circ,&rank.iter().collect::<Vec<_>>(),zero,left,right,dirty);
            }Some(left)
        },(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    // Restore original C before low-S/C1 predicates inspect it. The literal
    // reverse returned here includes both C translations and all dirty echoes.
    add(circ,a,c,None,true);(nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}
pub(super) fn remaining<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],w1:&'a[QReg],helpers:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){route(circ,rank,a,c,w1,helpers,0)}
pub(super) fn exchanges(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,passengers:&[&QReg],w1:&[QReg],helpers:&[QReg]){
    let(root,ops)=route(circ,rank,a,c,w1,helpers,1);
    for &p in passengers{circ.cswap(g,root,p);}
    circ.b.ops.extend(ops.into_iter().rev());
}
