//! V12 arithmetic quotient pop/mask route with an existing conditional-zero carry.
//! Low S uses SM0 and the already-live SM2 endpoint flag; high S uses phase P2.
//! The unchanged fused arithmetic restores both lenders before mask return.
//! carry=0 is required only on g. The complete center is guarded by g;
//! off g the routing unitary and its literal inverse cancel for arbitrary data.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::metadata_arithmetic5_encoded::add;
fn high_swap(circ:&mut Circuit,rank:&[QReg],carry:&QReg,g:&QReg,bit:usize,left:&QReg,right:&QReg){
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let truth:Vec<_>=(0..64).map(|r|((ts[r&31][0]+ts[r&31][1]+(r>>5))>>bit)&1!=0).collect();
    let controls:Vec<_>=rank.iter().chain(std::iter::once(carry)).collect();
    if super::q792_esop_r01::active(){circ.cx(right,left);circ.x(g);super::q792_esop_r01::paired(circ,&controls,truth,&[(left,true)],right,g);circ.x(g);circ.cx(right,left);return;}
    let(polarity,terms)=super::metadata_muxlease::swap_terms(truth,6);
    for(i,q)in controls.iter().enumerate(){if polarity>>i&1!=0{circ.x(q);}}
    circ.cx(right,left);circ.x(g);
    // On original g1, X(g) supplies a clean scratch. Off g this is only
    // part of the arbitrary routing unitary, undone before the boundary.
    for m in terms{let mut cs=vec![(left,true)];cs.extend((0..6).filter(|&i|m>>i&1!=0).map(|i|(controls[i],true)));super::paired_clean_mcx::toggle(circ,&cs,right,g);}
    circ.x(g);circ.cx(right,left);
    for(i,q)in controls.iter().enumerate().rev(){if polarity>>i&1!=0{circ.x(q);}}
}

pub(super) fn exchanges(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,passengers:&[&QReg],source:&[QReg],helpers:&[QReg],carry:&QReg,endpoint:Option<&QReg>){
    let start=circ.b.ops.len();add(circ,a,c,Some(carry),false);
    let hi=if endpoint.is_some(){256}else{254};assert!(source.len()>hi);
    let mut nodes:Vec<_>=(0..256).map(|s|if s!=0&&s+1<=hi{Some(&source[s+1])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&c[level],left,right);}else{high_swap(circ,rank,carry,g,level-6,left,right);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let root=nodes[0].unwrap();let route=circ.b.ops[start..].to_vec();
    for &p in passengers{
        circ.cx(p,root);let mut cs=vec![(g,true),(root,true)];if let Some(e)=endpoint{cs.push((e,false));}
        super::q794_t10_quotient::gate(circ,&cs,p,helpers);circ.cx(p,root);
    }
    circ.b.ops.extend(route.into_iter().rev());
}

pub(super) fn pop_and_mask(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,p:&QReg,mask:&QReg,endpoint:&QReg,carry:&QReg,source:&[QReg],target:&[QReg],dirty:&[QReg]){
    exchanges(circ,rank,a,c,g,&[p,mask],source,dirty,carry,Some(endpoint));
    // Identical endpoint-local map to q794_t10_quotient::pop_and_mask_cached.
    // SM2 already holds g*M256 and stays invariant throughout arithmetic.
    circ.cx(p,&target[1]);super::q794_t10_quotient::gate(circ,&[(g,true),(endpoint,true),(&source[0],false),(&target[1],true)],p,dirty);circ.cx(p,&target[1]);
    super::q794_t10_quotient::gate(circ,&[(g,true),(endpoint,true),(&source[0],true),(&target[0],false)],p,dirty);
    super::q794_t10_quotient::gate(circ,&[(g,true),(endpoint,true)],&target[258],dirty);
    circ.cx(mask,&target[258]);super::q794_t10_quotient::gate(circ,&[(g,true),(endpoint,true),(&target[258],true)],mask,dirty);circ.cx(mask,&target[258]);
}
pub(super) fn mask_return(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,mask:&QReg,endpoint:&QReg,carry:&QReg,source:&[QReg],target:&[QReg],dirty:&[QReg]){
    exchanges(circ,rank,a,c,g,&[mask],source,dirty,carry,Some(endpoint));
    circ.cx(mask,&target[258]);super::q794_t10_quotient::gate(circ,&[(g,true),(endpoint,true),(&target[258],true)],mask,dirty);circ.cx(mask,&target[258]);
    super::q794_t10_quotient::gate(circ,&[(g,true),(endpoint,true)],&target[258],dirty);
}
