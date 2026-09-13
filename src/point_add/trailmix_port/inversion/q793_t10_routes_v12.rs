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
    let plan=super::metadata_muxlease::swap_plan(truth,6,1,super::metadata_muxlease::McxModel::Clean);
    // On original g1, X(g) supplies a clean scratch. Off g this is only
    // part of the arbitrary routing unitary, undone before the boundary.
    super::metadata_muxlease::emit_plan(circ,&controls,plan,left,right,|circ|{circ.cx(right,left);circ.x(g);},|circ|{circ.x(g);circ.cx(right,left);},|circ,cs,right|{super::paired_clean_mcx::toggle(circ,&cs,right,g);});
}

/// A17+A9a consumer-window leaf cut (W47 research-lane packet; default ON,
/// =0 kills). Same T10 consumer bound as the v10 A16+A12 cut: at the block-b
/// T10 consumer the proved bound M=A+C<=4b+3 caps the tree address and the
/// analytic A support floors it. circ.q797_a_support carries the block's
/// (A_lo,A_hi); floor=max(1,A_lo), cap=min(2*A_hi-7,hi_shipped). Dropped
/// leaves are off the live address, where the routing unitary cancels with
/// its literal inverse, so the cut is an exact identity there.
fn leaf_window(circ:&Circuit,hi:usize)->(usize,usize){
    let mut w=(1usize,hi);
    if let Some((lo,a_hi))=circ.q797_a_support{
        if std::env::var("Q793_A9A_V12").ok().as_deref()!=Some("0"){w.0=lo.max(1).min(255);}
        if std::env::var("Q793_A17_V12").ok().as_deref()!=Some("0"){w.1=(2*a_hi).saturating_sub(7).min(hi);}
    }
    w
}
pub(super) fn exchanges(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],g:&QReg,passengers:&[&QReg],source:&[QReg],helpers:&[QReg],carry:&QReg,endpoint:Option<&QReg>){
    let start=circ.b.ops.len();add(circ,a,c,Some(carry),false);
    let hi=if endpoint.is_some(){256}else{254};assert!(source.len()>hi);
    let w=leaf_window(circ,hi);
    let mut nodes:Vec<_>=(0..256).map(|s|if s!=0&&s+1<=hi&&s>=w.0&&s<=w.1{Some(&source[s+1])}else{None}).collect();
    // Rail trap: an empty window retains the minimum shipped leaf (a lone leaf
    // emits no routing at all), keeping the tree root well formed.
    if nodes.iter().all(|n|n.is_none()){nodes[1]=Some(&source[2]);}
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
