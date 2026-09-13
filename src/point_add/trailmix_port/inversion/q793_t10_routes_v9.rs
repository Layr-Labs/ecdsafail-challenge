//! V9 codec digit selector with an actual borrowed carry, not dirty carry echoes.
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
pub(super) fn digit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],w1:&[QReg],out:&QReg,helpers:&[QReg],offset:isize,controls:&[(&QReg,bool)],g:&QReg,carry:&QReg){
    assert!((-1..=1).contains(&offset));assert!(controls.iter().any(|&(q,v)|q.id()==g.id()&&v));let start=circ.b.ops.len();
    add(circ,a,c,Some(carry),false);
    let mut nodes:Vec<_>=(0..256).map(|s|{let i=s as isize+offset;if(3..=255).contains(&i){Some(&w1[i as usize])}else{None}}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&c[level],left,right);}else{high_swap(circ,rank,carry,g,level-6,left,right);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let root=nodes[0].unwrap();let route=circ.b.ops[start..].to_vec();
    circ.cx(root,out);let mut cs=controls.to_vec();cs.push((out,true));super::q794_t10_quotient::gate(circ,&cs,root,helpers);circ.cx(root,out);
    circ.b.ops.extend(route.into_iter().rev());
}
