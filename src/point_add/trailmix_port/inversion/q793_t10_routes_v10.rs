//! V10 semantic XOR readout. The address is restored before the center.
//! Held phase10 lends its two phase bits as clean semantic data readouts.
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
/// A16+A12 consumer-window leaf cut on the 9e4cfaf (A11-on-W45) body.
/// Default ON; Q793_A12_V12=0 / Q793_A16_V10=0 restore the parent v10 trees.
/// Cap M=A+C at min(2*A_hi-7,255)==min(4b+3,255); floor at block A_lo.
/// Dropped leaves are off the live address; routing cancels with its inverse.
fn leaf_window(circ:&Circuit)->(usize,usize){
    let mut w=(0usize,255usize);
    if let Some((lo,hi))=circ.q797_a_support{
        if std::env::var("Q793_A12_V12").ok().as_deref()!=Some("0"){w.0=lo.min(255);}
        if std::env::var("Q793_A16_V10").ok().as_deref()!=Some("0"){w.1=(2*hi).saturating_sub(7).min(255);}
    }
    w
}
fn leaf_nodes<'a>(circ:&Circuit,w1:&'a[QReg],offset:isize)->Vec<Option<&'a QReg>>{
    let w=leaf_window(circ);
    let mut nodes:Vec<_>=(0..256).map(|s|{let i=s as isize+offset;if(3..=255).contains(&i)&&s>=w.0&&s<=w.1{Some(&w1[i as usize])}else{None}}).collect();
    // Rail trap: an empty window retains the minimum shipped leaf (a lone leaf
    // emits no routing at all), keeping the tree root well formed.
    if nodes.iter().all(|n|n.is_none()){let s0=(3-offset).max(0)as usize;nodes[s0]=Some(&w1[(s0 as isize+offset)as usize]);}
    nodes
}
pub(super) fn digit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],w1:&[QReg],out:&QReg,helpers:&[QReg],offset:isize,controls:&[(&QReg,bool)],g:&QReg,carry:&QReg){
    assert!((-1..=1).contains(&offset));assert!(controls.iter().any(|&(q,v)|q.id()==g.id()&&v));let start=circ.b.ops.len();
    add(circ,a,c,Some(carry),false);
    let mut nodes=leaf_nodes(circ,w1,offset);
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&c[level],left,right);}else{high_swap(circ,rank,carry,g,level-6,left,right);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let root=nodes[0].unwrap();let route=circ.b.ops[start..].to_vec();
    circ.cx(root,out);let mut cs=controls.to_vec();cs.push((out,true));super::q794_t10_quotient::gate(circ,&cs,root,helpers);circ.cx(root,out);
    circ.b.ops.extend(route.into_iter().rev());
}


/// XOR a selected physical digit into out under a metadata polynomial.
/// Restore the address and carry before the center so each term sees the
/// original C and carry=0 on g. Off g every center term is identity and
/// the arbitrary routing unitary cancels with its literal inverse.
pub(super) fn digit_xor(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],w1:&[QReg],out:&QReg,helpers:&[QReg],offset:isize,controls:&[Vec<(&QReg,bool)>],g:&QReg,carry:&QReg){
    assert!((-1..=1).contains(&offset));let start=circ.b.ops.len();
    add(circ,a,c,Some(carry),false);
    let mut nodes=leaf_nodes(circ,w1,offset);
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&c[level],left,right);}else{high_swap(circ,rank,carry,g,level-6,left,right);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let root=nodes[0].unwrap();
    add(circ,a,c,Some(carry),true);
    let route=circ.b.ops[start..].to_vec();
    for term in controls{
        assert!(term.iter().any(|&(q,v)|q.id()==g.id()&&v));
        let mut others:Vec<_>=term.iter().copied().filter(|(q,_)|q.id()!=g.id()).collect();others.push((root,true));
        super::conditional_mcx::guarded(circ,g,&others,out,carry,false,&helpers[0]);
    }
    circ.b.ops.extend(route.into_iter().rev());
}
