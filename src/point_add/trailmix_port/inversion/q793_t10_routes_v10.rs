//! V10 semantic XOR readout. The address is restored before the center.
//! Held phase10 lends its two phase bits as clean semantic data readouts.
//! carry=0 is required only on g. The complete center is guarded by g;
//! off g the routing unitary and its literal inverse cancel for arbitrary data.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::metadata_arithmetic5_encoded::add;
fn high_swap(circ:&mut Circuit,rank:&[QReg],carry:&QReg,g:&QReg,bit:usize,left:&QReg,right:&QReg){
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    let truth:Vec<_>=(0..64).map(|r|((ts[r&31][0]+ts[r&31][1]+(r>>5))>>bit)&1!=0).collect();
    let controls:Vec<_>=rank.iter().chain(std::iter::once(carry)).collect();let(polarity,terms)=super::metadata_muxlease::swap_terms(truth,6);
    for(i,q)in controls.iter().enumerate(){if polarity>>i&1!=0{circ.x(q);}}
    circ.cx(right,left);circ.x(g);
    // On original g1, X(g) supplies a clean scratch. Off g this is only
    // part of the arbitrary routing unitary, undone before the boundary.
    for m in terms{let mut cs=vec![(left,true)];cs.extend((0..6).filter(|&i|m>>i&1!=0).map(|i|(controls[i],true)));super::paired_clean_mcx::toggle(circ,&cs,right,g);}
    circ.x(g);circ.cx(right,left);
    for(i,q)in controls.iter().enumerate().rev(){if polarity>>i&1!=0{circ.x(q);}}
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


/// XOR a selected physical digit into out under a metadata polynomial.
/// Restore the address and carry before the center so each term sees the
/// original C and carry=0 on g. Off g every center term is identity and
/// the arbitrary routing unitary cancels with its literal inverse.
pub(super) fn digit_xor(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],w1:&[QReg],out:&QReg,helpers:&[QReg],offset:isize,controls:&[Vec<(&QReg,bool)>],g:&QReg,carry:&QReg){
    assert!((-1..=1).contains(&offset));let start=circ.b.ops.len();
    add(circ,a,c,Some(carry),false);
    let mut nodes:Vec<_>=(0..256).map(|s|{let i=s as isize+offset;if(3..=255).contains(&i){Some(&w1[i as usize])}else{None}}).collect();
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
