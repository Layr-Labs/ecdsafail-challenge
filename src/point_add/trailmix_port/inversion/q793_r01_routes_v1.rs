//! R01 selectors with one actual carry loan and an exact guarded center.
//! carry must be zero only on g. All routing wires restore for arbitrary
//! off-guard metadata/work/carry because the complete route is reversed.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::metadata_arithmetic5::add;
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
/// A+C-addressed physical W1[M+offset] for the normal M<=253 domain.
/// Any A support lower bound also bounds M; empty active late domains retain
/// one arbitrary leaf so the enclosing off-guard identity stays well formed.
pub(super) fn gather<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],w1:&'a[QReg],g:&QReg,carry:&QReg,offset:usize)->(&'a QReg,Vec<crate::circuit::Op>){
    assert!(offset<=2);assert_eq!(w1.len(),259);let start=circ.b.ops.len();
    let lo=circ.q797_a_support.map_or(0,|(lo,_)|lo.min(253));
    add(circ,a,c,Some(carry),false);
    let mut nodes:Vec<_>=(0..256).map(|m|if(lo..=253).contains(&m){Some(&w1[m+offset])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&c[level],left,right);}else{high_swap(circ,rank,carry,g,level-6,left,right);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    (nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}
pub(super) fn quotient(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],w1:&[QReg],g:&QReg,carry:&QReg,decision:&QReg){
    let(root,route)=gather(circ,rank,a,c,w1,g,carry,2);
    circ.cswap(g,root,decision);circ.b.ops.extend(route.into_iter().rev());
}
