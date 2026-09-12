//! Exact indexed cargo handoffs. No quantum allocation or measurement.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{metadata_muxlease as mux,length_recompute::mixed_mcx};
fn triples()->Vec<[usize;3]>{(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect()}
pub(super) fn gather_a<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&'a[QReg],offset:usize,dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    let start=circ.b.ops.len();
    if let Some((lo,hi))=circ.q797_a_support {
        assert!(lo<hi&&hi<=256);
        // Retain terminal A255 even for early-block synthetic terminal tests.
        // Offset3 is only selected by nonterminal C1/newborn cargo guards.
        // The impossible terminal leaf would otherwise touch the omitted r0.
        let mut nodes:Vec<_>=(0..256).map(|v|if ((lo..hi).contains(&v)||v==255)&&!(super::q796_parity::enabled()&&offset==3&&v==255){Some(&word[v+offset])}else{None}).collect();
        for level in 0..8 {
            let mut next=Vec::new();
            for pair in nodes.chunks_exact(2) {next.push(match(pair[0],pair[1]){
                (Some(left),Some(right))=>{
                    if level<6{circ.cswap(&a[level],left,right);}
                    else{mux::predicate_swap(circ,rank,0,level-6,left,right,dirty);}
                    Some(left)
                },
                (Some(q),None)|(None,Some(q))=>Some(q),
                (None,None)=>None,
            });}
            nodes=next;
        }
        return (nodes[0].unwrap(),circ.b.ops[start..].to_vec());
    }
    for level in 0..8{let d=1<<level;for base in (0..256).step_by(2*d){
        if level<6{circ.cswap(&a[level],&word[base+offset],&word[base+d+offset]);}
        else{mux::predicate_swap(circ,rank,0,level-6,&word[base+offset],&word[base+d+offset],dirty);}
    }}
    (&word[offset],circ.b.ops[start..].to_vec())
}
pub(super) fn move_t10(circ:&mut Circuit,rank:&[QReg],a:&[QReg],p1:&QReg,p2:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg]){
    let(left,l)=gather_a(circ,rank,a,w1,1,dirty);let(right,r)=gather_a(circ,rank,a,w2,2,dirty);
    circ.cx(right,left);mixed_mcx(circ,&[(p1,true),(p2,false),(left,true)],right,dirty);circ.cx(right,left);
    circ.b.ops.extend(r.into_iter().rev());circ.b.ops.extend(l.into_iter().rev());
}
/// g is the recoded phase11 enable; cache is zero under g before this call.
/// C+S is interpreted literally (S0 means zero, not 256). Active C>=1.
pub(super) fn move_t11(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);
    let start=circ.b.ops.len();let mut nodes=vec![None;512];
    for value in 1..=257{nodes[value]=Some(&w2[258-value]);}
    for level in 0..9{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&c[level],left,right);}else{
            let ts=triples();let ctrls:Vec<_>=rank.iter().chain(std::iter::once(cache)).collect();
            let truth:Vec<_>=(0..64).map(|r|((ts[r&31][1]+ts[r&31][2]+(r>>5))>>(level-6))&1!=0).collect();
            mux::truth_swap(circ,&ctrls,truth,left,right,dirty);
        }Some(left)},(Some(x),None)|(None,Some(x))=>Some(x),(None,None)=>None,
    });}nodes=next;}
    let right=nodes[0].unwrap();let r=circ.b.ops[start..].to_vec();
    let(left,l)=gather_a(circ,rank,a,w1,1,dirty);circ.cswap(g,left,right);
    circ.b.ops.extend(l.into_iter().rev());circ.b.ops.extend(r.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);
}
