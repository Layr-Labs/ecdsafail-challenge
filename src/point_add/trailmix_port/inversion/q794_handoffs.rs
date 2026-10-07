//! Own physically pruned selector; omitted word suffix has no tree leaves.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
pub(super) fn gather_a<'a>(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&'a[QReg],offset:usize,dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    let start=circ.b.ops.len();let(lo,hi)=circ.q797_a_support.unwrap_or((0,256));assert!(lo<hi&&hi<=256);
    let mut nodes:Vec<_>=(0..256).map(|v|if v+offset<word.len()&&((lo..hi).contains(&v)||v==255)&&!(offset==3&&v==255){Some(&word[v+offset])}else{None}).collect();
    for level in 0..8{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(left),Some(right))=>{if level<6{circ.cswap(&a[level],left,right);}else{super::metadata_muxlease::predicate_swap(circ,rank,0,level-6,left,right,dirty);}Some(left)},
        (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    let root=nodes[0].expect("nonempty physical selector");let ops=circ.b.ops[start..].to_vec();super::q792_passive_r01::gather(circ,&ops,word,offset,root);(root,ops)
}
