//! T11 target-top loan from bit_length(u)+C<=257. No extra physical wire.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
fn gather<'a>(circ:&mut Circuit,rank:&[QReg],c:&[QReg],cache:&QReg,word:&'a[QReg],dirty:&[QReg])->(&'a QReg,Vec<crate::circuit::Op>){
    let start=circ.b.ops.len();let mut nodes=vec![None;512];for value in 1..=257{nodes[value]=Some(&word[257-value]);}
    let ts:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    for level in 0..9{let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(l),Some(r))=>{if level<6{circ.cswap(&c[level],l,r);}else{
            let controls:Vec<_>=rank.iter().chain(std::iter::once(cache)).collect();let truth:Vec<_>=(0..64).map(|v|((ts[v&31][1]+ts[v&31][2]+(v>>5))>>(level-6))&1!=0).collect();
            super::metadata_muxlease::truth_swap(circ,&controls,truth,l,r,dirty);
        }Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
    });}nodes=next;}
    (nodes[0].unwrap(),circ.b.ops[start..].to_vec())
}
pub(super) fn move_cargo(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    let(left,l)=super::q798_handoffs::gather_a(circ,rank,a,w1,2,dirty);
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);
    let(right,r)=gather(circ,rank,c,cache,w2,dirty);circ.cswap(g,left,right);circ.b.ops.extend(r.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);circ.b.ops.extend(l.into_iter().rev());
}
pub(super) fn top_flag(circ:&mut Circuit,rank:&[QReg],c:&[QReg],sm:&[QReg],g:&QReg,cache:&QReg,flag:&QReg,w1:&[QReg],dirty:&[QReg],j:usize){
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,false);
    let(root,ops)=gather(circ,rank,c,cache,w1,dirty);circ.ccx(g,root,flag);circ.b.ops.extend(ops.into_iter().rev());
    super::metadata_phase115_phased::prepare(circ,c,sm,g,Some(cache),dirty,j,true);
}
