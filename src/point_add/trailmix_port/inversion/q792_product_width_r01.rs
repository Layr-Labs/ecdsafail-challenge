//! Two paid head probes replace coefficient/residual full length scans only
//! at the ordinary S=0 exit, where p=t*r+tprime*rprime, 0<=r<rprime and
//! 0<t<=tprime prove p/2<tprime*rprime<=p. No allocation or free address.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::super::length_recompute::mixed_mcx;

fn eq<'a>(address:&'a [QReg], value:usize, guard:&'a QReg)->Vec<(&'a QReg,bool)>{
    std::iter::once((guard,true)).chain(address.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0))).collect()
}

// Sparse mux routes are restored literally. Missing addresses are explicitly
// cancelled, because dropping a leaf alone does NOT give a zero oracle.
fn gather(c:&mut Circuit, address:&[QReg], bank:Vec<Option<&QReg>>, guard:&QReg, flag:&QReg, dirty:&[QReg]){
    assert_eq!(address.len(),8);assert_eq!(bank.len(),256);
    let missing:Vec<_>=bank.iter().enumerate().filter_map(|(v,q)|q.is_none().then_some(v)).collect();
    let at=c.b.ops.len();let mut nodes=bank;
    for q in address {let mut next=Vec::new();for pair in nodes.chunks_exact(2){next.push(match(pair[0],pair[1]){
        (Some(l),Some(r))=>{c.cswap(q,l,r);Some(l)},(Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None});}nodes=next;}
    let route=c.b.ops[at..].to_vec();let root=nodes[0].unwrap();c.ccx(guard,root,flag);
    for value in missing{let mut cs=eq(address,value,guard);cs.push((root,true));mixed_mcx(c,&cs,flag,dirty);}
    c.b.ops.extend(route.into_iter().rev());
}

fn coefficient_probe(c:&mut Circuit,boundary:&[QReg],source:&[QReg],guard:&QReg,flag:&QReg,dirty:&[QReg],high:bool){
    gather(c,boundary,(0..256).map(|v|if v>=1&&(high||v<255){Some(&source[if high{256-v}else{255-v}])}else{None}).collect(),guard,flag,dirty);
    if !high{mixed_mcx(c,&eq(boundary,255,guard),flag,dirty);}
}
fn residual_probe(c:&mut Circuit,boundary:&[QReg],source:&[QReg],prefix:&[QReg],guard:&QReg,flag:&QReg,dirty:&[QReg],high:bool){
    let shift=if high{3}else{4};
    gather(c,boundary,(0..256).map(|v|if v+shift<=255{Some(&source[v+shift])}else{None}).collect(),guard,flag,dirty);
    let chart=[&source[0],&source[1],&source[2],&prefix[0],&prefix[1],&prefix[2],&prefix[258],&prefix[257],&prefix[256]];
    let a:Vec<_>=boundary.iter().collect();
    for bit in 1..=2 {let value=258-bit-shift;super::super::q793_exit_low::xor_r(c,chart,&a,bit,&eq(boundary,value,guard),flag,dirty);}
    // Nonzero residual has bit-length one whenever neither higher bit is set.
    mixed_mcx(c,&eq(boundary,258-shift,guard),flag,dirty);
}

// Fixed secp p excludes L+C=255: the maximal product in that case is
// 2^255-2^127-2^128+1 < p/2. Thus A_new+C_old is 255 or256.
// A_old has first been erased by the original complete length scan. Swap
// the old C into the now-zero A bank, complement it, then conditionally add1.
// H is held on the existing P1 rail through all intervening cargo moves.
pub(super) fn coefficient_hold(c:&mut Circuit,boundary:&[QReg],out:&[QReg],source:&[QReg],guard:&QReg,high:&QReg,dirty:&[QReg]){
    coefficient_probe(c,boundary,source,guard,high,dirty,true);
    for bit in 0..8{c.cswap(guard,&boundary[bit],&out[bit]);c.cx(guard,&out[bit]);}
    for bit in (0..8).rev(){let mut cs=vec![(guard,true),(high,true)];cs.extend(out[..bit].iter().map(|q|(q,true)));mixed_mcx(c,&cs,&out[bit],dirty);}
}
pub(in super::super) fn residual_finish(c:&mut Circuit,boundary:&[QReg],_out:&[QReg],source:&[QReg],prefix:&[QReg],guard:&QReg,high:&QReg,dirty:&[QReg]){
    residual_probe(c,boundary,source,prefix,guard,high,dirty,true);
}
