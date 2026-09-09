//! Experimental direct arithmetic on the odd-invariant parity encoding.
//! Not selected by the submitted Q797 circuit; no physical Q796 claim yet.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
pub(crate) fn enabled()->bool{std::env::var("Q796_PARITY").ok().as_deref()==Some("1")}
pub(super) fn cycle_swap(circ:&mut Circuit,t:&QReg,b:&QReg,v:&QReg,g:&QReg,dirty:&[QReg]){
    // Valid q0=0 chart: 4<->1, 6<->5, 3<->7. Excluded0,2 stay fixed.
    // Each transposition uses a Gray path and its reversed interior.
    let word=[t,b,v];
    for (left,right) in [(4usize,1usize),(6,5),(3,7)]{
        let mut value=left;let mut path=Vec::new();
        for bit in 0..3{if (left^right)>>bit&1!=0{path.push((bit,value));value^=1<<bit;}}
        let mut edges=path.clone();edges.extend(path[..path.len()-1].iter().rev().copied());
        for (bit,value) in edges{
            let mut cs=vec![(g,true)];cs.extend((0..3).filter(|&i|i!=bit).map(|i|(word[i],value>>i&1!=0)));
            super::length_recompute::mixed_mcx(circ,&cs,word[bit],dirty);
        }
    }
}
