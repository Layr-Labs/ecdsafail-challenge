//! Exact affine endpoint transpositions for active Q794 exit consumers.
//! The unguarded Aupdate frame is paired around the unchanged guard-rooted
//! length maps. Each individual transposition is exact on all 32 inputs.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};

pub(super) fn unguarded_swap(circ:&mut Circuit,rank:&[QReg],helpers:&[QReg],left:usize,right:usize){
    assert_eq!(rank.len(),5);assert!(left<32&&right<32&&left!=right);assert!(helpers.len()>=2);
    let mut ids:Vec<_>=rank.iter().chain(&helpers[..2]).map(QReg::id).collect();ids.sort_unstable();assert!(ids.windows(2).all(|w|w[0]!=w[1]),"unguarded affine lender alias");
    let diff=left^right;let pivot=diff.trailing_zeros()as usize;let targets:Vec<_>=(0..5).filter(|&i|i!=pivot&&diff>>i&1!=0).collect();let mut value=left;
    for &i in &targets{circ.cx(&rank[pivot],&rank[i]);if left>>pivot&1!=0{value^=1<<i;}}
    let cs:Vec<_>=(0..5).filter(|&i|i!=pivot).map(|i|(&rank[i],value>>i&1!=0)).collect();
    super::length_recompute::mixed_mcx(circ,&cs,&rank[pivot],helpers);
    for &i in targets.iter().rev(){circ.cx(&rank[pivot],&rank[i]);}
}
