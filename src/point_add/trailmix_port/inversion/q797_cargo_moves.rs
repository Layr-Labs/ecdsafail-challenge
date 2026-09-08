//! Indexed cargo movement without allocating a quantum wire.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
/// Between different words their independent selection permutations cannot alias.
pub(super) fn across_a_terms(circ:&mut Circuit,rank:&[QReg],a:&[QReg],left_word:&[QReg],left_offset:usize,right_word:&[QReg],right_offset:usize,terms:&[Vec<(&QReg,bool)>],flip_left:bool,dirty:&[QReg]) {
    let(left,l)=super::q798_handoffs::gather_a(circ,rank,a,left_word,left_offset,dirty);
    let(right,r)=super::q798_handoffs::gather_a(circ,rank,a,right_word,right_offset,dirty);
    circ.cx(right,left);
    for term in terms{let mut cs=term.clone();cs.push((left,true));mixed_mcx(circ,&cs,right,dirty);}
    circ.cx(right,left);
    if flip_left{for term in terms{mixed_mcx(circ,term,left,dirty);}}
    circ.b.ops.extend(r.into_iter().rev());circ.b.ops.extend(l.into_iter().rev());
}
pub(super) fn flip_a_terms(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&[QReg],offset:usize,terms:&[Vec<(&QReg,bool)>],dirty:&[QReg]) {
    let(root,ops)=super::q798_handoffs::gather_a(circ,rank,a,word,offset,dirty);
    for term in terms{mixed_mcx(circ,term,root,dirty);}circ.b.ops.extend(ops.into_iter().rev());
}
pub(super) fn exchange_a_terms(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&[QReg],offset:usize,passenger:&QReg,terms:&[Vec<(&QReg,bool)>],dirty:&[QReg]) {
    exchange_a_terms_inner(circ,rank,a,word,offset,passenger,terms,dirty,false);
}
fn exchange_a_terms_inner(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&[QReg],offset:usize,passenger:&QReg,terms:&[Vec<(&QReg,bool)>],dirty:&[QReg],flip_root:bool) {
    let(root,ops)=super::q798_handoffs::gather_a(circ,rank,a,word,offset,dirty);
    circ.cx(passenger,root);
    for term in terms {let mut cs=term.clone();cs.push((root,true));mixed_mcx(circ,&cs,passenger,dirty);}
    circ.cx(passenger,root);if flip_root{for term in terms{mixed_mcx(circ,term,root,dirty);}}circ.b.ops.extend(ops.into_iter().rev());
}
pub(super) fn adjacent_a_terms_flip(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&[QReg],from:usize,to:usize,terms:&[Vec<(&QReg,bool)>],helpers:&[QReg]) {
    assert_ne!(from,to);let shuttle=&helpers[0];let dirty=&helpers[1..];
    exchange_a_terms(circ,rank,a,word,from,shuttle,terms,dirty);
    exchange_a_terms(circ,rank,a,word,to,shuttle,terms,dirty);
    exchange_a_terms_inner(circ,rank,a,word,from,shuttle,terms,dirty,true);
}
pub(super) fn adjacent_a_terms(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&[QReg],from:usize,to:usize,terms:&[Vec<(&QReg,bool)>],helpers:&[QReg]) {
    assert_ne!(from,to);let shuttle=&helpers[0];let dirty=&helpers[1..];
    exchange_a_terms(circ,rank,a,word,from,shuttle,terms,dirty);
    exchange_a_terms(circ,rank,a,word,to,shuttle,terms,dirty);
    exchange_a_terms(circ,rank,a,word,from,shuttle,terms,dirty);
}
pub(super) fn exchange_a(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&[QReg],offset:usize,passenger:&QReg,controls:&[(&QReg,bool)],dirty:&[QReg]) {
    let(root,ops)=super::q798_handoffs::gather_a(circ,rank,a,word,offset,dirty);
    circ.cx(passenger,root);let mut cs=controls.to_vec();cs.push((root,true));
    mixed_mcx(circ,&cs,passenger,dirty);circ.cx(passenger,root);
    circ.b.ops.extend(ops.into_iter().rev());
}
/// Three exchanges avoid aliasing two overlapping gathers in the same word.
pub(super) fn adjacent_a(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&[QReg],from:usize,to:usize,controls:&[(&QReg,bool)],helpers:&[QReg]) {
    assert_ne!(from,to);let shuttle=&helpers[0];let dirty=&helpers[1..];
    exchange_a(circ,rank,a,word,from,shuttle,controls,dirty);
    exchange_a(circ,rank,a,word,to,shuttle,controls,dirty);
    exchange_a(circ,rank,a,word,from,shuttle,controls,dirty);
}
