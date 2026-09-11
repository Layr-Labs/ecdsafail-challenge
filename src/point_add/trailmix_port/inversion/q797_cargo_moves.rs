//! Indexed cargo movement without allocating a quantum wire.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
/// Gather each endpoint from disjoint residue classes. For a fixed low-address
/// residue the two trees never share a data wire, so both roots may stay live.
/// Every tree is undone before moving to the next residue. No clean scratch is
/// assumed, and each residue control is retained on the central exchange.
fn paired_a_terms(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&[QReg],from:usize,to:usize,terms:&[Vec<(&QReg,bool)>],dirty:&[QReg],flip:bool) {
    // Both whole endpoint supports stay live. Lenders and central controls
    // therefore exclude the entire data word, not merely the two roots.
    for q in dirty {
        assert!(!word.iter().chain(rank).chain(a).any(|p|p.id()==q.id()));
        assert!(!terms.iter().flatten().any(|&(p,_)|p.id()==q.id()));
    }
    assert!(!terms.iter().flatten().any(|&(q,_)|word.iter().any(|p|p.id()==q.id())));
    let bits=from.abs_diff(to).trailing_zeros() as usize+1;
    assert!(bits<=6);
    let stride=1usize<<bits;
    let (lo,hi)=circ.q797_a_support.unwrap_or((0,256));
    for residue in 0..stride {
        let start=circ.b.ops.len();let mut roots=Vec::new();
        for offset in [from,to] {
            let mut nodes:Vec<_>=(residue..256).step_by(stride).map(|v|{
                if ((lo..hi).contains(&v)||v==255)&&!(super::q796_parity::enabled()&&(from==3||to==3)&&v==255){Some(&word[v+offset])}else{None}
            }).collect();
            for level in bits..8 {
                let mut next=Vec::new();
                for pair in nodes.chunks_exact(2) {next.push(match(pair[0],pair[1]){
                    (Some(left),Some(right))=>{
                        if level<6{circ.cswap(&a[level],left,right);}else{super::metadata_muxlease::predicate_swap(circ,rank,0,level-6,left,right,dirty);}
                        Some(left)
                    },
                    (Some(q),None)|(None,Some(q))=>Some(q),(None,None)=>None,
                });}nodes=next;
            }
            roots.push(nodes[0]);
        }
        let route=circ.b.ops[start..].to_vec();
        if let (Some(left),Some(right))=(roots[0],roots[1]) {
            let mut controls=Vec::new();
            for term in terms {
                let mut cs=term.clone();let mut valid=true;
                for i in 0..bits {
                    let value=residue>>i&1!=0;
                    if let Some(&(_,v))=cs.iter().find(|&&(q,_)|q.id()==a[i].id()){if v!=value{valid=false;break;}}
                    else{cs.push((&a[i],value));}
                }
                if valid{controls.push(cs);}
            }
            circ.cx(right,left);
            for term in &controls{let mut cs=term.clone();cs.push((left,true));mixed_mcx(circ,&cs,right,dirty);}
            circ.cx(right,left);
            if flip{for term in &controls{mixed_mcx(circ,term,left,dirty);}}
        }
        circ.b.ops.extend(route.into_iter().rev());
    }
}
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
    if super::metadata_muxlease::active("Q795_CARGO_PAIR"){paired_a_terms(circ,rank,a,word,from,to,terms,helpers,true);return;}
    assert_ne!(from,to);let shuttle=&helpers[0];let dirty=&helpers[1..];
    exchange_a_terms(circ,rank,a,word,from,shuttle,terms,dirty);
    exchange_a_terms(circ,rank,a,word,to,shuttle,terms,dirty);
    exchange_a_terms_inner(circ,rank,a,word,from,shuttle,terms,dirty,true);
}
pub(super) fn adjacent_a_terms(circ:&mut Circuit,rank:&[QReg],a:&[QReg],word:&[QReg],from:usize,to:usize,terms:&[Vec<(&QReg,bool)>],helpers:&[QReg]) {
    if super::metadata_muxlease::active("Q795_CARGO_PAIR"){paired_a_terms(circ,rank,a,word,from,to,terms,helpers,false);return;}
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
    if super::metadata_muxlease::active("Q795_CARGO_PAIR"){paired_a_terms(circ,rank,a,word,from,to,&[controls.to_vec()],helpers,false);return;}
    assert_ne!(from,to);let shuttle=&helpers[0];let dirty=&helpers[1..];
    exchange_a(circ,rank,a,word,from,shuttle,controls,dirty);
    exchange_a(circ,rank,a,word,to,shuttle,controls,dirty);
    exchange_a(circ,rank,a,word,from,shuttle,controls,dirty);
}
