//! Three-hole passenger transport. Endpoint hosts are phase-local ports.
//! V2 fixes A254 C1 return: the replacement destination is zero, so no flip.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{q792_numeric_moves_r01 as moves,length_recompute::mixed_mcx};
type Terms<'a> = Vec<Vec<(&'a QReg,bool)>>;

fn joined<'a>(left:&[(&'a QReg,bool)],right:&[(&'a QReg,bool)])->Option<Vec<(&'a QReg,bool)>> {
    let mut cs=left.to_vec();
    for &(q,v) in right {
        if let Some(&(_,old))=cs.iter().find(|&&(p,_)|p.id()==q.id()) {
            if old!=v{return None;}
        } else {cs.push((q,v));}
    }
    Some(cs)
}
pub(super) fn at<'a>(a:&'a[QReg],value:usize,terms:&Terms<'a>)->Terms<'a> {
    assert!((253..=255).contains(&value));
    let address:Vec<_>=a.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)).collect();terms.iter().filter_map(|term|joined(term,&address)).collect()
}

fn below253<'a>(a:&'a[QReg],terms:&Terms<'a>)->Terms<'a> {
    let mut out=terms.clone();for value in 253..=255{out.extend(at(a,value,terms));}out
}
fn swap(circ:&mut Circuit,terms:&Terms<'_>,left:&QReg,right:&QReg,dirty:&[QReg]) {
    assert_ne!(left.id(),right.id());
    circ.cx(right,left);
    for term in terms {
        assert!(term.iter().all(|&(q,_)|q.id()!=left.id()&&q.id()!=right.id()));
        let mut cs=term.clone();cs.push((left,true));mixed_mcx(circ,&cs,right,dirty);
    }
    circ.cx(right,left);
}
fn flip(circ:&mut Circuit,terms:&Terms<'_>,target:&QReg,dirty:&[QReg]) {
    for cs in terms {mixed_mcx(circ,cs,target,dirty);}
}

/// Enter the final-digit T10 cargo chart. At A253 the two passengers
/// exchange directly and are already in their final boundary ports.
pub(super) fn inbound(circ:&mut Circuit,a:&[QReg],w1:&[QReg],w2:&[QReg],from:usize,terms:&Terms<'_>,dirty:&[QReg]) {
    assert!(from==0||from==2);
    moves::adjacent_a_terms_flip(circ,a,&w1[..256],from,3,&below253(a,terms),dirty);
    let a253=at(a,253,terms);let a254=at(a,254,terms);
    swap(circ,&a253,&w1[255],&w2[255],dirty);
    if from==0 {swap(circ,&a253,&w1[253],&w2[255],dirty);}
    if from==0 {swap(circ,&a254,&w1[254],&w2[257],dirty);}
    else {swap(circ,&a254,&w2[254],&w2[257],dirty);flip(circ,&a254,&w2[254],dirty);}
}

/// R01 -> T10's leading-digit port. C1 endpoint transport has already
/// completed in inbound, while C>=2 still needs the leading passenger move.
pub(super) fn head_to_two(circ:&mut Circuit,a:&[QReg],c:&[QReg],w1:&[QReg],w2:&[QReg],terms:&Terms<'_>,dirty:&[QReg]) {
    moves::adjacent_a_terms(circ,a,&w1[..256],0,2,&below253(a,terms),dirty);
    // A>=253 implies C_high=0 at an active transition. Cancel C_low=1.
    for av in [253,254] {
        let mut cs=at(a,av,terms);let one:Vec<_>=c.iter().enumerate().map(|(i,q)|(q,i==0)).collect();
        let copy=cs.clone();for term in copy {if let Some(term)=joined(&term,&one){cs.push(term);}}
        if av==253 {swap(circ,&cs,&w1[253],&w1[255],dirty);}
        else {swap(circ,&cs,&w1[254],&w2[255],dirty);flip(circ,&cs,&w1[254],dirty);}
    }
}

