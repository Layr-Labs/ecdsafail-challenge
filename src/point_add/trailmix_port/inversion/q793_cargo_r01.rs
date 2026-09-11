//! Three-hole passenger transport. Endpoint hosts are phase-local ports.
//! Candidate: the composed native boundary/step tests are still required.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::{q794_moves as moves,length_recompute::mixed_mcx};
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
pub(super) fn at<'a>(rank:&'a[QReg],a:&'a[QReg],value:usize,terms:&Terms<'a>)->Terms<'a> {
    assert!((253..=255).contains(&value));
    let mut out=Vec::new();
    // Exact XOR cover of A_high=3 on all32 physical rank codes.
    for term in terms {for (m,v) in [(28usize,28usize),(31,28)] {
        let mut address:Vec<_>=(0..5).filter(|&i|m>>i&1!=0).map(|i|(&rank[i],v>>i&1!=0)).collect();
        address.extend(a.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));
        if let Some(cs)=joined(term,&address){out.push(cs);}
    }}
    out
}
fn below253<'a>(rank:&'a[QReg],a:&'a[QReg],terms:&Terms<'a>)->Terms<'a> {
    let mut out=terms.clone();for value in 253..=255{out.extend(at(rank,a,value,terms));}out
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
pub(super) fn inbound(circ:&mut Circuit,rank:&[QReg],a:&[QReg],w1:&[QReg],w2:&[QReg],from:usize,terms:&Terms<'_>,dirty:&[QReg]) {
    assert!(from==0||from==2);
    moves::adjacent_a_terms_flip(circ,rank,a,&w1[..256],from,3,&below253(rank,a,terms),dirty);
    let a253=at(rank,a,253,terms);let a254=at(rank,a,254,terms);
    swap(circ,&a253,&w1[255],&w2[255],dirty);
    if from==0 {swap(circ,&a253,&w1[253],&w2[255],dirty);}
    if from==0 {swap(circ,&a254,&w1[254],&w2[257],dirty);}
    else {swap(circ,&a254,&w2[254],&w2[257],dirty);flip(circ,&a254,&w2[254],dirty);}
}

/// R01 -> T10's leading-digit port. C1 endpoint transport has already
/// completed in inbound, while C>=2 still needs the leading passenger move.
pub(super) fn head_to_two(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],w1:&[QReg],w2:&[QReg],terms:&Terms<'_>,dirty:&[QReg]) {
    moves::adjacent_a_terms(circ,rank,a,&w1[..256],0,2,&below253(rank,a,terms),dirty);
    // A>=253 implies C_high=0 at an active transition. Cancel C_low=1.
    for av in [253,254] {
        let mut cs=at(rank,a,av,terms);let one:Vec<_>=c.iter().enumerate().map(|(i,q)|(q,i==0)).collect();
        let copy=cs.clone();for term in copy {if let Some(term)=joined(&term,&one){cs.push(term);}}
        if av==253 {swap(circ,&cs,&w1[253],&w1[255],dirty);}
        else {swap(circ,&cs,&w1[254],&w2[255],dirty);flip(circ,&cs,&w1[254],dirty);}
    }
}

/// Last digit leaves C0. At A254 restore the residual head for entry's
/// two head readers; the passengers temporarily occupy W2[254]/W2[255].
pub(super) fn before_entry(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w2:&[QReg],dirty:&[QReg]) {
    let mut base=vec![(p1,true),(p2,false),(&rank[1],false)];base.extend(c.iter().chain(sm).map(|q|(q,false)));
    let terms=at(rank,a,254,&vec![base]);
    swap(circ,&terms,&w2[256],&w2[255],dirty);flip(circ,&terms,&w2[256],dirty);
}
pub(super) fn after_entry(circ:&mut Circuit,rank:&[QReg],a:&[QReg],sign:&QReg,w2:&[QReg],dirty:&[QReg]) {
    let terms=at(rank,a,254,&vec![vec![(sign,true)]]);
    flip(circ,&terms,&w2[256],dirty);swap(circ,&terms,&w2[256],&w2[255],dirty);
    swap(circ,&terms,&w2[254],&w2[255],dirty);
}

/// The generic newborn selector already has the residual head gathered.
/// Pruned W1 leaves support A<=252. A253 uses its post-rotation W2[254]
/// zero port via an independent copy of the head address route.
pub(super) fn newborn_regular(circ:&mut Circuit,rank:&[QReg],a:&[QReg],sign:&QReg,left:&QReg,right:&QReg,dirty:&[QReg]) {
    let terms=below253(rank,a,&vec![vec![(sign,true)]]);
    swap(circ,&terms,left,right,dirty);flip(circ,&terms,left,dirty);
}
pub(super) fn newborn_253(circ:&mut Circuit,rank:&[QReg],a:&[QReg],sign:&QReg,left:&QReg,right:&QReg,dirty:&[QReg]) {
    let terms=at(rank,a,253,&vec![vec![(sign,true)]]);
    swap(circ,&terms,left,right,dirty);flip(circ,&terms,left,dirty);
}

/// Finish C1 transport. A253 was a direct two-passenger exchange before
/// entry and is intentionally omitted here. A254 restores v's head1.
pub(super) fn finish_c1(circ:&mut Circuit,rank:&[QReg],a:&[QReg],w1:&[QReg],w2:&[QReg],terms:&Terms<'_>,dirty:&[QReg]) {
    moves::across_a_terms(circ,rank,a,w2,2,&w1[..256],2,&below253(rank,a,terms),true,dirty);
    let cs=at(rank,a,254,terms);swap(circ,&cs,&w2[256],&w2[255],dirty);flip(circ,&cs,&w2[256],dirty);
}

/// Existing phase11 rotates the second passenger right by one. For S>0
/// return it to the boundary port; at S0 keep W2[256] for the cycle exit.
pub(super) fn normalize_old11(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,w2:&[QReg],j:usize,dirty:&[QReg]) {
    let mut terms=at(rank,a,254,&vec![vec![(p1,true),(p2,true)]]);
    if j==0 {
        // Active A254 forces S_high=0; phase11 S_low is -j modulo4.
        let low:Vec<_>=sm.iter().map(|q|(q,false)).collect();
        let copy=terms.clone();for cs in copy {if let Some(cs)=joined(&cs,&low){terms.push(cs);}}
    }
    let _=c;swap(circ,&terms,&w2[256],&w2[255],dirty);
}
