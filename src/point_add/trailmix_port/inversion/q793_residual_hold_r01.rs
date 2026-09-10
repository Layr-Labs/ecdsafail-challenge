//! Hold one residual C1 flag across both consumers, then restore all lenders.
use super::*;
pub(super) const SWITCH:&str="Q793_RESIDUAL_HOLD";
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],c:&[QReg],sm:&[QReg],p1:&QReg,p2:&QReg,sign:&QReg,w1:&[QReg],w2:&[QReg],dirty:&[QReg],j:usize){
    let p01=vec![(p1,false),(p2,true)];
    let rflag=vec![vec![(p1,false),(sign,true)]];
    let zero=product(&vec![p01.clone()],&szero(rank,c,sm,j));
    let mut peak=Vec::new();
    if j==0{let mut term=p01.clone();term.extend(rank.iter().chain(a).chain(c).chain(sm).map(|q|(q,false)));term.push((&w2[258],false));peak.push(term);}
    let mut c1=Vec::new();
    if j==2{for r in [0,13,23,29]{let mut term=p01.clone();term.extend((0..5).map(|i|(&rank[i],r>>i&1!=0)));term.extend(c.iter().enumerate().map(|(i,q)|(q,i==0)));term.extend(sm.iter().map(|q|(q,false)));c1.push(term);}}
    if zero.is_empty()&&peak.is_empty()&&c1.is_empty(){return;}
    if !super::super::metadata_muxlease::active(SWITCH){
        let mut head=zero;head.extend(peak);head.extend(c1.clone());
        if !c1.is_empty(){toggle_pair_around(circ,&c1,rank,sign,dirty,"Q793_C1_J2_HOLD",|circ,lenders|super::super::q793_cargo_r02::inbound(circ,rank,a,w1,w2,0,&rflag,lenders));}
        toggle_terms(circ,&head,rank,sign,dirty);
        super::super::q793_cargo_r02::head_to_two(circ,rank,a,c,w1,w2,&rflag,dirty);
        toggle_terms(circ,&head,rank,sign,dirty);
        return;
    }
    // Inbound preserves every C1/S-zero/peak control, including W2[258].
    // Predicate toggles all target Sign and commute. Thus the middle C1
    // uncompute/recompute cancels even with the S-zero/peak toggles between.
    // Outer and inner rank lenders stay excluded until their chart is erased.
    toggle_pair_around(circ,&c1,rank,sign,dirty,SWITCH,|circ,c1_lenders|{
        if !c1.is_empty(){super::super::q793_cargo_r02::inbound(circ,rank,a,w1,w2,0,&rflag,c1_lenders);}
        toggle_pair_around(circ,&zero,rank,sign,c1_lenders,SWITCH,|circ,body_lenders|{
            // The j=0 peak has24 controls and retains22 dirty helpers.
            // At j=2 there is no peak, so two held charts are affordable.
            assert!(peak.is_empty()||body_lenders.len()>=22);
            toggle_terms(circ,&peak,rank,sign,body_lenders);
            super::super::q793_cargo_r02::head_to_two(circ,rank,a,c,w1,w2,&rflag,body_lenders);
            toggle_terms(circ,&peak,rank,sign,body_lenders);
        });
    });
}

