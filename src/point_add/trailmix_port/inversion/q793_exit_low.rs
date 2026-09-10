//! Logical low-three-bit readers for the q=0 cycle exit.
//! No clean allocations. Physical coefficient heads may carry passengers.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

fn gate(circ:&mut Circuit,controls:&[(&QReg,bool)],target:&QReg,dirty:&[QReg]) {
    let mut cs:Vec<(&QReg,bool)>=Vec::new();
    for &(q,v) in controls {
        assert_ne!(q.id(),target.id());
        if let Some(&(_,old))=cs.iter().find(|&&(p,_)|p.id()==q.id()) {
            if old!=v{return;}
        }else{cs.push((q,v));}
    }
    mixed_mcx(circ,&cs,target,dirty);
}

/// chart=[t0,t1,t2,b0,b1,b2,v0,v1,v2], before head cargo is inserted.
pub(super) fn xor_u(circ:&mut Circuit,chart:[&QReg;9],bit:usize,controls:&[(&QReg,bool)],target:&QReg,dirty:&[QReg]) {
    assert!((1..=2).contains(&bit));
    let [t0,t1,t2,b0,b1,b2,_v0,v1,v2]=chart;
    let terms=if bit==1 {
        vec![vec![(t0,true),(b1,true)],vec![(t0,false)],vec![(t0,false),(v1,true)],vec![(t0,false),(t1,true),(b0,true)]]
    } else {
        vec![vec![(t0,true),(b2,true)],vec![(t0,false)],vec![(t0,false),(v2,true)],vec![(t0,false),(t2,true),(b0,true)],vec![(t0,false),(t1,true),(b1,true)]]
    };
    for term in terms{let mut cs=controls.to_vec();cs.extend(term);gate(circ,&cs,target,dirty);}
}

/// Decode r1/r2 after the new t head has received an arbitrary passenger.
/// A254 implies r<4 and A255 implies r<2, so affected charts are ignored.
pub(super) fn xor_r(circ:&mut Circuit,chart:[&QReg;9],a_bits:&[&QReg],bit:usize,controls:&[(&QReg,bool)],target:&QReg,dirty:&[QReg]) {
    assert_eq!(a_bits.len(),8);assert!((1..=2).contains(&bit));
    let mut anf:Vec<bool>=(0..4096).map(|z|{
        let mut t=z&7;let b=z>>3&7;let v=z>>6&7;
        if z>>9&1!=0{t=1;}else if z>>10&1!=0{t=(t&1)|2;}else if z>>11&1!=0{t|=4;}
        let r=if t&1!=0{7usize.wrapping_sub(b*v).wrapping_mul(t)&7}else{b};
        r>>bit&1!=0
    }).collect();
    for k in 0..12{for z in 0..4096{if z>>k&1!=0{anf[z]^=anf[z^(1<<k)];}}}
    for(z,on) in anf.into_iter().enumerate(){
        if !on || (z>>9).count_ones()>1{continue;}
        let mut cs=controls.to_vec();
        cs.extend((0..9).filter(|&i|z>>i&1!=0).map(|i|(chart[i],true)));
        for value in 0..3{if z>>(9+value)&1!=0{cs.extend(a_bits.iter().enumerate().map(|(i,&q)|(q,value>>i&1!=0)));}}
        gate(circ,&cs,target,dirty);
        // Exact zero cofactor from t*r<=p, not a data-specific exception.
        cs.extend(a_bits[if bit==1{0}else{1}..].iter().map(|&q|(q,true)));
        gate(circ,&cs,target,dirty);
    }
}
