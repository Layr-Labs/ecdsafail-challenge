//! Exact q=0 chart readers for the actual cycle-exit length networks.
//! Callers keep chart rails out of the dirty-prefix workspace. All outputs
//! are XOR targets; no clean or persistent lane is allocated here.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use crate::point_add::trailmix_port::inversion::length_recompute::mixed_mcx;

fn gate(circ:&mut Circuit,controls:&[(&QReg,bool)],target:&QReg,dirty:&[QReg]) {
    let mut unique=Vec::new();
    for &(q,v) in controls {
        assert_ne!(q.id(),target.id(),"chart reader target aliases input");
        if let Some(&(_,old))=unique.iter().find(|&&(p,_) : &&(&QReg,bool)|p.id()==q.id()) {
            if old!=v{return;}
        }else{unique.push((q,v));}
    }
    mixed_mcx(circ,&unique,target,dirty);
}

/// Chart is [t0,t1,b0,b1,v0,v1]. No coefficient-head passenger is present
/// during the A update; the caller has not yet reinserted that passenger.
pub(crate) fn xor_u1(circ:&mut Circuit,chart:[&QReg;6],controls:&[(&QReg,bool)],target:&QReg,dirty:&[QReg]) {
    let [t0,t1,b0,b1,_v0,v1]=chart;
    for term in [vec![(t0,true),(b1,true)],vec![(t0,false)],vec![(t0,false),(v1,true)],vec![(t0,false),(t1,true),(b0,true)]] {
        let mut cs=controls.to_vec();cs.extend(term);gate(circ,&cs,target,dirty);
    }
}

/// q=0 residual bit1, after the new coefficient head has received cargo.
/// `a_bits` is the unpacked eight-bit A_raw selector. A0 is included in
/// the total Boolean extension although every normalized real exit has A>=1.
pub(crate) fn xor_r1(circ:&mut Circuit,chart:[&QReg;6],a_bits:&[&QReg],controls:&[(&QReg,bool)],target:&QReg,dirty:&[QReg]) {
    assert_eq!(a_bits.len(),8);
    // Last two abstract variables indicate A0 and A1. Their conjunction is
    // impossible; normalization in gate() discards such product terms.
    let mut anf:Vec<bool>=(0..256).map(|code| {
        let mut t=code&3;let b=code>>2&3;let v=code>>4&3;
        if code>>6&1!=0{t=1;}else if code>>7&1!=0{t|=2;}
        let r=if t&1!=0{3usize.wrapping_sub(b*v).wrapping_mul(t)&3}else{b};
        r&2!=0
    }).collect();
    for bit in 0..8{for mask in 0..256{if mask>>bit&1!=0{anf[mask]^=anf[mask^(1<<bit)];}}}
    for (mask,on) in anf.into_iter().enumerate(){if !on{continue;}
        let mut cs=controls.to_vec();
        for i in 0..6{if mask>>i&1!=0{cs.push((chart[i],true));}}
        for h in 0..2{if mask>>(6+h)&1!=0{cs.extend(a_bits.iter().enumerate().map(|(i,&q)|(q,(h>>i)&1!=0)));}}
        gate(circ,&cs,target,dirty);
        // At new A255 the second phase passenger occupies chart v1.
        // Logical t>=2^255 implies r<=1, independently of that passenger.
        // Cancel this entire r1 decoder on A255, rather than reading cargo.
        let mut terminal=cs;terminal.extend(a_bits.iter().map(|&q|(q,true)));
        gate(circ,&terminal,target,dirty);
    }
}

/// First cycle only: the padding loan is at t1, which must be restored to
/// logical zero before the six-bit chart permutation. On the exit guard,
/// t=1, q=0 and r<p<2^256 guarantee Work1[2]=0 as the substitute host.
pub(crate) fn swap_a0(circ:&mut Circuit,rank:&[QReg],a:&[QReg],guard:&QReg,left:&QReg,right:&QReg,dirty:&[QReg]) {
    let triples:Vec<_>=(0..4).flat_map(|a|(0..4).flat_map(move|c|(0..4).filter(move|&s|a+c+s<=4).map(move|s|[a,c,s]))).collect();
    circ.cx(right,left);
    for (r,t) in triples.iter().enumerate(){if t[0]!=0{continue;}
        let mut cs=vec![(guard,true),(left,true)];cs.extend(a.iter().map(|q|(q,false)));
        cs.extend(rank.iter().enumerate().map(|(i,q)|(q,r>>i&1!=0)));
        gate(circ,&cs,right,dirty);
    }
    circ.cx(right,left);
}

