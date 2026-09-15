//! Borrow into bit2 without materializing either omitted residual bit.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

fn toggle(circ:&mut Circuit, cs:&[(&QReg,bool)], out:&QReg, dirty:&[QReg]) {
    let mut unique:Vec<(&QReg,bool)>=Vec::new();
    for &(q,v) in cs {
        assert_ne!(q.id(),out.id());
        if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()) {
            if old!=v{return;}
        }else{unique.push((q,v));}
    }
    mixed_mcx(circ,&unique,out,dirty);
}

pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],source:&[QReg],target:&[QReg],mask:&QReg,carry:&QReg,dirty:&[QReg],j:usize) {
    // R00's active lower bound is S+1. Only entry S=0 can reach bit1.
    // The existing mask includes that test; j!=0 excludes it statically.
    if j!=0{return;}
    let chart=[&target[0],&target[1],&source[258],&source[0],&source[257],&source[256]];
    let mut anf:Vec<bool>=(0..256).map(|code| {
        let mut t=code&3;let b=code>>2&3;let v=code>>4&3;
        if code&64!=0{t=1;}else if code&128!=0{t|=2;}
        let r=if t&1!=0{3usize.wrapping_sub(b*v).wrapping_mul(t)&3}else{b};
        v&1!=0 && r&2==0
    }).collect();
    for bit in 0..8{for m in 0..256{if m>>bit&1!=0{anf[m]^=anf[m^(1<<bit)];}}}
    for (m,on) in anf.into_iter().enumerate() {
        if !on || m&192==192 {continue;}
        let mut cs=vec![(mask,true)];
        for i in 0..6{if m>>i&1!=0{cs.push((chart[i],true));}}
        // At S=0 and A=0/1 the high-triple rank is exactly0. This
        // substitution protects arbitrary head/padding passengers.
        if m&192!=0 {
            cs.extend(rank.iter().map(|q|(q,false)));
            let value=usize::from(m&128!=0);
            cs.extend(a.iter().enumerate().map(|(i,q)|(q,value>>i&1!=0)));
        }
        toggle(circ,&cs,carry,dirty);
    }
}
