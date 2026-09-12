//! R02 adds A253/shift2 cargo correction. t>=2^253, r<8 and 2v<=r imply v2=0.
//! R00 low3 reader in the post-pre-rotation production physical frame.
//! Required contract supplied by the root boundary/cargo audit; no allocation.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

fn gate(circ:&mut Circuit,controls:&[(&QReg,bool)],out:&QReg,dirty:&[QReg]) {
    let mut unique:Vec<(&QReg,bool)>=Vec::new();
    for &(q,v)in controls{assert_ne!(q.id(),out.id());
        if let Some(&(_,old))=unique.iter().find(|&&(p,_)|p.id()==q.id()){
            if old!=v{return;}
        }else{unique.push((q,v));}
    }mixed_mcx(circ,&unique,out,dirty);
}

/// Only bit2's active mask can select S0 (j0) or S1 (j1); C=0 then.
/// Other j have no low seed. Thus flag A0/A1/A2 uses exact rank0, and A254
/// uses exact rank29. Those selectors are exact on the required active
/// domain; outside it this is a pure carry-XOR extension undone by W^-1.
///
/// Normalization contract in this R00 internal frame:
/// A0: logical t=1,b=0; A1: t1=1,t2=0; A2: t2=1.
/// A254/shift1: v2=0; A254/shift2: v1=v2=0 (v=1).
/// Raw shortword/cargo bits remain untouched, even when they contain loans.
pub(super) fn emit(circ:&mut Circuit,rank:&[QReg],a:&[QReg],w1:&[QReg],w2:&[QReg],mask:&QReg,carry:&QReg,dirty:&[QReg],j:usize) {
    assert!(j<4);if j>=2{return;}let shift=j+1;
    assert_eq!(rank.len(),5);assert_eq!(a.len(),6);assert_eq!(w1.len(),259);assert_eq!(w2.len(),259);
    let chart=[&w1[0],&w1[1],&w1[2],
        &w2[(259-shift)%259],&w2[(260-shift)%259],&w2[(261-shift)%259],
        &w2[258-shift],&w2[257-shift],&w2[256-shift]];
    let mut anf:Vec<_>=(0..16384).map(|z|{
        let mut t=z&7;let mut b=(z>>3)&7;let mut v=(z>>6)&7;
        if z>>9&1!=0{t=1;b=0;}else if z>>10&1!=0{t=(t&1)|2;}else if z>>11&1!=0{t=(t&3)|4;}
        if z>>12&1!=0{v&=if shift==1{3}else{1};}
        if shift==2&&z>>13&1!=0{v&=3;} // A253 second cargo occupies raw v2.
        let r=if t&1!=0{(7usize.wrapping_sub(b*v).wrapping_mul(t))&7}else{b};
        (r>>shift)<(v&((1usize<<(3-shift))-1))
    }).collect();
    for bit in 0..14{for m in 0..16384{if m>>bit&1!=0{anf[m]^=anf[m^(1<<bit)];}}}
    let owned=circ.b.next_qubit;let start=circ.b.ops.len();
    for(m,on)in anf.into_iter().enumerate(){
        if !on||(m>>9).count_ones()>1{continue;}
        let mut cs=vec![(mask,true)];
        cs.extend((0..9).filter(|&i|m>>i&1!=0).map(|i|(chart[i],true)));
        for f in 0..5{if m>>(9+f)&1!=0{
            let av=[0usize,1,2,254,253][f];let rv=if f>=3{29}else{0};
            cs.extend((0..5).map(|i|(&rank[i],rv>>i&1!=0)));
            cs.extend((0..6).map(|i|(&a[i],av>>i&1!=0)));
        }}gate(circ,&cs,carry,dirty);
    }
    assert_eq!(circ.b.next_qubit,owned);
    for op in &circ.b.ops[start..]{for h in [256usize,257,258]{let q=w1[h].id()as u64;
        assert!(op.q_target.0!=q&&op.q_control1.0!=q&&op.q_control2.0!=q,"dynamic R00 seed touched hole{h}");
    }}
}
