//! Fixed low-three residual borrow for R00. No production cargo assumption.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

fn r_low(t:usize,b:usize,v:usize)->usize {
    if t&1!=0 {(7usize.wrapping_sub(b*v).wrapping_mul(t))&7}else{b}
}
/// XOR borrow into bit3 when comparing r against v<<shift, beginning at
/// the active interval's bit=shift. Production R00 shift is S+1>=1.
/// For shift>=3 the seed is zero; high cells start without low borrow.
/// chart contains actual logical t,b,v low3 on disjoint available rails.
pub(super) fn emit(circ:&mut Circuit,chart:[&QReg;9],out:&QReg,dirty:&[QReg],shift:usize,width:usize) {
    assert!((1..=3).contains(&width));if shift>=width{return;}
    let mut anf:Vec<_>=(0..512).map(|code|{
        let t=code&7;let b=(code>>3)&7;let v=(code>>6)&7;
        let mask=(1usize<<(width-shift))-1;
        ((r_low(t,b,v)>>shift)&mask)<(v&mask)
    }).collect();
    for bit in 0..9{for m in 0..512{if m>>bit&1!=0{anf[m]^=anf[m^(1<<bit)];}}}
    for(m,on)in anf.into_iter().enumerate(){if !on{continue;}let mut cs=Vec::new();
        for(i,&q)in chart.iter().enumerate(){if m>>i&1!=0{
            assert_ne!(q.id(),out.id());
            if !cs.iter().any(|&(p,_):&(&QReg,bool)|p.id()==q.id()){cs.push((q,true));}
        }}mixed_mcx(circ,&cs,out,dirty);
    }
}

/// Full fixed-width comparator. target_high=r[3..width], source_shifted is
/// the physical shifted source v<<shift, with bits below shift ignored.
/// carry is zero only on guard1. All other data, phase and dirty restore.
pub(super) fn compare(circ:&mut Circuit,chart:[&QReg;9],target_high:&[QReg],source_shifted:&[QReg],guard:&QReg,carry:&QReg,sign:&QReg,dirty:&[QReg],shift:usize,width:usize) {
    assert!(width>=1);assert!(target_high.len()>=width.saturating_sub(3));assert!(source_shifted.len()>=width);
    let owned=circ.b.next_qubit;let start=circ.b.ops.len();
    emit(circ,chart,carry,dirty,shift,width.min(3));
    for i in 3.max(shift)..width{let s=&source_shifted[i];let t=&target_high[i-3];
        circ.cx(s,t);circ.cx(carry,s);circ.ccx(t,s,carry);
    }
    let compute=circ.b.ops[start..].to_vec();circ.ccx(guard,carry,sign);
    circ.b.ops.extend(compute.into_iter().rev());assert_eq!(circ.b.next_qubit,owned);
}
