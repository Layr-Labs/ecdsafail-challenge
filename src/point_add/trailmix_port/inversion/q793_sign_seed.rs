//! Fixed-width modulo-eight Sign comparator. Logical low bits are explicit.
//! This kernel deliberately does NOT assume production A/C cargo readers.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;

fn u_low(t:usize,b:usize,v:usize)->usize {
    if t&1!=0 { b } else if v&1!=0 {
        // Every odd residue modulo8 is its own inverse.
        (7usize.wrapping_sub(t*b).wrapping_mul(v))&7
    } else { b } // Explicit reversible target-XOR extension off the chart.
}
fn xor_truth(circ:&mut Circuit,inputs:&[&QReg],out:&QReg,dirty:&[QReg],f:impl Fn(usize)->bool) {
    assert!(inputs.len()<=12); let size=1usize<<inputs.len();
    let mut anf:Vec<_>=(0..size).map(f).collect();
    for bit in 0..inputs.len(){for m in 0..size{if m>>bit&1!=0{anf[m]^=anf[m^(1<<bit)];}}}
    for(m,on)in anf.into_iter().enumerate(){if !on{continue;}
        let mut cs=Vec::new();
        for(i,&q)in inputs.iter().enumerate(){if m>>i&1!=0 {
            assert_ne!(q.id(),out.id());
            if !cs.iter().any(|&(p,_):&(&QReg,bool)|p.id()==q.id()){cs.push((q,true));}
        }}
        mixed_mcx(circ,&cs,out,dirty);
    }
}

/// XOR the borrow after the first min(3,width) bits of t-(u>>shift).
/// chart=(t[0..3],b[0..3],v[0..3]), b=u if t odd, otherwise b=r.
/// shifted_target[i] physically supplies u[shift+i] only when shift+i>=3;
/// its lower physical b bits are ignored in favor of the exact chart decode.
/// All inputs and arbitrary dirty rails restore; out may start arbitrary.
pub(super) fn emit(circ:&mut Circuit,chart:[&QReg;9],shifted_target:&[QReg],out:&QReg,dirty:&[QReg],shift:usize,width:usize) {
    assert!(shift<=3); assert!((1..=3).contains(&width));
    assert!(shifted_target.len()>=width);
    let mut inputs=chart.to_vec();let mut positions=[None;3];
    for i in 0..width{if shift+i>=3{positions[i]=Some(inputs.len());inputs.push(&shifted_target[i]);}}
    xor_truth(circ,&inputs,out,dirty,|code|{
        let t=code&7;let b=(code>>3)&7;let v=(code>>6)&7;let u=u_low(t,b,v);
        let mut rhs=0;
        for i in 0..width{let value=if let Some(k)=positions[i]{code>>k&1}else{u>>(shift+i)&1};rhs|=value<<i;}
        (t&((1<<width)-1))>rhs
    });
}

/// Full fixed-width read-only comparison with a phase-free W/center/W^-1.
/// carry is zero only on guard=1. Sign may be arbitrary; every other rail
/// restores for both guards, including arbitrary off-guard carry. No allocate.
/// source_high supplies t[3..width], shifted_target supplies physical u>>shift.
pub(super) fn compare(circ:&mut Circuit,chart:[&QReg;9],source_high:&[QReg],shifted_target:&[QReg],guard:&QReg,carry:&QReg,sign:&QReg,dirty:&[QReg],shift:usize,width:usize) {
    assert!(width>=1);assert!(source_high.len()>=width.saturating_sub(3));assert!(shifted_target.len()>=width);
    let owned=circ.b.next_qubit;let start=circ.b.ops.len();
    emit(circ,chart,shifted_target,carry,dirty,shift,width.min(3));
    for i in 3..width{let s=&source_high[i-3];let t=&shifted_target[i];
        circ.cx(s,t);circ.cx(carry,s);circ.ccx(t,s,carry);
    }
    let compute=circ.b.ops[start..].to_vec();circ.ccx(guard,carry,sign);
    circ.b.ops.extend(compute.into_iter().rev());assert_eq!(circ.b.next_qubit,owned);
}
