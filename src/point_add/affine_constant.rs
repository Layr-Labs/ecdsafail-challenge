//! Add a constant on a proved subspace where the complete output is affine
//! in unchanged, disjoint live wires. This is NOT an unrestricted adder.
use super::Builder;
use alloy_primitives::U256;
use crate::circuit::QubitId;

pub(crate) fn add_known(c:&mut Builder,b:&[QubitId],a:U256,out:&[(bool,Vec<QubitId>)]){
    let n=b.len();assert!(n>=1 && n<=256);assert_eq!(n,out.len());
    assert!(out.iter().all(|(_,qs)|qs.iter().all(|q|!b.contains(q))));
    let carries=c.alloc_qubits(n-1);
    // c_i = old_b[i+1] XOR a[i+1] XOR desired_sum[i+1].
    // Compute all of them before touching the original accumulator.
    for(i,&q)in carries.iter().enumerate(){
        c.cx(b[i+1],q);if a.bit(i+1)^out[i+1].0{c.x(q);}
        for &s in &out[i+1].1{c.cx(s,q);}
    }
    for(i,&q)in b.iter().enumerate(){if a.bit(i){c.x(q);}if i>0{c.cx(carries[i-1],q);}}
    // Given the completed sum s and incoming p:
    // a_i=0: c_i=p XOR p*s; a_i=1: c_i=1 XOR s XOR p*s.
    // Both are quadratic, so measured carry repair uses Clifford gates only.
    for i in(0..n-1).rev(){
        let m=c.alloc_bit();c.hmr(carries[i],m);
        if i>0{c.cz_if(carries[i-1],b[i],m);}
        if a.bit(i){c.x(b[i]);c.z_if(b[i],m);c.x(b[i]);}
        else if i>0{c.z_if(carries[i-1],m);}
        c.free_bit(m);c.free(carries[i]);
    }
}
