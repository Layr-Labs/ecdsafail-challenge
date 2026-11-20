//! Exact signed high-word half-step, with its inverse; no persistent guard rail.
use super::{Builder,bridge};
use crate::circuit::QubitId;
fn run(c:&mut Builder,a:&[QubitId],b:&[QubitId],cin:QubitId,cout:QubitId,bridges:usize,
    consume:impl FnOnce(&mut Builder,Option<QubitId>,QubitId,QubitId,Option<QubitId>)) {
    let n=a.len();let k=bridges+1;
    if bridges>=2 && 2*k<=n {
        // Both chunks and the full, exact repair fit the direct bridge budget.
        let boundary=c.alloc_qubit();
        bridge::run(c,&a[..k],&b[..k],Some(cin),Some(boundary),0,|_,_,_,_,_|{});
        bridge::run(c,&a[k..],&b[k..],Some(boundary),Some(cout),0,consume);
        // For s=(a+b+cin) mod 2^k, carry == borrow(s-a-cin).
        // The source, completed low sum and original carry-in are still live.
        super::compare::erase_with_compare(c,boundary,&b[..k],&a[..k],Some(cin));
        c.free(boundary);
    } else {bridge::run(c,a,b,Some(cin),Some(cout),bridges,consume);}
}
fn right(c:&mut Builder,b:&[QubitId]){for i in 0..b.len()-1{c.swap(b[i],b[i+1]);}}
fn left(c:&mut Builder,b:&[QubitId]){for i in(0..b.len()-1).rev(){c.swap(b[i],b[i+1]);}}
pub(crate) fn forward(c:&mut Builder,source:&[QubitId],target:&[QubitId],sign:QubitId,bridges:usize){
    let m=source.len();assert_eq!(m,target.len());assert!(m>=4);
    // sign=source[0] XOR target[0]. Complementing source makes the low
    // operands equal; the low sum is1 and its outgoing carry is source[0].
    c.cx_all(sign,source);c.cx(source[0],target[0]);
    run(c,&source[1..],&target[1..],source[0],target[0],bridges,|c,o,_a,s,p|{
        // Correct signed extension = unsigned carry XOR both original signs.
        // Their XOR is completed top sum XOR its incoming carry.
        let q=o.unwrap();c.cx(s,q);c.cx(p.unwrap(),q);
    });
    c.cx_all(sign,source);right(c,target);
}
// q is the old signed doubling bit. On the valid inverse image,
// q = carry_out XOR source_top XOR sum_top. Measure q, then repair its
// phase while the carry into the top is live. q itself hosts that carry.
fn receive_single(c:&mut Builder,a:&[QubitId],b:&[QubitId],cin:QubitId,q:QubitId,bridges:usize) {
    let n=a.len();assert!(n>=3 && bridges<n-2);assert_eq!(n,b.len());
    let phase=c.alloc_bit();c.hmr(q,phase);
    let first=n-2-bridges;
    let is_bridge=|i:usize|i>=first && i<n-2;
    let mut carries:Vec<_>=(0..n-2).map(|i|if is_bridge(i){a[i]}else{c.alloc_qubit()}).collect();
    carries.push(q);
    let previous=|i:usize|if i==0{cin}else{carries[i-1]};
    for i in 0..n-1 {let p=previous(i);
        if is_bridge(i){c.cx(a[i],b[i]);c.cx(a[i],p);c.ccx(b[i],p,a[i]);}
        else {c.cx(p,a[i]);c.cx(p,b[i]);c.ccx(a[i],b[i],carries[i]);c.cx(p,carries[i]);}
    }
    c.cx(q,b[n-1]);c.cx(a[n-1],b[n-1]);
    // In completed-top coordinates: q_old = a*s + a*p + s*p + p + s.
    c.cz_if(a[n-1],b[n-1],phase);c.cz_if(a[n-1],q,phase);
    c.cz_if(b[n-1],q,phase);c.z_if(q,phase);c.z_if(b[n-1],phase);c.free_bit(phase);
    for i in(0..n-1).rev(){let p=previous(i);
        if is_bridge(i){c.ccx(b[i],p,a[i]);c.cx(a[i],p);c.cx(p,b[i]);}
        else {c.cx(p,carries[i]);let bit=c.alloc_bit();c.hmr(carries[i],bit);
            c.cz_if(a[i],b[i],bit);c.free_bit(bit);if i<n-2{c.free(carries[i]);}
            c.cx(p,a[i]);c.cx(a[i],b[i]);}
    }
}
fn receive(c:&mut Builder,a:&[QubitId],b:&[QubitId],cin:QubitId,q:QubitId,bridges:usize) {
    let n=a.len();let k=bridges+1;
    if bridges>=2 && 2*k<n {
        let boundary=c.alloc_qubit();
        bridge::run(c,&a[..k],&b[..k],Some(cin),Some(boundary),0,|_,_,_,_,_|{});
        receive_single(c,&a[k..],&b[k..],boundary,q,0);
        super::compare::erase_with_compare(c,boundary,&b[..k],&a[..k],Some(cin));
        c.free(boundary);
    } else {receive_single(c,a,b,cin,q,bridges);}
}
pub(crate) fn reverse(c:&mut Builder,source:&[QubitId],target:&[QubitId],sign:QubitId,bridges:usize){
    let m=source.len();assert_eq!(m,target.len());assert!(m>=4);
    left(c,target);c.x(sign);c.cx_all(sign,source);
    // target[0] holds the discarded signed doubling bit, not a clean zero.
    // The final carry only XORs into it and is never consumed as a carry-in.
    receive(c,&source[1..],&target[1..],source[0],target[0],bridges);
    c.cx(source[0],target[0]);c.x(target[0]);
    c.cx_all(sign,source);c.x(sign);
}
