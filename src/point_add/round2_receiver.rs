use super::{Builder,const_arith::{add_const,sub_const},known_stream};
use alloy_primitives::U256;
use crate::circuit::QubitId;

/// At inverse round2, sign is already inverted: R=1 XOR s2. The target is
/// the restored pre-halving odd sum D. The source U is unchanged round1.
/// Requires the finite round1 relation; no extra long-lived sign record.
pub(crate) fn receive(c:&mut Builder,u:&[QubitId],v:&[QubitId],r:QubitId,k:usize,h:U256,top:usize){
 let n=u.len();assert_eq!(n,v.len());assert!(2<=k && k<=top && top+2<=n);
 let first=(0..k).find(|&i|h.bit(i)).unwrap_or(k);
 let indices:Vec<_>=(0..n-1).filter(|&i|(first..k).contains(&i)||i>=top).collect();
 let buf=c.alloc_qubits(indices.len());
 // Compute only the non-affine portion of X, copy it, then restore U.
 // Every constant operation, its scratch and the retained copies are paid.
 sub_const(c,&u[top..],U256::from(1));add_const(c,&u[..k],h);
 for(&i,&q)in indices.iter().zip(&buf){c.cx(u[i],q);}
 sub_const(c,&u[..k],h);add_const(c,&u[top..],U256::from(1));
 let mut out=Vec::with_capacity(n);out.push((true,vec![u[0]]));
 for j in 1..n{
  let i=j-1;let x=indices.iter().position(|&at|at==i).map_or(u[i],|at|buf[at]);
  out.push((false,vec![x,u[0]]));
 }
 // s1=R XOR U0, so the inner sum V XOR R has no separate sign wire:
 // desired=(2X) XOR signmask(U0) XOR1.
 c.cx_all(r,v);known_stream::add(c,u,v,Some(r),&out);
 // The newly restored target supplies every retained X bit for free cleanup.
 for(&i,&q)in indices.iter().zip(&buf){c.cx(v[i+1],q);c.cx(u[0],q);c.free(q);}
 c.cx_all(r,v);
}
