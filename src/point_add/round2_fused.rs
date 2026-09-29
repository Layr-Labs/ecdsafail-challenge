//! Keep the round1 source in its normalized frame after reversing round2.
//! Round1 then performs only its existing affine cleanup and phase handling.
use super::{Builder,const_arith::{add_const,sub_const},known_stream,affine_constant};
use alloy_primitives::U256;
use crate::circuit::QubitId;
thread_local!{static NORMALIZED:std::cell::Cell<bool>=const{std::cell::Cell::new(false)};}
pub(crate) fn mark(){NORMALIZED.with(|x|assert!(!x.replace(true)));}
pub(crate) fn take()->bool{NORMALIZED.with(|x|x.replace(false))}
pub(crate) fn receive(c:&mut Builder,u:&[QubitId],v:&[QubitId],r:QubitId,k:usize,h:U256,top:usize){
 let n=u.len();assert_eq!(n,v.len());assert!(2<=k&&k<=top&&top+2<=n);
 let first=(0..k).find(|&i|h.bit(i)).unwrap_or(k);let low=k-first;
 let indices:Vec<_>=(first..k).chain(top..n).collect();let buf=c.alloc_qubits(indices.len());
 let mut old_source=u.to_vec();
 for(&i,&q)in indices.iter().zip(&buf){c.cx(u[i],q);old_source[i]=q;}
 // A single paid inverse transform. U intentionally stays at X afterward.
 sub_const(c,&u[top..],U256::from(1));add_const(c,&u[..k],h);
 let mut out=Vec::with_capacity(n);out.push((true,vec![old_source[0]]));
 for j in 1..n{out.push((false,vec![u[j-1],old_source[0]]));}
 c.cx_all(r,v);known_stream::add(c,&old_source,v,Some(r),&out);
 // The old low/high source copies have a structurally known result X:
 // apply the restricted zero-Toffoli receiver and erase them by XOR copies.
 if low>0{
  let desired:Vec<_>=u[first..k].iter().map(|&q|(false,vec![q])).collect();
  affine_constant::add_known(c,&buf[..low],h>>first,&desired);
 }
 let desired:Vec<_>=u[top..].iter().map(|&q|(false,vec![q])).collect();
 affine_constant::add_known(c,&buf[low..],U256::MAX,&desired);
 for(&i,&q)in indices.iter().zip(&buf){c.cx(u[i],q);c.free(q);}
 c.cx_all(r,v);
}
