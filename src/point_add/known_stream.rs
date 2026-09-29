//! Restricted known-output addition with two streaming carry wires.
use super::Builder;
use crate::circuit::QubitId;
pub(crate) fn add(c:&mut Builder,a:&[QubitId],b:&[QubitId],cin:Option<QubitId>,out:&[(bool,Vec<QubitId>)]){
 let n=b.len();assert!(n>=1);assert_eq!(a.len(),n);assert_eq!(out.len(),n);
 assert!(a.iter().all(|q|!b.contains(q)));
 assert!(out.iter().all(|(_,qs)|qs.iter().all(|q|!b.contains(q))));
 let mut outgoing=None;
 for i in(0..n).rev(){
  let incoming=if i==0{cin}else{
   let p=c.alloc_qubit();c.cx(a[i],p);c.cx(b[i],p);if out[i].0{c.x(p);}for &q in &out[i].1{c.cx(q,p);}Some(p)
  };
  c.cx(a[i],b[i]);if let Some(p)=incoming{c.cx(p,b[i]);}
  if let Some(q)=outgoing{
   let m=c.alloc_bit();c.hmr(q,m);
   // Carry out, written in terms of completed sum s, source a, carry p:
   // a*s XOR a XOR a*p XOR s*p XOR p.
   c.cz_if(a[i],b[i],m);c.z_if(a[i],m);
   if let Some(p)=incoming{c.cz_if(a[i],p,m);c.cz_if(b[i],p,m);c.z_if(p,m);}
   c.free_bit(m);c.free(q);
  }
  outgoing=if i>0{incoming}else{None};
 }
 assert!(outgoing.is_none());
}
