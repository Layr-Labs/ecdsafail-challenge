//! Exact finite-control implied-odd head multiplication with arbitrary full target.
//! Source and dirty lanes restored, c0/h/anc/andc clean on every branch.
use super::builder::B;
use crate::circuit::QubitId;
fn signed_add(b:&mut B,sign:QubitId,t:&[QubitId],s:&[QubitId],tail:&[QubitId],c0:QubitId,anc:&[QubitId],andc:&[QubitId],dirty:&[QubitId]){
 use super::arith::{up_m,down_m,Dm};let n=t.len();assert!(n>=1&&s.len()==n);let k=andc.len().min(n);let low=n-k;
 b.cx(sign,c0);for&q in s{b.cx(sign,q);}
 let up=up_m(b,&t[..low],&s[..low],c0,false);let dn=down_m(b,&t[..low],&s[..low],c0,Dm::Sum,false);b.play(&up,false);
 let carry=|i:usize|if i==low{if low==0{c0}else{s[low-1]}}else{andc[i-low-1]};
 for i in low..n{let c=carry(i);b.cx(c,t[i]);b.cx(c,s[i]);b.and_c(t[i],s[i],andc[i-low]);b.cx(c,andc[i-low]);}
 if !tail.is_empty(){let cout=if k>0{andc[k-1]}else{s[n-1]};b.cx(sign,cout);for&q in tail{b.cx(sign,q);}super::frogdrop::inc_mixed(b,cout,tail,anc,dirty);for&q in tail{b.cx(sign,q);}b.cx(sign,cout);}
 for i in (low..n).rev(){let c=carry(i);b.cx(c,andc[i-low]);b.and_u(t[i],s[i],andc[i-low]);b.cx(c,t[i]);b.cx(s[i],t[i]);b.cx(c,s[i]);}
 b.play(&dn,false);for&q in s{b.cx(sign,q);}b.cx(sign,c0);
}

// Every descending signed row retains sign=1-original t[0]. After its
// first MAJ CNOTs c0=original B0 and t[0]=!original B0. Their CCX is zero.
// This exact relation lends c0 during the tail, without any source-bit care.
fn inc_cost(n:usize,bank:usize)->usize {
 if n==0{return 0;}let k=bank.min(n-1);let mut best=k+if n-k==1{0}else{4*(n-k)};
 for k in 0..=bank.min(n-1){let rest=n-k;let need=super::frogdrop::conditional_inc_need(rest);
  if need<=bank-k{best=best.min(k+super::frogdrop::conditional_inc_cost(rest));}}
 best
}
fn signed_lsb_add(b:&mut B,sign:QubitId,t:&[QubitId],s:&[QubitId],tail:&[QubitId],c0:QubitId,anc:&[QubitId],andc:&[QubitId],dirty:&[QubitId]){
 let n=t.len();assert!(n>=1&&s.len()==n);
 // A retained low MAJ lane is required for the exact first-cell relation.
 let maxk=andc.len().min(n-1);let mut k=0;let mut price=usize::MAX;
 for candidate in 0..=maxk {let cost=2*n-candidate-2+inc_cost(tail.len(),anc.len()+andc.len()-candidate+1);
  if cost<price {price=cost;k=candidate;}}
 let low=n-k;b.cx(sign,c0);for&q in s{b.cx(sign,q);}
 b.begin();
 for i in 0..low {let c=if i==0{c0}else{s[i-1]};b.cx(s[i],t[i]);b.cx(s[i],c);if i>0{b.ccx(c,t[i],s[i]);}}
 let up=b.end();
 b.begin();
 for i in (0..low).rev(){let c=if i==0{c0}else{s[i-1]};if i>0{b.ccx(c,t[i],s[i]);}b.cx(s[i],c);b.cx(c,t[i]);}
 let dn=b.end();b.play(&up,false);
 let carry=|i:usize|if i==low{s[low-1]}else{andc[i-low-1]};
 for i in low..n {let c=carry(i);b.cx(c,t[i]);b.cx(c,s[i]);b.and_c(t[i],s[i],andc[i-low]);b.cx(c,andc[i-low]);}
 // t0 is unchanged by all later MAJ cells and both tail conjugations.
 b.x(c0);b.cx(t[0],c0);
 let mut bank=anc.to_vec();bank.extend_from_slice(&andc[k..]);bank.push(c0);
 if !tail.is_empty(){let cout=if k>0{andc[k-1]}else{s[n-1]};b.cx(sign,cout);for&q in tail{b.cx(sign,q);}
  super::frogdrop::inc_mixed(b,cout,tail,&bank,dirty);
  for&q in tail{b.cx(sign,q);}b.cx(sign,cout);}
 b.cx(t[0],c0);b.x(c0);
 for i in (low..n).rev(){let c=carry(i);b.cx(c,andc[i-low]);b.and_u(t[i],s[i],andc[i-low]);b.cx(c,t[i]);b.cx(s[i],t[i]);b.cx(c,s[i]);}
 b.play(&dn,false);for&q in s{b.cx(sign,q);}b.cx(sign,c0);
}

pub fn head_product(b:&mut B,t:&[QubitId],a:&[QubitId],c0:QubitId,h:QubitId,anc:&[QubitId],andc:&[QubitId],dirty:&[QubitId]){
 let width=a.len();assert_eq!(t.len(),2*width);if width<=1{return;}let n=width-1;
 // +B*2^H, initial h=0 retained throughout this unsigned add.
 signed_add(b,h,&t[width..width+n],&a[1..],&t[width+n..],c0,anc,andc,dirty);
 // Original low-control b_i is unread until its row. Earlier rows start above it.
 for i in (1..width).rev(){b.x(h);b.cx(t[i],h);signed_lsb_add(b,h,&t[i..i+n],&a[1..],&t[i+n..],c0,anc,andc,dirty);
  // new t_i = old b_i XOR B_lsb for either sign. h=1-old b_i.
  b.x(h);b.cx(t[i],h);b.cx(a[1],h);
 }
 // -(1-b0)*B*2, old exact controlled addition replayed inversely.
 b.x(t[0]);b.begin();super::frogdrop::cadd_tail_and_mixed(b,t[0],&t[1..1+n],&a[1..],&t[1+n..],c0,h,anc,dirty,andc);let r=b.end();b.play(&r,true);b.x(t[0]);
}
