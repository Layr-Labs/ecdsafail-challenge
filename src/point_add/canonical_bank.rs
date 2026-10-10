//! Exact clean-flag canonical arithmetic using a growing, explicitly clean bank.
//! All bank lanes are returned zero. Dirty loans are preserved for every value.
use super::{builder::B,arith::{ttk_add,ttk_carry},mask::mc_xor};
use crate::circuit::QubitId;
fn mcx(b:&mut B,cs:&[QubitId],out:QubitId,dirty:&[QubitId],bank:&[QubitId]){
 assert!(!cs.contains(&out));assert!(bank.iter().all(|q|!cs.contains(q)&&*q!=out));
 let d:Vec<_>=dirty.iter().copied().filter(|q|!bank.contains(q)).collect();
 let lits:Vec<_>=cs.iter().map(|&q|(q,false)).collect();mc_xor(b,&lits,out,bank,&d);
}
fn inc_mixed(b:&mut B,ctl:QubitId,t:&[QubitId],bank:&[QubitId],dirty:&[QubitId]){
 if t.is_empty(){return;}let k=bank.len().min(t.len()-1);let mut prev=ctl;
 for i in 0..k{b.and_c(prev,t[i],bank[i]);prev=bank[i];}
 if t.len()-k==1{b.cx(prev,t[k]);}else{let mut v=vec![prev];v.extend_from_slice(&t[k..]);let d:Vec<_>=dirty.iter().copied().filter(|q|!bank.contains(q)).collect();super::modp_frogdrop::inc_dirty_free(b,&v,&d);b.x(prev);}
 for i in(0..k).rev(){let p=if i==0{ctl}else{bank[i-1]};b.and_u(p,t[i],bank[i]);b.cx(p,t[i]);}
}
fn add_const(b:&mut B,t:&[QubitId],ctl:QubitId,mut c:u64,dirty:&[QubitId],bank:&[QubitId]){
 let mut i=0;while c!=0{if c&1==0{c>>=1;i+=1;continue;}let neg=c&3==3;if neg{c=(c>>1)+1;}else{c>>=1;}
  if i<t.len(){assert!(!t[i..].contains(&ctl));b.begin();inc_mixed(b,ctl,&t[i..],bank,dirty);let r=b.end();b.play(&r,neg);}i+=1;
 }
}
fn direct(b:&mut B,z:&[QubitId],c:u64,ctl:Option<QubitId>,out:QubitId,d:&[QubitId],bank:&[QubitId]){
 for i in(0..z.len().min(64)).rev(){if(c>>i)&1==0{continue;}let mut cs=vec![];if let Some(q)=ctl{cs.push(q);}let mut flips=vec![];
  for j in i..z.len(){cs.push(z[j]);let want=j!=i&&j<64&&(c>>j)&1!=0;if !want{b.x(z[j]);flips.push(z[j]);}}
  mcx(b,&cs,out,d,bank);for&q in flips.iter().rev(){b.x(q);}
 }
}
fn xor_lt_small(b:&mut B,z:&[QubitId],c:u64,ctl:Option<QubitId>,out:QubitId,dirty:&[QubitId],bank:&[QubitId]){
 if c==0{return;}let low=(u64::BITS-c.leading_zeros())as usize;assert!(low<=z.len());
 let hi=z.len()-low+usize::from(ctl.is_some());let needed=hi.saturating_sub(2).max(low.saturating_sub(1));
 if low==z.len()||dirty.len()<needed+1{direct(b,z,c,ctl,out,dirty,bank);return;}
 let flag=dirty[0];assert!(!bank.contains(&flag));let d=&dirty[1..];
 for _ in 0..2{direct(b,&z[..low],c,Some(flag),out,d,bank);let mut cs=vec![];if let Some(q)=ctl{cs.push(q);}for&q in&z[low..]{b.x(q);cs.push(q);}mcx(b,&cs,flag,d,bank);for&q in&z[low..]{b.x(q);}}
}
fn short_less(b:&mut B,z:&[QubitId],a:&[QubitId],ctl:QubitId,out:QubitId,d:QubitId,e:QubitId){
 let n=a.len();assert_eq!(z.len(),n+1);assert!(n>=2);
 for &q in z{b.x(q);}
 // Same exact shared carry query already used by canonical_short_clean.
 // The additional target-high enable is applied to both carry terms.
 b.begin();for i in 1..n{b.cx(a[i],z[i]);}let s1=b.end();b.play(&s1,false);
 super::mask::mcx_dirty(b,&[ctl,z[n],a[n-1]],out,&[d]);
 b.begin();for i in(1..n-1).rev(){b.cx(a[i],a[i+1]);}
 for i in 0..n-1{b.ccx(z[i],a[i],a[i+1]);}let s23=b.end();b.play(&s23,false);
 super::mask::mcx_dirty(b,&[ctl,z[n],z[n-1],a[n-1]],out,&[d,e]);
 b.play(&s23,true);b.play(&s1,true);
 for &q in z{b.x(q);}
}
fn short_add_carry(b:&mut B,z:&[QubitId],a:&[QubitId],ctl:QubitId,g:QubitId,d:QubitId,e:QubitId,bank:&[QubitId]){
 let n=a.len();for i in 1..n{b.cx(a[i],z[i]);}mcx(b,&[ctl,z[n],a[n-1]],g,&[d],bank);
 for i in(1..n-1).rev(){b.cx(a[i],a[i+1]);}for i in 0..n-1{b.ccx(z[i],a[i],a[i+1]);}
 mcx(b,&[ctl,z[n],z[n-1],a[n-1]],g,&[d,e],bank);mcx(b,&[ctl,z[n-1],a[n-1]],z[n],&[d],bank);
 for i in(1..n).rev(){b.ccx(ctl,a[i],z[i]);b.ccx(z[i-1],a[i-1],a[i]);}for i in 1..n-1{b.cx(a[i],a[i+1]);}b.ccx(ctl,a[0],z[0]);for i in 1..n{b.cx(a[i],z[i]);}b.ccx(ctl,a[n-1],z[n]);
}
pub fn short_modadd(b:&mut B,z:&[QubitId],a:&[QubitId],ctl:QubitId,g:QubitId,d:QubitId,e:QubitId,c:u64,bank:&[QubitId]){
 assert_eq!(z.len(),a.len()+1);short_add_carry(b,z,a,ctl,g,d,e,bank);
 for&q in z{b.x(q);}xor_lt_small(b,z,c,Some(ctl),g,a,bank);for&q in z{b.x(q);}
 let mut dirty=a.to_vec();dirty.extend([d,e]);add_const(b,z,g,c,&dirty,bank);short_less(b,z,a,ctl,g,d,e);
}
fn add_small(b:&mut B,t:&[QubitId],ctl:QubitId,c:u64,g:QubitId,dirty:&[QubitId],bank:&[QubitId]){
 if c==0{return;}let shift=c.trailing_zeros()as usize;if shift>=t.len(){return;}let z=&t[shift..];let k=c>>shift;let l=(u64::BITS-k.leading_zeros())as usize;
 if l>=z.len(){add_const(b,z,ctl,k,dirty,bank);return;}
 for&q in&z[..l]{b.x(q);}xor_lt_small(b,&z[..l],k,Some(ctl),g,dirty,bank);for&q in&z[..l]{b.x(q);}
 add_const(b,&z[..l],ctl,k,dirty,bank);inc_mixed(b,g,&z[l..],bank,dirty);xor_lt_small(b,&z[..l],k,Some(ctl),g,dirty,bank);
}
pub fn mod_double(b:&mut B,z:&mut Vec<QubitId>,dirty:&[QubitId],c:u64,g:QubitId,bank:&[QubitId]){
 assert_eq!(c&1,1);let n=z.len();let d=(c-1)/2;let h=z[n-1];let low=(u64::BITS-d.leading_zeros())as usize;
 for&q in&z[..n-1]{b.x(q);}
 if d!=0{
  if low>=n-1{xor_lt_small(b,&z[..n-1],d,None,h,dirty,bank);}else{
   for&q in&z[low..n-1]{b.x(q);}mcx(b,&z[low..n-1],g,dirty,bank);for&q in&z[low..n-1]{b.x(q);}
   xor_lt_small(b,&z[..low],d,Some(g),h,dirty,bank);
   for&q in&z[low..n-1]{b.x(q);}mcx(b,&z[low..n-1],g,dirty,bank);for&q in&z[low..n-1]{b.x(q);}
  }
 }
 for&q in&z[..n-1]{b.x(q);}let high=z.pop().unwrap();z.insert(0,high);add_small(b,z,z[0],c-1,g,dirty,bank);
}
