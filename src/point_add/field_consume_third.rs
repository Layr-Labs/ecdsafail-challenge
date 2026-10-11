//! Three-bit seed via canonical pair transpositions. Generic stage only;
//! source cross-alias exceptions need the separate exact correction stage.
use super::builder::B;
use super::mask::mcx_dirty;
use super::modp_frogdrop::inc_dirty_free;
use super::canonical_short::short_modadd_canonical;
use crate::circuit::QubitId;
pub type N=ruint::Uint<384,6>;
fn dirty(a:&[QubitId],y:&[QubitId])->Vec<QubitId>{let mut d=a.to_vec();d.extend_from_slice(&y[6..]);d}
/// Exact modulo2^n constant addition by signed NAF increments. Every borrowed
/// wire is arbitrary and restored. No truncation beyond the actual target.
pub fn add_const(b:&mut B,z:&[QubitId],ctl:QubitId,mut k:N,d:&[QubitId],subtract:bool){
 let mut i=0;while k!=N::ZERO{if k.bit(0){let neg=k.bit(1);if neg{k+=N::from(1u64);}else{k-=N::from(1u64);}
  if i<z.len(){let mut v=vec![ctl];v.extend_from_slice(&z[i..]);assert!(d.len()>=v.len());b.begin();inc_dirty_free(b,&v,d);b.x(ctl);let r=b.end();b.play(&r,neg^subtract);}}
  k>>=1;i+=1;
 }
}
/// Exact constant predicate, with an optional independent quantum enable.
pub fn lt_const(b:&mut B,z:&[QubitId],k:N,ctl:QubitId,out:QubitId,d:&[QubitId]){
 for i in(0..z.len()).rev(){if !k.bit(i){continue;}let mut v=vec![ctl];let mut flips=Vec::new();
  for j in i..z.len(){v.push(z[j]);if j==i||!k.bit(j){b.x(z[j]);flips.push(z[j]);}}
  mcx_dirty(b,&v,out,d);for &q in flips.iter().rev(){b.x(q);}
 }
}
pub fn eq_const(b:&mut B,z:&[QubitId],k:N,out:QubitId,d:&[QubitId]){
 for(i,&q)in z.iter().enumerate(){if !k.bit(i){b.x(q);}}
 mcx_dirty(b,z,out,d);
 for(i,&q)in z.iter().enumerate(){if !k.bit(i){b.x(q);}}
}
/// Canonical z+=ctl*K modp; K>=C and K<p. The source a is only borrowed here.
pub fn add_const_mod(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],ctl:QubitId,k:N,c:u64){
 let p=(N::from(1u64)<<z.len())-N::from(c);assert!(N::from(c)<=k&&k<p);let h=y[1];assert_ne!(h,ctl);let d=dirty(a,y);
 add_const(b,z,ctl,k,&d,false);
 for _ in 0..2{for &q in z{b.cx(h,q);}add_const(b,z,h,k-N::from(c),&d,false);
  lt_const(b,z,k,ctl,h,a);b.cx(ctl,h);lt_const(b,z,p,ctl,h,a);
 }
 for _ in 0..2{for &q in z{b.cx(h,q);}add_const(b,z,h,k,&d,false);lt_const(b,z,k,ctl,h,a);}
}
fn add_a(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],ctl:QubitId,c:u64){short_modadd_canonical(b,z,a,ctl,y[1],y[2],y[3],y[4],c);}
/// Zero-extension TTK sum without a quantum enable; carry-out toggles z high.
fn short_add_plain(b:&mut B,z:&[QubitId],a:&[QubitId]){
 let n=a.len();assert_eq!(z.len(),n+1);assert!(n>=2);
 for i in 1..n{b.cx(a[i],z[i]);}b.cx(a[n-1],z[n]);
 for i in(1..n-1).rev(){b.cx(a[i],a[i+1]);}
 for i in 0..n-1{b.ccx(z[i],a[i],a[i+1]);}
 b.ccx(z[n-1],a[n-1],z[n]);
 for i in(1..n).rev(){b.cx(a[i],z[i]);b.ccx(z[i-1],a[i-1],a[i]);}
 for i in 1..n-1{b.cx(a[i],a[i+1]);}b.cx(a[0],z[0]);
 for i in 1..n{b.cx(a[i],z[i]);}
}
/// Exact g^=[z<a], using complemented target high as the carry enable.
fn short_less_plain(b:&mut B,z:&[QubitId],a:&[QubitId],g:QubitId,d:QubitId){
 let n=a.len();for &q in z{b.x(q);}
 super::arith::ttk_carry(b,a,&z[..n],z[n],g,d);
 for &q in z{b.x(q);}
}
fn high_interval_plain(b:&mut B,z:&[QubitId],c:u64,g:QubitId,a:&[QubitId]){
 for &q in z{b.x(q);}
 for i in(0..z.len().min(64)).rev(){if(c>>i)&1==0{continue;}
  let mut controls=Vec::new();let mut flips=Vec::new();
  for j in i..z.len(){controls.push(z[j]);let want=j!=i&&j<64&&(c>>j)&1!=0;if !want{b.x(z[j]);flips.push(z[j]);}}
  mcx_dirty(b,&controls,g,a);for &q in flips.iter().rev(){b.x(q);}
 }
 for &q in z{b.x(q);}
}
/// Canonical z+=a modp, with the same two globally invariant reflections as
/// canonical_short; only the absent external enable and its dirty echo disappear.
pub fn add_a_uncontrolled(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],c:u64){
 let n=a.len();let(g,d,e)=(y[2],y[3],y[4]);short_add_plain(b,z,a);
 for _ in 0..2{
  for &q in z{b.cx(g,q);}
  super::arith::ttk_add(b,a,&z[..n],Some(g),Some((z[n],d)));
  let mut dirty=a.to_vec();dirty.extend([d,e]);
  b.begin();super::modp_frogdrop::add_const_exact(b,z,Some(g),c,&dirty);let shift=b.end();b.play(&shift,true);
  short_less_plain(b,z,a,g,d);high_interval_plain(b,z,c,g,a);
 }
 for _ in 0..2{
  for &q in &z[..n]{b.cx(g,q);}
  super::arith::ttk_add(b,a,&z[..n],Some(g),None);
  short_less_plain(b,z,a,g,d);
 }
}
/// Controlled canonical involution R(z)=A_k+k*a-z modp.
pub fn reflection(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],k:usize,c:u64){
 let ctl=y[0];let d=dirty(a,y);for &q in z{b.cx(ctl,q);}add_const(b,z,ctl,N::from(c),&d,true);
 for _ in 0..k{add_a(b,z,a,y,ctl,c);}
 let anchor=N::from(k as u64)<<(z.len()-3);add_const_mod(b,z,a,y,ctl,anchor+N::from(1u64),c);
}
/// g ^= [z=A_k] XOR[z=k*a modp], preserving z/source/all other borrowed lanes.
pub fn pair_predicate(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],k:usize,c:u64){
 let anchor=N::from(k as u64)<<(z.len()-3);eq_const(b,z,anchor,y[0],a);
 b.begin();for _ in 0..k{add_a_uncontrolled(b,z,a,y,c);}let shift=b.end();b.play(&shift,true);eq_const(b,z,N::ZERO,y[0],a);b.play(&shift,false);
}
/// Exact canonical transposition A_k <-> k*a modp, for every positive a<=p/2.
/// If both points coincide, identity. Other canonical inputs unchanged.
pub fn pair_swap(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],k:usize,c:u64){
 assert_eq!(z.len(),a.len()+1);assert!(y.len()>=8&&k>=1&&k<=7);assert!(N::from(c)<(N::from(1u64)<<(z.len()-3)));
 for _ in 0..2{reflection(b,z,a,y,k,c);pair_predicate(b,z,a,y,k,c);}
}
pub fn generic_seed(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],c:u64){for k in 1..=7{pair_swap(b,z,a,y,k,c);}}

/// Exact field product with a positive inverse magnitude 1..p/2. Entry z low253
/// is zero, z high3 holds the old multiplier high3, and ylow preserves its low253.
/// All borrowed lanes are restored; output wire order follows doubling relabels.
pub fn product_consume_three_high_nf(b:&mut B,z:&mut Vec<QubitId>,a:&[QubitId],ylow:&[QubitId]){
 assert_eq!(z.len(),256);assert_eq!(a.len(),255);assert_eq!(ylow.len(),253);
 let c=super::modp_frogdrop::C;generic_seed(b,z,a,ylow,c);
 super::seed_exception_corrections::correct_seed_exceptions(b,z,a,ylow);
 for i in(0..253).rev(){horner_round(b,z,a,ylow,i);}
}
pub fn horner_round(b:&mut B,z:&mut Vec<QubitId>,a:&[QubitId],ylow:&[QubitId],i:usize){
 let c=super::modp_frogdrop::C;
 super::canonical_short::mod_double_canonical(b,z,ylow,c);
 short_modadd_canonical(b,z,a,ylow[i],ylow[(i+1)%253],ylow[(i+2)%253],ylow[(i+3)%253],ylow[(i+4)%253],c);
}
