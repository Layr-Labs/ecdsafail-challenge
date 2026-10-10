//! Five-bit seed via canonical pair transpositions. Generic stage only;
//! source cross-alias exceptions need the separate exact correction stage.
use super::builder::B;
use super::mask::mcx_dirty;
use super::modp_frogdrop::inc_dirty_free;
use super::canonical_short_clean::short_modadd_canonical;
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
/// Exact on every n-bit state: ctl XOR ctl*[z<2^n-C] equals ctl*[~z<C].
/// The complement is paid and restored; all MCX borrow lanes remain arbitrary.
pub fn xor_ge_p(b:&mut B,z:&[QubitId],ctl:QubitId,out:QubitId,d:&[QubitId],c:u64){
 for &q in z{b.x(q);}super::canonical_short_clean::xor_lt_small(b,z,c,Some(ctl),out,d);for &q in z{b.x(q);}
}
/// Canonical z+=ctl*K modp; K>=C and K<p. The source a is only borrowed here.
pub fn add_const_mod(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],ctl:QubitId,k:N,c:u64,clean:QubitId){
 let p=(N::from(1u64)<<z.len())-N::from(c);assert!(N::ZERO<k&&k<p);let d=dirty(a,y);
 add_const(b,z,ctl,k,&d,false);
 lt_const(b,z,k,ctl,clean,a);xor_ge_p(b,z,ctl,clean,a,c);
 add_const(b,z,clean,N::from(c),&d,false);
 lt_const(b,z,k,ctl,clean,a);
}
fn add_a(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],ctl:QubitId,c:u64,clean:QubitId){short_modadd_canonical(b,z,a,ctl,y[1],clean,y[3],y[4],c);}
/// Zero-extension TTK sum without a quantum enable; carry-out toggles z high.
fn short_add_plain(b:&mut B,z:&[QubitId],a:&[QubitId],clean:QubitId,d:QubitId){
 let n=a.len();assert_eq!(z.len(),n+1);assert!(n>=2);
 for i in 1..n{b.cx(a[i],z[i]);}b.ccx(z[n],a[n-1],clean);
 for i in(1..n-1).rev(){b.cx(a[i],a[i+1]);}
 for i in 0..n-1{b.ccx(z[i],a[i],a[i+1]);}
 mcx_dirty(b,&[z[n],z[n-1],a[n-1]],clean,&[d]);
 b.ccx(z[n-1],a[n-1],z[n]);
 for i in(1..n).rev(){b.cx(a[i],z[i]);b.ccx(z[i-1],a[i-1],a[i]);}
 for i in 1..n-1{b.cx(a[i],a[i+1]);}b.cx(a[0],z[0]);
 for i in 1..n{b.cx(a[i],z[i]);}b.cx(a[n-1],z[n]);
}
/// Exact g^=[z<a], using complemented target high as the carry enable.
fn short_less_plain(b:&mut B,z:&[QubitId],a:&[QubitId],g:QubitId,d:QubitId){
 let n=a.len();for &q in z{b.x(q);}
 super::arith::ttk_carry(b,a,&z[..n],z[n],g,d);
 for &q in z{b.x(q);}
}
fn high_interval_plain(b:&mut B,z:&[QubitId],c:u64,g:QubitId,a:&[QubitId]){
 for &q in z{b.x(q);}
 super::canonical_short_clean::xor_lt_small(b,z,c,None,g,a);
 for &q in z{b.x(q);}
}
/// Canonical z+=a modp, with the same two globally invariant reflections as
/// canonical_short; only the absent external enable and its dirty echo disappear.
pub fn add_a_uncontrolled(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],c:u64,clean:QubitId){
 let(d,e)=(y[3],y[4]);short_add_plain(b,z,a,clean,d);
 high_interval_plain(b,z,c,clean,a);
 let mut dirty=a.to_vec();dirty.extend([d,e]);
 super::modp_frogdrop::add_const_exact(b,z,Some(clean),c,&dirty);
 short_less_plain(b,z,a,clean,d);
}
/// Exact canonical inverse of doubling, with explicit inverse wire relabeling.
fn halve_target(b:&mut B,z:&mut Vec<QubitId>,dirty:&[QubitId],c:u64,clean:QubitId){
 let mut prev=z.clone();prev.rotate_left(1);let mut after=prev.clone();
 b.begin();super::canonical_short_clean::mod_double_canonical(b,&mut after,dirty,c,clean);let rec=b.end();
 assert_eq!(&after,z);b.play(&rec,true);*z=prev;
}
/// z+=k*a (or ctl*k*a) modp for a positive public k. The initial m inverse
/// doublings and final m doublings cancel the scale on z, including ctl=0.
/// Their wire rotations cancel too. Every dirty/source loan is exactly returned.
fn multiple_digits(k:usize,controlled:bool)->Vec<i8>{
 assert!((1..=31).contains(&k));
 let ds:Option<&[i8]>=match (controlled,k){
  (false,15)=>Some(&[-1, 0, 0, 0, 1]),
  (false,23)=>Some(&[-1, 0, 0, 1, 1]),
  (false,30)=>Some(&[0, -1, 0, 0, 0, 1]),
  (false,31)=>Some(&[-1, 0, 0, 0, 0, 1]),
  (true,7)=>Some(&[-1, 0, 0, 1]),
  (true,14)=>Some(&[0, -1, 0, 0, 1]),
  (true,15)=>Some(&[-1, 0, 0, 0, 1]),
  (true,23)=>Some(&[-1, 0, 0, 1, 1]),
  (true,27)=>Some(&[-1, 0, -1, 0, 0, 1]),
  (true,28)=>Some(&[0, 0, -1, 0, 0, 1]),
  (true,29)=>Some(&[-1, -1, 0, 0, 0, 1]),
  (true,30)=>Some(&[0, -1, 0, 0, 0, 1]),
  (true,31)=>Some(&[-1, 0, 0, 0, 0, 1]),
  _=>None,
 };
 if let Some(d)=ds{d.to_vec()}else{(0..k.ilog2()+1).map(|i|((k>>i)&1)as i8).collect()}
}
pub fn add_multiple(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],k:usize,c:u64,ctl:Option<QubitId>,clean:QubitId){
 let digits=multiple_digits(k,ctl.is_some());let m=digits.len()-1;
 let mut zz=z.to_vec();let mut dirty=y.to_vec();dirty.extend_from_slice(&a[..2]);
 for _ in 0..m{halve_target(b,&mut zz,&dirty,c,clean);}
 for i in(0..=m).rev(){
  if digits[i]!=0{
   if digits[i]<0{b.begin();}
   if let Some(g)=ctl{add_a(b,&zz,a,y,g,c,clean);}else{add_a_uncontrolled(b,&zz,a,y,c,clean);}
   if digits[i]<0{let add=b.end();b.play(&add,true);}
  }
  if i>0{super::canonical_short_clean::mod_double_canonical(b,&mut zz,&dirty,c,clean);}
 }
 assert_eq!(zz,z);
}
/// Controlled canonical involution R(z)=A_k+k*a-z modp.
pub fn reflection(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],k:usize,c:u64,clean:QubitId){
 let ctl=y[0];let d=dirty(a,y);for &q in z{b.cx(ctl,q);}b.begin();super::canonical_short_clean::add_small_clean(b,z,ctl,c,clean,&d);let shift=b.end();b.play(&shift,true);
 add_multiple(b,z,a,y,k,c,Some(ctl),clean);
 let anchor=N::from(k as u64)<<(z.len()-5);add_const_mod(b,z,a,y,ctl,anchor+N::from(1u64),c,clean);
}
/// g ^= [z=A_k] XOR[z=k*a modp], preserving z/source/all other borrowed lanes.
pub fn pair_predicate(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],k:usize,c:u64,clean:QubitId){
 let anchor=N::from(k as u64)<<(z.len()-5);eq_const(b,z,anchor,y[0],a);
 b.begin();add_multiple(b,z,a,y,k,c,None,clean);let shift=b.end();b.play(&shift,true);eq_const(b,z,N::ZERO,y[0],a);b.play(&shift,false);
}
/// Exact canonical transposition A_k <-> k*a modp, for every positive a<=p/2.
/// If both points coincide, identity. Other canonical inputs unchanged.
pub fn pair_swap(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],k:usize,c:u64,clean:QubitId){
 assert_eq!(z.len(),a.len()+1);assert!(y.len()>=8&&k>=1&&k<=31);assert!(N::from(c)+N::from(1u64)<(N::from(1u64)<<(z.len()-5)));
 for _ in 0..2{reflection(b,z,a,y,k,c,clean);pair_predicate(b,z,a,y,k,c,clean);}
}
pub fn generic_seed(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],c:u64,clean:QubitId){for k in 1..=31{pair_swap(b,z,a,y,k,c,clean);}}

/// Exact field product with a positive inverse magnitude 1..p/2. Entry z low251
/// is zero, z high5 holds the old multiplier high5, and ylow preserves its low251.
/// clean starts and ends zero; all borrowed lanes are restored. Output wire
/// order follows doubling relabels. No physical wire ID is hardcoded.
pub fn product_consume_five_high_clean(b:&mut B,z:&mut Vec<QubitId>,a:&[QubitId],ylow:&[QubitId],clean:QubitId){
 assert_eq!(z.len(),256);assert_eq!(a.len(),255);assert_eq!(ylow.len(),251);
 super::descending_seed::seed(b,z,a,ylow,clean);
 for i in(0..251).rev(){horner_round(b,z,a,ylow,i,clean);}
}
pub fn horner_round(b:&mut B,z:&mut Vec<QubitId>,a:&[QubitId],ylow:&[QubitId],i:usize,clean:QubitId){
 let c=super::modp_frogdrop::C;
 // Doubling does not read the inverse source. Its exact digit4 increment
 // needs253 dirty loans, so borrow and restore source a[0..2] alongside ylow251.
 let mut double_dirty=ylow.to_vec();double_dirty.extend_from_slice(&a[..2]);
 super::canonical_short_clean::mod_double_canonical(b,z,&double_dirty,c,clean);
 short_modadd_canonical(b,z,a,ylow[i],ylow[(i+1)%251],clean,ylow[(i+3)%251],ylow[(i+4)%251],c);
}
