//! Exact full joint-state anchor activation, requiring only the old processed flag.
use super::{builder::B,mask::mcx_dirty,descending_seed::{Word,xor_eq}};
use crate::circuit::QubitId;
fn anchor(n:usize,j:usize)->Word{let mut x=[0;5];for i in 0..5{if j&(1<<i)!=0{let k=n-5+i;x[k/64]|=1<<(k%64);}}x}
/// Full257-bit transposition (A_j,0) <-> (0,1), with arbitrary dirty source restored.
pub fn activate(b:&mut B,z:&[QubitId],flag:QubitId,j:usize,dirty:&[QubitId]){activate_bits(b,z,flag,j,dirty,5)}
/// lane CURVE: the same transposition with A_j = j in z's top `w` lanes (w = 5 is the parent's activation).
pub fn activate_bits(b:&mut B,z:&[QubitId],flag:QubitId,j:usize,dirty:&[QubitId],w:usize){
 assert!(z.len()>=w+1&&z.len()<=256&&j>=1&&j<(1usize<<w));
 for i in 0..w{if j&(1<<i)!=0{b.x(z[z.len()-w+i]);}}
 for i in 0..w{if j&(1<<i)!=0{b.cx(flag,z[z.len()-w+i]);}}
 for &q in z{b.x(q);}mcx_dirty(b,z,flag,dirty);for &q in z{b.x(q);}
 for i in(0..w).rev(){if j&(1<<i)!=0{b.cx(flag,z[z.len()-w+i]);}}
 for i in(0..w).rev(){if j&(1<<i)!=0{b.x(z[z.len()-w+i]);}}
}
pub fn seed_with_c(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],flag:QubitId,c:u64){seed_bits(b,z,a,y,flag,c,5)}
/// lane CURVE: descending w-bit seed, z = (j in the top w lanes) -> j a mod p, for every a in [1, p): states of later
/// j' > j hold (j' - j) a != 0 with flag 1 when j is activated, so the transpositions never collide.
pub fn seed_bits(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],flag:QubitId,c:u64,w:usize){
 assert_eq!(z.len(),a.len()+1);assert!(y.len()>=5);
 for j in(1..(1usize<<w)).rev(){activate_bits(b,z,flag,j,a,w);super::seed_fold::short_modadd_canonical(b,z,a,flag,y[4],y[1],y[2],y[3],c);}
 b.x(flag);xor_eq(b,z,[0;5],flag,a);
}
pub fn seed(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],flag:QubitId){seed_with_c(b,z,a,y,flag,super::modp_frogdrop::C);}
/// w-bit seed for a product whose multiplier keeps 256 - w low lanes (w = 5: `seed`).
pub fn seed_w(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],flag:QubitId,w:usize){seed_bits(b,z,a,y,flag,super::modp_frogdrop::C,w);}
