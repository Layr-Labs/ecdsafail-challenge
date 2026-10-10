//! Exact full joint-state anchor activation, requiring only the old processed flag.
use super::{builder::B,mask::mcx_dirty,descending_seed::{Word,xor_eq}};
use crate::circuit::QubitId;
fn anchor(n:usize,j:usize)->Word{let mut x=[0;5];for i in 0..5{if j&(1<<i)!=0{let k=n-5+i;x[k/64]|=1<<(k%64);}}x}
/// Full257-bit transposition (A_j,0) <-> (0,1), with arbitrary dirty source restored.
pub fn activate(b:&mut B,z:&[QubitId],flag:QubitId,j:usize,dirty:&[QubitId]){
 assert!(z.len()>=6&&z.len()<=256&&(1..=31).contains(&j));
 for i in 0..5{if j&(1<<i)!=0{b.x(z[z.len()-5+i]);}}
 for i in 0..5{if j&(1<<i)!=0{b.cx(flag,z[z.len()-5+i]);}}
 for &q in z{b.x(q);}mcx_dirty(b,z,flag,dirty);for &q in z{b.x(q);}
 for i in(0..5).rev(){if j&(1<<i)!=0{b.cx(flag,z[z.len()-5+i]);}}
 for i in(0..5).rev(){if j&(1<<i)!=0{b.x(z[z.len()-5+i]);}}
}
pub fn seed_with_c(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],flag:QubitId,c:u64){
 assert_eq!(z.len(),a.len()+1);assert!(y.len()>=5);
 for j in(1..=31).rev(){activate(b,z,flag,j,a);super::seed_fold::short_modadd_canonical(b,z,a,flag,y[4],y[1],y[2],y[3],c);}
 b.x(flag);xor_eq(b,z,[0;5],flag,a);
}
pub fn seed(b:&mut B,z:&[QubitId],a:&[QubitId],y:&[QubitId],flag:QubitId){seed_with_c(b,z,a,y,flag,super::modp_frogdrop::C);}
