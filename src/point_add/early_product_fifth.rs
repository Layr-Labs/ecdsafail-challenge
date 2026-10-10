//! Forward-only D1 product: descending exact five-bit seed, then HMR at each low bit's last logical Horner use.
use super::builder::B;
use crate::circuit::{QubitId,BitId};
pub fn round(b:&mut B,z:&mut Vec<QubitId>,a:&[QubitId],y:&[QubitId],i:usize,g:QubitId,m:BitId){
 assert_eq!(y.len(),251);assert_eq!(z.len(),256);assert_eq!(a.len(),255);assert!(i<251);
 assert!(!a.contains(&g)&&!y.contains(&g)&&!z.contains(&g));
 let de:Vec<_>=y.iter().copied().filter(|q|*q!=y[i]).take(2).collect();
 let bank:Vec<_>=y[i+1..].iter().copied().filter(|q|!de.contains(q)).collect();
 let c=super::modp_frogdrop::C;
 super::canonical_bank::mod_double(b,z,a,c,g,&bank);
 super::canonical_bank::short_modadd(b,z,a,y[i],g,de[0],de[1],c,&bank);
 b.hmr_to(y[i],m);
}
pub fn product(b:&mut B,z:&mut Vec<QubitId>,a:&[QubitId],y:&[QubitId],g:QubitId,m1:&[BitId]){
 assert_eq!(m1.len(),251);
 super::descending_seed::seed(b,z,a,y,g);
 for i in (0..251).rev(){round(b,z,a,y,i,g,m1[i]);}
}
