//! Preserve the existing measured known-top-output channel with fewer carries.
use super::builder::Builder;use crate::circuit::QubitId;
pub(super) fn apply(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],cin:Option<QubitId>,drops:&[usize],desired:bool)->bool{
 apply_with_hook(c,acc,rows,ones,cin,drops,desired,&mut|_,_,_|{})
}
pub(super) fn apply_with_hook(c:&mut Builder,acc:&[QubitId],rows:&[Vec<QubitId>],ones:&[bool],cin:Option<QubitId>,drops:&[usize],desired:bool,hook:&mut dyn FnMut(&mut Builder,usize,QubitId))->bool{
 if let Some(ci)=cin{return super::phase_pebble::known_top_with_hook(c,acc,rows,ones,ci,drops,desired,hook);}
 if !super::zero_carry::valid(acc,rows,ones,drops){return false;}let row=&rows[0];let q=row[0];for &r in &row[1..]{c.cx(r,q);}if ones[0]{c.x(q);}
 let carry=c.alloc_qubit();c.ccx(q,acc[0],carry);if ones[0]{c.x(q);}for &r in row[1..].iter().rev(){c.cx(r,q);}hook(c,1,carry);
 for &r in row{c.cx(r,acc[0]);}if ones[0]{c.x(acc[0]);}
 assert!(super::phase_pebble::known_top_with_hook(c,&acc[1..],&rows[1..],&ones[1..],carry,drops,desired,&mut|c,i,q|hook(c,i+1,q)));
 let bit=c.alloc_bit();c.hmr(carry,bit);c.x(acc[0]);for &r in row{c.cz_if(r,acc[0],bit);}if ones[0]{c.z_if(acc[0],bit);}c.x(acc[0]);c.free_bit(bit);c.release_clean(carry);true
}
