//! Exact paid HT quantum-window parking, preserving foreign window lanes.
//! active=pool54, q26=Q121..138+pool55..64, held qcache=pool0..26.
//! empty q slots become foreignbank26. work=pool26..54 GLOBAL0, all distinct.
//! Active care:1<=hc<=hy<=m<=121, hy-hc<=26; Q abovehc contains only
//! foreign window until hy and GLOBAL0 abovehy. False active0 arbitraryQ,
//! ring, hc/hy and heldq, with allwork GLOBAL0. Allfalse parking identity.
use super::{builder::{B,G},frogdrop::{crot_up,reg_add_into},mask::{Dec,ge_const,mc_xor}};
use crate::circuit::QubitId;
fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn gated_ge(b:&mut B,h:&[QubitId],k:usize,act:QubitId,out:QubitId,work:&[QubitId]){
 let rr=rec(b,|b|ge_const(b,h,k as isize,work[1],&work[2..2+h.len()-1]));
 b.play(&rr,false);b.ccx(act,work[1],out);b.play(&rr,true);
}
fn rotate(b:&mut B,v:&[QubitId],hc:&[QubitId],act:QubitId,e:QubitId,down:bool){
 // active hc<128; omitted hc7 is care-only and falseact masks every swap.
 let rr=rec(b,|b|for(k,&c)in hc[..7].iter().enumerate(){b.and_c(act,c,e);crot_up(b,e,v,1usize<<k);b.and_u(act,c,e);});b.play(&rr,down);
}
pub fn park(b:&mut B,v:&[QubitId],foreign:&[QubitId],hc:&[QubitId],hy:&[QubitId],act:QubitId,work:&[QubitId]){
 assert!(v.len()<=121&&v.len()>=26&&foreign.len()==26&&hc.len()==8&&hy.len()==8&&work.len()>=8);
 let mut seen=std::collections::BTreeSet::new();for&q in v.iter().chain(foreign).chain(hc).chain(hy).chain(work).chain(std::iter::once(&act)){assert!(seen.insert(q));}
 // Compute d=(hy-hc) mod32 in hy low5. Exact d<=26 on activecare.
 let diff=rec(b,|b|reg_add_into(b,&hy[..5],&hc[..5],&[],work[7]));b.play(&diff,true);
 rotate(b,v,hc,act,work[0],true);
 let f=work[0];gated_ge(b,&hy[..5],1,act,f,work);
 let mut dec=Dec::new(&hy[..5],&work[2..6]);
 for i in 0..26{b.cswap(f,v[i],foreign[i]);let mut cs=dec.ctrls(b,i+1);cs.push((act,false));mc_xor(b,&cs,f,&[work[6]],&[]);}
 dec.clear(b);gated_ge(b,&hy[..5],27,act,f,work);
 rotate(b,v,hc,act,work[0],false);b.play(&diff,false);
}
pub(super) fn swap_hy(b:&mut B,a:&[QubitId],t:&[QubitId],hy:&[QubitId],act:QubitId,work:&[QubitId]){
 let f=work[0];gated_ge(b,hy,1,act,f,work);let mut dec=Dec::new(hy,&work[2..9]);
 for i in 0..a.len(){b.cswap(f,a[i],t[i]);let mut cs=dec.ctrls(b,i+1);cs.push((act,false));mc_xor(b,&cs,f,&[work[9]],&[]);}
 dec.clear(b);gated_ge(b,hy,a.len()+1,act,f,work);
}






