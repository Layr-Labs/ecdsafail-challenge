//! Exact radix4 source-preserving HT echo with paid overflow restoration.
//! Same Q770 physical slots: act=pool54, q26=pool0..26, work28=pool26..54.
//! Vacated Q121..138/pool55..64 is LIVE foreign26 and never scratch.
//! Source C full public m is clean of foreign only after paid parking.
use super::{builder::{B,G},frogdrop::{cadd_tail_and_mixed,crot_up},arith::{up_m,down_m,Dm},row_add::{Row,MuxSource,mux_best}};
use crate::circuit::QubitId;
fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn selectors(b:&mut B,lo:QubitId,prev:Option<QubitId>,hi:QubitId,sigma:QubitId,u:QubitId,tmp:QubitId){
 // sigma=!(lo XOR prev), u=[(hi,lo,prev) neither000 nor111].
 b.x(sigma);b.cx(lo,sigma);if let Some(p)=prev{b.cx(p,sigma);}
 b.cx(hi,u);if let Some(p)=prev{b.cx(p,u);}
 b.cx(hi,tmp);b.cx(lo,tmp);b.x(sigma);b.ccx(tmp,sigma,u);b.x(sigma);b.cx(lo,tmp);b.cx(hi,tmp);
}
pub(super) fn echo(b:&mut B,t:&[QubitId],c:&[QubitId],q:&[QubitId],act:QubitId,w:&[QubitId],dirty:&[QubitId],inverse:bool)->(usize,usize){
 assert_eq!(t.len(),c.len());assert_eq!(q.len(),26);assert_eq!(w.len(),28);
 let mut seen=std::collections::BTreeSet::new();for&a in t.iter().chain(c).chain(q).chain(w).chain(dirty).chain(std::iter::once(&act)){assert!(seen.insert(a));}
 let sigma=w[0];let u=w[1];let g=w[2];let pad=w[3];let h=w[4];let bank=&w[5..];let(mut mux,mut fallback)=(0,0);
 let rr=rec(b,|b|{
  // Exact unsigned radix4 guard: q25*C*2^26, then thirteen signed digits.
  if t.len()>26{b.and_c(act,q[25],g);cadd_tail_and_mixed(b,g,&t[26..],&c[..c.len()-26],&[],sigma,h,&[],dirty,bank);b.and_u(act,q[25],g);}
  for i in (0..13).rev(){let off=2*i;let n=t.len()-off;let source=&c[..n];let target=&t[off..];let hi=q[off+1];
   let sr=rec(b,|b|selectors(b,q[off],off.checked_sub(1).map(|j|q[j]),hi,sigma,u,pad));b.play(&sr,false);b.and_c(act,u,g);
   if let Some((cost,chunk))=mux_best(n,0,bank.len()).filter(|(cost,_)|*cost<=10*n){
    let _=cost;mux+=1;b.row_add(Row{signed_binary:false,mux:Some(MuxSource{sigma}),g,t:target.to_vec(),s:source.to_vec(),tail:vec![],c0:hi,h,bank:bank.to_vec(),dirty:dirty.to_vec(),chunk});
   }else{
    fallback+=1;
    // Unitariy mux fallback: C or2C mod2^n by rotating [Cprefix,pad0].
    // The occupied overflow pad is restored before selectors/HMR query it.
    let mut ext=source.to_vec();ext.push(pad);let rotation=rec(b,|b|crot_up(b,sigma,&ext,1));b.play(&rotation,false);
    for&a in source{b.cx(hi,a);}let up=up_m(b,target,source,hi,false);let down=down_m(b,target,source,hi,Dm::Cond(g),false);b.play(&up,false);b.play(&down,false);for&a in source{b.cx(hi,a);}b.play(&rotation,true);
   }
   b.and_u(act,u,g);b.play(&sr,true);
  }
 });b.play(&rr,inverse);(mux,fallback)
}




