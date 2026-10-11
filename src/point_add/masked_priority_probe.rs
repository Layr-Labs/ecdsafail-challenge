//! Private exact masked priority probe. Unchanged cut envelope; bank globallyzero.
use super::{builder::{B,G},frogdrop::Cut,mask::{Dec,mc_xor,ge_const}};
use crate::circuit::QubitId;
fn compute_or(b:&mut B,a:Option<QubitId>,v:QubitId,t:QubitId){if let Some(a)=a{b.and_c(a,v,t);b.cx(a,t);b.cx(v,t);}else{b.cx(v,t);}}
fn erase_or(b:&mut B,a:Option<QubitId>,v:QubitId,t:QubitId){if let Some(a)=a{b.cx(v,t);b.cx(a,t);b.and_u(a,v,t);}else{b.cx(v,t);}}
fn onehot(b:&mut B,a:Option<QubitId>,v:QubitId,t:QubitId,out:&[QubitId],value:usize){
 let put=|b:&mut B,q|{for(i,&o)in out.iter().enumerate(){if value&(1usize<<i)!=0{b.cx(q,o);}}};
 if let Some(a)=a{b.x(a);b.and_c(a,v,t);b.x(a);put(b,t);b.x(a);b.and_u(a,v,t);b.x(a);}else{put(b,v);}
}
fn ge(b:&mut B,cut:&Cut,k:usize,t:QubitId,pre:&[QubitId]){
 if cut.neg{ge_const(b,&cut.v,cut.a-k as isize+1,t,pre);b.x(t);}else{ge_const(b,&cut.v,k as isize-cut.a,t,pre);}
}
fn val(cut:&Cut,l:usize)->Option<usize>{let x=if cut.neg{cut.a-l as isize}else{l as isize-cut.a};if x<0||x as usize>=(1usize<<cut.v.len()){None}else{Some(x as usize)}}
fn copy(b:&mut B,v:&[QubitId],cut:&Cut,clo:usize,chi:usize,bottom:usize,top:usize,cells:&[QubitId],f:QubitId,pre:&[QubitId],tmp:QubitId,dirty:&[QubitId])->Vec<G>{
 b.begin();let lo=bottom.max(clo);let hi=top.min(chi);
 if lo<hi {
  ge(b,cut,hi,f,pre);let mut dec=Dec::new(&cut.v,pre);
  for l in(lo..hi).rev(){if l+1<hi{if let Some(k)=val(cut,l+1){let c=dec.ctrls(b,k);mc_xor(b,&c,f,&[tmp],dirty);}}b.and_c(f,v[l],cells[top-1-l]);}
  dec.clear(b);ge(b,cut,lo+1,f,pre);
 }
 for l in bottom..top.min(clo){b.cx(v[l],cells[top-1-l]);}
 b.end()
}
pub fn emit(b:&mut B,v:&[QubitId],cut:&Cut,clo:usize,chi:usize,lo:usize,hi:usize,out:&[QubitId],bank:&[QubitId],dirty:&[QubitId]){
 assert!(lo<=hi&&hi<=v.len()&&clo<=chi);let n=hi-lo;if n==0{return;}
 let mut seen=std::collections::BTreeSet::new();for&q in bank{assert!(seen.insert(q));assert!(!v.contains(&q)&&!out.contains(&q)&&!cut.v.contains(&q)&&!dirty.contains(&q));}
 let np=cut.v.len().saturating_sub(1);assert!(bank.len()>np+2);let pre=&bank[..np];let f=bank[np];let masktmp=bank[np+1];let rest=&bank[np+2..];
 let chunk=(1..=n).filter(|&c|n.div_ceil(c)-1+2*c<=rest.len()).min_by_key(|&c|{let blocks=n.div_ceil(c);2*n+(blocks-1)*(c-1)+2*(blocks-1)*c+32*blocks}).expect("masked priority bank insufficient");
 let blocks=n.div_ceil(chunk);let nf=blocks-1;let flags=&rest[..nf];let cells=&rest[nf..nf+chunk];let work=&rest[nf+chunk..nf+2*chunk-1];let tmp=rest[nf+2*chunk-1];
 for j in 0..blocks {
  let top=hi-j*chunk;let bottom=lo.max(top.saturating_sub(chunk));let len=top-bottom;let incoming=j.checked_sub(1).map(|i|flags[i]);let mut prev=incoming;
  let cr=copy(b,v,cut,clo,chi,bottom,top,cells,f,pre,masktmp,dirty);b.play(&cr,false);
  for k in 0..len{onehot(b,prev,cells[k],tmp,out,top-k);if k+1<len{compute_or(b,prev,cells[k],work[k]);prev=Some(work[k]);}else if j<nf{compute_or(b,prev,cells[k],flags[j]);}}
  for k in(0..len-1).rev(){erase_or(b,if k==0{incoming}else{Some(work[k-1])},cells[k],work[k]);}
  b.play(&cr,true);
 }
 for j in(0..nf).rev(){
  let top=hi-j*chunk;let bottom=lo.max(top.saturating_sub(chunk));let len=top-bottom;let incoming=j.checked_sub(1).map(|i|flags[i]);let mut prev=incoming;
  let cr=copy(b,v,cut,clo,chi,bottom,top,cells,f,pre,masktmp,dirty);b.play(&cr,false);
  for k in 0..len-1{compute_or(b,prev,cells[k],work[k]);prev=Some(work[k]);}
  erase_or(b,prev,cells[len-1],flags[j]);for k in(0..len-1).rev(){erase_or(b,if k==0{incoming}else{Some(work[k-1])},cells[k],work[k]);}b.play(&cr,true);
 }
}
