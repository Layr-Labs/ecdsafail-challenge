use super::builder::B;
use crate::circuit::QubitId;

fn inc_need(n:usize)->usize {
 if n<=1{return 0;}let(mut remaining,mut lower,mut depth)=(n-1,2usize,1usize);
 while remaining>lower+1{remaining-=lower+1;lower=2*lower+1;depth+=1;}depth
}



// Exact conditional source addition with a short source and an arbitrary
// long target. The source MAJ carry controls a unitary high-tail increment.
// GLOBAL work = c0,h,seven summary wires; no measured or clean source loan.




// Read-only hc gives cut L=288-hc. On active care 1<=hc<=m<=121.
// Arbitrary inactive source, target and header are unchanged. All workGLOBAL0.
use super::mask::{Dec,ge_const};
struct CutWriter<'a>{ hc:&'a[QubitId], pre:&'a[QubitId], f:QubitId,g:QubitId,lo:usize,dec:Dec<'a>,last:Option<usize> }
impl<'a>CutWriter<'a>{
 fn advance(&mut self,b:&mut B,i:usize)->bool{
  assert!(self.last.is_none_or(|old|i<old));self.last=Some(i);
  if i<self.lo{return false;}
  let lits=self.dec.ctrls(b,288-i-1);assert_eq!(lits.len(),1);b.cx(lits[0].0,self.f);true
 }
 fn ccx(&mut self,b:&mut B,a:QubitId,c:QubitId,t:QubitId,i:usize){
  if self.advance(b,i){b.and_c(a,self.f,self.g);b.ccx(self.g,c,t);b.and_u(a,self.f,self.g);}else{b.ccx(a,c,t);}
 }
 fn cx(&mut self,b:&mut B,a:QubitId,t:QubitId,i:usize){
  if self.advance(b,i){b.ccx(a,self.f,t);}else{b.cx(a,t);}
 }
 fn clear(&mut self,b:&mut B,shift:usize,chain:&[QubitId]){
  self.dec.clear(b);let max=288-shift.max(self.lo)-1;
  if max>=1{ge_const(b,self.hc,1,self.f,chain);ge_const(b,self.hc,(max+1)as isize,self.f,chain);}
 }
}
fn inc_cut_upper(b:&mut B,summary:QubitId,lower:&[QubitId],remaining:&[QubitId],anc:&[QubitId],offset:usize,w:&mut CutWriter){
 if remaining.is_empty(){return;}
 let size=remaining.len().min(lower.len()+1);let(head,rest)=remaining.split_at(size);
 for j in 1..size{let prev=if j==1{head[0]}else{lower[j-2]};b.x(lower[j-1]);b.ccx(prev,head[j],lower[j-1]);}
 if !rest.is_empty(){let last=if size==1{head[0]}else{lower[size-2]};let next=anc[0];b.ccx(summary,last,next);
  let mut known=lower.to_vec();known.extend_from_slice(head);inc_cut_upper(b,next,&known,rest,&anc[1..],offset+size,w);b.ccx(summary,last,next);}
 for j in(1..size).rev(){let prev=if j==1{head[0]}else{lower[j-2]};b.ccx(prev,head[j],lower[j-1]);b.x(lower[j-1]);w.ccx(b,summary,prev,head[j],offset+j);}
 w.cx(b,summary,head[0],offset);
}
fn inc_cut(b:&mut B,ctrl:QubitId,bits:&[QubitId],anc:&[QubitId],offset:usize,w:&mut CutWriter){
 if bits.is_empty(){return;}if bits.len()==1{w.cx(b,ctrl,bits[0],offset);return;}
 let need=inc_need(bits.len());assert!(anc.len()>=need);let summary=anc[0];b.ccx(ctrl,bits[0],summary);
 inc_cut_upper(b,summary,&[ctrl,bits[0]],&bits[1..],&anc[1..need],offset+1,w);
 b.ccx(ctrl,bits[0],summary);w.cx(b,ctrl,bits[0],offset);
}
fn add_cut_shift(b:&mut B,target:&[QubitId],q:&[QubitId],hc:&[QubitId],m:usize,shift:usize,active:QubitId,work:&[QubitId]){
 assert_eq!(target.len(),288);assert_eq!(hc.len(),8);assert!((1..=121).contains(&m));assert_eq!(work.len(),18);
 let(c0,h,f,g)=(work[0],work[1],work[9],work[10]);let pre=&work[11..18];let chi=287;let lo=288-m;
 if shift>=chi{return;}let len=q.len().min(chi-shift);let t=&target[shift..shift+len];let tail=&target[shift+len..chi];let s=&q[..len];
 let mut w=CutWriter{hc,pre,f,g,lo,dec:Dec::new(hc,pre),last:None};
 for i in 0..len{let carry=if i==0{c0}else{s[i-1]};b.cx(s[i],t[i]);b.cx(s[i],carry);b.ccx(carry,t[i],s[i]);}
 if !tail.is_empty(){b.ccx(active,s[len-1],h);inc_cut(b,h,tail,&work[2..9],shift+len,&mut w);b.ccx(active,s[len-1],h);}
 for i in(0..len).rev(){let carry=if i==0{c0}else{s[i-1]};b.ccx(carry,t[i],s[i]);b.cx(s[i],carry);b.cx(s[i],t[i]);
  b.cx(s[i],carry);w.ccx(b,active,carry,t[i],shift+i);b.cx(s[i],carry);
 }
 w.clear(b,shift,&work[2..9]);
}


pub fn correction(b:&mut B,target:&[QubitId],q:&[QubitId],hc:&[QubitId],m:usize,active:QubitId,work:&[QubitId]){
 assert_eq!(q.len(),26);let mut all=target.to_vec();all.extend(q);all.extend(hc);all.push(active);all.extend(work);let n=all.len();all.sort();all.dedup();assert_eq!(all.len(),n);
 for(shift,negative)in[(256,false),(32,true),(10,true),(5,false),(4,false),(0,true)]{
  b.begin();add_cut_shift(b,target,q,hc,m,shift,active,work);let r=b.end();b.play(&r,negative);
 }
}


