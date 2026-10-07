//! Apex-only T H, same V^-1 C W^-1 Q W C^-1 V on A253/254.
//! Source lowA plus known 2^A; source[A:A+2] is arbitrary packed cargo.
//! On g, upper is253 or254 and mask/carry are zero. Off g arbitrary identity.
//! The only range endpoints are0/253/254. Top gathering reads only253..255.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
fn dirty(c:&mut Circuit,cs:&[&QReg],out:&QReg,d:&[QReg]){match cs.len(){0=>c.x(out),1=>c.cx(cs[0],out),2=>c.ccx(cs[0],cs[1],out),n=>{assert!(d.len()>=n-2);let ds=&d[..n-2];for seed in[true,false]{if seed{c.ccx(cs[0],cs[1],&ds[0]);}for i in 1..ds.len(){c.ccx(&ds[i-1],cs[i+1],&ds[i]);}c.ccx(ds.last().unwrap(),cs[n-1],out);for i in(1..ds.len()).rev(){c.ccx(&ds[i-1],cs[i+1],&ds[i]);}if seed{c.ccx(cs[0],cs[1],&ds[0]);}}}}}
fn swap(c:&mut Circuit,g:&QReg,a:&QReg,b:&QReg){c.cx(b,a);c.ccx(g,a,b);c.cx(b,a);}
struct E<'a>{x:&'a[QReg],y:&'a[QReg],upper:&'a[QReg],q:&'a QReg,g:&'a QReg,mask:&'a QReg,carry:&'a QReg,d:&'a[QReg]}
impl E<'_>{
 fn range(&self,c:&mut Circuit,i:usize){match i{0=>c.cx(self.g,self.mask),253=>c.ccx(self.g,&self.upper[0],self.mask),254=>{c.x(&self.upper[0]);c.ccx(self.g,&self.upper[0],self.mask);c.x(&self.upper[0]);},_=>{}}}
 fn tail(&self,c:&mut Circuit){for i in(0..self.x.len()).rev(){c.x(self.g);super::paired_clean_mcx::toggle(c,&[(self.mask,true),(&self.y[i],true),(&self.x[i],true)],self.carry,self.g);c.x(self.g);c.cx(self.carry,&self.x[i]);c.cx(&self.x[i],&self.y[i]);c.cx(self.carry,&self.x[i]);dirty(c,&[self.g,self.mask,&self.x[i],self.q],&self.y[i],self.d);c.cx(self.carry,&self.x[i]);let at=c.b.ops.len();self.range(c,i);c.b.ops[at..].reverse();}}
 fn prep<'b>(&'b self,c:&mut Circuit)->(&'b QReg,&'b QReg){
  let s1=&self.x[253];let t1=&self.y[253];let s0=&self.x[254];let t0=&self.y[254];
  c.x(&self.upper[0]);swap(c,&self.upper[0],s1,&self.x[255]);swap(c,&self.upper[0],t1,&self.y[255]);c.x(&self.upper[0]);
  swap(c,&self.upper[0],s0,s1);swap(c,&self.upper[0],t0,t1);c.cx(s0,t0);c.cx(s1,t1);(t0,t1)
 }
 fn w(&self,c:&mut Circuit,t0:&QReg,t1:&QReg){dirty(c,&[self.g,self.q,self.carry],t1,self.d);c.x(self.carry);c.x(t0);dirty(c,&[self.g,self.q,self.carry,t0],t1,self.d);c.x(t0);dirty(c,&[self.g,self.q,self.carry],t0,self.d);c.x(self.carry);}
 fn compare(&self,c:&mut Circuit,t0:&QReg,t1:&QReg){c.cx(self.g,self.q);dirty(c,&[self.g,self.carry,t1],self.q,self.d);c.x(self.carry);c.x(t0);c.x(t1);dirty(c,&[self.g,self.carry,t0,t1],self.q,self.d);c.x(t1);c.x(t0);c.x(self.carry);}
}
pub(super)fn emit(c:&mut Circuit,x:&[QReg],y:&[QReg],upper:&[QReg],q:&QReg,g:&QReg,mask:&QReg,carry:&QReg,d:&[QReg]){assert_eq!(x.len(),256);assert_eq!(upper.len(),8);assert_eq!(x.len(),y.len());assert!(d.len()>=18);let owned=c.b.next_qubit;let e=E{x,y,upper,q,g,mask,carry,d};let at=c.b.ops.len();e.tail(c);let v=c.b.ops[at..].to_vec();c.b.ops[at..].reverse();let at=c.b.ops.len();let(t0,t1)=e.prep(c);let cp=c.b.ops[at..].to_vec();let at=c.b.ops.len();e.w(c,t0,t1);let w=c.b.ops[at..].to_vec();c.b.ops[at..].reverse();e.compare(c,t0,t1);c.b.ops.extend(w);c.b.ops.extend(cp.into_iter().rev());c.b.ops.extend(v);assert_eq!(c.b.next_qubit,owned);}
