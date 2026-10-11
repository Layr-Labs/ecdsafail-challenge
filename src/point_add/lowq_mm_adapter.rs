//! Port of public d8e49fb / commit f84ef0e (Claude Opus 5.5), integrated into
//! the inherited SKY-COF caller. Local chunk phase repair is exact; finite
//! global fold/compare windows remain role guard/compare parameters.
use super::builder::Builder;
use super::lowq_mm_exact::{self as kernel,Circ,Kind,P,Q};
use crate::circuit::{BitId,NO_BIT};
impl Circ for Builder {
    fn q(&mut self)->Q {self.alloc_qubit()}
    fn free(&mut self,q:Q){self.release_clean(q)}
    fn bit(&mut self)->BitId{self.alloc_bit()}
    fn free_bit(&mut self,b:BitId){Builder::free_bit(self,b)}
    fn x(&mut self,t:Q){Builder::x(self,t)}
    fn z(&mut self,t:Q){self.z_if(t,NO_BIT)}
    fn cx(&mut self,a:Q,t:Q){Builder::cx(self,a,t)}
    fn ccx(&mut self,a:Q,b:Q,t:Q){Builder::ccx(self,a,b,t)}
    fn cz(&mut self,a:Q,b:Q){Builder::cz(self,a,b)}
    fn cz_if(&mut self,a:Q,b:Q,m:BitId){Builder::cz_if(self,a,b,m)}
    fn hmr(&mut self,t:Q,m:BitId){Builder::hmr(self,t,m)}
    fn push(&mut self,m:BitId){self.push_condition(m)}
    fn pop(&mut self){self.pop_condition()}
}
fn kind(k:usize,neg:bool)->Kind {
    match(k,neg){(0,false)=>Kind::Mu,(kernel::MUC_K,true)=>Kind::MuC,
        _=>panic!("exact-local signed kernel unsupported scale/sign k={k} neg={neg}")}
}
fn parameters(cfg:super::skycof_mm::Cfg)->P {
    let cbits=super::skycof_mm::Field::secp().cbits();
    assert!(cfg.fold_w>=cbits);
    // The signed correction contains ±2c: retain the inherited guard,
    // so sw=34+guard, one bit beyond old33+guard. Pure half sh=32+guard.
    P{g:cfg.fold_w-cbits,cw:cfg.cmp_w,room:cfg.room}
}
pub(crate) fn mulf(c:&mut Builder,cfg:super::skycof_mm::Cfg,a:&[Q],b:&[Q],k:usize,neg:bool)->Vec<Q>{
    assert_eq!(a.len(),kernel::N);assert_eq!(b.len(),kernel::N);
    let p=parameters(cfg);let before=c.active_qubits();
    let out=kernel::product_fwd(c,&p,kind(k,neg),a,b);
    assert_eq!(c.active_qubits(),before+kernel::N as u32,"kernel producer leaked owners");
    out
}
pub(crate) fn mulf_inv(c:&mut Builder,cfg:super::skycof_mm::Cfg,a:&[Q],b:&[Q],k:usize,neg:bool,out:Vec<Q>){
    assert_eq!(a.len(),kernel::N);assert_eq!(b.len(),kernel::N);assert_eq!(out.len(),kernel::N);
    let p=parameters(cfg);let before=c.active_qubits();
    kernel::product_inv(c,&p,kind(k,neg),a,b,out);
    assert_eq!(c.active_qubits()+kernel::N as u32,before,"kernel inverse leaked owners");
}
