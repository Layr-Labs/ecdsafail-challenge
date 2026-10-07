//! Persistent A-prefix in one existing conditionally clean padding loan.
//! Consecutive Gray prefix labels differ by one bit: XOR of their equality
//! predicates is the equality on all remaining bits. No data is measured.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
const SPLIT:usize=3;
pub(super) fn enabled(c:&Circuit,n:usize)->bool{
    let(lo,hi)=c.q797_a_support.unwrap_or((0,256));n>=64&&hi-lo>=64
}
pub(super) struct Gray<'a>{rank:&'a[QReg],a:&'a[QReg],g:&'a QReg,mask:&'a QReg,memo:&'a QReg,lo:usize,hi:usize,last:Option<(usize,usize)>}
impl<'a> Gray<'a>{
    pub(super) fn current(&self)->Option<(usize,usize)>{self.last}
    pub(super) fn new(c:&Circuit,rank:&'a[QReg],a:&'a[QReg],g:&'a QReg,mask:&'a QReg,memo:&'a QReg)->Self{
        let(lo,hi)=c.q797_a_support.unwrap_or((0,256));
        Self{rank,a,g,mask,memo,lo,hi,last:None}
    }
    fn toggle(&self,c:&mut Circuit,h:usize,code:usize,omit:Option<usize>){
        // A is restored immediately, so other arithmetic continues to see
        // its ordinary binary representation while the predicate persists.
        for b in SPLIT..5{c.cx(&self.a[b+1],&self.a[b]);}
        let mut cs=if self.lo/64==(self.hi-1)/64{Vec::new()}else{super::super::q792_t10_a_chart_r01::prefix(self.rank,h)};
        for b in SPLIT..6{if omit!=Some(b-SPLIT){cs.push((&self.a[b],code>>(b-SPLIT)&1!=0));}}
        c.x(self.g);super::super::paired_clean_mcx::toggle(c,&cs,self.memo,self.g);c.x(self.g);
        for b in (SPLIT..5).rev(){c.cx(&self.a[b+1],&self.a[b]);}
    }
    pub(super) fn equality(&mut self,c:&mut Circuit,value:usize){
        if !(self.lo..self.hi).contains(&value){return;}
        let h=value/64;let raw=(value&63)>>SPLIT;let code=raw^(raw>>1);
        if self.last!=Some((h,code)){
            match self.last{
                Some((old_h,old_code)) if old_h==h&&(old_code^code).is_power_of_two()=>{
                    self.toggle(c,h,code,Some((old_code^code).trailing_zeros()as usize));
                },
                Some((old_h,old_code))=>{self.toggle(c,old_h,old_code,None);self.toggle(c,h,code,None);},
                None=>self.toggle(c,h,code,None),
            }
            self.last=Some((h,code));
        }
        let left=self.lo.max(h*64);let right=self.hi.min((h+1)*64);
        let mut cs=vec![(self.memo,true)];
        for b in 0..SPLIT{if left>>b!=(right-1)>>b{cs.push((&self.a[b],value>>b&1!=0));}}
        c.x(self.g);super::super::paired_clean_mcx::toggle(c,&cs,self.mask,self.g);c.x(self.g);
    }
    pub(super) fn finish(&mut self,c:&mut Circuit){
        if let Some((h,code))=self.last.take(){self.toggle(c,h,code,None);}
    }
}
