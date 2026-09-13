//! Strengthen the existing C2 high-A cache during the R00 comparator W.
//! C2 and scratch C3 are zero on phase00. Only the external center changes
//! Sign; arbitrary off-phase cache extensions cancel in literal W inverse.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
include!("q792_r00_lifetime_plans_r01.rs");
pub(super) struct Upper<'a>{word:Vec<&'a QReg>,cache:&'a QReg,scratch:&'a QReg,mask:&'a QReg,lo:usize,hi:usize,split:usize,last:Option<(usize,usize)>}
impl<'a> Upper<'a>{
    pub(super) fn new(c:&Circuit,rank:&'a[QReg],a:&'a[QReg],cache:&'a QReg,scratch:&'a QReg,mask:&'a QReg,end:usize)->Option<Self>{
        let(lo,hi)=c.q797_a_support.unwrap_or((0,256));let &(_,_,_,split)=R00_PLANS.iter().find(|p|(p.0,p.1,p.2)==(lo,hi,end))?;
        assert_eq!((rank.len(),a.len()),(4,6));let word=a.iter().chain(&rank[..2]).collect();
        Some(Self{word,cache,scratch,mask,lo,hi,split,last:None})
    }
    fn toggle(&self,c:&mut Circuit,m:usize,v:usize){
        let cs:Vec<_>=self.word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(i,&q)|(q,v>>i&1!=0)).collect();
        super::paired_clean_mcx::toggle(c,&cs,self.cache,self.scratch);
    }
    pub(super) fn equality(&mut self,c:&mut Circuit,value:usize){
        if !(self.lo..self.hi).contains(&value){return;}
        let h=value/64;let left=self.lo.max(h*64);let right=self.hi.min((h+1)*64);
        let low=(0..6).filter(|&b|left>>b!=(right-1)>>b).fold(0,|m,b|m|(1<<b));
        let m=(low&!((1<<self.split)-1))|if self.lo/64==(self.hi-1)/64{0}else{192};let v=value&m;
        if self.last!=Some((m,v)){self.clear(c);self.toggle(c,m,v);self.last=Some((m,v));}
        let mut cs=vec![(self.cache,true)];cs.extend((0..self.split).filter(|&b|low>>b&1!=0).map(|b|(self.word[b],value>>b&1!=0)));
        super::paired_clean_mcx::toggle(c,&cs,self.mask,self.scratch);
    }
    pub(super) fn clear(&mut self,c:&mut Circuit){if let Some((m,v))=self.last.take(){self.toggle(c,m,v);}}
}
