//! GPU-selected persistent prefixes on metadata rails with proved lifetimes.
//! General T10: a schedule-fixed A-chart rail is restored before chart closure.
//! C1: C4/C5 are zero on g and remain private through the whole arithmetic.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
include!("q792_lifetime_plans_r01.rs");
fn paired(c:&mut Circuit,cs:&[(&QReg,bool)],out:&QReg,g:&QReg){
    c.x(g);super::paired_clean_mcx::toggle(c,cs,out,g);c.x(g);
}
// E_m(v) XOR E_m(w) becomes one (k-1)-literal equality after
// an affine frame aligns every changed bit with one pivot. This updates
// a live memo directly and restores the input coordinates immediately.
fn paired_delta(c:&mut Circuit,word:&[&QReg],m:usize,v:usize,old:usize,out:&QReg,g:&QReg){
    let delta=(v^old)&m;assert_ne!(delta,0);let pivot=delta.trailing_zeros()as usize;
    for i in 0..word.len(){if i!=pivot&&delta>>i&1!=0{c.cx(word[pivot],word[i]);}}
    let transformed=v^if v>>pivot&1!=0{delta&!(1<<pivot)}else{0};
    let cs:Vec<_>=word.iter().enumerate().filter(|(i,_)|m>>i&1!=0&&*i!=pivot).map(|(i,&q)|(q,transformed>>i&1!=0)).collect();
    paired(c,&cs,out,g);
    for i in (0..word.len()).rev(){if i!=pivot&&delta>>i&1!=0{c.cx(word[pivot],word[i]);}}
}
fn low_mask(lo:usize,hi:usize,value:usize)->usize{
    let h=value/64;let left=lo.max(h*64);let right=hi.min((h+1)*64);assert!(left<right);
    (0..6).filter(|&b|left>>b!=(right-1)>>b).fold(0,|m,b|m|(1<<b))
}
pub(super) struct General<'a>{word:Vec<&'a QReg>,g:&'a QReg,mask:&'a QReg,lo:usize,hi:usize,fixed:usize,known:bool,wire:usize,split:usize,last:Option<(usize,usize)>}
impl<'a> General<'a>{
    pub(super) fn begin(c:&mut Circuit,rank:&'a[QReg],a:&'a[QReg],g:&'a QReg,mask:&'a QReg,n:usize)->Option<Self>{
        let (lo,hi)=c.q797_a_support.unwrap_or((0,256));
        let &(_,_,_,fixed,value,wire,split)=GENERAL.iter().find(|p|(p.0,p.1,p.2)==(lo,hi,n))?;
        assert_eq!((rank.len(),a.len()),(5,6));assert!(fixed>>wire&1!=0);
        let word:Vec<_>=rank.iter().chain(a).collect();let known=value>>wire&1!=0;
        if known{c.x(word[wire]);}
        Some(Self{word,g,mask,lo,hi:hi.min(252),fixed,known,wire,split,last:None})
    }
    fn toggle(&self,c:&mut Circuit,m:usize,v:usize){
        assert_eq!(m>>self.wire&1,0);
        let cs:Vec<_>=self.word.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(i,&q)|(q,v>>i&1!=0)).collect();
        paired(c,&cs,self.word[self.wire],self.g);
    }
    pub(super) fn equality(&mut self,c:&mut Circuit,value:usize){
        if !(self.lo..self.hi).contains(&value){return;}
        let h=value/64;let low=low_mask(self.lo,self.hi,value)<<5;
        let (pm,pv)=match h{0=>(16,0),1=>(24,16),2=>(28,24),3=>(28,28),_=>unreachable!()};
        let m=(low&!((1<<(5+self.split))-1))|(pm&!self.fixed);
        let v=(((value&63)<<5)|pv)&m;
        if self.last!=Some((m,v)){
            if let Some((om,ov))=self.last.filter(|&(om,ov)|om==m&&ov!=v){
                assert_eq!(om>>self.wire&1,0);paired_delta(c,&self.word,m,v,ov,self.word[self.wire],self.g);
            }else{if let Some((om,ov))=self.last{self.toggle(c,om,ov);}self.toggle(c,m,v);}
            self.last=Some((m,v));
        }
        let mut cs=vec![(self.word[self.wire],true)];
        for b in 0..self.split{if low>>(b+5)&1!=0{assert_ne!(b+5,self.wire);cs.push((self.word[b+5],value>>b&1!=0));}}
        paired(c,&cs,self.mask,self.g);
    }
    pub(super) fn known_value(&self)->bool{self.known}
    pub(super) fn rail(&self)->&QReg{self.word[self.wire]}
    pub(super) fn finish(&mut self,c:&mut Circuit){
        if let Some((m,v))=self.last.take(){self.toggle(c,m,v);}
        if self.known{c.x(self.word[self.wire]);}
    }
}

pub(super) struct C1Cache<'a>{a:&'a[QReg],high:&'a QReg,one:&'a QReg,two:&'a QReg,g:&'a QReg,mask:&'a QReg,lo:usize,hi:usize,s1:usize,s2:usize,last1:Option<(usize,usize)>,last2:Option<(usize,usize)>}
impl<'a>C1Cache<'a>{
    pub(super) fn new(c:&Circuit,a:&'a[QReg],high:&'a QReg,one:&'a QReg,two:&'a QReg,g:&'a QReg,mask:&'a QReg,n:usize)->Option<Self>{
        let(lo,hi)=c.q797_a_support.unwrap_or((0,256));let &(_,_,_,s1,s2)=C1.iter().find(|p|(p.0,p.1,p.2)==(lo,hi,n))?;
        Some(Self{a,high,one,two,g,mask,lo,hi,s1,s2,last1:None,last2:None})
    }
    fn toggle(&self,c:&mut Circuit,second:bool,m:usize,v:usize){
        let mut cs:Vec<_>=self.a.iter().enumerate().filter(|(i,_)|m>>i&1!=0).map(|(i,q)|(q,v>>i&1!=0)).collect();
        if m&64!=0{cs.push((if second{self.one}else{self.high},true));}
        paired(c,&cs,if second{self.two}else{self.one},self.g);
    }
    fn clear2(&mut self,c:&mut Circuit){if let Some((m,v))=self.last2.take(){self.toggle(c,true,m,v);}}
    /// Must run before the caller mutates the high-cache control.
    pub(super) fn clear(&mut self,c:&mut Circuit){
        self.clear2(c);if let Some((m,v))=self.last1.take(){self.toggle(c,false,m,v);}
    }
    pub(super) fn equality(&mut self,c:&mut Circuit,value:usize,use_high:bool){
        assert!((self.lo..self.hi).contains(&value));
        let low=low_mask(self.lo,self.hi,value);let m1=(low&!((1<<self.s1)-1))|if use_high{64}else{0};let v1=(value|64)&m1;
        if self.last1!=Some((m1,v1)){
            self.clear2(c);
            if let Some((om,ov))=self.last1.filter(|&(om,ov)|om==m1&&ov!=v1){
                let word:Vec<_>=self.a.iter().chain(std::iter::once(self.high)).collect();paired_delta(c,&word,om,v1,ov,self.one,self.g);
            }else{if let Some((om,ov))=self.last1{self.toggle(c,false,om,ov);}self.toggle(c,false,m1,v1);}
            self.last1=Some((m1,v1));
        }
        let (output,split)=if self.s2==7{(self.one,self.s1)}else{
            let m2=(low&((1<<self.s1)-1)&!((1<<self.s2)-1))|64;let v2=(value|64)&m2;
            if self.last2!=Some((m2,v2)){
                if let Some((om,ov))=self.last2.filter(|&(om,ov)|om==m2&&ov!=v2){
                    let word:Vec<_>=self.a.iter().chain(std::iter::once(self.one)).collect();paired_delta(c,&word,om,v2,ov,self.two,self.g);
                }else{self.clear2(c);self.toggle(c,true,m2,v2);}
                self.last2=Some((m2,v2));
            }
            (self.two,self.s2)
        };
        let mut cs=vec![(output,true)];cs.extend((0..split).filter(|&b|low>>b&1!=0).map(|b|(&self.a[b],value>>b&1!=0)));
        paired(c,&cs,self.mask,self.g);
    }
}

#[path="q792_lifetime_cache_check_r01.rs"]mod check;
pub fn run(){check::run();}
