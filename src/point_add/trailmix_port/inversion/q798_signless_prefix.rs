//! Single prefix mask with direct high-rank predicates; no separate clean cache.
use crate::point_add::trailmix_port::circuit::{Circuit,QReg};
use super::length_recompute::mixed_mcx;
#[path="metadata_arithmetic5_programs.rs"] mod programs;
struct Range<'a>{rank:&'a[QReg],low:&'a[QReg],guards:&'a[(&'a QReg,bool)],mask:&'a QReg,dirty:&'a[QReg],threshold:usize}
impl Range<'_>{
    fn equality(&self,circ:&mut Circuit,value:usize,extra:&[(&QReg,bool)],target:&QReg){
        if value>255{return;}
        for &(m,v) in programs::A_EQUAL[value/64] {
            let mut cs=self.guards.to_vec();cs.extend((0..5).filter(|&i|m>>i&1!=0).map(|i|(&self.rank[i],v>>i&1!=0)));
            cs.extend((0..6).map(|i|(&self.low[i],value>>i&1!=0)));cs.extend_from_slice(extra);
            mixed_mcx(circ,&cs,target,self.dirty);
        }
    }
    fn set(&mut self,circ:&mut Circuit,t:usize){let t=t.min(256);for value in self.threshold.min(t)..self.threshold.max(t){self.equality(circ,value,&[],self.mask);}self.threshold=t;}
}
pub(super) fn prefix(circ:&mut Circuit,rank:&[QReg],source:&[QReg],target:&[QReg],low:&[QReg],guards:&[(&QReg,bool)],mask:&QReg,sign_out:Option<&QReg>,sign_control:Option<&QReg>,dirty:&[QReg],subtract:bool,n:usize){
    let start=circ.b.ops.len();let mut r=Range{rank,low,guards,mask,dirty,threshold:0};mixed_mcx(circ,guards,mask,dirty);
    let mut cells:Vec<(usize,u8,Vec<&QReg>,&QReg)>=Vec::new();
    for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}cells.push((0,3,vec![&source[0]],&target[0]));
    for i in (1..n).rev(){if let Some(z)=sign_out{cells.push((i,1,vec![&source[i]],z));}if i+1<n{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}}
    for i in 0..n{if i+1<n{cells.push((i+1,0,vec![&source[i],&target[i]],&source[i+1]));}if let Some(z)=sign_out{cells.push((i,1,vec![&source[i],&target[i]],z));}}
    for i in (1..n).rev(){cells.push((i,0,vec![&source[i]],&target[i]));cells.push((i,0,vec![&source[i-1],&target[i-1]],&source[i]));}
    for i in 1..n-1{cells.push((i+1,2,vec![&source[i]],&source[i+1]));}for i in 0..n{cells.push((i,2,vec![&source[i]],&target[i]));}
    for(i,tag,data,out)in cells{
        if tag==2{circ.cx(data[0],out);continue;}
        let mut extras:Vec<_>=data.iter().map(|&q|(q,true)).collect();if let Some(s)=sign_control{extras.push((s,false));}
        if tag==1{if i>=1{r.equality(circ,i-1,&extras,out);}continue;}
        let mut cs=guards.to_vec();if tag==0{r.set(circ,i.saturating_sub(1));cs.push((mask,true));}cs.extend(extras);mixed_mcx(circ,&cs,out,dirty);
    }
    r.set(circ,0);mixed_mcx(circ,guards,mask,dirty);
    if subtract{circ.b.ops[start..].reverse();}
}
