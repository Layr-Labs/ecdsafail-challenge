//! Source-only skipped-branch witness. This is ONE combined predicate;
//! do not nest independent Y and S witness transfers on the same e bit.
use super::builder::{B,G};
use super::sum_size::SumSize;
use crate::circuit::QubitId;

#[derive(Clone,Copy)]
pub(crate) struct Guard{pub y:(usize,usize),pub sum_limit:isize}

fn cover(bits:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>>{
    assert!(lo<=hi&&hi<=1usize<<bits.len());let mut out=vec![];
    while lo<hi{
        let mut f=if lo==0{bits.len()}else{lo.trailing_zeros()as usize};
        f=f.min(bits.len());while lo+(1usize<<f)>hi{f-=1;}
        out.push((f..bits.len()).map(|i|(bits[i],lo>>i&1==0)).collect());lo+=1usize<<f;
    }out
}
impl Guard{
    pub(crate) fn terms(&self,meta:&SumSize,positive:bool)->Vec<Vec<(QubitId,bool)>>{
        assert!(1<=self.y.0&&self.y.0<=self.y.1&&self.y.1<=128);
        let bound=(self.sum_limit.saturating_add(1).max(0)as usize).min(32);
        let yt=cover(&meta.y,self.y.0-1,self.y.1);
        let st=if positive{cover(&meta.sum,0,bound)}else{cover(&meta.sum,bound,32)};
        let mut out=vec![];
        if !positive{
            out.extend(cover(&meta.y,0,self.y.0-1));out.extend(cover(&meta.y,self.y.1,128));
        }
        for y in yt{for s in &st{let mut t=y.clone();t.extend_from_slice(s);out.push(t);}}out
    }
    /// Forward e0: (A,e)->(A&G,A&!G). Body must be identity when
    /// narrowed A0 even if e1. Reverse this record only after that body.
    /// On inverse entry e=>A&G; reverse of the complete sandwich is exact.
    pub(crate) fn witness_record(&self,b:&mut B,meta:&SumSize,a:QubitId,e:QubitId,
        dirty:&[QubitId])->Vec<G>{
        assert!(a!=e);b.begin();
        meta.xor_terms(b,self.terms(meta,false),e,&[(a,false)],dirty);
        meta.xor_terms(b,self.terms(meta,false),a,&[(e,false)],dirty);
        b.end()
    }
    /// Ordinary positive gate, for park/fetch outside the witness epoch.
    pub(crate) fn xor(&self,b:&mut B,meta:&SumSize,target:QubitId,
        extra:&[(QubitId,bool)],dirty:&[QubitId]){
        meta.xor_terms(b,self.terms(meta,true),target,extra,dirty);
    }
}
