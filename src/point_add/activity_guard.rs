//! Source-only skipped-branch witness. This is ONE combined predicate;
//! do not nest independent Y and S witness transfers on the same e bit.
use super::builder::{B,G};
use super::sum_size::SumSize;
use crate::circuit::QubitId;

#[derive(Clone,Copy)]
pub(crate) struct Guard{pub y:(usize,usize),pub sum_limit:isize}

#[path = "guard_parity.rs"]
mod guard_parity;

impl Guard {
    pub(crate) fn terms(&self, meta: &SumSize, positive: bool) -> Vec<Vec<(QubitId,bool)>> {
        assert!(1 <= self.y.0 && self.y.0 <= self.y.1 && self.y.1 <= 128);
        let bound = self.sum_limit.saturating_add(1).clamp(0,32) as u16;
        guard_parity::terms((self.y.0-1) as u16,self.y.1 as u16,bound,positive,&meta.y,&meta.sum)
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
