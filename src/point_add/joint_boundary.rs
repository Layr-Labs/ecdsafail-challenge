//! Raw column-boundary size/phase/high-Q readers.
//!
//! This is deliberately distinct from midg::joint_size. Between columns
//! HR has Q=t_previous<t_current, whereas HT may have up to31 additional
//! Q bits. The two aligned envelopes have192 and1152 values respectively;
//! their union still fits below1344 and leaves the inherited binary done
//! class at1536. The pre-map epoch reverses which active phase is narrow;
//! size and data readers are unchanged, only logical-phase decoding flips.

use crate::circuit::QubitId;
use super::builder::B;
use super::frogdrop_col::Fd;
use super::mask::mc_xor;
use super::midg::joint_size::View;
use std::collections::BTreeSet;

pub(crate) const HT_OFFSET:usize=192;
pub(crate) const ACTIVE_END:usize=1344;
pub(crate) const DONE_BASE:usize=1536;

#[derive(Clone,Debug)]
pub(crate) struct BoundaryView {
    pub low:[QubitId;5],
    pub high:[QubitId;6],
    /// Only the active class is reversed; done remains logical PH=1.
    pub pre_map:bool,
}
impl BoundaryView {
    pub(crate) const HT_OFFSET:usize=HT_OFFSET;
    pub(crate) fn from_fd(fd:&Fd)->Self {
        assert_eq!(fd.sy.len(),5);assert_eq!(fd.q.len(),128);
        Self{low:fd.sy.as_slice().try_into().unwrap(),
            high:[fd.q[123],fd.q[124],fd.q[125],fd.q[126],fd.q[127],fd.ph],pre_map:false}
    }
    pub(crate) fn pre_map(fd:&Fd)->Self {let mut v=Self::from_fd(fd);v.pre_map=true;v}
    pub(crate) fn ports(&self)->Vec<QubitId> {self.low.iter().chain(&self.high).copied().collect()}
    pub(crate) fn word(&self)->Vec<QubitId> {self.ports()}

    pub(crate) fn interval(size:usize,wide:bool)->(usize,usize) {
        assert!((1..=128).contains(&size));
        if wide {
            match size {
                1..=92=>(size-1,0),93=>(92,1),94=>(96,2),95=>(104,3),96=>(112,4),
                _=>(128+32*(size-97),5),
            }
        }else{
            match size {
                1..=123=>(size-1,0),124=>(124,1),125=>(128,2),126=>(136,3),127=>(144,4),128=>(160,5),
                _=>unreachable!(),
            }
        }
    }
    fn class_range_terms(&self,lo:usize,hi:usize,wide:bool)->Vec<Vec<(QubitId,bool)>> {
        let lo=lo.max(1);let hi=hi.min(128);if lo>hi{return vec![];}
        let (first,_)=Self::interval(lo,wide);let(last,free)=Self::interval(hi,wide);
        let offset=if wide {HT_OFFSET}else{0};
        View::interval_terms(&self.word(),offset+first,offset+last+(1<<free))
    }
    pub(crate) fn size_terms(&self,lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>> {
        let mut terms=self.class_range_terms(lo,hi,false);
        terms.extend(self.class_range_terms(lo,hi,true));
        let (lo,hi)=(lo.max(1),hi.min(26));
        if lo<=hi {terms.extend(View::interval_terms(&self.word(),DONE_BASE+16*(lo-1),DONE_BASE+16*hi));}
        terms
    }
    fn toggle(&self,b:&mut B,terms:Vec<Vec<(QubitId,bool)>>,target:QubitId,
        extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
        let mut used:BTreeSet<_>=self.ports().into_iter().collect();used.insert(target);
        used.extend(extra.iter().map(|&(q,_)|q));
        for &q in clean {assert!(used.insert(q),"boundary query clean owner aliases a port");}
        let mut seen=BTreeSet::new();
        let bank:Vec<_>=dirty.iter().copied().filter(|q|!used.contains(q)&&seen.insert(*q)).collect();
        for mut term in terms {
            let mut contradiction=false;
            for &(q,neg) in extra {
                if let Some(&(_,old))=term.iter().find(|(p,_)|*p==q) {
                    if old!=neg {contradiction=true;break;}
                }else{term.push((q,neg));}
            }
            if contradiction {continue;}
            assert!(!term.iter().any(|&(q,_)|q==target));
            mc_xor(b,&term,target,clean,&bank);
        }
    }
    pub(crate) fn xor_range(&self,b:&mut B,lo:usize,hi:usize,target:QubitId,
        extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
        self.toggle(b,self.size_terms(lo,hi),target,extra,clean,dirty);
    }
    pub(crate) fn xor_eq(&self,b:&mut B,size:usize,target:QubitId,
        extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
        self.xor_range(b,size,size,target,extra,clean,dirty);
    }
    pub(crate) fn xor_le(&self,b:&mut B,limit:usize,target:QubitId,
        extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
        self.xor_range(b,1,limit,target,extra,clean,dirty);
    }
    pub(crate) fn xor_bit(&self,b:&mut B,bit:usize,target:QubitId,
        extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
        assert!(bit<8);let step=1usize<<bit;
        for lo in (step..=128).step_by(2*step) {
            self.xor_range(b,lo,(lo+step-1).min(128),target,extra,clean,dirty);
        }
    }
    pub(crate) fn xor_phase(&self,b:&mut B,target:QubitId,extra:&[(QubitId,bool)],
        dirty:&[QubitId]) {
        let mut terms=if self.pre_map {View::interval_terms(&self.word(),0,HT_OFFSET)}
            else{View::interval_terms(&self.word(),HT_OFFSET,ACTIVE_END)};
        terms.extend(View::interval_terms(&self.word(),DONE_BASE,2048));
        self.toggle(b,terms,target,extra,&[],dirty);
    }
    pub(crate) fn xor_done(&self,b:&mut B,target:QubitId,extra:&[(QubitId,bool)],dirty:&[QubitId]) {
        self.toggle(b,View::interval_terms(&self.word(),DONE_BASE,2048),target,extra,&[],dirty);
    }
    /// Read logical Q123..127. The original high bit is a free low code
    /// bit only in branches with sufficient capacity; elsewhere it is a
    /// known zero. On done Q123..126 are H4, while Q127 is zero after the
    /// public159 relocation (and was zero before it).
    pub(crate) fn xor_q_high_bit(&self,b:&mut B,bit:usize,target:QubitId,
        extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
        assert!(bit<5);
        let mut terms=self.class_range_terms(124+bit,128,false);
        terms.extend(self.class_range_terms(93+bit,128,true));
        if bit<4 {terms.extend(View::interval_terms(&self.word(),DONE_BASE,2048));}
        for term in &mut terms {assert!(!term.iter().any(|&(q,_)|q==self.low[bit]));term.push((self.low[bit],false));}
        self.toggle(b,terms,target,extra,clean,dirty);
    }
}
