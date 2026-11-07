//! SOURCE-ONLY active-coordinate compression. Not registered or compiled.
//! First retain A=(original activity)&Y-band&sum-bound outside this module.
//! Normalize E7 to R-lo modulo128. On A, only ceil(log2(hi-lo+1)) bits
//! contain information; the remaining E bits and guard-forced S high bits
//! may be used as conditionally zero arithmetic/decoder owners.
//! Every borrowed cell must return before the inverse coordinate record.

use super::builder::{B,G};
use super::mask::mc_xor;
use super::sum_size::SumSize;
use super::ttk_virtual_leading::Size;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn bits_for(maximum:usize)->usize{
    if maximum==0{0}else{usize::BITS as usize-maximum.leading_zeros()as usize}
}

pub(crate) struct SizeWindow<'a>{
    pub meta:&'a SumSize,
    pub kind:Size,
    pub lo:usize,
    pub hi:usize,
    pub width:usize,
    pub sum_width:usize,
    high_y_z:bool,
}
impl<'a> SizeWindow<'a>{
    /// Caller proves A=>lo<=R<=hi and A=>S<=sum_limit BEFORE entry.
    /// On SizeZ require hi-lo<128, making Zmod128 injective on A.
    pub(crate) fn new(meta:&'a SumSize,kind:Size,lo:usize,hi:usize,sum_limit:usize)->Self{
        assert!(1<=lo&&lo<=hi&&hi-lo<128&&sum_limit<=31);
        match kind{Size::Y=>assert!(hi<=128),Size::Z=>assert!(98<=lo&&hi<=256)}
        Self{meta,kind,lo,hi,width:bits_for(hi-lo),sum_width:bits_for(sum_limit),high_y_z:false}
    }
    /// Additional joint compression for A=>121<=Y<=128. Retain y=Y-121
    /// in S.low3 instead of retaining all S5. E becomes Z-lo. Thus the
    /// two S high bits and at least one E high bit are conditional zero,
    /// including the first digit where the original S guard allows31.
    /// No original-S predicate may run until this epoch is reversed.
    pub(crate) fn high_y_z(meta:&'a SumSize,lo:usize,hi:usize,y_band:(usize,usize))->Self{
        assert!(121<=y_band.0&&y_band.0<=y_band.1&&y_band.1<=128);
        assert!(98<=lo&&lo<=hi&&hi<=136);
        Self{meta,kind:Size::Z,lo,hi,width:bits_for(hi-lo),sum_width:3,high_y_z:true}
    }
    pub(crate) fn address(&self)->&[QubitId]{&self.meta.y[..self.width]}
    /// These cells are zero ONLY on retained A. They cannot be read as
    /// metadata while borrowed and cannot use a measured dirty uncompute.
    pub(crate) fn spares(&self)->Vec<QubitId>{
        self.meta.y[self.width..].iter().chain(&self.meta.sum[self.sum_width..]).copied().collect()
    }
    /// Full7-bit reversible coordinate change on every basis state.
    /// Off A it merely chooses an arbitrary reversible completion; body
    /// must return all state there before this record is reversed.
    pub(crate) fn entry_record(&self,b:&mut B,dirty:&[QubitId])->Vec<G>{
        let mut used:BTreeSet<_>=self.meta.y.iter().chain(&self.meta.sum).copied().collect();
        let bank:Vec<_>=dirty.iter().copied().filter(|q|used.insert(*q)).collect();
        assert!(bank.len()>=7); // a general seven-bit constant may use an odd NAF digit
        b.begin();
        if self.high_y_z{
            // E=Y-1 -> y=Y-121. On A, y occupies only three bits.
            super::frogdrop::add_const_dirty_exact(b,&self.meta.y,8,&bank);
            for i in 0..5{
                b.cx(self.meta.y[i],self.meta.sum[i]);
                b.cx(self.meta.sum[i],self.meta.y[i]);
                b.cx(self.meta.y[i],self.meta.sum[i]);
            }
            // E now holds original S, sum holds y. Exact zero extension
            // uses two arbitrary restored dirty padding bits, not helpers.
            let padded:Vec<_>=self.meta.sum.iter().chain(&bank[..2]).copied().collect();
            b.begin();super::arith::ttk_add(b,&padded,&self.meta.y,None,None);
            let subtraction=b.end();b.play(&subtraction,true);
            super::arith::ttk_add(b,&bank[..2],&self.meta.y[5..],None,None);
            // Z=105+originalS-y; E=Z-lo on A, modulo128 everywhere.
            let constant=(105isize-self.lo as isize).rem_euclid(128)as usize;
            super::frogdrop::add_const_dirty_exact(b,&self.meta.y,constant,&bank);
        }else{
            if matches!(self.kind,Size::Z){let z=self.meta.z_epoch(b,&bank);b.play(&z,false);}
            let base=match self.kind{Size::Y=>self.lo-1,Size::Z=>self.lo%128};
            super::frogdrop::add_const_dirty_exact(b,&self.meta.y,(128-base)%128,&bank);
        }
        b.end()
    }
}

/// Literal prefix cache over the compressed address. Prefixes need be
/// zero only on retained A. Every query explicitly includes A, including
/// queries used inside paired preparation tapes. All prefixes are undone
/// with CCX, never measured AND cleanup.
pub(crate) struct WindowDecoder<'a,'m>{
    window:&'a SizeWindow<'m>,pre:&'a [QubitId],activity:QubitId,cur:Option<usize>,
}
impl<'a,'m> WindowDecoder<'a,'m>{
    pub(crate) fn new(window:&'a SizeWindow<'m>,pre:&'a [QubitId],activity:QubitId)->Self{
        assert!(pre.len()<=window.width.saturating_sub(1));
        assert!(!window.address().contains(&activity)&&!pre.contains(&activity));
        let mut used=BTreeSet::new();
        assert!(window.address().iter().chain(pre).all(|q|used.insert(*q)));
        Self{window,pre,activity,cur:None}
    }
    fn cell(&self,b:&mut B,i:usize,v:usize){
        let n=self.window.width;let addr=self.window.address();
        let(a,na)=if i==0{(addr[n-1],v>>(n-1)&1==0)}else{(self.pre[i-1],false)};
        let(c,nc)=(addr[n-2-i],v>>(n-2-i)&1==0);
        if na{b.x(a);}if nc{b.x(c);}b.ccx(a,c,self.pre[i]);if nc{b.x(c);}if na{b.x(a);}
    }
    fn controls(&mut self,b:&mut B,v:usize)->Vec<(QubitId,bool)>{
        let n=self.window.width;let h=self.pre.len();
        if h>0{
            let mut keep=0;
            if let Some(old)=self.cur{
                while keep<h&&((old^v)>>(n-2-keep))==0{keep+=1;}
                for i in(keep..h).rev(){self.cell(b,i,old);}
            }
            for i in keep..h{self.cell(b,i,v);}self.cur=Some(v);
        }
        let mut c=vec![(self.activity,false)];
        let low=if h>0{c.push((self.pre[h-1],false));n-1-h}else{n};
        c.extend((0..low).map(|i|(self.window.address()[i],v>>i&1==0)));c
    }
    pub(crate) fn clear(&mut self,b:&mut B){
        if let Some(old)=self.cur{for i in(0..self.pre.len()).rev(){self.cell(b,i,old);}}
        self.cur=None;
    }
    /// XOR A&[R==value]&extra, with exact returned dirty donors.
    /// The caller excludes every live non-control role from dirty. This
    /// method additionally excludes full metadata, all prefixes and its
    /// actual controls/target. Conditional metadata targets are permitted.
    pub(crate) fn xor(&mut self,b:&mut B,value:usize,target:QubitId,
        extra:&[(QubitId,bool)],dirty:&[QubitId]){
        assert!((self.window.lo..=self.window.hi).contains(&value));
        assert!(target!=self.activity&&!self.window.address().contains(&target)&&!self.pre.contains(&target));
        let mut c=self.controls(b,value-self.window.lo);let mut contradiction=false;
        for &(q,neg)in extra{
            assert!(q!=target);
            if let Some((_,n))=c.iter().find(|p|p.0==q){if *n!=neg{contradiction=true;break;}}
            else{c.push((q,neg));}
        }
        if contradiction{return;}
        let mut used:BTreeSet<_>=self.window.meta.y.iter().chain(&self.window.meta.sum)
            .chain(self.pre).copied().chain([target]).chain(c.iter().map(|p|p.0)).collect();
        let bank:Vec<_>=dirty.iter().copied().filter(|q|used.insert(*q)).collect();
        mc_xor(b,&c,target,&[],&bank);
    }
}
