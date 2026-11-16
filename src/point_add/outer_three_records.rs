//! Explicit S1/S2/S3 records only. No production caller or selector is changed.
//! Three named roles; donors are drawn only from the explicit ring/Q data.
//! P0/P1 external loans, PH epochs, U12, endpoint and fixed-middle are separate.
use super::builder::{B, G};
use super::frogdrop_col::ColPar;
use super::mask::mc_xor;
use super::sum_size::SumSize;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[path = "k6_outer_dispatch.rs"]
mod dispatch;
pub(crate) use dispatch::ColumnPlan;

#[derive(Clone, Copy, Debug)]
pub(crate) struct ThreeRoles { tag: QubitId, cut: QubitId, toggle: QubitId }
impl ThreeRoles {
    pub(crate) fn new(tag: QubitId, cut: QubitId, toggle: QubitId) -> Self {
        assert_ne!(tag,cut); assert_ne!(tag,toggle); assert_ne!(cut,toggle);
        Self { tag, cut, toggle }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProbeGate { Always, TagSet, TagClear }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SwapBoundary {
    /// The schedule proves tag zero only when the previous column has no SW/DL.
    Enter,
    /// Caller must have closed the COMPLETE middle, returning every role zero.
    AfterCompleteMiddle,
}

/// Immutable physical ownership view. No dirty/clean external slice or fourth
/// role can enter this API. All 257 ring and 128 Q lanes are ordinary data.
pub(crate) struct OuterRecords<'a> {
    size: &'a SumSize, roles: ThreeRoles, ring: &'a [QubitId], q: &'a [QubitId],
}
impl<'a> OuterRecords<'a> {
    pub(crate) fn new(size: &'a SumSize, roles: ThreeRoles, ring: &'a [QubitId], q: &'a [QubitId]) -> Self {
        assert_eq!((ring.len(),q.len()),(257,128));
        let mut used=BTreeSet::new();
        assert!(size.y.iter().chain(&size.sum).chain(ring).chain(q).copied()
            .chain([roles.tag,roles.cut,roles.toggle]).all(|x|used.insert(x)));
        Self { size, roles, ring, q }
    }
    fn literals(&self,gate:ProbeGate)->Vec<(QubitId,bool)> {
        match gate { ProbeGate::Always=>vec![], ProbeGate::TagSet=>vec![(self.roles.tag,false)],
            ProbeGate::TagClear=>vec![(self.roles.tag,true)] }
    }
    fn all_data(&self)->Vec<QubitId> { self.ring.iter().chain(self.q).copied().collect() }
    fn check_phase(&self,phase:QubitId) {
        assert!(!self.ring.contains(&phase)&&!self.q.contains(&phase)
            &&!self.size.y.contains(&phase)&&!self.size.sum.contains(&phase));
        assert!(![self.roles.tag,self.roles.cut,self.roles.toggle].contains(&phase));
    }

    /// Exact old priority-probe ordering. On enabled lanes S starts zero;
    /// disabled lanes may have arbitrary S. The public partial window is
    /// unchanged. cut/toggle start and return zero; tag/E/ring/Q are restored.
    /// No known-prefix or known-literal shortcut is used.
    pub(crate) fn sum_probe_record(&self,b:&mut B,bits:(usize,usize),gate:ProbeGate)->Vec<G> {
        assert!(bits.0<=bits.1&&bits.1<=self.ring.len());
        let extra=self.literals(gate); let r=self.roles; let d=self.q;
        rec(b,|b|for l in (bits.0..bits.1).rev() {
            let lo=(224isize-l as isize).clamp(0,128)as usize;
            let hi=(256isize-l as isize).clamp(0,128)as usize;
            if lo>=hi {continue;}
            xor_interval(b,&self.size.y,lo,hi,r.cut,&[r.toggle],d);
            let mut c=eq(&self.size.sum,0);
            c.extend([(self.ring[l],false),(r.cut,false)]);c.extend_from_slice(&extra);
            mc_xor(b,&c,r.toggle,&[],d);
            let v=rec(b,|b|super::frogdrop::add_const_dirty_exact(b,&self.size.y[..5],l&31,d));
            b.play(&v,false);
            for i in 0..5 {b.ccx(r.toggle,self.size.y[i],self.size.sum[i]);}
            for i in 0..5 {b.cx(self.size.y[i],self.size.sum[i]);}
            mc_xor(b,&c,r.toggle,&[],d);
            for i in 0..5 {b.cx(self.size.y[i],self.size.sum[i]);}
            b.play(&v,true);
            xor_interval(b,&self.size.y,lo,hi,r.cut,&[r.toggle],d);
        })
    }
    /// Preserve the parent's public aligned/old selection exactly. In the
    /// aligned branch its stronger whole-window care contract still applies.
    fn complete_probe(&self,b:&mut B,bits:(usize,usize),gate:ProbeGate)->Vec<G> {
        assert!(bits.0<=bits.1&&bits.1<=257);
        let extra=self.literals(gate);
        if super::aligned_sum_probe::preferred(bits,!extra.is_empty()) {
            super::aligned_sum_probe::record(b,self.size,self.ring,extra.first().copied(),self.q)
        } else {self.sum_probe_record(b,bits,gate)}
    }
    pub(crate) fn stage1_record(&self,b:&mut B,plan:&ColumnPlan)->Vec<G> {
        let probe=self.complete_probe(b,plan.stage1_bits(),ProbeGate::TagClear);
        rec(b,|b|{
            b.play(&probe,false);
            for i in 0..5 {b.ccx(self.roles.tag,self.size.y[i],self.size.sum[i]);}
        })
    }
    /// Fresh output probe inverse; outgoing C is never confused with input C.
    pub(crate) fn output_erase_record(&self,b:&mut B,plan:&ColumnPlan)->Vec<G> {
        let probe=self.complete_probe(b,plan.output_bits(),ProbeGate::Always);
        rec(b,|b|b.play(&probe,true))
    }
    /// S2: positive Q (<=128 bits), enabled E starts zero. Disabled metadata
    /// is arbitrary. cut is the only clean MCX temporary and is returned.
    fn offset_probe(&self,b:&mut B)->Vec<G> {
        let r=self.roles; let d=self.ring;
        rec(b,|b|for l in (0..self.q.len()).rev() {
            let mut c=eq(&self.size.y,0);c.extend([(self.q[l],false),(r.tag,false)]);
            mc_xor(b,&c,r.toggle,&[r.cut],d);
            for i in 0..7 {if l>>i&1!=0 {b.cx(r.toggle,self.size.y[i]);}}
            let mut c=eq(&self.size.y,l);c.extend([(self.q[l],false),(r.tag,false)]);
            mc_xor(b,&c,r.toggle,&[r.cut],d);
        })
    }
    /// C=1 entry E=M-1 in97..127, S=E mod32 and positive Q. C=0 is an
    /// identity for arbitrary metadata/Q. C stays held for the later erasure.
    pub(crate) fn tagged_refill_record(&self,b:&mut B)->Vec<G> {
        let probe=self.offset_probe(b); let r=self.roles;
        rec(b,|b|{
            for i in 0..5 {b.ccx(r.tag,self.size.sum[i],self.size.y[i]);}
            b.cx(r.tag,self.size.y[5]);b.cx(r.tag,self.size.y[6]);
            b.play(&probe,false);
            super::arith::ttk_add(b,&self.size.y[..5],&self.size.sum,Some(r.tag),None);
        })
    }
    /// The existing C/W/D conjugation surrounds the two COMPLETE S1 tapes.
    /// Source care: old lower128 is the previous value, upper cells may have
    /// changed, and PH is metadata outside a payload epoch. No S4 is hidden.
    pub(crate) fn delayed_reprobe_record(&self,b:&mut B,plan:&ColumnPlan,phase:QubitId)->Vec<G> {
        let (bitlo,xw)=plan.reprobe().expect("DL column required");self.check_phase(phase);
        let old=self.sum_probe_record(b,(bitlo,128),ProbeGate::TagSet);
        let new=self.sum_probe_record(b,(bitlo,xw),ProbeGate::TagSet);
        rec(b,|b|{
            super::direct_size_predicates::xor_switch(b,self.size,phase,self.roles.tag,self.q);
            b.play(&old,true);b.play(&new,false);
            super::direct_size_predicates::xor_switch(b,self.size,phase,self.roles.tag,self.q);
        })
    }
    /// S3 exact Z-1 byte. On enter with incoming C possible, tag remains an
    /// immutable negative control and both high decoder literals stay inline.
    /// Otherwise tag is the zero decoder host and is never a simultaneous
    /// control or independent donor. Clear it before closing the byte epoch.
    pub(crate) fn cut_swap_record(&self,b:&mut B,plan:&ColumnPlan,boundary:SwapBoundary)->Vec<G> {
        let host=boundary==SwapBoundary::AfterCompleteMiddle||!plan.incoming_c();
        let extra=if boundary==SwapBoundary::Enter&&!host {self.literals(ProbeGate::TagClear)}else{vec![]};
        self.swap_impl(b,host,&extra)
    }
    fn swap_impl(&self,b:&mut B,host:bool,extra:&[(QubitId,bool)])->Vec<G> {
        let r=self.roles;let d=self.all_data();
        assert!(!host||extra.is_empty(),"host cannot remain a live tag control");
        let address=super::direct_frame::z_byte_record(b,self.size,r.toggle,&d);
        rec(b,|b|{
            b.play(&address,false);
            let mut dec=Decoder {word:&self.size.y,host:if host{Some(r.tag)}else{None},old:None};
            mc_xor(b,extra,r.cut,&[],&d);
            for lane in (129..257).rev() {
                if lane<256 {
                    let mut c=dec.controls(b,lane&127);
                    c.push((r.toggle,false));c.extend_from_slice(extra);
                    mc_xor(b,&c,r.cut,&[],&d);
                }
                b.cswap(r.cut,self.ring[lane],self.q[256-lane]);
            }
            mc_xor(b,extra,r.cut,&[],&d);
            let mut high=extra.to_vec();high.push((r.toggle,false));
            mc_xor(b,&high,r.cut,&[],&d);
            let mut last=dec.controls(b,0);last.extend(high);
            mc_xor(b,&last,r.cut,&[],&d);
            dec.clear(b);b.play(&address,true);
        })
    }
    #[cfg(test)]
    pub(crate) fn mutant_swap_record(&self,b:&mut B,fault:SwapFault)->Vec<G> {
        match fault {
            SwapFault::WrongLiveHost=>self.swap_impl(b,true,&[]),
            SwapFault::OmittedTagControl=>self.swap_impl(b,false,&[]),
            SwapFault::UncleanReturn=>{
                let tape=self.swap_impl(b,false,&self.literals(ProbeGate::TagClear));
                rec(b,|b|{b.play(&tape,false);b.x(self.roles.toggle);})
            }
        }
    }
}
#[cfg(test)]
#[derive(Clone,Copy,Debug)]
pub(crate) enum SwapFault { WrongLiveHost, OmittedTagControl, UncleanReturn }

fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn eq(word:&[QubitId],value:usize)->Vec<(QubitId,bool)>{
    word.iter().enumerate().map(|(i,&q)|(q,value>>i&1==0)).collect()
}
fn xor_interval(b:&mut B,word:&[QubitId],mut lo:usize,hi:usize,target:QubitId,clean:&[QubitId],dirty:&[QubitId]){
    assert!(lo<=hi&&hi<=1usize<<word.len());
    while lo<hi {
        let mut free=if lo==0{word.len()}else{lo.trailing_zeros()as usize};free=free.min(word.len());
        while lo+(1usize<<free)>hi {free-=1;}
        let term:Vec<_>=(free..word.len()).map(|i|(word[i],lo>>i&1==0)).collect();
        mc_xor(b,&term,target,clean,dirty);lo+=1usize<<free;
    }
}
struct Decoder<'a>{word:&'a[QubitId],host:Option<QubitId>,old:Option<usize>}
impl Decoder<'_>{
    fn cell(&self,b:&mut B,value:usize){
        let host=self.host.expect("hosted decoder cell");
        if value&64==0{b.x(self.word[6]);}if value&32==0{b.x(self.word[5]);}
        b.ccx(self.word[6],self.word[5],host);
        if value&32==0{b.x(self.word[5]);}if value&64==0{b.x(self.word[6]);}
    }
    fn controls(&mut self,b:&mut B,value:usize)->Vec<(QubitId,bool)>{
        if let Some(host)=self.host {
            if self.old.map(|v|v>>5)!=Some(value>>5){self.clear(b);self.cell(b,value);self.old=Some(value);}
            std::iter::once((host,false)).chain((0..5).map(|i|(self.word[i],value>>i&1==0))).collect()
        }else{eq(self.word,value)}
    }
    fn clear(&mut self,b:&mut B){if let Some(v)=self.old{self.cell(b,v);}self.old=None;}
}

/// A schedule binding is checked before selecting a source-proven boundary.
pub(crate) fn bind_column(cp:&ColPar)->ColumnPlan { ColumnPlan::bind(cp) }
