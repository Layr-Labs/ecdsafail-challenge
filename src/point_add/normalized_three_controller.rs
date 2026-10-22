//! Three-owner normalized controller, retaining complete parent epochs.
//!
//! Intended sibling modules: normalized_three_frame and
//! normalized_three_arithmetic. Cross/Kernels retain the existing public
//! port ABI. This controller owns software frame state only, no qubits.
//! V sees RAW Q and the common normalized ring. Activity/payload
//! callbacks run with BOTH coordinate frames closed.
//! Final HR ticks use normalized Q/P and a fixed full161-k target, with
//! a proved zero carry across the true W/d boundary. PH remains payload.

use super::builder::{B,G};
use super::cross_three::{Cross,Gate,Kernels,VTop};
use super::normalized_three_arithmetic::D;
use super::normalized_three_frame as frame;
use super::normalized_three_payload::{self,PayloadPorts};
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn range(word:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>>{
    assert!(lo<=hi&&hi<=1usize<<word.len());let mut out=vec![];
    while lo<hi{let mut free=if lo==0{word.len()}else{lo.trailing_zeros()as usize};
        free=free.min(word.len());while lo+(1usize<<free)>hi{free-=1;}
        out.push((free..word.len()).map(|i|(word[i],lo>>i&1==0)).collect());lo+=1usize<<free;
    }out
}
/// `has_payload` is the public T1/T4 software path, not a quantum branch.
/// Caller must bind it to Column.compact.is_some(). The same three scalar
/// ports and optional two no-P terminal loans are used throughout.
pub(crate) trait NativeRingV {
    /// Ring is in common C, but Q129 has returned to its exact raw layout.
    fn native_ring_v(&mut self,b:&mut B,c:&Cross<'_>,ht:bool,inverse:bool);
}

pub(crate) struct Controller<'a,'q>{
    c:&'a Cross<'q>,has_payload:bool,
    q_coordinate:Option<Vec<G>>,ring_coordinate:Option<Vec<G>>,
    open:bool,ring_open:bool,
}
impl<'a,'q> Controller<'a,'q>{
    pub(crate) fn new(c:&'a Cross<'q>,has_payload:bool)->Self{
        assert_eq!((c.q.len(),c.ring.len(),c.qb),(128,257,30));
        assert!(1<=c.y_bounds.0&&c.y_bounds.0<=c.y_bounds.1&&c.y_bounds.1<=128);
        assert!(c.clean_external.is_empty()||(!has_payload&&c.clean_external.len()==2));
        let r=c.roles;let mut seen=BTreeSet::new();
        assert!(c.q.iter().chain(c.ring).chain(&c.size.y).chain(&c.size.sum).copied()
            .chain([c.phase,r.activity,r.flight,r.work])
            .chain(c.clean_external.iter().copied()).all(|q|seen.insert(q)));
        Self{c,has_payload,q_coordinate:None,ring_coordinate:None,open:false,ring_open:false}
    }
    fn bank(&self,extra:&[QubitId])->Vec<QubitId>{
        let c=self.c;let r=c.roles;
        let mut seen:BTreeSet<_>=c.size.y.iter().chain(&c.size.sum).copied()
            .chain([c.phase,r.activity,r.flight,r.work])
            .chain(c.clean_external.iter().copied()).chain(extra.iter().copied()).collect();
        c.dirty.iter().chain(c.ring).chain(c.q).copied().filter(|q|seen.insert(*q)).collect()
    }
    fn enter_ring(&mut self,b:&mut B){
        assert!(!self.open&&!self.ring_open);
        if self.ring_coordinate.is_none(){self.ring_coordinate=Some(frame::ring_record(b,self.c));}
        b.play(self.ring_coordinate.as_ref().unwrap(),false);self.ring_open=true;
    }
    fn leave_ring(&mut self,b:&mut B){
        assert!(!self.open&&self.ring_open);
        b.play(self.ring_coordinate.as_ref().unwrap(),true);self.ring_open=false;
    }
    fn enter_q(&mut self,b:&mut B){
        assert!(!self.open&&self.ring_open);
        if self.q_coordinate.is_none(){self.q_coordinate=Some(frame::q_record(b,self.c));}
        b.play(self.q_coordinate.as_ref().unwrap(),false);self.open=true;
    }
    fn leave_q(&mut self,b:&mut B){
        assert!(self.open&&self.ring_open);
        b.play(self.q_coordinate.as_ref().unwrap(),true);self.open=false;
    }
    fn enter(&mut self,b:&mut B){self.enter_ring(b);self.enter_q(b);}
    fn leave(&mut self,b:&mut B){self.leave_q(b);self.leave_ring(b);}
    fn raw_v(&mut self,b:&mut B,k:&mut(impl Kernels+NativeRingV),ht:bool,park:Option<usize>,inverse:bool,reopen:bool){
        assert!(park.is_none()||park==Some(0)||park==Some(2));
        self.leave_q(b);k.native_ring_v(b,self.c,ht,inverse);
        if reopen{self.enter_q(b);}else{self.leave_ring(b);}
    }
    fn arithmetic(&self,ht:bool)->D{assert!(self.open);D{ht,payload_open:false}}

    /// Only at the six complete epochs documented at the call sites below.
    /// Every Q park is zero on original A, so normalized x128=Q[Y]=0
    /// is a valid returned carry and the whole Q128 source has zero padding.
    /// `payload_open` is the existing arithmetic ABI for this unparked
    /// source, not a request to open a payload or modify PH/software state.
    /// Keep the cheaper 114-cell kernel where its complete prefix is already
    /// public-impossible; otherwise replace 534T prefix by 42T ordinary cells.
    fn arithmetic_empty_q(&self,ht:bool,gate:Gate)->D{
        assert!(self.open);
        let hi=match gate{
            Gate::Top(j)=>self.c.y_bounds.1.min(128-j),
            Gate::Bottom(_)=>self.c.y_bounds.1,
            Gate::Natural(_)=>unreachable!("empty-Q selector is scoped to Top/Bottom"),
        };
        D{ht,payload_open:hi>=115}
    }

    /// Complete selected write with no retained predicate. Metadata is
    /// restored before returning, and no query is performed per ripple cell.
    fn xor_gate(&self,b:&mut B,gate:Gate,extra:&[(QubitId,bool)],out:QubitId){
        assert!(self.open);let c=self.c;let r=c.roles;
        let gate=match gate{
            Gate::Top(j) if c.y_bounds.1<=128-j=>Gate::Natural(j),
            Gate::Bottom(k) if c.y_bounds.1<=114=>Gate::Natural(k+15),g=>g};
        let mut held:Vec<_>=extra.iter().map(|p|p.0).collect();held.extend([out,c.q[127]]);
        let d=self.bank(&held);
        let xor=|b:&mut B,terms:&[Vec<(QubitId,bool)>],controls:&[(QubitId,bool)],target:QubitId|{
            for term in terms{if let Some(t)=super::three_control::merged(term,controls){
                super::mask::mc_xor(b,&t,target,c.clean_external,&d);
            }}
        };
        if let Gate::Bottom(k)=gate{
            super::normalized_three_bottom::xor_gate(b,c,k,extra,out,&d);
        }else if let Gate::Top(j)=gate{
            // Preserve the parent's leading-cell capacity query. On A,
            // X(Q127) starts zero; off A every central write is disabled.
            // Both source and metadata return before the selected action.
            let head=c.q[127];let fail=range(&c.size.y,128-j,128);
            let prep=rec(b,|b|{b.x(head);xor(b,&fail,&[],head);});
            let positive=range(&c.size.sum,0,32-j);let negative=range(&c.size.sum,32-j,32);
            let price=|n:usize|match n{0|1=>0,2=>1,_=>4*(n-2)};
            let n=extra.len()+2;
            let pp:usize=positive.iter().map(|t|price(t.len()+n)).sum();
            let np:usize=price(n)+negative.iter().map(|t|price(t.len()+n)).sum::<usize>();
            let mut controls=vec![(r.activity,false),(head,true)];controls.extend_from_slice(extra);
            b.play(&prep,false);
            if np<pp{xor(b,&[vec![]],&controls,out);xor(b,&negative,&controls,out);}
            else{xor(b,&positive,&controls,out);}
            b.play(&prep,true);
        }else{
            let mut controls=vec![(r.activity,false)];controls.extend_from_slice(extra);
            xor(b,&c.gate_terms(gate),&controls,out);
        }
    }
    fn swap_gate(&self,b:&mut B,gate:Gate,left:QubitId,right:QubitId){
        assert_ne!(left,right);b.cx(left,right);
        self.xor_gate(b,gate,&[(right,false)],left);b.cx(left,right);
    }
    fn inplace(&self,b:&mut B,t:&[QubitId],gate:Gate){
        assert_eq!(t.len(),129);self.swap_gate(b,gate,t[128],self.c.roles.flight);
    }
    fn park(&self,b:&mut B,j:usize,erase:bool){
        assert!(self.open&&j<15);let c=self.c;let r=c.roles;
        if c.y_bounds.0>128-j{return;}
        let slot=frame::park(c,j);
        if erase{b.cx(r.flight,slot);}
        else if c.y_bounds.1<=128-j{b.cswap(r.activity,slot,r.flight);}
        else{
            let d=self.bank(&[slot]);
            super::three_control::swap_terms(b,&range(&c.size.y,0,128-j),
                &[(r.activity,false)],slot,r.flight,&d);
        }
    }
    fn store(&self,b:&mut B,t:&[QubitId],gate:Gate,top:VTop,inverse:bool){
        assert_eq!(t.len(),129);let c=self.c;let r=c.roles;let root=t[128];
        let flip=|b:&mut B|match top{
            VTop::Zero=>self.xor_gate(b,gate,&[],root),
            VTop::Frame(j)=>if j!=0{self.xor_gate(b,gate,&[],root)}else{
                // Frame0 has the same exact S<2 top selector as parent.
                for term in range(&c.size.sum,0,32-c.qb){self.xor_gate(b,gate,&term,root);}
            },
        };
        if inverse{self.swap_gate(b,gate,root,r.flight);flip(b);}
        else{flip(b);self.swap_gate(b,gate,root,r.flight);}
    }
    fn search_top(&self,b:&mut B,k:&mut impl Kernels,ht:bool,extract:bool){
        assert!(self.open);let f=k.top_frame(b,self.c);b.play(&f,false);
        // HR first search: Q is the unchanged positive source. Extraction
        // begins only AFTER this entire V-bit/store sweep; stores touch ring.
        for j in 0..15{let t=frame::top_target(self.c,j);
            let mut d=self.arithmetic_empty_q(ht,Gate::Top(j));
            d.vbit_store(b,self.c,&t,Gate::Top(j),VTop::Frame(j));}
        if extract{for j in 0..15{let t=frame::top_target(self.c,j);
            self.store(b,&t,Gate::Top(j),VTop::Frame(j),true);self.park(b,j,false);}}
        b.play(&f,true);
    }
    fn search_bottom(&self,b:&mut B,ht:bool,extract:bool){
        assert!(self.open);
        // HR search follows complete Top-park erasure. The only HT caller
        // captures the inverse AFTER every Bottom park has been fetched.
        // This sweep stores solely in ring, so Q stays unparked throughout.
        for j in(0..15).rev(){let t=frame::natural_target(self.c,j);
            let mut d=self.arithmetic_empty_q(ht,Gate::Bottom(j));
            // The only non-extract caller is the HT captured inverse.
            // Its store0 inverse cancels the adjacent forward store0.
            if extract||j!=0{d.vbit_store(b,self.c,&t,Gate::Bottom(j),VTop::Zero);}
            else{d.vbit(b,self.c,&t,Gate::Bottom(j),VTop::Zero);}}
        if extract{for j in(0..15).rev(){let t=frame::natural_target(self.c,j);
            self.store(b,&t,Gate::Bottom(j),VTop::Zero,true);self.park(b,j,false);}}
    }
    /// Starts raw; one ring epoch spans all four V plays. Q is raw at
    /// every V and normalized only for the intervening arithmetic epochs.
    pub(crate) fn hr_begin(&mut self,b:&mut B,k:&mut(impl Kernels+NativeRingV),whole_only:bool){
        assert!(whole_only&&!self.open);k.z_flip(b,self.c);k.toggle_activity(b,self.c,false);
        self.enter_ring(b);k.native_ring_v(b,self.c,false,false);
        self.enter_q(b);self.search_top(b,k,false,true);
        self.raw_v(b,k,false,Some(0),true,true);
        let f=k.top_frame(b,self.c);b.play(&f,false);let mut d=self.arithmetic(false);
        for j in 0..15{let t=frame::top_target(self.c,j);
            if j!=14{d.divide_erase_inplace(b,self.c,&t,Gate::Top(j),frame::park(self.c,j));}
            else{d.divide(b,self.c,&t,Gate::Top(j),false);self.park(b,j,true);}}
        // All15 Top parks were erased by the complete ascending sweep.
        // The descending inverse changes only ring/flight and restores Q.
        // Two adjacent complete inplace14 tapes are exact inverses.
        for j in(0..15).rev(){let t=frame::top_target(self.c,j);
            let mut d=self.arithmetic_empty_q(false,Gate::Top(j));
            if j!=14{d.divide_inplace(b,self.c,&t,Gate::Top(j),true);}
            else{d.divide(b,self.c,&t,Gate::Top(j),true);}}
        b.play(&f,true);self.raw_v(b,k,false,None,false,true);self.search_bottom(b,false,true);
        self.raw_v(b,k,false,Some(2),true,true);
    }
    /// Completes HR and returns RAW coordinates and all helper roles. The
    /// P loop keeps Q/ring/P normalized across all30 ticks and inverse divides.
    pub(crate) fn hr_finish(&mut self,b:&mut B,k:&mut (impl Kernels+PayloadPorts)){
        assert!(self.open);let f=k.top_frame(b,self.c);b.play(&f,false);let mut d=self.arithmetic(false);
        for j in 0..15{let t=frame::top_target(self.c,j);d.divide_inplace(b,self.c,&t,Gate::Top(j),false);}b.play(&f,true);
        for j in(0..15).rev(){let t=frame::natural_target(self.c,j);
            d.divide_erase_inplace(b,self.c,&t,Gate::Bottom(j),frame::park(self.c,j));}
        // Both park families, including q0/x128, have now returned.
        if self.has_payload{
            self.leave(b);k.hr_payload_open(b,self.c);
            // Both Q park families and the raw digit returned x128.
            // PH now belongs to raw P259. The temporary coordinate is
            // distinct from the earlier parked Q129 coordinate.
            let raw=k.hr_payload_word().to_vec();
            let coordinate=normalized_three_payload::frame_record(b,self.c,&raw);
            b.play(&coordinate,false);self.open=true;self.ring_open=true;
            // This final P coordinate is owned by its own captured record;
            // no partial-Q/ring helper is called until that record closes.
            let mut d=D{ht:false,payload_open:true};
            for bit in 0..30{let t=frame::natural_target(self.c,bit);
                self.inplace(b,&t,Gate::Natural(bit));
                normalized_three_payload::tick(b,self.c,&raw,bit);
                d.divide(b,self.c,&t,Gate::Natural(bit),true);}
            b.play(&coordinate,true);self.open=false;self.ring_open=false;
            k.hr_payload_close(b,self.c);
        }else{
            // Both Q park families are now empty. The existing native
            // unparked ABI uses normalized x128=old Q[Y]=0 on A as carry,
            // and reads all128 source cells with a genuine zero prefix.
            // No payload callback or PH payload lifetime is introduced.
            // CrossKernels.payload_open stays false throughout this path.
            let mut d=D{ht:false,payload_open:true};
            for bit in 0..30{let t=frame::natural_target(self.c,bit);
                d.divide_inplace(b,self.c,&t,Gate::Natural(bit),true);}
            self.leave(b);
        }
        k.z_flip(b,self.c);k.toggle_activity(b,self.c,false);
    }
    /// Starts/ends raw. One ring epoch spans all four identical V tapes;
    /// each V still sees exactly raw Q and the inherited catalyst value.
    pub(crate) fn ht_finish(&mut self,b:&mut B,k:&mut(impl Kernels+NativeRingV),whole_only:bool){
        assert!(whole_only&&!self.open);k.toggle_activity(b,self.c,true);self.enter(b);
        let mut d=self.arithmetic(true);
        for j in 0..15{let t=frame::natural_target(self.c,j);self.inplace(b,&t,Gate::Bottom(j));self.park(b,j,false);}
        let f=k.top_frame(b,self.c);b.play(&f,false);
        for j in(0..15).rev(){let t=frame::top_target(self.c,j);d.divide_inplace(b,self.c,&t,Gate::Top(j),true);}
        b.play(&f,true);self.raw_v(b,k,true,Some(2),false,true);
        for j in(0..15).rev(){let t=frame::natural_target(self.c,j);self.park(b,j,false);
            d.add(b,self.c,&t,Gate::Bottom(j));
            if j!=0{self.store(b,&t,Gate::Bottom(j),VTop::Zero,false);}}
        let undo=rec(b,|b|self.search_bottom(b,true,false));b.play(&undo,true);
        self.raw_v(b,k,true,None,true,true);
        let f=k.top_frame(b,self.c);b.play(&f,false);
        // Bottom parks were all fetched before the preceding inverse search.
        // Top extraction is a separate subsequent sweep; this divide/inplace
        // epoch therefore reads a complete unparked Q throughout.
        for j in 0..15{let t=frame::top_target(self.c,j);
            let mut d=self.arithmetic_empty_q(true,Gate::Top(j));
            d.divide_inplace(b,self.c,&t,Gate::Top(j),false);}
        for j in 0..15{let t=frame::top_target(self.c,j);self.inplace(b,&t,Gate::Top(j));self.park(b,j,false);}
        b.play(&f,true);self.raw_v(b,k,true,Some(0),false,true);
        let f=k.top_frame(b,self.c);b.play(&f,false);
        for j in 0..15{let t=frame::top_target(self.c,j);self.park(b,j,false);
            d.add(b,self.c,&t,Gate::Top(j));
            if j!=14{self.store(b,&t,Gate::Top(j),VTop::Frame(j),false);}}
        // F^-1 F cancels at this boundary. Inside that common frame,
        // store14 and its captured inverse cancel as complete records.
        let undo=rec(b,|b|{
            // Captured inverse starts after all15 Top fetches, including
            // q0/x128. The omitted store14 leaves flight live, not a Q park.
            // In either direction the complete V-bit/store sweep restores Q.
            for j in 0..15{let t=frame::top_target(self.c,j);
                let mut d=self.arithmetic_empty_q(true,Gate::Top(j));
                if j!=14{d.vbit_store(b,self.c,&t,Gate::Top(j),VTop::Frame(j));}
                else{d.vbit(b,self.c,&t,Gate::Top(j),VTop::Frame(j));}}
        });
        b.play(&undo,true);b.play(&f,true);
        self.raw_v(b,k,true,None,true,false);k.toggle_activity(b,self.c,true);k.z_flip(b,self.c);
    }
    pub(crate) fn is_raw(&self)->bool{!self.open&&!self.ring_open}
}

// HT S5 is deliberately not rewritten in this controller: it is a
// separately priced adapter around digit/zflip and before qg/transitions.
// Likewise there is no claim that fixed-middle/outer/whole cost fits.
