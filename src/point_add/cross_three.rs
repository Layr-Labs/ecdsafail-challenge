//! Exact full-width crossing controller with three physical scalar owners.
//! Activity and quotient flight are retained; the third owner is Q128.
//! All metadata masks are substituted as literal controls, never allocated.
use super::builder::{B,G};
use super::three_control::{range,rec,swap_terms,xor_terms};
use super::sum_size::SumSize;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[derive(Clone,Copy)]
pub(crate) struct Roles { pub activity:QubitId, pub flight:QubitId,
    pub work:QubitId }
#[derive(Clone,Copy)]
pub(crate) enum Gate { Top(usize), Bottom(usize), Natural(usize) }
#[derive(Clone,Copy)]
pub(crate) enum VTop { Zero, Frame(usize) }

/// Complete middle adapters. Arithmetic uses A/e plus PH as conditional
/// carry while PH is phase, or returned work after every Q park is erased.
/// work otherwise retains the physical Q128 quotient passenger. Metadata
/// predicates are evaluated in literal controls and leave no stored mask.
/// V and frame records preserve A, work, E/S and phase, and return e.
pub(crate) trait Kernels {
    fn top_frame(&mut self,b:&mut B,c:&Cross<'_>)->Vec<G>;
    fn natural_frame(&mut self,b:&mut B,c:&Cross<'_>)->Vec<G>;
    fn v(&mut self,b:&mut B,c:&Cross<'_>,ht:bool,park:Option<usize>,inverse:bool);
    fn toggle_activity(&mut self,b:&mut B,c:&Cross<'_>,ht:bool);
    fn divide(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate,inverse:bool);
    fn add(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate);
    fn vbit(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate,top:VTop);
    /// Payload may use all three scalar owners after every Q park is gone.
    /// Open may materialize P258 in PH. Tick must preserve e until the
    /// subsequent inverse divide consumes it; close restores phase PH.
    fn hr_payload_open(&mut self,b:&mut B,c:&Cross<'_>);
    fn hr_payload_tick(&mut self,b:&mut B,c:&Cross<'_>,bit:usize);
    fn hr_payload_close(&mut self,b:&mut B,c:&Cross<'_>);
    fn z_flip(&mut self,b:&mut B,c:&Cross<'_>);
}

pub(crate) struct Cross<'a> {
    pub size:&'a SumSize, pub ring:&'a [QubitId], pub q:&'a [QubitId],
    pub phase:QubitId, pub roles:Roles, pub dirty:&'a [QubitId],
    pub y_bounds:(usize,usize), pub qb:usize,
    /// Explicit globally-zero terminal P0/P1 loans only on whole T2/T3.
    pub clean_external:&'a [QubitId],
}

impl Cross<'_> {
    fn check(&self) {
        assert_eq!((self.ring.len(),self.q.len()),(257,128));
        assert_eq!(self.qb,30,"preserve the qualified two-band width");
        assert!(1<=self.y_bounds.0&&self.y_bounds.0<=self.y_bounds.1&&self.y_bounds.1<=128);
        let r=self.roles;let mut seen=BTreeSet::new();
        assert!(self.ring.iter().chain(self.q).chain(&self.size.y).chain(&self.size.sum)
            .copied().chain([self.phase,r.activity,r.flight,r.work])
            .all(|q|seen.insert(q)));
        assert!(self.clean_external.len()==0||self.clean_external.len()==2);
        assert!(self.clean_external.iter().all(|q|seen.insert(*q)));
    }
    pub(crate) fn bank(&self,extra:&[QubitId])->Vec<QubitId> {
        let r=self.roles;
        let excluded:BTreeSet<_>=self.size.y.iter().chain(&self.size.sum).copied()
            .chain([self.phase,r.activity,r.flight,r.work])
            .chain(extra.iter().copied()).collect();let mut seen=BTreeSet::new();
        self.dirty.iter().chain(self.ring).chain(self.q).copied()
            .filter(|q|!excluded.contains(q)&&seen.insert(*q)).collect()
    }
    fn product(&self,ylo:usize,yhi:usize,shi:usize)->Vec<Vec<(QubitId,bool)>> {
        if ylo>=yhi||shi==0{return vec![];}
        let mut out=vec![];
        for y in range(&self.size.y,ylo,yhi) {
            for s in range(&self.size.sum,0,shi.min(32)) {
                let mut t=y.clone();t.extend(s);out.push(t);
            }
        }out
    }
    /// Exact two-band predicates without mutating S or storing vprime.
    /// QTOP=QB-1. Top j: j<=gap and j<T(Y). Bottom k: k<=gap-T(Y).
    /// T(Y)=min(15,129-Y). These disjoint covers include all 128 Y values.
    pub(crate) fn gate_terms(&self,gate:Gate)->Vec<Vec<(QubitId,bool)>> {
        match gate {
            Gate::Natural(k)=>{assert!(k<self.qb);range(&self.size.sum,0,32-k)},
            Gate::Top(j)=>{assert!(j<15);self.product(0,128-j,32-j)},
            Gate::Bottom(k)=>{
                assert!(k<15);let mut out=self.product(0,114,17-k);
                for y in 115..=128 {
                    // S<32-k-(129-Y), E=Y-1. Public nonpositive limits
                    // are empty; no data-dependent precision is removed.
                    let bound=32isize-k as isize-(129-y)as isize;
                    if bound>0 {out.extend(self.product(y-1,y,bound as usize));}
                }out
            }
        }
    }
    fn natural_target(&self,k:usize)->Vec<QubitId> {
        let span=(self.y_bounds.1+1).min(257-k);
        (0..span).map(|i|self.ring[256-k-i]).collect()
    }
    fn frame_target(&self,j:usize)->Vec<QubitId> {
        let top=self.qb-1;let k=top-j;
        let span=(self.y_bounds.1+1).min(257-k);
        (0..span).map(|i|self.ring[(256-k-i+top)%257]).collect()
    }
    /// Gather is only a permutation of data; its complete reverse returns
    /// every port. The middle controlled action is disabled off activity.
    fn gathered(&self,b:&mut B,leaves:&[(usize,QubitId)],body:impl FnOnce(&mut B,QubitId)) {
        if leaves.is_empty(){return;}
        let mut swaps=vec![];
        let root=super::midg::swap_tree(&self.size.y,leaves,7,&mut swaps);
        for &(c,x,y) in &swaps {b.cswap(c,x,y);}
        body(b,root);
        for &(c,x,y) in swaps.iter().rev(){b.cswap(c,x,y);}
    }
    pub(crate) fn inplace(&self,b:&mut B,target:&[QubitId],gate:Gate) {
        let leaves:Vec<_>=(self.y_bounds.0..=self.y_bounds.1)
            .filter_map(|y|target.get(y).copied().map(|q|(y-1,q))).collect();
        self.gathered(b,&leaves,|b,root| {
            let d=self.bank(&[root]);swap_terms(b,&self.gate_terms(gate),
                &[(self.roles.activity,false)],root,self.roles.flight,&d);
        });
    }
    fn park(&self,b:&mut B,bit:usize,_gate:Gate,erase:bool) {
        let leaves:Vec<_>=(self.y_bounds.0..=self.y_bounds.1).filter_map(|y| {
            let pos=y+bit;let q=if pos<128{self.q[pos]}else if pos==128{
                self.roles.work}else{return None;};Some((y-1,q))
        }).collect();
        self.gathered(b,&leaves,|b,root| {
            if erase{b.cx(self.roles.flight,root);}else{
                let terms=range(&self.size.y,0,128-bit);let d=self.bank(&[root]);
                swap_terms(b,&terms,&[(self.roles.activity,false)],root,self.roles.flight,&d);
            }
        });
    }
    fn store(&self,b:&mut B,target:&[QubitId],gate:Gate,top:VTop,inverse:bool) {
        let leaves:Vec<_>=(self.y_bounds.0..=self.y_bounds.1)
            .filter_map(|y|target.get(y).copied().map(|q|(y-1,q))).collect();
        self.gathered(b,&leaves,|b,root| {
            let r=self.roles;let d=self.bank(&[root]);let terms=self.gate_terms(gate);
            let flip=|b:&mut B|{
                if matches!(top,VTop::Frame(0)){
                    for s in range(&self.size.sum,0,32-self.qb){let mut e=s;e.push((r.activity,false));
                        xor_terms(b,&terms,&e,root,&d);}
                }else{xor_terms(b,&terms,&[(r.activity,false)],root,&d);}
            };
            let sw=|b:&mut B|swap_terms(b,&terms,&[(r.activity,false)],root,r.flight,&d);
            if inverse{sw(b);flip(b);}else{flip(b);sw(b);}
        });
    }
    fn search_top(&self,b:&mut B,k:&mut impl Kernels,extract:bool) {
        let frame=k.top_frame(b,self);b.play(&frame,false);
        for j in 0..15 {
            let t=self.frame_target(j);k.vbit(b,self,&t,Gate::Top(j),VTop::Frame(j));
            self.store(b,&t,Gate::Top(j),VTop::Frame(j),false);
        }
        if extract {for j in 0..15 {
            let t=self.frame_target(j);self.store(b,&t,Gate::Top(j),VTop::Frame(j),true);
            self.park(b,j,Gate::Top(j),false);
        }}
        b.play(&frame,true);
    }
    fn search_bottom(&self,b:&mut B,k:&mut impl Kernels,extract:bool) {
        let frame=k.natural_frame(b,self);b.play(&frame,false);
        for i in (0..15).rev() {
            let t=self.natural_target(i);k.vbit(b,self,&t,Gate::Bottom(i),VTop::Zero);
            self.store(b,&t,Gate::Bottom(i),VTop::Zero,false);
        }
        if extract {for i in (0..15).rev() {
            let t=self.natural_target(i);self.store(b,&t,Gate::Bottom(i),VTop::Zero,true);
            self.park(b,i,Gate::Bottom(i),false);
        }}
        b.play(&frame,true);
    }
    /// Whole-only HR prefix. A stays retained until hr_finish. The callback
    /// boundary is a scheduling event, not a claim of original scratch state.
    pub(crate) fn hr_begin(&self,b:&mut B,k:&mut impl Kernels,whole_only:bool) {
        self.check();assert!(whole_only,"partial upto ABI is not implemented");
        k.z_flip(b,self);k.toggle_activity(b,self,false);
        k.v(b,self,false,None,false);self.search_top(b,k,true);
        k.v(b,self,false,Some(0),true);
        let frame=k.top_frame(b,self);b.play(&frame,false);
        for j in 0..15 {
            let t=self.frame_target(j);k.divide(b,self,&t,Gate::Top(j),false);
            self.park(b,j,Gate::Top(j),true);self.inplace(b,&t,Gate::Top(j));
        }
        for j in (0..15).rev() {
            let t=self.frame_target(j);self.inplace(b,&t,Gate::Top(j));
            k.divide(b,self,&t,Gate::Top(j),true);
        }
        b.play(&frame,true);
        k.v(b,self,false,None,false);self.search_bottom(b,k,true);
        k.v(b,self,false,Some(2),true);
    }
    pub(crate) fn hr_finish(&self,b:&mut B,k:&mut impl Kernels) {
        let frame=k.top_frame(b,self);b.play(&frame,false);
        for j in 0..15 {
            let t=self.frame_target(j);k.divide(b,self,&t,Gate::Top(j),false);
            self.inplace(b,&t,Gate::Top(j));
        }b.play(&frame,true);
        let frame=k.natural_frame(b,self);b.play(&frame,false);
        for i in (0..15).rev() {
            let t=self.natural_target(i);k.divide(b,self,&t,Gate::Bottom(i),false);
            self.park(b,i,Gate::Bottom(i),true);self.inplace(b,&t,Gate::Bottom(i));
        }b.play(&frame,true);
        // Every park, including Q[Y], is now returned. PH still has phase.
        k.hr_payload_open(b,self);
        for i in 0..self.qb {
            let t=self.natural_target(i);self.inplace(b,&t,Gate::Natural(i));
            k.hr_payload_tick(b,self,i);k.divide(b,self,&t,Gate::Natural(i),true);
        }
        k.hr_payload_close(b,self);k.z_flip(b,self);k.toggle_activity(b,self,false);
    }
    pub(crate) fn ht_finish(&self,b:&mut B,k:&mut impl Kernels,whole_only:bool) {
        self.check();assert!(whole_only,"partial upto ABI is not implemented");
        k.toggle_activity(b,self,true);
        let frame=k.natural_frame(b,self);b.play(&frame,false);
        for i in 0..15 {
            let t=self.natural_target(i);self.inplace(b,&t,Gate::Bottom(i));
            self.park(b,i,Gate::Bottom(i),false);
        }b.play(&frame,true);
        let frame=k.top_frame(b,self);b.play(&frame,false);
        for j in (0..15).rev() {
            let t=self.frame_target(j);self.inplace(b,&t,Gate::Top(j));
            k.divide(b,self,&t,Gate::Top(j),true);
        }b.play(&frame,true);
        k.v(b,self,true,Some(2),false);
        let frame=k.natural_frame(b,self);b.play(&frame,false);
        for i in (0..15).rev() {
            let t=self.natural_target(i);self.park(b,i,Gate::Bottom(i),false);
            k.add(b,self,&t,Gate::Bottom(i));self.store(b,&t,Gate::Bottom(i),VTop::Zero,false);
        }b.play(&frame,true);
        let undo=rec(b,|b|self.search_bottom(b,k,false));b.play(&undo,true);
        k.v(b,self,true,None,true);
        let frame=k.top_frame(b,self);b.play(&frame,false);
        for j in 0..15 {
            let t=self.frame_target(j);k.divide(b,self,&t,Gate::Top(j),false);
            self.inplace(b,&t,Gate::Top(j));
        }
        for j in 0..15 {
            let t=self.frame_target(j);self.inplace(b,&t,Gate::Top(j));
            self.park(b,j,Gate::Top(j),false);
        }b.play(&frame,true);
        k.v(b,self,true,Some(0),false);
        let frame=k.top_frame(b,self);b.play(&frame,false);
        for j in 0..15 {
            let t=self.frame_target(j);self.park(b,j,Gate::Top(j),false);
            k.add(b,self,&t,Gate::Top(j));self.store(b,&t,Gate::Top(j),VTop::Frame(j),false);
        }b.play(&frame,true);
        let undo=rec(b,|b|self.search_top(b,k,false));b.play(&undo,true);
        k.v(b,self,true,None,true);k.toggle_activity(b,self,true);k.z_flip(b,self);
    }
}
