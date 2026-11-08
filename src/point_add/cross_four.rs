//! SOURCE-ONLY controller, not registered or compiled.
//!
//! E7=Y-1 and S5=Z+Y-226 stay in the same view at every method boundary.
//! Four physical scalar ports: activity, quotient flight, returned mask,
//! and x128. No SX0, selector, retained ak, or sixth vprime bit is present.
//! The expensive arithmetic/V adapters below are explicit pending bindings;
//! they may NOT allocate or retain an undisclosed owner.
//!
//! Virtual-zero arithmetic never reads physical Q[Y] as its carry. Thus
//! q0 remains in Q[Y], like all higher park bits, for its entire lifetime.
//! All old SX0/PH q0 shuttles disappear. PH remains metadata until a
//! payload callback explicitly opens its separate P258 splice epoch.

use super::builder::{B,G};
use super::mask::mc_xor;
use super::sum_size::SumSize;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[derive(Clone,Copy)]
pub(crate) struct Roles { pub activity:QubitId, pub flight:QubitId,
    pub mask:QubitId, pub x128:QubitId }
#[derive(Clone,Copy)]
pub(crate) enum Gate { Top(usize), Bottom(usize), Natural(usize) }
#[derive(Clone,Copy)]
pub(crate) enum VTop { Zero, Frame(usize) }

/// These adapters are deliberately an unimplemented integration surface.
/// `divide`/`inverse_divide` use virtual ONE at Q[Y-1], virtual ZERO above
/// it, and restore arbitrary physical parked Q[Y..128]. They use A/e/m
/// only, leaving x128 as source data when it belongs to the word.
/// `add` retains incoming e and returns m; `vbit` computes the parent's
/// unchanged V threshold/addition BEFORE its separate store operation.
/// Frame and V records preserve E/S and phase, and return flight/mask.
/// A and parked x128 remain retained passengers of complete V records.
pub(crate) trait Kernels {
    fn top_frame(&mut self,b:&mut B,c:&Cross<'_>)->Vec<G>;
    fn natural_frame(&mut self,b:&mut B,c:&Cross<'_>)->Vec<G>;
    fn v(&mut self,b:&mut B,c:&Cross<'_>,ht:bool,park:Option<usize>,inverse:bool);
    fn toggle_activity(&mut self,b:&mut B,c:&Cross<'_>,ht:bool);
    fn divide(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate,inverse:bool);
    fn add(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate);
    fn vbit(&mut self,b:&mut B,c:&Cross<'_>,target:&[QubitId],gate:Gate,top:VTop);
    /// Payload may use all four scalar owners after every Q park is gone.
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

fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G> { b.begin();f(b);b.end() }
fn range(word:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>> {
    assert!(lo<=hi&&hi<=1usize<<word.len());let mut out=vec![];
    while lo<hi {
        let mut free=if lo==0 {word.len()}else{lo.trailing_zeros()as usize};
        free=free.min(word.len());while lo+(1usize<<free)>hi {free-=1;}
        out.push((free..word.len()).map(|i|(word[i],lo>>i&1==0)).collect());
        lo+=1usize<<free;
    }out
}

fn dirty_price(n:usize)->usize {if n<2{0}else if n==2{1}else{4*(n-2)}}
fn query_price(n:usize,clean:usize)->usize {
    if n<=2{return dirty_price(n);}
    let used=clean.min(n-2);if used==0{return dirty_price(n);}
    let rest=n-used-1;if rest==1{return used+1;}
    // mask::mc_xor's clean prefix, followed by its literal known-prefix
    // topology. No opaque multi-control operation has unit price here.
    let(mut available,mut pos,mut stack,mut prepare)=(2*used,0,1,0);
    while rest-pos>=2{let take=(available+1).min(rest-pos);
        prepare+=take-1;available=available-1+take;pos+=take;stack+=1;}
    used+2*prepare+dirty_price(stack+rest-pos)
}

impl Cross<'_> {
    fn check(&self) {
        assert_eq!((self.ring.len(),self.q.len()),(257,128));
        assert_eq!(self.qb,30,"preserve the qualified two-band width");
        assert!(1<=self.y_bounds.0&&self.y_bounds.0<=self.y_bounds.1&&self.y_bounds.1<=128);
        let r=self.roles;let mut seen=BTreeSet::new();
        assert!(self.ring.iter().chain(self.q).chain(&self.size.y).chain(&self.size.sum)
            .copied().chain([self.phase,r.activity,r.flight,r.mask,r.x128])
            .all(|q|seen.insert(q)));
        assert!(self.clean_external.len()==0||self.clean_external.len()==2);
        assert!(self.clean_external.iter().all(|q|seen.insert(*q)));
    }
    fn bank(&self,extra:&[QubitId])->Vec<QubitId> {
        let r=self.roles;
        let excluded:BTreeSet<_>=self.size.y.iter().chain(&self.size.sum).copied()
            .chain([self.phase,r.activity,r.flight,r.mask,r.x128])
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
    /// Compute A&Gate into returned m. Bottom has an exact cheaper
    /// coordinate when the real leading Q ONE is borrowed as its byte MSB.
    /// The complete gather/X/address/query/inverse/X/ungather returns Q
    /// before the middle action. Off A its interior query is identity, so
    /// the borrowed source bit may be arbitrary without a zero assertion.
    fn gate_record(&self,b:&mut B,gate:Gate)->Vec<G> {
        let r=self.roles;let old=self.gate_terms(gate);
        let old_price:usize=old.iter().map(|t|query_price(t.len()+1,self.clean_external.len())).sum();
        if let Gate::Bottom(k)=gate {
            // Both predicates are invariant through the selected body:
            // no body changes E/S/A or Q[Y-1]. The old band predicate is
            // A & !([Z-1>=128-k] & [S>=17-k]) on the complete size care.
            let mut byte=self.size.y.to_vec();byte.push(self.q[0]);
            let zc=range(&byte,128-k,256);
            let sc=range(&self.size.sum,17-k,32);
            let extras=self.clean_external;
            let clean=if extras.is_empty(){&[][..]}else{&extras[1..]};
            let predicate_price:usize=zc.iter().map(|z|sc.iter()
                .map(|s|query_price(z.len()+s.len()+1,clean.len())).sum::<usize>()).sum();
            let new_price=(if extras.is_empty(){2*(self.y_bounds.1-self.y_bounds.0)}else{0})+94+predicate_price;
            if new_price<old_price {
                let leaves:Vec<_>=(self.y_bounds.0..=self.y_bounds.1)
                    .map(|y|(y-1,self.q[y-1])).collect();
                let run=|b:&mut B,root:QubitId,leading:bool| {
                    let mut held=vec![root];held.extend_from_slice(clean);
                    let d=self.bank(&held);
                    let word:Vec<_>=self.size.y.iter().copied().chain([root]).collect();
                    let address=super::direct_frame::z_byte_record(b,self.size,root,&d);
                    if leading{b.x(root);}b.play(&address,false);b.cx(r.activity,r.mask);
                    for z in range(&word,128-k,256) {
                        for s in range(&self.size.sum,17-k,32) {
                            let mut t=z.clone();t.extend(s);t.push((r.activity,false));
                            mc_xor(b,&t,r.mask,clean,&d);
                        }
                    }
                    b.play(&address,true);if leading{b.x(root);}
                };
                return rec(b,|b|{
                    if let Some(&root)=extras.first(){run(b,root,false);}
                    else{self.gathered(b,&leaves,|b,root|run(b,root,true));}
                });
            }
        }
        let d=self.bank(self.clean_external);
        rec(b,|b|for mut t in old{t.push((r.activity,false));
            mc_xor(b,&t,r.mask,self.clean_external,&d);})
    }
    fn with_gate(&self,b:&mut B,gate:Gate,body:impl FnOnce(&mut B)) {
        let prepare=self.gate_record(b,gate);
        b.play(&prepare,false);body(b);b.play(&prepare,true);
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
    fn inplace(&self,b:&mut B,target:&[QubitId],gate:Gate) {
        let leaves:Vec<_>=(self.y_bounds.0..=self.y_bounds.1)
            .filter_map(|y|target.get(y).copied().map(|q|(y-1,q))).collect();
        self.with_gate(b,gate,|b|self.gathered(b,&leaves,|b,root|
            b.cswap(self.roles.mask,root,self.roles.flight)));
    }
    /// Same path for bit0 and all other parked bits. No phase/q0 shuttle.
    fn park(&self,b:&mut B,bit:usize,gate:Gate,erase:bool) {
        let leaves:Vec<_>=(self.y_bounds.0..=self.y_bounds.1).filter_map(|y| {
            let pos=y+bit;let q=if pos<128{self.q[pos]}else if pos==128{
                self.roles.x128}else{return None;};Some((y-1,q))
        }).collect();
        if erase {
            // The only erase callsites follow a complete Divide on the
            // SAME Gate, entered with e=0. Thus e=>A&Gate. Capacity failure
            // Y+bit>128 implies Gate=false, hence e0; a partial tree root
            // outside its public leaf set is then harmless. No m needed.
            self.gathered(b,&leaves,|b,root|b.cx(self.roles.flight,root));
        }else{
            // Each separate Top/Bottom session starts with empty Q parks.
            // Outside Gate, e and that session's Q[Y+bit] are both zero on
            // A. Slots are distinct and all complete V calls preserve them.
            // Thus only the capacity predicate is required for the swap.
            // It cannot be dropped when a partial tree has no actual leaf.
            if leaves.is_empty(){return;}
            let r=self.roles;
            if self.y_bounds.1<=128-bit {
                self.gathered(b,&leaves,|b,root|b.cswap(r.activity,root,r.flight));
            }else{
                let d=self.bank(self.clean_external);
                let prep=rec(b,|b|for mut t in range(&self.size.y,0,128-bit){
                    t.push((r.activity,false));mc_xor(b,&t,r.mask,self.clean_external,&d);
                });
                b.play(&prep,false);
                self.gathered(b,&leaves,|b,root|b.cswap(r.mask,root,r.flight));
                b.play(&prep,true);
            }
        }
    }
    fn store(&self,b:&mut B,target:&[QubitId],gate:Gate,top:VTop,inverse:bool) {
        let leaves:Vec<_>=(self.y_bounds.0..=self.y_bounds.1)
            .filter_map(|y|target.get(y).copied().map(|q|(y-1,q))).collect();
        self.with_gate(b,gate,|b|self.gathered(b,&leaves,|b,root| {
            let r=self.roles;let flip=|b:&mut B|match top {
                VTop::Zero=>b.cx(r.mask,root),
                VTop::Frame(j)=>{
                    if j!=0 {b.cx(r.mask,root);}else {
                        // top=[gap<QB]=[S>=32-QB]. Its complement is
                        // queried directly; the physical top flag is absent.
                        let mut held=vec![root];held.extend_from_slice(self.clean_external);
                        let d=self.bank(&held);
                        for mut t in range(&self.size.sum,0,32-self.qb) {
                            t.push((r.mask,false));mc_xor(b,&t,root,self.clean_external,&d);
                        }
                    }
                }
            };
            if inverse {b.cswap(r.mask,root,r.flight);flip(b);}
            else {flip(b);b.cswap(r.mask,root,r.flight);}
        }));
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
