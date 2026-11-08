//! Default-off K5 PH129 controller ports. No fourth role or allocation.
use super::builder::{B,G};
use super::cross_four::Gate;
use super::sum_size::SumSize;
use crate::circuit::QubitId;
use std::collections::BTreeSet;
#[derive(Clone,Copy)]
pub(crate) struct Roles {pub activity:QubitId,pub flight:QubitId,pub mask:QubitId}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Traversal {T1,T2,T3,T4}
impl Traversal {pub(crate) fn has_payload(self)->bool {matches!(self,Self::T1|Self::T4)}}
/// `ph` is raw phase only outside controller epochs, cycle DATA inside them.
/// `excluded` binds diagnostic spectators, including the original prefix owner.
/// P0/P1 are external loans only and may never appear in `q`, `ring` or roles.
pub(crate) struct Context<'a> {
 pub size:&'a SumSize,pub ring:&'a[QubitId],pub q:&'a[QubitId],pub ph:QubitId,
 pub roles:Roles,pub dirty:&'a[QubitId],pub y_bounds:(usize,usize),pub qb:usize,
 pub clean_external:&'a[QubitId],pub excluded:&'a[QubitId],pub traversal:Traversal,
}
fn range(word:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>> {
 assert!(lo<=hi&&hi<=1usize<<word.len());let mut out=vec![];
 while lo<hi {let mut free=if lo==0{word.len()}else{lo.trailing_zeros()as usize};
 free=free.min(word.len());while lo+(1usize<<free)>hi{free-=1;}
 out.push((free..word.len()).map(|i|(word[i],lo>>i&1==0)).collect());lo+=1usize<<free;}out
}
impl Context<'_> {
 pub(crate) fn check(&self) {
 assert_eq!((self.ring.len(),self.q.len(),self.size.y.len(),self.size.sum.len(),self.qb),(257,128,7,5,30));
 assert!(1<=self.y_bounds.0&&self.y_bounds.0<=self.y_bounds.1&&self.y_bounds.1<=128);
 let r=self.roles;let mut ports=BTreeSet::new();
 assert!(self.ring.iter().chain(self.q).chain(&self.size.y).chain(&self.size.sum).copied()
 .chain([self.ph,r.activity,r.flight,r.mask]).chain(self.clean_external.iter().copied())
 .chain(self.excluded.iter().copied()).filter(|q|super::c659::retained(*q)).all(|q|ports.insert(q)),"K5_PH_PORT_ALIAS");
 assert!(self.clean_external.is_empty()||(!self.traversal.has_payload()&&(self.clean_external.len()==2||super::c659::t23_enabled()&&self.clean_external.len()==1)),"K5_PH_LOANS");
 }
 pub(crate) fn bank(&self,extra:&[QubitId])->Vec<QubitId> {
 let r=self.roles;let mut held:BTreeSet<_>=self.size.y.iter().chain(&self.size.sum).copied()
 .chain([self.ph,r.activity,r.flight,r.mask]).chain(self.clean_external.iter().copied())
 .chain(self.excluded.iter().copied()).chain(extra.iter().copied()).filter(|q|super::c659::retained(*q)).collect();
 self.dirty.iter().chain(self.ring).chain(self.q).copied().filter(|q|held.insert(*q)).collect()
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
}
/// Raw source i moves to i+delta mod129. On active Y1..128:
/// leading Q[Y-1] ->127, park q0 ->128, park qj ->j-1 (j1..14).
/// Thus only normalized positions0..13 mix parks with source data.
/// Positions14..127 are genuine source bits or zero padding, with the
/// true leading ONE at127. Inactive passengers need not have this care.
pub(crate) fn q_cycle(c:&Context<'_>)->Vec<QubitId>{
    assert_eq!(c.q.len(),128);
    c.q.iter().copied().chain([c.ph]).collect()
}

/// Exact literal permutation on every binary input. E is restored before
/// returning and must keep its original value until the frame is closed.
/// The intended integration captures once around a complete arithmetic
/// epoch and closes before a raw V, payload tick, map, or phase query.
pub(crate) fn record(b:&mut B,c:&Context<'_>)->Vec<G>{
    assert_eq!(c.ring.len(),257);
    let q=q_cycle(c);
    let mut used=BTreeSet::new();
    assert!(q.iter().chain(c.ring).chain(&c.size.y).chain(&c.size.sum)
        .copied().chain([c.roles.activity,c.roles.flight,c.roles.mask]).filter(|q|super::c659::retained(*q))
        .all(|v|used.insert(v)));
    b.begin();
    for &e in &c.size.y{b.x(e);}
    for (k,&e) in c.size.y.iter().enumerate(){
        super::frogdrop::crot_up(b,e,&q,1usize<<k);
        super::frogdrop::crot_up(b,e,c.ring,257-(1usize<<k));
    }
    for &e in &c.size.y{b.x(e);}
    b.end()
}

/// Q-only half of the common coordinate. No ring or metadata value changes
/// at its boundary; preserves the original raw-Q catalyst around native V.
pub(crate) fn q_record(b:&mut B,c:&Context<'_>)->Vec<G>{
    let q=q_cycle(c);b.begin();
    for &e in &c.size.y{b.x(e);}
    for(k,&e)in c.size.y.iter().enumerate(){
        super::frogdrop::crot_up(b,e,&q,1usize<<k);
    }
    for &e in &c.size.y{b.x(e);}b.end()
}

/// Ring-only half. It remains open across the four complete native V
/// plays and closes before raw payload/activity/outer boundaries.
pub(crate) fn ring_record(b:&mut B,c:&Context<'_>)->Vec<G>{
    assert_eq!(c.ring.len(),257);b.begin();
    for &e in &c.size.y{b.x(e);}
    for(k,&e)in c.size.y.iter().enumerate(){
        super::frogdrop::crot_up(b,e,c.ring,257-(1usize<<k));
    }
    for &e in &c.size.y{b.x(e);}b.end()
}

/// Natural arithmetic source position j pairs with ring'[256-k-j].
/// At j128 this is the fixed virtual-zero target ring'[128-k].
pub(crate) fn natural_target(c:&Context<'_>,k:usize)->Vec<QubitId>{
    assert!(k<30);
    (0..129).map(|j|c.ring[256-k-j]).collect()
}

/// After the existing S-only top frame, source position j pairs with
/// ring'[(256+step-j) mod257]. The boundary is ring'[128+step].
pub(crate) fn top_target(c:&Context<'_>,step:usize)->Vec<QubitId>{
    assert!(step<15);
    (0..129).map(|j|c.ring[(256+step-j)%257]).collect()
}

pub(crate) fn park(c:&Context<'_>,j:usize)->QubitId{
    assert!(j<15);
    if j==0{c.ph}else{c.q[j-1]}
}

/// The inherited unconditional leading-Z flip can remain inside this
/// coordinate epoch: (Z-1)-delta=97+S, without modular wrap. All32 words
/// of S have one actual leaf; the complete gather returns every other cell.
pub(crate) fn z_flip_record(b:&mut B,c:&Context<'_>)->Vec<G>{
    let leaves:Vec<_>=(0..32).map(|s|(s,c.ring[97+s])).collect();
    let mut swaps=vec![];
    let root=super::midg::swap_tree(&c.size.sum,&leaves,5,&mut swaps);
    assert_eq!(swaps.len(),31);
    b.begin();
    for &(control,left,right) in &swaps{b.cswap(control,left,right);}
    b.x(root);
    for &(control,left,right) in swaps.iter().rev(){b.cswap(control,left,right);}
    b.end()
}

/// Each controlled rotation by2^k has one cycle: gcd(129,2^k)=1 and
/// gcd(257,2^k)=1. Each CSWAP has one literal Toffoli, so seven stages
/// cost7*(128+256)=2688 T in one direction, before any cancellation.
pub(crate) const ONE_DIRECTION_TOFFOLI:usize=2688;
pub(crate) const Z_FLIP_TOFFOLI:usize=62;


pub(crate) fn native_hr_q128_record(b:&mut B,c:&Context<'_>)->Vec<G>{
    c.check();b.begin();
    for &e in &c.size.y{b.x(e);}
    for(k,&e)in c.size.y.iter().enumerate(){
        super::frogdrop::crot_up(b,e,c.q,1usize<<k);
        super::frogdrop::crot_up(b,e,c.ring,257-(1usize<<k));
    }
    for &e in &c.size.y{b.x(e);}
    b.end()
}

