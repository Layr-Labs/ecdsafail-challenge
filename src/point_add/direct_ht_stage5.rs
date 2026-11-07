//! SOURCE-ONLY direct E7/S5 HT stage 5; no registration or execution.
//!
//! Entry is AFTER the outside switch witness was erased and complete HT
//! activity was retained on A. e/m/x128 are globally zero. This module
//! returns the SAME A, original E/S and raw phase; the caller erases A only
//! after this return. The inherited unconditional leading-Z flip remains
//! in the output ring representation, including on inactive branches.
//!
//! QB30 is preserved. With payload, PH is the 259th logical P cell from
//! digit through both exact nopark transition sweeps. During division
//! x128 is the returned carry; during the sweeps it holds q_g, and X(A)
//! is the conditional-zero carry instead. There is no phase query between
//! payload::digit and payload::finish_phase.

use super::builder::{B,G};
use super::cross_four::{Cross,Gate};
use super::cross_running_flight;
use super::direct_payload::{self,Arithmetic,Context,Ranges};
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn record(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn eq(word:&[QubitId],v:usize)->Vec<(QubitId,bool)>{
    word.iter().enumerate().map(|(i,&q)|(q,v>>i&1==0)).collect()
}
fn cover(word:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>>{
    assert!(lo<=hi&&hi<=1usize<<word.len());let mut out=vec![];
    while lo<hi{
        let mut free=if lo==0{word.len()}else{lo.trailing_zeros()as usize};
        free=free.min(word.len());while lo+(1usize<<free)>hi{free-=1;}
        out.push((free..word.len()).map(|i|(word[i],lo>>i&1==0)).collect());
        lo+=1usize<<free;
    }out
}
fn bank(c:&Cross<'_>,raw:&[QubitId],extra:&[QubitId])->Vec<QubitId>{
    let r=c.roles;
    let mut used:BTreeSet<_>=c.size.y.iter().chain(&c.size.sum).copied()
        .chain([c.phase,r.activity,r.flight,r.mask,r.x128])
        .chain(extra.iter().copied()).collect();
    c.dirty.iter().chain(c.ring).chain(c.q).chain(raw).copied()
        .filter(|q|used.insert(*q)).collect()
}
fn literal(b:&mut B,terms:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    assert!(!terms.iter().any(|p|p.0==target));
    let mut used:BTreeSet<_>=terms.iter().map(|p|p.0).chain([target]).collect();
    let d:Vec<_>=dirty.iter().copied().filter(|q|used.insert(*q)).collect();
    assert!(d.len()>=terms.len().saturating_sub(2));
    mc_xor(b,terms,target,&[],&d);
}
fn sum_le(b:&mut B,c:&Cross<'_>,limit:usize,dirty:&[QubitId]){
    assert!(limit<=31);let r=c.roles;
    for mut term in cover(&c.size.sum,0,limit+1){
        term.push((r.activity,false));literal(b,&term,r.mask,dirty);
    }
}
fn sum_eq(b:&mut B,c:&Cross<'_>,value:usize,dirty:&[QubitId]){
    assert!(value<=31);let mut term=eq(&c.size.sum,value);
    term.push((c.roles.activity,false));literal(b,&term,c.roles.mask,dirty);
}

/// All trees are full literal permutations with their exact reverse.
/// Their only middle write retains the complete activity/sum gate.
fn gathered(b:&mut B,address:&[QubitId],leaves:&[(usize,QubitId)],
    body:impl FnOnce(&mut B,QubitId)){
    assert!(!leaves.is_empty());
    let mut swaps=vec![];
    let root=super::midg::swap_tree(address,leaves,address.len(),&mut swaps);
    for &(q,l,r)in &swaps{b.cswap(q,l,r);}
    body(b,root);
    for &(q,l,r)in swaps.iter().rev(){b.cswap(q,l,r);}
}

fn natural_target(c:&Cross<'_>,k:usize)->Vec<QubitId>{
    let span=(c.y_bounds.1+1).min(257-k);
    (0..span).map(|i|c.ring[256-k-i]).collect()
}
fn inplace(b:&mut B,c:&Cross<'_>,k:usize,dirty:&[QubitId]){
    let r=c.roles;
    let leaves:Vec<_>=(c.y_bounds.0..=c.y_bounds.1)
        .map(|y|(y-1,c.ring[256-y-k])).collect();
    sum_le(b,c,31-k,dirty);
    gathered(b,&c.size.y,&leaves,|b,root|b.cswap(r.mask,root,r.flight));
    sum_le(b,c,31-k,dirty);
}

/// The Z byte occupies E7+returned m only within this tape. The selected
/// root is ring[Z-1]; neither A nor saved q_g enters the address/dirty bank.
fn save_top_record(b:&mut B,c:&Cross<'_>,zrange:(usize,usize),dirty:&[QubitId])->Vec<G>{
    let r=c.roles;
    let address=super::direct_frame::z_byte_record(b,c.size,r.mask,dirty);
    let word:Vec<_>=c.size.y.iter().copied().chain([r.mask]).collect();
    let leaves:Vec<_>=(zrange.0..=zrange.1).map(|z|(z-1,c.ring[z-1])).collect();
    record(b,|b|{
        b.play(&address,false);
        gathered(b,&word,&leaves,|b,root|b.cswap(r.activity,root,r.x128));
        b.play(&address,true);
    })
}

/// Fetch q_k while the true Z leading ONE is restored in the ring.
/// At k=g, exchange the root with saved q_g only around the flight swap;
/// the leading ONE returns to the root. Every predicate clears before the
/// next one; m is never held through an arithmetic ripple.
fn fetch_first(b:&mut B,c:&Cross<'_>,k:usize,dirty:&[QubitId]){
    let r=c.roles;
    let leaves:Vec<_>=(c.y_bounds.0..=c.y_bounds.1)
        .map(|y|(y-1,c.ring[256-y-k])).collect();
    gathered(b,&c.size.y,&leaves,|b,root|{
        let d=bank(c,&[],&[root]);
        sum_eq(b,c,31-k,&d);b.cswap(r.mask,root,r.x128);sum_eq(b,c,31-k,&d);
        sum_le(b,c,31-k,&d);b.cswap(r.mask,root,r.flight);sum_le(b,c,31-k,&d);
        sum_eq(b,c,31-k,&d);b.cswap(r.mask,root,r.x128);sum_eq(b,c,31-k,&d);
    });
    // The parent bank is deliberately not a stateful cache across the tree.
    let _=dirty;
}

/// Both metadata words are immutable throughout the complete transition.
/// Y is represented by E=Y-1, so boundary top-Y = (top-1)-E.
#[derive(Clone,Copy)]
enum Boundary{Y{top:usize,lo:usize,hi:usize},Sum{top:usize,lo:usize,hi:usize}}
impl Boundary{
    fn ports<'a>(&self,c:&'a Cross<'_>)->(&'a [QubitId],usize,usize,usize){
        match *self{
            Self::Y{top,lo,hi}=>(&c.size.y,top-1,lo-1,hi-1),
            Self::Sum{top,lo,hi}=>(&c.size.sum,top,lo,hi),
        }
    }
}

/// Exact inherited prefix addition with a virtual-zero boundary source.
/// Existing source cells at/above B may be arbitrary q/coeff passengers.
/// Full up/undo exposes the incoming carry; old m writes source below B,
/// new m writes the carry at B. No blanket upper-target zero is required.
fn transition(b:&mut B,c:&Cross<'_>,target:&[QubitId],source:&[QubitId],
    boundary:Boundary,dirty:&[QubitId]){
    assert_eq!(target.len(),source.len());assert!(!target.is_empty());
    let r=c.roles;let(word,top,lo,hi)=boundary.ports(c);
    assert!(lo<=hi&&hi<=top);
    let span=target.len().min(top-lo+1);
    let(t,s)=(&target[..span],&source[..span]);
    let mut used=BTreeSet::new();
    assert!(t.iter().chain(s).copied().chain([r.activity,r.flight,r.mask])
        .all(|q|used.insert(q)));
    assert!(word.iter().all(|q|!used.contains(q)));
    // Queries may borrow any operand transiently; each dirty chain restores
    // it before the next MAJ cell. They do NOT read the borrowed A carry.
    let d=bank(c,target,&[]);
    assert!(dirty.iter().all(|q|*q!=r.activity&&*q!=r.flight&&*q!=r.mask));
    b.x(r.activity); // e=>original A, hence conditional carry zero.
    for i in 0..span{let x=if i==0{r.activity}else{s[i-1]};
        b.cx(s[i],t[i]);b.cx(s[i],x);b.ccx(x,t[i],s[i]);}
    let mut next=lo;
    while next<=hi&&top-next>=span{
        let mut term=eq(word,next);term.push((r.flight,false));
        literal(b,&term,r.mask,&d);next+=1;
    }
    for i in(0..span).rev(){let x=if i==0{r.activity}else{s[i-1]};
        b.ccx(x,t[i],s[i]);b.cx(s[i],x);b.cx(s[i],t[i]);
        if next<=hi&&next<=top-i{
            b.ccx(r.mask,s[i],t[i]);
            while next<=hi&&next<=top-i{
                let mut term=eq(word,next);term.push((r.flight,false));
                literal(b,&term,r.mask,&d);next+=1;
            }
            b.ccx(r.mask,x,t[i]);
        }else{
            b.cx(x,s[i]);b.ccx(r.mask,s[i],t[i]);b.cx(x,s[i]);
        }
    }
    assert_eq!(next,hi+1);b.cx(r.flight,r.mask);b.x(r.activity);
}

fn fetch_correction(b:&mut B,c:&Cross<'_>,k:usize,sum_lo:usize,dirty:&[QubitId]){
    let r=c.roles;
    let leaves:Vec<_>=(sum_lo..=31-k).map(|s|{
        let gap=31-s;
        (s,if gap==k{r.x128}else{c.ring[(gap+256-k)%257]})
    }).collect();
    sum_le(b,c,31-k,dirty);
    gathered(b,&c.size.sum,&leaves,|b,root|b.cswap(r.mask,root,r.flight));
    sum_le(b,c,31-k,dirty);
}

/// Complete Cross HT stage5. `compact=None` is the inherited no-P path;
/// it still performs all thirty in-place quotient steps. With payload,
/// open/digit, both full correction sweeps, and close are all included.
/// A remains held on return for the outside exact activity cleanup.
pub(crate) fn run(b:&mut B,c:&Cross<'_>,zrange:(usize,usize),
    compact:Option<&[QubitId]>,arithmetic:&mut impl Arithmetic){
    assert_eq!((c.ring.len(),c.q.len(),c.qb),(257,128,30));
    assert!(98<=zrange.0&&zrange.0<=zrange.1&&zrange.1<=256);
    assert!(1<=c.y_bounds.0&&c.y_bounds.0<=c.y_bounds.1&&c.y_bounds.1<=128);
    let r=c.roles;let mut used=BTreeSet::new();
    assert!(c.ring.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum).copied()
        .chain([c.phase,r.activity,r.flight,r.mask,r.x128]).all(|q|used.insert(q)));
    if let Some(p)=compact{assert_eq!(p.len(),258);assert!(p.iter().all(|q|used.insert(*q)));}
    let roles=direct_payload::Roles{activity:r.activity,flight:r.flight,sign:r.mask,work:r.x128};
    let session=compact.map(|p|direct_payload::digit(b,&Context{
        meta:c.size,compact:p,ring:c.ring,q:c.q,phase:c.phase},roles,true,
        Ranges{z:zrange,y:c.y_bounds},arithmetic,c.dirty));
    let raw=session.as_ref().map(|s|s.raw.as_slice()).unwrap_or(&[]);
    let d=bank(c,raw,&[]);
    let zflip=super::direct_frame::z_lane_record(b,c.size,c.ring,r.mask,zrange,256,None,&d);
    b.play(&zflip,false);
    // The complete normalized epoch returns raw coordinates before q_g
    // is saved. PH may contain the materialized payload and is excluded.
    super::normalized_cross_s5::run(b,c);
    let Some(session)=session else{return;};
    let sum_lo=zrange.0.saturating_add(c.y_bounds.0).max(226)-226;
    assert!(sum_lo<=31);
    let kend=30.min(32-sum_lo);
    let save=save_top_record(b,c,zrange,&d);b.play(&save,false);
    b.play(&zflip,false); // q_g saved, expose Z's true leading ONE.

    for k in 0..kend{
        fetch_first(b,c,k,&d);
        let span=(259-k).min(257);
        let t:Vec<_>=(k..k+span).map(|pos|session.raw[258-pos]).collect();
        transition(b,c,&t,&c.ring[..span],Boundary::Y{
            top:258-k,lo:c.y_bounds.0,hi:c.y_bounds.1},&d);
        fetch_first(b,c,k,&d);
    }
    b.play(&zflip,false); // correction reads the isolated q block.
    let prev:Vec<_>=session.raw.iter().rev().copied().collect();
    let pr=super::direct_frame::rotate_z_record(b,c.size,&prev,r.mask,zrange,None,true,&d);
    let rr=super::direct_frame::rotate_z_record(b,c.size,c.ring,r.mask,zrange,None,true,&d);
    b.play(&pr,false);b.play(&rr,false);
    for k in 0..kend{
        fetch_correction(b,c,k,sum_lo,&d);
        // dl=-1 for ring257. B=g+2-k=33-S-k; at smallest S
        // this may be just beyond the slice, as in the original kernel.
        let span=33-sum_lo-k;
        let t:Vec<_>=(0..span).map(|i|prev[(k+258+i)%259]).collect();
        let s:Vec<_>=(0..span).map(|i|c.ring[(256+i)%257]).collect();
        for &q in &t{b.x(q);}
        transition(b,c,&t,&s,Boundary::Sum{top:33-k,lo:sum_lo,hi:31-k},&d);
        for &q in &t{b.x(q);}
        fetch_correction(b,c,k,sum_lo,&d);
    }
    b.play(&rr,true);b.play(&pr,true);b.play(&save,true);
    direct_payload::finish_phase(b,c.size,&session,c.y_bounds,r.mask,&d);
}
