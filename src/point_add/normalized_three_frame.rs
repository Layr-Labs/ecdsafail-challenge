//! Three-owner whole-epoch coordinate permutation.
//!
//! E=Y-1, delta=127-E. Move the complete (Q128,x128) cycle UP delta
//! and the complete ring257 DOWN delta. No zero-filled shift is used:
//! quotient parks and inactive counter passengers undergo permutations.
//! All 129 Q-cycle cells remain physical data while this frame is open.
use super::builder::{B,G};
use super::cross_three::Cross;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// Raw source i moves to i+delta mod129. On active Y1..128:
/// leading Q[Y-1] ->127, park q0 ->128, park qj ->j-1 (j1..14).
/// Thus only normalized positions0..13 mix parks with source data.
/// Positions14..127 are genuine source bits or zero padding, with the
/// true leading ONE at127. Inactive passengers need not have this care.
pub(crate) fn q_cycle(c:&Cross<'_>)->Vec<QubitId>{
    assert_eq!(c.q.len(),128);
    c.q.iter().copied().chain([c.roles.work]).collect()
}

/// Exact literal permutation on every binary input. E is restored before
/// returning and must keep its original value until the frame is closed.
/// The intended integration captures once around a complete arithmetic
/// epoch and closes before a raw V, payload tick, map, or phase query.
pub(crate) fn record(b:&mut B,c:&Cross<'_>)->Vec<G>{
    assert_eq!(c.ring.len(),257);
    let q=q_cycle(c);
    let mut used=BTreeSet::new();
    assert!(q.iter().chain(c.ring).chain(&c.size.y).chain(&c.size.sum)
        .copied().chain([c.roles.activity,c.roles.flight,c.phase])
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
pub(crate) fn q_record(b:&mut B,c:&Cross<'_>)->Vec<G>{
    let q=q_cycle(c);b.begin();
    for &e in &c.size.y{b.x(e);}
    for(k,&e)in c.size.y.iter().enumerate(){
        super::frogdrop::crot_up(b,e,&q,1usize<<k);
    }
    for &e in &c.size.y{b.x(e);}b.end()
}

/// Ring-only half. It remains open across the four complete native V
/// plays and closes before raw payload/activity/outer boundaries.
pub(crate) fn ring_record(b:&mut B,c:&Cross<'_>)->Vec<G>{
    assert_eq!(c.ring.len(),257);b.begin();
    for &e in &c.size.y{b.x(e);}
    for(k,&e)in c.size.y.iter().enumerate(){
        super::frogdrop::crot_up(b,e,c.ring,257-(1usize<<k));
    }
    for &e in &c.size.y{b.x(e);}b.end()
}

/// Natural arithmetic source position j pairs with ring'[256-k-j].
/// At j128 this is the fixed virtual-zero target ring'[128-k].
pub(crate) fn natural_target(c:&Cross<'_>,k:usize)->Vec<QubitId>{
    assert!(k<30);
    (0..129).map(|j|c.ring[256-k-j]).collect()
}

/// After the existing S-only top frame, source position j pairs with
/// ring'[(256+step-j) mod257]. The boundary is ring'[128+step].
pub(crate) fn top_target(c:&Cross<'_>,step:usize)->Vec<QubitId>{
    assert!(step<15);
    (0..129).map(|j|c.ring[(256+step-j)%257]).collect()
}

pub(crate) fn park(c:&Cross<'_>,j:usize)->QubitId{
    assert!(j<15);
    if j==0{c.roles.work}else{c.q[j-1]}
}

/// The inherited unconditional leading-Z flip can remain inside this
/// coordinate epoch: (Z-1)-delta=97+S, without modular wrap. All32 words
/// of S have one actual leaf; the complete gather returns every other cell.
pub(crate) fn z_flip_record(b:&mut B,c:&Cross<'_>)->Vec<G>{
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

