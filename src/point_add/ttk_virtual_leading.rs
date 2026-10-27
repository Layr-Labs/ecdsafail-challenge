//! SOURCE-ONLY four-scalar restoring digit; not registered or emitted.
//!
//! Metadata is SumSize(E=Y-1,S=Z+Y-226). The Z affine epoch costs34T
//! each way and touches no Q data. Scalar ports are activity A, quotient e,
//! mask/sign m, and optional saved physical source top b. There is no
//! initial carry owner and no separate retained quotient-guard owner.
//! Physical source bits at/above logical R may be arbitrary parked data.
//! The logical source top R-1 is always ONE; below it the source is real.
//!
//! A complete inverse may enter with m=1 only where A=0 and e=0. The
//! skipped guard is stored in e while A becomes A&G. Every e-dependent
//! write retains A explicitly, so both the dirty mask and witness return.
//! This is a guarded restoring-division interface, not a generic adder.

use super::builder::{B,G};
use super::mask::mc_xor;
use super::sum_size::SumSize;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[derive(Clone,Copy)]
pub(crate) enum Size { Y, Z }

fn terms(meta:&SumSize,size:Size,value:usize)->Vec<Vec<(QubitId,bool)>> {
    match size {Size::Y=>meta.y_terms(value),Size::Z=>meta.z_terms(value)}
}

fn query(b:&mut B,meta:&SumSize,size:Size,value:usize,target:QubitId,
    extra:&[(QubitId,bool)],dirty:&[QubitId]) {
    meta.xor_terms(b,terms(meta,size,value),target,extra,dirty);
}

/// Only the current query's controls/target are occupied. All other
/// arithmetic cells are arbitrary dirty loans and return before the next
/// ripple cell. Metadata/scalars remain excluded for the entire body.
fn data_bank(meta:&SumSize,t:&[QubitId],s:&[QubitId],roles:&[QubitId],
    dirty:&[QubitId])->Vec<QubitId> {
    let excluded:BTreeSet<_>=meta.y.iter().chain(&meta.sum).chain(roles).copied().collect();
    let mut seen=BTreeSet::new();
    dirty.iter().chain(t).chain(s).copied()
        .filter(|q|!excluded.contains(q)&&seen.insert(*q)).collect()
}

fn lower_write(b:&mut B,activity:QubitId,mask:QubitId,source:QubitId,
    target:QubitId,dirty:&[QubitId]) {
    let used=[activity,mask,source,target];
    let bank:Vec<_>=dirty.iter().copied().filter(|q|!used.contains(q)).collect();
    mc_xor(b,&[(activity,false),(mask,false),(source,false)],target,&[],&bank);
}

fn false_guard_terms(meta:&SumSize,limit:isize)->Vec<Vec<(QubitId,bool)>> {
    let mut lo=(limit.saturating_add(1).max(0)as usize).min(32);let mut out=vec![];
    while lo<32 {
        let mut free=if lo==0 {5}else{lo.trailing_zeros() as usize};
        while lo+(1usize<<free)>32 {free-=1;}
        out.push((free..5).map(|i|(meta.sum[i],(lo>>i)&1==0)).collect());
        lo+=1usize<<free;
    }
    out
}

/// XOR the carry polynomial into mask. At the selected boundary mask is
/// zero; at other boundaries its arbitrary running value is harmless
/// because all three central queries include the disjoint size equality.
/// Repeating this function erases the temporary carry: neither central
/// target e nor t[R] occurs among its inputs.
/// At R>1, prepared u=physical_top XOR carry and v=target_top XOR
/// physical_top. With saved physical top b, virtual-leading ONE gives
/// C=(u XOR b) OR (v XOR b)=u+v+uv+b+bu+bv over GF(2).
/// If physical top is known ONE, C=1+uv and no saved owner is needed.
fn toggle_carry(b:&mut B,t:&[QubitId],s:&[QubitId],r:usize,
    mask:QubitId,saved:Option<QubitId>) {
    assert!(r>=1&&r<=s.len());
    if r==1 {b.cx(t[0],mask);return;} // carry0=0; no TTK XOR on bit0.
    let (u,v)=(s[r-1],t[r-1]);
    if let Some(top)=saved {
        b.cx(u,mask);b.cx(v,mask);b.ccx(u,v,mask);b.cx(top,mask);
        b.ccx(top,u,mask);b.ccx(top,v,mask);
    }else{b.x(mask);b.ccx(u,v,mask);}
}

/// Capture a restoring division with logical source bits0..R-2 real,
/// bitR-1=ONE, and every higher logical bitZERO. The physical source is
/// completely restored. On A&G, m starts0, e starts0 and d<2*r; the guard
/// is the caller's unchanged sum bound. On A0, e=0 and m may be arbitrary.
/// Internally !G transports original A into e and clears A; the complete
/// body is identity on A0 even with arbitrary e/m/saved. Both are restored
/// by reversing the two guard queries after the arithmetic.
/// `saved=None` additionally requires physical source[R-1]=1 on A&G.
/// `saved=Some(g)` consumes the fourth scalar and allows arbitrary top.
#[allow(clippy::too_many_arguments)]
pub(crate) fn restoring_record(b:&mut B,meta:&SumSize,size:Size,
    t:&[QubitId],s:&[QubitId],activity:QubitId,e:QubitId,mask:QubitId,
    saved:Option<QubitId>,lo:usize,hi:usize,sum_limit:isize,dirty:&[QubitId])->Vec<G> {
    assert!(s.len()>=2&&(s.len()==t.len()||s.len()+1==t.len()));
    assert!(1<=lo&&lo<=hi&&hi<t.len()&&hi<=s.len());
    let mut ports=BTreeSet::new();
    assert!(meta.y.iter().chain(&meta.sum).chain(t).chain(s).copied()
        .chain([activity,e,mask]).chain(saved).all(|q|ports.insert(q)));
    let roles:Vec<_>=[activity,e,mask].into_iter().chain(saved).collect();
    let bank=data_bank(meta,t,s,&roles,dirty);
    // A query removes at most three of these data cells (target and two
    // controls). Remaining arbitrary cells fund even a 15-control query.
    assert!(bank.len()>=20,"literal queries need returned disjoint data loans");
    b.begin();
    b.begin();
    meta.xor_terms(b,false_guard_terms(meta,sum_limit),e,&[(activity,false)],&bank);
    meta.xor_terms(b,false_guard_terms(meta,sum_limit),activity,&[(e,false)],&bank);
    let guard_prep=b.end();b.play(&guard_prep,false);
    if let Some(g)=saved {
        for r in lo..=hi {
            query(b,meta,size,r,g,&[(activity,false),(s[r-1],false)],&bank);
        }
    }
    for &q in t {b.x(q);}
    b.begin();
    for i in 1..s.len() {b.cx(s[i],t[i]);}
    // Leave the virtual boundary target t[R] ORIGINAL. Only its one
    // initial CX is cancelled; preparation above R may be arbitrary
    // because the complete higher ladder is undone before R is queried.
    for r in lo..=hi {
        if r<s.len() {query(b,meta,size,r,t[r],&[(s[r],false)],&bank);}
    }
    let target_prep=b.end();b.play(&target_prep,false);
    for i in (1..s.len()-1).rev() {b.cx(s[i],s[i+1]);}
    for i in 0..s.len()-1 {b.ccx(t[i],s[i],s[i+1]);}
    for i in (0..t.len()).rev() {
        if (lo..=hi).contains(&i) {
            toggle_carry(b,t,s,i,mask,saved);
            // e ^= A&eq(R,i)&!(t[i]&C). A already includes G. Here t[i] is
            // the original complemented boundary on the selected shot.
            query(b,meta,size,i,e,&[(activity,false)],&bank);
            query(b,meta,size,i,e,&[(activity,false),(t[i],false),(mask,false)],&bank);
            // The virtual-zero source boundary writes e*C, never the
            // physical prepared source[i] which may contain a park.
            query(b,meta,size,i,t[i],&[(activity,false),(e,false),(mask,false)],&bank);
            toggle_carry(b,t,s,i,mask,saved);
        }
        if i<hi {
            assert!(i<s.len());
            // mask=e&[R>i] on A1. A is indispensable when inverse sign
            // occupies mask=1 on an off-activity shot.
            lower_write(b,activity,mask,s[i],t[i],&bank);
        }
        if let Some(g)=saved {
            if (lo..=hi).contains(&(i+1)) {
                // Ordinary TTK writes physical_top XOR carry. Correct
                // the top to ONE XOR carry without changing its source.
                query(b,meta,size,i+1,t[i],&[(activity,false),(e,false),(g,true)],&bank);
            }
        }
        if (lo..=hi).contains(&i) {
            query(b,meta,size,i,mask,&[(activity,false),(e,false)],&bank);
        }
        if i>=1&&i<s.len() {b.ccx(t[i-1],s[i-1],s[i]);}
    }
    b.ccx(activity,e,mask);
    for i in 1..s.len()-1 {b.cx(s[i],s[i+1]);}
    b.play(&target_prep,true);
    for &q in t {b.x(q);}
    if let Some(g)=saved {
        for r in lo..=hi {
            query(b,meta,size,r,g,&[(activity,false),(s[r-1],false)],&bank);
        }
    }
    b.play(&guard_prep,true);
    b.end()
}

/// Whole raw-size epoch. For inverse payload use, sign=>original A and
/// e=>A&!sign&guard are REQUIRED caller invariants. CX(sign,A) retains
/// A'=A&!sign without a fifth scalar; the sign owner itself is then a
/// conditionally-zero running mask. Restore it before reversing that CX.
/// P258 may occupy PH throughout: this wrapper never reads PH or payload
/// as phase metadata. It does not implement splice entry/exit itself.
#[allow(clippy::too_many_arguments)]
pub(crate) fn play(b:&mut B,meta:&SumSize,size:Size,t:&[QubitId],s:&[QubitId],
    activity:QubitId,e:QubitId,mask_sign:QubitId,saved:Option<QubitId>,
    lo:usize,hi:usize,sum_limit:isize,inverse:bool,dirty:&[QubitId]) {
    if inverse {b.cx(mask_sign,activity);}
    let roles:Vec<_>=[activity,e,mask_sign].into_iter().chain(saved).collect();
    let bank=data_bank(meta,t,s,&roles,dirty);
    let epoch=match size {Size::Y=>None,Size::Z=>Some(meta.z_epoch(b,&bank))};
    if let Some(a)=&epoch {b.play(a,false);}
    let arithmetic=restoring_record(b,meta,size,t,s,activity,e,mask_sign,saved,
        lo,hi,sum_limit,dirty);
    b.play(&arithmetic,inverse);
    if let Some(a)=&epoch {b.play(a,true);}
    if inverse {b.cx(mask_sign,activity);}
}
