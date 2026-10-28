//! SOURCE-ONLY complete Q-source payload loops, not registered or run.
//!
//! Applies ONLY to HT forward restoring division and HR inverse erasure.
//! Entry Q is the unparked Y operand: Q[Y-1]=1, Q[Y..128]=0 on A.
//! Rotate all Q128 UP delta=128-Y. Its low delta cells are genuine zeros,
//! not quotient parks. Rotate all raw P259 UP delta for forward division,
//! DOWN delta for inverse erasure. Every arithmetic boundary is then128.
//! The complete coordinate is held across all thirty possible k values.
//!
//! Four original scalar owners A/e/sign/work suffice. work is the clean
//! carry. Forward sign is a global-zero running mask; inverse sign may be
//! one off its narrowed A, so every inverse central/lower write keeps A.
//! PH is part of raw P259 throughout and is never read as phase or carry.

use super::activity_guard::Guard;
use super::builder::{B,G};
use super::direct_payload::{Ranges,Roles};
use super::mask::mc_xor;
use super::sum_size::SumSize;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn literal(b:&mut B,controls:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    assert!(!controls.iter().any(|p|p.0==target));
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied().filter(|q|*q!=target
        &&!controls.iter().any(|p|p.0==*q)&&seen.insert(*q)).collect();
    mc_xor(b,controls,target,&[],&bank);
}

fn checked_bank(meta:&SumSize,q:&[QubitId],raw:&[QubitId],r:Roles,
    dirty:&[QubitId])->Vec<QubitId>{
    assert_eq!((meta.y.len(),meta.sum.len(),q.len(),raw.len()),(7,5,128,259));
    let mut held=BTreeSet::new();
    assert!(meta.y.iter().chain(&meta.sum).chain(q).chain(raw).copied()
        .chain([r.activity,r.flight,r.sign,r.work]).all(|p|held.insert(p)));
    let bank:Vec<_>=dirty.iter().copied().filter(|p|held.insert(*p)).collect();
    // All queries have at most six controls. Ring data may be arbitrary
    // returned donors; the source/target words are deliberately excluded.
    assert!(bank.len()>=4);bank
}

fn frame_record(b:&mut B,meta:&SumSize,q:&[QubitId],raw:&[QubitId],inverse_loop:bool)->Vec<G>{
    b.begin();
    for &e in &meta.y{b.x(e);}
    for (k,&e) in meta.y.iter().enumerate(){
        let amount=1usize<<k;
        super::frogdrop::crot_up(b,e,q,amount);
        super::frogdrop::crot_up(b,e,raw,if inverse_loop{259-amount}else{amount});
    }
    for &e in &meta.y{b.x(e);}
    b.end()
}

fn cell(b:&mut B,s:QubitId,t:QubitId,x:QubitId,inverse:bool){
    if inverse{b.ccx(x,t,s);b.cx(s,x);b.cx(s,t);}
    else{b.cx(s,t);b.cx(s,x);b.ccx(x,t,s);}
}

/// Fixed128 restoring subtraction. `conditional_mask` denotes a retained
/// sign passenger off A, not a new owner or a fresh sign computation.
/// On A the initial sign/mask is0. The exact captured inverse is used for
/// HR erasure, after CX(original_sign,A) excludes the negative branch.
fn restoring_record(b:&mut B,q:&[QubitId],t:&[QubitId],r:Roles,
    conditional_mask:bool,first:usize,dirty:&[QubitId])->Vec<G>{
    assert_eq!((q.len(),t.len()),(128,129));
    b.begin();
    for &t in t{b.x(t);}
    assert!(first<128);
    for i in first..128{cell(b,q[i],t[i],if i==first{r.work}else{q[i-1]},false);}
    // The virtual source at128 is zero; q127 holds carry128 at this point.
    b.cx(r.activity,r.flight);
    literal(b,&[(r.activity,false),(t[128],false),(q[127],false)],r.flight,dirty);
    b.ccx(r.activity,r.flight,r.sign);
    if conditional_mask{
        literal(b,&[(r.activity,false),(r.sign,false),(q[127],false)],t[128],dirty);
    }else{b.ccx(r.sign,q[127],t[128]);}
    for i in(first..128).rev(){
        let x=if i==first{r.work}else{q[i-1]};
        cell(b,q[i],t[i],x,true);
        b.cx(q[i],x);
        if conditional_mask{
            literal(b,&[(r.activity,false),(r.sign,false),(x,false)],t[i],dirty);
        }else{b.ccx(r.sign,x,t[i]);}
        b.cx(q[i],x);
    }
    b.ccx(r.activity,r.flight,r.sign);
    for &t in t{b.x(t);}
    b.end()
}

/// HR inverse uses the actual normalized leading ONE as conditional
/// carry, returning it exactly. The global-zero work then holds A*e;
/// the retained sign is a passenger throughout the complete arithmetic.
fn physical_inverse_record(b:&mut B,q:&[QubitId],t:&[QubitId],r:Roles,
    first:usize,dirty:&[QubitId])->Vec<G>{
    assert_eq!((q.len(),t.len()),(128,129));assert!(first<128);
    let carry=q[127];
    b.begin();b.x(carry);for &a in t{b.x(a);}
    for i in first..127{cell(b,q[i],t[i],if i==first{carry}else{q[i-1]},false);}
    // The omitted physical leading cell is a logical ONE. Its carry is
    // OR(t127,carry127), exposed temporarily on globally-zero work.
    let top=|b:&mut B|{b.cx(t[127],r.work);b.cx(q[126],r.work);
        b.ccx(t[127],q[126],r.work);};
    top(b);b.cx(r.activity,r.flight);
    literal(b,&[(r.activity,false),(t[128],false),(r.work,false)],r.flight,dirty);
    literal(b,&[(r.activity,false),(r.flight,false),(r.work,false)],t[128],dirty);
    top(b);b.ccx(r.activity,r.flight,r.work);
    // The leading sum bit is ONE XOR carry127.
    b.cx(r.work,t[127]);b.ccx(r.work,q[126],t[127]);
    for i in (first..127).rev(){
        let x=if i==first{carry}else{q[i-1]};cell(b,q[i],t[i],x,true);
        b.cx(q[i],x);b.ccx(r.work,x,t[i]);b.cx(q[i],x);
    }
    b.ccx(r.activity,r.flight,r.work);
    for &a in t{b.x(a);}b.x(carry);b.end()
}

fn permitted(ranges:Ranges,k:usize)->bool{
    ranges.z.0.saturating_add(ranges.y.0).max(226)<=257-k
}

fn selected_swap(b:&mut B,meta:&SumSize,r:Roles,k:usize,slot:QubitId,dirty:&[QubitId]){
    let g=Guard{y:(1,128),sum_limit:31-k as isize};
    g.xor(b,meta,r.work,&[(r.activity,false)],dirty);
    b.cswap(r.work,r.flight,slot);
    g.xor(b,meta,r.work,&[(r.activity,false)],dirty);
}

/// Replace the entire HT forward k-descending/band loop, after PRE
/// expansion and before the original sign read/reflection. A is the full
/// inherited HT activity; e/sign/work enter and leave zero globally.
/// The unchanged public skip matches direct_payload::digit exactly.
pub(crate) fn forward(b:&mut B,meta:&SumSize,q:&[QubitId],raw:&[QubitId],
    r:Roles,ranges:Ranges,dirty:&[QubitId]){
    let d=checked_bank(meta,q,raw,r,dirty);
    let frame=frame_record(b,meta,q,raw,false);b.play(&frame,false);
    for k in(0..30).rev(){
        if !permitted(ranges,k){continue;}
        let guard=Guard{y:(1,128),sum_limit:31-k as isize}
            .witness_record(b,meta,r.activity,r.flight,&d);
        b.play(&guard,false);
        // Normalization proves the omitted low source prefix exactly0
        // on the complete guard. Every target bit and full carry tail remains.
        let yhi=ranges.y.1.min((257-k).saturating_sub(ranges.z.0));
        assert!((1..=128).contains(&yhi));
        let arithmetic=restoring_record(b,q,&raw[k..k+129],r,false,128-yhi,&d);
        b.play(&arithmetic,false);b.play(&guard,true);
        // Raw P[Y+k] maps exactly to Pprime[128+k].
        selected_swap(b,meta,r,k,raw[128+k],&d);
    }
    b.play(&frame,true);
}

/// Replace the entire HR inverse k-ascending/band loop, after the original
/// sign read/reflection and before widening/sign erase. Sign is retained.
/// Entry e/work0; e is fetched only under S<=31-k. Arithmetic deliberately
/// retains the inherited one-unit wider S<=32-k condition, including k0.
pub(crate) fn inverse(b:&mut B,meta:&SumSize,q:&[QubitId],raw:&[QubitId],
    r:Roles,ranges:Ranges,dirty:&[QubitId]){
    let d=checked_bank(meta,q,raw,r,dirty);
    let frame=frame_record(b,meta,q,raw,true);b.play(&frame,false);
    for k in 0..30{
        if !permitted(ranges,k){continue;}
        // Raw P[257-Y-k] maps exactly to Pprime[129-k].
        selected_swap(b,meta,r,k,raw[129-k],&d);
        b.cx(r.sign,r.activity);
        let guard=Guard{y:(1,128),sum_limit:32-k as isize}
            .witness_record(b,meta,r.activity,r.flight,&d);
        b.play(&guard,false);
        let t:Vec<_>=(0..129).map(|i|raw[258-k-i]).collect();
        let yhi=ranges.y.1.min((258-k).saturating_sub(ranges.z.0));
        assert!((1..=128).contains(&yhi));
        let arithmetic=physical_inverse_record(b,q,&t,r,128-yhi,&d);
        b.play(&arithmetic,true);b.play(&guard,true);
        b.cx(r.sign,r.activity);
    }
    b.play(&frame,true);
}

// Integration is deliberately absent. In the shell retain HR forward
// and HT inverse unchanged; call these two APIs only in their named
// Q-source halves. Do not keep either coordinate through reflection,
// sign reads, P258 compression, a raw transition, V, or a phase reader.
