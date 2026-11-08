//! SOURCE-ONLY shared Bottom comparator; not registered or executed.
//!
//! B_k = S < max(17,E-96)-k. The complete normalized Q source has its
//! actual leading ONE at Q127 on every original activity branch. Expose
//! H=[E>=112] there, then use E5/E6 as conditional metadata scratch.
//! All metadata/source cells return BEFORE any arithmetic/selected body.

use super::builder::{B,G};
use super::cross_four::Cross;
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn mc_price(n:usize)->usize{match n{0|1=>0,2=>1,_=>4*(n-2)}}
fn cover(mut lo:usize,hi:usize)->Vec<(usize,usize)>{
    assert!(lo<=hi&&hi<=32);let mut out=Vec::new();
    while lo<hi{
        let mut free=if lo==0{5}else{(lo.trailing_zeros()as usize).min(5)};
        while lo+(1usize<<free)>hi{free-=1;}
        out.push((lo,free));lo+=1usize<<free;
    }out
}
fn selected_terms(k:usize)->(bool,Vec<(usize,usize)>,usize){
    assert!(k<15);
    let p=cover(0,17-k);let n=cover(17-k,32);
    let price=|terms:&[(usize,usize)]|terms.iter()
        .map(|&(_,free)|mc_price(7-free)).sum::<usize>();
    let(pp,np)=(price(&p),price(&n));
    if pp<=np{(true,p,pp)}else{(false,n,np)}
}
fn constant_price(k:usize)->usize{
    let(mut left,mut bit,mut total)=(((32-k)%32)as isize,0usize,0usize);
    while left!=0&&bit<5{
        if left&1!=0{
            let digit=2-(left&3);
            total+=[0,0,0,1,5,13][5-bit];left-=digit;
        }
        left>>=1;bit+=1;
    }total
}
/// Includes BOTH appearances of the entire activity/flight witness.
pub(crate) fn arithmetic_price(k:usize)->usize{
    88+4*constant_price(k)+4*selected_terms(k).2
}
/// One complete A&Bottom XOR record; the selected caller uses it twice.
pub(crate) fn controller_price(k:usize)->usize{
    42+2*constant_price(k)+selected_terms(k).2
}

fn bank(c:&Cross<'_>,dirty:&[QubitId])->Vec<QubitId>{
    let r=c.roles;let mut ports=BTreeSet::new();
    assert_eq!((c.size.y.len(),c.size.sum.len(),c.q.len()),(7,5,128));
    assert!(c.size.y.iter().chain(&c.size.sum).copied()
        .chain([c.q[127],r.activity,r.flight,r.mask]).filter(|q|super::c659::retained(*q)).all(|q|ports.insert(q)));
    ports.extend([c.phase,r.x128]);ports.extend(c.clean_external.iter().copied());
    let d:Vec<_>=dirty.iter().copied().filter(|q|ports.insert(*q)).collect();
    assert!(d.len()>=5);d // largest low-class query has seven controls
}
fn literal(b:&mut B,controls:&[(QubitId,bool)],target:QubitId,d:&[QubitId]){
    assert!(!controls.iter().any(|p|p.0==target));
    mc_xor(b,controls,target,&[],d);
}

/// E6 ^= [E.low4==0] on H. E5 is zero only on H and is returned.
/// For arithmetic, m is globally zero and returned before becoming the
/// comparison output (five CCX). For controller, m is the eventual output
/// and is deliberately absent from this entire prep (six CCX).
fn clamp_zero(b:&mut B,c:&Cross<'_>,controller:bool,d:&[QubitId]){
    let e=&c.size.y;let m=c.roles.mask;
    for &q in &e[..4]{b.x(q);}
    b.ccx(e[3],e[2],e[5]);
    if controller{
        literal(b,&[(e[5],false),(e[1],false),(e[0],false)],e[6],d);
    }else{
        b.ccx(e[5],e[1],m);b.ccx(m,e[0],e[6]);b.ccx(e[5],e[1],m);
    }
    b.ccx(e[3],e[2],e[5]);
    for &q in &e[..4]{b.x(q);}
}

/// On original activity: Q127 becomes H, E6 stores the zero-low4 flag,
/// and E.low5 becomes max(17,16+u)-k for H1, u=original E.low4.
/// This value is3..31, so the five-bit subtraction cannot wrap on H.
/// The comparison output is [S < that value] on H. Off H the prep is an
/// arbitrary reversible completion and its result is ignored centrally.
fn prepare(b:&mut B,c:&Cross<'_>,k:usize,controller:bool,d:&[QubitId])->Vec<G>{
    assert!(k<15);let e=&c.size.y;let s=&c.size.sum;
    let cmp=if controller{e[5]}else{c.roles.mask};
    b.begin();
    b.x(c.q[127]);
    literal(b,&[(e[4],false),(e[5],false),(e[6],false)],c.q[127],d);
    b.x(e[5]);b.x(e[6]);
    clamp_zero(b,c,controller,d);
    b.cx(e[6],e[0]);
    super::frogdrop::add_const_dirty_exact(b,&e[..5],(32-k)%32,d);
    for &q in s{b.x(q);}
    super::arith::ttk_carry_u(b,s,&e[..5],cmp,d[0]);
    for &q in s{b.x(q);}
    b.end()
}

/// XOR ctl&Bottom or ctl&!Bottom, whichever caller requests. All reads
/// are independent of ctl/target; every high-class term retains H and
/// every low-class term retains !H. No off-H clean-helper claim is used.
fn xor_gate(b:&mut B,c:&Cross<'_>,k:usize,ctl:QubitId,target:QubitId,
    cmp:QubitId,want_positive:bool,d:&[QubitId]){
    let(positive,terms,_)=selected_terms(k);
    if positive!=want_positive{b.cx(ctl,target);}
    for(base,free)in terms{
        let mut controls=vec![(ctl,false),(c.q[127],true)];
        controls.extend((free..5).map(|i|(c.size.sum[i],base>>i&1==0)));
        literal(b,&controls,target,d);
    }
    literal(b,&[(ctl,false),(c.q[127],false),(cmp,!positive)],target,d);
}

/// Input m0 and e0 on forward entry; the exact inverse has its inherited
/// quotient/witness image. Q127 is ONE on A or on the skipped e witness.
/// Full metadata/source and m return, while A/e get the same two-transfer
/// activity compression as the existing Bottom witness.
pub(crate) fn witness_record(b:&mut B,c:&Cross<'_>,k:usize,dirty:&[QubitId])->Vec<G>{
    let d=bank(c,dirty);let r=c.roles;let prep=prepare(b,c,k,false,&d);
    b.begin();b.play(&prep,false);
    xor_gate(b,c,k,r.activity,r.flight,r.mask,false,&d);
    xor_gate(b,c,k,r.flight,r.activity,r.mask,false,&d);
    b.play(&prep,true);b.end()
}

/// XOR A&Bottom into the caller's mask. The prep does not use that mask
/// as a source, target, cache or donor, so its inverse remains exact when
/// the mask changes. E5 is the conditional comparison output, not m.
pub(crate) fn gate_record(b:&mut B,c:&Cross<'_>,k:usize,dirty:&[QubitId])->Vec<G>{
    let d=bank(c,dirty);let prep=prepare(b,c,k,true,&d);
    b.begin();b.play(&prep,false);
    xor_gate(b,c,k,c.roles.activity,c.roles.mask,c.size.y[5],true,&d);
    b.play(&prep,true);b.end()
}

// Three-role PH controller overloads; original bodies above remain byte-preserved.
fn bank3(c:&super::k5_ph_ports::Context<'_>,dirty:&[QubitId])->Vec<QubitId>{
    let r=c.roles;let mut ports=BTreeSet::new();
    assert_eq!((c.size.y.len(),c.size.sum.len(),c.q.len()),(7,5,128));
    assert!(c.size.y.iter().chain(&c.size.sum).copied()
        .chain([c.q[127],r.activity,r.flight,r.mask]).filter(|q|super::c659::retained(*q)).all(|q|ports.insert(q)));
    ports.extend([c.ph]);ports.extend(c.excluded.iter().copied());ports.extend(c.clean_external.iter().copied());
    let d:Vec<_>=dirty.iter().copied().filter(|q|ports.insert(*q)).collect();
    assert!(d.len()>=5);d // largest low-class query has seven controls
}
/// E6 ^= [E.low4==0] on H. E5 is zero only on H and is returned.
/// For arithmetic, m is globally zero and returned before becoming the
/// comparison output (five CCX). For controller, m is the eventual output
/// and is deliberately absent from this entire prep (six CCX).
fn clamp_zero3(b:&mut B,c:&super::k5_ph_ports::Context<'_>,controller:bool,d:&[QubitId]){
    let e=&c.size.y;let m=c.roles.mask;
    for &q in &e[..4]{b.x(q);}
    b.ccx(e[3],e[2],e[5]);
    if controller{
        literal(b,&[(e[5],false),(e[1],false),(e[0],false)],e[6],d);
    }else{
        b.ccx(e[5],e[1],m);b.ccx(m,e[0],e[6]);b.ccx(e[5],e[1],m);
    }
    b.ccx(e[3],e[2],e[5]);
    for &q in &e[..4]{b.x(q);}
}

/// On original activity: Q127 becomes H, E6 stores the zero-low4 flag,
/// and E.low5 becomes max(17,16+u)-k for H1, u=original E.low4.
/// This value is3..31, so the five-bit subtraction cannot wrap on H.
/// The comparison output is [S < that value] on H. Off H the prep is an
/// arbitrary reversible completion and its result is ignored centrally.
fn prepare3(b:&mut B,c:&super::k5_ph_ports::Context<'_>,k:usize,controller:bool,d:&[QubitId])->Vec<G>{
    assert!(k<15);let e=&c.size.y;let s=&c.size.sum;
    let cmp=if controller{e[5]}else{c.roles.mask};
    b.begin();
    b.x(c.q[127]);
    literal(b,&[(e[4],false),(e[5],false),(e[6],false)],c.q[127],d);
    b.x(e[5]);b.x(e[6]);
    clamp_zero3(b,c,controller,d);
    b.cx(e[6],e[0]);
    super::frogdrop::add_const_dirty_exact(b,&e[..5],(32-k)%32,d);
    for &q in s{b.x(q);}
    super::arith::ttk_carry_u(b,s,&e[..5],cmp,d[0]);
    for &q in s{b.x(q);}
    b.end()
}

/// XOR ctl&Bottom or ctl&!Bottom, whichever caller requests. All reads
/// are independent of ctl/target; every high-class term retains H and
/// every low-class term retains !H. No off-H clean-helper claim is used.
fn xor_gate3(b:&mut B,c:&super::k5_ph_ports::Context<'_>,k:usize,ctl:QubitId,target:QubitId,
    cmp:QubitId,want_positive:bool,d:&[QubitId]){
    let(positive,terms,_)=selected_terms(k);
    if positive!=want_positive{b.cx(ctl,target);}
    for(base,free)in terms{
        let mut controls=vec![(ctl,false),(c.q[127],true)];
        controls.extend((free..5).map(|i|(c.size.sum[i],base>>i&1==0)));
        literal(b,&controls,target,d);
    }
    literal(b,&[(ctl,false),(c.q[127],false),(cmp,!positive)],target,d);
}

/// Input m0 and e0 on forward entry; the exact inverse has its inherited
/// quotient/witness image. Q127 is ONE on A or on the skipped e witness.
/// Full metadata/source and m return, while A/e get the same two-transfer
/// activity compression as the existing Bottom witness.
pub(crate) fn witness_record3(b:&mut B,c:&super::k5_ph_ports::Context<'_>,k:usize,dirty:&[QubitId])->Vec<G>{
    let d=bank3(c,dirty);let r=c.roles;let prep=prepare3(b,c,k,false,&d);
    b.begin();b.play(&prep,false);
    xor_gate3(b,c,k,r.activity,r.flight,r.mask,false,&d);
    xor_gate3(b,c,k,r.flight,r.activity,r.mask,false,&d);
    b.play(&prep,true);b.end()
}

/// Experimental held-prep probe; the caller must check the source invariant.
pub(crate) fn held_prep_record3(b:&mut B,c:&super::k5_ph_ports::Context<'_>,k:usize,dirty:&[QubitId])->Vec<G>{
    let d=bank3(c,dirty);prepare3(b,c,k,true,&d)
}

/// FP3 uses the controller form only in short gate groups, never across a
/// prefix sweep. The returned inverse restores Q127 and every E lane.
pub(crate) fn fp3_prep_record3(b:&mut B,c:&super::k5_ph_ports::Context<'_>,k:usize,dirty:&[QubitId])->Vec<G>{
    let d=bank3(c,dirty);prepare3(b,c,k,true,&d)
}

/// FP3 multi-literal Bottom query while fp3_prep_record3 is live. Donors
/// are filtered against every control and target before mcx_dirty.
pub(crate) fn fp3_xor_gate3_multi(b:&mut B,c:&super::k5_ph_ports::Context<'_>,k:usize,
    ctl:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    assert!(!ctl.is_empty());let(positive,terms,_)=selected_terms(k);
    let mut used=BTreeSet::new();
    let emit=|b:&mut B,controls:&[(QubitId,bool)]|{
        assert!(!controls.iter().any(|x|x.0==target));
        let mut seen=BTreeSet::new();
        let donors:Vec<_>=dirty.iter().copied().filter(|q|*q!=target
            &&!controls.iter().any(|x|x.0==*q)&&seen.insert(*q)).collect();
        assert!(donors.len()>=controls.len().saturating_sub(2));
        mc_xor(b,controls,target,&[],&donors);
    };
    for &(q,_) in ctl {assert!(used.insert(q));}
    if !positive{emit(b,ctl);}
    for(base,free)in terms{
        let mut controls=ctl.to_vec();controls.push((c.q[127],true));
        controls.extend((free..5).map(|i|(c.size.sum[i],base>>i&1==0)));
        emit(b,&controls);
    }
    let mut controls=ctl.to_vec();controls.extend([(c.q[127],false),(c.size.y[5],!positive)]);
    emit(b,&controls);
}

/// Bottom witness with the comparison held in E5, leaving pool[2] idle.
/// On entry m=0 and (A or e)=>Q127; the returned prep is exact on all wires.
pub(crate) fn witness_record3_e5(b:&mut B,c:&super::k5_ph_ports::Context<'_>,k:usize,dirty:&[QubitId])->Vec<G>{
    let d=bank3(c,dirty);let r=c.roles;let prep=prepare3(b,c,k,true,&d);
    b.begin();b.play(&prep,false);
    xor_gate3(b,c,k,r.activity,r.flight,c.size.y[5],false,&d);
    xor_gate3(b,c,k,r.flight,r.activity,c.size.y[5],false,&d);
    b.play(&prep,true);b.end()
}

/// XOR A&Bottom into the caller's mask. The prep does not use that mask
/// as a source, target, cache or donor, so its inverse remains exact when
/// the mask changes. E5 is the conditional comparison output, not m.
pub(crate) fn gate_record3(b:&mut B,c:&super::k5_ph_ports::Context<'_>,k:usize,dirty:&[QubitId])->Vec<G>{
    let d=bank3(c,dirty);let prep=prepare3(b,c,k,true,&d);
    b.begin();b.play(&prep,false);
    xor_gate3(b,c,k,c.roles.activity,c.roles.mask,c.size.y[5],true,&d);
    b.play(&prep,true);b.end()
}


/// Bottom prep3 is a returned conjugation; its comparison result lives in E5.
/// Distribute A, the caller's extra controls, and each comparison term to
/// the target without writing the three-role mask.
pub(crate) fn folded_gate_xor3(b:&mut B,c:&super::k5_ph_ports::Context<'_>,k:usize,
    target:QubitId,extra:&[(QubitId,bool)],dirty:&[QubitId]){
    let mut d=bank3(c,dirty);
    d.retain(|q|*q!=target&&!extra.iter().any(|x|x.0==*q));
    let prep=prepare3(b,c,k,true,&d);
    b.play(&prep,false);
    let(positive,terms,_)=selected_terms(k);
    if !positive{let mut ctl=vec![(c.roles.activity,false)];ctl.extend_from_slice(extra);
        mc_xor(b,&ctl,target,&[],&d);}
    for(base,free)in terms{
        let mut ctl=vec![(c.roles.activity,false),(c.q[127],true)];
        ctl.extend((free..5).map(|i|(c.size.sum[i],base>>i&1==0)));
        ctl.extend_from_slice(extra);mc_xor(b,&ctl,target,&[],&d);
    }
    let mut ctl=vec![(c.roles.activity,false),(c.q[127],false),(c.size.y[5],!positive)];
    ctl.extend_from_slice(extra);mc_xor(b,&ctl,target,&[],&d);
    b.play(&prep,true);
}
