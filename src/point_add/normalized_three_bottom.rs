//! Three-owner Bottom comparator, borrowing only returned metadata.
//!
//! B_k = S < max(17,E-96)-k. The complete normalized Q source has its
//! actual leading ONE at Q127 on every original activity branch. Expose
//! H=[E>=112] there, then use E5/E6 as conditional metadata scratch.
//! All metadata/source cells return BEFORE any arithmetic/selected body.

use super::builder::{B,G};
use super::cross_three::Cross;
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
    92+4*constant_price(k)+4*selected_terms(k).2
}
/// One complete A&Bottom XOR record; the selected caller uses it twice.
pub(crate) fn controller_price(k:usize)->usize{
    42+2*constant_price(k)+selected_terms(k).2
}

fn bank(c:&Cross<'_>,dirty:&[QubitId],extra:&[QubitId])->Vec<QubitId>{
    let r=c.roles;let mut ports=BTreeSet::new();
    assert_eq!((c.size.y.len(),c.size.sum.len(),c.q.len()),(7,5,128));
    assert!(c.size.y.iter().chain(&c.size.sum).copied()
        .chain([c.q[127],r.activity,r.flight,r.work,c.phase]).all(|q|ports.insert(q)));
    ports.extend(c.clean_external.iter().copied());ports.extend(extra.iter().copied());
    let d:Vec<_>=dirty.iter().copied().filter(|q|ports.insert(*q)).collect();
    assert!(d.len()>=6);d
}
fn literal(b:&mut B,controls:&[(QubitId,bool)],target:QubitId,d:&[QubitId]){
    super::three_control::literal(b,controls,target,d);
}

/// All prep uses E5, never a fourth scalar. The E4..6 high class
/// guarantees E5/E6 are conditional zero; off that class the central
/// predicate ignores this reversible completion.
fn prepare(b:&mut B,c:&Cross<'_>,k:usize,d:&[QubitId])->Vec<G>{
    assert!(k<15);let e=&c.size.y;let s=&c.size.sum;
    b.begin();b.x(c.q[127]);
    literal(b,&[(e[4],false),(e[5],false),(e[6],false)],c.q[127],d);
    b.x(e[5]);b.x(e[6]);
    for &q in &e[..4]{b.x(q);}
    b.ccx(e[3],e[2],e[5]);
    literal(b,&[(e[5],false),(e[1],false),(e[0],false)],e[6],d);
    b.ccx(e[3],e[2],e[5]);
    for &q in &e[..4]{b.x(q);}
    b.cx(e[6],e[0]);
    super::frogdrop::add_const_dirty_exact(b,&e[..5],(32-k)%32,d);
    for &q in s{b.x(q);}
    super::arith::ttk_carry_u(b,s,&e[..5],e[5],d[0]);
    for &q in s{b.x(q);}
    b.end()
}

fn xor_prepared(b:&mut B,c:&Cross<'_>,k:usize,controls:&[(QubitId,bool)],
    target:QubitId,want_positive:bool,d:&[QubitId]){
    let(positive,terms,_)=selected_terms(k);
    if positive!=want_positive{literal(b,controls,target,d);}
    for(base,free)in terms{
        let mut t=controls.to_vec();t.push((c.q[127],true));
        t.extend((free..5).map(|i|(c.size.sum[i],base>>i&1==0)));
        literal(b,&t,target,d);
    }
    let mut t=controls.to_vec();t.extend([(c.q[127],false),(c.size.y[5],!positive)]);
    literal(b,&t,target,d);
}

/// Exactly the parent's two-transfer activity compression. On its forward
/// e0 entry and inverse image Q127 is ONE on either A or skipped flight.
/// No metadata or source cell remains borrowed at the arithmetic boundary.
pub(crate) fn witness_record(b:&mut B,c:&Cross<'_>,k:usize,dirty:&[QubitId])->Vec<G>{
    let d=bank(c,dirty,&[]);let r=c.roles;let prep=prepare(b,c,k,&d);
    b.begin();b.play(&prep,false);
    xor_prepared(b,c,k,&[(r.activity,false)],r.flight,false,&d);
    xor_prepared(b,c,k,&[(r.flight,false)],r.activity,false,&d);
    b.play(&prep,true);b.end()
}

/// XOR A*Bottom*extra into target. Extra is data only, not metadata:
/// this prep temporarily changes E/S and the actual source-leading cell.
pub(crate) fn xor_gate(b:&mut B,c:&Cross<'_>,k:usize,extra:&[(QubitId,bool)],
    target:QubitId,dirty:&[QubitId]){
    assert!(extra.iter().all(|p|!c.size.y.contains(&p.0)&&!c.size.sum.contains(&p.0)
        &&p.0!=c.q[127]));
    let mut excluded:Vec<_>=extra.iter().map(|p|p.0).collect();excluded.push(target);
    let d=bank(c,dirty,&excluded);let prep=prepare(b,c,k,&d);
    let mut controls=vec![(c.roles.activity,false)];controls.extend_from_slice(extra);
    b.play(&prep,false);xor_prepared(b,c,k,&controls,target,true,&d);b.play(&prep,true);
}
