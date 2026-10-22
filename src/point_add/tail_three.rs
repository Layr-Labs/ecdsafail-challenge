//! Three-role switching tail. C + U7 are the only independent scratch
//! owners; PH supplies U7's eighth bit only on the unchanged C care.
//! Priority probes use output-basis transpositions, not a found helper.
use super::builder::B;
use super::frogdrop::direct_tail::TailPar;
use super::map_three::{bank,cover,record,swap,zero_transposition};
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn probe(b:&mut B,source:&[QubitId],limit:usize,cut:&[QubitId],cut_a:usize,
    out:&[QubitId],base:usize,c:QubitId,d:&[QubitId]){
    assert!(limit<=source.len()&&base<=1&&limit-base<1usize<<out.len());
    for lane in(0..limit).rev(){let value=lane+1-base;if value==0{continue;}
        let end=cut_a.saturating_sub(lane).min(1usize<<cut.len());
        for mut term in cover(cut,0,end){term.extend([(c,false),(source[lane],false)]);
            zero_transposition(b,out,value,&term,d);
        }
    }
}
pub(crate) fn apply(b:&mut B,ring:&[QubitId],q:&[QubitId],e:&[QubitId],
    scratch:&[QubitId],ph:QubitId,p:&TailPar,phase_already_moved:bool,dirty:&[QubitId]){
    assert_eq!((ring.len(),q.len(),e.len(),scratch.len()),(257,128,7,8));
    let c=scratch[0];let u:Vec<_>=scratch[1..8].iter().copied().chain([ph]).collect();
    let ports:Vec<_>=ring.iter().chain(q).chain(e).chain(scratch).copied().chain([ph]).collect();
    assert_eq!(ports.len(),ports.iter().collect::<BTreeSet<_>>().len());
    let all:Vec<_>=ports.iter().chain(dirty).copied().collect();let d=bank(&all,&[c]);
    if phase_already_moved{b.cx(c,ph);}
    let n=ring.len();let rev:Vec<_>=ring.iter().rev().copied().collect();
    let ylo=p.szlo.min(p.sylo).max(1);let umax=(p.l0+p.qb+1).min(n-ylo);
    assert!(umax<256&&p.swl_hi<=q.len()&&p.m<=128);
    let p1=record(b,|b|probe(b,ring,umax,e,n-1,&u,0,c,&d));b.play(&p1,false);
    let p2=record(b,|b|probe(b,&rev,p.l0,&u,n,e,1,c,&d));b.play(&p2,true);
    for l in 0..n/2{b.cswap(c,ring[l],ring[n-1-l]);}
    let lmin=(n-umax).min(p.swl_hi);
    for l in 0..lmin{b.cswap(c,ring[l],q[l]);}
    for l in(lmin..p.swl_hi).rev(){
        // Baseline retained tmp is exactly C & U <= n-l-1 at lane l.
        for mut term in cover(&u,0,n-l){term.push((c,false));swap(b,&term,ring[l],q[l],&d);}
    }
    let pm=record(b,|b|probe(b,ring,p.m,&u,n,e,1,c,&d));b.play(&pm,false);
    let pu=record(b,|b|probe(b,&rev,umax,e,n-1,&u,0,c,&d));b.play(&pu,true);
    b.cx(c,ph);
}
