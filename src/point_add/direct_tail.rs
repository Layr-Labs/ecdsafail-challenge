//! Source-only direct Y-1 switching tail; intended frogdrop child module.
//! No codec, virtual Q, new owner, or width cut. Entry scratch is C+U7+tmp.
use super::super::builder::{B,G};
use super::super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

// A donor universe may include other operands. Borrow only across one
// complete primitive and exclude that primitive's live ports before use.
fn bank(universe:&[QubitId],held:&[QubitId])->Vec<QubitId>{
    let mut seen=BTreeSet::new();universe.iter().copied()
        .filter(|q|!held.contains(q)&&seen.insert(*q)).collect()
}
fn xor(b:&mut B,c:&[(QubitId,bool)],t:QubitId,pre:&[QubitId],universe:&[QubitId]){
    let held:Vec<_>=c.iter().map(|x|x.0).chain([t]).chain(pre.iter().copied()).collect();
    let d=bank(universe,&held);assert!(d.len()>=c.len().saturating_sub(2));
    mc_xor(b,c,t,pre,&d);
}

fn record(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}

/// XOR C & (lo<=word<hi). The dyadic cubes are disjoint, including on
/// arbitrary off-C data; no clean prefix or cut flag is required.
fn range(b:&mut B,word:&[QubitId],mut lo:usize,hi:usize,c:QubitId,
    target:QubitId,dirty:&[QubitId]) {
    assert!(lo<=hi && hi<=1usize<<word.len());
    while lo<hi {
        let aligned=if lo==0 {word.len()}else{lo.trailing_zeros() as usize};
        let remaining=(usize::BITS-1-(hi-lo).leading_zeros()) as usize;
        let free=aligned.min(remaining).min(word.len());
        let mut ctl=vec![(c,false)];
        ctl.extend((free..word.len()).map(|i|(word[i],lo>>i&1==0)));
        xor(b,&ctl,target,&[],dirty);
        lo+=1usize<<free;
    }
}

/// Priority probe under C and lane<cut_a-value(cut). Output is size-base,
/// where base=0 gives raw size, base=1 gives positive size-minus1. Only tmp
/// is globally clean; out may be arbitrary on C=0 shots. Every source and
/// cut is unchanged, and each complete input/output predicate returns tmp.
fn probe(b:&mut B,source:&[QubitId],limit:usize,cut:&[QubitId],cut_a:usize,
    out:&[QubitId],base:usize,c:QubitId,tmp:QubitId,dirty:&[QubitId]){
    assert!(limit<=source.len() && base<=1 && limit-base<1usize<<out.len());
    b.x(tmp);b.cx(c,tmp); // !C is a held found bit for the whole inactive branch
    for lane in(0..limit).rev(){
        let value=lane+1-base;if value==0{continue;}
        let pivot=value.trailing_zeros()as usize;
        let end=cut_a.saturating_sub(lane).min(1usize<<cut.len());
        b.x(tmp);
        let mut at=0usize;
        while at<end{
            let aligned=if at==0{cut.len()}else{at.trailing_zeros()as usize};
            let remaining=(usize::BITS-1-(end-at).leading_zeros())as usize;
            let free=aligned.min(remaining).min(cut.len());
            let mut ctl=vec![(tmp,false),(source[lane],false)];
            ctl.extend((free..cut.len()).map(|i|(cut[i],at>>i&1==0)));
            xor(b,&ctl,out[pivot],&[],dirty);at+=1usize<<free;
        }
        for(i,&q)in out.iter().enumerate(){if i!=pivot && value>>i&1!=0{b.ccx(tmp,out[pivot],q);}}
        b.x(tmp);
        let mut ctl=vec![(c,false)];
        ctl.extend(out.iter().enumerate().map(|(i,&q)|(q,value>>i&1==0)));
        xor(b,&ctl,tmp,&[],dirty);
    }
    b.x(tmp);let mut ctl=vec![(c,false)];ctl.extend(out.iter().map(|&q|(q,true)));
    xor(b,&ctl,tmp,&[],dirty);
}

/// Original public tail bounds, copied without narrowing by the caller.
pub(crate) struct TailPar{
    pub l0:usize,pub qb:usize,pub szlo:usize,pub sylo:usize,
    pub swl_hi:usize,pub m:usize,
}
/// Entry E=bl(top)-1 in seven bits; C=W|delayedD is scratch[0].
/// On C, original HR phase is zero, or has already been changed to one when
/// `phase_already_moved`. scratch[1..9] are globally zero, Q remains full raw.
/// Output tagged E=bl(bottom t_j)-1 and C retained; phase is HT on C.
/// Every off-C datum, including arbitrary PH used as U[7], returns unchanged.
#[allow(clippy::too_many_arguments)]
pub(crate) fn apply(b:&mut B,ring:&[QubitId],q:&[QubitId],e:&[QubitId],
    scratch:&[QubitId],ph:QubitId,par:&TailPar,phase_already_moved:bool,dirty:&[QubitId]){
    assert_eq!(ring.len(),257);assert_eq!(q.len(),128);assert_eq!(e.len(),7);assert_eq!(scratch.len(),9);
    let c=scratch[0];let tmp=scratch[8];
    let u:Vec<_>=scratch[1..8].iter().copied().chain([ph]).collect();
    let ports:Vec<_>=ring.iter().chain(q).chain(e).chain(scratch).copied().chain([ph]).collect();
    assert_eq!(ports.len(),ports.iter().collect::<BTreeSet<_>>().len());
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=ring.iter().chain(q).chain(e).chain(&scratch[1..]).chain([ph].iter()).chain(dirty).copied()
        .filter(|v|*v!=c&&seen.insert(*v)).collect();
    if phase_already_moved{b.cx(c,ph);} // now U is zero on C, arbitrary only off C
    let n=ring.len();let rev:Vec<_>=ring.iter().rev().copied().collect();
    let ylo=par.szlo.min(par.sylo).max(1);let umax=(par.l0+par.qb+1).min(n-ylo);
    assert!(umax<256 && par.swl_hi<=q.len() && par.m<=128);
    let p1=record(b,|b|probe(b,ring,umax,e,n-1,&u,0,c,tmp,&bank));b.play(&p1,false);
    let p2=record(b,|b|probe(b,&rev,par.l0,&u,n,e,1,c,tmp,&bank));b.play(&p2,true);
    for l in 0..n/2{b.cswap(c,ring[l],ring[n-1-l]);}
    let lmin=(n-umax).min(par.swl_hi);
    for l in 0..lmin{b.cswap(c,ring[l],q[l]);}
    if lmin<par.swl_hi{
        range(b,&u,0,n-par.swl_hi+1,c,tmp,&bank);
        for l in(lmin..par.swl_hi).rev(){
            b.cswap(tmp,ring[l],q[l]);if l>lmin{range(b,&u,n-l,n-l+1,c,tmp,&bank);}
        }
        range(b,&u,0,n-lmin,c,tmp,&bank);
    }
    let pm=record(b,|b|probe(b,ring,par.m,&u,n,e,1,c,tmp,&bank));b.play(&pm,false);
    let pu=record(b,|b|probe(b,&rev,umax,e,n-1,&u,0,c,tmp,&bank));b.play(&pu,true);
    b.cx(c,ph); // original phase transition, or restore the already-moved HT phase
}
