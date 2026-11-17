//! All-pattern found-bit-free K1 switching tail. No optional fanout selector.
use super::*;

fn probe3(b:&mut B,source:&[QubitId],limit:usize,cut:&[QubitId],cut_a:usize,
    out:&[QubitId],base:usize,c:QubitId,dirty:&[QubitId]) {
    assert!(limit<=source.len()&&base<=1&&limit-base<1usize<<out.len());
    for lane in (0..limit).rev() {
        let value=lane+1-base;if value==0 {continue;}
        let pivot=value.trailing_zeros()as usize;
        let end=cut_a.saturating_sub(lane).min(1usize<<cut.len());
        let mut at=0;
        while at<end {
            let free=(if at==0{cut.len()}else{at.trailing_zeros()as usize})
                .min((usize::BITS-1-(end-at).leading_zeros())as usize).min(cut.len());
            let mut ctl=vec![(c,false),(source[lane],false)];
            ctl.extend((free..cut.len()).map(|i|(cut[i],at>>i&1==0)));
            ctl.extend(out.iter().enumerate().filter(|(i,_)|*i!=pivot).map(|(_,&q)|(q,true)));
            xor(b,&ctl,out[pivot],&[],dirty);at+=1usize<<free;
        }
        let mut pattern=1usize<<pivot;
        for(i,&target)in out.iter().enumerate() {
            if i==pivot||value>>i&1==0 {continue;}
            let ctl:Vec<_>=std::iter::once((c,false)).chain(out.iter().enumerate()
                .filter(|(j,_)|*j!=i).map(|(j,&q)|(q,pattern>>j&1==0))).collect();
            xor(b,&ctl,target,&[],dirty);pattern|=1usize<<i;
        }
    }
}

pub(crate) fn apply3(b:&mut B,ring:&[QubitId],q:&[QubitId],e:&[QubitId],
    scratch:&[QubitId],ph:QubitId,par:&TailPar,phase_already_moved:bool,dirty:&[QubitId]) {
    assert_eq!((ring.len(),q.len(),e.len(),scratch.len()),(257,128,7,8));
    let c=scratch[0];let u:Vec<_>=scratch[1..].iter().copied().chain([ph]).collect();
    let ports:Vec<_>=ring.iter().chain(q).chain(e).chain(scratch).copied().chain([ph]).collect();
    assert_eq!(ports.len(),ports.iter().collect::<BTreeSet<_>>().len());
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=ring.iter().chain(q).chain(e).chain(&scratch[1..]).chain([ph].iter()).chain(dirty).copied()
        .filter(|v|*v!=c&&seen.insert(*v)).collect();
    if phase_already_moved {b.cx(c,ph);}
    let n=ring.len();let rev:Vec<_>=ring.iter().rev().copied().collect();
    let ylo=par.szlo.min(par.sylo).max(1);let umax=(par.l0+par.qb+1).min(n-ylo);
    assert!(umax<256&&par.swl_hi<=q.len()&&par.m<=128);
    let p1=record(b,|b|probe3(b,ring,umax,e,n-1,&u,0,c,&bank));b.play(&p1,false);
    let p2=record(b,|b|probe3(b,&rev,par.l0,&u,n,e,1,c,&bank));b.play(&p2,true);
    for l in 0..n/2 {b.cswap(c,ring[l],ring[n-1-l]);}
    let lmin=(n-umax).min(par.swl_hi);
    for l in 0..lmin {b.cswap(c,ring[l],q[l]);}
    if lmin<par.swl_hi {
        let flag=e[0];range(b,&u,0,n-par.swl_hi+1,c,flag,&bank);
        for l in (lmin..par.swl_hi).rev() {
            let(a,z)=(ring[l],q[l]);b.cx(a,z);
            #[cfg(test)]
            if MISSING_C.with(|v|v.get()) {xor(b,&[(flag,false),(z,false)],a,&[],&bank);}
            else {xor(b,&[(c,false),(flag,false),(z,false)],a,&[],&bank);}
            #[cfg(not(test))]
            xor(b,&[(c,false),(flag,false),(z,false)],a,&[],&bank);
            b.cx(a,z);
            if l>lmin {range(b,&u,n-l,n-l+1,c,flag,&bank);}
        }
        range(b,&u,0,n-lmin,c,flag,&bank);
    }
    let pm=record(b,|b|probe3(b,ring,par.m,&u,n,e,1,c,&bank));b.play(&pm,false);
    let pu=record(b,|b|probe3(b,&rev,umax,e,n-1,&u,0,c,&bank));b.play(&pu,true);
    b.cx(c,ph);
}

#[cfg(test)]
thread_local! {static MISSING_C:std::cell::Cell<bool>=const{std::cell::Cell::new(false)};}
#[cfg(test)]
pub(crate) fn with_missing_c<R>(body:impl FnOnce()->R)->R {
    MISSING_C.with(|c|assert!(!c.replace(true)));
    struct Reset;impl Drop for Reset{fn drop(&mut self){MISSING_C.with(|c|c.set(false));}}
    let _reset=Reset;body()
}
