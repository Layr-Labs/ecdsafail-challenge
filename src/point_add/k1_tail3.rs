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
    let ports:Vec<_>=ring.iter().chain(q).chain(e).chain(scratch).copied().chain([ph]).filter(|q|super::super::super::c659::retained(*q)).collect();
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


// TAIL-7S code (tag,cut,PH): !C PH0/1 = 000/001;
// C u[7:5] = 0,1,2,3,4 -> 100,110,101,111,010.
// The unused code 011 is outside the inherited tail support.
const CODE:[usize;5]=[4,6,5,7,2];
fn price(k:usize)->usize {if k<=1{0}else if k==2{1}else{4*(k-2)}}
fn split_code(ctl:&[(QubitId,bool)],c:QubitId,u:&[QubitId])
    ->(Vec<(QubitId,bool)>,[Option<bool>;3]){
    let mut rest=Vec::new();let mut hi=[None;3];let mut saw_c=false;
    for &(q,neg) in ctl {
        if q==c {assert!(!neg&&!saw_c);saw_c=true;}
        else if q==u[5] {assert!(hi[0].replace(!neg).is_none());}
        else if q==u[6] {assert!(hi[1].replace(!neg).is_none());}
        else if q==u[7] {assert!(hi[2].replace(!neg).is_none());}
        else {rest.push((q,neg));}
    }
    assert!(saw_c);(rest,hi)
}
fn high_mask(hi:[Option<bool>;3])->usize {
    (0..5).filter(|&h|(0..3).all(|i|hi[i].is_none_or(|v|v==((h>>i)&1!=0))))
        .fold(0,|a,h|a|(1<<h))
}
fn code_cubes(mask:usize,other:usize)->Vec<Vec<(usize,bool)>> {
    if mask==0{return vec![];}
    let mut candidates=Vec::new();
    for pattern in 0..27 {
        let mut t=pattern;let mut literals=Vec::new();
        for bit in 0..3 {
            let choice=t%3;t/=3;
            if choice!=0 {literals.push((bit,choice==1));}
        }
        let matches=|code:usize|literals.iter().all(|&(bit,neg)|((code>>(2-bit))&1!=0)!=neg);
        if matches(0)||matches(1){continue;}
        let hits=(0..5).filter(|&i|matches(CODE[i])).fold(0,|a,i|a|(1<<i));
        if hits!=0&&hits&!mask==0 {candidates.push((hits,literals));}
    }
    let mut cost=[usize::MAX;32];let mut path=[None;32];cost[0]=0;
    for state in 0..32 {
        if cost[state]==usize::MAX||state&!mask!=0{continue;}
        for(j,(hit,lits))in candidates.iter().enumerate(){
            if state&hit!=0{continue;}
            let next=state|hit;let value=cost[state]+price(other+lits.len());
            if value<cost[next] {cost[next]=value;path[next]=Some((state,j));}
        }
    }
    assert!(cost[mask]!=usize::MAX);
    let mut out=Vec::new();let mut at=mask;
    while at!=0 {let(prev,j)=path[at].unwrap();out.push(candidates[j].1.clone());at=prev;}
    out
}
fn encoded_xor(b:&mut B,ctl:&[(QubitId,bool)],target:QubitId,c:QubitId,u:&[QubitId],dirty:&[QubitId]) {
    let(mut rest,hi)=split_code(ctl,c,u);
    let(tag,cut,ph)=(c,u[5],u[7]);
    if target==u[5] { // u5 toggles on both u6 strata; u7 cannot coexist.
        if hi[2]==Some(true){return;}
        rest.push((tag,false));if let Some(v)=hi[1]{rest.push((ph,!v));}
        xor(b,&rest,cut,&[],dirty);return;
    }
    if target==u[6] { // u6 toggles on both u5 strata.
        if hi[2]==Some(true){return;}
        rest.push((tag,false));if let Some(v)=hi[0]{rest.push((cut,!v));}
        xor(b,&rest,ph,&[],dirty);return;
    }
    if target==u[7] { // u7 is the isolated 100 <-> 010 swap.
        if hi[0]==Some(true)||hi[1]==Some(true){return;}
        rest.push((ph,true));
        let mut first=rest.clone();first.push((tag,false));xor(b,&first,cut,&[],dirty);
        let mut second=rest.clone();second.push((cut,false));xor(b,&second,tag,&[],dirty);
        xor(b,&first,cut,&[],dirty);return;
    }
    let mask=high_mask(hi);let code=[tag,cut,ph];
    for cube in code_cubes(mask,rest.len()) {
        let mut controls=rest.clone();controls.extend(cube.into_iter().map(|(bit,neg)|(code[bit],neg)));
        xor(b,&controls,target,&[],dirty);
    }
}
#[cfg(test)]
pub(crate) fn fixture_encoded_xor(b:&mut B,ctl:&[(QubitId,bool)],target:QubitId,
    c:QubitId,u:&[QubitId],dirty:&[QubitId]) {
    encoded_xor(b,ctl,target,c,u,dirty);
}
fn swap_c7(b:&mut B,c:QubitId,u:&[QubitId],a:QubitId,z:QubitId,dirty:&[QubitId]) {
    b.cswap(c,a,z);
    b.cx(a,z);
    xor(b,&[(c,true),(u[5],false),(z,false)],a,&[],dirty);
    b.cx(a,z);
}
fn range7(b:&mut B,word:&[QubitId],mut lo:usize,hi:usize,c:QubitId,
    target:QubitId,dirty:&[QubitId]) {
    assert_eq!(word.len(),8);assert!(lo<=hi&&hi<=256);
    while lo<hi {
        let aligned=if lo==0{word.len()}else{lo.trailing_zeros()as usize};
        let remaining=(usize::BITS-1-(hi-lo).leading_zeros())as usize;
        let free=aligned.min(remaining).min(word.len());
        let mut ctl=vec![(c,false)];
        ctl.extend((free..word.len()).map(|i|(word[i],lo>>i&1==0)));
        encoded_xor(b,&ctl,target,c,word,dirty);lo+=1usize<<free;
    }
}
fn probe7(b:&mut B,source:&[QubitId],limit:usize,cut:&[QubitId],cut_a:usize,
    out:&[QubitId],base:usize,c:QubitId,u:&[QubitId],dirty:&[QubitId]) {
    assert!(limit<=source.len()&&base<=1&&limit-base<1usize<<out.len());
    for lane in (0..limit).rev() {
        let value=lane+1-base;if value==0{continue;}
        let pivot=value.trailing_zeros()as usize;
        let end=cut_a.saturating_sub(lane).min(1usize<<cut.len());
        let mut at=0;
        while at<end {
            let free=(if at==0{cut.len()}else{at.trailing_zeros()as usize})
                .min((usize::BITS-1-(end-at).leading_zeros())as usize).min(cut.len());
            let mut ctl=vec![(c,false),(source[lane],false)];
            ctl.extend((free..cut.len()).map(|i|(cut[i],at>>i&1==0)));
            ctl.extend(out.iter().enumerate().filter(|(i,_)|*i!=pivot).map(|(_,&q)|(q,true)));
            encoded_xor(b,&ctl,out[pivot],c,u,dirty);at+=1usize<<free;
        }
        let mut pattern=1usize<<pivot;
        for(i,&target)in out.iter().enumerate(){
            if i==pivot||value>>i&1==0{continue;}
            let ctl:Vec<_>=std::iter::once((c,false)).chain(out.iter().enumerate()
                .filter(|(j,_)|*j!=i).map(|(j,&q)|(q,pattern>>j&1==0))).collect();
            encoded_xor(b,&ctl,target,c,u,dirty);pattern|=1usize<<i;
        }
    }
}

/// T1/T4-only seven-state tail. No operation names scratch[7] (old toggle).
/// The source contracts provide clean scratch, PH=0 on C and u<=159.
#[allow(clippy::too_many_arguments)]
pub(crate) fn apply7(b:&mut B,ring:&[QubitId],q:&[QubitId],e:&[QubitId],
    scratch:&[QubitId],ph:QubitId,par:&TailPar,phase_already_moved:bool,dirty:&[QubitId]) {
    assert_eq!((ring.len(),q.len(),e.len(),scratch.len()),(257,128,7,8));
    if super::super::super::c659::drop_enabled(){assert_eq!(scratch[7],crate::circuit::NO_QUBIT,"C658_DROP: eighth scratch position is evicted");}
    let c=scratch[0];let u:Vec<_>=scratch[1..].iter().copied().chain([ph]).collect();
    let ports:Vec<_>=ring.iter().chain(q).chain(e).chain(scratch).copied().chain([ph]).filter(|q|super::super::super::c659::retained(*q)).collect();
    assert_eq!(ports.len(),ports.iter().collect::<BTreeSet<_>>().len());
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=ring.iter().chain(q).chain(e).chain(&scratch[1..]).chain([ph].iter()).chain(dirty).copied()
        .filter(|v|*v!=c&&*v!=scratch[7]&&seen.insert(*v)).collect();
    if phase_already_moved {b.cx(c,ph);}
    let n=ring.len();let rev:Vec<_>=ring.iter().rev().copied().collect();
    let ylo=par.szlo.min(par.sylo).max(1);let umax=(par.l0+par.qb+1).min(n-ylo);
    assert!(umax<=159&&par.swl_hi<=q.len()&&par.m<=128);
    let p1=record(b,|b|probe7(b,ring,umax,e,n-1,&u,0,c,&u,&bank));b.play(&p1,false);
    let p2=record(b,|b|probe7(b,&rev,par.l0,&u,n,e,1,c,&u,&bank));b.play(&p2,true);
    for l in 0..n/2 {swap_c7(b,c,&u,ring[l],ring[n-1-l],&bank);}
    let lmin=(n-umax).min(par.swl_hi);
    for l in 0..lmin {swap_c7(b,c,&u,ring[l],q[l],&bank);}
    if lmin<par.swl_hi {
        let flag=e[0];range7(b,&u,0,n-par.swl_hi+1,c,flag,&bank);
        for l in (lmin..par.swl_hi).rev() {
            let(a,z)=(ring[l],q[l]);b.cx(a,z);
            encoded_xor(b,&[(c,false),(flag,false),(z,false)],a,c,&u,&bank);
            b.cx(a,z);
            if l>lmin {range7(b,&u,n-l,n-l+1,c,flag,&bank);}
        }
        range7(b,&u,0,n-lmin,c,flag,&bank);
    }
    let pm=record(b,|b|probe7(b,ring,par.m,&u,n,e,1,c,&u,&bank));b.play(&pm,false);
    let pu=record(b,|b|probe7(b,&rev,umax,e,n-1,&u,0,c,&u,&bank));b.play(&pu,true);
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
