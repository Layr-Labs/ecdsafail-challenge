//! Exact source-preserving bitlength XOR, using only globally clean bank lanes.
//! The bank is clean at both ends. Output is arbitrary and is never read.
use super::builder::B;
use crate::circuit::QubitId;

fn compute_or(b:&mut B,a:Option<QubitId>,v:QubitId,t:QubitId){
    if let Some(a)=a {b.and_c(a,v,t);b.cx(a,t);b.cx(v,t);} else {b.cx(v,t);}
}
fn erase_or(b:&mut B,a:Option<QubitId>,v:QubitId,t:QubitId){
    if let Some(a)=a {b.cx(v,t);b.cx(a,t);b.and_u(a,v,t);} else {b.cx(v,t);}
}
fn onehot(b:&mut B,seen:Option<QubitId>,v:QubitId,tmp:QubitId,out:&[QubitId],value:usize){
    let put=|b:&mut B,q:QubitId| {for (j,&o) in out.iter().enumerate(){if value&(1usize<<j)!=0 {b.cx(q,o);}}};
    if let Some(q)=seen {
        b.x(q);b.and_c(q,v,tmp);b.x(q);put(b,tmp);
        b.x(q);b.and_u(q,v,tmp);b.x(q);
    }else {put(b,v);}
}
pub fn need(n:usize,chunk:usize)->usize{
    if n==0{return 0;}n.div_ceil(chunk)-1+chunk.saturating_sub(1)+1
}
pub fn choose(n:usize,bank:usize)->Option<usize>{
    (1..=n).filter(|&c|need(n,c)<=bank).min_by_key(|&c|{
        let blocks=n.div_ceil(c);
        if n==1{0}else if blocks==1{2*n-3}else{2*n-4+(blocks-1)*(c-1)}
    })
}
pub fn emit(b:&mut B,v:&[QubitId],lo:usize,hi:usize,out:&[QubitId],bank:&[QubitId]){
    emit_mapped(b,v,lo,hi,out,bank,|lane|lane+1);
}
fn emit_mapped(b:&mut B,v:&[QubitId],lo:usize,hi:usize,out:&[QubitId],bank:&[QubitId],value:impl Fn(usize)->usize){
    assert!(lo<=hi&&hi<=v.len());let n=hi-lo;if n==0{return;}
    assert!((lo..hi).all(|lane|value(lane)<(1usize<<out.len())));
    let mut seen=std::collections::BTreeSet::new();
    for &q in bank {assert!(seen.insert(q));assert!(!v.contains(&q)&&!out.contains(&q));}
    let chunk=choose(n,bank.len()).expect("priority probe clean bank is insufficient");
    let blocks=n.div_ceil(chunk);let nf=blocks-1;
    let flags=&bank[..nf];let work=&bank[nf..nf+chunk-1];let tmp=bank[nf+chunk-1];
    // Blocks run high to low. Their output summary is the OR of every higher
    // input lane, including this block. Work prefixes stay live until each
    // one-hot bit has been copied and the block summary has been computed.
    for j in 0..blocks {
        let top=hi-j*chunk;let bottom=lo.max(top.saturating_sub(chunk));let len=top-bottom;
        let incoming=j.checked_sub(1).map(|i|flags[i]);let mut prev=incoming;
        for k in 0..len {
            let lane=top-1-k;onehot(b,prev,v[lane],tmp,out,value(lane));
            if k+1<len {let next=work[k];compute_or(b,prev,v[lane],next);prev=Some(next);}
            else if j<nf {compute_or(b,prev,v[lane],flags[j]);}
        }
        for k in (0..len-1).rev(){let prev=if k==0{incoming}else{Some(work[k-1])};erase_or(b,prev,v[top-1-k],work[k]);}
    }
    // Summaries are returned zero before any source/size/caller reuse.
    // Rebuild each block's internal prefixes from the unchanged input, then
    // erase its final OR and all prefixes by the original quadratic predicate.
    for j in (0..nf).rev(){
        let top=hi-j*chunk;let bottom=lo.max(top.saturating_sub(chunk));let len=top-bottom;
        let incoming=j.checked_sub(1).map(|i|flags[i]);let mut prev=incoming;
        for k in 0..len-1 {compute_or(b,prev,v[top-1-k],work[k]);prev=Some(work[k]);}
        erase_or(b,prev,v[bottom],flags[j]);
        for k in (0..len-1).rev(){let prev=if k==0{incoming}else{Some(work[k-1])};erase_or(b,prev,v[top-1-k],work[k]);}
    }
}
// Same capped trailing-zero value as the old zero-prefix walk, including the
// all-zero low prefix. The unchanged caller domain requires v2<=emax. Each
// selected lower one XORs k^emax into the public default emax.
pub fn trailing(b:&mut B,v:&[QubitId],emax:usize,out:&[QubitId],bank:&[QubitId]){
    assert!(emax<=v.len()&&emax<(1usize<<out.len()));
    for (j,&o) in out.iter().enumerate(){if emax&(1usize<<j)!=0{b.x(o);}}
    if emax==0{return;}
    let rev:Vec<_>=v[..emax].iter().rev().copied().collect();
    emit_mapped(b,&rev,0,emax,out,bank,|lane|((emax-1)-lane)^emax);
}
pub fn map_bank(sc:&super::frogdrop::MapScr)->Vec<QubitId>{
    let mut bank=vec![sc.c0,sc.h,sc.e,sc.g,sc.f,sc.tmp,sc.one];
    bank.extend(sc.anc.iter().chain(&sc.pre).chain(&sc.ez).chain(&sc.epre).chain(&sc.andc).copied());
    bank.sort();bank.dedup();bank
}
