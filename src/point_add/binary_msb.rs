//! Literal reversible binary search for the highest set bit.
//! No allocation; source is restored and all borrowed donors are restored.
//! Active care requires out=0. Zero source and source=1 both encode index0.
//! Off gate this is the identity even with arbitrary source and output.
use super::super::builder::{B,G};
use super::super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// Public price of the bounded binary search below: (CX, CCX). No gate
/// tape is built to choose between the two source-level implementations.
pub(crate) fn bounded_price(len:usize,gated:bool)->(usize,usize){
    assert!(len>0);
    let bits=len.next_power_of_two().trailing_zeros()as usize;
    let(mut cx,mut ccx)=(0,0);
    let mut query=|n:usize|{match n{0=>(),1=>cx+=1,2=>ccx+=1,n=>ccx+=4*(n-2)}};
    for k in(0..bits).rev(){
        let half=1usize<<k;let full=half.min(len-half);
        query(usize::from(gated));query(full+usize::from(gated));
        let rem=len%(2*half);
        if k+1<bits&&rem!=0{
            let prefix=bits-k-1+usize::from(gated);
            query(prefix+rem.saturating_sub(half));query(prefix+half);
        }
    }
    drop(query);
    let swaps:usize=(0..bits).map(|k|{let h=1usize<<k;h.min(len-h)}).sum();
    (cx+4*swaps,ccx+2*swaps)
}

/// MSB search without padding a short physical source to a power of two.
/// After each fold, the selected valid subword is a prefix of the physical
/// work window. Only the last possible address prefix can be short. For
/// that prefix, OR(full) is corrected to OR(valid) by XORing
/// AND(!valid) and AND(!full). Invalid physical cells may be arbitrary.
/// The literal inverse restores the source and all dirty donors exactly.
pub(crate) fn bounded_record(b:&mut B,word:&[QubitId],out:&[QubitId],
    gate:Option<(QubitId,bool)>,dirty:&[QubitId])->Vec<G>{
    assert!(!word.is_empty());
    let bits=word.len().next_power_of_two().trailing_zeros()as usize;
    assert_eq!(out.len(),bits);
    let ports:Vec<_>=word.iter().chain(out).copied().chain(gate.map(|x|x.0)).collect();
    assert_eq!(ports.len(),ports.iter().collect::<BTreeSet<_>>().len());
    let query=|b:&mut B,ctl:&[(QubitId,bool)],t:QubitId|{
        let mut seen=BTreeSet::new();
        let bank:Vec<_>=dirty.iter().copied().filter(|q|*q!=t
            &&!ctl.iter().any(|p|p.0==*q)&&seen.insert(*q)).collect();
        mc_xor(b,ctl,t,&[],&bank);
    };
    b.begin();let mut swaps=Vec::new();
    for k in(0..bits).rev(){
        let half=1usize<<k;let end=(2*half).min(word.len());
        let active:Vec<_>=gate.into_iter().collect();
        query(b,&active,out[k]);
        let mut all=active.clone();all.extend(word[half..end].iter().map(|&q|(q,true)));
        query(b,&all,out[k]);
        let rem=word.len()%(2*half);
        if k+1<bits&&rem!=0{
            let last=(word.len()-1)/(2*half);
            let mut prefix=active;
            prefix.extend((k+1..bits).map(|i|(out[i],last>>(i-k-1)&1==0)));
            let mut valid=prefix.clone();
            valid.extend(word[half..half+rem.saturating_sub(half)].iter().map(|&q|(q,true)));
            query(b,&valid,out[k]);
            prefix.extend(word[half..2*half].iter().map(|&q|(q,true)));
            query(b,&prefix,out[k]);
        }
        for i in 0..end-half{
            b.cswap(out[k],word[i],word[i+half]);swaps.push((out[k],word[i],word[i+half]));
        }
    }
    for &(c,a,z)in swaps.iter().rev(){b.cswap(c,a,z);}
    b.end()
}

/// Captures U: |word,0> -> |word,msb(word)> on the active gate.
/// Replaying this exact tape backwards erases a previously computed index.
/// `word` must have a power-of-two length; no implicit padding is allowed.
/// Gate is immutable and outside word/out; callers with a source gate must
/// first copy that gate into a separate existing, returned helper.
pub(crate) fn record(b:&mut B,word:&[QubitId],out:&[QubitId],
    gate:Option<(QubitId,bool)>,dirty:&[QubitId])->Vec<G>{
    assert!(!word.is_empty() && word.len().is_power_of_two());
    assert_eq!(out.len(),word.len().trailing_zeros()as usize);
    let ports:Vec<_>=word.iter().chain(out).copied().chain(gate.map(|x|x.0)).collect();
    assert_eq!(ports.len(),ports.iter().collect::<BTreeSet<_>>().len());
    b.begin();
    let mut swaps=Vec::with_capacity(word.len().saturating_sub(1));
    for k in(0..out.len()).rev(){
        let n=1usize<<k;
        // A singleton OR is the source itself. For larger halves,
        // OR(upper) = 1 XOR AND(!upper), restricted by the stable gate.
        if n>1{match gate{
            None=>b.x(out[k]),
            Some((g,neg))=>{if neg{b.x(out[k]);}b.cx(g,out[k]);}
        }}
        let controls:Vec<_>=gate.into_iter()
            .chain(word[n..2*n].iter().map(|&q|(q,n>1))).collect();
        let mut seen=BTreeSet::new();
        let bank:Vec<_>=dirty.iter().copied().filter(|q|
            *q!=out[k] && !controls.iter().any(|p|p.0==*q) && seen.insert(*q)).collect();
        assert!(bank.len()>=controls.len().saturating_sub(2));
        mc_xor(b,&controls,out[k],&[],&bank);
        // The selected half becomes the next prefix. Other halves remain
        // stored in the same word until all index bits have been queried.
        for i in 0..n{
            b.cswap(out[k],word[i],word[i+n]);
            swaps.push((out[k],word[i],word[i+n]));
        }
    }
    // Controls above are never changed by lower queries, so this is the
    // exact reverse of every source permutation, with index bits retained.
    for &(c,a,z)in swaps.iter().rev(){b.cswap(c,a,z);}
    b.end()
}
