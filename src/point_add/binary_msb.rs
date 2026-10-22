//! Literal reversible binary search for the highest set bit.
//! No allocation; source is restored and all borrowed donors are restored.
//! Active care requires out=0. Zero source and source=1 both encode index0.
//! Off gate this is the identity even with arbitrary source and output.
use super::super::builder::{B,G};
use super::super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

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
