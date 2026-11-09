//! Frame-row carry tail without a dedicated clean `h` owner.
//!
//! Source integration only. The lowerer preserves the caller's complete
//! source span, carry-tail span, and clean-carry policy. It allocates nothing.
//! With no spare clean tail owner, two controls form the low part of one
//! literal increment; undoing their two-bit increment returns both controls.

use super::super::arith::{down_m, up_m, Dm};
use super::super::builder::B;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// tail += a*b, with both arbitrary controls restored. Every `clean` owner
/// starts and returns zero; every dirty donor is arbitrary and restored.
pub(crate) fn inc_two(b: &mut B, a: QubitId, c: QubitId, tail: &[QubitId],
                     clean: &[QubitId], dirty: &[QubitId]) {
    if tail.is_empty() { return; }
    let mut ports = BTreeSet::new();
    for &q in [a,c].iter().chain(tail).chain(clean) {
        assert!(ports.insert(q), "two-control carry aliases an operand");
    }
    let mut seen = BTreeSet::new();
    let bank: Vec<_> = dirty.iter().copied()
        .filter(|q| !ports.contains(q) && seen.insert(*q)).collect();
    if tail.len() == 1 { b.ccx(a,c,tail[0]); return; }
    if let Some((&flag, rest)) = clean.split_first() {
        b.and_c(a,c,flag);
        super::inc_mixed(b,flag,tail,rest,&bank);
        b.and_u(a,c,flag);
        return;
    }
    let word: Vec<_> = [a,c].iter().chain(tail).copied().collect();
    assert!(bank.len() >= word.len(), "two-control increment lacks restored donors");
    // One ordinary binary increment carries into tail iff original a=c=1.
    // Its low pair is (a+2c+1) mod4. The inverse low-pair increment below
    // depends on no tail cell, and returns that pair for all four inputs.
    super::super::modp_frogdrop::inc_dirty_free(b,&word,&bank);
    b.x(a);
    b.cx(a,c);
}

/// Exact `cadd_tail_and_mixed` row without the separately allocated h.
/// `c0` and all explicit clean owners obey the parent's zero contracts.
#[allow(clippy::too_many_arguments)]
pub(crate) fn cadd_tail_no_h(b: &mut B, g: QubitId, t: &[QubitId],
    s: &[QubitId], tail: &[QubitId], c0: QubitId, clean: &[QubitId],
    dirty: &[QubitId], andc: &[QubitId]) {
    let n=t.len();
    assert!(n>=1 && s.len()==n);
    let k=andc.len().min(n);
    let low=n-k;
    let up=up_m(b,&t[..low],&s[..low],c0,false);
    let down=down_m(b,&t[..low],&s[..low],c0,Dm::Cond(g),false);
    let carry=|i:usize| {
        if i==low {if low==0 {c0} else {s[low-1]}}
        else {andc[i-1-low]}
    };
    if low>0 {b.play(&up,false);}
    for i in low..n {
        let c=carry(i);
        b.cx(c,t[i]); b.cx(c,s[i]);
        b.and_c(t[i],s[i],andc[i-low]);
        b.cx(c,andc[i-low]);
    }
    if !tail.is_empty() {
        let cout=if k>0 {andc[k-1]} else {s[n-1]};
        let held: BTreeSet<_> = t.iter().chain(s).chain(&andc[..k])
            .copied().chain([g,c0]).collect();
        assert!(clean.iter().all(|q|!held.contains(q) && !tail.contains(q)));
        let bank:Vec<_>=dirty.iter().copied().filter(|q|!held.contains(q)).collect();
        inc_two(b,g,cout,tail,clean,&bank);
    }
    for i in (low..n).rev() {
        let c=carry(i);
        b.cx(c,andc[i-low]);
        b.and_u(t[i],s[i],andc[i-low]);
        b.cx(c,t[i]); b.ccx(g,s[i],t[i]); b.cx(c,s[i]);
    }
    if low>0 {b.play(&down,false);}
}
