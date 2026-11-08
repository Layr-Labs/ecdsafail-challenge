//! Exact metadata coordinates for complete empty-Q payload epochs.
//!
//! The direct-Z coordinate is used only by complete ring-source kernels;
//! every frame is reversed before another normalized size reader runs.
//!
//! At a complete active payload boundary Q=Y, no quotient bits are parked,
//! and 1<=SY<=128. The current normalized ten-bit packet E is transformed to
//! V=SY-1 for SY<=123, or V=128+H for SY>=124, H=Q[123..128].
//! The latter H is in [1,32), with its leading one at SY-124. Thus exactly
//! 123+(1+2+4+8+16)=154 states occupy V<160; E[8],E[9] become zero.
//!
//! These two outputs are only CONDITIONALLY zero under `act`. Every borrower
//! must preserve act/retained-enable semantics and return both before inverse
//! replay. They are not globally clean measured-AND ancillas on skipped shots.
//! The record itself is a full literal permutation for every input, and the
//! complete controlled record is exactly identity when act=0.
//!
//! Low five packet ports remain the logical Q123..127 source view. For high
//! SY, V=128+H preserves all five H bits. For low SY they are arbitrary data
//! above the true Q boundary, requiring the existing virtual-boundary kernel.
//! High-size queries need a one-cell lookahead: H's leading bit at source
//! SY-1 must be restored before it is read. See SOURCE_PROOF.json.

use super::builder::{B, G};
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// Swap two equal-width aligned prefix cubes, keeping `free` low bits.
/// Clifford conjugation maps their XOR difference to one pivot. One MCX
/// then transposes the prefixes; reversing the Clifford frame restores every
/// other word. The only extra MCX literal is act, so off-act is identity.
fn prefix_transposition(b:&mut B, word:&[QubitId], a:usize, z:usize,
    free:usize, act:QubitId, dirty:&[QubitId]) {
    assert_eq!(word.len(),10);
    assert!(free<10 && a<1024 && z<1024 && a!=z);
    assert_eq!(a&((1usize<<free)-1),0);
    assert_eq!(z&((1usize<<free)-1),0);
    let delta=a^z;
    let pivot=delta.trailing_zeros() as usize;
    assert!(pivot>=free);
    let changed:Vec<_>=(free..10)
        .filter(|&i|i!=pivot && (delta>>i)&1!=0).collect();
    for &i in &changed {b.cx(word[pivot],word[i]);}
    let ap=(a>>pivot)&1;
    let mut literals=vec![(act,false)];
    for i in free..10 {
        if i==pivot {continue;}
        let transformed=((a>>i)&1) ^ (ap & ((delta>>i)&1));
        literals.push((word[i],transformed==0));
    }
    mc_xor(b,&literals,word[pivot],&[],dirty);
    for &i in changed.iter().rev() {b.cx(word[pivot],word[i]);}
}

/// Capture the complete exact permutation. Play forward at empty-Q entry,
/// backward before any quotient park, field/class conversion or code reader
/// expecting the existing normalized E representation.
pub(crate) fn record(b:&mut B, word:&[QubitId], act:QubitId,
    dirty:&[QubitId])->Vec<G> {
    assert_eq!(word.len(),10);
    let mut ports=BTreeSet::new();
    assert!(word.iter().copied().chain([act]).all(|q|ports.insert(q)));
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied()
        .filter(|q|!ports.contains(q) && seen.insert(*q)).collect();
    assert!(bank.len()>=8,"empty packet needs eight returned dirty donors");
    b.begin();
    // Ascending source order vacates old112/120/128 before a later
    // transposition can move a valid state into one of those addresses.
    for sy in 110..=123 {
        let old=match sy {110=>112,111=>120,112=>128,_=>32*(sy-108)};
        prefix_transposition(b,word,old,sy-1,0,act,&bank);
    }
    for sy in 124..=128 {
        let free=sy-124;
        let leading=1usize<<free;
        let old=32*(sy-108)+leading;
        let new=128+leading;
        prefix_transposition(b,word,old,new,free,act,&bank);
    }
    b.end()
}

/// Empty-packet size equality, gated by an immutable retained enable.
/// Size1..123 is one raw eight-bit equality. Size124..128 is a dyadic
/// prefix: V[7..5]=100, V[m]=1, V[m+1..5]=0, m=size-124.
/// Equalities remain disjoint on every eight-bit word, including holes.
/// Ignored word[8..10] may be conditionally borrowed, but are not assumed
/// globally clean by this literal reader. The caller must restore the
/// source leading bit before high-size queries.
pub(crate) fn xor_eq(b:&mut B, word:&[QubitId], size:usize,
    target:QubitId, enable:QubitId, extra:&[(QubitId,bool)],
    dirty:&[QubitId]) {
    assert_eq!(word.len(),10);
    if !(1..=128).contains(&size) {return;}
    assert!(!word.contains(&target) && !word.contains(&enable));
    assert!(target!=enable);
    let mut literals=vec![(enable,false)];
    if size<=123 {
        let value=size-1;
        literals.extend((0..8).map(|i|(word[i],(value>>i)&1==0)));
    } else {
        let m=size-124;
        literals.extend([(word[7],false),(word[6],true),(word[5],true)]);
        literals.push((word[m],false));
        literals.extend((m+1..5).map(|i|(word[i],true)));
    }
    for &(q,neg) in extra {
        assert!(q!=target);
        if let Some((_,old))=literals.iter().find(|(p,_)|*p==q) {
            if *old!=neg {return;}
        } else {literals.push((q,neg));}
    }
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied().filter(|q|
        !word.contains(q) && *q!=target && !literals.iter().any(|(p,_)|p==q)
        && seen.insert(*q)).collect();
    mc_xor(b,&literals,target,&[],&bank);
}

/// Query-only one-cell lookahead for a Q-source cached DIV membership.
/// Entry is immediately after the main undo_cell(boundary). The query
/// must not read the old carry at s[boundary-1], write this lower cell, or
/// retain a borrow of it. It may write only its separate membership flag.
/// The original carry is restored before DIV's local e/target updates.
/// Low queries need no lookahead: all encoded source ports123..127 are
/// already restored. This helper is NOT the ADD/compare carry-extra ABI.
pub(crate) fn membership_after_q_restore(b:&mut B,t:&[QubitId],s:&[QubitId],
    carry:QubitId,boundary:usize,mut query:impl FnMut(&mut B)) {
    if !(124..=128).contains(&boundary) {query(b);return;}
    let j=boundary-1;
    assert!(j<s.len() && j<t.len());
    let x=if j==0 {carry}else{s[j-1]};
    b.ccx(x,t[j],s[j]);b.cx(s[j],x);b.cx(s[j],t[j]);
    query(b);
    b.cx(s[j],t[j]);b.cx(s[j],x);b.ccx(x,t[j],s[j]);
}

/// EMPTY V8 -> direct SizeZ address, for a complete RING-source kernel.
/// Keep Vlow7 unchanged; store floor(Z/32)-3 on old V7,E8,E9.
/// Valid active sizes obey226<=Z+Y<=257,1<=Y<=128, hence98<=Z<=256.
/// The new address is Z=96+zlow+32*rank, rank0..5, including Z256.
///
/// `flag` is globally zero at entry/exit. E8/E9 need only be zero on act.
/// Every target write is gated so off-act is exactly identity, including
/// arbitrary E8/E9. Dirty carry echoes never assume a clean dirty target.
/// The complete inverse must run after the kernel restores its size/data
/// sources and act. No logical Q reader may use this direct-Z frame.
pub(crate) fn z_rank_from_empty_record(b:&mut B,word:&[QubitId],zlow:&[QubitId],
    act:QubitId,flag:QubitId,dirty:&[QubitId])->Vec<G> {
    assert_eq!(word.len(),10);assert_eq!(zlow.len(),5);
    let mut ports=BTreeSet::new();
    assert!(word.iter().chain(zlow).copied().chain([act,flag])
        .all(|q|ports.insert(q)));
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied()
        .filter(|q|!ports.contains(q)&&seen.insert(*q)).collect();
    assert!(bank.len()>=10);
    let (d,helper)=(bank[0],bank[1]);
    let rest=&bank[2..];
    let v=&word[..7];let h=&word[7..10];
    b.begin();
    // On act: move old EMPTY high class into flag, leaving h=000.
    b.ccx(act,h[0],flag);b.cx(flag,h[0]);
    // Ordinary class Y=v+1. Let a=v>>5, l=v mod32. Its rank is
    // 5-a-carry5(l+z)-[(l+z)mod32 !=0]. Start at5-a:
    // rank0=!v5, rank1=v6, rank2=!v6.
    for (target,source,negative) in [(h[0],v[5],true),
        (h[1],v[6],false),(h[2],v[6],true)] {
        mc_xor(b,&[(act,false),(flag,true),(source,negative)],target,&[],rest);
    }
    // Decrement rank under carry. Each bit is a dirty XOR echo; its lower
    // rank controls remain unchanged until that descending bit completes.
    // The carry oracle reads only restored vlow/zlow, never rank or flag.
    for k in (0..3).rev() {
        let mut ctl=vec![(act,false),(flag,true),(d,false)];
        ctl.extend(h[..k].iter().map(|&q|(q,true)));
        super::arith::ttk_carry_u(b,&v[..5],zlow,d,helper);
        mc_xor(b,&ctl,h[k],&[],rest);
        super::arith::ttk_carry_u(b,&v[..5],zlow,d,helper);
        mc_xor(b,&ctl,h[k],&[],rest);
    }
    b.begin();super::arith::ttk_add(b,&v[..5],zlow,None,None);
    let add=b.end();b.play(&add,false);
    // Decrement under sum!=0: a cube XOR the same cube with sum==0.
    for k in (0..3).rev() {
        let mut ctl=vec![(act,false),(flag,true)];
        ctl.extend(h[..k].iter().map(|&q|(q,true)));
        mc_xor(b,&ctl,h[k],&[],rest);
        ctl.extend(zlow.iter().map(|&q|(q,true)));
        mc_xor(b,&ctl,h[k],&[],rest);
    }
    b.play(&add,true);
    // High EMPTY class has Y=124+m, identified by its leading H bit.
    // rank is the one bit [zlow<=5-m]; the other two rank bits stay zero.
    // flag implies act, so an additional act literal is unnecessary here.
    for m in 0..5 {
        let mut prefix=vec![(flag,false),(v[m],false)];
        prefix.extend((m+1..5).map(|i|(v[i],true)));
        let mut lo=0usize;let end=6-m;
        while lo<end {
            let alignment=if lo==0 {5}else{lo.trailing_zeros() as usize};
            let remaining=usize::BITS as usize-1-(end-lo).leading_zeros() as usize;
            let free=alignment.min(remaining).min(5);
            let mut ctl=prefix.clone();
            ctl.extend((free..5).map(|i|(zlow[i],(lo>>i)&1==0)));
            mc_xor(b,&ctl,h[0],&[],rest);
            lo+=1usize<<free;
        }
    }
    // Recover the old high class from the output: high has v<32,rank<=1.
    // Colliding ordinary v0..31 means Y1..32, Z>=194, so rank>=3.
    mc_xor(b,&[(act,false),(v[5],true),(v[6],true),
        (h[1],true),(h[2],true)],flag,&[],rest);
    b.end()
}

/// Direct SizeZ equality in the above frame. No size enumeration or class
/// split: zlow5 plus biased rank3 is one eight-bit address. All equality
/// values remain disjoint for arbitrary off-domain address words.
pub(crate) fn xor_z_eq(b:&mut B,word:&[QubitId],zlow:&[QubitId],size:usize,
    target:QubitId,extra:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
    assert_eq!(word.len(),10);assert_eq!(zlow.len(),5);
    if !(98..=256).contains(&size) {return;}
    let address:Vec<_>=zlow.iter().chain(&word[7..10]).copied().collect();
    let value=size-96;
    let mut ctl:Vec<_>=address.iter().enumerate()
        .map(|(i,&q)|(q,(value>>i)&1==0)).collect();
    for &(q,neg) in extra {
        assert!(q!=target);
        if let Some((_,old))=ctl.iter().find(|(p,_)|*p==q) {
            if *old!=neg{return;}
        } else {ctl.push((q,neg));}
    }
    assert!(!word.contains(&target)&&!zlow.contains(&target));
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied().filter(|q|
        !word.contains(q)&&!zlow.contains(q)&&*q!=target&&!clean.contains(q)
        &&!ctl.iter().any(|(p,_)|p==q)&&seen.insert(*q)).collect();
    assert!(clean.iter().all(|q|!word.contains(q)&&!zlow.contains(q)
        &&*q!=target&&!ctl.iter().any(|(p,_)|p==q)));
    mc_xor(b,&ctl,target,clean,&bank);
}
