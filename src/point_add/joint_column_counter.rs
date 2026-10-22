//! Stage-15 counter update in the outside joint metadata representation.
//!
//! Register this beside frogdrop's other external helpers. The caller has
//! completed the map and switching tail: E is the outside boundary packet,
//! except that `escape_tag` may retain C=W|delayed-D on SX3. That
//! class is excluded from every update. DONE implies C=0, and C=1 cannot
//! be a fresh finisher at this boundary. All supplied clean owners are zero.
//!
//! A done packet is E=1536+16*(SY-1)+H4. Thus its counter bits2..5 occupy
//! E[0..4] (physical SY[0..4]), while bits0/1 stay Q121/Q122. Counter bit6 is
//! absent before the public column159 handoff and then lives in Q120.
//! The top two E bits are a class tag, never an unencoded phase read here.

use super::super::arith;
use super::super::builder::B;
use super::super::frogdrop_col::{ColPar, Fd};
use super::super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

const DONE_BASE: usize = 3 << 9;

/// Update existing done counters, then create counter1 for a fresh finish.
/// `boundary_ht_offset` is the caller's named BoundaryView HT base (192 in
/// the asymmetric outside codec), not the middle's symmetric HT base672.
/// The counter and all map-parity consumers retain their actual low bit.
#[allow(clippy::too_many_arguments)]
pub(crate) fn finish_column(b: &mut B, fd: &Fd, cp: &ColPar,
    escape_tag: QubitId, flag: QubitId, clean: &[QubitId],
    dirty: &[QubitId], boundary_ht_offset: usize) {
    if !cp.dn && !cp.fin { return; }
    assert_eq!(fd.sy.len(),5);
    assert_eq!(fd.q.len(),128);
    assert_eq!(fd.cnt.len(),7);
    assert_eq!(&fd.cnt[..2],&fd.q[121..123]);
    assert!(boundary_ht_offset < DONE_BASE);
    let late = fd.cnt[6] == fd.q[120];
    assert!(late || fd.cnt[6] == fd.q[127]);
    assert_eq!(late,cp.col>=159,
        "joint stage15 must use the caller's public counter epoch");
    // Derive the no-wrap bound from the inherited public schedule, not an
    // input sample. Before159 no omitted high counter bit can be generated.
    let schedule=super::super::frogdrop_sched::from_text(
        super::super::pointadd_frogdrop::SCHED_FROGDROP);
    let first_finish=schedule.cols.iter().position(|c|c.fin)
        .expect("joint counter requires a public first-finish column");
    assert!(cp.col < schedule.cols.len());
    let max_after=cp.col.saturating_sub(first_finish)+1;
    assert!(max_after < 128);
    if !late { assert!(max_after < 64); }

    let word:Vec<_>=fd.sy.iter().chain(fd.q[123..128].iter())
        .copied().chain(std::iter::once(fd.ph)).collect();
    assert_eq!(word.len(),11);
    let mut counter=vec![fd.q[121],fd.q[122]];
    counter.extend_from_slice(&fd.sy[..4]);
    if late { counter.push(fd.q[120]); }
    assert_eq!(counter.iter().copied().collect::<BTreeSet<_>>().len(),counter.len());

    let mut protected:BTreeSet<_>=word.iter().chain(&counter).copied().collect();
    assert!(protected.insert(escape_tag));
    assert!(protected.insert(flag));
    assert!(!fd.ring.contains(&flag) && !fd.q.contains(&flag));
    for &q in clean {
        assert!(!fd.ring.contains(&q) && !fd.q.contains(&q));
        assert!(protected.insert(q),"joint counter clean owners alias held data");
    }
    assert!(clean.len() >= counter.len()-1);
    let mut seen=BTreeSet::new();
    let donors:Vec<_>=dirty.iter().copied()
        .filter(|q|!protected.contains(q)&&seen.insert(*q)).collect();
    let done=[(word[9],false),(word[10],false),(escape_tag,true)];

    if cp.dn {
        mc_xor(b,&done,flag,clean,&donors);
        arith::inc(b,flag,&counter,&clean[..counter.len()-1]);
        // Only counter cells changed; neither tag bit nor W was touched.
        mc_xor(b,&done,flag,clean,&donors);
    }
    if cp.fin {
        // HT + SY1 + no high-Y payload is exactly the named active base.
        // It is disjoint from every done tag, so old done shots cannot be
        // counted twice. The switching escape is explicitly excluded.
        let mut fresh:Vec<_>=word.iter().enumerate()
            .map(|(i,&q)|(q,(boundary_ht_offset>>i)&1==0)).collect();
        fresh.push((escape_tag,true));
        mc_xor(b,&fresh,flag,clean,&donors);
        b.cx(flag,counter[0]);
        let delta=boundary_ht_offset ^ DONE_BASE;
        for (i,&q) in word.iter().enumerate() {
            if (delta>>i)&1!=0 {b.cx(flag,q);}
        }
        // Fresh finish now has SY1,counter1. Every previously done shot
        // has counter>=2 after its no-wrap increment, so this exact output
        // predicate erases only the inserted flag. E already contains the
        // four high counter bits; do not duplicate those as MCX controls.
        let mut made:Vec<_>=word.iter().enumerate()
            .map(|(i,&q)|(q,(DONE_BASE>>i)&1==0)).collect();
        made.extend([(counter[0],false),(counter[1],true),(escape_tag,true)]);
        if late {made.push((fd.q[120],true));}
        mc_xor(b,&made,flag,clean,&donors);
    }
}
