//! Whole direct-layout endpoint, source only. Counter remains Q121..127.
//! The B0 map uses the same positive-size-minus1 map ABI as ordinary columns;
//! only the final payload epoch enters the inherited raw-size endpoint ABI.
use super::builder::B;
use super::direct_column::Column;
use super::frogdrop_col::{Fd,ColPar,ColScr};
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn b0_flag(b:&mut B,col:&Column<'_>,flag:QubitId,dirty:&[QubitId]){
    let cnt=&col.q[121..128];
    b.x(flag);b.cx(cnt[0],flag);
    for value in 1..128{
        if super::frogdrop_col::map_ctrl_skipped(value)%2==1{
            let ctl:Vec<_>=cnt.iter().enumerate().map(|(i,&q)|(q,value>>i&1==0)).collect();
            mc_xor(b,&ctl,flag,&[],dirty);
        }
    }
}

/// Entry every shot DONE: Q=R<2^26, E=bl(top)-1, PH1, S/four roles0.
/// Exit ring top1, E0, PH1, same counter, Q=R; optional P is in the
/// original compact terminal ABI. The caller's final constants omit E0.
pub(crate) fn finish(b:&mut B,col:&Column<'_>,b0:Option<&ColPar>,last:&ColPar){
    assert!(!super::frogdrop_col::c660_joint_size());
    assert!(last.nomap&&last.ht&&last.sy==(1,1));
    assert_eq!((col.ring.len(),col.q.len()),(257,128));
    let r=col.roles;
    let scratch:Vec<_>=std::iter::once(r.tag).chain(col.meta.sum.iter().copied())
        .chain([r.cut,r.toggle,r.prefix]).collect();
    let mut excluded:BTreeSet<_>=[r.tag,col.phase].into_iter().collect();
    excluded.extend(col.q[114..].iter().copied());
    if let Some(p)=col.compact{excluded.extend(p.iter().copied());}
    let mut seen=BTreeSet::new();
    let dirty:Vec<_>=col.ring.iter().chain(&col.q[..114]).chain(&col.meta.y)
        .chain(&scratch[1..]).chain(col.dirty).copied()
        .filter(|q|!excluded.contains(q)&&seen.insert(*q)).collect();
    if let Some(cp)=b0{
        // The schedule's B0 source envelope is28 although the terminal
        // arithmetic remainder bound KD is26. Preserve that full public
        // envelope; it only needs to fit the counter-free Q prefix below.
        assert!(cp.sz==(0,0)&&cp.dn&&cp.m<=114&&cp.emax<=31);
        let par=super::frogdrop::MapPar{clo:257-cp.smax.1,chi:257-cp.smax.0,
            m:128,tail:cp.tail,emax:cp.emax};
        // Every original row/tail remains in the full128-bit target
        // envelope. Only the proved-zero source suffix is represented by
        // source_bound, as in every ordinary direct map.
        let old_booth=b.allow_booth;b.allow_booth=false;
        let tape=super::frogdrop::direct_map::stage_record(b,col.ring,&col.q[..114],
            &col.meta.y,&scratch,col.phase,&par,cp.m,&dirty);
        b.allow_booth=old_booth;
        // C is globally0 here and excluded from the whole stage; retain
        // the exact parity-corrected B0 flag there. PH is globally1 and
        // becomes a clean replay helper only for the complete map tape.
        b0_flag(b,col,r.tag,&dirty);
        b.x(col.phase);b.play_ctrl(&tape,r.tag,col.phase);b.x(col.phase);
        b0_flag(b,col,r.tag,&dirty);
        // New top is1 on both A0 and mapped B0, hence E0 directly. The
        // map's inverse entry has already returned every scratch owner.
    }
    if let Some(p)=col.compact{
        let(layout,entry)=super::fixed_epoch::endpoint_entry_record(b,col.meta,r,
            col.q,col.phase,col.ring);
        let raw=Fd{ring:col.ring.to_vec(),q:col.q.to_vec(),sy:layout.raw_y.to_vec(),
            sx:layout.sx.to_vec(),ph:col.phase,cnt:col.q[121..128].to_vec()};
        let mut sc=ColScr::carve_col(&layout.pool,&layout.sx,col.dirty,
            last.kp,last.qb,last.tail,false);
        sc.sz=layout.raw_z.to_vec();
        // Explicit independent raw-Z ports are returned by pl_end. SX7
        // remains a complete probe/digit bank, never a size/carry alias.
        let payload=super::pointadd_frogdrop::pl_col(p,&raw,&layout.pool);
        b.play(&entry,false);
        super::payload::pl_end(b,&raw,last,&sc,&payload);
        b.play(&entry,true);
    }
}
