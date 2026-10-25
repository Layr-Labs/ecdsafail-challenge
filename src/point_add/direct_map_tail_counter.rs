//! Direct E7/S5 complete stages11..15. Source only; no allocation or dispatch.
//! The map/tail reuse S5 and the three returned scalar owners as eight zero
//! ports. C stays on tag, E stays size-minus1, PH stays outside the map.
use super::builder::B;
use super::direct_column::Column;
use super::frogdrop_col::ColPar;
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn xor(b:&mut B,c:&[(QubitId,bool)],t:QubitId,clean:&[QubitId],universe:&[QubitId]){
    assert!(!c.iter().any(|q|q.0==t));
    let mut seen=BTreeSet::new();
    let d:Vec<_>=universe.iter().copied().filter(|q|*q!=t&&!clean.contains(q)
        &&!c.iter().any(|p|p.0==*q)&&seen.insert(*q)).collect();
    mc_xor(b,c,t,clean,&d);
}

/// Same RA64 predicate as the qualified parent, with the complete physical
/// counter always at Q121..127. No predicate is read inside a map frame.
fn done(b:&mut B,col:&Column<'_>,target:QubitId,extra:&[(QubitId,bool)],bank:&[QubitId]){
    let mut base=vec![(col.phase,false)];
    base.extend(col.q[64..121].iter().map(|&q|(q,true)));
    for &(q,n) in extra{
        if let Some(old)=base.iter().find(|x|x.0==q){if old.1!=n{return;}}
        else{base.push((q,n));}
    }
    xor(b,&base,target,&[],bank);
    base.extend(col.q[121..128].iter().map(|&q|(q,true)));
    xor(b,&base,target,&[],bank);
}

/// This must also supply MAP_CTRL_S before the special B0 endpoint, because
/// its map-parity correction depends on the actual skipped columns.
pub(crate) fn controlled(cp:&ColPar)->bool{
    !cp.nomap&&cp.sz!=(0,0)&&cp.dn&&cp.m>121
}

/// Entry after stage10: E=top size-1, S=0, tag=C, three other roles0.
/// Exit: tagged E if C, phase updated, counter incremented exactly once.
pub(crate) fn finish(b:&mut B,col:&Column<'_>,cp:&ColPar){
    assert!(!cp.nomap&&cp.sz!=(0,0));
    assert_eq!((cp.n,cp.nq,col.q.len(),col.ring.len()),(257,128,128,257));
    assert!((2..=128).contains(&cp.m)&&cp.emax<=31);
    let r=col.roles;
    let scratch:Vec<_>=std::iter::once(r.tag).chain(col.meta.sum.iter().copied())
        .chain([r.cut,r.toggle,r.prefix]).collect();
    assert_eq!(scratch.len(),9);
    let mut held:BTreeSet<_>=[col.phase,r.tag].into_iter().collect();
    if let Some(p)=col.compact{held.extend(p.iter().copied());}
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=col.ring.iter().chain(col.q).chain(&col.meta.y)
        .chain(&scratch[1..]).chain(col.dirty).copied()
        .filter(|q|!held.contains(q)&&seen.insert(*q)).collect();
    let par=super::frogdrop::MapPar{clo:cp.n-cp.smax.1,chi:cp.n-cp.smax.0,
        m:if cp.dn{128}else{cp.m},tail:cp.tail,emax:cp.emax};
    // Public pure-HT makes PH a global one; map replay borrows it only after
    // an explicit X and returns it before the second derived-DONE query.
    let pure_ht=cp.ht&&!cp.hr&&!cp.sw&&!cp.dl&&!cp.dq;
    super::frogdrop::direct_map::apply_stage_with_loans(b,col.ring,col.q,&col.meta.y,
        &scratch,col.phase,&par,cp.m,cp.dn,pure_ht,&bank,col.clean_external,
        |b,target,donors|done(b,col,target,&[],donors));
    if cp.sw||cp.dl{
        assert!(cp.sw,"delayed C uses the complete public switching-tail envelope");
        let par=super::frogdrop::direct_tail::TailPar{l0:cp.l0,qb:cp.qb,
            szlo:cp.sz.0,sylo:cp.sy.0,swl_hi:cp.swl.1,m:cp.m};
        super::frogdrop::direct_tail::apply(b,col.ring,col.q,&col.meta.y,
            &scratch,col.phase,&par,false,&bank);
    }
    counter(b,col,cp,&bank);
}

/// S5 is zero after the complete tail. Its five lanes plus toggle supply
/// the six exact increment carries. Neither metadata E nor persistent C
/// is borrowed as clean. No physical counter relocation is used.
fn counter(b:&mut B,col:&Column<'_>,cp:&ColPar,bank:&[QubitId]){
    if !cp.dn&&!cp.fin{return;}
    let r=col.roles;let flag=r.cut;
    let clean:Vec<_>=col.meta.sum.iter().copied().chain([r.toggle]).collect();
    let cnt=&col.q[121..128];
    let sched=super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP);
    let first=sched.cols.iter().position(|c|c.fin).expect("public first finisher");
    assert!(cp.col<sched.cols.len()&&cp.col.saturating_sub(first)+1<128);
    if cp.dn{
        done(b,col,flag,&[(r.tag,true)],bank);
        super::arith::inc(b,flag,cnt,&clean);
        done(b,col,flag,&[(r.tag,true)],bank);
    }
    if cp.fin{
        let mut fresh=vec![(col.phase,false),(r.tag,true)];
        fresh.extend(col.meta.y.iter().map(|&q|(q,true)));
        // Fresh = PH & Y1 & !C & !DONE, using the unchanged exact parent
        // notion of DONE. Previous counters are now at least2, without wrap.
        xor(b,&fresh,flag,&clean,bank);
        done(b,col,flag,&fresh,bank);
        b.cx(flag,cnt[0]);
        let mut made=fresh;
        made.push((cnt[0],false));made.extend(cnt[1..].iter().map(|&q|(q,true)));
        // Inherited l0=128 lies above the physical data end121, so the
        // old l0..ctop payload-zero clause is empty, exactly as in parent.
        assert_eq!(cp.l0,128);
        xor(b,&made,flag,&clean,bank);
    }
}
