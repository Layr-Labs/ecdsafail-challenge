//! SOURCE-ONLY child of midg. Complete P1 head32 / paid Cross window33 pair,
//! with direct E/S addressing. The baseline uses two returned helpers;
//! record_three returns the same tape contract with only flight clean.
//! The pair is unconditional as in the qualified route-free P1 source;
//! no phase/activity/parked-x128 owner participates in its internals.

use super::{B,G,S1,S1Gate,S1_GATE,S1_NOACT,S1_TIER,CROSS_TC};
use super::super::sum_size::SumSize;
use super::super::{direct_frame,mask::mc_xor};
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}

/// Entry e=mask=0 globally. Q[Y..128] and x128 may contain quotient
/// passengers. Small Y is protected by the inherited Q0..30/Q64..94
/// swap. It returns before any caller reads Q; every R lane is dirty data.
pub(crate) fn record(b:&mut B,meta:&SumSize,ring:&[QubitId],q:&[QubitId],
    activity:QubitId,flight:QubitId,mask:QubitId,phase:QubitId,x128:QubitId,
    zrange:(usize,usize),dirty:&[QubitId])->Vec<G>{
    record_impl(b,meta,ring,q,activity,flight,Some(mask),phase,x128,zrange,dirty)
}

/// Three-role Cross adapter: activity and x128 are arbitrary passengers;
/// flight alone starts/returns zero. Its frame, catalyst-swap flag, and
/// reciprocal comparator lifetimes are disjoint. No mask port is aliased
/// or allocated; direct threshold queries use only restored dirty donors.
pub(crate) fn record_three(b:&mut B,meta:&SumSize,ring:&[QubitId],q:&[QubitId],
    activity:QubitId,flight:QubitId,phase:QubitId,x128:QubitId,
    zrange:(usize,usize),dirty:&[QubitId])->Vec<G>{
    record_impl(b,meta,ring,q,activity,flight,None,phase,x128,zrange,dirty)
}

fn record_impl(b:&mut B,meta:&SumSize,ring:&[QubitId],q:&[QubitId],
    activity:QubitId,flight:QubitId,mask:Option<QubitId>,phase:QubitId,x128:QubitId,
    zrange:(usize,usize),dirty:&[QubitId])->Vec<G>{
    assert_eq!((ring.len(),q.len()),(257,128));
    assert_eq!(CROSS_TC,33);
    assert!(98<=zrange.0&&zrange.0<=zrange.1&&zrange.1<=256);
    let mut seen=BTreeSet::new();
    assert!(ring.iter().chain(q).chain(&meta.y).chain(&meta.sum).copied()
        .chain([activity,flight,phase,x128]).chain(mask).all(|a|seen.insert(a)));
    let excluded:BTreeSet<_>=meta.y.iter().chain(&meta.sum).copied()
        .chain([activity,flight,phase,x128]).chain(mask).collect();
    let mut seen=BTreeSet::new();
    let whole_dirty:Vec<_>=dirty.iter().chain(ring).chain(q).copied()
        .filter(|a|!excluded.contains(a)&&seen.insert(*a)).collect();
    let support:BTreeSet<_>=(0..CROSS_TC).chain(225..257).collect();
    // rotate_z_record returns its flag before low/catalyst or reciprocal
    // work begins; inverse frame is likewise entered only after flight=0.
    let frame=direct_frame::rotate_z_record(b,meta,ring,mask.unwrap_or(flight),
        zrange,Some(&support),true,&whole_dirty);
    let low=rec(b,|b|{
        // Y<=31 iff E<31: dyadic prefix decomposition of [0,31).
        for bit in(0..5).rev(){
            let mut c=vec![(meta.y[5],true),(meta.y[6],true),(meta.y[bit],true)];
            c.extend(((bit+1)..5).map(|h|(meta.y[h],false)));
            mc_xor(b,&c,flight,&[],&whole_dirty);
        }
    });
    let swap=rec(b,|b|for i in 0..31{b.cswap(flight,q[i],q[64+i]);});
    let gap=rec(b,|b|for &a in &meta.sum{b.x(a);});
    let zero=ring[256];
    let zh=ring[225..257].to_vec();
    let win:Vec<_>=std::iter::once(zero).chain(ring[..CROSS_TC].iter().copied()).collect();
    let r:Vec<_>=q[..31].iter().copied().chain([zero]).collect();
    let occupied:BTreeSet<_>=r.iter().chain(&zh).chain(&win).copied()
        .chain(excluded.iter().copied()).collect();
    let core_dirty:Vec<_>=whole_dirty.iter().copied().filter(|a|!occupied.contains(a)).collect();
    assert!(core_dirty.len()>=40);
    let s=S1{r,f:zero,zero,sgn:zero,gt:vec![flight],anc:vec![],andc:vec![flight],
        chain:vec![],dirty:core_dirty};
    // Explicit one-clean-owner family. The two missing cached products
    // cost three more CCX/comparator; they are NOT silently borrowed.
    let gate=match mask{
        Some(carry)=>S1Gate::Direct{size:meta.clone(),carry},
        None=>S1Gate::DirectNoCarry{size:meta.clone()},
    };
    let old_gate=S1_GATE.with(|g|g.replace(gate));
    let old_noact=S1_NOACT.with(|g|g.replace(true));
    assert!(S1_TIER.with(|g|g.get()).is_none());
    let fv=super::stage1_v_window(b,&zh,&win,&meta.sum,zrange,&s,activity,true,Some(flight),CROSS_TC);
    let fr=super::stage1_v_window(b,&zh,&win,&meta.sum,zrange,&s,activity,false,Some(flight),CROSS_TC);
    S1_NOACT.with(|g|g.set(old_noact));S1_GATE.with(|g|*g.borrow_mut()=old_gate);
    let convert=rec(b,|b|{
        for &a in &s.r{b.x(a);}
        super::b12a_add_virtual_endpoints(b,&zh,&s.r);
        for &a in &s.r[..31]{b.x(a);}
    });
    let core=rec(b,|b|{
        b.play(&fv,false);b.play(&fr,true);b.play(&convert,false);
        b.play(&fr,false);b.play(&fv,true);b.play(&convert,true);
    });
    rec(b,|b|{
        b.play(&frame,false);b.play(&gap,false);
        b.play(&low,false);b.play(&swap,false);b.play(&low,true);
        b.play(&core,false);
        b.play(&low,false);b.play(&swap,true);b.play(&low,true);
        b.play(&gap,true);b.play(&frame,true);
    })
}
