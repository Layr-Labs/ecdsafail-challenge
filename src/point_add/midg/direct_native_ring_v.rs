//! SOURCE-ONLY P1 V with normalized ring and RAW Q throughout.
//! Paid window33; the original head32 and raw Q0..30 / low-Y
//! Q64..94 catalyst are unchanged.
//! Only the ring coordinate is composed with the common DOWN(128-Y)
//! frame: the exact active head frame is now DOWN(98+S). All four V
//! occurrences use this one identical tape, including inactive shots.

use super::{B,G,S1,S1Gate,S1_GATE,S1_NOACT,S1_TIER,CROSS_TC};
use super::super::sum_size::SumSize;
use super::super::{frogdrop,mask::mc_xor};
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn rec(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}

/// Entry e=mask=0 globally. Ring is raw DOWN(128-Y); Q is fully raw,
/// including its original quotient/counter passengers and raw x128.
/// Keep the exact inherited catalyst value: returning a different dirty
/// word would NOT preserve the B12A rounding bit. Small Y uses the same
/// original Q0..30/Q64..94 swap. The complete tape returns its helpers.
pub(crate) fn record(b:&mut B,meta:&SumSize,ring:&[QubitId],q:&[QubitId],
    activity:QubitId,flight:QubitId,mask:QubitId,phase:QubitId,x128:QubitId,
    zrange:(usize,usize),dirty:&[QubitId])->Vec<G>{
    record_impl(b,meta,ring,q,activity,flight,Some(mask),phase,x128,zrange,dirty)
}

/// Three-role normalized-ring adapter. Only flight is clean; activity,
/// phase, x128, and every quotient passenger retain their original value.
/// No sixth threshold bit remains latched across the reciprocal core.
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
    // S=Z+Y-226, delta=128-Y: Z-delta=98+S. The full queried
    // support is paid window0..32 plus unchanged head225..256 (including shared zero).
    // The existing partial permutation maps ALL these lanes exactly for
    // every S0..31; its captured inverse returns every other arbitrary
    // lane. Body uses outside lanes only as exactly restored dirty donors.
    let support:BTreeSet<_>=(0..CROSS_TC).chain(225..257).collect();
    let frame=rec(b,|b|frogdrop::rot_by_off_care(
        b,ring,&meta.sum,98,129,true,&support));
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
        Some(carry)=>S1Gate::DirectLatched{size:meta.clone(),carry},
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
    // Only the baseline retains a sixth sum bit across the core. The
    // three-role path returns original metadata after every threshold.
    let threshold=match mask{
        Some(carry) if zrange.1+CROSS_TC-1>=257=>
            super::super::direct_frame::v_gate_prepare_record(b,meta,carry,&whole_dirty),
        _=>vec![],
    };
    let core=rec(b,|b|{
        b.play(&threshold,false);
        b.play(&fv,false);b.play(&fr,true);b.play(&convert,false);
        b.play(&fr,false);b.play(&fv,true);b.play(&convert,true);
        b.play(&threshold,true);
    });
    rec(b,|b|{
        b.play(&frame,false);b.play(&gap,false);
        b.play(&low,false);b.play(&swap,false);b.play(&low,true);
        b.play(&core,false);
        b.play(&low,false);b.play(&swap,true);b.play(&low,true);
        b.play(&gap,true);b.play(&frame,true);
    })
}
