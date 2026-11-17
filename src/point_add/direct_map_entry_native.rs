//! SOURCE-ONLY native NAND entry for the full128 mixed map.
//! Intended sibling of frogdrop::direct_map and frogdrop::binary_msb.
//! No registration, workspace integration, build or circuit execution.
use super::super::builder::{B,G};
use super::super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

fn capture(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn bank(universe:&[QubitId],held:&[QubitId])->Vec<QubitId>{
    let mut seen=BTreeSet::new();universe.iter().copied()
        .filter(|q|!held.contains(q)&&seen.insert(*q)).collect()
}
fn xor(b:&mut B,ctrl:&[(QubitId,bool)],out:QubitId,universe:&[QubitId]){
    let held:Vec<_>=ctrl.iter().map(|v|v.0).chain([out]).collect();
    let dirty=bank(universe,&held);
    assert!(dirty.len()>=ctrl.len().saturating_sub(2));
    mc_xor(b,ctrl,out,&[],&dirty);
}
/// out ^= AND(ctrl) & !(ph & c), with immutable ph/c outside all donors.
/// The two minterms are XORed; no clean prefix or measured AND is used.
fn xor_active(b:&mut B,ctrl:&[(QubitId,bool)],out:QubitId,
    ph:QubitId,c:QubitId,universe:&[QubitId]){
    assert!(ctrl.iter().all(|x|x.0!=ph&&x.0!=c));
    assert!(out!=ph&&out!=c);
    xor(b,ctrl,out,universe);
    let mut off=ctrl.to_vec();off.extend([(ph,false),(c,false)]);
    xor(b,&off,out,universe);
}
fn cubes(mut lo:usize,hi:usize,mut f:impl FnMut(usize,usize)){
    assert!(lo<=hi&&hi<=128);
    while lo<hi{
        let a=if lo==0{7}else{lo.trailing_zeros()as usize};
        let r=(usize::BITS-1-(hi-lo).leading_zeros())as usize;
        let free=a.min(r).min(7);f(lo,free);lo+=1usize<<free;
    }
}
/// Exact TTK carry oracle. The ladder is unconditional; only its two
/// writes to the returned flag are NAND-controlled. All operands restore
/// for arbitrary input, including inactive M=0 and arbitrary old y.
fn carry_active(b:&mut B,a:&[QubitId],t:&[QubitId],out:QubitId,
    ph:QubitId,c:QubitId,dirty:&[QubitId]){
    assert_eq!(a.len(),7);assert_eq!(t.len(),7);
    let first=capture(b,|b|for i in 1..7{b.cx(a[i],t[i]);});
    b.play(&first,false);
    xor_active(b,&[(a[6],false)],out,ph,c,dirty);
    let ladder=capture(b,|b|{
        for i in(1..6).rev(){b.cx(a[i],a[i+1]);}
        for i in 0..6{b.ccx(t[i],a[i],a[i+1]);}
    });
    b.play(&ladder,false);
    xor_active(b,&[(a[6],false),(t[6],false)],out,ph,c,dirty);
    b.play(&ladder,true);b.play(&first,true);
}

/// Ring priority probe with gate q0 & !(ph & c).
/// On the true gate, out starts0 and has exactly the inherited cut domain.
/// On the false gate, arbitrary out/ring/M is unchanged and tmp returns0.
/// This is a care-clean probe, NOT an all-out self-inverse oracle; callers
/// erase a computed result by replaying this exact literal tape backwards.
fn ring_probe(b:&mut B,ring:&[QubitId],q0:QubitId,out:&[QubitId],
    mword:&[QubitId],tmp:QubitId,ph:QubitId,c:QubitId,dirty:&[QubitId]){
    b.x(tmp);xor_active(b,&[(q0,false)],tmp,ph,c,dirty); // !gate
    for value in(1usize..128).rev(){
        let pivot=value.trailing_zeros()as usize;
        b.x(tmp);
        cubes(value,128,|at,free|{
            let mut ctl=vec![(tmp,false),(ring[256-value],false)];
            ctl.extend((free..7).map(|i|(mword[i],at>>i&1==0)));
            xor(b,&ctl,out[pivot],dirty);
        });
        for(i,&q)in out.iter().enumerate(){
            if i!=pivot&&value>>i&1!=0{b.ccx(tmp,out[pivot],q);}
        }
        b.x(tmp);
        let mut eq=vec![(q0,false)];
        eq.extend(out.iter().enumerate().map(|(i,&q)|(q,value>>i&1==0)));
        xor_active(b,&eq,tmp,ph,c,dirty);
    }
    b.x(tmp);
    let eq:Vec<_>=std::iter::once((q0,false))
        .chain(out.iter().map(|&q|(q,true))).collect();
    xor_active(b,&eq,tmp,ph,c,dirty);
}

/// Full128 entry U_A, captured once for both directions.
/// Entry: mword=0, helper=0; y=bl(top)-1; A=!(ph&c).
/// On A, Q/top are positive and their complete public128 domains satisfy
/// the inherited nonoverlapping-top support. Exit is old entry exactly:
/// y=0, mword=max(bl(Q),bl(top))-1, helper=0, ordered/rotated values as old U.
/// On !A, arbitrary ring/Q/y is unchanged and mword/helper stay0.
/// Thus the caller may then D-swap y and mword, execute the native core,
/// D-swap back and replay this SAME record inversely. PH/C never change.
#[allow(clippy::too_many_arguments)]
pub(crate) fn record(b:&mut B,ring:&[QubitId],q:&[QubitId],y:&[QubitId],
    mword:&[QubitId],helper:QubitId,ph:QubitId,c:QubitId,dirty:&[QubitId])->Vec<G>{
    assert_eq!((ring.len(),q.len(),y.len(),mword.len()),(257,128,7,7));
    let ports:Vec<_>=ring.iter().chain(q).chain(y).chain(mword).copied()
        .chain([helper,ph,c]).collect();
    assert_eq!(ports.len(),ports.iter().collect::<BTreeSet<_>>().len());
    // No global extra clean owner. Every primitive filters live controls
    // and target from this arbitrary, returned universe.
    let universe=bank(dirty,&[ph,c]);
    capture(b,|b|{
        xor_active(b,&[],helper,ph,c,&universe); // held A
        let max=super::binary_msb::record(b,q,mword,Some((helper,false)),&universe);
        b.play(&max,false);
        xor_active(b,&[],helper,ph,c,&universe);

        for &x in mword{b.x(x);}
        carry_active(b,mword,y,helper,ph,c,&universe);
        for &x in mword{b.x(x);}
        for i in 0..7{b.cswap(helper,mword[i],y[i]);}

        // M=0 on !A, so both plain rotations are exact identities there.
        let rot=capture(b,|b|super::rot_by_range(b,q,mword,0,127,false,&bank(&universe,mword)));
        b.play(&rot,true);
        xor_active(b,&[(q[0],true)],helper,ph,c,&universe);

        // Preserve inherited controlled subtraction. On !A its addend M
        // is zero; the complete arithmetic is identity for arbitrary y.
        let translate=capture(b,|b|{
            b.x(q[0]);
            let add=capture(b,|b|super::super::arith::ttk_add(b,mword,y,Some(q[0]),None));
            b.play(&add,true);
            b.x(q[0]); // q.len()%128=0: no constant correction
        });
        b.play(&translate,false);

        let min=capture(b,|b|{
            xor_active(b,&[(q[0],true)],helper,ph,c,&universe);
            let r=super::binary_msb::record(b,q,y,Some((helper,false)),&universe);
            b.play(&r,false);
            xor_active(b,&[(q[0],true)],helper,ph,c,&universe);
        });
        b.play(&min,true);
        let rmin=capture(b,|b|ring_probe(b,ring,q[0],y,mword,helper,ph,c,&universe));
        b.play(&rmin,true);
        b.play(&rot,false);
    })
}
