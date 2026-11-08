//! Three-role fixed ABI. Original fixed comparator/head policy is retained.
//! q[Yhi] replaces SX2 for the COMPLETE middle. It lies below every fixed
//! quotient park (Yhi+1+k), below reserved raw-size/R suffix owners, and
//! above active Q data and every inherited DONE remainder. Column139's
//! counter passengers and held DONE retain their exact original transport.
use super::builder::{B,G};
use super::c659_column::Column;
use super::fixed_epoch::{FixedColumn,FixedRawLayout,Repark};
use super::frogdrop_col::ColPar;
use super::sum_size::SumSize;
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;
fn transport_bank(meta:&SumSize,roles:super::c659::Roles,q:&[QubitId],phase:QubitId,dirty:&[QubitId])->Vec<QubitId>{
 assert_eq!(q.len(),128);let mut used:BTreeSet<_>=meta.y.iter().chain(&meta.sum).copied().collect();
 assert_eq!(used.len(),12);for p in [roles.tag,roles.cut,roles.toggle.port(),phase].into_iter().filter(|q|super::c659::retained(*q)){assert!(used.insert(p));}
 for &p in q{assert!(used.insert(p));}
 let d:Vec<_>=dirty.iter().copied().filter(|p|used.insert(*p)).collect();assert!(d.len()>=12);d
}
fn done_toggle(b:&mut B,q:&[QubitId],dirty:&[QubitId]) {
    // On c139 counter bit6 is globally0 at entry.  Low six bits contain
    // the complete counter, so XOR OR into Q127 is exact.  No PH predicate
    // is needed: active counter is zero and DONE counter is nonzero.
    b.x(q[127]);
    let zero:Vec<_>=q[121..127].iter().map(|&x|(x,true)).collect();
    mc_xor(b,&zero,q[127],&[],dirty);
}

/// Capture direct metadata -> raw fixed ABI.  The three role lanes and Q[Yhi] start0;
/// incoming C is absent by the public column guard.  E encodes actual Y,
/// fixed active Y<=y_hi<=96, DONE Y<=26.  Q has no quotient parks yet.
/// The suffix is globally0 after the explicit c139 counter transport.
///
/// Play forward, run ONE COMPLETE fixed middle, then play this tape
/// backwards.  The body returns raw_y, S, all SX roles, counter passengers,
/// and held_done before the inverse.  Its ring/Q-low/payload changes may
/// persist: arbitrary ring donors are exactly restored within each gate
/// helper, so entry inverse does not require their old values.
fn entry_record(b:&mut B,meta:&SumSize,roles:super::c659::Roles,q:&[QubitId],
    phase:QubitId,col:FixedColumn,dirty:&[QubitId],host_sx1:bool)->(FixedRawLayout,Vec<G>) {
    assert!((col.hr||col.ht)&&!(col.sw||col.psw||col.dl||col.dq));
    assert!((28..=96).contains(&col.y_hi));
    let d=transport_bank(meta,roles,q,phase,dirty);
    let loan=q[col.y_hi]; // Q[Yhi] is zero before any quotient park; DONE R<2^26, Yhi>=28.
    let hi=col.y_hi;
    let special=col.column==139;
    if special {
        assert!(col.ht&&!col.hr&&col.done_possible&&hi==96&&col.counter_max<64);
    } else {
        assert!(!col.done_possible||hi+26<121,
            "a persistent raw-size owner must not alias a live counter bit");
    }
    let reserved_size=[q[hi+24],q[hi+25],q[hi+26]];
    let mut repark=vec![];
    let reciprocal_loans=if hi<=87 {
        assert!(hi+32<120);
        q[hi+27..hi+33].to_vec()
    } else {
        let first=if hi>=94 {14}else{17};
        let offset=if hi>=94 {13}else{16};
        assert!(col.z_lo+hi>=if hi>=94 {244}else{241});
        for k in first..23 {
            let target=hi+offset-k;
            assert!(target>=26&&target<hi&&hi+1+k<120);
            repark.push(Repark{quotient_bit:k,source:q[hi+1+k],
                target:q[target],code_limit:32-k});
        }
        let mut r:Vec<_>=(17..23).map(|k|q[hi+1+k]).collect();
        if hi>=94 {r.extend((14..17).map(|k|q[hi+1+k]));}
        r
    };
    assert!(!reciprocal_loans.iter().any(|x|reserved_size.contains(x)));
    if host_sx1 {
        // c1: Y<=39 and DONE is absent. Q101 is zero at entry and excluded
        // from the fixed middle's entire scratch bank while SX1 is live.
        assert_eq!((col.column,col.y_hi,col.done_possible),(1,39,false));
        assert!(!reserved_size.contains(&q[101])
            && !reciprocal_loans.contains(&q[101]));
    }
    let layout=FixedRawLayout{
        raw_y:[meta.y[0],meta.y[1],meta.y[2],meta.y[3],meta.y[4],
            reserved_size[0],reserved_size[1],reserved_size[2]],
        pool:[meta.sum[0],meta.sum[1],meta.sum[2],meta.sum[3]],
        sx:[roles.cut,if host_sx1{q[101]}else{roles.toggle.lane()},loan,roles.tag,
            meta.sum[4],meta.y[5],meta.y[6]],
        sum:meta.sum,reserved_size,
        held_done:special.then_some(q[127]),
        counter_passengers:if special {vec![q[118],q[119]]}else{vec![]},
        reciprocal_loans,repark,q_data_end:121,fixed_r_extra_index:120,
    };
    b.begin();
    if special {
        done_toggle(b,q,&d);
        for (from,to) in [(q[121],q[118]),(q[122],q[119])] {
            b.cx(from,to);b.cx(to,from);
        }
    }
    // E+1 is raw Y: fixed Y<=96/DONE<=26 never wraps the seven-bit word.
    super::frogdrop::add_const_dirty_exact(b,&meta.y,1,&d);
    for i in 0..2 {
        b.cx(meta.y[5+i],reserved_size[i]);
        b.cx(reserved_size[i],meta.y[5+i]);
    }
    // reserved_size[2] is raw Y's globally-zero eighth bit.  No transfer
    // from a non-existent E7 is emitted, and E5/E6 now start globally0.
    (layout,b.end())
}

pub(crate) fn run(b:&mut B,col:&Column<'_>,cp:&ColPar){
 assert!(!cp.nomap&&(!cp.hr||cp.tt)&&cp.sy.1<=96&&!(cp.sw||cp.psw||cp.dl||cp.dq));
 let descriptor=FixedColumn{column:cp.col,y_hi:cp.sy.1,z_lo:cp.sz.0,hr:cp.hr,ht:cp.ht,
 done_possible:cp.dn,counter_max:cp.cntmax,sw:cp.sw,psw:cp.psw,dl:cp.dl,dq:cp.dq};
 let host_sx1=std::env::var("C658_WP4").as_deref()==Ok("1")
     &&std::env::var("C658_WP4_C1").as_deref()!=Ok("0")
     &&cp.col==1&&col.compact.is_some();
 let(entry,transport)=entry_record(b,col.meta,col.roles,col.q,col.phase,descriptor,col.ring,host_sx1);
 assert_eq!(entry.sx[2],col.q[cp.sy.1]);
 assert!(!entry.reserved_q().contains(&entry.sx[2]));
 super::midg::direct_fixed_middle::run_three(b,col,cp,entry,&transport);
}
