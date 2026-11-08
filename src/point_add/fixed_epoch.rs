//! SOURCE-ONLY relabel reserve; not registered, compiled, or emitted.
//!
//! E7 + S5 + four roles have the SAME sixteen physical owners as the
//! existing joint fixed adapter's SY5 + pool4 + SX7.  At a complete fixed
//! middle boundary Q is unparked Y (or the inherited DONE R/1).  Put the
//! two high bits of raw Y in the old three-owner Q suffix, leaving its
//! third lane zero.  The returned E5/E6 become the two missing SX roles.
//! This is an ABI adapter, not an implementation of the middle body.
//!
//! Body must retain fixed QB23/head24/TC32, original comparator family,
//! complete V pairs, the suffix exclusions, and the supplied R remapping.
//! In particular, this must NOT enable the old global joint-size switch.

use super::builder::{B,G};
use super::mask::mc_xor;
use super::outer_size::Roles;
use super::sum_size::SumSize;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

#[derive(Clone,Copy)]
pub(crate) struct FixedColumn {
    pub column: usize,
    pub y_hi: usize,
    pub z_lo: usize,
    pub hr: bool,
    pub ht: bool,
    pub done_possible: bool,
    pub counter_max: usize,
    /// All four flags must be false.  This rejects first-HT/DQ/tagged care.
    pub sw: bool,
    pub psw: bool,
    pub dl: bool,
    pub dq: bool,
}

#[derive(Clone)]
pub(crate) struct FixedRawLayout {
    pub raw_y: [QubitId;8],
    pub pool: [QubitId;4],
    /// SX3 remains the zero/predicate role; SX4 is code bit4, NOT scratch.
    pub sx: [QubitId;7],
    pub sum: [QubitId;5],
    pub reserved_size: [QubitId;3],
    pub held_done: Option<QubitId>,
    pub counter_passengers: Vec<QubitId>,
    pub reciprocal_loans: Vec<QubitId>,
    pub repark: Vec<Repark>,
    /// Direct architecture retains counter121..127 throughout all columns.
    pub q_data_end: usize,
    pub fixed_r_extra_index: usize,
}

#[derive(Clone)]
pub(crate) struct Repark {
    pub quotient_bit: usize,
    pub source: QubitId,
    pub target: QubitId,
    /// Swap under sum < code_limit.  Also require !held_done when present.
    pub code_limit: usize,
}

impl FixedRawLayout {
    /// Apply to EVERY old fixed R occurrence, not just its first capture.
    pub(crate) fn reciprocal_owner(&self,q:&[QubitId],old:QubitId)->QubitId {
        for (i,index) in [120usize,121,122].into_iter().enumerate() {
            if old==q[index] && self.reserved_size.contains(&old) {
                assert!(self.reciprocal_loans.len()==9);
                return self.reciprocal_loans[6+i];
            }
        }
        old
    }

    /// Clean thresholds, unpark banks, payload top/adjacent saves and all
    /// ordinary Q loans must exclude this COMPLETE set.  The R engine may
    /// explicitly use reciprocal_loans; it may not silently change family
    /// from the parent's TTK comparator to a clean comparator on DONE data.
    pub(crate) fn reserved_q(&self)->BTreeSet<QubitId> {
        self.reserved_size.iter().chain(&self.reciprocal_loans)
            .chain(&self.counter_passengers).copied().chain(self.held_done).collect()
    }
}

fn bank(meta:&SumSize,roles:Roles,q:&[QubitId],phase:QubitId,dirty:&[QubitId])
    ->Vec<QubitId> {
    assert_eq!(q.len(),128);
    let mut used:BTreeSet<_>=meta.y.iter().chain(&meta.sum).copied().collect();
    assert_eq!(used.len(),12);
    for x in [roles.tag,roles.cut,roles.toggle,roles.prefix,phase] {
        assert!(used.insert(x));
    }
    for &x in q {assert!(used.insert(x));}
    let result:Vec<_>=dirty.iter().copied().filter(|x|used.insert(*x)).collect();
    // Use ring donors: neither the entry arithmetic nor D reads ring/P.
    assert!(result.len()>=12,"fixed adapter requires twelve external restored dirty donors");
    result
}

fn done_toggle(b:&mut B,q:&[QubitId],dirty:&[QubitId]) {
    // On c139 counter bit6 is globally0 at entry.  Low six bits contain
    // the complete counter, so XOR OR into Q127 is exact.  No PH predicate
    // is needed: active counter is zero and DONE counter is nonzero.
    b.x(q[127]);
    let zero:Vec<_>=q[121..127].iter().map(|&x|(x,true)).collect();
    mc_xor(b,&zero,q[127],&[],dirty);
}

/// Capture direct metadata -> raw fixed ABI.  All four role lanes start0;
/// incoming C is absent by the public column guard.  E encodes actual Y,
/// fixed active Y<=y_hi<=96, DONE Y<=26.  Q has no quotient parks yet.
/// The suffix is globally0 after the explicit c139 counter transport.
///
/// Play forward, run ONE COMPLETE fixed middle, then play this tape
/// backwards.  The body returns raw_y, S, all SX roles, counter passengers,
/// and held_done before the inverse.  Its ring/Q-low/payload changes may
/// persist: arbitrary ring donors are exactly restored within each gate
/// helper, so entry inverse does not require their old values.
pub(crate) fn entry_record(b:&mut B,meta:&SumSize,roles:Roles,q:&[QubitId],
    phase:QubitId,col:FixedColumn,dirty:&[QubitId])->(FixedRawLayout,Vec<G>) {
    assert!((col.hr||col.ht)&&!(col.sw||col.psw||col.dl||col.dq));
    assert!((28..=96).contains(&col.y_hi));
    let d=bank(meta,roles,q,phase,dirty);
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
    let layout=FixedRawLayout{
        raw_y:[meta.y[0],meta.y[1],meta.y[2],meta.y[3],meta.y[4],
            reserved_size[0],reserved_size[1],reserved_size[2]],
        pool:[meta.sum[0],meta.sum[1],meta.sum[2],meta.sum[3]],
        sx:[roles.cut,roles.toggle,roles.prefix,roles.tag,
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

#[derive(Clone)]
pub(crate) struct EndpointLayout {
    pub raw_y:[QubitId;8],
    pub sx:[QubitId;7],
    pub pool:[QubitId;4],
    pub raw_z:[QubitId;8],
    pub qmap_end:usize,
    pub replay_helper:QubitId,
    pub b0_flag:QubitId,
    pub tz:QubitId,
    pub payload_extra:QubitId,
    pub sum_ninth:QubitId,
}

/// Endpoint input: all shots DONE, Q=R<2^26, S/fourroles zero, E=Y-1
/// with Y=1 (A0) or bl(R)<=26 (B0).  Q121..127 remains the full counter.
/// Return raw descriptors for the inherited B0-map and P258 endpoint.
/// The captured inverse is played only after the endpoint has returned
/// raw Y=1, PH=1 and all described scratch zero.  It then returns E=0.
/// B0 arithmetic is limited to Q[..114]; Q113 is borrowed as payload only
/// AFTER that map is complete, never concurrently with its data prefix.
pub(crate) fn endpoint_entry_record(b:&mut B,meta:&SumSize,roles:Roles,
    q:&[QubitId],phase:QubitId,dirty:&[QubitId])->(EndpointLayout,Vec<G>) {
    let d=bank(meta,roles,q,phase,dirty);
    let high=[q[114],q[115],q[116]];
    let layout=EndpointLayout{
        raw_y:[meta.y[0],meta.y[1],meta.y[2],meta.y[3],meta.y[4],high[0],high[1],high[2]],
        sx:[roles.cut,roles.toggle,roles.prefix,roles.tag,meta.sum[4],meta.y[5],meta.y[6]],
        pool:[meta.sum[0],meta.sum[1],meta.sum[2],meta.sum[3]],
        raw_z:[meta.sum[0],meta.sum[1],meta.sum[2],meta.sum[3],q[112],q[109],q[110],q[111]],
        qmap_end:114,replay_helper:q[117],b0_flag:q[118],tz:q[119],
        payload_extra:q[113],sum_ninth:q[117],
    };
    b.begin();
    super::frogdrop::add_const_dirty_exact(b,&meta.y,1,&d);
    for i in 0..2 {b.cx(meta.y[5+i],high[i]);b.cx(high[i],meta.y[5+i]);}
    (layout,b.end())
}
