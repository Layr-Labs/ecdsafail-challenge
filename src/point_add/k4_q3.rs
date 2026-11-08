//! K4 U2/U3/U9/U10 sibling. Parent normalized-Q implementation is unchanged.
use super::*;
use super::super::direct_payload::k4_complete::{Roles3, filtered};

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum CarryChoice { QPrefix { first:usize }, GuardedSum, Ttk }

pub(crate) fn carry_choice(first:usize,k:usize)->CarryChoice {
    assert!(first<128&&k<30);
    if first>0 {CarryChoice::QPrefix{first}}
    else if k>=16 {CarryChoice::GuardedSum} else {CarryChoice::Ttk}
}
fn bank3(meta:&SumSize,q:&[QubitId],raw:&[QubitId],r:Roles3,dirty:&[QubitId],forbidden:&[QubitId])->Vec<QubitId>{
    assert_eq!((meta.y.len(),meta.sum.len(),q.len(),raw.len()),(7,5,128,259));
    let ports:Vec<_>=meta.y.iter().chain(&meta.sum).chain(q).chain(raw).copied()
        .chain(r.ports()).collect();
    assert_eq!(ports.len(),ports.iter().copied().collect::<BTreeSet<_>>().len());
    assert!(forbidden.iter().all(|p|!ports.contains(p)));
    let mut held=ports;held.extend(forbidden);let d=filtered(dirty,&held);
    assert!(d.len()>=4);d
}

/// Exact replacement for the controlled subtraction and its selected add-back.
/// Complementing the target under activity turns their net action into one
/// positive add controlled by sign XOR (activity AND the new flight bit).
/// All incoming role, target and source values are allowed.
pub(crate) fn ttk_restoring_record(b:&mut B,q:&[QubitId],t:&[QubitId],r:Roles3,
    _dirty:&[QubitId])->Vec<G>{
    let n = q.len();
    assert!(n >= 2 && t.len() == n + 1);
    let ports: BTreeSet<_> = q.iter().chain(t).copied().chain(r.ports()).collect();
    assert_eq!(ports.len(), n + t.len() + 3);
    let hi = n - 1;
    let top = t[n];
    b.begin();
    for &bit in t { b.cx(r.activity, bit); }

    // Ordinary TTK forward sweep on the n lower bits. If p is the
    // product t[hi]*q[hi] at the apex, the carry out is old_q[hi] XOR p.
    b.cx(q[hi], top);
    for i in 1..n { b.cx(q[i], t[i]); }
    for i in (1..hi).rev() { b.cx(q[i], q[i+1]); }
    for i in 0..hi { b.ccx(t[i], q[i], q[i+1]); }
    b.ccx(t[hi], q[hi], top);

    // The high target is now the true trial-sum high bit used by the
    // reference. The sign owner temporarily contains the selected enable.
    b.ccx(r.activity, top, r.flight);
    b.ccx(r.activity, r.flight, r.sign);
    b.x(r.sign);
    // Drop p from the high target when the add is disabled. q[0] is an
    // arbitrary already-occupied operand restored by these four gates.
    b.ccx(r.sign, q[hi], q[0]); b.ccx(q[0], t[hi], top);
    b.ccx(r.sign, q[hi], q[0]); b.ccx(q[0], t[hi], top);
    b.x(r.sign);

    // Return the carry ladder, writing the selected lower sum.
    for i in (1..n).rev() {
        b.ccx(r.sign, q[i], t[i]);
        b.ccx(t[i-1], q[i-1], q[i]);
    }
    for i in 1..hi { b.cx(q[i], q[i+1]); }
    b.ccx(r.sign, q[0], t[0]);
    for i in 1..n { b.cx(q[i], t[i]); }
    // The source is ordinary again. Drop its original high bit on the
    // same disabled sector and restore the two signed coordinates.
    b.x(r.sign); b.ccx(r.sign, q[hi], top); b.x(r.sign);
    b.ccx(r.activity, r.flight, r.sign);
    for &bit in t { b.cx(r.activity, bit); }
    b.end()
}

pub(crate) fn selected_swap3(b:&mut B,meta:&SumSize,r:Roles3,k:usize,slot:QubitId,dirty:&[QubitId]){
    assert!(k<30&&!r.ports().contains(&slot));
    let g=Guard{y:(1,128),sum_limit:31-k as isize};
    b.cx(slot,r.flight);
    for mut term in g.terms(meta,true){
        term.extend([(r.activity,false),(r.flight,false)]);literal(b,&term,slot,dirty);
    }
    b.cx(slot,r.flight);
}

/// U10. The sign owner stays immutable; the arbitrary w is excluded from
/// every query donor bank. All 128-first lower writes share constant A&e.
pub(crate) fn physical_inverse_record3(b:&mut B,q:&[QubitId],t:&[QubitId],r:Roles3,
    first:usize,dirty:&[QubitId])->Vec<G>{
    assert_eq!((q.len(),t.len()),(128,129));assert!(first<128);
    let mut held=q.to_vec();held.extend(t);held.extend(r.ports());
    assert_eq!(held.len(),held.iter().copied().collect::<BTreeSet<_>>().len());
    let d=filtered(dirty,&held);let w=*d.first().expect("U10 arbitrary alternating donor");
    let d=filtered(&d,&[w]);assert!(d.len()>=2);
    let carry=q[127];b.begin();b.x(carry);for &a in t{b.x(a);}
    for i in first..127{cell(b,q[i],t[i],if i==first{carry}else{q[i-1]},false);}
    b.cx(r.activity,r.flight);
    // OR(t127,q126) as two disjoint cubes, in the original top order.
    literal(b,&[(r.activity,false),(t[128],false),(t[127],false)],r.flight,&d);
    literal(b,&[(r.activity,false),(t[128],false),(t[127],true),(q[126],false)],r.flight,&d);
    literal(b,&[(r.activity,false),(r.flight,false),(t[127],false)],t[128],&d);
    literal(b,&[(r.activity,false),(r.flight,false),(t[127],true),(q[126],false)],t[128],&d);
    b.ccx(r.activity,r.flight,t[127]);
    let alternating=|b:&mut B,x:QubitId,target:QubitId|{
        b.ccx(x,w,target);b.ccx(r.activity,r.flight,w);b.ccx(x,w,target);
    };
    alternating(b,q[126],t[127]);
    for i in(first..127).rev(){
        let x=if i==first{carry}else{q[i-1]};cell(b,q[i],t[i],x,true);
        b.cx(q[i],x);alternating(b,x,t[i]);b.cx(q[i],x);
    }
    if (128-first)%2!=0{b.ccx(r.activity,r.flight,w);}
    for &a in t{b.x(a);}b.x(carry);b.end()
}

pub(crate) fn forward3(b:&mut B,meta:&SumSize,q:&[QubitId],raw:&[QubitId],r:Roles3,
    ranges:Ranges,dirty:&[QubitId],forbidden:&[QubitId]){
    let d=bank3(meta,q,raw,r,dirty,forbidden);
    let frame=frame_record(b,meta,q,raw,false);b.play(&frame,false);
    for k in(0..30).rev(){
        if !permitted(ranges,k){continue;}
        let guard=Guard{y:(1,128),sum_limit:31-k as isize}
            .witness_record(b,meta,r.activity,r.flight,&d);b.play(&guard,false);
        let yhi=ranges.y.1.min((257-k).saturating_sub(ranges.z.0));
        assert!((1..=128).contains(&yhi));let first=128-yhi;
        let arithmetic=match carry_choice(first,k){
            CarryChoice::QPrefix{first}=>restoring_record(b,q,&raw[k..k+129],
                Roles{activity:r.activity,flight:r.flight,sign:r.sign,work:q[first-1]},false,first,&d),
            CarryChoice::GuardedSum=>restoring_record(b,q,&raw[k..k+129],
                Roles{activity:r.activity,flight:r.flight,sign:r.sign,work:meta.sum[4]},false,first,&d),
            CarryChoice::Ttk=>ttk_restoring_record(b,q,&raw[k..k+129],r,&d),
        };
        b.play(&arithmetic,false);b.play(&guard,true);
        // U3's former work is the sign owner, returned globally0 by U2.
        let g=Guard{y:(1,128),sum_limit:31-k as isize};
        g.xor(b,meta,r.sign,&[(r.activity,false)],&d);
        b.cswap(r.sign,r.flight,raw[128+k]);
        g.xor(b,meta,r.sign,&[(r.activity,false)],&d);
    }b.play(&frame,true);
}

pub(crate) fn inverse3(b:&mut B,meta:&SumSize,q:&[QubitId],raw:&[QubitId],r:Roles3,
    ranges:Ranges,dirty:&[QubitId],forbidden:&[QubitId]){
    let d=bank3(meta,q,raw,r,dirty,forbidden);
    let frame=frame_record(b,meta,q,raw,true);b.play(&frame,false);
    for k in 0..30{
        if !permitted(ranges,k){continue;}
        selected_swap3(b,meta,r,k,raw[129-k],&d);
        b.cx(r.sign,r.activity);
        let guard=Guard{y:(1,128),sum_limit:32-k as isize}
            .witness_record(b,meta,r.activity,r.flight,&d);b.play(&guard,false);
        let t:Vec<_>=(0..129).map(|i|raw[258-k-i]).collect();
        let yhi=ranges.y.1.min((258-k).saturating_sub(ranges.z.0));
        assert!((1..=128).contains(&yhi));
        let arithmetic=physical_inverse_record3(b,q,&t,r,128-yhi,&d);
        b.play(&arithmetic,true);b.play(&guard,true);b.cx(r.sign,r.activity);
    }b.play(&frame,true);
}
