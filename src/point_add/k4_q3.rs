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

/// U2. The first add is controlled by A: the saved design's unconditional
/// first add plus A&!e add-back did not restore the inactive branch. This
/// literal form pays 130 extra raw CCX at n129 and keeps the original off-A
/// identity for arbitrary q/t/e. On A it uses the parent's d<2r care.
pub(crate) fn ttk_restoring_record(b:&mut B,q:&[QubitId],t:&[QubitId],r:Roles3,
    dirty:&[QubitId])->Vec<G>{
    assert_eq!(q.len()+1,t.len());assert!(q.len()>=2);
    let mut held=q.to_vec();held.extend(t);held.extend(r.ports());
    assert_eq!(held.len(),held.iter().copied().collect::<BTreeSet<_>>().len());
    let d=filtered(dirty,&held);let pad=*d.first().expect("U2 arbitrary padding donor");
    let source:Vec<_>=q.iter().copied().chain([pad]).collect();let top=t[q.len()];
    b.begin();for &p in t{b.x(p);}
    super::super::arith::ttk_add(b,&source,t,Some(r.activity),None);
    b.ccx(r.activity,pad,top);
    b.ccx(r.activity,top,r.flight);
    b.x(r.flight);b.ccx(r.activity,r.flight,r.sign);b.x(r.flight);
    b.begin();super::super::arith::ttk_add(b,&source,t,Some(r.sign),None);
    let undo=b.end();b.play(&undo,true);b.ccx(r.sign,pad,top);
    b.x(r.flight);b.ccx(r.activity,r.flight,r.sign);b.x(r.flight);
    for &p in t{b.x(p);}b.end()
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
