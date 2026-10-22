//! Payload digit using three scalar owners and an existing source-leading loan.
//! Q is unparked at this whole-digit boundary. Its complete 128-cell
//! normalization makes Q127 a conditional-zero carry for both named halves.
//! The physical leading cell is never used as source data: a virtual ONE
//! is substituted in every affected sum/carry expression. The same frame
//! is literally reversed before the digit returns. No source domain shrinks.
use super::activity_guard::Guard;
use super::builder::{B,G};
use super::sum_size::SumSize;
use super::ttk_virtual_leading::Size;
use super::three_control::{literal,swap_terms,range,xor_terms};
use crate::circuit::QubitId;
use std::collections::BTreeSet;
pub(crate) use super::direct_payload::{Context,Ranges,Session,finish_phase};
pub(crate) const LOGICAL_P:usize=259;
#[derive(Clone,Copy)]
pub(crate) struct Roles{pub activity:QubitId,pub flight:QubitId,pub work:QubitId}
fn record(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}
fn eq(word:&[QubitId],v:usize)->Vec<(QubitId,bool)>{
    word.iter().enumerate().map(|(i,&q)|(q,v>>i&1==0)).collect()
}
fn donors(dirty:&[QubitId],forbidden:&[QubitId])->Vec<QubitId>{
    let mut used:BTreeSet<_>=forbidden.iter().copied().collect();
    dirty.iter().copied().filter(|q|used.insert(*q)).collect()
}
fn metadata_ports(meta:&SumSize)->Vec<QubitId>{
    meta.y.iter().chain(&meta.sum).copied().collect()
}
fn in_view(b:&mut B,meta:&SumSize,size:Size,dirty:&[QubitId],f:impl FnOnce(&mut B)){
    let view=match size{Size::Y=>None,Size::Z=>Some(meta.z_epoch(b,dirty))};
    if let Some(v)=&view{b.play(v,false);}f(b);if let Some(v)=&view{b.play(v,true);}
}
fn terms(meta:&SumSize,size:Size,v:usize)->Vec<Vec<(QubitId,bool)>>{
    match size{Size::Y=>meta.y_terms(v),Size::Z=>meta.z_terms(v)}
}
/// Metadata must already be in the matching whole Y or Z view.
fn query(b:&mut B,meta:&SumSize,size:Size,v:usize,target:QubitId,
    extra:&[(QubitId,bool)],dirty:&[QubitId]){
    meta.xor_terms(b,terms(meta,size,v),target,extra,dirty);
}
fn query_range(b:&mut B,meta:&SumSize,size:Size,range:(usize,usize),target:QubitId,
    extra:&[(QubitId,bool)],dirty:&[QubitId]){
    if range.0>range.1{return;}
    for v in range.0..=range.1{query(b,meta,size,v,target,extra,dirty);}
}

fn checked_bank(ctx:&Context<'_>,roles:Roles,dirty:&[QubitId])->Vec<QubitId>{
    assert_eq!((ctx.compact.len(),ctx.ring.len(),ctx.q.len()),(258,257,128));
    let mut used=BTreeSet::new();
    assert!(ctx.meta.y.iter().chain(&ctx.meta.sum).chain(ctx.compact)
        .chain(ctx.ring).chain(ctx.q).copied().chain([ctx.phase,roles.activity,
            roles.flight,roles.work]).all(|q|used.insert(q)));
    let mut excluded=metadata_ports(ctx.meta);excluded.extend_from_slice(ctx.compact);
    excluded.extend([ctx.phase,roles.activity,roles.flight,roles.work]);
    let pool:Vec<_>=dirty.iter().chain(ctx.ring).chain(ctx.q).copied().collect();
    let bank=donors(&pool,&excluded);
    assert!(bank.len()>=20);bank
}

fn read_selected(b:&mut B,meta:&SumSize,size:Size,range:(usize,usize),
    raw:&[QubitId],lane:impl Fn(usize)->usize,target:QubitId,act:QubitId,work:QubitId,dirty:&[QubitId]){
    if matches!(size,Size::Y)||range.1-range.0+1>=8{
        let address=if matches!(size,Size::Z){super::direct_frame::z_byte_record(b,meta,work,dirty)}else{vec![]};
        let mut word=meta.y.to_vec();if matches!(size,Size::Z){word.push(work);}
        let leaves:Vec<_>=(range.0..=range.1).map(|v|(v-1,raw[lane(v)])).collect();
        let mut swaps=vec![];let root=super::midg::swap_tree(&word,&leaves,word.len(),&mut swaps);
        b.play(&address,false);
        for &(c,a,z)in &swaps{b.cswap(c,a,z);}
        b.ccx(act,root,target);
        for &(c,a,z)in swaps.iter().rev(){b.cswap(c,a,z);}
        b.play(&address,true);return;
    }
    in_view(b,meta,size,dirty,|b|for v in range.0..=range.1{
        let cell=raw[lane(v)];assert!(cell!=target&&cell!=act);
        query(b,meta,size,v,target,&[(act,false),(cell,false)],dirty);
    });
}

/// Complete PRE insertion; PH is already conditionalzero under A.
fn expand_pre(b:&mut B,meta:&SumSize,size:Size,range:(usize,usize),
    raw:&[QubitId],act:QubitId,flag:QubitId,dirty:&[QubitId]){
    in_view(b,meta,size,dirty,|b|{
        b.cx(act,flag);let mut threshold=0;
        for i in ((257-range.1)+1..LOGICAL_P).rev(){
            let next=258-i;
            while threshold<next{
                if (range.0..=range.1).contains(&threshold){
                    query(b,meta,size,threshold,flag,&[(act,false)],dirty);
                }threshold+=1;
            }
            b.cswap(flag,raw[i],raw[i-1]);
        }
        query_range(b,meta,size,(threshold,range.1),flag,&[(act,false)],dirty);
    });
}

fn rotate_const(b:&mut B,word:&[QubitId],amount:usize,flag:Option<QubitId>){
    let n=word.len();let r=amount%n;if r==0{return;}
    let(mut a,mut d)=(n,r);while d!=0{let t=a%d;a=d;d=t;}
    for start in 0..a{
        let mut orbit=vec![start];let mut next=(start+r)%n;
        while next!=start{orbit.push(next);next=(next+r)%n;}
        for i in (1..orbit.len()).rev(){
            if let Some(c)=flag{b.cswap(c,word[orbit[i]],word[orbit[i-1]]);}
            else{b.swap(word[orbit[i]],word[orbit[i-1]]);}
        }
    }
}

/// Full-word rotation by logical R, with an exact inverse on every word.
/// Y uses E+1 directly. Z uses the full byte Z-1 on E7||work, then
/// UP1 followed by UP(Z-1). The work owner is globally zero on entry and
/// returned before reflection; all 259 payload lanes remain in the cycle.
/// No public support restriction or active-only size assumption is used.
fn rotation_record(b:&mut B,meta:&SumSize,size:Size,raw:&[QubitId],
    flag:QubitId,dirty:&[QubitId])->Vec<G>{
    if matches!(size,Size::Z){
        return super::direct_frame::rotate_z_record(b,meta,raw,flag,
            (98,256),None,false,dirty);
    }
    record(b,|b|{
        rotate_const(b,raw,1,None);
        for i in 0..7{rotate_const(b,raw,1usize<<i,Some(meta.y[i]));}
    })
}

/// Retain a complete range flag through a monotone lane walk. Endpoint
/// equality deltas update it without re-decoding the whole prefix each
/// time. All size ports stay outside the written payload word.
fn walk(b:&mut B,meta:&SumSize,size:Size,first:usize,end:usize,flag:QubitId,
    extra:&[(QubitId,bool)],dirty:&[QubitId],full_end:Option<QubitId>,range:impl Fn(usize)->(usize,usize),
    mut body:impl FnMut(&mut B,usize)){
    if first>=end{return;}
    in_view(b,meta,size,dirty,|b|{
        let mut old=range(first);query_range(b,meta,size,old,flag,extra,dirty);
        for i in first..end{
            let new=range(i);
            // General symmetric difference; these public sets have at
            // most one entering/leaving value in production walks.
            if old!=new{
                for v in 1..=256{
                    let a=old.0<=v&&v<=old.1;let z=new.0<=v&&v<=new.1;
                    if a!=z{query(b,meta,size,v,flag,extra,dirty);}
                }
            }
            body(b,i);old=new;
        }
        if let Some(a)=full_end{b.cx(a,flag);}else{query_range(b,meta,size,old,flag,extra,dirty);}
    });
}

fn reflect(b:&mut B,meta:&SumSize,size:Size,raw:&[QubitId],r:Roles,d:&[QubitId]){
    // e is zero at the whole-half boundary; work retains the sign.
    let rotation=rotation_record(b,meta,size,raw,r.flight,d);b.play(&rotation,true);
    for code in 0..32{let n=32-code;if n<2{continue;}
        let c=vec![eq(&meta.sum,code)];
        for i in 0..n/2{swap_terms(b,&c,&[(r.activity,false)],raw[i],raw[n-1-i],d);}
    }b.play(&rotation,false);
}
fn cell(b:&mut B,s:QubitId,t:QubitId,x:QubitId,inverse:bool){
    if inverse{b.ccx(x,t,s);b.cx(s,x);b.cx(s,t);}
    else{b.cx(s,t);b.cx(s,x);b.ccx(x,t,s);}
}
fn or_write(b:&mut B,terms:&[Vec<(QubitId,bool)>],extra:&[(QubitId,bool)],
    a:QubitId,c:QubitId,target:QubitId,d:&[QubitId]){
    for tail in [vec![(a,false)],vec![(c,false)],vec![(a,false),(c,false)]]{
        let mut e=extra.to_vec();e.extend(tail);xor_terms(b,terms,&e,target,d);
    }
}
/// Fixed128 divider, with Q127 already a conditional-zero carry and the
/// logical source bit127 replaced by ONE. Work temporarily holds its OR
/// carry, then A*e. In inverse use its off-A original-sign passenger is
/// retained, so every mask-controlled data write explicitly includes A.
fn q_record(b:&mut B,q:&[QubitId],t:&[QubitId],r:Roles,
    conditional_mask:bool,d:&[QubitId])->Vec<G>{
    assert_eq!((q.len(),t.len()),(128,129));let carry=q[127];
    record(b,|b|{
        for &a in t{b.x(a);}
        for i in 0..127{cell(b,q[i],t[i],if i==0{carry}else{q[i-1]},false);}
        let top=|b:&mut B|{b.cx(t[127],r.work);b.cx(q[126],r.work);
            b.ccx(t[127],q[126],r.work);};
        top(b);
        b.cx(r.activity,r.flight);
        literal(b,&[(r.activity,false),(t[128],false),(r.work,false)],r.flight,d);
        literal(b,&[(r.activity,false),(r.flight,false),(r.work,false)],t[128],d);
        top(b);b.ccx(r.activity,r.flight,r.work);
        let mut mask=vec![(r.work,false)];
        if conditional_mask{mask.push((r.activity,false));}
        literal(b,&mask,t[127],d);
        let mut top_controls=mask.clone();top_controls.push((q[126],false));
        literal(b,&top_controls,t[127],d);
        for i in (0..127).rev(){let x=if i==0{carry}else{q[i-1]};cell(b,q[i],t[i],x,true);
            b.cx(q[i],x);let mut controls=mask.clone();controls.push((x,false));
            literal(b,&controls,t[i],d);b.cx(q[i],x);
        }
        b.ccx(r.activity,r.flight,r.work);
        for &a in t{b.x(a);}
    })
}
/// Complete variable-Z divider. A one-cell lookahead restores the virtual
/// leading source passenger before its OR carry is evaluated. Work shuttles
/// between A*e and A*[Z=i], with an unchanged original-sign passenger off A.
/// Its two metadata queries per boundary replace repeated carry expansions.
/// Every inverse mask-controlled write retains A; the temporary B pairs
/// cancel off A. The forward mask is globally zero off A. The captured
/// inverse acts on the image of this complete record.
fn z_record(b:&mut B,meta:&SumSize,t:&[QubitId],s:&[QubitId],carry:QubitId,
    r:Roles,lo:usize,hi:usize,conditional_mask:bool,d:&[QubitId])->Vec<G>{
    assert_eq!(t.len(),s.len());assert!(hi<t.len()&&lo>=1);
    let undo=|b:&mut B,i:usize|{let x=if i==0{carry}else{s[i-1]};cell(b,s[i],t[i],x,true);x};
    record(b,|b|{
        for &a in t{b.x(a);}
        for i in 0..s.len(){cell(b,s[i],t[i],if i==0{carry}else{s[i-1]},false);}
        let mut x=undo(b,t.len()-1);
        for i in (0..t.len()).rev(){
            if i<hi{
                b.cx(s[i],x);
                if conditional_mask{literal(b,&[(r.activity,false),(r.work,false),(x,false)],t[i],d);}
                else{b.ccx(r.work,x,t[i]);}
                b.cx(s[i],x);
            }
            let previous=if i>=1{Some(undo(b,i-1))}else{None};
            if (lo..=hi).contains(&i){let c=previous.unwrap();let terms=meta.z_terms(i);
                // Remove the running quotient, borrow work for this one
                // membership, then restore the updated running quotient.
                b.ccx(r.activity,r.flight,r.work);
                xor_terms(b,&terms,&[(r.activity,false)],r.work,d);
                let mut member=vec![(r.work,false)];
                if conditional_mask{member.push((r.activity,false));}
                literal(b,&member,r.flight,d);
                // D=A*work and C=t[i-1] OR carry. B A B A, with
                // B:t[i]^=e*C and A:e^=D*t[i], is the exact central
                // order-three map. When D=0 the two arbitrary B cancel.
                for _ in 0..2{
                    or_write(b,&[vec![]],&[(r.flight,false)],t[i-1],c,t[i],d);
                    let mut controls=member.clone();controls.push((t[i],false));
                    literal(b,&controls,r.flight,d);
                }
                // The preceding cell is already restored. Its virtual
                // leading correction commutes with the next lower write,
                // so do it now while membership is still available.
                let mut correction=member;correction.extend([(r.flight,false),(s[i-1],true)]);
                literal(b,&correction,t[i-1],d);
                xor_terms(b,&terms,&[(r.activity,false)],r.work,d);
                b.ccx(r.activity,r.flight,r.work);
            }
            if let Some(v)=previous{x=v;}
        }
        b.ccx(r.activity,r.flight,r.work);
        for &a in t{b.x(a);}
    })
}
fn permitted(ranges:Ranges,k:usize)->bool{ranges.z.0.saturating_add(ranges.y.0).max(226)<=257-k}
fn p_frame(b:&mut B,meta:&SumSize,raw:&[QubitId],inverse:bool)->Vec<G>{
    record(b,|b|{for &e in &meta.y{b.x(e);}
        for (k,&e)in meta.y.iter().enumerate(){let amount=1usize<<k;
            super::frogdrop::crot_up(b,e,raw,if inverse{259-amount}else{amount});}
        for &e in &meta.y{b.x(e);}
    })
}
fn selected_swap(b:&mut B,meta:&SumSize,r:Roles,k:usize,slot:QubitId,d:&[QubitId]){
    swap_terms(b,&range(&meta.sum,0,32-k),&[(r.activity,false)],r.flight,slot,d);
}
fn q_half(b:&mut B,ctx:&Context<'_>,raw:&[QubitId],r:Roles,ranges:Ranges,inverse:bool,d:&[QubitId]){
    let frame=p_frame(b,ctx.meta,raw,inverse);b.play(&frame,false);
    let order:Vec<_>=if inverse{(0..30).collect()}else{(0..30).rev().collect()};
    for k in order{if !permitted(ranges,k){continue;}
        if inverse{selected_swap(b,ctx.meta,r,k,raw[129-k],d);b.cx(r.work,r.activity);}
        let guard=Guard{y:(1,128),sum_limit:(if inverse{32}else{31})-k as isize}
            .witness_record(b,ctx.meta,r.activity,r.flight,d);
        b.play(&guard,false);
        let t:Vec<_>=if inverse{(0..129).map(|i|raw[258-k-i]).collect()}else{raw[k..k+129].to_vec()};
        let arithmetic=q_record(b,ctx.q,&t,r,inverse,d);b.play(&arithmetic,inverse);b.play(&guard,true);
        if inverse{b.cx(r.work,r.activity);}else{selected_swap(b,ctx.meta,r,k,raw[128+k],d);}
    }
    b.play(&frame,true);
}
fn z_swap(b:&mut B,meta:&SumSize,raw:&[QubitId],r:Roles,carry:QubitId,
    ranges:Ranges,k:usize,inverse:bool,d:&[QubitId]){
    // Q127 is returned by every arithmetic record and is zero on original
    // A throughout qframe. Borrow it as the eighth exact Z-1 address bit.
    // Off A its arbitrary byte/gather permutation is conjugated around an
    // identity center, so no globally-zero address owner is required.
    let d=donors(d,&[carry]);
    let address=super::direct_frame::z_byte_record(b,meta,carry,&d);
    let byte:Vec<_>=meta.y.iter().copied().chain([carry]).collect();
    let leaves:Vec<_>=(ranges.z.0..=ranges.z.1).filter_map(|z|{
        let slot=if inverse{if z+1+k>=259{return None;}raw[257-z-k]}
            else{if z+k>=259{return None;}raw[z+k]};
        Some((z-1,slot))
    }).collect();
    if leaves.is_empty(){return;}
    let mut swaps=vec![];let root=super::midg::swap_tree(&byte,&leaves,8,&mut swaps);
    b.play(&address,false);
    for &(c,a,z) in &swaps{b.cswap(c,a,z);}
    swap_terms(b,&range(&meta.sum,0,32-k),&[(r.activity,false)],r.flight,root,&d);
    for &(c,a,z) in swaps.iter().rev(){b.cswap(c,a,z);}
    b.play(&address,true);
}
fn z_half(b:&mut B,ctx:&Context<'_>,raw:&[QubitId],r:Roles,ranges:Ranges,inverse:bool,d:&[QubitId]){
    let order:Vec<_>=if inverse{(0..30).collect()}else{(0..30).rev().collect()};
    for k in order{if !permitted(ranges,k){continue;}
        if inverse{z_swap(b,ctx.meta,raw,r,ctx.q[127],ranges,k,true,d);b.cx(r.work,r.activity);}
        let limit=((if inverse{32}else{31})-k).min(31);let total=226+limit;
        let yl=ranges.y.0.max(226usize.saturating_sub(ranges.z.1));
        let yh=ranges.y.1.min(total.saturating_sub(ranges.z.0));
        if yl<=yh{
            let lo=ranges.z.0.max(226-yh);let hi=ranges.z.1.min(total-yl);
            if lo<=hi{
                let guard=Guard{y:(1,128),sum_limit:(if inverse{32}else{31})-k as isize}
                    .witness_record(b,ctx.meta,r.activity,r.flight,d);b.play(&guard,false);
                let view=ctx.meta.z_epoch(b,d);b.play(&view,false);
                let t:Vec<_>=if inverse{(0..=hi).map(|i|raw[258-k-i]).collect()}else{raw[k..k+hi+1].to_vec()};
                let arithmetic=z_record(b,ctx.meta,&t,&ctx.ring[..hi+1],ctx.q[127],r,lo,hi,inverse,d);
                b.play(&arithmetic,inverse);b.play(&view,true);b.play(&guard,true);
            }
        }
        if inverse{b.cx(r.work,r.activity);}else{z_swap(b,ctx.meta,raw,r,ctx.q[127],ranges,k,false,d);}
    }
}
pub(crate) fn digit(b:&mut B,ctx:&Context<'_>,r:Roles,ht:bool,ranges:Ranges,dirty:&[QubitId])->Session{
    let d=checked_bank(ctx,r,dirty);let meta=ctx.meta;
    let raw:Vec<_>=ctx.compact.iter().copied().chain([ctx.phase]).collect();
    let(rsize,rr,tsize,tr)=if ht{(Size::Y,ranges.y,Size::Z,ranges.z)}else{(Size::Z,ranges.z,Size::Y,ranges.y)};
    if ht{b.cx(r.activity,ctx.phase);}
    expand_pre(b,meta,tsize,tr,&raw,r.activity,r.work,&d);
    let qframe=super::single_z_maj::frame_record(b,meta,ctx.q);b.play(&qframe,false);
    if ht{q_half(b,ctx,&raw,r,ranges,false,&d);}else{z_half(b,ctx,&raw,r,ranges,false,&d);}
    read_selected(b,meta,tsize,tr,&raw,|t|258-t,r.work,r.activity,r.flight,&d);
    reflect(b,meta,rsize,&raw,r,&d);
    if ht{z_half(b,ctx,&raw,r,ranges,true,&d);}else{q_half(b,ctx,&raw,r,ranges,true,&d);}
    b.play(&qframe,true);
    let end=258-tr.0;
    walk(b,meta,rsize,rr.0,end,r.flight,&[],&d,None,
        |l|(l+1,rr.1),|b,l|b.ccx(r.work,r.flight,raw[l]));
    walk(b,meta,tsize,rr.0,end.min(258),r.flight,&[],&d,None,
        |l|(tr.0,(257-l).min(tr.1)),|b,l|b.ccx(r.work,r.flight,raw[l]));
    read_selected(b,meta,rsize,rr,&raw,|v|v,r.work,r.activity,r.flight,&d);
    walk(b,meta,rsize,rr.0+1,259,r.flight,&[(r.activity,false)],&d,Some(r.activity),
        |l|(rr.0,(l-1).min(rr.1)),|b,l|b.cx(r.flight,raw[l]));
    Session{raw,activity:r.activity,phase:ctx.phase,ht}
}
/// Three-owner boundary narrowing. Direct metadata controls remove the
/// separate byte+predicate overlap of the gathered four-owner adapter.
pub(crate) fn narrow_three(b:&mut B,meta:&SumSize,p:&[QubitId],q:&[QubitId],ring:Option<&[QubitId]>,
    bounds:(usize,usize),activity:QubitId,dirty:&[QubitId],ht:bool){
    assert_eq!((p.len(),q.len()),(258,128));let mut excluded=metadata_ports(meta);
    excluded.extend(p);excluded.extend(q);excluded.push(activity);
    let d=donors(dirty,&excluded);let view=meta.z_epoch(b,&d);b.play(&view,false);
    for z in bounds.0..=bounds.1{let bit=256-z;let i=if ht{bit}else{z};
        let mut e=vec![(activity,false),(p[i+1],false)];
        if let Some(&a)=q.get(bit).or_else(||ring.and_then(|w|w.get(bit))){e.push((a,true));}
        xor_terms(b,&meta.z_terms(z),&e,p[i],&d);
    }b.play(&view,true);
}
