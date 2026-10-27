//! SOURCE-ONLY direct E7/S5 payload shell. Not registered or emitted.
//!
//! This module owns representation changes, park/fetch and the non-ripple
//! digit operations. Arithmetic is delegated through `Arithmetic`; its
//! contract includes ONE combined activity guard, size-window entry/exit,
//! virtual leading ONE and literal inverse. No joint Q/size codec or saved
//! physical leading bit is introduced by this shell.
//!
//! Four scalar owners are [A,e,sign,work]. PH is the logical259th payload
//! lane from PRE expansion through the complete q/bq transition. It is
//! restored only by finish_phase, before the next phase/activity reader.

use super::activity_guard::Guard;
use super::builder::{B,G};
use super::mask::mc_xor;
use super::sum_size::SumSize;
use super::ttk_virtual_leading::Size;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

pub(crate) const PHYSICAL_P:usize=258;
pub(crate) const LOGICAL_P:usize=259;
pub(crate) const KE:usize=30;
pub(crate) const Y_BANDS:[(usize,usize);3]=[(1,96),(97,120),(121,128)];

#[derive(Clone,Copy)]
pub(crate) struct Roles{pub activity:QubitId,pub flight:QubitId,pub sign:QubitId,pub work:QubitId}

#[derive(Clone,Copy)]
pub(crate) struct Ranges{pub z:(usize,usize),pub y:(usize,usize)}

#[derive(Clone,Copy)]
pub(crate) enum Leading {
    /// The selected physical source top is one on complete enabled care.
    PhysicalOne,
    /// HR ring top may hold an in-place quotient passenger. Treat the
    /// selected logical top as one and restore the physical top unchanged.
    VirtualOne,
}

#[derive(Clone,Copy)]
pub(crate) struct Kernel {
    pub size:Size,
    pub bounds:(usize,usize),
    pub guard:Guard,
    pub inverse:bool,
    pub leading:Leading,
}

/// Complete arithmetic ABI, not a callback at an internal MAJ midpoint.
///
/// Entry/exit metadata is the ORIGINAL E=Y-1,S view. A is restored. Forward
/// starts e/sign/work=0 and computes exactly one quotient bit. Inverse
/// keeps original sign on `sign`, returns e/work=0, and preserves sign.
/// Sign=>original A and e=>A&!sign&forward_guard are inherited digit care.
/// The inverse may first do CX(sign,A), BEFORE its one combined guard.
/// Never nest a band witness and a second sum witness using the same e.
///
/// The record must be identity off its complete enabled guard, including
/// arbitrary high source passengers and the skipped-activity e witness.
/// All metadata/helper/cache loans return before this call returns.
/// Target low R+1 is the restoring dividend d<2*r; higher target cells may
/// be arbitrary passengers. No source/payload top-save is available here.
pub(crate) trait Arithmetic {
    fn apply(&mut self,b:&mut B,meta:&SumSize,roles:Roles,call:Kernel,
        target:&[QubitId],source:&[QubitId],dirty:&[QubitId]);
}

pub(crate) struct Context<'a>{
    pub meta:&'a SumSize,
    pub compact:&'a [QubitId],
    pub ring:&'a [QubitId],
    pub q:&'a [QubitId],
    pub phase:QubitId,
}

/// This is an open PH-as-payload lifetime. The caller must preserve its
/// retained A (or update this field after an exact two-CX role transfer).
/// No phase/done predicate is allowed until finish_phase has completed.
pub(crate) struct Session{
    pub raw:Vec<QubitId>,pub activity:QubitId,pub phase:QubitId,pub ht:bool,
}

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
            roles.flight,roles.sign,roles.work]).all(|q|used.insert(q)));
    let mut excluded=metadata_ports(ctx.meta);excluded.extend_from_slice(ctx.compact);
    excluded.extend([ctx.phase,roles.activity,roles.flight,roles.sign,roles.work]);
    let pool:Vec<_>=dirty.iter().chain(ctx.ring).chain(ctx.q).copied().collect();
    let bank=donors(&pool,&excluded);
    assert!(bank.len()>=20);bank
}

/// Full G=original Yband & S<=31-k is retained on work BEFORE a Z epoch.
/// Every band-selected public range has fewer than129 consecutive values,
/// hence Z mod128 (or Y-1) is injective on the actual selected leaves.
/// Gather, one work-controlled swap, and literal ungather restore every
/// other payload lane. Off work this is identity for arbitrary metadata
/// and payload, even outside the partial tree's public address care.
fn park_or_fetch(b:&mut B,meta:&SumSize,size:Size,range:(usize,usize),
    lane:impl Fn(usize)->Option<QubitId>,roles:Roles,guard:Guard,dirty:&[QubitId]){
    assert!(range.0<=range.1&&range.1-range.0<128,
        "band-selected size range must be injective modulo128");
    guard.xor(b,meta,roles.work,&[(roles.activity,false)],dirty);
    in_view(b,meta,size,dirty,|b|{
        let mut leaves=Vec::new();let mut owners=BTreeSet::new();
        for v in range.0..=range.1{if let Some(cell)=lane(v){
            assert!(![roles.activity,roles.flight,roles.sign,roles.work].contains(&cell));
            assert!(owners.insert(cell));
            let key=if matches!(size,Size::Y){assert!((1..=128).contains(&v));v-1}else{v%128};
            leaves.push((key,cell));
        }}
        if leaves.is_empty(){return;}
        leaves.sort_unstable_by_key(|p|p.0);
        assert!(leaves.windows(2).all(|w|w[0].0<w[1].0));
        let mut swaps=Vec::new();
        let root=super::midg::swap_tree(&meta.y,&leaves,7,&mut swaps);
        for &(c,a,z) in &swaps{b.cswap(c,a,z);}
        b.cswap(roles.work,roles.flight,root);
        for &(c,a,z) in swaps.iter().rev(){b.cswap(c,a,z);}
    });
    guard.xor(b,meta,roles.work,&[(roles.activity,false)],dirty);
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

fn reflect(b:&mut B,meta:&SumSize,rsize:Size,raw:&[QubitId],roles:Roles,dirty:&[QubitId]){
    let rotation=rotation_record(b,meta,rsize,raw,roles.work,dirty);
    b.play(&rotation,true);
    for code in 0..32{
        let length=32-code;if length<2{continue;}
        let mut c=eq(&meta.sum,code);c.push((roles.activity,false));
        mc_xor(b,&c,roles.work,&[],dirty);
        for i in 0..length/2{b.cswap(roles.work,raw[i],raw[length-1-i]);}
        mc_xor(b,&c,roles.work,&[],dirty);
    }
    b.play(&rotation,false);
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

fn intersect(a:(usize,usize),z:(usize,usize))->Option<(usize,usize)>{
    let out=(a.0.max(z.0),a.1.min(z.1));(out.0<=out.1).then_some(out)
}
fn branch_range(size:Size,public:(usize,usize),band:(usize,usize))->Option<(usize,usize)>{
    match size{Size::Y=>intersect(public,band),
        Size::Z=>intersect(public,(226-band.1,257-band.0))}
}

/// Open P258, run the complete non-transition digit, keep PH as raw P258.
/// Caller supplies the already retained COMPLETE phase A (including DONE,
/// switch and delayed guards). On A, raw Q is exactly Y and every quotient
/// park in Q has already returned; inverse HT/HR arithmetic uses physical
/// coefficient-leading ONE. HR forward uses virtual leading ONE instead.
/// No metadata phase reader may run between this function and finish_phase.
pub(crate) fn digit(b:&mut B,ctx:&Context<'_>,roles:Roles,ht:bool,
    ranges:Ranges,_arithmetic:&mut impl Arithmetic,dirty:&[QubitId])->Session{
    assert!(98<=ranges.z.0&&ranges.z.0<=ranges.z.1&&ranges.z.1<=256);
    assert!(1<=ranges.y.0&&ranges.y.0<=ranges.y.1&&ranges.y.1<=128);
    let bank=checked_bank(ctx,roles,dirty);let meta=ctx.meta;
    let raw:Vec<_>=ctx.compact.iter().copied().chain([ctx.phase]).collect();
    let(rsize,rr,tsize,tr)=if ht{
        (Size::Y,ranges.y,Size::Z,ranges.z)
    }else{(Size::Z,ranges.z,Size::Y,ranges.y)};
    if ht{b.cx(roles.activity,ctx.phase);}
    expand_pre(b,meta,tsize,tr,&raw,roles.activity,roles.work,&bank);

    if ht{
        // Q is unparked for this entire digit epoch. The full coordinate
        // pair closes before sign/reflection and every raw transition.
        super::normalized_payload_q::forward(b,meta,ctx.q,&raw,roles,ranges,&bank);
    }else{
        // The unused raw-Q operand is positive and unparked on A for this
        // entire Z half. Keep its normalized leading-ONE carry through all
        // quotient bits; metadata returns to raw E/S before each park.
        let zframe=super::single_z_maj::frame_record(b,meta,ctx.q);
        let leading=super::single_z_maj::leading_one_record(b,meta,ctx.ring,
            roles,ranges.z,&bank);
        b.play(&zframe,false);b.play(&leading,false);
        for k in (0..KE).rev(){
            if (rr.0+tr.0).max(226)>257usize.saturating_sub(k){continue;}
            super::single_z_maj::apply(b,meta,ctx.q,&raw,ctx.ring,
                roles,ranges,k,false,&bank);
            for band in Y_BANDS{
                if intersect(ranges.y,band).is_none(){continue;}
                let Some(mut bounds)=branch_range(rsize,rr,band)else{continue;};
                let end=(k+bounds.1+1).min(LOGICAL_P);bounds.1=bounds.1.min(end-k-1);
                if bounds.0>bounds.1{continue;}
                let guard=Guard{y:band,sum_limit:31-k as isize};
                // Preserve each original complete park guard and leaf set.
                // The disjoint Y bands now consume the single merged e.
                park_or_fetch(b,meta,rsize,bounds,|r|(r+k<LOGICAL_P).then(||raw[r+k]),roles,guard,&bank);
            }
        }
        b.play(&leading,true);b.play(&zframe,true);
    }
    read_selected(b,meta,tsize,tr,&raw,|t|258-t,roles.sign,roles.activity,roles.work,&bank);
    reflect(b,meta,rsize,&raw,roles,&bank);

    if !ht{
        // Exact inverse Q epoch; sign is retained off its narrowed A.
        super::normalized_payload_q::inverse(b,meta,ctx.q,&raw,roles,ranges,&bank);
    }else{
        let zframe=super::single_z_maj::frame_record(b,meta,ctx.q);
        b.play(&zframe,false);
        for k in 0..KE{
            if (rr.0+tr.0).max(226)>257usize.saturating_sub(k){continue;}
            // Disjoint complete Y guards permit fetching all three bands
            // before the one inverse Z kernel. Off each band its original
            // gather/swap/ungather remains the literal identity.
            for band in Y_BANDS{
                if intersect(ranges.y,band).is_none(){continue;}
                let Some(mut bounds)=branch_range(tsize,tr,band)else{continue;};
                let end=(k+bounds.1+1).min(LOGICAL_P);bounds.1=bounds.1.min(end-k-1);
                if bounds.0>bounds.1{continue;}
                let fetch=Guard{y:band,sum_limit:31-k as isize};
                park_or_fetch(b,meta,tsize,bounds,|t|(t+1+k<LOGICAL_P).then(||raw[257-t-k]),roles,fetch,&bank);
            }
            super::single_z_maj::apply(b,meta,ctx.q,&raw,ctx.ring,
                roles,ranges,k,true,&bank);
        }
        b.play(&zframe,true);
    }
    // R+T<=257: [R<=l<258-T] = [l<R] XOR [l<258-T]. Sign0 offA.
    let end=258-tr.0;
    walk(b,meta,rsize,rr.0,end,roles.work,&[],&bank,None,
        |l|(l+1,rr.1),|b,l|b.ccx(roles.sign,roles.work,raw[l]));
    walk(b,meta,tsize,rr.0,end.min(258),roles.work,&[],&bank,None,
        |l|(tr.0,(257-l).min(tr.1)),|b,l|b.ccx(roles.sign,roles.work,raw[l]));
    // Strict complement never changes raw[R], so erase sign first.
    read_selected(b,meta,rsize,rr,&raw,|r|r,roles.sign,roles.activity,roles.work,&bank);
    // Final l258 includes the complete active R range, so the retained
    // mask equals A. A0 made every delta query zero, including off-range
    // inactive metadata. Clear it by this identity rather than re-decoding.
    walk(b,meta,rsize,rr.0+1,LOGICAL_P,roles.work,&[(roles.activity,false)],&bank,Some(roles.activity),
        |l|(rr.0,(l-1).min(rr.1)),|b,l|b.cx(roles.work,raw[l]));
    Session{raw,activity:roles.activity,phase:ctx.phase,ht}
}

/// Call ONLY after every q/bq payload transition has completed. The POST
/// identity P[R]^P[R+1]^1=0 does not hold merely after the digit. Retained A
/// and original E/S are supplied; PH is data and is never read as phase.
pub(crate) fn finish_phase(b:&mut B,meta:&SumSize,session:&Session,
    range:(usize,usize),flag:QubitId,dirty:&[QubitId]){
    assert_eq!(session.raw.len(),LOGICAL_P);
    assert!(1<=range.0&&range.0<=range.1&&range.1<=256);
    let mut excluded=metadata_ports(meta);excluded.extend(&session.raw);
    excluded.extend([flag,session.activity]);let bank=donors(dirty,&excluded);
    assert!(bank.len()>=12&&!session.raw.contains(&flag)&&flag!=session.activity);
    let size=if session.ht{Size::Y}else{Size::Z};
    let gathered=range.1-range.0+1>=32;
    if gathered{
        let support:BTreeSet<_>=[0,1].into_iter().collect();
        let pair=if matches!(size,Size::Z){
            super::direct_frame::rotate_z_record(b,meta,&session.raw,flag,range,Some(&support),true,&bank)
        }else{record(b,|b|super::frogdrop::rot_by_off_care(b,&session.raw,&meta.y,1,128,true,&support))};
        b.play(&pair,false);
        b.ccx(session.activity,session.raw[1],session.raw[0]);
        b.cx(session.activity,session.raw[0]);
        b.play(&pair,true);
    }
    in_view(b,meta,size,&bank,|b|{
        if !gathered{for r in range.0..=range.1{
            query(b,meta,size,r,flag,&[(session.activity,false)],&bank);
            b.ccx(flag,session.raw[r+1],session.raw[r]);b.cx(flag,session.raw[r]);
            query(b,meta,size,r,flag,&[(session.activity,false)],&bank);
        }}
        for i in range.0+1..LOGICAL_P{
            if i-1<=range.1{query(b,meta,size,i-1,flag,&[(session.activity,false)],&bank);}
            b.cswap(flag,session.raw[i],session.raw[i-1]);
        }
        // Every active R in the complete public range entered the mask
        // once; off activity no equality toggled it. The mask is now A.
        b.cx(session.activity,flag);
    });
    if session.ht{b.cx(session.activity,session.phase);}
}

/// Compact HR POST->PRE at stage9, only in the inherited domain Z>=129.
/// Metadata still names old remainder Z; Q is t_next below128. Delayed
/// HR keeps POST through DQ and is narrowed by the later deferred HT call.
/// If Q[256-Z]=0, omitted hole moves Z->Z+1 and compact[Z]^=compact[Z+1].
pub(crate) fn narrow_hr(b:&mut B,meta:&SumSize,compact:&[QubitId],q:&[QubitId],ring:&[QubitId],
    range:(usize,usize),act:QubitId,flag:QubitId,byte:QubitId,dirty:&[QubitId]){
    assert_eq!(ring.len(),257);assert!(range.0>=129);
    narrow_gathered(b,meta,compact,q,Some(ring),range,act,flag,byte,dirty,false);
}
/// Compact deferred HT narrow. Z names t_next; active includes ordinary
/// previous HT and fresh DONE(counter1), excludes incoming C and old DONE.
/// If Q[256-Z]=0, compact[256-Z]^=compact[257-Z]. No counter probe occurs.
pub(crate) fn narrow_ht(b:&mut B,meta:&SumSize,compact:&[QubitId],q:&[QubitId],
    range:(usize,usize),act:QubitId,flag:QubitId,byte:QubitId,dirty:&[QubitId]){
    assert!(range.1<256,"previous HT coefficient has R>=2; col0 never narrows");
    narrow_gathered(b,meta,compact,q,None,range,act,flag,byte,dirty,true);
}

/// Exact range-gated pair transform. Below Z129 the old virtual Q-zero
/// path remains literal. Above it, gather Q[256-Z] and the two adjacent
/// payload lanes, apply the same central CCX, then undo every permutation.
/// The complete original public range remains in the central predicate:
/// HR activity alone does not exclude delayed Z<=128 states.
fn narrow_gathered(b:&mut B,meta:&SumSize,compact:&[QubitId],q:&[QubitId],upper:Option<&[QubitId]>,
    range:(usize,usize),act:QubitId,flag:QubitId,byte:QubitId,dirty:&[QubitId],ht:bool){
    let lo=range.0.max(129);
    if lo>range.1||range.1-lo+1<32{
        narrow(b,meta,compact,q,upper,range,act,flag,dirty,ht);return;
    }
    if range.0<129{narrow(b,meta,compact,q,upper,(range.0,128),act,flag,dirty,ht);}
    let held:Vec<_>=meta.y.iter().chain(&meta.sum).chain(compact).chain(q).copied()
        .chain([act,flag,byte]).collect();
    assert_eq!(held.iter().copied().collect::<BTreeSet<_>>().len(),held.len());
    let bank=donors(dirty,&held);assert!(bank.len()>=12);
    let address=super::direct_frame::z_byte_record(b,meta,byte,&bank);
    let word:Vec<_>=meta.y.iter().copied().chain([byte]).collect();
    let payload:Vec<_>=if ht{compact.iter().rev().copied().collect()}else{compact.to_vec()};
    let support:BTreeSet<_>=[0,1].into_iter().collect();
    let pair=record(b,|b|super::frogdrop::rot_by_off_care(b,&payload,&word,1,256,true,&support));
    let leaves:Vec<_>=(lo..=range.1).map(|z|(z-1,q[256-z])).collect();
    let mut swaps=vec![];let root=super::midg::swap_tree(&word,&leaves,8,&mut swaps);
    let guard=record(b,|b|{
        let(mut low,high)=(lo-1,range.1);
        while low<high{
            let mut free=if low==0{8}else{low.trailing_zeros()as usize};
            while low+(1usize<<free)>high{free-=1;}
            let mut c:Vec<_>=(free..8).map(|i|(word[i],low>>i&1==0)).collect();
            c.extend([(act,false),(root,true)]);mc_xor(b,&c,flag,&[],&bank);
            low+=1usize<<free;
        }
    });
    b.play(&address,false);b.play(&pair,false);
    for &(c,a,z)in &swaps{b.cswap(c,a,z);}
    b.play(&guard,false);
    b.ccx(flag,payload[usize::from(!ht)],payload[usize::from(ht)]);
    b.play(&guard,true);
    for &(c,a,z)in swaps.iter().rev(){b.cswap(c,a,z);}
    b.play(&pair,true);b.play(&address,true);
}
fn narrow(b:&mut B,meta:&SumSize,compact:&[QubitId],q:&[QubitId],upper:Option<&[QubitId]>,range:(usize,usize),
    act:QubitId,flag:QubitId,dirty:&[QubitId],ht:bool){
    assert_eq!((compact.len(),q.len()),(258,128));
    assert!(98<=range.0&&range.0<=range.1&&range.1<=256&&act!=flag);
    let mut unique=BTreeSet::new();
    assert!(meta.y.iter().chain(&meta.sum).chain(compact).chain(q).copied()
        .chain(upper.into_iter().flatten().copied()).chain([act,flag])
        .all(|p|unique.insert(p)));
    let mut excluded=metadata_ports(meta);excluded.extend(compact);excluded.extend(q);
    // Only the selected upper coefficient bit is a query control. Other
    // ring lanes remain arbitrary returned dirty donors for that query.
    excluded.extend([act,flag]);let bank=donors(dirty,&excluded);
    assert!(bank.len()>=if upper.is_some(){13}else{12});
    in_view(b,meta,Size::Z,&bank,|b|for z in range.0..=range.1{
        let bit=256-z;let mut extra=vec![(act,false)];
        if let Some(&cell)=q.get(bit).or_else(||upper.and_then(|u|u.get(bit))){
            extra.push((cell,true));
        }
        query(b,meta,Size::Z,z,flag,&extra,&bank);
        let target=if ht{bit}else{z};b.ccx(flag,compact[target+1],compact[target]);
        query(b,meta,Size::Z,z,flag,&extra,&bank);
    });
}
