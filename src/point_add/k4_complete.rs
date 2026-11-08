//! Complete K4 three-role payload sibling. No production selector reads this module.
//! The caller retains COMPLETE activity before digit3 and keeps PH as raw[258]
//! until all payload transitions and finish_phase3 have returned.
use super::*;

#[derive(Clone,Copy,Debug,Default,PartialEq,Eq)]
pub(crate) enum Diagnostic { #[default] Parent, ThreeRole }
#[derive(Clone,Copy,Debug)]
pub(crate) struct Roles3 {pub activity:QubitId,pub flight:QubitId,pub sign:QubitId}
impl Roles3 {pub(crate) fn ports(self)->[QubitId;3]{[self.activity,self.flight,self.sign]}}
pub(crate) fn filtered(dirty:&[QubitId],excluded:&[QubitId])->Vec<QubitId>{donors(dirty,excluded)}

fn checked_bank3(ctx:&Context<'_>,roles:Roles3,dirty:&[QubitId],forbidden:&[QubitId])->Vec<QubitId>{
    assert_eq!((ctx.compact.len(),ctx.ring.len(),ctx.q.len()),(258,257,128));
    let ports:Vec<_>=ctx.meta.y.iter().chain(&ctx.meta.sum).chain(ctx.compact)
        .chain(ctx.ring).chain(ctx.q).copied().chain([ctx.phase]).chain(roles.ports()).collect();
    assert_eq!(ports.len(),ports.iter().copied().collect::<BTreeSet<_>>().len());
    assert!(forbidden.iter().all(|q|!ports.contains(q)));
    let mut excluded=metadata_ports(ctx.meta);excluded.extend(ctx.compact);
    excluded.extend([ctx.phase]);excluded.extend(roles.ports());excluded.extend(forbidden);
    let pool:Vec<_>=dirty.iter().chain(ctx.ring).chain(ctx.q).copied().collect();
    let d=filtered(&pool,&excluded);assert!(d.len()>=20);d
}
fn literal3(b:&mut B,c:&[(QubitId,bool)],t:QubitId,dirty:&[QubitId]){
    assert!(!c.iter().any(|p|p.0==t));
    assert_eq!(c.len(),c.iter().map(|p|p.0).collect::<BTreeSet<_>>().len());
    let mut held:Vec<_>=c.iter().map(|p|p.0).collect();held.push(t);
    let d=filtered(dirty,&held);assert!(d.len()>=c.len().saturating_sub(2));
    mc_xor(b,c,t,&[],&d);
}

/// U5: guard terms are evaluated in original E/S, outside the Z view.
/// The two extra view plays move only metadata and returned dirty donors;
/// both complete gather permutations close even when activity is false.
pub(crate) fn park_or_fetch3(b:&mut B,meta:&SumSize,size:Size,range:(usize,usize),
    lane:impl Fn(usize)->Option<QubitId>,r:Roles3,guard:Guard,dirty:&[QubitId]){
    assert!(range.0<=range.1&&range.1-range.0<128);
    let mut leaves=vec![];let mut owners=BTreeSet::new();
    for v in range.0..=range.1{if let Some(cell)=lane(v){
        assert!(!r.ports().contains(&cell)&&!meta.y.contains(&cell)&&!meta.sum.contains(&cell));
        assert!(owners.insert(cell));
        let key=match size{Size::Y=>{assert!((1..=128).contains(&v));v-1},Size::Z=>v%128};
        leaves.push((key,cell));
    }}
    if leaves.is_empty(){return;}
    leaves.sort_unstable_by_key(|p|p.0);assert!(leaves.windows(2).all(|w|w[0].0<w[1].0));
    let mut held=metadata_ports(meta);held.extend(r.ports());held.extend(owners.iter());
    let d=filtered(dirty,&held);assert!(d.len()>=12);
    let view=match size{Size::Y=>vec![],Size::Z=>meta.z_epoch(b,&d)};
    let mut swaps=vec![];let root=super::super::midg::swap_tree(&meta.y,&leaves,7,&mut swaps);
    b.play(&view,false);for &(c,a,z)in &swaps{b.cswap(c,a,z);}b.play(&view,true);
    b.cx(root,r.flight);
    for mut c in guard.terms(meta,true){c.extend([(r.activity,false),(r.flight,false)]);literal3(b,&c,root,&d);}
    b.cx(root,r.flight);
    b.play(&view,false);for &(c,a,z)in swaps.iter().rev(){b.cswap(c,a,z);}b.play(&view,true);
}

fn reflect3(b:&mut B,meta:&SumSize,rsize:Size,raw:&[QubitId],r:Roles3,dirty:&[QubitId]){
    let rotation=rotation_record(b,meta,rsize,raw,r.flight,dirty);b.play(&rotation,true);
    for code in 0..32{
        let length=32-code;if length<2{continue;}
        let mut c=eq(&meta.sum,code);c.push((r.activity,false));
        literal3(b,&c,r.flight,dirty);
        for i in 0..length/2{b.cswap(r.flight,raw[i],raw[length-1-i]);}
        literal3(b,&c,r.flight,dirty);
    }b.play(&rotation,false);
}

pub(crate) fn digit3(b:&mut B,ctx:&Context<'_>,roles:Roles3,ht:bool,
    ranges:Ranges,dirty:&[QubitId],forbidden:&[QubitId])->Session{
    assert!(98<=ranges.z.0&&ranges.z.0<=ranges.z.1&&ranges.z.1<=256);
    assert!(1<=ranges.y.0&&ranges.y.0<=ranges.y.1&&ranges.y.1<=128);
    let bank=checked_bank3(ctx,roles,dirty,forbidden);let meta=ctx.meta;
    let raw:Vec<_>=ctx.compact.iter().copied().chain([ctx.phase]).collect();
    let(rsize,rr,tsize,tr)=if ht{
        (Size::Y,ranges.y,Size::Z,ranges.z)
    }else{(Size::Z,ranges.z,Size::Y,ranges.y)};
    if ht{b.cx(roles.activity,ctx.phase);}
    expand_pre(b,meta,tsize,tr,&raw,roles.activity,roles.sign,&bank);

    if ht{
        // Q is unparked for this entire digit epoch. The full coordinate
        // pair closes before sign/reflection and every raw transition.
        super::super::normalized_payload_q::k4_q3::forward3(b,meta,ctx.q,&raw,roles,ranges,&bank,forbidden);
    }else{
        // The unused raw-Q operand is positive and unparked on A for this
        // entire Z half. Keep its normalized leading-ONE carry through all
        // quotient bits; metadata returns to raw E/S before each park.
        let zframe=super::super::single_z_maj::frame_record(b,meta,ctx.q);
        let leading=super::super::single_z_maj::k4_z3::leading_one_record3(b,meta,ctx.ring,
            roles,ranges.z,&bank);
        b.play(&zframe,false);b.play(&leading,false);
        for k in (0..KE).rev(){
            if (rr.0+tr.0).max(226)>257usize.saturating_sub(k){continue;}
            super::super::single_z_maj::k4_z3::apply3(b,meta,ctx.q,&raw,ctx.ring,
                roles,ranges,k,false,&bank,forbidden);
            for band in Y_BANDS{
                if intersect(ranges.y,band).is_none(){continue;}
                let Some(mut bounds)=branch_range(rsize,rr,band)else{continue;};
                let end=(k+bounds.1+1).min(LOGICAL_P);bounds.1=bounds.1.min(end-k-1);
                if bounds.0>bounds.1{continue;}
                let guard=Guard{y:band,sum_limit:31-k as isize};
                // Preserve each original complete park guard and leaf set.
                // The disjoint Y bands now consume the single merged e.
                park_or_fetch3(b,meta,rsize,bounds,|r|(r+k<LOGICAL_P).then(||raw[r+k]),roles,guard,&bank);
            }
        }
        b.play(&leading,true);b.play(&zframe,true);
    }
    read_selected(b,meta,tsize,tr,&raw,|t|258-t,roles.sign,roles.activity,roles.flight,&bank);
    reflect3(b,meta,rsize,&raw,roles,&bank);

    if !ht{
        // Exact inverse Q epoch; sign is retained off its narrowed A.
        super::super::normalized_payload_q::k4_q3::inverse3(b,meta,ctx.q,&raw,roles,ranges,&bank,forbidden);
    }else{
        let zframe=super::super::single_z_maj::frame_record(b,meta,ctx.q);
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
                park_or_fetch3(b,meta,tsize,bounds,|t|(t+1+k<LOGICAL_P).then(||raw[257-t-k]),roles,fetch,&bank);
            }
            super::super::single_z_maj::k4_z3::apply3(b,meta,ctx.q,&raw,ctx.ring,
                roles,ranges,k,true,&bank,forbidden);
        }
        b.play(&zframe,true);
    }
    // R+T<=257: [R<=l<258-T] = [l<R] XOR [l<258-T]. Sign0 offA.
    let end=258-tr.0;
    walk(b,meta,rsize,rr.0,end,roles.flight,&[],&bank,None,
        |l|(l+1,rr.1),|b,l|b.ccx(roles.sign,roles.flight,raw[l]));
    walk(b,meta,tsize,rr.0,end.min(258),roles.flight,&[],&bank,None,
        |l|(tr.0,(257-l).min(tr.1)),|b,l|b.ccx(roles.sign,roles.flight,raw[l]));
    // Strict complement never changes raw[R], so erase sign first.
    read_selected(b,meta,rsize,rr,&raw,|r|r,roles.sign,roles.activity,roles.flight,&bank);
    // Final l258 includes the complete active R range, so the retained
    // mask equals A. A0 made every delta query zero, including off-range
    // inactive metadata. Clear it by this identity rather than re-decoding.
    walk(b,meta,rsize,rr.0+1,LOGICAL_P,roles.flight,&[(roles.activity,false)],&bank,Some(roles.activity),
        |l|(rr.0,(l-1).min(rr.1)),|b,l|b.cx(roles.flight,raw[l]));
    Session{raw,activity:roles.activity,phase:ctx.phase,ht}
}


/// Default goes straight to the original API before any candidate check.
/// work is used only as a forbidden diagnostic spectator in the candidate.
pub(crate) fn digit_diagnostic(b:&mut B,ctx:&Context<'_>,r:Roles,ht:bool,ranges:Ranges,
    arithmetic:&mut impl Arithmetic,dirty:&[QubitId],selector:Diagnostic)->Session{
    if selector==Diagnostic::Parent{return super::digit(b,ctx,r,ht,ranges,arithmetic,dirty);}
    digit3(b,ctx,Roles3{activity:r.activity,flight:r.flight,sign:r.sign},ht,ranges,dirty,&[r.work])
}

/// The caller certifies q/bq payload transitions returned, as required by
/// the unchanged finish_phase POST identity. This is not an earlier PH close.
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum CloseBoundary { PayloadTransitionsReturned }
pub(crate) fn finish_phase3(b:&mut B,meta:&SumSize,session:&Session,range:(usize,usize),
    flag:QubitId,dirty:&[QubitId],forbidden:&[QubitId],boundary:CloseBoundary){
    assert_eq!(boundary,CloseBoundary::PayloadTransitionsReturned);
    assert!(forbidden.iter().all(|q|!session.raw.contains(q)&&*q!=session.activity&&*q!=flag
        &&!meta.y.contains(q)&&!meta.sum.contains(q)));
    let mut held=forbidden.to_vec();held.push(session.phase);
    super::finish_phase(b,meta,session,range,flag,&filtered(dirty,&held));
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Address3 {
    /// The original eighth bit on tag, globally zero at this exact boundary.
    HostedTag(QubitId),
    /// Public column Z lower bound; never silently replace it by range.lo.
    SevenBit { column_z_floor:usize },
}

/// U12. Keep the complete public range: capped gathered leaves followed by
/// exact disambiguated per-Z tails. Z256 must take the hosted path.
pub(crate) fn narrow3(b:&mut B,meta:&SumSize,compact:&[QubitId],q:&[QubitId],upper:Option<&[QubitId]>,
    range:(usize,usize),act:QubitId,flag:QubitId,address:Address3,dirty:&[QubitId],forbidden:&[QubitId],ht:bool){
    assert_eq!((compact.len(),q.len()),(258,128));
    assert!(98<=range.0&&range.0<=range.1&&range.1<=256);
    let ports:Vec<_>=meta.y.iter().chain(&meta.sum).chain(compact).chain(q)
        .copied().chain(upper.into_iter().flatten().copied()).chain([act,flag]).collect();
    assert_eq!(ports.len(),ports.iter().copied().collect::<BTreeSet<_>>().len());
    assert!(forbidden.iter().all(|p|!ports.contains(p)));
    if let Address3::HostedTag(byte)=address{
        assert!(!ports.contains(&byte)&&!forbidden.contains(&byte));
        super::narrow_gathered(b,meta,compact,q,upper,range,act,flag,byte,
            &filtered(dirty,forbidden),ht);return;
    }
    let Address3::SevenBit{column_z_floor}=address else{unreachable!()};
    assert!(98<=column_z_floor&&column_z_floor<=range.0&&range.1<=255,
        "Z256 requires the original hosted eight-bit address");
    let lo=range.0.max(129);
    if lo>range.1||range.1-lo+1<32{
        super::narrow(b,meta,compact,q,upper,range,act,flag,&filtered(dirty,forbidden),ht);return;
    }
    if range.0<129{super::narrow(b,meta,compact,q,upper,(range.0,128),act,flag,
        &filtered(dirty,forbidden),ht);}
    let mut held=metadata_ports(meta);held.extend(compact);held.extend(q);
    held.extend([act,flag]);held.extend(forbidden);
    let bank=filtered(dirty,&held);assert!(bank.len()>=12);
    let cap=range.1.min(column_z_floor+127);assert!(lo<=cap);
    let view=meta.z_epoch(b,&bank);
    let payload:Vec<_>=if ht{compact.iter().rev().copied().collect()}else{compact.to_vec()};
    let support:BTreeSet<_>=[0,1].into_iter().collect();
    // hi128+127: unlike the eight-bit form, this passes exactly seven levels.
    let pair=record(b,|b|super::super::frogdrop::rot_by_off_care(b,&payload,&meta.y,128,255,true,&support));
    let leaves:Vec<_>=(lo..=cap).map(|z|(z-128,q[256-z])).collect();
    let mut swaps=vec![];let root=super::super::midg::swap_tree(&meta.y,&leaves,7,&mut swaps);
    let guard=record(b,|b|{
        let(mut low,high)=(lo-128,cap-127);
        while low<high{
            let mut free=if low==0{7}else{low.trailing_zeros()as usize};
            while low+(1usize<<free)>high{free-=1;}
            let mut c:Vec<_>=(free..7).map(|i|(meta.y[i],low>>i&1==0)).collect();
            c.extend([(act,false),(root,true)]);literal3(b,&c,flag,&bank);low+=1usize<<free;
        }
    });
    b.play(&view,false);
    for z in cap+1..=range.1{
        let extra=[(act,false),(q[256-z],true)];
        query(b,meta,Size::Z,z,flag,&extra,&bank);
        let t=if ht{256-z}else{z};b.ccx(flag,compact[t+1],compact[t]);
        query(b,meta,Size::Z,z,flag,&extra,&bank);
    }
    b.play(&pair,false);for &(c,a,z)in &swaps{b.cswap(c,a,z);}
    b.play(&guard,false);b.ccx(flag,payload[usize::from(!ht)],payload[usize::from(ht)]);b.play(&guard,true);
    for &(c,a,z)in swaps.iter().rev(){b.cswap(c,a,z);}b.play(&pair,true);b.play(&view,true);
}

/// Bind every public field consumed by these K4 routes to the literal
/// frozen schedule. Parsing public metadata does not touch MAP_CTRL_S or
/// read a runtime selector. No sampled quantum value chooses a route.
pub(crate) fn source_parameters(cp:&super::super::frogdrop_col::ColPar){
    let schedule=super::super::frogdrop_sched::from_text(super::super::pointadd_frogdrop::SCHED_FROGDROP);
    assert_eq!(schedule.cols.len(),203);assert!(cp.col<schedule.cols.len()&&!cp.nomap);
    assert_eq!((cp.n,cp.nq,cp.h,cp.l0,cp.qb),(257,128,0,128,30));
    let e=&schedule.cols[cp.col];let cap=if cp.col==0{256}else{255};
    assert_eq!(cp.sz,(e.sz.0.min(cap),e.sz.1.min(cap)));
    assert_eq!(cp.sy,(e.sy.0.min(255),e.sy.1.min(255)));
    assert_eq!((cp.hr,cp.ht,cp.sw,cp.dn,cp.dl,cp.dq),(e.hr,e.ht,e.sw,e.dn,e.dl,e.dq));
    let previous=cp.col.checked_sub(1).map(|i|&schedule.cols[i]);
    assert_eq!(cp.pht,previous.is_some_and(|p|p.ht));assert_eq!(cp.psw,previous.is_some_and(|p|p.sw));
    assert_eq!(cp.psy,previous.map(|p|(p.sy.0.min(255),p.sy.1.min(255))).unwrap_or((0,0)));
    assert_eq!(cp.tt,cp.col==1);
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum EntryBoundary { HrAfterControllerLeave, HtBeforeStage5Arithmetic }
/// Whole named payload half. K2 still owns HT5 proper after this digit;
/// K3 owns HR ticks after this digit. Neither transition is synthesized here.
pub(crate) fn digit_at_boundary3(b:&mut B,ctx:&Context<'_>,r:Roles3,
    cp:&super::super::frogdrop_col::ColPar,boundary:EntryBoundary,dirty:&[QubitId],forbidden:&[QubitId])->Session{
    source_parameters(cp);
    let fixed=(!cp.hr||cp.tt)&&cp.sy.1<=96&&!(cp.sw||cp.psw||cp.dl||cp.dq);
    assert!(!fixed,"K4 direct payload excludes inherited fixed-middle route");
    let ht=boundary==EntryBoundary::HtBeforeStage5Arithmetic;
    assert!(if ht{cp.ht}else{cp.hr});
    digit3(b,ctx,r,ht,Ranges{z:cp.sz,y:(cp.sy.0.max(1),cp.sy.1.min(128))},dirty,forbidden)
}
