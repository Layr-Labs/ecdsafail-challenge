//! Complete K4 three-role payload sibling. No production selector reads this module.
//! The caller retains COMPLETE activity before digit3 and keeps PH as raw[258]
//! until all payload transitions and finish_phase3 have returned.
use super::*;
pub(crate) use super::FlagHost;

#[derive(Clone,Copy,Debug,Default,PartialEq,Eq)]
pub(crate) enum Diagnostic { #[default] Parent, ThreeRole }
#[derive(Clone,Copy,Debug)]
pub(crate) struct Roles3 {pub activity:QubitId,pub flight:QubitId,pub sign:QubitId}
impl Roles3 {
    pub(crate) fn lane(activity:QubitId,flight:QubitId,sign:QubitId)->Self{Self{activity,flight,sign}}
    pub(crate) fn ports(self)->[QubitId;3]{[self.activity,self.flight,self.sign]}
}
/// Scalar roles of the admitted DS/ZH digit. The sign is encoded in
/// (activity,flight); no physical third role is passed by the caller.
#[derive(Clone,Copy,Debug)]
pub(crate) struct Roles2 {pub activity:QubitId,pub flight:QubitId}
const NONLANE_SIGN:QubitId=QubitId(u64::MAX);

pub(crate) fn filtered(dirty:&[QubitId],excluded:&[QubitId])->Vec<QubitId>{donors(dirty,excluded)}

fn checked_bank3(ctx:&Context<'_>,roles:Roles3,dirty:&[QubitId],forbidden:&[QubitId])->Vec<QubitId>{
    assert_eq!((ctx.compact.len(),ctx.ring.len(),ctx.q.len()),(258,257,128));
    let ports:Vec<_>=ctx.meta.y.iter().chain(&ctx.meta.sum).chain(ctx.compact)
        .chain(ctx.ring).chain(ctx.q).copied().chain([ctx.phase]).chain(roles.ports()).filter(|q|super::super::c659::retained(*q)).collect();
    assert_eq!(ports.len(),ports.iter().copied().collect::<BTreeSet<_>>().len());
    assert!(forbidden.iter().all(|q|!ports.contains(q)));
    let mut excluded=metadata_ports(ctx.meta);excluded.extend(ctx.compact);
    excluded.extend([ctx.phase]);excluded.extend(roles.ports().into_iter().filter(|q|super::super::c659::retained(*q)));excluded.extend(forbidden);
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

/// The flight lane is clean between read #1 and the inverse epoch, by the
/// digit3 schedule. The overflow predicate is an exact union of z_epoch
/// equalities over all 4096 E/S words, and is erased after the rotation.
fn rotate_z7_latched_record(b:&mut B,meta:&SumSize,raw:&[QubitId],
    floor:usize,flag:QubitId,dirty:&[QubitId])->Vec<G>{
    assert!(floor+128<=256);
    assert!(!raw.contains(&flag));
    let d=filtered(dirty,&[flag]);
    let view=meta.z_epoch(b,&d);
    let mut terms=vec![];
    for z in floor+128..=256 {terms.extend(meta.z_terms(z));}
    record(b,|b|{
        b.play(&view,false);
        meta.xor_terms(b,terms.clone(),flag,&[],&d);
        b.play(&view,true);
        rotate_const(b,raw,128,Some(flag));
        let low=super::super::direct_frame::rotate_z7_record(b,meta,raw,floor,0,false,&d);
        b.play(&low,false);
        b.play(&view,false);
        meta.xor_terms(b,terms,flag,&[],&d);
        b.play(&view,true);
    })
}

fn reflect3(b:&mut B,meta:&SumSize,rsize:Size,range:(usize,usize),raw:&[QubitId],r:Roles3,dirty:&[QubitId]){
    let overflow=range.1.saturating_sub(range.0+127);
    // The W1a 8th stage is exact on the active box; paired playback closes
    // its passenger action off the box because every reflect swap is A-gated.
    let rotation=if wp3_g1_enabled()&&matches!(rsize,Size::Z)&&overflow>0&&overflow<=16{
        if std::env::var("C658_WP3_ROT_LATCH").as_deref()!=Ok("0"){
            rotate_z7_latched_record(b,meta,raw,range.0,r.flight,dirty)
        }else{
            super::super::direct_frame::rotate_z7_record(b,meta,raw,range.0,overflow,false,dirty)
        }
    }else{rotation_record(b,meta,rsize,raw,r.flight,dirty)};
    b.play(&rotation,true);
    for code in 0..32{
        let length=32-code;if length<2{continue;}
        let mut c=eq(&meta.sum,code);c.push((r.activity,false));
        if wp3_ff_enabled(){
            for i in 0..length/2{
                let x=raw[i];let y=raw[length-1-i];
                b.cx(x,y);let mut folded=c.clone();folded.push((y,false));
                literal3(b,&folded,x,dirty);b.cx(x,y);
            }
        }else{
            literal3(b,&c,r.flight,dirty);
            for i in 0..length/2{b.cswap(r.flight,raw[i],raw[length-1-i]);}
            literal3(b,&c,r.flight,dirty);
        }
    }b.play(&rotation,false);
}

fn wp3_enabled()->bool { std::env::var("C658_WP3").as_deref()==Ok("1") }
fn wp3_g1_enabled()->bool { wp3_enabled() && std::env::var("C658_WP3_G1").as_deref()!=Ok("0") }
fn wp3_ff_enabled()->bool { wp3_enabled() && std::env::var("C658_WP3_FF").as_deref()!=Ok("0") }
fn ds_enabled()->bool { wp3_enabled() && std::env::var("C658_WP3_DS").as_deref()==Ok("1") }

/// P-DWALK: after the GF(2) difference transform, a suffix XOR is a
/// single point XOR. Both address gathers are fully uncomputed.
fn gathered_point_xor(b:&mut B,meta:&SumSize,size:Size,range:(usize,usize),
    lane:impl Fn(usize)->QubitId,control:QubitId,byte:QubitId,dirty:&[QubitId]){
    if range.0>range.1{return;}
    if control==byte&&matches!(size,Size::Z){
        // In C1 the cut carries sign, so it cannot also hold the eighth Z
        // address bit.  Query each physical point in the exact Z view.
        in_view(b,meta,size,dirty,|b|for v in range.0..=range.1{
            query(b,meta,size,v,lane(v),&[(control,false)],dirty);
        });
        return;
    }
    let address=if matches!(size,Size::Z){
        super::super::direct_frame::z_byte_record(b,meta,byte,dirty)
    }else{vec![]};
    let mut word=meta.y.to_vec();if matches!(size,Size::Z){word.push(byte);}
    let leaves:Vec<_>=(range.0..=range.1).map(|v|(v-1,lane(v))).collect();
    let mut swaps=vec![];
    let root=super::super::midg::swap_tree(&word,&leaves,word.len(),&mut swaps);
    b.play(&address,false);
    for &(c,a,z) in &swaps{b.cswap(c,a,z);}
    b.cx(control,root);
    for &(c,a,z) in swaps.iter().rev(){b.cswap(c,a,z);}
    b.play(&address,true);
}

fn difference_prefix(b:&mut B,raw:&[QubitId],lo:usize,end:usize,inverse:bool){
    assert!(lo<end&&end<=raw.len());
    if inverse{for i in lo+1..end{b.cx(raw[i-1],raw[i]);}}
    else{for i in (lo+1..end).rev(){b.cx(raw[i-1],raw[i]);}}
}

fn dwalk_sign(b:&mut B,meta:&SumSize,raw:&[QubitId],rsize:Size,rr:(usize,usize),
    tsize:Size,tr:(usize,usize),sign:QubitId,byte:QubitId,dirty:&[QubitId]){
    let lo=rr.0;let end=258-tr.0;assert!(lo<end&&end<=raw.len());
    difference_prefix(b,raw,lo,end,false);
    gathered_point_xor(b,meta,rsize,(rr.0,rr.1.min(end-1)),|r|raw[r],sign,byte,dirty);
    let thi=tr.1.min(257-lo);
    gathered_point_xor(b,meta,tsize,(tr.0,thi),|t|raw[258-t],sign,byte,dirty);
    // T=tr.0 selects raw[end], outside the transformed segment; cancel it.
    in_view(b,meta,tsize,dirty,|b|{
        if sign==byte{
            query(b,meta,tsize,tr.0,raw[end],&[(sign,false)],dirty);
        }else{
            query(b,meta,tsize,tr.0,byte,&[(sign,false)],dirty);
            b.cx(byte,raw[end]);
            query(b,meta,tsize,tr.0,byte,&[(sign,false)],dirty);
        }
    });
    difference_prefix(b,raw,lo,end,true);
}

fn dwalk_activity(b:&mut B,meta:&SumSize,raw:&[QubitId],size:Size,
    range:(usize,usize),activity:QubitId,byte:QubitId,dirty:&[QubitId]){
    let lo=range.0+1;let end=LOGICAL_P;
    difference_prefix(b,raw,lo,end,false);
    gathered_point_xor(b,meta,size,range,|r|raw[r+1],activity,byte,dirty);
    difference_prefix(b,raw,lo,end,true);
}

/// C1 sign read.  Most Z ranges use W1a's flag-free seven-bit gather; the
/// few wider ranges use literal exact Z queries because cut is live data.
fn read_selected_cut(b:&mut B,meta:&SumSize,size:Size,range:(usize,usize),
    raw:&[QubitId],lane:impl Fn(usize)->usize,tag:QubitId,cut:QubitId,dirty:&[QubitId]){
    if matches!(size,Size::Z)&&range.1-range.0+1>=8
        &&range.1.saturating_sub(range.0+127)>16{
        in_view(b,meta,size,dirty,|b|for v in range.0..=range.1{
            query(b,meta,size,v,cut,&[(tag,false),(raw[lane(v)],false)],dirty);
        });
    }else{read_selected(b,meta,size,range,raw,lane,cut,tag,cut,dirty);}
}

pub(crate) fn digit3(b:&mut B,ctx:&Context<'_>,roles:Roles3,ht:bool,
    ranges:Ranges,dirty:&[QubitId],forbidden:&[QubitId])->Session{
    assert!(98<=ranges.z.0&&ranges.z.0<=ranges.z.1&&ranges.z.1<=256);
    assert!(1<=ranges.y.0&&ranges.y.0<=ranges.y.1&&ranges.y.1<=128);
    let bank=checked_bank3(ctx,roles,dirty,forbidden);let meta=ctx.meta;
    let ds=ds_enabled();
    let zh=wp3_enabled()&&std::env::var("C658_WP3_ZH").as_deref()==Ok("1");
    let raw:Vec<_>=ctx.compact.iter().copied().chain([ctx.phase]).collect();
    let(rsize,rr,tsize,tr)=if ht{
        (Size::Y,ranges.y,Size::Z,ranges.z)
    }else{(Size::Z,ranges.z,Size::Y,ranges.y)};
    if ht{b.cx(roles.activity,ctx.phase);}
    // At entry e=0 on the inherited digit ABI, so cut can carry PRE's
    // temporary flag and return to zero before the quotient epoch.
    let pre_flag=if wp3_enabled(){roles.flight}else{roles.sign};
    expand_pre(b,meta,tsize,tr,&raw,roles.activity,pre_flag,&bank);

    if ht{
        // Q is unparked for this entire digit epoch. The full coordinate
        // pair closes before sign/reflection and every raw transition.
        super::super::normalized_payload_q::k4_q3::forward3(b,meta,ctx.q,&raw,roles,ranges,&bank,forbidden);
    }else{
        // The unused raw-Q operand is positive and unparked on A for this
        // entire Z half. Keep its normalized leading-ONE carry through all
        // quotient bits; metadata returns to raw E/S before each park.
        let zframe=super::super::single_z_maj::frame_record(b,meta,ctx.q);
        let leading=if zh{vec![]}else{super::super::single_z_maj::k4_z3::leading_one_record3(
            b,meta,ctx.ring,roles,ranges.z,&bank)};
        b.play(&zframe,false);if !zh{b.play(&leading,false);}
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
        if !zh{b.play(&leading,true);}b.play(&zframe,true);
    }
    if ds{
        // The sign source is raw[R+32-S], one cell past reflect3's
        // [R,R+32-S) reversal.  Moving the read after reflection keeps cut
        // clean for the exact latched eighth rotation stage.
        reflect3(b,meta,rsize,rr,&raw,roles,&bank);
        read_selected_cut(b,meta,tsize,tr,&raw,|t|258-t,roles.activity,roles.flight,&bank);
    }else{
        read_selected(b,meta,tsize,tr,&raw,|t|258-t,roles.sign,roles.activity,roles.flight,&bank);
        reflect3(b,meta,rsize,rr,&raw,roles,&bank);
    }

    #[cfg(test)]
    if std::env::var("R14_DIG_TRACE_STOP").as_deref()==Ok("read1"){
        return Session{raw,activity:roles.activity,phase:ctx.phase,ht,finish_flag:None};
    }
    if !ht{
        // Exact inverse Q epoch; sign is retained off its narrowed A.
        super::super::normalized_payload_q::k4_q3::inverse3(b,meta,ctx.q,&raw,roles,ranges,&bank,forbidden);
    }else{
        let zframe=super::super::single_z_maj::frame_record(b,meta,ctx.q);
        b.play(&zframe,false);
        if ds{b.cx(roles.flight,roles.activity);}
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
        if ds{b.cx(roles.flight,roles.activity);}
        b.play(&zframe,true);
    }
    #[cfg(test)]
    if std::env::var("R14_DIG_TRACE_STOP").as_deref()==Ok("inverse"){
        return Session{raw,activity:roles.activity,phase:ctx.phase,ht,finish_flag:None};
    }
    // R+T<=257: [R<=l<258-T] = [l<R] XOR [l<258-T]. Sign0 offA.
    let end=258-tr.0;
    if wp3_enabled(){
        dwalk_sign(b,meta,&raw,rsize,rr,tsize,tr,
            if ds{roles.flight}else{roles.sign},roles.flight,&bank);
    }else{
        walk(b,meta,rsize,rr.0,end,roles.flight,&[],&bank,None,
            |l|(l+1,rr.1),|b,l|b.ccx(roles.sign,roles.flight,raw[l]));
        walk(b,meta,tsize,rr.0,end.min(258),roles.flight,&[],&bank,None,
            |l|(tr.0,(257-l).min(tr.1)),|b,l|b.ccx(roles.sign,roles.flight,raw[l]));
    }
    #[cfg(test)]
    if std::env::var("R14_DIG_TRACE_STOP").as_deref()==Ok("walk"){
        return Session{raw,activity:roles.activity,phase:ctx.phase,ht,finish_flag:None};
    }
    // Strict complement never changes raw[R], so erase sign first.
    if ds{read_selected_cut(b,meta,rsize,rr,&raw,|r|r,roles.activity,roles.flight,&bank);}
    else{read_selected(b,meta,rsize,rr,&raw,|r|r,roles.sign,roles.activity,roles.flight,&bank);}
    #[cfg(test)]
    if std::env::var("R14_DIG_TRACE_STOP").as_deref()==Ok("read2"){
        return Session{raw,activity:roles.activity,phase:ctx.phase,ht,finish_flag:None};
    }
    // Final l258 includes the complete active R range, so the retained
    // mask equals A. A0 made every delta query zero, including off-range
    // inactive metadata. Clear it by this identity rather than re-decoding.
    if wp3_enabled(){
        dwalk_activity(b,meta,&raw,rsize,rr,roles.activity,roles.flight,&bank);
    }else{
        walk(b,meta,rsize,rr.0+1,LOGICAL_P,roles.flight,&[(roles.activity,false)],&bank,Some(roles.activity),
            |l|(rr.0,(l-1).min(rr.1)),|b,l|b.cx(roles.flight,raw[l]));
    }
    Session{raw,activity:roles.activity,phase:ctx.phase,ht,finish_flag:Some(roles.flight)}
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
    let selected=if wp3_enabled(){session.finish_flag.unwrap_or(flag)}else{flag};
    let mut held=forbidden.to_vec();held.push(session.phase);
    super::finish_phase(b,meta,session,range,selected,&filtered(dirty,&held));
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Address3 {
    /// The original eighth bit on tag, globally zero at this exact boundary.
    HostedTag(QubitId),
    /// Exact per-Z query, including Z256, without a borrowed address bit.
    Direct,
    /// Public column Z lower bound; never silently replace it by range.lo.
    SevenBit { column_z_floor:usize },
}

/// U12. Keep the complete public range: capped gathered leaves followed by
/// exact disambiguated per-Z tails. Z256 must take the hosted path.
pub(crate) fn narrow3(b:&mut B,meta:&SumSize,compact:&[QubitId],q:&[QubitId],upper:Option<&[QubitId]>,
    range:(usize,usize),act:QubitId,flag:impl Into<FlagHost>,address:Address3,dirty:&[QubitId],forbidden:&[QubitId],ht:bool){
    let flag=flag.into();assert!(matches!(flag,FlagHost::Lane(q) if q!=act)||matches!(flag,FlagHost::Encoded{tag,cut} if cut==act&&tag!=cut));
    assert_eq!((compact.len(),q.len()),(258,128));
    assert!(98<=range.0&&range.0<=range.1&&range.1<=256);
    let ports:Vec<_>=meta.y.iter().chain(&meta.sum).chain(compact).chain(q)
        .copied().chain(upper.into_iter().flatten().copied()).chain([act])
        .chain(flag.ports().into_iter().filter(|q|*q!=act)).collect();
    assert_eq!(ports.len(),ports.iter().copied().collect::<BTreeSet<_>>().len());
    assert!(forbidden.iter().all(|p|!ports.contains(p)));
    if address==Address3::Direct{
        super::narrow(b,meta,compact,q,upper,range,act,flag,
            &filtered(dirty,forbidden),ht);return;
    }
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
    held.push(act);held.extend(flag.ports());held.extend(forbidden);
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
            c.extend([(act,false),(root,true)]);literal3(b,&c,flag.target(),&bank);low+=1usize<<free;
        }
    });
    b.play(&view,false);
    for z in cap+1..=range.1{
        let extra=[(act,false),(q[256-z],true)];
        query(b,meta,Size::Z,z,flag.target(),&extra,&bank);
        let t=if ht{256-z}else{z};flag.read_ccx(b,compact[t+1],compact[t],&bank);
        query(b,meta,Size::Z,z,flag.target(),&extra,&bank);
    }
    b.play(&pair,false);for &(c,a,z)in &swaps{b.cswap(c,a,z);}
    b.play(&guard,false);flag.read_ccx(b,payload[usize::from(!ht)],payload[usize::from(ht)],&bank);b.play(&guard,true);
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
    #[cfg(test)]
    if std::env::var("R14_DIG_MARK_COL").ok().and_then(|s|s.parse::<usize>().ok())==Some(cp.col)
        &&(std::env::var("R14_DIG_MARK_HT").as_deref()==Ok("1"))
            ==(boundary==EntryBoundary::HtBeforeStage5Arithmetic){
        b.x(ctx.phase);b.x(r.activity);b.x(ctx.phase);b.x(r.activity);
    }
    source_parameters(cp);
    let fixed=(!cp.hr||cp.tt)&&cp.sy.1<=96&&!(cp.sw||cp.psw||cp.dl||cp.dq);
    assert!(!fixed||(std::env::var("C658_WP4").as_deref()==Ok("1")
        &&(cp.col>=139||(cp.col==1
            &&std::env::var("C658_WP4_C1").as_deref()!=Ok("0")))),
        "K4 direct payload excludes inherited fixed-middle route");
    let ht=boundary==EntryBoundary::HtBeforeStage5Arithmetic;
    assert!(if ht{cp.ht}else{cp.hr});
    digit3(b,ctx,r,ht,Ranges{z:cp.sz,y:(cp.sy.0.max(1),cp.sy.1.min(128))},dirty,forbidden)
}

/// Additive toggle-free call. Valid only with WP3, DS, and ZH enabled,
/// at a direct HR/HT digit boundary. The selected branches encode sign in
/// (activity,flight) and never emit an operation on the synthetic sign ID.
/// The sentinel is only a uniqueness witness for inherited port checks;
/// F3-W3b compares the complete emitted tapes against Roles3 on every
/// source direct-digit column under the admitted gates.
pub(crate) fn two_role_ready()->bool{wp3_enabled()&&ds_enabled()
    &&std::env::var("C658_WP3_ZH").as_deref()==Ok("1")}

pub(crate) fn digit_at_boundary2(b:&mut B,ctx:&Context<'_>,r:Roles2,
    cp:&super::super::frogdrop_col::ColPar,boundary:EntryBoundary,
    dirty:&[QubitId],forbidden:&[QubitId])->Session{
    assert!(two_role_ready());
    assert!((b.width() as u64)<NONLANE_SIGN.0);
    digit_at_boundary3(b,ctx,Roles3{activity:r.activity,flight:r.flight,
        sign:NONLANE_SIGN},cp,boundary,dirty,forbidden)
}

#[cfg(test)]
#[path="r14_dig_fixture.rs"]
mod r14_dig_fixture;
