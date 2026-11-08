//! Focused WP5 fixtures. This module is included from the owned counter source.
use super::{counter3_with, B};
use super::super::{frogdrop::direct_map::k1_map3::{Boundary,Context,Roles3},
    frogdrop_sched,pointadd_frogdrop,k1_complete_io as io};
use crate::circuit::QubitId;

fn initial(ring:&[QubitId],q:&[QubitId],payload:&[QubitId],ph:QubitId)->io::Image {
    let mut image=io::Image::zero();
    let mut seed=0xa54f_98d6_7721_44b1u64;
    for &wire in ring.iter().chain(q[..64].iter()).chain(payload) {
        seed^=seed<<13;seed^=seed>>7;seed^=seed<<17;
        image.q[wire.0 as usize]=seed;
    }
    // 16 fresh DONE, 16 already DONE with cnt=1, 16 with cnt=2,
    // and 16 inactive passengers. All S and the old toggle are clean.
    image.q[ph.0 as usize]=0x0000_ffff_ffff_ffff;
    image.q[q[121].0 as usize]=0x0000_0000_ffff_0000;
    image.q[q[122].0 as usize]=0x0000_ffff_0000_0000;
    image
}

fn run(wp5:bool,inverse:bool)->(io::Image,io::Image,u64){
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let cp=&cps[120];assert!(cp.dn&&cp.fin);
    let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let mut ring=b.alloc_n(256);let payload=b.alloc_n(258);ring.extend(b.alloc_n(1));
    let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
    assert_eq!(b.width(),659);
    let ctx=Context{ring:&ring,q:&q,y:&y,sum:&sum,
        roles:Roles3{tag:pool[0],cut:pool[1],toggle:pool[2]},ph,
        payload:Some(&payload),terminal_loans:&[],boundary:Boundary::Stage10Returned};
    let before=initial(&ring,&q,&payload,ph);
    let scope=io::begin(before.clone(),b"r14-k1-counter3",io::RECORD_OP_CAP);
    if wp5 {io::forbid(pool[2]);}
    let bank=ctx.donors();
    b.begin();counter3_with(&mut b,&ctx,cp,&bank,wp5);let tape=b.end();
    b.play(&tape,false);if inverse{b.play(&tape,true);}b.flush_global();
    let(after,receipt)=io::finish(scope);
    assert_eq!(after.phase,0,"WP5 counter phase");
    if !inverse {
        assert_eq!(after.q[q[121].0 as usize],0x0000_ffff_0000_ffff,"fresh to 1; cnt1 to 2; cnt2 to 3");
        assert_eq!(after.q[q[122].0 as usize],0x0000_ffff_ffff_0000,"cnt1 and cnt2 high bit");
        for &wire in &q[123..128] {assert_eq!(after.q[wire.0 as usize],0);}
        for &wire in sum.iter().chain([pool[1],pool[2]].iter()) {assert_eq!(after.q[wire.0 as usize],0);}
    }
    (before,after,receipt.ops)
}

#[test]
fn r14_k1_f5_cnt_fresh_done_and_inverse(){
    let (_initial,base,base_ops)=run(false,false);
    let (_initial,new,new_ops)=run(true,false);
    base.signed_eq(&new,"F5-CNT base/new");
    let (before,after,_) = run(true,true);
    before.signed_eq(&after,"F5-CNT WP5 inverse");
    let (before,after,_) = run(false,true);
    before.signed_eq(&after,"F5-CNT base inverse");
    eprintln!("F5_CNT_PASS fresh=16 cnt1=16 cnt2=16 inactive=16 base_ops={base_ops} new_ops={new_ops} phase=0");
}

#[test]
fn r14_k1_f5_cnt_increment_exhaustive(){
    for chunk in 0..4 {
        for new in [false,true] {
            let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
            let ctrl=b.alloc();let bits=b.alloc_n(7);let clean=b.alloc_n(6);let donor=b.alloc();
            let mut before=io::Image::zero();let mut expected=before.clone();
            for lane in 0..64 {
                let case=chunk*64+lane;let value=case/2;let enable=case%2==1;
                let mask=1u64<<lane;
                if enable{before.q[ctrl.0 as usize]|=mask;expected.q[ctrl.0 as usize]|=mask;}
                for j in 0..7 {
                    if value>>j&1!=0{before.q[bits[j].0 as usize]|=mask;}
                    if ((value+usize::from(enable))&127)>>j&1!=0{expected.q[bits[j].0 as usize]|=mask;}
                }
                if (case*37+11)%7<3{before.q[donor.0 as usize]|=mask;expected.q[donor.0 as usize]|=mask;}
            }
            let scope=io::begin(before.clone(),b"r14-k1-inc7",io::RECORD_OP_CAP);
            if new{io::forbid(clean[5]);}
            b.begin();
            if new{super::inc_wp5(&mut b,ctrl,&bits,&clean[..5],&[donor]);}
            else{super::super::arith::inc(&mut b,ctrl,&bits,&clean);}
            let tape=b.end();b.play(&tape,false);b.flush_global();
            let(after,_)=io::finish(scope);expected.signed_eq(&after,"F5-CNT inc7 exhaustive");
            let scope=io::begin(after,b"r14-k1-inc7-inverse",io::RECORD_OP_CAP);
            b.play(&tape,true);b.flush_global();
            let(restored,_)=io::finish(scope);before.signed_eq(&restored,"F5-CNT inc7 inverse");
        }
    }
    eprintln!("F5_CNT_INC7_PASS cases=256 ctrl=0,1 count=0..127 base,new inverse phase=0");
}

// Full K1 map adapter pairs on the original stage-10 source images.
fn map_context<'a>(ring:&'a[QubitId],q:&'a[QubitId],y:&'a[QubitId],sum:&'a[QubitId],
    ph:QubitId,pool:&[QubitId],terminal:&'a[QubitId],payload:bool)->Context<'a>{
    Context{ring,q,y,sum,roles:Roles3{tag:pool[0],cut:pool[1],
        toggle:if payload{pool[2]}else{terminal[0]}},ph,
        payload:payload.then_some(terminal),terminal_loans:if payload{&[]}else{&terminal[1..2]},
        boundary:Boundary::Stage10Returned}
}
fn map(b:&mut B,ctx:&Context<'_>,cp:&super::super::frogdrop_col::ColPar,inverse:bool){
    b.begin();super::super::frogdrop::direct_map::k1_map3::apply(b,ctx,cp,|b,target,donors|
        super::done3(b,ctx,target,&[],donors));
    let tape=b.end();b.play(&tape,inverse);
}
#[test]
fn r14_k1_m6_entry_and_stage_diagnostic(){
    use super::super::{frogdrop_col,k1_complete_caller};
    k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut source=k1_complete_caller::builder();let layout=k1_complete_caller::Layout::allocate(&mut source);
    let initial=k1_complete_caller::initial(&layout,true,0);
    let scope=io::begin(initial,b"r14-k1-m6-diagnostic",io::PRODUCER_OP_CAP);
    source.x(layout.fd.ring[256]);drop(source);drop(layout);
    let mut image=None;
    for cp in &cps[..=50] {
        let mut b=k1_complete_caller::builder();let mut l=k1_complete_caller::Layout::allocate(&mut b);
        frogdrop_col::set_counter_epoch(&mut l.fd,cp.col);
        let col=l.column(true);let mut middle=super::super::direct_middle::DirectMiddle;
        super::super::direct_column::through_stage10(&mut b,&col,cp,&mut middle);b.flush_global();
        if cp.col==50 {image=Some(io::snapshot().0);break;}
        super::finish_k1_observed(&mut b,&col,cp,|_|{});
        assert!(b.ops.is_empty()&&b.pending_count()==0);
    }
    let _=io::finish(scope);let image=image.unwrap();
    let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let mut ring=b.alloc_n(256);let p=b.alloc_n(258);ring.extend(b.alloc_n(1));
    let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
    let ctx=map_context(&ring,&q,&y,&sum,ph,&pool,&p,true);
    for entry_only in [true,false] {
        let mut after=Vec::new();
        for new in [false,true] {
            let scope=io::begin(image.clone(),b"r14-k1-m6-compare",io::RECORD_OP_CAP);
            super::super::frogdrop::direct_map::k1_map3::diagnostic_plain(&mut b,&ctx,&cps[50],new,entry_only);
            b.flush_global();after.push(io::finish(scope).0);
        }
        if entry_only {
            let m6=after[1].q[y[5].0 as usize];
            after[1].q[y[5].0 as usize]=0;
            after[1].q[pool[2].0 as usize]=m6;
        }
        after[0].signed_eq(&after[1],if entry_only{"M6 entry base/new"}else{"M6 stage base/new"});
        eprintln!("M6_DIAG_PASS entry_only={entry_only} col=50 phase=0");
    }
}

#[test]
#[allow(warnings)]
fn r14_k1_m6_entry_rare_states(){
    use super::super::{frogdrop_col,k1_complete_caller};
    assert!(super::wp5_enabled()&&super::super::c659::t23_enabled());
    k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let mut ring=b.alloc_n(256);let p=b.alloc_n(258);ring.extend(b.alloc_n(1));
    let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
    let ctx=map_context(&ring,&q,&y,&sum,ph,&pool,&p,true);
    let mut before=io::Image::zero();
    for lane in 0..64 {
        let mask=1u64<<lane;
        let (c,e,qhi,qlo)=match lane%8 {
            0=>(true,97,None,None),1=>(true,97,None,Some(0)),
            2=>(true,97,Some(96),Some(0)),3=>(true,127,None,None),
            4=>(true,127,None,Some(0)),5=>(false,31,Some(32),None),
            6=>(false,32,None,None),_=>(false,127,None,Some(0)),
        };
        if c{before.q[pool[0].0 as usize]|=mask;}
        for j in 0..7 {if e>>j&1!=0{before.q[y[j].0 as usize]|=mask;}}
        before.q[ring[256-e].0 as usize]|=mask;
        before.q[ring[256].0 as usize]|=mask;
        if let Some(j)=qhi{before.q[q[j].0 as usize]|=mask;}
        if let Some(j)=qlo{before.q[q[j].0 as usize]|=mask;}
        if lane%3==0{before.q[ph.0 as usize]|=mask;before.q[p[4].0 as usize]|=mask;}
    }
    let mut after=Vec::new();
    for new in [false,true] {
        let scope=io::begin(before.clone(),b"r14-k1-m6-rare-entry",io::RECORD_OP_CAP);
        if new{io::forbid(pool[2]);}
        b.begin();super::super::frogdrop::direct_map::k1_map3::diagnostic_plain(&mut b,&ctx,&cps[41],new,true);
        let tape=b.end();b.play(&tape,false);b.flush_global();
        let (image,_)=io::finish(scope);
        let scope=io::begin(image.clone(),b"r14-k1-m6-rare-inverse",io::RECORD_OP_CAP);
        b.play(&tape,true);b.flush_global();let (restored,_)=io::finish(scope);
        before.signed_eq(&restored,"M6 rare entry inverse");after.push(image);
    }
    let m6=after[1].q[y[5].0 as usize];after[1].q[y[5].0 as usize]=0;
    after[1].q[pool[2].0 as usize]=m6;
    after[0].signed_eq(&after[1],"M6 rare entry base/new");
    eprintln!("F_M6E_PASS C1_M97 C1_M127 C0_M32 Q0 Y128 inverse pool2=0 phase=0 cases=64");
}

#[test]
#[allow(warnings)] // rustc 1.93 early-lint renderer ICEs on this packed fixture otherwise.
fn r14_k1_m6_plain_rare_stage(){
    use super::super::{frogdrop_col,k1_complete_caller};
    assert!(super::wp5_enabled()&&super::super::c659::t23_enabled());
    k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let mut ring=b.alloc_n(256);let p=b.alloc_n(258);ring.extend(b.alloc_n(1));
    let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
    let ctx=map_context(&ring,&q,&y,&sum,ph,&pool,&p,true);
    for column in [41,60,81] {
        let mut before=io::Image::zero();
        for lane in 0..64 {
            let mask=1u64<<lane;
            let kind=lane%4;
            let e=if kind==2{127}else if kind==3{if column==60{56}else{32}}else{97};
            let c=kind!=3;
            if c{before.q[pool[0].0 as usize]|=mask;}else{before.q[ph.0 as usize]|=mask;}
            // A 128-bit Z lies inside the public sz box.  For the Y-even
            // case, p-Z*X must be divisible by 2^31 (X=1), so Z mod 2^31
            // is p mod 2^31 = 2^31-977.
            before.q[ring[127].0 as usize]|=mask;
            let zlow=if kind==1{(1u64<<31)-977}else{1};
            for j in 0..31 {if zlow>>j&1!=0{before.q[ring[j].0 as usize]|=mask;}}
            for j in 0..7 {if e>>j&1!=0{before.q[y[j].0 as usize]|=mask;}}
            before.q[ring[256-e].0 as usize]|=mask;
            let ylow=if kind==1{31}else if kind==3{1}else{0};
            before.q[ring[256-ylow].0 as usize]|=mask;
            if kind==3{before.q[ring[256].0 as usize]|=mask;}
            let qhi=if kind==2{Some(127)}else if kind==3{Some(e)}else{None};
            if let Some(h)=qhi{before.q[q[h].0 as usize]|=mask;}
            let qlo=if kind==2{5}else{0};before.q[q[qlo].0 as usize]|=mask;
            if lane%7==0{before.q[p[11].0 as usize]|=mask;}
        }
        for entry_only in [true,false] {
            let mut after=Vec::new();
            for new in [false,true] {
                let scope=io::begin(before.clone(),b"r14-k1-m6-rare-stage",io::RECORD_OP_CAP);
                if new{io::forbid(pool[2]);}
                b.begin();if super::wp5_m6a_enabled(){
                    super::super::frogdrop::direct_map::k1_map3::diagnostic_v(&mut b,&ctx,&cps[column],new,entry_only);
                }else{super::super::frogdrop::direct_map::k1_map3::diagnostic_plain(&mut b,&ctx,&cps[column],new,entry_only);}
                let tape=b.end();b.play(&tape,false);b.flush_global();
                let (image,_)=io::finish(scope);
                let scope=io::begin(image.clone(),b"r14-k1-m6-rare-stage-inv",io::RECORD_OP_CAP);
                b.play(&tape,true);b.flush_global();let (restored,_)=io::finish(scope);
                before.signed_eq(&restored,"M6 rare stage inverse");after.push(image);
            }
            if entry_only {let m6=after[1].q[y[5].0 as usize];after[1].q[y[5].0 as usize]=0;
                after[1].q[pool[2].0 as usize]=m6;}
            after[0].signed_eq(&after[1],if entry_only{"M6 rare entry base/new"}else{"M6 rare stage base/new"});
            eprintln!("F_M6B_STEP column={column} entry_only={entry_only} passed");
        }
        eprintln!("F_M6B_PASS column={column} C1_M97 C1_M127 C0_boundary ez=0,5,31 Y128 inverse pool2=0 phase=0");
    }
}

#[test]
#[allow(warnings)]
fn r14_k1_f_ea_plain_entry_exit(){
    use super::super::k1_complete_caller;
    assert!(super::wp5_enabled()&&super::wp5_m6a_enabled());
    k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let mut ring=b.alloc_n(256);let p=b.alloc_n(258);ring.extend(b.alloc_n(1));
    let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
    let ctx=map_context(&ring,&q,&y,&sum,ph,&pool,&p,true);
    let mut before=io::Image::zero();
    for lane in 0..64 {
        let mask=1u64<<lane;
        let (e,qlow,qhigh,c)=match lane%8 {
            0=>(97,0,None,true),1=>(126,31,Some(127),true),
            2=>(63,0,Some(64),false),3=>(0,31,None,false),
            4=>(127,0,None,true),5=>(32,0,Some(63),false),
            6=>(64,0,None,false),_=>(65,0,Some(127),false),
        };
        before.q[q[qlow].0 as usize]|=mask;
        if let Some(j)=qhigh{before.q[q[j].0 as usize]|=mask;}
        if c{before.q[pool[0].0 as usize]|=mask;}
        if lane%3==0{before.q[ph.0 as usize]|=mask;}
        for j in 0..7{if e>>j&1!=0{before.q[y[j].0 as usize]|=mask;}}
        before.q[ring[256-e].0 as usize]|=mask;
        before.q[ring[256].0 as usize]|=mask;
        before.q[ring[127].0 as usize]|=mask;
    }
    for col in [36,40,41,60,81,82,89,96] {
        let mut out=Vec::new();
        for new in [false,true] {
            let scope=io::begin(before.clone(),b"r14-k1-ea-entry",io::RECORD_OP_CAP);
            if new{io::forbid(pool[2]);}
            b.begin();super::super::frogdrop::direct_map::k1_map3::diagnostic_v(&mut b,&ctx,&cps[col],new,true);
            let tape=b.end();b.play(&tape,false);b.flush_global();let (image,_)=io::finish(scope);
            out.push((image,tape));
        }
        let m6=out[1].0.q[y[5].0 as usize];
        let mut mapped=out[1].0.clone();mapped.q[y[5].0 as usize]=0;mapped.q[pool[2].0 as usize]=m6;
        out[0].0.signed_eq(&mapped,"F-EA1 base/new entry");
        let mut relabelled=out[0].0.clone();
        relabelled.q[y[5].0 as usize]=relabelled.q[pool[2].0 as usize];
        relabelled.q[pool[2].0 as usize]=0;
        let scope=io::begin(relabelled,b"r14-k1-ea-exit",io::RECORD_OP_CAP);
        io::forbid(pool[2]);b.play(&out[1].1,true);b.flush_global();let (returned,_)=io::finish(scope);
        before.signed_eq(&returned,"F-EA2 post-body shaped exit");
        eprintln!("F_EA1_EA2_PASS column={col} shots=64 inverse=true pool2=0 phase=0");
    }
}

#[test]
#[allow(warnings)]
fn r14_k1_f_ea0_add_carry(){
    let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let a=b.alloc_n(6);let t=b.alloc_n(6);let z=b.alloc();let ph=b.alloc();let tag=b.alloc();
    let dirty=b.alloc_n(3);
    let tape=super::super::frogdrop::direct_map::k1_map3::diagnostic_add_carry(
        &mut b,&a,&t,z,Some((ph,tag)),&dirty);
    for active in [true,false] {
        for batch in 0..128 {
            let mut before=io::Image::zero();let mut expected=before.clone();
            for lane in 0..64 {
                let index=batch*64+lane;let mask=1u64<<lane;
                let av=index&63;let tv=(index>>6)&127;
                for j in 0..6{if av>>j&1!=0{before.q[a[j].0 as usize]|=mask;}}
                for j in 0..6{if tv>>j&1!=0{before.q[t[j].0 as usize]|=mask;}}
                if tv>>6&1!=0{before.q[z.0 as usize]|=mask;}
                before.q[tag.0 as usize]|=mask;
                if !active{before.q[ph.0 as usize]|=mask;}
                for j in 0..3{if (index>>(j+2))&1!=0{before.q[dirty[j].0 as usize]|=mask;}}
                let sum=if active{(tv+av)&127}else{tv};
                for j in 0..6{if sum>>j&1!=0{expected.q[t[j].0 as usize]|=mask;}}
                if sum>>6&1!=0{expected.q[z.0 as usize]|=mask;}
            }
            for &v in a.iter().chain([ph,tag].iter()).chain(dirty.iter()){
                expected.q[v.0 as usize]=before.q[v.0 as usize];
            }
            let scope=io::begin(before.clone(),b"r14-k1-ea0",io::RECORD_OP_CAP);
            b.play(&tape,false);b.flush_global();let (after,_)=io::finish(scope);
            expected.signed_eq(&after,"F-EA0 add carry exhaustive");
            let scope=io::begin(after,b"r14-k1-ea0-inverse",io::RECORD_OP_CAP);
            b.play(&tape,true);b.flush_global();let (restored,_)=io::finish(scope);
            before.signed_eq(&restored,"F-EA0 inverse");
        }
        eprintln!("F_EA0_PASS active={active} 8192 inputs dirty restored inverse phase=0");
    }
}

#[test]
#[allow(warnings)]
fn r14_k1_f_ql4_native_entry_stage(){
    use super::super::k1_complete_caller;
    assert!(super::wp5_enabled()&&super::wp5_m6b_enabled());
    k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let mut ring=b.alloc_n(256);let p=b.alloc_n(258);ring.extend(b.alloc_n(1));
    let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
    let ctx=map_context(&ring,&q,&y,&sum,ph,&pool,&p,true);
    let mut before=io::Image::zero();
    for lane in 0..64 {
        let mask=1u64<<lane;let kind=lane%8;
        let (e,qlow,qhigh,phv,cv,cnt)=match kind{
            0=>(97,0,None,false,true,0),
            1=>(126,31,Some(127),false,true,0),
            2=>(63,0,Some(64),true,false,0),
            3=>(63,0,Some(64),true,false,1),
            4=>(127,63,None,true,false,1),
            5=>(0,63,None,true,false,64),
            6=>(127,0,None,false,false,0),
            _=>(0,0,None,true,false,0),
        };
        if phv{before.q[ph.0 as usize]|=mask;}
        if cv{before.q[pool[0].0 as usize]|=mask;}
        if cnt!=0{for j in 0..7{if cnt>>j&1!=0{before.q[q[121+j].0 as usize]|=mask;}}}
        before.q[q[qlow].0 as usize]|=mask;
        if let Some(j)=qhigh{before.q[q[j].0 as usize]|=mask;}
        if kind==1{for j in 31..128{before.q[q[j].0 as usize]|=mask;}}
        for j in 0..7{if e>>j&1!=0{before.q[y[j].0 as usize]|=mask;}}
        if matches!(kind,4|5){
            for j in 1..5{if (lane+j)%2==0{before.q[sum[j].0 as usize]|=mask;}}
            if lane%2==0{before.q[ring[256].0 as usize]|=mask;}
            if lane%3==0{before.q[y[5].0 as usize]|=mask;}
        }else{
            before.q[ring[256-e].0 as usize]|=mask;
            before.q[ring[256].0 as usize]|=mask;
            let z:u128=if kind==1{0xfdc08fdb91fb81237023f6e47ee048e2}else{(1u128<<127)|1};
            for j in 0..128{if z>>j&1!=0{before.q[ring[j].0 as usize]|=mask;}}
        }
        if lane%7==0{before.q[p[11].0 as usize]|=mask;}
    }
    for col in [97,105,111,113] {
        for entry_only in [true,false] {
            let mut out=Vec::new();
            for new in [false,true] {
                let scope=io::begin(before.clone(),b"r14-k1-ql4-native",io::RECORD_OP_CAP);
                if new{io::forbid(pool[2]);}
                b.begin();
                super::done3(&mut b,&ctx,ctx.roles.tag,&[],&ctx.donors());
                super::super::frogdrop::direct_map::k1_map3::diagnostic_ql4(&mut b,&ctx,&cps[col],new,entry_only);
                if !entry_only{super::done3(&mut b,&ctx,ctx.roles.tag,&[],&ctx.donors());}
                let tape=b.end();b.play(&tape,false);b.flush_global();let (image,_)=io::finish(scope);
                let scope=io::begin(image.clone(),b"r14-k1-ql4-native-inverse",io::RECORD_OP_CAP);
                b.play(&tape,true);b.flush_global();let (restored,_)=io::finish(scope);
                before.signed_eq(&restored,"F-QL4 native inverse");out.push(image);
            }
            if entry_only{
                let m6=out[0].q[pool[2].0 as usize];
                out[0].q[y[5].0 as usize]^=m6;out[0].q[pool[2].0 as usize]=0;
            }
            out[0].signed_eq(&out[1],if entry_only{"F-QL4E native entry"}else{"F-QL4S native stage"});
            eprintln!("F_QL4_PASS col={col} entry_only={entry_only} shots=64 DONE/fresh/PH1/C1 pool2=0 phase=0");
        }
    }
}

#[test]
#[allow(warnings)]
fn r14_k1_m6_exact_quotient_screen(){
    use super::super::k1_complete_caller;
    assert!(super::wp5_enabled()&&super::wp5_m6a_enabled());
    k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let mut ring=b.alloc_n(256);let p=b.alloc_n(258);ring.extend(b.alloc_n(1));
    let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
    let ctx=map_context(&ring,&q,&y,&sum,ph,&pool,&p,true);
    let mut before=io::Image::zero();
    for &v in &[q[31],q[127],pool[0],y[1],y[2],y[3],y[4],y[5],y[6],ring[130],ring[256]]{
        before.q[v.0 as usize]=!0u64;
    }
    for j in 31..128{before.q[q[j].0 as usize]=!0u64;}
    let z:u128=0xfdc08fdb91fb81237023f6e47ee048e2;
    for j in 0..128{if z>>j&1!=0{before.q[ring[j].0 as usize]=!0u64;}}
    let mut out=Vec::new();
    for new in [false,true]{
        let scope=io::begin(before.clone(),b"r14-k1-plain-screen",io::RECORD_OP_CAP);
        if new{io::forbid(pool[2]);}
        super::super::frogdrop::direct_map::k1_map3::diagnostic_v(&mut b,&ctx,&cps[97],new,false);
        b.flush_global();out.push(io::finish(scope).0);
    }
    out[0].signed_eq(&out[1],"native cex on Plain body");
    eprintln!("M6_NATIVE_CEX_PLAIN_SCREEN_PASS");
}

#[test]
#[allow(warnings)] // rustc 1.93 early-lint renderer ICEs on packed fixtures otherwise.
fn r14_k1_m6_pureht_done_rare(){
    use super::super::{frogdrop_col,k1_complete_caller};
    assert!(super::wp5_enabled()&&super::super::c659::t23_enabled());
    k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for column in [114,116,119] {
        let cp=&cps[column];
        for payload in [true,false] {
            let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
            let mut ring=b.alloc_n(256);let p=b.alloc_n(258);ring.extend(b.alloc_n(1));
            let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
            let forward=map_context(&ring,&q,&y,&sum,ph,&pool,&p,payload);
            let inverse=map_context(&ring,&q,&y,&sum,ph,&pool,&p,!payload);
            let mut before=io::Image::zero();
            before.q[ph.0 as usize]=u64::MAX;
            for lane in 0..64 {
                let mask=1u64<<lane;let kind=lane%4;
                let e=if kind==1{cp.m-1}else{0};
                for j in 0..7 {if e>>j&1!=0{before.q[y[j].0 as usize]|=mask;}}
                before.q[ring[256-e].0 as usize]|=mask;
                before.q[ring[256].0 as usize]|=mask;
                if kind==0{before.q[q[121].0 as usize]|=mask;}
                else{before.q[q[0].0 as usize]|=mask;}
                if lane%7==0{before.q[p[11].0 as usize]|=mask;}
            }
            let scope=io::begin(before.clone(),b"r14-k1-m6-pureht-rare",io::RECORD_OP_CAP);
            io::forbid(pool[2]);map(&mut b,&forward,cp,false);map(&mut b,&inverse,cp,true);b.flush_global();
            let(after,_)=io::finish(scope);before.signed_eq(&after,"F-M6P DONE and active pair");
            eprintln!("F_M6P_PASS column={column} pair=T{}T{} DONE=16 maxY=16 M0=32 pool2=0 phase=0",if payload{1}else{3},if payload{2}else{4});
        }
    }
}
#[test]
fn r14_k1_f5_host_pairs(){
    use super::super::{frogdrop_col,k1_complete_caller};
    assert!(super::super::c659::t23_enabled(),"run with C658_T23=1");
    assert!(super::wp5_enabled(),"run with C658_WP5=1");
    k1_complete_caller::frozen_environment();
    const COLS:[usize;23]=[0,35,36,40,41,50,60,81,82,89,96,97,105,111,113,114,116,119,120,126,159,160,202];
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for payload in [true,false]{
        let mut source=k1_complete_caller::builder();
        let layout=k1_complete_caller::Layout::allocate(&mut source);
        let initial=k1_complete_caller::initial(&layout,payload,0);
        let seed=if payload{b"r14-k1-host-payload".as_slice()}else{b"r14-k1-host-no-payload".as_slice()};
        let scope=io::begin(initial,seed,io::PRODUCER_OP_CAP);
        source.x(layout.fd.ring[256]);drop(source);drop(layout);
        let mut captures=vec![];
        for cp in &cps {
            let mut b=k1_complete_caller::builder();let mut l=k1_complete_caller::Layout::allocate(&mut b);
            frogdrop_col::set_counter_epoch(&mut l.fd,cp.col);
            {let col=l.column(payload);let mut middle=super::super::direct_middle::DirectMiddle;
                super::super::direct_column::through_stage10(&mut b,&col,cp,&mut middle);
                b.flush_global();
                if COLS.contains(&cp.col){let(image,_)=io::snapshot();captures.push((cp.col,image));}
                super::finish_k1_observed(&mut b,&col,cp,|_|{});
            }
            assert!(b.ops.is_empty()&&b.pending_count()==0);
        }
        let(_,source_receipt)=io::finish(scope);
        assert_eq!(captures.len(),COLS.len());
        eprintln!("F5_HOST_SOURCE payload={payload} ops={} captures={}",source_receipt.ops,captures.len());
        for(column,mut image)in captures{
            let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
            let mut ring=b.alloc_n(256);let p=b.alloc_n(258);ring.extend(b.alloc_n(1));
            let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
            assert_eq!(b.width(),659);
            image.q[p[0].0 as usize]=0;image.q[p[1].0 as usize]=0;
            let cp=&cps[column];
            if column==35 {eprintln!("F5_HOST_C35_SOURCE m={} q127_mask={:016x} C_mask={:016x}",cp.m,image.q[q[127].0 as usize],image.q[pool[0].0 as usize]);}
            let forward=map_context(&ring,&q,&y,&sum,ph,&pool,&p,payload);
            let inverse=map_context(&ring,&q,&y,&sum,ph,&pool,&p,!payload);
            let before=image.clone();let seed=(column as u64 ^ ((payload as u64)<<32)).to_le_bytes();
            let scope=io::begin(image,&seed,io::RECORD_OP_CAP);
            let pool2_forbidden=matches!(column,0..=35|41..=81|114..=202)
                ||super::wp5_m6a_enabled()&&(36..=96).contains(&column)
                ||super::wp5_m6b_enabled()&&(97..=113).contains(&column);
            if pool2_forbidden{io::forbid(pool[2]);}
            map(&mut b,&forward,cp,false);map(&mut b,&inverse,cp,true);b.flush_global();
            let(after,receipt)=io::finish(scope);
            before.signed_eq(&after,&format!("F5-HOST column={column} pair=T{}T{}",if payload{1}else{3},if payload{2}else{4}));
            eprintln!("F5_MAP_PASS column={column} pair=T{}T{} ops={} shots=64 pool2_forbidden={pool2_forbidden} phase=0",if payload{1}else{3},if payload{2}else{4},receipt.ops);
        }
    }
}

#[test]
fn r14_k1_f5_tail7_pairs(){
    use super::super::{frogdrop_col,k1_complete_caller,frogdrop::direct_tail};
    assert!(super::super::c659::t23_enabled());assert!(super::wp5_enabled());
    k1_complete_caller::frozen_environment();
    const COLS:[usize;5]=[36,50,81,96,113];
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for payload in [true,false] {
        let mut source=k1_complete_caller::builder();let layout=k1_complete_caller::Layout::allocate(&mut source);
        let initial=k1_complete_caller::initial(&layout,payload,0);
        let seed=if payload{b"r14-k1-tail-payload".as_slice()}else{b"r14-k1-tail-no-payload".as_slice()};
        let scope=io::begin(initial,seed,io::PRODUCER_OP_CAP);
        source.x(layout.fd.ring[256]);drop(source);drop(layout);
        let mut captures=vec![];
        for cp in cps.iter().take(114) {
            let mut b=k1_complete_caller::builder();let mut l=k1_complete_caller::Layout::allocate(&mut b);
            frogdrop_col::set_counter_epoch(&mut l.fd,cp.col);
            {let col=l.column(payload);let mut middle=super::super::direct_middle::DirectMiddle;
                super::super::direct_column::through_stage10(&mut b,&col,cp,&mut middle);
                super::finish_k1_observed(&mut b,&col,cp,|b|{
                    if COLS.contains(&cp.col){b.flush_global();let(image,_)=io::snapshot();captures.push((cp.col,image));}
                });
            }
            assert!(b.ops.is_empty()&&b.pending_count()==0);
        }
        let(_,source_receipt)=io::finish(scope);assert_eq!(captures.len(),COLS.len());
        eprintln!("F5_TAIL_SOURCE payload={payload} ops={} captures={}",source_receipt.ops,captures.len());
        for(column,mut image)in captures {
            let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
            let mut ring=b.alloc_n(256);let p=b.alloc_n(258);ring.extend(b.alloc_n(1));
            let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
            image.q[p[0].0 as usize]=0;image.q[p[1].0 as usize]=0;
            let cp=&cps[column];let par=direct_tail::TailPar{l0:cp.l0,qb:cp.qb,
                szlo:cp.sz.0,sylo:cp.sy.0,swl_hi:cp.swl.1,m:cp.m};
            let mut scratch8=vec![pool[0]];scratch8.extend(&sum);scratch8.extend([pool[1],pool[2]]);
            let mut scratch9=scratch8.clone();scratch9[7]=p[0];scratch9.push(p[1]);
            let bank:Vec<_>=ring.iter().chain(&q).chain(&y).chain(&sum).chain([pool[1]] .iter()).copied().collect();
            let before=image.clone();let seed=(column as u64 ^ ((payload as u64)<<32)).to_le_bytes();
            let scope=io::begin(image,&seed,io::RECORD_OP_CAP);io::forbid(pool[2]);
            let new=|b:&mut B,inverse:bool|{b.begin();direct_tail::k1_tail3::apply7(b,&ring,&q,&y,&scratch8,ph,&par,false,&bank);let tape=b.end();b.play(&tape,inverse);};
            let old=|b:&mut B,inverse:bool|{b.begin();direct_tail::k1_terminal_hosted(b,&ring,&q,&y,&scratch9,ph,&par,false,&bank);let tape=b.end();b.play(&tape,inverse);};
            if payload {new(&mut b,false);old(&mut b,true);}else{old(&mut b,false);new(&mut b,true);}
            b.flush_global();let(after,receipt)=io::finish(scope);
            before.signed_eq(&after,&format!("F5-TAIL7 column={column} pair=T{}T{}",if payload{1}else{3},if payload{2}else{4}));
            eprintln!("F5_TAIL_PASS column={column} pair=T{}T{} ops={} shots=64 pool2=0 phase=0",if payload{1}else{3},if payload{2}else{4},receipt.ops);
        }
    }
}

#[test]
fn r14_k1_f5_tail7_exhaustive_emitted_shapes(){
    use super::super::frogdrop::direct_tail::k1_tail3::fixture_encoded_xor;
    const CODES:[usize;7]=[0,1,4,6,5,7,2];
    // Complete distinct shape list from scratch/r14-k1-tail-search.py over
    // the five requested sw columns. The Python enumerator checks each column.
    const READ:[(usize,usize);32]=[
        (0,7),(0,8),(0,9),(0,10),(0,11),(0,12),
        (1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),
        (15,0),(15,7),(16,1),(16,2),(16,3),(16,4),(16,5),(16,7),
        (16,8),(16,9),(16,10),(16,11),(16,12),
        (31,1),(31,2),(31,6),(31,7)];
    const MOVE:[((usize,usize),usize);7]=[
        ((0,1),5),((0,1),6),((0,2),5),((0,2),6),
        ((0,4),5),((0,4),6),((1,3),5)];
    for (kind,mask,other,pair) in READ.iter().map(|&(m,o)|(false,m,o,(0,0)))
        .chain(MOVE.iter().map(|&(p,o)|(true,0,o,p))) {
        for (state,&code) in CODES.iter().enumerate() {
            let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
            let c=b.alloc();let u=b.alloc_n(8);let rest=b.alloc_n(other);let target=b.alloc();
            let donors=b.alloc_n(24);let mut before=io::Image::zero();let mut expected=before.clone();
            let mut ctl=vec![(c,false)];
            if !kind {
                match mask {
                    0=>{ctl.push((u[6],false));ctl.push((u[7],false));},
                    1=>{ctl.extend([(u[5],true),(u[6],true),(u[7],true)]);},
                    15=>ctl.push((u[7],true)),16=>ctl.push((u[7],false)),31=>{},
                    _=>unreachable!(),
                }
            }else{
                match pair {
                    (0,1)=>ctl.extend([(u[6],true),(u[7],true)]),
                    (0,2)=>ctl.extend([(u[5],true),(u[7],true)]),
                    (1,3)=>ctl.extend([(u[5],false),(u[7],true)]),
                    (0,4)=>ctl.extend([(u[5],true),(u[6],true)]),
                    _=>unreachable!(),
                }
            }
            ctl.extend(rest.iter().copied().map(|q|(q,false)));
            for lane in 0..64 {
                let flag=1u64<<lane;let low=lane%32;let enable=other==0||lane>=32;
                for (wire,value) in [(c,code&4!=0),(u[5],code&2!=0),(u[7],code&1!=0)] {
                    if value {before.q[wire.0 as usize]|=flag;}
                }
                let mut next=code;
                if kind&&enable&&state>=2 {
                    let high=state-2;
                    if high==pair.0 {next=CODES[2+pair.1];}
                    else if high==pair.1 {next=CODES[2+pair.0];}
                }
                for (wire,value) in [(c,next&4!=0),(u[5],next&2!=0),(u[7],next&1!=0)] {
                    if value {expected.q[wire.0 as usize]|=flag;}
                }
                for bit in 0..5 {if low>>bit&1!=0 {
                    before.q[u[bit].0 as usize]|=flag;expected.q[u[bit].0 as usize]|=flag;
                }}
                for (j,&wire) in rest.iter().enumerate() {
                    if j>0||lane>=32 {before.q[wire.0 as usize]|=flag;expected.q[wire.0 as usize]|=flag;}
                }
                for (j,&wire) in donors.iter().enumerate() {
                    if (lane*17+j*13+3)%11<5 {before.q[wire.0 as usize]|=flag;expected.q[wire.0 as usize]|=flag;}
                }
                if !kind {
                    let high=(state>=2).then_some(state.saturating_sub(2));
                    let active=enable&&high.is_some_and(|h|mask>>h&1!=0);
                    let start=low.count_ones()%2==1;
                    if start{before.q[target.0 as usize]|=flag;}
                    if start^active{expected.q[target.0 as usize]|=flag;}
                }
            }
            let sink=if kind{u[match pair{(0,1)=>5,(0,2)|(1,3)=>6,(0,4)=>7,_=>unreachable!()}]}else{target};
            let scope=io::begin(before.clone(),b"r14-k1-tail7-shapes",io::RECORD_OP_CAP);
            io::forbid(u[6]);
            b.begin();fixture_encoded_xor(&mut b,&ctl,sink,c,&u,&donors);let tape=b.end();
            b.play(&tape,false);b.flush_global();let(after,_)=io::finish(scope);
            expected.signed_eq(&after,&format!("F5-TAIL7 shape kind={kind} mask={mask} other={other} pair={pair:?} state={state}"));
            let scope=io::begin(after,b"r14-k1-tail7-shapes-inverse",io::RECORD_OP_CAP);
            b.play(&tape,true);b.flush_global();let(restored,_)=io::finish(scope);
            before.signed_eq(&restored,"F5-TAIL7 emitted shape inverse");
        }
    }
    eprintln!("F5_TAIL7_SHAPES_PASS shapes=39 states=7 low=0..31 enable=0,1 u128..159 inverse phase=0");
}

#[test]
fn r14_k1_f5_all_changed_kernel_no_pool2(){
    use super::super::frogdrop::direct_tail;
    assert!(super::wp5_enabled()&&super::super::c659::t23_enabled());
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut counts=[0u64;3];let mut covered=[0usize;3];
    for cp in &cps {
        let hosted=matches!(cp.col,0..=35|41..=81|114..=202)
            ||super::wp5_m6a_enabled()&&matches!(cp.col,36..=40|82..=96)
            ||super::wp5_m6b_enabled()&&matches!(cp.col,97..=113);
        let tail=cp.sw||cp.dl;
        let counter=cp.dn||cp.fin;
        if !hosted&&!tail&&!counter{continue;}
        let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let mut ring=b.alloc_n(256);let p=b.alloc_n(258);ring.extend(b.alloc_n(1));
        let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
        assert_eq!(b.width(),659);
        let ctx=map_context(&ring,&q,&y,&sum,ph,&pool,&p,true);
        let bank=ctx.donors();
        if hosted {
            let scope=io::hash_only();io::forbid(pool[2]);
            map(&mut b,&ctx,cp,false);b.flush_global();
            let(_,receipt)=io::finish(scope);counts[0]+=receipt.ops;covered[0]+=1;
        }
        if tail {
            let par=direct_tail::TailPar{l0:cp.l0,qb:cp.qb,szlo:cp.sz.0,
                sylo:cp.sy.0,swl_hi:cp.swl.1,m:cp.m};
            let scratch=ctx.scratch();
            let scope=io::hash_only();io::forbid(pool[2]);
            b.begin();direct_tail::k1_tail3::apply7(&mut b,&ring,&q,&y,&scratch,ph,&par,false,&bank);
            let tape=b.end();b.play(&tape,false);b.flush_global();
            let(_,receipt)=io::finish(scope);counts[1]+=receipt.ops;covered[1]+=1;
        }
        if counter {
            let scope=io::hash_only();io::forbid(pool[2]);
            b.begin();counter3_with(&mut b,&ctx,cp,&bank,true);let tape=b.end();
            b.play(&tape,false);b.flush_global();
            let(_,receipt)=io::finish(scope);counts[2]+=receipt.ops;covered[2]+=1;
        }
        assert!(b.ops.is_empty()&&b.pending_count()==0);
    }
    let expect_maps=166+(if super::wp5_m6a_enabled(){20}else{0})
        +(if super::wp5_m6b_enabled(){17}else{0});
    assert_eq!(covered,[expect_maps,78,107]);
    eprintln!("F5_ALL_NO_POOL2_PASS hosted_cols={} tail_cols={} counter_cols={} emitted_ops={:?}",
        covered[0],covered[1],covered[2],counts);
}
