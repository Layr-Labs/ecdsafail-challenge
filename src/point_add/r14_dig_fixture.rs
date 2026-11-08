//! Focused all-wire checks for the WP3 difference walks.
use super::{dwalk_sign,dwalk_activity,B,Size,SumSize};
use crate::circuit::QubitId;
use crate::point_add::tests_frogdrop::{run,Rng};
use std::collections::BTreeSet;

fn bit(words:&mut[u64],q:QubitId,shot:usize,value:usize){
    if value&1!=0 { words[q.0 as usize]|=1u64<<shot; }
}
fn word(words:&mut[u64],lanes:&[QubitId],shot:usize,value:usize){
    for (i,&q) in lanes.iter().enumerate(){bit(words,q,shot,value>>i);}
}

#[test]
fn f3_dwalk_full_public_metadata_all_wire(){
    // The source relation is Y=E+1, Z=225+S-E, so Y+Z=226+S<=257.
    // Exhaust every E in 0..128 and S in 0..31; this includes every
    // public R/T pair allowed by the actual source relation.
    let cases:Vec<_>=(0..128).flat_map(|e|(0..32).map(move |s|(e,s))).collect();
    for hr in [false,true]{
        let mut b=B::new();b.global_cancel=false;
        b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let raw=b.alloc_n(259);let y=b.alloc_n(7);let sum=b.alloc_n(5);
        let sign=b.alloc();let flight=b.alloc();let activity=b.alloc();
        let dirty=b.alloc_n(32);
        let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
        let (rsize,rr,tsize,tr)=if hr{(Size::Z,(98,256),Size::Y,(1,128))}
            else{(Size::Y,(1,128),Size::Z,(98,256))};
        b.begin();dwalk_sign(&mut b,&meta,&raw,rsize,rr,tsize,tr,sign,flight,&dirty);
        let tape=b.end();b.play(&tape,false);let forward=b.ops.len();b.play(&tape,true);
        let width=b.width() as usize;let mut rng=Rng::new(0xd3a1+u64::from(hr));
        for chunk in cases.chunks(64){
            let mut input=vec![0u64;width];
            for &q in raw.iter().chain(dirty.iter()) {input[q.0 as usize]=rng.next();}
            let mut expected=input.clone();
            for (shot,&(e,s)) in chunk.iter().enumerate(){
                word(&mut input,&y,shot,e);word(&mut input,&sum,shot,s);
                word(&mut expected,&y,shot,e);word(&mut expected,&sum,shot,s);
                bit(&mut input,sign,shot,1);bit(&mut expected,sign,shot,1);
                let yy=e+1;let zz=225+s-e;
                let (r,t)=if hr{(zz,yy)}else{(yy,zz)};
                for l in r..258-t {expected[raw[l].0 as usize]^=1u64<<shot;}
            }
            let got=run(&b.ops[..forward],width,&|q|*q=input.clone());
            assert_eq!(got.phase,0,"hr={hr} forward phase");
            if got.q!=expected { let i=(0..width).find(|&i|got.q[i]!=expected[i]).unwrap(); let shot=(got.q[i]^expected[i]).trailing_zeros() as usize; panic!("hr={hr} q={i} shot={shot} case={:?} got={} want={} ops={forward}",chunk.get(shot),got.q[i]>>shot&1,expected[i]>>shot&1); }
            let back=run(&b.ops,width,&|q|*q=input.clone());
            assert_eq!(back.phase,0,"hr={hr} inverse phase");
            assert_eq!(back.q,input,"hr={hr} inverse E,S={chunk:?}");
        }
        eprintln!("F3_DWALK_PASS hr={hr} cases={} ops={forward} phase=0",cases.len());
    }
}

#[test]
fn f3_final_a_walk_full_public_r_all_wire(){
    for &(size,range) in &[(Size::Y,(1,128)),(Size::Z,(98,256))]{
        let mut b=B::new();b.global_cancel=false;
        b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let raw=b.alloc_n(259);let y=b.alloc_n(7);let sum=b.alloc_n(5);
        let activity=b.alloc();let flight=b.alloc();let dirty=b.alloc_n(32);
        let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
        b.begin();dwalk_activity(&mut b,&meta,&raw,size,range,activity,flight,&dirty);
        let tape=b.end();b.play(&tape,false);let forward=b.ops.len();b.play(&tape,true);
        let width=b.width() as usize;let mut rng=Rng::new(0xa71 + range.0 as u64);
        let cases:Vec<_>=(0..128).flat_map(|e|(0..32).map(move |s|(e,s))).collect();
        for chunk in cases.chunks(64){
            let mut input=vec![0u64;width];
            for &q in raw.iter().chain(dirty.iter()){input[q.0 as usize]=rng.next();}
            let mut expected=input.clone();
            for (shot,&(e,s)) in chunk.iter().enumerate(){
                word(&mut input,&y,shot,e);word(&mut input,&sum,shot,s);
                word(&mut expected,&y,shot,e);word(&mut expected,&sum,shot,s);
                bit(&mut input,activity,shot,1);bit(&mut expected,activity,shot,1);
                let r=if matches!(size,Size::Y){e+1}else{225+s-e};
                for l in r+1..259 {expected[raw[l].0 as usize]^=1u64<<shot;}
            }
            let got=run(&b.ops[..forward],width,&|q|*q=input.clone());
            assert_eq!(got.phase,0,"range={range:?} forward phase");
            assert_eq!(got.q,expected,"range={range:?} forward E,S={chunk:?}");
            let back=run(&b.ops,width,&|q|*q=input.clone());
            assert_eq!(back.phase,0,"range={range:?} inverse phase");
            assert_eq!(back.q,input,"range={range:?} inverse E,S={chunk:?}");
        }
        eprintln!("F3_AWALK_PASS range={range:?} cases={} ops={forward} phase=0",cases.len());
    }
}


fn rotation_builder(floor:usize,latched:bool)->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,usize){
    let mut b=B::new();b.global_cancel=false;
    b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let raw=b.alloc_n(259);let y=b.alloc_n(7);let sum=b.alloc_n(5);
    let flight=b.alloc();let dirty=b.alloc_n(32);
    let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
    let tape=if latched{super::rotate_z7_latched_record(&mut b,&meta,&raw,floor,flight,&dirty)}
        else{super::rotation_record(&mut b,&meta,Size::Z,&raw,flight,&dirty)};
    b.play(&tape,false);let forward=b.ops.len();b.play(&tape,true);
    (b,raw,y,sum,flight,forward)
}

#[test]
fn f3_rotate_latched_columns(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut columns=0;
    for cp in cps.iter().filter(|cp|cp.hr&&(85..=112).contains(&cp.col)
        &&cp.sz.1>cp.sz.0+127){
        let floor=cp.sz.0;let hi=cp.sz.1;assert!(hi-floor-127<=16);
        let (old,raw,y,sum,flight,old_f)=rotation_builder(floor,false);
        let (new,nraw,ny,nsum,nflight,new_f)=rotation_builder(floor,true);
        assert_eq!((raw.clone(),y.clone(),sum.clone(),flight),
            (nraw,ny,nsum,nflight));
        let width=old.width() as usize;assert_eq!(width,new.width() as usize);
        let mut cases=vec![];
        for z in [98,floor.saturating_sub(1),floor,floor+1,floor+63,
            floor+127,floor+128,hi,hi.saturating_add(1).min(256),256]{
            if !(98..=256).contains(&z){continue;}
            if let Some((e,s))=(0..128).flat_map(|e|(0..32).map(move |s|(e,s)))
                .find(|&(e,s)|225+s-e==z){cases.push((e,s,z));}
        }
        // Add passengers on both sides of the box and across the overflow.
        for s in [0,1,15,31]{for e in [0,31,63,95,127]{
            cases.push((e,s,225+s-e));
        }}
        cases.sort_unstable();cases.dedup();assert!(cases.len()<=64);
        let mut input=vec![0u64;width];let mut rng=Rng::new(0x3707+cp.col as u64);
        for &q in &raw{input[q.0 as usize]=rng.next();}
        for q in (flight.0 as usize+1)..width{input[q]=rng.next();}
        for (shot,&(e,s,_)) in cases.iter().enumerate(){
            word(&mut input,&y,shot,e);word(&mut input,&sum,shot,s);
        }
        let a=run(&old.ops[..old_f],width,&|q|*q=input.clone());
        let n=run(&new.ops[..new_f],width,&|q|*q=input.clone());
        assert_eq!((a.phase,n.phase),(0,0),"col={}",cp.col);
        for (shot,&(_,_,z)) in cases.iter().enumerate(){
            if z>=floor&&z<=hi{
                for q in 0..width{
                    assert_eq!((a.q[q]>>shot)&1,(n.q[q]>>shot)&1,
                        "col={} Z={z} q={q} active rotation",cp.col);
                }
            }
        }
        let back=run(&new.ops,width,&|q|*q=input.clone());
        assert_eq!(back.phase,0,"col={} paired phase",cp.col);
        assert_eq!(back.q,input,"col={} paired rotation; out-of-box passengers",cp.col);
        columns+=1;
        eprintln!("F3_ROT col={} floor={} hi={} cases={} old_ops={} new_ops={}",
            cp.col,floor,hi,cases.len(),old_f,new_f);
    }
    assert_eq!(columns,27,"expected all span>128 HR columns in 85..112");
}


#[test]
fn f3_sb_read_all_wire(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    assert_eq!(std::env::var("C658_WP3").as_deref(),Ok("1"));
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for &col in &[37,50,85,96,110,113,126]{for reverse in [false,true]{
        let range=cps[col].sz;
        let mut b=B::new();b.global_cancel=false;
        b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let raw=b.alloc_n(259);let y=b.alloc_n(7);let sum=b.alloc_n(5);
        let target=b.alloc();let act=b.alloc();let work=b.alloc();let dirty=b.alloc_n(32);
        let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
        b.begin();if reverse{
            super::super::read_selected(&mut b,&meta,Size::Z,range,&raw,|z|258-z,
                target,act,work,&dirty);
        }else{
            super::super::read_selected(&mut b,&meta,Size::Z,range,&raw,|z|z,
                target,act,work,&dirty);
        }
        let tape=b.end();b.play(&tape,false);let forward=b.ops.len();b.play(&tape,true);
        let width=b.width() as usize;let mut rng=Rng::new(0x513+col as u64+u64::from(reverse));
        let cases:Vec<_>=(0..128).flat_map(|e|(0..32).map(move|s|(e,s))).collect();
        for chunk in cases.chunks(64){
            let mut input=vec![0u64;width];for &q in raw.iter().chain(dirty.iter()){
                input[q.0 as usize]=rng.next();
            }
            input[target.0 as usize]=rng.next();let mut expected=input.clone();
            for (shot,&(e,s)) in chunk.iter().enumerate(){
                word(&mut input,&y,shot,e);word(&mut input,&sum,shot,s);
                word(&mut expected,&y,shot,e);word(&mut expected,&sum,shot,s);
                let z=225+s-e;
                if range.0<=z&&z<=range.1{
                    bit(&mut input,act,shot,1);bit(&mut expected,act,shot,1);
                    let index=if reverse{258-z}else{z};
                    expected[target.0 as usize]^=(input[raw[index].0 as usize]>>shot&1)<<shot;
                }
            }
            let got=run(&b.ops[..forward],width,&|q|*q=input.clone());
            assert_eq!(got.phase,0,"col={col} reverse={reverse}");
            assert_eq!(got.q,expected,"col={col} reverse={reverse} chunk={chunk:?}");
            let back=run(&b.ops,width,&|q|*q=input.clone());
            assert_eq!(back.phase,0);assert_eq!(back.q,input);
        }
        eprintln!("F3_SB_PASS col={col} reverse={reverse} range={range:?} cases=4096 ops={forward}");
    }}
}


fn reflect_builder(size:Size,range:(usize,usize),candidate:bool)
    ->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,QubitId,QubitId,usize){
    let mut b=B::new();b.global_cancel=false;
    b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let raw=b.alloc_n(259);let y=b.alloc_n(7);let sum=b.alloc_n(5);
    let activity=b.alloc();let flight=b.alloc();let sign=b.alloc();let dirty=b.alloc_n(32);
    let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
    let roles=super::Roles3::lane(activity,flight,sign);
    b.begin();
    if candidate{super::reflect3(&mut b,&meta,size,range,&raw,roles,&dirty);}
    else{
        let rotation=super::rotation_record(&mut b,&meta,size,&raw,flight,&dirty);
        b.play(&rotation,true);
        for code in 0..32{
            let length=32-code;if length<2{continue;}
            let mut c=super::super::eq(&meta.sum,code);c.push((activity,false));
            super::literal3(&mut b,&c,flight,&dirty);
            for i in 0..length/2{b.cswap(flight,raw[i],raw[length-1-i]);}
            super::literal3(&mut b,&c,flight,&dirty);
        }
        b.play(&rotation,false);
    }
    let tape=b.end();b.play(&tape,false);let forward=b.ops.len();b.play(&tape,true);
    (b,raw,y,sum,activity,flight,sign,forward)
}

#[test]
fn f3_reflect_all_wire(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    assert_eq!(std::env::var("C658_WP3").as_deref(),Ok("1"));
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for &col in &[37,50,85,96,110,113,126]{for size in [Size::Y,Size::Z]{
        let cp=&cps[col];let is_z=matches!(size,Size::Z);let range=if is_z{cp.sz}else{cp.sy};
        let (old,raw,y,sum,activity,flight,sign,old_f)=reflect_builder(size,range,false);
        let (new,nraw,ny,nsum,nactivity,nflight,nsign,new_f)=reflect_builder(size,range,true);
        assert_eq!((raw.clone(),y.clone(),sum.clone(),activity,flight,sign),
            (nraw,ny,nsum,nactivity,nflight,nsign));
        let width=old.width() as usize;assert_eq!(width,new.width() as usize);
        let mut rng=Rng::new(0xf3ff + col as u64 + 512*u64::from(matches!(size,Size::Z)));
        let cases:Vec<_>=(0..128).flat_map(|e|(0..32).map(move|s|(e,s))).collect();
        for chunk in cases.chunks(64){
            let mut input=vec![0u64;width];
            for &q in &raw{input[q.0 as usize]=rng.next();}
            for i in sign.0 as usize..width{input[i]=rng.next();}
            for (shot,&(e,s)) in chunk.iter().enumerate(){
                word(&mut input,&y,shot,e);word(&mut input,&sum,shot,s);
                let r=if matches!(size,Size::Y){e+1}else{225+s-e};
                if range.0<=r&&r<=range.1{bit(&mut input,activity,shot,1);}
            }
            let a=run(&old.ops[..old_f],width,&|q|*q=input.clone());
            let n=run(&new.ops[..new_f],width,&|q|*q=input.clone());
            assert_eq!((a.phase,n.phase),(0,0),"col={col} size={is_z}");
            assert_eq!(a.q,n.q,"col={col} size={is_z} chunk={chunk:?}");
            let back=run(&new.ops,width,&|q|*q=input.clone());
            assert_eq!(back.phase,0);assert_eq!(back.q,input);
        }
        eprintln!("F3_REFL_PASS col={col} size={is_z} cases=4096 old_ops={old_f} new_ops={new_f}");
    }}
}

fn wf_builder(first:usize,k:usize,candidate:bool)
    ->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,QubitId,QubitId,usize){
    use crate::point_add::normalized_payload_q::k4_q3;
    let mut b=B::new();b.global_cancel=false;
    b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let q=b.alloc_n(128);let t=b.alloc_n(129);let y=b.alloc_n(7);let sum=b.alloc_n(5);
    let activity=b.alloc();let flight=b.alloc();let sign=b.alloc();let dirty=b.alloc_n(32);
    let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
    let roles=super::super::Roles{activity,flight,sign,work:if first==0{sum[4]}else{q[first-1]}};
    let gate=super::super::Guard{y:(1,128),sum_limit:31-k as isize};
    b.begin();
    if candidate{
        let tape=k4_q3::restoring_wf_record(&mut b,&meta,gate,&q,&t,roles,first,&dirty);
        b.play(&tape,false);
    }else{
        let witness=gate.witness_record(&mut b,&meta,activity,flight,&dirty);
        b.play(&witness,false);
        let tape=k4_q3::restoring_parent_for_fixture(&mut b,&q,&t,roles,first,&dirty);
        b.play(&tape,false);b.play(&witness,true);
    }
    let tape=b.end();b.play(&tape,false);let forward=b.ops.len();b.play(&tape,true);
    (b,q,t,y,sum,activity,flight,sign,forward)
}

#[test]
fn f3_wf_forward_q_all_wire(){
    assert_eq!(std::env::var("C658_WP3").as_deref(),Ok("1"));
    for (first,k) in [(1,0),(0,16)]{
        let (old,q,t,y,sum,a,e,m,old_f)=wf_builder(first,k,false);
        let (new,nq,nt,ny,nsum,na,ne,nm,new_f)=wf_builder(first,k,true);
        assert_eq!((q.clone(),t.clone(),y.clone(),sum.clone(),a,e,m),(nq,nt,ny,nsum,na,ne,nm));
        let width=old.width() as usize;assert_eq!(width,new.width() as usize);
        let mut rng=Rng::new(0x47b + k as u64);
        let cases:Vec<_>=(0..128).flat_map(|ee|(0..32).map(move|s|(ee,s))).collect();
        for chunk in cases.chunks(64){
            let mut input=vec![0u64;width];
            for &p in q.iter().chain(&t){input[p.0 as usize]=rng.next();}
            for i in m.0 as usize+1..width{input[i]=rng.next();}
            for (shot,&(ee,s)) in chunk.iter().enumerate(){
                word(&mut input,&y,shot,ee);word(&mut input,&sum,shot,s);
                let active=(shot+ee+s)%3!=0;
                if active{bit(&mut input,a,shot,1);}
                if active&&s<=31-k&&(shot+ee)%2==0{bit(&mut input,e,shot,1);}
            }
            let prior=run(&old.ops[..old_f],width,&|x|*x=input.clone());
            let next=run(&new.ops[..new_f],width,&|x|*x=input.clone());
            assert_eq!(prior.phase,0);assert_eq!(next.phase,0);
            assert_eq!(prior.q,next.q,"F3-WF first={first} k={k} chunk={chunk:?}");
            let back=run(&new.ops,width,&|x|*x=input.clone());
            assert_eq!(back.phase,0);assert_eq!(back.q,input);
        }
        eprintln!("F3_WF_PASS first={first} k={k} cases=4096 old_ops={old_f} new_ops={new_f}");
    }
}

fn tr_builder(n:usize,candidate:bool)
    ->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,QubitId,QubitId,Vec<QubitId>,usize){
    use crate::point_add::normalized_payload_q::k4_q3;
    let mut b=B::new();b.global_cancel=false;
    b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let q=b.alloc_n(n);let t=b.alloc_n(n+1);let y=b.alloc_n(7);let sum=b.alloc_n(5);
    let a=b.alloc();let e=b.alloc();let m=b.alloc();let dirty=b.alloc_n(8);
    let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
    let gate=super::super::Guard{y:(1,128),sum_limit:26};
    let roles=super::Roles3::lane(a,e,m);
    b.begin();
    if candidate{
        let tape=k4_q3::ttk_restoring_wf_record(&mut b,&meta,gate,&q,&t,roles,&dirty);
        b.play(&tape,false);
    }else{
        let witness=gate.witness_record(&mut b,&meta,a,e,&dirty);
        b.play(&witness,false);
        let tape=k4_q3::ttk_restoring_record(&mut b,&q,&t,roles,&dirty);
        b.play(&tape,false);b.play(&witness,true);
    }
    let tape=b.end();b.play(&tape,false);let forward=b.ops.len();b.play(&tape,true);
    (b,q,t,y,sum,a,e,m,dirty,forward)
}

#[test]
fn f3_tr_compare_then_subtract_exhaustive(){
    assert_eq!(std::env::var("C658_WP3").as_deref(),Ok("1"));
    for n in 2..=8{
        let (old,q,t,y,sum,a,e,m,dirty,old_f)=tr_builder(n,false);
        let (new,nq,nt,ny,nsum,na,ne,nm,nd,new_f)=tr_builder(n,true);
        assert_eq!((q.clone(),t.clone(),y.clone(),sum.clone(),a,e,m,dirty.clone()),
            (nq,nt,ny,nsum,na,ne,nm,nd));
        let width=old.width() as usize;assert_eq!(width,new.width() as usize);
        let mut rng=Rng::new(0x47c+n as u64);let mut cases=Vec::new();
        for qv in 0..1usize<<n{for tv in 0..1usize<<(n+1){for gate in [false,true]{
            for activity in [false,true]{for flight in 0..=usize::from(gate&&activity){
                cases.push((qv,tv,gate,activity,flight));
            }}
        }}}
        for chunk in cases.chunks(64){
            let mut input=vec![0u64;width];
            for &p in &dirty{input[p.0 as usize]=rng.next();}
            for (shot,&(qv,tv,gate,activity,flight)) in chunk.iter().enumerate(){
                word(&mut input,&q,shot,qv);word(&mut input,&t,shot,tv);
                word(&mut input,&y,shot,0);word(&mut input,&sum,shot,if gate{0}else{31});
                if activity{bit(&mut input,a,shot,1);}if flight!=0{bit(&mut input,e,shot,1);}
            }
            let prior=run(&old.ops[..old_f],width,&|x|*x=input.clone());
            let next=run(&new.ops[..new_f],width,&|x|*x=input.clone());
            assert_eq!(prior.phase,0);assert_eq!(next.phase,0);
            assert_eq!(prior.q,next.q,"F3-TR n={n} chunk={chunk:?}");
            let back=run(&new.ops,width,&|x|*x=input.clone());
            assert_eq!(back.phase,0);assert_eq!(back.q,input);
        }
        eprintln!("F3_TR_PASS n={n} cases={} old_ops={old_f} new_ops={new_f}",cases.len());
    }
}

struct NoDigitArithmetic;
impl super::super::Arithmetic for NoDigitArithmetic {
    fn apply(&mut self,_b:&mut B,_meta:&SumSize,_roles:super::super::Roles,
        _call:super::super::Kernel,_target:&[QubitId],_source:&[QubitId],_dirty:&[QubitId]){
        panic!("complete K4 digit must not use the legacy arithmetic callback");
    }
}

fn digit_builder(cp:&crate::point_add::frogdrop_col::ColPar,ht:bool,candidate:bool)
    ->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,
       QubitId,QubitId,QubitId,QubitId,QubitId,usize){
    use crate::point_add::direct_payload::{Context,Ranges,Roles};
    let mut b=B::new();b.global_cancel=false;
    b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let ring=b.alloc_n(257);let compact=b.alloc_n(258);let q=b.alloc_n(128);
    let y=b.alloc_n(7);let sum=b.alloc_n(5);let phase=b.alloc();
    let a=b.alloc();let e=b.alloc();let sign=b.alloc();let work=b.alloc();
    let dirty=b.alloc_n(32);
    let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
    let ctx=Context{meta:&meta,compact:&compact,ring:&ring,q:&q,phase};
    let roles=Roles{activity:a,flight:e,sign,work};
    if std::env::var("R14_DIG_G4_PROBE").as_deref()==Ok("1"){
        b.r14_pass=1;b.r14_roles=[a,e,sign];
    }
    let ranges=Ranges{z:cp.sz,y:(cp.sy.0.max(1),cp.sy.1.min(128))};
    std::env::set_var("C658_WP3",if candidate{"1"}else{"0"});
    b.begin();
    let _=super::digit_diagnostic(&mut b,&ctx,roles,ht,ranges,&mut NoDigitArithmetic,
        &dirty,if candidate{super::Diagnostic::ThreeRole}else{super::Diagnostic::Parent});
    let tape=b.end();b.play(&tape,false);let forward=b.ops.len();b.play(&tape,true);
    (b,ring,compact,q,y,sum,phase,a,e,sign,work,forward)
}

#[test]
fn f3_digit3_column_all_wire(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    let previous=std::env::var_os("C658_WP3");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for &col in &[37,50,85,96,110,113,126,139,146,202]{for ht in [false,true]{
        if col>=139&&!ht{continue;}
        let cp=&cps[col];
        let (old,ring,p,q,y,sum,phase,a,e,sign,work,old_f)=digit_builder(cp,ht,false);
        let (new,nring,np,nq,ny,nsum,nphase,na,ne,nsign,nwork,new_f)=digit_builder(cp,ht,true);
        assert_eq!((ring.clone(),p.clone(),q.clone(),y.clone(),sum.clone(),phase,a,e,sign,work),
            (nring,np,nq,ny,nsum,nphase,na,ne,nsign,nwork));
        let width=old.width() as usize;assert_eq!(width,new.width() as usize);
        let active:Vec<_>=(0..128).flat_map(|ee|(0..32).map(move|s|(ee,s)))
            .filter(|&(ee,s)|{
                let yy=ee+1;let zz=225+s-ee;
                cp.sy.0<=yy&&yy<=cp.sy.1.min(128)&&cp.sz.0<=zz&&zz<=cp.sz.1
            }).collect();
        assert!(!active.is_empty(),"F3-DIG no active metadata c{col}");
        let mut input=vec![0u64;width];let mut rng=Rng::new(0xd163+col as u64+u64::from(ht));
        for d in width-32..width{input[d]=rng.next();}
        for shot in 0..64{
            let (ee,s)=if shot<32{active[(shot*17+col)%active.len()]}
                else{((shot*37+col)%128,(shot*11+col)%32)};
            let yy=ee+1;let zz=225+s-ee;
            word(&mut input,&y,shot,ee);word(&mut input,&sum,shot,s);
            if shot<32{
                bit(&mut input,a,shot,1);bit(&mut input,q[yy-1],shot,1);
                for i in 0..yy-1{if (i+shot*7)%5==0{bit(&mut input,q[i],shot,1);}}
                bit(&mut input,ring[zz-1],shot,1);
                for i in 0..zz-1{if (i+shot*13)%7==0{bit(&mut input,ring[i],shot,1);}}
            }
        }
        let prior=run(&old.ops[..old_f],width,&|x|*x=input.clone());
        let next=run(&new.ops[..new_f],width,&|x|*x=input.clone());
        let clean=if std::env::var("C658_WP3_DS").as_deref()==Ok("1")
            ||std::env::var("C658_WP3_ZH").as_deref()==Ok("1"){
            !(prior.q[sign.0 as usize]|prior.q[e.0 as usize]|prior.phase)
        }else{u64::MAX};
        assert_ne!(clean,0,"F3-DIG no ABI-clean shots col={col} ht={ht}");
        assert_eq!((prior.phase^next.phase)&clean,0,"F3-DIG phase col={col} ht={ht}");
        let first=prior.q.iter().zip(&next.q).enumerate()
            .find(|(_, (a,b))|(*a^*b)&clean!=0).map(|(i,(a,b))|(i,(*a^*b)&clean));
        assert!(first.is_none(),"F3-DIG col={col} ht={ht} forward all-wire first_diff={first:?}");
        let back=run(&new.ops,width,&|x|*x=input.clone());
        assert_eq!(back.phase,0);assert_eq!(back.q,input,
            "F3-DIG col={col} ht={ht} inverse all-wire");
        // Cross-traversal kernel pair on the inherited successful-digit ABI:
        // T1 new then T2 parent inverse, and T3 parent then T4 new inverse.
        let mut t1_t2=Vec::with_capacity(new_f+old.ops.len()-old_f);
        t1_t2.extend_from_slice(&new.ops[..new_f]);
        t1_t2.extend_from_slice(&old.ops[old_f..]);
        let mut t3_t4=Vec::with_capacity(old_f+new.ops.len()-new_f);
        t3_t4.extend_from_slice(&old.ops[..old_f]);
        t3_t4.extend_from_slice(&new.ops[new_f..]);
        for (pair,ops) in [("T1T2",&t1_t2),("T3T4",&t3_t4)] {
            let got=run(ops,width,&|x|*x=input.clone());
            assert_eq!(got.phase&clean,0,"F3-DIG pair phase col={col} ht={ht} {pair}");
            let first=got.q.iter().zip(&input).enumerate()
                .find(|(_, (a,b))|(*a^*b)&clean!=0)
                .map(|(i,(a,b))|(i,(*a^*b)&clean));
            assert!(first.is_none(),"F3-DIG pair col={col} ht={ht} {pair} first_diff={first:?}");
        }
        eprintln!("F3_DIG_PAIR_PASS col={col} ht={ht} pair=T1T2/T3T4 abi_clean={}",clean.count_ones());
        eprintln!("F3_DIG_PASS col={col} ht={ht} shots=64 active=32 old_ops={old_f} new_ops={new_f}");
    }}
    if let Some(v)=previous{std::env::set_var("C658_WP3",v);}else{std::env::remove_var("C658_WP3");}
}

#[test]
fn f3_ds_sign_injected(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    assert!(matches!(std::env::var("C658_WP3_DS").as_deref(),Ok("0")|Ok("1")));
    assert!(matches!(std::env::var("C658_WP3_ZH").as_deref(),Ok("0")|Ok("1")));
    let prior3=std::env::var_os("C658_WP3");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut cases=vec![];
    for &col in &[37,50,85,96,110,113,126]{for ht in [false,true]{cases.push((col,ht));}}
    cases.extend([(139,true),(146,true),(202,true)]);
    for (col,ht) in cases{
        let cp=&cps[col];
        let ds=std::env::var("C658_WP3_DS").unwrap();
        let zh=std::env::var("C658_WP3_ZH").unwrap();
        std::env::set_var("C658_WP3_DS","0");std::env::set_var("C658_WP3_ZH","0");
        let(old,ring,p,q,y,sum,phase,a,e,sign,_work,old_f)=digit_builder(cp,ht,true);
        std::env::set_var("C658_WP3_DS",&ds);std::env::set_var("C658_WP3_ZH",&zh);
        let(new,_,_,_,_,_,_,_,_,_,_,new_f)=digit_builder(cp,ht,true);
        let active:Vec<_>=(0..128).flat_map(|ee|(0..32).map(move|s|(ee,s)))
            .filter(|&(ee,s)|{let yy=ee+1;let zz=225+s-ee;
                cp.sy.0<=yy&&yy<=cp.sy.1.min(128)&&cp.sz.0<=zz&&zz<=cp.sz.1})
            .collect();
        let width=old.width()as usize;let mut input=vec![0u64;width];
        for shot in 0..64{
            let(ee,s)=if !ht&&col==85&&shot==0{(22,31)}
                else{active[(shot*17+col)%active.len()]};
            let yy=ee+1;let zz=225+s-ee;
            word(&mut input,&y,shot,ee);word(&mut input,&sum,shot,s);
            bit(&mut input,a,shot,1);bit(&mut input,q[yy-1],shot,1);
            if !ht&&col==85&&shot==0{
                bit(&mut input,ring[zz-2],shot,1);
                bit(&mut input,p[233],shot,1);
                assert_eq!((yy,zz,s),(23,234,31));
            }else{bit(&mut input,ring[zz-1],shot,1);}
        }
        // A local sign=1 / slots=0 read-boundary state is inverted through
        // the old prefix.  Direct W=-1 at digit entry is not on this image.
        if col==37&&!ht{
            std::env::set_var("C658_WP3_DS","0");std::env::set_var("C658_WP3_ZH","0");
            std::env::set_var("R14_DIG_TRACE_STOP","read1");
            let(pre,_,_,_,_,_,_,_,_,_,_,pf)=digit_builder(cp,ht,true);
            std::env::remove_var("R14_DIG_TRACE_STOP");
            std::env::set_var("C658_WP3_DS",&ds);std::env::set_var("C658_WP3_ZH",&zh);
            let mut desired=vec![0u64;width];
            word(&mut desired,&y,0,58);word(&mut desired,&sum,0,23);bit(&mut desired,a,0,1);
            bit(&mut desired,q[58],0,1);bit(&mut desired,ring[189],0,1);bit(&mut desired,p[0],0,1);
            for i in 199..258{bit(&mut desired,p[i],0,1);}bit(&mut desired,phase,0,1);
            bit(&mut desired,sign,0,1);
            let image=run(&pre.ops[pf..],width,&|v|*v=desired.clone());
            let check=run(&pre.ops[..pf],width,&|v|*v=image.q.clone());
            assert_eq!(check.q,desired,"F3-DS read-boundary preimage");
            for i in 0..width{
                input[i]&=!(1u64<<63);input[i]|=(image.q[i]&1)<<63;
            }
        }
        let before=run(&old.ops[..old_f],width,&|v|*v=input.clone());
        let after=run(&new.ops[..new_f],width,&|v|*v=input.clone());
        // A successful inherited digit returns sign and flight clean.
        // Synthetic shots outside this necessary source ABI are diagnostic
        // only; do not promote their mismatches to a design counterexample.
        let valid=!(before.q[sign.0 as usize]|before.q[e.0 as usize]|before.phase);
        if !ht&&col==85{
            assert_ne!(valid&1,0,"F3-ZH c85 k0 virtual top shot excluded");
            assert_eq!(input[ring[233].0 as usize]&1,0,"F3-ZH c85 virtual top must be zero");
            eprintln!("F3_ZH_C85_TOP old_t233={} new_t233={} ring_top={} d233={}",
                before.q[p[233].0 as usize]&1,after.q[p[233].0 as usize]&1,
                input[ring[233].0 as usize]&1,input[p[233].0 as usize]&1);
        }
        assert_ne!(valid,0,"F3-DS no ABI-clean shots c{col} ht={ht}");
        assert_eq!((before.phase^after.phase)&valid,0,"F3-DS phase c{col} ht={ht}");
        let first=before.q.iter().zip(&after.q).enumerate()
            .find(|(_, (a,b))| (*a^*b)&valid!=0).map(|(i,(a,b))|(i,(*a^*b)&valid));
        assert!(first.is_none(),"F3-DS forward c{col} ht={ht} first_diff={first:?}");
        if ds=="1"{assert_eq!(after.q[sign.0 as usize]&valid,0,"F3-DS toggle touched c{col} ht={ht}");}
        let closed=run(&new.ops,width,&|v|*v=input.clone());
        assert_eq!(closed.phase,0,"F3-DS inverse phase c{col} ht={ht}");
        assert_eq!(closed.q,input,"F3-DS inverse all-wire c{col} ht={ht}");
        eprintln!("F3_DS_SIGN_PASS col={col} ht={ht} shots=64 local_sign={} abi_clean={} old_ops={old_f} new_ops={new_f}",usize::from(col==37&&!ht),valid.count_ones());
    }
    if let Some(v)=prior3{std::env::set_var("C658_WP3",v);}else{std::env::remove_var("C658_WP3");}
}


fn mt_builder(l:usize,evict:bool)
    ->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,QubitId,QubitId,usize){
    use crate::point_add::outer_three_records::{OuterRecords,ProbeGate,ThreeRoles};
    let mut b=B::new();b.global_cancel=false;
    b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let ring=b.alloc_n(257);let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);
    let tag=b.alloc();let cut=b.alloc();let toggle=b.alloc();
    if std::env::var("R14_DIG_G4_PROBE").as_deref()==Ok("1"){
        b.r14_pass=1;b.r14_roles=[tag,cut,toggle];
    }
    let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
    let roles=ThreeRoles::new(tag,cut,toggle);
    let outer=OuterRecords::new(&meta,roles,&ring,&q,evict);
    let tape=outer.sum_probe_record(&mut b,(l,l+1),ProbeGate::TagClear);
    b.play(&tape,false);let forward=b.ops.len();b.play(&tape,true);
    (b,ring,q,y,sum,tag,cut,toggle,forward)
}

#[test]
fn f4_mt_probe_all_wire(){
    for l in [200,207,230,241,255]{
        let (old,ring,q,y,sum,tag,cut,toggle,old_f)=mt_builder(l,false);
        let (new,nring,nq,ny,nsum,ntag,ncut,ntoggle,new_f)=mt_builder(l,true);
        assert_eq!((ring.clone(),q.clone(),y.clone(),sum.clone(),tag,cut,toggle),
            (nring,nq,ny,nsum,ntag,ncut,ntoggle));
        let width=old.width() as usize;assert_eq!(width,new.width() as usize);
        let lo=(224isize-l as isize).clamp(0,128)as usize;
        let hi=(256isize-l as isize).clamp(0,128)as usize;
        let cases:Vec<_>=(0..128).flat_map(|e|(0..32).flat_map(move|s|
            [false,true].into_iter().map(move|tagged|(e,s,tagged)))).collect();
        let mut rng=Rng::new(0x4a7 + l as u64);
        for chunk in cases.chunks(64){
            let mut input=vec![0u64;width];
            for &p in ring.iter().chain(&q){input[p.0 as usize]=rng.next();}
            for (shot,&(e,s,tagged)) in chunk.iter().enumerate(){
                word(&mut input,&y,shot,e);word(&mut input,&sum,shot,s);
                if tagged{bit(&mut input,tag,shot,1);}
                // Source S-inh: enabled interval hit implies S=0.
                if !tagged&&lo<=e&&e<hi&&s!=0{
                    input[ring[l].0 as usize]&=!(1u64<<shot);
                }
            }
            let a=run(&old.ops[..old_f],width,&|x|*x=input.clone());
            let n=run(&new.ops[..new_f],width,&|x|*x=input.clone());
            assert_eq!((a.phase,n.phase),(0,0),"l={l} chunk={chunk:?}");
            assert_eq!(a.q,n.q,"l={l} chunk={chunk:?}");
            let back=run(&new.ops,width,&|x|*x=input.clone());
            assert_eq!(back.phase,0);assert_eq!(back.q,input);
        }
        eprintln!("F4_MT_PASS l={l} lo={lo} hi={hi} cases={} old_ops={old_f} new_ops={new_f}",cases.len());
    }
}


fn cut_builder(cp:&crate::point_add::frogdrop_col::ColPar,
    boundary:crate::point_add::outer_three_records::SwapBoundary,evict:bool)
    ->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,QubitId,QubitId,usize){
    use crate::point_add::outer_three_records::{OuterRecords,ThreeRoles,bind_column};
    let mut b=B::new();b.global_cancel=false;
    b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let ring=b.alloc_n(257);let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);
    let tag=b.alloc();let cut=b.alloc();let toggle=b.alloc();
    if std::env::var("R14_DIG_G4_PROBE").as_deref()==Ok("1"){
        b.r14_pass=1;b.r14_roles=[tag,cut,toggle];
    }
    let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
    let outer=OuterRecords::new(&meta,ThreeRoles::new(tag,cut,toggle),&ring,&q,evict);
    let tape=outer.cut_swap_record(&mut b,&bind_column(cp),boundary);
    b.play(&tape,false);let forward=b.ops.len();b.play(&tape,true);
    (b,ring,q,y,sum,tag,cut,toggle,forward)
}

#[test]
fn f4_cut_swap_exact_all_wire(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    use crate::point_add::outer_three_records::SwapBoundary;
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for &col in &[37,88,97,114,115]{for boundary in
        [SwapBoundary::Enter,SwapBoundary::AfterCompleteMiddle]{
        let cp=&cps[col];let enter=matches!(boundary,SwapBoundary::Enter);
        let (old,ring,q,y,sum,tag,cut,toggle,old_f)=cut_builder(cp,boundary,false);
        let (new,nring,nq,ny,nsum,ntag,ncut,ntoggle,new_f)=cut_builder(cp,boundary,true);
        assert_eq!((ring.clone(),q.clone(),y.clone(),sum.clone(),tag,cut,toggle),
            (nring,nq,ny,nsum,ntag,ncut,ntoggle));
        let width=old.width() as usize;assert_eq!(width,new.width() as usize);
        let mut rng=Rng::new(0xc47 + col as u64 + 512*u64::from(enter));
        let cases:Vec<_>=(0..128).flat_map(|e|(0..32).map(move|s|(e,s))).collect();
        for chunk in cases.chunks(64){
            let mut input=vec![0u64;width];
            for &p in ring.iter().chain(&q){input[p.0 as usize]=rng.next();}
            for (shot,&(e,s)) in chunk.iter().enumerate(){
                word(&mut input,&y,shot,e);word(&mut input,&sum,shot,s);
                if enter&&cp.psw&&(e+s)&1!=0{bit(&mut input,tag,shot,1);}
            }
            let a=run(&old.ops[..old_f],width,&|x|*x=input.clone());
            let n=run(&new.ops[..new_f],width,&|x|*x=input.clone());
            assert_eq!((a.phase,n.phase),(0,0),"col={col} enter={enter}");
            assert_eq!(a.q,n.q,"col={col} enter={enter} chunk={chunk:?}");
            let back=run(&new.ops,width,&|x|*x=input.clone());
            assert_eq!(back.phase,0);assert_eq!(back.q,input);
        }
        eprintln!("F4_CUT_PASS col={col} enter={enter} cases=4096 old_ops={old_f} new_ops={new_f}");
    }}
}


fn nrc_builder(cp:&crate::point_add::frogdrop_col::ColPar,enter:bool,encoded:bool)
    ->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,QubitId,QubitId,usize){
    let mut b=B::new();b.global_cancel=false;
    b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let compact=b.alloc_n(258);let q=b.alloc_n(128);let upper=b.alloc_n(257);
    let y=b.alloc_n(7);let sum=b.alloc_n(5);
    let tag=b.alloc();let cut=b.alloc();let toggle=b.alloc();let dirty=b.alloc_n(32);
    if std::env::var("R14_DIG_G4_PROBE").as_deref()==Ok("1"){
        b.r14_pass=1;b.r14_roles=[tag,cut,toggle];
    }
    let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
    let range=if enter{
        (cp.sz.0.max(256-cp.psy.1.min(128)),cp.sz.1.min(255).min(257-cp.psy.0.max(1)))
    }else{(cp.sz.0.max(129),cp.sz.1)};
    assert!(range.0<=range.1&&range.1<=255);
    let flag=if encoded{super::FlagHost::Encoded{tag,cut}}else{super::FlagHost::Lane(toggle)};
    b.begin();super::narrow3(&mut b,&meta,&compact,&q,(!enter).then_some(upper.as_slice()),
        range,cut,flag,super::Address3::SevenBit{column_z_floor:cp.sz.0},
        &dirty,&[],enter);
    let tape=b.end();b.play(&tape,false);let forward=b.ops.len();b.play(&tape,true);
    (b,compact,q,upper,y,sum,tag,cut,toggle,forward)
}

#[test]
fn f4_nrc_narrow_all_wire(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for &col in &[85,96,110,112]{for enter in [true,false]{
        let cp=&cps[col];let (old,p,q,u,y,sum,tag,cut,toggle,old_f)=nrc_builder(cp,enter,false);
        let (new,np,nq,nu,ny,nsum,ntag,ncut,ntoggle,new_f)=nrc_builder(cp,enter,true);
        assert_eq!((p.clone(),q.clone(),u.clone(),y.clone(),sum.clone(),tag,cut,toggle),
            (np,nq,nu,ny,nsum,ntag,ncut,ntoggle));
        let width=old.width() as usize;assert_eq!(width,new.width() as usize);
        let mut rng=Rng::new(0x4c9 + col as u64 + 512*u64::from(enter));
        let cases:Vec<_>=(0..128).flat_map(|e|(0..32).map(move|s|(e,s))).collect();
        for chunk in cases.chunks(64){
            let mut input=vec![0u64;width];
            for &w in p.iter().chain(&q).chain(&u){input[w.0 as usize]=rng.next();}
            for i in toggle.0 as usize+1..width{input[i]=rng.next();}
            for (shot,&(e,s)) in chunk.iter().enumerate(){
                word(&mut input,&y,shot,e);word(&mut input,&sum,shot,s);
                let c=(e+s)&1;let a=(e+2*s)&1;
                if c!=0{bit(&mut input,tag,shot,1);}
                if c==0&&a!=0{bit(&mut input,cut,shot,1);}
            }
            let a=run(&old.ops[..old_f],width,&|w|*w=input.clone());
            let n=run(&new.ops[..new_f],width,&|w|*w=input.clone());
            assert_eq!((a.phase,n.phase),(0,0),"col={col} enter={enter}");
            assert_eq!(a.q,n.q,"col={col} enter={enter} chunk={chunk:?}");
            let back=run(&new.ops,width,&|w|*w=input.clone());
            assert_eq!(back.phase,0);assert_eq!(back.q,input);
        }
        eprintln!("F4_NRC_PASS col={col} enter={enter} cases=4096 old_ops={old_f} new_ops={new_f}");
    }}
}


fn static_layout()->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,Vec<QubitId>){
    let mut b=B::new();b.global_cancel=false;
    b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
    let mut ring=b.alloc_n(256);let compact=b.alloc_n(258);ring.extend(b.alloc_n(1));
    let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);
    let phase=b.alloc();let pool=b.alloc_n(3);assert_eq!(b.width(),659);
    (b,ring,compact,q,y,sum,phase,pool)
}
fn touches(op:&crate::circuit::Op,q:QubitId)->bool{
    [op.q_target,op.q_control1,op.q_control2].contains(&q)
}

fn native_c659_column(image:crate::point_add::k1_complete_io::Image,
    cp:&crate::point_add::frogdrop_col::ColPar,
    pass:crate::point_add::k5_ph_ports::Traversal,seed:&[u8])
    ->crate::point_add::k1_complete_io::Image{
    use crate::point_add::{c659,frogdrop_col,k1_complete_io as io,k5_ph_ports::Traversal};
    let (mut b,ring,compact,q,y,sum,phase,pool)=static_layout();
    let mut fd=frogdrop_col::Fd{ring,q:q.clone(),sy:y,sx:sum,
        ph:phase,cnt:q[121..128].to_vec()};
    frogdrop_col::set_counter_epoch(&mut fd,cp.col);
    let scope=io::begin(image,seed,io::RECORD_OP_CAP);
    b.r14_pass=match pass{Traversal::T1=>1,Traversal::T2=>2,Traversal::T3=>3,Traversal::T4=>4};
    b.r14_roles=[compact[0],compact[1],pool[2]];
    c659::pair_column_for_fixture(&mut b,&fd,cp,&pool,&compact,pass);
    b.r14_pass=0;b.flush_global();
    let(next,receipt)=io::finish(scope);
    eprintln!("F3_G3_NATIVE col={} pass={} ops={}",cp.col,match pass{Traversal::T1=>1,Traversal::T2=>2,Traversal::T3=>3,Traversal::T4=>4},receipt.ops);
    next
}

#[test]
fn f4_static_port_scans(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop,c659_column,c659_fixed,c659_endpoint,c659};
    crate::point_add::bake_knobs();
    let previous3=std::env::var_os("C658_WP3");let previous4=std::env::var_os("C658_WP4");
    std::env::set_var("C658_WP3","0");std::env::set_var("C658_WP4","0");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,b0,last)=pointadd_frogdrop::col_pars(&schedule);
    let mut fixed=0;
    for cp in cps.iter().filter(|cp|(146..=202).contains(&cp.col)){
        assert!(cp.sy.1<=86&&cp.sy.1+33<120,"col={} host Yhi",cp.col);
        let (mut b,ring,compact,q,y,sum,phase,pool)=static_layout();
        let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
        let roles=c659::Roles{tag:pool[0],cut:pool[1],toggle:pool[2].into()};
        let col=c659_column::Column{meta:&meta,roles,ring:&ring,q:&q,phase,
            compact:Some(&compact),dirty:&compact,clean_external:&[]};
        c659_fixed::run(&mut b,&col,cp);b.flush_global();
        let host=q[cp.sy.1+33];
        let uses=b.ops.iter().filter(|op|touches(op,host)).count();
        let used:BTreeSet<_>=b.ops.iter().flat_map(|op|
            [op.q_target,op.q_control1,op.q_control2]).collect();
        let free:Vec<_>=(cp.sy.1+24..120).filter(|&i|!used.contains(&q[i])).collect();
        fixed+=1;
        eprintln!("F4_FIX_SCAN col={} Yhi={} host={} uses={} free={:?} ops={}",
            cp.col,cp.sy.1,host.0,uses,free,b.ops.len());
    }
    assert_eq!(fixed,57);
    let (mut b,ring,compact,q,y,sum,phase,pool)=static_layout();
    let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
    let roles=c659::Roles{tag:pool[0],cut:pool[1],toggle:pool[2].into()};
    let col=c659_column::Column{meta:&meta,roles,ring:&ring,q:&q,phase,
        compact:Some(&compact),dirty:&compact,clean_external:&[]};
    let cp=b0.as_ref().expect("B0 endpoint source");
    let (scratch,dirty)=c659_endpoint::b0_ports(&col);
    assert_eq!(scratch[7],pool[2]);assert_eq!(scratch[8],q[114]);
    assert!(!scratch.contains(&q[115]));
    assert!(!dirty.contains(&q[115]));
    std::env::set_var("C658_WP4","1");
    let (hosted,hosted_dirty)=c659_endpoint::b0_ports(&col);
    assert_eq!(hosted[7],q[115]);assert_eq!(hosted[8],q[114]);
    assert!(!hosted_dirty.contains(&q[115]));
    std::env::set_var("C658_WP4","0");
    let par=crate::point_add::frogdrop::MapPar{
        clo:257-cp.smax.1,chi:257-cp.smax.0,m:128,tail:cp.tail,emax:cp.emax};
    let old_booth=b.allow_booth;b.allow_booth=false;
    let tape=crate::point_add::frogdrop::direct_map::stage_record(&mut b,&ring,&q[..114],
        &meta.y,&scratch,phase,&par,28,&dirty);
    b.allow_booth=old_booth;b.play(&tape,false);b.flush_global();
    assert!(!b.ops.iter().any(|op|touches(op,q[115])),"F4-END B0 base tape touches Q115");
    eprintln!("F4_END_B0_SCAN_PASS host=Q115 ops={}",b.ops.len());

    let (mut b,ring,compact,q,y,sum,phase,pool)=static_layout();
    let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
    let roles=c659::Roles{tag:pool[0],cut:pool[1],toggle:pool[2].into()};
    let col=c659_column::Column{meta:&meta,roles,ring:&ring,q:&q,phase,
        compact:Some(&compact),dirty:&compact,clean_external:&[]};
    c659_endpoint::finish(&mut b,&col,None,&last);b.flush_global();
    assert!(!b.ops.iter().any(|op|touches(op,q[98])),"F4-END raw base tape touches Q98");
    eprintln!("F4_END_RAW_SCAN_PASS host=Q98 ops={}",b.ops.len());
    if let Some(v)=previous3{std::env::set_var("C658_WP3",v);}else{std::env::remove_var("C658_WP3");}
    if let Some(v)=previous4{std::env::set_var("C658_WP4",v);}else{std::env::remove_var("C658_WP4");}
}


#[test]
#[ignore = "diagnostic start state is not a valid paired traversal image; g7 is the dispatch admission"]
fn f4_139_cross_pair_done_and_fresh(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop,frogdrop_col,c659,k5_ph_ports};
    crate::point_add::bake_knobs();
    assert_eq!(std::env::var("C658_T23").as_deref(),Ok("1"));
    assert_eq!(std::env::var("C658_WP4").as_deref(),Ok("1"));
    let baseline=std::env::var("F4_139_BASELINE").as_deref()==Ok("1");
    if baseline{std::env::set_var("C658_WP4","0");}
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for col in 139..=145{for payload_first in [true,false]{
        let mut b=B::new();b.global_cancel=false;
        b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let mut ring=b.alloc_n(256);let terminal=b.alloc_n(258);
        ring.extend(b.alloc_n(1));let q=b.alloc_n(128);
        let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
        assert_eq!(b.width(),659);
        let mut fd=frogdrop_col::Fd{ring:ring.clone(),q:q.clone(),sy:y.clone(),sx:sum.clone(),
            ph,cnt:q[121..128].to_vec()};
        frogdrop_col::set_counter_epoch(&mut fd,col);
        let cp=&cps[col];
        let (first,second)=if payload_first{
            (k5_ph_ports::Traversal::T1,k5_ph_ports::Traversal::T2)
        }else{(k5_ph_ports::Traversal::T3,k5_ph_ports::Traversal::T4)};
        b.r14_pass=if payload_first{1}else{3};
        b.r14_roles=[terminal[0],terminal[1],pool[2]];
        c659::pair_column_for_fixture(&mut b,&fd,cp,&pool,&terminal,first);
        b.r14_pass=if payload_first{2}else{4};
        c659::pair_column_for_fixture(&mut b,&fd,cp,&pool,&terminal,second);
        b.r14_pass=0;b.flush_global();
        let width=b.width() as usize;let mut rng=Rng::new(0x139 + col as u64+u64::from(payload_first));
        let mut input=vec![0u64;width];
        // The fixed DONE source has R < 2^26. Keep its high ring cells zero.
        for &w in ring[..26].iter().chain(&terminal[2..]){input[w.0 as usize]=rng.next();}
        // DONE has PH=1, Q[64..121)=0, and a nonzero counter. Half the
        // packed shots have the fresh counter 1; half have held counters.
        for shot in 0..64{
            let yy=1+((shot*17+col)%26);
            let cnt=if shot<32{1}else{2+(shot-32)%62};
            word(&mut input,&q[..64],shot,yy);
            word(&mut input,&y,shot,yy-1);
            word(&mut input,&q[121..128],shot,cnt);
            bit(&mut input,ph,shot,1);
        }
        let got=run(&b.ops,width,&|v|*v=input.clone());
        assert_eq!(got.phase,0,"F4-139 col={col} payload_first={payload_first} phase");
        assert_eq!(got.q,input,"F4-139 col={col} payload_first={payload_first} all-wire");
        eprintln!("F4_139_PAIR_PASS col={col} baseline={baseline} pair=T{}T{} shots=64 fresh=32 held=32 ops={}",
            if payload_first{1}else{3},if payload_first{2}else{4},b.ops.len());
    }}
}

#[test]
#[ignore = "diagnostic start state is not a valid paired traversal image; g7 is the dispatch admission"]
fn f4_139_pair_captured_source(){
    use crate::point_add::{c659,frogdrop_col,
        frogdrop_sched,k1_complete_caller,k1_complete_io as io,k5_ph_ports,
        pointadd_frogdrop};
    crate::point_add::bake_knobs();
    std::env::set_var("R14_DIG_FIXTURE_RECIPE_CAP","1");
    assert_eq!(std::env::var("C658_T23").as_deref(),Ok("1"));
    assert_eq!(std::env::var("C658_WP4").as_deref(),Ok("1"));
    k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut checks=0;
    for payload_first in [true,false]{
        let mut source=k1_complete_caller::builder();
        let layout=k1_complete_caller::Layout::allocate(&mut source);
        let input=k1_complete_caller::initial(&layout,payload_first,0);
        let seed=if payload_first{b"r14-dig-c139-T1".as_slice()}
            else{b"r14-dig-c139-T3".as_slice()};
        let scope=io::begin(input,seed,io::PRODUCER_OP_CAP);
        source.x(layout.fd.ring[256]);drop(source);drop(layout);
        let mut captures=Vec::new();
        for cp in cps.iter().take(146){
            let mut b=B::new();b.global_cancel=false;
            b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
            let mut ring=b.alloc_n(256);let terminal=b.alloc_n(258);
            ring.extend(b.alloc_n(1));let q=b.alloc_n(128);
            let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
            assert_eq!(b.width(),659);
            let mut fd=frogdrop_col::Fd{ring,q:q.clone(),sy:y,sx:sum,
                ph,cnt:q[121..128].to_vec()};
            frogdrop_col::set_counter_epoch(&mut fd,cp.col);
            if (139..=145).contains(&cp.col){
                let(image,_)=io::snapshot();captures.push((cp.col,image));
            }
            std::env::set_var("C658_WP4","0");
            b.r14_pass=if payload_first{1}else{3};
            b.r14_roles=[terminal[0],terminal[1],pool[2]];
            c659::pair_column_for_fixture(&mut b,&fd,cp,&pool,&terminal,
                if payload_first{k5_ph_ports::Traversal::T1}else{k5_ph_ports::Traversal::T3});
            b.r14_pass=0;b.flush_global();
            assert!(b.ops.is_empty()&&b.pending_count()==0);
        }
        let(_,receipt)=io::finish(scope);
        assert_eq!(captures.len(),7);
        eprintln!("F4_139_SOURCE payload_first={payload_first} producer_ops={}",receipt.ops);
        for (col,image) in captures{
            let mut results=Vec::new();
            for wp4 in [false,true]{
                std::env::set_var("C658_WP4",if wp4{"1"}else{"0"});
                let mut b=B::new();b.global_cancel=false;
                b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
                let mut ring=b.alloc_n(256);let terminal=b.alloc_n(258);
                ring.extend(b.alloc_n(1));let q=b.alloc_n(128);
                let y=b.alloc_n(7);let sum=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
                assert_eq!(b.width(),659);
                let mut fd=frogdrop_col::Fd{ring:ring.clone(),q:q.clone(),sy:y,sx:sum,
                    ph,cnt:q[121..128].to_vec()};
                frogdrop_col::set_counter_epoch(&mut fd,col);
                let cp=&cps[col];
                let (first,second)=if payload_first{
                    (k5_ph_ports::Traversal::T1,k5_ph_ports::Traversal::T2)
                }else{(k5_ph_ports::Traversal::T3,k5_ph_ports::Traversal::T4)};
                b.r14_pass=if payload_first{1}else{3};
                b.r14_roles=[terminal[0],terminal[1],pool[2]];
                c659::pair_column_for_fixture(&mut b,&fd,cp,&pool,&terminal,first);
                b.r14_pass=if payload_first{2}else{4};
                c659::pair_column_for_fixture(&mut b,&fd,cp,&pool,&terminal,second);
                b.r14_pass=0;b.flush_global();
                let input=image.q[..659].to_vec();
                let got=run(&b.ops,659,&|x|*x=input.clone());
                let mut bad=0u64;
                for i in 0..659{if !(256..514).contains(&i){bad|=got.q[i]^input[i];}}
                let mut fresh=image.q[q[121].0 as usize];
                for &p in &q[122..128]{fresh&=!image.q[p.0 as usize];}
                let done=image.q[ph.0 as usize];
                eprintln!("F4_139_SOURCE_PAIR col={col} payload_first={payload_first} wp4={wp4} phase={:016x} nonpayload_bad={bad:016x} done={done:016x} fresh={fresh:016x} ops={}",got.phase,b.ops.len());
                results.push((got.phase,got.q));checks+=1;
            }
            assert_eq!(results[0],results[1],"F4-139 captured pair mismatch col={col} payload_first={payload_first}");
        }
    }
    std::env::set_var("C658_WP4","1");
    std::env::remove_var("R14_DIG_FIXTURE_RECIPE_CAP");
    assert_eq!(checks,28);
}


#[test]
fn f3_ds_hr_inverse_sign_shot_only(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    use crate::point_add::direct_payload::{Ranges};
    use crate::point_add::normalized_payload_q::k4_q3;
    fn make(cp:&crate::point_add::frogdrop_col::ColPar,ds:bool)
        ->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,QubitId,QubitId,QubitId,usize){
        let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let raw=b.alloc_n(259);let q=b.alloc_n(128);let y=b.alloc_n(7);let sum=b.alloc_n(5);
        let tag=b.alloc();let cut=b.alloc();let sign=b.alloc();let dirty=b.alloc_n(32);
        let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
        let ranges=Ranges{z:cp.sz,y:(cp.sy.0.max(1),cp.sy.1.min(128))};
        let roles=super::Roles3{activity:tag,flight:cut,sign};
        std::env::set_var("C658_WP3","1");
        std::env::set_var("C658_WP3_DS",if ds{"1"}else{"0"});
        b.begin();k4_q3::inverse3(&mut b,&meta,&q,&raw,roles,ranges,&dirty,&[]);
        let tape=b.end();b.play(&tape,false);let f=b.ops.len();b.play(&tape,true);
        (b,raw,q,y,sum,tag,cut,sign,dirty[0],f)
    }
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);let cp=&cps[37];
    let active:Vec<_>=(0..128).flat_map(|ee|(0..32).map(move|s|(ee,s)))
        .filter(|&(ee,s)|{let yy=ee+1;let zz=225+s-ee;
            cp.sy.0<=yy&&yy<=cp.sy.1.min(128)&&cp.sz.0<=zz&&zz<=cp.sz.1}).collect();
    let(ee,s)=active[(63*17+37)%active.len()];let yy=ee+1;let zz=225+s-ee;
    let(old,raw,q,y,sum,tag,cut,sign,_d,of)=make(cp,false);
    let(new,_,_,_,_,_,_,_,_,nf)=make(cp,true);
    let mut a=vec![0u64;old.width() as usize];let mut z=a.clone();
    word(&mut a,&y,63,ee);word(&mut a,&sum,63,s);bit(&mut a,tag,63,1);bit(&mut a,sign,63,1);
    bit(&mut a,q[yy-1],63,1);
    for i in 258-yy..=258{bit(&mut a,raw[i],63,1);}
    z.clone_from(&a);z[sign.0 as usize]=0;bit(&mut z,cut,63,1);
    let ao=run(&old.ops[..of],old.width() as usize,&|x|*x=a.clone());
    let zo=run(&new.ops[..nf],new.width() as usize,&|x|*x=z.clone());
    let ad:Vec<_>=a.iter().zip(&ao.q).enumerate().filter(|(_, (x,y))|x!=y)
        .map(|(i,(x,y))|(i,*x^*y)).take(8).collect();
    let zd:Vec<_>=z.iter().zip(&zo.q).enumerate().filter(|(_, (x,y))|x!=y)
        .map(|(i,(x,y))|(i,*x^*y)).take(8).collect();
    eprintln!("F3_DS_HR_KERNEL c37 shot63 E={ee} S={s} Y={yy} Z={zz} old_diffs={ad:?} new_diffs={zd:?} phases={:x}/{:x}",ao.phase,zo.phase);
    assert_eq!(ao.phase,zo.phase);assert_eq!(ad,zd,"HR inverse3 sign-shot delta");
}

#[test]
fn f3_ds_c37_read_and_walk_only(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    fn make(cp:&crate::point_add::frogdrop_col::ColPar,ds:bool,walk:bool)
        ->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,QubitId,QubitId,usize){
        let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let raw=b.alloc_n(259);let y=b.alloc_n(7);let sum=b.alloc_n(5);
        let tag=b.alloc();let cut=b.alloc();let sign=b.alloc();let dirty=b.alloc_n(32);
        let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
        let rr=cp.sz;let tr=(cp.sy.0.max(1),cp.sy.1.min(128));
        b.begin();
        if walk{super::dwalk_sign(&mut b,&meta,&raw,Size::Z,rr,Size::Y,tr,
            if ds{cut}else{sign},cut,&dirty);
            if ds{super::read_selected_cut(&mut b,&meta,Size::Z,rr,&raw,
                |r|r,tag,cut,&dirty);}
            else{super::super::read_selected(&mut b,&meta,Size::Z,rr,&raw,
                |r|r,sign,tag,cut,&dirty);}}
        else if ds{super::read_selected_cut(&mut b,&meta,Size::Y,tr,&raw,
            |t|258-t,tag,cut,&dirty);}
        else{super::super::read_selected(&mut b,&meta,Size::Y,tr,&raw,
            |t|258-t,sign,tag,cut,&dirty);}
        let tape=b.end();b.play(&tape,false);let f=b.ops.len();b.play(&tape,true);
        (b,raw,y,sum,tag,cut,sign,f)
    }
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);let cp=&cps[37];
    for walk in [false,true]{
        let(old,raw,y,sum,tag,cut,sign,of)=make(cp,false,walk);
        let(new,_,_,_,_,_,_,nf)=make(cp,true,walk);
        let mut a=vec![0u64;old.width() as usize];let mut z=a.clone();
        word(&mut a,&y,63,58);word(&mut a,&sum,63,23);bit(&mut a,tag,63,1);
        for i in 199..=258{bit(&mut a,raw[i],63,1);}
        z.clone_from(&a);
        if walk {bit(&mut a,sign,63,1);bit(&mut z,cut,63,1);}
        let ao=run(&old.ops[..of],old.width() as usize,&|x|*x=a.clone());
        let zo=run(&new.ops[..nf],new.width() as usize,&|x|*x=z.clone());
        let diffs:Vec<_>=raw.iter().filter_map(|q|{
            let i=q.0 as usize;let delta=ao.q[i]^zo.q[i];(delta!=0).then_some((i,delta))
        }).take(12).collect();
        eprintln!("F3_DS_C37_STAGE walk={walk} raw_diffs={diffs:?} old_flag={:x} new_flag={:x} phase={:x}/{:x}",
            ao.q[sign.0 as usize],zo.q[cut.0 as usize],ao.phase,zo.phase);
        assert!(diffs.is_empty()&&ao.phase==zo.phase,"DS read/walk mismatch");
        assert_eq!(ao.q[sign.0 as usize],zo.q[cut.0 as usize],"DS encoded flag");
    }
}


#[test]
fn f3_ds_c37_stage_trace(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);let cp=&cps[37];
    std::env::set_var("C658_WP3_ZH","0");
    for stage in ["read1","inverse","walk"]{
        std::env::set_var("R14_DIG_TRACE_STOP",stage);
        std::env::set_var("C658_WP3_DS","0");
        let(old,ring,p,q,y,sum,ph,tag,cut,sign,_work,of)=digit_builder(cp,false,true);
        std::env::set_var("C658_WP3_DS","1");
        let(new,_,_,_,_,_,_,_,_,_,_,nf)=digit_builder(cp,false,true);
        let mut input=vec![0u64;old.width() as usize];
        for shot in 0..64{
            word(&mut input,&y,shot,58);word(&mut input,&sum,shot,23);bit(&mut input,tag,shot,1);
            bit(&mut input,q[58],shot,1);bit(&mut input,ring[189],shot,1);bit(&mut input,p[0],shot,1);
            let w=(1u64<<59)-(shot as u64+1);
            for j in 0..59{if w>>j&1==1{if j==0{bit(&mut input,ph,shot,1);}
                else{bit(&mut input,p[258-j],shot,1);}}}
        }
        let a=run(&old.ops[..of],old.width() as usize,&|x|*x=input.clone());
        let z=run(&new.ops[..nf],new.width() as usize,&|x|*x=input.clone());
        let rawdiff:Vec<_>=p.iter().chain([&ph]).filter_map(|lane|{
            let i=lane.0 as usize;let delta=a.q[i]^z.q[i];(delta!=0).then_some((i,delta))
        }).take(12).collect();
        let qdiff:Vec<_>=q.iter().filter_map(|lane|{
            let i=lane.0 as usize;let delta=a.q[i]^z.q[i];(delta!=0).then_some((i,delta))
        }).take(12).collect();
        let mut slots_old=0u64;let mut slots_new=0u64;
        for i in 190..199{slots_old|=a.q[p[i].0 as usize];slots_new|=z.q[p[i].0 as usize];}
        eprintln!("F3_DS_STAGE c37 {stage} rawdiff={rawdiff:?} qdiff={qdiff:?} slots={slots_old:x}/{slots_new:x} tag={:x}/{:x} cut={:x}/{:x} sign={:x}/{:x} phase={:x}/{:x}",
            a.q[tag.0 as usize],z.q[tag.0 as usize],a.q[cut.0 as usize],z.q[cut.0 as usize],
            a.q[sign.0 as usize],z.q[sign.0 as usize],a.phase,z.phase);
    }
    std::env::remove_var("R14_DIG_TRACE_STOP");
}


#[test]
fn f3_ds_c37_sign_preimage(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);let cp=&cps[37];
    std::env::set_var("C658_WP3_ZH","0");std::env::set_var("C658_WP3_DS","0");
    std::env::set_var("R14_DIG_TRACE_STOP","read1");
    let(pre,ring,p,q,y,sum,ph,tag,cut,sign,_work,pf)=digit_builder(cp,false,true);
    let width=pre.width() as usize;let mut desired=vec![0u64;width];
    word(&mut desired,&y,0,58);word(&mut desired,&sum,0,23);bit(&mut desired,tag,0,1);
    bit(&mut desired,q[58],0,1);bit(&mut desired,ring[189],0,1);bit(&mut desired,p[0],0,1);
    for i in 199..258{bit(&mut desired,p[i],0,1);}bit(&mut desired,ph,0,1);
    bit(&mut desired,sign,0,1);
    let back=run(&pre.ops[pf..],width,&|x|*x=desired.clone());
    let entry=back.q;
    let high_d=(0..190).filter(|&i|entry[p[i].0 as usize]&1!=0).collect::<Vec<_>>();
    let quotient=(190..199).filter(|&i|entry[p[i].0 as usize]&1!=0).collect::<Vec<_>>();
    let pre_w=(199..258).filter(|&i|entry[p[i].0 as usize]&1!=0).collect::<Vec<_>>();
    eprintln!("F3_DS_PREIMAGE c37 entry a={} cut={} sign={} ph={} qtop={} rtop={} d_bits={high_d:?} q_bits={quotient:?} w_bits={pre_w:?}",
        entry[tag.0 as usize]&1,entry[cut.0 as usize]&1,entry[sign.0 as usize]&1,
        entry[ph.0 as usize]&1,entry[q[58].0 as usize]&1,entry[ring[189].0 as usize]&1);
    let check=run(&pre.ops[..pf],width,&|x|*x=entry.clone());
    assert_eq!(check.q,desired,"prefix inverse image");
    std::env::remove_var("R14_DIG_TRACE_STOP");
    std::env::set_var("C658_WP3_DS","0");let(old,_,_,_,_,_,_,_,_,_,_,of)=digit_builder(cp,false,true);
    std::env::set_var("C658_WP3_DS","1");let(new,_,_,_,_,_,_,_,_,_,_,nf)=digit_builder(cp,false,true);
    let ao=run(&old.ops[..of],width,&|x|*x=entry.clone());
    let zo=run(&new.ops[..nf],width,&|x|*x=entry.clone());
    let diffs:Vec<_>=ao.q.iter().zip(&zo.q).enumerate().filter(|(_, (x,y))|x!=y)
        .map(|(i,(x,y))|(i,*x^*y)).take(16).collect();
    eprintln!("F3_DS_PREIMAGE_FULL c37 first_diffs={diffs:?} phases={:x}/{:x} old_ops={of} new_ops={nf}",ao.phase,zo.phase);
}

#[test]
fn f3_ds_c37_ht_stage_trace(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);let cp=&cps[37];
    let active:Vec<_>=(0..128).flat_map(|ee|(0..32).map(move|s|(ee,s)))
        .filter(|&(ee,s)|{let yy=ee+1;let zz=225+s-ee;
            cp.sy.0<=yy&&yy<=cp.sy.1.min(128)&&cp.sz.0<=zz&&zz<=cp.sz.1}).collect();
    let shot=9;let(ee,s)=active[(shot*17+37)%active.len()];let yy=ee+1;let zz=225+s-ee;
    for stage in ["read1","inverse","walk","read2","full"]{
        if stage=="full"{std::env::remove_var("R14_DIG_TRACE_STOP");}else{std::env::set_var("R14_DIG_TRACE_STOP",stage);}
        std::env::set_var("C658_WP3_ZH","0");std::env::set_var("C658_WP3_DS","0");
        let(old,ring,p,q,y,sum,ph,tag,cut,sign,_work,of)=digit_builder(cp,true,true);
        std::env::set_var("C658_WP3_DS","1");
        let(new,_,_,_,_,_,_,_,_,_,_,nf)=digit_builder(cp,true,true);
        let mut input=vec![0u64;old.width() as usize];
        word(&mut input,&y,0,ee);word(&mut input,&sum,0,s);bit(&mut input,tag,0,1);
        bit(&mut input,q[yy-1],0,1);bit(&mut input,ring[zz-1],0,1);bit(&mut input,p[0],0,1);
        let a=run(&old.ops[..of],old.width() as usize,&|x|*x=input.clone());
        let z=run(&new.ops[..nf],new.width() as usize,&|x|*x=input.clone());
        let diff:Vec<_>=a.q.iter().zip(&z.q).enumerate().filter(|(_, (x,y))|x!=y)
            .map(|(i,(x,y))|(i,*x^*y)).take(15).collect();
        let slots_old=(190..199).filter(|&i|a.q[p[i].0 as usize]&1!=0).collect::<Vec<_>>();
        let slots_new=(190..199).filter(|&i|z.q[p[i].0 as usize]&1!=0).collect::<Vec<_>>();
        eprintln!("F3_DS_HT_STAGE c37 shot9 E={ee} S={s} Y={yy} Z={zz} {stage} diff={diff:?} slots={slots_old:?}/{slots_new:?} tag={}/{}, cut={}/{}, sign={}/{}, phase={}/{}",a.q[tag.0 as usize]&1,z.q[tag.0 as usize]&1,a.q[cut.0 as usize]&1,z.q[cut.0 as usize]&1,a.q[sign.0 as usize]&1,z.q[sign.0 as usize]&1,a.phase,z.phase);
    }
    std::env::remove_var("R14_DIG_TRACE_STOP");
}

#[test]
fn f3_ds_ht_c1_mandatory(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    use crate::point_add::direct_payload::Ranges;
    use crate::point_add::single_z_maj::k4_z3;
    fn make(cp:&crate::point_add::frogdrop_col::ColPar,k:usize,ds:bool)
        ->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,QubitId,QubitId,usize){
        let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let ring=b.alloc_n(257);let raw=b.alloc_n(259);let q=b.alloc_n(128);
        let y=b.alloc_n(7);let sum=b.alloc_n(5);let tag=b.alloc();let cut=b.alloc();let sign=b.alloc();
        let dirty=b.alloc_n(32);let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
        let ranges=Ranges{z:cp.sz,y:(cp.sy.0.max(1),cp.sy.1.min(128))};
        let roles=super::Roles3{activity:tag,flight:cut,sign};
        std::env::set_var("C658_WP3","1");std::env::set_var("C658_WP3_ZH","0");
        std::env::set_var("C658_WP3_DS",if ds{"1"}else{"0"});
        let zframe=crate::point_add::single_z_maj::frame_record(&mut b,&meta,&q);
        b.begin();b.play(&zframe,false);
        k4_z3::apply3(&mut b,&meta,&q,&raw,&ring,roles,ranges,k,true,&dirty,&[]);
        b.play(&zframe,true);let tape=b.end();b.play(&tape,false);let f=b.ops.len();b.play(&tape,true);
        (b,ring,raw,q,y,sum,tag,cut,sign,f)
    }
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for &(col,k,yy,zz,s) in &[(52,4,127,130,31),(37,7,128,125,27),
        (95,17,16,238,28),(95,17,4,238,16)]{
        let cp=&cps[col];let(old,ring,raw,q,y,sum,tag,cut,sign,of)=make(cp,k,false);
        let(new,_,_,_,_,_,_,_,_,nf)=make(cp,k,true);
        assert_eq!(old.width(),new.width());
        let mut input=vec![0u64;old.width() as usize];
        word(&mut input,&y,0,yy-1);word(&mut input,&sum,0,s);bit(&mut input,tag,0,1);
        bit(&mut input,q[yy-1],0,1);bit(&mut input,ring[zz-1],0,1);
        // q1 is the c52 source's dirty high-address prefix; other prefixes
        // are deliberately dirty as well. The skipped call must stay inert.
        if col==52 { bit(&mut input,q[0],0,1); }
        bit(&mut input,q[1],0,1);bit(&mut input,q[3],0,1);
        if col==52 {
            let mut frame_builder=B::new();
            let _ring=frame_builder.alloc_n(257);let _raw=frame_builder.alloc_n(259);
            let fq=frame_builder.alloc_n(128);let fy=frame_builder.alloc_n(7);
            let fs=frame_builder.alloc_n(5);
            let fm=SumSize{y:fy.as_slice().try_into().unwrap(),
                sum:fs.as_slice().try_into().unwrap()};
            let frame=crate::point_add::single_z_maj::frame_record(&mut frame_builder,&fm,&fq);
            frame_builder.play(&frame,false);
            let framed=run(&frame_builder.ops,frame_builder.width() as usize,
                &|x|*x=input[..frame_builder.width() as usize].to_vec());
            assert_eq!(framed.q[fq[1].0 as usize]&1,1,"F3-C1 c52 q1 active after frame");
        }
        for i in 0..259{if i%7==0{bit(&mut input,raw[i],0,1);}}
        let a=run(&old.ops[..of],old.width() as usize,&|x|*x=input.clone());
        let z=run(&new.ops[..nf],new.width() as usize,&|x|*x=input.clone());
        let diff=a.q.iter().zip(&z.q).enumerate().filter(|(_, (x,y))|x!=y)
            .map(|(i,(x,y))|(i,*x^*y)).take(10).collect::<Vec<_>>();
        eprintln!("F3_DS_HT_C1 col={col} k={k} Y={yy} Z={zz} S={s} diff={diff:?} phase={}/{} old_ops={of} new_ops={nf}",a.phase,z.phase);
        assert_eq!(a.phase,z.phase);assert!(diff.is_empty(),"C1 alias mismatch");
        let back=run(&new.ops,new.width() as usize,&|x|*x=input.clone());
        assert_eq!(back.phase,0);assert_eq!(back.q,input,"C1 inverse closure");
        let _=(cut,sign);
    }
}

#[test]
fn f3_pds_negative_sign_slot(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);let cp=&cps[37];
    std::env::set_var("C658_WP3_ZH","0");std::env::set_var("C658_WP3_DS","0");
    std::env::set_var("R14_DIG_TRACE_STOP","read1");
    let(pre,ring,p,q,y,sum,ph,tag,_cut,sign,_work,pf)=digit_builder(cp,false,true);
    let width=pre.width() as usize;let mut desired=vec![0u64;width];
    word(&mut desired,&y,0,58);word(&mut desired,&sum,0,23);bit(&mut desired,tag,0,1);
    bit(&mut desired,q[58],0,1);bit(&mut desired,ring[189],0,1);
    for i in 199..258{bit(&mut desired,p[i],0,1);}bit(&mut desired,ph,0,1);
    bit(&mut desired,sign,0,1);bit(&mut desired,p[198],0,1);
    let back=run(&pre.ops[pf..],width,&|x|*x=desired.clone());
    let entry=back.q;
    let check=run(&pre.ops[..pf],width,&|x|*x=entry.clone());
    assert_eq!(check.q,desired,"F3-PDS injected read-boundary preimage");
    std::env::remove_var("R14_DIG_TRACE_STOP");
    std::env::set_var("C658_WP3_DS","0");let(old,_,_,_,_,_,_,_,_,_,_,of)=digit_builder(cp,false,true);
    std::env::set_var("C658_WP3_DS","1");let(new,_,_,_,_,_,_,_,_,_,_,nf)=digit_builder(cp,false,true);
    let a=run(&old.ops[..of],width,&|x|*x=entry.clone());
    let z=run(&new.ops[..nf],width,&|x|*x=entry.clone());
    let diff=a.q.iter().zip(&z.q).enumerate().filter(|(_, (x,y))|x!=y)
        .map(|(i,(x,y))|(i,*x^*y)).take(12).collect::<Vec<_>>();
    eprintln!("F3_PDS_NEG c37 HR read1 sign=1 slot198=1 diff={diff:?} phases={}/{} old_ops={of} new_ops={nf}",a.phase,z.phase);
    assert!(!diff.is_empty()||a.phase!=z.phase,"P_DS negative control must detect violation");
}

#[test]
fn f3_zh_c85_virtual_top_c2_negative(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    crate::point_add::bake_knobs();
    std::env::set_var("C658_WP3","1");
    std::env::set_var("C658_WP3_DS","0");
    std::env::set_var("C658_WP3_ZH","0");
    std::env::set_var("C658_WP3_ZH_GATHER","1");
    std::env::set_var("R14_DIG_TRACE_STOP","read1");
    std::env::remove_var("R14_DIG_MUT_C2_OFF");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let cp=&cps[85];
    let(old,ring,p,q,y,sum,_phase,a,_e,_sign,_work,of)=digit_builder(cp,false,true);
    std::env::set_var("C658_WP3_ZH","1");
    let(new,_,_,_,_,_,_,_,_,_,_,nf)=digit_builder(cp,false,true);
    std::env::set_var("R14_DIG_MUT_C2_OFF","1");
    let(bad,_,_,_,_,_,_,_,_,_,_,bf)=digit_builder(cp,false,true);
    std::env::remove_var("R14_DIG_MUT_C2_OFF");
    std::env::remove_var("R14_DIG_TRACE_STOP");
    let mut input=vec![0u64;old.width() as usize];
    for shot in 0..64{
        word(&mut input,&y,shot,22);word(&mut input,&sum,shot,31);
        bit(&mut input,a,shot,1);bit(&mut input,q[22],shot,1);
        for j in 0..3{if shot>>j&1!=0{bit(&mut input,ring[232-j],shot,1);}}
        for j in 0..3{if shot>>(j+3)&1!=0{bit(&mut input,p[233+j],shot,1);}}
    }
    assert_eq!(input[ring[233].0 as usize],0);
    let prior=run(&old.ops[..of],old.width() as usize,&|x|*x=input.clone());
    let next=run(&new.ops[..nf],new.width() as usize,&|x|*x=input.clone());
    let wrong=run(&bad.ops[..bf],bad.width() as usize,&|x|*x=input.clone());
    let exact_bad=prior.q.iter().zip(&next.q)
        .fold(prior.phase^next.phase,|m,(x,y)|m|(x^y));
    let mutant_bad=prior.q.iter().zip(&wrong.q)
        .fold(prior.phase^wrong.phase,|m,(x,y)|m|(x^y));
    let witness=(!exact_bad)&mutant_bad;
    let case=1u64<<8;
    let diff8:Vec<_>=next.q.iter().zip(&wrong.q).enumerate()
        .filter(|(_, (x,y))|(*x^*y)&case!=0).map(|(i,_)|i).collect();
    eprintln!("F3_ZH_C85_SEARCH exact_bad={exact_bad:016x} mutant_bad={mutant_bad:016x} witness={witness:016x} ops={of}/{nf}/{bf}");
    eprintln!("F3_ZH_C85_K0 shot=8 diff_wires={diff8:?} t233={} t105={} ring_top={} d233={}",
        (next.q[p[233].0 as usize]^wrong.q[p[233].0 as usize])&case!=0,
        (next.q[p[105].0 as usize]^wrong.q[p[105].0 as usize])&case!=0,
        input[ring[233].0 as usize]&case!=0,input[p[233].0 as usize]&case!=0);
    assert_ne!(witness&case,0,"F3-ZH mandatory c85 k0 shot8");
    assert_ne!(witness,0,"F3-ZH c85 must reach C2 correction");
}

#[test]
fn f3_b2_real_calls_and_negative(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    use crate::point_add::direct_payload::Ranges;
    use crate::point_add::single_z_maj::k4_z3;
    fn make(cp:&crate::point_add::frogdrop_col::ColPar,k:usize,inverse:bool,b2:bool)
        ->(B,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,Vec<QubitId>,QubitId,QubitId,QubitId,usize){
        let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let ring=b.alloc_n(257);let raw=b.alloc_n(259);let q=b.alloc_n(128);
        let y=b.alloc_n(7);let sum=b.alloc_n(5);let tag=b.alloc();let cut=b.alloc();let sign=b.alloc();
        let dirty=b.alloc_n(32);let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
        let ranges=Ranges{z:cp.sz,y:(cp.sy.0.max(1),cp.sy.1.min(128))};
        let roles=super::Roles3{activity:tag,flight:cut,sign};
        std::env::set_var("C658_WP3","1");std::env::set_var("C658_WP3_DS","0");
        std::env::set_var("C658_WP3_ZH","0");std::env::set_var("C658_WP3_B2",if b2{"1"}else{"0"});
        let zframe=crate::point_add::single_z_maj::frame_record(&mut b,&meta,&q);
        b.begin();b.play(&zframe,false);
        if !inverse{
            let lead=k4_z3::leading_one_record3(&mut b,&meta,&ring,roles,cp.sz,&dirty);
            b.play(&lead,false);
            k4_z3::apply3(&mut b,&meta,&q,&raw,&ring,roles,ranges,k,false,&dirty,&[]);
            b.play(&lead,true);
        }else{k4_z3::apply3(&mut b,&meta,&q,&raw,&ring,roles,ranges,k,true,&dirty,&[]);}
        b.play(&zframe,true);let tape=b.end();b.play(&tape,false);let f=b.ops.len();b.play(&tape,true);
        (b,ring,raw,q,y,sum,tag,cut,sign,f)
    }
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut checked=0;
    for &(col,inverse) in &[(37,false),(50,false),(85,false),(96,false),(110,false),(112,false),
        (37,true),(50,true),(97,true),(114,true),(126,true),(138,true)]{
        let cp=&cps[col];let k=0usize;
        let active=(0..128).flat_map(|ee|(0..32).map(move|s|(ee,s)))
            .find(|&(ee,s)|{let yy=ee+1;let zz=225+s-ee;
                cp.sy.0<=yy&&yy<=cp.sy.1.min(128)&&cp.sz.0<=zz&&zz<=cp.sz.1});
        let Some((ee,s))=active else{continue;};let yy=ee+1;let zz=225+s-ee;
        let(old,ring,raw,q,y,sum,tag,_cut,_sign,of)=make(cp,k,inverse,false);
        let(new,_,_,_,_,_,_,_,_,nf)=make(cp,k,inverse,true);
        let mut input=vec![0u64;old.width() as usize];
        word(&mut input,&y,0,ee);word(&mut input,&sum,0,s);bit(&mut input,tag,0,1);
        bit(&mut input,q[yy-1],0,1);bit(&mut input,ring[zz-1],0,1);
        // d has only bits below r's top, hence d<r<2r.
        for i in (0..zz-1).step_by(11){let lane=if inverse{258-k-i}else{k+i};bit(&mut input,raw[lane],0,1);}
        let a=run(&old.ops[..of],old.width() as usize,&|x|*x=input.clone());
        let z=run(&new.ops[..nf],new.width() as usize,&|x|*x=input.clone());
        let diff=a.q.iter().zip(&z.q).enumerate().filter(|(_, (x,y))|x!=y)
            .map(|(i,(x,y))|(i,*x^*y)).take(8).collect::<Vec<_>>();
        eprintln!("F3_B2 col={col} inverse={inverse} Y={yy} Z={zz} S={s} diff={diff:?} phase={}/{} old_ops={of} new_ops={nf}",a.phase,z.phase);
        assert!(diff.is_empty()&&a.phase==z.phase,"B2 success-support mismatch");
        let back=run(&new.ops,new.width() as usize,&|x|*x=input.clone());
        assert_eq!(back.phase,0);assert_eq!(back.q,input);checked+=1;
    }
    assert_eq!(checked,12,"B2 real call coverage");
    // Deliberate violation: r=2^(Z-1), d=2^Z+low >= 2r.
    let cp=&cps[37];let(old,ring,raw,q,y,sum,tag,_cut,_sign,of)=make(cp,0,false,false);
    let(new,_,_,_,_,_,_,_,_,nf)=make(cp,0,false,true);
    let ee=58usize;let s=23usize;let yy=ee+1;let zz=225+s-ee;
    let mut found=None;
    for chunk in 0..64{
        let mut input=vec![0u64;old.width() as usize];
        for i in 0..y.len(){if ee>>i&1!=0{input[y[i].0 as usize]=u64::MAX;}}
        for i in 0..sum.len(){if s>>i&1!=0{input[sum[i].0 as usize]=u64::MAX;}}
        input[tag.0 as usize]=u64::MAX;input[q[yy-1].0 as usize]=u64::MAX;
        input[ring[zz-1].0 as usize]=u64::MAX;input[raw[zz].0 as usize]=u64::MAX;
        let mut rng=Rng::new(0xb200_0000+chunk);
        for i in 0..zz{input[raw[i].0 as usize]=rng.next();}
        let a=run(&old.ops[..of],old.width() as usize,&|x|*x=input.clone());
        let z=run(&new.ops[..nf],new.width() as usize,&|x|*x=input.clone());
        if let Some((wire,mask))=a.q.iter().zip(&z.q).enumerate().find_map(|(i,(x,y))|
            ((*x^*y)!=0).then_some((i,*x^*y))){found=Some((chunk,wire,mask));break;}
        if a.phase!=z.phase{found=Some((chunk,usize::MAX,a.phase^z.phase));break;}
    }
    eprintln!("F3_B2_NEG c37 HR r=2^189 d>=2^190 result={found:?}");
    assert!(found.is_some(),"B2 negative control must differ on d>=2r");
}

#[test]
fn f3_g4_probe_c37_ht(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    std::env::set_var("R14_CENSUS_OUT","/tmp/r14-dig-g4-probe.tsv");
    std::env::set_var("R14_K5_FORBID_POOL2","1");
    std::env::set_var("R14_DIG_G4_PROBE","1");
    std::env::set_var("C658_WP3_DS","1");
    std::env::set_var("C658_WP3_ZH","1");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let(b,_,_,_,_,_,_,_,_,_,_,f)=digit_builder(&cps[37],true,true);
    eprintln!("F3_G4_PROBE no pool2 touch width={} ops={f}",b.width());
}

#[test]
fn f3_g4_probe_all_digit_columns(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    std::env::set_var("R14_CENSUS_OUT","/tmp/r14-dig-g4-all.tsv");
    std::env::set_var("R14_K5_FORBID_POOL2","1");
    std::env::set_var("R14_DIG_G4_PROBE","1");
    std::env::set_var("C658_WP3_DS","1");
    std::env::set_var("C658_WP3_ZH","1");
    std::env::remove_var("C658_WP3_DS_DIRECT");
    std::env::set_var("C658_WP3_ZH_GATHER","1");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut nhr=0;let mut nht=0;
    for cp in &cps{
        if cp.hr{let _=digit_builder(cp,false,true);nhr+=1;}
        if cp.ht{let _=digit_builder(cp,true,true);nht+=1;}
        if cp.col%20==0{eprintln!("F3_G4_PROGRESS col={} HR={} HT={}",cp.col,nhr,nht);}
    }
    eprintln!("F3_G4_ALL_PASS HR={nhr} HT={nht} pool2_ops=0");
}

#[test]
fn f4_g4_probe_owned(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    use crate::point_add::outer_three_records::SwapBoundary;
    std::env::set_var("R14_CENSUS_OUT","/tmp/r14-dig-f4-g4-probe.tsv");
    std::env::set_var("R14_K5_FORBID_POOL2","1");
    std::env::set_var("R14_DIG_G4_PROBE","1");
    for l in [200,207,230,241,255]{let _=mt_builder(l,true);}
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for &col in &[37,88,97,114,115]{
        for boundary in [SwapBoundary::Enter,SwapBoundary::AfterCompleteMiddle]{
            let _=cut_builder(&cps[col],boundary,true);
        }
    }
    for &col in &[85,96,110,112]{for enter in [true,false]{
        let _=nrc_builder(&cps[col],enter,true);
    }}
    eprintln!("F4_G4_PROBE_PASS outer MT/cut/NRC pool2_ops=0");
}

#[test]
fn f4_g4_probe_column_outer(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop,c659,c659_column};
    std::env::set_var("C658_WP4","1");
    std::env::set_var("C658_WP3","1");
    std::env::set_var("R14_CENSUS_OUT","/tmp/r14-dig-f4-g4-column.tsv");
    std::env::set_var("R14_K5_FORBID_POOL2","1");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for cp in &cps{
        if cp.nomap{continue;}
        let col=cp.col;
        let(mut b,ring,terminal,q,y,sum,phase,pool)=static_layout();
        let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
        let roles=c659::Roles{tag:pool[0],cut:pool[1],toggle:pool[2].into()};
        let outer=c659_column::Column{meta:&meta,roles,ring:&ring,q:&q,phase,
            compact:Some(&terminal),dirty:&terminal,clean_external:&[]};
        b.r14_pass=1;b.r14_roles=[terminal[0],terminal[1],pool[2]];
        outer.enter_middle(&mut b,cp);
        outer.leave_middle(&mut b,cp);
        eprintln!("F4_G4_COLUMN_PASS col={col} ops={}",b.ops.len());
    }
}

#[test]
fn f4_c0_direct_narrow_all_wire(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop};
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let cp=&cps[0];let range=(cp.sz.0.max(129),cp.sz.1);
    assert_eq!(range.1,256);
    let make=|encoded:bool|{
        let mut b=B::new();b.global_cancel=false;
        b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let compact=b.alloc_n(258);let q=b.alloc_n(128);let upper=b.alloc_n(257);
        let y=b.alloc_n(7);let sum=b.alloc_n(5);
        let tag=b.alloc();let cut=b.alloc();let toggle=b.alloc();let dirty=b.alloc_n(32);
        let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
        let flag=if encoded{super::FlagHost::Encoded{tag,cut}}else{super::FlagHost::Lane(toggle)};
        let address=if encoded{super::Address3::Direct}else{super::Address3::HostedTag(tag)};
        b.begin();super::narrow3(&mut b,&meta,&compact,&q,Some(&upper),range,cut,flag,address,
            &dirty,&[],false);
        let tape=b.end();b.play(&tape,false);let f=b.ops.len();b.play(&tape,true);
        (b,compact,q,upper,y,sum,tag,cut,toggle,dirty,f)
    };
    let(old,p,q,u,y,sum,tag,cut,toggle,dirty,of)=make(false);
    let(new,_,_,_,_,_,_,_,_,_,nf)=make(true);
    let width=old.width()as usize;assert_eq!(width,new.width()as usize);
    let mut rng=Rng::new(0xc000_0256);
    for chunk in 0..64{
        let mut input=vec![0u64;width];
        for &w in p.iter().chain(&q).chain(&u).chain(&dirty){input[w.0 as usize]=rng.next();}
        for shot in 0..64{let n=chunk*64+shot;let e=n/32;let s=n%32;
            word(&mut input,&y,shot,e);word(&mut input,&sum,shot,s);
            if (e+s)&1!=0{bit(&mut input,cut,shot,1);}
        }
        let a=run(&old.ops[..of],width,&|v|*v=input.clone());
        let z=run(&new.ops[..nf],width,&|v|*v=input.clone());
        assert_eq!((a.phase,z.phase),(0,0));
        assert_eq!(a.q,z.q,"F4-C0 direct forward chunk={chunk}");
        let back=run(&new.ops,width,&|v|*v=input.clone());
        assert_eq!(back.phase,0);assert_eq!(back.q,input,"F4-C0 inverse chunk={chunk}");
    }
    eprintln!("F4_C0_DIRECT_PASS range={range:?} cases=4096 tag=0 toggle=0 old_ops={of} new_ops={nf}");
}

#[test]
fn f4_c1_static_port_scan(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop,c659_column,c659_fixed,c659};
    crate::point_add::bake_knobs();
    std::env::set_var("C658_DROP","0");
    std::env::set_var("C658_WP4_C1","0");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let cp=&cps[1];
    assert_eq!((cp.col,cp.sy.1),(1,39));
    let (mut b,ring,compact,q,y,sum,phase,pool)=static_layout();
    let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
    let roles=c659::Roles{tag:pool[0],cut:pool[1],toggle:pool[2].into()};
    let col=c659_column::Column{meta:&meta,roles,ring:&ring,q:&q,phase,
        compact:Some(&compact),dirty:&compact,clean_external:&[]};
    c659_fixed::run(&mut b,&col,cp);b.flush_global();
    let used:BTreeSet<_>=b.ops.iter().flat_map(|op|
        [op.q_target,op.q_control1,op.q_control2]).collect();
    let free:Vec<_>=(40..121).filter(|&i|!used.contains(&q[i])).collect();
    assert!(!cp.dn&&cp.sy.1<101,"c1 Q101 entry-zero source box");
    assert!(!used.contains(&q[101]),"c1 inherited fixed tape names Q101");
    eprintln!("F4_C1_SCAN col=1 Yhi={} Zlo={} done={} free={free:?} q98_uses={} ops={}",
        cp.sy.1,cp.sz.0,cp.dn,b.ops.iter().filter(|op|touches(op,q[98])).count(),b.ops.len());
    let mut old=b.ops.clone();
    for op in &mut old {
        for port in [&mut op.q_target,&mut op.q_control1,&mut op.q_control2] {
            if *port==pool[2] {*port=q[101];}
        }
    }
    std::env::set_var("C658_WP4_C1","1");
    let(mut h,ring_h,compact_h,q_h,y_h,sum_h,phase_h,pool_h)=static_layout();
    assert_eq!((pool_h[2],q_h[101]),(pool[2],q[101]));
    let meta_h=SumSize{y:y_h.as_slice().try_into().unwrap(),sum:sum_h.as_slice().try_into().unwrap()};
    let roles_h=c659::Roles{tag:pool_h[0],cut:pool_h[1],toggle:pool_h[2].into()};
    let col_h=c659_column::Column{meta:&meta_h,roles:roles_h,ring:&ring_h,q:&q_h,phase:phase_h,
        compact:Some(&compact_h),dirty:&compact_h,clean_external:&[]};
    c659_fixed::run(&mut h,&col_h,cp);h.flush_global();
    assert!(!h.ops.iter().any(|op|touches(op,pool_h[2])),"c1 host tape names evicted toggle");
    let first=old.iter().zip(&h.ops).position(|(a,b)|a!=b);
    eprintln!("F4_C1_HOST_TAPE old_ops={} new_ops={} first_diff={first:?}",old.len(),h.ops.len());
    assert_eq!(old,h.ops,"c1 host fixed tape must be a lane renaming");
}

#[test]
fn f3_w3b_two_role_tape_equal_all_direct_columns(){
    use crate::point_add::{frogdrop_sched,pointadd_frogdrop,direct_payload::Context};
    crate::point_add::bake_knobs();
    use crate::point_add::builder::G;
    std::env::set_var("C658_WP3","1");
    std::env::set_var("C658_WP3_DS","1");
    std::env::set_var("C658_WP3_ZH","1");
    std::env::set_var("C658_WP3_ZH_GATHER","1");
    std::env::set_var("C658_WP4","1");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut calls=0;
    for cp in &cps {
        let fixed=(!cp.hr||cp.tt)&&cp.sy.1<=96&&!(cp.sw||cp.psw||cp.dl||cp.dq);
        if fixed&&cp.col<139 {continue;}
        for ht in [false,true]{
            if if ht{!cp.ht}else{!cp.hr}{continue;}
            let tape=|two:bool|->Vec<G>{
                let (mut b,ring,compact,q,y,sum,phase,pool)=static_layout();
                let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
                let ctx=Context{meta:&meta,compact:&compact,ring:&ring,q:&q,phase};
                let boundary=if ht{super::EntryBoundary::HtBeforeStage5Arithmetic}
                    else{super::EntryBoundary::HrAfterControllerLeave};
                b.begin();
                if two{
                    super::digit_at_boundary2(&mut b,&ctx,
                        super::Roles2{activity:pool[0],flight:pool[1]},cp,boundary,&compact,&[]);
                }else{
                    super::digit_at_boundary3(&mut b,&ctx,
                        super::Roles3{activity:pool[0],flight:pool[1],sign:pool[2]},
                        cp,boundary,&compact,&[]);
                }
                b.end()
            };
            let old=tape(false);let new=tape(true);
            assert_eq!(old.len(),new.len(),"W3b tape length c{} ht={ht}",cp.col);
            let first=old.iter().zip(&new).position(|(a,b)|a!=b);
            assert!(first.is_none(),"W3b tape difference c{} ht={ht} index={first:?}",cp.col);
            calls+=1;
        }
        if cp.col%20==0 {eprintln!("F3_W3B_PROGRESS col={} calls={calls}",cp.col);}
    }
    eprintln!("F3_W3B_PASS calls={calls} tape_identical=true");
}

#[test]
fn f4_c1_source_all_wire_and_pair(){
    use crate::point_add::{c659,frogdrop_col,frogdrop_sched,k1_complete_caller,
        k1_complete_io as io,k5_ph_ports,pointadd_frogdrop};
    crate::point_add::bake_knobs();
    std::env::set_var("R14_DIG_FIXTURE_RECIPE_CAP","1");
    std::env::set_var("C658_T23","1");
    std::env::set_var("C658_WP3","1");
    std::env::set_var("C658_WP3_DS","1");
    std::env::set_var("C658_WP3_ZH","1");
    std::env::set_var("C658_WP3_ZH_GATHER","1");
    std::env::set_var("C658_WP4","1");
    k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let (cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for payload_first in [true,false]{
        let mut source=k1_complete_caller::builder();
        let layout=k1_complete_caller::Layout::allocate(&mut source);
        let input=k1_complete_caller::initial(&layout,payload_first,0);
        let seed=if payload_first{b"r14-dig-c1-T1".as_slice()}else{b"r14-dig-c1-T3".as_slice()};
        let scope=io::begin(input,seed,io::PRODUCER_OP_CAP);
        source.x(layout.fd.ring[256]);drop(source);drop(layout);
        let cp0=&cps[0];
        let (mut b,ring,compact,q,y,sum,phase,pool)=static_layout();
        let mut fd=frogdrop_col::Fd{ring,q:q.clone(),sy:y.clone(),sx:sum.clone(),
            ph:phase,cnt:q[121..128].to_vec()};
        frogdrop_col::set_counter_epoch(&mut fd,0);
        std::env::set_var("C658_WP4_C1","0");
        b.r14_pass=if payload_first{1}else{3};
        b.r14_roles=[compact[0],compact[1],pool[2]];
        c659::pair_column_for_fixture(&mut b,&fd,cp0,&pool,&compact,
            if payload_first{k5_ph_ports::Traversal::T1}else{k5_ph_ports::Traversal::T3});
        b.r14_pass=0;b.flush_global();assert!(b.ops.is_empty());
        let(image,receipt)=io::finish(scope);
        let mut input=image.q[..659].to_vec();
        // The inherited T23 pair harness clears the two terminal loans
        // before comparing a payload and a no-payload traversal.
        input[compact[0].0 as usize]=0;input[compact[1].0 as usize]=0;
        eprintln!("F4_C1_SOURCE_BITS payload_first={payload_first} nonzero={}",
            image.bits.iter().filter(|&&v|v!=0).count());
        let mut single=Vec::new();let mut paired=Vec::new();let mut second_tapes=Vec::new();
        for c1 in [false,true]{
            std::env::set_var("C658_WP4_C1",if c1{"1"}else{"0"});
            let mut b=B::new();b.global_cancel=false;
            b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
            let mut ring=b.alloc_n(256);let compact=b.alloc_n(258);
            ring.extend(b.alloc_n(1));let q=b.alloc_n(128);
            let y=b.alloc_n(7);let sx=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
            assert_eq!(b.width(),659);
            let mut fd=frogdrop_col::Fd{ring,q:q.clone(),sy:y,sx,
                ph,cnt:q[121..128].to_vec()};
            frogdrop_col::set_counter_epoch(&mut fd,1);
            let cp=&cps[1];
            let (first,second)=if payload_first{
                (k5_ph_ports::Traversal::T1,k5_ph_ports::Traversal::T2)
            }else{(k5_ph_ports::Traversal::T3,k5_ph_ports::Traversal::T4)};
            b.r14_pass=if payload_first{1}else{3};
            b.r14_roles=[compact[0],compact[1],pool[2]];
            c659::pair_column_for_fixture(&mut b,&fd,cp,&pool,&compact,first);
            b.r14_pass=0;b.flush_global();
            let one=run(&b.ops,659,&|q|*q=input.clone());
            let first_ops=b.ops.len();
            b.r14_pass=if payload_first{2}else{4};
            c659::pair_column_for_fixture(&mut b,&fd,cp,&pool,&compact,second);
            b.r14_pass=0;b.flush_global();
            let mut second_input=one.q.clone();
            second_input[compact[0].0 as usize]=0;
            second_input[compact[1].0 as usize]=0;
            let tail=run(&b.ops[first_ops..],659,&|q|*q=second_input.clone());
            let pair=(one.phase^tail.phase,tail.q);
            second_tapes.push(b.ops[first_ops..].to_vec());
            let pool2_first=b.ops[..first_ops].iter().filter(|op|touches(op,pool[2])).count();
            let pool2_pair=b.ops.iter().filter(|op|touches(op,pool[2])).count();
            eprintln!("F4_C1_POOL2 payload_first={payload_first} c1={c1} first={pool2_first} pair={pool2_pair}");
            single.push((one.phase,one.q));paired.push(pair);
            eprintln!("F4_C1_TRACE payload_first={payload_first} c1={c1} source_ops={} first_ops={first_ops} pair_ops={}",receipt.ops,b.ops.len());
        }
        if payload_first {assert_eq!(single[0],single[1],"F4-C1 g2 T1 all-wire");}
        let second_diff=second_tapes[0].iter().zip(&second_tapes[1]).position(|(a,b)|a!=b);
        eprintln!("F4_C1_SECOND_TAPE payload_first={payload_first} diff={second_diff:?} old_len={} new_len={}",
            second_tapes[0].len(),second_tapes[1].len());
        let first_diff=(0..659).find(|&i|paired[0].1[i]!=paired[1].1[i]);
        if let Some(i)=first_diff{let mask=paired[0].1[i]^paired[1].1[i];
            eprintln!("F4_C1_PAIR_DIFF payload_first={payload_first} wire={i} shot={} old={} new={} phase_old={:016x} phase_new={:016x}",
                mask.trailing_zeros(),paired[0].1[i],paired[1].1[i],paired[0].0,paired[1].0);}
        let payload=compact[0].0 as usize..=compact[257].0 as usize;
        let bad=(0..659).filter(|&i|!payload.contains(&i))
            .fold(0u64,|acc,i|acc|(paired[1].1[i]^input[i]));
        eprintln!("F4_C1_PAIR_RESULT payload_first={payload_first} base_phase={:016x} new_phase={:016x} new_nonpayload_bad={bad:016x}",paired[0].0,paired[1].0);
        assert_eq!(bad,0,"F4-C1 g3 nonpayload pair={payload_first}");
        assert_eq!(paired[1].0,0,"F4-C1 g3 phase pair={payload_first}");
    }
    std::env::remove_var("R14_DIG_FIXTURE_RECIPE_CAP");
    eprintln!("F4_C1_PASS g2_g3_g4 source_state=true");
}

#[test]
fn f4_c1_native_column_pair(){
    use crate::point_add::{c659,frogdrop_col,frogdrop_sched,k1_complete_caller,
        k1_complete_io as io,k5_ph_ports,pointadd_frogdrop};
    crate::point_add::bake_knobs();
    std::env::set_var("R14_DIG_FIXTURE_RECIPE_CAP","1");
    std::env::set_var("C658_T23","1");
    std::env::set_var("C658_WP3","1");
    std::env::set_var("C658_WP3_DS","1");
    std::env::set_var("C658_WP3_ZH","1");
    std::env::set_var("C658_WP3_ZH_GATHER","1");
    std::env::set_var("C658_WP4","1");
    k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    for payload_first in [true]{
        let mut source=k1_complete_caller::builder();
        let layout=k1_complete_caller::Layout::allocate(&mut source);
        let input=k1_complete_caller::initial(&layout,payload_first,0);
        let seed=if payload_first{b"r14-c1-native-T1".as_slice()}else{b"r14-c1-native-T3".as_slice()};
        let scope=io::begin(input,seed,io::PRODUCER_OP_CAP);
        source.x(layout.fd.ring[256]);drop(source);drop(layout);
        let (mut b,ring,compact,q,y,sum,phase,pool)=static_layout();
        let mut fd=frogdrop_col::Fd{ring,q:q.clone(),sy:y,sx:sum,
            ph:phase,cnt:q[121..128].to_vec()};
        frogdrop_col::set_counter_epoch(&mut fd,0);
        std::env::set_var("C658_WP4_C1","0");
        b.r14_pass=if payload_first{1}else{3};
        b.r14_roles=[compact[0],compact[1],pool[2]];
        c659::pair_column_for_fixture(&mut b,&fd,&cps[0],&pool,&compact,
            if payload_first{k5_ph_ports::Traversal::T1}else{k5_ph_ports::Traversal::T3});
        b.r14_pass=0;b.flush_global();
        let(mut source_image,_)=io::finish(scope);
        source_image.q[compact[0].0 as usize]=0;
        source_image.q[compact[1].0 as usize]=0;
        for c1 in [false,true]{
            std::env::set_var("C658_WP4_C1",if c1{"1"}else{"0"});
            let mut image=source_image.clone();
            let (first,second)=if payload_first{
                (k5_ph_ports::Traversal::T1,k5_ph_ports::Traversal::T2)
            }else{(k5_ph_ports::Traversal::T3,k5_ph_ports::Traversal::T4)};
            for (step,pass) in [first,second].into_iter().enumerate(){
                let mut b=B::new();b.global_cancel=false;
                b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
                let mut ring=b.alloc_n(256);let compact=b.alloc_n(258);
                ring.extend(b.alloc_n(1));let q=b.alloc_n(128);
                let y=b.alloc_n(7);let sx=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
                let mut fd=frogdrop_col::Fd{ring,q:q.clone(),sy:y,sx,
                    ph,cnt:q[121..128].to_vec()};
                frogdrop_col::set_counter_epoch(&mut fd,1);
                let seed=[u8::from(payload_first),step as u8,1,0];
                let scope=io::begin(image,&seed,io::RECORD_OP_CAP);
                b.r14_pass=if step==0{if payload_first{1}else{3}}
                    else if payload_first{2}else{4};
                b.r14_roles=[compact[0],compact[1],pool[2]];
                c659::pair_column_for_fixture(&mut b,&fd,&cps[1],&pool,&compact,pass);
                b.r14_pass=0;b.flush_global();
                let(next,receipt)=io::finish(scope);image=next;
                if step==0{
                    image.q[compact[0].0 as usize]=0;
                    image.q[compact[1].0 as usize]=0;
                }
                eprintln!("F4_C1_NATIVE_STEP payload_first={payload_first} c1={c1} step={step} ops={} phase={:016x}",receipt.ops,image.phase);
            }
            let mut bad=0u64;
            for i in 0..659{if !(256..514).contains(&i){bad|=image.q[i]^source_image.q[i];}}
            eprintln!("F4_C1_NATIVE_PAIR payload_first={payload_first} c1={c1} bad={bad:016x} phase_diff={:016x}",image.phase^source_image.phase);
            assert_eq!(bad,0,"F4-C1 native g3 nonpayload");
            assert_eq!(image.phase,source_image.phase,"F4-C1 native g3 phase");
            let reverse_start=image.clone();
            for (step,pass) in [k5_ph_ports::Traversal::T3,k5_ph_ports::Traversal::T4]
                .into_iter().enumerate(){
                let mut b=B::new();b.global_cancel=false;
                b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
                let mut ring=b.alloc_n(256);let compact=b.alloc_n(258);
                ring.extend(b.alloc_n(1));let q=b.alloc_n(128);
                let y=b.alloc_n(7);let sx=b.alloc_n(5);let ph=b.alloc();let pool=b.alloc_n(3);
                let mut fd=frogdrop_col::Fd{ring,q:q.clone(),sy:y,sx,
                    ph,cnt:q[121..128].to_vec()};
                frogdrop_col::set_counter_epoch(&mut fd,1);
                let seed=[3u8,step as u8,1,0];
                let scope=io::begin(image,&seed,io::RECORD_OP_CAP);
                b.r14_pass=if step==0{3}else{4};
                b.r14_roles=[compact[0],compact[1],pool[2]];
                c659::pair_column_for_fixture(&mut b,&fd,&cps[1],&pool,&compact,pass);
                b.r14_pass=0;b.flush_global();
                let(next,receipt)=io::finish(scope);image=next;
                if step==0{
                    image.q[compact[0].0 as usize]=0;
                    image.q[compact[1].0 as usize]=0;
                }
                eprintln!("F4_C1_NATIVE_REVERSE_STEP c1={c1} step={step} ops={} phase={:016x}",receipt.ops,image.phase);
            }
            let mut reverse_bad=0u64;
            for i in 0..659{if !(256..514).contains(&i){reverse_bad|=image.q[i]^reverse_start.q[i];}}
            eprintln!("F4_C1_NATIVE_REVERSE_PAIR c1={c1} bad={reverse_bad:016x} phase_diff={:016x}",image.phase^reverse_start.phase);
            assert_eq!(reverse_bad,0,"F4-C1 native T3/T4 nonpayload");
            assert_eq!(image.phase,reverse_start.phase,"F4-C1 native T3/T4 phase");
        }
    }
    std::env::remove_var("R14_DIG_FIXTURE_RECIPE_CAP");
}

#[test]
fn f4_c1_full_source_diagnose(){
    use crate::point_add::{c659,frogdrop_col,frogdrop_sched,k1_complete_caller,
        k1_complete_io as io,k5_ph_ports,pointadd_frogdrop};
    crate::point_add::bake_knobs();
    std::env::set_var("C658_DROP","0");
    std::env::set_var("C658_WP4_C1","0");
    std::env::set_var("R14_DIG_FIXTURE_RECIPE_CAP","1");
    k1_complete_caller::frozen_environment();
    let input={
        let mut b=k1_complete_caller::builder();
        let layout=k1_complete_caller::Layout::allocate(&mut b);
        k1_complete_caller::initial(&layout,true,0)
    };
    let mut source=k1_complete_caller::builder();
    let scope=io::begin(input,b"r14-c1-full-source",io::PRODUCER_OP_CAP);
    std::env::set_var("R14_C1_CAPTURE_SOURCE","1");
    let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||{
        pointadd_frogdrop::point_add_pl(&mut source)
    }));
    std::env::remove_var("R14_C1_CAPTURE_SOURCE");
    drop(scope);
    assert!(result.is_err(),"source must stop at c1 T4");
    let captures=c659::c1_take_source();
    assert_eq!(captures.len(),4,"source c1 capture count");
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let cp=&cps[1];
    let mut bad_count=0;
    for(pass,image)in captures{
        let mut outputs=Vec::new();
        for variant in 0..3 {
            std::env::set_var("C658_WP4_C1",if variant==0{"0"}else{"1"});
            if variant==1{std::env::set_var("R14_C1_BAD_FORM","1");}
            else{std::env::remove_var("R14_C1_BAD_FORM");}
            let (mut b,ring,compact,q,y,sum,phase,pool)=static_layout();
            b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
            let mut fd=frogdrop_col::Fd{ring,q:q.clone(),sy:y,sx:sum,
                ph:phase,cnt:q[121..128].to_vec()};
            frogdrop_col::set_counter_epoch(&mut fd,1);
            let seed=[pass as u8,1,0,0];
            let replay=io::begin(image.clone(),&seed,io::RECORD_OP_CAP);
            b.r14_pass=match pass{k5_ph_ports::Traversal::T1=>1,
                k5_ph_ports::Traversal::T2=>2,k5_ph_ports::Traversal::T3=>3,
                k5_ph_ports::Traversal::T4=>4};
            b.r14_roles=[compact[0],compact[1],pool[2]];
            c659::pair_column_for_fixture(&mut b,&fd,cp,&pool,&compact,pass);
            b.r14_pass=0;b.flush_global();
            let(out,receipt)=io::finish(replay);
            eprintln!("C1_DIAG pass={pass:?} variant={variant} ops={} phase={:016x}",receipt.ops,out.phase);
            outputs.push(out);
        }
        for variant in [1,2] {
            let old=&outputs[0];let new=&outputs[variant];
            let first_q=(0..old.q.len()).find(|&j|old.q[j]!=new.q[j]);
            let first_bit=(0..old.bits.len()).find(|&j|old.bits[j]!=new.bits[j]);
            let first_mask=first_q.map(|j|old.q[j]^new.q[j]).unwrap_or(0);
            let bit_mask=first_bit.map(|j|old.bits[j]^new.bits[j]).unwrap_or(0);
            let phase=old.phase^new.phase;
            eprintln!("C1_DIFF pass={pass:?} variant={variant} first_q={first_q:?} qmask={first_mask:016x} first_bit={first_bit:?} bitmask={bit_mask:016x} phase={phase:016x}");
            if variant==1&&(first_q.is_some()||first_bit.is_some()||phase!=0){bad_count+=1;}
            if variant==2 {
                assert!(first_q.is_none()&&first_bit.is_none()&&phase==0,
                    "c1 fixed host differs from inherited fixed on source state");
            }
        }
    }
    assert!(bad_count>0,"source did not witness the all-four c1 failure");
    eprintln!("C1_DIAG_PASS bad_traversals={bad_count} host_exact_on_source=true");
}

#[test]
fn f3_ht_digit_source_entry_all_shots(){
    use crate::circuit::OperationType;
    use crate::point_add::{c659,frogdrop_col,frogdrop_sched,k1_complete_caller,
        k1_complete_io as io,k5_ph_ports,pointadd_frogdrop};
    use crate::point_add::direct_payload::Context;
    crate::point_add::bake_knobs();
    std::env::set_var("R14_DIG_FIXTURE_RECIPE_CAP","1");
    for gate in ["C658_T23","C658_WP3","C658_WP3_DS","C658_WP3_ZH",
        "C658_WP3_ZH_GATHER","C658_WP4","C658_WP4_C1"]{
        std::env::set_var(gate,"1");
    }
    k1_complete_caller::frozen_environment();
    let schedule=frogdrop_sched::from_text(pointadd_frogdrop::SCHED_FROGDROP);
    let(cps,_,_)=pointadd_frogdrop::col_pars(&schedule);
    let mut source=k1_complete_caller::builder();
    let layout=k1_complete_caller::Layout::allocate(&mut source);
    let mut image=k1_complete_caller::initial(&layout,true,0);
    image.q[layout.fd.ring[256].0 as usize]^=u64::MAX;
    drop(source);drop(layout);
    let hr_mode=std::env::var("R14_DIG_HR_SELECTED").as_deref()==Ok("1");
    for cp in cps.iter().take(if hr_mode{113}else{203}){
        let target=if hr_mode{cp.hr&&[37,85,112].contains(&cp.col)}
            else{cp.ht&&(std::env::var("R14_DIG_HT_SELECTED").as_deref()!=Ok("1")
                ||[37,50,85,96,97,110,113,126,139,146,202].contains(&cp.col))};
        if target{
            std::env::set_var("R14_DIG_MARK_COL",cp.col.to_string());
            std::env::set_var("R14_DIG_MARK_HT",if hr_mode{"0"}else{"1"});
        }
        let (mut b,ring,compact,q,y,sum,phase,pool)=static_layout();
        let mut fd=frogdrop_col::Fd{ring,q:q.clone(),sy:y.clone(),sx:sum.clone(),
            ph:phase,cnt:q[121..128].to_vec()};
        frogdrop_col::set_counter_epoch(&mut fd,cp.col);
        b.r14_pass=1;b.r14_roles=[compact[0],compact[1],pool[2]];
        c659::pair_column_for_fixture(&mut b,&fd,cp,&pool,&compact,k5_ph_ports::Traversal::T1);
        b.r14_pass=0;b.flush_global();
        std::env::remove_var("R14_DIG_MARK_COL");
        std::env::remove_var("R14_DIG_MARK_HT");
        if target{
            let mark=b.ops.windows(4).position(|w|
                w.iter().all(|op|op.kind==OperationType::X)
                &&[w[0].q_target,w[1].q_target,w[2].q_target,w[3].q_target]
                    ==[phase,pool[0],phase,pool[0]])
                .expect("F3 source digit boundary marker absent");
            let scope=io::begin(image.clone(),b"r14-dig-digit-entry",io::RECORD_OP_CAP);
            for op in &b.ops[..mark]{assert!(io::observe_op(op));}
            let(entry,receipt)=io::finish(scope);
            assert_eq!(entry.q[pool[2].0 as usize],0,"source digit sign entry");
            assert_eq!(entry.q[pool[1].0 as usize],0,"source digit flight entry");
            eprintln!("F3_SOURCE_ENTRY col={} hr={} activity_shots={} phase={:016x}",
                cp.col,hr_mode,entry.q[pool[0].0 as usize].count_ones(),entry.phase);
            let digit_tape=|wp3:bool|{
                let (mut d,ring,compact,q,y,sum,phase,pool)=static_layout();
                let meta=SumSize{y:y.as_slice().try_into().unwrap(),sum:sum.as_slice().try_into().unwrap()};
                let ctx=Context{meta:&meta,compact:&compact,ring:&ring,q:&q,phase};
                let roles=super::Roles3{activity:pool[0],flight:pool[1],sign:pool[2]};
                let dirty:Vec<_>=if hr_mode{compact.iter().chain(&ring).chain(&q).copied().collect()}
                    else{compact.clone()};
                std::env::set_var("C658_WP3",if wp3{"1"}else{"0"});
                d.begin();super::digit_at_boundary3(&mut d,&ctx,roles,cp,
                    if hr_mode{super::EntryBoundary::HrAfterControllerLeave}
                        else{super::EntryBoundary::HtBeforeStage5Arithmetic},&dirty,&[]);
                let tape=d.end();d.play(&tape,false);d.flush_global();d.ops
            };
            let old=digit_tape(false);let new=digit_tape(true);
            std::env::set_var("C658_WP3","1");
            let replay=|ops:&[crate::circuit::Op]|{
                let scope=io::begin(entry.clone(),b"r14-dig-digit-compare",io::RECORD_OP_CAP);
                for op in ops{assert!(io::observe_op(op));}
                io::finish(scope).0
            };
            let prior=replay(&old);let next=replay(&new);
            let first=(0..659).find(|&i|prior.q[i]!=next.q[i]);
            let clean=!(prior.q[pool[2].0 as usize]|prior.q[pool[1].0 as usize]
                |(prior.phase^entry.phase));
            eprintln!("F3_SOURCE col={} hr={} prefix_ops={} digit_old={} digit_new={} clean={} first_diff={first:?} phase_diff={:016x}",
                cp.col,hr_mode,receipt.ops,old.len(),new.len(),clean.count_ones(),prior.phase^next.phase);
            assert!(first.is_none(),"F3 source all-wire c{} hr={hr_mode} first={first:?}",cp.col);
            assert_eq!(prior.phase,next.phase,"F3 source phase c{} hr={hr_mode}",cp.col);
            if hr_mode{
                let mut lead_zero=0u64;
                for shot in 0..64{
                    let bit=1u64<<shot;
                    let ee=y.iter().enumerate().fold(0usize,|v,(i,&lane)|v+(((entry.q[lane.0 as usize]&bit!=0)as usize)<<i));
                    let s=sum.iter().enumerate().fold(0usize,|v,(i,&lane)|v+(((entry.q[lane.0 as usize]&bit!=0)as usize)<<i));
                    let zz=225+s-ee;
                    if zz>0&&zz<=257&&entry.q[fd.ring[zz-1].0 as usize]&bit==0{lead_zero|=bit;}
                }
                eprintln!("F3_HR_VIRTUAL_TOP col={} zero_shots={} active_zero_shots={}",
                    cp.col,lead_zero.count_ones(),
                    (lead_zero&entry.q[pool[0].0 as usize]).count_ones());
                if cp.col==85{
                    std::env::set_var("R14_DIG_MUT_C2_OFF","1");
                    let no_c2=digit_tape(true);
                    std::env::remove_var("R14_DIG_MUT_C2_OFF");
                    let wrong=replay(&no_c2);
                    let mutant_bad=next.q.iter().zip(&wrong.q)
                        .fold(next.phase^wrong.phase,|m,(x,y)|m|(x^y));
                    eprintln!("F3_HR_C85_C2_SOURCE mutant_bad={mutant_bad:016x} active_zero={:016x}",
                        lead_zero&entry.q[pool[0].0 as usize]);
                }
            }
            if !hr_mode&&[37,85,97,139,146,202].contains(&cp.col){
                std::env::set_var("R14_DIG_TRACE_STOP","read1");
                let prefix=digit_tape(true);
                std::env::remove_var("R14_DIG_TRACE_STOP");
                let mid=replay(&prefix);
                eprintln!("F3_HT_SIGN_READ1 col={} sign1_shots={} activity={} prefix_ops={}",
                    cp.col,mid.q[pool[1].0 as usize].count_ones(),
                    mid.q[pool[0].0 as usize].count_ones(),prefix.len());
            }
            if !hr_mode&&[37,50,85,96,97,110,113,126,139,146,202].contains(&cp.col){
                let mut start=image.clone();
                start.q[compact[0].0 as usize]=0;
                start.q[compact[1].0 as usize]=0;
                let mut paired=native_c659_column(start.clone(),cp,
                    k5_ph_ports::Traversal::T1,b"r14-g3-T1");
                paired.q[compact[0].0 as usize]=0;
                paired.q[compact[1].0 as usize]=0;
                paired=native_c659_column(paired,cp,
                    k5_ph_ports::Traversal::T2,b"r14-g3-T2");
                let mut bad=0u64;
                for i in 0..659{if !(256..514).contains(&i){bad|=paired.q[i]^start.q[i];}}
                eprintln!("F3_G3_SOURCE col={} pair=T1T2 bad={bad:016x} phase_diff={:016x}",
                    cp.col,paired.phase^start.phase);
                assert_eq!(bad,0,"F3 g3 T1/T2 nonpayload c{}",cp.col);
                assert_eq!(paired.phase,start.phase,"F3 g3 T1/T2 phase c{}",cp.col);
                let reverse_start=paired.clone();
                paired=native_c659_column(paired,cp,
                    k5_ph_ports::Traversal::T3,b"r14-g3-T3");
                paired.q[compact[0].0 as usize]=0;
                paired.q[compact[1].0 as usize]=0;
                paired=native_c659_column(paired,cp,
                    k5_ph_ports::Traversal::T4,b"r14-g3-T4");
                let mut reverse_bad=0u64;
                for i in 0..659{if !(256..514).contains(&i){reverse_bad|=paired.q[i]^reverse_start.q[i];}}
                eprintln!("F3_G3_SOURCE col={} pair=T3T4 bad={reverse_bad:016x} phase_diff={:016x}",
                    cp.col,paired.phase^reverse_start.phase);
                assert_eq!(reverse_bad,0,"F3 g3 T3/T4 nonpayload c{}",cp.col);
                assert_eq!(paired.phase,reverse_start.phase,"F3 g3 T3/T4 phase c{}",cp.col);
            }
        }
        let seed=(cp.col as u64).to_le_bytes();
        let scope=io::begin(image,&seed,io::RECORD_OP_CAP);
        for op in &b.ops{assert!(io::observe_op(op));}
        let(next,_)=io::finish(scope);image=next;
        if cp.col%20==0{eprintln!("F3_HT_SOURCE_PROGRESS col={}",cp.col);}
    }
    std::env::remove_var("R14_DIG_FIXTURE_RECIPE_CAP");
    eprintln!("F3_SOURCE_ALL_SHOTS_PASS hr={hr_mode} shots=64");
}
