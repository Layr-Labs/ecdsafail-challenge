//! One future native test. Source preparation does not execute this harness.
//! Fixtures are local ABI probes; no complete traversal reachability is claimed.
use super::*;
use super::super::{cross_four::Roles, sum_size::SumSize, normalized_cross_controller::Controller};
use crate::circuit::{Op as NativeOp, OperationType as K, NO_BIT};
use crate::sim::Simulator;
use sha3::{Digest, digest::{ExtendableOutput, Update}};

const BIT:usize=13;
const BATCHES:usize=160; // exactly 10,240 shots per named sector/profile
const SEED:u64=0x4b335f54544b_2026;
const SECTORS:[&str;6]=["acted_e0","skipped_a1_e0","inactive_passed_dirty_e",
    "inactive_skipped_e0","flight_image_skipped","acted_e1"];
fn rng(s:&mut u64)->u64 { *s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s }
fn put(w:&mut[u64],q:QubitId,k:usize,v:bool) {
    let mask=1u64<<k;if v { w[q.0 as usize]|=mask; } else { w[q.0 as usize]&=!mask; }
}
fn word(w:&mut[u64],q:&[QubitId],k:usize,v:usize) {
    for (i,&q) in q.iter().enumerate() { put(w,q,k,(v>>i)&1!=0); }
}
fn emit(b:&mut B,tape:&[G],inverse:bool)->Vec<NativeOp> {
    b.ops.clear();b.tof=0;b.global_cancel=false;b.play(tape,inverse);b.flush_global();
    assert!(b.c162_audit.is_empty()); b.ops.clone()
}
fn pure(ops:&[NativeOp]) {
    for op in ops { assert!(matches!(op.kind,K::X|K::CX|K::CCX));assert_eq!(op.c_condition,NO_BIT); }
}
fn fingerprint(ops:&[NativeOp])->String {
    let mut h=sha3::Keccak256::new();
    for o in ops { Digest::update(&mut h,(o.kind as u32).to_le_bytes());
        for v in [o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0] {
            Digest::update(&mut h,v.to_le_bytes());
        }
    } format!("{:x}",h.finalize())
}
fn count(ops:&[NativeOp])->(usize,usize) { (ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len()) }
fn play(ops:&[NativeOp],w:&[u64],sign:u64)->(Vec<u64>,u64) {
    let mut h=sha3::Shake256::default();Update::update(&mut h,b"k3-signed-native-fixed-v1");
    let mut xof=h.finalize_xof();let mut sim=Simulator::new(w.len(),10002,&mut xof);
    sim.qubits.clone_from_slice(w);sim.phase=sign;sim.apply_iter(ops.iter());(sim.qubits,sim.phase)
}
fn compare(ops:&[NativeOp],input:&[u64],expected:&[u64],sign:u64,label:&str) {
    let (out,phase)=play(ops,input,sign);
    assert_eq!(phase,sign,"signed phase {label}");
    assert_eq!(out,expected,"all wires {label}");
}
fn difference(a:&[u64],b:&[u64])->u64 { a.iter().zip(b).fold(0,|m,(a,b)|m|(a^b)) }
fn uses(op:&NativeOp,q:QubitId)->bool { [op.q_control1,op.q_control2,op.q_target].contains(&q) }

/// Independent binary subtraction oracle. It does not transcribe either carry
/// ladder. Compute a full (n+1)-bit t-q difference and borrow, decide e XOR ge,
/// then select subtraction; wrap it in the Boolean witness and optional close.
/// Inputs require mask=0 and the parent carry=0 on NARROWED activity.
fn arithmetic_oracle(w:&[u64],q:&[QubitId],t:&[QubitId],a:QubitId,e:QubitId,
                     passed:u64,inplace:bool)->Vec<u64> {
    assert_eq!(t.len(),q.len()+1);let mut out=w.to_vec();let(a,e)=(a.0 as usize,e.0 as usize);
    let delta=out[a]&!passed;out[e]^=delta;let delta=out[e]&!passed;out[a]^=delta;
    let mut borrow=0u64;let mut difference=Vec::with_capacity(t.len());
    for i in 0..t.len() {
        let x=out[t[i].0 as usize];let y=if i<q.len(){out[q[i].0 as usize]}else{0};
        difference.push(x^y^borrow);borrow=(!x&(y|borrow))|(y&borrow);
    }
    let decision=out[a]&!borrow;out[e]^=decision;let enabled=out[a]&out[e];
    for (i,&q) in t.iter().enumerate() { let x=&mut out[q.0 as usize];*x^=(*x^difference[i])&enabled; }
    if inplace { let top=t[q.len()].0 as usize;let delta=(out[top]^out[e])&out[a];out[top]^=delta;out[e]^=delta; }
    let delta=out[e]&!passed;out[a]^=delta;let delta=out[a]&!passed;out[e]^=delta;out
}

// Width-generic frozen Cuccaro ladder, retaining the parent's exact gate order.
// The full-record reference below instead calls the preserved parent function.
fn small_cuccaro(b:&mut B,t:&[QubitId],q:&[QubitId],carry:QubitId,a:QubitId,e:QubitId,m:QubitId,d:&[QubitId]) {
    let n=q.len();assert_eq!(t.len(),n+1);
    for i in 0..n { cell(b,q[i],t[i],if i==0{carry}else{q[i-1]},false); }
    normal_decision(b,a,e,t[n],q[n-1],d);b.ccx(a,e,m);b.ccx(m,q[n-1],t[n]);
    for i in (0..n).rev() { let x=if i==0{carry}else{q[i-1]};cell(b,q[i],t[i],x,true);
        b.cx(q[i],x);b.ccx(m,x,t[i]);b.cx(q[i],x);
    } b.ccx(a,e,m);
}
fn small_exhaustive()->usize {
    let mut total=0;let mut sign_seed=SEED;
    for n in 2..=6 {
        let mut b=B::new();b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let q=b.alloc_n(n);let t=b.alloc_n(n+1);let a=b.alloc();let e=b.alloc();let m=b.alloc();
        let carry=b.alloc();let dirty=b.alloc_n(2);let width=b.width()as usize;
        let mut tapes=Vec::new();
        for candidate in [false,true] { b.begin();for &t in &t { b.x(t); }
            if candidate { ttk_natural(&mut b,&t,&q,a,e,m,&dirty); }
            else { small_cuccaro(&mut b,&t,&q,carry,a,e,m,&dirty); }
            for &t in &t { b.x(t); }tapes.push(b.end());
        }
        let pf=emit(&mut b,&tapes[0],false);let pi=emit(&mut b,&tapes[0],true);
        let cf=emit(&mut b,&tapes[1],false);let ci=emit(&mut b,&tapes[1],true);
        pure(&pf);pure(&cf);pure(&pi);pure(&ci);
        assert_eq!(count(&pf),(3*n+7,11*n+10));assert_eq!(count(&cf),(3*n+10,9*n+11));
        assert!(!cf.iter().any(|o|uses(o,carry)));
        let mut batch=vec![0u64;width];let mut shot=0;let mut cases=0;
        for av in 0..2 { for ev in 0..2 { for cv in 0..if av==0{2}else{1} {
            let qlo=if av==0{0}else{1usize<<(n-1)};
            for qv in qlo..(1usize<<n) { for tv in 0..(1usize<<(n+1)) { for dv in 0..4 {
                word(&mut batch,&q,shot,qv);word(&mut batch,&t,shot,tv);word(&mut batch,&dirty,shot,dv);
                put(&mut batch,a,shot,av!=0);put(&mut batch,e,shot,ev!=0);put(&mut batch,carry,shot,cv!=0);
                cases+=1;shot+=1;
                if shot==64 {
                    let expected=arithmetic_oracle(&batch,&q,&t,a,e,u64::MAX,false);let sign=rng(&mut sign_seed);
                    compare(&pf,&batch,&expected,sign,"small parent forward independent arithmetic");
                    compare(&cf,&batch,&expected,sign,"small K3 forward independent arithmetic");
                    compare(&pi,&expected,&batch,sign,"small parent inverse independent image");
                    compare(&ci,&expected,&batch,sign,"small K3 inverse independent image");
                    batch.fill(0);shot=0;
                }
            } } }
        } } }
        assert_eq!(shot,0);assert_eq!(cases,5*(1usize<<(2*n+3)));total+=cases;
        println!("K3_SMALL n={n} cases={cases} directions=2 T_parent={} N_parent={} T_ttk={} N_ttk={} signed=true dirty_exhaustive=true",count(&pf).0,count(&pf).1,count(&cf).0,count(&cf).1);
    }
    assert_eq!(total,218240);total
}

struct Rig { b:B,ring:Vec<QubitId>,q:Vec<QubitId>,p:Vec<QubitId>,meta:SumSize,ph:QubitId,r:Roles }
impl Rig {
    fn new()->Self {
        let mut b=B::new();let ring=b.alloc_n(257);let q=b.alloc_n(128);let p=b.alloc_n(258);
        let meta=SumSize{y:b.alloc_n(7).try_into().unwrap(),sum:b.alloc_n(5).try_into().unwrap()};
        let ph=b.alloc();let r=Roles{activity:b.alloc(),flight:b.alloc(),mask:b.alloc(),x128:b.alloc()};
        assert_eq!(b.width(),660);assert_eq!(r.x128.0,659);Self{b,ring,q,p,meta,ph,r}
    }
    fn target(&self)->Vec<QubitId> { (0..129).map(|j|self.ring[256-BIT-j]).collect() }
    fn capture(&mut self,first:usize,site:HrSite,profile:K3Diagnostic,original:bool,optimized:bool)->Vec<G> {
        self.b.cancel_simple_pairs=optimized;self.b.cancel_commuting_pairs=optimized;
        let loans=[self.p[0],self.p[1]];
        let c=Cross{size:&self.meta,ring:&self.ring,q:&self.q,phase:self.ph,roles:self.r,
            dirty:&self.p,y_bounds:(1,128-first),qb:30,
            clean_external:if site==HrSite::NoPayloadTwin{&loans}else{&[]}};
        let t=super::super::normalized_cross_frame::natural_target(&c,BIT);assert_eq!(t,self.target());
        let controller=if profile==K3Diagnostic::Parent { Controller::new(&c,site==HrSite::PayloadTick) }
            else { Controller::new_k3_diagnostic(&c,site==HrSite::PayloadTick) };
        // This is the exact selector called by both production HR sites.
        let d=controller.hr_arithmetic(site);
        let close=if site==HrSite::PayloadTick{Close::None}else{Close::Inplace};
        if original { D::parent(false,true).parent_record(&mut self.b,&c,&t,Gate::Natural(BIT),Op::Divide,close) }
        else { d.record(&mut self.b,&c,&t,Gate::Natural(BIT),Op::Divide,close) }
    }
    fn fixture(&self,first:usize,site:HrSite,sector:usize,batch:usize)->Vec<u64> {
        let mut seed=SEED^((first as u64)<<40)^((sector as u64)<<32)^(batch as u64+1);
        let mut w:Vec<_>=(0..660).map(|_|rng(&mut seed)).collect();
        let passed=matches!(sector,0|2|5);let narrowed=matches!(sector,0|4|5);
        w[self.r.activity.0 as usize]=if matches!(sector,0|1|5){u64::MAX}else{0};
        w[self.r.flight.0 as usize]=match sector {2=>rng(&mut seed),4|5=>u64::MAX,_=>0};
        w[self.r.mask.0 as usize]=0;
        for k in 0..64 {
            let y=if narrowed{1+(rng(&mut seed)as usize%(128-first))}else{1+(rng(&mut seed)as usize%128)};
            let sum=if passed{rng(&mut seed)as usize%(32-BIT)}else{32-BIT+rng(&mut seed)as usize%BIT};
            word(&mut w,&self.meta.y,k,y-1);word(&mut w,&self.meta.sum,k,sum);
            if narrowed {
                for &q in &self.q[..128-y] { put(&mut w,q,k,false); }
                put(&mut w,self.q[127],k,true);put(&mut w,self.r.x128,k,false);
            }
        }
        if site==HrSite::NoPayloadTwin { w[self.p[0].0 as usize]=0;w[self.p[1].0 as usize]=0; }
        w
    }
}

fn selector_controls()->usize {
    // Existing parent operation/prefix choices remain literal and cannot select K3.
    for (ht,unparked) in [(false,false),(false,true),(true,false),(true,true)] {
        assert_eq!(D::parent(ht,unparked).contract.body,ArithmeticBody::ParentCuccaro);
    }
    let mut rig=Rig::new();let t=rig.target();let loans=[rig.p[0],rig.p[1]];
    let c=Cross{size:&rig.meta,ring:&rig.ring,q:&rig.q,phase:rig.ph,roles:rig.r,dirty:&rig.p,
        y_bounds:(1,128),qb:30,clean_external:&loans};
    let mut rejected=0;
    for which in 0..12 {
        let mut d=D::hr(K3Diagnostic::OptionB,HrSite::PayloadTick);
        let mut gate=Gate::Natural(BIT);let mut op=Op::Divide;let mut close=Close::None;
        match which {
            0=>gate=Gate::Top(0),1=>gate=Gate::Bottom(0),2=>gate=Gate::Natural(30),
            3=>op=Op::Add,4=>op=Op::VBit(VTop::Zero),5=>close=Close::Inplace,
            6=>close=Close::EraseInplace(rig.r.x128),7=>d.ht=true,8=>d.payload_open=false,
            9=>d.contract.frame=ArithmeticFrame::Controller129EmptyParks,
            10=>d.contract.carry=CarrySource::ParentDefined,11=>d.contract.source=SourcePolicy::ParentDefined,_=>unreachable!(),
        }
        let result=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||d.record(&mut rig.b,&c,&t,gate,op,close)));
        assert!(result.is_err(),"selector disjointness {which}");rejected+=1;
    }
    assert_eq!(rejected,12);println!("K3_SELECTOR parent_choices=4 rejected_incompatible=12");16
}

#[test]
fn k3_ttk_native_component() {
    // One test, serial execution. No stream writer or implicit alternate knobs.
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());
    assert!(std::env::var_os("LS_NO_BAKE").is_none());
    for key in include_str!("c162_consulted_env.txt").lines() {
        if let Some(value)=std::env::var_os(key) {
            let expected=super::super::BAKED_KNOBS.iter().find(|(k,_)|*k==key).map(|(_,v)|*v);
            assert!(expected.is_some_and(|v|value==std::ffi::OsStr::new(v)),"K3 inherited override key {}",key);
        }
    }
    let mut rig=Rig::new();let mut bound=Vec::new();
    // Freeze ALL baseline/disabled record identities before constructing any K3 tape.
    for optimized in [false,true] { for first in [0,1,13,95] { for site in [HrSite::PayloadTick,HrSite::NoPayloadTwin] {
        let parent=rig.capture(first,site,K3Diagnostic::Parent,true,optimized);
        let disabled=rig.capture(first,site,K3Diagnostic::Parent,false,optimized);
        assert_eq!(parent,disabled,"parent/default record identity");
        for inverse in [false,true] {
            let p=emit(&mut rig.b,&parent,inverse);let d=emit(&mut rig.b,&disabled,inverse);
            assert_eq!(p,d);pure(&p);
            println!("K3_BASELINE first={first} site={site:?} optimized={optimized} inverse={inverse} Q=660 T={} N={} hash={}",count(&p).0,count(&p).1,fingerprint(&p));
        }
        bound.push((optimized,first,site,parent));
    } } }
    let selectors=selector_controls();let small=small_exhaustive();
    let(mut profiles,mut full_rows,mut directional_pairs,mut dropped_detected,mut leading_detected)=(0,0,0,0,0);
    let mut sign_seed=SEED;
    for (optimized,first,site,parent) in bound {
        let candidate=rig.capture(first,site,K3Diagnostic::OptionB,false,optimized);let t=rig.target();
        let pf=emit(&mut rig.b,&parent,false);let pi=emit(&mut rig.b,&parent,true);
        let cf=emit(&mut rig.b,&candidate,false);let ci=emit(&mut rig.b,&candidate,true);pure(&cf);pure(&ci);
        assert!(!cf.iter().chain(&ci).any(|o|uses(o,rig.r.x128)||uses(o,rig.ph)));
        if site==HrSite::NoPayloadTwin {
            assert!(!cf.iter().chain(&ci).any(|o|uses(o,rig.p[0])||uses(o,rig.p[1])));
        }
        if !optimized {
            let n=128-first;let close=usize::from(site==HrSite::NoPayloadTwin);
            // Natural(13)'s uncancelled witness is 56 CCX / 68 operations;
            // forward and inverse guards contribute 112 / 136.
            assert_eq!(count(&pf),(3*n+119+close,9*n+402+3*close));
            assert_eq!(count(&cf),(3*n+122+close,7*n+403+3*close));
        }
        let mut dropped=candidate.clone();let gate=G::Cx(rig.q[126],rig.q[127]);
        let at=dropped.iter().position(|&g|g==gate).expect("S2 top gate must be emitted");
        assert_eq!(dropped.iter().filter(|&&g|g==gate).count(),2,"S2 and S12 exact pair");dropped.remove(at);
        let df=emit(&mut rig.b,&dropped,false);assert_ne!(fingerprint(&df),fingerprint(&cf));
        let(mut drop_bits,mut lead_bits)=(0u64,0u64);
        for sector in 0..SECTORS.len() { for batch in 0..BATCHES {
            let w=rig.fixture(first,site,sector,batch);let passed=if matches!(sector,0|2|5){u64::MAX}else{0};
            let expected=arithmetic_oracle(&w,&rig.q,&t,rig.r.activity,rig.r.flight,passed,site==HrSite::NoPayloadTwin);
            let sign=rng(&mut sign_seed);
            compare(&pf,&w,&expected,sign,"full parent independent arithmetic");
            compare(&cf,&w,&expected,sign,"full K3 independent arithmetic");
            compare(&pi,&expected,&w,sign,"full parent inverse independent image");
            compare(&ci,&expected,&w,sign,"full K3 inverse independent image");
            let (mutant,phase)=play(&df,&w,sign);assert_eq!(phase,sign);drop_bits|=difference(&mutant,&expected);
            if sector==0 && batch<8 {
                let mut broken=w.clone();broken[rig.q[127].0 as usize]=0;
                let (p,pp)=play(&pf,&broken,sign);let (c,cp)=play(&cf,&broken,sign);
                assert_eq!((pp,cp),(sign,sign));lead_bits|=difference(&p,&c);
                // Reserved fourth lane is an arbitrary active spectator for K3.
                let mut dirty=w.clone();dirty[rig.r.x128.0 as usize]=u64::MAX;
                let mut dirty_expected=expected.clone();dirty_expected[rig.r.x128.0 as usize]=u64::MAX;
                compare(&cf,&dirty,&dirty_expected,sign,"active fourth spectator");
            }
            full_rows+=64;directional_pairs+=128;
        }
        println!("K3_SECTOR first={first} site={site:?} optimized={optimized} sector={} rows={} directions=2",SECTORS[sector],64*BATCHES);
        }
        assert_ne!(drop_bits,0,"dropped S2 must dynamically differ");assert_ne!(lead_bits,0,"broken leading one must dynamically differ");
        dropped_detected+=1;leading_detected+=1;
        // Harness falsifiers: phase-only and donor-only corruption must be visible.
        let w=rig.fixture(first,site,0,0);let sign=rng(&mut sign_seed);
        let expected=arithmetic_oracle(&w,&rig.q,&t,rig.r.activity,rig.r.flight,u64::MAX,site==HrSite::NoPayloadTwin);
        let mut phase_bad=candidate.clone();phase_bad.push(G::Cz(rig.r.activity,rig.q[127]));
        let phase_ops=emit(&mut rig.b,&phase_bad,false);let (same,phase)=play(&phase_ops,&w,sign);
        assert_eq!(same,expected);assert_ne!(phase,sign);
        let mut donor_bad=candidate.clone();donor_bad.push(G::X(rig.p[2]));
        let donor_ops=emit(&mut rig.b,&donor_bad,false);let (wrong,phase)=play(&donor_ops,&w,sign);
        assert_eq!(phase,sign);assert_ne!(difference(&wrong,&expected),0);
        println!("K3_PROFILE first={first} site={site:?} optimized={optimized} Q=660 fourth_spectator=659 parent_T={} parent_N={} candidate_T={} candidate_N={} parent_hash={} candidate_hash={} dropped_s2_hash={} dropped_s2_mask={drop_bits:016x} broken_leading_mask={lead_bits:016x} phase_control=true donor_control=true",
            count(&pf).0,count(&pf).1,count(&cf).0,count(&cf).1,fingerprint(&pf),fingerprint(&cf),fingerprint(&df));
        profiles+=1;
    }
    assert_eq!((profiles,full_rows,directional_pairs,dropped_detected,leading_detected),(16,983040,1966080,16,16));
    println!("K3_NATIVE_COMPLETE tests=1 profiles={profiles} small_basis_rows={small} small_directional_pairs={} full_rows={full_rows} full_directional_pairs={directional_pairs} selector_controls={selectors} required_mutant_profiles=32 harness_controls=32 baseline_direction_records=32 Q=660 whole_result=false traversal_image_proven=false submit=CLOSED",2*small);
}
