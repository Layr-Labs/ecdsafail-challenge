//! One future bounded K2 experiment. Source preparation never runs this file.
use super::*;
use super::super::{cross_four::Roles,sum_size::SumSize};
use super::super::normalized_cross_arithmetic::{D,k2_stage5::{Contract,Division,GuardCode,GuardViolation}};
use crate::circuit::{Op as NativeOp,OperationType as K,NO_BIT};
use crate::sim::Simulator;
use sha3::{Digest,digest::{Update,ExtendableOutput}};

const SEED:u64=0x4b325f53355f2026;
const MAX_OPS:usize=1_000_000;
static PLAY_CALLS:std::sync::atomic::AtomicUsize=std::sync::atomic::AtomicUsize::new(0);
const SUMS:[usize;9]=[0,1,2,15,18,19,29,30,31];
#[derive(Clone,Copy,Debug)]
struct Column { id:usize,z:(usize,usize),y:(usize,usize),schedule_z:(usize,usize),schedule_y:(usize,usize) }
const COLUMNS:[Column;4]=[
    Column{id:55,z:(107,207),y:(49,128),schedule_z:(107,207),schedule_y:(49,139)},
    Column{id:94,z:(110,251),y:(5,128),schedule_z:(110,251),schedule_y:(5,140)},
    Column{id:116,z:(129,255),y:(1,126),schedule_z:(129,259),schedule_y:(1,126)},
    Column{id:138,z:(158,255),y:(1,97),schedule_z:(158,259),schedule_y:(1,97)},
];
fn metadata(col:Column)->Vec<(usize,usize)> {
    let mut out=vec![];
    for s in SUMS {
        let lo=col.y.0.max((226+s).saturating_sub(col.z.1));
        let hi=col.y.1.min(226+s-col.z.0);
        assert!(lo<hi);out.push((lo,s));out.push((hi,s));
    }
    assert_eq!(out.len(),18);out
}
fn rng(s:&mut u64)->u64{*s^=*s<<13;*s^=*s>>7;*s^=*s<<17;*s}
fn put(w:&mut[u64],q:QubitId,k:usize,v:bool){let m=1u64<<k;if v{w[q.0 as usize]|=m;}else{w[q.0 as usize]&=!m;}}
fn word(w:&mut[u64],q:&[QubitId],k:usize,v:usize){for(i,&q)in q.iter().enumerate(){put(w,q,k,(v>>i)&1!=0);}}
fn uses(op:&NativeOp,q:QubitId)->bool{[op.q_control1,op.q_control2,op.q_target].contains(&q)}
// Payload rotations emit unconditional Swap; it is phase-free and self-inverse.
fn pure(ops:&[NativeOp]){for o in ops{assert!(matches!(o.kind,K::X|K::CX|K::CCX|K::Swap),"non-classical K2 operation: {o:?}");assert_eq!(o.c_condition,NO_BIT);}}
fn count(ops:&[NativeOp])->(usize,usize){(ops.iter().filter(|o|o.kind==K::CCX).count(),ops.len())}
fn fingerprint(ops:&[NativeOp])->String{
    let mut h=sha3::Keccak256::new();for o in ops{Digest::update(&mut h,(o.kind as u32).to_le_bytes());
        for v in[o.q_control2.0,o.q_control1.0,o.q_target.0,o.c_target.0,o.c_condition.0,o.r_target.0]{Digest::update(&mut h,v.to_le_bytes());}}
    format!("{:x}",h.finalize())
}
fn emit(b:&mut B,tape:&[G],inverse:bool)->Vec<NativeOp>{
    assert!(tape.len()<=MAX_OPS);assert!(b.ops.is_empty());b.tof=0;b.global_cancel=false;b.play(tape,inverse);b.flush_global();
    // Transfer exact operations and discard spare capacity before retention.
    // Shrinking may allocate transiently; the external RSS cap still governs.
    assert!(b.ops.len()<=MAX_OPS);
    let out=std::mem::take(&mut b.ops).into_boxed_slice().into_vec();
    assert_eq!(out.capacity(),out.len());out
}
fn play(ops:&[NativeOp],w:&[u64],sign:u64)->(Vec<u64>,u64){
    PLAY_CALLS.fetch_add(1,std::sync::atomic::Ordering::Relaxed);
    let mut h=sha3::Shake256::default();Update::update(&mut h,b"k2-stage5-fixed-signed-v1");let mut xof=h.finalize_xof();
    let mut sim=Simulator::new(w.len(),10002,&mut xof);sim.qubits.clone_from_slice(w);sim.phase=sign;
    sim.apply_iter(ops.iter());(sim.qubits,sim.phase)
}
fn checked(ops:&[NativeOp],w:&[u64],sign:u64)->Vec<u64>{let(out,phase)=play(ops,w,sign);assert_eq!(phase,sign);out}
fn difference(a:&[u64],b:&[u64])->u64{assert_eq!(a.len(),b.len());a.iter().zip(b).fold(0,|m,(x,y)|m|(x^y))}
fn memory_bound(gates:&[&Vec<G>],ops:&[&Vec<NativeOp>]){
    let bytes=gates.iter().map(|x|x.capacity()*std::mem::size_of::<G>()).sum::<usize>()
        +ops.iter().map(|x|x.capacity()*std::mem::size_of::<NativeOp>()).sum::<usize>();
    assert!(bytes<=768*1024*1024,"retained gate/operation data exceeds bounded allowance");
}
struct UnusedArithmetic;
impl Arithmetic for UnusedArithmetic{
    fn apply(&mut self,_:&mut B,_:&SumSize,_:direct_payload::Roles,_:direct_payload::Kernel,
        _:&[QubitId],_:&[QubitId],_:&[QubitId]){panic!("unexpected delegated arithmetic in frozen digit");}
}

struct Rig{b:B,ring:Vec<QubitId>,q:Vec<QubitId>,p:Vec<QubitId>,meta:SumSize,ph:QubitId,r:Roles}
impl Rig{
    fn new(optimized:bool)->Self{
        let mut b=B::new();b.cancel_simple_pairs=optimized;b.cancel_commuting_pairs=optimized;
        let ring=b.alloc_n(257);let q=b.alloc_n(128);let p=b.alloc_n(258);
        let meta=SumSize{y:b.alloc_n(7).try_into().unwrap(),sum:b.alloc_n(5).try_into().unwrap()};
        let ph=b.alloc();let r=Roles{activity:b.alloc(),flight:b.alloc(),mask:b.alloc(),x128:b.alloc()};
        assert_eq!(b.width(),660);assert_eq!(r.x128.0,659);Self{b,ring,q,p,meta,ph,r}
    }
    fn capture_full(&mut self,col:Column,payload:bool,disabled:bool)->Vec<G>{
        let loans=[self.p[0],self.p[1]];
        let c=Cross{size:&self.meta,ring:&self.ring,q:&self.q,phase:self.ph,roles:self.r,dirty:&self.p,
            y_bounds:col.y,qb:30,clean_external:if payload{&[]}else{&loans}};
        let mut a=UnusedArithmetic;self.b.begin();
        if disabled{run_diagnostic(&mut self.b,&c,col.z,payload.then_some(self.p.as_slice()),&mut a,Diagnostic::default());}
        else{run(&mut self.b,&c,col.z,payload.then_some(self.p.as_slice()),&mut a);}
        let out=self.b.end();assert!(out.len()<=MAX_OPS);out
    }
    fn capture_suffix(&mut self,col:Column,payload:bool,candidate:bool,fault:Fault)->Vec<G>{
        let loans=[self.p[0],self.p[1]];
        let c=Cross{size:&self.meta,ring:&self.ring,q:&self.q,phase:self.ph,roles:self.r,dirty:&self.p,
            y_bounds:col.y,qb:30,clean_external:if payload{&[]}else{&loans}};
        let session=payload.then(||direct_payload::Session{raw:self.p.iter().copied().chain([self.ph]).collect(),
            activity:self.r.activity,phase:self.ph,ht:true,finish_flag:None});
        self.b.begin();if candidate{k2_post_digit(&mut self.b,&c,col.z,session,fault);}
        else{assert_eq!(fault,Fault::None);k2_parent_post_digit(&mut self.b,&c,col.z,session);}
        let out=self.b.end();assert!(out.len()<=MAX_OPS);out
    }
    fn capture_primitive(&mut self,col:Column,k:usize,candidate:bool)->Vec<G>{
        let loans=[self.p[0],self.p[1]];
        let c=Cross{size:&self.meta,ring:&self.ring,q:&self.q,phase:self.ph,roles:self.r,dirty:&self.p,
            y_bounds:col.y,qb:30,clean_external:&loans};
        let t=super::super::normalized_cross_frame::natural_target(&c,k);
        self.b.begin();if candidate{let tape=Division::new(Contract::default()).record(&mut self.b,&c,&t,k,Fault::None);self.b.play(&tape,false);}
        else{D::parent(true,true).divide_inplace(&mut self.b,&c,&t,Gate::Natural(k),false);}
        self.b.end()
    }
    fn fixture(&self,col:Column,y:usize,s:usize,active:bool,payload:bool)->Vec<u64>{
        let mut seed=SEED^(col.id as u64)<<40^(y as u64)<<24^(s as u64)<<8^u64::from(active);
        let mut w:Vec<_>=(0..660).map(|_|rng(&mut seed)).collect();
        for bit in 0..64{word(&mut w,&self.meta.y,bit,y-1);word(&mut w,&self.meta.sum,bit,s);}
        w[self.r.activity.0 as usize]=if active{u64::MAX}else{0};w[self.r.flight.0 as usize]=0;w[self.r.mask.0 as usize]=0;
        let z=226+s-y;assert!(col.z.0<=z&&z<=col.z.1);assert!(col.y.0<=y&&y<=col.y.1);
        if active{
            for &q in &self.q[y..]{w[q.0 as usize]=0;}w[self.q[y-1].0 as usize]=u64::MAX;
            w[self.ring[z-1].0 as usize]=u64::MAX;w[self.r.x128.0 as usize]=0;
            // The first executed restoring window has a zero virtual top.
            // In S=0/1 the retained 30-bit quotient does not cover q30/q31.
            let first_k=(31-s).min(29);let bits=y+first_k;
            for j in bits..257-z{w[self.ring[256-j].0 as usize]=0;}
        }
        if !payload{w[self.p[0].0 as usize]=0;w[self.p[1].0 as usize]=0;}w
    }
    fn primitive_fixture(&self,col:Column,k:usize,y:usize,s:usize,sector:usize)->Vec<u64>{
        let mut seed=SEED^(col.id as u64)<<40^(y as u64)<<24^(s as u64)<<12^(k as u64)<<4^sector as u64;
        let mut w:Vec<_>=(0..660).map(|_|rng(&mut seed)).collect();
        for bit in 0..64{word(&mut w,&self.meta.y,bit,y-1);word(&mut w,&self.meta.sum,bit,s);}
        let passed=s<=31-k;w[self.r.activity.0 as usize]=if sector==0{u64::MAX}else{0};
        w[self.r.flight.0 as usize]=if sector==2&&passed{rng(&mut seed)}else{0};w[self.r.mask.0 as usize]=0;
        if sector==0&&passed{for &q in &self.q[..128-y]{w[q.0 as usize]=0;}w[self.q[127].0 as usize]=u64::MAX;w[self.r.x128.0 as usize]=0;}
        w[self.p[0].0 as usize]=0;w[self.p[1].0 as usize]=0;w
    }
}

/// Independent subtraction/borrow oracle for the full normalized word. This
/// does not transcribe the Cuccaro cells or the flight-carry implementation.
fn primitive_oracle(w:&[u64],q:&[QubitId],t:&[QubitId],r:Roles,passed:u64)->Vec<u64>{
    let mut out=w.to_vec();let(a,e)=(r.activity.0 as usize,r.flight.0 as usize);
    let delta=out[a]&!passed;out[e]^=delta;let delta=out[e]&!passed;out[a]^=delta;
    let mut borrow=0;let mut diff=vec![];for i in 0..t.len(){let x=out[t[i].0 as usize];let y=if i<q.len(){out[q[i].0 as usize]}else{0};
        diff.push(x^y^borrow);borrow=(!x&(y|borrow))|(y&borrow);}
    let dec=out[a]&!borrow;out[e]^=dec;let enabled=out[a]&out[e];
    for(i,&q)in t.iter().enumerate(){let x=&mut out[q.0 as usize];*x^=(*x^diff[i])&enabled;}
    let top=t[q.len()].0 as usize;let delta=(out[top]^out[e])&out[a];out[top]^=delta;out[e]^=delta;
    let delta=out[e]&!passed;out[a]^=delta;let delta=out[a]&!passed;out[e]^=delta;out
}

/// Raw-coordinate 30-step restoring division, independent of either frame
/// circuit. Used only for the no-payload proper suffix, including its initial
/// unconditional leading-Z flip. Full payload sweeps use the literal parent.
fn division_oracle(rig:&Rig,w:&[u64],y:usize,s:usize)->Vec<u64>{
    let mut out=w.to_vec();let z=226+s-y;out[rig.ring[z-1].0 as usize]^=u64::MAX;
    for shot in 0..64{if (w[rig.r.activity.0 as usize]>>shot)&1==0{continue;}
        for k in (0..30).rev(){if s>31-k{continue;}
            let mut borrow=false;let mut diff=vec![];
            for i in 0..=y{let x=(out[rig.ring[256-k-i].0 as usize]>>shot)&1!=0;
                let q=i<y&&((w[rig.q[i].0 as usize]>>shot)&1!=0);
                diff.push(x^q^borrow);borrow=(!x&&(q||borrow))||(q&&borrow);}
            if !borrow{for(i,v)in diff.iter().copied().enumerate(){put(&mut out,rig.ring[256-k-i],shot,v);}}
            assert_eq!((out[rig.ring[256-k-y].0 as usize]>>shot)&1,0,"restoring-window fixture premise");
            put(&mut out,rig.ring[256-k-y],shot,!borrow);
        }
    }out
}

fn expect_guard(expected:GuardViolation,f:impl FnOnce()){
    let caught=std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).expect_err("missing K2 typed guard");
    match caught.downcast::<GuardViolation>(){Ok(actual)=>assert_eq!(*actual,expected),Err(other)=>std::panic::resume_unwind(other)}
}
fn guard_controls()->usize{
    use super::super::normalized_cross_arithmetic::k2_stage5::{Site,Frame,Carry,Source,S5QFrame};
    let expected=|code,wire|GuardViolation{site:"K2/S01",code,wire};let mut n=0;
    for site in [Site::H01,Site::H02,Site::C07,Site::C13]{let mut c=Contract::default();c.site=site;
        expect_guard(expected(GuardCode::Site,None),||{Division::new(c);});n+=1;}
    for frame in [Frame::Parent129,Frame::Controller129,Frame::NativeHrQ128]{let mut c=Contract::default();c.frame=frame;
        expect_guard(expected(GuardCode::Frame,None),||{Division::new(c);});n+=1;}
    for carry in [Carry::ParentFourth,Carry::None]{let mut c=Contract::default();c.carry=carry;
        expect_guard(expected(GuardCode::Carry,None),||{Division::new(c);});n+=1;}
    let mut contract=Contract::default();contract.source=Source::Parked;
    expect_guard(expected(GuardCode::Source,None),||{Division::new(contract);});n+=1;
    let mut rig=Rig::new(false);let loans=[rig.p[0],rig.p[1]];
    let base=Cross{size:&rig.meta,ring:&rig.ring,q:&rig.q,phase:rig.ph,roles:rig.r,dirty:&rig.p,
        y_bounds:(1,128),qb:30,clean_external:&loans};
    fn make<'a>(c:&Cross<'a>,roles:Roles,loans:&'a[QubitId])->Cross<'a>{Cross{size:c.size,ring:c.ring,q:c.q,
        phase:c.phase,roles,dirty:c.dirty,y_bounds:c.y_bounds,qb:c.qb,clean_external:loans}}
    expect_guard(expected(GuardCode::Alias,Some(rig.r.flight)),||{let mut r=rig.r;r.activity=r.flight;k2::validate(&make(&base,r,&loans),None);});n+=1;
    expect_guard(expected(GuardCode::Loans,None),||k2::validate(&make(&base,rig.r,&loans[..1]),None));n+=1;
    let same=[rig.p[0],rig.p[0]];expect_guard(expected(GuardCode::Alias,Some(rig.p[0])),||k2::validate(&make(&base,rig.r,&same),None));n+=1;
    let raw:Vec<_>=rig.p.iter().copied().chain([rig.ph]).collect();
    expect_guard(expected(GuardCode::Loans,None),||k2::validate(&make(&base,rig.r,&loans),Some(&raw)));n+=1;
    let mut bad=raw.clone();bad[258]=rig.p[0];expect_guard(expected(GuardCode::Shape,None),||k2::validate(&make(&base,rig.r,&[]),Some(&bad)));n+=1;
    let mut bad=raw.clone();bad[0]=rig.ring[0];expect_guard(expected(GuardCode::Alias,Some(rig.ring[0])),||k2::validate(&make(&base,rig.r,&[]),Some(&bad)));n+=1;
    let c=make(&base,rig.r,&loans);let token=S5QFrame::open(&mut rig.b,&c,Fault::None);
    let mut changed=make(&base,rig.r,&loans);changed.y_bounds=(2,128);
    expect_guard(expected(GuardCode::FrameBinding,None),||{token.close(&mut rig.b,&changed,Fault::None);});n+=1;
    #[derive(Debug)]struct Sentinel;
    let outer=std::panic::catch_unwind(||expect_guard(expected(GuardCode::Frame,None),||std::panic::panic_any(Sentinel)));
    assert!(outer.unwrap_err().is::<Sentinel>());n+=1;
    assert_eq!(n,18);println!("K2_GUARDS typed_rejections=17 unknown_panic_propagation=true controls={n}");n
}

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
enum QualificationPhase { Full, Baseline(usize), Component }
impl QualificationPhase {
    fn from_env()->Self {
        match std::env::var("K2_QUALIFICATION_PHASE") {
            Err(std::env::VarError::NotPresent)=>Self::Full,
            Ok(value) if value=="component"=>Self::Component,
            Ok(value)=>{
                let id=value.strip_prefix("baseline:").and_then(|s|s.parse::<usize>().ok()).expect("invalid K2 qualification phase");
                assert!(id<16 && value==format!("baseline:{id}"),"noncanonical/out-of-range K2 baseline group");
                Self::Baseline(id)
            },
            Err(_)=>panic!("non-UTF8 K2 qualification phase"),
        }
    }
}

#[test]
fn k2_stage5_native_component(){
    assert_eq!(PLAY_CALLS.swap(0,std::sync::atomic::Ordering::Relaxed),0);
    assert!(std::env::var_os("LOWQ_EXACT_STREAM_PATH").is_none());assert!(std::env::var_os("LS_NO_BAKE").is_none());
    for key in include_str!("c162_consulted_env.txt").lines(){if let Some(value)=std::env::var_os(key){
        let expected=super::super::BAKED_KNOBS.iter().find(|(k,_)|*k==key).map(|(_,v)|*v);
        assert!(expected.is_some_and(|v|value==std::ffi::OsStr::new(v)),"K2 inherited override {key}");}}
    let sc=super::super::frogdrop_sched::from_text(include_str!("sched_frogdrop.txt"));
    let(cols,_,_)=super::super::pointadd_frogdrop::col_pars(&sc);
    for col in COLUMNS{assert_eq!((sc.cols[col.id].sz,sc.cols[col.id].sy),(col.schedule_z,col.schedule_y));
        assert_eq!((cols[col.id].sz,(cols[col.id].sy.0.max(1),cols[col.id].sy.1.min(128))),(col.z,col.y));
        println!("K2_COLUMN column={} schedule_Z={:?} schedule_Y={:?} actual_Z={:?} actual_Y={:?} metadata_pairs={}",col.id,col.schedule_z,col.schedule_y,col.z,col.y,metadata(col).len());}
    let phase=QualificationPhase::from_env();
    let mut baselines=0;
    for optimized in [false,true]{for (column_index,col) in COLUMNS.into_iter().enumerate(){for payload in [false,true]{
        let group=usize::from(optimized)*8+column_index*2+usize::from(payload);
        if phase==QualificationPhase::Component || matches!(phase,QualificationPhase::Baseline(id) if id!=group){continue;}
        let mut a=Rig::new(optimized);let mut d=Rig::new(optimized);
        let parent=a.capture_full(col,payload,false);let disabled=d.capture_full(col,payload,true);assert_eq!(parent,disabled);
        for inverse in [false,true]{let p=emit(&mut a.b,&parent,inverse);let q=emit(&mut d.b,&disabled,inverse);assert_eq!(p,q);
            memory_bound(&[&parent,&disabled],&[&p,&q,&a.b.ops,&d.b.ops]);
            println!("K2_BASELINE column={} payload={payload} optimized={optimized} inverse={inverse} Q=660 T={} N={} hash={}",col.id,count(&p).0,count(&p).1,fingerprint(&p));baselines+=1;}
    }}}
    match phase {
        QualificationPhase::Full=>assert_eq!(baselines,32),
        QualificationPhase::Baseline(id)=>{
            assert_eq!(baselines,2);
            println!("K2_BASELINE_GROUP_COMPLETE group={id} baseline_direction_records=2 candidate_plays=0 submit=CLOSED");
            return;
        },
        QualificationPhase::Component=>assert_eq!(baselines,0),
    }
    let guards=guard_controls();let mut sign_seed=SEED;let mut primitive_rows=0;
    for optimized in [false,true]{for col in COLUMNS{for k in [0,13,29]{
        let mut rig=Rig::new(optimized);let p=rig.capture_primitive(col,k,false);let c=rig.capture_primitive(col,k,true);
        let pf=emit(&mut rig.b,&p,false);let pi=emit(&mut rig.b,&p,true);let cf=emit(&mut rig.b,&c,false);let ci=emit(&mut rig.b,&c,true);
        for ops in [&pf,&pi,&cf,&ci]{pure(ops);}assert!(!cf.iter().chain(&ci).any(|o|uses(o,rig.r.x128)||uses(o,rig.ph)||uses(o,rig.p[0])||uses(o,rig.p[1])));
        memory_bound(&[&p,&c],&[&pf,&pi,&cf,&ci,&rig.b.ops]);
        // All four emissions are complete; only their operation vectors recur.
        drop(p);drop(c);
        let t:Vec<_>=(0..129).map(|j|rig.ring[256-k-j]).collect();
        for(y,s)in metadata(col){for sector in 0..3{
            let w=rig.primitive_fixture(col,k,y,s,sector);let passed=if s<=31-k{u64::MAX}else{0};
            let expected=primitive_oracle(&w,&rig.q,&t,rig.r,passed);let sign=rng(&mut sign_seed);
            let parent=checked(&pf,&w,sign);assert_eq!(parent,expected);let candidate=checked(&cf,&w,sign);assert_eq!(candidate,expected);
            assert_eq!(checked(&pi,&expected,sign),w);assert_eq!(checked(&ci,&expected,sign),w);primitive_rows+=64;
        }}
        println!("K2_PRIMITIVE column={} k={k} optimized={optimized} rows=3456 directions=2 parent_T={} parent_N={} candidate_T={} candidate_N={} parent_hash={} candidate_hash={}",col.id,count(&pf).0,count(&pf).1,count(&cf).0,count(&cf).1,fingerprint(&pf),fingerprint(&cf));
    }}}
    assert_eq!(primitive_rows,82944);
    let(mut full_rows,mut profiles,mut mutations,mut harness_controls,mut active_spectator_rows)=(0,0,0,0,0);
    for optimized in [false,true]{for col in COLUMNS{for payload in [false,true]{
        let mut rig=Rig::new(optimized);let p=rig.capture_suffix(col,payload,false,Fault::None);let c=rig.capture_suffix(col,payload,true,Fault::None);
        let pf=emit(&mut rig.b,&p,false);let pi=emit(&mut rig.b,&p,true);let cf=emit(&mut rig.b,&c,false);let ci=emit(&mut rig.b,&c,true);
        for ops in [&pf,&pi,&cf,&ci]{pure(ops);}
        assert!(!cf.iter().chain(&ci).any(|o|uses(o,rig.r.x128)));
        if !payload{assert!(!cf.iter().chain(&ci).any(|o|uses(o,rig.ph)||uses(o,rig.p[0])||uses(o,rig.p[1])));}
        memory_bound(&[&p,&c],&[&pf,&pi,&cf,&ci,&rig.b.ops]);
        drop(p); // Parent operations retain every later comparison/count/hash.
        let mut digest=sha3::Keccak256::new();
        for(y,s)in metadata(col){for active in [false,true]{
            let w=rig.fixture(col,y,s,active,payload);let sign=rng(&mut sign_seed);for x in &w{Digest::update(&mut digest,x.to_le_bytes());}
            let parent=checked(&pf,&w,sign);if !payload{assert_eq!(parent,division_oracle(&rig,&w,y,s));}
            let candidate=checked(&cf,&w,sign);assert_eq!(parent,candidate);
            assert_eq!(checked(&pi,&parent,sign),w);assert_eq!(checked(&ci,&candidate,sign),w);
            assert_eq!(candidate[rig.r.flight.0 as usize],0);assert_eq!(candidate[rig.r.mask.0 as usize],0);
            for &q in &rig.q{assert_eq!(candidate[q.0 as usize],w[q.0 as usize],"raw Q return");}
            for &q in rig.meta.y.iter().chain(&rig.meta.sum){assert_eq!(candidate[q.0 as usize],w[q.0 as usize]);}
            if active{let mut dirty=w.clone();dirty[rig.r.x128.0 as usize]=u64::MAX;let mut expected=candidate.clone();expected[rig.r.x128.0 as usize]=u64::MAX;
                assert_eq!(checked(&cf,&dirty,sign),expected);active_spectator_rows+=64;}
            full_rows+=64;
        }}
        // Both inverse comparisons are complete for the entire fixed profile.
        drop(pi);drop(ci);
        for fault in [Fault::WrongEntry129,Fault::OmitQReturn,Fault::MissingQgFlip,Fault::CarryDecision]{
            if fault==Fault::MissingQgFlip&&!payload{continue;}
            let bad=rig.capture_suffix(col,payload,true,fault);let bad_ops=emit(&mut rig.b,&bad,false);assert_ne!(fingerprint(&bad_ops),fingerprint(&cf));
            memory_bound(&[&c,&bad],&[&pf,&cf,&bad_ops,&rig.b.ops]);
            drop(bad); // The actual emitted mutant remains for all fixed cases.
            let mut mask=0;for(y,s)in metadata(col){for active in [false,true]{let w=rig.fixture(col,y,s,active,payload);let sign=rng(&mut sign_seed);
                let normal=checked(&cf,&w,sign);let corrupted=checked(&bad_ops,&w,sign);mask|=difference(&normal,&corrupted);}}
            assert_ne!(mask,0,"ineffective K2 mutant {fault:?} column {}",col.id);mutations+=1;
            println!("K2_MUTANT column={} payload={payload} optimized={optimized} kind={fault:?} mask={mask:016x} normal_hash={} mutant_hash={}",col.id,fingerprint(&cf),fingerprint(&bad_ops));
        }
        let(y,s)=metadata(col)[0];let w=rig.fixture(col,y,s,true,payload);let sign=rng(&mut sign_seed);let expected=checked(&cf,&w,sign);
        let mut phase_bad=c.clone();phase_bad.push(G::Cz(rig.r.activity,rig.q[y-1]));let phase_ops=emit(&mut rig.b,&phase_bad,false);
        memory_bound(&[&c,&phase_bad],&[&pf,&cf,&phase_ops,&rig.b.ops]);
        let(same,phase)=play(&phase_ops,&w,sign);assert_eq!(same,expected);assert_ne!(phase,sign);harness_controls+=1;
        drop(phase_ops);drop(phase_bad); // Release before constructing donor-only control.
        let mut donor_bad=c.clone();donor_bad.push(G::X(rig.p[2]));let donor_ops=emit(&mut rig.b,&donor_bad,false);
        memory_bound(&[&c,&donor_bad],&[&pf,&cf,&donor_ops,&rig.b.ops]);
        let(wrong,phase)=play(&donor_ops,&w,sign);assert_eq!(phase,sign);assert_ne!(difference(&wrong,&expected),0);harness_controls+=1;
        println!("K2_PROFILE column={} payload={payload} optimized={optimized} rows=2304 directions=2 Q=660 parent_T={} parent_N={} candidate_T={} candidate_N={} parent_hash={} candidate_hash={} input_hash={:x} phase_control=true donor_control=true",col.id,count(&pf).0,count(&pf).1,count(&cf).0,count(&cf).1,fingerprint(&pf),fingerprint(&cf),digest.finalize());profiles+=1;
    }}}
    assert_eq!((profiles,full_rows,mutations,harness_controls,active_spectator_rows),(16,36864,56,32,18432));
    let calls=PLAY_CALLS.load(std::sync::atomic::Ordering::Relaxed);assert_eq!(calls,11856);assert_eq!(calls*64,758784);
    println!("{} tests=1 baseline_direction_records={baselines} guards={guards} primitive_rows={primitive_rows} primitive_direction_pairs={} full_rows={full_rows} full_direction_pairs={} profiles={profiles} mutants={mutations} harness_controls={harness_controls} active_spectator_rows={active_spectator_rows} native_play_calls={calls} packed_lane_evaluations={} Q=660 site7_closed=false whole_result=false traversal_image_proven=false submit=CLOSED",if phase==QualificationPhase::Component{"K2_COMPONENT_COMPLETE"}else{"K2_NATIVE_COMPLETE"},primitive_rows*2,full_rows*2,calls*64);
}
