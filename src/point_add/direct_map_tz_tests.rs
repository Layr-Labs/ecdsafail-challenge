//! Bounded direct-map fixtures for the trailing-zero erasure candidate.
//! These are mechanism checks, not a whole-circuit equivalence or score claim.
use super::builder::{B,G};
use super::frogdrop::direct_map::{apply_stage_with_loans,stage_record};
use super::frogdrop::MapPar;
use super::frogdrop_col::ColPar;
use super::frogdrop_sched::N;
use super::tests_frogdrop::{run,Rng};
use crate::circuit::{BitId,Op,OperationType as K,QubitId,NO_BIT};
use std::collections::{BTreeMap,BTreeSet};
use std::sync::{Arc,Barrier};

struct Flag(super::D660TestFlag,Option<bool>);
impl Flag{
    fn new(name:&'static str,value:&str)->Self{
        let flag=match name{
            "D660_DEFER_S"=>super::D660TestFlag::S,
            "D660_DEFER_TAG"=>super::D660TestFlag::Tag,
            "D660_DEFER_TZ"=>super::D660TestFlag::Tz,
            _=>panic!("not a D660 test flag"),
        };
        let old=super::d660_test_override(flag,Some(value=="1"));Self(flag,old)
    }
}
impl Drop for Flag{
    fn drop(&mut self){super::d660_test_override(self.0,self.1);}
}

#[derive(Clone)]
struct Layout{
    ring:Vec<QubitId>,q:Vec<QubitId>,y:Vec<QubitId>,scratch:Vec<QubitId>,ph:QubitId,
    suffix:Vec<QubitId>,loans:Vec<QubitId>,
}
fn layout(b:&mut B)->Layout{
    Layout{ring:b.alloc_n(257),q:b.alloc_n(128),y:b.alloc_n(7),scratch:b.alloc_n(9),
        ph:b.alloc(),suffix:b.alloc_n(23),loans:b.alloc_n(2)}
}
fn par(cp:&ColPar)->MapPar{
    MapPar{clo:257-cp.smax.1,chi:257-cp.smax.0,m:if cp.dn{128}else{cp.m},tail:cp.tail,emax:cp.emax}
}
fn pure_ht(cp:&ColPar)->bool{cp.ht&&!cp.hr&&!cp.sw&&!cp.dl&&!cp.dq}
fn apply(b:&mut B,f:&Layout,cp:&ColPar,dirty:&[QubitId],loans:&[QubitId]){
    assert!(!(cp.dn&&cp.m>121));
    apply_stage_with_loans(b,&f.ring,&f.q,&f.y,&f.scratch,f.ph,&par(cp),cp.m,cp.dn,
        pure_ht(cp),dirty,loans,|_,_,_|panic!("ordinary map queried DONE"));
}

struct Emitted{
    ops:Vec<Op>,forward:usize,q:u64,masks:Vec<BitId>,forward_ccx:usize,total_ccx:usize,
}
fn ccx(ops:&[Op])->usize{ops.iter().filter(|op|op.kind==K::CCX).count()}
fn emit_pair(cp:&ColPar,boxed:bool,rows:bool,asymmetric:bool)->Emitted{
    let mut b=B::new();b.allow_booth=rows;let f=layout(&mut b);
    if boxed{b.deferred_forward_boxes();}
    apply(&mut b,&f,cp,&[],&[]);
    let forward=b.ops.len();
    if boxed{
        assert_eq!(b.deferred_tape_boxes(),1);assert_eq!(b.deferred_tape_rows(),0);
        assert_eq!(b.deferred_recipe_live(),0);
        b.deferred_inverse();
    }
    b.begin();
    if asymmetric{apply(&mut b,&f,cp,&f.suffix,&f.loans);}else{apply(&mut b,&f,cp,&[],&[]);}
    let inverse=b.end();b.play(&inverse,true);
    if boxed{
        assert_eq!(b.deferred_tape_boxes(),0);assert_eq!(b.deferred_tape_rows(),0);
        assert_eq!(b.deferred_recipe_live(),0);b.deferred_finish();
    }
    let masks=find_new_masks(&b.ops[..forward],&f.y);
    if boxed{
        assert_eq!(masks.len(),5);
        for &m in &masks{
            assert_eq!(b.ops[forward..].iter().filter(|op|op.kind==K::Z&&op.c_condition==m).count(),1);
        }
    }else{assert!(masks.is_empty());}
    let total_ccx=ccx(&b.ops);let forward_ccx=ccx(&b.ops[..forward]);let q=b.width();
    Emitted{ops:b.ops,forward,q,masks,forward_ccx,total_ccx}
}
fn find_new_masks(ops:&[Op],y:&[QubitId])->Vec<BitId>{
    let mut found=None;
    for i in 0..ops.len().saturating_sub(4){
        let w=&ops[i..i+5];
        if w.iter().enumerate().all(|(j,op)|op.kind==K::Hmr&&op.q_target==y[j]
            &&op.c_condition==NO_BIT&&op.c_target.0>=10_000){
            assert!(found.is_none(),"duplicate trailing-erasure mask window");found=Some(w.iter().map(|op|op.c_target).collect());
        }
    }
    found.unwrap_or_default()
}
fn forward_ops(e:&Emitted)->&[Op]{&e.ops[..e.forward]}

fn putn(w:&mut[u64],qs:&[QubitId],shot:usize,v:&N){
    for(i,q)in qs.iter().enumerate(){
        let bit=i<256&&v.bit(i);let x=&mut w[q.0 as usize];
        *x=(*x&!(1u64<<shot))|((bit as u64)<<shot);
    }
}
fn getn(w:&[u64],qs:&[QubitId],shot:usize)->N{
    let mut v=N::ZERO;for(i,q)in qs.iter().enumerate(){
        if(i<256)&&(w[q.0 as usize]>>shot)&1==1{v|=N::from(1u64)<<i;}
    }v
}
fn rev_put(w:&mut[u64],lanes:&[QubitId],shot:usize,v:&N){
    let r:Vec<_>=lanes.iter().rev().copied().collect();putn(w,&r,shot,v);
}
fn rev_getn(w:&[u64],lanes:&[QubitId],shot:usize)->N{
    let r:Vec<_>=lanes.iter().rev().copied().collect();getn(w,&r,shot)
}
fn bl(x:&N)->usize{x.bit_len()}
fn gcd(a:&N,b:&N)->N{let(mut x,mut y)=(*a,*b);while!y.is_zero(){let r=x%y;x=y;y=r;}x}
fn modinv(a:&N,m:&N)->N{
    let(mut r0,mut r1)=(*m,*a%*m);
    let(mut t0,mut t1):((N,bool),(N,bool))=((N::ZERO,false),(N::from(1u64),false));
    while!r1.is_zero(){
        let q=r0/r1;let r2=r0-q*r1;let qt=q*t1.0;
        let t2=if t0.1==t1.1{
            if t0.0>=qt{(t0.0-qt,t0.1)}else{(qt-t0.0,!t0.1)}
        }else{(t0.0+qt,t0.1)};
        r0=r1;r1=r2;t0=t1;t1=t2;
    }
    assert_eq!(r0,N::from(1u64));if t0.1{*m-(t0.0%*m)}else{t0.0%*m}
}
fn map_case(rng:&mut Rng,bx:usize,ex:usize,ey:usize)->(N,N,N,N){
    let p=super::frogdrop_sched::p();
    loop{
        let bxo=bx-ex;
        let xo=rng.below(bxo-1)|(N::from(1u64)<<(bxo-1))|N::from(1u64);let x=xo<<ex;
        let by=(bx-8+(rng.next()as usize%9)).min(bx);let byo=by-ey;
        let yo=rng.below(byo-1)|(N::from(1u64)<<(byo-1))|N::from(1u64);let y=yo<<ey;
        if gcd(&x,&y)!=N::from(1u64){continue;}
        let yv=(p%x)*modinv(&(y%x),&x)%x;if yv*y>=p{continue;}
        let z=(p-yv*y)/x;if z.is_zero(){continue;}
        assert_eq!(z*x+yv*y,p);return(z,x,y,yv);
    }
}
#[derive(Clone)]
struct Case{x:N,y:N,yv:N,cnt:u64,done:bool}
fn input(f:&Layout,cp:&ColPar,seed:u64)->(Vec<u64>,Vec<Case>){
    let mut rng=Rng::new(seed);let mut q=vec![0u64;257+128+7+9+1+23+2];
    for&p in&f.suffix{q[p.0 as usize]=rng.next();}
    q[f.scratch[0].0 as usize]=rng.next();
    q[f.ph.0 as usize]=if cp.col==0{0}else{u64::MAX};
    let mut cases=Vec::new();
    for shot in 0..64{
        let(z,x,y,yv,cnt,done)=if cp.col==0{
            let bx=28+rng.next()as usize%12;
            let e=[0usize,31,23,22,20,17,13,9,5,1,0,3,7,11,31,0][shot%16].min(bx-1);
            let(ex,ey)=if shot%2==0{(e,0)}else{(0,e.min(bx-10))};
            let c=map_case(&mut rng,bx,ex,ey);(c.0,c.1,c.2,c.3,0,false)
        }else{match shot%4{
            0|1=>{
                let e=[0usize,3,9,17,23,1,0,12][(shot/4)%8];let rb=26-e;
                let odd=(rng.next()%(1u64<<(rb-1)))|1|(1u64<<(rb-2));
                let mut r=N::from(odd)<<e;if r==N::from(1u64){r=N::from(3u64);}
                let cnt=1+rng.next()%cp.cntmax.max(1)as u64;
                if shot%4==0{
                    let p=super::frogdrop_sched::p();let z=(p-(rng.below(64)|N::from(1u64)))/r;
                    (z,r,N::from(1u64),p-z*r,cnt,true)
                }else{
                    let p=super::frogdrop_sched::p();let yv=p/r-rng.below(64);
                    (p-yv*r,N::from(1u64),r,yv,cnt,true)
                }
            },
            2=>{
                let bx=100+rng.next()as usize%22;
                let e=[0usize,31,23,20,13,5,1,7][(shot/4)%8];
                let(ex,ey)=if(shot/4)%2==0{(e,0)}else{(0,e)};
                let c=map_case(&mut rng,bx,ex,ey);(c.0,c.1,c.2,c.3,0,false)
            },
            _=>{let bx=40+rng.next()as usize%20;let c=map_case(&mut rng,bx,0,0);(c.0,c.1,c.2,c.3,0,false)}
        }};
        assert!(bl(&x).max(bl(&y))<=cp.m);
        let cut=257-bl(&x).max(bl(&y));
        putn(&mut q,&f.ring[..cut],shot,&z);rev_put(&mut q,&f.ring[cut..],shot,&y);
        putn(&mut q,&f.q,shot,&x);if done{putn(&mut q,&f.q[121..],shot,&N::from(cnt));}
        putn(&mut q,&f.y,shot,&N::from((bl(&y)-1)as u64));
        cases.push(Case{x,y,yv,cnt,done});
    }
    (q,cases)
}
fn check_forward(f:&Layout,input:&[u64],cases:&[Case],old:&Emitted,new:&Emitted,label:&str){
    let a=run(forward_ops(old),input.len(),&|w|*w=input.to_vec());
    let z=run(forward_ops(new),input.len(),&|w|*w=input.to_vec());
    assert_eq!(a.phase,0,"{label} parent forward phase");
    assert_eq!(z.q,a.q,"{label} disabled/enabled forward classical states (intermediate phase debt is repaired later)");
    for(shot,c)in cases.iter().enumerate(){
        let cut=257-bl(&c.x).max(bl(&c.y));
        assert_eq!(getn(&a.q,&f.ring[..cut],shot),c.yv,"{label} bottom shot{shot}");
        assert_eq!(rev_getn(&a.q,&f.ring[cut..],shot),c.x,"{label} top shot{shot}");
        let want=c.y|(N::from(c.cnt)<<121);assert_eq!(getn(&a.q,&f.q,shot),want,"{label} Q shot{shot}");
        assert_eq!(getn(&a.q,&f.y,shot),N::from((bl(&c.x)-1)as u64),"{label} new-top E shot{shot}");
        let _=c.done;
    }
}

fn symbolic(ops:&[Op],mut q:Vec<u64>,label:&str)->Vec<u64>{
    let original=q.clone();let mut measured=BTreeMap::new();let mut phases=Vec::<u64>::new();let mut constant=0u64;
    for op in ops{
        let t=op.q_target.0 as usize;let a=op.q_control1.0 as usize;let c=op.q_control2.0 as usize;
        match op.kind{
            K::X=>{assert_eq!(op.c_condition,NO_BIT);q[t]^=u64::MAX;},
            K::CX=>{assert_eq!(op.c_condition,NO_BIT);q[t]^=q[a];},
            K::CCX=>{assert_eq!(op.c_condition,NO_BIT);q[t]^=q[a]&q[c];},
            K::Swap=>{assert_eq!(op.c_condition,NO_BIT);q.swap(a,t);},
            K::Hmr=>{assert_eq!(op.c_condition,NO_BIT);measured.insert(op.c_target,phases.len());phases.push(q[t]);q[t]=0;},
            K::CZ=>{
                if op.c_condition==NO_BIT{constant^=q[a]&q[t];}else{phases[measured[&op.c_condition]]^=q[a]&q[t];}
            },
            K::Z=>{
                if op.c_condition==NO_BIT{constant^=q[t];}else{phases[measured[&op.c_condition]]^=q[t];}
            },
            other=>panic!("{label}: unexpected operation {other:?}; input={original:?}"),
        }
    }
    if constant!=0||phases.iter().any(|&v|v!=0){
        panic!("{label}: nonzero HMR phase constant={constant:x} coefficients={phases:?}; input={original:?}");
    }
    q
}
fn check_roundtrip(e:&Emitted,input:&[u64],label:&str,symbolic_too:bool){
    let actual=run(&e.ops,input.len(),&|w|*w=input.to_vec());
    assert_eq!(actual.phase,0,"{label}: native phase; input={input:?}");
    assert_eq!(actual.q,input,"{label}: all-wire restoration; input={input:?}");
    if symbolic_too{
        let sym=symbolic(&e.ops,input.to_vec(),label);assert_eq!(sym,input,"{label}: symbolic restoration");
        assert_eq!(actual.q,sym,"{label}: native vs independent symbolic");
    }
}
fn recipe_ports(recipe:&[G])->BTreeSet<QubitId>{
    let mut out=BTreeSet::new();
    for&g in recipe{match g{
        G::X(a)|G::ZIf(a,_)|G::XIf(a,_)=>{out.insert(a);},
        G::Cx(a,t)|G::Cz(a,t)|G::Swap(a,t)=>{out.insert(a);out.insert(t);},
        G::Ccx(a,c,t)|G::AndC(a,c,t)|G::AndU(a,c,t)=>{out.insert(a);out.insert(c);out.insert(t);},
        G::RowAdd(..)=>panic!("row in trailing probe"),G::DeferredErase(..)=>panic!("nested trailing erasure"),
    }}out
}
fn physical_recipe(cp:&ColPar,asymmetric:bool)->((u32,Vec<G>,Vec<QubitId>),Layout){
    let mut b=B::new();b.allow_booth=false;let f=layout(&mut b);
    if asymmetric{apply(&mut b,&f,cp,&f.suffix,&f.loans);}else{apply(&mut b,&f,cp,&[],&[]);}
    assert_eq!(b.deferred_tape_boxes(),0);assert_eq!(b.deferred_recipe_live(),1);
    (b.deferred_erasure_recipe(0),f)
}
fn check_physical_recipe(cp:&ColPar){
    let(a,f)=physical_recipe(cp,false);let(z,_)=physical_recipe(cp,true);
    assert_eq!(a,z,"column{} actual forward/inverse donor IDs differ",cp.col);
    assert_eq!(a.0,6603);assert_eq!(a.2,f.y[..5]);
    let ports=recipe_ports(&a.1);
    for&q in f.suffix.iter().chain(&f.loans).chain([f.scratch[0],f.ph].iter()){
        assert!(!ports.contains(&q),"column{} excluded donor q{} entered recipe",cp.col,q.0);
    }
}
fn op_hash(ops:&[Op])->String{
    use sha3::Digest;let mut h=sha3::Keccak256::new();
    for op in ops{
        Digest::update(&mut h,(op.kind as u32).to_le_bytes());
        for v in[op.q_control2.0,op.q_control1.0,op.q_target.0,op.c_target.0,op.c_condition.0,op.r_target.0]{
            Digest::update(&mut h,v.to_le_bytes());
        }
    }
    format!("{:x}",h.finalize())
}
fn columns()->Vec<ColPar>{
    super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP)).0
}
fn check_column(ci:usize){
    super::bake_knobs();let cp=columns()[ci].clone();
    let mut geometry=B::new();let f=layout(&mut geometry);
    let(inp,cases)=input(&f,&cp,0xd660_0000+ci as u64);
    let(old,old_hash)={
        let _flag=Flag::new("D660_DEFER_TZ","0");let e=emit_pair(&cp,false,false,true);let h=op_hash(&e.ops);(e,h)
    };
    let(new,new_hash)={
        let _flag=Flag::new("D660_DEFER_TZ","1");let e=emit_pair(&cp,true,false,true);let h=op_hash(&e.ops);(e,h)
    };
    let label=format!("col{ci} literal");check_forward(&f,&inp,&cases,&old,&new,&label);
    check_roundtrip(&old,&inp,&format!("{label} parent"),true);
    check_roundtrip(&new,&inp,&format!("{label} boxed"),true);
    assert_eq!(old.q,new.q);let forward_delta=old.forward_ccx-new.forward_ccx;
    let roundtrip_delta=old.total_ccx-new.total_ccx;assert!(forward_delta>0);
    {
        let _flag=Flag::new("D660_DEFER_TZ","1");check_physical_recipe(&cp);
    }
    eprintln!("D660_TZ_FIXTURE col={ci} rows=false Q={} parent_forward_CCX={} boxed_forward_CCX={} forward_delta_CCX={forward_delta} parent_roundtrip_CCX={} boxed_roundtrip_CCX={} roundtrip_delta_CCX={roundtrip_delta} parent_ops={} boxed_ops={} parent_keccak={old_hash} boxed_keccak={new_hash}",
        old.q,old.forward_ccx,new.forward_ccx,old.total_ccx,new.total_ccx,old.ops.len(),new.ops.len());
    let(old_rows,new_rows)={
        let _flag=Flag::new("D660_DEFER_TZ","0");let old=emit_pair(&cp,false,true,true);
        drop(_flag);let _flag=Flag::new("D660_DEFER_TZ","1");let new=emit_pair(&cp,true,true,true);(old,new)
    };
    let label=format!("col{ci} production-rows");check_forward(&f,&inp,&cases,&old_rows,&new_rows,&label);
    check_roundtrip(&old_rows,&inp,&format!("{label} parent"),false);
    check_roundtrip(&new_rows,&inp,&format!("{label} boxed"),false);
    assert_eq!(old_rows.q,new_rows.q);let forward_delta=old_rows.forward_ccx-new_rows.forward_ccx;
    let roundtrip_delta=old_rows.total_ccx-new_rows.total_ccx;assert!(forward_delta>0);
    eprintln!("D660_TZ_FIXTURE col={ci} rows=true Q={} parent_forward_CCX={} boxed_forward_CCX={} forward_delta_CCX={forward_delta} parent_roundtrip_CCX={} boxed_roundtrip_CCX={} roundtrip_delta_CCX={roundtrip_delta}",
        old_rows.q,old_rows.forward_ccx,new_rows.forward_ccx,old_rows.total_ccx,new_rows.total_ccx);
}

#[test]
fn d660_tz_col0_exact_erasure(){check_column(0);}
#[test]
fn d660_tz_col120_plain_done_exact_erasure(){check_column(120);}
#[test]
fn d660_tz_parent_fixture_bytes(){
    super::bake_knobs();let _flag=Flag::new("D660_DEFER_TZ","0");
    for(ci,want)in[
        (0usize,"374410975fc21d35b85a31d62752c099bfef7d931a684a1bd2baa97296ff820b"),
        (120,"8ad0f9aa5ba9fbd2b2e8a4828db29d2ae4227b3c89b97bd1cd3361342e69c7d6"),
    ]{
        let e=emit_pair(&columns()[ci],false,false,true);let got=op_hash(&e.ops);
        assert_eq!(got,want,"column{ci} disabled stream differs from f8ae4bdf fixture bytes");
        eprintln!("D660_TZ_PARENT_BYTES col={ci} ops={} CCX={} keccak={got}",e.ops.len(),e.total_ccx);
    }
}

#[test]
fn d660_tz_controlled_and_b0_never_box(){
    super::bake_knobs();let _flag=Flag::new("D660_DEFER_TZ","1");
    let _s=Flag::new("D660_DEFER_S","0");let _tag=Flag::new("D660_DEFER_TAG","0");
    assert!(super::d660_defer_tz()&&super::d660_defer_any());
    assert!(super::BAKED_KNOBS.contains(&("D660_DEFER_TZ","1")));
    let cols=columns();let cp=&cols[97];assert!(cp.dn&&cp.m>121);
    for force_pair in[false,true]{
        let mut b=B::new();b.allow_booth=false;let f=layout(&mut b);
        let pht=if force_pair{true}else{pure_ht(cp)};
        apply_stage_with_loans(&mut b,&f.ring,&f.q,&f.y,&f.scratch,f.ph,&par(cp),cp.m,cp.dn,pht,
            &f.suffix,&f.loans,|_,_,_|{});
        assert_eq!(b.deferred_recipe_live(),0);assert_eq!(b.deferred_tape_boxes(),0);
        assert!(find_new_masks(&b.ops,&f.y).is_empty());
    }
    let(_,b0,_)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let b0=b0.unwrap();let mut b=B::new();b.allow_booth=false;let f=layout(&mut b);
    let bp=MapPar{clo:257-b0.smax.1,chi:257-b0.smax.0,m:128,tail:b0.tail,emax:b0.emax};
    let tape=stage_record(&mut b,&f.ring,&f.q[..114],&f.y,&f.scratch,f.ph,&bp,b0.m,&f.suffix);
    assert!(!tape.iter().any(|g|matches!(g,G::DeferredErase(..))));assert_eq!(b.deferred_recipe_live(),0);
}

// R1 remains column-invariant. This checks only the deterministic ordinary gate;
// existing S boxes separate consecutive TZ boxes, not asymmetric/S-disabled replay.
fn mixed_box_column(flip_tz:bool){
    let cp=columns()[0].clone();let mut b=B::new();b.allow_booth=false;b.global_cancel=true;
    let f=layout(&mut b);let aux=b.alloc_n(2);let(mut inp,_)=input(&f,&cp,0xd660_1111);
    inp.resize(b.width()as usize,0);
    b.deferred_forward_boxes();
    {
        let _flag=Flag::new("D660_DEFER_TZ",if flip_tz{"0"}else{"1"});
        b.deferred_erasure(6602,vec![],vec![aux[0]]);
        b.deferred_erasure(6601,vec![],vec![aux[1]]);
        apply(&mut b,&f,&cp,&[],&[]);
    }
    assert_eq!(b.deferred_tape_boxes(),if flip_tz{2}else{3});
    let _flag=Flag::new("D660_DEFER_TZ","1");
    b.deferred_inverse();b.begin();
    b.deferred_erasure(6602,vec![],vec![aux[0]]);
    b.deferred_erasure(6601,vec![],vec![aux[1]]);
    apply(&mut b,&f,&cp,&f.suffix,&f.loans);
    let inverse=b.end();
    if flip_tz{
        let panic=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||b.play(&inverse,true)))
            .expect_err("forward TZ=0/inverse TZ=1 must expose the missing 6603");
        let text=if let Some(s)=panic.downcast_ref::<String>(){s.clone()}
            else if let Some(s)=panic.downcast_ref::<&str>(){(*s).to_string()}else{String::new()};
        assert!(text.contains("left: 6601")&&text.contains("right: 6603"),"unexpected mismatch {text}");
        eprintln!("D660_TZ_FLIP_REPRO forward=[6602,6601] inverse_first=6603 panic=left 6601/right 6603");
        return;
    }
    b.play(&inverse,true);assert_eq!(b.deferred_tape_boxes(),0);assert_eq!(b.deferred_tape_rows(),0);
    b.deferred_finish();b.flush_global();
    let out=run(&b.ops,inp.len(),&|w|*w=inp.clone());assert_eq!(out.phase,0);assert_eq!(out.q,inp);
    eprintln!("D660_TZ_MIXED_LIFO forward=[6602,6601,6603] inverse=[6603,6601,6602] global_cancel=true PASS");
}

#[test]
fn d660_tz_mixed_boxes_lifo_global_cancel(){super::bake_knobs();mixed_box_column(false);}
#[test]
fn d660_tz_flag_flip_reproduces_6601_6603(){super::bake_knobs();mixed_box_column(true);}

#[test]
fn d660_test_flag_overrides_are_thread_local(){
    let _s=Flag::new("D660_DEFER_S","0");let _tag=Flag::new("D660_DEFER_TAG","0");
    let _tz=Flag::new("D660_DEFER_TZ","1");
    let barrier=Arc::new(Barrier::new(2));let child_barrier=barrier.clone();
    let child=std::thread::spawn(move||{
        let _s=Flag::new("D660_DEFER_S","1");let _tag=Flag::new("D660_DEFER_TAG","1");
        let _tz=Flag::new("D660_DEFER_TZ","0");
        child_barrier.wait();
        let values=(super::d660_defer_s(),super::d660_defer_tag(),super::d660_defer_tz(),super::d660_defer_any());
        child_barrier.wait();values
    });
    barrier.wait();
    assert_eq!((super::d660_defer_s(),super::d660_defer_tag(),super::d660_defer_tz(),super::d660_defer_any()),
        (false,false,true,true));
    barrier.wait();
    assert_eq!(child.join().unwrap(),(true,true,false,true));
    assert_eq!((super::d660_defer_s(),super::d660_defer_tag(),super::d660_defer_tz(),super::d660_defer_any()),
        (false,false,true,true));
}

#[test]
fn d660_tz_col182_late_fallback_boundary(){
    super::bake_knobs();let _flag=Flag::new("D660_DEFER_TZ","1");let cols=columns();
    let eligible:Vec<_>=cols.iter().filter(|cp|cp.emax==31&&!(cp.dn&&cp.m>121)).map(|cp|cp.col).collect();
    let segment=|lo,hi|cols[lo..hi].iter().filter(|cp|cp.emax==31&&!(cp.dn&&cp.m>121)).count();
    eprintln!("D660_TZ_ELIGIBLE_PARSED columns={} includes182={} segments=[{},{},{},{},{}]",eligible.len(),eligible.contains(&182),
        segment(0,37),segment(37,97),segment(97,120),segment(120,183),segment(183,cols.len()));
    assert_eq!(eligible.len(),159,"parsed ordinary/emax31 census");
    assert!(eligible.contains(&181)&&!eligible.contains(&182));
    for ci in[181usize,182,183]{
        let cp=&cols[ci];let mut b=B::new();b.allow_booth=false;let f=layout(&mut b);
        b.begin();apply(&mut b,&f,cp,&f.suffix,&f.loans);let tape=b.end();
        let boxes=tape.iter().filter(|g|matches!(g,G::DeferredErase(..))).count();
        let expected=usize::from(cp.emax==31&&!(cp.dn&&cp.m>121));
        assert_eq!(boxes,expected,"column{ci} DeferredErase count");assert_eq!(b.deferred_recipe_live(),expected);
        eprintln!("D660_TZ_LATE_BOUNDARY col={ci} smax={:?} m={} emax={} dn={} controlled={} boxes={boxes}",
            cp.smax,cp.m,cp.emax,cp.dn,cp.dn&&cp.m>121);
    }
}
