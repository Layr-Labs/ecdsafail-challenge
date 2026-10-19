//! Test-only bounded V-form capture; never proceeds into middle sessions.
use super::{builder::{B,G},frogdrop_col::{rec,ColScr}};
use crate::circuit::QubitId;
use std::cell::RefCell;
thread_local!{static FORMS:RefCell<(Vec<G>,Vec<Vec<G>>)>=const{RefCell::new((Vec::new(),Vec::new()))};}
pub(crate) fn capture(v:&[G],p:&[Vec<G>]){assert!(p.is_empty()||p.len()==5);FORMS.with(|x|*x.borrow_mut()=(v.to_vec(),p.to_vec()));}
pub(crate) use super::q675_support::parked_forms;
#[test]
fn q675_actual_vform_inactive_cancellation(){
    super::bake_knobs();let(mut b,fd,pool,dirty)=super::q675_layout_tests::ports(258);
    let(mut cols,_,_)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let cp=&mut cols[36];cp.n=258;cp.h=1;
    let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
    super::q675_layout_tests::vform_mode(true);
    super::midg::middle(&mut b,&fd,cp,&sc,None,&[],&mut |_|panic!("V capture entered production session"));
    super::q675_layout_tests::vform_mode(false);assert_eq!(b.op_count(),0);
    let(v,parked)=FORMS.with(|x|std::mem::take(&mut *x.borrow_mut()));
    eprintln!("Q675_V_CAPTURE col={} sy={:?} sz={:?} unparked_G={} parked_G={:?} Q={}",cp.col,cp.sy,cp.sz,v.len(),parked.iter().map(|p|p.len()).collect::<Vec<_>>(),b.width());
    let mut lanes=0;
    for(fam,p)in parked.iter().enumerate(){
        b.ops.clear();b.tof=0;b.play(&v,false);b.play(p,true);
        for batch in 0..4 {for guards in 0..3 {for noise in 0..3 {
            let mut q=vec![0u64;675];
            for(i,&d)in dirty.iter().enumerate(){q[d.0 as usize]=match noise{0=>0,1=>u64::MAX,_=>0x9e3779b97f4a7c15u64.rotate_left(i as u32)};}
            q[fd.ph.0 as usize]=if guards==2&&cp.sw{0x5555555555555555}else{u64::MAX};
            q[sc.sw.0 as usize]=if guards==0{0}else if guards==1{u64::MAX}else if cp.sw{0xaaaaaaaaaaaaaaaa}else{0};
            for lane in 0..64 {
                let sy=batch*64+lane;let sz=(lane*17+batch*31)%256;
                for i in 0..8{q[fd.sy[i].0 as usize]|=(((sy>>i)&1)as u64)<<lane;q[sc.sz[i].0 as usize]|=(((sz>>i)&1)as u64)<<lane;}
                for i in 0..128{if (i+lane+noise)%3==0{q[fd.q[i].0 as usize]|=1<<lane;}}
                // Inactive payload may be arbitrary; all actual ring lanes are data.
                for(i,&r)in fd.ring.iter().enumerate(){if (i*13+lane*7+noise)%5<2{q[r.0 as usize]|=1<<lane;}}
            }
            receipt_audit(&b.ops);let out=run_tape(&b.ops,675,&q,noise);
            let diff:Vec<_>=out.q.iter().zip(&q).enumerate().filter(|(_, (a,b))|a!=b).map(|(i,(a,b))|(i,a^b)).collect();
            assert!(diff.is_empty()&&out.phase==0,"inactive mismatch family={fam} noise={noise} batch={batch} guards={guards} diff={diff:?} phase={:x}",out.phase);lanes+=64;
        }}}
    }
    eprintln!("Q675_V_INACTIVE_PASS lanes={lanes} full_quantum=true phase_zero=true production=false");
}

pub(crate) fn take()->(Vec<G>,Vec<Vec<G>>){FORMS.with(|x|std::mem::take(&mut *x.borrow_mut()))}

#[derive(Clone)]
struct Tape{mode:usize,state:u64,bytes:usize}
impl sha3::digest::XofReader for Tape{fn read(&mut self,b:&mut[u8]){for x in b{
    self.state^=self.state<<13;self.state^=self.state>>7;self.state^=self.state<<17;
    *x=match self.mode{0=>0,1=>255,_=>self.state as u8};self.bytes+=1;
}}}
pub(crate) fn run_tape(ops:&[crate::circuit::Op],nq:usize,input:&[u64],mode:usize)->super::tests_frogdrop::Sim{
    use crate::circuit::{OperationType as K,NO_BIT};use sha3::digest::XofReader;
    let(_,nb,_,_)=crate::circuit::analyze_ops(ops.iter());let mut tape=Tape{mode,state:0x9e3779b97f4a7c15,bytes:0};let mut oracle_tape=tape.clone();
    let mut sim=crate::sim::Simulator::new(nq,(nb as usize).max(1),&mut tape);sim.qubits.copy_from_slice(input);
    for(i,b)in sim.bits.iter_mut().enumerate(){*b=0xd1b54a32d192ed03u64.rotate_left(i as u32);}
    let mut bits=sim.bits.clone();sim.apply_iter(ops.iter());
    // Independent unitary oracle: at each measurement pair, prove the exact AND support,
    // replace HMR+repair by its coherent CCX erase, and account for private receipt/RNG/stats.
    let mut q=input.to_vec();let mut t=0;let mut cliff=0;let mut i=0;
    while i<ops.len(){let o=&ops[i];assert_eq!(o.c_condition,NO_BIT);let a=o.q_control1.0 as usize;let c=o.q_control2.0 as usize;let z=o.q_target.0 as usize;
        match o.kind{
            K::X=>q[z]^=u64::MAX,
            K::CX=>{q[z]^=q[a];cliff+=64;},
            K::CCX=>{q[z]^=q[a]&q[c];t+=64;},
            K::Swap=>{q.swap(z,a);cliff+=64;},
            K::Hmr=>{let repair=&ops[i+1];assert_eq!(repair.kind,K::CZ);assert_eq!(repair.c_condition,o.c_target);
                let product=q[repair.q_target.0 as usize]&q[repair.q_control1.0 as usize];
                assert_eq!(q[z],product,"HMR support failed at op {i}, target={z}");q[z]^=product;
                let mut bytes=[0u8;8];oracle_tape.read(&mut bytes);let m=u64::from_le_bytes(bytes);bits[o.c_target.0 as usize]=m;cliff+=64+m.count_ones()as u64;i+=1;
            },
            _=>panic!("unhandled oracle operation {:?} at {i}",o.kind),
        }i+=1;
    }
    assert_eq!(sim.qubits,q);assert_eq!(sim.phase,0);assert_eq!(sim.bits,bits);
    assert_eq!(sim.stats.toffoli_gates,t);assert_eq!(sim.stats.clifford_gates,cliff);
    let answer=super::tests_frogdrop::Sim{q:sim.qubits,phase:sim.phase,tof:sim.stats.toffoli_gates};
    assert_eq!((tape.state,tape.bytes),(oracle_tape.state,oracle_tape.bytes));answer
}
#[test]
fn q675_measured_and_repair_negative(){
    let mut b=B::new();let q=b.alloc_n(3);b.and_c(q[0],q[1],q[2]);b.and_u(q[0],q[1],q[2]);
    let input=vec![u64::MAX,0x5555555555555555,0];
    for mode in 0..3{let good=run_tape(&b.ops,3,&input,mode);assert_eq!(good.q,input);}
    let bad=&b.ops[..b.ops.len()-1];let mut tape=Tape{mode:1,state:1,bytes:0};let mut sim=crate::sim::Simulator::new(3,1,&mut tape);
    sim.qubits=input.clone();sim.apply_iter(bad.iter());assert_eq!(sim.qubits,input);assert_eq!(sim.phase,0x5555555555555555);
    eprintln!("Q675_MEASURED_AND_NEGATIVE_PASS missing_CZ_phase_detected=32 classical_data_unchanged=true");
}

pub(crate) fn receipt_audit(ops:&[crate::circuit::Op])->usize{
    use crate::circuit::{OperationType as K,NO_BIT};let mut count=0;
    for(i,o)in ops.iter().enumerate(){
        if o.kind==K::Hmr{assert_eq!(o.c_target.0,0);assert_eq!(o.c_condition,NO_BIT);let next=&ops[i+1];assert_eq!(next.kind,K::CZ);assert_eq!(next.c_condition,o.c_target);count+=1;}
        if o.c_condition!=NO_BIT{assert!(i>0);assert_eq!(o.kind,K::CZ);assert_eq!(ops[i-1].kind,K::Hmr);assert_eq!(ops[i-1].c_target,o.c_condition);}
        assert!(matches!(o.kind,K::X|K::CX|K::CCX|K::Swap|K::Hmr|K::CZ));
    }count
}

#[test]
fn q675_vform_resource_census(){
    use std::io::Write;
    super::bake_knobs();let path=std::env::var("Q675_VFORM_COST_ROWS").expect("fresh cost census path");
    let mut output=std::fs::OpenOptions::new().write(true).create_new(true).open(path).unwrap();
    let(mut b,mut fd,pool,dirty)=super::q675_layout_tests::ports(258);
    let(mut cols,_,_)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
    let mut records=0;let mut max_ops=0;let mut crossing=0;
    for cp in &mut cols {cp.n=258;cp.h=1;
        let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,cp.kp,cp.qb,cp.tail,cp.sz.1>255);
        super::q675_layout_tests::vform_mode(true);
        super::midg::middle(&mut b,&fd,cp,&sc,None,&[],&mut |_|panic!("cost census entered production"));
        super::q675_layout_tests::vform_mode(false);assert!(b.ops.is_empty());
        let(v,parked)=take();if parked.len()==5{crossing+=1;}
        for(family,r)in std::iter::once((-1isize,&v)).chain(parked.iter().enumerate().map(|(i,r)|(i as isize,r))){for inverse in[false,true]{
            b.tof=0;b.ops.clear();b.play(r,inverse);let hmr=b.ops.iter().filter(|o|o.kind==crate::circuit::OperationType::Hmr).count();
            assert!(b.ops.len()<5_000_000,"bounded local record cap");assert_eq!(b.width(),675);max_ops=max_ops.max(b.ops.len());
            writeln!(output,"{{\"col\":{},\"family\":{family},\"inverse\":{inverse},\"ops\":{},\"T\":{},\"HMR\":{hmr},\"hr\":{},\"ht\":{},\"tt\":{},\"sw\":{},\"dl\":{},\"dq\":{},\"dn\":{}}}",cp.col,b.ops.len(),b.tof,cp.hr,cp.ht,cp.tt,cp.sw,cp.dl,cp.dq,cp.dn).unwrap();records+=1;
        }}
        b.ops.clear();b.tof=0;std::mem::swap(&mut fd.sy,&mut fd.sx);
    }
    assert_eq!(cols.len(),203);assert_eq!(crossing,108);
    eprintln!("Q675_VFORM_COST_PASS columns=203 crossing={crossing} records={records} max_local_ops={max_ops} Q=675 geometry_only_no_arithmetic_validation=true");
}

#[test]
fn q675_baseline_middle_resource_control(){
    use std::io::Write;super::bake_knobs();
    let path=std::env::var("Q675_MIDDLE_CONTROL_ROWS").expect("fresh local control census");
    let mut out=std::fs::OpenOptions::new().write(true).create_new(true).open(path).unwrap();
    for with_payload in[false,true]{
        let(mut b,fd,pool,dirty)=super::q675_layout_tests::ports(259);
        let(cols,_,_)=super::pointadd_frogdrop::col_pars(&super::frogdrop_sched::from_text(super::pointadd_frogdrop::SCHED_FROGDROP));
        let cp=&cols[36];assert_eq!(cp.n,259);let sc=ColScr::carve_col(&pool,&fd.sx,&dirty,24,23,40,false);
        let pl=super::pointadd_frogdrop::pl_col(&dirty,&fd,&pool);let mut stage=2;let mut prior_ops=0;let mut prior_t=0;
        super::midg::middle(&mut b,&fd,cp,&sc,with_payload.then_some(&pl),&[],&mut |b|{
            stage+=1;assert!(b.ops.len()<5_000_000,"bounded one-column control");
            writeln!(out,"{{\"col\":36,\"n\":259,\"with_payload\":{with_payload},\"stage\":{stage},\"ops\":{},\"T\":{}}}",b.ops.len()-prior_ops,b.tof-prior_t).unwrap();prior_ops=b.ops.len();prior_t=b.tof;true
        });
        assert_eq!(b.width(),676);eprintln!("Q675_LOCAL_CONTROL col=36 n=259 payload={with_payload} ops={} T={} Q=676 source_geometry_control_only=true",b.ops.len(),b.tof);
    }
}
