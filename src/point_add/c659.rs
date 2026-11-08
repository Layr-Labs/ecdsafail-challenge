//! Complete production three-role traversal, selected only by C659_THREE_ROLES=1.
//! Every tape is captured and immediately consumed on the same owning Builder.
use super::builder::B;
use super::c659_column::Column;
use super::frogdrop_col::{ColPar,Fd};
use super::k5_ph_ports::{self,Context,Traversal};
use super::pointadd_frogdrop::{self as point,Trav};
use super::sum_size::SumSize;
use crate::circuit::{QubitId,NO_QUBIT};
use std::collections::BTreeSet;
#[path="c659_selectors.rs"] mod selectors;

#[derive(Clone,Copy,Debug)]
pub(crate) struct Roles {pub tag:QubitId,pub cut:QubitId,pub toggle:Toggle}
#[derive(Clone,Copy,Debug)]
pub(crate) enum Toggle { Pool(QubitId), P0(QubitId), Evicted }
impl From<QubitId> for Toggle {fn from(q:QubitId)->Self{Self::Pool(q)}}
impl Toggle {
    pub(crate) fn lane(self)->QubitId {match self{Self::Pool(q)|Self::P0(q)=>q,Self::Evicted=>panic!("C658_DROP: evicted toggle used as lane")}}
    pub(crate) fn port(self)->QubitId {match self{Self::Pool(q)|Self::P0(q)=>q,Self::Evicted=>NO_QUBIT}}
}
pub(crate) fn drop_enabled()->bool {std::env::var("C658_DROP").as_deref()==Ok("1")}
pub(crate) fn retained(q:QubitId)->bool {!drop_enabled()||q!=NO_QUBIT}
pub(crate) fn enabled()->bool {std::env::var("C659_THREE_ROLES").as_deref()==Ok("1")}
pub(crate) fn t23_enabled()->bool {std::env::var("C658_T23").as_deref()==Ok("1")}
fn configuration(b:&B) {
    assert!(enabled());
    for &(key,value) in super::BAKED_KNOBS {
        if key!="C659_THREE_ROLES"&&!key.starts_with("C658_") {assert_eq!(std::env::var(key).as_deref(),Ok(value),"C659 requires exact inherited selector {key}");}
    }
    for &key in selectors::OTHER_SOURCE_SELECTORS {
        assert!(std::env::var_os(key).is_none(),"C659 incompatible diagnostic {key}");
    }
    assert!(!b.force_unitary_and&&!b.no_rows,"C659 requires original measurement/row recipes");
    super::direct_traversal::require_admitted();
}
fn meta(fd:&Fd)->SumSize {
    assert_eq!((fd.sy.len(),fd.sx.len(),fd.q.len()),(7,5,128));
    assert_eq!(fd.cnt,fd.q[121..128]);
    SumSize{y:fd.sy.as_slice().try_into().unwrap(),sum:fd.sx.as_slice().try_into().unwrap()}
}
fn column_view<'a>(fd:&'a Fd,meta:&'a SumSize,pool:&[QubitId],terminal:&'a[QubitId],pass:Traversal)->Column<'a> {
    assert_eq!((pool.len(),terminal.len()),(if drop_enabled(){2}else{3},258));
    let t23=t23_enabled()&&!pass.has_payload();
    let toggle=if drop_enabled(){if t23{Toggle::P0(terminal[0])}else{Toggle::Evicted}}else{Toggle::Pool(if t23{terminal[0]}else{pool[2]})};
    let roles=Roles{tag:pool[0],cut:pool[1],toggle};
    let ports:Vec<_>=fd.ring.iter().chain(&fd.q).chain(&meta.y).chain(&meta.sum).chain(terminal)
        .copied().chain([fd.ph]).chain(pool.iter().copied()).collect();
    let width=if drop_enabled(){658}else{659};
    assert_eq!(ports.len(),width);assert_eq!(ports.iter().copied().collect::<BTreeSet<_>>().len(),width);
    Column{meta,roles,ring:&fd.ring,q:&fd.q,phase:fd.ph,
        compact:pass.has_payload().then_some(terminal),dirty:terminal,
        clean_external:if pass.has_payload(){&[]}else if t23{&terminal[1..2]}else{&terminal[..2]}}
}
fn middle(b:&mut B,col:&Column<'_>,cp:&ColPar,pass:Traversal) {
    super::direct_payload::k4_complete::source_parameters(cp);
    let fixed=(!cp.hr||cp.tt)&&cp.sy.1<=96&&!(cp.sw||cp.psw||cp.dl||cp.dq)
        &&!(std::env::var("C658_WP4").as_deref()==Ok("1")
            &&(cp.col>=139||(cfg!(test)&&cp.col==1
                &&std::env::var("R14_C1_BAD_FORM").as_deref()==Ok("1"))));
    if fixed {super::r13prof::mk(b,10);super::c659_fixed::run(b,col,cp);super::r13prof::mk(b,10);return;}
    let r=col.roles;
    let c=Context{size:col.meta,ring:col.ring,q:col.q,ph:col.phase,
        roles:k5_ph_ports::Roles{activity:r.tag,flight:r.cut,mask:r.toggle.port()},
        dirty:col.dirty,y_bounds:(cp.sy.0.max(1),cp.sy.1.min(128)),qb:30,
        clean_external:col.clean_external,excluded:&[],traversal:pass};
    c.check();
    if cp.hr {
        super::r13prof::mk(b,11);super::k5_ph_controller::k4_bridge::HrCaller::new(cp,cp.col,pass,&c,col.compact).append_forward(b);super::r13prof::mk(b,11);
    }
    if cp.sw {super::r13prof::mk(b,12);col.xor_switch(b,r.tag);super::r13prof::mk(b,12);}
    if cp.ht {
        super::r13prof::mk(b,13);col.xor_ht_activity(b,cp,r.tag);
        super::c659_ht::run(b,col,cp,pass);
        col.xor_ht_activity(b,cp,r.tag);super::r13prof::mk(b,13);
        super::r13prof::mk(b,14);let mut controller=super::k5_ph_controller::Controller::new(&c,pass.has_payload());
        let mut kernels=super::k5_ph_controller::RawKernels::new(cp,super::k5_ph_controller::NoPayload);
        controller.ht_finish(b,&mut kernels,true);assert!(controller.is_raw());super::r13prof::mk(b,14);
    }
}
/// Capture K1 without early cancellation, restore every flag even on unwind,
/// then play exactly once on the SAME builder which owns its RowAdd recipes.
fn finish(b:&mut B,col:&Column<'_>,cp:&ColPar) {
    use super::frogdrop::direct_map::k1_map3::{Context,Roles3,Boundary};
    assert!(!b.force_unitary_and&&!b.no_rows);
    let context=Context{ring:col.ring,q:col.q,y:&col.meta.y,sum:&col.meta.sum,
        roles:Roles3{tag:col.roles.tag,cut:col.roles.cut,toggle:col.roles.toggle.port()},
        ph:col.phase,payload:col.compact,terminal_loans:col.clean_external,boundary:Boundary::Stage10Returned};
    let old=(b.cancel_simple_pairs,b.cancel_commuting_pairs,b.global_cancel);
    b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;b.global_cancel=false;
    let captured=std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        b.begin();super::direct_map_tail_counter::finish3(b,&context,cp);b.end()
    }));
    (b.cancel_simple_pairs,b.cancel_commuting_pairs,b.global_cancel)=old;
    match captured {Ok(tape)=>b.play(&tape,false),Err(panic)=>std::panic::resume_unwind(panic)}
}
/// Always construct forward; ONLY this complete caller decides one inversion.
fn column(b:&mut B,fd:&Fd,cp:&ColPar,pool:&[QubitId],terminal:&[QubitId],pass:Traversal) {
    #[cfg(test)]
    if cp.col==1&&std::env::var("R14_C1_CAPTURE_SOURCE").as_deref()==Ok("1") {
        let (image,receipt)=super::k1_complete_io::snapshot();
        eprintln!("C1_SOURCE_CAPTURE pass={pass:?} ops={}",receipt.ops);
        C1_SOURCE.with(|cell|cell.borrow_mut().push((pass,image)));
        if pass==Traversal::T4 {std::panic::panic_any("C1_SOURCE_DONE");}
    }
    let metadata=meta(fd);let col=column_view(fd,&metadata,pool,terminal,pass);
    let depth=b.k5_bridge_recording_depth();
    let pid=match pass{Traversal::T1=>1,Traversal::T2=>2,Traversal::T3=>3,Traversal::T4=>4};
    b.begin();super::r13prof::ctx(b,pid,cp.col as u32);
    super::r13prof::mk(b,1);col.enter_middle(b,cp);super::r13prof::mk(b,1);super::r13prof::mk(b,2);middle(b,&col,cp,pass);super::r13prof::mk(b,2);
    super::r13prof::mk(b,3);col.leave_middle(b,cp);super::r13prof::mk(b,3);
    super::r13prof::mk(b,4);finish(b,&col,cp);super::r13prof::mk(b,4);
    super::r13prof::ctx(b,pid,cp.col as u32);
    let tape=b.end();assert_eq!(b.k5_bridge_recording_depth(),depth);
    b.play(&tape,matches!(pass,Traversal::T2|Traversal::T4));
}
#[cfg(test)]
thread_local! {static C1_SOURCE:std::cell::RefCell<Vec<(Traversal,super::k1_complete_io::Image)>>=const{std::cell::RefCell::new(Vec::new())};}
#[cfg(test)]
pub(crate) fn c1_take_source()->Vec<(Traversal,super::k1_complete_io::Image)>{
    C1_SOURCE.with(|cell|std::mem::take(&mut *cell.borrow_mut()))
}
#[cfg(test)]
pub(crate) fn r14_k5_pair_column_for_fixture(b:&mut B,fd:&Fd,cp:&ColPar,
    pool:&[QubitId],terminal:&[QubitId],pass:Traversal){
    column(b,fd,cp,pool,terminal,pass);
}
#[cfg(test)]
pub(crate) fn r14_k5_pair_endpoint_for_fixture(b:&mut B,fd:&Fd,b0:Option<&ColPar>,
    last:&ColPar,pool:&[QubitId],terminal:&[QubitId],pass:Traversal){
    endpoint(b,fd,b0,last,pool,terminal,pass);
}
#[cfg(test)]
pub(crate) fn pair_column_for_fixture(b:&mut B,fd:&Fd,cp:&ColPar,
    pool:&[QubitId],terminal:&[QubitId],pass:Traversal){
    column(b,fd,cp,pool,terminal,pass);
}
fn endpoint(b:&mut B,fd:&Fd,b0:Option<&ColPar>,last:&ColPar,pool:&[QubitId],terminal:&[QubitId],pass:Traversal) {
    let metadata=meta(fd);let col=column_view(fd,&metadata,pool,terminal,pass);
    let pid=match pass{Traversal::T1=>1,Traversal::T2=>2,Traversal::T3=>3,Traversal::T4=>4};
    b.begin();super::r13prof::ctx(b,pid,999);super::r13prof::mk(b,5);super::c659_endpoint::finish(b,&col,b0,last);super::r13prof::mk(b,5);super::r13prof::ctx(b,pid,999);let tape=b.end();
    b.play(&tape,matches!(pass,Traversal::T2|Traversal::T4));
}
pub(crate) fn forward(b:&mut B,x:&[QubitId],terminal:&[QubitId],pass:Traversal)->Trav {
    assert!(matches!(pass,Traversal::T1|Traversal::T3));configuration(b);
    assert_eq!((x.len(),terminal.len()),(256,258));
    let mut ring=x.to_vec();ring.extend(b.alloc_n(1));let q=b.alloc_n(128);let cnt=q[121..128].to_vec();
    let fd=Fd{ring,q,sy:b.alloc_n(7),sx:b.alloc_n(5),ph:b.alloc(),cnt};
    let pool=b.alloc_n(if drop_enabled(){2}else{3}); // C658_DROP removes exactly the final physical lane.
    let mut t=Trav{fd,pool,parked:vec![]};
    b.r14_pass=if matches!(pass,Traversal::T3){3}else{1};
    b.r14_roles=[terminal[0],terminal[1],if drop_enabled(){if matches!(pass,Traversal::T3){terminal[0]}else{NO_QUBIT}}else{t.pool[2]}];
    b.x(t.fd.ring[256]);
    let (cols,b0,last)=point::col_pars(&super::frogdrop_sched::from_text(point::SCHED_FROGDROP));
    for cp in &cols {
        super::frogdrop_col::set_counter_epoch(&mut t.fd,cp.col);
        column(b,&t.fd,cp,&t.pool,terminal,pass);
    }
    endpoint(b,&t.fd,b0.as_ref(),&last,&t.pool,terminal,pass);
    point::final_consts(b,&t.fd);t.parked=point::parked_of(&t);b.free_n(&t.parked);b.r14_pass=0;t
}
pub(crate) fn inverse(b:&mut B,mut t:Trav,terminal:&[QubitId],pass:Traversal) {
    assert!(matches!(pass,Traversal::T2|Traversal::T4));configuration(b);
    assert_eq!((t.pool.len(),terminal.len()),(if drop_enabled(){2}else{3},258));
    b.r14_pass=if matches!(pass,Traversal::T2){2}else{4};
    b.r14_roles=[terminal[0],terminal[1],if drop_enabled(){if matches!(pass,Traversal::T2){terminal[0]}else{NO_QUBIT}}else{t.pool[2]}];
    for &q in &t.parked {b.acquire(q);}point::final_consts(b,&t.fd);
    let (cols,b0,last)=point::col_pars(&super::frogdrop_sched::from_text(point::SCHED_FROGDROP));
    endpoint(b,&t.fd,b0.as_ref(),&last,&t.pool,terminal,pass);
    for cp in cols.iter().rev() {
        super::frogdrop_col::set_counter_epoch(&mut t.fd,cp.col);
        column(b,&t.fd,cp,&t.pool,terminal,pass);
    }
    b.x(t.fd.ring[256]);b.free_n(&t.fd.ring[256..]);b.free_n(&t.fd.q);
    b.free_n(&t.fd.sy);b.free_n(&t.fd.sx);b.free(t.fd.ph);b.free_n(&t.pool);b.r14_pass=0;b.r14_roles=[NO_QUBIT;3];
}

#[cfg(test)]
#[test]
fn r14_int_drop_t3_c0_slice() {
    assert!(t23_enabled(),"run with C658_T23=1");
    let run=|drop:bool|{
        std::env::set_var("C658_DROP",if drop{"1"}else{"0"});
        let mut b=B::new();b.global_cancel=false;b.cancel_simple_pairs=false;b.cancel_commuting_pairs=false;
        let mut ring=b.alloc_n(256);let terminal=b.alloc_n(258);ring.extend(b.alloc_n(1));
        let q=b.alloc_n(128);let sy=b.alloc_n(7);let sx=b.alloc_n(5);let ph=b.alloc();
        let pool=b.alloc_n(if drop{2}else{3});assert_eq!(b.width(),if drop{658}else{659});
        let mut fd=Fd{ring,q:q.clone(),sy,sx,ph,cnt:q[121..128].to_vec()};
        let (cols,_,_)=point::col_pars(&super::frogdrop_sched::from_text(point::SCHED_FROGDROP));
        let cp=&cols[0];super::frogdrop_col::set_counter_epoch(&mut fd,cp.col);
        b.r14_pass=3;b.r14_roles=[terminal[0],terminal[1],if drop{terminal[0]}else{pool[2]}];
        column(&mut b,&fd,cp,&pool,&terminal,Traversal::T3);b.flush_global();b.ops
    };
    let a=run(false);let b=run(true);assert_eq!(a.len(),b.len());let n=a.len();
    for (i,(mut x,y)) in a.into_iter().zip(b).enumerate(){
        for q in [&mut x.q_control2,&mut x.q_control1,&mut x.q_target]{
            assert_ne!(*q,QubitId(658),"removed lane named at op {i}");
            if *q!=NO_QUBIT&&q.0>658{q.0-=1;}
        }
        assert_eq!(x,y,"renumbering mismatch at op {i}");
    }
    eprintln!("R14_INT_DROP_T3_C0_EQ width_a=659 width_b=658 ops={n} removed_id=658");
}
