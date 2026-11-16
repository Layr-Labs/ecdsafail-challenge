//! Complete production three-role traversal, selected only by C659_THREE_ROLES=1.
//! Every tape is captured and immediately consumed on the same owning Builder.
use super::builder::B;
use super::c659_column::Column;
use super::frogdrop_col::{ColPar,Fd};
use super::k5_ph_ports::{self,Context,Traversal};
use super::pointadd_frogdrop::{self as point,Trav};
use super::sum_size::SumSize;
use crate::circuit::QubitId;
use std::collections::BTreeSet;
#[path="c659_selectors.rs"] mod selectors;

#[derive(Clone,Copy,Debug)]
pub(crate) struct Roles {pub tag:QubitId,pub cut:QubitId,pub toggle:QubitId}
pub(crate) fn enabled()->bool {std::env::var("C659_THREE_ROLES").as_deref()==Ok("1")}
fn configuration(b:&B) {
    assert!(enabled());
    for &(key,value) in super::BAKED_KNOBS {
        if key!="C659_THREE_ROLES" {assert_eq!(std::env::var(key).as_deref(),Ok(value),"C659 requires exact inherited selector {key}");}
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
    assert_eq!((pool.len(),terminal.len()),(3,258));
    let roles=Roles{tag:pool[0],cut:pool[1],toggle:pool[2]};
    let ports:Vec<_>=fd.ring.iter().chain(&fd.q).chain(&meta.y).chain(&meta.sum).chain(terminal)
        .copied().chain([fd.ph,roles.tag,roles.cut,roles.toggle]).collect();
    assert_eq!(ports.len(),659);assert_eq!(ports.iter().copied().collect::<BTreeSet<_>>().len(),659);
    Column{meta,roles,ring:&fd.ring,q:&fd.q,phase:fd.ph,
        compact:pass.has_payload().then_some(terminal),dirty:terminal,
        clean_external:if pass.has_payload(){&[]}else{&terminal[..2]}}
}
fn middle(b:&mut B,col:&Column<'_>,cp:&ColPar,pass:Traversal) {
    super::direct_payload::k4_complete::source_parameters(cp);
    let fixed=(!cp.hr||cp.tt)&&cp.sy.1<=96&&!(cp.sw||cp.psw||cp.dl||cp.dq);
    if fixed {super::c659_fixed::run(b,col,cp);return;}
    let r=col.roles;
    let c=Context{size:col.meta,ring:col.ring,q:col.q,ph:col.phase,
        roles:k5_ph_ports::Roles{activity:r.tag,flight:r.cut,mask:r.toggle},
        dirty:col.dirty,y_bounds:(cp.sy.0.max(1),cp.sy.1.min(128)),qb:30,
        clean_external:col.clean_external,excluded:&[],traversal:pass};
    c.check();
    if cp.hr {
        super::k5_ph_controller::k4_bridge::HrCaller::new(cp,cp.col,pass,&c,col.compact).append_forward(b);
    }
    if cp.sw {col.xor_switch(b,r.tag);}
    if cp.ht {
        col.xor_ht_activity(b,cp,r.tag);
        super::c659_ht::run(b,col,cp,pass);
        col.xor_ht_activity(b,cp,r.tag);
        let mut controller=super::k5_ph_controller::Controller::new(&c,pass.has_payload());
        let mut kernels=super::k5_ph_controller::RawKernels::new(cp,super::k5_ph_controller::NoPayload);
        controller.ht_finish(b,&mut kernels,true);assert!(controller.is_raw());
    }
}
/// Capture K1 without early cancellation, restore every flag even on unwind,
/// then play exactly once on the SAME builder which owns its RowAdd recipes.
fn finish(b:&mut B,col:&Column<'_>,cp:&ColPar) {
    use super::frogdrop::direct_map::k1_map3::{Context,Roles3,Boundary};
    assert!(!b.force_unitary_and&&!b.no_rows);
    let context=Context{ring:col.ring,q:col.q,y:&col.meta.y,sum:&col.meta.sum,
        roles:Roles3{tag:col.roles.tag,cut:col.roles.cut,toggle:col.roles.toggle},
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
    if !pass.has_payload() && (36..=119).contains(&cp.col) {
        // T2/T3's compact 256-bit word occupies terminal[2..258].
        // Reserve P0 as the fourth scratch owner for this entire column. The
        // four-role fallback supports no separately advertised external loans.
        assert_eq!((pool.len(), terminal.len()), (3, 258));
        let four = [pool[0], pool[1], pool[2], terminal[0]];
        let dirty = &terminal[1..];
        b.begin();
        let metadata=meta(fd);
        let roles=super::outer_size::Roles{tag:four[0],cut:four[1],toggle:four[2],prefix:four[3]};
        let four_col=super::direct_column::Column{meta:&metadata,roles,ring:&fd.ring,q:&fd.q,
            phase:fd.ph,compact:None,dirty,clean_external:&[]};
        super::direct_column::through_stage10(b,&four_col,cp,&mut super::direct_middle::DirectMiddle);
        // Stage 10 returned its scratch prefix. P0 and P1 are both once
        // again globally zero, so K1 may use its two external row loans.
        let post=column_view(fd,&metadata,pool,terminal,pass);
        finish(b,&post,cp);
        let tape = b.end();
        b.play(&tape, matches!(pass, Traversal::T2));
        return;
    }
    let metadata=meta(fd);let col=column_view(fd,&metadata,pool,terminal,pass);
    let depth=b.k5_bridge_recording_depth();
    b.begin();col.enter_middle(b,cp);middle(b,&col,cp,pass);col.leave_middle(b,cp);finish(b,&col,cp);
    let tape=b.end();assert_eq!(b.k5_bridge_recording_depth(),depth);
    b.play(&tape,matches!(pass,Traversal::T2|Traversal::T4));
}
fn endpoint(b:&mut B,fd:&Fd,b0:Option<&ColPar>,last:&ColPar,pool:&[QubitId],terminal:&[QubitId],pass:Traversal) {
    let metadata=meta(fd);let col=column_view(fd,&metadata,pool,terminal,pass);
    b.begin();super::c659_endpoint::finish(b,&col,b0,last);let tape=b.end();
    b.play(&tape,matches!(pass,Traversal::T2|Traversal::T4));
}
pub(crate) fn forward(b:&mut B,x:&[QubitId],terminal:&[QubitId],pass:Traversal)->Trav {
    assert!(matches!(pass,Traversal::T1|Traversal::T3));configuration(b);
    assert_eq!((x.len(),terminal.len()),(256,258));
    let mut ring=x.to_vec();ring.extend(b.alloc_n(1));let q=b.alloc_n(128);let cnt=q[121..128].to_vec();
    let fd=Fd{ring,q,sy:b.alloc_n(7),sx:b.alloc_n(5),ph:b.alloc(),cnt};
    let pool=b.alloc_n(3); // No fourth physical allocation on this path.
    let mut t=Trav{fd,pool,parked:vec![]};
    b.x(t.fd.ring[256]);
    let (cols,b0,last)=point::col_pars(&super::frogdrop_sched::from_text(point::SCHED_FROGDROP));
    for cp in &cols {
        super::frogdrop_col::set_counter_epoch(&mut t.fd,cp.col);
        column(b,&t.fd,cp,&t.pool,terminal,pass);
    }
    endpoint(b,&t.fd,b0.as_ref(),&last,&t.pool,terminal,pass);
    point::final_consts(b,&t.fd);t.parked=point::parked_of(&t);b.free_n(&t.parked);t
}
pub(crate) fn inverse(b:&mut B,mut t:Trav,terminal:&[QubitId],pass:Traversal) {
    assert!(matches!(pass,Traversal::T2|Traversal::T4));configuration(b);
    assert_eq!((t.pool.len(),terminal.len()),(3,258));
    for &q in &t.parked {b.acquire(q);}point::final_consts(b,&t.fd);
    let (cols,b0,last)=point::col_pars(&super::frogdrop_sched::from_text(point::SCHED_FROGDROP));
    endpoint(b,&t.fd,b0.as_ref(),&last,&t.pool,terminal,pass);
    for cp in cols.iter().rev() {
        super::frogdrop_col::set_counter_epoch(&mut t.fd,cp.col);
        column(b,&t.fd,cp,&t.pool,terminal,pass);
    }
    b.x(t.fd.ring[256]);b.free_n(&t.fd.ring[256..]);b.free_n(&t.fd.q);
    b.free_n(&t.fd.sy);b.free_n(&t.fd.sx);b.free(t.fd.ph);b.free_n(&t.pool);
}
