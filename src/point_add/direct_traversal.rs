//! Direct E7/S5 traversal dispatch. Source-only until width/cost admission.
//! Fd is a transport descriptor here: sy=E7, sx=S5, pool=four roles.
use super::builder::B;
use super::direct_column::Column;
use super::frogdrop_col::{Fd,ColPar};
use super::outer_size::Roles;
use super::sum_size::SumSize;
use crate::circuit::QubitId;

pub(crate) fn enabled()->bool{std::env::var("C660_DIRECT_SUM").as_deref()==Ok("1")}

thread_local!{
    static TERMINAL_LOANS:std::cell::Cell<Option<[QubitId;2]>>=const{std::cell::Cell::new(None)};
}
/// The only callers are point_add_pl's complete T2/T3 epochs. Compact
/// terminal W uses P[2..258], so P0/P1 are returned zero before/after each.
/// This capability is explicit; an arbitrary dirty slice is never assumed
/// to contain clean bits. It carries no input-dependent control or width.
pub(crate) fn with_terminal_loans<R>(b:&mut B,p:&[QubitId],body:impl FnOnce(&mut B)->R)->R{
    if !enabled(){return body(b);}
    assert!(super::payload::splice258::enabled()&&p.len()==258);
    let old=TERMINAL_LOANS.with(|c|c.replace(Some([p[0],p[1]])));
    assert!(old.is_none());
    struct Restore(Option<[QubitId;2]>);
    impl Drop for Restore{fn drop(&mut self){TERMINAL_LOANS.with(|c|c.set(self.0));}}
    let _restore=Restore(old);body(b)
}
fn loans(payload:Option<&[QubitId]>)->Vec<QubitId>{
    let loans=TERMINAL_LOANS.with(|c|c.get());
    assert!(payload.is_none()||loans.is_none(),"terminal zeros cannot cross a payload epoch");
    loans.map(|q|q.to_vec()).unwrap_or_default()
}

const SOURCE_AND_COST_ADMITTED:bool=true;
pub(crate) fn require_admitted(){
    assert!(!enabled()||SOURCE_AND_COST_ADMITTED,
        "direct compression remains source-only: complete whole cost admission required");
    if enabled(){
        assert!(!super::frogdrop_col::c660_joint_size());
        assert!(super::frogdrop_col::c665_pool4()&&super::frogdrop_col::c660_sx7_raw());
        assert!(super::frogdrop_col::c660_fixed_banks()&&super::payload::splice258::enabled());
    }
}

fn meta(fd:&Fd)->SumSize{
    assert_eq!((fd.sy.len(),fd.sx.len(),fd.q.len(),fd.cnt.len()),(7,5,128,7));
    assert_eq!(fd.cnt,fd.q[121..128]);
    SumSize{y:fd.sy.as_slice().try_into().unwrap(),sum:fd.sx.as_slice().try_into().unwrap()}
}
fn roles(pool:&[QubitId])->Roles{
    assert_eq!(pool.len(),4);
    Roles{tag:pool[0],cut:pool[1],toggle:pool[2],prefix:pool[3]}
}

pub(crate) fn column(b:&mut B,fd:&Fd,cp:&ColPar,pool:&[QubitId],dirty:&[QubitId],
    payload:Option<&[QubitId]>){
    let meta=meta(fd);let clean_external=loans(payload);
    let col=Column{meta:&meta,roles:roles(pool),ring:&fd.ring,q:&fd.q,
        phase:fd.ph,compact:payload,dirty,clean_external:&clean_external};
    let mut middle=super::direct_middle::DirectMiddle;
    super::direct_column::through_stage10(b,&col,cp,&mut middle);
    super::direct_map_tail_counter::finish(b,&col,cp);
}

pub(crate) fn endpoint(b:&mut B,fd:&Fd,b0:Option<&ColPar>,last:&ColPar,
    pool:&[QubitId],dirty:&[QubitId],payload:Option<&[QubitId]>){
    let meta=meta(fd);let clean_external=loans(payload);
    let col=Column{meta:&meta,roles:roles(pool),ring:&fd.ring,q:&fd.q,
        phase:fd.ph,compact:payload,dirty,clean_external:&clean_external};
    super::direct_endpoint::finish(b,&col,b0,last);
}
