//! Whole-traversal three-owner selection. This one source constant changes
//! allocation and every column/endpoint adapter together; no environment
//! knob is required to select the width-first architecture.
use super::builder::B;
use super::direct_three::Column;
use super::frogdrop_col::{Fd,ColPar};
use super::outer_three::Roles;
use super::sum_size::SumSize;
use crate::circuit::QubitId;
/// Width-first candidate. Official whole-circuit validation remains required.
pub(crate) const WIDTH_FIRST_THREE_ROLES:bool=true;
fn meta(fd:&Fd)->SumSize{
    assert_eq!((fd.sy.len(),fd.sx.len(),fd.q.len(),fd.cnt.len()),(7,5,128,7));
    assert_eq!(fd.cnt,fd.q[121..128]);
    SumSize{y:fd.sy.as_slice().try_into().unwrap(),sum:fd.sx.as_slice().try_into().unwrap()}
}
fn roles(pool:&[QubitId])->Roles{assert_eq!(pool.len(),3);Roles{tag:pool[0],cut:pool[1],work:pool[2]}}
pub(crate) fn column(b:&mut B,fd:&Fd,cp:&ColPar,pool:&[QubitId],dirty:&[QubitId],
    payload:Option<&[QubitId]>,clean_external:&[QubitId]){
    let meta=meta(fd);let column=Column{meta:&meta,roles:roles(pool),ring:&fd.ring,q:&fd.q,
        phase:fd.ph,compact:payload,dirty,clean_external};
    let mut middle=super::middle_three::DirectMiddle;
    super::direct_three::through_stage10(b,&column,cp,&mut middle);
    super::map_three::finish(b,&column,cp);
}
pub(crate) fn endpoint(b:&mut B,fd:&Fd,b0:Option<&ColPar>,last:&ColPar,
    pool:&[QubitId],dirty:&[QubitId],payload:Option<&[QubitId]>,clean_external:&[QubitId]){
    let meta=meta(fd);let column=Column{meta:&meta,roles:roles(pool),ring:&fd.ring,q:&fd.q,
        phase:fd.ph,compact:payload,dirty,clean_external};
    super::endpoint_three::finish(b,&column,b0,last);
}
