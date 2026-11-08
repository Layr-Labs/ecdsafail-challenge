//! Default-off complete K4 digit plus K2 HT-S5 transition bridge.
//! This diagnostic retains Cross's excluded fourth-port metadata at Q660.
//! It neither allocates nor claims a Q659 whole circuit.
use super::*;
use crate::point_add::direct_column::Column;
use crate::point_add::frogdrop_col::ColPar;
use crate::point_add::direct_payload::k4_complete as payload3;

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Traversal { T1,T2,T3,T4 }
impl Traversal {fn has_payload(self)->bool{matches!(self,Self::T1|Self::T4)}}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum EntryEpoch { HtActivityRetainedBeforeDigit }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Error { Column,Traversal,Capture }
fn require(ok:bool,error:Error){if !ok{std::panic::panic_any(error);}}

/// Named original caller entry. A already contains the complete HT predicate;
/// e/m and the excluded fourth role are returned. These are native premises,
/// not facts established by constructing this software value.
pub(crate) struct Entry<'a,'p> {
    column:&'a Column<'p>,cp:&'a ColPar,traversal:Traversal,
}
impl<'a,'p> Entry<'a,'p> {
    pub(crate) fn new(column:&'a Column<'p>,cp:&'a ColPar,traversal:Traversal,
        epoch:EntryEpoch)->Self {
        assert_eq!(epoch,EntryEpoch::HtActivityRetainedBeforeDigit);
        payload3::source_parameters(cp);
        let fixed=(!cp.hr||cp.tt)&&cp.sy.1<=96&&!(cp.sw||cp.psw||cp.dl||cp.dq);
        require(cp.ht&&!fixed,Error::Column);
        require(traversal.has_payload()==column.compact.is_some(),Error::Traversal);
        let entry=Self{column,cp,traversal};let c=entry.cross();
        let raw=column.compact.map(|p|p.iter().copied().chain([column.phase]).collect::<Vec<_>>());
        k2::validate(&c,raw.as_deref());
        entry
    }
    fn cross(&self)->Cross<'_>{
        let col=self.column;let r=col.roles;
        Cross{size:col.meta,ring:col.ring,q:col.q,phase:col.phase,
            roles:crate::point_add::cross_four::Roles{activity:r.tag,flight:r.cut,mask:r.toggle,x128:r.prefix},
            dirty:col.dirty,y_bounds:(self.cp.sy.0.max(1),self.cp.sy.1.min(128)),qb:30,
            clean_external:col.clean_external}
    }
    /// Append forward stage5 inside the caller's enclosing capture. Original
    /// T4 must invert the entire column, including this span, once. The depth
    /// guard does not prove that the outer caller captured a complete column.
    pub(crate) fn append_to_column_capture(self,b:&mut B){
        require(b.k2_k4_recording_depth()>0,Error::Capture);
        require(self.traversal.has_payload()==self.column.compact.is_some(),Error::Traversal);
        let c=self.cross();let r=c.roles;
        let session=self.column.compact.map(|p|payload3::digit_at_boundary3(b,&Context{
            meta:c.size,compact:p,ring:c.ring,q:c.q,phase:c.phase},
            payload3::Roles3{activity:r.activity,flight:r.flight,sign:r.mask},self.cp,
            payload3::EntryBoundary::HtBeforeStage5Arithmetic,c.dirty,&[r.x128]));
        complete_post_digit3(b,&c,self.cp.sz,session,Fault::None);
    }
}

// Literal independently qualified K2 post-digit body, with only its final
// original finish_phase call replaced by K4's strict three-role close wrapper.
// That call remains after both sweeps, coordinate inverses and Q-frame return.
fn complete_post_digit3(b:&mut B,c:&Cross<'_>,zrange:(usize,usize),
    session:Option<direct_payload::Session>,fault:Fault){
    k2::require(98<=zrange.0&&zrange.0<=zrange.1&&zrange.1<=256,k2::GuardCode::Shape,None);
    k2::validate(c,session.as_ref().map(|s|s.raw.as_slice()));
    if let Some(session)=&session {
        k2::require(session.activity==c.roles.activity&&session.phase==c.phase&&session.ht,
            k2::GuardCode::Frame,None);
    }
    let r=c.roles;let raw=session.as_ref().map(|s|s.raw.as_slice()).unwrap_or(&[]);
    let d=k2_bank(c,raw,&[]);
    let zflip=super::direct_frame::z_lane_record(b,c.size,c.ring,r.mask,zrange,256,None,&d);
    b.play(&zflip,false);
    let qframe=super::normalized_cross_s5::run_k2(b,c,fault);
    let Some(session)=session else {qframe.close(b,c,fault);return;};
    let host=qframe.host(c);
    let sum_lo=zrange.0.saturating_add(c.y_bounds.0).max(226)-226;
    assert!(sum_lo<=31);let kend=30.min(32-sum_lo);
    let save=k2_save_top_record(b,c,zrange,host,&d);b.play(&save,false);
    // Save exposed the leading ONE. The parent's immediate zflip is omitted.
    for k in 0..kend{
        k2_fetch_first(b,c,k,host,&d);
        let span=(259-k).min(257);
        let t:Vec<_>=(k..k+span).map(|pos|session.raw[258-pos]).collect();
        k2_transition(b,c,&t,&c.ring[..span],Boundary::Y{
            top:258-k,lo:c.y_bounds.0,hi:c.y_bounds.1},&d);
        k2_fetch_first(b,c,k,host,&d);
    }
    b.play(&zflip,false);
    let prev:Vec<_>=session.raw.iter().rev().copied().collect();
    let pr=super::direct_frame::rotate_z_record(b,c.size,&prev,r.mask,zrange,None,true,&d);
    let rr=super::direct_frame::rotate_z_record(b,c.size,c.ring,r.mask,zrange,None,true,&d);
    b.play(&pr,false);b.play(&rr,false);
    for k in 0..kend{
        k2_fetch_correction(b,c,k,sum_lo,host,&d);
        let span=33-sum_lo-k;
        let t:Vec<_>=(0..span).map(|i|prev[(k+258+i)%259]).collect();
        let s:Vec<_>=(0..span).map(|i|c.ring[(256+i)%257]).collect();
        for &q in &t{b.x(q);}
        k2_transition(b,c,&t,&s,Boundary::Sum{top:33-k,lo:sum_lo,hi:31-k},&d);
        for &q in &t{b.x(q);}
        k2_fetch_correction(b,c,k,sum_lo,host,&d);
    }
    b.play(&rr,true);b.play(&pr,true);
    if fault!=Fault::MissingQgFlip { b.play(&zflip,false); }
    b.play(&save,true);qframe.close(b,c,fault);
    payload3::finish_phase3(b,c.size,&session,c.y_bounds,r.mask,&d,&[r.x128],
        payload3::CloseBoundary::PayloadTransitionsReturned);
}
