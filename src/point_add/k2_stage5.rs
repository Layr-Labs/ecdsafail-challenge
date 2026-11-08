//! K2-only S01 arithmetic and private retained Q128 frame.
//! Parent/K3 code is unchanged. This defines a diagnostic, not a product switch.
use super::*;

#[derive(Clone,Copy,Debug,Default,PartialEq,Eq)]
pub(crate) enum Diagnostic { #[default] Parent, K2 }
#[derive(Clone,Copy,Debug,Default,PartialEq,Eq)]
pub(crate) enum Fault { #[default] None, WrongEntry129, OmitQReturn, MissingQgFlip, CarryDecision }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Site { S01, H01, H02, C07, C13 }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Frame { S5Q128, Parent129, Controller129, NativeHrQ128 }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Carry { InternalFlightDecisionMask, ParentFourth, None }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum Source { Unparked, Parked }
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) struct Contract { pub site:Site,pub frame:Frame,pub carry:Carry,pub source:Source }
impl Default for Contract { fn default()->Self { Self{site:Site::S01,frame:Frame::S5Q128,
    carry:Carry::InternalFlightDecisionMask,source:Source::Unparked} } }

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum GuardCode { Site, Frame, Carry, Source, Shape, Alias, Loans, FrameBinding, HostBinding }
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) struct GuardViolation { pub site:&'static str,pub code:GuardCode,pub wire:Option<QubitId> }
pub(crate) fn require(ok:bool,code:GuardCode,wire:Option<QubitId>) {
    if !ok { std::panic::panic_any(GuardViolation{site:"K2/S01",code,wire}); }
}

pub(crate) fn validate(c:&Cross<'_>,raw:Option<&[QubitId]>) {
    require(c.q.len()==128&&c.ring.len()==257&&c.qb==30&&c.size.y.len()==7&&c.size.sum.len()==5
        &&1<=c.y_bounds.0&&c.y_bounds.0<=c.y_bounds.1&&c.y_bounds.1<=128,GuardCode::Shape,None);
    let r=c.roles;let mut used=BTreeSet::new();
    for q in c.q.iter().chain(c.ring).chain(&c.size.y).chain(&c.size.sum).copied()
        .chain([c.phase,r.activity,r.flight,r.mask,r.x128]) {
        require(used.insert(q),GuardCode::Alias,Some(q));
    }
    if let Some(raw)=raw {
        require(raw.len()==259&&raw.last()==Some(&c.phase),GuardCode::Shape,None);
        for &q in &raw[..258] { require(used.insert(q),GuardCode::Alias,Some(q)); }
        require(c.clean_external.is_empty(),GuardCode::Loans,None);
    } else {
        require(c.clean_external.len()==2,GuardCode::Loans,None);
        for &q in c.clean_external { require(used.insert(q),GuardCode::Alias,Some(q)); }
    }
}

pub(crate) struct Division { contract:Contract }
impl Division {
    pub(crate) fn new(contract:Contract)->Self {
        require(contract.site==Site::S01,GuardCode::Site,None);
        require(contract.frame==Frame::S5Q128,GuardCode::Frame,None);
        require(contract.carry==Carry::InternalFlightDecisionMask,GuardCode::Carry,None);
        require(contract.source==Source::Unparked,GuardCode::Source,None);
        Self{contract}
    }
    /// Natural Divide/Inplace only. Flight is zero on narrowed activity and
    /// mask globally zero; every inverse must consume the full forward image.
    pub(crate) fn record(&self,b:&mut B,c:&Cross<'_>,t:&[QubitId],k:usize,fault:Fault)->Vec<G> {
        require(self.contract==Contract::default(),GuardCode::Frame,None);
        require(c.q.len()==128&&t.len()==129&&c.qb==30&&k<30
            &&1<=c.y_bounds.0&&c.y_bounds.0<=c.y_bounds.1&&c.y_bounds.1<=128,GuardCode::Shape,None);
        let r=c.roles;let mut used=BTreeSet::new();
        for q in t.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum).copied()
            .chain([r.activity,r.flight,r.mask,c.phase,r.x128]) {
            require(used.insert(q),GuardCode::Alias,Some(q));
        }
        let first=128-c.y_bounds.1;let d=bank(c);
        b.begin();let guard=witness(b,c,Gate::Natural(k),&d);b.play(&guard,false);
        for &q in t { b.x(q); }
        for i in first..128 { cell(b,c.q[i],t[i],if i==first{r.flight}else{c.q[i-1]},false); }
        normal_decision(b,r.activity,r.mask,t[128],c.q[127],&d);
        // Deliberately reintroduce the removed old decision transfer at its
        // real location for the bounded negative control, only at k=0.
        if fault==Fault::CarryDecision&&k==0 { b.ccx(r.activity,r.flight,r.mask); }
        b.ccx(r.mask,c.q[127],t[128]);
        for i in (first..128).rev() { let x=if i==first{r.flight}else{c.q[i-1]};
            cell(b,c.q[i],t[i],x,true);b.cx(c.q[i],x);b.ccx(r.mask,x,t[i]);b.cx(c.q[i],x);
        }
        b.cx(r.mask,r.flight);b.ccx(r.activity,r.flight,r.mask);
        for &q in t { b.x(q); }
        b.cswap(r.activity,t[128],r.flight);b.play(&guard,true);b.end()
    }
}

#[derive(Clone,Debug,PartialEq,Eq)]
struct Binding { q:Vec<QubitId>,ring:Vec<QubitId>,y:Vec<QubitId>,sum:Vec<QubitId>,
    roles:[QubitId;5],loans:Vec<QubitId>,bounds:(usize,usize),qb:usize }
impl Binding { fn of(c:&Cross<'_>)->Self { let r=c.roles;Self{q:c.q.to_vec(),ring:c.ring.to_vec(),
    y:c.size.y.to_vec(),sum:c.size.sum.to_vec(),roles:[c.phase,r.activity,r.flight,r.mask,r.x128],
    loans:c.clean_external.to_vec(),bounds:c.y_bounds,qb:c.qb} } }

/// Only K2 creates this token. It binds the actual forward capture, not just
/// an open flag or an interchangeable 128/129-element slice.
pub(crate) struct S5QFrame { binding:Binding,tape:Vec<G>,host:QubitId }
impl S5QFrame {
    pub(crate) fn open(b:&mut B,c:&Cross<'_>,fault:Fault)->Self {
        require(c.q.len()==128,GuardCode::Shape,None);
        b.begin();for &e in &c.size.y { b.x(e); }
        for (k,&e) in c.size.y.iter().enumerate() {
            super::super::frogdrop::crot_up(b,e,c.q,1usize<<k);
        }
        for &e in &c.size.y { b.x(e); }let tape=b.end();
        if fault==Fault::WrongEntry129 {
            // One-sided bad frame: wrong entry while the owned return stays
            // the original Q128 capture. A whole Q129 pair is not this mutant.
            let wrong=super::super::normalized_cross_frame::q_record(b,c);b.play(&wrong,false);
        } else { b.play(&tape,false); }
        Self{binding:Binding::of(c),tape,host:c.q[127]}
    }
    pub(crate) fn host(&self,c:&Cross<'_>)->QubitId {
        require(self.binding==Binding::of(c),GuardCode::FrameBinding,None);
        require(self.host==c.q[127],GuardCode::HostBinding,Some(self.host));self.host
    }
    pub(crate) fn close(self,b:&mut B,c:&Cross<'_>,fault:Fault) {
        self.host(c);if fault!=Fault::OmitQReturn { b.play(&self.tape,true); }
    }
}
