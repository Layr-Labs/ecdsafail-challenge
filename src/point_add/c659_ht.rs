//! Production K2/K4 HT closure with exactly three scalar ports.
//! Arithmetic bodies are retained from the qualified K2 donor; x128 was
//! diagnostic-only metadata in those bodies and does not exist in this ABI.
use super::builder::{B,G};
use super::c659_column::Column;
use super::direct_payload::{self,Context};
use super::direct_payload::k4_complete as payload3;
use super::frogdrop_col::ColPar;
use super::k5_ph_ports::Traversal;
use super::sum_size::SumSize;
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;
#[derive(Clone,Copy)]
struct Roles {activity:QubitId,flight:QubitId,mask:QubitId}
struct Cross<'a>{size:&'a SumSize,ring:&'a[QubitId],q:&'a[QubitId],phase:QubitId,
 roles:Roles,dirty:&'a[QubitId],y_bounds:(usize,usize),qb:usize,clean_external:&'a[QubitId],payload:bool}
fn wp2_base(c:&Cross<'_>)->bool{c.payload&&std::env::var("C658_WP2").as_deref()==Ok("1")}
/// The single WP2 gate admits every site. Explicit 0 disables one site;
/// STAGED=1 makes unset subgates off for isolated price experiments.
fn wp2_site(c:&Cross<'_>,key:&str)->bool{
    wp2_base(c)&&match std::env::var(key).as_deref(){
        Ok("0")=>false,Ok("1")=>true,
        _=>std::env::var("C658_WP2_STAGED").as_deref()!=Ok("1"),
    }
}
fn wp2(c:&Cross<'_>)->bool{wp2_site(c,"C658_WP2_K2C")}
fn record(b:&mut B,f:impl FnOnce(&mut B))->Vec<G>{b.begin();f(b);b.end()}

fn eq(word:&[QubitId],v:usize)->Vec<(QubitId,bool)>{
    word.iter().enumerate().map(|(i,&q)|(q,v>>i&1==0)).collect()
}

fn cover(word:&[QubitId],mut lo:usize,hi:usize)->Vec<Vec<(QubitId,bool)>>{
    assert!(lo<=hi&&hi<=1usize<<word.len());let mut out=vec![];
    while lo<hi{
        let mut free=if lo==0{word.len()}else{lo.trailing_zeros()as usize};
        free=free.min(word.len());while lo+(1usize<<free)>hi{free-=1;}
        out.push((free..word.len()).map(|i|(word[i],lo>>i&1==0)).collect());
        lo+=1usize<<free;
    }out
}

fn bank(c:&Cross<'_>,raw:&[QubitId],extra:&[QubitId])->Vec<QubitId>{
    let r=c.roles;
    let mut used:BTreeSet<_>=c.size.y.iter().chain(&c.size.sum).copied()
        .chain([c.phase,r.activity,r.flight,r.mask]).filter(|q|super::c659::retained(*q))
        .chain(extra.iter().copied()).collect();
    c.dirty.iter().chain(c.ring).chain(c.q).chain(raw).copied()
        .filter(|q|used.insert(*q)).collect()
}

fn literal(b:&mut B,terms:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    assert!(!terms.iter().any(|p|p.0==target));
    let mut used:BTreeSet<_>=terms.iter().map(|p|p.0).chain([target]).collect();
    let d:Vec<_>=dirty.iter().copied().filter(|q|used.insert(*q)).collect();
    assert!(d.len()>=terms.len().saturating_sub(2));
    mc_xor(b,terms,target,&[],&d);
}

fn sum_le(b:&mut B,c:&Cross<'_>,limit:usize,dirty:&[QubitId]){
    assert!(limit<=31);let r=c.roles;
    for mut term in cover(&c.size.sum,0,limit+1){
        term.push((r.activity,false));literal(b,&term,r.mask,dirty);
    }
}

fn sum_eq(b:&mut B,c:&Cross<'_>,value:usize,dirty:&[QubitId]){
    assert!(value<=31);let mut term=eq(&c.size.sum,value);
    term.push((c.roles.activity,false));literal(b,&term,c.roles.mask,dirty);
}

fn gathered(b:&mut B,address:&[QubitId],leaves:&[(usize,QubitId)],
    body:impl FnOnce(&mut B,QubitId)){
    assert!(!leaves.is_empty());
    let mut swaps=vec![];
    let root=super::midg::swap_tree(address,leaves,address.len(),&mut swaps);
    for &(q,l,r)in &swaps{b.cswap(q,l,r);}
    body(b,root);
    for &(q,l,r)in swaps.iter().rev(){b.cswap(q,l,r);}
}

#[cfg(test)]
pub(crate) fn r14_fixture_k2g(b:&mut B,word:&[QubitId],target:&[QubitId],
    source:&[QubitId],cut:QubitId,lo:usize,hi:usize,top:usize,
    dirty:&[QubitId],use_gathered:bool)->Vec<G>{
    assert_eq!(target.len(),source.len());assert!(lo<=hi&&hi<1usize<<word.len());
    let keys:Vec<_>=(lo..=hi).filter(|&v|v<=top&&top-v<target.len()).collect();
    assert!(!keys.is_empty());
    b.begin();
    if use_gathered{
        let t:Vec<_>=keys.iter().map(|&v|(v,target[top-v])).collect();
        let s:Vec<_>=keys.iter().map(|&v|(v,source[top-v])).collect();
        gathered(b,word,&t,|b,rt|gathered(b,word,&s,|b,rs|{
            for mut guard in cover(word,keys[0],keys[keys.len()-1]+1){
                guard.extend([(cut,false),(rs,false)]);literal(b,&guard,rt,dirty);
            }
        }));
    }else{for &v in &keys{
        let mut term=eq(word,v);term.extend([(cut,false),(source[top-v],false)]);
        literal(b,&term,target[top-v],dirty);
    }}
    b.end()
}

fn arithmetic_bank(c:&Cross<'_>)->Vec<QubitId>{let r=c.roles;
    let mut seen:BTreeSet<_>=c.size.y.iter().chain(&c.size.sum).copied()
        .chain(c.clean_external.iter().copied())
        .chain([c.phase,r.activity,r.flight,r.mask,c.q[127]]).filter(|q|super::c659::retained(*q)).collect();
    c.dirty.iter().chain(c.ring).chain(c.q).copied().filter(|q|seen.insert(*q)).collect()
}
fn lit(b:&mut B,c:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]){
    assert!(!c.iter().any(|p|p.0==target));let mut seen=BTreeSet::new();
    let d:Vec<_>=dirty.iter().copied().filter(|q|*q!=target&&!c.iter().any(|p|p.0==*q)&&seen.insert(*q)).collect();
    mc_xor(b,c,target,&[],&d);
}
fn xor_terms(b:&mut B,t:&[Vec<(QubitId,bool)>],out:QubitId,extra:&[(QubitId,bool)],d:&[QubitId]){
    for term in t{let mut all=term.clone();all.extend_from_slice(extra);lit(b,&all,out,d);}
}
fn cell(b:&mut B,s:QubitId,t:QubitId,x:QubitId,inverse:bool){
    if inverse{b.ccx(x,t,s);b.cx(s,x);b.cx(s,t);}
    else{b.cx(s,t);b.cx(s,x);b.ccx(x,t,s);}
}

fn normal_decision(b:&mut B,enable:QubitId,e:QubitId,t:QubitId,x:QubitId,d:&[QubitId]){
    b.cx(enable,e);lit(b,&[(enable,false),(t,false),(x,false)],e,d);
}

fn witness(b:&mut B,c:&Cross<'_>,k:usize,d:&[QubitId])->Vec<G>{
 let r=c.roles;let positive=cover(&c.size.sum,0,32-k);let negative=cover(&c.size.sum,32-k,32);
 fn price(t:&[Vec<(QubitId,bool)>])->usize{t.iter().map(|x|match x.len()+1{0|1=>0,2=>1,n=>4*(n-2)}).sum()}
 let complement=price(&positive)<price(&negative);let terms=if complement{positive}else{negative};
 record(b,|b|for(a,t)in[(r.activity,r.flight),(r.flight,r.activity)]{
  if complement{b.cx(a,t);}xor_terms(b,&terms,t,&[(a,false)],d);
 })
}

mod k2 { use super::*;
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
        .chain([c.phase,r.activity,r.flight,r.mask]).filter(|q|super::super::c659::retained(*q)) {
        require(used.insert(q),GuardCode::Alias,Some(q));
    }
    if let Some(raw)=raw {
        require(raw.len()==259&&raw.last()==Some(&c.phase),GuardCode::Shape,None);
        for &q in &raw[..258] { require(used.insert(q),GuardCode::Alias,Some(q)); }
        require(c.clean_external.is_empty(),GuardCode::Loans,None);
    } else {
        require(c.clean_external.len()==2||super::super::c659::t23_enabled()&&c.clean_external.len()==1,GuardCode::Loans,None);
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
            .chain([r.activity,r.flight,r.mask,c.phase]).filter(|q|super::super::c659::retained(*q)) {
            require(used.insert(q),GuardCode::Alias,Some(q));
        }
        if wp2_site(c,"C658_WP2_K2D")&&fault==Fault::None{
            let first=128-c.y_bounds.1;let d=arithmetic_bank(c);
            return super::super::normalized_cross_arithmetic::ph_controller::natural_divide_inplace_wf(
                b,t,c.q,first,r.activity,r.flight,&c.size.sum,k,&d);
        }
        let first=128-c.y_bounds.1;let d=arithmetic_bank(c);
        b.begin();let guard=witness(b,c,k,&d);b.play(&guard,false);
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
    roles:[QubitId;4],loans:Vec<QubitId>,bounds:(usize,usize),qb:usize }
impl Binding { fn of(c:&Cross<'_>)->Self { let r=c.roles;Self{q:c.q.to_vec(),ring:c.ring.to_vec(),
    y:c.size.y.to_vec(),sum:c.size.sum.to_vec(),roles:[c.phase,r.activity,r.flight,r.mask],
    loans:c.clean_external.to_vec(),bounds:c.y_bounds,qb:c.qb} } }

/// Only K2 creates this token. It binds the actual forward capture, not just
/// an open flag or an interchangeable 128/129-element slice.
pub(crate) struct S5QFrame { binding:Binding,tape:Vec<G>,host:QubitId }
impl S5QFrame {
    pub(crate) fn open(b:&mut B,c:&Cross<'_>,fault:Fault)->Self {
        require(c.q.len()==128,GuardCode::Shape,None);
        b.begin();for &e in &c.size.y { b.x(e); }
        for (k,&e) in c.size.y.iter().enumerate() {
            crate::point_add::frogdrop::crot_up(b,e,c.q,1usize<<k);
        }
        for &e in &c.size.y { b.x(e); }let tape=b.end();
        if fault==Fault::WrongEntry129 {
            // One-sided bad frame: wrong entry while the owned return stays
            // the original Q128 capture. A whole Q129 pair is not this mutant.
            panic!("parent Q129 frame is not a three-role product operation");
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

}
use k2::{Fault,Division,Contract,S5QFrame};
pub(crate) fn ring_record(b:&mut B,c:&Cross<'_>)->Vec<G>{
    assert_eq!(c.ring.len(),257);b.begin();
    for &e in &c.size.y{b.x(e);}
    for(k,&e)in c.size.y.iter().enumerate(){
        crate::point_add::frogdrop::crot_up(b,e,c.ring,257-(1usize<<k));
    }
    for &e in &c.size.y{b.x(e);}b.end()
}
pub(crate) fn natural_target(c:&Cross<'_>,k:usize)->Vec<QubitId>{
    assert!(k<30);
    (0..129).map(|j|c.ring[256-k-j]).collect()
}
pub(crate) fn run_k2(b:&mut B,c:&Cross<'_>,fault:Fault)
    ->S5QFrame {

    let qframe=S5QFrame::open(b,c,fault);
    let ring=ring_record(b,c);b.play(&ring,false);
    let arithmetic=Division::new(Contract::default());
    for k in (0..30).rev() {
        let target=natural_target(c,k);
        let tape=arithmetic.record(b,c,&target,k,fault);b.play(&tape,false);
    }
    b.play(&ring,true);qframe
}
#[derive(Clone,Copy)]
enum Boundary{Y{top:usize,lo:usize,hi:usize},Sum{top:usize,lo:usize,hi:usize}}
impl Boundary{
    fn ports<'a>(&self,c:&'a Cross<'_>)->(&'a [QubitId],usize,usize,usize){
        match *self{
            Self::Y{top,lo,hi}=>(&c.size.y,top-1,lo-1,hi-1),
            Self::Sum{top,lo,hi}=>(&c.size.sum,top,lo,hi),
        }
    }
}

fn k2_bank(c:&Cross<'_>,raw:&[QubitId],extra:&[QubitId])->Vec<QubitId>{
    let held:Vec<_>=extra.iter().copied().chain([c.q[127]])
        .chain(c.clean_external.iter().copied()).collect();
    bank(c,raw,&held)
}

fn k2_save_top_record(b:&mut B,c:&Cross<'_>,zrange:(usize,usize),host:QubitId,dirty:&[QubitId])->Vec<G>{
    k2::require(host==c.q[127],k2::GuardCode::HostBinding,Some(host));
    let r=c.roles;
    if wp2_site(c,"C658_WP2_SB"){
        let floor=zrange.0;let cap=(floor+127).min(zrange.1);
        let overflow=zrange.1.saturating_sub(floor+127);assert!(overflow<=16);
        let address=super::direct_frame::z_byte7_record(b,c.size,dirty);
        let mut leaves:Vec<_>=(floor..=cap).map(|z|((z-1)%128,c.ring[z-1])).collect();
        leaves.sort_unstable_by_key(|x|x.0);
        return record(b,|b|{
            b.play(&address,false);
            gathered(b,&c.size.y,&leaves,|b,root|b.cswap(r.activity,root,host));
            for z in cap+1..=cap+overflow{
                let low=c.ring[z-129];let high=c.ring[z-1];
                let terms=byte7_z_terms(c.size,z);
                folded_cswap_terms(b,&terms,r.activity,low,host,dirty);
                folded_cswap_terms(b,&terms,r.activity,high,host,dirty);
            }
            b.play(&address,true);
        });
    }
    let address=super::direct_frame::z_byte_record(b,c.size,r.mask,dirty);
    let word:Vec<_>=c.size.y.iter().copied().chain([r.mask]).collect();
    let leaves:Vec<_>=(zrange.0..=zrange.1).map(|z|(z-1,c.ring[z-1])).collect();
    record(b,|b|{
        b.play(&address,false);
        gathered(b,&word,&leaves,|b,root|b.cswap(r.activity,root,host));
        b.play(&address,true);
    })
}

fn byte7_z_terms(meta:&SumSize,z:usize)->Vec<Vec<(QubitId,bool)>>{
    let (lo,hi)=match z{98..=127=>(0,z-97),128=>(0,31),129..=225=>(0,32),
        226..=255=>(z-225,32),256=>(31,32),_=>return vec![]};
    let eq=eq(&meta.y,(z-1)%128);
    cover(&meta.sum,lo,hi).into_iter().map(|mut t|{t.extend(eq.iter().copied());t}).collect()
}
fn folded_cswap_terms(b:&mut B,terms:&[Vec<(QubitId,bool)>],a:QubitId,
    x:QubitId,y:QubitId,dirty:&[QubitId]){
    b.cx(y,x);
    for term in terms{let mut c=term.clone();c.extend([(a,false),(x,false)]);
        literal(b,&c,y,dirty);
    }
    b.cx(y,x);
}

fn k2_fetch_first(b:&mut B,c:&Cross<'_>,k:usize,host:QubitId,dirty:&[QubitId]){
    let r=c.roles;
    let leaves:Vec<_>=(c.y_bounds.0..=c.y_bounds.1)
        .map(|y|(y-1,c.ring[256-y-k])).collect();
    gathered(b,&c.size.y,&leaves,|b,root|{
        let d=k2_bank(c,&[],&[root]);
        if wp2_site(c,"C658_WP2_FETCH"){
            folded_sum_cswap(b,c,31-k,true,root,host,&d);
            folded_sum_cswap(b,c,31-k,false,root,r.flight,&d);
            folded_sum_cswap(b,c,31-k,true,root,host,&d);
        }else{
            sum_eq(b,c,31-k,&d);b.cswap(r.mask,root,host);sum_eq(b,c,31-k,&d);
            sum_le(b,c,31-k,&d);b.cswap(r.mask,root,r.flight);sum_le(b,c,31-k,&d);
            sum_eq(b,c,31-k,&d);b.cswap(r.mask,root,host);sum_eq(b,c,31-k,&d);
        }
    });
    // The parent bank is deliberately not a stateful cache across the tree.
    let _=dirty;
}
fn folded_sum_cswap(b:&mut B,c:&Cross<'_>,limit:usize,exact:bool,
    x:QubitId,y:QubitId,dirty:&[QubitId]){
    let terms=if exact{vec![eq(&c.size.sum,limit)]}else{cover(&c.size.sum,0,limit+1)};
    folded_cswap_terms(b,&terms,c.roles.activity,x,y,dirty);
}

/// At the S5 rotation boundary the in-range K2C return restores tag=A.
/// On active shots A=1, so its complement is a clean byte carry for this
/// captured frame. The tag is restored before the intervening body.
pub(crate) fn rotate_tag_record(b:&mut B,meta:&SumSize,cycle:&[QubitId],tag:QubitId,
    zrange:(usize,usize),inverse:bool,dirty:&[QubitId])->Vec<G>{
    let frame=super::direct_frame::rotate_z_record(b,meta,cycle,tag,zrange,None,inverse,dirty);
    record(b,|b|{b.x(tag);b.play(&frame,false);b.x(tag);})
}

fn k2_transition(b:&mut B,c:&Cross<'_>,target:&[QubitId],source:&[QubitId],
    boundary:Boundary,dirty:&[QubitId]){
    if wp2(c){k2_transition_ttk(b,c,target,source,boundary,dirty);return;}
    assert_eq!(target.len(),source.len());assert!(!target.is_empty());
    let r=c.roles;let(word,top,lo,hi)=boundary.ports(c);
    assert!(lo<=hi&&hi<=top);
    let span=target.len().min(top-lo+1);
    let(t,s)=(&target[..span],&source[..span]);
    let mut used=BTreeSet::new();
    assert!(t.iter().chain(s).copied().chain([r.activity,r.flight,r.mask]).filter(|q|super::c659::retained(*q))
        .all(|q|used.insert(q)));
    assert!(word.iter().all(|q|!used.contains(q)));
    // Queries may borrow any operand transiently; each dirty chain restores
    // it before the next MAJ cell. They do NOT read the borrowed A carry.
    let d=k2_bank(c,target,&[]);
    assert!(dirty.iter().all(|q|*q!=r.activity&&*q!=r.flight&&*q!=r.mask));
    b.x(r.activity); // e=>original A, hence conditional carry zero.
    for i in 0..span{let x=if i==0{r.activity}else{s[i-1]};
        b.cx(s[i],t[i]);b.cx(s[i],x);b.ccx(x,t[i],s[i]);}
    let mut next=lo;
    while next<=hi&&top-next>=span{
        let mut term=eq(word,next);term.push((r.flight,false));
        literal(b,&term,r.mask,&d);next+=1;
    }
    for i in(0..span).rev(){let x=if i==0{r.activity}else{s[i-1]};
        b.ccx(x,t[i],s[i]);b.cx(s[i],x);b.cx(s[i],t[i]);
        if next<=hi&&next<=top-i{
            b.ccx(r.mask,s[i],t[i]);
            while next<=hi&&next<=top-i{
                let mut term=eq(word,next);term.push((r.flight,false));
                literal(b,&term,r.mask,&d);next+=1;
            }
            b.ccx(r.mask,x,t[i]);
        }else{
            b.cx(x,s[i]);b.ccx(r.mask,s[i],t[i]);b.cx(x,s[i]);
        }
    }
    assert_eq!(next,hi+1);b.cx(r.flight,r.mask);b.x(r.activity);
}

/// K2C tag/cut code with a carry-free TTK ladder. `tag=A^m, cut=e` on
/// the four reachable chain states; no operation touches the mask lane.
/// The indexed correction uses two physical swap trees and an explicit
/// in-set guard because omitted keys still route to a tree leaf.
fn k2_transition_ttk(b:&mut B,c:&Cross<'_>,target:&[QubitId],source:&[QubitId],
    boundary:Boundary,dirty:&[QubitId]){
    assert_eq!(target.len(),source.len());assert!(!target.is_empty());
    let r=c.roles;let(word,top,lo,hi)=boundary.ports(c);
    assert!(lo<=hi&&hi<=top);
    let span=target.len().min(top-lo+1);
    let(t,s)=(&target[..span],&source[..span]);
    let mut used=BTreeSet::new();
    assert!(t.iter().chain(s).copied().chain([r.activity,r.flight,r.mask]).filter(|q|super::c659::retained(*q)).all(|q|used.insert(q)));
    assert!(word.iter().all(|q|!used.contains(q)));
    let d=k2_bank(c,target,&[]);
    assert!(dirty.iter().all(|q|*q!=r.activity&&*q!=r.flight&&*q!=r.mask));
    for i in 1..span{b.cx(s[i],t[i]);}
    for i in (1..span-1).rev(){b.cx(s[i],s[i+1]);}
    for i in 0..span-1{b.ccx(s[i],t[i],s[i+1]);}
    let mut next=lo;
    while next<=hi&&top-next>=span{
        let mut term=eq(word,next);term.push((r.flight,false));
        literal(b,&term,r.activity,&d);next+=1;
    }
    for i in (0..span).rev(){
        while next<=hi&&next<=top-i{
            let mut term=eq(word,next);term.push((r.flight,false));
            literal(b,&term,r.activity,&d);next+=1;
        }
        literal(b,&[(r.flight,false),(r.activity,true),(s[i],false)],t[i],&d);
        if i>0{b.ccx(s[i-1],t[i-1],s[i]);}
    }
    assert_eq!(next,hi+1);
    for i in 1..span-1{b.cx(s[i],s[i+1]);}
    for i in 1..span{b.cx(s[i],t[i]);}
    let low=lo.max(top+1-span);let high=hi.min(top);
    if low<=high{
        let tl:Vec<_>=(low..=high).map(|v|(v,t[top-v])).collect();
        let sl:Vec<_>=(low..=high).map(|v|(v,s[top-v])).collect();
        gathered(b,word,&tl,|b,rt|gathered(b,word,&sl,|b,rs|{
            for mut condition in cover(word,low,high+1){
                condition.extend([(r.flight,false),(rs,false)]);
                literal(b,&condition,rt,&d);
            }
        }));
    }
    b.cx(r.flight,r.activity);
}

#[cfg(test)]
pub(crate) fn r14_fixture_k2_transition(b:&mut B,size:&SumSize,source:&[QubitId],
    q:&[QubitId],phase:QubitId,roles:[QubitId;3],dirty:&[QubitId],
    target:&[QubitId],boundary:(bool,usize,usize,usize),new:bool)->Vec<G>{
    let c=Cross{size,ring:source,q,phase,
        roles:Roles{activity:roles[0],flight:roles[1],mask:roles[2]},dirty,
        y_bounds:(1,128),qb:30,clean_external:&[],payload:false};
    let bound=if boundary.0{Boundary::Y{top:boundary.1,lo:boundary.2,hi:boundary.3}}
        else{Boundary::Sum{top:boundary.1,lo:boundary.2,hi:boundary.3}};
    b.begin();if new{k2_transition_ttk(b,&c,target,source,bound,dirty)}
        else{k2_transition(b,&c,target,source,bound,dirty)}b.end()
}

#[cfg(test)]
pub(crate) fn r14_fixture_k2_division(b:&mut B,size:&SumSize,ring:&[QubitId],
    q:&[QubitId],phase:QubitId,roles:[QubitId;3],dirty:&[QubitId],
    y_bounds:(usize,usize),k:usize,new:bool)->Vec<G>{
    let c=Cross{size,ring,q,phase,
        roles:Roles{activity:roles[0],flight:roles[1],mask:roles[2]},dirty,
        y_bounds,qb:30,clean_external:&[],payload:new};
    let target=natural_target(&c,k);
    k2::Division::new(k2::Contract::default()).record(b,&c,&target,k,k2::Fault::None)
}

#[cfg(test)]
pub(crate) fn r14_fixture_save_top(b:&mut B,size:&SumSize,ring:&[QubitId],
    q:&[QubitId],phase:QubitId,roles:[QubitId;3],dirty:&[QubitId],
    zrange:(usize,usize),new:bool)->Vec<G>{
    let c=Cross{size,ring,q,phase,
        roles:Roles{activity:roles[0],flight:roles[1],mask:roles[2]},dirty,
        y_bounds:(1,128),qb:30,clean_external:&[],payload:new};
    k2_save_top_record(b,&c,zrange,q[127],dirty)
}

#[cfg(test)]
pub(crate) fn r14_fixture_fetch(b:&mut B,size:&SumSize,ring:&[QubitId],
    q:&[QubitId],phase:QubitId,roles:[QubitId;3],dirty:&[QubitId],
    y_bounds:(usize,usize),k:usize,sum_lo:usize,correction:bool,new:bool)->Vec<G>{
    let c=Cross{size,ring,q,phase,
        roles:Roles{activity:roles[0],flight:roles[1],mask:roles[2]},dirty,
        y_bounds,qb:30,clean_external:&[],payload:new};
    b.begin();if correction{k2_fetch_correction(b,&c,k,sum_lo,q[127],dirty)}
        else{k2_fetch_first(b,&c,k,q[127],dirty)}b.end()
}

#[cfg(test)]
pub(crate) fn r14_fixture_k2_first_step(b:&mut B,size:&SumSize,ring:&[QubitId],
    q:&[QubitId],phase:QubitId,roles:[QubitId;3],dirty:&[QubitId],
    raw:&[QubitId],k:usize,new:bool)->Vec<G>{
    let c=Cross{size,ring,q,phase,
        roles:Roles{activity:roles[0],flight:roles[1],mask:roles[2]},dirty,
        y_bounds:(1,128),qb:30,clean_external:&[],payload:new};
    b.begin();
    let target=natural_target(&c,k);
    let divide=k2::Division::new(k2::Contract::default()).record(b,&c,&target,k,k2::Fault::None);
    b.play(&divide,false);
    let d=k2_bank(&c,&[],&[]);let host=q[127];
    k2_fetch_first(b,&c,k,host,&d);
    let span=(259-k).min(257);
    let t:Vec<_>=(k..k+span).map(|pos|raw[258-pos]).collect();
    k2_transition(b,&c,&t,&ring[..span],Boundary::Y{top:258-k,lo:1,hi:128},&d);
    k2_fetch_first(b,&c,k,host,&d);
    b.end()
}

#[cfg(test)]
pub(crate) fn r14_fixture_post_digit(b:&mut B,size:&SumSize,ring:&[QubitId],
    q:&[QubitId],phase:QubitId,roles:[QubitId;3],dirty:&[QubitId],
    raw:&[QubitId],y_bounds:(usize,usize),zrange:(usize,usize),new:bool)->Vec<G>{
    let c=Cross{size,ring,q,phase,
        roles:Roles{activity:roles[0],flight:roles[1],mask:roles[2]},dirty,
        y_bounds,qb:30,clean_external:&[],payload:new};
    let session=direct_payload::Session{raw:raw.to_vec(),activity:roles[0],phase,ht:true,finish_flag:None};
    b.begin();complete_post_digit3(b,&c,zrange,Some(session),Fault::None);b.end()
}

fn k2_fetch_correction(b:&mut B,c:&Cross<'_>,k:usize,sum_lo:usize,host:QubitId,dirty:&[QubitId]){
    let r=c.roles;
    let leaves:Vec<_>=(sum_lo..=31-k).map(|s|{
        let gap=31-s;
        (s,if gap==k{host}else{c.ring[(gap+256-k)%257]})
    }).collect();
    if wp2_site(c,"C658_WP2_FETCH"){
        gathered(b,&c.size.sum,&leaves,|b,root|
            folded_sum_cswap(b,c,31-k,false,root,r.flight,dirty));
    }else{
        sum_le(b,c,31-k,dirty);
        gathered(b,&c.size.sum,&leaves,|b,root|b.cswap(r.mask,root,r.flight));
        sum_le(b,c,31-k,dirty);
    }
}
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
    let sb=wp2_site(c,"C658_WP2_SB");
    let tagrot=sb&&wp2_site(c,"C658_WP2_ROT_TAG");
    let floor=zrange.0;let overflow=zrange.1.saturating_sub(floor+127);
    let zflip=if sb{super::direct_frame::z_lane7_record(b,c.size,c.ring,floor,overflow,256,None,&d)}
        else{super::direct_frame::z_lane_record(b,c.size,c.ring,r.mask,zrange,256,None,&d)};
    b.play(&zflip,false);
super::r13prof::mk(b,92);let qframe=run_k2(b,c,fault);super::r13prof::mk(b,92);
    let Some(session)=session else {qframe.close(b,c,fault);return;};super::r13prof::mk(b,93);
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
    let pr=if tagrot{rotate_tag_record(b,c.size,&prev,r.activity,zrange,true,&d)}
        else if sb{super::direct_frame::rotate_z7_record(b,c.size,&prev,floor,overflow,true,&d)}
        else{super::direct_frame::rotate_z_record(b,c.size,&prev,r.mask,zrange,None,true,&d)};
    let rr=if tagrot{rotate_tag_record(b,c.size,c.ring,r.activity,zrange,true,&d)}
        else if sb{super::direct_frame::rotate_z7_record(b,c.size,c.ring,floor,overflow,true,&d)}
        else{super::direct_frame::rotate_z_record(b,c.size,c.ring,r.mask,zrange,None,true,&d)};
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
    b.play(&save,true);qframe.close(b,c,fault);super::r13prof::mk(b,93);
    let flag=if wp2_site(c,"C658_WP2_FLAG"){r.flight}else{r.mask};
    super::r13prof::mk(b,94);payload3::finish_phase3(b,c.size,&session,c.y_bounds,flag,&d,&[],
        payload3::CloseBoundary::PayloadTransitionsReturned);super::r13prof::mk(b,94);
}

pub(crate) fn run(b:&mut B,col:&Column<'_>,cp:&ColPar,pass:Traversal){
 assert!(cp.ht);assert_eq!(pass.has_payload(),col.compact.is_some());
 assert!(b.k5_bridge_recording_depth()>0);
 let r=col.roles;let c=Cross{size:col.meta,ring:col.ring,q:col.q,phase:col.phase,
 roles:Roles{activity:r.tag,flight:r.cut,mask:r.toggle.port()},dirty:col.dirty,
 y_bounds:(cp.sy.0.max(1),cp.sy.1.min(128)),qb:30,clean_external:col.clean_external,
 payload:pass.has_payload()};
 let raw=col.compact.map(|p|p.iter().copied().chain([col.phase]).collect::<Vec<_>>());
 k2::validate(&c,raw.as_deref());
 super::r13prof::mk(b,90);let session=col.compact.map(|p|{
     let ctx=Context{meta:c.size,compact:p,ring:c.ring,q:c.q,phase:c.phase};
     if payload3::two_role_ready(){
         payload3::digit_at_boundary2(b,&ctx,
             payload3::Roles2{activity:r.tag,flight:r.cut},cp,
             payload3::EntryBoundary::HtBeforeStage5Arithmetic,c.dirty,&[])
     }else{
         payload3::digit_at_boundary3(b,&ctx,
             payload3::Roles3{activity:r.tag,flight:r.cut,sign:r.toggle.lane()},cp,
             payload3::EntryBoundary::HtBeforeStage5Arithmetic,c.dirty,&[])
     }
 });super::r13prof::mk(b,90);
 complete_post_digit3(b,&c,cp.sz,session,Fault::None);
}
