//! SOURCE-ONLY reserve. No registration, compilation, or circuit execution.
//!
//! Four scalar roles A/e/mask/membership plus one conditionally-zero carry.
//! The physical source top may be arbitrary: the logical bit R-1 is ONE,
//! and every logical source bit >=R is ZERO. A one-cell lookahead restores
//! the top cell before reading its virtual carry, without a saved-top lane.
//!
//! A must already include the immutable band/sum guard. Off-A, e may hold
//! the skipped-activity witness and carry/mask may be arbitrary. A globally
//! zero membership role gives M=>A. A conditional membership role instead
//! retains A in every central write. Both modes use literal unitary cleanup.

use super::builder::{B,G};
use super::mask::mc_xor;
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// The implementation may retain a unitary prefix decoder across calls.
/// Its address and cache cells MUST be outside both arithmetic operands
/// and all five scalar/carry ports. Prefixes need be zero only on A1;
/// every xor invocation below includes A, and clear must reverse every
/// prefix literally. Do not use measurement-based AND cleanup.
pub(crate) trait BoundaryQuery {
    fn xor(&mut self,b:&mut B,value:usize,target:QubitId,
        extra:&[(QubitId,bool)],dirty:&[QubitId]);
    fn clear(&mut self,b:&mut B);
}

impl<'a,'m> BoundaryQuery for super::size_window::WindowDecoder<'a,'m> {
    fn xor(&mut self,b:&mut B,value:usize,target:QubitId,
        extra:&[(QubitId,bool)],dirty:&[QubitId]) {
        super::size_window::WindowDecoder::xor(self,b,value,target,extra,dirty);
    }
    fn clear(&mut self,b:&mut B) {super::size_window::WindowDecoder::clear(self,b);}
}

fn literal(b:&mut B,controls:&[(QubitId,bool)],target:QubitId,dirty:&[QubitId]) {
    assert!(!controls.iter().any(|p|p.0==target));
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().copied().filter(|q|*q!=target
        &&!controls.iter().any(|p|p.0==*q)&&seen.insert(*q)).collect();
    mc_xor(b,controls,target,&[],&bank);
}

fn up(b:&mut B,t:&[QubitId],s:&[QubitId],carry:QubitId) {
    for i in 0..s.len() {
        let x=if i==0{carry}else{s[i-1]};
        b.cx(s[i],t[i]);b.cx(s[i],x);b.ccx(x,t[i],s[i]);
    }
}

/// Return physical cell i to its input values and expose carry_i on x.
fn undo(b:&mut B,t:&[QubitId],s:&[QubitId],carry:QubitId,i:usize)->QubitId {
    let x=if i==0{carry}else{s[i-1]};
    if i<s.len() {
        b.ccx(x,t[i],s[i]);b.cx(s[i],x);b.cx(s[i],t[i]);
    }x
}

/// x already holds the carry into this restored physical cell. M from the
/// preceding iteration selects exactly the virtual-leading cell R-1.
/// Change the sum source b to ONE by x ^= M&!b around the output write.
/// All controls of these two CCX are unchanged by the target write.
fn write_lower(b:&mut B,t:&[QubitId],s:&[QubitId],x:QubitId,i:usize,
    activity:QubitId,mask:QubitId,membership:QubitId,virtual_top:bool,
    mask_globally_zero:bool,dirty:&[QubitId]) {
    b.cx(s[i],x);
    if virtual_top {b.x(s[i]);b.ccx(membership,s[i],x);b.x(s[i]);}
    if mask_globally_zero {b.ccx(mask,x,t[i]);}
    else {literal(b,&[(activity,false),(mask,false),(x,false)],t[i],dirty);}
    if virtual_top {b.x(s[i]);b.ccx(membership,s[i],x);b.x(s[i]);}
    b.cx(s[i],x);
}

fn toggle_or(b:&mut B,a:QubitId,c:QubitId,target:QubitId) {
    b.cx(a,target);b.cx(c,target);b.ccx(a,c,target);
}

/// Capture a complete restoring bit (including decoder erasure).
///
/// On A1: carry0, e0, mask0, membership0, logical R in lo..hi, and the
/// low R+1 target window is d<2*r. Higher target bits are arbitrary and
/// returned. On A0, each role may be arbitrary except a role marked
/// globally-zero by its boolean, which must actually enter zero globally.
/// The exact literal inverse acts on the image of this complete record.
///
/// Low-Y loan example: carry=Q120, metadata prefixes=Q122..127 and an
/// optional additional helper Q121; a Q arithmetic source is Q[..120]
/// and target length<=121. Size-window high bits may instead fund carry.
/// No clean source-top lane or adjacent PH shuttle is required.
#[allow(clippy::too_many_arguments)]
pub(crate) fn restoring_record(b:&mut B,t:&[QubitId],s:&[QubitId],
    activity:QubitId,e:QubitId,mask:QubitId,membership:QubitId,carry:QubitId,
    lo:usize,hi:usize,mask_globally_zero:bool,membership_globally_zero:bool,dirty:&[QubitId],
    query:&mut impl BoundaryQuery)->Vec<G> {
    assert!(!s.is_empty()&&(s.len()==t.len()||s.len()+1==t.len()));
    assert!(1<=lo&&lo<=hi&&hi<t.len()&&hi<=s.len());
    let roles=[activity,e,mask,membership,carry];let mut ports=BTreeSet::new();
    assert!(t.iter().chain(s).copied().chain(roles).all(|q|ports.insert(q)));
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().chain(t).chain(s).copied()
        .filter(|q|!roles.contains(q)&&seen.insert(*q)).collect();
    b.begin();
    for &q in t {b.x(q);}
    up(b,t,s,carry);
    // The last target may be an absent virtual source cell. Every real
    // MAJ cell is undone exactly once, never replayed for a query.
    let mut x=undo(b,t,s,carry,t.len()-1);
    for i in (0..t.len()).rev() {
        if i<hi {
            write_lower(b,t,s,x,i,activity,mask,membership,
                (lo..=hi).contains(&(i+1)),mask_globally_zero,&bank);
        }
        // M from R=i+1 had to remain until that cell's virtual-top write.
        if (lo..=hi).contains(&(i+1)) {
            query.xor(b,i+1,membership,&[(activity,false)],&bank);
        }
        let previous=if i>=1 {Some(undo(b,t,s,carry,i-1))}else{None};
        if (lo..=hi).contains(&i) {
            query.xor(b,i,membership,&[(activity,false)],&bank);
            let c=previous.expect("positive boundary has a preceding cell");
            // Previous physical source/target are now restored. A logical
            // leading ONE has carry C=target[i-1] OR carry_(i-1), regardless
            // of the physical source[i-1] passenger.
            toggle_or(b,t[i-1],c,mask);
            // If M is globally zero initially, M=>A throughout; otherwise
            // retain A in every central operation (M may hold off-A sign).
            let mut central=vec![(membership,false)];
            if !membership_globally_zero {central.push((activity,false));}
            literal(b,&central,e,&bank);
            let mut decide=central.clone();decide.extend([(t[i],false),(mask,false)]);
            literal(b,&decide,e,&bank);
            let mut write=central.clone();write.extend([(e,false),(mask,false)]);
            literal(b,&write,t[i],&bank);
            toggle_or(b,t[i-1],c,mask);
            central.push((e,false));literal(b,&central,mask,&bank);
            // Keep M for the next iteration's virtual-leading correction.
        }
        if let Some(p)=previous{x=p;}
    }
    query.clear(b);
    b.ccx(activity,e,mask);
    for &q in t {b.x(q);}
    b.end()
}

/// Physical leading ONE permits using the carry before undoing the
/// preceding MAJ cell. A single globally-zero work lane alternates
/// between A*e and A*[R=i]; a retained sign is never read or modified.
/// On A1: source[R-1]=1, carry0, e0, work0, d<2*r. Off A the
/// source/carry/e may be arbitrary and the complete record is identity.
/// Higher source and target cells are arbitrary, even on A1.
pub(crate) fn physical_restoring_record(b:&mut B,t:&[QubitId],s:&[QubitId],
    activity:QubitId,e:QubitId,work:QubitId,carry:QubitId,
    lo:usize,hi:usize,dirty:&[QubitId],query:&mut impl BoundaryQuery)->Vec<G>{
    assert!(!s.is_empty()&&(s.len()==t.len()||s.len()+1==t.len()));
    assert!(1<=lo&&lo<=hi&&hi<t.len()&&hi<=s.len());
    let roles=[activity,e,work,carry];let mut ports=BTreeSet::new();
    assert!(t.iter().chain(s).copied().chain(roles).all(|q|ports.insert(q)));
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().chain(t).chain(s).copied()
        .filter(|q|!roles.contains(q)&&seen.insert(*q)).collect();
    b.begin();for &q in t{b.x(q);}up(b,t,s,carry);
    for i in (0..t.len()).rev(){
        let x=undo(b,t,s,carry,i);
        // Above R, e and work are zero; below R, work=A*e. Read the
        // physical source bit only after undo restores its MAJ cell.
        if i<hi{b.cx(s[i],x);b.ccx(work,x,t[i]);b.cx(s[i],x);}
        if (lo..=hi).contains(&i){
            b.ccx(activity,e,work);
            query.xor(b,i,work,&[(activity,false)],&bank);
            // x is the actual carry into R, whose physical leading
            // source bit is ONE. No saved top or virtual carry is needed.
            // The two cubic updates form a controlled order-three map.
            // B A B A (B: t^=x*e, A: e^=work*t) is that map when
            // work=x=1 and identity when either control is0. It replaces
            // both dirty four-CCX expansions, for arbitrary e/t inputs.
            b.cx(work,e);
            b.ccx(x,e,t[i]);b.ccx(work,t[i],e);
            b.ccx(x,e,t[i]);b.ccx(work,t[i],e);
            query.xor(b,i,work,&[(activity,false)],&bank);
            b.ccx(activity,e,work);
        }
    }
    query.clear(b);b.ccx(activity,e,work);
    for &q in t{b.x(q);}b.end()
}

/// Complete four-scalar adapter for `direct_payload`, still reserve-only.
/// The caller binds q to the unparked physical Y bank and supplies the
/// unchanged public column ranges. Every low-Y Q loan is zero only on A.
pub(crate) struct MajArithmetic<'a>{
    pub q:&'a [QubitId],
    pub ranges:super::direct_payload::Ranges,
}

impl super::direct_payload::Arithmetic for MajArithmetic<'_>{
    fn apply(&mut self,b:&mut B,meta:&super::sum_size::SumSize,
        roles:super::direct_payload::Roles,call:super::direct_payload::Kernel,
        target:&[QubitId],source:&[QubitId],dirty:&[QubitId]){
        use super::size_window::{SizeWindow,WindowDecoder};
        use super::ttk_virtual_leading::Size;
        assert_eq!(self.q.len(),128);
        let limit=call.guard.sum_limit.clamp(0,31)as usize;
        assert!(call.guard.sum_limit>=0);
        let total=226+limit;
        let yl=self.ranges.y.0.max(call.guard.y.0).max(226usize.saturating_sub(self.ranges.z.1));
        let yh=self.ranges.y.1.min(call.guard.y.1).min(total.saturating_sub(self.ranges.z.0));
        if yl>yh{return;}
        let zl=self.ranges.z.0.max(226-yh);
        let zh=self.ranges.z.1.min(total-yl);
        if zl>zh{return;}
        let (lo,hi)=match call.size{Size::Y=>(yl,yh),Size::Z=>(zl,zh)};
        let (lo,hi)=(lo.max(call.bounds.0),hi.min(call.bounds.1));
        if lo>hi{return;}
        assert!(hi<target.len()&&hi<=source.len());
        let t=&target[..hi+1];
        // Real Q bits at or above its selected bitlength are virtual zero.
        // Truncate the public source BEFORE any Q120/cache loan is used.
        let s=&source[..match call.size{Size::Y=>hi,Size::Z=>(hi+1).min(source.len())}];
        let window=if matches!(call.size,Size::Z)&&call.guard.y.0>=121{
            SizeWindow::high_y_z(meta,lo,hi,call.guard.y)
        }else{SizeWindow::new(meta,call.size,lo,hi,limit)};
        let (carry,pre)=if call.guard.y.1<=120{
            let h=window.width.saturating_sub(1).min(6);
            (self.q[120],self.q[122..122+h].to_vec())
        }else{
            assert!(call.guard.y.0>=121);
            let spares=window.spares();assert!(!spares.is_empty());
            let h=window.width.saturating_sub(1).min(spares.len()-1);
            (spares[0],spares[1..1+h].to_vec())
        };
        let scalar=[roles.activity,roles.flight,roles.sign,roles.work];
        let mut ports=BTreeSet::new();
        assert!(t.iter().chain(s).copied().chain(scalar).chain([carry])
            .chain(pre.iter().copied()).all(|q|ports.insert(q)));
        assert!(meta.y.iter().chain(&meta.sum).all(|q|!t.contains(q)&&!s.contains(q)&&!scalar.contains(q)));
        // Coordinate records may borrow the returned loan cells as dirty;
        // kernel queries exclude all metadata/cache/carry for their lifetime.
        let mut excluded:BTreeSet<_>=meta.y.iter().chain(&meta.sum).copied().chain(scalar).collect();
        let coordinate_dirty:Vec<_>=dirty.iter().chain(t).chain(s).chain(self.q).copied()
            .filter(|q|excluded.insert(*q)).collect();
        let mut excluded:BTreeSet<_>=meta.y.iter().chain(&meta.sum).chain(&pre).copied()
            .chain(scalar).chain([carry]).collect();
        let kernel_dirty:Vec<_>=dirty.iter().chain(t).chain(s).chain(self.q).copied()
            .filter(|q|excluded.insert(*q)).collect();

        if call.inverse{b.cx(roles.sign,roles.activity);}
        let guard=call.guard.witness_record(b,meta,roles.activity,roles.flight,&coordinate_dirty);
        b.play(&guard,false);
        let coordinate=window.entry_record(b,&coordinate_dirty);b.play(&coordinate,false);
        let n=hi-lo+1;
        // Sign is zero on the narrowed active branch. Off it, retaining
        // sign as the mask costs three extra CCX/lower cell; retaining it
        // as membership costs twelve extra CCX/boundary instead.
        let sign_membership=call.inverse&&3*hi>12*n;
        let(mask,membership,mask_global,membership_global)=if sign_membership{
            (roles.work,roles.sign,true,false)
        }else{
            (roles.sign,roles.work,!call.inverse,true)
        };
        let mut decoder=WindowDecoder::new(&window,&pre,roles.activity);
        let arithmetic=restoring_record(b,t,s,roles.activity,roles.flight,mask,membership,
            carry,lo,hi,mask_global,membership_global,&kernel_dirty,&mut decoder);
        b.play(&arithmetic,call.inverse);
        b.play(&coordinate,true);b.play(&guard,true);
        if call.inverse{b.cx(roles.sign,roles.activity);}
    }
}

/// K4 U6's decoder boundary capability. `protected` binds all metadata and
/// every possible retained prefix owner for the entire record, not just the
/// current cursor. The literal is TRUE exactly when logical R is odd on A.
#[derive(Clone,Debug)]
pub(crate) struct K4QueryContract {
    pub protected:Vec<QubitId>,
    pub activity:QubitId,
    pub parity:(QubitId,bool),
    pub lo:usize,
    pub hi:usize,
}
pub(crate) trait K4BoundaryQuery:BoundaryQuery {
    fn k4_contract(&self)->K4QueryContract;
}
impl K4BoundaryQuery for super::size_window::WindowDecoder<'_,'_> {
    fn k4_contract(&self)->K4QueryContract {
        super::size_window::WindowDecoder::k4_contract(self)
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub(crate) enum K4Mutation { None, DropParity, WrongParitySign, DropAlternation, DamageBoundary }
#[derive(Clone,Debug,PartialEq,Eq)]
pub(crate) enum K4Error {
    Geometry, Alias(u64), DecoderHeld(u64), HeldOwner(u64), ActivityMismatch, NoDirtyLane, NoParityDonor,
}
pub(crate) struct K4Record {pub tape:Vec<G>,pub dirty_lane:QubitId,pub parity:(QubitId,bool)}

/// Sibling diagnostic U6 body. No production dispatcher selects this function.
/// A/e/sign are the three scalar roles. Sign is an arbitrary immutable owner.
/// On A: physical source[R-1]=1, e=carry=0, low target d<2r. Off A:
/// source/carry/e/sign and every passenger are arbitrary. Upper source/target
/// bits are arbitrary in both sectors. The exact inverse uses the oracle image.
#[allow(clippy::too_many_arguments)]
pub(crate) fn physical_restoring_record3(b:&mut B,t:&[QubitId],s:&[QubitId],
    activity:QubitId,e:QubitId,sign:QubitId,carry:QubitId,lo:usize,hi:usize,
    dirty:&[QubitId],held:&[QubitId],query:&mut impl K4BoundaryQuery,
    mutation:K4Mutation)->Result<K4Record,K4Error> {
    if s.is_empty()||!(s.len()==t.len()||s.len()+1==t.len())
        ||!(1<=lo&&lo<=hi&&hi<t.len()&&hi<=s.len()) {return Err(K4Error::Geometry);}
    let contract=query.k4_contract();
    if (contract.lo,contract.hi)!=(lo,hi)||!contract.protected.contains(&contract.parity.0) {
        return Err(K4Error::Geometry);
    }
    for &q in &contract.protected {
        if held.contains(&q){return Err(K4Error::DecoderHeld(q.0));}
    }
    let roles=[activity,e,sign,carry];let mut ports=BTreeSet::new();
    for &q in &roles {if held.contains(&q){return Err(K4Error::HeldOwner(q.0));}}
    for &q in t.iter().chain(s).chain(&roles) {
        if !ports.insert(q){return Err(K4Error::Alias(q.0));}
        if contract.protected.contains(&q){return Err(K4Error::DecoderHeld(q.0));}
    }
    if contract.activity!=activity{return Err(K4Error::ActivityMismatch);}
    let w=dirty.iter().copied().find(|q|!ports.contains(q)
        &&!contract.protected.contains(q)&&!held.contains(q)).ok_or(K4Error::NoDirtyLane)?;
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().chain(t).chain(s).copied().filter(|q|
        *q!=w&&!roles.contains(q)&&!contract.protected.contains(q)&&!held.contains(q)
        &&seen.insert(*q)).collect();
    if bank.is_empty(){return Err(K4Error::NoParityDonor);}
    b.begin();for &q in t{b.x(q);}up(b,t,s,carry);
    let mut dropped=false;
    for i in (0..t.len()).rev() {
        let x=undo(b,t,s,carry,i);
        if i<hi {
            b.cx(s[i],x);b.ccx(x,w,t[i]);
            if mutation==K4Mutation::DropAlternation&&!dropped {dropped=true;}
            else {b.ccx(activity,e,w);}
            b.ccx(x,w,t[i]);b.cx(s[i],x);
        }
        if (lo..=hi).contains(&i) {
            // Reusing xor retains actual cursor/clear and sum-cover semantics.
            // Same-value calls leave the cursor in place; no copied term maker.
            query.xor(b,i,e,&[(activity,false)],&bank);
            b.ccx(x,e,t[i]);
            query.xor(b,i,e,&[(activity,false),(t[i],false)],&bank);
            b.ccx(x,e,t[i]);
            if mutation!=K4Mutation::DamageBoundary {
                query.xor(b,i,e,&[(activity,false),(t[i],false)],&bank);
            }
        }
    }
    query.clear(b);
    if mutation!=K4Mutation::DropParity {
        let(parity,neg)=contract.parity;
        literal(b,&[(parity,neg^(mutation==K4Mutation::WrongParitySign)),
            (activity,false),(e,false)],w,&bank);
    }
    for &q in t{b.x(q);}
    Ok(K4Record{tape:b.end(),dirty_lane:w,parity:contract.parity})
}


/// Gather only unique coordinate keys. Each collision remains a physical
/// per-value query, and the unique-root operation carries an exact key-set
/// guard so off-box passengers are unchanged.
fn gathered_virtual_correction(b:&mut B,t:&[QubitId],s:&[QubitId],
    activity:QubitId,e:QubitId,lo:usize,hi:usize,
    address:&[QubitId],base:usize,bank:&[QubitId]){
    let modulus=1usize<<address.len();
    let mut values:Vec<(usize,usize)>=(lo..=hi).filter(|&v|
        !(v>=lo+modulus||v+modulus<=hi))
        .map(|v|((v+modulus-base%modulus)%modulus,v)).collect();
    if values.is_empty(){return;}
    values.sort_unstable_by_key(|p|p.0);
    assert!(values.windows(2).all(|w|w[0].0<w[1].0));
    let tl:Vec<_>=values.iter().map(|&(key,v)|(key,t[v-1])).collect();
    let sl:Vec<_>=values.iter().map(|&(key,v)|(key,s[v-1])).collect();
    let mut ts=vec![];let mut ss=vec![];
    let tr=super::midg::swap_tree(address,&tl,address.len(),&mut ts);
    let sr=super::midg::swap_tree(address,&sl,address.len(),&mut ss);
    let mut selected=vec![false;modulus];
    for &(key,_) in &values{selected[key]=true;}
    for &(c,x,y) in &ts{b.cswap(c,x,y);}
    for &(c,x,y) in &ss{b.cswap(c,x,y);}
    let mut key=0usize;
    while key<modulus{
        if !selected[key]{key+=1;continue;}
        let mut f=if key==0{address.len()}else{(key.trailing_zeros() as usize).min(address.len())};
        while key+(1usize<<f)>modulus || !selected[key..key+(1usize<<f)].iter().all(|x|*x){f-=1;}
        let mut c:Vec<_>=(f..address.len()).map(|i|(address[i],key>>i&1==0)).collect();
        c.extend([(activity,false),(e,false),(sr,true)]);
        literal(b,&c,tr,bank);
        key+=1usize<<f;
    }
    for &(c,x,y) in ss.iter().rev(){b.cswap(c,x,y);}
    for &(c,x,y) in ts.iter().rev(){b.cswap(c,x,y);}
}
/// Digit B2 boundary.  The optional virtual ONE keeps the physical source
/// head untouched.  Its top correction is deliberately decoded per value:
/// colliding seven-bit keys are never gathered into one ambiguous leaf.
#[allow(clippy::too_many_arguments)]
pub(crate) fn physical_restoring_record3_b2(b:&mut B,t:&[QubitId],s:&[QubitId],
    activity:QubitId,e:QubitId,sign:QubitId,carry:QubitId,lo:usize,hi:usize,
    dirty:&[QubitId],held:&[QubitId],address:&[QubitId],address_base:usize,
    query:&mut impl K4BoundaryQuery,virtual_one:bool)->Result<K4Record,K4Error>{
    if s.is_empty()||!(s.len()==t.len()||s.len()+1==t.len())
        ||!(1<=lo&&lo<=hi&&hi<t.len()&&hi<=s.len()) {return Err(K4Error::Geometry);}
    let contract=query.k4_contract();
    if (contract.lo,contract.hi)!=(lo,hi)||!contract.protected.contains(&contract.parity.0)
        ||contract.activity!=activity{return Err(K4Error::Geometry);}
    for &p in &contract.protected{if held.contains(&p){return Err(K4Error::DecoderHeld(p.0));}}
    let roles=[activity,e,sign,carry];let mut ports=BTreeSet::new();
    for &p in &roles{if held.contains(&p){return Err(K4Error::HeldOwner(p.0));}}
    for &p in t.iter().chain(s).chain(&roles){
        if !ports.insert(p){return Err(K4Error::Alias(p.0));}
        if contract.protected.contains(&p){return Err(K4Error::DecoderHeld(p.0));}
    }
    let w=dirty.iter().copied().find(|p|!ports.contains(p)
        &&!contract.protected.contains(p)&&!held.contains(p)).ok_or(K4Error::NoDirtyLane)?;
    let mut seen=BTreeSet::new();
    let bank:Vec<_>=dirty.iter().chain(t).chain(s).copied().filter(|p|
        *p!=w&&!roles.contains(p)&&!contract.protected.contains(p)&&!held.contains(p)
        &&seen.insert(*p)).collect();
    if bank.is_empty(){return Err(K4Error::NoParityDonor);}
    b.begin();for &p in t{b.x(p);}up(b,t,s,carry);
    let mut prior=if virtual_one{Some(undo(b,t,s,carry,t.len()-1))}else{None};
    for i in (0..t.len()).rev(){
        let x=if let Some(p)=prior{p}else{undo(b,t,s,carry,i)};
        if i<hi{
            b.cx(s[i],x);b.ccx(x,w,t[i]);b.ccx(activity,e,w);
            b.ccx(x,w,t[i]);b.cx(s[i],x);
        }
        let prev=if virtual_one&&i>0{Some(undo(b,t,s,carry,i-1))}else{None};
        if (lo..=hi).contains(&i){
            if virtual_one{
                let p=prev.expect("virtual leading predecessor");
                let lo_write=|b:&mut B|{
                    literal(b,&[(p,true),(t[i-1],false),(e,false)],t[i],&bank);
                    literal(b,&[(p,true),(t[i-1],true)],t[i],&bank);
                };
                b.ccx(p,e,t[i]);lo_write(b);
                query.xor(b,i,e,&[(activity,false),(t[i],true)],&bank);
                lo_write(b);b.ccx(p,e,t[i]);
            }else{
                b.ccx(x,e,t[i]);b.x(x);b.cx(x,t[i]);b.x(x);
                query.xor(b,i,e,&[(activity,false),(t[i],true)],&bank);
                b.x(x);b.cx(x,t[i]);b.x(x);b.ccx(x,e,t[i]);
            }
        }
        if virtual_one{prior=prev;}
    }
    let gather=virtual_one&&std::env::var("C658_WP3_ZH_GATHER").as_deref()==Ok("1");
    let c2_off=cfg!(test)&&std::env::var("R14_DIG_MUT_C2_OFF").as_deref()==Ok("1");
    if virtual_one&&!c2_off{
        // C2: each colliding key has two physically distinct corrections.
        let modulus=1usize<<address.len();
        for v in lo..=hi{
            if !gather||v>=lo+modulus||v+modulus<=hi{
                query.xor(b,v,t[v-1],&[(activity,false),(e,false),(s[v-1],true)],&bank);
            }
        }
    }
    query.clear(b);
    if gather&&!c2_off{
        gathered_virtual_correction(b,t,s,activity,e,lo,hi,address,address_base,&bank);
    }
    let(parity,neg)=contract.parity;
    literal(b,&[(parity,neg),(activity,false),(e,false)],w,&bank);
    for &p in t{b.x(p);}
    Ok(K4Record{tape:b.end(),dirty_lane:w,parity:contract.parity})
}
