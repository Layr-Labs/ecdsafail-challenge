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
