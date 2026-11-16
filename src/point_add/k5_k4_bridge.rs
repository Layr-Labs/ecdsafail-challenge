//! Concrete default-off HR K5/K4 composition. No production dispatch selects it.
//! This child can use the frozen controller's private schedule helpers without
//! changing any inherited method or the qualified local PH test.
use super::*;
use super::super::direct_payload::{Context as PayloadContext, Session};
use super::super::direct_payload::k4_complete::{self, CloseBoundary, EntryBoundary, Roles3};
use super::super::frogdrop_col::ColPar;
use super::super::k5_ph_ports::Traversal;

/// Immutable physical binding; software data only, with no quantum allocation.
#[derive(Debug, PartialEq, Eq)]
struct Binding {
    column: usize,
    traversal: Traversal,
    ports: Vec<QubitId>,
    lengths: [usize; 4],
    y_bounds: (usize, usize),
    qb: usize,
}
impl Binding {
    fn new(cp: &ColPar, c: &Cross<'_>, compact: Option<&[QubitId]>) -> Self {
        let r = c.roles;
        let p = compact.unwrap_or(&[]);
        Self {
            column: cp.col,
            traversal: c.traversal,
            ports: c.ring.iter().chain(c.q).chain(&c.size.y).chain(&c.size.sum)
                .copied().chain([c.ph, r.activity, r.flight, r.mask])
                .chain(p.iter().copied()).chain(c.clean_external.iter().copied())
                .chain(c.excluded.iter().copied()).chain(c.dirty.iter().copied()).collect(),
            lengths: [p.len(), c.clean_external.len(), c.excluded.len(), c.dirty.len()],
            y_bounds: c.y_bounds,
            qb: c.qb,
        }
    }
    fn check(&self, cp: &ColPar, c: &Cross<'_>, compact: Option<&[QubitId]>) {
        assert_eq!(self, &Self::new(cp, c, compact), "K5_K4_REBIND");
    }
}

fn check_entry(cp: &ColPar, expected_column: usize, traversal: Traversal,
    c: &Cross<'_>, compact: Option<&[QubitId]>) {
    c.check();
    k4_complete::source_parameters(cp);
    assert_eq!(cp.col, expected_column, "K5_K4_COLUMN");
    assert_eq!(c.traversal, traversal, "K5_K4_TRAVERSAL");
    assert!(cp.hr, "K5_K4_NOT_HR");
    assert!(!((!cp.hr || cp.tt) && cp.sy.1 <= 96 && !(cp.sw || cp.psw || cp.dl || cp.dq)),
        "K5_K4_FIXED_MIDDLE_IS_SEPARATE");
    assert_eq!(c.y_bounds, (cp.sy.0.max(1), cp.sy.1.min(128)), "K5_K4_RANGE");
    assert_eq!(compact.is_some(), traversal.has_payload(), "K5_K4_PAYLOAD_TRAVERSAL");
    if let Some(p) = compact {
        assert_eq!(p.len(), 258, "K5_K4_COMPACT_WIDTH");
        assert!(c.clean_external.is_empty(), "K5_K4_NO_PAYLOAD_LOAN");
        let r = c.roles;
        let mut seen = BTreeSet::new();
        assert!(p.iter().chain(c.ring).chain(c.q).chain(&c.size.y).chain(&c.size.sum)
            .copied().chain([c.ph, r.activity, r.flight, r.mask])
            .chain(c.excluded.iter().copied()).all(|q| seen.insert(q)), "K5_K4_PORT_ALIAS");
    }
}

#[derive(Debug, PartialEq, Eq)]
enum PayloadState { Fresh, Open, TransitionsReturned, Closed }

/// Non-Clone capability, constructed at exactly one source site below, after
/// every tick/inverse divide and the captured Q128/ring/P259 inverse. Its
/// fields and the concrete bridge are private; an enum assertion at open
/// cannot manufacture it. It certifies source ordering, never quantum care.
struct ReturnedCoordinate { raw: Vec<QubitId> }

struct HrPayload<'a> {
    cp: &'a ColPar,
    compact: &'a [QubitId],
    binding: Binding,
    state: PayloadState,
    session: Option<Session>,
}
impl<'a> HrPayload<'a> {
    fn new(cp: &'a ColPar, c: &Cross<'_>, compact: &'a [QubitId]) -> Self {
        check_entry(cp, cp.col, c.traversal, c, Some(compact));
        Self { cp, compact, binding: Binding::new(cp, c, Some(compact)),
            state: PayloadState::Fresh, session: None }
    }
    fn check(&self, c: &Cross<'_>) {
        self.binding.check(self.cp, c, Some(self.compact));
    }
    fn accept_return(&mut self, c: &Cross<'_>, returned: ReturnedCoordinate) {
        self.check(c);
        assert_eq!(self.state, PayloadState::Open, "K5_K4_RETURN_EPOCH");
        assert_eq!(&self.session.as_ref().expect("K5_K4_OPEN_SESSION").raw, &returned.raw,
            "K5_K4_RAW_REBIND");
        self.state = PayloadState::TransitionsReturned;
    }
    fn assert_closed(&self) {
        assert_eq!(self.state, PayloadState::Closed, "K5_K4_UNCLOSED");
        assert!(self.session.is_none());
    }
}
impl PayloadBridge for HrPayload<'_> {
    fn open(&mut self, b: &mut B, c: &Cross<'_>) {
        self.check(c);
        assert_eq!(self.state, PayloadState::Fresh, "K5_K4_DOUBLE_OPEN");
        assert!(self.session.is_none());
        let r = c.roles;
        let session = k4_complete::digit_at_boundary3(b, &PayloadContext {
            meta: c.size, compact: self.compact, ring: c.ring, q: c.q, phase: c.ph,
        }, Roles3 { activity: r.activity, flight: r.flight, sign: r.mask }, self.cp,
            EntryBoundary::HrAfterControllerLeave, &c.bank(&[]), c.excluded);
        assert!(!session.ht);
        assert_eq!(session.activity, r.activity);
        assert_eq!(session.phase, c.ph);
        assert_eq!(session.raw.len(), 259);
        assert_eq!(&session.raw[..258], self.compact);
        assert_eq!(session.raw[258], c.ph);
        self.session = Some(session);
        self.state = PayloadState::Open;
    }
    fn close(&mut self, b: &mut B, c: &Cross<'_>) {
        self.check(c);
        // Reject before emitting even one POST gate. Only hr_finish_bound's
        // captured-coordinate inverse can advance this private bridge state.
        assert_eq!(self.state, PayloadState::TransitionsReturned, "K5_K4_EARLY_CLOSE");
        let session = self.session.as_ref().expect("K5_K4_OPEN_SESSION");
        k4_complete::finish_phase3(b, c.size, session, self.cp.sz, c.roles.mask,
            &c.bank(&[]), c.excluded, CloseBoundary::PayloadTransitionsReturned);
        self.session = None;
        self.state = PayloadState::Closed;
    }
    fn raw(&self) -> &[QubitId] {
        assert_eq!(self.state, PayloadState::Open, "K5_K4_RAW_EPOCH");
        &self.session.as_ref().expect("K5_K4_OPEN_SESSION").raw
    }
}

/// Source caller for the complete forward HR half at its RAW entry boundary.
/// The caller's original W occupies A; e/m are returned-zero roles. This
/// typed handle checks port/schedule identity, not the actual quantum values.
/// No complete column, HT/S5, outer allocation, or caller-image claim is made.
pub(crate) struct HrCaller<'a, 'q> {
    cp: &'a ColPar,
    c: &'a Cross<'q>,
    compact: Option<&'a [QubitId]>,
    binding: Binding,
}
impl<'a, 'q> HrCaller<'a, 'q> {
    /// expected_column and traversal come from the outer caller's cursor,
    /// independently of ColPar and Context, and are checked before emission.
    pub(crate) fn new(cp: &'a ColPar, expected_column: usize, traversal: Traversal,
        c: &'a Cross<'q>, compact: Option<&'a [QubitId]>) -> Self {
        check_entry(cp, expected_column, traversal, c, compact);
        Self { cp, c, compact, binding: Binding::new(cp, c, compact) }
    }

    /// Always APPEND FORWARD to the enclosing complete column recording.
    /// T1/T4 use identical open/tick/close order. The unchanged original
    /// trav_inverse_pl captures rec_col and plays that WHOLE tape inverse
    /// for T4; this module exposes no local reverse-open/close operation.
    /// An open recording is necessary but does not prove the caller supplied
    /// the entire original column. That integration remains a separate gate.
    pub(crate) fn append_forward(&self, b: &mut B) {
        self.binding.check(self.cp, self.c, self.compact);
        let depth = b.k5_bridge_recording_depth();
        assert!(depth > 0, "K5_K4_REQUIRES_COMPLETE_CALLER_CAPTURE");
        let mut controller = Controller::new(self.c, self.c.traversal.has_payload());
        if let Some(compact) = self.compact {
            let payload = HrPayload::new(self.cp, self.c, compact);
            let mut kernels = RawKernels::new(self.cp, payload);
            controller.hr_begin(b, &mut kernels, true);
            controller.hr_finish_bound(b, &mut kernels);
            kernels.payload.assert_closed();
            assert!(!kernels.payload_open);
        } else {
            // Exact inherited no-payload path: no bridge, raw259, PH payload
            // epoch or fourth owner is introduced on T2/T3.
            let mut kernels = RawKernels::new(self.cp, NoPayload);
            controller.hr_begin(b, &mut kernels, true);
            controller.hr_finish(b, &mut kernels);
            assert!(!kernels.payload_open);
        }
        assert!(controller.is_raw());
        assert_eq!(b.k5_bridge_recording_depth(), depth, "K5_K4_CAPTURE_DEPTH");
    }
}

// The complete hr_finish_bound method below is transported mechanically
// from the frozen K5 hr_finish body with only the named private binding and
// completion checks. The original function remains byte-for-byte intact.
impl Controller<'_, '_> {
    fn hr_finish_bound(&mut self,b:&mut B,k:&mut RawKernels<'_,HrPayload<'_>>){
        assert!(self.has_payload&&self.c.traversal.has_payload());
        assert!(std::ptr::eq(k.cp,k.payload.cp),"K5_K4_COLUMN_REBIND");
        k.payload.check(self.c);
        assert!(self.open&&self.epoch==Epoch::Hr);let f=k.top_frame(b,self.c);b.play(&f,false);let mut d=self.arithmetic(false);
        for j in 0..15{let t=frame::top_target(self.c,j);d.divide_inplace(b,self.c,&t,Gate::Top(j),false);}b.play(&f,true);
        for j in(0..15).rev(){let t=frame::natural_target(self.c,j);
            d.divide_erase_inplace(b,self.c,&t,Gate::Bottom(j),frame::park(self.c,j));}
        if self.has_payload{
            self.leave(b);k.hr_payload_open(b,self.c);
            // PH now belongs to raw P259. The temporary coordinate is
            // distinct from the earlier parked Q129 coordinate.
            let raw=k.hr_payload_word().to_vec();
            let coordinate=native_hr_payload::frame_record3(b,self.c,&raw);
            b.play(&coordinate,false);self.open=true;self.ring_open=true;
            // This final P coordinate is owned by its own captured record;
            // no partial-Q/ring helper is called until that record closes.
            let mut d=self.hr_arithmetic(HrSite::PayloadTick);
            for bit in 0..30{let t=frame::natural_target(self.c,bit);
                self.inplace(b,&t,Gate::Natural(bit));
                native_hr_payload::tick3(b,self.c,&raw,bit);
                d.divide(b,self.c,&t,Gate::Natural(bit),true);}
            b.play(&coordinate,true);self.open=false;self.ring_open=false;
            k.payload.accept_return(self.c,ReturnedCoordinate{raw});
            k.hr_payload_close(b,self.c);
        }else{
            // Both Q park families are now empty. The existing native
            // and reads all128 source cells with a genuine zero prefix.
            // No payload callback or PH payload lifetime is introduced.
            // No payload lifetime is opened on T2/T3.
            let mut d=self.hr_arithmetic(HrSite::NoPayloadTwin);
            for bit in 0..30{let t=frame::natural_target(self.c,bit);
                d.divide_inplace(b,self.c,&t,Gate::Natural(bit),true);}
            self.leave(b);
        }
        k.z_flip(b,self.c);k.toggle_activity(b,self.c,false);self.epoch=Epoch::Raw;
    }
}
