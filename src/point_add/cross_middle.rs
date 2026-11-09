//! Explicit, default-off complete NONFIXED middle. No production selector uses it.
//! The fourth physical role is an excluded spectator of this middle only;
//! unchanged outer/map stages retain their original four-role Q660 ABI.
use super::builder::B;
use super::direct_column::{Column, Middle};
use super::direct_ht_stage5::k4_bridge as ht;
use super::direct_payload::k4_complete;
use super::frogdrop_col::ColPar;
use super::k5_ph_controller::{self, NoPayload, RawKernels};
use super::k5_ph_ports::{Context, Roles, Traversal};
use crate::circuit::QubitId;
use std::collections::BTreeSet;

/// The traversal driver supplies this cursor independently of ColPar. It is
/// a source identity, not evidence about an actual original caller image.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Cursor {
    traversal: Traversal,
    column: usize,
}
impl Cursor {
    pub(crate) fn new(traversal: Traversal, column: usize) -> Self {
        Self { traversal, column }
    }
    pub(crate) fn traversal(self) -> Traversal { self.traversal }
    pub(crate) fn column(self) -> usize { self.column }
    pub(crate) fn inverse(self) -> bool {
        matches!(self.traversal, Traversal::T2 | Traversal::T4)
    }
    fn ht(self) -> ht::Traversal {
        match self.traversal {
            Traversal::T1 => ht::Traversal::T1,
            Traversal::T2 => ht::Traversal::T2,
            Traversal::T3 => ht::Traversal::T3,
            Traversal::T4 => ht::Traversal::T4,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Error {
    Endpoint, FixedColumn, Column, PayloadBinding, TerminalLoans,
    PortShape, PortAlias, PhysicalWidth, Rebind, Capture, Reuse,
}
pub(crate) fn require(ok: bool, error: Error) {
    if !ok { std::panic::panic_any(error); }
}

fn context<'a, 'p: 'a>(column: &'a Column<'p>, cp: &ColPar,
    cursor: Cursor, excluded: &'a [QubitId]) -> Context<'a> {
    let r = column.roles;
    Context {
        size: column.meta, ring: column.ring, q: column.q, ph: column.phase,
        roles: Roles { activity: r.tag, flight: r.cut, mask: r.toggle },
        dirty: column.dirty, y_bounds: (cp.sy.0.max(1), cp.sy.1.min(128)),
        qb: 30, clean_external: column.clean_external, excluded,
        traversal: cursor.traversal,
    }
}

/// All checks are classical source/port checks and have no Builder argument.
/// terminal_compact names the SAME original 258 payload owners on all passes.
/// On T2/T3 only its P0/P1 may be offered as named clean loans; their actual
/// zero support still belongs to the original complete traversal contract.
fn validate(column: &Column<'_>, cp: &ColPar, cursor: Cursor,
    terminal_compact: &[QubitId]) {
    require(!cp.nomap && cp.sz != (0, 0), Error::Endpoint);
    let fixed = (!cp.hr || cp.tt) && cp.sy.1 <= 96
        && !(cp.sw || cp.psw || cp.dl || cp.dq);
    require(!fixed, Error::FixedColumn);
    require(cp.col == cursor.column && (cp.hr || cp.ht), Error::Column);
    require((cp.n, cp.nq, cp.qb, cp.h, cp.l0) == (257, 128, 30, 0, 128),
        Error::Column);
    require(98 <= cp.sz.0 && cp.sz.0 <= cp.sz.1 && cp.sz.1 <= 256
        && cp.xw <= 257 && cp.swl.0 <= 128 && (2..=128).contains(&cp.m)
        && cp.emax <= 31, Error::Column);
    k4_complete::source_parameters(cp);
    require((column.ring.len(), column.q.len(), terminal_compact.len())
        == (257, 128, 258), Error::PortShape);
    if cursor.traversal.has_payload() {
        require(column.compact == Some(terminal_compact), Error::PayloadBinding);
        require(column.clean_external.is_empty(), Error::TerminalLoans);
    } else {
        require(column.compact.is_none(), Error::PayloadBinding);
        require(column.clean_external == &terminal_compact[..2], Error::TerminalLoans);
    }
    let r = column.roles;
    let mut used = BTreeSet::new();
    require(column.ring.iter().chain(column.q).chain(&column.meta.y)
        .chain(&column.meta.sum).chain(terminal_compact).copied()
        .chain([column.phase, r.tag, r.cut, r.toggle, r.prefix])
        .all(|q| used.insert(q)), Error::PortAlias);
    require(used.len() == 660 && used.iter().all(|q| q.0 < 660)
        && column.dirty.iter().all(|q| used.contains(q)), Error::PhysicalWidth);
    let excluded = [r.prefix];
    let c = context(column, cp, cursor, &excluded);
    c.check();
    if cp.ht {
        // Validate the imported suffix's shape/alias/loan contract before
        // any outer gate. Construct the retained-A Entry only at its epoch.
        let old = super::cross_four::Cross {
            size: column.meta, ring: column.ring, q: column.q, phase: column.phase,
            roles: super::cross_four::Roles {
                activity: r.tag, flight: r.cut, mask: r.toggle, x128: r.prefix,
            },
            dirty: column.dirty, y_bounds: c.y_bounds, qb: 30,
            clean_external: column.clean_external,
        };
        let raw = column.compact.map(|p|
            p.iter().copied().chain([column.phase]).collect::<Vec<_>>());
        super::normalized_cross_arithmetic::k2_stage5::validate(&old, raw.as_deref());
    }
}

/// One exact complete Middle invocation. Borrowed immutable descriptors bind
/// every ColPar field and ordered owner list without constructing a new one.
/// No forward/inverse half-record API is exposed here.
pub(crate) struct CompleteMiddle<'a, 'p: 'a> {
    column: &'a Column<'p>,
    cp: &'a ColPar,
    cursor: Cursor,
    terminal_compact: &'a [QubitId],
    returned: bool,
}
impl<'a, 'p: 'a> CompleteMiddle<'a, 'p> {
    pub(crate) fn new(column: &'a Column<'p>, cp: &'a ColPar, cursor: Cursor,
        terminal_compact: &'a [QubitId]) -> Self {
        validate(column, cp, cursor, terminal_compact);
        Self { column, cp, cursor, terminal_compact, returned: false }
    }
    pub(crate) fn assert_returned(&self) { require(self.returned, Error::Capture); }
}
impl<'a, 'p: 'a> Middle for CompleteMiddle<'a, 'p> {
    fn run_complete(&mut self, b: &mut B, column: &Column<'_>, cp: &ColPar) {
        require(!self.returned, Error::Reuse);
        require(std::ptr::eq(self.column, column) && std::ptr::eq(self.cp, cp), Error::Rebind);
        validate(column, cp, self.cursor, self.terminal_compact);
        let depth = b.k5_bridge_recording_depth();
        require(depth > 0, Error::Capture);
        let excluded = [column.roles.prefix];
        let c = context(column, cp, self.cursor, &excluded);

        if cp.hr {
            // Literal qualified HR caller owns begin, all V/park/native work,
            // K4 open/POST and raw return. Its final activity restores W.
            let caller = k5_ph_controller::k4_bridge::HrCaller::new(
                cp, self.cursor.column, self.cursor.traversal, &c, column.compact);
            caller.append_forward(b);
        }
        if cp.sw { column.xor_switch(b, column.roles.tag); } // W -> 0.
        if cp.ht {
            column.xor_ht_activity(b, cp, column.roles.tag);
            let entry = ht::Entry::new(column, cp, self.cursor.ht(),
                ht::EntryEpoch::HtActivityRetainedBeforeDigit);
            entry.append_to_column_capture(b);
            // Complete digit/S5 has closed PH and returned Q128/host. Clear
            // retained A before the distinct HT PH129 controller lifetime.
            column.xor_ht_activity(b, cp, column.roles.tag);
            let mut controller = k5_ph_controller::Controller::new(
                &c, self.cursor.traversal.has_payload());
            let mut kernels = RawKernels::new(cp, NoPayload);
            controller.ht_finish(b, &mut kernels, true);
            require(controller.is_raw(), Error::Capture);
        }
        require(b.k5_bridge_recording_depth() == depth, Error::Capture);
        self.returned = true;
        // This returns the original full Middle boundary. Actual role zeros,
        // support, signed state and restored passengers need native evidence.
    }
}
