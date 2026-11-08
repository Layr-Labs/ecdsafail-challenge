//! Opt-in complete nonfixed column recording. Default traversal is unchanged.
//! T2/T4 apply ONE inverse of outer entry + full middle + outer exit + the
//! unchanged original map/tail/counter. This is not an actual caller-image proof.
use super::builder::{B, G};
use super::cross_middle::{require, CompleteMiddle, Cursor, Error};
use super::direct_column::Column;
use super::frogdrop_col::ColPar;
use crate::circuit::QubitId;

/// Private full tape prevents this adapter from exposing an isolated HR/HT
/// inverse. Cursor binds the source pass and column; no partial stage exists.
pub(crate) struct ColumnRecord {
    cursor: Cursor,
    tape: Vec<G>,
}
impl ColumnRecord {
    pub(crate) fn capture(b: &mut B, column: &Column<'_>, cp: &ColPar,
        cursor: Cursor, terminal_compact: &[QubitId]) -> Self {
        // Fixed/endpoint/range/owner/loan mismatches stop BEFORE b.begin or
        // any outer emission. No fallback calls DirectMiddle or an endpoint.
        let mut middle = CompleteMiddle::new(column, cp, cursor, terminal_compact);
        require(b.width() == 660, Error::PhysicalWidth);
        let depth = b.k5_bridge_recording_depth();
        b.begin();
        super::direct_column::through_stage10(b, column, cp, &mut middle);
        middle.assert_returned();
        super::direct_map_tail_counter::finish(b, column, cp);
        let tape = b.end();
        require(b.k5_bridge_recording_depth() == depth, Error::Capture);
        Self { cursor, tape }
    }

    /// T1/T3 forward; T2/T4 inverse. T4 reverses the entire captured forward
    /// description once through Builder::play, including compute/uncompute
    /// transport and all outer/map/counter work. Never reverse local callbacks.
    pub(crate) fn apply(&self, b: &mut B, cursor: Cursor) {
        require(cursor == self.cursor, Error::Rebind);
        require(b.width() == 660, Error::PhysicalWidth);
        let depth = b.k5_bridge_recording_depth();
        b.play(&self.tape, cursor.inverse());
        require(b.k5_bridge_recording_depth() == depth, Error::Capture);
    }

    /// Counts G entries/capacity only. This is not an emitted Op count or
    /// process-memory bound; nested construction and consumer overlap remain.
    pub(crate) fn gate_storage(&self) -> (usize, usize) {
        (self.tape.len(), self.tape.capacity())
    }
}
