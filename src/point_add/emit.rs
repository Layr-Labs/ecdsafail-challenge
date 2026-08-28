use super::*;
use alloy_primitives::U256;
use std::collections::HashMap;

/// Per-`emit` call lease table.
///
/// Each entry records the parked-low carry QubitIds that a
/// `cconst_nbit_direct_trunc_fast_parked` call returned to the free pool at
/// the end of its life, keyed by the constant addend `c` and the
/// `is_add` direction. The next call with the same `c` and direction
/// can reacquire the same QubitIds from the free pool and skip the
/// forward (compute) carry phase — the carry bits are already sitting at
/// zero in the free pool, so the controlled-jump logic only has to apply
/// the sum phase and uncompute, which saves a stack of CCX gates per
/// parked carry per point-add iteration.
///
/// The table is intentionally bounded: at most one entry per `(c, is_add)`
/// key. When the same key is reused we drop the previous entry; the
/// underlying QubitIds are still owned by the free pool because the
/// previous emit call returned them, so the drop is just dropping the
/// record (no qubit bookkeeping is touched).
#[derive(Default)]
pub(crate) struct LeaseTable {
    /// Keyed by `(c, is_add)`; value is the QubitIds returned to the free
    /// pool by the most recent call with that key.
    by_const: HashMap<(U256, bool), Vec<QubitId>>,
    /// Diagnostic counters used by the diagnostic env var path; not
    /// read by the hot path.
    pub hits: u64,
    pub misses: u64,
    pub returns: u64,
}

impl LeaseTable {
    pub(crate) fn new() -> Self {
        Self {
            by_const: HashMap::new(),
            hits: 0,
            misses: 0,
            returns: 0,
        }
    }

    /// Look up the parked carry QubitIds from the most recent call with
    /// the same `c` and `is_add` direction. The caller must already
    /// have placed the returned qubits back in the free pool — `lease_for_const`
    /// does not touch the free pool itself; it just returns the
    /// recorded handle so the caller can `reacquire` each QubitId.
    pub(crate) fn lookup(&mut self, c: U256, is_add: bool) -> Option<Vec<QubitId>> {
        let entry = self.by_const.get(&(c, is_add)).cloned();
        if entry.is_some() {
            self.hits += 1;
        } else {
            self.misses += 1;
        }
        entry
    }

    /// Record the parked carry QubitIds for the most recent call with
    /// `c` and `is_add`. Overwrites any prior entry for the same key
    /// (the previous QubitIds remain in the free pool and are simply
    /// orphaned by the new record — they will be reused by the next
    /// `alloc_qubit` that pulls from the free pool, which is the
    /// intended behavior).
    pub(crate) fn return_qubits(&mut self, c: U256, is_add: bool, qs: &[QubitId]) {
        self.by_const
            .insert((c, is_add), qs.to_vec());
        self.returns += 1;
    }
}
