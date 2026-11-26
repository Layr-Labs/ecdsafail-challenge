//! (internal) work package 2 tool (NOT part of any package): a child module of a COPY of q633a's `point_add`
//! (add `pub mod w2; pub mod w2rw;` to that copy's mod.rs).
//!
//! Modes (env W2_MODE):
//!   snap : stream the whole raw builder stream (= census.rs, no peephole) through a 256-shot bit-sliced simulator
//!          (sim.rs semantics + phase parity) and save the full simulator state at the START of the segments in
//!          W2_SEGS (e.g. "5,25") to W2_OUT/snap-seg<S>.bin; at the end write W2_OUT/fails.txt (failing shots, garbage).
//!   item : load snapshots (W2_SNAPS, comma list; masks from <snap dir>/fails.txt), emit ITEM W2_ITEM's records
//!          (wire map + inserts + segment lane map, as mod.rs `items`), optionally rewritten by w2rw (W2_RW), and
//!          report per-record liveness (peak, records at 633 / 632, runs); with W2_CMP=1 also run the ORIGINAL
//!          block from the same state and compare every lane, every classical bit and the phase parity per shot.
//!          W2_RANDOM=<seed>: instead of snapshots, start from uniformly random lanes 0..632 (all 256 shots),
//!          with the rewriter's preconditions applied (lanes it asserts are 0 at entry are forced 0) -> W2_CMP check.
//!   stat : static anatomy of one item (wire space): W2_ITEM, W2_RANGE=a..b dumps records with lane names.
use super::*;
/// packaged build: no environment access (measuring knobs read as unset = the defaults the build always used)
#[inline] pub fn env(_k: &str) -> Option<String> { None }
use std::io::{Read as _, Write as _};

pub const W: usize = 4;
pub type V = [u64; W];
pub const Z: V = [0; W];
pub const ALL: V = [u64::MAX; W];
pub const NL: usize = 633;
pub const NQ: usize = 640;
#[inline] pub fn and(a: V, b: V) -> V { let mut r = Z; for i in 0..W { r[i] = a[i] & b[i]; } r }
#[inline] pub fn xor(a: &mut V, b: V) { for i in 0..W { a[i] ^= b[i]; } }



#[inline] pub fn to_lanes(mut row: Row, m: &[u16]) -> Row { for j in 1..=qubits(row[0]) { let l = m[row[j] as usize]; assert!(l != NONE, "unmapped wire {}", row[j]); row[j] = l; } row }



// ------------------------------------------------------------------------------------------------ snap

// ------------------------------------------------------------------------------------------------ item




// ------------------------------------------------------------------------------------------------ stat
