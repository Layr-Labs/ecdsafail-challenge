//! q631 / fl2 (agent fl2, 2026-11-20; local research, NOT part of any package; nothing in the builder calls it): ITEM 4's last records
//! with no free lane.  Each fix is its own submodule behind its own switch, all OFF:
//!   fl2pb: phase B (A = 2^256 |v| mod mg by aligned doublings / halvings): lane 2 free (a G1 split of the doubling, ov -> 257 XOR G1).
//!   fl2up: the unpark head (extract .. delta, up to agent i4b's E_A window): lane 258 free (G1 coded into (259, 616) = (0, 1)).
//! Input: ITEM 4's rows as fl::fli4::rewrite leaves them; apply fl2pb, then fl2up (rewrite below).  Report:
//! ~/Projects/ecdsafail/q631/fl2/summary.py.
#[path = "fl2pb.rs"]
#[allow(dead_code)]
pub mod fl2pb;
#[path = "fl2up.rs"]
#[allow(dead_code)]
pub mod fl2up;
use super::Row;
pub const ON: bool = false;
/// both fixes on ITEM 4's rows (after fl::fli4): (rows, phase-B stats, unpark-head stats)
pub fn rewrite(rows: &[Row]) -> (Vec<Row>, fl2pb::Stats, fl2up::Stats) {
    let (a, s1) = fl2pb::rewrite(rows);
    let (b, s2) = fl2up::rewrite(&a);
    (b, s1, s2)
}
