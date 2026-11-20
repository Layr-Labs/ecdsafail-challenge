//! Replace the post-relabel, pre-peephole F-prime bracket of t632final2.
//! The edit header checks both parent and result lengths and row hashes.
use super::{b5gen, Slot};
pub const START: usize = 1_805_115_649;
pub const PARENT_ROWS: usize = 249_150_278;
pub const ASSIGNED_ROWS: usize = 349_535_908;

pub(super) fn replace<S: Slot>(out: &mut Vec<S>, start: usize) {
    let end = start + PARENT_ROWS;
    let parent: Vec<_> = out[start..end].iter().map(|s| s.to_row()).collect();
    let assigned = b5gen::decode(&parent, include_bytes!("data/fprime.b5"));
    assert_eq!(assigned.len(), ASSIGNED_ROWS);
    drop(parent);
    out.splice(start..end, assigned.into_iter().map(S::from_row));
}
