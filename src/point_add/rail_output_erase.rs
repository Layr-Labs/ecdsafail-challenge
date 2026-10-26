// Fixed rail-output erasures after the inherited stream tables.
use crate::circuit::Op;
pub(super) fn run(v:Vec<Op>)->Vec<Op>{super::source_edits::run(v,include_str!("rail_output_erase.txt"))}
