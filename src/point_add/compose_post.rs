//! Post-reader_pass stage of this tree, in place of 4cb9cf0's call of its 6-hunk table on the whole stream:
//!   1. the 6-hunk table placed by the stream prefix it edits (frozen_stack::run_prefix). All six hunks lie in ops
//!      [0, 3,236,272), which this tree emits unchanged (it changes only the square, emitted later); that prefix must
//!      hash to 4cb9cf0's own prefix, so the result there equals 4cb9cf0's op for op;
//!   2. the two generic classical-control passes (classical_factors_xor, classical_wide; exact);
//!   3. CCX cuts proved on this stream, as a table bound to the complete input (micro_compose.txt, source_edits format).
use crate::circuit::{Op, OperationType};

fn tof(v: &[Op]) -> usize { v.iter().filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ)).count() }

pub(super) fn run(mut v: Vec<Op>) -> Vec<Op> {
    for s in ["frozen", "cfx", "cwide", "micro"] {
        let (before, tb) = (v.len(), tof(&v));
        v = match s {
            "frozen" => super::frozen_stack::run_prefix(v),
            "cfx" => super::classical_factors_xor::simplify_classical(v),
            "cwide" => super::classical_wide::simplify_classical(v),
            _ => super::source_edits::run(v, include_str!("micro_compose.txt")),
        };
        eprintln!("COMPOSE_POST {s}: ops {before} -> {}, toffoli ops {tb} -> {}", v.len(), tof(&v));
    }
    v
}
