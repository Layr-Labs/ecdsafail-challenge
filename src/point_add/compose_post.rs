//! Post-reader_pass stage of this tree:
//!   1. the two generic classical-control passes (classical_factors_xor, classical_wide; exact);
//!   2. CCX cuts proved on this stream, as a table bound to the complete input (micro_compose.txt, source_edits format).
//! The parent's 6-hunk table is bound to the parent's divide prefix, which this tree changes (the record slot and k3
//! changes in the walk), so it is not applied.
use crate::circuit::{Op, OperationType};

fn tof(v: &[Op]) -> usize { v.iter().filter(|o| matches!(o.kind, OperationType::CCX | OperationType::CCZ)).count() }

pub(super) fn run(mut v: Vec<Op>) -> Vec<Op> {
    for s in ["cfx", "cwide", "micro"] {
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
