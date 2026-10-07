//! Build a phase-only inverse of the exact forward Sign producer:
//!   CCX(p1,p2,Sign); R00 comparator
//! Excludes BOTH passenger loans. Install next to sign_phase_output.rs.
//! No HMR/condition stack is emitted here; the caller wraps this phase body
//! for inverse ERASURE only after verifying its reachable pure-Sign input.
use crate::circuit::{Op,OperationType as K,QubitId};
#[path="sign_phase_output.rs"] mod output;
pub fn body(forward_producer:&[Op],sign:QubitId)->Vec<Op> {
    assert!(!forward_producer.is_empty());
    assert_eq!(forward_producer[0].kind,K::CCX,"missing deterministic phase11 term");
    assert_eq!(forward_producer[0].q_target,sign);
    let mut inverse:Vec<_>=forward_producer.iter().rev().copied().collect();
    output::phase_output(&mut inverse,sign);
    inverse
}
