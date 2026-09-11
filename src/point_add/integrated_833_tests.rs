//! The source lease can be invalidated by optimizing logical IDs first.
//! Exercise the actual production pair and the finalization order on a tiny
//! complete counterexample, including q0 elimination and optional cancellation.
use super::*;
use crate::sim::Simulator;
use sha3::digest::XofReader;

struct Outcomes;
impl XofReader for Outcomes {
    fn read(&mut self, out: &mut [u8]) {
        out.fill(0);
    }
}
fn gate(kind: OperationType, a: u64, b: u64, target: u64) -> Op {
    let mut op = Op::empty();
    op.kind = kind;
    op.q_target = QubitId(target);
    if matches!(kind, OperationType::CX | OperationType::CCX) {
        op.q_control1 = QubitId(a);
    }
    if kind == OperationType::CCX {
        op.q_control2 = QubitId(b);
    }
    op.validate();
    op
}
#[test]
fn integrated_833_lease_precedes_physical_peepholes() {
    use OperationType::{CCX, CX, X};
    let h = 787;
    let p = 834;
    let original = vec![
        gate(X, 0, 0, 0),
        gate(CCX, 1, 2, p),
        gate(CX, p, 0, 3),
        gate(CCX, 1, 2, p),
        gate(X, 0, 0, h),
        gate(CX, h, 0, 4),
        gate(X, 0, 0, h),
        gate(CCX, 1, 2, p),
        gate(CX, p, 0, 5),
        gate(CCX, 1, 2, p),
        gate(X, 0, 0, 0),
    ];
    let mut physical = original.clone();
    let report = coalesce_metadata_lifetime(&mut physical);
    assert!(report.high_ops > 0 && report.pool_ops > 0);
    peephole::cancel_identical_pairs(&mut physical);
    eliminate_constant_outer_control(&mut physical, QubitId(0));
    commuting_cancel::cancel(&mut physical);
    let mut wrong_order = original.clone();
    let logical = peephole::cancel_identical_pairs(&mut wrong_order);
    assert!(logical.ccx_uncond_pairs > 0);
    coalesce_metadata_lifetime(&mut wrong_order);
    eliminate_constant_outer_control(&mut wrong_order, QubitId(0));

    let (mut ra, mut rb, mut rc) = (Outcomes, Outcomes, Outcomes);
    let mut source = Simulator::new(835, 0, &mut ra);
    let mut got = Simulator::new(833, 0, &mut rb);
    let mut bad = Simulator::new(833, 0, &mut rc);
    for bit in 0..5 {
        let word = (0..64usize).fold(0u64, |w, lane| w | ((((lane >> bit) & 1) as u64) << lane));
        source.qubits[bit + 1] = word;
        got.qubits[bit] = word;
        bad.qubits[bit] = word;
    }
    source.phase = 0x89ab_cdef_0123_4567;
    got.phase = source.phase;
    bad.phase = source.phase;
    source.apply_iter(original.iter());
    got.apply_iter(physical.iter());
    bad.apply_iter(wrong_order.iter());
    let lease = metadata_lt8::Lease { high: h, pool: p };
    assert_eq!(source.qubits[h as usize], 0);
    assert_eq!(source.qubits[0], 0);
    for q in 1..835 {
        if q != h {
            let mapped = lease.map(QubitId(q)).0 - 1;
            assert_eq!(source.qubits[q as usize], got.qubits[mapped as usize]);
        }
    }
    assert_eq!(source.phase, got.phase);
    assert_eq!(source.stats.toffoli_gates, got.stats.toffoli_gates);
    assert_ne!(
        source.qubits[4], bad.qubits[3],
        "logical-first cancellation must expose the lifetime counterexample"
    );
}
