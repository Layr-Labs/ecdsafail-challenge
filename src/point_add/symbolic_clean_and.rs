//! Adapter for welttowelt's Q834 immutable Boolean-expression proof engine.
//!
//! q834_clean_and.rs is copied byte-for-byte from submission 347258d5-dfc4-4bf3-
//! 91a1-4040ad600922. See memory/2026-09-10-symbolic-clean-and.md and the copied
//! upstream NOTICE for attribution/provenance. This adapter is new campaign work.
//!
//! The proof consumes each SOURCE operation exactly once. Only its original
//! clean-AND and support-lowering actions are admitted. With MIDQ_SYMBOLIC_RESIDUAL,
//! its original proved constant-one and one-live-wire cleanup actions are also admitted. Source phases, resets, HMRs, conditions, and ABI metadata stay
//! unchanged. Inserted HMR outcomes use fresh non-ABI classical bits.
use crate::circuit::{analyze_ops, BitId, Op, QubitId, QubitOrBit, NO_BIT};

#[path = "q834_clean_and.rs"]
mod proof_engine;

#[cfg(test)]
#[path = "symbolic_clean_and_tests.rs"]
mod tests;

struct AbiInputs {
    nq: usize,
    nb: usize,
    qinputs: Vec<usize>,
    cinputs: Vec<usize>,
}

impl AbiInputs {
    fn from_ops(ops: &[Op]) -> Self {
        // Metadata may occur at the END. Read the complete stream before any
        // clean-entry inference. Widths are determined by declarations, allowing
        // small structurally identical ABIs in component tests; the trusted
        // benchmark separately requires the real four 256-wire registers.
        let (nq, nb, _, regs) = analyze_ops(ops.iter());
        assert_eq!(regs.len(), 4, "symbolic pass requires four ABI registers");
        let nq = usize::try_from(nq).expect("qubit count does not fit usize");
        let nb = usize::try_from(nb).expect("classical count does not fit usize");
        let mut qinputs = Vec::new();
        let mut cinputs = Vec::new();
        let mut seen_q = vec![false; nq];
        let mut seen_c = vec![false; nb];
        for (index, reg) in regs.iter().enumerate() {
            assert!(!reg.is_empty(), "empty ABI register");
            for wire in reg {
                match (index < 2, wire) {
                    (true, QubitOrBit::Qubit(q)) => {
                        let q = q.0 as usize;
                        assert!(!seen_q[q], "duplicate quantum ABI input");
                        seen_q[q] = true;
                        qinputs.push(q);
                    }
                    (false, QubitOrBit::Bit(b)) => {
                        let b = b.0 as usize;
                        assert!(!seen_c[b], "duplicate classical ABI input");
                        seen_c[b] = true;
                        cinputs.push(b);
                    }
                    _ => panic!("ABI must be quantum, quantum, classical, classical"),
                }
            }
        }
        Self {
            nq,
            nb,
            qinputs,
            cinputs,
        }
    }
}

#[derive(Debug)]
struct Stats {
    source_ops: usize,
    measured_ands: u64,
    residual_wires: u64,
    residual_ones: u64,
    affine_queries: u64,
    support_dead: u64,
    support_x: u64,
    support_cx: u64,
    ccx_seen: u64,
    conditional_ccx: u64,
    evictions: u64,
    fresh_classical_bits: u64,
    #[cfg(test)]
    proof_fingerprint: String,
}

fn transform(ops: Vec<Op>, visit: impl FnMut(&Op, &[Op])) -> (Vec<Op>, Stats) {
    transform_mode(ops, visit, std::env::var("MIDQ_SYMBOLIC_RESIDUAL").ok().as_deref() == Some("1"))
}

fn transform_mode(ops: Vec<Op>, mut visit: impl FnMut(&Op, &[Op]), residual: bool) -> (Vec<Op>, Stats) {
    let abi = AbiInputs::from_ops(&ops);
    let mut proof = proof_engine::Proof::new(abi.nq, abi.nb, &abi.qinputs, &abi.cinputs);
    proof.affine_allowed = residual;
    let mut residual_wires = 0;
    let mut residual_ones = 0;
    // analyze_ops returns one above the largest bit ID anywhere in the stream,
    // including conditions and late declarations. Inserted IDs never alias one.
    let mut next_bit = u64::try_from(abi.nb).expect("classical bit count overflow");
    let first_bit = next_bit;
    let source_ops = ops.len();
    let mut output = Vec::with_capacity(source_ops);
    for original in ops {
        let start = output.len();
        // DO NOT step emitted HMR/CZ or lowered operations: Proof already tracks
        // the original gate's outgoing value, equal to that of its replacement.
        let rewrite = proof.step(&original);
        let to_one = residual && !rewrite && proof.ccx_result_is_one(&original);
        let to_wire = if residual && !rewrite && !to_one { proof.residual_action } else { None };
        if rewrite || to_one || to_wire.is_some() {
            assert_ne!(next_bit, NO_BIT.0, "classical bit ID exhausted");
            let measurement = BitId(next_bit);
            next_bit = next_bit.checked_add(1).expect("classical bit ID exhausted");
            let replacement = if to_one {
                residual_ones += 1;
                proof_engine::replacement_to_one(&original, measurement).to_vec()
            } else if let Some((wire, parity)) = to_wire {
                residual_wires += 1;
                proof_engine::replacement_to_wire(&original, measurement, QubitId(wire as u64), parity)
            } else {
                proof_engine::replacement(&original, measurement).to_vec()
            };
            for op in &replacement {
                op.validate();
            }
            output.extend(replacement);
        } else if let Some(lowered) = proof.support_lowering.apply(original) {
            output.push(lowered);
        }
        visit(&original, &output[start..]);
    }
    assert!(proof.balanced(), "unbalanced symbolic condition stack");
    if !residual { assert_eq!(proof.affine_queries, 0, "affine queries must stay disabled"); }
    let stats = Stats {
        source_ops,
        measured_ands: proof.rewrites,
        residual_wires,
        residual_ones,
        affine_queries: proof.affine_queries,
        support_dead: proof.support_dead,
        support_x: proof.support_x,
        support_cx: proof.support_cx,
        ccx_seen: proof.ccx_seen,
        conditional_ccx: proof.conditional_ccx,
        evictions: proof.evictions(),
        fresh_classical_bits: next_bit - first_bit,
        #[cfg(test)]
        proof_fingerprint: proof.diagnostic_fingerprint(),
    };
    assert_eq!(stats.measured_ands + stats.residual_wires + stats.residual_ones, stats.fresh_classical_bits);
    (output, stats)
}

pub(super) fn simplify(ops: Vec<Op>) -> Vec<Op> {
    let (output, stats) = transform(ops, |_, _| {});
    eprintln!("MIDQ_SYMBOLIC_CLEAN_AND {stats:?}");
    output
}
