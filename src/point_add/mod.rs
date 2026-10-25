//! frogdrop: a low-qubit 3-of-4 Euclid point addition (holds three of the four extended-Euclid values).

pub mod arith;
mod affine_simplify;
mod quadratic_simplify;
mod truth_simplify;
mod classical_wide;
mod cond_pass;
pub mod builder;
pub mod frogdrop;
pub mod head_product_care;
pub mod canonical_short;
pub mod field_consume_second;
mod field_consume_third;
mod seed_exception_corrections;
mod field_consume_fourth;
mod seed_exception_corrections_fourth;
pub mod frogdrop_col;
pub mod frogdrop_sched;
pub mod mask;
pub mod modp_frogdrop;
pub mod pointadd_frogdrop;
#[cfg(test)]
mod tests_frogdrop;
#[cfg(test)]
mod tests_carry_lifetime;
#[cfg(test)]
mod tests_mask;

use crate::circuit::{Op, OperationType, QubitId, NO_BIT};

/// Fiat-Shamir nonce: the qubit of the final identity X X pair (0 = x[0])
pub const NONCE: usize = 4;

/// Truth-table pass rounds (capped: on ~1e9-op streams round 1 carries ~95% of the gain and each round costs ~1.5 h).
pub const BW_TRUTH_MAX: usize = 1;
/// Post-pass nonce: identity X X pairs on qubit 0 appended AFTER the post-passes; 0 = none.
pub const BW_NONCE: usize = 0;
fn bw_nonce() -> usize { std::env::var("BW_NONCE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(BW_NONCE) }
/// Post-pass suite switch (BW_POSTPASS=0 disables, for A/B); inert when the environment is empty.
fn postpass_on() -> bool { std::env::var("BW_POSTPASS").map(|v| v != "0").unwrap_or(true) }

pub fn build() -> Vec<Op> {
    let mut b = builder::B::new();
    pointadd_frogdrop::point_add(&mut b);
    b.flush_dependency(); // publish the literal filtered ops before any consumer
    eprintln!("frogdrop: ops {} peak qubits {} width {} emitted Toffoli {}", b.ops.len(), b.peak, b.width(), b.tof);
    if let Some(count) = b.finish_stream() {
        eprintln!("LOWQ_EXACT_STREAM Q={} T={} N={} width={}", b.peak, b.tof, count, b.width());
    }
    let mut ops = b.ops;
    if postpass_on() {
        let before = counts(&ops);
        for pass in 1..=BW_TRUTH_MAX {
            let previous = counts(&ops);
            ops = truth_simplify::simplify_products(ops);
            let after = counts(&ops);
            eprintln!("POSTPASS_T pass={pass} before={previous:?} after={after:?}");
            if previous == after { break; }
        }
        let previous = counts(&ops);
        ops = classical_wide::simplify_products(ops);
        eprintln!("POSTPASS_W before={previous:?} after={:?}", counts(&ops));
        let previous = counts(&ops);
        ops = cond_pass::run_with(ops, "mfs");
        eprintln!("POSTPASS_C before={previous:?} after={:?}", counts(&ops));
        eprintln!("POSTPASS raw={before:?} final={:?}", counts(&ops));
    }
    for _ in 0..bw_nonce() {
        let mut x = Op::empty();
        x.kind = OperationType::X;
        x.q_target = QubitId(0);
        ops.push(x);
        ops.push(x);
    }
    ops
}

pub mod virtual_odd;

mod canonical_short_clean;
mod field_consume_fifth;
mod seed_exception_corrections_fifth;

mod canonical_short_seed_dirty;
mod descending_seed;

mod row_add;
mod canonical_bank;
mod early_product_fifth;

mod priority_probe;

mod masked_priority_probe;

mod joint_seed;

pub(crate) mod seed_fold;

mod ht_packed_divmod;
mod qp_naf_cut;
mod ht_window_parking;
mod ht_radix4_clean_echo;
mod ht_fusion_qphase;
mod ht_fusion_pair;

mod signed_batch;
mod signed_batch_frame;

fn counts(ops: &[Op]) -> (usize, u64, f64) {
    let mut weight = 1.0;
    let mut stack = vec![];
    let mut native = 0;
    let mut expected = 0.0;
    for op in ops {
        match op.kind {
            OperationType::PushCondition => { stack.push(weight); weight *= 0.5; },
            OperationType::PopCondition => weight = stack.pop().expect("balanced condition stack"),
            OperationType::CCX | OperationType::CCZ => {
                native += 1;
                expected += weight * if op.c_condition == NO_BIT { 1.0 } else { 0.5 };
            },
            _ => {},
        }
    }
    assert!(stack.is_empty());
    (ops.len(), native, expected)
}
