//! froghop-double: a low-qubit exact-packed Euclid point addition (two hops per Euclid step), lean bookkeeping.

pub mod arith;
pub mod builder;
pub mod froghop_double;
pub mod mask;
pub mod modp_double;
pub mod pointadd_double;
pub mod refmodel_double;
mod affine_simplify;
mod quadratic_simplify;
mod truth_simplify;
mod classical_wide;
mod cond_pass;
#[cfg(test)]
mod tests_double;
#[cfg(test)]
mod tests_a4;
#[cfg(test)]
mod tests_g1;

use crate::circuit::{Op, OperationType, NO_BIT};

pub const SCHED_DOUBLE: &str = include_str!("sched_double.txt");
/// Fiat-Shamir nonce (number of identity X X pairs appended)
pub const NONCE: usize = 2;

pub fn nonce() -> usize {
    std::env::var("FH_NONCE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(NONCE)
}
/// Post-pass suite switch (BW_POSTPASS=0 disables, for A/B)
fn postpass_on() -> bool { std::env::var("BW_POSTPASS").map(|v| v != "0").unwrap_or(true) }

pub fn layout_double() -> froghop_double::LayDouble {
    froghop_double::LayDouble::from_text(SCHED_DOUBLE, 24)
}

pub fn build() -> Vec<Op> {
    let mut b = builder::B::new();
    let lay = layout_double();
    pointadd_double::point_add(&mut b, &lay);
    eprintln!("froghop-double: ops {} peak qubits {} width {} emitted Toffoli {}", b.ops.len(), b.peak, b.width(),
              b.tof);
    let mut ops = b.ops;
    if !postpass_on() { return ops; }
    // Nonce tail (2*NONCE identity X ops) is split off so the passes never touch it.
    let n2 = 2 * nonce();
    let tail = ops.split_off(ops.len() - n2);
    assert!(tail.iter().all(|o| o.kind == OperationType::X));
    let before = counts(&ops);
    for pass in 1..=32 {
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
    ops.extend(tail);
    ops
}
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

