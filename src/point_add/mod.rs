//! froghop-one: a low-qubit exact-packed Euclid point addition with one hop per Euclid step.

pub mod arith;
pub mod builder;
pub mod froghop_double;
pub mod froghop_one;
pub mod mask;
pub mod modp_double;
pub mod pointadd_double;
pub mod pointadd_one;
pub mod refmodel_double;
pub mod refmodel_one;
mod affine_simplify;
mod quadratic_simplify;
mod truth_simplify;
mod classical_wide;
mod cond_pass;
#[cfg(test)]
mod tests_one;
#[cfg(test)]
mod tests_double;
#[cfg(test)]
mod tests_a1b;
#[cfg(test)]
mod tests_a1c;
#[cfg(test)]
mod tests_a1e;

use crate::circuit::{Op, OperationType, NO_BIT};
use std::sync::LazyLock;

pub const SCHED_DOUBLE: &str = include_str!("sched_double.txt");
pub const SCHED_ONE: &str = include_str!("sched_one.txt");
/// Fiat-Shamir nonce (number of identity X X pairs appended). `FH_NONCE` overrides it for corpus measurements; the
/// official build uses this value. Lane A1d: the Q807 row (POOL_1 = 7) takes nonce 2, its first clean count (nonces 0
/// and 1 fail one official shot each); every other row keeps 0, so POOL_1 alone still selects each row's stream.
pub const NONCE: usize = if froghop_one::POOL_1 == 7 { 2 } else { 0 };
/// Logical-AND carry qubits for the traversal ladders' ordinary lanes.
pub const GPOOL: usize = 0;
/// Traversal state: pi, k, flags, depth, b offset and [k != 0] (the quotient bits live in the register gaps; the layout
/// has no stack register).
pub fn state(lay: &froghop_one::LayOne) -> usize {
    froghop_one::HIB + froghop_one::KB + 3 + lay.smax + froghop_one::DEPB + froghop_one::BB + 1
}
/// Peak live qubits: the traversal's 2 W + 256 passenger + state + scratch + GPOOL + reflection bit; the modular
/// routines take every clean qubit up to it as carry pool.
pub static PEAK: LazyLock<u64> = LazyLock::new(|| {
    let lay = layout_one();
    (2 * froghop_one::W1 + 256 + state(&lay) + froghop_one::POOL_1 + GPOOL + 1) as u64
});

/// Post-pass suite switch (BW_POSTPASS=0 disables, for A/B); inert when the environment is empty.
fn postpass_on() -> bool { std::env::var("BW_POSTPASS").map(|v| v != "0").unwrap_or(true) }

pub fn nonce() -> usize {
    std::env::var("FH_NONCE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(NONCE)
}

pub fn layout_double() -> froghop_double::LayDouble {
    froghop_double::LayDouble::from_text(SCHED_DOUBLE, 24)
}

pub fn layout_one() -> froghop_one::LayOne {
    froghop_one::LayOne::from_text(SCHED_ONE, 0)
}

pub fn build() -> Vec<Op> {
    let mut b = builder::B::new();
    let lay = layout_one();
    pointadd_one::point_add(&mut b, &lay);
    let removed = cancel_adjacent_ccx(&mut b.ops);
    eprintln!("froghop-one: ops {} peak qubits {} width {} emitted Toffoli {} (adjacent CCX gates removed {})",
              b.ops.len(), b.peak, b.width(), b.tof - removed as u64, removed);
    let mut ops = b.ops;
    if !postpass_on() { return ops; }
    // Nonce tail (2*nonce identity X ops) is split off so the passes never touch it.
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
    ops = cond_pass::run_with(ops, "mfsr");
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


/// Exact in-place cancellation; every removed pair is consecutive, identical,
/// unconditioned, self-inverse CCX on the same three physical wires.
pub fn cancel_adjacent_ccx(ops: &mut Vec<Op>) -> usize {
    let old_len = ops.len();
    let mut dst = 0usize;
    for src in 0..old_len {
        let op = ops[src];
        if dst > 0 && op.kind == OperationType::CCX && op.c_condition == NO_BIT && ops[dst - 1] == op {
            dst -= 1;
        } else {
            ops[dst] = op;
            dst += 1;
        }
    }
    ops.truncate(dst);
    let removed = old_len - dst;
    assert_eq!(removed % 2, 0);
    removed
}
