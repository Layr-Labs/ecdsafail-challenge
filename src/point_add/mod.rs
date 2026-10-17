//! froghop-one: a low-qubit exact-packed Euclid point addition with one hop per Euclid step.

pub mod arith;
pub mod builder;
pub mod froghop_double;
pub mod froghop_one;
#[cfg(test)]
mod froghop_one_before_rxd;
#[cfg(test)]
mod froghop_one_before_topbit;
#[cfg(test)]
mod froghop_one_before_s7diet;
#[cfg(test)]
mod froghop_one_before_s2diet;
#[cfg(test)]
mod froghop_one_diet_bb6;
#[cfg(test)]
#[path = "../../../r10-c6z/src/point_add/froghop_one.rs"]
mod froghop_one_before_b1cache;
pub mod mask;
pub mod modp_double;
pub mod pointadd_double;
pub mod pointadd_one;
pub mod refmodel_double;
pub mod refmodel_one;
#[cfg(test)]
mod tests_one;
#[cfg(test)]
mod tests_double;

use crate::circuit::{Op, OperationType, NO_BIT};

pub const SCHED_DOUBLE: &str = include_str!("sched_double.txt");
pub const SCHED_ONE: &str = include_str!("sched_one.txt");
/// Fiat-Shamir nonce (number of identity X X pairs appended). `FH_NONCE` overrides it for corpus measurements; the
/// official build uses this value.
pub const NONCE: usize = 1;
/// Logical-AND carry qubits for the traversal ladders' ordinary lanes.
pub const GPOOL: usize = 0;
/// Traversal state: pi, k, flags, the 27-lane stack/DONE counter, depth and b offset.
pub const STATE: usize = froghop_one::HIB + froghop_one::KB + 3 + 27 + froghop_one::DEPB + froghop_one::BB + 1;
/// Peak live qubits: the traversal's 2 W + 256 passenger + state + scratch + GPOOL + reflection bit; the modular
/// routines take every clean qubit up to it as carry pool.
pub const PEAK: u64 = (2 * froghop_one::W1 + 256 + STATE + froghop_one::POOL_1 + GPOOL + 1) as u64;

pub fn nonce() -> usize {
    std::env::var("FH_NONCE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(NONCE)
}

pub fn layout_double() -> froghop_double::LayDouble {
    froghop_double::LayDouble::from_text(SCHED_DOUBLE, 24)
}

pub fn layout_one() -> froghop_one::LayOne {
    froghop_one::LayOne::from_text(SCHED_ONE, 27)
}

pub fn build() -> Vec<Op> {
    let mut b = builder::B::new();
    let lay = layout_one();
    pointadd_one::point_add(&mut b, &lay);
    let removed = cancel_adjacent_ccx(&mut b.ops);
    eprintln!("froghop-one: ops {} peak qubits {} width {} emitted Toffoli {} (adjacent CCX gates removed {})",
              b.ops.len(), b.peak, b.width(), b.tof - removed as u64, removed);
    b.ops
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
