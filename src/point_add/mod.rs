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
#[cfg(test)]
mod tests_one;
#[cfg(test)]
mod tests_double;

use crate::circuit::Op;

pub const SCHED_DOUBLE: &str = include_str!("sched_double.txt");
pub const SCHED_ONE: &str = include_str!("sched_one.txt");
/// Fiat-Shamir nonce (number of identity X X pairs appended). `FH_NONCE` overrides it for corpus measurements; the
/// official build uses this value.
pub const NONCE: usize = 2;
/// Logical-AND carry qubits for the traversal ladders' ordinary lanes.
pub const GPOOL: usize = 0;
/// Traversal state: pi, k, three phase flags, depth, b offset (the quotient bits live in the register gaps).
pub const STATE: usize = froghop_one::PIB + froghop_one::KB + 3 + froghop_one::DEPB + froghop_one::BB;
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
    froghop_one::LayOne::from_text(SCHED_ONE, 24)
}

pub fn build() -> Vec<Op> {
    let mut b = builder::B::new();
    let lay = layout_one();
    pointadd_one::point_add(&mut b, &lay);
    eprintln!("froghop-one: ops {} peak qubits {} width {} emitted Toffoli {}", b.ops.len(), b.peak, b.width(), b.tof);
    b.ops
}
