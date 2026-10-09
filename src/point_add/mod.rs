//! froghop-double: a low-qubit exact-packed Euclid point addition (two hops per Euclid step).

pub mod arith;
pub mod builder;
pub mod froghop_double;
pub mod mask;
pub mod modp_double;
pub mod pointadd_double;
pub mod refmodel_double;
#[cfg(test)]
mod tests_double;

use crate::circuit::Op;

pub const SCHED_DOUBLE: &str = include_str!("sched_double.txt");
/// Fiat-Shamir nonce (number of identity X X pairs appended)
pub const NONCE: usize = 1;

pub fn layout_double() -> froghop_double::LayDouble {
    froghop_double::LayDouble::from_text(SCHED_DOUBLE, 24)
}

pub fn build() -> Vec<Op> {
    let mut b = builder::B::new();
    let lay = layout_double();
    pointadd_double::point_add(&mut b, &lay);
    eprintln!("froghop-double: ops {} peak qubits {} width {} emitted Toffoli {}", b.ops.len(), b.peak, b.width(),
              b.tof);
    b.ops
}
