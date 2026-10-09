//! froghop-single: a low-qubit packed-Euclid point addition (one hop per Euclid step).

pub mod arith;
pub mod builder;
pub mod froghop_single;
pub mod modp;
pub mod pointadd;
pub mod refmodel;
#[cfg(test)]
mod tests;

use crate::circuit::Op;

pub const SCHED: &str = include_str!("sched.txt");

pub fn layout() -> froghop_single::Lay {
    froghop_single::Lay::from_text(SCHED, 24, 60)
}

pub fn build() -> Vec<Op> {
    let mut b = builder::B::new();
    let lay = layout();
    pointadd::point_add(&mut b, &lay);
    eprintln!("froghop-single: ops {} peak qubits {} width {} emitted Toffoli {}", b.ops.len(), b.peak, b.width(), b.tof);
    b.ops
}
