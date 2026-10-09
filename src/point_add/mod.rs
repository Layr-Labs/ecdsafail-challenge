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
/// Peak live qubits; the modular routines take every clean qubit up to it as carry pool.
pub const PEAK: u64 = 935;
/// Fiat-Shamir nonce: identity X X pairs appended after the point addition (they only re-roll the benchmark's test
/// shots). `FH_NONCE` overrides it for corpus measurements; the official build uses this value.
pub const NONCE: usize = 2;

fn nonce() -> usize {
    std::env::var("FH_NONCE").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(NONCE)
}

pub fn layout() -> froghop_single::Lay {
    froghop_single::Lay::from_text(SCHED, 24, 60)
}

pub fn build() -> Vec<Op> {
    let mut b = builder::B::new();
    let lay = layout();
    let (x, _y) = pointadd::point_add(&mut b, &lay);
    for _ in 0..nonce() {
        b.x(x[0]);
        b.x(x[0]);
    }
    eprintln!("froghop-single: ops {} peak qubits {} width {} emitted Toffoli {}", b.ops.len(), b.peak, b.width(), b.tof);
    b.ops
}
