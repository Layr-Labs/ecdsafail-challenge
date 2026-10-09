//! frogdrop: a low-qubit 3-of-4 Euclid point addition (holds three of the four extended-Euclid values).

pub mod arith;
pub mod builder;
pub mod frogdrop;
pub mod frogdrop_col;
pub mod frogdrop_sched;
pub mod frogtail;
pub mod mask;
pub mod modp_frogdrop;
pub mod modp_ft;
pub mod pointadd_frogdrop;
pub mod pointadd_frogtail;
#[cfg(test)]
mod tests_frogdrop;
#[cfg(test)]
mod tests_mask;
#[cfg(test)]
mod tests_frogtail;

use crate::circuit::Op;

/// Fiat-Shamir nonce: the qubit of the final identity X X pair (0 = x[0])
pub const NONCE: usize = 3;

pub fn build() -> Vec<Op> {
    let mut b = builder::B::new();
    pointadd_frogtail::point_add(&mut b);
    eprintln!("frogtail: ops {} peak qubits {} width {} emitted Toffoli {}", b.ops.len(), b.peak, b.width(), b.tof);
    b.ops
}
