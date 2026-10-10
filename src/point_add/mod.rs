//! frogdrop: a low-qubit 3-of-4 Euclid point addition (holds three of the four extended-Euclid values).

pub mod arith;
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
pub mod payload;
#[cfg(test)]
mod tests_frogdrop;
#[cfg(test)]
mod tests_carry_lifetime;
#[cfg(test)]
mod tests_mask;

use crate::circuit::Op;

/// Fiat-Shamir nonce: the qubit of the final identity X X pair (0 = x[0])
pub const NONCE: usize = 5;

pub fn build() -> Vec<Op> {
    let mut b = builder::B::new();
    pointadd_frogdrop::point_add_pl(&mut b);
    eprintln!("frogdrop: ops {} peak qubits {} width {} emitted Toffoli {}", b.ops.len(), b.peak, b.width(), b.tof);
    if let Some(count) = b.finish_stream() {
        eprintln!("LOWQ_EXACT_STREAM Q={} T={} N={} width={}", b.peak, b.tof, count, b.width());
    }
    b.ops
}

pub mod virtual_odd;

mod canonical_short_clean;
mod field_consume_fifth;
mod seed_exception_corrections_fifth;
mod row_add;
