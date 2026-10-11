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
#[cfg(test)]
mod tests_frogdrop;
#[cfg(test)]
mod tests_carry_lifetime;
#[cfg(test)]
mod tests_mask;

use crate::circuit::Op;

/// Fiat-Shamir nonce: the qubit of the final identity X X pair (0 = x[0])
pub const NONCE: usize = 4;

pub fn build() -> Vec<Op> {
    let mut b = builder::B::new();
    pointadd_frogdrop::point_add(&mut b);
    b.flush_dependency(); // publish the literal filtered ops before any consumer
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
