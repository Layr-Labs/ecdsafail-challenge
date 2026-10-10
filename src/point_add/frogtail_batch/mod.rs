//! Tape-free Frogtail-917 with even-tick digit erasure and average-T carry cleanup.
//!
//! Base: gnuchev's e303771 / commit 897d06a, descended from BitWonka's Frogtail.
//! The numerical walk, 308+308 rings, 556 ticks, width schedule, gap cap,
//! absorption, and product formula are retained.
//!
//! Active j has parity t at the start of tick t: negating j preserves parity,
//! and each halve decrements it. Therefore j=0 (the final digit) occurs only
//! on even ticks. Erase the digit word immediately after that digit, when
//! j=-1. During the following idle tail, nu(A.c) increases while j decreases;
//! b=A.c/2^nu(A.c), g=nu(A.c)+j, B.c and the completed Q are unchanged. Thus
//! the same congruence erases Q before the tail, and the large eraser is
//! emitted only on even ticks. Completed, absorbed inputs keep j=+1 and Q=0.
//!
//! Product overflow flags are measured away, with a comparison phase oracle
//! under a classical measurement condition. Its inverse computes the flag
//! coherently. The trusted evaluator's average executed Toffoli is the metric;
//! the builder's emitted/native count deliberately includes both branches.
//!
//! Run: FROGTAIL_BATCH=1 cargo run --release --bin build_circuit
//!      cargo run --release --bin eval_circuit
//! Test: cargo test --release --bin build_circuit frogtail_batch:: -- --include-ignored
//!       --skip predict_nonce --skip mbu_bisect
mod arith;
mod builder;
mod chunked;
mod frogdrop;
mod frogdrop_sched;
mod frogtail;
mod mask;
mod modp_frogdrop;
mod modp_ft;
mod pointadd_frogtail;
#[cfg(test)]
mod tests_average;
#[cfg(test)]
mod tests_chunked;
#[cfg(test)]
mod tests_prod;
#[cfg(test)]
mod tests_frogdrop;
#[cfg(test)]
mod tests_frogtail;

// First clean nonce in the fixed-body scan 0..3. The inherited nonce 3
// has one post-halve width-envelope failure predicted by the original model.
pub const NONCE: usize = 4;
pub fn build() -> Vec<crate::circuit::Op> {
    let mut b = builder::B::new();
    pointadd_frogtail::point_add(&mut b);
    eprintln!(
        "FROGTAIL_BATCH native_T={} cond_T={} expected_T={:.1} peak={} ops={}",
        b.tof,
        b.tof_cond,
        b.tof as f64 - b.tof_cond as f64 / 2.0,
        b.peak,
        b.ops.len()
    );
    b.ops
}
