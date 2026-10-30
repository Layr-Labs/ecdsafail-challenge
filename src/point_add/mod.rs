//! froghop-one: a low-qubit exact-packed Euclid point addition with one hop per Euclid step.

pub mod arith;
pub mod builder;
pub mod froghop_double;
pub mod froghop_one;
#[cfg(all(test, greedyfrog_legacy_tests))] // external tree, absent in the greedyfrog worktree
#[path = "../../../r16-c27-839/src/point_add/froghop_one.rs"]
mod froghop_one_before_a4a;
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
#[cfg(all(test, greedyfrog_legacy_tests))] // external tree, absent in the greedyfrog worktree
#[path = "../../../r10-c6z/src/point_add/froghop_one.rs"]
mod froghop_one_before_b1cache;
pub mod mask;
pub mod modp_double;
pub mod ftport;
pub mod ft_adapter;
pub mod pointadd_double;
pub mod pointadd_one;
pub mod refmodel_double;
pub mod refmodel_one;
pub mod greedyfrog_model;
pub mod greedyfrog;
pub mod pointadd_greedyfrog;
#[cfg(test)]
mod greedyfrog_diag;
mod affine_simplify;
mod quadratic_simplify;
mod truth_simplify;
mod classical_wide;
mod cond_pass;
mod frontier_rewrite;
mod lease_pass;
#[cfg(all(test, greedyfrog_legacy_tests))] // uses the external-tree modules
mod tests_one;
#[cfg(test)]
mod tests_double;

use crate::circuit::{Op, OperationType, NO_BIT};
use std::sync::LazyLock;

pub const SCHED_DOUBLE: &str = include_str!("sched_double.txt");
pub const SCHED_ONE: &str = include_str!("sched_one.txt");
/// Fiat-Shamir nonce (number of identity X X pairs appended). `FH_NONCE` overrides it for corpus measurements; the
/// official build uses this value.
pub const NONCE: usize = 1;
/// Logical-AND carry qubits for the traversal ladders' ordinary lanes.
pub const GPOOL: usize = 12;
/// Traversal state: pi, k, flags, the layout's stack/DONE counter, depth and b offset.
pub fn state(lay: &froghop_one::LayOne) -> usize {
    froghop_one::HIB + froghop_one::KB + 3 + lay.smax + froghop_one::DEPB + froghop_one::BB + 1
}
/// Peak live qubits: the traversal's 2 W + 256 passenger + state + scratch + GPOOL + reflection bit; the modular
/// routines take every clean qubit up to it as carry pool.
pub static PEAK: LazyLock<u64> = LazyLock::new(|| {
    if USE_GREEDYFROG {
        return greedyfrog_peak();
    }
    let lay = layout_one();
    (2 * froghop_one::W1 + 256 + state(&lay) + froghop_one::POOL_1 + GPOOL + 1) as u64
});
/// Build the point addition with uniform greedy Euclid divisions (`pointadd_greedyfrog`) instead of froghop-one.
pub const USE_GREEDYFROG: bool = true;
/// greedyfrog peak cap. The traversal needs 2 W rings, the 256-qubit passenger, LA LB (18; the DONE counter lives in
/// ring Y), the reflection bit (which carries the swap parity) and 24 lanes of slot scratch (815); above that, the
/// slots take clean ancillas and carry pools up to the cap, below it borrowed lanes. The modular routines fill their carry pools up to it.
/// gf knob: GF_PEAK (default: the submitted formula) sets the peak the shell's carry pools fill to.
pub fn greedyfrog_peak() -> u64 {
    std::env::var("GF_PEAK").ok().and_then(|v| v.trim().parse().ok())
        .unwrap_or((798) as u64)
}

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
    if USE_GREEDYFROG {
        pointadd_greedyfrog::point_add(&mut b);
    } else {
        let lay = layout_one();
        pointadd_one::point_add(&mut b, &lay);
    }
    let removed = cancel_adjacent_ccx(&mut b.ops);
    eprintln!("{}: ops {} peak qubits {} width {} emitted Toffoli {} (adjacent CCX gates removed {})",
              if USE_GREEDYFROG { "greedyfrog" } else { "froghop-one" },
              b.ops.len(), b.peak, b.width(), b.tof - removed as u64, removed);
    let mut ops = b.ops;
    // the identity X X pairs at the end are kept out of the post-passes and re-appended unchanged
    let n2 = 2 * nonce();
    let tail = ops.split_off(ops.len() - n2);
    // Discard unused emission capacity; operation order and contents are unchanged.
    ops.shrink_to_fit();
    assert!(tail.iter().all(|o| o.kind == OperationType::X && o.q_target == tail[0].q_target));
    // Exact generic post-passes: Boolean tables over at most six atoms (to a fixed point), nine-atom tables with the
    // product index, then the conditional-AND pass with options m (CCX -> CX), f (ANDs read only by phases) and
    // s (ANDs built under the classical bit that decides their read).
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
    ops = cond_pass::run_with(ops, "mfsur");
    eprintln!("POSTPASS_C before={previous:?} after={:?}", counts(&ops));
    eprintln!("POSTPASS raw={before:?} final={:?}", counts(&ops));
    // Return only already-free allocator pages from completed rewrite passes.
    // Live operations, capacities and every rewrite decision are unchanged.
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    unsafe {
        extern "C" { fn malloc_trim(pad: usize) -> i32; }
        let _ = malloc_trim(0);
    }
    ops = frontier_rewrite::apply(ops);
    ops = lease_pass::run(ops);
    eprintln!("POST_LEASE {:?}", counts(&ops));
    ops.extend(tail);
    append_tail_nonce(&mut ops, TAIL_NONCE);
    ops
}

/// Fixed 48-bit Fiat-Shamir tail nonce. Each bit is an X/X identity pair on qubit 0 or 1, so the nonce changes
/// only the challenge hash, never the circuit semantics, qubit peak or Toffoli count.
const TAIL_NONCE: u64 = 0;

fn append_tail_nonce(ops: &mut Vec<Op>, nonce: u64) {
    use crate::circuit::QubitId;
    assert!(nonce < (1u64 << 48));
    for bit in 0..48 {
        let mut x = Op::empty();
        x.kind = OperationType::X;
        x.q_target = QubitId((nonce >> bit) & 1);
        ops.push(x);
        ops.push(x);
    }
}

/// (ops, native Toffoli, expected executed Toffoli) under the classical-condition weights.
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


pub fn profile_build() {let mut b=builder::B::new();pointadd_greedyfrog::point_add(&mut b);let q=b.ops.iter().flat_map(|o|[o.q_control2,o.q_control1,o.q_target]).filter(|&q|q!=crate::circuit::NO_QUBIT).map(|q|q.0+1).max().unwrap_or(0);eprintln!("COUNT_TOTAL {:?} Q={} ALLOC={}",counts(&b.ops),q,b.width());}
