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
pub mod mid2;
pub mod midg;
pub mod quot_klane;
#[cfg(test)]
mod tests_quot;
#[cfg(test)]
mod tests_midg;
#[cfg(test)]
mod tests_frogdrop;
#[cfg(test)]
mod tests_carry_lifetime;
#[cfg(test)]
mod tests_mask;

use crate::circuit::Op;

// F1 emission census. Values are emitted Toffolis, not model or executed costs.
pub(crate) fn f1_profile(name: &'static str, before: u64, after: u64) {
    if !*F1_PROFILE.get_or_init(|| std::env::var_os("F1_PROFILE").is_some()) { return; }
    F1_COUNTS.with(|m| {
        let mut m = m.borrow_mut();
        let e = m.entry(name).or_insert((0u64, 0u64));
        e.0 += 1;
        e.1 += after - before;
    });
}
static F1_PROFILE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
thread_local! { static F1_COUNTS: std::cell::RefCell<std::collections::BTreeMap<&'static str, (u64,u64)>> =
    std::cell::RefCell::new(std::collections::BTreeMap::new()); }
pub(crate) fn f1_dump() {
    if !*F1_PROFILE.get_or_init(|| std::env::var_os("F1_PROFILE").is_some()) { return; }
    F1_COUNTS.with(|m| for (name, (calls, tof)) in m.borrow().iter() {
        eprintln!("F1_PROFILE {name} calls={calls} emitted_t={tof}");
    });
}

/// Fiat-Shamir nonce: the qubit of the final identity X X pair (0 = x[0])
pub const NONCE: usize = 2;
/// with a control qubit the identity pair is CX(NONCE_CTRL, NONCE) twice: a two-qubit nonce space
pub const NONCE_CTRL: Option<usize> = Some(5);

/// The B2 design's switches (ring 262 / K3: Y root, act, and SX0 lent to R, chunk cuts, trailing-zero map,
/// stage-5 reserve 5 lanes + Y-top slot, exact switch-tail and delayed-move cuts), baked as defaults so an env-less
/// build emits it.
pub(crate) const BAKED_KNOBS: &[(&str, &str)] = &[
    ("FD_NARROW_DELTA", "1"), ("FD_NHT_PRE", "3"), ("FD_NHT_TMP", "1"), ("FD_PSW_DELTA", "1"), ("FD_S2_PRE", "3"),
    ("FD_DIG_FREE", "7"), ("FD_LEAN_SX", "4"), ("FD_CNT_ANC", "2"), ("FD_SWT_DELTA", "1"), ("FD_ZBANK", "8"),
    ("FD_MAP_PBANK", "32"), ("FD_MAP_SYBANK", "32"), ("FD_DINV_PRE", "1"), ("FD_DINV_NOPAD", "1"), ("FD_MIDG_YCOMP", "1"),
    ("FD_MIDG_ZOFF", "1"), ("FD_LOOP_PRE", "2"), ("FD_MID_CHAIN", "2"),
    ("QUOT_CUTS_NARROW", "1,3,7,13,19"), ("QUOT_CUTS_WIDE", "1,3,7,13,19"), ("QUOT_CUTS_CROSS_ONLY", "1"), ("FD_MIDG_SGW", "1"),
    ("QUOT_MAP_TZ", "1"), ("QUOT_RES_S", "6"), ("QUOT_CUTS_NONCROSS", "6,12,18"), ("LANE_SWT_CUT", "1"), ("LANE_DL_CUT", "1"),
    ("QUOT_MAP_CTRL", "104-113"),
    ("LANE_S5_YTOP", "1"),
    ("B7A_VSEARCH", "1"), ("B7A_A_HR", "1"), ("B7A_A_HT", "1"),
    ("B8A_MAP_FRAME_BANK", "1"),
    ("FD_MAP_DFORM", "1"),
    ("B8B_O3", "1"),
    // lowq-672: stage 5 without the park, the two-engine crossing tiers, the 9-lane pool (bq/cmpc/f/g re-bound per
    // region, the crossing middle on sx0/sx1/sx6/sx7 with the top band kept in Q), controlled done-column maps
    ("S5_NOPARK", "1"), ("L672_TIER", "1"), ("L672_POOL9", "1"), ("L672_MID8", "1"), ("L672_J1Q", "1"),
    ("C55_POOL8", "1"),
    ("FD_NODEFERASE", "1"),
    ("B12A_P1", "1"),
    // (jackylee0424 8d916b42, Q675: the fused N258 digit inverse at margin 1)
    ("R9_DIGIT_FUSED", "1"),
    // C45 source-integration pilot: 8-bit one-based scan, decoded back to the
    // inherited 9-bit raw size until the other size readers have been rekeyed.
    ("C45_WIDE_OFFSET_PILOT", "1"),
];

/// Set every baked knob the environment does not already set (LS_NO_BAKE=1: leave the environment alone).
pub(crate) fn bake_knobs() {
    if std::env::var_os("LS_NO_BAKE").is_some() { return; }
    for &(k, v) in BAKED_KNOBS {
        if std::env::var_os(k).is_none() { std::env::set_var(k, v); }
    }
}

pub fn build() -> Vec<Op> {
    bake_knobs();
    let mut b = builder::B::new();
    b.global_cancel = std::env::var_os("F2_NO_GLOBAL_CANCEL").is_none();
    pointadd_frogdrop::point_add_pl(&mut b);
    b.flush_global();
    f1_dump();
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
mod priority_probe;
mod masked_priority_probe;

#[cfg(test)]
mod tests_fold64;

#[cfg(test)]
mod tests_midg_k24;
#[cfg(test)]
mod tests_f1;
#[cfg(test)]
mod tests_f2;

#[cfg(test)]
mod c55_tests;
