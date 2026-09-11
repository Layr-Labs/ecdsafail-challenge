//! Explicit fixed pending-quotient storage for the existing SROT5 route.
//! HYBRID_QRETAIN=32 overrides both thin q taper and target-induced q clipping.
//! It does not force any one-A, CLZ, carry, margin or metadata optimization.
//! The semantic support still requires exact greedy PZ transitions, true
//! per-rotator shift/window fit and faithful value/coefficient widths. Only
//! quotient-storage losses are removed; allocation alone proves no membership.

pub(crate) const WIDTH: usize = 32;

fn requested(value: Option<&str>) -> bool {
    match value {
        None | Some("0" | "off") => false,
        Some("32") => true,
        _ => panic!("HYBRID_QRETAIN must be32 or off (0)"),
    }
}

pub(crate) fn fixed_width() -> Option<usize> {
    if !requested(std::env::var("HYBRID_QRETAIN").ok().as_deref()) {
        return None;
    }
    assert_eq!(
        super::trailmix_srot_width(),
        5,
        "fixed q32 is scoped to SROT5"
    );
    assert_eq!(
        super::env_usize("TRAILMIX_Q_TARGET", 0),
        684,
        "fixed q32 preserves Q_TARGET684 and its existing backend guards"
    );
    assert!(
        super::midq_tail_enabled(),
        "fixed q32 is scoped to the hybrid prefix"
    );
    assert!(
        super::env_usize("TRAILMIX_Q_CAP", 99).max(1) >= WIDTH,
        "explicit quotient cap below32 conflicts with fixed q32"
    );
    Some(WIDTH)
}

pub(crate) fn initial_width(raw: usize) -> usize {
    fixed_width().unwrap_or_else(|| raw.max(1))
}

/// Use the same policy as the actual allocator, before scalar repair checks.
/// Model-only shrinking guards have no role in the fixed physical q word.
pub(crate) fn apply_to_model_rows(rows: &mut [[u16; 5]]) -> bool {
    let Some(width) = fixed_width() else {
        return false;
    };
    for row in rows {
        row[4] = width as u16;
    }
    true
}

pub(crate) fn report() {
    if let Some(width) = fixed_width() {
        eprintln!("HYBRID_QRETAIN fixed_bits={width} initial_and_prefix=true overrides_thin_and_target_q_taper=true Q_TARGET=684 one_A_borrow_CLZ_flags_unchanged=true support=exact_greedy_true_SROT5_fit quotient_membership_not_inferred_from_allocation=true generic_tag_bits=6 legacy_rank_q18_ineligible=true actual_Q_T_unmeasured_by_policy=true");
    }
}

#[path = "qretain_selftest.rs"]
mod tests;
pub(crate) use tests::run as selftest;
