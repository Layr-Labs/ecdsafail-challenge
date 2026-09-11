//! Conditional coefficient-margin certificate for alternate hybrid profiles.
//!
//! HYBRID_MARGIN_SUPPORT=exact-positive-l31 explicitly selects this support:
//! positive raw handoff; every GREEDY PZ/quotient transition has its exact nonnegative
//! integer lift; every active true pre-offset division shift and reverse
//! j+offset fits its actually used min(rot_bits,SROT) range; faithful quotient
//! flush, normalization, signed resizes and tail sums; canonical coefficient
//! initialization, with the subsequent canonicality induction in the proof.
//! These are input premises, not consequences of allocation or sampled success.
//!
//! Under that exact-lift premise, every begun division writes its true leading
//! quotient bit into the allocated q word. Allocations<=32 therefore imply
//! leading index L<=31, including unfinished divisions. Width alone is not a
//! membership proof. The legacy profile follows its original code unchanged.
use ruint::Uint;
type Wide = Uint<512, 8>;
const LEADING_BOUND: usize = 31;

#[derive(Clone, Copy, Debug)]
pub(super) struct Bounds {
    pub full_fused: bool,
    pub forward_drop: Option<usize>,
    pub inverse_drop: Option<usize>,
}
fn modulus() -> Wide {
    (Wide::from(1) << 256) - (Wide::from(1) << 32) - Wide::from(977)
}
fn gap_minus_one() -> Wide {
    (Wide::from(1) << 32) + Wide::from(976)
}

/// All products fit512 bits: first require D*(1+correction)<p, hence D<2^256
/// before multiplying by2^k (k<=255). There is no floating-point threshold.
fn largest_drop(p: Wide, d: Wide, correction: Wide) -> Option<usize> {
    let one = Wide::from(1);
    if p <= d * (one + correction) {
        return None;
    }
    (0..=255).rev().find(|&k| p > d * ((one << k) + correction))
}
pub(super) fn numerical_bounds(value_bits: usize, leading: usize) -> Bounds {
    assert!((1..=255).contains(&value_bits));
    assert!(
        leading <= 63,
        "bounded certificate arithmetic supports leading<=63"
    );
    let one = Wide::from(1);
    let p = modulus();
    let value_bound = one << value_bits;
    // q_max=2^(L+1)-1; the threshold pair gives p<2*(q_max+2)*value_bound*V.
    let denominator = Wide::from(2) * ((one << (leading + 1)) + one) * value_bound;
    let forward_correction = Wide::from(2) * gap_minus_one();
    let inverse_correction = gap_minus_one();
    if p <= Wide::from(2) * value_bound {
        return Bounds {
            full_fused: false,
            forward_drop: None,
            inverse_drop: None,
        };
    }
    Bounds {
        full_fused: p > denominator * forward_correction,
        forward_drop: largest_drop(p, denominator, forward_correction),
        inverse_drop: largest_drop(p, denominator, inverse_correction),
    }
}

fn flag(name: &str) -> bool {
    std::env::var(name).ok().as_deref() == Some("1")
}
pub(super) fn named_support_enabled() -> bool {
    std::env::var("HYBRID_MARGIN_SUPPORT").ok().as_deref() == Some("exact-positive-l31")
}
fn configured_support() -> bool {
    if !named_support_enabled()
        || super::trailmix_srot_width() != 5
        || ![
            "MIDQ_PZ_PINGPONG_TAIL",
            "MIDQ_PREFIX_NO_TERMINAL",
            "LOWQ_HYBRID_GATE_HOLD",
            "MIDQ_RETAIN_DIV_LENGTHS",
            "MIDQ_RETAIN_MUL_LENGTHS",
        ]
        .into_iter()
        .all(flag)
        || !super::prefix_no_terminal_eligible(0)
    {
        return false;
    }
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::reg_widths;
    (0..super::MIDQ_PZ_CUT).all(|step| {
        let (a, b, ca, cb, q) = reg_widths(step);
        super::trailmix_q_width_step(q, a, b, ca, cb) <= LEADING_BOUND + 1
    })
}
pub(super) fn admitted_bounds() -> Option<Bounds> {
    configured_support()
        .then(|| numerical_bounds(super::MIDQ_TAIL_VALUE_WIDTH[0] as usize, LEADING_BOUND))
}
pub(super) fn full_fused_allowed() -> bool {
    admitted_bounds().is_some_and(|b| b.full_fused)
}
pub(super) fn forward_drop() -> usize {
    admitted_bounds().and_then(|b| b.forward_drop).unwrap_or(0)
}
pub(super) fn inverse_drop() -> usize {
    admitted_bounds().and_then(|b| b.inverse_drop).unwrap_or(0)
}

pub(crate) fn report() {
    if named_support_enabled() {
        let b = admitted_bounds();
        eprintln!("HYBRID_MARGIN support=exact-positive-l31 numeric_membership_not_checked=true value_bound=2^{} every_begun_leading_bound={} actual_rotator_fit_is_a_premise=true admitted={b:?} legacy_path_unchanged={}",super::MIDQ_TAIL_VALUE_WIDTH[0],LEADING_BOUND,super::hybrid_profile::legacy_margin_allowed());
    }
}

#[path = "hybrid_margin_selftest.rs"]
mod tests;
pub(crate) use tests::run as selftest;
