//! Compile-time PZ/tail profile. Generated empirical envelopes are not proofs
//! of all-input success. The exact submitted profile remains the default.

#[derive(Clone, Copy, Debug)]
pub(super) struct Profile {
    pub id: &'static str,
    pub pz_cut: usize,
    pub rounds: usize,
    pub value_widths: &'static [u16],
    pub ctz_bits: usize,
    pub checkpoint_start: usize,
    pub handoff_unsigned_bits: usize,
    pub handoff_signed_bits: usize,
    pub payload_replay_start: usize,
    pub baseline_compatible: bool,
    pub provenance: &'static str,
}

include!("hybrid_profile_baseline_widths.rs");
include!("hybrid_profiles_generated.rs");

const fn str_eq(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}
const fn select() -> Profile {
    let name = match option_env!("HYBRID_PROFILE") {
        None => "cut360",
        Some(s) => s,
    };
    let mut i = 0;
    while i < PROFILES.len() {
        if str_eq(PROFILES[i].id, name) {
            return PROFILES[i];
        }
        i += 1;
    }
    panic!("HYBRID_PROFILE has no generated profile: install calibrated include; never reuse another cut's widths")
}
pub(super) const SELECTED: Profile = select();

const fn bits_needed(mut n: usize) -> usize {
    let mut bits = 0;
    while n > 0 {
        bits += 1;
        n >>= 1;
    }
    bits
}
pub(super) const fn baseline_layout(profile: Profile) -> bool {
    if !profile.baseline_compatible
        || profile.pz_cut != 360
        || profile.rounds != 224
        || profile.ctz_bits != 7
        || profile.checkpoint_start != 220
        || profile.value_widths.len() != 225
        || profile.payload_replay_start != 180
    {
        return false;
    }
    let mut i = 0;
    while i < 225 {
        if profile.value_widths[i] != BASELINE_WIDTHS[i] {
            return false;
        }
        i += 1;
    }
    true
}
pub(super) const fn validate(profile: Profile) {
    assert!(
        matches!(profile.pz_cut, 260 | 280 | 300 | 320 | 340 | 360),
        "cut outside initial profile ladder"
    );
    assert!(
        profile.rounds >= 16 && profile.rounds % 4 == 0,
        "tail rounds must be a multiple of four"
    );
    assert!(
        profile.value_widths.len() == profile.rounds + 1,
        "wrong number of tail boundary widths"
    );
    assert!(
        profile.checkpoint_start + 4 == profile.rounds,
        "checkpoint must start at N-4"
    );
    assert!(
        profile.ctz_bits == bits_needed(profile.value_widths[0] as usize),
        "CTZ count must include the initial width accumulator"
    );
    assert!(
        profile.payload_replay_start == 0
            || (profile.payload_replay_start >= 8
                && profile.payload_replay_start < profile.checkpoint_start),
        "invalid payload replay boundary"
    );
    let mut i = 0;
    while i < profile.value_widths.len() {
        assert!(
            profile.value_widths[i] >= 4 && profile.value_widths[i] <= 255,
            "unsupported finite signed width"
        );
        if i > 0 {
            assert!(
                profile.value_widths[i] <= profile.value_widths[i - 1],
                "tail envelope must be nonincreasing"
            );
        }
        if i >= profile.checkpoint_start {
            assert!(
                profile.value_widths[i] == 4,
                "checkpoint cannot cross width reduction"
            );
        }
        i += 1;
    }
    if profile.baseline_compatible {
        assert!(
            baseline_layout(profile),
            "baseline tag is reserved for the exact submitted profile"
        );
    } else {
        assert!(
            profile.handoff_unsigned_bits <= profile.handoff_signed_bits,
            "invalid handoff signed bound"
        );
        assert!(
            profile.handoff_signed_bits <= profile.value_widths[0] as usize,
            "handoff does not fit the new signed envelope"
        );
    }
}
const _: () = validate(SELECTED);

pub(super) const fn width_array<const N: usize>() -> [u8; N] {
    assert!(N == SELECTED.value_widths.len());
    let mut out = [0; N];
    let mut i = 0;
    while i < N {
        out[i] = SELECTED.value_widths[i] as u8;
        i += 1;
    }
    out
}
/// Existing proof-restricted arithmetic is enabled only for the exact baseline
/// layout. In particular the full-width rotation oracle also needs its margin
/// theorem, so merely keeping all comparator bits does not generalize it.
pub(super) const fn legacy_margin_allowed() -> bool {
    baseline_layout(SELECTED)
}
/// The old rank codec hardcodes CTZ<=85 and a terminal code for that alphabet.
pub(super) const fn legacy_metadata_allowed() -> bool {
    baseline_layout(SELECTED)
}
pub(crate) fn default_payload_replay_start() -> usize {
    SELECTED.payload_replay_start
}
pub(crate) const fn pz_cut() -> usize {
    SELECTED.pz_cut
}

const SOFT_CAPS: [&str; 7] = [
    "MIDQ_OUTER_VENT_QCAP",
    "MIDQ_PZ_VENT_QCAP",
    "MIDQ_PREFIX_QCAP",
    "MIDQ_CHUNK_COMPARE_QCAP",
    "MIDQ_CONTROLLED_ADD_QCAP",
    "MIDQ_CELL_QCAP",
    "MIDQ_ZERO_SCRATCH_QCAP",
];
fn parsed_runtime_cap(raw: Option<&str>) -> Option<usize> {
    raw.map(|s| {
        let cap = s.parse::<usize>().expect("HYBRID_QCAP must be an integer");
        assert!(
            (1000..=1132).contains(&cap),
            "HYBRID_QCAP outside1000..1132 exploration range"
        );
        cap
    })
}
fn runtime_cap() -> Option<usize> {
    parsed_runtime_cap(std::env::var("HYBRID_QCAP").ok().as_deref())
}
/// No override preserves the exact old hard ceiling1019, independently of the
/// seven old soft defaults1009. An explicit override replaces all seven soft
/// caps and this ceiling. It limits scratch selection, not allocator live size.
pub(crate) fn hard_ceiling() -> usize {
    runtime_cap().unwrap_or(1019)
}
pub(crate) fn configure_runtime_caps() {
    // Reject conflicts before any circuit construction.
    let _ = super::qretain::fixed_width();
    if let Ok(raw) = std::env::var("MIDQ_PZ_CUT") {
        assert_eq!(
            raw.parse::<usize>()
                .expect("MIDQ_PZ_CUT must be an integer"),
            SELECTED.pz_cut,
            "runtime MIDQ_PZ_CUT disagrees with compile-time HYBRID_PROFILE"
        );
    }
    if let Some(cap) = runtime_cap() {
        let cap = cap.to_string();
        for key in SOFT_CAPS {
            std::env::set_var(key, &cap);
        }
    }
    // A5-bit shift address cannot address q lanes32 and above. The legacy684
    // path is untouched. For a relaxed data-pack budget, cap only this padding
    // allocation, conditional on the existing support that true shifts fit5.
    let target = std::env::var("TRAILMIX_Q_TARGET")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(0);
    if target > 685 && super::trailmix_srot_width() == 5 {
        let old = std::env::var("TRAILMIX_Q_CAP")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
            .unwrap_or(99);
        if old > 32 {
            std::env::set_var("TRAILMIX_Q_CAP", "32");
        }
    }
}

pub(crate) fn report() {
    super::qretain::report();
    eprintln!("HYBRID_PROFILE id={} compile_time=true cut={} rounds={} handoff_width={} ctz_bits={} checkpoint_start={} replay_default={} baseline_compatible={} legacy_margin_shortcuts={} legacy_metadata={} provenance={}",
        SELECTED.id,SELECTED.pz_cut,SELECTED.rounds,SELECTED.value_widths[0],SELECTED.ctz_bits,
        SELECTED.checkpoint_start,SELECTED.payload_replay_start,baseline_layout(SELECTED),
        legacy_margin_allowed(),legacy_metadata_allowed(),SELECTED.provenance);
    eprintln!("HYBRID_RESOURCES explicit_global_cap={:?} hard_ceiling={} data_pack_target={} srot_bits={} counter_bits={} actual_peak_must_be_measured=true",
        runtime_cap(),hard_ceiling(),std::env::var("TRAILMIX_Q_TARGET").unwrap_or_else(|_|"unset".into()),super::trailmix_srot_width(),super::trailmix_counter_width());
    eprintln!("HYBRID_QUOTIENT allocation_cap={} generic_tag_bits=bit_length(raw_width) host_width_metadata_only=true legacy_rank_requires_raw18=true",std::env::var("TRAILMIX_Q_CAP").unwrap_or_else(|_|"unset".into()));
}

/// Root-owned diagnostic. reg_widths may initialize the existing thin schedule;
/// this is deliberately not part of the small static/native selftest.
pub(crate) fn dump_runtime_schedule() {
    use crate::point_add::trailmix_port::inversion::shrunken_pz_schedule::{
        reg_los, reg_widths, shift_bounds,
    };
    report();
    print!("{{\"profile\":\"{}\",\"cut\":{},\"rounds\":{},\"ctz_bits\":{},\"checkpoint_start\":{},\"value_widths\":{:?},\"runtime_prefix\":[",SELECTED.id,SELECTED.pz_cut,SELECTED.rounds,SELECTED.ctz_bits,SELECTED.checkpoint_start,SELECTED.value_widths);
    for i in 0..SELECTED.pz_cut {
        let (a, b, ca, cb, q) = reg_widths(i);
        let (la, lb, lca, lcb, lq) = reg_los(i);
        let (sd, sm) = shift_bounds(i);
        let ab = super::trailmix_ab_width(a.max(b));
        let cc = super::trailmix_cacb_width(ca.max(cb));
        let qq = super::trailmix_q_width_step(q, a, b, ca, cb);
        if i > 0 {
            print!(",");
        }
        print!("{{\"step\":{},\"raw\":[{},{},{},{},{}],\"effective\":[{},{},{},{},{}],\"lo\":[{},{},{},{},{}],\"shift_ceiling\":[{},{}]}}",i,a,b,ca,cb,q,ab,ab,cc,cc,qq,la,lb,lca,lcb,lq,sd,sm);
    }
    println!(
        "],\"srot_bits\":{},\"counter_bits\":{},\"no_terminal_admitted\":{},\"fixed_quotient_bits\":{}}}",
        super::trailmix_srot_width(),
        super::trailmix_counter_width(),
        super::prefix_no_terminal_eligible(0),
        super::qretain::fixed_width().unwrap_or(0)
    );
}

#[path = "hybrid_profile_selftest.rs"]
mod tests;
pub(crate) use tests::run as selftest;
