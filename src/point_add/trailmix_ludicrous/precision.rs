//! Parsing and lookup for the divstep-walk "precision" (schedule-widening) spec.
//!
//! The baked `SCHED_J2` schedule truncates the divstep working registers, which is one of
//! the two remaining structural sources of classical mismatch in the gcd walk (it drops a
//! nonzero bit and still terminates). Widening register `i` by a `margin` recovers the
//! dropped bit -- but only if the comparator window computed by `cmp_window` in `gcd.rs` is
//! widened by that SAME margin, otherwise the top-k compared slice shifts upward and the
//! walk starts comparing different bits than the baked circuit did. `sched_margin` is the
//! single source of truth both call sites (forward and reverse gcd walk, in `gcd.rs`) read
//! from, so the two widenings can never drift apart -- see
//! `schedule_margin_keeps_the_original_compared_bits` below for the algebraic invariant this
//! guarantees, and `gcd::tests::cmp_window_preserves_top_slice_invariant_for_real_margins`
//! for the same invariant exercised through the actual `cmp_window` implementation.
//!
//! `sched_margin` reads the `TLM_SCHED_MARGIN` env var, generalizing the old two-knob
//! `TLM_SCHED_J2_WIDEN` / `TLM_SCHED_J2_WIDEN_AT` mechanism (a global margin plus a
//! point-list of per-index overrides) into one spec string that additionally supports
//! inclusive ranges. Grammar, comma-separated:
//!   - `42`        -- bare index, margin 1 at i=42
//!   - `154:2`     -- explicit margin 2 at i=154
//!   - `225-240:3` -- margin 3 for every i in [225, 240] inclusive
//! Duplicate matches at the same index take the maximum margin. Absent (or empty) is an
//! additive no-op, not an absolute reset: the effective margin is `max` of the env spec
//! and `schedule::BAKED_SCHED_MARGIN` (Task 6 Step 7's baked lookup, authoritative by
//! default), so an unset env var reproduces the baked schedule exactly, and the pre-Step-7
//! tree (an empty `BAKED_SCHED_MARGIN`) reproduces "margin 0 everywhere" exactly as
//! before. A malformed spec panics naming the offending string -- silently ignoring a
//! typo'd diagnostic override would defeat the point of running one.

use super::arith;
use super::schedule;

/// One parsed spec entry: apply `value` to every index in the half-open range `[lo, hi)`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct RangeValue {
    pub(crate) lo: usize,
    pub(crate) hi: usize,
    pub(crate) value: usize,
}

/// Env var carrying the margin spec described in the module docs above.
const SCHED_MARGIN_ENV: &str = "TLM_SCHED_MARGIN";

/// Parse a comma-separated precision-margin spec into ranges. Pure: never touches the
/// environment, so it is fully unit-testable on its own.
///
/// Grammar per comma-separated entry:
///   `INDEX`       -- value defaults to 1
///   `INDEX:VALUE`
///   `LO-HI:VALUE` -- inclusive on both ends
/// Reversed ranges (`hi < lo`) and unparsable integers are errors. An empty spec parses to
/// an empty (no-op) list.
pub(crate) fn parse_ranges(spec: &str) -> Result<Vec<RangeValue>, String> {
    let spec = spec.trim();
    if spec.is_empty() {
        return Ok(Vec::new());
    }
    let mut out = Vec::with_capacity(spec.split(',').count());
    for entry in spec.split(',') {
        let entry = entry.trim();
        if entry.is_empty() {
            return Err(format!("empty entry in spec {spec:?}"));
        }
        let (range_part, value_part) = match entry.split_once(':') {
            Some((r, v)) => (r, Some(v)),
            None => (entry, None),
        };
        let (lo, hi) = if let Some((lo_s, hi_s)) = range_part.split_once('-') {
            let lo = lo_s
                .trim()
                .parse::<usize>()
                .map_err(|_| format!("bad range start in {entry:?}"))?;
            let hi = hi_s
                .trim()
                .parse::<usize>()
                .map_err(|_| format!("bad range end in {entry:?}"))?;
            if hi < lo {
                return Err(format!("reversed range in {entry:?}: {lo} > {hi}"));
            }
            (lo, hi + 1)
        } else {
            let point = range_part
                .trim()
                .parse::<usize>()
                .map_err(|_| format!("bad index in {entry:?}"))?;
            (point, point + 1)
        };
        let value = match value_part {
            Some(v) => v
                .trim()
                .parse::<usize>()
                .map_err(|_| format!("bad value in {entry:?}"))?,
            None => 1,
        };
        out.push(RangeValue { lo, hi, value });
    }
    Ok(out)
}

/// Look up the margin at index `i`: the maximum `value` among every range that contains it,
/// or 0 if none do.
pub(crate) fn value_at(ranges: &[RangeValue], i: usize) -> usize {
    ranges
        .iter()
        .filter(|r| i >= r.lo && i < r.hi)
        .map(|r| r.value)
        .max()
        .unwrap_or(0)
}

/// Render `ranges` as a `schedule.rs`-ready `pub static` array of `RangeValue` literals,
/// sorted by `(lo, hi, value)` so the output is deterministic regardless of the input
/// slice's order (Task 6 Step 7). The output is meant to be pasted verbatim into
/// `schedule.rs` as the baked default for `name`, and is directly consumable by
/// `value_at` since it is literally a `&[RangeValue]` -- no separate tuple-to-RangeValue
/// conversion step is needed at the call site.
pub(crate) fn render_profile(name: &str, ranges: &[RangeValue]) -> String {
    let mut sorted: Vec<RangeValue> = ranges.to_vec();
    sorted.sort_by_key(|r| (r.lo, r.hi, r.value));
    let mut out = format!("pub static {name}: &[RangeValue] = &[\n");
    for r in &sorted {
        out.push_str(&format!(
            "    RangeValue {{ lo: {}, hi: {}, value: {} }},\n",
            r.lo, r.hi, r.value
        ));
    }
    out.push_str("];\n");
    out
}

/// The margin to add to `SCHED_J2[i]` (and, coupled, to the comparator window inside
/// `cmp_window`) for divstep `i`.
///
/// Task 6 Step 7: the baked lookup (`schedule::BAKED_SCHED_MARGIN`, populated by pasting
/// `render_profile`'s output for the accepted search profile) is now authoritative --
/// `TLM_SCHED_MARGIN` is an *additive* diagnostic override on top of it, not a
/// replacement, and defaults to no override (0) when unset. Concretely: the effective
/// margin at `i` is `max(baked_margin(i), env_margin(i))`, which is exactly what you'd
/// get by parsing the baked and env range lists into one pool and calling `value_at` on
/// the union (duplicate matches already take the max there) -- computing the two halves
/// separately and taking `.max()` is just the same thing without allocating a merged
/// `Vec`. Before any baking (an empty `BAKED_SCHED_MARGIN`, i.e. every task before this
/// one), `baked_margin(i)` is always 0, so this reproduces the pre-Step-7 env-only
/// behavior byte for byte -- see `sched_margin_defaults_to_baked_value_when_env_is_unset`.
pub(crate) fn sched_margin(i: usize) -> usize {
    let baked = value_at(schedule::BAKED_SCHED_MARGIN, i);
    let env = match std::env::var(SCHED_MARGIN_ENV) {
        Ok(spec) => {
            let ranges = parse_ranges(&spec).unwrap_or_else(|e| {
                panic!("{SCHED_MARGIN_ENV}={spec:?} is not a valid precision spec: {e}")
            });
            value_at(&ranges, i)
        }
        Err(_) => 0,
    };
    baked.max(env)
}

/// Which GCD-apply pass a contextual fold width applies to.
///
/// `gcd::apply_step_reverse` runs the modular folds during the *inverse-forward* walk
/// (`gcd::forward_gcd_jump`'s `apply_inv` argument, the `"inverse-forward"` trace phase),
/// and `gcd::apply_step_forward` runs them during the *multiply-reverse* walk
/// (`gcd::reverse_gcd_jump`'s `apply_fwd` argument, the `"multiply-reverse"` trace phase).
/// The variant names below track those trace-phase names, not the (identically named but
/// structurally unrelated) `apply_step_forward`/`apply_step_reverse` function names.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ApplyPass {
    InverseForward,
    MultiplyReverse,
}

impl ApplyPass {
    /// The `TLM_APPLY_LSBS` spec tag for this pass.
    fn tag(self) -> &'static str {
        match self {
            ApplyPass::InverseForward => "ifwd",
            ApplyPass::MultiplyReverse => "mrev",
        }
    }
}

/// Env var carrying the per-pass fold-width spec described below.
const APPLY_LSBS_ENV: &str = "TLM_APPLY_LSBS";

/// Parse a `TLM_APPLY_LSBS`-shaped spec, keeping only the entries tagged for `pass`.
///
/// Grammar, comma-separated: `TAG:RANGE_ENTRY`, where `TAG` is `ifwd` or `mrev` and
/// `RANGE_ENTRY` is anything a single `parse_ranges` entry accepts (`INDEX`, `INDEX:VALUE`,
/// or `LO-HI:VALUE`), e.g. `ifwd:0-260:57,mrev:0-260:61`. Entries tagged for the other pass
/// are still parsed (so a typo in them surfaces immediately rather than silently doing
/// nothing) but are discarded from the result. Pure: never touches the environment.
pub(crate) fn parse_apply_lsbs_ranges(
    spec: &str,
    pass: ApplyPass,
) -> Result<Vec<RangeValue>, String> {
    let spec = spec.trim();
    if spec.is_empty() {
        return Ok(Vec::new());
    }
    let mut out = Vec::new();
    for entry in spec.split(',') {
        let entry = entry.trim();
        if entry.is_empty() {
            return Err(format!("empty entry in spec {spec:?}"));
        }
        let (tag, rest) = entry
            .split_once(':')
            .ok_or_else(|| format!("entry {entry:?} is missing a ifwd:/mrev: pass tag"))?;
        let tag = tag.trim();
        if tag != "ifwd" && tag != "mrev" {
            return Err(format!(
                "entry {entry:?} has unknown pass tag {tag:?} (expected ifwd or mrev)"
            ));
        }
        let parsed = parse_ranges(rest)?;
        if tag == pass.tag() {
            out.extend(parsed);
        }
    }
    Ok(out)
}

/// The fold width (`lsbs`) to use for GCD-apply-path modular folds at divstep `i` in
/// `pass`.
///
/// Task 6 Step 7: the baked lookup (`schedule::BAKED_APPLY_LSBS_IFWD`/`_MREV`, populated
/// by pasting `render_profile`'s output for the accepted search profile) is now
/// authoritative -- `TLM_APPLY_LSBS` is an *additive* diagnostic override on top of it,
/// not a replacement, and defaults to no override when unset. The effective width is
/// `max(baked_width(i), env_width(i))`, falling back to `arith::LSBS` only when NEITHER
/// the baked table nor the env spec covers `i` for this pass (both `value_at`-return 0,
/// the "uncovered" sentinel) -- exactly the pre-Step-7 fallback, just fed by the max of
/// two sources instead of one. Before any baking (empty `BAKED_APPLY_LSBS_*`, i.e. every
/// task before this one), this reproduces the pre-Step-7 env-only behavior byte for byte
/// -- see `apply_lsbs_defaults_to_baked_value_when_env_is_unset`.
///
/// This is the only knob that widens the GCD-apply folds. `square.rs`'s `mod_sub` and the
/// rest of the coordinate-arithmetic path keep reading `arith::LSBS` directly and are
/// unaffected by this spec -- see the module docs above for why the two must stay
/// independent.
pub(crate) fn apply_lsbs(pass: ApplyPass, i: usize) -> usize {
    let baked_ranges = match pass {
        ApplyPass::InverseForward => schedule::BAKED_APPLY_LSBS_IFWD,
        ApplyPass::MultiplyReverse => schedule::BAKED_APPLY_LSBS_MREV,
    };
    let baked = value_at(baked_ranges, i);
    let env = match std::env::var(APPLY_LSBS_ENV) {
        Ok(spec) => {
            let ranges = parse_apply_lsbs_ranges(&spec, pass).unwrap_or_else(|e| {
                panic!("{APPLY_LSBS_ENV}={spec:?} is not a valid apply-lsbs spec: {e}")
            });
            value_at(&ranges, i)
        }
        Err(_) => 0,
    };
    let v = baked.max(env);
    if v == 0 { arith::LSBS } else { v }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::schedule::{GAP_J2, ITERS, SCHED_J2};

    #[test]
    fn parses_points_ranges_and_explicit_values() {
        assert_eq!(
            parse_ranges("42,154:2,225-240:3").unwrap(),
            vec![
                RangeValue { lo: 42, hi: 43, value: 1 },
                RangeValue { lo: 154, hi: 155, value: 2 },
                RangeValue { lo: 225, hi: 241, value: 3 },
            ]
        );
    }

    #[test]
    fn rejects_reversed_or_empty_ranges() {
        assert!(parse_ranges("9-4:1").is_err());
        assert!(parse_ranges("").unwrap().is_empty());
    }

    #[test]
    fn duplicate_matches_take_the_maximum() {
        // 4 covers index 10 too (range 5-15), and is larger than the point override of 1.
        let ranges = parse_ranges("10:1,5-15:4").unwrap();
        assert_eq!(value_at(&ranges, 10), 4);
        // Outside every range: no margin.
        assert_eq!(value_at(&ranges, 4), 0);
    }

    /// Serializes every test below that mutates `TLM_SCHED_MARGIN`: cargo runs tests in
    /// this binary in parallel by default and the env var is process-global, so without a
    /// lock one test's `set_var` can race another's "must be unset" check (same hazard
    /// `APPLY_LSBS_ENV_LOCK` below guards against). Recovers from a poisoned lock the same
    /// way.
    static SCHED_MARGIN_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    fn lock_sched_margin_env() -> std::sync::MutexGuard<'static, ()> {
        SCHED_MARGIN_ENV_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    #[test]
    fn malformed_spec_panics_naming_the_offending_string() {
        let _guard = lock_sched_margin_env();
        std::env::set_var(SCHED_MARGIN_ENV, "not-a-spec:::");
        let result = std::panic::catch_unwind(|| sched_margin(0));
        std::env::remove_var(SCHED_MARGIN_ENV);
        let err = result.expect_err("malformed spec must panic");
        let msg = err
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| err.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_default();
        assert!(
            msg.contains("not-a-spec:::"),
            "panic message should name the offending spec, got: {msg}"
        );
    }

    /// Task 6 Step 7: with `TLM_SCHED_MARGIN` unset, the effective margin must come
    /// straight from the baked table -- computed here via the same `value_at` call
    /// `sched_margin` itself makes, so this test stays correct regardless of what has
    /// actually been baked (including the pre-Step-7 state, where `BAKED_SCHED_MARGIN`
    /// is empty and every index reads back 0, byte-identical to the old env-only
    /// behavior).
    #[test]
    fn sched_margin_defaults_to_baked_value_when_env_is_unset() {
        let _guard = lock_sched_margin_env();
        assert!(
            std::env::var(SCHED_MARGIN_ENV).is_err(),
            "{SCHED_MARGIN_ENV} must be unset for this test to exercise the baked-only path"
        );
        for i in [0usize, 11, 50, 150, 257] {
            assert_eq!(sched_margin(i), value_at(schedule::BAKED_SCHED_MARGIN, i));
        }
    }

    /// Task 6 Step 7: the env override is additive (max), never a replacement -- an env
    /// spec that asks for LESS than the baked margin at a baked-covered index must not
    /// narrow it, and a spec that asks for MORE must win.
    #[test]
    fn sched_margin_env_override_is_additive_not_a_replacement() {
        let _guard = lock_sched_margin_env();
        // Pick an index the baked table actually covers; if none does (an unbaked tree),
        // the two branches below degenerate to the same 0-vs-env comparison, which is
        // still a valid (if less interesting) exercise of the max() combinator.
        let i = (0..schedule::ITERS)
            .find(|&i| value_at(schedule::BAKED_SCHED_MARGIN, i) > 0)
            .unwrap_or(0);
        let baked = value_at(schedule::BAKED_SCHED_MARGIN, i);

        std::env::set_var(SCHED_MARGIN_ENV, format!("{i}:0"));
        let low = std::panic::catch_unwind(|| sched_margin(i));
        std::env::remove_var(SCHED_MARGIN_ENV);
        assert_eq!(low.unwrap(), baked, "a lower env value must not narrow the baked margin");

        let higher = baked + 5;
        std::env::set_var(SCHED_MARGIN_ENV, format!("{i}:{higher}"));
        let raised = std::panic::catch_unwind(|| sched_margin(i));
        std::env::remove_var(SCHED_MARGIN_ENV);
        assert_eq!(raised.unwrap(), higher, "a higher env value must win over the baked margin");
    }

    /// Serializes every test below that mutates `TLM_APPLY_LSBS`: cargo runs tests in this
    /// binary in parallel by default and the env var is process-global, so without a lock
    /// one test's `set_var` can race another's "must be unset" check. Recovers from a
    /// poisoned lock (a *held* guard's thread panicking, as opposed to a panic caught by
    /// `catch_unwind` inside the guarded region below, which never poisons) rather than
    /// cascading one failure into every later test.
    static APPLY_LSBS_ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    fn lock_apply_lsbs_env() -> std::sync::MutexGuard<'static, ()> {
        APPLY_LSBS_ENV_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    /// An index guaranteed to be uncovered by whatever profile is currently baked into
    /// `schedule::BAKED_APPLY_LSBS_IFWD`/`_MREV`, for tests below that need to exercise
    /// the env-only (or the true `arith::LSBS` fallback) path in isolation from Step 7's
    /// baked defaults. Panics loudly -- rather than silently asserting something false --
    /// if a future re-bake ever covers every one of `ITERS` indices for both passes.
    fn index_uncovered_by_baked_apply_lsbs() -> usize {
        (0..schedule::ITERS)
            .find(|&i| {
                value_at(schedule::BAKED_APPLY_LSBS_IFWD, i) == 0
                    && value_at(schedule::BAKED_APPLY_LSBS_MREV, i) == 0
            })
            .expect("expected at least one index uncovered by the baked apply-lsbs tables")
    }

    /// Task 6 Step 7: with `TLM_APPLY_LSBS` unset, the effective width must come straight
    /// from the baked table (falling back to `arith::LSBS` only where the baked table
    /// itself does not cover `i`), computed here via the same `value_at` call `apply_lsbs`
    /// itself makes -- so this test stays correct regardless of what has actually been
    /// baked (including the pre-Step-7 state, where both `BAKED_APPLY_LSBS_*` are empty
    /// and every index falls through to `arith::LSBS`, byte-identical to the old
    /// env-only behavior).
    #[test]
    fn apply_lsbs_defaults_to_baked_value_when_env_is_unset() {
        let _guard = lock_apply_lsbs_env();
        assert!(
            std::env::var(APPLY_LSBS_ENV).is_err(),
            "{APPLY_LSBS_ENV} must be unset for this test to exercise the baked-only path"
        );
        for i in [0usize, 32, 100, 200, 257] {
            let expect = |ranges: &[RangeValue]| {
                let v = value_at(ranges, i);
                if v == 0 { arith::LSBS } else { v }
            };
            assert_eq!(
                apply_lsbs(ApplyPass::InverseForward, i),
                expect(schedule::BAKED_APPLY_LSBS_IFWD)
            );
            assert_eq!(
                apply_lsbs(ApplyPass::MultiplyReverse, i),
                expect(schedule::BAKED_APPLY_LSBS_MREV)
            );
        }
    }

    #[test]
    fn apply_lsbs_ifwd_range_affects_only_inverse_forward() {
        let _guard = lock_apply_lsbs_env();
        let i = index_uncovered_by_baked_apply_lsbs();
        std::env::set_var(APPLY_LSBS_ENV, format!("ifwd:{i}:57"));
        let result = std::panic::catch_unwind(|| {
            assert_eq!(apply_lsbs(ApplyPass::InverseForward, i), 57);
            assert_eq!(apply_lsbs(ApplyPass::MultiplyReverse, i), arith::LSBS);
        });
        std::env::remove_var(APPLY_LSBS_ENV);
        result.unwrap();
    }

    #[test]
    fn apply_lsbs_mrev_range_affects_only_multiply_reverse() {
        let _guard = lock_apply_lsbs_env();
        let i = index_uncovered_by_baked_apply_lsbs();
        std::env::set_var(APPLY_LSBS_ENV, format!("mrev:{i}:61"));
        let result = std::panic::catch_unwind(|| {
            assert_eq!(apply_lsbs(ApplyPass::MultiplyReverse, i), 61);
            assert_eq!(apply_lsbs(ApplyPass::InverseForward, i), arith::LSBS);
        });
        std::env::remove_var(APPLY_LSBS_ENV);
        result.unwrap();
    }

    #[test]
    fn apply_lsbs_combined_spec_keeps_passes_independent() {
        let _guard = lock_apply_lsbs_env();
        let i = index_uncovered_by_baked_apply_lsbs();
        std::env::set_var(APPLY_LSBS_ENV, format!("ifwd:{i}:57,mrev:{i}:61"));
        let result = std::panic::catch_unwind(|| {
            assert_eq!(apply_lsbs(ApplyPass::InverseForward, i), 57);
            assert_eq!(apply_lsbs(ApplyPass::MultiplyReverse, i), 61);
        });
        std::env::remove_var(APPLY_LSBS_ENV);
        result.unwrap();
    }

    /// Task 6 Step 7: the env override is additive (max), never a replacement -- an env
    /// spec that asks for LESS than the baked width at a baked-covered index must not
    /// narrow it, and a spec that asks for MORE must win. Mirrors
    /// `sched_margin_env_override_is_additive_not_a_replacement`.
    ///
    /// The "must not narrow" half only makes sense where the baked table genuinely
    /// covers `i` (`value_at(...) > 0`): where it does not, `apply_lsbs`'s literal-0
    /// sentinel means an env value of `1` legitimately IS the effective width (there is
    /// no baked floor to protect), not a synonym for the `arith::LSBS` fallback -- so
    /// that half is skipped, loudly, on an entirely-unbaked tree instead of asserting
    /// something that was never true.
    #[test]
    fn apply_lsbs_env_override_is_additive_not_a_replacement() {
        let _guard = lock_apply_lsbs_env();
        for (pass, baked_ranges) in [
            (ApplyPass::InverseForward, schedule::BAKED_APPLY_LSBS_IFWD),
            (ApplyPass::MultiplyReverse, schedule::BAKED_APPLY_LSBS_MREV),
        ] {
            match (0..schedule::ITERS).find(|&i| value_at(baked_ranges, i) > 0) {
                Some(i) => {
                    let baked = value_at(baked_ranges, i);
                    std::env::set_var(APPLY_LSBS_ENV, format!("{}:{i}:1", pass.tag()));
                    let low = std::panic::catch_unwind(|| apply_lsbs(pass, i));
                    std::env::remove_var(APPLY_LSBS_ENV);
                    assert_eq!(
                        low.unwrap(),
                        baked,
                        "a lower env value must not narrow the baked width"
                    );

                    let higher = baked + 5;
                    std::env::set_var(APPLY_LSBS_ENV, format!("{}:{i}:{higher}", pass.tag()));
                    let raised = std::panic::catch_unwind(|| apply_lsbs(pass, i));
                    std::env::remove_var(APPLY_LSBS_ENV);
                    assert_eq!(
                        raised.unwrap(),
                        higher,
                        "a higher env value must win over the baked width"
                    );
                }
                None => {
                    eprintln!(
                        "apply_lsbs_env_override_is_additive_not_a_replacement: \
                         BAKED_APPLY_LSBS for {:?} is entirely empty, skipping the \
                         narrow-doesn't-win half (nothing to protect)",
                        pass
                    );
                }
            }
        }
    }

    #[test]
    fn apply_lsbs_malformed_spec_panics_naming_the_offending_string() {
        let _guard = lock_apply_lsbs_env();
        std::env::set_var(APPLY_LSBS_ENV, "not-a-spec:::");
        let result = std::panic::catch_unwind(|| apply_lsbs(ApplyPass::InverseForward, 0));
        std::env::remove_var(APPLY_LSBS_ENV);
        let err = result.expect_err("malformed spec must panic");
        let msg = err
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| err.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_default();
        assert!(
            msg.contains("not-a-spec:::"),
            "panic message should name the offending spec, got: {msg}"
        );
    }

    #[test]
    fn parse_apply_lsbs_ranges_rejects_missing_or_unknown_tag() {
        assert!(parse_apply_lsbs_ranges("42", ApplyPass::InverseForward).is_err());
        assert!(parse_apply_lsbs_ranges("xyz:42", ApplyPass::InverseForward).is_err());
    }

    /// Step 7 of the Task 6 brief: `render_profile`'s output must be exact, byte-for-byte,
    /// on a fixed, minimal input -- not just "parses back to the same ranges". This is what
    /// lets a human (or a later task) trust "apply that exact generated text to schedule.rs"
    /// without re-deriving what the renderer is supposed to produce.
    #[test]
    fn render_profile_matches_fixed_expected_output() {
        let ranges = [RangeValue { lo: 42, hi: 43, value: 1 }];
        let out = render_profile("TEST_PROFILE", &ranges);
        assert_eq!(
            out,
            "pub static TEST_PROFILE: &[RangeValue] = &[\n    RangeValue { lo: 42, hi: 43, value: 1 },\n];\n"
        );
    }

    /// A multi-entry profile must come out sorted (by `lo`, matching the order a human
    /// scanning the source top-to-bottom would expect the divstep index to advance in),
    /// regardless of the order the caller happened to build the slice in.
    #[test]
    fn render_profile_sorts_multiple_entries_by_lo() {
        let ranges = [
            RangeValue { lo: 100, hi: 200, value: 3 },
            RangeValue { lo: 0, hi: 10, value: 1 },
        ];
        let out = render_profile("SORTED_PROFILE", &ranges);
        assert_eq!(
            out,
            "pub static SORTED_PROFILE: &[RangeValue] = &[\n    RangeValue { lo: 0, hi: 10, value: 1 },\n    RangeValue { lo: 100, hi: 200, value: 3 },\n];\n"
        );
    }

    /// An empty profile still renders a syntactically valid, empty static array -- this is
    /// what a not-yet-baked table (or a range dimension nobody ever widened) looks like.
    #[test]
    fn render_profile_handles_empty_ranges() {
        let out = render_profile("EMPTY_PROFILE", &[]);
        assert_eq!(out, "pub static EMPTY_PROFILE: &[RangeValue] = &[\n];\n");
    }

    /// Step 5 of the task brief: a pure algebraic restatement of the invariant that
    /// widening `SCHED_J2[i]` and the comparator window by the same margin leaves the
    /// number of *dropped* (non-compared) low bits unchanged. This is deliberately
    /// implementation-free -- it only uses the baked tables -- and is complemented by
    /// `gcd::tests::cmp_window_preserves_top_slice_invariant_for_real_margins`, which
    /// exercises the same invariant through the actual `cmp_window` function.
    #[test]
    fn schedule_margin_keeps_the_original_compared_bits() {
        for i in 0..ITERS {
            for margin in 0..=8 {
                let old_n = SCHED_J2[i] as usize;
                let old_k = GAP_J2[i].min(SCHED_J2[i]) as usize;
                if old_n + margin > 256 {
                    continue;
                }
                let new_n = (old_n + margin).min(256);
                let new_k = (old_k + margin).min(new_n);
                assert_eq!(old_n - old_k, new_n - new_k);
            }
        }
    }
}
