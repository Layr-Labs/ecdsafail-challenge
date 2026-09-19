//! Packed-prefix register layout (tools/spike/packed_design.md): two fixed
//! 257-wire rings R1 = [A | gap | cb], R2 = [B | gap | ca] with persisted
//! exponents. Each primitive lives in its own file with its own selftest.

#[path = "onehot_stream.rs"]
pub(crate) mod onehot_stream;
#[path = "ring_rotate.rs"]
pub(crate) mod ring_rotate;
pub(crate) mod window_gather;
#[path = "masked_add.rs"]
pub(crate) mod masked_add;
#[path = "capture_compare.rs"]
pub(crate) mod capture_compare;
#[path = "aligned_scan.rs"]
pub(crate) mod aligned_scan;
#[path = "exponent_arith.rs"]
pub(crate) mod exponent_arith;
/// P0 shape build: packed registers with no-op substeps (allocation timeline only).
#[path = "p0_shape.rs"]
pub(crate) mod p0_shape;
/// Packed division substep D0..D12 (design 3.1) and its oracle harness.
#[path = "division.rs"]
pub(crate) mod division;
/// Per-step envelope shared by the substeps (`StepWidths`), the packed peak budget.
#[path = "sched.rs"]
pub(crate) mod sched;
/// `shift ^= gate * ctz(q)` (direct ctz kernel, chunked to the packed scratch budget).
#[path = "ctz.rs"]
pub(crate) mod ctz;
/// Packed multiply substep M1..M12 (design 3.2), forward, and its oracle harness.
#[path = "multiply.rs"]
pub(crate) mod multiply;
/// The substep inverses under the plan's names (`division_cancel`, `multiply_cancel`).
#[path = "inverse.rs"]
pub(crate) mod inverse;
/// The per-step driver (design 3.3 / 3.4): exact role pair, real substeps, swap, terminal rows.
#[path = "driver.rs"]
pub(crate) mod driver;
/// Adversarial review harness of the multiply (2026-09-14): backward, round trips, wide steps, late terminators, thin schedule.
#[path = "multiply_review.rs"]
pub(crate) mod multiply_review;
/// Adversarial review harness of the driver (2026-09-14): pool-selected extreme rows at the widest steps, earliest terminators, S_0/teardown end to end.
#[path = "review_cases.rs"]
pub(crate) mod review_cases;

/// Run every packed primitive selftest (MIDQ_PACKED_SELFTEST=1).
#[allow(dead_code)]
pub(crate) fn selftest_all() {
    // `MIDQ_PACKED_SELFTEST_ONLY=<name>` runs one harness (the driver round
    // trip generates the production thin schedule, which is process-cached:
    // run it alone when a different schedule env was used earlier).
    if let Ok(only) = std::env::var("MIDQ_PACKED_SELFTEST_ONLY") {
        match only.as_str() {
            "masked_add" => masked_add::selftest(),
            "window_gather" => window_gather::selftest(),
            "aligned_scan" => aligned_scan::selftest(),
            "division" => division::selftest(),
            "multiply" => multiply::selftest(),
            "driver" => driver::selftest(),
            "multiply_review" => multiply_review::run(),
            "driver_review" => review_cases::run(),
            other => panic!("MIDQ_PACKED_SELFTEST_ONLY={other}: unknown harness"),
        }
        return;
    }
    onehot_stream::selftest();
    ring_rotate::selftest();
    window_gather::selftest();
    masked_add::selftest();
    capture_compare::selftest();
    aligned_scan::selftest();
    exponent_arith::selftest();
    division::selftest();
    multiply::selftest();
    driver::selftest();
    multiply_review::run();
    review_cases::run();
}
