//! SKY-COF research seam (inert in the default build; nothing here is called by `point_add::build`
//! unless `SKYCOF_TICK_SELFTEST` is set, and then the process exits after the selftest).
//!
//! * [`adder`]: room-aware exact (controlled) ripple adds.
//! * [`tick`]: the walk tick (Skywalk rails + Kaliski-frame cofactors), forward and reverse.
//! * [`selftest`]: gate-level selftests and the per-call cost report.
pub mod adder;
pub mod decoder;
pub mod k2dec;
pub mod k2_selftest;
pub mod dec_selftest;
pub mod selftest;
pub mod tick;
pub mod walk;
pub mod pointadd;
pub mod walk_probe;
pub mod pa_probe;
