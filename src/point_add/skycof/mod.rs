//! SKY-COF research seam (inert in the default build; nothing here is called by `point_add::build`
//! unless `SKYCOF_TICK_SELFTEST` is set, and then the process exits after the selftest).
//!
//! * [`adder`]: room-aware exact (controlled) ripple adds.
//! * [`tick`]: the walk tick (Skywalk rails + Kaliski-frame cofactors), forward and reverse.
//! * [`selftest`]: gate-level selftests and the per-call cost report.
pub mod adder;
pub mod dec_selftest;
pub mod decoder;
pub mod effective_selector;
pub mod effective_selector_probe;
pub mod migration_header;
pub mod pa_probe;
pub mod packed_seam;
pub mod pointadd;
pub mod selftest;
pub mod tick;
pub mod walk;
pub mod walk_probe;

pub mod sentinel_handoff;
