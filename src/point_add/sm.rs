//! q631 / sm (agent sm, 2026-11-19; local research, NOT part of any package; nothing in the builder calls it): the park-seam
//! rewrites of the two divides, each behind its own switch that is OFF (sm12::ON, sm4::ON = false).
//!   sm12: ITEM 12, applied after i12w::rewrite_full (every agent-i12 switch on): ipark seam + unpark head with lane 258 free.
//!   sm4:  ITEM 4, applied after i4g -> i4w R1 -> i4dwalk -> i4ewalk: ipark seam with lane 258 free.
//! Report: ~/Projects/ecdsafail/q631/sm/summary.py.
#[path = "sm12.rs"]
#[allow(dead_code)]
pub mod sm12;
#[path = "sm4.rs"]
#[allow(dead_code)]
pub mod sm4;
