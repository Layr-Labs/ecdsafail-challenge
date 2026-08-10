//! Library entry point shared by the two challenge binaries:
//!
//! * `build_circuit` (untrusted) calls `point_add::build` and serializes the
//!   resulting op stream to `ops.bin`. This is the only place contestant
//!   code executes.
//! * `eval_circuit` (trusted) reads `ops.bin`, re-simulates against the
//!   secp256k1 reference adder, validates correctness/reversibility/phase,
//!   counts gates, and writes `score.json`.
//!
//! Splitting the harness into two binaries keeps the trust boundary aligned
//! with the process boundary: contestant code cannot tamper with the
//! simulator, the test inputs, or the score because none of that runs in
//! `build_circuit`.
//!
//! NOTE: `point_add` (contestant code) is deliberately NOT a module of this
//! library. It is compiled directly into the `build_circuit` binary via a
//! `#[path]` module (see `src/bin/build_circuit.rs`). If it lived here, the
//! shared crate would be linked into `eval_circuit` too, and an
//! `.init_array` constructor in contestant code would run before `main` in
//! the trusted scorer — enough to forge `score.json` and exit 0 before any
//! validation runs.

#[allow(dead_code)]
pub mod circuit;
#[allow(dead_code)]
pub mod sim;
#[allow(dead_code)]
pub mod weierstrass_elliptic_curve;
