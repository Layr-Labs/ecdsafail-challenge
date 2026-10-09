//! SKY-COF masked-ring research seam (inert in the default build; nothing here is called by
//! `point_add::build` unless `SKYCOF_RING_SELFTEST` is set, and then the process exits after the
//! selftest).
//!
//! * [`engine`]: iterative one-hot engine over a boundary register.
//! * [`mc`]: masked single-carry-wire Cuccaro add / subtract and the capture compare.
//! * [`lod`]: masked leading-one deposit (boundary conversions).
//! * [`ring`]: the shared-register layout, canonical boundaries, swap-first Kaliski rail step and the
//!   masked cofactor update, forward and exact reverse.
//! * [`selftest`]: gate-level selftests and the per-call cost report.
//!
//! # Integration API ([`ring`])
//! * State [`ring::Ring`] `{ n, cap, a, b, ka, vb }`: `a`, `b` are the two `n`-wire registers in logical
//!   position order (`n = 257`), `ka`, `vb` the `bitlen(n)`-bit boundary registers. Encoding at a tick
//!   boundary: `A = u + sum_j s_j 2^(n-1-j)`, `B = v + sum_j r_j 2^(n-1-j)`, `KA = bits(s)`, `VB = bits(v)`.
//!   Walk start (`u, v, s, r) = (d, p, 0, 1)`: `A = d`, `B = p + 2^(n-1)`, `KA = 0`, `VB = bits(p)`.
//!   `cap = Some(k)`: absolute live-wire cap for the room-aware conversions.
//! * [`ring::tick_fwd`]`(cb, &mut ring, &TickZ, &mut StepLog) -> (c, isc)`: one Kaliski step from a
//!   pre-park state (`u >= 1`). `c = [B or C]` (= NOT typ) and `isc = [C]` are returned live; the
//!   tick relabels `ring.a` (rotation). `isc` equals cofactor bit 1 of `A` afterwards:
//!   [`ring::isc_erase`] / [`ring::isc_recompute`] are one CNOT each.
//! * [`ring::tick_rev`]`(cb, &mut ring, &TickZ, c, isc, &mut StepLog)`: exact inverse; consumes `c`, `isc`.
//! * [`ring::TickZ`]: per-tick windows (inclusive ranges of `bits(s), bits(u), bits(v)` at entry and of
//!   `bits(s'), bits(u'), bits(v')` after the swap). A walk whose bit lengths leave a window gets a
//!   wrong result (an error event), exactly like a public-boundary envelope miss.
//! * Post-park (`u = 0`) ticks, the decoder, the history accumulator and the park fold are outside this
//!   module.
pub mod dec;
pub mod engine;
pub mod hybsim;
pub mod costs;
pub mod conv;
pub mod hwalk;
pub mod hprobe;
pub mod lod;
pub mod mc;
pub mod pointadd;
pub mod replay;
pub mod ring;
pub mod rwalk;
pub mod selftest;
pub mod wfull;
pub mod wtest;
