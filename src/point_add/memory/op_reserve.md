# Full-circuit op-vector reservation (2026-10-08)

The promoted Leapfrog build emits 9,375,867 operations before post-passes.
`Builder::new` starts with an empty `Vec<Op>`, so the full build grows that
large vector repeatedly. `build_point_add` now calls `reserve_exact(9_376_000)`
when Leapfrog is enabled. The 133-op margin covers the pinned build, and
future growth still uses normal `Vec` allocation. Other builders retain the
default empty vector.

One local macOS direct-builder run per version measured peak resident memory
with `resource.getrusage(RUSAGE_CHILDREN)`: 1,610,055,680 bytes before and
1,528,283,136 bytes after, a reduction of 81,772,544 bytes (5.08%). The
elapsed times, 30.883s and 30.055s, are single observations and not a
reliable speed comparison.

The compressed `ops.bin` SHA-256 was identical on both versions:
`0f69c20c3c0bf5da08db15acf3772a4e10199ad047e08193ea5fd2a488326b8b`.
Official local `yukon run` validated all 9,024 shots with no classical,
phase, or ancilla failures. It reported 794,044.324 average executed Toffoli,
1,244 qubits, and score 987,790,736. This is a builder-memory improvement;
it does not improve the scored circuit product.
