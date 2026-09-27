# Optimization progress - 2026-09-26

## Scope and baseline

Read the README, the affine point-addition construction, the ping-pong walk
and replay, arithmetic helpers, simplifiers, and existing measurement notes.
All pre-existing worktree changes are preserved. Source changes remain under
`src/point_add/`; the harness, dependencies, and configuration are not changed.
Only `ecdsafail run` is used from the ECDSA Fail CLI.

The baseline was independently rerun with `ecdsafail run`:

| Metric | Baseline |
|---|---:|
| Accepted shots | 9,024 / 9,024 |
| Classical mismatches | 0 |
| Phase-garbage batches | 0 |
| Ancilla-garbage batches | 0 |
| Average executed Toffoli | 897,596.816 |
| Scored integer Toffoli | 897,597 |
| Qubits | 1,251 |
| Score | 1,122,893,847 |
| Emitted operations | 12,220,076 |

Baseline compressed `ops.bin` SHA-256:
`ca4fe4f256730bb795fde3c20f761cf551460fdab7f4e304dcfdadd1c4bddb7f`.
Provenance is HEAD `1097818d4b9ab7724d336b2027e4cd7861ec9496` plus the
pre-existing dirty worktree, not a clean commit.

This is accepted-stream validation, not an all-input correctness proof.
The existing independent measurement notes report finite-round, signed-width,
fold-window, and comparison approximations. Changing the operation stream also
changes its Fiat-Shamir input set. No nonce search or nonce change is performed
in this work.

## Iteration 1: exact bit-parallel Boolean simplification

The truth simplifier and physical-product lookup previously evaluated AND/XOR
one assignment at a time, repeatedly projecting each assignment into both
operand supports. Canonicalization separately scanned assignments for every
possibly irrelevant variable.

Replace those loops with word-wide cofactor operations on the existing
64-bit truth tables:

- Detect an essential variable by comparing its two cofactors with a masked
  shift and XOR.
- Remove an irrelevant variable by compacting its zero cofactor.
- Align supports by spreading and duplicating row blocks for missing
  variables, then apply a single word-wide AND or XOR.
- Share this exact binary operation with product-witness lookup. Keep the
  six-atom cap and fresh, non-reused opaque values unchanged.

This improves the circuit-construction algorithm, not its gate count.
The acceptance requirement is equality of every emitted operation, including
conditions and operands, followed by an official `ecdsafail run`.

Tests compare the optimized operations with an independent scalar reference:
all truth tables on up to four variables, larger tables and removable columns,
every pair of support subsets from seven atom IDs (including cap overflow),
and distinct opaque fallback values.

Results:

| Check | Result |
|---|---|
| Fast regression suite | 17 passed; 6 explicitly ignored |
| Scalar-reference microbenchmark | 0.068786 s |
| Bit-parallel microbenchmark | 0.017827 s; 3.86x faster |
| Baseline instrumented build/census | 21.323 s |
| Bit-parallel instrumented build/census | 19.203 s; 9.9% faster |
| Full stream comparison | All 12,220,076 records identical |

Times are individual local measurements, not stable cross-machine guarantees.
The missing pinned-toolchain `rustfmt` component was installed after the
formatter reported it unavailable; no dependency manifests changed.

## Iteration 2: eliminate redundant whole-stream analyses

`simplify_products` already advances the affine, quadratic, and truth models
on each original operation before considering a product witness. The pinned
configuration nevertheless ran separate affine and quadratic passes and then
a truth pass that ran all three models again.

Select the combined product pass alone. This does not assume repeated
simplification is redundant for every possible input circuit: retain the
individual passes, and require a full baseline-record comparison for this
specific construction. The nonce and arithmetic policies remain unchanged.
Continuation result: `ecdsafail run` accepted all 9,024 shots with zero
classical mismatches, phase-garbage batches, or ancilla-garbage batches.
The score remains **1,122,893,847**, and the compressed artifact has the
same SHA-256 recorded above. Three read-only comparisons also matched every
one of the 12,220,076 operation records. The existing regression suite
passed: 17 tests, with 6 research experiments explicitly ignored.

The continuation environment initially lacked the CLI and Rust. Installed
the CLI with its optional skill-install command disabled, restored the pinned
Rust 1.93.0 toolchain, and populated the locked crate cache after the official
offline run reported missing packages. No authentication was needed for the
local run; no credential was stored. No other `ecdsafail` command was invoked.

## Iteration 3: allocation-free slot traversal and bounded support merge

The product index constructed three short heap-backed vectors per
state-changing operation: one touched-slot list and two changed-slot lists.
Replace these with stack-backed iterators, preserving the precise slot order,
reset eligibility policy, and before/after updates. Borrow exact lookup keys
instead of cloning them, and construct a complemented key only after an
exact-witness miss.

Advance the independent affine/quadratic interpreters first, so a winning
proof can suppress an unused product query. Eligibility maintenance still
runs for every original operation, and the product query still observes the
truth state before that operation changes it.

Truth supports are already sorted and unique. Merge them linearly into a
six-element stack buffer instead of allocating, concatenating, sorting, and
deduplicating vectors. Reject a seventh distinct atom before allocating any
result; preserve the existing fresh-whole-value fallback and truth tables.

Fresh local pre-change measurements (not directly comparable with the earlier
session's timings):

| Run | Instrumented build + census | Maximum resident set |
|---|---:|---:|
| Baseline 1 | 9.008 s | 1,507,917,824 bytes |
| Baseline 2 | 8.907 s | 1,507,868,672 bytes |
| Baseline 3 | 8.908 s | 1,507,885,056 bytes |

The median baseline is **8.908 s**. This includes observer/census overhead,
but excludes compilation, decompressed-stream comparison, and scored
simulation. Timings are observations, not a CI threshold.

Six new focused regression tests cover all 18 operation kinds, deterministic
witness selection and operand exclusions, skipped-query index parity, reset
and later-touch eligibility, unsupported products, and classical-condition
preservation. These and the existing truth-table reference tests pass.
All operation records matched the preserved baseline in three runs. Build
times were **7.968, 7.958, and 7.950 s**: median **7.958 s**, a **10.7%**
reduction from the fresh 8.908 s baseline. Peak host memory was essentially
unchanged. This is a construction-time improvement, not a lower circuit score.

## Iteration 4: in-place operation-stream compaction

The simplifiers held the original and rewritten 56-byte operation arrays
simultaneously. Share an in-place rewrite helper across the affine, quadratic,
truth, and combined-product passes instead.

Use `Vec::retain_mut` for the common zero/one-output case. A complemented
product witness can legitimately emit `X; CX`: retain its second operation
and buffer only the extra first operation and insertion position. After all
originals have been interpreted, expand these sparse insertions backwards.
This prevents overwriting unread input and supports both shrinking and
growing streams without unsafe code.

Represent the complemented rewrite explicitly and report each original
operation once to the observers. Both phase and replay labels now support
zero, one, or two outputs; both expanded gates inherit the original label.
Previously those observers assumed every rewrite had at most one output.

Regression coverage checks all **3,125** five-operation combinations of keep,
drop, X, CX, and complemented-CX rewrites, including classical conditions and
growth beyond original capacity. A separate test verifies pointer/capacity
reuse for nonexpanding rewrites, all-deleted input, and empty input. Updated
phase/replay tests cover two-output rewrites. The suite passed **25 tests**,
with 6 research experiments ignored.

All 12,220,076 baseline records matched in three further runs:

| Run | Instrumented build + census | Maximum resident set |
|---|---:|---:|
| Compaction 1 | 8.116 s | 823,672,832 bytes |
| Compaction 2 | 8.108 s | 823,754,752 bytes |
| Compaction 3 | 8.147 s | 823,689,216 bytes |

Median host memory fell from **1,507,885,056 to 823,689,216 bytes**: approximately
**45.4% less**. The first implementation cost about 2% runtime relative to
iteration 3, although it remained faster than the session baseline. These
are host-process measurements, not quantum-register widths.

## Iteration 5: shared input analysis and unchanged-operation fast path

All three proof interpreters and the physical-product index separately
scanned the same 12-million-operation input to recover the same ABI layout.
Compute the input masks once and share them across independent state
initializers. Keep quantum-before-classical atom numbering, duplicate-register
handling, scratch-zero initialization, and initial witness eligibility intact.
Add a regression distinguishing ABI inputs, scratch slots, and duplicate
annotations.

In the in-place loop, let `Keep` bypass replacement construction and copying.
Only actual rewrites construct replacement operations.

| Run | Instrumented build + census | Maximum resident set |
|---|---:|---:|
| Shared analysis 1 | 7.981 s | 823,181,312 bytes |
| Shared analysis 2 | 7.703 s | 823,263,232 bytes |
| Shared analysis 3 | 7.694 s | 823,246,848 bytes |

Every operation record still matched. Final median construction time is
**7.703 s**, **13.5% below** the session baseline. Final median maximum
resident set is **823,246,848 bytes**, **45.4% below** baseline.

An additional trusted-simulator regression exercises all four simplifier
entrypoints on every assignment of three quantum inputs and one classical
condition. It checks exact and complemented product witnesses, actual
two-operation expansion, phase preservation, and clean scratch release.

## Final verification and scope of the improvement

The final `ecdsafail run` completed successfully:

| Metric | Final |
|---|---:|
| Accepted shots | 9,024 / 9,024 |
| Classical mismatches | 0 |
| Phase-garbage batches | 0 |
| Ancilla-garbage batches | 0 |
| Average executed Toffoli | 897,596.816 |
| Scored integer Toffoli | 897,597 |
| Qubits | 1,251 |
| Score | 1,122,893,847 |
| Emitted operations | 12,220,076 |
| Active regression tests | 27 passed |
| Ignored research experiments | 6 |

The final compressed artifact is byte-for-byte identical to the preserved
baseline, including SHA-256
`ca4fe4f256730bb795fde3c20f761cf551460fdab7f4e304dcfdadd1c4bddb7f`.
The protected harness, dependency manifests, arithmetic configuration,
approximation windows, and nonce are unchanged. Only the official harness
appended to `results.tsv`. All pre-existing worktree changes were retained.

This work improves the **classical circuit-construction algorithm and host
memory footprint**, not the Toffoli-by-qubit score. It does not establish a
new quantum-circuit Pareto point or change the inherited correctness regime.
The emitted-gate census still attributes 506,101 CCX/CCZ to modular replay,
382,605 to the forward/backward GCD walks, 45,770 to squaring, and 1,665 to
coordinate arithmetic. Those are emitted counts, not average executed
Toffolis. Actual score reduction remains a separate arithmetic-design task.

Verification used the existing release test binary and its read-only
`measurement::census` experiment, plus `ecdsafail run` for official scoring.
Raw timing logs (`baseline-census-*`, `allocation-census-*`,
`compaction-census-*`, `shared-analysis-census-*`), the baseline artifact,
and `final-ecdsafail-run.log` are retained in the local session artifact folder.
No other ECDSA Fail CLI subcommand or nonce search was used.
