# Exact Borrowed-Register Outer Folds

Base: `472a85f`, branch `codex/midq-outer-exact`.
Worktree: `/Users/jieyilong/Personal/research/ShorOptimization/shor_optimization_workspace/ecdsafail-midq-outer-exact`.

## Integration

Default OFF. Enable only with `MIDQ_OUTER_DIRTY_CONST=1`.
The unset/default build is byte-identical to the baseline compressed `ops.bin`:
`ff9f1866ab5815ec727a19d208d5d4517badf051f4a912aa3822307e7bca9d73`.
No PZ state-machine, Khattar-Gidney, or trusted-harness source was edited.
No widths, guards, iterations, correction predicates, or approximation support changed.
No submission or nonce search was run.

## Change and Exactness

Three live call sites in `trailmix_port/rfold_mbu.rs` now optionally use the
existing `controlled_add_const_gidney`: controlled modular add, double, and
structural halve. Controlled subtraction inherits the change through its
unchanged X-sandwich. The low target is still exactly `a[..73]`, modulo `2^73`.
The dirty donor is `a[73..145]`, disjoint from the target and overflow control
`a[256]`. All donor bits are restored before any shift or phase comparator.
The existing Gidney ghost corrections are emitted unchanged. Both the
64-bit phase comparator and all other inherited correction paths are retained.

This is an exact replacement of the baseline window permutation, not a claim
that the inherited approximate field arithmetic is exact on all inputs.

## Resource Evidence

The live profile contains 1,794 controlled-add folds, 1,277 doubles, and 1,022
halves. Each changes from 417 to 215 emitted Toffolis and from 12 to 3 extra
clean qubits. These 4,093 calls contribute 1,706,781 baseline emitted Toffolis.
Other large outer buckets: integer adds 1,383,174 and phase correction 229,632.

| Metric | Baseline | Enabled |
| --- | ---: | ---: |
| Global Q | 1051 | 1051 |
| Hot fold phase Q | 1051 | 1042 |
| Pre-cancellation emitted T | 20,915,309 | 20,088,523 |
| Final emitted T | 20,507,903 | 19,787,535 |
| Final emitted operations | 66,169,133 | 67,204,662 |
| Classical bit slots | 720,467 | 982,419 |
| Fixed-corpus average executed T | 19,841,617.110 | 19,120,856.935 |
| Fixed-corpus average executed Clifford | 28,782,928.696 | 30,832,729.649 |

Gross emitted saving is 826,786; final saving is 720,368 because 106,418
baseline Toffoli cancellations no longer apply. Average T saves 720,760.175
on the common corpus. The baseline's previously validated Fiat-Shamir average
19,841,480.807 belongs to a different corpus and is not the matched comparison.
Enabled compressed `ops.bin` SHA256:
`c39ea1b811f718f160fcded40c4c8935865eadf16a9998db997d6f66c9ce0628`.

## Validation

`MIDQ_OUTER_EXACT_SELFTEST=1 target/release/count_tof` passes using the actual
`crate::sim::Simulator`, not the port's no-op contract methods:

- 599,168 exhaustive inputs for widths 2 through 6, every constant, both
  directions and controls, and every dirty-donor value.
- 399,840 production-width cases, both backends, each with all-zero, all-one,
  and pseudorandom measurement outcomes. Includes carry/borrow boundaries
  through all 255 bit positions, near-modulus values, and random values.
- Actual folds, double/halve, and controlled add/sub with 256/257-bit sources;
  independent controls and source aliases at bits 0, 96, and 255.
- Independent value reference, restored donor/source/control, zero live scratch,
  zero before every reset, and the inherited comparator phase syndrome,
  including deliberately out-of-support boundary inputs.
- Resource assertions require lower emitted T and no increased component Q.

Full fixed-corpus diagnostic: 9,024 inputs, same five classical failures
`4174, 4968, 5407, 7617, 7854`, no ancilla failures. Enabled phase failures are
`4968, 5407, 7617`, all within that same classical-failure set. The evaluator
correctly returns FAIL for inherited failures; this is not a clean validation.
The unchanged diagnostic executable was reused from `ecdsafail-midq-sub20`.
Its single appended metrics row was moved into this worktree's local evidence,
leaving the sibling's prior results untouched.

## Reproduction and Remaining Risks

Build: `cargo build --offline --release --bin count_tof --bin build_circuit`.
The copied `src/bin/count_tof.rs` is local diagnostic source, not committed.
Profile/build: set `MIDQ_OUTER_DIRTY_CONST=1 TRACE_EMITTED_PHASE_OPS=1
TRACE_EMITTED_PHASE_OPS_TOP=100000 TRACE_PHASE_ACTIVE=1` when running
`target/release/build_circuit`. Count with `MIDQ_OUTER_DIRTY_CONST=1
target/release/count_tof`.

Durable local logs and the metrics row: `research/outer-exact/` in this worktree.
Original run logs: `/private/tmp/midq-outer-{selftest,baseline-profile,candidate-profile,candidate-count,common,default-off}.log`.

The isolated branch does not reach Q<=1024 or T<15M. The remaining global peak
is still in the parent inversion phases; composed Q/T must be remeasured after
integration with the independent PZ/checkpoint/predicate/endpoint changes.
The extra measurements increase Clifford count, classical bits, and total ops.
New emitted bytes change Fiat-Shamir inputs; no clean nonce was sought.
`cargo test --lib` was not used because the baseline has known compilation errors.
