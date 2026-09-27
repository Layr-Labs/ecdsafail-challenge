# Unscored measurements

## Width-research extensions

`MEASURE_CONFIG` is an optional **test-only**, semicolon-separated numeric
configuration. It is absent from production builds and cannot set a nonce.
For example, `MEASURE_CONFIG='qubits=1238;rounds=720;guard=8;tail_from=700;tail_bits=13'`
selects a complete laboratory candidate; tail width is physical width before
the budget-derived taper. Unsupported keys/ranges and incomplete tail settings
are rejected. Normal builds remain fixed and environment-independent.

`MEASURE_ASSERT_QUBITS=1238` rejects the first allocation above that limit,
with the phase name. Combine it with `RUST_BACKTRACE=1` and `census` to locate
the actual offending primitive.

`small_tail=1` enables an exact tape-free continuation when both final native
register widths match and are 5, 6, 7, or 8. `ROUNDS` reports native and exact
continuation counts separately; the bounds are 6, 10, 12, and 17 rounds. Classical
walk-risk measurements append the corresponding virtual signed widths and
do not apply the native rotation's extra rail-bit restriction to exact steps.
`early_sign=1` selects exact sign-two retirement and its matching head schedule;
the `retired_signs` field records the resulting live-tape accounting.

`tail_cap=<budget>` pins the numerical walk footprint independently of the
hardware `qubits` budget; zero uses the hardware budget. This permits more
exact carry workspace without automatically widening the integer snapshot.
It must not exceed the hardware cap. `head_div` / `head_mul` vary replay
head boundaries, and `retain_extra_div` / `retain_extra_mul` vary the allowed
exact retained prefix. Nonpositive final modeled savings are rejected.

Two explicitly ignored diagnostic tests extend the same independent sampler:
`point_add::measurement::stages::diagnose_point_stages` identifies the first
wrong affine stage; `point_add::measurement::stages::diagnose_division_rounds`
checks each division replay update against exact modular arithmetic for
`MEASURE_DIAGNOSTIC_CASES=<comma-separated zero-based indices>`.
They report failures as observations, not acceptance. Setting
`MEASURE_DIAGNOSTIC_STREAM=fiat-shamir` reproduces the current unmodified
operation stream's official inputs for diagnosis; it does not search, change,
or replace a nonce.

`MEASURE_DIAGNOSTIC_OPS=<saved ops.bin>` instead reuses a previous circuit's
input stream, opened read-only. This makes a new algorithm's regression against
previously failing inputs possible without changing either circuit's nonce.
It is mutually exclusive with `MEASURE_DIAGNOSTIC_STREAM`.

Timed searches use immutable laboratory-executable snapshots in the session
artifact folder. Their suggestions are **unscored** until integrated and
accepted by `ecdsafail run`.

The laboratory is compiled only by `cargo test --bin build_circuit`.
E1/E2 call `point_add::build()` and, for E1, the trusted `Simulator` directly.
X1's paired sampler runs only reference EC arithmetic and the classical walk.
Neither binary's `main` runs. The tests never write `ops.bin`, `score.json`,
`results.tsv`, or another file. No dependencies or manifest changes are needed.

## Commands

```sh
# Small instrumentation regression tests.
cargo test --release --bin build_circuit point_add::measurement:: -- --nocapture

# E1 + E2: 1,024 fresh shots and actual executed, post-simplification Toffolis.
# Optional read-only comparison against every record of the existing ops.bin.
MEASURE_SHOTS=1024 MEASURE_VERIFY_OPS=ops.bin \
  cargo test --release --bin build_circuit \
  point_add::measurement::fresh_sample -- --ignored --exact --nocapture

# E2 only: emitted counts and width, without simulation.
MEASURE_VERIFY_OPS=ops.bin cargo test --release --bin build_circuit \
  point_add::measurement::census -- --ignored --exact --nocapture

# X1: both real affine denominators, classical walk only (no circuit build).
# Defaults to 262,144 attempts; the same MEASURE_SEED option applies.
MEASURE_SHOTS=262144 cargo test --release --bin build_circuit \
  point_add::measurement::walk::paired_walk_sample -- --ignored --exact --nocapture
```

`MEASURE_SEED=<64 hex characters>` replays a printed sample seed. Without it,
32 bytes from OS entropy seed domain-separated SHAKE256, independent of the
op stream and its fixed nonce. `MEASURE_SHOTS` defaults to 1024 for `fresh_sample`
and 262144 for `paired_walk_sample`; larger samples give better confidence.
Multiples of 64 avoid a partial simulator batch in E1.
Point generation matches `eval_circuit`: two
uniform 256-bit scalars, reference generator multiplication, identical
degenerate-input exclusions, and generation of all points before HMR/reset
randomness. Excluded attempts are reported through the accepted-shot count.
No nonce search or replacement occurs.

## Interpretation and limits

- `p = failures / accepted shots`; `lambda9024 = 9024*p`. Both have approximate
  95% Wilson intervals. Classical, phase, final-ancilla, and their per-shot union
  are separate; phase/ancilla bad-batch counts also match the evaluator.
  Zero observed failures is **not** evidence of a zero failure rate.
- A measurement test passes even when the circuit has observed failures:
  it is an estimator, not a scored acceptance run. Structural, stream-identity,
  or simulator-parity errors fail the test.
- Census labels follow every deletion/replacement in all four simplifier
  passes, including both gates of an expanded `X; CX` product rewrite.
  Each original operation advances the rewrite trace exactly once.
  Function-scoped labels distinguish interleaved replay from forward
  and backward walk; top-level `set_phase` names alone cannot do that.
  Endpoint modular negations count as replay; setup/restoration as other.
  Deferred walk-phase repair counts where executed, in walk-back.
- Executed CCX **and CCZ** come from differences in the trusted simulator's
  counters, not 50%-condition estimates. Each slice must have a balanced
  condition stack. The first full simulation is also run unsliced; all qubits,
  classical bits, phase, counters, and RNG position must match.
- `peak_live` is the builder's simultaneous allocation high-water mark while
  that phase is active, including registers/tape held across phase boundaries.
  `max_wire_id_plus_1` is the evaluator's width rule applied to that phase's
  operations; reused high IDs can exceed that phase's live count. Widths are
  **not additive**. The maximum `max_wire_id_plus_1` is the scored width.
  `PEAK_OWN` additionally prints allocation-site ownership at the global peak;
  its operation index is **before** simplification.
- The trusted simulator executes all 64 lanes even in a short final batch.
  Failure checks mask unused lanes; census averages omit partial batches so
  they are not inflated by inactive lanes.
- This checkout has no `src/main.rs`. The actual evaluator does **not** run a
  gate-reversed inverse or assert that each reset input is zero. A dirty reset
  is detected statistically through its randomized phase, and final ancillas
  are scanned explicitly. This lab faithfully reproduces those actual checks;
  it does not claim the stronger forward/inverse guarantee in the README.
  Naively reversing HMR, reset, and classical-store operations is not an inverse.

All observer hooks are `#[cfg(test)]`; they cannot affect the normal scored
build. To prove identity to an existing artifact, use `MEASURE_VERIFY_OPS`;
this streams and compares all 56 bytes of each decompressed record, including
padding and all operands, and never rewrites the compressed file.

## X1 classical attribution

`measurement/walk.rs` derives both denominators from each accepted reference
point addition: `(target.x-offset.x) mod p` and `(offset.x-sum.x) mod p`.
It uses a signed five-limb integer representation for the fused round-zero
lift and the alternating plus/minus recurrence. It checks the pinned width
schedule **including guard bits**, never truncates its ideal integer state,
and may stop at `(±1,±1)` because every remaining round is then an identity.

The output separates:

- `CONV`: not at `(±1,±1)` after the fixed round budget.
- `WIDTH`: an ideal value does not fit the next scheduled signed register
  (the last round uses the current width). First-miss indices are zero-based
  **rounds just completed**.
- `ARITHMETIC_RAIL`: in an ordinary round, the pre-rotation half-sum does not
  fit the signed `value_width(round)-1` bit-1-and-up rail. This is a distinct
  condition from the next-width shrink check. An exhaustive emitted
  **single-round** test at widths 5–7 verifies it; the large sample uses no
  circuit simulation.
- `CONV_OR_SCHEDULE_WIDTH`: the first two predicates' union.
- `WALK_PREDICTED`: all three predicates' union, deduplicated across passes.

Tables include divide-only, multiply-only, both, and neither. Correlation is
reported without treating sparse overlap as a proof of independence.
Wilson intervals describe these **walk predicates**, not actual full-circuit
failure. Fold/comparison failures, classical/phase correlation, precision,
recall, and a new total circuit λ require a separate paired E1 experiment.

`WALK_TIMING` separates reference point generation and paired walking. It
prints full-9024-set extrapolations and an **idealized** lazy, first-failure
abort estimate. It does not implement nonce search or measure parallel
scaling, cached Fiat–Shamir hashing, or replay checking.

## X1 round and approximation inventory

`census` additionally prints:

- `REPLAY_ROUNDS_BEGIN` … `REPLAY_ROUNDS_END`: 698 rows per direction plus
  one endpoint accounting row per direction. Every round includes selected
  path, allocation-based live/free counts at entry and peak, fold width,
  main-adder chunk bounds, retained prefix, and the selected/candidate cost
  model's savings. Rows follow traversal order (multiply mostly descends).
- Post-simplification CCX/CCZ split into main add, fold, F erasure, B erasure,
  exact prefix erasure, selectors, and other. Each category has unconditioned
  `U` and syntactically classically conditioned `C` counts. `U_plus_half_C`
  is only a half-execution **proxy**, not an observed execution counter.
  Exact mapped-fold internal comparisons stay in the fold category.
- `APPROXIMATION_SITES_BEGIN` … `APPROXIMATION_SITES_END`: B/F/K reports,
  replay fold-top windows, retained low cuts, shell/square erasures and folds,
  square register windows, walk widths/lifts, endpoint promises/windows,
  and the rare round-zero bit predictor. Exact local comparisons are also
  listed as controls. `seeded` means a borrow/seed is supplied; an exact
  incoming carry and a statistical predictor must not be conflated.

Every replay CCX/CCZ is accounted for, with an assertion that rows plus
outside-round operations equal the phase census. Normal builds contain none
of these observers. Tiny exact leading B windows are not automatically risky:
the site inventory is not a license to sum `2^-width` over all rows.

Measured X1 results, full approximation map, resource-table summary, timing
assumptions, and validation limitations:
`.squad/decisions/inbox/rust-eng-x1-findings.md`.
