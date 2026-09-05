# Chunked Comparator Handoff

Branch: `codex/midq-chunk-compare`, based on `bdfd306`.
Worktree: `/Users/jieyilong/Personal/research/ShorOptimization/shor_optimization_workspace/ecdsafail-midq-chunk-compare`.
Only `src/point_add` changes. No harness/dependency changes, submissions,
nonce searches, or changes to inherited approximation parameters.

## Integration

Enable with `MIDQ_CHUNK_COMPARE=1`. Default is OFF.
Optional `MIDQ_CHUNK_COMPARE_QCAP` defaults to 1019 and is clamped at 1019;
`MIDQ_CHUNK_COMPARE_SIZE` is a maximum candidate size, default 32, NOT a
fixed chunk size. The planner minimizes boundary replay Toffolis across
feasible sizes, breaking ties by scratch width. It can choose K=1 when a
complete carry chain fits. Low-headroom calls keep the old comparator.

The existing `MIDQ_MEASURE_COMPARE` flag still controls measured output
cleanup. Its phase oracle is separate from the XOR emitter, preventing
recursive fallback or reuse of the output measurement as an inner flag.
The core module is attached by a path attribute in
`trailmix_port/inversion/shrunken_pz_primitives.rs`, requiring no shared
module-root edit. The only other integration edits are its two comparator
dispatches and the existing measured-comparator selftest hook.

## Whole-Circuit Measurements

All numbers below are from the unmodified real `crate::sim::Simulator` on
the SAME 256 independent EC-addition inputs, seed
`midq-exact-density-check-v1`. This is a smoke regression, NOT a full
9024-shot or newly Fiat-Shamir-clean validation receipt.

| Variant | Q | Emitted Toffolis | Average executed Toffolis | cls/pha/anc |
| --- | ---: | ---: | ---: | --- |
| Baseline, disabled | 1024 | 18,162,098 | 17,206,512.828125 | 0/0/0 |
| Initial largest-K/full-endpoint version, superseded | 1024 | 18,016,042 | 16,801,174.199219 | 0/0/0 |
| Final replay-minimizing/three-CZ-endpoint version | 1024 | 17,594,450 | 16,643,555.937500 | 0/0/0 |

Final saving: 567,648 emitted and **562,956.890625 average executed
Toffolis (3.2717663%)**. The inherited overall peak remains 1024. The
comparator's new allocations are capped at 1019, not a claim that unrelated
baseline allocations now fit that cap. Main's prefix optimization and the
Q worker's changes are NOT included here; combined savings require a fresh
measurement because live headroom changes affect chunk choice.

All variants have identical output digest:
`e33d8d42b6511c00db8923212940659553843fe38ee79cff48606b14a210a752`.

Final operation digest:
`6da5d7d491c65774c10a302046b6f417c13324d8c8c48f8049acfea6350cab28`.
Baseline operation digest:
`688861cd8a815f70fe73726849a6be41c233015fd8494cbe005b4d7308ebbf75`.
An explicit run with `MIDQ_CHUNK_COMPARE` unset reproduced the baseline
operation digest and all resource/output numbers exactly after the final
production implementation was built.

Tradeoff: total emitted operations rise from 64,318,142 to 79,913,316
(+24.2469287%). Classical bit IDs rise from 1,512,084 to 2,893,308. The
extra Clifford, HMR, and condition operations are not hidden by the lower
Toffoli figure. Runtime/reaction depth is not claimed to improve.

Local driver: `/private/tmp/midq-predicate-resources.rs` (pre-existing,
unchanged); final executable `/private/tmp/midq-chunk-resources-v2`.
It was linked against this worktree's release library using rustc with
`-O -C lto=thin -C codegen-units=1` and its Cargo-built dependencies.

```sh
env -u MIDQ_CHUNK_COMPARE /private/tmp/midq-chunk-resources-v2 256
MIDQ_CHUNK_COMPARE=1 /private/tmp/midq-chunk-resources-v2 256
```

Logs: `/private/tmp/midq-chunk-default-off-256.log`,
`/private/tmp/midq-chunk-candidate-v2-256.log`. This local diagnostic does
not replace the trusted full evaluator.

## Component Measurements

Forward plus known-flag measured cleanup, n=256, 65,536 native measurement
shots. The 514 persistent qubits include both operands, the flag, and an
arbitrary witness. K=0 denotes the old pair. Full-width random correctness
is checked separately; these averages use u=1,v=0 and independent HMR draws.

| K | Scratch Q | Total Q | Emitted T | Exact expected T | Measured average T |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 (old) | 1 | 515 | 1024 | 768 | 768.234375000 |
| 1 | 256 | 770 | 511 | 383.5 | 383.075881958 |
| 2 | 129 | 643 | 765 | 478.75 | 478.843826294 |
| 16 | 31 | 545 | 961 | 552.25 | 551.649185181 |
| 24 | 33 | 547 | 971 | 556 | 555.912750244 |
| 32 | 39 | 553 | 945 | 546.25 | 546.770935059 |

Resource identity: `R=(ceil(n/K)-1)(K-1)`; XOR emits n+R and expects
n+R/2, phase emits n-1+R and expects n-1+R/2. The pair emits
2n-1+2R and expects 1.5n-0.5+0.75R. Boundary and final phase endpoints
use the three-CZ majority phase without an endpoint allocation/CCX.

Cap sweep, n=256 (persistent live Q includes operands, flag, witness):

| Live Q | Selected K | Observed Q | Emitted pair T |
| ---: | ---: | ---: | ---: |
| 514 | 1 | 770 | 511 |
| 970 | 6 | 1017 | 931 |
| 982 | 9 | 1018 | 959 |
| 985 | 16 | 1016 | 961 |
| 990 | old fallback | 991 | 1024 |
| 1000 | old fallback | 1001 | 1024 |
| 1018 | old fallback | 1019 | 1024 |

## Verification Receipt

Release build and `git diff --check` pass. Native component suite:
**2,350,720 basis/measurement cases** across all modes, plus the resource
averages and exhaustive sizing checks. Counts include repeated input states
across distinct circuit/measurement configurations; they are not a claim
of that many unique basis vectors.

- 1,843,200 small exhaustive cases: widths 0..5, each K, both carry-in
  constants, both complement settings, XOR/phase/cleanup endpoints, and nesting.
- 368,640 full-width cases through 257 bits: random inputs, equality,
  carry propagation, top-bit/sign patterns, and both initial carries.
- 3,072 repeated/overlapping/noncontiguous input-slot cases. Invalid output
  aliases and widths reject before emission. Every emitted Op is validated.
- 4,096 cases enumerating every tiny HMR transcript, including nested
  conditions and intentionally stale inactive classical bits.
- 131,712 integration cases: measured/unmeasured output cleanup, plus both
  directions of forward/cleanup headroom changes forcing mixed new/old paths.
- Forced-zero, forced-one, and randomized measurements; strict zero before
  every reset, cross-checked against complete native nested execution.
- No aliased gates, malformed slots, shared-condition-flag loops, unexpected
  output phases, or dirty scratch. Exact fallback operation-stream equality.

Selftest command uses the existing build entry point, without a harness edit:

```sh
MIDQ_MEASURE_COMPARE_SELFTEST=1 MIDQ_CHUNK_COMPARE_SELFTEST=1 /private/tmp/midq-chunk-target/release/build_circuit
```

Receipt: `/private/tmp/midq-chunk-selftest-final.log`.
Proof: `chunked_compare_proof.md`. General `cargo test --lib` was not used:
this inherited port has documented test-only dependency/API failures and
stub contract simulation. The component suite instead uses real emitted
operations and the original Simulator. Full combined 9024 validation,
reprofiling under Q-worker headroom, and the overall T<15M target remain
integration work, not claimed as achieved by this isolated patch.
