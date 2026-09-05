# ECDSA Fail research rig

Companion to [`CEILING.md`](CEILING.md). This rig instruments the current trusted
verifier; it never substitutes for `ecdsafail run`.

## Contract

| field | pinned value |
|---|---|
| objective | minimize `round(avg executed CCX/CCZ) × max referenced qubit id + 1` |
| official regime | 9,024 SHAKE256-of-semantic-stream shots; zero classical, phase, and ancilla failures |
| frontier | `1,489,216,228 = 1,290,482 × 1,154`, submission `705b36a`, source `7fa872d` |
| artifact | compressed `e1f6f50a…c76f333`, canonical `ddea3e8d…1767ce7` |
| absolute scorer floor | `0`; requires at most `4,511` total executed Toffoli |
| iteration cap | 500; checkpoint every 10 completed iterations |
| editable | `src/point_add/**`, durable memory/reproducers, ignored `.autoresearch/**` |
| frozen | trusted evaluator/simulator/circuit, benchmark scripts/config, toolchain, retained tests/history |

Literal registration:

```sh
python3 src/point_add/memory/repro/verifier_ceiling.py --verify --json
python3 src/point_add/memory/repro/schema_harness.py init
python3 src/point_add/memory/repro/schema_harness.py backtest
```

## Instruments

| tier | instrument | authority |
|---|---|---|
| Hash | `artifact_io.py::fingerprint` | Exact artifact identity, width, and static operation census. First check after every build. |
| Rank | retained exact synthesis/proof reproducers and source-level models | Refutes scoped mechanisms and ranks hypotheses; cannot update frontier. |
| Gate | paired fixed-randomness differential, exact stream census, `dirtyscan`, `TRACE_TLM_TOF` | Allocates trusted-run spend. Any surprise invalidates affected calibrations. |
| Certify | `ecdsafail run` | Sole correctness and score authority for an exact artifact. |
| Promote | `world_model.py::promotion_gate` followed by `ecdsafail submit` | Requires refreshed frontier, exact hash, 9,024-shot pass, and strict score beat. Official promotion is ground truth. |

No `.opencode` controller is installed. `schema_harness.py` is the single thin
content-addressed recorder/backtester, while the active goal session remains the only
controller. This preserves the prior deletion of unmeasured controller infrastructure.

## Niches

The harness accepts exactly the `CEILING.md` terms:

| niche | mechanism | initial champion | exhausted? |
|---|---|---|---|
| `H0-zero-rounding` | seed-independent or fixed-point verifier-specific construction | none; frozen lookup and direct fixed-point census retired | no |
| `H1-gcd-apply` | controlled arithmetic, composite synthesis, or one-traversal representation | promoted frontier | no |
| `H2-square` | modular-square structure | promoted frontier | no |
| `H3-coordinate-shell` | source-indexed invariants and coordinate shell | promoted frontier | no |
| `H4-postpasses` | exact transforms, strip provenance, cost calibration | promoted frontier | locally mature, not globally exhausted |
| `H5-width` | schedule/cap geometry or complete alternative representation | promoted frontier | no |

`schema_harness.py select` samples the least-attempted niche; proposals may branch from
any live candidate. A globally dominated candidate remains live when it is the best witness
for an unclosed mechanism.

## Gates

1. **Backtest before action.** A broken hash chain, invalidation mismatch, missing prior
   observation, unresolved surprise without a reframe, or missing tenth-iteration checkpoint
   makes the rig red. Measurement remains legal; optimization edits do not.
2. **Prediction before experiment.** Every prediction names niche, parent candidate and
   artifact, action class, mechanism, `ΔQ`, mean/SD of `ΔT`, correctness risk, invalidations,
   and full-run budget.
3. **Hash before spend.** A byte-identical semantic artifact is `no_effect` and cannot receive
   a full verification allocation.
4. **Evidence hardness.** Exact proof channels hard-block only their scope. Statistical
   proxies are calibrated bets and never certify a circuit.
5. **Mismatch abort.** `prediction_match=false` requires a reframe with a compression claim
   and forward prediction before the next iteration.
6. **Full run.** Stage `full` requires the exact artifact hash, trusted evidence kind,
   9,024 shots, all failure channels, qubits, average Toffoli, and score.
7. **Promotion.** Refresh frontier, require exact passing artifact and strict score beat,
   then submit. Record rejected, failed, accepted, and promotion outcomes without omission.

## Court

The initial ontology change is `H0-zero-rounding`: the numerical floor is zero, so arithmetic
constant-factor grinding cannot establish the absolute optimum. Its first forward prediction
was tested by `zero_score_lookup.py`: a frozen 27-bit-prefix table fit all 9,024 points at
zero Toffoli in 3,042,193 operations, but its own semantic stream reseeded the draw and failed
9,024/9,024 with zero table hits. Iteration 28 then exhaustively enumerated 1,149,296 reduced
self-seeded lookup states with exact field serialization and SHAKE256 coupling. The seven
scopes had 0–2 fixed points each, while the analogous production table family has
approximately `2^4,758,375` states. The compressed model is: artifact identity and verifier
draw are one endogenous state, and direct canonical fixed-point search has inverse-density
cost. Further H0 proposals must be seed-independent or generically transform the quantum
input; fitting a draw or searching the direct table map is retired.

## Acceptance

| instrument gate | observed acceptance |
|---|---|
| scorer replay | `exact_scorer.py` green on 7 retained rows and exact current totals |
| public frontier replay | `world_model.py` green on all 416 promoted rows in strict order |
| trusted pin | `verifier_ceiling.py --verify --json` green on all six trusted hashes and both rounding boundaries |
| baseline identity | `artifact_io.fingerprint(ops.bin)` reproduces both promoted hashes, 9,062,420 ops, and 1,154 qubits |
| no-op safety | `TRACE_TLM_TOF=1` rebuild preserved compressed hash `7333b19d…e890b8c9` |
| seeded bad discriminator | zero-score lookup self-reseed produced 9,024 classical failures; q1145 trusted counterexample remains denied by tests |
| reduced fixed-point census | `h0_fixed_point_census.py` exhaustively checked 1,149,296 states; instrument SHA-256 `9e2ce86a…a8c0edc`; 0–2 fixed points per scope |
| latest official witness | submission `705b36a` promoted at score `1,489,216,228`, exact 9,024-shot pass; this updates only the upper bound |
| phase cost model | profiler terms sum `1,304,986.5`; calibrated postpass credit `-13,127.198` reproduces official `1,291,859.302` exactly |
| harness contracts | full retained, ceiling, Schema, world-model, and fixed-point contract suite green |
| live ledger | `.autoresearch/measurements.jsonl` backtest green through iteration 28; tail `87b2cf73…72cbaa` |

## Source

Pinned instrument identity:
`db5c1340408626b17fb37eebc18b3bdc1be42bbb141e34e8f70a2af328ddccbd`.
Recompile this rig if a trusted hash, scorer, world-model invalidation contract, ceiling term,
or calibrated proxy turns red.
