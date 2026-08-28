# Local frontier experiments at `edeed3f`

Date: 2026-08-28

## Baseline

- Commit: `edeed3f54e8712b481e58e36a7d0f77ae2708277`
- Average executed Toffoli: `903462.889`
- Peak qubits: `1266`
- Official rounded score: `1143784158`
- Correctness: `9024/9024`, zero classical, phase, and ancilla failures

## Experiment 1: endpoint fold window 18 -> 17

- Method: runtime override `SUB4_PP_ENDPOINT_FOLD_WINDOW=17`
- Emitted operations: `12438785` (84 fewer than baseline)
- Peak qubits: `1266` (unchanged)
- Full verifier result: FAIL
- Classical mismatches: `17`
- Phase-garbage batches: `21`
- Ancilla-garbage batches: `0`
- Disposition: rejected; no source change retained

The one-step window cut is not a short local nonce-grind candidate. Its observed
failure band is consistent with the existing notes' warning that approximate
window savings require a large Fiat-Shamir nonce search.

## Experiment 2: ping-pong split-point sweeps

The emitted operation count was swept without editing source, then only the
best candidate was sent to the full verifier.

- `SUB4_PP_R1_MUL=318..334`: current `326` remained the unique local minimum
  at `12438869` emitted operations.
- `SUB4_PP_R1=329..341`: current `335` remained the local minimum at
  `12438869` emitted operations.
- `SUB4_PP_R2=640..650`: `641` was the emitted-op minimum at `12438857`, 12
  fewer operations than the shipped `645` setting.

Full verification of `SUB4_PP_R2=641` with the shipped nonce failed:

- Peak qubits: `1266`
- Classical mismatches: `23`
- Phase-garbage batches: `19`
- Ancilla-garbage batches: `0`
- Disposition: rejected; no source change retained

## Conclusion

The three discrete split-point neighborhoods are locally exhausted for cheap,
deterministic gate-count improvements. `R2=641` is a real 12-op emitted-count
candidate, but every changed stream receives a new Fiat-Shamir test set and
therefore needs a clean nonce. The current circuit comments report that even a
10,000-candidate search budget is at least two orders of magnitude below the
expected clean-search cost. Do not bake `R2=641` without a separately verified
9024-shot clean nonce.

## Reproducible narrative

### Context, environment, and rules

The local clone was already installed and authenticated. The user's first
`ecdsafail run` error came from running in `/home/ssgkgk`, where no
`benchmark.json` exists; all experiments here ran in the challenge repository
or a worktree created from it. The repository was at `edeed3f`, with only
`results.tsv` already dirty from the user's successful baseline. `README.md`
and `benchmark.json` were read before editing. They agree that only
`src/point_add/**` is editable, so harness code, Cargo files, toolchain,
benchmark logic, score artifacts, and test inputs were left untouched.

The baseline command and result were:

```sh
cd /home/ssgkgk/ecdsafail-challenge
ecdsafail run
```

It emitted 12,438,869 operations and passed all 9,024 official shots. The
trusted evaluator reported total executed Toffoli `8,152,849,109`, average
Toffoli `903462.889`, average Clifford `10271192.373`, 1,266 qubits, and score
`1143784158`. These measured values, not stale README reference numbers, were
used for comparison.

For safe editing, a branch/worktree was created from that exact frontier:

```sh
git worktree add -b codex-opt \
  /mnt/c/Users/ssgkg/Documents/test/ecdsafail-opt HEAD
```

### Architecture and hypothesis selection

The active `point_add::build()` path uses the ping-pong point-add circuit. Its
dominant live-width term is the division sign tape held during coefficient
replay. The tuning surface includes divide/multiply rounds, `R1`, `R1_MUL`,
`R2`, peak governors, replay chunk geometry, and approximate comparison/fold
windows. Recent promoted commits guided this pass toward two bounded classes:
the newest endpoint-window change and the discrete schedule split points.

The emitted circuit ends in 48 `X;X` identity pairs. A 48-bit nonce selects
qubit 0 or 1 for each pair. This never changes the circuit function, but it
changes the serialized operation stream and therefore the SHAKE256
Fiat-Shamir test population. As a result, every real gate-count change needs a
separately clean nonce; inheriting the previous nonce is useful only as one
full-verifier sample, never as proof that the new stream is invalid for every
nonce.

Experiment 1 followed commit `edeed3f`, which lowered
`SUB4_PP_ENDPOINT_FOLD_WINDOW` from 26 to 18 and supplied a new clean nonce. A
one-step cut to 17 was the smallest adjacent Toffoli-first hypothesis. It was
tested only as an environment override so failure could be discarded without
editing source.

Experiment 2 followed the source comment that `R1_MUL` has a jagged, discrete
response. Rather than assuming the promoted minimum survived later rebases,
finite neighborhoods of `R1_MUL`, `R1`, and `R2` were screened by emitted
operation count. This count was used only for cheap ranking; the best candidate
still had to pass the untouched 9,024-shot verifier.

### Commands, failures, and course correction

The endpoint candidate used:

```sh
SUB4_PP_ENDPOINT_FOLD_WINDOW=17 ./target/release/build_circuit
./target/release/eval_circuit \
  --note "exp1 endpoint fold 17 existing nonce"
```

It emitted 12,438,785 operations, 84 fewer than baseline, with peak width
unchanged at 1,266. Full verification found 17 classical mismatches and phase
garbage in 21 batches. It was rejected and never baked into source.

The split-point sweeps repeatedly ran `build_circuit`, one override at a time:

```text
SUB4_PP_R1_MUL = 318 through 334
SUB4_PP_R1     = 329 through 341
SUB4_PP_R2     = 640 through 650
```

The first two ranges confirmed the shipped values 326 and 335 as their local
minima. The `R2` range found 641 at 12,438,857 emitted operations, twelve fewer
than the shipped stream. It was fully tested with:

```sh
SUB4_PP_R2=641 ./target/release/build_circuit
./target/release/eval_circuit --note "exp2 R2 645 to 641"
```

That run kept 1,266 qubits but found 23 classical mismatches and 19
phase-garbage batches. The candidate was rejected and no production source
change was retained.

### Nonce-search tradeoff

An exact development-only CPU screener was temporarily implemented. It cloned
the SHAKE256 prefix state, encoded each identity-tail nonce exactly like the
trusted evaluator, generated the same 9,024 elliptic-curve inputs, and rejected
on the first bad 64-shot batch. It was cross-checked against known clean nonce
`6003138460055` and correctly reported a pass. The screener was then completely
removed; it is not present in the final diff or emitted circuit.

The tool confirmed that local infrastructure was not the blocker. Existing
source notes report that even favorable configurations remain at least two
orders of magnitude beyond a 10,000-candidate budget. A twelve-operation gain
does not justify days of CPU grinding, particularly while the shared frontier
can move. This pass therefore records a correct negative result instead of
claiming an unverified improvement.

### Final audit and official verification

The final committed diff contains this Markdown file only. Every circuit
source file is byte-identical to `edeed3f`; no dependency, benchmark, score,
results, or frozen file was committed. The final run was:

```sh
cd /mnt/c/Users/ssgkg/Documents/test/ecdsafail-opt
ecdsafail run
```

It rebuilt the official binaries, emitted 12,438,869 operations, loaded 1,266
qubits and 941,670 classical bits, and passed all 9,024 shots with zero
classical mismatches, zero phase-garbage batches, and zero ancilla-garbage
batches. It exactly reproduced average Toffoli `903462.889`, average Clifford
`10271192.373`, and score `1143784158`.

This submission does not claim a new score frontier. It closes three nearby
schedule searches and records `R2=641` as a concrete future nonce-grind lead.
Do not repeat these ranges. Revisit 641 only with a high-throughput exact
search fleet, then rebase onto the latest promoted head and require another
clean `ecdsafail run` before claiming or submitting a score improvement.
