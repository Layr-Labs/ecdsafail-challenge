# Bounded Exact Boolean Pass

Base: `bdfd306`, verified Q1024 / T17206967.075576 / nonce14130.
Branch: `codex/midq-boolean-pass`, separate `ecdsafail-midq-boolean-pass` worktree.
Only `src/point_add` changed. No harness/dependency edits, public actions, nonce
search, CLZ phase cleanup, terminal counter/tape edits, or new-prefix integration.

## Controls And Placement

- `MIDQ_EXACT_BOOLEAN=1`: enable constants and versioned clean-AND discharge.
- `MIDQ_EXACT_BOOLEAN_ALIASES=1`: additionally enable exact two-term affine aliases.
- Both require the literal value `1`; both default OFF. Aliases alone do nothing.
- `MIDQ_EXACT_BOOLEAN_SELFTEST=1`: local component tests, returns an empty circuit.
- `MIDQ_EXACT_BOOLEAN_PROFILE=1`: with the pass enabled, run a bounded 64-input
  paired diagnostic and return the same optimized circuit. Not a scored evaluator.

Placement is AFTER adjacent, disjoint-commuting, and X-family cancellations,
BEFORE reattaching the unchanged final 96 X;X nonce operations. A regression test
demonstrates that running this pass first can block a two-CCX cancellation.

## Proof Boundary

Registered qubits start unknown, using a full-stream metadata scan BEFORE any
propagation, including declarations at the END. Other qubits start zero only under
the existing benchmark simulator contract; this is not an arbitrary dirty-input
compiler API. Constants are propagated forward only. An unconditional R or
HMR proves its OUTPUT zero, never its input. Every source phase gate, including
conditional NEG/Z/CZ/CCZ, is retained unchanged.

An AND witness is recorded only for an unconditional CCX into a proven-zero
target. Its later cleanup requires the same control IDs and versions, no target
write, and the same barrier epoch. Replace only that cleanup with HMR(t)->m and
CZ(a,b) conditioned on the fresh m: (-1)^(m*t+m*a*b)=1 when t=a*b. Diagonal use
and coherent controlled use of the target do not invalidate this value relation.

X/CX/CCX targets, both SWAP wires, and R/HMR targets advance their versions.
Every source measurement/reset, classical instruction, condition-stack boundary,
or per-op classical condition invalidates all AND/affine relations. No rewrite
occurs inside a condition block or on a classically conditioned instruction.
Untouched computational constants remain valid. Inserted *corrected* measurements
preserve other value relations; writes to their target still invalidate dependents.

Affine facts are XORs of at most two opaque atoms plus a constant. Equality and
complementarity are exact; atom independence is never assumed. Expressions wider
than two atoms are forgotten, not truncated. No version or barrier rule is relaxed.
Runtime is O(operations), fact storage O(qubits), with an output operation vector.

## Measured Results

Both candidates pass the original nonce14130's frozen 9024 inputs with 0 classical,
0 phase, and 0 ancilla failures. These are fixed-input local regressions, NOT new
Fiat-Shamir-clean submissions. Unmodified local `eval_common` was reused externally.

| Mode | Q | Total T / 9024 | Average T | Average saving vs baseline |
| --- | ---: | ---: | ---: | ---: |
| Baseline/pass OFF | 1024 | 155275670890 | 17206967.075576 | 0 |
| Constants + AND | 1024 | 154366416886 | 17106207.544991 | 100759.530585 |
| Plus affine aliases | 1024 | 154275572478 | 17096140.567154 | 110826.508422 |

The affine candidate saves 0.644079% measured T. Its average Clifford count is
31006315.191489, +81629.771609 over baseline. No extra qubits are allocated.

| Mode | Constant T rewrites | Alias T rewrites | Measured ANDs | Ops including tail | Classical bits |
| --- | ---: | ---: | ---: | ---: | ---: |
| OFF | 0 | 0 | 0 | 64318142 | 1512084 |
| Constants + AND | 20061 | 0 | 80445 | 64376616 | 1592529 |
| Plus aliases | 27752 | 2679 | 80449 | 64334793 | 1592533 |

On the paired 64-input profile, original total T=1101261548; the basic candidate
has 1094829164 and affine has 1094165228. Exact matched-tape savings are respectively
100506 and 110880 T per shot. Every rewritten T gate is unconditional. These differ
from independently evaluated 9024 averages because inserted HMRs shift subsequent
RNG draws, including source classically conditioned T/CCZ execution counts.
The prior approximately 210k prototype estimate is NOT reproduced or claimed.

## Correctness Receipts

- Final release selftest: 78571520 basis/measurement cases, aliases both OFF/ON
  and input register declarations at both the beginning and END of every circuit.
  Includes all small gate pairs, 512 longer deterministic random circuits, dirty
  registered targets, control/target writes and restore sequences, SWAP orientation,
  classical nesting/conditions, forced zero/one and random measurements, phases,
  two-term alias equality/complement/overflow/barriers, and live controlled witnesses.
- Compare actual emitted original/replacement sequences at EVERY source boundary,
  including before resets with garbage; no final reset is added to conceal scratch.
  Final states are also cross-checked with the unchanged `Simulator`.
- 20 complete coherent measurement branches compare complex entangled-witness
  amplitudes, including global phase and the explicit fresh-HMR Kraus normalization.
- Full production paired profile: all 64318046 prefix boundaries agree, including
  623 pre-reset dirty events. All quantum wires, original classical bits, and phase
  agree with the unchanged simulator. One shared baseline classical failure on the
  fixed 64-input sample; no phase/ancilla failures and no newly failing inputs.
- Independent 9024 corpus, affine candidate: same five classical failure IDs as
  baseline: 4174,4968,5407,7617,7854. Phase failures occur on those same five inputs
  (baseline had phase failure only at5407); no new any-channel failing input and
  no ancilla failure. The phase-count change is on already-bad inputs with shifted
  measurement randomness, not a matched-tape phase-equivalence claim.
- `cargo build --offline --release --bin build_circuit` passes. Ordinary
  `cargo test --lib --no-run` remains blocked by the documented baseline test-port
  problems: 207 errors, including missing `tests`, `rand`, and `zkp_ecc_lib`.
  No dependencies or trusted code were changed to work around this.

## Hashes And Local Artifacts

SHA256 of compressed `ops.bin`:

```text
OFF:    fc8d00bbb7f56ce6e05d171b9316719f8b54277addbda06169ce6c22323218e8
basic:  86ddb622dac4e61fffd325e9a428c85858b3b115ee865d65053bda77a87f403e
affine: c95f1e9918652c61c32ff555dfd09c7fe24ce8e8efd6aa0aa2cd719770853be1
tail:   ba1d82b40f3a6371f3bdf72b006131e5df82408a4aef3b5f9362bfbd5ae4b4bf
```

OFF matches the verified baseline byte for byte. `tail` is the SHA256 of the last
5376 decompressed record bytes (96 operations); baseline and affine are identical.
The final rebuilt affine artifact matches the tested artifact byte for byte.

Local-only logs/artifacts live under `/private/tmp`:
`midq-boolean-{off,on,alias,final}/`, `midq-boolean-selftest.log`,
`midq-boolean-build.log`, `midq-boolean-cargo-test.log`.

```text
SHA256 selftest log:       dc52df76a1d7100a008d29f95044fcbbce1ac9a5ff02d8cb1c413101b8c0b4f4
SHA256 basic frozen9024:   2bf1be4a7b53084297f79f42dc93bfa983f1bdb19a5b2972a12bdbc6415f1a40
SHA256 affine frozen9024:  a2ece572e710077cd8dd3de6bc68c1db3cb800d1d4ccce6d00354d03fa307aa0
SHA256 affine common9024:  499eacb2e2fd7e9b99ae10c9480b793f28592a6023d950a8467893ce5f0be60b
```

## Reproduction And Handoff

Build in this worktree with `cargo build --offline --release --bin build_circuit
--target-dir /private/tmp/midq-boolean-target`. Run that absolute binary from a
dedicated diagnostic directory, since it writes `ops.bin` in its current directory.
For component tests set `MIDQ_EXACT_BOOLEAN_SELFTEST=1`. For the stronger candidate
set `MIDQ_EXACT_BOOLEAN=1 MIDQ_EXACT_BOOLEAN_ALIASES=1`; add
`MIDQ_EXACT_BOOLEAN_PROFILE=1` for the 64-input matched-tape diagnostic.

The frozen-input command, run in a candidate artifact directory, was:

```sh
COMMON_SEED_OPS=/private/tmp/midq-boolean-off/ops.bin \
  /Users/jieyilong/Personal/research/ShorOptimization/shor_optimization_workspace/ecdsafail-midq-further/target/release/eval_common
```

Main reported a separate clean Q1024/T15.62M prefix-query improvement during this
work. This branch intentionally stays on bdfd306. Integrate only after that route's
existing cancellations, retain the detached nonce tail, and reprofile composition:
the available proofs and measured savings can change. Do not assume a 200k delta.
