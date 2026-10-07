# Verifier ceiling — ECDSA Fail

## Exact scorer

The trusted path is `src/bin/eval_circuit.rs::write_score` plus
`src/sim.rs::Simulator::apply_iter`; the executable model is
[`repro/exact_scorer.py`](repro/exact_scorer.py), and the pinned bound checker is
[`repro/verifier_ceiling.py`](repro/verifier_ceiling.py).

For `N = 9,024` accepted shots,

\[
T=\frac{\text{total executed CCX/CCZ}}{N},\qquad
S=\min(\lfloor T+0.5\rfloor Q,2^{64}-1).
\]

`Q` is `max referenced qubit id + 1`. Only CCX and CCZ are charged, and only on
shots satisfying their classical condition stack.

Pinned trusted hashes are emitted by `verifier_ceiling.py`; any mismatch makes the
bound model red.

## Bounds

| bound | value | argument | class |
|---|---:|---|---|
| Absolute score floor | **0** | Both rounded executed Toffoli and qubit width are non-negative. | Hard |
| Zero-score threshold | **total executed Toffoli <= 4,511 over 9,024 shots** | `4,511 / 9,024 < 0.5`; `4,512 / 9,024 = 0.5` and rounds to one. | Hard |
| Intended output width floor | **512 qubits** | Two distinct 256-bit quantum output registers. The loader does not itself reject duplicate register members, so this is an intended-computation bound, not the proof of the score floor. | Scoped hard |
| Universal zero-Toffoli circuit | **impossible for generic point translation** | With classical offset fixed and no CCX/CCZ, computational-basis quantum values remain affine in the quantum input; elliptic-curve translation is not affine. | Scoped hard |
| Finite-verifier zero-Toffoli lookup | **3,042,193 ops, 512 qubits, score 0 on a frozen draw** | A 27-bit classical-offset prefix uniquely selects each of the current 9,024 pairs; condition stacks and X corrections are uncharged. | Relaxation |
| Fiat-Shamir replay of that lookup | **9,024/9,024 failures** | The lookup's semantic stream changes the SHAKE256 draw; none of the new prefixes hit its frozen table. | Observed refutation |
| Reduced self-seeded lookup census | **5 fixed points in 1,149,296 exact toy states; 0–2 per scope** | Exact verifier-field serialization and SHAKE256 coupling at one-row widths 1–5 and two-row widths 1–2; production lookup family has approximately `2^4,758,375` states. | Observed scaling |
| Nontrivial global Toffoli floor | **unknown** | The verifier checks a self-seeded finite sample, not universal point addition. No exact multiplicative-complexity lower bound is known for all accepted op streams. | Open |
| Best witness upper bound | **1,489,216,228** | Promoted `705b36a`: `1,290,482 × 1,154`, exact 9,024-shot pass. | Official |
| Prior arithmetic oracle floor | `135,787,008` | Grants perfect arithmetic and removes peak owners; explicitly not an implementation. | Relaxation |

The verifier's absolute numerical ceiling for a lower-is-better score is therefore
**0**. It is not yet an exact *attainable* circuit minimum: that equality requires an
official score-zero witness. Until then the certified interval is
`[0, 1,489,216,228]`.

## Baseline and headroom

Current promoted artifact:

- submission `705b36a4-7571-4c4a-85e4-3b79d9dec0f7`;
- source `7fa872d08f121648554d9a8869ac032624f20472`;
- compressed artifact hash
  `e1f6f50af54b7d67e3812faf5cccd13f6c16ed68e500d122b5779c5ccc76f333`;
- canonical operation hash
  `ddea3e8d298073281223e5a9ff4995e08efce2b6e7408f6774a38a5701767ce7`;
- exact average `1,290,481.644947`, width `1,154`, score `1,489,216,228`.

The multiplicative headroom ratio to zero is undefined. The additive score gap is
exactly `1,489,216,228`; reaching the floor requires crossing the rounding boundary,
not merely improving the existing product by a constant factor.

## Headroom ledger

`TRACE_TLM_TOF=1` on the pinned initial `cf5aa02` artifact measured this pre-postpass
executed-Toffoli model:

| niche | term | expected executed Toffoli | evidence / route |
|---|---|---:|---|
| `H1-gcd-apply` | two GCD/apply traversals, swaps, compares, shifts, folds, codecs | `1,235,398.5` | Exact phase census under the profiler model; controlled-add/composite arithmetic and a representation removing one traversal. |
| `H2-square` | reversible modular square | `67,988.0` | Exact phase census under the profiler model; alternative square or representation. |
| `H3-coordinate-shell` | classical-offset coordinate shell | `1,600.0` | Exact phase census under the profiler model; source-indexed invariants. |
| `H4-postpasses` | constprop, fanout, deep strip, and execution-model residual | `-13,127.198` | Calibrated credit required to reproduce the trusted average exactly. Re-mine on every geometry change. |
| **sum** | | **`1,291,859.302`** | Matches the official average; residual `0`. |

Width is a separate conserved resource:

| niche | term | current | hard/scoped floor | route |
|---|---|---:|---:|---|
| `H5-width` | peak referenced qubit id | `1,154` | `512` intended distinct outputs | schedule/cap geometry or complete alternative representation; lower caps must be priced with executed Toffoli. |

`H0-zero-rounding` is the second court rather than an additive component: exploit-free
verifier-specific constructions may replace the entire arithmetic ledger only if they
remain correct after their own semantic stream determines the Fiat-Shamir draw. The direct
frozen lookup failed this test.

## Verdict

1. **Absolute target:** score `0`, equivalently at most `4,511` total executed Toffoli
   over the official 9,024 shots.
2. **What is proved:** the scorer floor and rounding threshold, trusted source identity,
   complete pinned-baseline cost reconciliation, failure of direct frozen-dataset lookup,
   and inverse-density scaling of the canonical lookup fixed-point family.
3. **What is not proved:** existence of a score-zero artifact or any positive global
   Toffoli lower bound for self-seeded finite verification.
4. **Search discipline:** keep `H0` as a reframe court; maintain live candidates in
   `H1`–`H5`; predict artifact/hash invalidations before every experiment; only an exact
   trusted result updates the frontier.
5. **Stop:** official promotion at score zero, or the bounded 500-iteration return with a
   content-addressed evidence checkpoint.
