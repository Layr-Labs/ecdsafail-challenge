# Research status — what is proved, what failed, what remains open

This is the handoff for the verifier-centered research performed against promoted source
`cf5aa02147d4e1a698bbf84c10d33920d4356489`. The repository has been reset to that official source. Experimental
production edits, raw solver traces, generated CNFs, ledgers, and controller infrastructure were deliberately removed.
The small programs in `repro/` are the retained executable knowledge.

## Official frontier and evidence standard

| field | certified value |
|---|---:|
| promoted submission | `0c5b1b7b-561a-48a0-abc6-5fefaffdc0ad` |
| score | `1,490,805,286` |
| average executed Toffoli | `1,291,859.302` (`1,291,859` rounded) |
| total executed Toffoli | `11,657,738,337` over `9,024` shots |
| qubits | `1,154` |
| emitted operations | `9,062,420` |
| compressed `ops.bin` SHA-256 | `7333b19de3f3171a70d1b5132e867b7fb28cd5d77b34668175b391c420eed8c9` |
| canonical decompressed-operation SHA-256 | `ec90afeadf8d294819e1e2128764c9da8d0742730c09d4ac1ae19d3b1a99dfba` |
| official result | `9,024/9,024`; zero classical, phase, and end-of-forward ancilla failures |

The trusted scorer is

\[
S(T,Q)=\min(\lfloor T+0.5\rfloor Q,2^{64}-1).
\]

`T` is the verifier's average executed Toffoli count and `Q` is `max referenced qubit id + 1`; neither emitted gate
count nor live-qubit count substitutes for these values. Only a byte-identical artifact or a complete `ecdsafail run`
is transfer evidence. See `repro/exact_scorer.py` and `04-traps.md`.

The verifier accepts exactly four 256-bit registers typed quantum/quantum/classical/classical, all affine outputs
correct, zero residual phase, and zero non-output qubits after the forward pass. The operation cap is four billion.
The ABI alone gives `Q >= 512`; no nontrivial global Toffoli lower bound was proved.

## Status vocabulary

- **Established:** proof, exact enumeration, or exhaustive replay within the stated scope.
- **Observed:** measured on named artifacts/seeds; not a theorem.
- **Refuted:** a preregistered prediction received a concrete counterexample.
- **Unresolved:** neither a witness nor a lower-bound certificate exists. Timeout is not evidence of UNSAT.
- **Relaxation:** an oracle or assumption used only to price headroom, not an implementation.

## Established scoped results

### 1. The standalone five-wire pair normalizer needs exactly six CCX in the tested class

`compress_2sym_fast` feeds `NORMALIZER_OPS` 25 distinct five-wire states, not five raw three-bit symbols. On those 25
states the normalizer maps bijectively to canonical values `0..24`.

For the class **no ancilla, arbitrary affine gates, and affine-conjugated CCX gates on those five wires**, every CCX is
one reversible generalized shear. Exhaustive quotient search produced:

- input depth-two frontier: `913,220` states;
- output depth-two frontier: `908,804` states;
- exactly one shared rank-five hyperplane pair;
- all `420` admissible independent affine-control products on that hyperplane rejected as a bridge;
- no path of five or fewer generalized shears;
- the shipped six-shear reference independently replayed through pinned Kissat and CaDiCaL SAT witnesses.

Therefore the exact minimum is **six CCX in this class**. This is not a global normalizer bound: ancillas, non-affine
intermediate representations, or absorbing surrounding compressor logic are outside scope. Do not rerun a standalone
at-most-five search unless the gate/representation class changes.

Reproducer sources: `repro/y5_pair25_quotient.py`, `repro/hyperplane_mitm.cpp`,
`repro/y5_normalizer_synth.py`.

### 2. Two one-shear neighborhoods of the joint six-wire codec are closed

The useful broader map combines `compress_2sym_fast` with `NORMALIZER_OPS`. Its verified reference costs eight CCX
forward and nine CCX in the reversible cleanup. It replays all 64 six-wire states, including all 25 reachable inputs,
and has an explicitly invertible affine output map.

For exact-eight synthesis:

- all `8/8` branches replacing one adjacent pair of the nine reference shears by one arbitrary shear are UNSAT;
- all `288/288` branches retaining seven reference shears and inserting one arbitrary shear are UNSAT; the sole initial
  timeout was independently settled UNSAT by Kissat and CaDiCaL.

These are class results around the shipped reference, not a global eight-CCX lower bound. Reproducers:
`repro/y5_joint_codec_neighborhood.py` and `repro/y5_joint_codec_two_rebase.py`.

### 3. Small-width composite controlled arithmetic did not expose a gain

For the restricted `n=3` GCD cswap-plus-controlled-subtract map (`u` odd, `v0=t`, `s=>t`), exact XOR/AND synthesis
settled multiplicative complexity at five: bounds zero through four were UNSAT and five was SAT in both Kissat and
CaDiCaL. That equals the reference. This refutes this small branch as an immediate optimization surface; it does not
prove the large-width optimum. Reproducer: `repro/y1_composite_synth.py`.

### 4. Whole-dialog information slack exists, but no usable streaming codec is known

With fixed initial `u=p`, the exact complete dialog and terminal state identify one input `x`; all `p-1` inputs give
distinct dialogs. The exact information rank is 256 bits versus the current 609-bit representation, a 353-bit
information gap. This is only an information bound. No reversible streaming rank/unrank construction was found that
keeps the apply traversal below the current peak. The naive endpoint construction regenerates the full tape and saves
zero peak qubits. Reproducer: `repro/y3_global_codec.py`.

### 5. One source-level implication is exact but already represented empirically

Before `controlled_clean_add_threaded` call 0, bit 0, in the no-carry branch, the source state implies the redundant
control. Two solvers proved the violating assignment UNSAT before and after an identity perturbation. Replacing that
specific CCX with CX is sound, but it merely reproduced one existing empirical downgrade: the emitted artifact and
score stayed byte-identical. The important reusable result is methodological: source-indexed certificates survive
same-tuple ordinal shifts that invalidate persistent census keys. Further work must find *new* source implications, not
re-encode existing table entries.

## Refuted or exhausted approaches

| approach | decisive result | implication |
|---|---|---|
| Five raw-symbol normalizer restriction | After rebasing its stale key, the official verifier failed `9,024/9,024` classical shots and all `141` phase batches. | The true domain is the 25 post-compressor five-wire states. |
| Direct terminal-carry reuse | Isolated miter passed 2,736 cases and predicted one CCX saved per call; production official run failed 24 classical shots and 15 phase batches. Individual GCD, less-than, and carry surfaces also produced trusted counterexamples. | The isolated phase/value abstraction was not compositional. |
| Four-bit terminal dialog codec | Tape bits fell 609→605, but peak qubits stayed 1,154 and final CCX rose by 8,038; break-even was 4,493. Support-miss rate was about `3e-4`. | Statically product-negative and not exact. |
| Final CCX self-inverse cancellation | Exact strict-clean and net-restore analyzers both found zero pairs in 9,073,163 pre-strip operations. | Do not rerun these same-tuple pair classes. |
| Deep-strip localization | On a committed root, full and completely unstripped streams had the identical 13 classical failure shots; restoring all final empirical transforms cost 12,803.278 executed Toffoli. | Transfer failures originate upstream, not in the final deep-strip table. |
| Coordinate ports | No tested ABI-compatible representation cleared its qubit-specific Toffoli cap. The strongest local `Q=835` case already required 6,443,568 Toffoli for two inversions before shell cost, versus a cap of 1,785,395. | A new representation needs a complete four-register-compatible cost, not a qubit claim alone. |
| Perfect coordinate-shell oracle | Granting the measured shell zero cost would save about 1,600 executed Toffoli and lower score by 1,846,400 (`1,488,958,886`). | Headroom exists, but the oracle supplies no reversible implementation. |
| More nonce grinding | The current artifact's pooled nonce Toffoli SD was 8.694 over 384 disjoint draws; correctness success remains exponentially rare on ordinary seeds. | Nonce outcomes select artifacts but do not create transferable structural gain. |

The coordinate-shell score delta is exactly `1,846,400`: `1,490,805,286 - 1,488,958,886`. The displayed oracle is a
relaxation, not a candidate.

## Open problems — do not overstate the stop

### Unrestricted exact-eight joint synthesis remains open

The exact-eight CNF had 11,416 variables and 54,051 clauses. Kissat, CaDiCaL, and diversified CryptoMiniSat runs timed
out or exited indeterminate. No witness was found, but there is **no UNSAT proof**. All seven branches replacing a
contiguous reference triple by at most two arbitrary shears also remain unresolved.

The run stopped at its preregistered two-local-CPU-hour cap (`7,113.268` conservatively charged seconds), not because a
theoretical ceiling or abstraction impossibility was demonstrated. Repeating the same CNF and solver portfolio had low
expected return. Reopen with one of:

1. a machine-checkable symmetry reduction;
2. a materially stronger exact encoding;
3. a distinct synthesis representation or gate class;
4. a compiled exact-eight witness that replays all 25 forward/inverse pairs.

Do not describe the generalized-shear abstraction as globally saturated: only the two named neighborhoods and the
standalone five-wire class are closed.

### Other high-leverage uncertainties

1. Controlled quantum addition has a proven `n` lower bound and a roughly `2n` construction; the factor-two gap remains.
2. A streaming exact dialog ranker could exploit a large information gap only if its rank/unrank logic and live set beat
   the current product.
3. New source-state implications can outperform ordinal census keys only when they remove gates not already downgraded.
4. Any low-qubit representation must price both inversions, affine-output cleanup, four-register ABI compatibility, and
   executed—not emitted—Toffoli.
5. The current representation's oracle floor `(T,Q)=(132,864,1,022)` and score `135,787,008` is a deliberately impossible
   relaxation: it grants perfect arithmetic outside retained swaps and releases 132 peak owners. It maps headroom; it
   is not an attainable design.

## Re-entry commands

Run all lightweight retained checks first:

```sh
python3 -m unittest discover -s src/point_add/memory/repro -p 'test_*.py' -v
python3 src/point_add/memory/repro/exact_scorer.py --backtest results.tsv
```

Regenerate the pair25 depth-two frontiers only when auditing the exact-six proof; this is intentionally expensive and
creates transient `.autoresearch/` output:

```sh
python3 src/point_add/memory/repro/y5_pair25_quotient.py \
  --output .autoresearch/measurements/pair25/report.json \
  --frontier-dir .autoresearch/measurements/pair25
clang++ -std=c++20 -O3 -DNDEBUG src/point_add/memory/repro/hyperplane_mitm.cpp \
  -o .autoresearch/measurements/pair25/hyperplane_mitm
.autoresearch/measurements/pair25/hyperplane_mitm \
  .autoresearch/measurements/pair25/x-depth2.bin \
  .autoresearch/measurements/pair25/y-depth2.bin
```

For a genuinely improved joint encoding, start from `repro/y5_joint_codec_synth.py`; the three neighboring scripts
encode the already-tested subclasses. Any SAT witness must be compiled, replayed forward and inverse on all 25 valid
pairs, then passed to the untouched official court:

```sh
ecdsafail run
```

Never submit from a proxy result. Never treat a timeout as a lower bound. Re-run `ecdsafail benchmark` and
`ecdsafail sync` before new work because the promoted frontier can move.

## Retained files

| file | purpose |
|---|---|
| `repro/exact_scorer.py` | exact score arithmetic and historical backtest |
| `repro/y1_composite_synth.py` | reusable XOR/AND CNF support plus the scoped `n=3` experiment |
| `repro/y3_global_codec.py` | exact dialog-rank and bounded suffix experiments |
| `repro/y5_normalizer_synth.py` | five-wire generalized-shear encoding and reference compiler |
| `repro/y5_pair25_quotient.py` | exact depth-two affine-quotient frontier generator |
| `repro/hyperplane_mitm.cpp` | exact fifth-edge bridge checker for the pair25 proof |
| `repro/y5_joint_codec_synth.py` | unrestricted joint six-wire exact synthesis encoding |
| `repro/y5_joint_codec_{neighborhood,two_rebase,triple_fusion}.py` | closed and unresolved local subclasses |
| `repro/y6_source_invariant.py`, `repro/artifact_io.py` | source-indexed invariant proof utility |
| `repro/test_*.py` | fast contracts for the retained machinery |

Everything else from the research harness was operational scaffolding or bulky evidence. It was removed after these
scoped conclusions, counterexamples, hashes, and reproducers were retained.