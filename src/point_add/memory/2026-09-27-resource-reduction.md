# Resource reduction, 2026-09-27

## Verified result

**The one-qubit target is achieved: 1250 to 1249 physical qubits.**

| Metric | Starting circuit | Final circuit | Change |
| --- | ---: | ---: | ---: |
| Peak qubits | 1250 | 1249 | -1 |
| Average executed Toffoli | 889084.873 | 1047142.930 | +158058.057 |
| Rounded Toffoli in `score.json` | 889085 | 1047143 | +158058 |
| Score | 1111356250 | 1307881607 | +196525357 |
| Emitted operations | 12191303 | 14975823 | +2784520 |

`ecdsafail run` passes all 9024 shots with zero classical mismatches,
phase-garbage batches, or ancilla-garbage batches. The independent audit also
passes 8192 fixed-seed inputs plus 64 measurement trials of the saved regression
point, checking zero-valued resets and unconditional clean-wire loans.

**The total Toffoli count and score did not improve.** Exact local gate savings
were outweighed by correcting inherited overflow/precision/convergence
failures instead of searching validation nonces. The identity-tail value was
never changed. Both the qubit improvement and the gate-count tradeoff are
reported here rather than treating an invalid low-gate circuit as a win.

## Scope and baseline

Only `src/point_add/` is editable. The evaluator, simulator, dependency files,
and benchmark script are unchanged; `results.tsv` is written by the evaluator.
The starting sources were archived before editing.

The starting circuit is substantially optimized beyond the README's original
reference circuit. A fresh `ecdsafail run` established this baseline:

| Circuit | Qubits | Average executed Toffoli | Score | Operations | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| Starting circuit | 1250 | 889084.873 | 1111356250 | 12191303 | All 9024 shots pass |

The baseline has zero classical mismatches, phase-garbage batches, and
ancilla-garbage batches.

## Investigation

The point adder uses classical-coordinate arithmetic, a shrinking alternating
binary-GCD walk and interleaved coefficient replay for division/multiplication,
and recursive squaring. Carry ladders are sized from the builder's actual live
qubit count, with `PP_WALK_MAX_QUBITS` as their common budget. The evaluator
counts the largest referenced physical wire ID plus one, so lowering an
allocation estimate alone is insufficient: the emitted circuit must use fewer
physical wires.

The inherited implementation also contains explicitly approximate comparison
windows and a previously selected identity-tail nonce. Changing circuit gates
changes the Fiat-Shamir test inputs. No nonces were searched, the evaluator was
not weakened, and failing inputs were retained and investigated.

## Experiments

1. Lower the shared carry-ladder budget from 1250 to 1249 without changing
   arithmetic widths, round counts, comparison guards, or the tail nonce.
   Measure the actual physical width and run the complete evaluator.
2. Independently investigate exact squaring identities and published reversible
   arithmetic techniques for gate savings without increasing the live width.

### One-qubit budget experiment

The unmodified arithmetic could not build at budget 1249: a squaring WCIN
window asserted `room 150 owned 153`. This is a construction constraint, not a
passing resource reduction. That path had to honor its actual workspace budget
rather than merely lower the configuration value.

### Exact terminal-carry fusion

`const_arith::carry_ladder` unnecessarily allocated and measured the carry into
the highest sum bit. That bit is already the intended destination of the
carry, so the last majority/AND can instead XOR directly into it. Only the
lower internal carries are subsequently measured and phase-corrected.

This mirrors the existing register adder's terminal-step optimization. It
saves one clean scratch qubit in an ordinary constant/controlled-constant
ladder without adding Toffolis, and removes the highest carry's measurement,
phase correction, reset, and sum-copy Clifford operations. A borrowed clean
low bit can still host the highest *internal* carry. Zero and top-bit-only
constants naturally require no carry scratch.

Exhaustive small-width tests cover every constant, accumulator, and control
value for addition/subtraction at widths 2 through 7, including the borrowed
low-bit subtraction precondition. They check arithmetic, unchanged controls,
zero ancillas, zero phase, exact width, and unchanged Toffoli count. Independent
per-position controls are also checked exhaustively.

### Exact squaring improvements

The merged correction's maximum value is 975, so it needs ten bits, not eleven.
Two inverse additions now reuse the existing affine-output carry-streaming
helper. The measured local fixture improves from 104 to 59 Toffolis and from
140 to 139 peak qubits. The diagonal correction also omits an always-zero top
pad in both directions, saving a scratch qubit without changing its Toffolis.

The WCIN window now falls back to the existing exact, workspace-bounded
composition planner when more than one wire short. Tests cover the actual
155-bit window with 150 scratch wires, narrower budgets, and fold guards
through 40. Arithmetic, unchanged operands, phase cleanup, clean resets, and
inverse composition are checked, including exhaustive small-width cases.

### Independent precision checks

The exact arithmetic changes alone exposed the inherited seed sensitivity:
one complete 1250-wire run had 14 classical mismatches and 12 phase-garbage
batches. A separate, fixed-input-seed 8192-shot regression found 20 classical
and 13 phase failures. Instrumenting the builder only in tests attributed dirty
resets to terminal walk loans, coefficient cleanup, and walk restoration, not
the new constant-adder primitives.

The terminal loan assumes both GCD values have reached +/-1. The inherited
depth did not always suffice. Twelve additional narrow terminal rounds were
evaluated first in both traversals. Fold and comparison windows are widened
by eight bits to reduce the separate truncation channels rather than selecting
a different validation nonce. These changes have a resource cost; final
reported metrics must include it.

### Root causes and successful correctness checkpoint

Increasing terminal depth alone did not fix the same failing inputs. The
ordinary walk first formed a fixed-width signed sum and then halved it; the
sum can overflow even when the average fits. The existing `average` primitive
preserves the correct signed carry, but had been enabled only on selected
rounds. It is now used on every ordinary round from round 3 onward. Exhaustive
4- through 7-bit tests cover all signed operand pairs, supported bridge counts,
phase cleanup, and forward/inverse composition.

Once signed overflow was fixed, the audit exposed overly aggressive walk
shrinks. Seven guard bits were first retained across the original width schedule,
and the incompatible one-bit narrowing exceptions are disabled. Retained
division/multiplication receivers now use a complete finite-window fold or
fall back to the standard receiver; they never select the independent
32-bit low-carry-dropping approximation.

A checkpoint using 22 extra terminal rounds passed all 9024 official shots
and all 8192 independent shots, but used **1256**, not fewer qubits. Its
average Toffoli count was 1009203.377. This was a correctness checkpoint,
not a completed resource improvement.

### Exact space-bounded phase comparison

An allocation census found the remaining peak: a 1233-wire live state plus
23 comparison carries. The phase comparator had not respected the shared
workspace budget. It now keeps as many Gidney product carries as fit, then
uses in-place Cuccaro majority stages for the remainder. The final phase
predicate is unchanged, and inverse majority restores both operands exactly.
Each omitted carry costs one extra Toffoli, executed only on the existing
classical condition.

Exhaustive 2- through 6-bit tests cover all operands, external carry inputs,
carry inputs aliasing any supported source bit, every available scratch
budget, and an outer classical condition. The circuit then used **1249
physical qubits**, but one newly drawn official input still failed. Retaining
that exact input and adding round attribution located the first dirty shrink
near round 643 at width 34. Tapering the terminal rails alone did not fix it.
The original walk schedule therefore now receives twelve, rather than seven,
guard bits. The additional terminal rounds retire one guard bit every four
rounds, from fifteen-bit to ten-bit rails; the terminal footprint is unchanged.

An emitted-lifetime wire-compaction experiment did not lower the whole-circuit
peak and was removed rather than retaining an ineffective pass.

The retained-fold planner now includes the complete exact cleanup cost before
selecting a candidate. A negative gate saving rejects that candidate in favor
of the standard receiver, avoiding Toffolis spent on an unprofitable fusion.

## Algorithm research

- [Gidney, *Halving the cost of quantum addition* (2018)](https://arxiv.org/abs/1709.06648):
  temporary logical ANDs can be erased by X-basis measurement and conditional
  phase repair, rather than a second Toffoli. The nested adder uses linear live
  scratch, not one arbitrary dirty ancilla. This is the measured portion of
  the hybrid comparator and the existing carry-uncomputation mechanism.
- [Cuccaro, Draper, Kutin, and Moulton, *A new quantum ripple-carry addition circuit*
  (2004)](https://arxiv.org/abs/quant-ph/0410184):
  in-place majority/unmajority trades gates for workspace. The standard
  initial carry is clean or explicitly defined; arbitrary dirty carry-in
  changes the sum. The bounded comparator uses these exact in-place majority
  identities only where a separate product carry would exceed the budget.
- [Haener et al., *Improved Quantum Circuits for Elliptic Curve Discrete
  Logarithms* (2020)](https://arxiv.org/abs/2001.09580):
  inversion, arithmetic scheduling, and reversible workspace reuse are central
  resource tradeoffs. The repository's record/replay organization was retained,
  rather than replacing it with an unrelated field representation.
- [Bernstein and Yang, *Fast constant-time gcd computation and modular
  inversion* (2019)](https://eprint.iacr.org/2019/266):
  fixed iteration bounds require a proof for the particular recurrence.
  Bounds for their signed-delta divsteps cannot be applied to this alternating
  odd-value walk. The added rounds and width margins here are empirically
  validated, not presented as a transferred worst-case proof.

For a non-aliased `n`-bit phase comparison retaining `k` product carries, the
hybrid construction uses `2*(n-1)-k` Toffolis and `k` scratch qubits, before
the caller's existing classical condition is applied. It restores both
operands and any borrowed carry input. An aliased low source seed first removes
the algebraically redundant lowest position, as in the original helper.

## Reproduction and limitations

From the repository root:

```sh
ecdsafail run
. "$HOME/.cargo/env"
cargo test --release --locked --offline --bin build_circuit -- --include-ignored --test-threads=1
```

The opt-in tests include exhaustive arithmetic primitives, the physical-width
regression, independent points, the saved failing point, and diagnostics using
the input seed from the current `ops.bin`. These diagnostics only read that
artifact; the trusted evaluator remains the source of `score.json` and
`results.tsv`. Final verification passed **all 14 tests**, including the opt-in
tests, with none ignored. Repeating `ecdsafail run` produced a byte-identical
`ops.bin` and the same score. Hashes of the harness and dependency files matched
the pre-edit snapshot.

The primitive rewrites are exact on their stated domains. The complete point
adder still has finite fold/comparison windows and scheduled GCD widths, so
passing these tests is **not an all-input correctness proof** or a complete
Shor-algorithm resource estimate. No claim of universal correctness or a lower
total Toffoli count is made.
