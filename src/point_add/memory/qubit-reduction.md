# Quantum-width reduction - 2026-09-26

## Completed score phase - 2026-09-27 12:00 CEST

The extended run completed after **15.8066 active research hours**. The final
working score candidate was reconfirmed with `ecdsafail run`: **1,022,301
Toffolis**, **1,250 qubits**, score **1,277,876,250**, and **9,024/9,024**
official shots passing. It improves the product by **41.5%** from the preserved
1,228-qubit incumbent, while meeting the original 1,250-qubit limit.

The lower-width frontier and all documented statistical limitations remain
preserved. Full results, exact arithmetic changes, independent audits, and
failed-candidate handling are in [score-optimization.md](score-optimization.md).

## Objective update - 2026-09-27 09:14 CEST

The user changed the active objective to reducing **Toffoli x qubits** and
extended work to **12:00 CEST**. The 1,228-qubit result below remains the
preserved width incumbent, not the current score-optimal choice.

The current verified score-focused circuit uses **1,250 qubits** and
**1,022,301 Toffolis**, scoring **1,277,876,250**: approximately 41.5% lower product than
the 1,228-qubit circuit while still meeting the original <=1,250 requirement.
See [score-optimization.md](score-optimization.md) for the implementation,
official results, matched independent audits, and ongoing noon-bound search.

## Ten-hour milestone - 2026-09-27 06:12 CEST

The process clock confirms **10.0585 active research hours**, **9,892**
completed experiment/audit records, and **334** independent audit batches
(10 scheduled hourly audits). The requested minimum duration has therefore
actually elapsed; it is not an estimate or a planned future run.

The verified 1,228-qubit source and artifacts remain intact. No failing
independent-audit recommendation is treated as qualified. Research continues
to the previously announced **10:00 CEST** deadline.

## Independent reliability checkpoint - 2026-09-27 04:37 CEST

The current 1,228-qubit artifact was evaluated on **131,072 predeclared,
operation-stream-independent points**. It had **4 classical failures**, one
of which also had phase garbage, and **zero ancilla failures**. The union
rate was 4/131,072, or `lambda9024 = 0.2754`, with Wilson 95% interval
**0.1071-0.7081**. This does not change the successful official 9,024-shot
validation, but it establishes that the circuit is not universally correct.

A matched stage diagnostic reproduced all four cases. Each coincided with
a predicted native-prefix signed-rail / width miss, before the exact compact
continuation: divide cases at shots 78,923 and 81,736; multiply cases at
81,091 and 110,605. This is consistent with the documented finite-prefix
limitation, rather than evidence that the exact lookup or dirty-workspace
gates can be treated as approximate.

The timed worker remains active. Its independent audit rejection is now
honored: no rejected recommendation is silently marked qualified.

## Latest checkpoint - 2026-09-27 02:45 CEST

**1,228 qubits are officially verified**, with **1,777,434** scored Toffolis
and score **2,182,688,952**. `ecdsafail run` accepted all 9,024 shots with zero
classical, phase, and ancilla failures. The saved known-regression input set
also passes. SHA-256:
`124335a92d712dd5d271b74adfbc14f8c4948a918e56bcc9e367efc2ef0d7b0e`.
The `verified-q1228-polarity*` artifacts preserve this version.

The compact-tail Boolean oracles now use an exact fixed-polarity search.
Gray-code traversal updates one variable's translated coefficients at a time;
the cost function counts actual emitted Toffolis first and Clifford gates
second. Input X frames are undone before each field replay. This reduced
approximately 25,900 Toffolis without changing the truth functions, register
width, or numerical precision. Exhaustive truth-function and dirty-state
tests cover the change, including the known regression.

The active timed search continues with mandatory regression checks and
independent audit revocation. At the latest clock check approximately
**6.56 active hours** had elapsed; the requested ten hours are not yet complete.

## Latest checkpoint - 2026-09-27 02:04 CEST

The current **1,229-qubit** circuit uses an exact additional tape-bit
retirement, 706 native rounds, and a 17-round compact continuation.
`ecdsafail run` passed all **9,024 shots** with zero classical, phase, or
ancilla failures: **1,784,662** Toffolis, score **2,193,349,598**.
SHA-256:
`fbd63e84fc4342485145ee61fe99b24371f37aece40f5fae25ecc46b650c9dd1`.
The `verified-q1229-early-sign*` artifacts preserve this version.

### Retire one more tape bit exactly

The fixed prime is 7 modulo 8. After native round two, its recorded sign is
exactly `1 XOR u[1] XOR u[2] XOR v[1]`. This identity is checked both
algebraically and against emitted boot-walk circuits. It erases and later
reconstructs the tape bit with Clifford gates, without a new approximation.

Division performs its first three field replays early so the bit can be
retired immediately. Multiplication interleaves head replay and inverse
walking so the bit is reconstructed at the matching state. The corresponding
width model now counts three retired signs, and tests check that reducing
the physical cap by one can preserve the previous numerical width envelope.

### Preserve known fixes instead of accepting lucky revalidation

A cheaper 1,229-qubit / 12-round-tail version reintroduced the saved
regression despite passing its own official input stream. It was superseded.
Compact snapshots now support width 8 (magnitudes up to 63), with a proved
17-round bound. Exhaustive quantum tests cover **2,236,928** signed-state /
dirty-workspace combinations across widths 5-8; dirty control-gate tests
extend through ten controls. The current suite has **64 passing tests** and
8 ignored laboratory experiments.

The current circuit passes the original saved failing 9,024-point set and an
independent 9,024-point sample. It does **not** fix every possible prefix
truncation: a newer saved cohort still contains a tracked classical/phase
failure. These finite-prefix limitations are not hidden or reclassified as
universal correctness.

The timed search now requires the saved regression set as an additional
acceptance stage. A post-grid auditing bug was also corrected: failures in
that path now revoke recommendations just like scheduled audits, and periodic
audit counts are distinct from total audit batches. The obsolete unscored
1,227-qubit recommendation was rejected, never promoted, after regression and
independent-audit failures. Its raw observations remain in the journal.

The v7 worker retains the original start/deadline and enforces at least ten
active hours using a monotonic clock. Research is still running.

## Latest checkpoint - 2026-09-27 00:41 CEST

The sweep's **1,229-qubit** candidate passed both 9,024-point laboratory
samples, a separate 4,096-point audit, and the official **9,024/9,024**-shot
`ecdsafail run`. Official metrics: **1,501,372** Toffolis and score
**1,845,186,188**, with zero classical, phase, or ancilla failures.
SHA-256:
`5431064963e2dda598281acda384a2032d3053c7433c5be7d204166478fa77a2`.
The `verified-q1229*` artifacts preserve the source and result.

It retains eight-bit native guards and a 12-round exact continuation after
707 native rounds. The lower-cost field policy uses fold guard 32, outer
comparison 30, replay comparisons 29/28, and replay fold window 66. These are
less conservative than the immediately preceding candidate but still wider
than the inherited settings; finite field-window risk remains. Both qubits
and score improve relative to the preceding 1,230-qubit candidate, not relative
to the inherited low-score circuit.

Timed research remains active; fewer than ten active hours have elapsed.

## Latest checkpoint - 2026-09-27 00:22 CEST

**1,230 qubits are officially verified.** The circuit uses 708 native GCD
rounds plus 12 exact, tape-free continuation rounds per direction. Both
predeclared 9,024-point laboratory samples passed, followed by an official
**9,024/9,024**-shot `ecdsafail run` with zero classical, phase, or ancilla
failures. Scored Toffoli: **1,600,030**; score: **1,968,036,900**.
SHA-256:
`18f00a964a953ffae929206877a028db5ec78f0c079512647643904cfc9b52d2`.
The `verified-q1230-wide-tail*` artifacts preserve the source and result.

### Exact small-state continuation

A 1,235-qubit native-only candidate passed the laboratory samples but failed
one official shot. Instead of changing its nonce or merely retrying, an exact
continuation now handles the small integer pair remaining after the native
walk. It fixed **the same saved failing 9,024-point input set**, independently
of the new circuit's hash, and passed a fresh official run at 1,235 qubits.

After two ordinary rounds at the same width, both walk registers have a
structurally duplicated sign bit. Clear and release those two duplicates.
Normalize the remaining odd values into magnitude bits and their two signs.
Negating either input flips every future replay selector, but only its own
terminal sign; therefore each selector is
`original_u_sign XOR original_v_sign XOR f(magnitudes)`.
An exact Boolean polynomial computes it in an existing sign wire, which is
restored after the field update. No new tape wire is allocated.

Complete finite-state enumeration establishes these bounds:

| Native snapshot width | Signed odd magnitude limit | Exact continuation rounds |
|---|---:|---:|
| 5 | 7 | 6 |
| 6 | 15 | 10 |
| 7 | 31 | 12 |

Both directions retain the snapshot until all associated field replays
finish. Terminal signs are also computed from it, and the snapshot is restored
before the ordinary inverse walk. Tests cover **139,776** signed-state and
dirty-workspace combinations, both starting parities, and field bodies that
change the borrowed bits between oracle computation and uncomputation.

Two small exact adder changes make this work with only the two released
qubits: a supplied incoming carry removes the otherwise-needed zero carry;
and the inverse field update reuses its redundant low bit as the high-word
carry. The ancilla-free constant-adder path handles genuinely full budgets.
The resulting peak accounting is `native_rounds + 2*snapshot_width + 508`.

The 1,235-qubit six-round version passed at **1,427,193** scored Toffolis and
score **1,762,583,355**, hash
`29ed8861a49500d741d6c1e38b77d19bfcc4360bfa2bbe8859855950e3194ba1`.
Larger snapshots allow earlier native stopping without introducing an extra
integer truncation in the continuation.

### Removing the next allocation floor

At 1,230 qubits, the remaining fixed square carry ladder exceeded the budget.
Wrapped arithmetic now uses exact chunking when the native ladder cannot fit,
or an ancilla-free full-source adder at a full budget. Output/carry promises
are still validated; deferred-phase and externally borrowed ladders keep
their specialized paths. This changes workspace, not the arithmetic window.
Both default and 1,230-qubit regression configurations passed.

The prefix walk and existing finite field windows remain statistical
approximations. The exact continuation does **not** establish universal
correctness for inputs already corrupted by an earlier truncation.

Timed research remains active with its original 20:06 CEST start and
10:00 CEST deadline. The v6 sweep prioritizes smaller budgets, stronger
guards, and wider exact snapshots, then lower gate counts. The ten-hour
minimum is still not complete.

## Latest checkpoint - 22:44 CEST

The timed sweep found a **1,236-qubit** candidate with the existing eight-bit
guards and 718 rounds. It passed both predeclared 9,024-point laboratory
samples, then passed the official **9,024/9,024**-shot `ecdsafail run`:
**1,385,910** scored Toffolis, score **1,712,984,760**, and zero classical,
phase, or ancilla failures. SHA-256:
`18b416fcee27a07ecb37d84aa6a899e7767076b90ebbda54e4bf834019aa7a1c`.
The `verified-q1236*` session artifacts preserve the source and result.

At this checkpoint the timed worker had completed 1,903 trials and two
independent hourly audits, with approximately **2.60 active hours** elapsed.
Research continues; the ten-hour minimum is not complete. Same-binary resumes
now retain completed candidates and recommendations, and full validation is
not repeated for configurations already dominated in width and guard strength.

## Latest checkpoint - 22:25 CEST

**1,237 qubits are officially verified**, with **1,375,225** scored Toffolis
and score **1,701,153,325**. All 9,024 official shots passed with zero
classical, phase, or ancilla failures. The eight-bit guard policy was retained.
SHA-256:
`ef900f122e0554ef9888423785fbbec973aa764476fb3102c4c855cc39c4f4d2`.
Source and artifacts are preserved under `verified-q1237*`.

Signed-digit constant decomposition reduced the cost of dirty-register
arithmetic: `f = 1 + 2^4 - 2^6 + 2^10 + 2^32` needs five increments/decrements,
not seven binary increments. A 64-bit controlled `+f` is checked at exactly
**1,072 Toffolis**, versus 1,528 for binary expansion. Reconstruction is
exhaustively checked for all constants through 12 bits, including negative
digits and modular overflow, and arithmetic is tested in both directions.
At 1,238 qubits this lowered the verified score from 1,839,946,550 to
**1,685,584,044** before proceeding to the smaller circuit.

The sweep then showed that the stronger guard at 1,237 qubits was blocked by
an unbounded inverse boot constant, not arithmetic correctness. A shared
`cadd_const_fitted` implementation now budgets both boot directions, chooses
native, exact mapped, or dirty-register arithmetic, and restores the untouched
high word. This removed the overrun without adopting the sweep's weaker-guard
alternative. The current small suite has **56 passing tests** and 8 ignored
laboratory experiments.

Research v5 continues below 1,237 qubits and prefers stronger guards when
width is tied. Hourly independent audits are now anchored to the original
start, so executable upgrades cannot postpone them; missed audit intervals
are caught up. The original 20:06 CEST start and 10:00 CEST deadline remain.
**The ten-hour run is still in progress.**

## Latest checkpoint - 22:08 CEST

The official result is now **1,238 qubits**, **1,486,225** scored Toffolis,
score **1,839,946,550**, with all **9,024 shots accepted** and zero classical,
phase, or ancilla failures. Artifact SHA-256:
`aa9338c2efc9cd7a7de53ce622f5e8b4610b8dec7ee4c52c8e161c105a89b5d6`.
`verified-q1238-source.tar.gz`, `verified-q1238.ops.bin`, and
`verified-q1238.score.json` preserve that result. The current small regression
suite has **53 passing tests**, plus 8 explicitly ignored experiments.

The sweep identified a real fixed-width floor rather than just failing
arithmetic: configurations requesting 1,238 qubits still used 1,239. Two exact
changes remove it. Parent Karatsuba cross arithmetic borrows constant-zero
bits from child retained cross registers, restoring their ownership before
child inverses. Boot-round modular doubling now selects an exact mapped or
dirty-register fold when its native constant carry ladder cannot fit.
`MEASURE_ASSERT_QUBITS` can fail at the first excessive allocation and show
its call stack, instead of waiting for the final census.

An ancilla-free wrapped adder was also implemented and exhaustively checked
against the primary-source construction in Section 2.9 / Figure 15 of
arXiv:1706.07884. Always selecting it added approximately 1.1 million Clifford
operations without reducing this circuit's peak. That unconditional policy
was rejected: the existing carry adder remains preferred when a clean carry
is available, and the ancilla-free version handles genuinely full budgets.
Both paths retain the controlled increment's `4n` Toffoli bound.

**Independent reliability result:** the preceding verified 1,239-qubit
artifact was evaluated on a new 65,536-point full-circuit sample. It had
1 classical failure and no phase/ancilla failures:
`lambda9024 = 0.1377`, Wilson 95% interval `[0.0243, 0.7800]`.
The failing point's ideal multiply walk missed an early signed rail and
required 737 rounds, beyond the finite 721-round budget. The official
accepted-stream result is valid, but is not an all-input correctness proof.
This is not claimed fixed by the subsequent one-qubit reduction.

Timed work remains in progress. The v4 sweep preserves the original
20:06 CEST start and 10:00 CEST deadline, now investigates widths below
1,238, and rejects recommendations if an independent audit fails. Candidates
must pass two separate 9,024-shot laboratory samples after the coarse and
confirmation stages. The ten-hour minimum has **not** yet elapsed.

## Latest checkpoint - 21:32 CEST

**1,239 qubits are officially verified**, down from 1,251. The latest
`ecdsafail run` accepted all 9,024 shots with zero classical mismatches,
phase-garbage batches, and ancilla-garbage batches:

| Metric | Latest verified circuit |
|---|---:|
| Qubits | **1,239** |
| Average executed Toffoli | 1,451,842.823 |
| Scored Toffoli | 1,451,843 |
| Score | 1,798,833,477 |
| Operations | 16,360,001 |
| Active regression tests | 49 passed |
| Explicitly ignored laboratory experiments | 8 |

Compressed artifact SHA-256:
`3590f1bc07a3d2494b79b44ac5758dc47e69c11edd60d68cb6847295b97a82a6`.
The operations, score, and source are preserved as `verified-q1239.*` and
`verified-q1239-source.tar.gz` in the session artifact folder. Earlier
verified 1,250-, 1,249-, and 1,247-qubit candidates are also preserved.

This improves the width objective, **not the original score**. The 1,247-qubit
alternative uses substantially fewer Toffolis (1,076,969 scored; score
1,342,980,343) and remains useful on the space/gate-count tradeoff frontier.

The timed research sweep started at **20:06:02 CEST** and remains active, with
deadline **2026-09-27 10:00 CEST**. At the 21:31 clock check it had completed
1,475 laboratory trials; **the requested ten hours have not yet elapsed**.
Results are recorded continuously in `overnight-qubit-sweep/trials.jsonl`
and `progress.json`. Executable upgrades retain the original start, counters,
and deadline.

## Verified result

The requested **1,250-qubit** threshold has been achieved by a changed quantum
circuit, not by reducing host memory or changing the scorer.

| Metric | Previous accepted circuit | Verified width-reduced circuit |
|---|---:|---:|
| Qubits | 1,251 | **1,250** |
| Average executed Toffoli | 897,596.816 | 1,041,080.804 |
| Scored integer Toffoli | 897,597 | 1,041,081 |
| Score | 1,122,893,847 | 1,301,351,250 |
| Accepted shots | 9,024 / 9,024 | 9,024 / 9,024 |
| Classical mismatches | 0 | 0 |
| Phase-garbage batches | 0 | 0 |
| Ancilla-garbage batches | 0 | 0 |

The width target takes priority in this iteration. Stronger precision and
space-saving arithmetic cost additional gates; this is **not** an improvement
in the Toffoli-by-qubit product.

Official verification used only `ecdsafail run`. Compressed `ops.bin` SHA-256:
`80cde1898f996527370bfacba1fe5f7efb2ef77c3b9bfd39887dcade30e0da8e`.
The accepted operations, score, and source snapshot are preserved in the local
session artifact folder as `verified-q1250.*` and `verified-q1250-source.tar.gz`.
The harness, dependencies, and fixed identity-tail nonce were not changed.

## Research and implementation

Primary sources checked:

- [Cuccaro, Draper, Kutin and Moulton, *A new quantum ripple-carry addition
  circuit*](https://arxiv.org/abs/quant-ph/0410184): in-place carry propagation
  with a single ancillary qubit rather than an entire stored carry ladder.
- [Gidney, *Halving the cost of quantum addition*](https://arxiv.org/abs/1709.06648):
  temporary logical ANDs and measurement-based uncomputation with the
  appropriate phase correction. Its T-gate estimates are not substituted for
  this harness's CCX/CCZ counts.

Applied changes:

1. **Budget-aware phase comparison.** When a stored borrow ladder does not fit,
   compute its carry through the complemented accumulator, apply its phase,
   and invert the MAJ chain. Operand-aliasing borrow predictors are copied
   safely. An already-measured output supplies clean scratch where available.
2. **Reuse the GCD loan in both halves.** The parked bit-1 wire was lent to the
   high chunk but not the low, vented chunk. Lending it to both nonoverlapping
   ladders fixes a real one-qubit overrun. For example, at live count 1,246,
   the old low chunk needed five additional wires although the high needed
   only four.
3. **Exact chunk workspace accounting.** Full and zero-extended additions now
   have an allocation-checked workspace model. A caller-owned clean wire can
   hold the first boundary; it is restored, not returned to the allocator.
4. **Budget-aware square windows.** Wide square folds use exact chunking when
   their full carry ladder exceeds the available workspace. This retains the
   arithmetic window rather than shortening it to hide the width overrun.
5. **Zero-workspace wrapped addition.** When even a compact chunk layout does
   not fit, the live incoming carry drives an in-place MAJ/UMA adder. Deferred
   carry-phase corrections remain attached to the same arithmetic predicate.
6. **Stronger precision.** Both walks now have 715 rounds, eight guard bits
   across the wide envelope, and a 13-bit physical tail from round 700.
   Replay and shell fold/comparison windows are also widened.

Small-width exhaustive simulator tests cover the new comparisons, source-bit
borrow aliases, phase cleanup, addition/subtraction, incoming/outgoing carries,
borrowed-wire restoration, zero workspace, and deferred carry phases.
Workspace predictions are checked against emitted wire IDs, not just formulas.

## Attempts and evidence

| Candidate | Width | Outcome |
|---|---:|---|
| Only reduce the old budget to 1,250 | 1,250 | Official failure: 13 classical mismatches, 9 phase-garbage batches |
| 714 rounds, four guard bits, wider windows | 1,258 | Census exposed square-window and GCD low-chunk overruns |
| Fit square windows and borrow compact boundaries | 1,251 | Census isolated the remaining low-chunk carry overrun |
| Share the low/high carry loan | 1,250 | Official failure: 3 classical mismatches, 1 phase-garbage batch |
| 715 rounds, eight guard bits, stronger windows and zero-workspace fallback | **1,250** | **Official 9,024-shot pass** |

The same predeclared, operation-stream-independent sample of 65,536 point
pairs was used for classical walk analysis. The 714-round candidate had 14
predicted walk failures; the 715-round candidate had zero. These are classical
walk-risk predicates, not full-circuit failure measurements. For zero out of
65,536, the reported Wilson 95% upper bound is approximately 0.00005861 per
point pair, or 0.5289 per 9,024-shot set. Zero observations do not prove zero
failure probability, and the inherited finite-round construction is not an
all-input correctness proof.

## Continued timed research

The user requested continued optimization for at least ten hours, with clock
checks. The accepted circuit is preserved while lower-width candidates are
studied separately.

`MEASURE_CONFIG` is **test-only**: its allowlisted numeric settings can change
the width, rounds, guard/tail profile, comparison windows, and source-sign loan
inside the laboratory executable. It cannot change a validation nonce.
Normal scored builds do not contain this override mechanism. With no research
settings, all 14,915,522 records were compared to the accepted artifact and
matched exactly.

The timed driver is a session artifact, `quantum_sweep.py`, not submission
code. It uses an immutable test-executable snapshot, compares configurations
on shared predeclared inputs, and escalates viable candidates through 64,
1,024, and 9,024 independent shots. It explicitly reads failure counts because
the existing measurement experiment is an estimator and can exit successfully
after observing circuit failures. Hourly fresh-input audits are reported
separately. Candidate errors and timeouts are recorded, not treated as success.

Research outputs are unscored suggestions only. The driver never edits
submission sources, `ops.bin`, `score.json`, or `results.tsv`. Any promoted
candidate still requires source integration and an official `ecdsafail run`.
The timed process must remain attached to an open CLI session; closing that
session can terminate it.

## Further reductions after the first verified result

### 1,249 qubits: eliminate a mandatory carry and genuine residual errors

When the live set fills the budget, `walk_add_single` now stores its bit-2
carry on its already-parked bit-1 target. The high add uses no extra workspace,
and the parked bit is reconstructed only after its carry is uncomputed.
This is exact under the same forward/reverse walk preconditions.

An independent 9,024-point audit found two division failures in the previously
accepted 1,250-qubit circuit. Stage and per-round diagnostics reproduced them
at retained-prebias rounds 123 and 351. Both differences began at the dropped
32-bit low-fold carry. Requesting an "exact retained" path previously still
fell back to a finite low cut when the exact retained frame did not fit.
The planner now falls back to the complete ordinary prebias fold instead.
Both division and multiplication exact-path policies have regressions.

A subsequent official failure was reproduced without changing its
Fiat-Shamir stream and attributed to a walk not converged after 715 rounds.
The accepted 1,249-qubit version uses 721 rounds and a budget-derived late
width taper. This remains a finite-round statistical construction, not a
universal inverse. The taper's live-word accounting and full-budget arithmetic
are tested explicitly.

The 1,249-qubit official result was 1,060,653 scored Toffolis and score
1,324,755,597, with zero failures. Its SHA-256 was
`f767b6fc413c8476975b8f91db3b5d1e51ba2557c656fe643d6a84e87221b16f`.

### 1,247 qubits: recycle selector workspace across two additions

Mapped arithmetic now accepts an exactly-zero incoming carry without
allocating a wire for it. Low-space replay division also uses the exact
composition adder rather than abandoning the prebiased representation.

For the halving correction, the identity
`J = (p XOR s)*(f-1)/2 + (2s-1)*q*f`, with
`q = p AND NOT(o XOR s)`, needs only one selector AND if the two constant
additions run sequentially. The multiply correction is even simpler:
`k*f = o*f + (-1)^s*d*f`; its sequential form needs no selector ancillas.
Both alternatives restore all controls and use exact phase repair.

The 1,247-qubit circuit passed the held-out 9,024-point sample and official
9,024-shot run. SHA-256:
`0ee46e2944b863cd0751a96c3ec86a66abe1c8251c8e1c8a45d3af5b8844ffbe`.

### 1,239 qubits: borrow the untouched high word

When a clean carry ladder cannot fit, the high bits outside a finite fold
window are available as **dirty workspace**. They may be in arbitrary,
entangled states and must be restored, not reset.

The first implementation used echoed multi-control ladders, but its gate
cost was excessive. The improved controlled increment uses the identity
`x - a - (~a) = x + 1 (mod 2^n)` with a borrowed dirty register. Appending the
control as the least significant bit makes the increment propagate into the
target exactly when that control is one; a final X restores the control.
Two exact in-place additions use one clean carry when available and exactly
**4n Toffolis per n-bit controlled increment**. Both the count and arbitrary
borrowed-state restoration have regressions. The zero-clean-workspace echo
remains a correct fallback, not the preferred path.

This follows the dirty-register approach discussed in
[Gidney, *Factoring with n+2 clean qubits and n-1 dirty qubits*,
arXiv:1706.07884](https://ar5iv.labs.arxiv.org/html/1706.07884).
The implementation and its resource counts are independently tested here;
paper T counts are not substituted for harness Toffolis.

The same lower-width work exposed an unbounded source-sign-loan branch in
the inverse GCD adder. It now checks its actual remaining ladder budget and
uses the zero-workspace alternative when needed.

The initial 1,239-qubit circuit passed official validation at 1,637,493 scored
Toffolis. Combining the dirty-register increment with the two-term corrections
reduced that to the latest **1,451,843**, without increasing width. All 65,536
classical walk sample pairs and all 9,024 held-out full-circuit samples
examined for this width had zero observed failures. These observations do
not prove an all-input guarantee.
