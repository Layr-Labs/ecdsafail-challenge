# Toffoli-by-qubit optimization - 2026-09-27

## Completed at noon

The extended worker finished at **2026-09-27 12:00:26 CEST**, after **15.8066
active hours** across the combined width/score research. Its journal contains
10,943 experiment/audit records, including 656 score-focused records covering
488 distinct configuration/executable pairs. These are measurements, not
claims that every candidate is correct.

After completion, a final `ecdsafail run` reconfirmed the working circuit:
**1,022,301 scored Toffolis x 1,250 qubits = 1,277,876,250**, all **9,024**
official shots accepted, zero classical/phase/ancilla failures, and the same
compressed artifact hash recorded below. The current regression suite passes
70 tests; 8 laboratory experiments remain explicitly ignored by default.
The protected harness and dependency manifests are unchanged.

## Objective and verified progress

The user switched the objective to improving **T x Q**, while retaining the
original limit of **1,250 qubits or fewer**, and extended the run to
**12:00 CEST**. The lower-width incumbents remain preserved.

| Circuit | Scored Toffoli | Qubits | Score | Official result |
|---|---:|---:|---:|---|
| Starting width-optimized incumbent | 1,777,434 | 1,228 | 2,182,688,952 | 9,024 / 9,024 |
| First score-focused candidate | 1,019,407 | 1,250 | 1,274,258,750 | 9,024 / 9,024 |
| Longer-prefix candidate | 1,023,762 | 1,250 | 1,279,702,500 | 9,024 / 9,024 |
| Current refined replay-head schedule | 1,022,301 | 1,250 | 1,277,876,250 | 9,024 / 9,024 |

The current source therefore uses approximately **42.5% fewer Toffolis** and has a **41.5%
lower product** than the starting width-optimized incumbent. This spends 22
additional qubits, still within the requested threshold. It is not a claim
to beat the historical, less-conservative 1,122,893,847-score circuit.

Current verified artifact SHA-256:
`26f4e8c61545fa1a09f6561ea82511c30ed235f8135c23a8fe0139db0cf1193d`.
The `verified-tq-head208*` session artifacts preserve the source, operations, and
score. Only `ecdsafail run` is used for official verification.

## Why these changes help

The starting circuit spent approximately **72.35% of executed Toffolis in
modular field replay**, versus 24.92% in the forward/inverse GCD walks and
2.63% in squaring. Optimizing small square details alone cannot deliver a
large product improvement.

### Separate precision storage from arithmetic workspace

`PP_WALK_TAIL_CAP` pins the numerical GCD envelope independently of the
hardware cap. Zero retains the old behavior. Extra hardware can therefore
fund exact carry ladders instead of forcing repeated dirty-register constant
increments, without automatically changing the integer snapshot.

The first isolated 64-point probe kept the old walk envelope and lowered
Toffolis from approximately 1.78 million to 1.31 million at 1,250 qubits.
Further qualified candidates restore delayed coefficient allocation
(`PP_RECOMPUTE_SIGN2=0`) and use smaller exact-tail snapshots. The current
candidate has 717 native rounds, a six-round exact continuation, eight guard
bits, precision footprint 1,235, and hardware cap 1,250. This schedule differs
from the starting incumbent and is validated separately.

### Share exact Boolean products

Compact-tail polynomials now share common control products while clean
workspace is available. Each shared AND is measured out with its exact phase
correction before the field replay, so its workspace can be reused. The
dirty-ancilla implementation remains the fallback when no clean space fits.

For example, `ab XOR abc XOR abd` falls from nine Toffolis to three using
one temporary qubit, returned clean. Tests cover all three-variable Boolean
functions, both full and empty workspace budgets, and the complete compact
snapshot state spaces. Polarity selection uses conservative dirty-workspace
costs; final emitted costs are measured, not inferred from that bound.

### Retain only profitable exact carry frames

The exact retained-fold planners now reject a nonpositive final modeled
saving, including the extra prefix-uncomputation cost. Research settings
can vary the allowed retained prefix and the replay head boundaries without
changing production behavior by default. Small probes of head timing and
larger retained prefixes offered only modest gains; they are not blindly
promoted. Keeping the 717-round precision envelope and moving the multiply
head boundary from 403 to 208 passed both the independent 9,024-point sample
and the saved regression set before official promotion. It saves another
1,461 scored Toffolis without changing the numerical walk widths.

## Correctness and limits

Both official score-focused results above passed all 9,024 shots, with zero
classical mismatches, phase-garbage batches, or ancilla-garbage batches.
The shared-product candidate also passed the saved known-regression set.
The harness, dependencies, and identity-tail nonce are unchanged.

All three score-focused variants above were evaluated on the **same
131,072-point independent sample** as the old width incumbent. Each had four
classical/union failures. Each score candidate had three phase failures,
all in those failing cases, versus one
previously. The union estimate remains
`lambda9024 = 0.2754`, Wilson 95% interval `0.1071-0.7081`. These are finite
prefix/window circuits, not universally correct point-addition constructions.

A cheaper 713-round candidate passed laboratory samples but failed three
official shots. The same three input pairs also fail in the old incumbent;
diagnostics identify native-prefix width/rail misses. It was not promoted.
A wider-guard experiment delayed those misses but did not eliminate them.
The current verified source uses a longer, wider prefix instead of changing
the validation nonce.

The failed 713-round laboratory candidate was matched byte-for-byte against
all 14,320,585 records of its rejected official artifact. It is explicitly
blocked for that laboratory executable. On resume, the worker recovers the
next fully validated candidate instead of allowing an officially rejected
but cheap estimate to dominate all subsequent research.

A second 713-round variant with a larger exact-retention allowance failed
one official shot (including phase garbage). Its 14,314,226 records were
matched to the laboratory candidate and it was likewise excluded. Neither
failed experiment was left as the submission: the 717-round source was
restored, `ecdsafail run` passed all 9,024 shots again, and its compressed
artifact matched the previously accepted SHA-256 exactly.

## Research record

The score-first worker retained the original start and ran through the
requested **2026-09-27 12:00 CEST** deadline. It ranked by measured T x Q under
the 1,250-qubit limit, then checked independent samples, saved regressions,
periodic audits, and official-failure feedback. Lower estimated scores that
failed qualification were not left as the submission. Laboratory suggestions
remain distinct from officially accepted results.
