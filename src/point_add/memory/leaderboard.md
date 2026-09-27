# Point-addition design leaderboard

Lower score is better: **scored average executed Toffoli × peak qubits**.
This file is a human-maintained record, not an input to circuit construction.
Do not edit the harness-owned `results.tsv` to update this table.

## Measured design iterations

The first row transcribes the inherited baseline; it was not rerun for this
research task. Reported 9024-shot success comes from the merged Quantum-Lead
decision; integer metrics and score were checked against `score.json`.

| ID / recorded date | Construction / rounds | Scored avg Toffoli | Peak qubits | Score | λ per 9024 shots / 95% CI | Validation failures / shots | Commit / artifact provenance | Grind trials |
|---|---|---:|---:|---:|---|---|---|---|
| 001 / 2026-09-25 | Inherited I10; affine two-pass ping-pong binary-GCD divider; 698 rounds/pass; replay modular updates; Karatsuba square | 897,597 | 1,251 | 1,122,893,847 | ≈16 **hypothesis, not measured**; CI unavailable | 0 / 9024 in the reported accepted-stream run; no fresh-seed measurement recorded | Inherited result label `cc7f10e`; local checkout HEAD `1097818d4b9ab7724d336b2027e4cd7861ec9496`, dirty; `score.json`; baseline op-stream hash not recorded here | Unknown; do not infer trial count from nonce value |
| 002 / 2026-09-26 | Width-priority circuit; 715 rounds/pass, stronger guards/windows, borrowed carry ladders and low-workspace exact arithmetic | 1,041,081 | **1,250** | 1,301,351,250 | Not measured for the full circuit; independent classical walk predicates 0 / 65,536 | **0 / 9024**, official `ecdsafail run` | HEAD `1097818d4b9ab7724d336b2027e4cd7861ec9496`, dirty; compressed ops SHA-256 `80cde1898f996527370bfacba1fe5f7efb2ef77c3b9bfd39887dcade30e0da8e`; source/artifact snapshots in session files | No nonce search; unchanged inherited nonce |
| 003 / 2026-09-26 | 721-round fitted tail, full-budget carry reuse, exact-fold fallback | 1,060,653 | 1,249 | 1,324,755,597 | Not established | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `f767b6fc413c8476975b8f91db3b5d1e51ba2557c656fe643d6a84e87221b16f`; preserved source/artifacts | None |
| 004 / 2026-09-26 | Sequential selector-free multiply fold and one-selector prebias fold | 1,076,969 | 1,247 | 1,342,980,343 | 0 / 9024 on one independent held-out full-circuit sample; not a zero-error proof | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `0ee46e2944b863cd0751a96c3ec86a66abe1c8251c8e1c8a45d3af5b8844ffbe`; preserved source/artifacts | None |
| 005 / 2026-09-26 | Dirty high-word borrowing, linear-cost controlled increments, two-term folds | 1,451,843 | **1,239** | 1,798,833,477 | Not established for final artifact; prior 1,239-qubit variant passed one independent 9024-shot sample | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `3590f1bc07a3d2494b79b44ac5758dc47e69c11edd60d68cb6847295b97a82a6`; preserved source/artifacts | None |
| 006 / 2026-09-26 | 720 rounds; child-cross zero loans and bounded boot doubling | 1,486,225 | **1,238** | 1,839,946,550 | Not measured for this artifact | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `aa9338c2efc9cd7a7de53ce622f5e8b4610b8dec7ee4c52c8e161c105a89b5d6`; preserved source/artifacts | None |
| 007 / 2026-09-26 | Signed-digit controlled constants at the same width | 1,361,538 | 1,238 | 1,685,584,044 | Not measured for this artifact | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `0eebb3d4e39ae3f0575e4defea6d1e511042e77556c1b3751b9f93a3510be477`; preserved source/artifacts | None |
| 008 / 2026-09-26 | 719 rounds; shared budgeted forward/inverse boot constants; eight guard bits | 1,375,225 | **1,237** | 1,701,153,325 | Not measured for this artifact | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `ef900f122e0554ef9888423785fbbec973aa764476fb3102c4c855cc39c4f4d2`; preserved source/artifacts | None |
| 009 / 2026-09-26 | Timed-sweep candidate; 718 rounds, eight guard bits | 1,385,910 | **1,236** | 1,712,984,760 | 0 failures on each of two predeclared 9024-point laboratory samples; finite-sampling limit applies | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `18b416fcee27a07ecb37d84aa6a899e7767076b90ebbda54e4bf834019aa7a1c`; preserved source/artifacts | None |
| 010 / 2026-09-26 | 717 native rounds plus 6 exact tape-free rounds, snapshot width 5 | 1,427,193 | **1,235** | 1,762,583,355 | Fixed the prior failing 9024-point input set; separate 9024-point sample passed | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `29ed8861a49500d741d6c1e38b77d19bfcc4360bfa2bbe8859855950e3194ba1`; preserved source/artifacts | None |
| 011 / 2026-09-27 | 708 native rounds plus 12 exact tape-free rounds, snapshot width 7 | 1,600,030 | **1,230** | 1,968,036,900 | Two predeclared 9024-point samples passed; prefix risk remains | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `18f00a964a953ffae929206877a028db5ec78f0c079512647643904cfc9b52d2`; preserved source/artifacts | None |
| 012 / 2026-09-27 | 707 native + 12 exact rounds; eight-bit guards; lower-cost field windows | 1,501,372 | **1,229** | 1,845,186,188 | Two 9024-point samples and separate 4096-point audit passed; finite-prefix/window risk remains | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `5431064963e2dda598281acda384a2032d3053c7433c5be7d204166478fa77a2`; preserved source/artifacts | None |
| 013 / 2026-09-27 | 706 native + 17 exact rounds; exact sign-two retirement; stronger snapshot | 1,784,662 | **1,229** | 2,193,349,598 | Original saved regression and independent9024-point sample pass; newer prefix-failure cohort remains a limitation | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `fbd63e84fc4342485145ee61fe99b24371f37aece40f5fae25ecc46b650c9dd1`; preserved source/artifacts | None |
| 014 / 2026-09-27 | 705 native + 17 exact rounds; sign-two retirement and polarity-optimized exact oracles | 1,777,434 | **1,228** | 2,182,688,952 | Saved known-regression set passes; finite-prefix/window limitations remain | 0 / 9024 official | Dirty HEAD as above; ops SHA-256 `124335a92d712dd5d271b74adfbc14f8c4948a918e56bcc9e367efc2ef0d7b0e`; preserved source/artifacts | None |
| 015 / 2026-09-27 | Score objective: separate precision/carry budgets; delayed coefficient allocation; 715 + 6 rounds | 1,019,407 | 1,250 | 1,274,258,750 | 4 union failures / 131072 independent points, including 3 phase failures; no ancilla failures | 0 / 9024 official | Ops SHA-256 `83c9918f2a526c265bc9357984d5a29ee80761fe0ddb23b8550c4a2f1296199a`; `verified-tq-first` operation/score artifacts | None |
| 016 / 2026-09-27 | Wider 717 + 6 prefix; shared exact Boolean products; precision footprint 1235, carry budget 1250 | 1,023,762 | 1,250 | 1,279,702,500 | 4 union failures / 131072 matched independent points, including 3 phase failures; no ancilla failures | 0 / 9024 official | Ops SHA-256 `3a0809222fd275b8f39001b681c86a779e3fd38f97529eba7cc9c3c0908c6dde`; `verified-tq-717` source/operation/score artifacts | None |
| 017 / 2026-09-27 | Same 717 + 6 precision envelope; multiply head moved to 208 | 1,022,301 | 1,250 | 1,277,876,250 | Independent9024 and saved regression pass; 4 union failures/131072 matched points, including3 phase failures; zero ancilla failures | 0 / 9024 official | Ops SHA-256 `26f4e8c61545fa1a09f6561ea82511c30ed235f8135c23a8fe0139db0cf1193d`; `verified-tq-head208` source/operation/score artifacts | None |

Rows 015-017 answer the user's later **T x Q** objective under the original
1,250-qubit limit. Row 017 is the current working score candidate and reduces
the product by approximately 41.5% from row 014. The lower-width frontier remains preserved.

Row 017 was reconfirmed after the extended research run completed at noon:
all 9,024 official shots passed again, with the identical score and operation
artifact. The broader independent-audit failures remain documented; this is
not a claim of all-input correctness.

Row 012 is retained as history, not the current recommendation: it reintroduced
the saved regression on a different input stream. Row 013 preserves that
specific fix; neither row is a universal correctness proof.

Row 014's independent 131,072-point audit observed **4 classical failures**,
including **1 phase failure**, and zero ancilla failures. Union
lambda9024 is **0.2754**, Wilson 95% interval **0.1071-0.7081**.
All four cases coincide with native-prefix width / signed-rail misses.

Row 002 meets the requested qubit threshold at a higher Toffoli cost and score.
Research, failed attempts, exact workspace changes, and validation limits:
[qubit-reduction.md](qubit-reduction.md).

Rows 003-005 continue reducing width rather than claiming a lower total score.
The later independent audit of row 002 found 2 classical failures (one with
phase garbage) in 9,024 samples; the exact-fold fallback addresses their
reproduced root cause. Its official accepted-stream result remains historical.

A later independent full-circuit audit of row 005 observed **1 / 65,536**
classical failures, zero phase/ancilla failures: lambda9024 **0.1377**,
Wilson 95% interval **0.0243-0.7800**. Its ideal multiply walk required
737 rounds and missed an earlier rail. Row 006 is not asserted to remove
that finite-walk risk.

The plan also reports an unrounded average of **897,596.816**. The displayed
score above is exactly `897597 × 1251`; use the scorer's integer value for
leaderboard arithmetic, and retain raw averages separately when available.
The owner's acceptance of the current statistical-correctness regime is settled.
Marking λ as unmeasured records evidence quality; it does not reopen that decision.

### Revalidation - 2026-09-26

`ecdsafail run` independently revalidated the same circuit on all 9,024 shots,
with zero classical mismatches, phase-garbage batches, or ancilla-garbage
batches. Score remains **1,122,893,847**. The compressed `ops.bin` SHA-256 is
`ca4fe4f256730bb795fde3c20f761cf551460fdab7f4e304dcfdadd1c4bddb7f`.

The construction algorithm now uses less host time and memory, but emits the
identical operation stream. This is therefore a revalidation of row 001, not
a new scored design or fresh-input failure-rate estimate. Measurements and
implementation details are in [optimization-progress.md](optimization-progress.md).

## Convention for subsequent rows

1. **One row per built design/artifact.** Record a short construction name,
   round/width policy and any changed approximations. Assign the next ID;
   preserve prior rows rather than overwriting the incumbent.
2. **Use measured units.** Toffoli means average *executed* CCX+CCZ, including
   effects of classical conditions, not emitted gates, T gates, or a full ECDLP.
   Q is the harness-reported peak, not average width. Copy the official score
   and check its product against the recorded scored metrics.
3. **Preserve provenance.** Include commit plus dirty status (or diff identity),
   op-stream hash, measurement date and location of the result artifact.
   A commit alone is insufficient for a dirty circuit. For the inherited row,
   missing provenance is explicit rather than reconstructed.
4. **Separate validation from failure-rate measurement.** Record unique failing
   shots `F` and total independent sampled shots `N` for an external fresh-input
   measurement, then `λ̂ = 9024 × F/N`. Report a named 95% binomial confidence
   interval for `F/N`, scaled by 9024; if sampling is clustered, document the
   clustering and use a suitable interval instead. `0/N` is not proof of λ=0.
   Distinguish classical/phase/ancilla failures, without double-counting a shot.
   A successful accepted-stream run is not a fresh-input rate measurement.
5. **Compare like reliability regimes.** Keep the accepted regime fixed unless
   the owner changes it. Use predeclared independent sample sets for candidate
   comparisons, with matched samples where practical. Record uncertainty or
   “not measured”; never silently treat missing λ as zero. A lower score with
   a changed/unknown error profile is a trade-off, not an established
   same-budget improvement.
6. **Keep grind provenance descriptive.** Record trial counts only if measured;
   otherwise write “unknown”. A nonce value is not evidence of sequential trial
   count. This convention does not prescribe new grinding.
7. **Keep hypotheses out of the measured leaderboard.** Literature results and
   paper-based extrapolations belong in research notes, not measured iteration
   rows. If an experiment is incomplete, explicitly label its state and do not
   call it the new verified incumbent. Circuit evaluation remains the designated
   engineer/lead's task.

For a candidate `(T,Q)`, improvement relative to row 001 is
`1 − (T×Q)/1,122,893,847`. The baseline marginal exchange rate is approximately
**717.50 Toffolis per qubit**, but use the exact product for finite changes.

Literature and candidate rationale:
`.squad/decisions/inbox/scientist-research-findings.md` (or its subsequently
merged entry in `.squad/decisions.md`).
