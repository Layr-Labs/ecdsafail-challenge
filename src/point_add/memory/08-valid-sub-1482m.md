# 08 — Task 8 score/lambda decision gate

## Verdict

**NO-GO for Task 9.** The exact composed ITERS=258 candidate fails both mandatory gates. Per Task 8 Step 5 item 4, do not launch a long tail-nonce search and do not report a failing low score.

## Exact ITERS=258 composed stream

Production defaults: ITERS=258, Task 6 baked K3-shift precision, Task 7 stable-ancestry strip (6,633 dead + 1,255 downgrade), tail nonce zero for measurement.

Command:

```bash
TLM_GRIND=1 TLM_GRIND_MODE=lambda TLM_GRIND_NONCES=500 \
  TLM_GRIND_BATCHES=141 TLM_GRIND_THREADS=10 TLM_GRIND_START=0 \
  SUB4_TAIL_NONCE=0 target/release/build_circuit
```

Artifact: `artifacts/task8/lambda-500.log`

- 500 nonces, 70,500 batches, 4,512,000 shots, 514.0 s
- ops: 9,315,175; qubits: 1,155; bits: 538,830
- clean batches: 63,605 / 70,500 (`p_clean=0.90219858`)
- union lambda: **14.51**; Wilson 95% interval **[14.17, 14.86]**
- average executed Toffoli: **1,320,008.218**; rounded 1,320,008
- projected score: **1,524,609,240**, exceeding 1,482,000,000 by 42,609,240
- no clean nonce found

Trusted 9,024-shot evaluation is INVALID: 7 classical mismatches, 7 phase-garbage batches, 0 ancilla-garbage batches. `score.json` is absent; the FAIL rows in `results.tsv` are not valid scores.

## Task 7 strip A/B

Identical 40-nonce x 141-batch probes:

- strip OFF: avg Toffoli 1,327,584.813; lambda 13.94
- strip ON: avg Toffoli 1,320,009.052; lambda 14.00
- strip value: 7,575.761 average executed Toffoli/shot
- strip-induced lambda: +0.06, within the <=2.0 strip-local limit

Artifacts: `artifacts/task7/step8-grind-off/`, `artifacts/task7/step8-grind-on/`.

## Fixed-order fallback checks

1. Removing translated strip keys is inapplicable: score has no margin and removing savings worsens score.
2. Narrowing ITERS=258 precision is inapplicable: lambda has no margin (95% lower estimate is above 14).
3. ITERS=259 was tested before paying for certificate retranslation:
   - baked precision, strip OFF, 40x141: lambda 8.98, avg Toffoli 1,330,824.130, 1,155 qubits, projected score 1,537,101,720 (fails score by 55,101,720).
   - precision completely OFF, strip OFF, 40x141: lambda 20.87, avg Toffoli 1,297,856.286, 1,154 qubits. It fails both gates; narrowing recovered cost only by destroying lambda margin.
   - artifacts: `artifacts/task8/iters259-probe/` and `artifacts/task8/iters259-raw-probe/`.

The temporary ITERS=259 edits were restored byte-for-byte to the ITERS=258 snapshot (`schedule.rs` SHA-256 `954ba46dcd90883609dd267d7c7e3553c4d0a35e7bb8a764e63de5485e4294af`) and the release binary was rebuilt.

## Consequence

Task 9's interface requires a stream that passed Task 8. This stream did not, so nonce grinding/baking is blocked. Task 10's trusted final-valid completion criteria cannot be claimed on this candidate.
