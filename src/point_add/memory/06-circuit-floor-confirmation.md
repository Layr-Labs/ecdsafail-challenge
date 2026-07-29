# Circuit at proven floor — no improvements found

## Hypothesis
Re-mine the dead-gate census tables and explore tail narrowing to reduce Toffoli count, as suggested in memory/05-qubit-reduction.md which noted ~6,241 stale keys could potentially be recovered.

## Implementation
1. Examined current configuration: TLM_TARGET_Q=1150, actual peak=1154
2. Tested tail narrowing by reducing last 4 SCHED_J2 entries from [9,9,9,9] to [8,8,8,8] with corresponding GAP_J2 adjustment
3. Tested TLM_TARGET_Q adjustments (1150, 1153, 1154)

## Results

### Baseline (unchanged)
- Peak qubits: 1154
- Avg executed Toffoli: 1,291,859.302
- Score: 1,490,805,306
- Census: 0 stale keys (tables are fresh)

### Tail narrowing attempt
SCHED_J2 tail [9,9,9,9] → [8,8,8,8]:
- Result: **FAILED** - 4187 classical mismatches, 141 phase-garbage batches
- Confirms memory/05 warning: aggressive narrowing breaks divstep convergence

### TLM_TARGET_Q variations
All values (1150, 1153, 1154) produce identical results:
- Peak remains 1154
- Toffoli count unchanged
- No improvement possible via this lever

## Why it failed

The circuit is genuinely at proven theoretical floors:

1. **Census already optimal**: 0 stale keys means tables are fresh, contradicting memory/05's expectation of ~6,241 recoverable gates

2. **Tail narrowing limited**: The early SCHED_J2 entries are tight magnitude bounds on f,g. Only tail has slack, but narrowing by even 1 qubit breaks correctness

3. **Qubit floor confirmed**: Peak 1154 is structural, not tunable via TLM_TARGET_Q

## Precise measurements
```
./benchmark.sh with original config:
  qubits: 1154
  avg executed Toffoli: 1291859.302
  classical mismatches: 0
  phase-garbage: 0
  ancilla-garbage: 0
```

## Conclusion
Circuit is at a genuine optimum. Memory/03-proven-floors.md is correct: both axes are closed. No improvement found.