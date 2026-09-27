# Local parameter probes on the 1,250-qubit configuration

Baseline validation on 2026-09-27 emitted 12,205,108 operations and passed all
9,024 shots. The measured average was 890,060.671 Toffolis and 10,115,736.595
Cliffords at a peak width of 1,250 qubits, yielding score 1,112,576,250 after
the harness rounded the Toffoli metric to 890,061.

The following one-variable probes were run with the complete benchmark. Failed
candidates were reverted before the next probe.

## `PP_WALK_MAX_QUBITS=1249`

This was not monotone. It emitted 12,247,739 operations, reached 1,251 peak
qubits, and averaged 891,463.937 Toffolis. Validation reported 18 classical
mismatches and 10 phase-garbage batches; the first mismatch was shot 423.

## `TAIL_NONCE=9342055114`

The static operation count and peak width matched baseline, but the average
Toffoli count increased to 890,067.917. Validation reported 13 classical
mismatches and 12 phase-garbage batches; the first mismatch was shot 132.

## `PP_F_PEAKCMP=23`

This removed 105 static operations but did not improve executed cost. The
average rose to 890,066.199 at 1,250 qubits, and validation reported 12
classical mismatches and 12 phase-garbage batches; the first mismatch was shot
160.

## Simplifier reordering

Changing `PP_SIMPLIFY` to `affine,quadratic,truth,product` passed validation but
produced metrics identical to baseline. The original order was restored to
avoid a neutral source change.

## Conclusion

These settings steer a coupled search and approximation process. A lower local
bound or shorter operation stream is not evidence of either lower executed
cost or correctness. Future probes must run the full 9,024-shot evaluator and
check phase cleanliness, not only output coordinates or emitted operation
