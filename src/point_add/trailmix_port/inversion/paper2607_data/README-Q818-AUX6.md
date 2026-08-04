# Q818 Aux6 research candidate

This directory contains a six-clean-auxiliary continuation of the public Q819
paper2607 route.  The EEA stream references 572 local wires.  The surrounding
point-add circuit contributes a fixed 246-wire context.  The production Rust
count-only build measures the resulting peak at 818 qubits.

This is a reproducible, locally trusted research candidate, not yet an official
server result.  The full primitive stream is generated, certified, integrated,
and has passed the required 9,024-shot trusted replay.  The lowest official
measured public result at the time of this work was Q820; the public Q819
lineage passed a local trusted replay but its official uploads failed before
returning metrics.

## Structural changes

The candidate removes one clean lane from the Q819 generator by replacing the
remaining six-lane decoders with restored dirty-lender constructions:

- the live-R equality predicate borrows the ten dirty passengers;
- LC swap exposes the final three decoder levels as raw controls;
- T subtraction exposes the final six levels and restores five dirty lenders;
- midpoint T addition uses five-clean modulo-259 and upper-zero scans;
- terminal length repair exposes the final four levels and restores its eight
  dirty passengers;
- the terminal endpoint predicate temporarily borrows `Iter`, restoring its
  entry value before the iteration update.

Clean auxiliary elimination alone cannot reach sub-800: the fixed register
budget is 556 semantic/control wires plus ten dirty passengers, so the
zero-clean local floor is 566 and the corresponding point-add peak is Q812.
Going below Q800 therefore requires eliminating at least thirteen additional
semantic/context wires, not merely another auxiliary decoder rewrite.

## Current evidence

The differential verifier compares this generator with the clean public Q819
commit on bit-sliced basis states.  It covers the live predicate, terminal
endpoint, LC swap, T subtraction, midpoint T addition, terminal length repair,
and a complete step-1 caller.  It also checks clean scratch, restoration of
every arbitrary dirty lender, and exact inverse replay.

Current local results:

- 128 bit-sliced cases per representative component/window passed;
- 1,024 exhaustive live-predicate cases passed;
- 2,048 targeted/exhaustive terminal-endpoint cases passed;
- all 1,616 certified schedule rows constructed at local width 572;
- source SHA-256:
  `7650dae7b9ad14ffc3f674d60dfefd865365469b5dc12a69c7a94f10afc343dd`.

The certified serialized aggregate has SHA-256
`39989d3fa2fe8d30cd2b0bc4eea218eb2b0b5969a83fb2cdffab161d047895d3`.
Its exact stream totals are recorded alongside the recursive-definition count
in `q818_aux6_schedule_count.json`:

```text
records per traversal              289,538,524
emitted ops per traversal          289,557,916
executed Toffoli per traversal     255,886,404
four-traversal emitted ops       1,158,231,664
four-traversal executed Toffoli  1,023,545,616
```

The recursive counter is slightly higher because it expands each of the 6,464
clean-C3X markers into its definition.  The values above come from the
verified serialized stream and are authoritative for Rust integration.

The 36 certified shards are integrated into the production Rust backend.  An
independent production count-only build completes with the baked drift guards
enabled and reports:

```text
whole-circuit emitted ops       1,182,759,471
whole-circuit structural T      1,034,191,207
measured peak qubits                      818
peak phase                         ec3.inv_fwd
```

The exact primitive breakdown is recorded in
`q818_aux6_schedule_count.json`.  This build uses the production circuit path
and was subsequently confirmed by materializing and evaluating the complete
approximately 1.18-billion-element operation vector.

The official local benchmark command completed with score 845,968,407,326 and
the following trusted result:

```text
tested shots                         9,024
classical mismatches                     0
phase-garbage batches                    0
ancilla-garbage batches                  0
average executed Toffoli     1,034,191,207
average executed Clifford       58,328,088.918
qubits                                  818
```

This confirms the expected space/time trade: Q818 is structurally valid but
substantially heavier than Q819.  Its EEA stream alone is beyond the prior
Q819 whole-circuit operation envelope, so official server acceptance must not
be assumed from construction or differential checks.

## Reproduction

Use Qiskit 2.5.0 and the pinned Luo support checkout at commit
`ac1ecffee14b5a977421b75669c52db6b4033646`.  Set `PYTHONPATH` to the directory
containing `eea_circuit_updated.py`, then run:

```powershell
python verify_q818_aux6_reductions.py `
  --original <q819-commit>/eea_circuit_s835_exactwidth_dirty12.py `
  --candidate ./eea_circuit_s835_exactwidth_dirty12.py `
  --cases 128 `
  --construct-all
```

The remaining promotion gate is an official server upload.  Server acceptance
must still be treated separately from this successful local trusted run because
the Q819 lineage previously exhausted the official resource envelope before
returning metrics.

An official submission must carry this complete public record and must not be
described as server-measured unless the platform returns Q818 metrics.
