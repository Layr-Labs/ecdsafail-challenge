# Q814 repaired Aux2 certified primitive stream

These 36 contiguous shards are the fixed-point-reduced primitive stream for all
1,616 steps of the repaired two-clean-auxiliary paper2607 schedule.  Each
sidecar records its compressed hash, raw-record hash, primitive histogram, and
per-step totals.  `aggregate.json`, `aggregate_manifest.json`,
`reduction_manifest.json`, and `SHA256SUMS` bind the traversal and reduction
receipts.

The candidate descends from trusted Q815.  Its compact R step temporarily stores
the complete original Phase2 bit in `Mode`, clears Phase2 for use as the equality
accumulator, compensates the affine high source, and conditionally restores the
swapped 255/511 sentinel.  This handles the reachable phase-B endpoint with
physical `l_q=511` that falsified the first Q814 attempt.  The second scan keeps
the trusted implicit `NOT(Mode & Sign)` primitives; no lossy selector conversion
is used.

The source was generated from
`paper2607_data/eea_circuit_s835_exactwidth_dirty12.py`, reduced by the Q814
fixed-point reducer, and independently checked by
`paper2607_data/verify_q814_stream.py`.  The embedded local layout has width 568:
a 558-qubit persistent EEA core plus ten restored dirty references supplied by
the surrounding point-add circuit.  With the external point lane, the measured
challenge peak is 814 qubits.

The reduced stream contains 294,387,780 records per traversal.  It emits
294,407,124 operations and executes 267,801,634 Toffolis per traversal.  The
primitive histogram is 14,300,100 X, 12,292,494 CX, 267,788,738 CCX, and 6,448
clean-C3X MBU markers.  Four EEA traversals contribute 1,177,628,496 emitted
operations and 1,071,206,536 executed Toffolis before the unchanged surrounding
point-add operations.

The full trusted local replay loaded 1,202,156,283 operations, measured 814
qubits, and passed all 9,024 shots with zero classical mismatches, zero phase
garbage, and zero ancilla garbage.  The high Toffoli count is a deliberate width
trade for the qubit/custom leaderboard and the Q813-to-Q808 descent; it is not a
scalar-score improvement.

Model attribution: GPT-5.6 Codex.
