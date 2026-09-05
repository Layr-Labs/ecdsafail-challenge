# Q813 repaired Aux1 candidate primitive stream

These 36 contiguous shards are the fixed-point-reduced primitive stream for all
1,616 steps of the repaired one-clean-auxiliary paper2607 schedule. Each
sidecar records its compressed hash, raw-record hash, primitive histogram, and
per-step totals. `aggregate.json`, `aggregate_manifest.json`,
`reduction_manifest.json`, and `SHA256SUMS` bind the traversal and reduction
receipts.

The candidate descends from the fully trusted repaired Q814 source. It retains
Q814's exact phase-B sentinel repair. Two earlier Q813 builds were falsified by
the full trusted replay with 9,024 classical mismatches and 141 phase-garbage
batches: first a direct `Iter` carry loan, then the false assumption that
`Iter` matched the terminal `l_rp` sentinel. Exact classical trajectories locate
the first counterexample at schedule step 3, where live phase B has `Iter=1`.

The repaired R block instead uses the proved live transformed quotient-boundary
domain 3..258. It folds 256..258 onto unused codes 0..2, stores `Iter` in the
freed ninth quotient bit, clears the R carry, and decodes the low quotient byte
modulo 256. Conservative arithmetic-envelope labels 2 and 259 are retained as
cells but excluded from quotient equality. The encoding is reversed inside R,
so every external register is restored exactly. The exhaustive codec
differential covered every boundary/mode pair and both `Iter` values on 3,723
trusted-clean-carry cases, and reachable full-step comparisons passed against
Q814 from schedule steps 1 through 1,616. Both falsified streams remain negative
regression artifacts and are not part of this stream.

The remaining one-clean reductions use direct nine-bit quotient decoding,
one-clean modulo-259 scans, raw T-sub control synthesis, and two-lane terminal
length maps. The terminal maps use an eight-raw-control decoder: it was checked
against Q814 for every certified live boundary value in six representative
windows, and for all 512 physical endpoint codes with the terminal control off.
Each reduced block passed forward and inverse differential checks against
repaired Q814 before stream generation.

The source was generated from
`paper2607_data/eea_circuit_s835_exactwidth_dirty12.py`, reduced by the frozen
fixed-point reducer, and checked by `paper2607_data/verify_q813_stream.py`. The
embedded local layout has width 567: a 557-qubit persistent EEA core plus ten
restored dirty references supplied by the surrounding point-add circuit. With
the external point lane, the expected challenge peak is 813 qubits.

The reduced stream contains 316,231,401 records and operations per traversal.
Its primitive histogram is 14,145,878 X, 12,243,674 CX, and 289,841,849 CCX.
Four EEA traversals contribute 1,264,925,604 emitted operations and
1,159,367,396 executed Toffolis before the unchanged surrounding point-add
operations. The integrated guards expect 1,289,453,386 whole-circuit emitted
operations and 1,170,012,987 structural Toffolis.

This checkpoint is not submission-authorized until the integrated Rust build,
trusted replay over all 9,024 challenge shots with `0/0/0`, and official
`ecdsafail run` all pass on the exact frozen source.

Model attribution: GPT-5.6 Codex.
