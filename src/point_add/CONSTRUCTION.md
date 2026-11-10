# Rebuild the Q651 cached-product circuit

This circuit adds a classical offset to a quantum point on secp256k1. It descends from jackylee0424's Q651 upper Euclidean construction, the Q651 arithmetic and gate reductions in b573fae1 and d04ea485, and the upper compiler in 76c5c6cc. The immediate parent is nasqret's parity-fusion submission bf0d45f0 in PR 2627 at commit 6541ab74d3a5dd2bd817c05e40d97dc408b2d361. Its bounded reversible compiler propagates a target XOR difference between two Toffolis sharing the same controls.

This revision caches a repeated Boolean product on one temporarily available qubit. It groups Toffoli gates that read the same two control wires without an intervening write to either. The chosen qubit is either clean already or can be cleared by XORing a known duplicate or complement. Its original value and donor are tracked until the end of the group. A cached product fans out to the original targets through CNOTs. At its final use an X-basis measurement erases the product, and a CZ on its two still-available controls removes the phase when the measurement outcome is one. The donor-restoration gates then restore borrowed storage. The same phase identity permits elimination of a standalone Toffoli whose target already equals its control product.

The compiler keeps per-wire Boolean expressions for these equality checks and discards facts conservatively when the expression table fills. A 256-gate window supplies future-read and future-write bounds for the loan search. Every condition scope is flushed before entry and exit. Eligibility inside a classically controlled scope is computed from conservative branch-local wire values. The emitted measurement, its feedback and reset follow the active condition. All additional measurements reuse one classical bit. Native forward and reverse checks include quantum and classical outputs, ancillary cleanup and measurement phase.

Run from the construction directory on a little-endian host with Node 24. The top-level TRACE-SHA256 identifies the raw stream and span table. The Rust entrypoint emits the ordinary stock circuit operations.

```sh
node q651/point.cjs raw trace.u16le
node q651/point.cjs spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
```
