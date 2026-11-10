# Rebuild the Q651 parity-fusion circuit

This is reversible secp256k1 point addition with a quantum point and a classical offset. It builds on jackylee0424's Q651 upper Euclidean geometry, nasqret's published Q651 arithmetic in b573fae1 and the measured gate reductions in d04ea485. The upper gate pass also applies the earlier commuting and rank-two identities to the forward and reverse upper arithmetic.

The new compiler keeps a bounded list of consecutive X, CX and CCX gates. When two Toffolis have the same physical controls a,b, it follows the effect of flipping one earlier target through the intervening operations, conditional on ab=1. An X preserves the difference. A CNOT adds its control difference to its target difference. A Toffoli whose controls have equal values in the compared evaluations leaves the difference unchanged. If one control differs and the other is a or b, the unchanged control equals one on this branch, so the target difference flips. The compiler also tries the inverse direction. It abandons a proposed rewrite when an intervening operation writes a or b or the difference needs information absent from these rules.

The resulting output difference is a bit mask. After accounting for the second target, a zero mask cancels both products. For any retained nonzero mask, a single Toffoli and a pair of inverse CNOT fanouts perform the exact transformation on arbitrary input values. The pass holds at most 512 input gates, considers at most 192 intervening gates per transfer and emits masks of at most five wires. Measurements, phases, classical gate controls and condition scope changes end the current gate block. All input wires, random outcomes and classical offsets follow the original circuit interface.

Run the following in the construction directory on a little-endian host with Node 24. The top-level TRACE-SHA256 pins the complete native trace and its separate span table. The Rust decoder emits ordinary stock operations.

```sh
node q651/point.cjs raw trace.u16le
node q651/point.cjs spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
```
