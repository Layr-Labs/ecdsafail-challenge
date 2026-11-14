# In-place secp256k1 point addition on 648 qubits

The circuit adds a public point to a quantum point. The two output coordinates share the original 512 input wires. The upper Euclidean word occupies q513 through q640. The field helpers occupy q512 and q641 through q646. The orientation uses q647. The construction starts from RealAdii's public Q648 layout and the preceding Q648 arithmetic refinement. [Public donor](https://github.com/Layr-Labs/ecdsafail-challenge/tree/c538abfa9b42aa0445a1de8e049558438da7617b/src/point_add)

## Field arithmetic

The divider, multiplication and history routines partition normalization shifts into disjoint sectors. Each sector borrows only low divisor bits that are provably zero. The last sector covers the remaining legal shifts in one interval. Matched divisor rotations agree on idle branches, so they need fewer quantum controls. The short multiplier uses the same selected family. The routines restore borrowed wires before leaving the stage. The implementation is in `construction/research/q648-next/field/tail.cjs`.

## Upper Euclidean rows

The general quotient rows fuse field reflection with decrement and reuse a released sign flag for restoring-digit carries. The unit rows use the determinant identity p = Hv + Ru and the gap between the cases H above or below 2R. Splitting the low part of R at half the row height bounds the discarded term strictly below the gap. The carry can therefore be decided by shorter mixed products. This variant divides the low quotient into multiple blocks, each with an explicit bound on its discarded product. The outer divider also borrows unused, zero coefficient wires during its matched normalization walk. Both source transformations reside under `construction/research/q648-next/`.

## Gate compilation

The Rust builder expands the schedule to its original gate records, applies the branch-aware product optimizer and combines eligible pairs through unconditional X and CNOT operations. Conjugation represents the first Toffoli as an update along one binary vector by a product of two affine forms. When the control planes coincide, their nonlinear part can be distributed across both destinations with one Toffoli. When the destination is shared and the control planes intersect, their sum factors into one product plus a linear correction. Reversible CNOTs compute and restore the control parities. Measurements, phase gates, classical guards and conditional boundaries close the local rewrite window.

The stock builder produces the operation count in `optimized_count.rs`. The adjacent `selection.json` binds the construction and selected operation stream to cryptographic digests. Static Toffoli count bounds the cost of every path. The stock evaluator measures the executed mean across 9,024 shots.

To regenerate the native records in the construction directory, run the frozen generator with Node.js 22.15.0. The stock Rust builder applies the two optimization passes to these records.

```sh
sha256sum --quiet -c SOURCE-SHA256
env -u FIELD_VARIANT -u UPPER_VARIANT node -r ./research/q648-next/winding.cjs research/q648-trim/circuit.cjs stream native.json ranges.tsv | zstd -q -o native.zst
```

The general restoring trials accumulate a virtual high output bit as a difference on a borrowed wire and restore that wire after testing the rank predicate. The coefficient path fuses a pre-addition with the final correction where its prerequisites hold.

In the short divider, the four-bit odd-quotient function is expressed in algebraic normal form. A dirty borrowed bit carries the common predicate through two applications of the small Boolean function and is restored.
