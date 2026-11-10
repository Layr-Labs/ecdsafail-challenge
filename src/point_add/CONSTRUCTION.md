# Rebuild the Q651 GCD rotation circuit

This is reversible secp256k1 point addition with a quantum point and a classical offset. Its immediate parent is nasqret's Q651 cached-product submission 1af84e41-574b-4a0c-b816-477993cc7f4a in PR 2629, commit d262ad558fab66ce966f75d05b97b376c472bcbb. That source includes the earlier arithmetic from jackylee0424 and nasqret, and the physical-gate parity and cache compilers. The current generator factors repeated controls at the arithmetic level before those inherited passes.

For an arbitrary dirty word d and an n-bit destination x, perform x += d. Under the desired enable predicate, complement both words. Subtract the current d from x and complement both words again under the same predicate. When the predicate is zero, the arithmetic operations cancel. When it is one, writing bitwise complement as -1-x modulo 2^n shows that the final word is x-1, while d is restored. Reversing the list gives x+1. The two large adders are unconditional. A set of target flips with the same predicate can use one target as an XOR pivot and compute the predicate only once.

A conditional adder tail temporarily masks each low target b_i by d(1 xor a_i), with d an unknown borrowed bit. The carry operation controlled by a_i and b_i then sees exactly its unmasked Boolean product. The updated targets depend on the required common predicate, and the added CNOTs and paired predicate toggles restore the donor. The construction also supports a controlled fixed permutation by factoring each cycle into two reflections and reusing one dirty selector. All steps are expressed in ordinary reversible operations. No new quantum or classical wire is required compared with the direct parent.

From the construction directory use Node 24 on a little-endian host. The top-level TRACE-SHA256 identifies the raw stream and span table. The Rust decoder expands the packed circuit into conventional operations.

```sh
node q651/point.cjs raw trace.u16le
node q651/point.cjs spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
```

The immediate arithmetic predecessor is the controlled-increment Q651 schedule with raw SHA-256 a43cc9489cdbd7412b50ace3193c9180f58ff8552ae63538cdf2119da69b15ea. This revision applies the two-involution control factorization to fixed rotations in the lower Euclidean kernels as well. Their local emitter reserves the first available disjoint dirty word sites, synthesizes the joint control into one borrowed bit, and restores every donor. One-pass gate emission uses the native canonical NCT operand order.
