# Rebuild the Q650 hosted arithmetic

This circuit adds a classical secp256k1 offset to a quantum point. The direct width-650 parent is jackylee0424's submission 3389bfa0-f3bc-426b-92cd-810eef428672 in PR 2628 at commit 12359bfb7386a0d9c29d9aed441be8c67cdcb16d. That public construction used nasqret's b573fae1 as its immediate base. Its ancestry and attribution are retained under construction/donor. The mixed-radix walk generator there contains the restoring-digit change described below. The current point shell uses the parent's nine-helper stage maps. The final constructor is construction/q650/point.cjs. The earlier under-cap hosted Q650 construction was published in PR 2636, commit 82d6f060bb821166c61dd71f18d12f29caf575d5, with raw trace SHA-256 988126fb17284046fd8f55de970f81189bb5958292436183c0053859ea73f962.

In the upper sign probe, only ranks from zero through its row-specific maximum are ordinary. The exceptional all-ones rank can be identified by its leading prefix through the highest zero of the ordinary maximum. Conjugating the exceptional-code flip by a CNOT fanout implements the same transposition. A controlled fixed permutation is factored into two involutions on a borrowed selector. A conditional increment uses two unconditional additions and conditional complements of its destination and borrowed word. The common predicates in a descending ripple are similarly shared using a restored arbitrary bit.

The fused digit handles a normalized divisor with an implicit high one. A borrowed qubit accumulates the two carry contributions that would have been written into that constant site. Two controlled involutions on the high target bits remove its arbitrary incoming value. The common lower-digit predicate is carried through the falling ripple and all loans are restored. The actual occupied high divisor site is untouched.

In the short division, an additional normalization bit uses the test site during initial alignment and moves into the released low remainder after the first active digit. This preserves the outer walk's nonzero-remainder tests and terminal ordering. The inner canonical walk, the signed history walk, and the multiplier use the matching endpoint variant. Direct gates for the virtual high-one digit are used wherever this schedule requires it. A 128-bit stage binds its actual surviving logical sites by the original fixed width-650 maps.

Use Node 24 on a little-endian host. The following commands run from the construction directory. The top-level manifest pins both complete outputs. The Rust decoder emits ordinary stock operations from the independently checked schedule.

```sh
node q650/point.cjs raw trace.u16le
node q650/point.cjs spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
```

After the reversible arithmetic is scheduled, the physical field and upper streams use commuting cancellation and low-rank Boolean reductions. A parity-transfer pass combines recurring Toffolis through supported linear effects. A bounded product cache then reuses equal controls on a proven available quantum wire, erasing the product by X-basis measurement and a conditioned CZ. All added measurements use one reusable classical bit.

The inherited lower-field pass runs after commuting and affine reduction in the short multiply, short divide and signed history. It compares the output differences from recurring Toffolis with identical read-only controls. Their nonlinear product is one only when both controls are one. Across a CNOT the difference propagates as an XOR mask. A later Toffoli may be crossed when its other operand has known value one on this branch. If the two differences cancel, both prior products disappear. Otherwise a single Toffoli applies the difference with CNOT fanout and reversal. The pass flushes at every measurement, phase or classical event. It adds no qubits or new measurement operations.


The immediate public parent is submission 7a17cf96-cb0c-485e-8e49-0e4dfa57fe80, PR 2640, at commit aba777ac14bbf66c79a1dd12aba0033db494017c. Its trace had SHA-256 d14c83882d43682ed18d3a7ab5fdb561baa207d82fa2506bcfc489e240dade2f.

The new generator changes the restoring digits inside the hosted field walks. In sector `base`, normalization leaves a factor of `2**base` in the operands for the first enabled restoring digit. The later digit reached after `i+1` shifts retains a factor of `2**max(0,base-i-1)`. Removing this common factor reduces the bit width of the compare and subtract. The final restoring carry has the same value because both operands have been divided by the same positive power of two. Disabling a digit still gives the identity. The hosted probe also computes its rank mask once, uses it to guard the comparison, and reverses the rank mask. These are the lower-field identities used in the prior Q649 field-port investigation, transferred here to the Q650 mixed-radix arithmetic and its field optimizer. See the marked common normalization edit in `construction/donor/research/agents/midpoint-implicit-query-20261109/q651-ten-field/multiply-nine.cjs`.
