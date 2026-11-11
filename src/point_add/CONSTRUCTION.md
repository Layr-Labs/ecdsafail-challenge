# Rebuild the Q650 hosted arithmetic

This circuit adds a classical secp256k1 offset to a quantum point. The direct width-650 parent is jackylee0424's submission 3389bfa0-f3bc-426b-92cd-810eef428672 in PR 2628 at commit 12359bfb7386a0d9c29d9aed441be8c67cdcb16d. That public construction used nasqret's b573fae1 as its immediate base. Its original source and attribution are retained under construction/donor. The current point shell uses the parent's nine-helper stage maps. The final constructor is construction/q650/point.cjs. The immediate arithmetic predecessor is the under-cap hosted Q650 construction with raw trace SHA-256 988126fb17284046fd8f55de970f81189bb5958292436183c0053859ea73f962.

In the upper sign probe, only ranks from zero through its row-specific maximum are ordinary. The exceptional all-ones rank can be identified by its leading prefix through the highest zero of the ordinary maximum. Conjugating the exceptional-code flip by a CNOT fanout implements the same transposition. A controlled fixed permutation is factored into two involutions on a borrowed selector. A conditional increment uses two unconditional additions and conditional complements of its destination and borrowed word. The common predicates in a descending ripple are similarly shared using a restored arbitrary bit.

The fused digit handles a normalized divisor with an implicit high one. A borrowed qubit accumulates the two carry contributions that would have been written into that constant site. Two controlled involutions on the high target bits remove its arbitrary incoming value. The common lower-digit predicate is carried through the falling ripple and all loans are restored. The actual occupied high divisor site is untouched.

In the short division, an additional normalization bit uses the test site during initial alignment and moves into the released low remainder after the first active digit. This preserves the outer walk's nonzero-remainder tests and terminal ordering. The inner canonical walk, the signed history walk, and the multiplier use the matching endpoint variant. Direct gates for the virtual high-one digit are used wherever this schedule requires it. A 128-bit stage binds its actual surviving logical sites by the original fixed width-650 maps.

Use Node 24 on a little-endian host. The following commands run from the construction directory. The top-level manifest pins both complete outputs. The Rust decoder emits ordinary stock operations from the independently checked schedule.

```sh
node q650/point.cjs raw trace.u16le
node q650/point.cjs spans ranges.tsv
sha256sum -c ../TRACE-SHA256.raw
bash codec/tpeep-fixpoint.sh trace.u16le ranges.tsv peep.u16le peep.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh peep.u16le peep.tsv rebuilt
bash codec/verify.sh peep.u16le rebuilt
```

The generator uses larger search bounds for the physical compilers and two whole-tape commute filters
(q650-joined-probes/h1-params.cjs). The packaged stream is the raw trace after an exact windowed pair-cancellation
peephole (codec/tpeep.c, from Akashneelesh's 650 submission 5909718a, run until a pass removes nothing): it deletes
two identical unconditional X, CX or CCX records when every record between them commutes with them. Measurement
records are never removed. At build time src/point_add/peephole.rs runs a further exact pass on the decoded
operations (identical-Toffoli pairs, shared-control merges and dirty-gadget alternation) before build() returns.

After the reversible arithmetic is scheduled, the physical field and upper streams use commuting cancellation and low-rank Boolean reductions. A parity-transfer pass combines recurring Toffolis through supported linear effects. A bounded product cache then reuses equal controls on a proven available quantum wire, erasing the product by X-basis measurement and a conditioned CZ. All added measurements use one reusable classical bit.
