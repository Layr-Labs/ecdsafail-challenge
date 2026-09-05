# Exact Chunked Fresh-Carry Comparator

Base: `bdfd306`. Opt-in: `MIDQ_CHUNK_COMPARE=1`. No arithmetic-width,
schedule, nonce, harness, dependency, or other primitive changes.

## Contract

`borrow_compare_refs(v,u,out)` XORs the unsigned predicate `[v<u]` into
an arbitrary output bit and restores both operand registers. Inputs are
little-endian views, not necessarily contiguous. The new path accepts
repeated input references and overlap between the input views, but the
output must be disjoint from both inputs. The old fallback retains its
original (more restrictive) operand-alias contract.

`clear_borrow_compare_refs` retains the existing contract: the output must
already equal the predicate on the current operands. It is NOT a reset of
an arbitrary output bit. If `MIDQ_MEASURE_COMPARE` is disabled, cleanup is
the usual XOR comparator. If enabled, cleanup measures the predicate and
corrects its phase using a separately implemented phase endpoint. It never
recurses through `borrow_compare_refs` after measuring its output.

## Local Majority

Over F2, `MAJ(a,b,c) = ab XOR ac XOR bc`
`= c XOR ((a XOR c) AND (b XOR c))`.
On a fresh target, XOR c into a and b, apply one CCX to the target, XOR c
into the target, and restore a,b. Thus every step restores its sources
immediately. Initial c=0 needs only CCX; c=1 uses CCX plus two CX gates
(the OR function). No assumption is made about the other input bits.

For a known majority target t, HMR with outcome m resets t to zero and
adds phase `(-1)^(m*MAJ)`. Under m, CZ(a,b), CZ(a,c), CZ(b,c) cancel that
phase exactly, with no Toffoli. For c=0 only CZ(a,b) remains; c=1 adds
Z(a), Z(b). These are pointwise identities for all eight local inputs.

The complement of b is applied only around a single computation or phase
correction, never across the whole register. Repeated slots are therefore
safe. If a and b are the same physical qubit, MAJ(a,a,c)=a, and
MAJ(a,~a,c)=c; these cases use copy/phase directly, without an aliased
quantum gate. A constant-one phase is an explicit `Neg`, not an omitted
global phase: under a classical condition that sign must still be tracked.

## Chunk Invariant

Before chunk j, the original operands are unchanged and the only live
scratch consists of its earlier boundary carries. Compute the local
fresh-carry chain using the preceding boundary (or the constant initial
carry). Clear interior carries right-to-left with the local identity,
keeping only the endpoint when another chunk follows. All controls are
still present when a carry is cleared. On the final chunk, first copy its
endpoint into out, then clear its entire chain. For a phase-only endpoint,
compute only the first L-1 carries, apply the three-CZ majority phase on
the last original input pair and preceding carry, then clear the prefix.
In particular, out need not start at zero for the XOR endpoint.

Clear retained boundaries right-to-left. HMR the boundary, free its now
zero slot, and, conditioned on its measurement m, recompute only that
chunk's first K-1 carries from the unchanged operands and preceding
boundary. Apply the final majority's three-CZ phase without computing or
allocating its endpoint, then MBU-clear the fresh prefix chain in reverse.
This is precisely the measured Boolean function's phase, so this
cancels `(-1)^(m*f)`; every nested HMR phase is separately canceled.
Earlier boundaries remain until their own cleanup. No measured classical
flag is reused for an inner HMR or modified while it controls a block.

Every branch of every measurement transcript therefore implements the
same basis permutation and phase channel. By linearity this proves the
coherent-input contract, not just classical correctness. The arbitrary
XOR-output bit is preserved except for the requested XOR. All scratch
is zero BEFORE every R emitted by `zero_and_free`.

The native Simulator intersects PushCondition masks, including direct
per-op conditions. HMR updates only active lanes and leaves inactive
classical lanes unchanged. Each inner HMR and its phase correction inherit
the same enclosing conditions. Scratch starts globally zero, is restored
in active lanes, and is untouched in inactive lanes, allowing unconditional
allocator reuse even when the reset itself was under a condition.

## Comparison, Signs, and Initial Carry

The production call adds `u + (2^n-1-v) + 0`. Its carry is `[u>v]`,
exactly `[v<u]`, including zero, equality, maximum words, and leading ones.
Initial carry one instead yields `[u>=v]`; both initial values are supported
and checked by the internal emitter. With no complement, it is the carry
of a+b+cin. At width zero it is the initial carry (production comparison
uses zero and remains a no-op).

No signed interpretation is silently introduced: sign/high bits are ordinary
bits of the existing unsigned predicate. An existing signed wrapper can
flip both sign bits before and after this unsigned comparator. An existing
complemented-predicate wrapper must remove its NOT before known-flag cleanup,
or account for the additional measured constant-one phase. The integration
does not change either caller convention.

## Resources and Cap

Let n>0, chunk bound K>0, B=ceil(n/K), L=n-(B-1)K. The peak new qubits are

`D = n` if B=1, otherwise `max(B-2+K, B-1+L)`.

This includes EVERY retained boundary and the final chunk. During replay a
boundary is measured and freed before its K-1 fresh slots are acquired, so
replay never exceeds that maximum. There is no initial-carry ancilla and
no separate phase-endpoint qubit. At n=256,K=32, D=39.

The planner flushes pending frees, then among K up to the configured
maximum (default 32) whose D fits the current live headroom, minimizes
`(B-1)(K-1)`, the boundary replay Toffoli count. Ties prefer smaller D,
then smaller K. It does not greedily maximize K: n=76 with 40 spare
qubits chooses K=2, not K=32. If there are n spare qubits it chooses K=1,
which needs no boundary-replay Toffolis at all.
`MIDQ_CHUNK_COMPARE_SIZE` overrides the maximum. The default cap
is 1019; `MIDQ_CHUNK_COMPARE_QCAP` may lower but cannot raise it. If no K
fits, it emits the old comparator unchanged. This bounds the extra path,
not unrelated allocations or an inherited baseline peak already over cap.

For distinct input bits (no local alias simplifications), let `R=(B-1)(K-1)`.
The XOR oracle emits `n+R` and expects `F=n+R/2` executed Toffolis. The
phase oracle emits `n-1+R` and expects `P=n-1+R/2`. The production
forward-plus-measured-cleanup pair emits `2n-1+2R` and has expected executed
count `F+P/2 = 1.5n-0.5+0.75R`, because the cleanup phase oracle runs with probability 1/2.
Each inner boundary replay inside that cleanup runs with probability 1/4.
The unchanged pair emits 4n and expects 3n. These are Toffoli counts, not
Clifford+T T-gate counts. At 256/32 the pair is 945 emitted, 546.25 expected,
versus 1024 emitted, 768 expected (28.8736979% expected saving). At 256/1
it emits 511 and expects 383.5, using 256 scratch qubits. The planner may
choose different K values for forward and cleanup if the live headroom
changes; each oracle's formula and phase proof applies independently.

## Verification

Run the selftest without editing the harness, via its existing entry point:

```sh
cargo build --release --offline --bin build_circuit --target-dir /private/tmp/midq-chunk-target
MIDQ_MEASURE_COMPARE_SELFTEST=1 MIDQ_CHUNK_COMPARE_SELFTEST=1 /private/tmp/midq-chunk-target/release/build_circuit
```

The test module calls the unmodified `crate::sim::Simulator`, not the port's
no-op contract stubs. A separately flattened classical-condition pass
checks zero immediately before every reset, then compares values, phases,
classical bits, and executed gate counts against the complete native
condition-stack run. Operation slots are also checked with `Op::validate`.
The expected output is an independent high-to-low integer comparator.

Coverage includes exhaustive widths 0..5, every chunk size at those widths,
both initial carries, both operand-complement modes, arbitrary output bits,
phase endpoints, known-flag cleanup, nested enclosing classical conditions,
forced-zero/forced-one/random measurements, stale inactive HMR bits,
full-width inputs through 257 bits, equality/propagation/high-bit cases,
noncontiguous and repeated input slots, invalid output aliases/widths rejected
before emission, native Q vs exact sizing through width 257, and exact
old-stream fallback, measured/unmeasured integration, and different forward/
cleanup headroom. All tiny measurement transcripts are enumerated as well.
Component averages additionally use 65,536 native shots.

The local majority identity is derived above. Measurement-based uncomputation
follows the temporary-AND principle of Craig Gidney,
[Halving the cost of quantum addition](https://arxiv.org/abs/1709.06648).
Whole-circuit measurement results and limitations are recorded separately in
`chunked_compare_results.md` when the runs finish. No submission or nonce search.
