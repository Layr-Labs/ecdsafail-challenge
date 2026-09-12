# Quotient-popcount metadata candidate — prepared, unmeasured

`prefix-popcount` is a separate copy of `prefix-no-terminal`. It repurposes the
existing eight-bit termination counter during the proved nonterminal prefix,
using its low six bits for C=popcount(q). No persistent quantum register is added.
The upper two counter bits remain zero. No prior candidate, arithmetic width,
iteration count, nonce, tail algorithm, trusted harness or Cargo file changed.

## Guard and fallback

Enable BOTH `MIDQ_PREFIX_NO_TERMINAL=1` and `MIDQ_PREFIX_POPCOUNT=1`.
The new option defaults off. All of the following are required:

- The predecessor's complete no-terminal guard, including the fixed 360-step
  ping-pong prefix and effective coefficient widths below 256.
- The cross-gated hybrid path is selected, with the higher-priority inline-active
  and recomputed-role alternatives disabled.
- The allocated counter is exactly the existing eight-bit counter-tape width.
- Every actual configured quotient allocation in all 360 steps is below 64 bits.

Each update also checks that this particular step is no-terminal eligible.
Outside that support, the original predecessor logic is emitted unchanged.
The stable all-step guard prevents mixing popcount and termination semantics
halfway through the prefix. All widths are queried through the real configured
thin schedule and existing effective-width functions, not raw table guesses.

## Counter invariant and capacity

On the predecessor's exact-transition/width support, active=1 and each PZ tick
performs exactly one quotient-bit change. With r=[A<B] before arithmetic,
multiplication removes the current lowest one when r=1, and division sets a
previously zero quotient position when r=0. Therefore

    C' = C + 1 - 2r = popcount(q').

The update emits CX(r,C_j) on each of six bits, controlled increment under the
existing active=1 wire, then the same CX framing. For r=0 it is +1; for r=1 the
bitwise-complement conjugation produces -1 modulo 64. The inverse uses the same
framing around controlled decrement. The role and active wires are preserved.

Because q has fewer than 64 allocated bits, its weight is at most 63. A removal
requires weight>=1. An insertion changes a zero position to one, so its new
weight still cannot exceed the allocation width. Consequently real supported
updates never wrap, despite the primitive being defined modulo 64. No empirical
popcount cap is introduced. High counter bits are untouched.

## Ordering and phase

Forward:

1. Compute the existing role r=[A<B].
2. Update C by +1-2r before the arithmetic; none of the no-terminal arithmetic
   controls reads C, because active is derived from the empty counter slice.
3. Run the unchanged multiply and division helpers and clear the role as before.
4. Compute the swap predicate from C==0. Since C=popcount(q), it equals q==0.
   Swap both row pairs and parity; C is unchanged, so the measured predicate
   cleanup remains valid.

Inverse:

1. Use the post-step C==0 to undo the swap FIRST.
2. Recover the inverse helper's initial role from c_a<c_b, equal to 1-r.
3. Undo division, complement role, then undo multiplication as before.
4. The role now equals original r=[A<B]. Apply the inverse counter update BEFORE
   clearing that role from the restored gcd pair.

Only existing phase-correct increment/decrement, CNOT framing, row swaps and
predicate-cleanup primitives are used. In particular a predicate is never
cleared after its count word has changed. The counter may temporarily describe
the future/past q inside arithmetic, but no predicate consumes it during that
interval. No reset is added to force a dirty counter clean.

## Tail handoff

Immediately before the existing tail transition, subtract each actual quotient
bit from C with a controlled decrement. This implements

    C <- C - sum_j q_j = 0

while preserving q. The unchanged tail counter codec therefore sees all eight
physical counter wires in exactly its required zero state and retains their
original ownership/lifetime. After tail replay has reconstructed q and returned
the same eight zero counter wires, controlled increments restore popcount(q)
before the first inverse-prefix swap. Reverse bit iteration is used for the
forward subtraction, matching the inverse's ascending addition order.

This is a reversible arithmetic conversion, not an assertion that the compiler
can infer zero. A whole-circuit cost check must account for any lost compiler
facts: the existing Boolean optimizer may not recognize C=0 after subtraction,
although the exact arithmetic invariant proves it. No synthetic reset is used
as a workaround. The conversion cost is included in the proposed census.

## Local cost screen

A tiny static translation of the existing KG layer shape gives 12 raw CCXs and
three temporary ancillas for a six-bit controlled increment. Complement framing
adds only CNOTs; decrement has the same Toffoli count. This is source-level
expansion, not a compiled-circuit measurement.

For a full-clean measured zero predicate, production plus phase-correct cleanup
costs 2n-3 raw emitted Toffolis, or 1.5n-2 expected executed Toffolis under its fair
measurement. Replacing an n-bit q predicate by six bits and adding one counter
update gives these local estimates:

| q width | Raw saving per boundary | Expected executed saving per boundary |
| ---: | ---: | ---: |
| 12 | 0 | -3 |
| 14 | 4 | 0 |
| 18 | 12 | 6 |
| 24 | 24 | 15 |
| 31 | 38 | 25.5 |

These exclude the once-per-cut conversion and changes from limited-scratch
predicate replay or global optimization. They justify a bounded experiment at
18+ bits, not a whole-circuit T forecast. They also make rejection cheap if the
actual configured width census or full compiler result is unfavorable.

`MIDQ_PREFIX_POPCOUNT_PROFILE=1` configures the production route and compares the
old q predicate against the cached six-bit predicate at every actual width,
including both update directions, row swaps, representative persistent ownership,
and both q-preserving cut conversions. It reports a SIGNED raw saving, so a loss
is visible. The final field accounts for both point-addition inversion pairs.
It also prints q-width range and helper peaks. The role wire is conservatively
held in both census variants; this is a source-helper screen before full
optimization, not the authoritative executed-T or whole-circuit Q measurement.

## Prepared tests and completed evidence

Source parsing/format checks passed. No local Rust build, gate generation or
quantum simulation ran. A small integer metadata model checked 5,992 small-prime
transitions and 46,080 transitions from 128 independent SHAKE-derived secp256k1
inputs. All C=popcount(q), swap-predicate, inverse-update, cross-role and cut
conversion identities held. Maximum observed weight was 9 and cut weight 4;
these observations are NOT used to narrow the proved six-bit capacity.

`MIDQ_PREFIX_POPCOUNT_SELFTEST=1` prepares emitted-gate tests for remote execution:

- All eight-bit counter values, both role values and active0/1, verifying the
  low-six-bit modular update, unchanged high bits and exact inverse.
- All q patterns at widths1,6,9 with C initialized to its true popcount, checking
  q preservation and zero C at the cut midpoint before reconstruction.
- Cached swap boundaries coupled to an actual toggled quotient bit, across three
  bit positions, both measured/unitary predicate cleanup and chunked on/off.
  Midpoint rows/parity are checked independently of the inverse. The reverse
  swap occurs before counter restoration, exactly as in the implementation.
- Four forced/mixed/random measurement streams, unchanged native simulator,
  every reset checked BEFORE execution, preserved initial phase and every
  non-output scratch bit required clean.

This does not test a complete PZ arithmetic step or establish whole-prefix
correctness. Root must run the component selftest, actual-width cost census,
flag-off byte comparison with prefix-no-terminal, and full frozen/independent
quantum regressions before accepting the candidate. For measured Q/T, preserve
the exact generated artifact and trusted benchmark receipt. No new persistent
qubits is a source lifetime fact; temporary ancillas can still move peak Q.
