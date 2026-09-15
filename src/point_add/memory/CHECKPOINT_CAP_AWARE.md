# Checkpoint constant-update cap awareness

Isolated candidate based on integrated-r5. Default off. No global cap, value
width, round count, state-support condition or trusted harness was changed.

## Observed cause

The cap1009 scout's Q1011 frame is
`ec3.inv_fwd/midq.tail.backward.checkpoint/gidney_cadd`. Its live names include
one `gcc_cy`, one `gcc_carry`, and no `gcc_anc`. The input live count is1009,
including a retained `midq.cell.overflow`; the existing compact constant adder
adds two fresh ripple lanes. It is already the compact two-clean variant.
`MIDQ_VALUE_VENTS` controls a different arithmetic helper and cannot fix this
allocation. There is no live-vent budget to clip in this constant kernel.

## Implemented fallback

Enable `MIDQ_CHECKPOINT_CAP_AWARE=1`. The cap is `MIDQ_CHECKPOINT_QCAP`, defaulting
to the existing `MIDQ_CELL_QCAP` value (or1009 if unset). Only checkpoint
coefficient rounds install the exact host-side `checkpoint.cap_aware` scope.
Only constant updates inside that scope can select the new fallback.

The selector flushes pending frees and compares actual live wires against the
required clean scratch. The compact dirty constant path requires two; the
legacy dirty path requires three. It does not invent a scratch bound for the
unrelated generic clean-ancilla constant adder. When the old path fits, its
original gate sequence is retained. Unsupported large constants or donor shapes
also retain the old route; this is not a blanket global-cap assertion.

For an admitted low-headroom update, write the constant as signed powers of two
using its nonadjacent binary form. Add/subtract each power by a controlled unit
update on the **entire remaining suffix**, preserving the existing word width.
For an arbitrary n-bit quantum donor D,

    D + NOT(D) = -1 modulo 2^n.

Two existing controlled hybrid additions with vent budget zero therefore
decrement the target under the control. Complementing the target before and
after gives an increment. Complementing the donor twice restores it exactly.
Both adders have zero clean workspace at zero vents; the recursive/chunked
admission also receives budget zero and cannot introduce a carry plan. A one-bit
suffix uses CX directly.

The new path emits only X, CX and CCX. It has no measurements, phase gates,
ancilla resets or fresh quantum allocation. It is an exact controlled modular
addition on every target word and arbitrary donor, including noncanonical and
wrapping values. Removing the old internally corrected carry measurements does
not remove any external predicate or error-phase obligation. The checkpoint
lookup, finite-word coefficient formulas, overflow cleanup, later signed resets
and checkpoint ownership are unchanged.

The control, whole target and required donor prefix must be pairwise disjoint.
Both donor additions restore their source. The kernel asserts unchanged active
and historical peak counts after execution. It does not free or borrow any
logical checkpoint/value lane as a clean qubit.

## Cost and limits

The signed decomposition is

    F = 2^32 + 2^10 - 2^6 + 2^4 + 1,
    (F-1)/2 = 2^31 + 2^9 - 2^5 + 2^3.

The local literal gate-template census is7,348 CCX for F on256 bits and5,816
CCX for (F-1)/2 on255 bits, versus raw compact-adder counts764 and761. These
are primitive counts before the global compiler, not complete-circuit executed
T. The tradeoff is deliberately explicit and must be measured in the scout.

A pre-existing live floor above the requested cap remains above it. Optional
`MIDQ_CHECKPOINT_CAP_TRACE=1` reports this condition and the actual input count.
The next whole-checkpoint peak may be the comparison scratch: the old cleanup
HMRs overflow but retains its zero lane while allocating a phase-comparator
carry. Consuming that zero lane before phase cleanup is a separate ownership
change, to consider only after the first scout confirms the next bottleneck.
This candidate does not silently change that protocol or claim Q1000/Q1009.

## Prepared hooks and completed local checks

`MIDQ_CHECKPOINT_CAP_PROFILE=1` runs a small count-only probe, including actual
1008/1009-wire pre-adder frames and requested caps1000,1009,1010,1011. It logs
actual peak, raw Toffolis, added clean wires, and whether the entry live floor
already exceeds the cap. It does not generate a whole circuit.

`MIDQ_CHECKPOINT_CAP_SELFTEST=1` prepares native comparisons against the unchanged
old constant kernel. They cover all target/donor/control assignments at small
widths, signed directions, wrapping constants, four independent measurement
streams, nested executing/skipped conditions, exact normal-headroom and
out-of-scope operation equality, legacy three-clean admission, and actual
255/256-bit primitives with arbitrary dirty data at the scout's1009-wire floor.
Every reset is audited, sources/spectators are preserved, and phase is checked.

`audit_checkpoint_cap_aware.py` passed281,344 small reversible gate-template cases
and256 full-width cases locally, with literal scratch/Toffoli accounting.
This independently implements the zero-vent controlled-adder gate template and
the new signed-unit composition; it is not a claim that the Rust native tests
have run. Rust parsing and the campaign source guard are recorded separately.

Root owns native execution, count-only scouting and complete-circuit tests.
Use the runtime flag with equal global caps on the unchanged r5 parent and this
candidate, then measure the actual next peak. No heavy local or remote job was
run by this worker.
