# Exact bounded control networks

Parent72190cc, verifiedQ1019/T14748731.513. All options below are default-off.
No arithmetic widths, quotient ranges, iteration counts, or guards change.

## Unequal chunks

MIDQ_VARIABLE_CHUNKS uses the shared clean_chunk_plan for prefix queries and
comparisons. A nonfinal chunk of length k retains one boundary and needs k-1
columns of local replay. If N columns end with b retained boundaries and f
columns in the final chunk, replay is N-b-f. Since b+f<=A available wires,
N-A is a lower bound, clamped at zero. The greedy unequal plan attains it
whenever the two-level schedule fits. Every forward and replay peak is checked
against the same compile-time budget. Infeasible queries retain the old path.
Boundary replay is conditioned on its HMR outcome, so expected replay cost is
half the emitted replay cost. No quantum branch decision is measured or skipped.

Planner tests cover263169 count/budget pairs. Prefix tests cover1391280
basis/measurement cases. Comparator tests retain2350720 original cases plus
1843200 unequal-chunk exhaustive cases and wide nested-condition batches.

## Predicates and one-hot writes

MIDQ_CHUNKED_PREDICATE uses exact bounded AND prefixes for zero/nonzero
queries and their phase oracles. For nonzero, its constant phase term remains
explicit. Tests cover1691802 cases, including512-bit inputs, forced/random
measurements, both classical conditions, and every reset before execution.

MIDQ_MEASURED_DEMUX writes q[address] XOR active through an address tree.
The two children of a prefix share one temporary AND. At a two-leaf endpoint,
CX(q1,q0),CCX(parent,address_bit,q1),CX(q1,q0),CX(parent,q0) toggles the selected
output with one Toffoli, even for arbitrary old q0/q1. Prefix ANDs are restored
by HMR plus conditionalCZ. Partial address ranges are pruned without changing
out-of-range behavior. Tests cover51552 basis/measurement cases, nested
conditions, arbitrary output values, phase and every pre-reset zero.

## Outer phase cleanup

MIDQ_MEASURED_OUTER_PHASE moves overflow HMR before the SAME64-bit comparator
oracle. The oracle and its reverse run only when that HMR outcome is1. The
cleared overflow becomes carry scratch. A control copy is allocated only when
the comparator mutates that control's original wire. The source overflow is
never borrowed. The inherited73-bit fold and64-bit comparison stay unchanged,
including their phase syndromes on noncanonical values. Remote tests cover
319872 full-width cases with aliases and three measurement streams, checking
the inherited syndrome and every reset.

## Controlled addition

MIDQ_CHUNKED_CONTROLLED_ADD is a separate optional extension. It computes
unconditional carries of a+b, then writes s_i=a_i XOR g*(b_i XOR c_i).
For both values of g, MAJ(a_i,b_i,c_i)=MAJ(s_i XOR g,b_i,c_i). This identity
permits exact measured carry cleanup using only Clifford phase corrections.
Boundary carries are replayed from updated sum bits under their HMR outcome.
The old adder is retained when fully vented, when no bounded plan fits, or
when input/control aliases are present. The caller's workspace budget is not
increased. Expected cost is2n-1 plus half the boundary replay, versus the old
3n-2-vents. Component tests passed3276032 cases covering long carries,
both controls, nested conditions, sources, phase and pre-reset cleanup.

## Whole-circuit receipts

First four options, all workspace caps1009, frozen parent9024:
Q1017, averageT13957182.604, totalT125949615822,0 classical/0 phase/0 ancilla.
The artifact contains80220443 operations. Independent9024 retains exactly
the baseline's five classical failure inputs4174,4968,5407,7617,7854, with
no phase or ancilla failure in this run. The controlled-adder extension and
coefficient-cell integration are not included in those measurements.

All heavy work is remote-only, serialized under the shared lock, within the
user-confirmed16vCPU/1RTX5090/32GB allocation. These are frozen/common-corpus
checks, not validation of a newly selected circuit-dependent nonce. The strict
Q<=1009 andT<12.5M target remains open.

## Zero-scratch field negation prototype

MIDQ_ZERO_SCRATCH_NEG is an optional peak-only fallback, not yet validated
in the combined circuit. Two zero-vent controlled additions, with the arbitrary
donor complemented between them, add g*(D+NOT D)=-g modulo2^n. Complementing
the destination around that pair implements +g instead. This uses no clean
quantum scratch and restores every donor bit. Apply these increments to the
four suffixes selected by p+1=2^256-2^32-2^10+2^5+2^4 after the original
controlled destination complement. The result remains p-x modulo the FULL
original word width, including noncanonical 257-bit edge representations.
It trades additional gates for two scratch qubits only where the ordinary
constant-adder scratch would exceed the requested cap. The increment primitive
passed87376 exhaustive target/donor/control/direction cases. The forced fallback
also passed the full257-bit endpoint tests, including noncanonical words.

## Rotation-based halving and doubling

MIDQ_ROTATED_HALVES implements the same finite-word permutations as the
original fast cells. Put N=2^256,L=2^255,C=(F-1)/2=0x800001e8. For x=2u+b,
the original halve is H(x)=((u-b*C) mod L)+b*L. Rotate x right by one bit,
then subtract C from the lower255 bits controlled by its new top bit. No
separate parity wire is needed. For x=u+b*L, the original double is
D(x)=(2u+b*F) mod N. Rotate left, then add C to bits1..255 controlled by
the new low bit, which has already supplied the carry's unit contribution.
The original257th word bit is untouched in both transformations. These are
identities on every256-bit word, not new claims of exact field division on
the baseline's rare approximation edge inputs. Differential tests against
the old cells passed, including noncanonical words and both directions.

## Checkpoint controls without fresh scratch

MIDQ_DIRTY_CHECKPOINT_LOOKUP replaces a cubic lookup's clean helper with
an unused checkpoint input as a dirty donor. The four-CCX identity restores
that donor and implements the same cubic monomial on every input.

MIDQ_INPLACE_CHECKPOINT_SIGN uses an exclusive linear coordinate in each
decision's ANF: sigma_i=v_i XOR f_i(other bits). The chosen input coordinates
for the four rounds are a[1],a[2],a[3],b[2]. Temporarily XOR f_i into v_i,
use v_i as the coefficient cell's sign, and reverse that XOR network. The
cell touches no other retained checkpoint bit, and the loaned odd lows are
distinct. This removes the separate sign wire without a new approximation.
Its integrated tests and full-circuit resource measurement remain pending.
