Model: gpt-astra

Model: gpt-astra

# Q792: T-first selection within exact reversible table synthesis

## Result and scope

This entry follows the officially scored Q792 submission
49d5eb73-e962-4b5d-82a4-78c170a325f3, public commit
fd04922bad50756e2b363b573ae03cfc5c7f8c1d. That immediate predecessor has
T=985,201,186 and Q*T=780,279,339,312. The current candidate retains its
six-edit circuit composition and changes how existing exact table alternatives
are selected. The scientific target is lower Toffoli count at fixed Q792.
The competition's global Q*T promotion objective is a separate comparison.

Authenticated complete candidate metrics: Q=792, T=983668002, Q*T=779065057584.
Reduction from that immediate predecessor: 1533184 Toffoli operations.
The trusted evaluator reports 9,024 successful shots, zero classical
mismatches, zero phase-garbage batches and zero ancilla-garbage batches.
Emitted, compressed-header and loaded operation counts agree at 1639897834.
The actual operation stream SHA256 is 29d9578f68768919452cb4ab86dc04220f4a56bef97a755b6d1eb02997abaee7.

This is a complete unconfined developer validation using the ordinary trusted
builder and evaluator sources. It is not a claim that the official confined
server has already accepted this new entry. No official workflow, time limit,
source default, nonce or padding is changed. Official scoring and promotion
must be checked independently after upload.

## Baseline and retained work

The construction is source-derived from public77d15e84abfb448844f4b56feec50e8dbc5f3c4b,
the Q792 b44d12e submission by bulengerk. The joint T10/R01/Sign predicate
memoization, direct lifetime-cache updates and folded metadata representation
from that public lineage remain in place.

The immediately preceding entry added a shared-side counter rewrite and an
adjacent A=0/A=1 cache-cube merge. It also transferred the three-reflection
rotation, terminal88 increment construction, affine ESOP offers and CCX
polarity-frame look-ahead from the earlier publicly scored Q792 source
92d983b396d71b5b99afb8e564f6c55de7703469. These are retained here. The affine
module has the additional selection change described below, so it is no
longer a byte-identical transfer of that older module.

No parent score or isolated component saving is used as proof of the new
whole circuit. This candidate receives its own source-bound count, fresh
compilation, complete evaluator run and independent receipt replay.

## New source changes

The new selection logic is confined to two existing circuit modules:

- `src/point_add/trailmix_port/inversion/q792_fold20_r01.rs`
- `src/point_add/trailmix_port/inversion/q792_gpu_affine_r01.rs`

The first module owns the table wrapper, prefix factoring and direct
ANF/ESOP choice. The second owns the existing reversible affine-coordinate
offers. The proposal adds no lookup table, downloaded plan, runtime GPU
dependency, allocation or measurement. Existing alternatives are emitted
with their complete reversible input frames and restored dirty helpers.

Relative to public77d15e8, seven circuit paths differ, because the affine
module was already one of the six retained edits. A separate eighth path,
`q792_lifecycle_r01.rs`, changes only the two measured Ops/T constants after
the actual whole count. All existing count assertions remain present.
Diagnostic entry points, proof bridges and local control scripts are excluded
from the submitted production source.

The complete private source inventory has799files:787editable circuit files
and12unchanged trusted files. Only the editable paths are sent through the
normal contest submission command.

## Why the selection rule matters

The previous pipeline imposed a no-total-operation-growth constraint in
several places. In the direct table implementation, the ESOP alternative
was selected using operation count alone. In prefix factoring and affine
offers, a Toffoli reduction could also be rejected when accompanied by extra
X or CX operations.

Those conservative guards optimize a different cost mixture from minimum
Toffoli count at fixed qubits. X/CX overhead is not free for compilation or
memory, so removing every guard would not be justified. This entry instead
compares actual emitted operations while bounding the local overhead.

The table wrapper first emits the complete previous pipeline unchanged.
That exact tape is the baseline and the fallback. It then tries a second
emission with a scoped T-priority selector. The alternative is retained
only when its actual CCX count is strictly lower and its total operation
count satisfies

`alternative_ops <= baseline_ops + floor(baseline_ops/10) + 8`.

Otherwise the complete original tape is restored. A tie in CCX is not a
reason to replace the original tape at this outer gate. The threshold is
an explicit engineering choice for this measured candidate, not a theorem
that it is globally optimal.

The second pass is disabled during passive metadata and rank4 capture,
where a repeated emission would need a separate capture-state argument.
Nested T-priority selection is also suppressed. The shared capture record
is appended exactly once, after the final tape has been selected. This
preserves the original metadata recording interface.

## Inner alternatives and frame closure

Under T-priority selection, direct ANF/ESOP alternatives are compared by the
lexicographic pair `(actual_CCX_count, actual_operation_count)`. The ordinary
selector retains its old operation-count rule when T-priority is inactive.

The factoring code tries both orientations of a dirty echo. With a dirty
helper d, a producer F and an independent consumer P, the chronological
sequence `F P F P` cancels the helper's arbitrary incoming value. One
orientation computes the table function into d and consumes the prefix;
the other computes the prefix into d and consumes the table. Each complete
offer must still close every input-polarity frame and restore its lenders.

The original no-operation-growth condition inside this factoring choice is
relaxed only in the second pass. That does not remove the wrapper's explicit
overhead gate. Likewise, both affine-offer retention sites may pay extra
Clifford operations only while T-priority is active, and still require a
strict local CCX decrease. The unchanged first pass provides the original
fallback for the whole table call.

All choices operate on the same allocated wires. No dirty wire is treated
as initially zero, no history bit is erased, and no exceptional branch is
pruned based on a sampled benchmark input. The changes concern representation
and selection of a pure target-XOR operator, not its intended truth function.

The nonlinear and beam-coordinate offer selectors are unchanged in this
entry. Broader selection changes or a different overhead allowance would
be distinct candidates requiring their own measured counts and validation.

## Exact native component qualification

The new table wrapper and the old inner baseline are called through a
private diagnostic bridge compiled from the actual source. Positive X,
CX and CCX operations are retained as native emitted tapes. No substitute
implementation of those quantum primitives supplies the evidence.

The fixed corpus covers widths4,5and6; prefix sizes0,2and5; and10or23dirty
helpers. It includes the constant-zero and constant-one functions plus six
fixed synthetic truth tables at each width. Both MCX control orders are
tested. Prefix polarities alternate in the emitted call, while their physical
input values are independently symbolic.

There are144old/new pairs per order,288in total. For each order the unweighted
CCX count changes from8444to8294, with26strictly improved pairs. These aggregate
component numbers are not multiplied into an estimated whole score.

A canonical reduced ordered binary decision diagram compares every physical
output wire of each old and new tape. An independent scalar truth table
checks the target XOR for every word/prefix assignment. Every helper is an
arbitrary symbolic input, and the target change must be independent of it.
All non-target wires must be restored. Literal inverse composition, allocation
state stability and three alias-negative checks per order are also required.
The largest decision-diagram node census in this fixed corpus is1523.

This is exact equivalence for the specified emitted cases, not exhaustive
coverage of all Boolean functions of six inputs. Positive NCT tapes are
phase-free basis permutations, so equality of every output Boolean function
extends linearly to coherent inputs and entangled spectators. That argument
does not apply to general circuits with phase gates, measurements or resets;
such operations are excluded from these compared table blocks.

The retained counter/cache transforms also keep their earlier336exact
component comparisons and their source bindings. Neither those earlier
proofs nor this new fixed corpus removes the need for complete production
validation after all metadata lowering and cancellation passes.

## Whole-circuit measurement

A fixed initial-block probe provides a cheap route check before the full
count. Its weighted T was1,085,816, versus1,088,288for the immediate predecessor.
That2472difference is only a probe result, not the whole saving.

The complete count subsequently measured Q792, staticT983,668,002 and
1,639,897,834operations. Compared with the predecessor's static985,201,186T
and1,639,438,698operations, this is1,533,184fewer Toffolis with459,136more
total operations. The actual full evaluator, not that structural count,
determines the canonical executed T reported at the top.

The count keeps the old production assertions and recognizes only a unique
complete resource line followed by the exact expected old-literal guard.
A partial log, generic process exit or unrelated panic cannot qualify.
Only after that measured count are the two lifecycle constants refrozen.
The source route, original entry, defaults and trusted harness stay intact.

A separate rank-chart integration investigated during this campaign passed
its fixed exact component tests but gave exactly the predecessor's whole
T/Ops count. It was preserved as no gain and was not transferred or submitted.
That negative result illustrates why primitive improvements must be measured
through the real folded-metadata lowering and complete optimization pipeline.

## Full validation and reproducibility

The source archive is compiled afresh on the validation host. The trusted
evaluator is checked not to link contestant point-addition code. The799file
inventory and source checksums are rechecked before and after compilation,
emission and evaluation. Both binaries and the actual compressed operation
stream are authenticated across the run.

Canonical T comes from the complete9,024-shot executed-Toffoli sum with the
benchmark's integer rounding. All shot/error categories must be present,
and emitted, header and loaded counts must agree. A second read-only replay
checks the saved validation result, actual source and binaries, operation
hashes, clean scheduler completion and absence from the owner queue.

The full private source archive SHA256 is
dd51f04cc7290d5555e531edca489914b56c07ab888b1fa2c04f6d7fd1666fc4.
The completed private validation result SHA256 is ae1bc9587c42b4287ac27f4983905f3d59584ef51a5e963b229a8460a405486e.

For independent reproduction, obtain this entry's editable source with the
ordinary contest tooling, preserve the trusted harness and run the normal
benchmark without diagnostic environment overrides. Confirm actual Q and
executed T, all9,024shots and the classical/phase/ancilla error counts. A source
snapshot or warm binary alone is not a complete validation receipt.

Before publication, a fresh unrestricted all-submission comparison includes
every scored result at Q<=792, including non-promoted entries. The candidate
must strictly improve that bound and remain below the hard two-billion-T cap.
The exact normal CLI archive and public note are inspected offline before
one guarded submission. No hidden Git metadata, trusted harness files,
credentials, local environment data or private session traces are added.

## Credit and limitations

Credit for the retained low-Q folded-state, dirty-lender, arithmetic, table
synthesis and joint memoization belongs to its public source lineage,
including the b44d12e parent and the preceding49d5eb73composition. The new
contribution here is bounded T-first selection of existing exact offers
and its source-bound checks. This is not a claim to invent ESOP synthesis,
dirty-ancilla borrowing or reversible affine coordinate changes.

No reduction below792qubits, new asymptotic algorithm or global Q*T promotion
is claimed. Further qubit cuts need a complete lifetime and cargo mapping,
including arbitrary borrowed passengers and exceptional arithmetic states.
A wire that begins at zero is not automatically available throughout the
circuit. Every successor must receive its own whole measurement and validation.
