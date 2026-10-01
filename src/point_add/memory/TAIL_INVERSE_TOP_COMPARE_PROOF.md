# Inverse tail top120 comparison

`inverse-top-compare` is a separate copy of frozen `fused-top-compare`.
Enable `MIDQ_TAIL_INVERSE_TOP_COMPARE=1`; this new flag defaults off and is
independent of both forward fused and forward top-comparison flags. Integrated-r4
and all predecessors were left unchanged. Only src/point_add changes.

## Qualified doubled-coefficient theorem

Use the same explicit hypotheses and lattice certificate as
`TAIL_CANONICAL_SUPPORT_PROOF.md`: ideal PZ transitions through cut360, begun
quotient leading shifts<=31, positive handoff values bounded by b_max<2^85,
true normalization and faithful tail value/sign/width/metadata transitions.
The threshold pair R>2*b_max and its coefficient V prove that any nonzero
relation c*x=v mod p with |v|<=2*b_max has modular coefficient distance>=V>2^137.
This is an exact-support theorem, not a statement about arbitrary cell inputs
or accidentally successful width-error executions.

At an inverse cell, the current canonical coefficient y represents an odd,
nonzero integer v_new with |v_new|<=b_max. Its canonical double

    A = 2*y mod p

represents2*v_new, still nonzero and within2*b_max. Hence

    min(A,p-A) >= V > 2^137.

The source rotated double agrees with that canonical A on the same margin.
This doubled margin is essential; a large distance for y alone would not suffice.
No forward-fused implementation assumption is required.

Let M=2^256, F=2^32+977, p=M-F, B be the source coefficient, t=1-sigma the local
subtract flag after inverse apply flips the source sign, and kappa the raw
signed-add overflow. At the existing folded/complemented-frame cleanup, the
ordinary word z satisfies:

| t | kappa | z-B |
| ---: | ---: | --- |
|0|0|A|
|0|1|A-p|
|1|0|M-1-A|
|1|1|F-1-A|

Therefore |z-B|>=V-(F-1)>2^136. Equal upper120-bit words could differ by at most
2^136-1, so their full unsigned ordering equals the upper120-bit ordering.
The implementation compares ordinary refs `target[136..256]` against
`source[136..256]`. This is intentionally DIFFERENT from the forward rotated
oracle's physical target[135..255] slice.

The original HMR of kappa stays in place. The shortened comparison phase still
computes kappa, so its correction cancels the measured phase exactly. Numerical
outputs and the source sign are unchanged. Equality holds coherently on the
certified support, including arbitrary entangled spectators.

## Scope and construction guard

The old private `signed_add` remains a full-comparator wrapper. A private
`signed_add_context` receives inverse_context=true ONLY from apply(inverse=true).
Forward nonfused apply and all standalone/generic signed_add callers use false.
The generic comparison primitive is unchanged, as is the entire forward fused
module. Inverse's nonrotated branch also passes the context, but its guard fails
and retains the full comparator.

Eligibility requires the new flag, measured comparison, rotated halves,
ping-pong tail, cut360,224 tail rounds, every constant value width<=85, and
shift-register width<=5. It does not require MIDQ_FUSED_ROTATION_CELL or
MIDQ_TAIL_TOP_COMPARE. Failed eligibility emits the original full256-bit cleanup.
These are configuration checks only. They do not establish actual input
membership in the exact-transition support. Whole-circuit membership and
frozen/independent regressions remain required.

A distinct diagnostic section `midq.cell.inverse.top120_compare` marks admitted
calls without adding gates. No persistent qubit, arithmetic width, iteration,
nonce or stored-value representation changes. Flag-off bytes must be compared
against the predecessor after compilation.

## Completed scalar evidence

All512 unchanged certified predecessor fixtures passed inverse scalar checks:
canonical doubled margin, literal signed-add folded result, full comparator,
top120 comparator, and recovery of the original coefficient. All four local
(subtract,carry) cases occur:150,134,120,108. The minimum observed doubled margin
has193 bits, and the minimum observed folded comparison gap has194 bits.
`TAIL_INVERSE_TOP_COMPARE_ALGEBRA.json` records hashes and results. The window
remains theorem-derived120 bits; these observed margins do not justify further
narrowing or certify the emitted circuit's inputs.

## Native tests and exact component census prepared

Remote entry point:

    MIDQ_CELL_FOLDS_SELFTEST=1 MIDQ_TAIL_INVERSE_TOP_COMPARE_SELFTEST=1 build_circuit

The suite prepares:

- Full inverse256-bit comparison versus top120 for all512 certified fixtures,
  256/257-bit interfaces, caps1000/1011,8/16 scratch headroom, and three forced/
  random measurement streams.
- Inverse-then-forward round trips using unchanged forward nonfused cells;
  a separate composition check enables the existing forward fused/top option.
- Active/inactive nested classical guards, unchanged source/sign/spectators,
  zero residual phase, every reset audited before execution and all scratch clean.
- Exact emitted-op byte equality for generic signed_add and forward nonfused
  apply when the inverse flag toggles, plus every mutable guard-failure fallback.
- Per-configuration raw emitted T, the independent-fair-measurement weighted
  count, native fixture executed-T average, and old/new helper peak Q. The
  complete inverse cell and its optional forward round trip are counted, not
  just a bare comparator. No numerical resource saving is claimed before this
  census runs.

An explicit outside-support COMPLETE inverse-cell witness is also tested:

    y=(p-1)/2, B=2^200+8, original sigma=1.

Doubling y gives A=p-1, at modular distance1 rather than>=V. The folded word is
B-1 with kappa=1. The full comparator is true and clears the old phase correctly;
the upper120-bit comparator ties and produces the predicted phase defect.
Both numerical outputs remain B-1. Native tests vary B's low word across64 lanes
and force/couple the original overflow measurement under three streams, requiring
old phase0 and narrowed phase equal to that measurement. This prevents a false
all-input channel-equivalence claim and shows why the doubled margin matters.

## Current status

Source parsing/format checks and scalar fixture algebra passed locally. No local
Rust build, circuit generation or quantum simulation ran. Prefix_arithmetic
independently confirmed the inverse theorem, flag independence, physical slice
and explicit outside-support witness. The component suite, cost census,
flag-off artifact identity and complete quantum regressions remain pending
remote execution under root's locked scheduler. Trusted harness files are
unchanged. No public submission is requested or performed.
