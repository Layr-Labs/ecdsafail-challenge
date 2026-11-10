# Grouped alpha step for the Q651 short divide (2026-11-10)

This folder documents one generator change on top of the Q651 construction of submission `7e88bf50`
(jackylee0424): the "alpha" step of the short divide (the load that follows the outer Euclid walk) is compiled once
per group of divisor heights instead of once per height. The idea and the code pattern are nasqret's
(`groupWindingHeights` in `q653-grouped/backend.cjs` of submission `3db0b38c`, reused in the 652 submission
`53d21251`); this is a port onto the Q651 divide, whose alpha step was rewritten by `div10-rewrite.cjs` and
`p-divide-d4.js` and therefore needs its own patch.

## Files

- `../midpoint-implicit-query-20261109/q651/group-alpha.cjs`: the source transform. It rewrites `outerloadJ`
  in the generated divide source. Anchors are checked (each must occur exactly once).
- `../midpoint-implicit-query-20261109/q651/p-group-alpha.js`: the overlay patch that applies it after the
  existing divide transforms; appended to `p-field651.js`.
- `alpha-diff.cjs`: differential test of the ungrouped against the grouped `outerloadJ` at the generator level.

## What the patch does

`D2Alpha` of the Q651 divide handles heights 127 and 128 itself (two count bits live in the output register
there) and calls `outerloadJ(..., t, t)` for every height `t <= 126`. Only those calls are grouped:

    {2:2, 64:3, 96:65, 112:97, 120:113, 124:121, 126:125}      key = compiled width t, value = lowest height lo

For a group `lo..t` the height flag is set when the divisor height is in `lo..t`, the divisor is used zero
extended to `t` bits, and the coefficient cells `u[h+1..t]` that belong to other data at height `h < t` are moved
(conditionally on the flag and on `v[j..t) == 0`) into divisor cells `v[t..2t-lo]`, which are zero for every height in
the group. This needs `2t - lo <= 127`. The table is nasqret's except that heights 125 and 126 form one group
(allowed by the same bound); 127 and 128 stay ungrouped because of the hosted count bits.

Static Toffolis of the alpha step per divide: 23,816,334 -> 4,094,910. Whole circuit: 638,962,281 -> 599,518,737.

## Test

    node --max-old-space-size=16000 alpha-diff.cjs <path to q651 dir> PASSES [variant]

The test builds both generators through the real `overlay.cjs`, records the gate lists of the alpha step for all
heights 2..126 on a local wire layout, and replays both on bit-sliced random states (32 states per pass), comparing
every wire. All registers are random except for the stated preconditions.

Results (variant `c` = the preconditions of the real circuit: coefficient below half the divisor, gap cell and
output register clean, flag clean; everything else random, including the cells above the gap and the borrowed
register):

| variant | states | result |
|---|---|---|
| `c` | 12,800 (at least 102 per height 2..126) | 0 mismatches |
| `co` (heights 1, 127, 128: the grouped circuits must act as the ungrouped ones) | 960 | 0 mismatches |
| `C` (coefficient above half the divisor: outside the contract) | 768 | 727 mismatches; the ungrouped circuit itself leaves its inputs changed in 508 |
| `ck`, `cj`, `cg` (dirty output register or gap: outside the contract) | 6,400 to 12,800 | mismatches; the ungrouped circuit itself leaves its inputs changed in 25 to 31% |

So the two circuits agree on the states that satisfy the contract of the ungrouped step, and on states outside
it the ungrouped step is already not a clean operation. The invariant `2u < v` is what I read from the outer walk (class `Reduced`, with its
"quotient is one" correction step); I did not prove it from the source, the evidence is the behaviour above. Random point additions only reach heights from
about 113 upwards (height `128-k` has probability about `2^-(k+1)`), which is why this test exists: it covers the
low heights that end-to-end tests cannot.

Limits: this is a randomized differential test, not a proof; it compares the alpha step in isolation, on a local
wire layout, and relies on the stated preconditions holding in the full circuit at all heights (they are observed
to hold on all end-to-end shots, which exercise the groups 126:125, 124:121 and 120:113).
