# Top120 forward fused overflow comparison

Candidate `fused-top-compare` is a separate copy of frozen `fused-rotation-cell`.
Only `src/point_add` changes. Enable `MIDQ_FUSED_ROTATION_CELL=1` together with
`MIDQ_TAIL_TOP_COMPARE=1`; the new option defaults off. Inverse signed-add and
all generic comparison helpers remain unchanged. No whole-circuit Q/T or native
validation result is claimed before remote execution.

## Support and guard

This uses the independently derived `TAIL_CANONICAL_SUPPORT_PROOF.md`, copied
unchanged into this candidate, and the predecessor's `FUSED_ROTATION_CELL_PROOF.md`.
The essential input hypotheses are exact ideal PZ transitions through cut360,
leading shifts of every begun division<=31, a positive handoff pair with maximum
below2^85, true normalization, and faithful tail sign/width/metadata transitions.
The canonical-support proof covers both initial257-bit cells, later256-bit cells,
and the final four checkpoint cells under those hypotheses. It does not cover
arbitrary standalone field words, lossy width-error states or all checkpoint
bit patterns.

`top_compare_eligible()` statically requires the new flag, fused/rotated/measured
modes, ping-pong tail enabled, cut360,224 tail rounds, all configured constant
value widths<=85, and shift-register width<=5. If any check fails, the original
full256-bit comparator is emitted. These checks only pin an eligible production
configuration; they cannot prove the quantum input satisfies positivity, exact
transitions or the coefficient-margin theorem. Actual circuit support membership
and frozen/independent regression remain mandatory. No new empirical width or
coefficient-margin cap is introduced.

## Predicate equality

Let M=2^256, p=M-F, F=2^32+977. The prior proof establishes a lattice coefficient
bound V>2^137 and min(a,p-a)>=V for each intended old target coefficient a, and
canonicality of the final forward output y. Its literal rotated double obeys

    D(y) = rotl1(y) + (F-1)*y[255]

without wrap. For subtract flag s and raw addition overflow kappa, the old
complemented-frame comparison gap is exactly:

| s | kappa | (D(y) XOR s*(M-1)) - b |
| ---: | ---: | --- |
|0|0|a|
|0|1|a-p|
|1|0|M-1-a|
|1|1|F-1-a|

Each has the proper sign to recover kappa. Its magnitude is at least V-(F-1).
Replacing D(y) by rotl1(y) changes the gap by at most F-1, hence the resulting
unsigned rotation-frame gap satisfies

    |(rotl1(y) XOR s*(M-1)) - b| >= V-2*(F-1) > 2^136.

Two256-bit unsigned integers with identical upper120 bits differ by at most
2^136-1. Therefore these operands have unequal upper120 bits, and their full
ordering equals the ordering of those high bits. Dropping exactly136 low bits
preserves the predicate pointwise on the certified support. The retained width
120 is theorem-derived; the larger empirical fixture margin is not used to
narrow it further.

The original overflow HMR remains, and its correction is now the high-bit
comparison phase oracle. Since that predicate still equals kappa,

    (-1)^(measurement*kappa) * (-1)^(measurement*predicate) = 1.

This proves coherent phase equality on any superposition of certified states,
including arbitrary entangled spectators. Numerical outputs are unchanged by
narrowing, but outside-support phase equality is explicitly NOT claimed.

## Exact wire mapping and implementation scope

The predecessor temporarily complements target bits by s and passes comparator
refs in little-endian order

    rotated = [target[255], target[0], ..., target[254]].

The new comparison uses `rotated[136..]`, which is physically
`target[135..255]`, against `source[136..256]`. Each slice has exactly120 wires.
Slicing the unrotated target at136 would be an off-by-one error. The inverse
comparator has a different unrotated frame and is deliberately left full-width.

`clear_rotated_overflow` is called only by forward `fused_rotation::try_apply`.
The generic `clear_borrow_compare_refs` implementation is not modified. The
narrow path receives a distinct count-profile section name ending in
`top120_compare`; section labels do not change circuit semantics. No persistent
qubit or arithmetic representation is added. Peak/T improvements still require
actual measurement because the comparator backend selects workspace strategies.

## Evidence and prepared tests

Local work was source parsing/formatting and scalar algebra only. On all512
unchanged certified predecessor fixtures, full comparison and top120 comparison
both equal the original carry. The four(sign,carry) cases occur120,108,150,134
 times respectively. The smallest observed rotation gap has183 bits. Fixture
hash and scalar results are recorded in `TAIL_TOP_COMPARE_ALGEBRA.json`.
Neither this fixture algebra nor the static guard is a whole-circuit membership
certificate.

Prepared native tests use the unchanged Simulator and existing pre-reset auditor:

- Full256 versus top120 fused cells for all512 certified fixtures, both256/257-bit
  interfaces,12/24 scratch headroom, and round trips through the UNCHANGED inverse.
- Three forced/random measurement streams, unchanged sources/signs/spectators,
  zero residual phase and all scratch clean before resets; active/inactive nested
  classical conditions are tested separately.
- A direct phase-oracle counterexample where lhs=2^200+6 and rhs=2^200+7. Full
  comparison is true but the high120-bit comparison ties. With the original
  overflow outcome coupled, tests require the predicted nonzero narrowed phase
  defect while keeping numerical values unchanged. This prevents treating the
  option as an all-bit-pattern identity.
- Full emitted comparator byte equality when each mutable configuration guard
  fails. The inherited rotation-only suite explicitly disables the new option
  to preserve its own documented outside-support phase oracle.

Remote command, through the existing locked scheduler:

    MIDQ_CELL_FOLDS_SELFTEST=1 MIDQ_TAIL_TOP_COMPARE_SELFTEST=1 build_circuit

Then compare `MIDQ_TAIL_TOP_COMPARE=0` and `=1` full artifacts with fused mode on.
Require off-mode bytes to match the frozen predecessor, no inverse/generic
comparison changes, actual operation-level support checks and frozen/independent
quantum regression, followed by the trusted complete benchmark. Source proof,
component resources and complete-circuit validation remain distinct evidence.
