# W1 one-use AND experiment (2026-10-08)

Baseline: promoted `94eae4a`, with 794,044.324 executed Toffoli per shot,
1,244 qubits, and score 987,790,736 in the official local `yukon run`.

In `leapfrog::fast_choice`, the nonconstant W1 branch computes
`g2 = g & (wq XOR !inv)`, toggles `out` with `g2`, then erases `g2` by
measurement and a phase correction. Since `g2` has no other consumer, an
equivalent Boolean toggle is `CCX(g, wq, out)` with an X conjugation on `wq`
when `!inv`. This removes the one-use quantum temporary and its measured
uncompute. The same rewrite was tested locally and then reverted.

The builder emitted 9,374,593 ops instead of 9,375,983, but reported the
same expected Toffoli count (794,105.0) and the same peak (1,244 qubits).
The official local validator reported 14 classical mismatches and 8
phase-garbage batches on the candidate's new Fiat-Shamir packet; therefore
it did not yield a valid score. Its actual average executed Toffoli on that
failed packet was 794,048.498. The exact local rewrite is not useful for
the scored product without a change at the global peak and a valid packet.

The built-in peak ownership census on the unmodified baseline found the
1,244-qubit peak at op 782,182 in `divide`. At that point 385 live wires are
stored fast-walk tape letters (231 from `s3/k1/k2`, 154 forced-step signs),
256 are the copied payload, 256 are the original `y` register, 125 are the
seed rail, 124 belong to the original `x` register, 95 are ripple carries,
and three are individual temporaries. The W1 one-use AND is outside this
peak, explaining why removing it did not lower the score.

The follow-up idea is to find an exact loan or earlier release among the
live tape, rail, and carry wires at this precise peak. Any such change
must be run through the full validator because the op-stream hash changes
the 9,024 input shots.

## Reorder/cap trial

I also tested `LF_REORDER=75` with `HEO_PIN_PP_WALK_MAX_QUBITS=1242`
against the promoted `77`/`1244` pair. The builder reported 795,564.5
expected Toffoli, 1,242 peak qubits, and 9,417,517 emitted operations.
Its expected product was 988,091,109, above the baseline builder product
987,866,620. The official local validator found 15 classical mismatches
and five phase-garbage batches. This pair is both costlier and invalid;
the recipe was restored to the promoted values.
