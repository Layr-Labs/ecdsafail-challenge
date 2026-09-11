# Proven floors — where the headroom is NOT

Each of these is a proof or an exact enumeration, not a failed search. Do not re-mine them.

## Controlled-permutation bucket — 545,969 CCX (39.2%) — CLOSED

Every item in the bucket is a **controlled GF(2)-linear map**: cswap ladders, cyclic shifts, conditional doubling
(shift + Solinas fold). Track, per wire, the bilinear `c(x)·v` component of its polynomial. CNOT/X move it linearly,
CCZ is diagonal so contributes nothing, and **each Toffoli adds at most ONE new vector to the span**. Therefore

$$\#\text{Toffoli} \;\ge\; \operatorname{rank}(M \oplus I)$$

over the reachable subspace. Ancillas — clean or dirty — do not lower the bound.

| item | floor | emitted |
|---|---|---|
| apply cswap | 256 | 256 |
| GCD cswap | n−1 | n−1 |
| GCD conditional shift | n−2 | **n−1** ← the only slack |
| apply conditional double | 256 | 256 |

Exactly **68 gates** in the whole bucket were removable (conditioned on ctrl=1 both `v[0]` and `v[w-1]` are zero, so
the last Fredkin swaps two zeros). Taken. That is the entire prize.

Related: the free-vs-conditional asymmetry is not an implementation artefact. An unconditional right shift is pure
SWAP relabelling and SWAP is Clifford, hence free in this cost model; a controlled n-cycle provably costs n−1 Toffoli.
That is the price of conditionality on a linear map and it is unavoidable.

## Adder bucket — 665,655 CCX (47.7%) — at best-known

Multiplicative complexity: each Toffoli contributes at most one AND to the ANF, so #CCX ≥ MC.

1. **Uncontrolled n-bit add**: `deg(c_{n-1}) = n`, so MC ≥ n−1. Achieved by `MAJ(x,y,c) = c ⊕ (x⊕c)(y⊕c)`, one AND per
   carry, Gidney temporary-AND erasure free. **Floor n−1, TIGHT, 1.00 CCX/bit.**
2. **Controlled add** `y += t·x`: two independent bounds both give n (degree, and a bilinear-rank argument on the
   restriction y=0 where the function becomes the n-fold fan-out `t·x_i`). Best known is **2n** — Gidney 2018,
   *Halving the cost of quantum addition*, 8n+O(1) T. Both natural decompositions land on 2n−1 and neither improves,
   because the carry-recursion gates all have zero degree-2 contribution and are necessarily disjoint from the n gates
   the rank bound forces. **Proven floor n, achieved 2n, factor-2 gap OPEN — that is a publishable result, not an
   engineering task.**
3. **Controlled modular add mod p**: for a CLASSICAL addend the required degree-2 forms are linear, so the rank bound
   gives zero and only the carry recursion is nonlinear → floor ~n−1, half the quantum-addend case. This is why the
   Solinas fold is cheap.

Measured: GCD body **1.971 CCX/bit** = 2n, already at it. The apply register phase ran 2.767 CCX/bit because it took
the chunked path; that gap is what we took.

**Why 2n is unreachable at k<n in the chunked path** (this is the load-bearing bit): the free measurement uncompute of
carry `i` requires ancilla `c_i` live AND register bit `i−1` still raised; unraising bit `j` needs `c_j`. That mutual
dependency means the vent window provably cannot slide, so vents cost exactly 1 qubit per bit and (n−k) bits must pay
the boundary. Cost is exactly `2n + 1 + l + m` — verified to the Toffoli at 14 separate k values with zero residual,
and it is the code's own objective at `gidney.rs:1517`.

## Dialog codec — 602 qubits — CLOSED, within 2 qubits

Exact BACKWARD enumeration from the pinned terminal state (u=1,v=0). The forward map `state_i → (symbol_i, state_{i+1})`
is a function, so the backward relation is injective and the enumeration is a tree: **nodes at depth k = distinct
reachable k-suffixes exactly.**

$$c_k = \frac{5^k + 1}{2} \quad\text{exactly for } k \le 8$$

Proof of the recursion: backward, `swp=1` forces `v2=u'` and `u=v'+u'`; consistency needs `u' < v'+u'`, which at
(u',v')=(1,0) is `1<1`, false. So both swp=1 symbols are unreachable from the terminal chain, giving
`c_k = 5·c_{k-1} − 2`. **That factor of ½ IS the entire capturable slack and it is worth exactly one bit, forever.**

Bits saved at codec-aligned k = 2,5,8,11,14,17: **1,1,1,1,1,2**. Max capturable = 2 qubits at k=17, requiring a 38-bit
reversible bijection over 2.4e11 elements. No.

Sampling at 1e8 walks confirms all `5^k` windows are reachable at every interior start index for k≤9. The only
structural unreachability anywhere in the tape is step 0 (already optimally coded, 2 bits for 3 values) and `swp=1` at
i=257 (0 occurrences in 2e8, and proven — which is why `TLM_APPLY_INV_CSWAP_SKIP_LAST=1` is free).

## Jump radix — optimal

Walk cost: JUMP=1 ≈ 729k, **JUMP=2 ≈ 624k**, JUMP=3 ≈ 655k CCX. K≥3 adds a conditional-shift and conditional-double
layer costing about what the fewer steps save (only ~12% of steps strip a third zero).

## Dead-gate census — OVER-drawn, not dry

At 1e9 inputs (1,000,089,600, 150 shards, disjoint seeds): only **1,290** of the shipped 1,442 keys are still
never-firing, 153 shipped keys actually fire, and exactly **ONE** genuinely new never-firing gate appears. A fire-census
dead set is monotone decreasing in depth, so deeper censuses can only shrink it.

Keeping the 153 that do fire costs ~153 × 2e-9 ≈ 0.003 expected mismatches — an excellent Toffoli/error trade, so they
stay stripped.

The orthogonal lever that IS productive: the right predicate is `cond & q1 & ~q2 == 0` (q1 implies q2), strictly weaker
than "q2 always 1" or "controls always equal", and the substitution `CCX→CX` is an identity wherever it holds — zero
error, unlike a strip entry. That yielded 1,193 → 2,050 downgrades on the re-mine.

## CCZ straddle cancellation — dead code, provably

`same_triple_candidates=0` is not a matching bug. Every CCZ is emitted alone inside its own
`push_condition(fresh measurement bit)` (gidney.rs:1303/1371, arith.rs:620/659), so no two CCZ share a condition
context and `CCZ_b1 · U · CCZ_b2` is not the identity. Replacing epoch equality with exact condition-stack interning
(strictly more permissive, still sound) still gives 0 pairs over all 5,299 CCZ.

CCX generalisation ceiling, measured: of 1,392,850 CCX there are 1,071,517 consecutive same-(target,controls,guard,
context) pairs, but 1,071,117 die on the target being READ in between — irreducible, since a compute/uncompute pair
whose AND is consumed is doing real work. True prize = 388 pairs = 776 CCX = **0.056%**, and it needs a wire-EQUALITY
analysis that constprop's affine pass already fixpoints on.

## Qubit side, as measured PRE-tripwire (see notes/05 — I now distrust these)

Apply-deferral works and is correct (full 9024: 15 classical / 12 phase) and moves the structural floor 1149 → 1134,
but costs +9.2% Toffoli. Stated ceiling of the entire qubit workstream: −1.56%, unreachable.

**Caveat that matters:** these were measured while the certificate machinery was silently corrupting perturbed
streams. Re-test before believing them.
