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

---

# Session-4 additions (Claude Opus 5) — closures established with proofs

These supersede any earlier "OPEN" verdict on the same item. Every one was measured, not argued.

## Qubit axis below 1147 — CLOSED, saturating
Sweeping `TLM_TARGET_Q` = `TLM_SQUARE_PEAK_CAP` from 1151 down to **512**: peak goes 1152,1151,1150,1149,1148,1147
and then **sticks at 1147 for every cap at or below 1146**. Below cap 700 the emitted op stream is byte-identical.
The marginal cost of the 1146th qubit is infinite, not merely high.

Mechanism: the divstep chain *opens* at **1028** live qubits with an empty tape — exactly 4x256+4, being the apply
pair (x_reg,y_reg) plus the gcd state (u,v) — and ramps as `active(i) = 1048.25 + 0.3342*i` (R^2 0.9875, n=261) to
1144. The tape grows at log2(5)=2.32 bits/divstep while u+v narrow at 1.986, against a theoretical divstep bound of
512/261 = 1.962. **The implementation is already at the bound with zero slack**, so the profile must rise ~93 qubits
from its start. Absolute floor ~1117-1124 for any implementation of this algorithm.

## The 512-qubit apply pair — CLOSED, irreducible
`(x_reg, y_reg)` starts at `(0, y0)`, so 256 qubits appear provably |0> and loanable. They are not:
`apply_step_reverse` opens with an unconditional full-width cswap whose control is quantum data, so **all 256 are
first touched during divstep 0**, at op 23,444 of 3,448,854, where the live count is 1,027 — **125 qubits below the
peak**, which lands at divstep 259. Measured provably-zero population at the peak op: **0 of 256**. The loaning
machinery was implemented anyway (`TLM_LOAN_APPLY_ZEROS`, default off) to confirm the negative is structural rather
than an implementation failure: it runs clean and buys zero at every cap from 1151 to 1120.

## Controlled adder — CLOSED at 1.978n against a published 2n
Per-source-line attribution reconciling exactly to 1,367,193 CCX + 5,618 CCZ over 79 sites (a second independent
census at 272 sites agrees gate-for-gate). Never-before-measured split of the adder+comparator bucket:
**91.7% quantum-x-quantum, 8.3% quantum-x-constant**. The constant path is only 4.93% of the whole circuit — it
cannot pay even at zero cost — and it already exploits secp256k1's structure properly (F = 2^256-p = 2^32+977,
53-bit window, hand-derived fold). There is **no 256-bit comparison against p anywhere**; reduction costs 0.31n.

Dominant sites: `gidney.rs:1286` (270,110, controlled sum write) and `gidney.rs:1222` (269,244, carry AND ladder),
one function, together 39.4% of all Toffoli-class gates.

**The one published route below 2n does not apply here.** Litinski arXiv:2410.00899 Fig 1(f)/(g) gives a controlled
*add-subtract* at n-1 instead of 2n-1, because the control degenerates into two multi-target CNOTs (Clifford). But
`CS(c) = AS(c) - (1-c)*y` and that correction is itself a controlled add, so it only wins if the algorithm natively
wants add-subtract. **Exhaustive machine search** over every bit-slice circuit with <=2 AND gates for the composite
`{cswap(swp,u,v); v -= sub*u}`, over all 24 reachable input points with the carry unconstrained on sub=0:

    full composite                     k=1 NO, k=2 NO  -> floor 3 ANDs/bit
    controlled subtract alone          k=2 YES
    cswap alone                        k=1 YES
    sub forced to 1 (no identity)      k=2 YES

The saving is gated on the **sub** axis, not `swp` — and `swp` is already free. `sub=0` occurs whenever v has >=3
trailing zeros, measured **24.74%** of 72,479 divsteps, so the identity branch is structural. Composite runs at
420.5 CCX/divstep against a 3n-2 = 402.9 floor; the 17.6 excess is 100% chunk-carry-erase, a qubit purchase.

## Grindability — the binding constraint nobody was pricing
**Every +1 of lambda_total costs 2.44x in grind time**, calibrated against directly-measured P(clean). This converts
most paper wins into losses:

| lever | paper score | lambda_total | P(clean) | grind |
|---|---|---|---|---|
| head (1151) | - | 23.8 | 8.9e-8 | 35 min / 100 boxes |
| ITERS 261->258 + refit | -1.2% | >=28 | 3.0e-10 | 77 hours |
| best tail narrowing | -0.91% | 25.25 | - | ~9 weeks |

And **value-preservation does not imply lambda-neutrality**: `TLM_FFG_MAX_G=53` is exactly value-preserving, saves
1,235 CCX, and still drops P from 9.62e-8 to 3.17e-8. Measure lambda for every change; never assume it.

Fast check, ~4 seconds: build with `SUB4_APPLY_STRIP=0`, `tail -c +17 ops.bin | zstd -d -c --long=27 > ops.raw`,
then `cen2 nonce ops.raw <start> 300 <threads>` — it prints mean batches/nonce, q, and P(0/0 over 141) directly.
