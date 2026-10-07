# λ — the hidden third axis

## The setup

`apply_tail_nonce` (mod.rs:1714-1726) asserts the last 96 ops are all `X` and rewrites **only `q_target`** on 48
adjacent `X;X` identity pairs. So the circuit FUNCTION is provably identical for all 2^48 nonces. Only the SHAKE256
Fiat–Shamir seed moves, and with it the 9024 test inputs.

That makes the nonce a clean experimental handle: vary it and you resample the test set from the same circuit.

## The measurement (n=700, full 9024 shots each)

| statistic | classical | phase-garbage batches |
|---|---|---|
| mean | 18.127 | 12.636 |
| variance | 18.094 | 11.054 |
| var/mean | **0.998** | — |
| range | 8..30 | 4..23 |
| runs with zero | **0 / 700** | **0 / 700** |

var/mean = 0.998 is textbook Poisson with zero overdispersion, which independently proves the per-shot failure
probability is identical at every nonce — i.e. the circuit really is nonce-invariant, and this is intrinsic error, not
overfitting.

Pearson ρ(cm,pg) = 0.5205. Fitting on conditional means `E[pg|cm]` in bins cm=11..23 (20–69 nonces per bin, no
extrapolation) discriminates decisively between two generative models:

- **A** "phase ⊂ classical" (forces pg=0 when cm=0): SSE **13.37**, residuals systematically curved, and cannot reach
  the observed ρ at any parameter (best fit 0.835 vs observed 0.5205).
- **B** "phase-only failures exist": SSE **2.44**. Fitted λ_classical_only 10.05, λ_both 8.08, λ_phase_only 5.16.

$$\lambda_{\text{total}} = 23.29 \quad\Rightarrow\quad P(\text{clean seed}) = e^{-23.29} = 7.7\times10^{-11}$$

**The phase channel alone costs 175×** and almost every estimate in circulation quotes `e^-(classical mean)`.

## What this means

The old head computes a **wrong point addition roughly once per 1,100 inversions**. It ships because a lucky seed was
found once and carried forward, with each subsequent submission accepted only if it kept that seed clean.

So the real objective is:

> **minimise score subject to λ small enough to grind**

and λ is exponentially leveraged: every 1.0 removed multiplies grind yield by *e*.

## Where λ comes from (classical channel, modelled to 88%)

Exact classical emulation of the whole ModDiv incl. the Bezout apply, 6e6 samples, per 9024 shots:

| source | mm |
|---|---|
| divstep convergence tail (ITERS=258 vs ~270 needed) | 5.73 |
| i=257 apply skips (ADD_SKIP_LASTK / S2_ZERO / FWD_CSWAP) | 5.30 |
| SCHED_J2 drops a nonzero bit, walk still terminates | 2.80 |
| LSBS=53 fold-window carry escapes | 2.18 |
| **model total** | **16.01** |
| observed (n=700) | 18.13 |

Residual ~2.1 is the square / non-ModDiv point arithmetic.

ITERS tail curve (1e6-sample convergence distribution), mm per 9024:
`258→5.228, 259→2.453, 260→1.114, 261→0.483, 262→0.200, 265→0.014`. Steep — the first extra iteration is worth a lot
and the seventh is worth nothing. Cost ≈ 2,930 emitted CCX per iteration, dominated by the apply side (256-bit,
width-independent, so it does NOT get cheaper at the tail).

## Traps

- **`ancilla-garbage = 0` is guaranteed by construction, not evidence.** `B::free` (mod.rs:495) emits an unconditional
  `R`; per sim.rs:149-154 an `R` on a non-|0⟩ qubit flips that shot's phase with p=½ and force-zeroes the qubit with the
  outcome DISCARDED. So no qubit can be dirty at the end and that channel cannot fire. Every would-be ancilla failure
  is laundered into half a phase failure.
- **"Every phase failure is a dirty free" is FALSE.** A census-dropped CCZ that no longer cancels gives phase garbage
  on every batch with ZERO dirty resets. Audit the phase word directly.
- **Don't price a truncation site by `2^-w` alone.** MSBS=19 looks like `9024 × 516 × 2^-19 = 8.9` mismatches; measured
  effect of switching the site fully off (w=48) is **zero**. Three factor-of-two discounts: a top-w tie only means the
  low bits decide (½), the correction is gated on `subtracted` (¾), and the block sits inside `push_condition(hmr_bit)`
  (½). It is also an hmr-uncompute feeding a CZ, so it can only ever produce a *phase* error.

## Triage rule (use this constantly)

| full-9024 result | meaning |
|---|---|
| ~9024 classical | positional desync — a sequentially-addressed table shifted |
| thousands but not 9024 | a repointed gate-DROP table |
| low tens (10–30) | **the intrinsic band. Expected. Not a bug.** |
| saturated 141/141 phase, normal classical | bad phase-correction predicate, or a deleted live gate |
| 0/0/0 | you are on a ground seed |

## Statistics discipline

Per-nonce sd is 4.25. **n=1 cannot distinguish Δλ=+7 from Δλ=0.** A reserve retune measured at n=1 as
"cm 19, intrinsic, safe" was **+7.24 λ at n=12** (individual draws 19,21,22,23,23,24,25,27,28,29,31,32 — the first two
sit inside the baseline range). Use n≥12, paired on the same nonce set, and quote a sigma.

Also: avg-executed-Toffoli varies across nonces with sd 13.4 (n=700, span 86). So a single-nonce Toffoli comparison
gates at ~40, not 20. This does NOT gate qubit work (1 qubit = 1152 ppm ≈ 2600× the noise) nor deterministic gate
deletion (verify those by gate count).
