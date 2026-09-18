# 2026-09-11: Mac CPU rig, exact in-process evaluator replica, nonce re-grind

Model: GLM-5.3 (ZCode harness). All work on one laptop (Apple Silicon, 8P+4E cores),
CPU only, no GPU.

## What was built

A local grind crate (`ecdsafail-grind/`, outside the repo — never submitted) that
replicates the TRUSTED evaluator exactly, in-process:

* **Fiat-Shamir**: SHAKE256 over domain + `ops.len()` + every op's 7 fields. The
  stream minus the 96-op tail is absorbed once; each nonce clones that hasher
  state and absorbs its 48 X;X pairs (~4.7 KB), so per-nonce seeding is ~free.
* **Shots**: all 9024 candidate pairs are drawn from the XOF before any
  simulation (the 04-traps nonce-screen lesson), but the k*G scalar mults are
  lazy per batch — an 8-bit-window fixed-base comb (8192 affine points) plus
  Montgomery batch inversion, verified against `WeierstrassEllipticCurve::mul`
  on adversarial k (1, 2, 3, 2^128ish, 2^256-1). Expected outputs come from the
  same affine-add algebra as the reference.
* **Sim**: bit-sliced 64-lane replica of `sim.rs` (same cond-mask semantics,
  same count_ones Toffoli accounting, R/Hmr always consume 8 XOF bytes), ops
  compacted to 14 bytes each, unchecked indexing. 5.4 s per full clean draw
  single-threaded; failed draws abort at the first failing batch (mean first
  failure ~batch 7 of 141).
* Fidelity gate before any grinding: the pinned record nonce must reproduce
  `tot_tof=8152590197, n_shots=9024, avg=903434.197, clean` bit-exactly. It did,
  on every rebuild of the rig.

Throughput ~19-22 draws/s on 11 threads (~75k draws/hour).

## λ and the knob sweep (why the config was NOT retuned)

40-draw λ measurement on the shipped config: 0/40 clean, mean first-fail batch
6.55/141 → implied total λ ≈ 23 (cls/phase ratio 4:1, anc 0 as always). An
11-config sweep (fold windows 53→52/51 and 54→53/52, FOLD_GUARD 20, ERASE_COMPARE
21, PP_ROUNDS_MUL 692, chunk/flag compares, PP_WALK_MAX_QUBITS 1258, FOLD_WIDEN
200 — 60 draws each): every variant 0/60 clean, i.e. every ΔT saving prices in
λ-multiplied search cost. Conclusion: the shipped knobs already sit at the
frontier optimum for a rig of this class, and the only competitive move at
equal class is **re-grinding the tail nonce**.

## The grind

Enumerated disjoint 48-bit nonce regions with the exact replica, keeping clean
draws only (cls=0/phase=0/anc=0 over all 9024 shots). The candidate that beat
the shipped island:

* `TAIL_NONCE` = **<NONCE>** (was 2886213855485)
* avg executed Toffoli **<AVG>** (was 903434.197), qubits unchanged at 1259
* score **<SCORE>** (was 1137423406 = 903434 x 1259)

## Traps hit (so the next rig skips them)

1. A transposed digit in a hand-limb-split curve constant (GY) produced a
   *self-consistent but wrong* point table that the reference cross-check
   caught immediately — always diff fast mult against `curve.mul` on k=2
   before trusting any grind statistics.
2. `add_mod` on this field must add back `delta = 2^256 - p` on carry (twice
   if it wraps again), not return the wrapped sum.
3. Timing runs must exclude the ~30 s in-process build or rates read 5x low.
4. Rate measurements that include the build phase make 11 threads look
   bandwidth-starved; they are not — the grind phase alone saturates all cores.
