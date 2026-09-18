# 2026-09-12: The λ↔product middle ground, priced and closed (CPU rig)

Model: GLM-5.3 (ZCode harness). Question (user-supplied strategy): the 1258q
frontier config is max-levered (λ≈21) and GPU-only; does the never-priced
LOOSER direction contain a config whose `avg_exec × peak_qubits` still beats
the frontier 1,137,367,864 while λ ≤ 16 (CPU-grindable overnight)?

**Answer: no.** Every λ-buying knob costs 0.1–0.6% of product per λ-halving
against a total budget of 0.0003%, and the only product-buying knob found
(PP_SPLIT_FOLD=1) *sells* 5.8 λ. The shipped pins are the measured joint
optimum for product at grindable λ. Details below; all numbers from the exact
rig (`ecdsafail-grind`, 200-nonce probes, 32–37 draws/s, nonces ≥31338000000000).

## Baseline correction (important for lane bookkeeping)

The tree @ 9700396 is **1258q**, not 1259q: `PP_WALK_MAX_QUBITS=1258`,
`PP_FOLD_PROFILE=38:0,32:-2,19:-5,0:-5`, TAIL_NONCE=230915643996243 (a *clean*
diagnostic nonce, avg-exec **904,107.547** → score 904,108×1258 =
**1,137,371,464**, i.e. 3,600 above the frontier). The 903,434.197×1259 row in
results.tsv is the older a39e07e config (WALK_MAX 1259, profile −1/−4/−4).
Rig fidelity gate: pinned nonce reproduces clean, avg 904,107.547, 4.6 s/draw.

Consequence: `ecdsafail-grind/grind-state/target.txt` (**903394.64**) is the
stale 1259-lane target. At 1258q the frontier beat bar is avg ≤ 904,107.499
(=1,137,366,606). The default-config driver flags winners only below 903,394.64
— that is 14σ below the config's clean-avg distribution (σ≈50/nonce): **the
current driver can never flag a real frontier beat**. Update to 904107.49 if
that lane is ever revived (CPU EV is still ~zero, see grind-hours below).

## λ estimation pipeline (validated)

Per-batch tof is uniform across the 141 batches (shots are iid), so a draw
failing at batch `b` (0-indexed, tot_tof accumulated through `b`) prices the
full-draw avg as `141 × tot_tof / ((b+1) × 9024)`. On the shipped config the
median over 200 draws gives 904,110.8 vs the true clean 904,107.5 (+0.0004%).
λ̂ = −141·ln(1 − 1/(1+b̄)) with b̄ = mean first-fail batch (0-indexed);
channel split λ_cls/λ_ph proportional to fail counts. SE ≈ ±1.5 at n=200.
Per-nonce clean-avg spread σ ≈ 39–50 (so P(clean nonce beats frontier) =
Φ((μ−904,107.5)/σ) at 1258q — a *coin flip* per clean nonce at the shipped μ).

**Grind-hour arithmetic correction:** at the measured 32 draws/s,
e^λ/32 s gives λ=12 → 0.9 h, λ=14 → 9.6 h, λ=16 → **76.6 h (3.2 days)**.
"λ≤16 ≈ overnight" is off by ~6×; a true 13 h overnight needs **λ ≤ 14.05**.
The shipped λ=21.2 → 14,080 h (1.6 yr) per clean nonce: CPU grinding the
frontier config is confirmed zero-EV (matches the earlier 24-CPU-year park
verdict, now at the corrected baseline).

## Pricing table (200-nonce probes each; product = round(avg_med) × nq)

| config (env delta vs shipped) | nq | avg_med | product | vs frontier | λ̂ ±1.5 | verdict |
|---|---|---|---|---|---|---|
| **shipped pins** | 1258 | 904,110.8 | 1,137,371,638 | +3,774 | **21.2** (cls 17.7 / ph 3.5) | frontier point |
| `PP_WALK_MAX_QUBITS=1264` | 1264 | 900,456.1 | 1,138,176,384 | +808,520 | 22.6 | worse both axes |
| `PP_WALK_MAX_QUBITS=1273` | 1273 | 896,618.5 | 1,141,394,714 | +4.03M | 24.4 | worse both axes |
| `PP_WALK_MAX_QUBITS=1280` | 1280 | 895,310.8 | 1,145,998,080 | +8.63M | 21.3 | worse both axes |
| `PP_WALK_MAX_QUBITS=1250` | 1258(!) | CCX +1.32% | ≈+1.3% | ≈+15M | — | peak **blocked**: trailing-batch fold floor 1210+window(48) binds at 1258; going below needs profile/window narrowing (λ↑) |
| `FOLD_GUARD=28` | 1264(!) | 904,534.9 | 1,143,328,240 | +5.96M | 20.5 | λ_cls 17.4 — guard sites are **not** the classical λ; +6q side effect via f_slice=33+guard ladders |
| `PP_FLAG_WIDEN_DIV=696` | 1258 | 903,799.3 | **1,136,979,142** | **−388,722** ✓ | **26.7** | same pattern: product −0.035% bought with +5.5 λ |
| `PP_CUT_WALKLOAN=0` | 1258 | CCX +382 | ≈+0.04% | worse | — | un-cut restores pre-cut stream (tof↑, hair of λ back) |
| `PP_CUT_SQIDENT=0` | 1258 | CCX +30 | ≈+0.003% | worse | — | neutral |
| `PP_WIDTH_SCHEDULE` +1/round (259-capped) | 1260(!) | 908,418.1 | 1,144,606,680 | +7.24M | 20.0 | walk envelope holds only ~3.5 λ; +0.48% tof +2q |
| `PP_SPLIT_FOLD=1` | 1258 | 902,719.7 | **1,135,621,760** | **−1,746,104** ✓ | **27.0** | beats frontier −0.15%; every clean nonce wins (~32σ below bar); but λ +5.8 — even GPU-hostile (e^27 ≈ 500 GPU-days at 12.3k n/s) |
| `PP_ROUNDS_MUL=696` | 1260(!) | CCX +0.13% | ≈+0.3% | ≈+3.6M | — | +2q; convergence tail not a λ lever at this depth |
| `PP_FOLD_PROFILE` all-flat | — | build assert | — | — | — | invalid: trailing batch must start past the fold ramp; the −5 bands are what make the 1210+48 floor *meet* the 1258 cap (peak co-design) |
| `A5_REPAIR=off` | 1258 | CCX identical | =shipped | =shipped | (unmeas.) | Clifford-only knob; score-neutral |
| `SQ_SPLIT_*=33` | 1343(!) | — | — | — | — | Karatsuba depth eats +85 q of peak |
| `SQ_SPLIT_*=off` | 1258 | ops +25k | worse | worse | — | exact, tof↑ |

Width cliff note: 1258→1264 drops static CCX −0.77% but avg-exec only −0.40%
(cond-discount shifts, executed/static 0.9547→0.9582), so the apparent
"trade +q for −tof" cliff does not survive execution accounting, and λ rises
with r1's growth (1264: 22.6, 1273: 24.4).

## λ attribution (what the 17.7 classical actually is)

- Replay fold carry-escapes dominate: ~10–12 λ from the flat-window region
  (window 53/54, walk widths ≥38, ~1232 cells/shot; escape ∝ 2^-(window−33),
  damped by the measured per-band collapse at narrow walks). Buying one bit of
  window everywhere costs ~+1.2k tof **and** +1 peak (trailing floor) ≈ +0.2%
  product per halving of this share.
- Walk envelope overflow: ~3.5 λ (schedule+1 halves it, costs +0.48% tof +2q).
- Square/shell `FOLD_GUARD` folds: ≈0.3 λ total (guard 21→28 left λ_cls at
  17.4) — the 2^-guard sites are few and cheap; guard is a *peak* knob in
  disguise (f_slice ladders), not a λ knob at this setting.
- Phase channel 3.5 λ (flag/chunk compares, erase-compare residuals): killing
  all of it still leaves λ_cls ≈ 17.7 > 16.

## Why the middle ground is closed (the arithmetic)

Beat bar: product < 1,137,367,864 while the shipped config sits at
1,137,371,638 (+0.0003%). Budget for λ-buying: ≤ −0.0003% of product.
Cheapest measured λ rate: ~0.15%/product per halving of the fold-share
(windows) or ~0.3–0.6% per halving elsewhere. Reaching λ ≤ 16 (Δλ = −5.2,
roughly one halving of the fold share plus all phase λ plus the envelope)
costs ≥ +0.15% product — **500× the budget**; reaching λ ≤ 14 (true overnight)
costs ≥ +0.4%. No combination on the knob surface inverts this: the shipped
1258q point is the product optimum conditional on λ ≈ 21; λ is not a free
design choice *at the frontier*, only away from it.

## GPU playbook (first moves if GPU access ever returns)

Both frontier-beating configs below are single-env-delta, peak 1258, measured
at the median of 200 partial-draw estimates (estimator validated to +0.0004%
on the pinned nonce); each still needs a clean nonce + `eval_circuit` confirm
before any submission, and each costs ≈5.5 λ vs shipped, so both are
multi-GPU-month grinds, not CPU and not single-4090 jobs:

1. **`PP_SPLIT_FOLD=1`** → product **1,135,621,760** (−0.17%, beats by 1.75M),
   λ̂=27.0, avg_med 902,719.7 (σ≈44). Every clean nonce beats (median is ~32σ
   below the bar) — the grind is purely "find one clean nonce", no tail-riding.
   Note: islands never survive a config change; regenerate any checkpoint.
2. **`PP_FLAG_WIDEN_DIV=696`** → product **1,136,979,142** (−0.034%), λ̂=26.7,
   avg_med 903,799.3 (σ≈50); bar 904,107.5 → ~6σ below, so effectively every
   clean nonce beats as well.

Stacking the two is untested (their λ costs may not add; their tof savings
partially overlap the same erase sites) — price a combined probe first.


## Artifacts

- Probes: `ecdsafail-grind/probe/{p0-baseline,p3-wm1264,p4-wm1273,p6-splitfold,
  e3-guard28,e5-sched1,p8-wm1280}.jsonl` + `probe/analyze.py` (λ/tof/product
  analysis) + `probe/pad_schedule.py` (schedule padder).
- Padded schedule spec: `ecdsafail-grind/probe/` regenerates via
  `python3 probe/pad_schedule.py`.
- No repo source modified; no submission. The grind driver was found stopped
  (PAUSE file present, partial block 31337002000000); `grind-state/target.txt`
  was corrected to the 1258-tree bar 904107.49 (see README.txt there) — the
  grind itself stays stopped.

## If this is ever reopened

1. The only frontier-beating direction found is `PP_SPLIT_FOLD=1` (−0.17%
   product, every clean nonce beats) — it needs a ~e^27 grinder (multi-GPU
   farm or a better split-fold repair that keeps the wrap error bounded).
2. A CPU-competitive config would need a *structurally different* error site
   than the replay fold (its window is simultaneously the tof, the peak, and
   the λ). The 792–793q family (600–700× off product) is the only known
   CPU-easy regime.
3. Corrected threshold for "overnight on this M4 Pro": λ ≤ 14.05 at 32 draws/s.
