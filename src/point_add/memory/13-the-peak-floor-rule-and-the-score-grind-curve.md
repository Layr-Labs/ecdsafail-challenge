Model: Claude Opus 5, high effort. Harness: Claude Code.
Single Apple M4 laptop (10 CPU cores). No cloud, no GPU.

# The peak-floor rule, and five configurations that beat the frontier

**TL;DR**

1. The peak qubit count is not a mystery and not a property of the clever
   mechanisms the current release note credits. It obeys
   `peak = max(governor, 1210 + PP_REPLAY_FOLD_WINDOW + band_offset)`, and each
   qubit below 1260 costs **one more bit off every lower fold band**. Verified
   over a 20-point grid.
2. `PP_WALK_MAX_QUBITS` (the governor) is **exactly lambda-free**: -666.18
   executed Toffoli for a qubit, `d_lambda +0.000 +/- 0.000`, failing-shot sets
   bit-identical. All of the grind cost of a lower peak is the fold narrowing
   that unlocks the floor, none of it the qubit.
3. Five configurations beat the live frontier, forming a measured score-vs-grind
   curve from -0.0177% at 1.26x grind to -0.2050% at 131x. All are environment
   values against the frontier source; no circuit code is changed.
4. The single best value is **`D695`** -- drop one round from the 8-wide tail of
   `PP_WIDTH_SCHEDULE` -- worth **-0.0527%**, four times the margin the frontier
   itself won by, at 1.83x its grind.
5. `PP_FOLD_WIDEN` is the only peak-neutral lambda purchase in the tree. Fold
   windows, multiply rounds and walk-width widening all break the peak.

---

## 1. What the frontier's qubit actually came from

The promoted Q1259 submission credits four exact op-stream simplification passes,
a walk-adder carry loan and square low-stage identities. Measured here, none of
them buys a qubit:

| change | realized Q | emitted CCX vs shipped |
|---|---|---|
| `PP_CUT_SQIDENT=0` | 1259 | +36 |
| `PP_CUT_WALKLOAN=0` | 1259 | +372 |
| both off | 1259 | +403 |
| `PP_SIMPLIFY=off` | 1259 | +18 |

The four passes remove **16 ops out of 12,267,299** as shipped (`product` 16;
`affine`, `quadratic`, `truth` zero each). The qubit comes from exactly two
values: the fold profile's `19:-3 -> 19:-4` bit and the governor `1260 -> 1259`.
Reverting the profile bit alone restores Q1260.

`REVBOTH` (both reverted) measures `dT -598.05 +/- 1.34` and scores
1,137,579,498 -- reproducing the *previous* frontier's 1,137,575,880. So their
"+600 T for the qubit" claim is exactly right, and the instrument is calibrated
against a second independent point.

## 2. The floor rule

| governor | profile | realized Q |
|---|---|---|
| 1259 | `38:0,32:-1,19:-3,0:-4` | 1260 |
| 1259 | `38:0,32:-1,19:-4,0:-4` (shipped) | 1259 |
| 1258 | `38:0,32:-2,19:-5,0:-5` | **1258** (minimal) |
| 1258 | `38:0,32:-2,19:-4,0:-5` | 1259 |
| 1258 | `38:0,32:-2,19:-5,0:-4` | 1259 |
| 1258 | `38:0,32:-1,19:-4,0:-5` | 1259 |
| 1258 | `38:0,32:-2,19:-4,0:-6` | 1259 |
| 1258 | `38:0,32:-2,19:-3,0:-5` | 1260 |
| 1257 | `38:0,32:-3,19:-5,0:-6` | 1258 |
| 1257 | `38:0,32:-3,19:-6,0:-7` | **1257** |
| 1257 | `38:-1,32:-3,19:-6,0:-7` | **1257** (cheaper in CCX) |

Every lower band must move together; leaving any one shallower lands one qubit
higher, and going deeper than the minimum buys nothing. The governor never
realizes on its own -- it is a cap, and the profile is what lowers the floor
beneath it.

Band populations, which set the lambda price: `>=38` is 616 rounds, `32..37` 16,
`19..31` 31, `<19` 33. The two tail bands are the same size, so a shallower
profile saves lambda by narrowing **fewer bands by fewer bits**, not by hitting a
smaller band. A fold fails at ~`2^-(w-33)`, so one bit shallower halves that
band's channel: the minimal 1258 profile measures `d_lambda +0.625` against
`+1.375` for the `-6/-6` profile -- the predicted halving -- while costing more
Toffoli (`dT +672.78` vs `+541.10`), because a shallower narrowing saves fewer
gates.

## 3. The score-grind curve

All paired over the rig's 48 frozen input draws; `d_score` is against the graded
frontier 1,137,423,406.

| config | d_score | grind factor | local grind |
|---|---|---|---|
| `D695_FW400` | -0.0177% | **x1.26** | ~71 d |
| `D695_FW300` | -0.0399% | x1.55 | ~87 d |
| **`D695`** | **-0.0527%** | x1.83 | ~102 d |
| `Q1258B_D695` | -0.0583% | x3.42 | ~192 d |
| `Q1258_D695` | -0.0720% | x7.24 | ~406 d |
| `Q1257_D695` | **-0.2050%** | x130.97 | ungrindable on one machine |

where `D695` shortens `PP_WIDTH_SCHEDULE`'s 8-wide tail run by one
(`...,9x4,8x9` -> `...,9x4,8x8`), `Q1258B` adds
`PP_WALK_MAX_QUBITS=1258 PP_FOLD_PROFILE=38:0,32:-2,19:-5,0:-5`, `Q1257` uses
governor 1257 with `38:-1,32:-3,19:-6,0:-7`, and `FWnnn` sets `PP_FOLD_WIDEN`.

`Q1257_D695` is worth stating separately: **-0.2050%, fifteen times the margin
the frontier won by**, at `d_lambda +4.875`. It is a dominant submission for
anyone holding fleet compute and out of reach for a single laptop. It is free for
the taking.

## 4. The lambda market, priced

Selling lambda (gaining score):

| sale | dT | d_lambda | rate |
|---|---|---|---|
| first divide round (`D695`) | -475.87 +/- 1.28 | +0.604 +/- 0.118 | **788 T/nat** |
| one multiply round (`M693`) | -356.15 | +0.729 | 488 T/nat |
| three more divide rounds (`d693m693`) | -1,538.8 | +2.917 | 459 T/nat marginal |
| five more (`d691m691`) | -2,964.5 | +7.105 | 340 T/nat marginal |

Lambda is sharply **convex** in depth, so only the first divide round clears the
purchase rates. Buying lambda, and this is where nearly everything dies:

| purchase | d_lambda | peak? |
|---|---|---|
| `PP_FOLD_WIDEN` 242->400 | -0.375 for +316 T (843 T/nat) | **neutral** |
| `PP_FOLD_WIDEN` 242->616 | -1.083 for +748 T (690 T/nat) | **neutral** |
| `38:` band +1 | -1.354 for +1,228 T (907 T/nat) | **neutral** |
| `PP_REPLAY_FOLD_WINDOW_MUL` 55 | -0.688 | breaks to Q1260 |
| `PP_REPLAY_FOLD_WINDOW_MUL` 56 | -0.917 | breaks to Q1261 |
| a multiply round at Q1259 | -0.708 | breaks to Q1260 |
| a multiply round inside Q1258 | -0.708 for +476 T (672 T/nat) | neutral |
| `PP_WIDTH_SCHEDULE` +1 bit, all rounds | -- | breaks to Q1260 |
| `PP_WIDTH_SCHEDULE` +1 bit, last 100 only | -- | breaks to Q1260 |
| `PP_WIDTH_SCHEDULE` +2 bits | -- | breaks to Q1263 |

The walk holds 16.15 of the 19.31 classical nats and is therefore the largest
lambda pool in the circuit, but it **cannot be tapped**: the walk registers are
live across the peak plateau, so any extra width is extra peak, even on the last
hundred rounds. That is why the shipped configuration sits where it does.

`PP_FOLD_WIDEN`'s marginal rate *improves* with more widening (610 T/nat between
400 and 616), but a round trip against `D695`'s 788 T/nat sale is roughly
break-even, so it buys grind time rather than free score.

## 5. Method notes

* **Never price a qubit move off emitted CCX.** The marginal executed/emitted
  ratio is 0.40-0.48, not the 0.955 average: Q1258's +1,362 emitted is only +541
  executed, and the Q1259 move's +1,260 emitted is +598. Pricing a Q move at the
  average ratio makes a winning trade look like a 0.054% loss. I made exactly
  that error and only caught it by measuring.
* Use paired frozen draws. `d_lambda` on the first divide round is
  `+0.604 +/- 0.118` paired against `+/- 0.87` from differencing arm means -- a
  5x tighter interval from the same 48 draws.
* The lambda decomposition at head is `19.312 +/- 0.62` classical =
  **walk 16.146 + truncation windows 3.166**, from a REF_W arm with every base
  window widened and the band shapes left shipped. A flat `PP_FOLD_PROFILE`
  trips the plan assertion via `fold_ramp_start`.
* A razor-thin score margin is the **expensive** choice, not the cheap one: the
  graded average has sd ~6.5 T per draw, so a winning draw must land below
  903,434.197. At `dT = -108` you are 16 sd clear and every clean draw
  qualifies; at `dT = -5` only about half do, which is ~+0.7 nats of grind.
* Do not infer a band mechanism from a partial grid. Two claims in this session
  ("the 19: band is irrelevant", "the tail band is cheapest because it is
  smaller") were wrong on partial data and had to be withdrawn.

## 6. What is still open

* Nothing peak-neutral buys lambda cheaply enough to make `Q1258B_D695` or
  `Q1257_D695` locally grindable. Either needs a genuinely new construction that
  reduces the walk channel without widening live registers.
* The walk channel's 16.15 nats remain the prize. A screener addresses it only
  up to 67% coverage (`lambda_model 10.750` of 16.146, zero false rejections over
  433,152 shots), and the two phase compares are invisible to any value model by
  construction, so ~3.1 nats always needs the full 9,024-shot verify.
* The grind itself is the only thing between any of these and a promotion:
  1.7e9 draws at 22.89 ms is ~10,750 core-hours, ~56 days on eight threads, and
  each configuration above multiplies that by its grind factor.
