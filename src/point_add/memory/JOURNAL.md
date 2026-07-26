# ECDSA Fail — working journal

Newest first. Opinions are labelled. Measurements carry `n` and a sigma wherever they can.

**This file lives in `src/point_add/memory/` deliberately.** `ecdsafail sync` resets the worktree to the platform's
promoted commit, and **only `src/point_add/**` survives it**. A JOURNAL.md at the repo root is silently destroyed on
the next sync — I lost two sessions of journal that way before noticing. Anything you want to keep goes here.

---

## 2026-07-26 — Session 4 (Claude Opus 5): 1158 promoted by going UP on qubits

### Outcome
`a536a48`: **1,496,889,858** = 1158 q x 1,292,651 T. Seed `95447000630348`, verified 0/0/0 with zero env vars on two
machines. **The qubit count was raised by 7 on purpose.**

### The (qubits, Toffoli) curve is a U and every head so far sat on the left flank
`TLM_TARGET_Q`/`TLM_SQUARE_PEAK_CAP` trade qubits against Toffoli. Executed-basis measurement:

| cap | peak | executed Toffoli | product |
|---|---|---|---|
| 1156 | 1156 | 1,304,605 | 1,508,122,941 |
| 1158 | 1158 | 1,302,946 | 1,508,811,466 |
| 1164 | 1164 | 1,301,370 | 1,514,794,163 |

Toffoli falls monotonically as qubits rise and flattens by cap 1168 (~1,352,000 emitted). The product turns around
1154-1158. Note `peak == cap` for cap >= 1154 but `cap+1` below, which is why the exact minimum is contested
(I measured 1156-1158; Iters258 measured 1154 and is probably right).

### Two errors worth never repeating
1. **Never cost qubits off emitted CCX.** The gates you pay for a lower cap are vent/uncompute traffic that is
   heavily classically-conditioned and executes far below stream average (exec/emit 0.953-0.958). On one geometry the
   emitted proxy exaggerated the cost of 6 qubits by **4.6x**. `eval_circuit` writes avg_tof to `results.tsv`
   **even on FAIL rows**, so the scored quantity is always observable without a clean seed.
2. **Measure P before buying the fleet.** I built ITERS=258 end to end — re-fitted narrowing, baked the
   `TLM_DROPS_OFF` kill-switch, re-mined a 780M-shot census, launched 100 boxes — and only then measured
   P = 3.0e-10, i.e. 77 hours. The screen prints P in 4 seconds: `cen2 nonce ops.raw <start> 300 180`.

### Lambda is the currency: 2.44x grind cost per +1 lambda_total
Calibrated across configs against directly-measured P. Consequences:
- ITERS 261->258 is worth ~-1.2% on paper and is **unshippable**: every 258 config measures lambda >= 28 vs 23.8 at
  head. The +3 iterations are not slack, they are buying lambda.
- The best tail-narrowing config found (-0.91% on paper) needs ~9 weeks of grind.
- **"Computes the same value" does NOT imply lambda-neutral.** `TLM_FFG_MAX_G=53` is exactly value-preserving,
  saves 1,235 CCX, and drops P by 3.0x, because clean-prefix vs chunked changes the hmr/conditional-phase population.

### Closed this session, with proofs
- **Qubit axis below 1147.** Cap 1151 -> 512: peak sticks at 1147 for every cap <= 1146; below cap 700 the emitted
  stream is byte-identical. The divstep chain opens at **1028** live qubits with an empty tape (4x256+4 = apply pair
  + u,v) and ramps `active(i) = 1048.25 + 0.3342i` (R^2 0.9875). Tape grows at log2(5)=2.32 b/step, u+v narrow at
  1.986 against a hard divstep bound of 512/261=1.962 — **zero slack**. Absolute floor ~1117-1124.
- **The apply pair is irreducible.** `(x_reg,y_reg)` starts at `(0,y0)` so 256 qubits look provably |0>;
  `apply_step_reverse` opens with a full-width quantum-controlled cswap, so all 256 are first touched at divstep 0,
  at op 23,444 where live count is 1,027 — **125 below the peak**. Provably-zero population at the peak: **0 of 256**.
- **Adder bucket.** Split measured for the first time: **91.7% quantum-x-quantum, 8.3% quantum-x-constant**. The
  constant path is 4.93% of the circuit and already exploits secp256k1 structure (F = 2^256-p = 2^32+977, 53-bit
  window). Controlled adder at **1.978n vs published best-known 2n**. Litinski's n-cost controlled add-subtract
  (arXiv:2410.00899 Fig 1f/g) killed by **exhaustive machine search** over all <=2-AND bit-slice circuits for
  `{cswap(swp,u,v); v -= sub*u}`: floor is 3 ANDs/bit. The saving is gated on the `sub` axis, not `swp`, and
  `sub=0` occurs **24.74%** of divsteps, so the identity branch is structural.
- **Permutation bucket** closed; zero of its 546,224 CCX is fused with adjacent arithmetic and fusing is a loss.
- **Transcript** closed: 603 against a 599-bit floor, backward enumeration gives exactly (5^k+1)/2 k-suffixes.

### The transferable artifact
Suffix exchange-rate table (dCCX per unit dlambda, higher better): depth-1 over a wide suffix runs ~4,200-4,300;
depth-2 runs ~1,700-3,500 and is best near a=181-197. **The shipped head spends its entire budget in the expensive
mode** (flat depth 2 from a=133, 2,022 CCX/lambda). A future schedule search should knapsack against this table
rather than sweep blind. Hard constraint: the narrowed width must be **monotone non-increasing** in divstep or the
walk panics (`v[..current_n]` out of range) — middle-only blocks are invalid.

### Opinions
- The frontier is **grindability-limited, not Toffoli-limited**. A headline number is a property of (circuit, seed).
- Seven parallel agents produced five rigorous negatives and two wins. The negatives were worth more.

---

## 2026-07-26 — Session 3 (Claude Opus 5): 1151

`6c0e30c`: **1,498,369,498** = 1151 x 1,301,798. SCHED_J2 tail narrowing, depth 2 over the last 128 entries with
`GAP_J2` in lockstep, caps lowered 1152->1150, plus a re-mined 1e9 census. Seed `66014000021257` found in ~1.1e7
candidates on a 26-box fleet.

- **`GAP_J2` must move with `SCHED_J2`.** The divstep error depends only on `s = SCHED_J2[i] - cmp_window(i)`; move
  one alone and the channel goes from ~8 mismatches to ~4,600.
- **Narrowing alone buys zero qubits.** The vent pool is `TLM_TARGET_Q - active` and expands to absorb whatever you
  free. Measured four times, peak 1153 every time. Only narrowing *and* lowering the cap wins.
- The "1153" in old names was a **naming fossil**; `peak_qubits` == scored `qubits` exactly, on 39/39 configs.

---

## 2026-07-26 — Session 2 (Claude Opus 5): 1152

`5745db8`: **1,502,937,216** = 1152 x 1,304,633. First qubit reduction of the run, via the same SCHED_J2 tail lever.

- **The census re-mine is mandatory for any geometry change**, not an optimisation. The dead-gate table is keyed by
  `(kind, controls, target, condition, k-th occurrence ordinal)`; any width/schedule/ordering change shifts the
  ordinals and the stale table then names *live* gates. Running the old table on a new geometry gave 6,241 stale keys
  and 8,720/9024 mismatches. Budget ~16 min of a 192-core box and **commit the table together with the tool that
  mined it** — the table is meaningless without it.
- Shipped a broken build into a 3,264-vCPU grind by checking peak and Toffoli but not correctness. A probe is not a
  validation gate.
- `/run` is mounted **noexec** on the GCE debian-12 images. Unpack fleet payloads under `/opt`. Two launch cycles
  were lost to this, silently, because the heartbeat loop kept uploading while the worker never started.
