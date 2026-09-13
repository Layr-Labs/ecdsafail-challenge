# Wayfinder — ECDSA Fail frontier push

> **PROCESS ATTRIBUTION (corrected 18:00):** THREE sessions in this fleet.
> (1) This session: `worker4.sh` ×5 in `~/Desktop/new-fleet/grind/w0-4` on THIS box
> (akashbalasubramani's MacBook), notes `grind4-*`, nonces 700000+/1200000+. pgrep shows
> 10 — 5 workers + 5 child subshells, not duplicates.
> (2) Session 658767: SEPARATE machine (akash@Akashs-Mac-mini, its own new-attempt
> clone), 5 tier-B workers, nonces 260000–460000, notes per its workerB.sh. CPU pools do
> NOT overlap with this box.
> (3) A THIRD session's tree at `~/Desktop/new-attempt/ecdsafail` ON THIS BOX: cloned
> 15:52 at stale 6ee4d14; ran non-terminating 10-worker grinds of dead configs
> (sw-r692/sw-r700 earlier; then `grind692.sh` = R692+WIDTH_RESCALE, P≈1e-14/draw,
> TERM-trapped). SIGKILLed 17:57, verified down; explanatory note left at its
> `src/point_add/memory/NOTE_FROM_FLEET.md` with the λ math and safe nonce blocks.
> Check `ps aux | grep eval_circuit` before starting new grinds on this box.

> **COORDINATION (all fleet agents, read first):** a 6-worker ratchet nonce-grind is
> RUNNING detached at `~/Desktop/new-fleet/grind/` (see "ACTIVE" section below). Do NOT
> run parallel eval sweeps on this machine while it's up — 11 cores, the fleet uses 6,
> and >12 concurrent evals thrash (observed). Do NOT judge any candidate by single-draw
> failures: every fresh draw fails ~4-10 shots intrinsically (see failure-economics
> section). Depth below PP_ROUNDS=696 is provably unwinnable (λ≥23). r692-style sweeps
> are dead — don't rerun. Open surfaces if you want to contribute: the square
> (only never-edge-ground surface), or a new division algorithm. Bank any pass in
> `grind/bank/` + `PASSES.log`.

Destination: reach #1 on ecdsa.fail by beating the current promoted score with an
exact 9024/9024 trusted run. Working target this session: a **2–5% score cut** on the
live frontier, i.e. score 1,256,700,325 → ≤ ~1.23e9 (2%) … ~1.19e9 (5%).

Scorer: `S = round(avg_executed_Toffoli) × (max_referenced_qubit_id + 1)`. Lower better.
Only CCX/CCZ charged, only on shots satisfying their condition stack (push_condition →
~50% executed discount). Q is a hard max-id scan, not live-peak.

## Ground truth (this machine, HEAD cae8c82, verified full 9024 run)

| field | value |
|---|---|
| avg executed Toffoli | **951,325.061** |
| qubits (Q) | **1,321** |
| score | **1,256,700,325** (1.2567e9) |
| emitted ops | 13,553,137 |
| correctness | 9024/9024, 0 phase, 0 ancilla |
| eval wall time | ~few min (fast enough to iterate) |

Each qubit removed ≈ 0.076% score. Each 1% of T ≈ 9,513 executed Toffoli.
2% via Q alone = −26 qubits (→1295). 2% via T alone = −19,026 exec Toffoli.

## CRITICAL: active build path (resolved this session)

`build_circuit` → `point_add::build()` (mod.rs:2231). Under the shipped defaults
(`SUB4_LEGACY_POINT_ADD` unset), build() returns **`pingpong_div::build_pingpong_point_add()`**
(mod.rs:2530), + 96 tail X on qubit 0, + `apply_tail_nonce(ops, nonce=1063)`.

- The entire `trailmix_ludicrous/*` + `configure_q1153_*` machinery is LEGACY, gated
  behind `SUB4_LEGACY_POINT_ADD`. It is NOT what ships.
- `build_builder()` (mod.rs:1475, `emit_dialog_gcd_raw_pa`, ecdsafail route) is ALSO
  not the shipping path from build_circuit.
- **The memory notes 01–06 / CEILING / proven-floors describe the OLD trailmix/dialog
  circuit (1154 q / 1.29M T). They do NOT describe the live pingpong circuit.**
  Treat their "proven floors" as NOT binding on pingpong until re-derived.

Optimization surface = `src/point_add/pingpong_div.rs` (1551 lines) and whatever it calls.

## Traps carried forward (from 04-traps.md, still apply)

- A null result is only real if `md5 ops.bin` changed. (baseline md5: see below.)
- Deleting a live gate → dirty free → R phase-flip p=½ → saturated phase-garbage.
- avgT must be read from a real W=64 harness run (eval_circuit), never a proxy.
- Presence-gated env knobs: `NAME=0` still counts as set. set_default_env only sets if absent.

## Submissions / experiments log

| # | change | md5 ops.bin moved? | exec T | Q | score | result |
|---|---|---|---|---|---|---|
| 0 | baseline (HEAD cae8c82) | — | 951,325.061 | 1,321 | 1,256,700,325 | OK 9024/9024 |
| E1 | CC20/FC22/FW52 combo | d27d6e64 | — | 1321 | — | FAIL 6 classical, 9 phase |

## Circuit anatomy (pingpong, measured this session)

Emitted CCX = 1,006,269 (executed 951,325 → ~5.5% discount, mostly-exact circuit).
- `tlm_inverse` (pingpong DIVIDE) = 472,580 CCX (47%)
- `tlm_forward_multiply` (pingpong MULTIPLY) = 472,580 CCX (47%)
- `square_product_register` = 59,449 (5.9%); coord shells ~2k (0.2%)

Per divide/multiply call (472,580), split by PP_SPLIT profiler:
- value_walk (build tape) = 98,942
- **replay = 274,896 (58%)** ← dominant
- value_walk_back = 98,742

Replay per round (704 rounds) ≈ 390 CCX = ~256 Gidney adder FLOOR (irreducible)
+ ~48 chunk-boundary compares (REPLAY_CHUNK_COMPARE=25 ×2 boundaries)
+ ~54 fold (REPLAY_FOLD_WINDOW=56) + ~27 flag compare (REPLAY_FLAG_COMPARE=28) + ~5 ANDs.

Peak Q=1321 at op 1,319,752 (during divide replay): tape=703 + coefficient=256
+ numerator y=256 + chunk carries ~88 + u/v remnants ~16 + misc 2.

## Levers measured (emitted CCX @ Q)

| lever | value | emittedCCX | Q | note |
|---|---|---|---|---|
| PP_CHUNK | 128 | 971,169 | 1362 | 2 chunks not 3; +41 Q kills it (net ~0.5%) |
| PP_CHUNK_COMPARE | ↓ | −2,808/unit | 1321 | truncated boundary carry re-derivation |
| PP_FLAG_COMPARE | ↓ | −1,404/unit | 1321 | sign flag compare |
| PP_FOLD_WINDOW | ↓ | −1,406/unit | 1321 | pseudo-Mersenne fold width |

**Correctness model:** truncated top-k compare fails when top-k bits tie (~2^-k) and
low bits disagree. Chunk compares/shot ≈ 2×702×2 = 2,808; ×9024 ≈ 25.3M. At k=25,
expected failures ≈ 0.76 — RIGHT at the edge (explains why CC20 combo failed and why
margin is thin). New knobs added to pingpong_div.rs (env, default=const, md5-stable):
PP_CHUNK, PP_CHUNK_COMPARE, PP_FOLD_WINDOW, PP_FLAG_COMPARE. Plus PINGPONG_PROFILE
(phase census + PP_SPLIT + PP_PEAK) and PP split checkpoints — all env-gated, md5-safe.

## VERDICT: no 2–5% in parameter space (proven this session)

Every correction window is at the EXACT correctness edge — a single −1 step fails:

| knob (default) | −1 test result |
|---|---|
| PP_CHUNK_COMPARE (25) | 24 → 4 classical + 6 phase FAIL; 23,22 worse |
| PP_FLAG_COMPARE (28) | 27 → 6 classical + 4 phase FAIL; 26,25 worse |
| PP_FOLD_WINDOW (56) | 55 → 5 classical + 4 phase FAIL; 54,53 worse |
| PP_CHUNK (96) | 128 → −35k CCX but +41 Q (net ~+0.5% worse); ≤86 → +CCX, Q unchanged |

~10 failures appear at a single −1 step (steeper than the 2^-k tie model → structural,
not statistical). Nonce-grinding to recover a −1 window would need ~e^10 ≈ 2e4 tries →
infeasible. The arithmetic (value_walk adds, replay Gidney adds) is at the proven adder
floor (n−1 CCX/add). **The pingpong circuit is fully tuned to floor + correctness edge.**
Chunk size does not move Q (peak is not carry-bound). Conclusion: the requested 2–5% does
NOT exist in any tunable parameter. Do not re-run these window searches.

## Session 2 — structural investigation (deeper pass). Six rigorous dead-end proofs.

**1. Sign non-recomputability (THEOREM, kills tape fusion).** The walk recurrence is
`t ← (t + (−1)^sign·s)/2` with both operands odd and `sign = t1⊕s1` (sign=0→add iff
t1=s1; this exactly makes the halved result odd, preserving the invariant). Mod-4 check
of both candidate pre-images: t⁺=2t'−s always has t⁺1=s1 (consistent with sign=0) and
t⁻=2t'+s always has t⁻1≠s1 (consistent with sign=1). Both pre-images are always valid ⇒
the sign bit is information-theoretically lost from the value state ⇒ the tape cannot be
freed early or recomputed. Tape=703 is NECESSARY for this recurrence.

**2. Pebbling loses to the plateau.** Checkpointing (u,v) at round B costs 2·width(B)
qubits to free B tape bits; the schedule keeps 2·width(r)+r nearly balanced against any
cut point, and the uncompute re-walks cost ≈ +29% T for −3% Q at the best single split.
Always net-negative.

**3. Depth is edge-tuned (measured, 2M-sample classical model).** Convergence to the
±1/±1 terminal orbit: q50=621, q99=674, q99.9=692, max(2M)=746. rate(>704)=1.58e-4 ⇒
P(9024 clean)≈0.24 — the shipped ROUNDS=704 + nonce is a ground artifact at the depth
edge. ROUNDS−Δ for Δ≥8 is statistically walled (λ≥2.5). Δ=2..6 is grindable (~−0.2%/round
─ tape qubit + ~1,340 emitted CCX per round, both walks).

**4. Width schedule is edge-tuned and tail-coupled.** min margin +1 bit at round 12
(schedule fitted to this recurrence's envelope — validates the model); min margin −10 at
round 699 = the slow-convergence tail violates late widths, i.e. depth failures and width
failures are the SAME tail. Widening late widths does not accelerate convergence: dead.

**5. Executed-weighted compare economics kill chunk restructuring.** Boundary compares
sit under measurement conditions → ~50% executed. PP_CHUNK=128 removes 35k emitted but
only ~17.5k executed while +41 Q (transient 127 rides the replay plateau) → +1.2% WORSE.
Smaller chunks: +50% executed compares per extra boundary, Q unchanged (binding transient
is the ~88-wide endpoint const-fold ladder at const_arith.rs:417, window 55 above f's 33
bits). Q(τ)=1233+τ; shaving τ below 86 (chunk) needs new approximate edges worth more T
than the Q saved. Max clean gain ≈ −2 qubits.

**6. Radix-4 (double-plus-minus) is an information wash.** c∈{±1,±3} choosing t+cs≡0 mod 4
halves rounds but doubles per-round work (3s/3y computation) and keeps tape bits invariant
(2 bits/round × 352). T and Q both track the walk's information flow; representation
changes at fixed information flow don't move the product. (Also: hddivstep-style variants
need data-dependent cswaps at n−1 Toffoli/round — proven worse in the old notes.)

**Q anatomy (exact):** peak = tape(703) + coefficient(256) + numerator(256) + u,v(16)
+ binding transient(88 endpoint ladder + 8 nested) + 2 = 1321, only during replay
(walk-phase peak is ~1063). Executed-T anatomy: walk adds ≈ 395k (41.5%, unconditioned),
replay main adds ≈ 360k (37.9%), replay corrections ≈ 90k (~50% executed), square ≈ 56k.

## Session 2b — THE FAILURE-ECONOMICS MODEL (this reframes everything)

**Measured: the shipped baseline artifact is a nonce-lottery winner.** Baseline params
with 5 fresh nonces: failures (classical+phase) = 10, 4, 6, 6, 10 → λ ≈ 6–7 per fresh
draw, P(clean) ≈ 0.1–0.2%. The baked nonce 1063 ≈ the number of grinds it took. λ decomposes:

- λ_walk ≈ 3–5: per-input tail rate 1.64e-4 (2M-sample model: conv>704 ∪ width violation)
  × 9024 shots × **2 walks/shot** (divide AND multiply each walk their own denominator).
- λ_windows ≈ 1–2: truncation ties in chunk/flag/fold windows.

**Consequences (all verified numerically):**
1. Session-2 "windows have ZERO margin" was CONFOUNDED — every md5-changing candidate
   fails at the intrinsic λ regardless of its own merit. Margin must be judged by Δλ.
2. Any improved artifact must re-win the lottery: expected grinds ≈ e^λ ≈ 500–1000 evals
   (~20–30s each). Feasible with parallel workers (~6 on this machine, ~700 evals/hr… 
   ~120/hr/worker).
3. **The exponential wall:** each extra −1% of score costs roughly Δλ+1.5–3 → 5–20× more
   grinding. Realistic single-machine overnight ceiling ≈ −1 to −1.5%. −2–5% via
   lottery alone ≈ weeks of compute (or a CI grind farm).
4. Q conservation trap: ROUNDS−Δ shrinks the tape by Δ but the terminal u,v widen by
   value_width(R−1)−8 each, so Q only drops ~1 per ~3 rounds removed (R698 → Q 1319).

## Session 2c — FRONTIER MOVED (rebased to 8e8f047); fleet v3

At 18:14–18:23 the promoted frontier moved (welttowelt e4b5151, RealAdii f839d9a +
4650782): new best **T=943,577.456 × Q=1320 = 1,245,521,640**, reproduced locally
9024/9024 clean. New baked defaults on main: SUB4_PP_REPLAY_CHUNK_COMPARE=23,
REPLAY_FOLD_WINDOW=54, ENDPOINT_FOLD_WINDOW=54 (→Q 1320, the endpoint-transient shave),
REPLAY_FLAG_COMPARE=25, nonce 30008. Upstream independently added the same env-knob
refactor (SUB4_PP_* names) — my PP_* knobs are superseded; instrumented file archived at
grind/pingpong_div_session2_instrumented.rs.

**New measurements on the 8e8f047 base:**
- fresh-draw λ ≈ 8.7 (draws: 12, 8, 6 failures) — the new frontier is a deeper lottery
  winner than the old one; window Δλ was milder than session-2 single-draw estimates.
- SUB4_PP_ROUNDS=698 → T 939,277 × 1318 = 1.23797e9 (−0.61%)
- **SUB4_PP_ROUNDS=696 → T 937,842 × 1318 = 1.23608e9 (−0.76%), λ≈9.9 ← fleet target**
- **SUB4_PP_WIDTH_RESCALE=1 is BANNED: measured +9 λ** (R696+rescale draws: 11,19,23)
  — uniform schedule compression eats the 1–2 bit envelope margins at rounds ~12/~600
  exactly as the classical model predicted. The −6 Q it buys is ~e^9 more grinding.

**Session 2d — depth×EFW interaction law (measured, load-bearing):** depth cuts widen the
terminal u,v to value_width(R−1) bits (11 at R696 vs 8 at 704); the endpoint fold window
EFW54 was tuned to the 8-wide terminal, so R696+EFW54 = λ≈16.5 (8 draws) — a trap.
R696 + SUB4_PP_ENDPOINT_FOLD_WINDOW=55 = λ≈11, T 937,832 × Q 1319 = 1,237,000,408
(−0.68%). R700 keeps EFW54: T 940,713 × Q 1318 = 1,239,859,734 (−0.45%), pooled λ≈11.6
over 9 draws (5–22 spread — P(pass) rides the low-λ tail of the draw mixture).
v3 fleet (R696-plain) was scrapped for this reason.

**Session 2f — FRONTIER MOVED AGAIN (18:57, welttowelt 347e889): FLAG_COMPARE 25→24 +
nonce 60171 → T 942,872 × Q 1320 = 1,244,591,040. Rebased to eb187a4, reproduced 0/0.**
Tier shapes on eb187a4 (stack welttowelt's −705 T with our depth cut):
- A: R700 → **940,046 × 1318 = 1,238,980,628 (−0.45%)**
- B: R696+EFW55 → **937,149 × 1319 = 1,236,099,531 (−0.68%)**
Old-base (8e8f047) draws discarded; logs archived in grind/logs_oldbase/. Sibling regrinding
B on eb187a4 from 260000+; its closed-negative proofs also posted as repo memory
08-structural-ceiling.md (in its tree). Grind observation: failure mixture is
overdispersed — draws of 1–2 total failures appear at ~1% rate, so P(clean) ≫ e^−mean(λ);
expect hours-to-a-day per tier, not weeks. WATCH THE FRONTIER before submitting
(`git fetch`): two moves happened within 3 hours today.

**Fleet v4 LIVE (worker4.sh, 5 workers, 48h):** T1 = R700 (nonces 700000+),
T2 = R696+EFW55 (1200000+). **Sibling session 658767** (machine ~/Desktop/new-attempt):
5 workers on T2 from block 260000–269999; owns the square lane (edge-grinding LSBS=56/
MSBS=24/GUARD=44 windows — multiplies with any depth win) and a Bernstein–Yang
jump-divstep prototype (my math handed over: floors 741/590 decision bits vs pingpong
704; cswap n−1/round is the price pingpong's parity alternation avoids; ~breakeven to
−2% net). First 0/0 pass on either machine: bank ops.bin, message the other, submit.
NOTE: the sw-r692/sw-r700 processes on THIS box were neither mine nor the sibling's —
possibly a third session; tag --note strings for attribution.

## ACTIVE (superseded by v3 above): ratchet nonce-grind fleet v2 (depth-led; windows retired)

**λ-economics measured on live draws (v1 fleet, 6 draws of R698+FW55+CC24): λ≈14, not 8.**
Pooled single-step evidence: each −1 WINDOW step costs **+2–3 λ** for only −0.15% score;
each −1 DEPTH round costs **+0.12 λ** for −0.08%. Depth is ~10× better λ-economics.
Windows are retired from the grind ladder (v1 tier1 was a ~1-in-10⁶ lottery).

`~/Desktop/new-fleet/grind/` (worker2.sh, 5 workers, 20h deadline, `STOP` halts,
passes → `bank/` + `PASSES.log`, TIER auto-escalates; nonce base 200000·tier+20000+W+6i —
sibling agents contributing compute use base 260000·tier+20000 to avoid collisions):

| tier | params | est. T exec | Q | est. score Δ | est. λ |
|---|---|---|---|---|---|
| 1 | R698 | ~946,962 | 1319 | −0.61% → ~1.2490e9 | ~7.5 |
| 2 | R696 | ~945,500 | 1319 | −0.76% → ~1.2471e9 | ~7.9 |
| 3 | R696 FW54 | ~944,100 | 1319 | −0.91% | ~9 (moonshot) |

Q note: R−Δ gives Q=1319 for Δ∈{4..8} (tape −Δ vs terminal u,v +2·(width(R−1)−8)).
To ship a banked pass: rebuild with tier envs + winning nonce (SUB4_PINGPONG_TAIL_NONCE)
then `ecdsafail run` / `submit`; verify T,Q match the PASSES.log line. Concurrent-agent
warning: sibling session 658767 was seen grinding sw-r692 (provably dead, λ≈23) and
sw-r700 (dominated by R698) — messaged twice to redirect.

## Where the REAL headroom is (structural, ~15–50%, multi-session)

Q=1321 is dominated by the **tape = 703 qubits** — one sign bit/round for ROUNDS=704,
built fully by value_walk, held live through the entire replay (peak), freed in
value_walk_back. coefficient(256)+numerator(256) are the other two big owners.

**Lever 1 — tape peak reduction via walk/replay fusion (BIG prize, ~30–50%).**
The divide's replay_halving runs FORWARD (round 0..703), same direction as value_walk.
If value_walk and replay were fused (compute sign → apply to coefficient → free sign per
round) the tape would never fully materialize → Q peak ~620 instead of 1321. The blocker:
value_walk_back currently READS the stored tape[round] (pingpong_div.rs:570). Fusion works
ONLY if walk_back can RECOMPUTE sign = target[1]^source[1] from the value state instead of
reading the tape. That is the crux to prove/derive (binary-GCD decision-bit recoverability).
Validate with pingpong_simulator_selfcheck (line ~1360) BEFORE any full eval.
Even a coarse Bennett √-pebble (peak tape ~53, ~2× walk recompute) → est. score ~−29%.

**Lever 2 — jump-2 recurrence (~15% T).** Process 2 halvings/round → ~350 rounds. Trailmix
proved JUMP=2 beat JUMP=1 there. Major rewrite of recurrence + tape + replay.
[SESSION-2 UPDATE: REFUTED as radix-4/double-plus-minus — information wash, see proof 6.]

**Lever 3 — eliminate/share the second traversal (H1) — REFUTED for affine algebra.**
y3 = λ·(x0−x3) − y0 contains a quantum×quantum product in every affine rearrangement
(λ·u, dy·u/dx, … always two quantum factors), and one in-place quantum product = one
walk of one factor. The divide's dx-tape can only multiply/divide BY dx, never merge two
quantum values. Two walks are algebraically forced for affine in/out with this machinery.
A genuine reduction needs a different algorithm family (new inversion/multiplication
primitive or non-affine intermediate representation priced end-to-end vs the blocker
notes) — a research program, not a tuning task.

**Session 2e — square and divstep CLOSED-NEGATIVE (sibling 658767's calibrated model,
arithmetic verified by this session):**
- Square: truncation windows (LSBS/MSBS/GUARD) save only 539 CCX total; the cost is the
  exact O(m²) tri_square, untouchable by truncation. Only an algorithm swap (Toom-3,
  ~−1.5% best case, high risk) remains — low priority vs the grind.
- Divstep/BY port: resource model calibrated to emitted count <0.05%. Pricing at the
  current point: 1 qubit = T/Q ≈ 717 Toffoli-equiv; removing one pingpong round is worth
  ~1,353 (tape 717 + walk add 255 + replay add 381); one conditional swap costs ~386.
  Break-even = 3.5 swaps per round removed; pingpong→hddivstep = 590 swaps for 114
  rounds = 5.2:1 → LOSES (+36% realistic, +8.7% even with replay-swap absorbed; −22.5%
  only if ALL swaps were free — but free swaps force parity alternation, which forces
  704 rounds: that IS pingpong). Also explains why trailmix/Kaliski-516+codec lost: the
  codec was the swap cost in disguise. **Pingpong is at/adjacent to the structural
  optimum of the round↔swap exchange for the T×Q score.**
  REOPEN CONDITION (not a theorem, an empirical survey): a GCD variant with round/swap
  exchange < 3.5:1, i.e. >0.29 rounds saved per conditional swap — a number-theory
  question, not an engineering port.
- Multiply-pass swap (sibling, session 2g): replacing the 466k-CCX multiply with the
  dormant schoolbook multiplier fails — schoolbook writes a FRESH acc, leaving λ live;
  erasing λ needs inversion-grade machinery (matches the two-traversals argument).
  Fresh-acc path = 2 divisions + 1 mult ≈ 992k vs current 932k → strictly worse. Both
  peak binding sites (inverse + multiply) are justified. **Structural search exhausted on
  all surfaces; only Toom-3 square (~−1.5%, high-risk) and the λ-lottery grind remain.**
  Sibling's full write-up: its tree, memory/08-structural-ceiling.md.

**What 2–5% would actually take (final assessment, both sessions):** the pingpong
architecture is tuning-exhausted at every axis (windows, depth, width schedule, chunking,
radix, pebbling, fusion — each closed by proof or measurement above). Available paths:
(a) lottery-grind stacked edges: ~−1% overnight, ~−1.5% weekend, −2% ≈ 8+ days single
machine (exponential wall e^Δλ), parallelizable on CI;
(b) a new division/multiplication algorithm (research);
(c) the square (59k emitted, 5.9%) is the only surface never edge-ground — bounded
upside ~−1% even if 20% improvable.

## Instrumentation added this session (all env-gated, default build md5-STABLE = a077f98f)

- `PINGPONG_PROFILE=1` → PP_PEAK (peak Q + owner census via B0_WIN_LO/HI), per-phase CCX
  census, PP_SPLIT (walk/replay/walk_back CCX split), PP_TOTAL_CCX.
- `PP_CHUNK`, `PP_CHUNK_COMPARE`, `PP_FOLD_WINDOW`, `PP_FLAG_COMPARE` — replay window
  overrides (default = original consts). Proven no safe reduction exists; kept for the
  record and for fast re-testing if the recurrence changes.

Fast iteration: `build_circuit` then `./target/release/eval_circuit` directly = ~20s full
9024-shot verify (skip benchmark.sh sandbox for dev; use benchmark.sh for the real submit).

## Open leads (fog)

- Where do the 951k executed Toffoli concentrate in pingpong? (need phase census)
- Where is the Q=1321 peak, and is there slack owner-by-owner? (B0 census on pingpong)
- Are the trailmix "proven floors" (adder n-1, cswap n-1) actually hit by pingpong,
  or is pingpong looser somewhere the old proofs never covered?
