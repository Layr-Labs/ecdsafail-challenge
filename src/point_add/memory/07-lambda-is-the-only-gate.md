# λ is the only gate — measured on the shipped stream, and three earlier notes are wrong

Session goal: get below 1,482,000,000 (−0.376% from the shipped 1,487,590,242).
Outcome: **not reachable without a cluster-scale nonce grind**, and the reason is now
measured rather than argued. The durable artefact is `src/point_add/grind.rs`.

Baseline re-verified end to end: `ops.bin` md5 `f5c5f98258ddb7a0b1f250750ad1c6d2`,
9024/9024 OK, **1,289,073.125 × 1154 = 1,487,590,242**.

---

## 1. `grind.rs` — what `census.rs` could not do

`census.rs` seeds its own Shake256, so it can measure a fault *rate* but can never say
whether a config **ships**. `eval_circuit` draws its 9024 test inputs from a Fiat-Shamir
hash of the whole op stream, so that question is only answerable by reproducing that hash.
`grind.rs` does, and is proved on every run:

- `fastec_check` — a fixed-base comb + Jacobian scalar-mult is asserted equal to
  `curve.mul` on 512 random and 64 small scalars.
- `mirror_check` — its replay loop is asserted equal to the frozen `crate::sim::Simulator`
  on (qubits, bits, phase, **toffoli**) at the real harness seed.
- It reproduces the score exactly: 1,289,073.125 on the shipped nonce.

Two tricks make it fast enough to be an experimental loop rather than a batch job:

1. **Incremental Fiat-Shamir.** `apply_tail_nonce` rewrites only `q_target` on the last 96
   ops, so the prefix is nonce-invariant. Absorb it once, clone the sponge per candidate:
   a 444 MB hash per nonce becomes 4.7 kB.
2. **Lazy point expansion.** A search trial rejects a nonce after ~7.6 of 141 batches, so
   expanding all 9024 curve points up front doubled the cost of the entire grind. Expanding
   per batch took search from 11.1 to **28.3 nonces/s** on 10 cores (0.35 core-s/nonce).

Config probe (score + λ in ~20 s):
`TLM_GRIND=1 TLM_GRIND_NONCES=40 TLM_GRIND_BATCHES=60 TLM_GRIND_THREADS=10 ./target/release/build_circuit`

---

## 2. λ = 19.3, and the phase channel is laundered classical error

15,174 batch samples, shipped stream: `p(batch clean) = 0.868`, **λ = 19.3–19.9**,
P(clean run) = 2.2e-9 – 4.1e-9. Grind = **2.4e8 nonces ≈ 100 days on 10 cores**
(≈2,400 core-hours; the shipped nonce came from a 1,344-vCPU grind).

The decomposition is the important part (8,460 batches):

| bad batches | count |
|---|---|
| classical only | 447 |
| phase only | 180 |
| **both** | **456** |

`both / (both + classical_only) = 0.505`. That is not a coincidence: `B::free` emits an
unconditional `R`, and per `sim.rs:149-154` an `R` on a non-|0⟩ qubit flips that shot's
phase with **p = ½**. So a classical error that dirties an ancilla shows up as a phase
fault half the time. **The phase channel is mostly laundered classical error, not an
independent failure mode.**

Consequence, and it is the single most useful number here:

| scenario | λ |
|---|---|
| shipped | 19.3 |
| phase-only batches fixed | 15.9 |
| classical-only batches fixed (conservative) | 11.0 |
| classical channel fixed, `both` therefore also clean | **≈ 3.0** |

**Killing the classical channel is the master key.** At λ≈3 a grind is ~21 nonces, and it
also frees ~9 λ of headroom to *spend* on score-reducing changes. Everything else is noise.

---

## 3. Three claims in `notes/01–05` are stale — do not act on them

- **`ITERS` is already 261** (`schedule.rs:4`), not 258. `notes/02`'s headline lever
  ("258→261 buys −4.7 λ") is **already spent**, which is exactly why λ is still 19.3.
  Measured here: 258 vs 261 is 9,214 executed Toffoli (−0.71% score) for **+4.1 λ** —
  a strictly losing exchange at ~0.17% score per λ. To buy a grindable λ≈12 costs ≈+1.2%.
- **`ITERS != BAKED_ITERS` ⇒ `baked_artifacts_valid()` is FALSE ⇒ all 18 certificate
  families are auto-retired** (`trailmix_ludicrous/mod.rs:212`). `TLM_DROPS_OFF=1` is
  therefore a **no-op on the shipped head** — it produces a byte-identical stream. Forcing
  ITERS=258 to re-activate them yields λ=3896 (every batch fails) even with the strip off:
  the tables are stale against the current geometry, so their apparent −0.82% is deleting
  live gates, not dead ones.
- **The six apply-skip knobs are not a λ source.** `notes/02` attributes 5.30 mismatches to
  the i=257 apply skips. Measured with `SUB4_APPLY_STRIP=0` (mandatory — see §4), disabling
  each one leaves λ flat at 16.7–20.9 against a 17.6 base, i.e. inside noise:

  | knob (=0) | λ | knob (=0) | λ |
  |---|---|---|---|
  | base | 17.62 | `FWD_S2_ZERO_LAST` | 16.89 |
  | `ADD_SKIP_LASTK` | 18.69 | `INV_S2_ZERO_LAST` | 16.70 |
  | `FWD_CSWAP_SKIP_LAST` | 18.36 | `INV_CSWAP_SKIP_LAST` | 20.92 |

  `TLM_APPLY_FWD_FIRST_CSWAP_SKIP` is fully subsumed by `FWD_CSWAP_SKIP_LAST=2` — setting
  it to 0 gives a byte-identical stream.

Also measured and **not** λ sources (all strip-off): `TLM_MSBS` 19→32 (18.4), `TLM_COORD_MSBS`
→32 (22.9), `SUB4_NO_GAP=1` (16.4), `TLM_COUT_ERASE_CAP`=48 (17.1), `TLM_FFG_MAX_G`=53 (19.4),
and the deep strip itself (19.0 with it off vs 19.3 with it on). The best combination found,
`TLM_MSBS=48 TLM_COORD_MSBS=32`, buys λ 17.6→15.3 for **+0.68% score** — nowhere near enough.

The residual ~15.7 classical mismatches per 9024 are structural: `SCHED_J2` width truncation,
the `LSBS=53` fold window, the square, and the codec. None has an env knob.

---

## 4. Two traps that cost real time this session

1. **A source-patching sweep that restores its edit still leaves a stale binary.**
   `sed` the const → build → probe → `git checkout` restores the source, but
   `target/release/build_circuit` still holds the *old* const. Every subsequent probe then
   silently reports the previous config's numbers. An entire qubit-dial sweep was garbage
   before the op count gave it away. **Rebuild inside the probe, not around it.**
2. **Any knob that changes the op stream also invalidates the deep-strip table**, and the
   occupancy tripwire is a heuristic, not a proof (`notes/06` §5). A knob probed with the
   strip ON conflates its own effect with strip corruption — `ADD_SKIP_LASTK=0` reads as
   λ=3896 with the strip on and λ=18.7 with it off. **Probe λ with `SUB4_APPLY_STRIP=0`.**

---

## 5. Where the headroom actually is

The score axis is genuinely Pareto-optimal at this λ; every knob that lowers score raises λ,
and the grind cost is `e^λ`. So the *only* productive line of attack left is:

> Find and fix the ~15.7 structural classical mismatches per 9024 shots.

That collapses λ to ≈3, makes the grind free, and *then* buys ≈9 λ of headroom to spend on
ITERS and the qubit dial (worth ≈−1.5% score together). Nothing else moves the needle.

The tool that would find them is a classical emulator of the divstep walk + Bezout apply that
reproduces this circuit's exact truncation behaviour, run against the failing inputs `grind.rs`
already identifies. `notes/02` says a previous agent built one; it is not in the repo.
Rebuilding it — and committing it this time — is the obvious next task.

---

## 6. The λ↔score exchange is provably lossy — BUILT AND MEASURED

The obvious play is arbitrage: pay score to buy λ, get to a grindable λ, then spend λ back on
score. **It does not close**, and the three measured exchange rates say why:

| move | Δscore | Δλ | rate |
|---|---|---|---|
| ITERS 261→258 (3 fewer divsteps) | **−0.71%** | **+4.1** | spending λ *returns* 0.173%/λ |
| `LSBS` 53→57 | +0.62% | −2.6 | buying λ *costs* 0.238%/λ |
| `TLM_MSBS` 19→48 | +0.68% | −2.3 | buying λ *costs* 0.296%/λ |

Buying λ costs 0.24–0.30% per unit; spending it returns only 0.173%. **The round trip loses
~30–40%**, so the head is a genuine local optimum on the frontier and no combination of these
knobs reaches a lower score at an equal-or-lower λ. Reaching a grindable λ≈13 costs ≈+1.5%.

`LSBS` 53→57 is nonetheless notable as the **first structural knob found that lowers λ without
destroying the circuit** (17.62→15.05, strip off, +1 qubit). By contrast `SCHED_J2` cannot move
at all: the new `TLM_SCHED_J2_WIDEN` knob (`trailmix_ludicrous/mod.rs`, a proven no-op at its
default 0) shows widening by just **+2 makes every batch fault** — `GAP_J2`, `GCD_SUB_K`,
`APPLY_COUT_K`, `FOLD_SCHED` and `FFG_G` are all co-fitted to those exact widths, so
`SCHED_J2` is only movable with a full schedule refit.

### The ITERS=258 + certs-off + re-mined-strip config, actually built

Not a projection any more. Census re-mined against that stream (2e6 inputs, `TLM_DROPS_OFF=1`,
`SUB4_APPLY_STRIP=0`): 15,934 dead + 4,668 downgrade = 18,962/shot of candidate value.

```
score 1,472,327,438  (avgT 1,275,846.646 x 1154, −1.03%, 0 stale keys)
harness verdict: FAIL — 37 classical mismatches, 19 phase-garbage batches
```

**It clears the 1,482,000,000 target and is still worthless**, because λ = 36.5.
Two lessons worth more than the number:

1. **A 2e6-depth census is far too shallow, and the cost is exponential.** The same stream
   measures λ=24.25 unstripped (census's own estimator, 95% CI 23.60–24.90) but **λ=36.5 once
   the fresh table is applied** — the over-called dead gates (15,934 here vs ~12,500 at
   3.2e8 depth, per `notes/06` §3) are false strips, and each is charged at `e^λ`. Re-mining
   *cost* 12 λ, i.e. a factor of 1.6e5 in grind yield, to buy 0.35% of score.
2. **The failing shot returns the correct x and the wrong y** (`shot 96`). The y-coordinate
   recovery — the second ModDiv, run as the division circuit backwards — is where to look
   first when hunting the structural classical mismatches of §5.
