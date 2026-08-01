# The re-census tool, λ, and the qubit axis measured properly

Session goal was "optimise the circuit". Three leads were priced and two of them are now
closed with measurements rather than argument. The tool built along the way
(`src/point_add/census.rs`) is the durable part — `notes/05` recorded that the census rig
"lived in `/tmp` and `/dev/shm` and did **not** survive the stop/start", and rebuilding it
was listed as the obvious next task. It is now in-repo and diagnostic-only.

Baseline for everything below: head `8af8a6f`, **1,289,073.125 × 1,154 = 1,487,590,242**,
reproduced locally (full 9024-shot run ≈ 17 s on a 10-core M-series box).

---

## 1. `census.rs` — what it is

`TLM_CENSUS=1` (pre-strip) or `TLM_CENSUS_FINAL=1` (post-strip, post-nonce) replays the op
stream over N random on-curve addition inputs and records, per CCX/CCZ:

| field | meaning |
|---|---|
| `live` | shots where the classical condition admitted the gate |
| `fire` | shots where `cond & c1 & c2` (`& t` for CCZ) was set |
| `viol_c2` | shots refuting the `CCX→CX(c1,t)` downgrade (`act=2`) |
| `viol_c1` | shots refuting the `CCX→CX(c2,t)` downgrade (`act=1`) |

It emits a `deep_strip_keys.rs`-shaped table plus a per-gate CSV (`TLM_CENSUS_STATS`).
`TLM_CENSUS_ROUND_OFFSET` shifts the input draw, so you can mine on one set and confirm on a
**disjoint** one — mining and confirming on the same sample measures nothing.

Two properties worth keeping:

- **The mirror is proved, not assumed.** Like `dirtyscan` it re-implements
  `Simulator::apply_iter` verbatim and asserts its own final (qubits, bits, phase) against
  the frozen `crate::sim::Simulator` on every run, and checks lane sums against `curve.add`.
- **It reproduces the score.** On the final stream it reports 1,289,027.9 executed
  Toffoli/shot against the harness's 1,289,073.125 — 0.003% over 192,000 shots vs the
  harness's one 9024-shot draw. Any accounting change that breaks this is wrong.

Throughput: ~6,100 inputs/s on 10 cores (1e6 inputs ≈ 2m45s).

**`live` is the score.** `sim.rs:82` adds `cond.count_ones()` to `toffoli_gates` *before*
looking at control values, so a gate that never fires still costs full Toffoli until it is
removed or downgraded. `live/lanes` is exactly what stripping or downgrading it takes off
the score, and it is also the sample size behind that gate's zero — value/risk scales as
`live²`, so gates under a rarely-true condition are nearly all risk and nearly no gain.

---

## 2. λ = 19.74 — the fact that dominates everything else

Measured on the **shipped** stream, 192,000 shots, per-round measurement randomness:

```
faults any=420 classical=358 phase=231  ->  λ = 19.74 per 9024-shot eval
95% CI 17.85..21.63     classical 16.83, phase 10.86
P(clean seed) = e^-λ = 2.67e-9   ->  ~3.7e8 tail nonces per accepted run
```

Same regime as `notes/02` measured for the old head (classical 18.1, phase 12.6, λ 23.29).

`eval_circuit::fiat_shamir_seed` hashes **every field of every op**, so changing a single
gate redraws all 9024 test inputs. A config therefore ships only when some tail nonce
happens to draw 9024 clean inputs. **This is the binding constraint at this frontier, not
Toffoli count.** Grind cost with early abort (~7.75 batches per nonce before the first
fault) is ≈2.6e16 op-executions ≈ 280 days on 10 cores; it is a cluster-scale job.

Consequences that should shape any further work here:

- Any Toffoli win must be *bought* with a nonce grind, so its real cost is `e^λ` trials.
- **Stripping more aggressively is counterproductive.** A shallow census over-calls dead
  (see §3), and every false strip adds to λ, which costs exponentially at the grind.
- Conversely a λ reduction is worth `e^Δλ` in grind yield. But `notes/02`'s budget prices
  the available reductions in Toffoli: ITERS 258→261 buys ≈−4.7 λ for ≈8,790 emitted CCX
  (+0.65% score), leaving λ≈15 — still 3.3e6 trials. The head sits at a deliberate
  "high λ, low Toffoli, grind hard" equilibrium.

Measure λ before trusting any candidate:
`TLM_CENSUS_FINAL=1 TLM_CENSUS_ROUNDS=3000 TLM_CENSUS_THREADS=10 ./target/release/build_circuit`

---

## 3. Census depth: a shallow census over-calls dead, badly

Dead-gate count against census depth, same stream (true value anchored by the shipped
3.2e8-input table at 12,543):

| inputs | dead found | downgrade found |
|---|---|---|
| 1,280 | 79,681 | 12,428 |
| 19,200 | 48,878 | 9,353 |
| 1,000,000 | 19,416 | 5,564 |
| 3.2e8 (shipped) | 12,543 | 3,923 |

A fire-census dead set is monotone decreasing in depth, so **a fresh census can only be used
to re-address keys that are already known dead — never to discover new ones** unless you can
match the base census's depth. At 1e6 inputs, 3,223 "new" downgrade candidates appear that
the 3.2e8 table does not have; most are sampling artefacts, and each one that is wrong is a
λ contribution charged at `e^λ`.

Cross-check at 1e6: 12,079 of the 12,543 shipped dead keys were confirmed never-firing,
and ~213 shipped keys *do* fire — the deliberate rare-fire strips `notes/03` describes.

---

## 4. The 251 "stale" keys are obsolete, not recoverable — CLOSED

Every build printed:

```
[deep-strip-identity] WARNING: 251 keys discarded -- ... Re-run the census against this
op stream to recover them.
```

There is nothing to recover. Checking each stale key's operand tuple against the actual
unstripped stream: **251/251 have tuples that occur nowhere in it** (0 slid, 251 absent).
Those gates were already eliminated upstream by constprop / `single_ccx_fanout` /
`ccx_final_cancel`; the keys are leftovers from an older stream.

They have been deleted from `deep_strip_keys.rs`. A key whose tuple is absent never matched
a gate, so this cannot change the emitted stream, and it doesn't: **`ops.bin` md5 stayed
`f5c5f98258ddb7a0b1f250750ad1c6d2`** across the edit, score identical, 9024/9024. The build
line is now `removed 12292 / 12292 dead; ... 0 stale keys skipped`. The misleading warning
is gone.

---

## 5. The qubit axis is already at its optimum — and `emitted` is a trap

`notes/05` only ever explored *downward* from the cap. Upward looked like a large win:
relaxing `TLM_TARGET_Q` cuts **emitted** Toffoli fast (−6,402 gates at q=1158), which
projects to −0.131%. **That projection is wrong.**

`notes/01` already warns "never compare an emitted delta against the executed baseline", and
this is exactly that trap: the gates a relaxed cap removes sit disproportionately inside
`push_condition` blocks and execute *below* average, so the executed saving is barely half
the emitted one (−3,584 executed vs −6,402 emitted at q=1158).

Measured properly — unstripped executed Toffoli/shot from a 19,200-lane census, minus the
shipped strip saving (14,910 executed/shot at q=1154, scaled by each config's candidate
value):

| q | unstripped exec | stripped exec | score | vs head |
|---|---|---|---|---|
| 1153 | 1,305,423.6 | 1,290,485.6 | 1,487,930,358 | +0.023% |
| **1154 (head)** | 1,303,983.1 | 1,289,073.1 | **1,487,590,242** | — |
| 1155 | 1,302,813.5 | 1,287,929.0 | 1,487,557,995 | −0.002% |
| 1156 | 1,301,946.2 | 1,287,064.7 | 1,487,847,140 | +0.017% |
| 1157 | 1,301,157.3 | 1,286,303.1 | 1,488,252,571 | +0.045% |
| 1158 | 1,300,398.8 | 1,285,553.4 | 1,488,670,374 | +0.073% |
| 1159 | 1,300,084.1 | 1,285,253.3 | 1,489,608,227 | +0.136% |

The head is at the optimum. q=1155 is −0.002%, i.e. inside the error of the strip-scaling
assumption — not a win worth a 3.7e8-nonce grind.

Also confirmed: **the dial cannot be moved without a full re-mine.** At q=1153 the tripwire
discarded 4,417 keys and the run still produced 8,975 classical mismatches — occupancy
matching is a heuristic, not a proof, and a tuple whose occupancy coincidentally survives a
structural change can still address a different gate.

---

## Next

1. Nothing here is shippable without a nonce grind; that is a cluster job, not a laptop job.
2. If a grind rig exists, the ordering that matters is λ first, Toffoli second.
3. If you want new strip keys, budget a census at ≥1e8 inputs (~4.5 h on 10 cores) and use
   `TLM_CENSUS_ROUND_OFFSET` for a disjoint confirmation pass. Below that depth you are
   buying λ, not score.
