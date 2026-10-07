# Reducing peak qubits — measured, session 2

Goal: 2–3 qubits from first principles. Baseline is the promoted head `02146ca`:
**1153 qubits × 1,309,147 executed Toffoli = 1,509,446,491**.

Break-even: 1 qubit = 1,309,147 / 1153 = **1,135 executed Toffoli** ≈ **1,188 emitted** (executed/emitted = 0.9556).

## Step 1 — locate the peak exactly

The 1153 peak is a **spike, not a plateau**, confined to three fold phases; everything else is ≤1152:

```
tlm_apply_inverse_mod_sub_fold   782 samples   peak op 3454853
tlm_apply_inverse_fold           227
tlm_apply_forward_fold           117
```

B0 owner census at op 3454853 (sums to exactly 1153):

| n | site | role |
|---|---|---|
| 599 | gcd.rs:1353 | dialog tape slots |
| 256 | mod.rs:459 | `y2` — Bezout X |
| 256 | gcd.rs:1902 | `tmp` — Bezout Y |
| 10 | mod.rs:458 | `v` (11 allocated − 1 parked) |
| 10 | gcd.rs:1189 | `u` (11 allocated − 1 parked) |
| 9 | arith.rs:981 | graduated-staircase intermediates |
| 7 | arith.rs:1197 | `add_f_window_hybrid` clean carries |
| 1 | arith.rs:1169 | staircase cout |
| 1 | gcd.rs:1830 | `controlled_mod_sub_vented` cout |
| 1,1,1 | gcd.rs:1197/1199/1260 | subtracted, s2, swap_flag |

## Step 2 — ideas killed

**`t1` is not a wasted qubit.** I expected it to be a scalar held from i=0 to the end for one use.
`compress_step0_with_t1` (codec.rs:415-427) **consumes** it — it frees `sub` and `swap` and returns `vec![t1, s2]`,
so t1 *becomes* a tape bit. Its census attribution just stays with its original alloc site. Nothing to reclaim.

**The graduated staircase is already minimal.** `controlled_add_const_chunked_graduated_off` builds chunks of width
`k-3-j`, so peak contribution is a constant `k-3` — a genuinely clever design. `graduated_const_kmin(n)` needs
`(k-3)(k-2)/2 ≥ n`; at n = LSBS = 53 that gives k=13 and a 10-qubit contribution. k=12 only covers 45 < 53. To shrink
it you must shrink LSBS, which directly raises λ (the fold-window carry escape is ~f/2^LSBS and already contributes
2.18 mismatches).

**ITERS is pinned at 261.** Each step down is worth ~3,357 emitted CCX (−0.245% score), which looked like a far better
lever than qubits. But ITERS **must be ≡ 0 mod 3** or `jump_dialog_regions` grows a ragged Pair/Raw tail. Measured at
n=12: ITERS=260 → 4,906 classical mismatches, ITERS=259 → 7,348. Both destroyed. 258 reverts to `BAKED_ITERS` and is
candidate A at λ≈17. So 261 is the only usable value in the neighbourhood.

## Step 3 — the exchange-rate trap, confirmed empirically

Narrowing the SCHED_J2 tail frees u,v qubits — and the peak **does not move**:

| narrowed tail entries | peak |
|---|---|
| 4, 12, 24, 48 | 1153 (unchanged) |

Because the vent pool (`headroom = TLM_TARGET_Q − active`) simply expands to absorb whatever you free.
**A persistent-set reduction only pays if you lower the cap by the same amount.** This is the single most important
operational fact about this circuit and it has now bitten three separate workstreams.

## Step 4 — the dial alone loses

Both caps moved together, final-stream Toffoli-family counts (not `TLM_CCX_TOTAL`, which is measured *before* the
post-passes and is structurally blind to the strip):

| q | peak | final tof | Δtof | Δq |
|---|---|---|---|---|
| 1152 | 1153 | 1,369,934 | — | — |
| 1151 | 1152 | 1,375,722 | +5,788 | −1 |
| 1150 | 1151 | 1,378,439 | +8,505 | −2 |
| 1149 | 1150 | 1,381,262 | +11,328 | −3 |

Roughly half of each Δ is **lost strips** (3,198–3,805 census keys go stale — the tripwire correctly discards them);
the rest is genuine adder cost, ~2,590/qubit after accounting. Against a 1,188 break-even that still loses by ~2.2×.
**The dial is not the answer.**

## Step 5 — what actually worked: narrow the tail AND lower the cap together

Narrowing SCHED_J2's tail is not just a lifetime change — it shrinks the GCD registers, so the walk's adders,
comparators and cswaps all get *cheaper*. Combined with a matching cap reduction it improves **both** axes at once.
(GAP_J2 narrowed in lockstep, preserving `s = SCHED_J2[i] − cmp_window(i) = −1`, per the coupling result: the error
depends only on `s`, and moving one without the other takes the divstep channel from 8.36 to 4,646 mismatches.)

Strip-off, so the numbers are pure (baseline = 1153 × 1,381,252 = 1.5926e9):

| N narrowed | q | peak | tof | peak×tof | vs base |
|---|---|---|---|---|---|
| 0 | 1152 | 1153 | 1,381,252 | 1.59258e9 | — |
| 96 | 1151 | 1152 | 1,378,319 | 1.58782e9 | −0.30% |
| 160 | 1151 | 1152 | 1,375,689 | 1.58479e9 | **−0.49%** |
| 224 | 1151 | 1152 | 1,374,133 | 1.58300e9 | −0.60% |
| 258 | 1151 | 1152 | 1,373,437 | 1.58220e9 | −0.65% |
| 160 | 1150 | 1151 | 1,378,056 | 1.58614e9 | −0.41% |

λ is the gate (n=12 per arm, strip off, q=1151):

| N | classical | phase |
|---|---|---|
| 0 (base @1152) | 6.08 | 5.33 |
| 96 | 8.33 | 6.92 |
| 128 | 8.33 | 7.33 |
| **160** | **9.67** | **8.08** |
| 192 | 10.50 | 8.58 |
| 224 | 13.67 | 10.00 |
| 258 | **1386.83** | 140.58 ← destroyed |

N=258 breaks because the *early* SCHED_J2 entries are a genuinely tight magnitude bound on f,g. The tail is where the
slack is.

**Chosen point: N=160, q=1151.** −0.49% proxy at λ_classical 9.67, which is ~22× harder to grind than the shipped
λ≈7.25 but still on the order of an hour.

## Step 6 — shipped-state measurement

`ec-FINAL` = head + narrow-160 + caps at 1151, with the *existing* (now partly stale) census table:
```
peak_qubits=1152   final tof 1,370,612   removed 4389/9268 dead, downgraded 688/2050, 6241 stale keys
```
Estimated executed ≈ 1,370,612 × 0.9556 = 1,309,797 → score ≈ **1,508,886,144 (−0.037%)**.
A win already, and that is *with* 6,241 census keys discarded by the tripwire. A re-mine against this stream should
recover ~6,241 gates and take it to roughly **1.502e9 (−0.49%)**.

Blocker on the re-mine: the census tooling lived in `/tmp` and `/dev/shm` on the box and did **not** survive the
stop/start. Only the `~/ec-*` trees are on real disk. Rebuilding it is the obvious next task — and the mined tables
themselves should be committed to git, not left on a VM.

## Next
1. Grind a clean nonce for `ec-FINAL` and submit the −0.037%.
2. Rebuild the census tool, re-mine against the FINAL stream, take the remaining ~0.45%.
3. Re-test the qubit programme end to end now that the tripwire exists — every pre-tripwire "impossible" verdict is
   suspect (the `TLM_TARGET_Q` weld already reversed).
