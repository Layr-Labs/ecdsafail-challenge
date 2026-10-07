# Traps in this codebase

Every one of these cost me or an agent real time. Read before running an experiment.

## 1. Four independent ways an env knob silently does nothing

All four produce a byte-identical `ops.bin` and a clean 0/0/0, which is indistinguishable from "my change was
harmless".

1. **Superseded.** `DIALOG_TAIL_NONCE` is unconditionally overwritten at mod.rs:1936. The live knob is
   `SUB4_TAIL_NONCE` (mod.rs ~2380).
2. **Presence-gated.** Every `*_has_structurally_dead_*` predicate tests `std::env::var_os(NAME).is_none()`, and
   `set_default_env` only sets when ABSENT. So once the code sets them, `NAME=0` yields `Some("0")`, `is_none()` is
   false, and the drop stays fully **active**. There is no environment-only way to disable any of them.
3. **Unconditional `set_var`.** `install_q1153_submission_defaults` (trailmix_ludicrous/mod.rs:339-353) discards the
   environment for `TLM_FOLD_CHUNK_ZERO_CIN`, `TLM_FFG_MAX_G`, `TLM_APPLY_ADD_SKIP_LASTK`.
4. **Never implemented.** `TLM_DROPS_OFF` did not exist in the pristine repo at all. Four agents each implemented it
   in their own sandbox, so it was load-bearing for some of us and a total no-op for others, and we compared results
   across those trees for hours.

> **Standing rule: a null result is only a result if `md5 ops.bin` changed.** Pristine head md5 was
> `7c79628f5d19664ebead263860b04ce1`. Six seconds, and it would have caught two of my own runs.

## 2. Positional addressing, at two levels

**Level 1 — the eight schedule vectors.** `load_schedule` (trailmix_ludicrous/mod.rs:261-306) loads flat vectors and
every consumer pulls the next value with `step()` (mod.rs:127-131) — a bare sequential pop. Values are addressed **by
position in the dynamic consumption order**, not by call identity.

Exact position formulas, verified against 5,807 traced consumptions, zero exceptions:
```
ord(pass,i) = i for passes 0,2 (forward) ; 257-i for passes 1,3 (reverse)
pass order  = 0 inverse-fwd, 1 inverse-rev, 2 multiply-fwd, 3 multiply-rev
GCD_SUB_K[1032] = GCD_BRANCH[1032] = pass*258 + ord
CMP_K[1028]     = pass*257 + (i-1 even | 257-i odd)
APPLY_COUT_K[516] = dir*258 + ord
FOLD_SCHED[514]   = dir*257 + (i-1 | 257-i)
FFG_G[516]        = dir==0 ? i : 257+(257-i)   # stride 257; slot 515 never read
HYB_V[1558]       = NOT a (pass,i) function; 1170 reads, passes 0 and 3 only, i<=201
SQ_ROW_K[512]     = zero reads under the shipped knob set (TLM_SQUARE_ADDSUB_SKIP_C=1 revives it)
```

**Level 2 — the ~30 gate-DROPPING predicates**, keyed by bare incrementing call counters plus ordinal-keyed strips.
This is the dangerous one: a desynced *schedule* value gives a wrong width, but a desynced *drop* table **silently
deletes a live Toffoli**. Deleted live gate → qubit dirty at its `free()` → unconditional `R` → phase flip with p=½,
outcome discarded, uncorrectable. Hence saturated 141/141 phase-garbage with a normal-looking classical count.

The **occupancy tripwire** now in `deep_strip_keys.rs` fixes the ordinal-keyed strip: each key records how often its
operand tuple occurred at census time, and any key whose occupancy moved is discarded with a warning instead of
applied. Build log line to watch: `"... ; N stale keys skipped"`. N > 0 means re-mine.

## 3. Inert knobs worth knowing (measured, all byte-identical)

- `HYB_V` values touch **no gate**. With `TLM_DIRECT_VARCHUNK=1` (shipped) `gidney.rs:1780-1795` passes `hi - lo` to
  the adder and the fit value only feeds a trace. All 1170 reads set to 0, and to 999, both give emitted CCX 1394540
  exactly. What IS lethal is the varchunk **segment count**, which drives the threaded-add call counter.
- `GCD_BRANCH` is read 1032 times and **ignored** — `TLM_GCD_RESELECT_LAYOUT=1` (mod.rs:2163) diverts first.
- `COUT_K` has zero slack: all 514 calls have effective == headroom exactly, local_peak == 1152 exactly.
- `GCD_SUB_K` is 100% clamped by live headroom — `TLM_GCD_K_ADJUST` in {0,40,120} gives a byte-identical ops.bin.
- Three drop flags are exact no-ops at 0 CCX: `TLM_ADD_CONST_SKIP_STRUCTURAL_DEAD_CARRIES`,
  `TLM_GCD_SKIP_EXACT_FORWARD_CSWAPS`, `TLM_GIDNEY_SKIP_EXACT_ERASE_ALL_CCZ`.
- `gidney.rs:1052` never fires; `square.rs:84 add_into` unreachable under the shipped knob set.

## 4. The nonce-screen trap

If you write your own screen: **draw all 9024 test pairs BEFORE simulating.** Drawing them lazily one pass at a time
from the same XOF the simulator consumes means that after the first pass your input draw reads bytes the simulator
already advanced past. The resulting points are still valid curve points, just not the harness's — and the circuit
computes valid inputs *correctly*, so they never mismatch and your screen reports false `classical=0`. Cost me a
1,344-vCPU grind.

Also: classical outcomes ARE insensitive to both the value and the consumption order of the Hmr/R stream (measured
identical at W=1024 and W=1 on four nonces). **Phase and avgT are NOT** — avgT counts `cond.count_ones()` and `cond`
depends on Hmr-derived bits, so avgT must only ever be read from a W=64 harness-order run.

## 5. Tree divergence

`ecbox:~/ec-NAME` can silently diverge from `/tmp/ec-NAME`. An `ecwork build` rsyncs local→remote with `--delete`, so
it will happily overwrite a remote-generated artifact (e.g. a freshly mined census table) with a stale local copy and
break the circuit in a way that looks like a logic bug. Always re-check `md5 ops.bin` on the box after a sync.

## 6. Validation gates, ranked

| gate | strength | needs a nonce? |
|---|---|---|
| `eval_circuit`'s printed qubit count (a max-ID scan, circuit.rs:348-363, printed BEFORE the tests) | weak but always available — even a 9024/9024 run reports it | no |
| byte-identical `ops.bin` vs pristine | proves nothing desynced | no |
| `TLM_STRADDLE_VERIFY=n` — runs pre/post streams side by side off ONE shared Shake256, comparing every qubit, every classical bit AND the phase word | proves a rewrite is bit-exact | no |
| `dirtyscan` — one 64-lane batch, flags every `R` on a non-|0⟩ target, self-asserts against the frozen simulator | deterministic phase audit, ~45 s | no |
| full 9024 `eval_circuit` | the only thing that ships | yes |

**Per-phase CCX equality is NOT a soundness certificate.** Two circuits can agree on every phase total and differ in
gate identity — same count, different operands, or an index-keyed drop table deleting a different set of the same size.
