# Exact Capped Vents for Outer Integer Adds

Separate follow-up to `07e867d` on `codex/midq-outer-exact`, based on `472a85f`.
The first constant-adder patch and its results remain unchanged and available.
This follow-up was not composed with the main task's frozen `6cbd69f` candidate.
No submission, nonce search, or experiments outside this bounded task were run.

## Gate and Scope

Optional, default-off `MIDQ_OUTER_VENT_QCAP=1024`. Unset, invalid, or zero uses
the original adder. The only production call-site change is the 257-bit-source
`cma:int` branch in `trailmix_port/rfold_mbu.rs`. Its subtraction wrapper inherits
the exact change. The 256-bit-source path is untouched.

The helper flushes pending frees, reserves one control-copy qubit if the control
aliases the source, and computes
`vents = min(n - 1, Qcap.saturating_sub(active_qubits + copy_reserve))`.
With no vents, it emits the original adder. Otherwise it calls the unchanged
`controlled_hybrid_add_refs`, preserving source and control and discharging every
vent through the existing HMR/CZ corrections. The copy prevents source carry
threading from changing the effective control during squaring.

Selection depends only on generator-time live allocation counts, register
identity, and the optional cap. It never reads quantum input values.
All RFOLD/COMPARE constants, approximation support, and existing correction paths
are unchanged. PZ/retained-division code and trusted harness source are untouched.

## Measurements

Both columns have `MIDQ_OUTER_DIRTY_CONST=1`; only the right column enables vents.

| Metric | Constant-only `07e867d` | Plus vent cap 1024 |
| --- | ---: | ---: |
| Global Q | 1051 | 1051 |
| Maximum active in vented phases | n/a | 1024 |
| Pre-cancellation emitted T | 20,088,523 | 19,827,150 |
| Final emitted T | 19,787,535 | 19,528,214 |
| Emitted operations | 67,204,662 | 68,236,816 |
| Classical bit slots | 982,419 | 1,241,740 |
| Fixed-corpus average executed T | 19,120,856.935 | 18,861,746.790 |
| Fixed-corpus average Clifford | 30,832,729.649 | 31,994,962.784 |

1,026 low-live integer adds use vents: 256 in the low-live multiplication under
`ec3.inv_fwd`, 256 in `ec3.dy_zero`, and 257 each in `ec3.new_x` and
`ec3.alt.new_dy`. High-live calls fall back. There are 259,321 vents total.
The gross saving is 261,373 Toffolis; losing 2,052 prior adjacent cancellations
leaves 259,321 net emitted Toffolis saved. Common-corpus average T saves
259,110.145. Increased measurements also increase classical bits and Clifford work.

Enabled compressed `ops.bin` SHA256:
`b127f07aea1927b389a7929fbafd68bd84161ca5a26a14c091b54756ded36fde`.
With the vent cap unset, compressed output is byte-identical to the constant-only
candidate: `c39ea1b811f718f160fcded40c4c8935865eadf16a9998db997d6f66c9ce0628`.

## Checks and Reproduction

Build: `cargo build --offline --release --bin count_tof --bin build_circuit`.
Run `MIDQ_OUTER_VENT_SELFTEST=1 target/release/count_tof`:

- 1,992,320 exhaustive small-width basis cases across selected dynamic budgets,
  both directions, every source-bit control alias, and spectator/pending-free cases.
- 399,840 production-width cases comparing against constant-only baseline,
  covering canonical and inherited exceptional states; both controls; add/sub;
  256/257-bit sources; all-zero, all-one, and random measurement modes.
- Value, phase support, source/control/spectator restoration, zero before every
  reset, clean final scratch, gate validation, and resource checks.
- Byte-identical fallback checks at zero headroom. Explicit 1024-cap accounting
  checks at live counts 771, 772, 1022, 1023, 1024, and 1040. Historical peak
  from deliberately allocated pending scratch is allowed to predate the cap;
  newly vented phases are independently verified to stay at or below 1024.

The original `MIDQ_OUTER_EXACT_SELFTEST=1` also passes after this follow-up.
Full fixed-corpus check: 9,024 shots; the same five classical failure IDs
`4174, 4968, 5407, 7617, 7854`; one phase-failure shot `4174`; no ancilla failures.
No new any-channel failure IDs. This is a diagnostic with inherited failures,
not a clean stock-validator pass. Measurement-stream changes explain why phase
failure subsets need not be identical. No fresh nonce was used.

Reproduce the enabled build/count with `MIDQ_OUTER_DIRTY_CONST=1
MIDQ_OUTER_VENT_QCAP=1024` and `target/release/build_circuit` or
`target/release/count_tof`. The existing fixed-corpus evaluator executable was
reused without editing harness source; its single appended metrics row was moved
to the local evidence directory and removed from the sibling's log.

Local artifacts: `research/outer-exact/midq-outer-vents-*.log`,
`research/outer-exact/vents-common-result.tsv`, and retained
`research/outer-exact/constant-only.ops.bin`. These and the copied `count_tof`
diagnostic remain uncommitted. The current worktree `ops.bin` contains both flags.

This isolated result remains above Q<=1024 and T<15M; integrated Q/T with the
other workers' PZ/checkpoint changes is unmeasured. Both gates remain default-off
for a later candidate, and the frozen submission was not modified.
