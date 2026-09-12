# Fixed pending quotient experiment

Parent: frozen `hybrid-margin-v3`, tree `e5834412075d6ecf163ce34ae17c566e78fa46afdcb177f254a3fd30331cab53`. This candidate makes one explicit allocation-policy experiment, with native tests prepared but not run locally. It is a bounded repair of failure density/storage support, not a solution to the user's ~1100q /5.6M executed-Toffoli goal. No Q/T or full-validation result is claimed.

## Policy and domain

`HYBRID_QRETAIN=32` allocates 32 pending-quotient bits from the initial setup through every PZ prefix step. It overrides BOTH the thin schedule's q width and the target-induced q taper. It is not merely a 32 ceiling. Unset, `off`, or `0` retains the parent's allocation path. Unsupported setting strings reject.

Enabled mode requires SROT5, the hybrid tail enabled, Q_TARGET684, and no explicit quotient cap below 32. A conflicting lower cap rejects rather than silently overriding the user. Q_TARGET684 is deliberately retained for the existing backend selection; its old q-budget formula is explicitly superseded by this policy. The PZ pack is therefore no longer promised to fit 684: at the known step 327, its data/coefficient/q subtotal changes666+18→666+32=698. Actual whole Q and arithmetic scratch must be measured.

The existing semantic support remains explicit: true GREEDY PZ integer transitions, faithful value/coefficient widths and windows, and true pre-offset/reverse-offset shifts fitting the actually used SROT5 rotators. Under that support, every fresh quotient bit has index≤31 and the retained word fits32 bits. This prevents premature loss of pending high bits. It does not prove membership from allocation, remove other width/window failures, or broaden the margin certificate silently.

`HYBRID_MARGIN_SUPPORT=exact-positive-l31` and its positive/faithful-support conditions are unchanged. New profiles still require that explicit declaration before their fused/top shortcuts activate. Generic quotient encoding becomes32→6 with constructor-captured raw width. The existing raw-width==18 guard excludes the old mixed-radix metadata pack. No new codec or phase simplification is introduced.

## One implementation feeds allocation and diagnostics

`qretain::fixed_width` is the shared accessor. It is called by both initial quotient allocations, `trailmix_q_width_step` for forward and reverse PZ loops, and the scalar support model's q rows. Runtime schedule dumps already use the actual width function and now explicitly report `fixed_quotient_bits=32` (zero means off). The support model no longer reapplies target/thin/model-only shrinking to the fixed physical word.

The two inversion constructors start with 32 wires directly. The generic quotient codec retains the original raw width for restoration, so the reverse prefix receives 32 wires. No handoff field or source/profile array is regenerated. The first eight counter/tape slots and six-bit popcount cache are unchanged; q width32 remains below the cache's64-position bound.

## Why backend predicates remain valid

No one-A, passenger-borrow or CLZ enable function was modified or forced true.

- One-A elimination replaces a controlled-|1> addition by the corresponding unconditional adder, and removes a materialized flag in the Gray-deposit consumer. For two controls, the latter is the exact dirty-pivot identity: copy pivot p into other targets, toggle p by f=a*b, then copy it again, so every target changes by f and initial pivot data cancels. The argument is independent of q length; the source/target registers remain distinct. The PZ CTZ helper’s literal zero sentinel at q32 is31, coinciding with ctz(1<<31); valid active multiply has q!=0, and inactive zero queries remain masked. This differs from the generic quotient-code tag, whose zero sentinel is32 and requires six bits.
- CLZ constant folding computes `(pos_a−pos_b+lo_a−lo_b) mod2^5`, instead of adding/canceling the two separate +1/window constants. The A/B and coefficient widths/windows are unchanged. A wider q word does not alter that identity or manufacture true shift-fit membership.
- The passenger carry is canonical field lane 256, removed from dy/new_dy while its owner remains live and returned before the next 257-bit field operation. It is not a quotient bit. The same complete Cuccaro add restores it. Extra q allocations cannot alias this live QReg. Its zero premise and return timing are unchanged.

The old Q_TARGET-specific gates are thus retained for their existing exact primitives, with a separately declared larger q allocation. Their resource footprint can change; the policy does not claim the old peak proof. A prepared native test compares optimized and plain backends with q32, retained high bits 21/31 and actual creation/consumption of bit31 on 40-bit operands, nonzero CLZ window offsets, active/skipped cases, fixed/random outcomes, forward/inverse values, phase and every reset. An explicit delta32/j31 negative witness must differ from the ideal greedy update even if the finite-word circuit round-trips; this guards the distinction between final index fit and pre-alignment fit. Actual native execution remains root-owned.

## Witness and tests

`memory/qretain_witness.py` independently replays the single recorded factor's ideal PZ integer recurrence through 338 steps. It verifies the dot product and both modular coefficient invariants. The generated JSON shows bit 21 created at 322, retained through the start of 337, and finally consumed. The old width policy first discards it entering 327; fixed32 discards nothing. This tiny scalar regression ran locally and passed. It does not sample new inputs or run a quantum simulator.

The Rust scalar fixture additionally checks the exact 322..337 quotient sequence and popcount-cache consistency. Policy tests verify shared allocator/model behavior, initial width, incompatible-knob rejection, and unchanged off behavior. Four caught constructor panics are expected in the negative policy tests.

Run externally from this candidate, retaining the same HYBRID_PROFILE value on every compile:

```sh
HYBRID_PROFILE=cut360 cargo test --release --locked --offline --bin build_circuit qretain_ -- --test-threads=1 --nocapture
HYBRID_PROFILE=cut360 cargo build --release --locked --offline --bin build_circuit
HYBRID_QRETAIN=32 HYBRID_QCAP=1080 MIDQ_QRETAIN_SELFTEST=1 /absolute/path/to/build_circuit
```

The native hook is diagnostic and returns an empty builder; run it in a separate output directory. It is not a benchmark artifact. For actual emission unset the selftest flag, keep `HYBRID_QRETAIN=32`, and choose the intended profile/cap. Then verify runtime rows all use 32 q bits, replay the known failed input and the original control corpus, and run the unchanged official evaluator on the new artifact's own FS inputs. Retain off-mode artifact comparison if byte identity is required; source equivalence alone is not a measured receipt.
