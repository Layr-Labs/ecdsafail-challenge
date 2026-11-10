# peephole-cancel-20261110

Post-processing of the 651-qubit op list: exact cancellation of identical self-inverse gate pairs, plus exact
merging of Toffoli pairs that share two wires. The result is shipped as `src/point_add/prune.zst` and
`src/point_add/merge.zst`, applied by `prune()` and `merge()` in `src/point_add/mod.rs`.

## Files

- `qopt/` : std-only Rust tool (no crates). `Cargo.toml.txt` is its manifest (renamed so it is inert here).
  - `src/opt.rs` : the passes. `cancel2` (unbounded-window pair cancellation), `cancel3` (same bookkeeping plus
    Toffoli merging), `cancel` (older bounded-window version), the writers (`encode` for the mask,
    `encode_patches` for the merge list, `apply2` for the rewritten op list), and an unused statistical selector
    (`roots`, NOT used for this submission).
  - `src/gvn.rs` : two analysis passes that found almost nothing and are NOT used for the shipped files
    (hash value numbering of wire contents; measured-target rule). Kept so the negative results can be re-run.
  - `src/sim.rs`, `src/stats.rs` : independent bit-sliced replay (64 shots per pass, multi-threaded) and profiler
    (per-gate fire flags, first-fire shot, per-stage tables).
  - `src/main.rs` : subcommands `decode`, `stats`, `verify`, `dump`, `children`, `prune`, `gvn`, `mt`.
  - `src/common.rs` : record format helpers.
- `gen_inputs.py` : random secp256k1 point pairs and expected sums for the replay (192 bytes per shot).
- `mask_by_stage.py` : attributes removed Toffolis to generator stages using the base's `ranges.tsv`.
- `removed_by_stage.tsv` : its output for the shipped mask (a merge counts as one removed Toffoli, in the
  stage of the earlier gate of the pair).

## Build and run

```
mkdir qopt-build && cp -r qopt/src qopt-build/ && cp qopt/Cargo.toml.txt qopt-build/Cargo.toml
cp ../../../../decoder.rs ../../../../schedule.rs qopt-build/src/     # the submission's own decoder
(cd qopt-build && cargo build --release)

zstd -dc ../../../../schedule.zst > schedule.raw
zstd -dc --long=30 ../../../../gates.zst | qopt-build/target/release/qopt decode schedule.raw trace.u16le
QOPT_MODE=23 qopt-build/target/release/qopt prune trace.u16le - 0 0 OUT   # cancel2, then merging
zstd -19 OUT.runs -o prune.zst            # 644,723 bytes
zstd -19 OUT.patch -o merge.zst           # 270,205 bytes

python3 gen_inputs.py inputs.bin 9216 1
qopt-build/target/release/qopt verify OUT.u16le inputs.bin 144
```

The trace needs about 15 GB of RAM as 64-bit records; the passes peak at about 63 GiB and take about seven minutes
on one core.

## Soundness rules

Cancellation. Two identical gates G (CCX, CX or X, no classical condition of their own, same PushCondition block
instance) are deleted when, on every wire of G, all surviving gates between them use the wire the same way G does
(control-like on G's controls, target-like on G's target) and no Hmr of those wires lies between.

Merging. Under the same conditions the earlier of two Toffolis can be moved forward until it is next to the later
one. If they then share two wires, the pair equals one Toffoli between two copies of a CX:

- same controls, different targets: `CCX(a,b,t1) CCX(a,b,t)  =  CX(t->t1) CCX(a,b,t) CX(t->t1)`
- same target, one shared control: `CCX(x,b1,t) CCX(x,c,t)  =  CX(b1->c) CCX(x,c,t) CX(b1->c)`

The earlier gate must be the top live gate on all three of its wires, in the same condition-block instance as the
later one. A merged Toffoli is pinned: it is not merged or cancelled again.

## File formats

`prune.zst` = zstd(LEB128 run lengths), runs alternate kept / deleted, first run is kept, lengths sum to the
expanded op count (1,838,867,579). After pruning 1,717,394,319 ops remain (asserted in `mod.rs`).

`merge.zst` = zstd(records), one record per merge, in increasing position: LEB128 delta of the surviving
Toffoli's index in the pruned list, then the CX control and the CX target as u16 little-endian. `merge()` puts
that CX directly before and directly after the Toffoli. 832,694 merges, so the final list has 1,719,059,707 ops.
