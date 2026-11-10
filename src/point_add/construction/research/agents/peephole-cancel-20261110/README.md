# peephole-cancel-20261110

Post-processing of the 652-qubit op list: exact cancellation of identical self-inverse gate pairs.
The result is shipped as `src/point_add/prune.zst` and applied by `prune()` in `src/point_add/mod.rs`.

## Files

- `qopt/` : std-only Rust tool (no crates). `Cargo.toml.txt` is its manifest (renamed so it is inert here).
  - `src/opt.rs` : the pass (`cancel`), the mask writer (`encode`), and an unused statistical selector (`roots`,
    NOT used for this submission; the shipped mask comes from `cancel` alone).
  - `src/sim.rs`, `src/stats.rs` : independent bit-sliced replay (64 shots per pass, multi-threaded) and profiler
    (per-gate fire flags, first-fire shot, per-stage tables).
  - `src/main.rs` : subcommands `decode`, `stats`, `verify`, `dump`, `children`, `prune`.
  - `src/common.rs` : record format helpers.
- `gen_inputs.py` : random secp256k1 point pairs and expected sums for the replay (192 bytes per shot).
- `mask_by_stage.py` : attributes removed Toffolis to generator stages using the base's `ranges.tsv`.
- `removed_by_stage.tsv` : its output for the shipped mask.

## Build and run

```
mkdir qopt-build && cp -r qopt/src qopt-build/ && cp qopt/Cargo.toml.txt qopt-build/Cargo.toml
cp ../../../../decoder.rs ../../../../schedule.rs qopt-build/src/     # the submission's own decoder
(cd qopt-build && cargo build --release)

zstd -dc ../../../../schedule.zst > schedule.raw
zstd -dc --long=30 ../../../../gates.zst | qopt-build/target/release/qopt decode schedule.raw trace.u16le
QOPT_CAP=512 QOPT_DEPTH=64 qopt-build/target/release/qopt prune trace.u16le - 0 0 OUT
zstd -19 OUT.runs -o prune.zst            # 547,171 bytes

python3 gen_inputs.py inputs.bin 9216 1
qopt-build/target/release/qopt verify OUT.u16le inputs.bin 144
```

The trace needs about 14 GB of RAM as 64-bit records; the pass itself runs in about two minutes on one core.

## Soundness rule

Two identical gates G (CCX, CX or X, no classical condition of their own, same PushCondition block instance) are
deleted when, on every wire of G, all surviving gates between them use the wire the same way G does (control-like on
G's controls, target-like on G's target) and no Hmr of those wires lies between. Bounded windows only pin entries;
they can miss a cancellation but cannot produce a wrong one.

## Mask format

`prune.zst` = zstd(LEB128 run lengths), runs alternate kept / deleted, first run is kept, lengths sum to the
expanded op count (1,736,726,885). After pruning 1,626,956,593 ops remain (asserted in `mod.rs`).
