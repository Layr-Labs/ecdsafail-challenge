# Building the Q657 point-addition circuit

The Rust entry point is `build()` in `mod.rs`. It reconstructs the input-independent gate sequence from `gates.zst` and `schedule.zst` through the contest `Op` interface. Run `./benchmark.sh` from the repository root. The four registers hold the quantum target x and y and the classical offset x and y, 256 sites each.

The readable construction and source packer are included in `construction/`. Node 24 can emit the same gate trace on a little-endian host. From this directory run

```sh
cd construction
p=research/campaigns/2026-11-08-lowq-next/nov09-joined/checkpoint
node "$p/export-native.cjs" trace.u16le
node "$p/export-native.cjs" --spans ranges.tsv
sha256sum trace.u16le
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
bash codec/verify.sh trace.u16le rebuilt
```

The trace contains 1,502,052,471 records of four little-endian 16-bit words. Its SHA-256 is `76b5a5d62818b1600641e94f3131ad66002ada07a697b4421b43c3daae38d80c`. Reserve at least 14 GiB of scratch for reconstruction. The Rust build materializes all contest operations, which alone need about 78.34 GiB at 56 bytes each.

`centered-point.cjs` implements the coordinate circuit, compact Euclidean walk and classical offset gates. `field656-clean-lease/index.cjs` binds the two short field operations while preserving the sign. `export-native.cjs` uses the full gate emitters for multiplication, division and geometric history restoration. Its input is an output path. Points and measurement outcomes are supplied by the evaluator at run time.

The schedule represents repetitions with a verified relabeling of the qubit and classical bit IDs, including reversed operation sequences where the records match exactly. The decoder appends ordinary contest operations to one vector. The optional source packer checks the reconstructed records against the original construction.
