# Building the Q656 point-addition circuit

The Rust entry `build()` in `mod.rs` expands the fixed gate program in `gates.zst` and `schedule.zst` using the ordinary contest `Op` interface. The four logical registers hold the quantum target x and y and the public classical offset x and y. Each coordinate is 256 bits. Run the repository's normal `./benchmark.sh` from its root.

The readable arithmetic and packer are in `construction/`. A Node 24 runtime on a little-endian host can reproduce the entire input-independent program. From the directory containing this file:

```sh
cd construction
p=research/agents/midpoint-implicit-query-20261109/field655-boundary
node "$p/point.cjs" raw trace.u16le
node "$p/point.cjs" spans ranges.tsv
sha256sum trace.u16le
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
bash codec/verify.sh trace.u16le rebuilt
```

The raw trace has 1,473,109,171 eight-byte records. Its SHA-256 is `0324005a2a7745c34c4b8cbc05921b304828dcaac5c1e787748199d4028ce09f`. The no-data producer takes an output path. The evaluator supplies points and measurement outcomes at run time. The optional verifier checks every reconstructed record against the emitted trace. Allow at least 13 GiB of scratch for reconstruction. At 56 bytes per `Op`, the Rust result vector alone needs about 76.83 GiB.

The coordinate shell and its classical offset gates are in `centered-point.cjs`. Its Euclidean encoder reaches a half-width remainder while carrying the other field coordinate. `field655-boundary/index.cjs` replaces a temporary carry in the forward restoring digit with a restored dirty wire. During inverse alignment the already-zero low right rail receives the terminal shift. These changes allow the full 128-bit factor operation and arbitrary companion to occupy 655 sites. `field655-boundary/regen.cjs` uses the known-zero low right pad during the modular shear and an otherwise unused upper left pad during the signed Euclidean walk. It reconstructs the midpoint coefficient within the same width. The independent orientation sign occupies the 656th site.

The source packer checks repeated spans under explicit qubit, classical-bit and register renamings. The decoder expands those spans in their original order, or in reverse only when every corresponding record matches. Neither the wire reduction nor the source encoding uses the evaluator's inputs.
