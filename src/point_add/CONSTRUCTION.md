# Building the Q655 point-addition circuit

The Rust entry `build()` in `mod.rs` reconstructs the fixed gate sequence from `gates.zst` and `schedule.zst` through the normal contest `Op` API. The two quantum target coordinates and two classical offset coordinates are each 256 bits. Run the original repository's `./benchmark.sh` from its root.

The readable construction in `construction/` takes an output path and no points or measurement outcomes. On a little-endian host with Node 24, C++17, Rust and zstd, run the following commands from this directory.

```sh
cd construction
a=research/agents/midpoint-implicit-query-20261109/q655-trim
node "$a/point.cjs" raw trace.u16le
node "$a/point.cjs" spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
bash codec/verify.sh trace.u16le rebuilt
```

The trace is 1,473,440,555 eight-byte records. The packer verifies each shared interval under a typed qubit, classical-bit and register mapping, including reverse references only where all gate records match. The Rust output vector needs about 76.85 GiB at 56 bytes per operation. Allow additional memory for decoding and the operating system.

In `q655-next/point.cjs`, a firing Euclidean row at public height k has the coefficient bit v[k] equal to one. Once N = r*v + u has been packed, that coefficient is free for the nearest-quotient direction until the divisor is restored. The direction, height rank and borrowed alignment scratch are reassigned by stage. This eliminates the upper encoder's highest physical wire without dropping an arithmetic band. During the short-factor operation, `q655-next/backend.cjs` uses five stored valuation bits and derives their high interval from the normalized modulus. The outer reduced-GCD walk lends an upper pad before terminal alignment, and its inner walk borrows the top of its active coefficient band. The reverse field kernel still supports nonunit payloads. `q655-next/regen.cjs` restores the midpoint coefficient using two free padding sites during the coprime walk and disjoint low right pads during the terminal shear. The resulting 654-wire field operators preserve an independent orientation sign within the 655-wire circuit.

The separate q655-trim source shares threshold predicates between consecutive valuation buckets. Its reduced-GCD coefficient load uses the padding immediately beside the selected coefficient at that height. Both transformations preserve all inactive lanes and the measurement phases.
