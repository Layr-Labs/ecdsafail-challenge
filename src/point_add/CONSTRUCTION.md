# Building the 653-qubit point-addition circuit

The Rust entry `build()` in `mod.rs` emits the complete input-independent circuit using the ordinary contest `Op` API. Its four registers are two quantum target coordinates and two classical offset coordinates, each 256 bits. The benchmark's `./benchmark.sh` builds and evaluates this source against its protected point-addition implementation.

The readable construction in `construction/` takes an output path alone. On a little-endian host with Node 24, C++17, Rust and zstd, run these commands from the directory containing this document.

```sh
cd construction
a=research/agents/midpoint-implicit-query-20261109/q653-centerfix
node "$a/point.cjs" raw trace.u16le
node "$a/point.cjs" spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
bash codec/verify.sh trace.u16le rebuilt
```

The encoder checks every scheduled interval under its typed renaming of quantum wires, classical bits and registers. The Rust decoder expands the same eight-byte raw records into the repository's native vector of `Op` values. At 56 bytes for each of the 1,596,388,061 operations, the final vector occupies about 83.26 GiB. The decode buffer, allocator and operating system require additional headroom.

The new input-independent entry is `q653-centerfix/point.cjs`. It reuses the complete coordinate driver. In early Euclidean slots the actual top bit of the remainder is zero after quotient-one preparation. If the packed number \(rv+u\) has its top bit set, the exact quotient is one. The other lanes normalize a 255-bit number. Their two additional height bits use the high storage and a known-zero explicit remainder bit, and the largest normalized quotient interval starts at height nine. The aligned sign comparison leaves the additional passenger bit at the lower end of the dirty carry and shifts the public comparison threshold by \(2^k\). Actual general rows grow the coefficient through \(2^{k+1}\), which bounds the centered error on both sides. This calculation includes every possible field passenger. [Centered sign implementation](construction/research/agents/midpoint-implicit-query-20261109/q653-centerfix/upper.cjs)

The positive-field multiplier uses three low valuation bits. Its three-hole remainder represents p−47 and is corrected modulo the selected variable modulus. One canonical inversion stores its high rank on the active coefficient rather than an extra helper. The divider runs descending rank groups on its two Euclidean walks and uses the genuine highest quotient bit as the active modular carry. The exceptional reduced positive moduli 2 and 3 share p mod m = 1. Signed negation cancels the dirty pad on inactive heights. The 128-bit winding top holds the retired normalization predicate where it is available. The coprime history replay rents a fixed left-one pad for its second terminal tag. The complete point preserves its independent orientation sign. [Short scalar and history sources](construction/research/agents/midpoint-implicit-query-20261109/q653-next/)
