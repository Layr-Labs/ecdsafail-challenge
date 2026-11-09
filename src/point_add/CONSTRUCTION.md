# Building the 654-qubit point-addition circuit

The Rust entry `build()` in `mod.rs` emits the complete input-independent circuit using the ordinary contest `Op` API. Its four registers are two quantum target coordinates and two classical offset coordinates, each 256 bits. The benchmark's `./benchmark.sh` builds and evaluates this source against its protected point-addition implementation.

The readable construction in `construction/` takes an output path alone. On a little-endian host with Node 24, C++17, Rust and zstd, run these commands from the directory containing this document.

```sh
cd construction
a=research/agents/midpoint-implicit-query-20261109/q654-next
node "$a/point.cjs" raw trace.u16le
node "$a/point.cjs" spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
bash codec/verify.sh trace.u16le rebuilt
```

The encoder checks every scheduled interval under its typed renaming of quantum wires, classical bits and registers. The Rust decoder expands the same eight-byte raw records into the repository's native vector of `Op` values. At 56 bytes for each of the 1,511,780,839 operations, the final vector occupies about 78.85 GiB. The decode buffer, allocator and operating system require additional headroom.

`q654-next/point.cjs` binds the coordinate driver to three native components. `upper.cjs` reserves a normalization-height bit in the high bit of the packed number r*v+u. On a firing row that bit is zero because r*v+u<p. When correcting the coefficient, the corresponding highest padded coefficient bit is also zero. The high divisor interval is derived from the stored high height bits. During the independent sign comparison the leading coefficient marker stores the rank and the restoring digit uses a disjoint dirty loan. The orientation sign survives at the point level.

`backend.cjs` uses four low valuation bits and zero-prefix intervals in the normalized modulus. Its four-hole remainder load represents p-15 and adds 15 modulo the normalized modulus. In the division circuit the ordinary outer Euclidean walk lends its selected leading coefficient to a height bit even on nonunit inputs. The canonical inner inversion processes descending public intervals of its divisor's leading-zero count, leaving six height bits and borrowing one of those from the leading coefficient. Each interval reconstructs its own selection from the output's older divisor. The input and output predicates meet correctly at an intervening preparatory quotient-one move because that move leaves the new upper remainder at least as large as its divisor. The carry and restoring digit operations return all dirty loans.

`regen.cjs` reconstructs the actual midpoint coefficient from the surviving numerator and denominator. The reversible coprime walk borrows a coefficient bit within each active height band. Its subsequent terminal conversion borrows two low zero pads on the right bank and a third on the left. Regeneration and both field actions require thirteen additional clean sites beyond the 640-wire scalar interface, leaving the independent orientation sign within the complete 654-wire construction. All deferred quantum-measurement phases are explicitly replayed.
