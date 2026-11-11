# Building the grouped-width 653-qubit point-addition circuit

The Rust entry in `mod.rs` emits the four-register circuit through the ordinary contest
`Op` API. The two target coordinates occupy quantum registers and the two offset
coordinates occupy classical registers. All four registers have 256 bits. The source
constructs their point addition over the secp256k1 prime field.

The construction files regenerate the complete native operation list. On a
little-endian machine with Node 24, C++17, Rust and zstd, run the following from this
directory.

```sh
cd construction
a=research/agents/midpoint-implicit-query-20261109/q653-grouped
node "$a/point.cjs" raw trace.u16le
node "$a/point.cjs" spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
bash codec/verify.sh trace.u16le rebuilt
```

The point entry composes the centered Q653 coordinate circuit with a grouped
terminal-winding division. Its Euclidean rails store the positive modulus in
reverse order and contain the coefficient and gcd in overlapping logical
regions. At true modulus height `t`, the coefficient is ready to use in the
first `t` cells. A grouped division needs zero extension up to a fixed group
endpoint `h`. Its high unused divisor cells provide enough space to park
overlapping gcd bits and the additional carry pad. Qualified swaps run before
the modular shear and in reverse after it, so the following stages recover
the complete gcd, coefficient, arbitrary passenger and all workspace.

For `t≥2` the division groups are `2`, `3..64`, `65..96`, `97..112`,
`113..120`, `121..124`, `125`, `126`, `127` and `128`. A nonrestoring
division on the wider word still computes the same quotient and remainder
because its incoming high part is smaller than the true modulus. The
numerical values have ordinary leading-zero extensions; the public widths
only determine where the circuit places its wires. All emitted gate
sequences depend on these public widths rather than the field inputs.

Each scheduled interval is checked under its renaming of quantum wires,
classical bits and registers. The Rust decoder expands the result into
the stock operation vector. At 56 bytes per record, the 1,426,614,991
operations occupy about 74.40 GiB before allocator and operating-system
overhead.
