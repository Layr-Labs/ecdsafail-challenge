# Rebuild the 651-qubit shared-loan point addition

The Rust entry point emits point addition on secp256k1 for one quantum input
point and one classical offset. It uses 651 quantum wires and ten clean helper
sites in the midpoint arithmetic. The source encodes the gate sequence in
short literal runs and a schedule. The stock evaluator expands that sequence
to its ordinary gate representation.

## Reproduce the native and scheduled representations

Use Node 24 on a little-endian host for the JavaScript generator. The codec
requires C++17, Rust and zstd. The two exports below are independent runs.
Both the native byte trace and the span table have hashes in TRACE-SHA256.

```sh
cd construction
node q651/point.cjs raw trace.u16le
node q651/point.cjs spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
bash codec/verify.sh trace.u16le rebuilt
```

The regenerated trace contains 1,603,275,477 entries of eight bytes each.
The ordinary Rust Op representation uses 56 bytes for each of those entries,
requiring about 83.62 GiB for the operation vector plus overhead. A machine
with sufficient memory can run the checkout's regular setup and benchmark.

## Source and arithmetic

The generator extends jackylee0424's public Q651 contribution, head
b8d54a9b13fc638d689ee9aa47fc5598b6ff7cff. Its Q652 parent and nasqret's
Q653, Q654 and Q655 series provide the underlying point operation and
midpoint Euclidean arithmetic. The reuse includes the finite-rank transforms,
coefficient reconstruction, fixed ten-site mapping and terminal high-bit
routing. Original patch sources, their Git blob identifiers and SHA-256
hashes are recorded in q651-ten-field/public-source.json under the research
agents directory. The complete incremental runtime digest list is RUNTIME-SHA256
in the same directory. [Public Q651 donor](https://github.com/Layr-Labs/ecdsafail-challenge/pull/2615)

In the new restoring digit, d denotes an uninitialized borrowed bit and p the
conjunction of stable enable and quotient bits. Before unwinding the carry
chain each lower B receives d*A xor d. The next carry is unchanged since
A*(B xor d*A xor d) equals A*B in binary arithmetic. Flipping d once by p
and applying the second set of products during the carry sweep produces the
desired p*A on each output. Two unconditional CNOT passes cancel the d
offsets, and a second controlled flip restores the original borrowed bit.
The highest target has no outgoing carry and needs no CNOT offset. This
saves 2*n-2 Toffolis per width-n controlled restoring digit for n at least 2.

The field divider groups compatible positive heights below 127 and retains
the donor handling of 127 and 128. High residue and gap bits are parked in
known-zero modulus positions. The field multiplier packs an extra valuation
digit onto the low modulus bit and runs a six-tag auxiliary-free walk.
History reconstruction uses two auxiliary-free signed walks and leases
the old walk auxiliary for a height tag. Its terminal increment borrows a
word and its bitwise complement. The grouped width choices, port mappings
and gate-level recurrences are in divide.cjs, multiply.cjs, regen.cjs and
shared-digit.cjs.
