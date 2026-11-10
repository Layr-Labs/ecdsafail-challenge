# Regenerating the 652-qubit affine-lease point addition

The stock Rust `build()` in `mod.rs` emits the complete reversible circuit for
adding a quantum secp256k1 point to a classical offset. Its four 256-bit ports
are the two quantum target coordinates and the two classical offset coordinates.

This revision uses the Q652 upper construction from jackylee0424, submission
`8933c99e-e85a-4e94-acad-d077f08a149e`, and the balanced field family from
the previously graded Q653 circuit. The upstream upper files are pinned by Git
blob and SHA-256 in `q652-hybrid/UPPER-SOURCES.json`. The new upper operation
parks its fourth normalization bit in the selected row's high coefficient bit
during the affine product. The gates undo the parking after this subproduct.
[Upstream Q652 PR](https://github.com/Layr-Labs/ecdsafail-challenge/pull/2614)
· [Earlier centered Q653 PR](https://github.com/Layr-Labs/ecdsafail-challenge/pull/2613)

The short 128-bit factor multiplier, divider and coefficient reconstruction
each use eleven workspace qubits. The divide uses ten groups of terminal
modulus heights. Sites that carry the live gcd below the true coefficient
can be parked in high zero divisor bits for the duration of a grouped
winding operation. The reduced coefficient is at most half the positive
modulus, so its true high bit carries the outer GCD orientation during
the winding calculation. The multiplier borrows the normalized modulus's
known leading bit for a modular carry. Its enabled dyadic step can use
the low zero modulus bit for one additional valuation index. In history
reconstruction the former input carry holds a normalization bit during
the carry-free modular arithmetic.

To regenerate the native list from public field constants, use Node 24 on
a little-endian machine. The scheduled encoder uses C++17, Rust, and zstd.

```sh
cd construction
a=research/agents/midpoint-implicit-query-20261109/q652-lease
node "$a/point.cjs" raw trace.u16le
node "$a/point.cjs" spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
bash codec/verify.sh trace.u16le rebuilt
```

The native schedule emits 1,541,598,167 stock operations. Its uncompressed 56-byte
operation vector requires approximately 80.40 GiB, plus evaluator and system
memory. Run the checkout's ordinary `./setup.sh` and `./benchmark.sh` to
obtain the resource metrics and check the full point operation.
