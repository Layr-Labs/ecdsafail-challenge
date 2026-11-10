# Regenerating the 652-qubit point addition with reversible gate optimization

The Rust entry in `mod.rs` emits a reversible secp256k1 point addition at
652 physical qubits. Its target x and y registers are quantum. Its two
offset coordinates use 256-bit classical registers. The ordinary contest
setup and benchmark scripts build and grade these same sources.

The circuit builds on submission `53d21251-794c-4d15-8795-2da445bdc296`.
Its upper Euclidean pipeline incorporates six files from jackylee0424's
submission `8933c99e-e85a-4e94-acad-d077f08a149e` at commit
`c5e51e3acb97a3c0948617a9cc666e265b860890`. The release lists individual
Git blob IDs and SHA-256 digests in `q652-hybrid/UPPER-SOURCES.json`. It
also includes the leased affine product, eleven-workspace field kernels
and measured coefficient reconstruction from the prior Q652 submission.
[Upstream Q652 arithmetic](https://github.com/Layr-Labs/ecdsafail-challenge/pull/2614)
· [Previous Q652 circuit](https://github.com/Layr-Labs/ecdsafail-challenge/pull/2619)

The new Q652 point entry binds a restoring digit with an arbitrary dirty
work bit. After the final digit flag is known, the same enable-and-flag
product controls each remaining output bit. Reading the dirty bit twice
with a product toggle between reads transfers that product to the target.
The implementation leaves the toggled bit in place between digit positions.
For an odd number of positions it performs one final toggle to restore the
original work bit. The one-bit boundary has a separate exact circuit.

This version extends the Q652 alternating-digit result in submission
`d4cbe56e-e6ba-48ad-9c35-d4871a89ab3a`. It applies the reversible local
gate rewrites and cached-product erasure used in the Q651 submission
`1af84e41-574b-4a0c-b816-477993cc7f4a`. Coefficient history and local
field optimizations preserve their measurement and conditional boundaries.
[Q652 parent](https://github.com/Layr-Labs/ecdsafail-challenge/pull/2621)
· [Q651 compiler source](https://github.com/Layr-Labs/ecdsafail-challenge/pull/2629)

On a little-endian machine with Node 24, C++17, Rust and zstd installed,
regenerate and verify the trace from this directory.

```sh
cd construction
a=research/agents/midpoint-implicit-query-20261109/q652-composed
node "$a/point.cjs" raw trace.u16le
node "$a/point.cjs" spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
bash codec/verify.sh trace.u16le rebuilt
```
