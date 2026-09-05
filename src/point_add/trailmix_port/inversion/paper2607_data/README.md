# Certified Luo et al. EEA primitive stream

This directory contains the executable fixed-schedule EEA used by
`paper2607_eea.rs`. It is derived from Luo et al.,
*Quantum Algorithm for Elliptic Curve Discrete Logarithms with
Space-Efficient Point Addition* (arXiv:2607.13816v1), but it does not rely on
the paper repository's resource-only inverse placeholder or its unsafe
fixed-step and active-window claims.

Upstream source:

- repository: `https://github.com/ZeroWang030221/Space-Efficient-Quantum-Algorithm-for-Elliptic-Curve-Discrete-Logarithms-with-Resource-Estimation`
- commit: `ac1ecffee14b5a977421b75669c52db6b4033646`
- license: MIT; retained in `UPSTREAM_LICENSE`

## Exact repairs

The emitted circuit uses:

- 1,616 microsteps, from a checked universal
  `sum(bit_length(q_i)) <= 404` continuant bound;
- a 9-bit modulo-259 shift encoding with exact terminal rotation restoration;
- a pinned 1,616-row secp256k1 active-window certificate;
- exact inactive-cell controls, endpoint decode, quotient direction, lower
  borrow, folded terminal R guard, and full length updates;
- ten clean auxiliary lanes, obtained by complementing the pre-shift phase
  predicate in place, replacing materialized conditions with restored
  dirty-borrowed controls, using direct-leaf endpoint decoders, and borrowing
  only conditionally clean phase/tail lanes with explicit restoration;
- clean-`C^3X` measurement uncomputation lowered to two executed CCX gates
  plus structural phase repair;
- exact reversed primitive replay for cleanup.

The local stream width is 576 wires: two phase bits, iteration, sign, two
259-bit work registers, an 8-bit `l_t`, 9-bit `l_q`, 9-bit `l_s`, 8-bit
`l_rp`, ten clean auxiliary wires, and ten restored dirty-passenger
references. The terminal guard is folded into the existing R control on the
valid Algorithm-3 domain, then uncomputed before the next phase; no retained
guard lane is needed.

Pinned identities:

- active-window table SHA-256:
  `3e1961f5550249604bf044edb65f1d1bc403ed75bd7178e283685ddb4f3cb880`
- generator module SHA-256:
  `b00c0801921234a7b7c528988addda914c8b229548959ab5c0d5fd2aeee922be`
- stream generator SHA-256:
  `84d0cf74b56e5b4c15b33eead15fe52b18160ee7f36ba4f5fb2cd44e29fb3114`
- schedule certificate SHA-256:
  `5ed80df7a2a34abdf7ecc0cf2a3d0245af20fe483ea15ff6ffa53f9d466c06cf`
- aggregate manifest SHA-256:
  `67663af3336d5e9fede94cd53f80b0fe74d7ae45810f85a304665a1d82b96c6a`
- independent bit-sliced probe source SHA-256:
  `1c85f6d7e6fc223c4f80b8a388df799b8d63830057ba267c23c86d4420e4d492`
- independent probe output SHA-256:
  `300526f195abcdd0fdf792289e52e4e147099d38af13acde6a289183175500df`

## Binary format

Each zstd file starts with:

```text
8 bytes  magic = P26EEA2\0
u32 LE   field width = 256
u32 LE   local width = 576
u32 LE   first schedule step (inclusive)
u32 LE   last schedule step (inclusive)
```

The payload is a stream of little-endian `u64` records. Bits `0..3`
encode the primitive kind (`1=X`, `2=CX`, `3=CCX`,
`7=clean-C^3X-MBU`), bits `4..7` encode arity, and five 10-bit local-wire
indices begin at bits 8, 18, 28, 38, and 48. The adjacent JSON file records
per-step counts and the SHA-256 of the uncompressed payload.

There are 36 chunks. The first 35 contain 45 steps each; the last contains
steps 1576 through 1616. The Rust backend checks contiguous headers and emits
each chunk independently to avoid retaining the decoded stream in memory.

For resource accounting, one kind-7 record lowers to two CCX, one HMR, and one
conditional CZ operation. Therefore:

```text
executed T per traversal = ordinary_ccx + 2 * kind7
emitted ops per traversal = records + 3 * kind7
```

The point-add integration executes four traversals: forward and reverse for
the initial quotient, then forward and reverse for exact quotient cleanup.
The verified aggregate is:

```text
records per traversal       = 97,385,770
emitted ops per traversal   = 97,405,162
executed T per traversal    = 57,629,188
four-traversal emitted ops  = 389,620,648
four-traversal executed T   = 230,516,752
```

## Regeneration

With Qiskit installed and the pinned upstream checkout available:

```sh
python generate_eea_blob.py \
  --paper /path/to/pinned-upstream \
  --out chunk-0001-0045.zst \
  --start 1 --end 45 \
  --schedule-end 1616 \
  --module eea_circuit_s835_exactwidth_dirty12 \
  --aux-size 10 --expected-qubits 576 --level 12
```

Repeat for the ranges encoded in `paper2607_eea.rs`. Promotion requires all
chunk hashes, the independent serialized endpoint/reverse probe, exact
count-only composition, and the official 9,024-shot benchmark.
