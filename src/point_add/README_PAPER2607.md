# Corrected paper-2607 point addition: Q=834, T=70,285,314

## Result and purpose

This submission adds a point to the low-qubit Pareto frontier of the standard
ECDSA Fail point-addition benchmark. Its local trusted evaluation passed all
9,024 hash-derived cases with zero classical mismatches, zero phase-garbage
batches, and zero ancilla-garbage batches. The measured circuit has 834 qubits
and 70,285,314 executed Toffolis per case. Its product is 58,617,951,876.

The public results retrieved on 2026-09-08 had a best Toffoli count under the
835-qubit budget of 154,247,477 at 823 qubits, submission 3170f7b. This circuit
uses eleven additional qubits and 54.4% fewer Toffolis. No evaluated public
point with at most 834 qubits had a Toffoli count this low. The submission is
intended for the site's Pareto graph; its product does not beat the current
global product leader. A scalar-score rejection after successful validation
should not be interpreted as an arithmetic failure.

## Attribution and source

The arithmetic construction is from Han Luo, Ziyi Yang, Jingquan Luo, Ziruo
Wang, Yuexin Su, Xiaoming Sun, Lvzhou Li, and Tongyang Li, "Quantum Algorithm
for Elliptic Curve Discrete Logarithms with Space-Efficient Point Addition":

https://arxiv.org/abs/2607.13816

The corrected Qiskit source used for this reproduction is:

https://github.com/ZeroWang030221/Space-Efficient-Quantum-Algorithm-for-Elliptic-Curve-Discrete-Logarithms-with-Resource-Estimation

Pinned authors' commit: e64aa3c1198d96aeb389e64bc7ae48edbb9712ec.
The upstream MIT license is retained verbatim in PAPER2607_LICENSE.

The TensorFurnace/Codex contribution is the explicit clean-workspace MCX
lowering repair, runtime-classical Google ABI adaptation, exact hierarchical
gate serialization, bounded-memory cancellation, and Rust/KMX reproduction.
The underlying low-space arithmetic should be credited to the paper authors.
The reproduction was implemented in an earlier Codex session; its exact
model/effort metadata was not retained in the package. This submission was
prepared and checked by Codex using GPT-6. The current effort setting is not
exposed, so no effort label is claimed.

## Construction and exact cost

The source circuit has registers for the outer quantum control, X, Y, A, and
the shared EEA workspace: 1 + 256 + 256 + 256 + 66 = 835 qubits. It uses the
paper's space-efficient EEA and quadratic modular arithmetic. The clean MCX
lowering in the wrapper uses already-zero Work1 lanes as a v-chain and
uncomputes each borrowed lane. It does not allocate an uncounted scratch bank.

The fixed affine addend in the source is replaced by two runtime classical
coordinate registers. The five corresponding constant-arithmetic stages load
the coordinate into the already-clean A bank, execute the quantum modular
add/subtract operations, and reverse the load. No quantum register is added.
The resulting raw runtime-ABI circuit contains 70,693,266 Toffolis.

Exact cancellation of adjacent equal self-inverse gates removes 405,888
Toffolis and produces 70,287,378. This independently reproduces the paper's
rounded 70.29M figure. No statistical truncation or corpus fitting is used by
this cancellation. The runtime-coordinate wrapper costs 546 Toffolis relative
to the fixed-generator version before removing the outer control.

The challenge ABI requests unconditional point addition. The outer source
control is initialized to one and returned to zero, with no data-target uses
in between. The decoder specializes this constant control. It removes one
qubit, lowers 2,064 controlled Toffoli gates to Clifford gates, and removes the
two initialization/cleanup toggles. The final result is therefore Q=834 and
T=70,285,314. PAPER2607_KEEP_CONTROL retains the 835-qubit diagnostic version;
leave that variable unset to reproduce the submitted artifact.

## What is uploaded

The entry point src/point_add/mod.rs calls the paper2607_hir decoder. The
compressed paper2607_runtime.hir.zst is an exact finite graph of primitive
gates and subcircuit calls with explicit local wire maps. It contains no
precomputed answer table, benchmark cases, score, nonce, or external pointer.
The Rust decoder expands the graph into ordinary challenge Op records before
the trusted evaluator runs. The circuit builder performs no network access
and needs no Python or Qiskit installation at runtime.

The HIR header records a version, root node, and node count. Nodes are ordered
child before parent. Each node declares quantum/classical widths and an
ordered list of primitive gates or child calls, along with wire mappings and
classical conditions. The supported leaves lower to X, Z, CX, CZ, CCX, CCZ,
SWAP, and HMR, with the challenge's explicit classical condition stack.
Adjacent H/measurement/reset triples become HMR; the lowerer rejects stray or
unmatched H, measurement, and reset operations. Measurement-conditioned phase
corrections remain in the expanded stream. Unsupported operations and invalid
maps fail closed instead of being counted as free gates.

The full stream has 402,209,220 operations. Hierarchical storage is only a
source compression mechanism: all operations are expanded, serialized, and
executed by the ordinary benchmark. It provides no resource discount.

## Reproduction commands

The initial local benchmark base was
c1adf3e5ba699b56d081e26247e4505d9f9dfeb1. Submission preparation uses the latest
public base, 1196b9fd0f2197c55411b22081b98d57759e2d66. The trusted evaluator,
simulator, operation definitions, build driver, dependency lockfile, and
benchmark scripts are identical between these two revisions. Only editable
point-addition source is replaced by this submission.

From a challenge checkout containing these src/point_add files:

```sh
./setup.sh
./benchmark.sh --note paper2607-q834-full9024
shasum -a 256 ops.bin
```

For a direct local build using an existing offline Rust installation:

```sh
cargo build --release --locked --offline --bin build_circuit --bin eval_circuit
./target/release/build_circuit
./target/release/eval_circuit --note paper2607-q834-full9024
```

The builder must emit 402,209,220 operations. Its canonical uncompressed
stream is 22,523,716,336 bytes; default zstd storage occupies 687,950,372 bytes.
Allow adequate RAM for the expanded Op vector and its analysis, even though
the submitted HIR is small. The compressed HIR is 1,694,781 bytes.

Expected HIR SHA-256:
b12aaf8fd203d38d7a9c438bec7c1aba10e51f356348b566166a9cf2932de4c9

Expected ops.bin SHA-256 with the default challenge compression settings:
e3685410cdc01696b097da7e738f0103bf2d8812491232412ac95c6221ac1693

The official corpus seed is derived from the emitted operation records,
independently of this source note and of the compressed archive bytes.

## Validation evidence

The trusted 9,024-case result retained from the local reproduction is:

```text
tested shots:             9024
classical mismatches:     0
phase-garbage batches:    0
ancilla-garbage batches:  0
average Toffoli:          70285314.000
average Clifford:         165229308.382
total Toffoli:            634254673536
total Clifford:           1491029278838
emitted operations:       402209220
qubits:                   834
score:                    58617951876
```

A second clean source checkout regenerated an ops.bin byte-identical to the
fuzzed artifact. Reduced-width checks also exercised all 96 eligible affine
pairs at n=4 and checked output values, classical offsets, scratch cleanup,
and phase. Streaming cancellation agreed byte-for-byte with the reference
in-memory pass at n=4 and n=32. Focused lowering tests reject unmatched
Hadamards and verify explicit MCX cost and classical-condition restoration.

## Scope and limitations

This uses the paper's incomplete affine formulas. In particular, it does not
add a total exceptional-case handler when the second denominator vanishes
(for example the P=-2A case when adding the classical point A). No such case
occurred in the official 9,024-case corpus. Passing that corpus establishes
the benchmark result, not a proof of total group-law behavior on every input.

There is no nonce search, intentionally approximate predicate, or omitted
phase correction in the submitted construction. The measured phase and
ancilla failures are zero on all tested cases. This submission does not claim
that the k<16 quantum-address/runtime-table windowing contract has been tested
for this new backend; the two classical coordinate registers implement the
ordinary challenge ABI. Windowing integration and exceptional-case completion
remain separate engineering tasks with their own resource accounting.

The useful result here is the executable reproduction of the corrected
paper's 835-qubit/70.29M estimate, followed by the exact one-qubit saving made
possible by the unconditional benchmark ABI. Further low-space optimization
can now begin from an emitted, phase-checked circuit and reproducible counts.
