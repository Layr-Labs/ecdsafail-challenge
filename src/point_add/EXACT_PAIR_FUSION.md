# Exact adjacent-Toffoli factoring candidate

Base: `457beedbd2714e2faf08f51725e773a8b5458ca3` in `ecdsafail-challenge`.
Status: enabled for remote evaluation, algebra verified, release and test builds
compiled successfully, not full-circuit validated locally.

## What changes

`exact_pair_fusion.rs` adds a small final-stream pass after the existing classical
control passes and all stream-bound rewrite tables, before the nonce tail. It
looks only at adjacent well-formed CCX operations outside condition-stack scopes.
It does not reorder gates, allocate qubits, measure anything, or modify the
protected harness or dependencies.

The pass applies three elementary Boolean identities:

1. Same controls, different dirty targets:
   `CCX(a,b;t); CCX(a,b;u)` becomes
   `CX(t;u); CCX(a,b;t); CX(t;u)`.
   The four wires a, b, t, u must be distinct.
2. Same target, one shared control:
   `CCX(a,b;t); CCX(a,c;t)` becomes
   `CX(b;c); CCX(a,c;t); CX(b;c)`.
   The four wires a, b, c, t must be distinct.
3. Identical CCX pairs cancel, including reversed control order.

Each factoring match replaces two CCX gates with one CCX and two CX gates, with
zero new wires. Cancellation removes two CCX gates. This is a per-match count,
not a measured improvement on the complete ECDSA circuit. Adjacent matches may
be rare or absent in the actual final stream.

Existing bounded-support/product-witness simplifiers can reuse known products.
These rules instead factor pairs on arbitrary dirty targets, without requiring
a pre-existing clean product witness or any bounded expression support. That
is the specific opportunity explored, not a claim of a new identity or algorithm.

## Exactness and limits

Let p = a AND b. In rule 1, u first becomes u XOR t, then t becomes
t XOR p, then u becomes (u XOR t) XOR (t XOR p) = u XOR p.
In rule 2, toggling c by b makes the middle Toffoli's product a AND (b XOR c),
which equals (a AND b) XOR (a AND c); the final CX restores c.
All gates are phase-free basis permutations, so equality on every basis state
also proves coherent equality on arbitrary superpositions and entangled inputs.

Every gate in a replacement retains the exact same per-operation classical
condition. Both originals must have that identical condition; no intervening
operation can change it. A false condition skips the entire identity.

The pass refuses malformed or aliased CCX operands, differing conditions,
unmatched control/target shapes, and every pair inside a PushCondition scope.
Any intervening operation is a hard boundary, including reset, measurement,
phase, classical write, annotation, and PushCondition/PopCondition operations.
An unbalanced condition stack causes the whole original stream to be returned.
No raw wire ID is assumed to preserve its value across another operation.

Changing serialized gates changes the circuit's Fiat-Shamir seed. The existing
fixed nonce is not changed. Therefore even an exact local rewrite still needs
the complete official correctness, reversibility, phase, and score checks.

## Enable and compare in a compatible environment

The research switch is the source constant near the top of
`src/point_add/exact_pair_fusion.rs`:

```rust
pub(super) const ENABLED: bool = true;
```

The submitted candidate sets this constant to true. Set it to false for the
inherited baseline. Rebuild and run the unchanged official benchmark in an environment that
supports its required confinement. Use `ecdsafail run` there; do not bypass the
harness or run `build_circuit` unconfined. Set the constant back to false to
disable. No HEO overlay or environment-variable changes are needed. A source
switch is intentional: the builder clears inherited environment, and the
benchmark may additionally strip it through sudo.

Record both full validations and their gate counts, width, score, and run time.
The enabled pass prints `EXACT_PAIR_FUSION` statistics to stderr. No local
baseline score or candidate score is available from this implementation work.

## Verification provided

- The independent dependency-free Python verifier enumerates all 5,184 ordered
  four-wire CCX pairs with no condition or either of two classical conditions.
  It verifies all 576 matched pairs on all 16 quantum-basis assignments and all
  four classical assignments: 36,864 equality checks passed. These include
  arbitrary dirty targets and both control orderings.
- Three counterexample checks confirm that merging different classical
  conditions would be unsound. They passed.
- Six Rust unit-test groups cover both identities, cancellation, all wire
  permutations, conditions, malformed/aliased operands, all non-CCX boundaries,
  nested/unbalanced scopes, and empty/single/greedy sequences. They are supplied
  for actual implementation testing; test compilation passed, but those tests
  were not executed here.
- Both release binaries compiled successfully. There were 25 existing warnings
  in the release build and 27 warnings from existing code in the test build;
  neither build reported a warning in the new module.
- The enabled variant also passed `cargo check --release --locked --offline
  --jobs 2 --bin build_circuit` in 9.32 seconds. The source switch was then
  restored to false for the initial offline package. It is now true for remote
  evaluation. This was compile-only; it did not generate a circuit.
- The Python verifier does not import, read, or run the Rust contestant code.
  Its success is an independent algebra check, not execution of the Rust pass.

Safe algebra-only command:

```sh
python3 src/point_add/verify_exact_pair_identities.py
```

Compile-only commands using the already installed official toolchain:

```sh
cargo build --release --locked --offline --jobs 2 --bin build_circuit --bin eval_circuit
cargo test --release --locked --offline --jobs 2 --bin build_circuit --no-run
```

Compilation is not circuit execution. Do not execute contestant binaries or
their test binary outside required confinement. This workspace's earlier
harmless bubblewrap smoke check failed with
`NETLINK_ROUTE socket: Operation not permitted`, so no contestant circuit or
full benchmark was executed. No sandbox restriction was bypassed.

## Research context

The direction is motivated by separating expensive nonlinear AND products from
linear XOR operations, as in the multiplicative-complexity perspective of
Meuli et al., [arXiv:1908.01609](https://arxiv.org/abs/1908.01609).
The identities above are elementary reversible factoring identities, not a
reimplementation of that paper's synthesis algorithm. Its T-count metric is
not the challenge's native Toffoli score.
