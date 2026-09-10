# Direct Q834 symbolic clean-AND port — prepared, unmeasured

Candidate `compiler-symbolic` is a fresh copy of the pinned Q1011 baseline,
submission `77730236-301d-4504-a940-e4d81faf851d`, commit
`32ac05183feb4299efd38e75703eb24478955dc9`. Neither `compiler-retention` nor
`compiler-phase` was changed. This is a distinct candidate; their enhancements
are not enabled or copied into this one.

## Attribution and exact source provenance

`q834_clean_and.rs` is a byte-for-byte copy of `src/point_add/clean_and.rs` from
welttowelt's Q834 submission `347258d5-dfc4-4bf3-91a1-4040ad600922`, commit
`af7bec983c8bc1478354080b58de972230d09769`. The upstream source snapshot is
[available at this commit](https://github.com/Gajesh2007/ecdsafail-challenge/blob/af7bec983c8bc1478354080b58de972230d09769/src/point_add/clean_and.rs).

SHA256 of both upstream and copied module: `a3e120a1098ef636aac20da98e0a29499ab5dec81a80ce484ffa675321093ce4`.
The module includes its original immutable Expr DAG, cache policy, support
lowering, optional affine/residual machinery, and all original unit tests.
Original formatting is preserved; rustfmt parses it but reports pre-existing
format differences. No proof-engine method, identity or eviction rule changed.

The original repository NOTICE is preserved verbatim as
`memory/q834-original-NOTICE.txt`. It credits Tanuj Khattar et al. and CC BY 4.0
for specified shared harness files. It does not identify clean_and.rs as one of
those reused files; no additional module-specific license header was present,
and this port does not relabel that engine under a different license. The new
adapter and adapter tests are campaign additions; credit for the copied symbolic
engine belongs to the Q834 source and its contributor, welttowelt.

## Scope and independent activation

`MIDQ_SYMBOLIC_CLEAN_AND=1` adds the pass immediately AFTER the existing
`exact_boolean::simplify`, while the final 96-operation nonce tail is still
detached. Its default is off and only literal `1` enables it. No arithmetic,
width, GCD round count, tail nonce, trusted harness or Cargo file changes.
With the option off, the exact baseline operation stream is expected and must
be compared remotely; merely compiling the unused module has no circuit effect.

The adapter scans the entire input stream with analyze_ops before proving any
entry constants. It requires four nonempty ABI registers in the actual order:
quantum target_x, quantum target_y, classical offset_x, classical offset_y.
Every declared quantum/classical wire becomes an independent unknown input.
Duplicate or mistyped ABI declarations are rejected. The pass uses actual
register widths; the trusted whole-circuit harness independently enforces 256.
This permits reduced four-register component tests without assuming q0 or any
registered late-declared coordinate wire is scratch.

## Admission and proof-state discipline

The adapter sets `Proof.affine_allowed = false` before consuming any source
operation. It calls the unchanged `Proof.step(&original)` exactly once, then
uses only its Boolean clean-AND result or its `support_lowering.apply(original)`
action. Emitted HMR, CZ, X or CX records are NEVER passed back through step.
Residual actions are asserted absent and affine query count is asserted zero.
Original q0 exclusions are retained, despite q0 not having the same specialized
outer-control role in the Q1011 route. That conservatively forgoes some gains.

The immutable value IDs represent Boolean functions; matching IDs prove equality
and unequal IDs assert nothing. XOR/AND interning and exact identities can recover
an operand's value after nonlinear or conditional writes followed by restoration.
Classical conditions and saved condition-stack masks receive symbolic values too.
Cache eviction clears definitions but never recycles IDs, so it only forgets
identities. These mechanisms are copied directly rather than approximated by
new ANF width bounds or sampled recognizers.

For a admitted cleanup, the source state satisfies `t = a AND b` and the engine
proves the effective source condition is identically one. The original CCX's
outgoing t is zero. Emitting HMR(t)->m and CZ(a,b) conditioned on fresh m has
Kraus action equal to that cleanup divided by sqrt(2), since its phase exponent
is `m*t + m*a*b = 0`. This remains exact with arbitrary entangled witnesses and
source diagonal phases. A syntactically conditional gate can be admitted only
when the engine proves its complete effective condition equals one. Inactive or
unknown conditions are not guessed. Support lowering uses the same proven
condition requirement and reduces only exact zero/one/equal-control products.

Fresh cleanup bit IDs start at analyze_ops' total original bit count: strictly
above every existing bit ID in gates, guards and late metadata. Each inserted
measurement receives a new unique ID. These bits are internal to replacements,
never ABI outputs and never inputs to the source proof. All source non-CCX
operations, including every R, HMR, phase, classical mutation, condition boundary
and declaration, are emitted byte-for-byte unchanged. No affine residual,
replacement-to-one or replacement-to-wire emission is enabled.

## Prepared verification and actual local evidence

Actual evidence is source-only: adapter/tests pass rustfmt parsing/format checks;
the unmodified upstream engine parses; the copied engine and original NOTICE
match their source bytes; inherited files outside src/point_add match baseline.
No local build, circuit generation, simulation or scoring was performed. No Q/T
gain or completed correctness receipt is claimed.

New adapter tests (pending remote execution) cover:

- Nonlinear and conditionally nonlinear control restoration; dirty targets and
  a single unrestored mutation are rejection cases. A composition test feeds the
  actual existing exact Boolean pass's output into the new engine.
- Full ABI scanning with declarations at beginning and end, quantum and classical
  input treatment, q0 exclusion, and rejection before proofs when ABI is missing.
- Multiple inserted cleanup bits beyond a source bit with ID 37; source HMR
  outcomes are consumed by later guarded quantum and phase operations.
- Symbolic classical updates, guard values that are unknown, globally true guard
  values, and condition-stack snapshots across source-bit mutation.
- Exact support Drop/X/CX, equal and complementary controls, and an affine
  residual opportunity that must remain untransformed.
- All basis assignments of the reduced ABI, including both classical input bits,
  evaluated in 64-lane batches for both metadata placements. Source and fresh
  measurements use four independent constant-outcome combinations plus mixed
  deterministic masks. Every source-boundary PREFIX is replayed through the
  unchanged native Simulator, comparing every qubit (including scratch), every
  source classical bit and phase. Full prefix replay is necessary because native
  apply_iter owns a condition stack; separate one-op calls would be incorrect.
- Direct single-stepping of an independent Proof produces the same final proof
  fingerprint as the adapter, checking that emitted replacements were not stepped.
- A bounded 32-by-24 mixed-gate corpus and the full original copied engine suite,
  including cache-eviction truth-table checks and decisive missing-phase witnesses.

The native fixed-branch basis checks imply the corresponding coherent equality
by linearity; each new HMR contributes only the explicit independent sqrt(2)
normalization in the cleanup proof. No terminal reset is appended to hide garbage.
The adapter's structural CCX savings counter is also checked against native
executed Toffoli differences: all admitted actions require condition==1, so each
saves one executed Toffoli per input lane.

## Remote handoff

Root owns the active remote server and serialized heavy-job scheduler. Suggested
unit-test command in the candidate directory, under that scheduler:

```sh
cargo test --release --locked --offline --bin build_circuit symbolic_clean_and:: -- --test-threads=1
```

This filter includes both the copied proof_engine tests and the adapter tests.
Build and emit separate `MIDQ_SYMBOLIC_CLEAN_AND=0` and `=1` artifacts through
the campaign's source guard and locked stage runner. Require off-mode bytes to
match baseline and the detached nonce tail to remain identical. Collect the
production `MIDQ_SYMBOLIC_CLEAN_AND Stats` line, output source hashes, complete
artifact hash, independently analyzed Q/T, and trusted frozen-input/independent
regressions. Unit tests alone do not establish the target whole-circuit resources.

The exact transformation changes generated operation bytes and inserts random
measurement draws. Consequently benchmark hash-derived inputs and sequential RNG
streams change. New benchmark cleanliness still needs the trusted full validator,
because the inherited arithmetic uses an approximate correctness envelope. No
public submission is requested or performed.
