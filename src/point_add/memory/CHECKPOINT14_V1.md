# Exact constant-four-bit checkpoint extension

Historical v1 preparation note. In this v2 copy, the validation commands
below are superseded by `CHECKPOINT14_V2_RELEASE_NATIVE.md`: use the release
diagnostic hook because unrelated inherited cfg(test) modules do not compile.

Status: candidate source prepared for root-owned native validation. No local
native build, heavy circuit emission, or benchmark run was performed.

Base is frozen `hybrid-qretain-v1`, tree SHA256
`d43a24460abf5e4d1f99cecfc37dd021676271df28e0db2aa4401df46bf6a51c`.
The tree digest hashes sorted `relative_path<TAB>file_sha256<NEWLINE>` entries.
The only inherited test-only repair is changing the first wide-test tuple's
`b=2` literal to `2u64` in qretain_selftest.rs, as requested by root. It is
recorded separately from checkpoint logic. All profile arrays and trusted
harness/build files are unchanged.

## Gate and scope

Set the **compile-time** variable `HYBRID_CHECKPOINT_ROUNDS=14` to request
the extension. Unset or `4` retains the original selected-profile checkpoint
start and the original four-round emission path. Any other value is rejected.

An extension build requires every actual selected boundary width from
N-14 through N, all fifteen entries, to equal4. It also requires the existing
N mod4=0 schedule and leaves the shared first8 rounds outside the checkpoint.
Unsupported arrays fail at compile time. They are never trimmed, replaced
by a different profile, or silently assumed to fit. The exact submitted
cut360/224 array does not have this suffix and intentionally rejects14.
The cohort cut340/256 array is an eligible native-test selection.

The selected profile's original `checkpoint_start=N-4` field remains intact.
The active checkpoint module uses N-14 only when the gate is selected. The
builder prints a separate `HYBRID_CHECKPOINT` line identifying that actual
start. Existing consumers of the module's START, including payload pack and
unpack, therefore receive the correct new checkpoint boundary. Runtime
payload replay selection retains its existing range guard.

## Exact finite-state argument

For an odd four-bit input, wrapped add/subtract followed by arithmetic
halving puts the updated value in `{−3,−1,1,3}`. Both rows have that property
after two alternating rounds. Equal absolute values are fixed points;
unequal absolute values reach equal absolute values within two further
rounds. Therefore every one of the64 input codes is stationary after four
rounds, including the magnitude3 fixed points. This is not a sampled
unit-convergence claim and never crosses a width-reset boundary.

The first four signs use the original Boolean lookups. Every later sign is
one common function f4 of the same six checkpoint bits. Its ANF has three
linear terms, seven quadratic terms and six cubic terms. The existing
exclusive-linear-coordinate trick does not apply to f4, so a single explicit
`midq.checkpoint14.stable_sign` qubit caches it.

Each cubic term borrows one checkpoint input outside that monomial as a dirty
donor. The four-CCX C3X construction restores it exactly. No fresh clean AND
workspace is allocated. Computing f4 takes31 CCX; clearing it takes31 more.
The coefficient cells preserve their supplied sign and the checkpoint seed.
Forward applies the first four cells then the ten cached-sign cells. Inverse
applies the cached cells in reverse order, then the original four in reverse.
All fourteen coefficient updates execute; no endpoint coefficient identity
or canonical-unit assumption is used to delete them.

The coefficient arithmetic implementation remains inherited. Its own valid
input/phase scope is not enlarged by this value/sign codec. Native fixtures
are nondegenerate canonical full-width coefficients, independently crossed
with every one of the64 wrapping value states.

## Live ownership and cost

The compressed checkpoint seed has exactly six wires. The stable-sign region
adds exactly one owned wire and zero clean lookup scratch. Construction-time
assertions check the active count before/after each lookup and ensure the
cache is freed. `MIDQ_CHECKPOINT14_TRACE=1` prints actual entry, cached,
post-body, exit and allocator-peak counts for each call.

The tests build three independently checkable local windows:

1. Fourteen ordinary odd-value rounds with fourteen sign slots.
2. Ten ordinary rounds plus an independently copied frozen four-round
   checkpoint emitter, with ten retained sign slots.
3. The new fourteen-round checkpoint with the single temporary cached sign.

All start from six odd-value input wires and two256-bit coefficient words,
or518 live inputs before optional world padding. Their exact checkpoint
midpoint data counts are respectively532,528 and518 before world padding.
The cached path reaches519 during its sign cache, before coefficient scratch.
The builder records its actual peak and operation-derived Q separately.

The pure lookup/removed-value arithmetic accounting is +62 lookup CCX and
−40 unvented value CCX per fourteen-round traversal, nominally +22 CCX
(+88 over four traversals). This is not a full T delta. Different live
headroom and checkpoint arithmetic scope can change carry/constant backends.
The native report therefore includes raw forward/inverse counts and average
executed forward/inverse T for every component, with forced and varying
measurement outcomes. It does not substitute the earlier seven-wire
whole-tail bookkeeping estimate for measured allocator counts.

The padded component includes an explicit extra256-bit field word, START
retained prefix bits, and an explicitly assumed12 metadata bits, all held
as arbitrary spectators and checked for restoration. This is a real local
allocation test under that declared world ABI. It is not the complete
point-addition peak, and12 must not be treated as a proved new-profile
metadata allocation. Earlier tail peaks and actual production metadata
remain separate full-builder checks.

The reference window omits the preexisting sign-extension padding loans so
that every arbitrary64-state checkpoint input is a valid independent test
input. Some such states do not have those earlier constructor facts. This
reference choice is printed in the native resource line and prevents its
local Q/T delta from being mislabeled the production delta.

## Root-owned native commands

Run from this new candidate with isolated Cargo target directories. The
trusted library does not import point_add, so use `--bin build_circuit`.
Use one test thread because arithmetic feature flags are process-wide.

Default-path literal-operation comparison:

```sh
HYBRID_PROFILE=cut360 HYBRID_CHECKPOINT_ROUNDS=4 \
cargo test --release --bin build_circuit checkpoint14_default_ops_unchanged \
  -- --nocapture --test-threads=1
```

Require one matched test and `CHECKPOINT14_DEFAULT_OPS PASS`. It compares
old/new four-round forward and inverse helper operation vectors byte for byte
under the same arithmetic environment. It does not replace a full default
point-addition artifact comparison if promotion requires one.

Extended native suite:

```sh
HYBRID_PROFILE=cut340 HYBRID_CHECKPOINT_ROUNDS=14 \
cargo test --release --bin build_circuit checkpoint14_ \
  -- --nocapture --test-threads=1
```

Require five matched tests. The default-only comparison explicitly skips
inside this14 build, while the four extended groups must report their PASS
markers. Required evidence includes512 cache cases,6144 coefficient cases,
and192 padded-resource cases. The suite also runs the inherited exhaustive
lookup, endpoint-sign and wrapped-value checks over the extended14 rounds.

The normal builder exposes the same suite through
`MIDQ_CHECKPOINT14_SELFTEST=1`, using a binary compiled for the eligible14
selection. A request against a4 build fails explicitly instead of reporting
a disabled/zero-case validation as success.

The suite checks all64 wrapping value inputs, eight independent full-width
coefficient fixtures, forced0/1 and two varying measurement streams, forward
outputs, standalone inverse outputs, and complete roundtrips. It verifies
phase, every R input under its active classical condition, all scratch,
checkpoint/tape representations, and arbitrary world spectators. It compares
against an independent modular arithmetic model as well as the old emitter.
Private measurement streams need not match across different implementations;
each path must implement the correct phase and value result for its outcomes.

Expected rejection gate: a build with `HYBRID_PROFILE=cut360` and
`HYBRID_CHECKPOINT_ROUNDS=14` must fail on the constant-width assertion.

No profile interpolation, new sampling, nonce search, or public action is
part of this candidate. Whole-circuit Q/T and own-FS9024 validation remain
root-owned and are not claimed here.
