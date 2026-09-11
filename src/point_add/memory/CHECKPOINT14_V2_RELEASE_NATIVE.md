# Checkpoint14 v2 release-native validation

Status: frozen for root-owned release builds and native runs. The files are
currently unmeasured. No native build or simulation was performed locally.

This candidate copies frozen `hybrid-checkpoint14-v1`, tree
`19f38659832b81b638d656932005c0e0dea74ae58fe222b090da24104dde6693`.
The checkpoint circuit implementation, compile-time gate, original4 reference,
profile arrays and public/trusted build files are byte-identical to v1.
Only the diagnostic dispatcher behavior and its documentation change.

The inherited repository contains unrelated broken cfg(test) modules, so
`cargo test --bin build_circuit` is not the validation route. Do not repair
those modules or change Cargo manifests for this task. All checkpoint14
assertions are normal release-compiled functions and are invoked directly
through the existing point_add-owned `MIDQ_CHECKPOINT14_SELFTEST=1` hook.

## Default-four build and run

On the root-owned remote host, from this candidate directory:

```sh
HYBRID_PROFILE=cut360 HYBRID_CHECKPOINT_ROUNDS=4 \
CARGO_TARGET_DIR=/root/hybrid-pareto-campaign/targets/checkpoint14-v2-default4 \
cargo build --release --bin build_circuit

MIDQ_CHECKPOINT14_SELFTEST=1 \
/root/hybrid-pareto-campaign/targets/checkpoint14-v2-default4/release/build_circuit
```

Require successful exit and these markers:

* `CHECKPOINT14_GEOMETRY PASS ... actual_rounds=4`
* `CHECKPOINT14_DEFAULT_OPS PASS ... byte_identical=true`
* `CHECKPOINT14_RELEASE_NATIVE PASS mode=default4 default_identity=true`

The hook compares original/new four-round forward+inverse helper operation
vectors exactly. It does not try to run the14-only tests in a4 build or report
them as zero-case successes. An unset checkpoint build flag is also the same
default4 route; the explicit4 above makes the receipt unambiguous.

## Extended build and run

```sh
HYBRID_PROFILE=cut340 HYBRID_CHECKPOINT_ROUNDS=14 \
CARGO_TARGET_DIR=/root/hybrid-pareto-campaign/targets/checkpoint14-v2-cut340-14 \
cargo build --release --bin build_circuit

MIDQ_CHECKPOINT14_SELFTEST=1 MIDQ_CHECKPOINT14_TRACE=1 \
/root/hybrid-pareto-campaign/targets/checkpoint14-v2-cut340-14/release/build_circuit
```

Require successful exit and all of:

* `CHECKPOINT14_GEOMETRY PASS ... actual_rounds=14 actual_start=242`
* `CHECKPOINT_LOOKUP PASS` from the complete14-decision/end-value lookup.
* `CHECKPOINT_ENDPOINT_INPLACE PASS` and `CHECKPOINT_VALUES PASS`.
* `CHECKPOINT14_LOOKUP_NATIVE PASS cache_cases=512`
* `CHECKPOINT14_COEFFICIENT_NATIVE PASS cases=6144`
* `CHECKPOINT14_RESOURCE_NATIVE PASS cases=192`
* `CHECKPOINT14_RELEASE_NATIVE PASS mode=extension14 cache_cases=512 coefficient_cases=6144 resource_cases=192`

The final marker is emitted only after all assertions have completed. The
resource fixture now fails explicitly if the selected profile cannot fit
its declared1120 fixture cap, rather than returning after zero cases. Use
the designated cut340/14 build for this full diagnostic.

Two unchanged inherited helper log strings still say "4" in their prose,
although their loops and arrays use the compiled ROUNDS=14. The explicit
CHECKPOINT14 markers and assertions provide the authoritative extension
counts; the old helper prefixes above are required for completion only.

The release hook runs the same all64 wrapping-state lookup/cache tests,
eight supported full-width coefficient fixtures, forward and standalone
inverse tests, full roundtrips, phase and every-R prechecks, and scoped
resource allocations as the v1 functions. It uses forced0/1 and two varying
measurement streams. The actual component lines report allocator/analyzed Q,
entry/mid/exit live wires and raw/executed T for raw14, original10+4 and
cached14. Those are measured local-window results after the run, not a
whole-point-addition prediction.

## Runtime support flags

Only `MIDQ_CHECKPOINT14_SELFTEST=1` is required at execution. The optional
TRACE variable emits actual cache lifetime counts. The diagnostic's scoped
environment guard explicitly sets its1120 caps and inherited arithmetic
features: narrow coefficients and measured comparison, cell folds/sum,
recursive carry and cost selection, rotated halves, dirty/compact constant
arithmetic, in-place checkpoint/endpoints and dirty lookup. It sets
`HYBRID_MARGIN_SUPPORT` to an empty value, so these independent fixtures do
not borrow the fixed-prefix margin theorem. Each scope restores the old
environment after the assertions.

`HYBRID_PROFILE` and `HYBRID_CHECKPOINT_ROUNDS` must be present during the
corresponding build. Setting them only while running a previously built
binary does not change its compiled geometry. Separate Cargo targets prevent
mixing the4 and14 diagnostics.

No production gate changes were made in v2. Unsupported profiles still reject
14 at compile time, the default still preserves the original checkpoint,
and all profile arrays remain frozen. Whole-circuit emission, Q/T, own-FS9024
validation and any public action remain separate root-owned steps.
