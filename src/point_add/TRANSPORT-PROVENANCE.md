# Q646 h11 transport packaging

This delivery uses exactly the same GATEIR2 intermediate and circuit as the
original h11 delivery. Only zstd framing and storage of construction provenance
have changed. No Rust runtime source, schedule, operation, or gate count changes.

The six-file runtime closure is mod.rs, decoder.rs, schedule.rs, gate_count.rs,
gates.zst and schedule.zst. Construction sources are not imported by that closure.

## Recover construction sources

From the repository root, in a fresh workspace, run:

```sh
zstd -dc src/point_add/construction-source-portable.tar.zst | tar -xf -
```

The archive preserves all 1,012 original construction files at their repository
relative paths and canonical modes (22 executable files). It also contains the
original full-tree SHA256 and mode manifests. ORIGINAL-RUNTIME-SHA256 preserves
the original runtime/source manifest; RUNTIME-SHA256 identifies this delivery.
The original full-tree manifest describes the original framing and expanded
construction layout, not this compact transport layout. Original gates.zst hash:
648f21175279f49d7301d06232d3142eeac08ad7abb253b91b2325f0eb1326bf.

## Exact transport binding

New gates.zst SHA256:
3e8f81517dd7eaf96156a3528ce7ce71f6c3cc32bee9c510d1c22fe5bf88ac5e

Both old and new frames decode to exactly 102,351,365 bytes, SHA256:
c69f12c27e6d8add12c06aa55478cca44009f4bd34275d41115f43552bf7dc93

Recompression used zstd 1.5.7 level 19, --long=27. CLI and frozen stock Rust
zstd 0.13.3 decoding matched the intermediate; independent Windows stdlib
decoding matched it too. The five runtime files other than gates.zst are unchanged.
The full circuit remains 2,005,557,255 raw records, Q646, raw u16le SHA256:
37cbc7b16b8670d7f20a2de44062a1aaf41849f5db705bcb2d5192046efaa2d6

Portable construction archive SHA256:
8d713f6da40a86b09e7ae2ffdf426d86081798f9351cae5f94fc172da897b56d

Decoded construction tar SHA256:
bd372cf410d9da271998632820521110f9454cdb5fb9a1af93d83d5c2c83727f

## Scope and limitations

The runtime is portable embedded data. Construction provenance declares external
original donor dependencies; those donor binaries were not regenerated. Two
fresh h11 assemblies from the declared dependencies matched the raw stream.
Primary 9,024 native shots and a fresh independent 9,024-shot paired panel were
clean (0/0/0). Finite qualification is not an all-input proof. The local stock
builder completed; local stock evaluation ended without a correctness verdict.
This framing check is not a new stock runtime or memory-fit result. The public
submission note records full method, dependencies, measurement and limitations.
