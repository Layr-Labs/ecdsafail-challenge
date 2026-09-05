# Q817 identity-stream source reproduction

This directory contains the exact source for the new Q817 R identity-stream
candidate and its two disclosed public support modules. The generator hash is
`b7ff97de22b36450d6fee3f267be62a00d8be24f6988849655e1fea04c9374d2`.
The implementation donor is public commit
`fdc8559391145bd057d582d57c82dc96608b4f20`. The support modules are the separately
identified public Q823 support sources pinned in `reproduce_identity.py`;
they are supplements, not files claimed to have originally accompanied Q817.
The preserved upstream license is `../paper2607_data/UPSTREAM_LICENSE`.

The executable contest circuit is the Rust backend and its embedded new
`paper2607_q817_identity_data` streams. The older source/reduced data are kept
as historical context and are not silently used as the new identity pipeline.
The historical reducer identified by hash
`212d5a207e11f606cde15c21cd8dd3cd489e0f98ac2f0b3837df17161b233391`
has not been recovered. This reproducer neither invokes nor substitutes it.

Use Python3.11.5 and Qiskit2.1.2, matching the source-generation environment.
The driver authenticates all four adjacent source/window inputs before imports,
compiles their source bytes directly, bypasses bytecode caches, disables cache
writes and clears all exposed constructor caches before and after every step.
It invokes the fixed n256/T1616/Aux5 source API with measurement_uncompute=False.
The actual local interface is571 wires:561 owned plus10 arbitrary dirty lenders.
The production flatten/pack routines preserve all seven primitive kinds;
kind7 is lowered by the Rust backend as two CCX plus a measurement-based
temporary-AND erasure. It is not a plain coherent CCX record.

For a complete shard, run, for example:

```
python3.11 -B reproduce_identity.py --start 226 --end 270 --output shard-0226-0270
```

The output directory must be new. Repeat with the36 source-defined ranges
1..45,46..90,...,1576..1616 for a complete schedule. Single-step runs are limited
to the four qualified boundaries1,256,1021,1616. The driver writes a complete
uncompressed P26EEA2 frame, raw step files, raw hashes/counts and observed cache
counters. Compare each raw step and prefix hash to the corresponding public
sidecar. A changed hash is a failure, not a reason to change a seed or retry a
different logical draw. No logical input/measurement/model draw is generated.

Source-generation compression originally used level3. Final packaging uses
Python zstandard0.19.0, level19, threads0, write_checksum=True and
write_content_size=True on each complete known-length frame. The same frame
must decode byte-identically in both zstandard0.19.0 and0.23.0; exact compressed
bytes are tied to the producer version, while the raw step hashes define
source reproducibility. Both framing and every raw step are checked against
the original independently decoded generation before packaging. Compression
changes no arithmetic and is not a canonical resource-count improvement.

For clarity, the original donor remains preserved in the authenticated Git
history. The new portable capsule excludes21 generated Python bytecode cache
files, preserving all their corresponding Python sources. It also replaces
legacy attribution text with neutral `[redacted]` labels; this does not credit
old work to the new submission. Fourteen ordinary tool-name occurrences in
historical application code remain under exact source-bound application
contexts. The historical driver interface and command selection are unchanged;
only three default submission-attribution strings are redacted. Rust changes
for this privacy step are one comment and one emitted attribution metadata
value, not arithmetic or source selection.

The complete-generation counts and source reproduction are distinct from
whole-circuit validation. Canonical Q and executed Toffoli cost must come from
the exact final source's complete trusted9024-shot validation. This source
README is not an official platform acceptance or a whole-score claim.
