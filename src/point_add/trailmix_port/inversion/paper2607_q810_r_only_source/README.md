# Q810 R-only source components

Model attribution: gpt-5.

These are inspectable source components, not a standalone regeneration package.
The executable contest source is the Rust point-adder and its embedded fixed
primitive streams. No numerical score or whole-circuit validation is claimed
by these component files.

`q810_r_root_loan.py` applies the R-only replacement to an already loaded,
independently authenticated baseline. It does not load or identify that
baseline itself. It never assigns or wraps the T-sub hook. The selected R
observer and relocation callback preserve the existing control captures,
mode/sign work, endpoints, arithmetic argument order and caller bookkeeping.

For distinct roles `(acc, a, b, target, root)`, the selected cell is

```
X(root)
CCX(a, b, root)
CCX(acc, root, target)
CCX(a, b, root)
X(root)
```

It restores `root` on every input. It agrees with the original controlled cell
on the subspace `acc => root`; outside that subspace it is not a replacement.
The qualified R caller establishes this implication at its selected interior
cells even with its existing terminal capture. The implication must not be
assumed for a different arithmetic caller. In particular, no T-sub root loan
is installed here. Relative to the selected four-CCX dirty-helper cell, each
replacement has one fewer CCX and two more X gates, with no new wire or
measurement. Those local counts are not whole-circuit reduced counts.

The observer accepts only the exact two interior arithmetic cell sites per
source position. It checks distinct roles, literal gate shape, original
source observer flags, matching masks/steps and complete expected coverage.
All unselected instructions are copied unchanged. Its named helper verifier
accepts only the exact five-gate definition, not a general protected-wire
exception. The callback preserves capture-marker offsets and restores its
process-local R hook on normal completion or failure.

`q810_commuting_involution.py` is the exact original bounded 32-pending
X/CX/CCX reducer. `q810_primitives.py` retains the exact recursive primitive
traversal. `q810_stream_transport.py` retains the exact production packing,
cache release and zstd streaming functions, using the already established
564-wire local ABI. It accepts constructor/release callbacks but supplies no
baseline loader or command-line generation mode. Compression reproduction
also depends on the original Python and zstandard runtime versions.

The separate Python baseline has historical loading and evidence dependencies;
they are intentionally not represented as a completed portable package here.
No private source inventory, validation receipt, scheduler output, local path
or account credential is included. A complete public Python reproducer would
need a closed baseline/data package and its own native byte comparison before
being called reproducible. This limitation does not replace the separate
trusted validation of the actual Rust source and embedded streams.

Preserve the upstream notice in
`../paper2607_q810_corrected_data/UPSTREAM_LICENSE` when redistributing the
surrounding implementation. `manifest.json` binds only these component files;
it is not a whole-source or validation manifest.
