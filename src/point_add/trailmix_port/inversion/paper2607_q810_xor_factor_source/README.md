# Q810 saved-cache adjacent XOR factor

Attribution: gpt-5.

This standalone cache-transform program takes the exact public baseline cache
from commit a7f329a7b4ee87b532a5b3eff4c9ca8bf4f4915b. Supply its
src/point_add/trailmix_port/inversion/paper2607_q810_corrected_data directory as
--baseline-root. All baseline frame, metadata and aggregate hashes are checked.
The program does not download data or load an old private Python generator.
It is not a complete point-adder regeneration package.

Manifest SHA256: c6fcad951e3e497cc110b42e106cef8fdd19d864c8d36d48194bfff159ebda3a
Transformer SHA256: 3b3b0bcd1602035eb2ca08a7e00968df1b8d399e1b6964d1f8687d5fb434bb4d
Use Python 3.11 and the zstandard 0.23.0 C extension with libzstd 1.5.6.
The optional --index 0..35
reproduces one shard; omitting it reproduces all 36 and the aggregate, into a
new output directory. Invoke portable_transform.py with --baseline-root,
--manifest, --manifest-sha256 and --output explicitly. A partial failed output
is preserved and is not silently reused. No network operation is performed.

The six kernel source spans are identical to the independently decoded runtime
transform. The public command itself has not been executed as a separate gate.
The manifest binds the actual expected full raw profiles and compressed bytes.
All 36 baseline and transformed streams have a separate complete decoder proof;
that proof is not full elliptic-curve arithmetic validation or a numerical score.

Only adjacent original positive CCX pairs with exactly four distinct wires are
rewritten. For a common control and target, CCX(a,b,t);CCX(a,c,t) equals
CX(c,b);CCX(a,b,t);CX(c,b). For common controls, CCX(a,b,t);CCX(a,b,u) equals
CX(t,u);CCX(a,b,t);CX(t,u). These equal positive permutation matrices restore
all borrowed data and preserve relative phase and literal inverses. No clean
ancilla or measurement assumption is introduced. Non-CCX and step boundaries
are preserved; generated output is never rematched. No additional reducer,
nonce change, sample selection or model draw is performed.

Inherited paper2607_q810_r_only_source files describe the original R-only source
components only. They are preserved as provenance; they are not claimed to
generate this later factored cache. The executable Rust backend changes only
the actual stream count literals and consumes the newly verified embedded
cache. Whole-circuit Q/T and full9024 validation remain separate requirements.
Preserve ../paper2607_q810_corrected_data/UPSTREAM_LICENSE when redistributing.
