# Q810 original-cache maximal XOR runs

Attribution: gpt-5.

The standalone program consumes the exact public baseline cache from commit
a7f329a7b4ee87b532a5b3eff4c9ca8bf4f4915b. Supply its paper2607_q810_corrected_data
directory as --baseline-root. It does not download data or import a private
generator. It is not a complete point-adder generator, and the preserved old
paper2607_q810_r_only_source components are not claimed to emit this new cache.

Manifest SHA256: 58515cfe689924d2681b26101eb21d037f096a2fba7afe411caa393904c13192
Transformer SHA256: f7b4c3b9f0d8823630fce8a332a20477dd1231040609dab2aec3da7032a48e68
Requires Python 3.11 and zstandard0.23.0 C extension / libzstd1.5.6.
Invoke portable_transform.py with explicit --baseline-root, --manifest,
--manifest-sha256 and --output. Optional --index0..35 selects one shard; no index
reproduces all36 frames and the aggregate. Output must be new, outside baseline.
Failures and partial outputs are preserved. The program emits exact 64-byte
witness streams as well as frames and public metadata. No network is used.

Six runtime and two pure-kernel function bodies are byte-identical to the
qualified maximal-run implementation. The manifest binds all36 independently
decoded raw profiles, compressed bytes, and complete witness hashes/ranges.
A separate bounded saved256/512 public-glue qualification is required by the
assembler; the full public command and all36 reproduction are not claimed run.

At each original CCX position, consider maximal common-control-and-target runs
in first-control then second-control order, followed by sorted-common-controls
target fanout. Choose largest CCX saving, then longest run, then shortest
replacement, then first mode. Non-CCX, step and shard boundaries are barriers.
Generated outputs are never rematched. Variable wires use first-encounter odd
multiplicity order. If m variables occur oddly, the replacement is one CCX
conjugated by 2(m-1) CX; if m=0, it is empty. Saving is L-(1 if m>0 else0).
Record and CX deltas are calculated independently, not inferred from pair counts.

These are exact positive permutation identities on arbitrary dirty inputs.
Parity pivots and fanout data are restored; arbitrary spectators, relative
phase, and literal inverses are preserved. No new quantum wire, measurement,
clean-scratch assumption, extra reducer, source nonce edit or sample fitting
is introduced. The 64-byte witnesses record step-local original/output interval
bounds, mode, two fixed wires, and saved CCX. Public source does not bundle that
large corpus: manifest hashes bind it and this program reproduces it exactly.

Only three stream-count literals in paper2607_eea.rs change. The outer operation
and Toffoli assertions use the unchanged WHOLE_* expressions; all other Rust,
nonce and arithmetic bytes are preserved. Count expressions are source-defined
expectations, not measured whole-circuit canonical Q/T. Full9024 and source/wire
privacy are separate gates. Preserve ../paper2607_q810_corrected_data/UPSTREAM_LICENSE.
