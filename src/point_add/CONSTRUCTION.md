# In-place point addition on 647 qubits

From `construction/`, run `node -r ./research/q648-frontier/grade/six-clean-trial.cjs research/q647-trim/circuit.cjs stream counts.json ranges.tsv` to write the native eight-byte records to standard output. The four 16-bit fields are little-endian. The source manifest covers the generator and arithmetic. The schedule decoder restores the same records before compilation.

The Rust builder applies the branch-aware and affine passes, then processes blocks of 8192 operations using the configuration in `config.rs`. The clean-product pass restores each borrowed wire using measurement with a controlled phase correction. All quantum input ports are declared before gate execution. `selection.json` records the complete native and compiled stream hashes.
