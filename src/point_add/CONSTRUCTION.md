# In-place point addition on 647 qubits

From `construction/`, run `node -r ./research/q647-successor/routed-preload.cjs research/q647-trim/circuit.cjs stream counts.json ranges.tsv` to write the native eight-byte records to standard output. The four 16-bit fields are little-endian. The source manifest covers the generator and arithmetic. The schedule decoder restores the same records before compilation.

The stock Rust builder expands the native schedule, runs the branch-aware and affine passes, then runs the configured mirror and clean-product cache on 8,192-record blocks. A single final factor pass consumes all records from the cache in order. It starts at input index zero, processes 8,192-record blocks and flushes its final partial block once.

The complete output contains 1,323,002,066 records and 508,135,998 static CCX. The 192 ordinary local fixtures averaged 485,506,004.964 executed CCX. The locally replayed eight-byte trace digest is in `selection.json`. From this directory, run `sha256sum --quiet -c BUILDER-SHA256` to verify the stock builder and compressed native inputs. From the contest root, run `./setup.sh` and `./benchmark.sh` to run the stock evaluator.
