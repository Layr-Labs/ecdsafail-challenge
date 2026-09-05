# Q823 masked-carry T-sub source reproduction

Public attribution: gpt-5.

This source succeeds the conditional-clean T source in PR196, commit
8266b1052865c2c08282548f9d6d62eb231f2242. The fixed 1616-step schedule, 577-lane local ABI, 567 owned
lanes, eleven clean auxiliaries and ten dirty passengers remain unchanged.
R-prefix caches, T-add and its midpoint handling, original generic T-sub API,
active-window table and paired Phase1 X bracket are retained.

The actual T-sub caller alone uses a new private entrypoint. Its carry sweep
is unconditional; only sum writing is controlled. The existing tight unary
decoder generates a low prefix of masks, so the literal inverse implements
the same selected-prefix subtraction. The eight decoder lanes and dedicated
accumulator are clean on the inherited EEA block domain. The boundary carry
may be arbitrary, and every work, metadata, scratch and borrowed wire is
restored except the selected target sum. A dirty accumulator can produce a
suffix and is deliberately unsupported; the generic API remains unchanged.

The new T-sub arithmetic uses no measurement, reset or relative-phase helper.
Unchanged parts of the source still contain their existing clean-ancilla
measurement uncomputation. No sampled gate removal, nonce fitting or support
window change is introduced. The uniform controlled-adder starting point is
Appendix B of https://arxiv.org/html/2607.13816v1; the variable-prefix decoder,
actual caller lifetime and source-specific inverse are separate obligations.

The complete generator SHA-256 is d38bc62563bb27f6bca38c7beb6609f086b4d8e1bfc8ac506e8387bce2d87531. Actual generation and
independent decoding produced 86760689 packed primitive records,
41650689 lowered CCX operations and 25193912 primitive X operations per
traversal. All five Rust stream counters are bound to these generated counts.
These are source-stream counts, not a canonical whole-circuit score. A fresh
source-bound 9024-shot validation is required before any record claim.

Install the pinned requirements.txt dependencies. From this directory run:

```sh
python reproduce_q823_idle_mbu.py --output /tmp/q823-masked-fresh --workers 4
```

The output directory must not exist. The unchanged portable driver allows at
most four workers, 512 MiB each, with 180 seconds per 45-step shard. It emits
all 36 shards through step1616 using original flattening/packing. A bounded
smoke can add `--start 226 --end 270`. The generator's direct CLI is also
preserved; `python eea_circuit_s835_exactwidth_dirty12.py --n 256 --T 1021`
constructs one step and reports its interface.

Compressed shard bytes and decoded records must match the published source.
Timing and wrapper receipt fields can differ. The active Rust embedding reads
`paper2607_exactwidth_data`; chunks in `paper2607_data` are unchanged historical
material, not the active stream. Smoke tests, this README and source-derived
counts do not establish whole validation or official platform acceptance.
