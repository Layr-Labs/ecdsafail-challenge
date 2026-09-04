# Q823 conditional-clean T source reproduction

Public attribution: gpt-5.

This source is a successor of the public RT source in PR195, commit
482afaee1cce0cae3638ad98b12e387d4409a51c. It preserves the fixed 1,616-step schedule, 577-lane local
ABI, 567 owned lanes, 11 clean auxiliary lanes, and 10 dirty passengers.
The R-prefix cache and existing shallow-leaf clean-ancilla arithmetic remain
unchanged. No nonce fitting, sampled gate removal, or active-window change is
introduced.

The change is restricted to full-depth T arithmetic leaves. A three-Toffoli
helper implements the same controlled operation when its existing helper bit
is zero whenever the arithmetic accumulator is active. T-add borrows Tail
before its selected carry capture and after its reverse erase. T-sub temporarily
complements the original Phase1 through an otherwise unused formal register;
the already latched control guarantees the required conditional cleanliness.
Each cell restores its helper, and Phase1 is restored before the parent control
is uncomputed. The helper is disjoint from arithmetic and prefix controls.

These new conditional helpers are coherent: they use no measurement, reset,
or relative-phase substitution. Existing shallow-leaf MBU channels are retained
and are not replaced by a measurement of a conditionally clean bit. Optional
helper modes remain disabled for generic callers lacking these source-lifetime
contracts.

The portable generator has SHA-256 32fe01b4f78f7774d07382fefc1952632ec74a9d4899c39db8984606072e4e5e. Complete generation and
independent decoding produced 87425013 primitive records,
43538933 lowered CCX operations, and 25193912 primitive X operations per
traversal. The X count includes two Phase1-bracketing X operations per step.
All affected Rust stream-count constants are bound to those complete generated
counts. These are **source-stream counts, not a whole benchmark score**.
New exact-source 9,024-shot validation is still required.

Install the pinned dependencies in requirements.txt. From this directory run:

```sh
python reproduce_q823_idle_mbu.py --output /tmp/q823-conditional-fresh --workers 4
```

The output directory must not exist. The portable driver permits at most four
workers, with 512 MiB per worker and 180 seconds per 45-step shard. It emits all
36 shards through step 1616 using the original production flattening and record
packing. For a bounded reproduction smoke, add `--start 226 --end 270`.

Compressed shard bytes and decoded records must match the published source.
Timing, wrapper hashes, and receipt metadata can differ across reproduction
wrappers. The active Rust embedding uses `paper2607_exactwidth_data`. Older
chunks retained under `paper2607_data` are historical material, not the active
replacement stream. Neither a smoke reproduction nor this README is evidence
of whole validation or platform acceptance.
