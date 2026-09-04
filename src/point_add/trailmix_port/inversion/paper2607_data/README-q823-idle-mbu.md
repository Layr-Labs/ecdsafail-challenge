# Q823 RT-cache source reproduction

Public attribution: gpt-5.

This source extends the previously officially scored Q823/T191910893 submission
9f4db1c2661948753d53ccb9dba432ec82795343. It preserves the same1616-step schedule,577-lane local ABI,11clean
auxiliary lanes,10dirty passengers and all unrelated arithmetic.

R caches a stable two-control prefix in an existing globally clean idle slot,
clearing it before defining bits change. T uses the first unused recursive path
slot only at a shallow leaf; full-depth leaves retain the original dirty-helper
implementation. The established clean-C3X measurement channel restores its
helper and exactly corrects both measurement outcomes. No sampled gate removal,
nonce fitting or active-window change is introduced.

Actual complete primitive generation has88369029 records per
traversal and44486181 loweredCCX per traversal, compared
with45454881 in the submitted baseline. These are source-stream counts, not a
new whole benchmark score. New exact-source9024-shot validation is required.

Install the pinned dependencies in requirements.txt. In this directory run:

```sh
python reproduce_q823_idle_mbu.py --output /tmp/q823-rt-fresh --workers 4
```

The directory must not exist. The driver has four workers maximum,512MiB per
worker and180seconds per45-step shard. It emits all36 deterministic chunks
through step1616. For a bounded smoke add `--start 226 --end 270` to the command.
Dependencies, source pins and cache cleanup are checked.

Reproduction must match compressed chunk bytes and decoded records; elapsed
time, compiler-driver digest and wrapper metadata can differ from the private
build receipts. The active Rust embedding reads paper2607_exactwidth_data.
Older chunks under paper2607_data are retained historical donor material and
are not the active replacement stream. Do not treat either a smoke run or this
README as whole validation. All public provenance files identify their scope.
