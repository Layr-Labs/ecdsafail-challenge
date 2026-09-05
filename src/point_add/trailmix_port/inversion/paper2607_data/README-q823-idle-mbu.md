# Q823 retained-carry T-add source reproduction

Public attribution: gpt-5.

This source succeeds the masked T-sub source in PR197, commit
994672dfa7946f8fbbe4982715fe6ef4198b59b6. The fixed 1,616-step schedule, 577-lane local ABI, 567 owned
lanes, eleven clean auxiliaries and ten dirty passengers remain unchanged.
R-prefix arithmetic, the masked T-sub, original generic APIs and active
window table are preserved. Only the actual T-add caller changes to a private
implementation; the K1 path remains byte-identical.

For each nontrivial prefix, an unconditional MAJ sweep computes the carry.
The existing tight endpoint trie captures only its selected value in the
existing clean Tail wire. The masked reverse sweep completes the selected
sum and restores the addend, boundary carry and decoder scratch. The unchanged
selected-sign/upper-zero-map sandwich then executes with this retained Tail.

Delaying this complete sandwich is safe because its selected zero predicate
reads target bits strictly above the selected prefix, restored by the completed
addition. The dirty map can start at different values at this later point: its
conjugated top toggle gives the same selected predicate and restores every
dirty input. This is a claim about the complete sandwich, not that individual
map gates commute with the arithmetic sweep.

Tail is erased from the original addend and final sum by computing the carry
of addend plus complemented sum plus incoming carry, capturing at the same
selected endpoint, and reversing that scratch computation. The equal carry
identity is exact, including the case addend plus carry reaches the modulus.
Only one additional endpoint trie is needed; its reverse cleanup is unselected.

The complete affine-prepared T-add entry retains the inherited valid EEA
domain: Tail and all scratch lanes are clean; Sign and dirty passengers may
be arbitrary. A dirty accumulator is outside this entry contract. Although
the abstract arithmetic identity covers both incoming carry values, that does
not authorize dirty boundary scratch at entry to the full affine preparation.
All eight-bit endpoint encodings follow the actual tight trie, including its
aliases; no clipping of the encoded length is assumed. K1 uses the old path.

New arithmetic uses exact positive X/CX/CCX gates, without new measurement,
reset or relative-phase helpers. Unchanged affine/map code retains its existing
clean-ancilla measurement uncomputation and phase contracts. No new nonce fit,
gate stripping, sample selection, empirical window change or extra wire is
introduced.

The complete generator SHA-256 is cf926e6782c8c4606627c299733646db8ee7359d62d8ffe4e6c1ea23a91cd216. Actual generation and
independent decoding produced 90314369 packed primitive records,
40887697 raw lowered CCX operations and 26878536 primitive X operations
per traversal. These are source-stream counts, not a canonical whole-circuit
score. All five Rust stream counters are updated from these actual records.
A fresh source-bound 9,024-shot validation is required before any record claim.

The source cost check and complete native tests cover both directions, phase,
dirty restoration, full maps and caller interfaces. Four complete steps and
four extra component widths are finite evidence, not a universal proof of
the inherited empirical window support. Whole-circuit validation remains
separate from component equivalence.

Install the pinned requirements.txt dependencies. From this directory run:

```sh
python reproduce_q823_idle_mbu.py --output /tmp/q823-retained-tadd-fresh --workers 4
```

The output directory must not exist. The unchanged portable driver allows at
most four workers, 512 MiB each, with 180 seconds per 45-step shard. It emits all 36
shards through step 1616 with original production flattening and packing. A
bounded smoke can add `--start 226 --end 270`. The generator's original CLI
is retained: `python eea_circuit_s835_exactwidth_dirty12.py --n 256 --T 1021`
constructs one step and reports its interface.

Compressed shard bytes and decoded records must match the published source.
Timing and wrapper receipt fields can differ. The active Rust embedding reads
paper2607_exactwidth_data; chunks in paper2607_data are unchanged historical
material, not the active stream. This README, source-derived raw counts and
smoke tests are not evidence of whole validation or official acceptance.
