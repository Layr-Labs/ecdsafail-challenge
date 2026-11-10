# Building the 651-qubit point-addition circuit

This is our 652-qubit construction (submission `8933c99e-e85a-4e94-acad-d077f08a149e`) with one further helper site
removed from every stage. It builds on nasqret's 653-qubit nested-Euclid point addition
`5b3c90fe-dd61-48b3-8e02-3c8797a3daf9`, and through it their 654
`84d263be-672b-4721-ab6a-ea208760cf29` and 655 `d2edfbb2-a635-4f60-83c9-722b3785988b`.
The underlying generator and codec are nasqret's. Model: Claude Fable 5, effort xhigh. Harness: Claude Code.
Stage research was carried out by Codex sub-agents.

The new overlay is `construction/research/agents/midpoint-implicit-query-20261109/q651/`; the short entry is
`construction/q651/point.cjs`. The 56 inherited construction files, including the sibling q652 directory and the codec,
were checked byte-identical to the frozen 652 package. The overlay patches pinned source text at generation time;
it does not edit the donor files. The packed `gates.zst`, `schedule.zst`, `gate_count.rs` and `TRACE-SHA256` for publication
must be regenerated from this stream. The inherited Rust decoding path is retained.

On a little-endian host with Node 22 or 24, C++17, Rust and zstd, run from the directory containing this document
(`src/point_add`):

```sh
cd construction
node q651/point.cjs raw trace.u16le
node q651/point.cjs spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
bash codec/verify.sh trace.u16le rebuilt
```

The final trace contains 1,838,867,579 operations of eight bytes each. The integration's measured emission was
1,838,867,579 operations, 14,710,940,632 bytes, with SHA256
`93b565e261dfef42c2a9315c703229d871fd8c7069394ea0c399613407d19b02`.
The Rust decoder expands the trace into native `Op` values; at 56 bytes per operation the vector occupies about
95.9 GiB. Use the hash file belonging to this 651 artifact, not the 652 hash file.

## What the overlay does

Here `q651/` in the table denotes `construction/research/agents/midpoint-implicit-query-20261109/q651/`.
Its `point.cjs` fixes width 651 and the field, history and upper patch configuration. The convenience entry under
`construction/q651/` delegates to it. Each textual anchor must occur exactly once or generation stops.

| stage | file | what frees the additional site |
|---|---|---|
| short.multiply | `q651/mul/p-mul651.js` | logical 651: dirty lift ticks; five-tag sector walk; two-tag valuation sweep; product scratch on the cleared normalized modulus top |
| short.divide | `q651/p-divide-d4.js` | logical 646: c5 routed through Q/U/count/sign hosts; auxiliary-free inner/reverse walks; selected V top holds c5 during winding |
| history.regenerate | `q651/regen/p-regen651.js` | logical 654: carry-free arithmetic, controlled increment for orientation, five/four-tag walks with fire on T[0] and released tag 650 |
| upper.forward, upper.reverse | `q651/upper/p-zz-u3.js` | logical rank[2]=652 hosted window by window; omitted quotient spare; coefficient-top affine lease; retained high coefficient bit in probes |
| physical binding | `q651/p-map651.js`, `p-stage-map.js`, `upper651.cjs` | tape narrowed to 651; ten-helper native maps; removed logical sites excluded from dirty loans |
| residual small windows | `q651/p-small-as-is.js` | empty list: their direct emissions already fit |

Field patch order in `q651/p-field651.js` is `p-field652.js`, `mul/p-mul651.js`, `p-divide-d4.js`, then
`p-stage-map.js`. History's complete `p-regen651.js` replaces the older regenerate list. The upper loader applies
the inherited upper lists followed by `p-zz-u3.js`; `upper651.cjs` then applies the tape mapping. Do not combine these
bundles with earlier alternative patch lists or apply the history-map edits twice.

Each half still runs
`upper.forward -> short.multiply -> short.divide -> history.regenerate -> upper.reverse`.
The physical clean helper set is **512,641..647,649,650**; persistent sign is physical 648. Physical 640 is data.
Backend logical 640 maps to physical 512. Divide first remaps its remaining logical 651 to 646 and 653 to 647;
history maps logical `0,1,130,131,388,646,647,648,649,650` in order to the common clean sites. Stage-local logical 648
must not be confused with the persistent physical sign.

Measured against the 652 stream, the complete emission adds 102,140,694 operations and 59,768,820 emitted CCX.
It uses 638,962,281 emitted CCX in total. These are static emission counts, not a grader mean or score.
The complete physical census has zero touches at wire 651 or above, including stage gaps. The maps add no operations.

## The construction this is built on

The inherited 653 uses a centered, truncated-quotient Euclid ladder with a midpoint stop and independent orientation
sign. Its short multiplier, divider, history replay and aligned sign comparison remain the underlying arithmetic.
The 654 supplies the sector-walk machinery and tag-count choices; the 655 supplies earlier field and per-stage mapping
code through the pinned source chain. Those source files are included unchanged.

The 652 overlay already replaced three-hole multiplier preparation with one hole and an exact constant add, uncomputed
the X+M carry around its single reader, uncomputed the C digit across unit/power, hosted the seventh divide count bit,
reduced history tag use, and hosted upper's fourth rank bit. Its balanced 129-wire probe split remains where applicable.
The 651 patches build on those changes; they do not reinstate the original three-hole preparation or original tag sites.

All new windows use fixed gate lists, active-entry known values, restored dirty loans, or inverse-paired inactive
bodies. The exactness discussion and window tables are in the accompanying public note. These are hand arguments
relative to inherited valid-entry contracts, supported by emission censuses and finite checks, not machine-checked
end-to-end equivalence. Invalid baseline inputs are not given a new correctness guarantee.

## Validation status

The composed source package passed the full physical emission ban, all six native map checks, stage bans and the named
multiply, history, upper and divide stress checks. Both public CLI modes were exercised through complete emission to
discard sinks, and the raw-byte hash above was reproduced; a 14 GB raw file was not materialized in that check.

The integration report did not establish full-point semantic replay, codec round trip or grader evaluation. Publication
requires recording those outcomes against this trace in the accompanying note. The commands above reproduce and verify
the artifact; their presence here is not a claim that packing or verification has already completed.
