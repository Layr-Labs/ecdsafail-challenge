# Building the 652-qubit point-addition circuit

This is nasqret's 653-qubit nested-Euclid point addition (submission `5b3c90fe-dd61-48b3-8e02-3c8797a3daf9`) with one more
helper site removed from every stage. The Rust entry `build()` in `mod.rs`, `decoder.rs`, `schedule.rs`, the codec in
`construction/codec` and the readable generator under `construction/research` are theirs and are unchanged. The new files
are the overlay directory `construction/research/agents/midpoint-implicit-query-20261109/q652/` and the regenerated
`gates.zst`, `schedule.zst`, `gate_count.rs` and `TRACE-SHA256`.

On a little-endian host with Node 22 or 24, C++17, Rust and zstd, run these commands from the directory containing this
document.

```sh
cd construction
a=research/agents/midpoint-implicit-query-20261109/q652
node "$a/point.cjs" raw trace.u16le
node "$a/point.cjs" spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
bash codec/verify.sh trace.u16le rebuilt
```

The trace has 1,736,726,885 operations of eight bytes each. The Rust decoder expands them into the repository's native vector
of `Op` values; at 56 bytes per operation that vector occupies about 90.6 GiB.

## What the overlay does

`q652/point.cjs` is the entry. It fixes the configuration (width 652 and the patch lists below) and then loads the 653's
own sources by path. Every patch is a `[from, to]` text pair applied to the pinned source text at build time; each anchor
must occur exactly once or the build stops. Nothing of the 653 is edited on disk.

The 653 hands every stage twelve clean helper sites. At each stage boundary all helper sites are clean except the upper
stage's sign, so the stages can be narrowed one at a time:

| stage | file | what frees the site |
|---|---|---|
| short.divide | `q652/div10-rewrite.cjs` | the seventh count bit of the walks is hosted on wires that are idle in each phase (right pad, `Q[n-1]`, `L[0]`, `Q[n-2]`, the unused top of U); the walks run on six tag wires |
| short.multiply | `q652/mul/p-mul652.js` | the X+M carry is uncomputed around its single reader; one hole and a dirty-borrow constant add in the preparation; the C digit is undone across unit+power; the unit walk is the six-tag sector walk |
| history.regenerate | `q652/regen/p-regen.js`, `p-regen2.js` | five-tag signed walk; one tag hosted on `T[0]` while U is empty; the quotient bit hosted on M's top wire |
| upper.forward, upper.reverse | `q652/g129.cjs`, `q652/upper/`, `q652/upper652.cjs` | the fourth probe tag is hosted, window by window, on a helper that is idle in that window |

`q652/upper652.cjs` then narrows the tape to 652 wires and hands the field and history stages eleven clean sites.

## The 653 this is built on

The description below is nasqret's, kept for the parts of the construction that are unchanged. Two things it mentions are
replaced by the overlay: the three-hole preparation of the multiplier (now one hole and a constant add) and the sites that
hold the walk and probe tags.

The new input-independent entry is `q653-centerfix/point.cjs`. It reuses the complete coordinate driver. In early Euclidean slots the actual top bit of the remainder is zero after quotient-one preparation. If the packed number \(rv+u\) has its top bit set, the exact quotient is one. The other lanes normalize a 255-bit number. Their two additional height bits use the high storage and a known-zero explicit remainder bit, and the largest normalized quotient interval starts at height nine. The aligned sign comparison leaves the additional passenger bit at the lower end of the dirty carry and shifts the public comparison threshold by \(2^k\). Actual general rows grow the coefficient through \(2^{k+1}\), which bounds the centered error on both sides. This calculation includes every possible field passenger. [Centered sign implementation](construction/research/agents/midpoint-implicit-query-20261109/q653-centerfix/upper.cjs)

The positive-field multiplier uses three low valuation bits. Its three-hole remainder represents p−47 and is corrected modulo the selected variable modulus. One canonical inversion stores its high rank on the active coefficient rather than an extra helper. The divider runs descending rank groups on its two Euclidean walks and uses the genuine highest quotient bit as the active modular carry. The exceptional reduced positive moduli 2 and 3 share p mod m = 1. Signed negation cancels the dirty pad on inactive heights. The 128-bit winding top holds the retired normalization predicate where it is available. The coprime history replay rents a fixed left-one pad for its second terminal tag. The complete point preserves its independent orientation sign. [Short scalar and history sources](construction/research/agents/midpoint-implicit-query-20261109/q653-next/)
