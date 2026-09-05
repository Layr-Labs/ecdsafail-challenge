# Exact Chunked Bit-Length Queries

Implementation: inversion/chunked_bitlength.rs, dispatched from the private
bit_length_lean_middle helper. Enable MIDQ_CHUNKED_PREFIX=1. Workspace cap
MIDQ_PREFIX_QCAP defaults to1019, and MIDQ_PREFIX_CHUNK is a maximum size32.

## Preserved Function

For an n-bit source, the existing position deposit XORs n XOR index into its
destination, reduced to the destination width. index is the highest set-bit
position, or zero for the inherited all-zero convention. Let f_i be the AND
of the i complemented high source bits, with f_0=1. The Gray differences
(n-1-i) XOR (n-i), controlled by f_i, telescope to exactly this deposit.
Only the first n-1 source bits are needed; the lowest source bit is unchanged.

The new implementation computes these same prefixes into fresh clean flags,
so each deposit uses only X/CX rather than a two-control consumer. All source
bits are restored. The private callbacks in this file consume only the
deposited position and independent metadata, not the old KG network's
temporarily borrowed/complemented source wires. The new query cleans its
scratch before invoking that callback, and repeats the deposit if requested.

## Cleanup and Budget

Interior prefix flags are known ANDs, so HMR plus conditional CZ clears them
exactly even when later prefix flags or the position register remain entangled.
Keep one boundary flag per completed chunk. Clear boundaries right-to-left,
with the previous boundary still live: measure the boundary, replay only its
local prefix under that classical result, apply a CZ endpoint, and clear the
temporary replay ANDs by measurement. All correction phases cancel, including
global branch phases. No unknown qubit is reset to enforce a promise.

For r=n-2 fresh prefixes and chunk maximum k, b=ceil(r/k)-1 boundaries are
retained. A conservative scratch bound is k+b, including local replay.
The emitted Toffoli cost is r+b(k-1), and its expected cost on the benchmark's
basis-state tests is r+b(k-1)/2. Each boundary HMR outcome is uniform.
Choose the feasible k minimizing boundary replay, breaking ties by workspace.
For example r=76 and40 free qubits favor k=2 over k=32.
Insufficient headroom falls back to the original implementation.

## Evidence

The emitted-operation selftest covers1,113,024 basis/measurement cases across
source widths1..10, destination widths1 and5, multiple real chunk sizes, and
forced zero/one/alternating/random measurements. It checks all outputs,
input restoration, exact phase, inverse application and zero before every
reset. Unused public input wires are explicitly allocated in the fixture.

Against verified4d7ee72c, prefix-only integration at unchanged Q1024 measured
T15620702.484 with an initial chunk planner, then T15365803.692 with replay-
minimizing chunks. Both passed the frozen9024 inputs with0/0/0, retaining the
same five independent-corpus failures. Combining counter sharing, chunked
comparators and Boolean cleanup measured Q1019/T14748626.053 with the same
checks. The paired50048 corpus retains exactly34 failing inputs, identical
to the parent. Fresh-nonce validation is documented separately.

These are circuit scheduling and measurement-uncomputation refinements,
not a new GCD algorithm or a change to empirical arithmetic bounds.
