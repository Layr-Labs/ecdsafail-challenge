# q650 upper width work (WIP, not wired into ../upper.cjs)

`p650-probe3.js`: removes logical tags[1]=651 from every aligned sign probe. Apply after ../p650-coef.js. It REPLACES ../p650-tail.js
(it carries its own tail-digit entry) and must not be combined with it.
- wideBand rows (k<=95), data probes: 2 passes, rank bit 1 constant per pass. The prefix ladder writes G(L)
  (compressed rank, or a sentinel for lanes outside the pass); the deposit is gated by register != sentinel. Rows with a full rank range get singleton passes.
- wideBand rows, retire probes: f1 (reset by hmr) hosts bit 1; the phase deposit goes to dirty y wire 640 (write;Z;write;Z).
- non-wideBand rows (96..124), all probes: v[k] (V's top, 1 on taken lanes) hosts bit 1 after CX(take->v[k]). The alignedMix
  lease of v[k] is disabled, and those tail digits take the dirty path.
Checks (harness, 64 lanes): production round trip exact, runFold fwd and rev exact, CENSUS=651 shows no probe window.
Cost vs the savings build (production, per ladder): forward +69.4M, reverse +5.8M, so +150.4M whole circuit.

`p650-v112.js`: v[k] hosts bit 1 in the row-112 trial/witness and in rows 113..125 estimate/removeDebt (about 0 ops).
`p650-trial.js`: quotient trial and witness in rows 0..111 run passes with rank bit 1 constant. G(s) (s+1 in deep rows) is written by the
prefix ladder over the top maxShift bits; a barrel shift replaces normalize. Taken lanes outside the pass are parked on S1->S2 with take
cleared, so every band write is identity for them. Adds constant-control support (-301/-302) to mc/toggle/indicator.
Order: ../p650-coef.js, p650-probe3.js, p650-v112.js, p650-trial.js. With these four, logical 651 is used only by affine (papers).
Production per ladder vs the savings build: forward +92.6M, reverse +40.0M, so +265.1M whole circuit (+234.9M vs the 651).

`p650-affv.js`, `p650-aff4.js` (papers; copied from ecdsafail-650mul q650/upper-affine/): affine rows 7..125 without tags[1].
`p650-aff0.js` (ringhole): affine rows 0..6 use the pass machinery of p650-trial.js. Window = normalizeA..guardedBarrel(r),
with the original carry-based guard/park/product, rank bit 1 constant per pass, and the ladder gated on take. Untaken lanes then hold 0 in every
helper-hosted rank wire, so the parking pattern S2 (it has a helper bit set) is unreachable for them.
Fix in p650-trial.js: the ladder deposits are take-gated for the same reason. Data-hosted rank wires (hi/free, v[k], A128, b256)
are arbitrary on untaken lanes and could otherwise hit S2.
FULL ORDER: ../p650-coef.js, p650-probe3.js, p650-v112.js, p650-trial.js, p650-affv.js, p650-aff4.js, p650-aff0.js.
Result: logical 651 is never touched anywhere in the upper (harness ban=651 passes on the production round and runFold fwd/rev).
Production per ladder: forward 346,599,805, reverse 327,177,142, so +306.4M whole circuit vs the savings build and +276.1M vs the plain 651.

Savings on the width stack:
- `p650-save2.js` (apply last): clean digits for affine mixedV in rows 0..63 (pick is free after the early normalizeA^-1), and the
  row-112 probe tail keeps its clean f2 digit. -5.3M whole circuit.
- `p650-trial.js` update: overflow values of a full rank class form ONE extra class instead of one singleton pass each
  (trial/witness/affine-0..6 passes 259 -> 244). -17.7M whole circuit.
WIDTH stack now: production per ladder 341,495,704 / 320,781,649, so +253.1M whole circuit vs the plain 651.
