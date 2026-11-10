# q650 history.regenerate (ledger), v2: evicts logical 388 and SAVES ops

Worktree `/Users/akashbalasubramani/Desktop/ecdsafail-650regen`, branch `q650-regen`. Local only; nothing pushed/posted/submitted.

## Result

history.regenerate runs on **9 helper sites** (logical `0,1,130,131,646,647,648,649,650`). Logical **388**
(park's `Jtop`) is never referenced: the generator's port check bans it, and the census confirms it. The stage
stays pure NCT, with no new phase/HMR/measurement records.

| | 651 regen | q650 v1 (integrated) | **q650 v2 (this)** |
|---|---:|---:|---:|
| ops per call | 80,844,042 | 112,736,463 | **76,141,719** |
| delta per call vs 651 | | +31,892,421 | **−4,702,323** |
| whole circuit, measured (full generator, 651 tape) | 1,838,867,579 | 1,902,652,421 | **1,829,462,933** |

v2 versus v1 is **−73,189,530 ops** on the whole circuit. Integration is unchanged from v1: the same `R35_REGEN`
file (`q650/regen/p-regen650.js`) and the same `p-map650-history.js` geometry. Re-pack and re-run fasteval with it.

## What changed since v1

1. **Aux-free walks** (`walkaf.cjs`). This is the regen's own SectorSigned source (the q654-next `split`) with exactly
   the six aux-elimination edits the 651 divide made for its D2 walks (`q651/p-divide-d4.js`, D2Flat). A source diff
   shows D2Flat = split + these edits and nothing else:
   - qcond and the sector match use zero `tag[0]` instead of aux;
   - the digit's constant-one top is flipped `tst`, with a dirty-temp `dirtyDigit`;
   - the restoring loop uses `r[i]` as carry and `fire` as the constant top;
   - `restore()` uses `dirtyDigit`.
   `aux` is pointed at a banned site, so any leftover use throws. The walk's scratch data wire **L[129]** is then idle
   during the walk.
2. **Stage-4 walk back to the 651 configuration:** SignedAF(n,4), tags 647,648,649 + row-top, fire 650. The parked bit
   b rides on L[129]: it is swapped 650↔L[129] after the walk's shift block and swapped back at the walk's end.
3. **walk6 at the class maximum, 7 tags:** 647..650, T[1], L[129], row-top; fire T[0]. Seven tags means one sector per
   row at n=128. The V ∈ {2,3} remap from v1 is kept; it was re-validated for this walk.
4. **Scale back to one core.** After the uncontrolled 7-tag normalization, F=[clz≥2] goes on M's known-one top and is
   flipped to G=[clz≤1]. Under G, M's two low bits move to tag wires 0,1 (tags 5,6, zero when clz≤1). Then M[0],M[1]
   are zero in every case and host b and the sign uniformly. The single core (TopHost, carry-free; f=650, yq=130,
   sign=M[1]) reads M's low bits from wires 0,1. Only the gates touching those wires (~47K of 8.0M) carry G as an
   extra control. With G=0 they vanish, which equals "low bits 0". This is exact by `lowzero.cjs`, below.

## Helper map (regen order)

| window | helpers / hosts | contract |
|---|---|---|
| park (entry) | tags 647,648,649,650,646,0,1; f 131; yq on normalized M top; b on 130 | Constant-one M-top arithmetic. Before denormalization (tags = clz), b moves 130 → T[127-clz] (zero below the parked q, U empty). Then 130↔647, so V=1 keeps b on 647 |
| exchange | — | |
| walk6 | SignedAF(n,7): 647,648,649,650,T[1],L[129] + row-top; fire T[0] | T[1] is zero for V ≥ 4; L[129] is idle in the aux-free walk. V=1: exhaustively transparent on {647,T[1]}. V ∈ {2,3}: remapped to the V=1 state (id on 648/649), then rewritten to their own outputs |
| scale | tags 647,648,649,131,646,0,1; f 650; yq 130; sign 130 → M[1]; b → M[0] | 647↔T[0] (V=1). b sits at T_rot[127] for every V after normalization, so the move is uniform. G-masked low bits as above. b ends on 650 |
| walk | SignedAF(n,4): 647,648,649 + row-top; fire 650; b on L[129] | 651 tag count |
| exchange | — | |
| park (exit) | as entry | 650 → 130, then the inverse park consumes b |

## Cost per call (vs 651)

| window | 651 | v2 | delta |
|---|---:|---:|---:|
| park ×2 | 0.71M | 0.98M | +0.27M |
| walk6 (5 tags, aux → 7 tags, aux-free) | 27.68M | 14.29M | **−13.39M** |
| scale (1 core → 1 core + masked low bits) | 8.04M | 8.11M | +0.07M |
| walk (4 tags; aux → aux-free, dirty digits) | 44.42M | 52.76M | +8.34M |
| total | 80.84M | 76.14M | **−4.70M** |

## Checks run (final source)

| check | result |
|---|---|
| bit-sliced simulator vs oracle U = (v==1 ? 0 : p·(r mod v)^-1 mod v); R,V,Y unchanged; every non-data logical wire clean | 4,096 random Euclid midpoints: 0 bad. 4,096 mixed (midpoints, v=1, synthetic coprime pairs): 0 bad. 256-lane seeds: 0 bad |
| directed edge set, 1,566 cases | every V bit length 1..128 with b forced 1 and 0 plus random R; V ∈ {1..5, 2^126(+1), 2^127−1, 2^127, 2^127+1, 2^127+3, 2^128−1, 2^128−2} × R specials; genuine and small-x midpoints: **0 bad** |
| census | 388 untouched in all 7 windows; non-data wires touched = 0,1,130,131,646..650 |
| `lowzero.cjs` (exact) | core emitted unmasked from w0=w1=0: no gate ever makes them nonzero (47,056 gates touch them; 0 zero-breaking targets). So the G=0 circuit equals low bits 0 for any w0,w1 contents. The mask control M[127] is never a target in the core |
| `smallv.cjs` (exhaustive) | V=1: joint {647,T[1]} transparency, 4/4. V ∈ {2,3} with b on T[1]: 6/6. V ∈ [4,7] with b on T[2]: 28/28 |
| full generator (q651/point.cjs spans, 651 field/upper/map, R35_REGEN=p-regen650.js) | ops **1,829,462,933** = 1,838,867,579 − 9,404,646 exactly; width 651; traceSha256 a9e77dc8…f21444; 172 s, 1.0 GB RSS |

Not run by me: pack and fasteval of the 650 tape (hole's pipeline). Exactness rests on the inherited regen and walk
contracts, the divide's argument for the aux-free walk edits (same plan text), and the checks above.

## Files (`src/point_add/construction/research/agents/midpoint-implicit-query-20261109/q650/regen/`)

- `p-regen650.js`: the R35_REGEN list (unchanged entry point).
- `regen650.cjs`: the stage emitter.
- `walkaf.cjs`: the aux-free walk, derived from the split source by the six anchored edits.
- `p-map650-history.js`: history geometry, unchanged.
- Tools: `sim.cjs`, `edge.cjs`, `census.cjs`, `lowzero.cjs`, `smallv.cjs`, `smallt.cjs`, `v1probe.cjs`, `live.cjs`,
  `peak.cjs`, `zeros.cjs`, `snap.cjs`, `blockcensus.cjs`, `load.cjs`.

## Remaining levers (small)

- The stage-4 walk pays +8.3M/call for dirty-temp digits. A clean temp would need one more free wire in that walk,
  and none exists: T holds U + q_low, and every helper is live.
- An aux-based 7-tag walk6 (T[1],T[2]) measured 12.2M versus 14.3M, but it needs 17 small-V states remapped, more
  than the transparent id space allows.
- Park's b placement costs 0.13M/call; a rotation-based placement could cut it.
