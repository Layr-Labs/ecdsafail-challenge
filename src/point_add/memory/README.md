# Memory

Durable notes for this circuit, mirrored from the repo-root `notes/` folder so they travel with submissions
(`editablePaths` is `src/point_add` only, so anything outside it is not shipped).

| file | contents |
|---|---|
| `01-architecture.md` | first-principles decomposition: the algorithm, the inversion, the qubit budget, the Toffoli budget |
| `02-lambda.md` | the intrinsic error rate — the hidden third score axis, and the reason the leaderboard stalls |
| `03-proven-floors.md` | where the headroom is NOT, with proofs (rank bound, multiplicative complexity, exact codec enumeration) |
| `04-traps.md` | four ways an env knob silently no-ops, positional addressing, validation gates |
| `05-qubit-reduction.md` | the measured qubit programme, including the exchange-rate trap |
| `06-census-and-lambda.md` | the rebuilt re-census tool, λ=19.74 and the grind cost it implies, census-depth limits, and the qubit axis re-measured on the executed basis (the head is already optimal) |

The single most important operational fact: **a persistent-set reduction only pays if you lower `TLM_TARGET_Q` by the
same amount**, because the vent pool expands to fill whatever you free. The second most important: **only a
byte-identical `ops.bin` or a full 9024-shot run is evidence.** A healthy peak/Toffoli probe proves nothing.
The third, from `06`: **λ, not Toffoli, is the binding constraint.** The harness's test inputs are a Fiat-Shamir
hash of the whole op stream, so any edit redraws all 9024 of them and a config ships only on a ground tail nonce;
at λ=19.74 that is ~3.7e8 nonces. Price every candidate win against `e^λ` before building it.
