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

The single most important operational fact: **a persistent-set reduction only pays if you lower `TLM_TARGET_Q` by the
same amount**, because the vent pool expands to fill whatever you free. The second most important: **only a
byte-identical `ops.bin` or a full 9024-shot run is evidence.** A healthy peak/Toffoli probe proves nothing.
