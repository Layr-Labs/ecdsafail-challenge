# Technique and source attribution

This candidate continues gnuchev's Q1011 circuit, submission
`77730236-301d-4504-a940-e4d81faf851d`, commit
`32ac05183feb4299efd38e75703eb24478955dc9`. The underlying inversion uses a
pipelined partial-Euclidean prefix followed by an odd-value GCD tail. The
reported resource target concerns the complete elliptic-curve point-addition
circuit.

The streaming Boolean proof engine in `q834_clean_and.rs` is copied unchanged
from welttowelt's Q834 submission `347258d5-dfc4-4bf3-91a1-4040ad600922`, commit
`af7bec983c8bc1478354080b58de972230d09769`. Its integration adapter recognizes
exact cleanup identities and supplies the corresponding measurement phase
corrections. Credit for that engine belongs to welttowelt and the Q834 source.

Other changes retain operand-length information, deposit trailing-zero shift
metadata directly, cache quotient popcounts, reuse odd-value and checkpoint
representations, and choose carry schedules according to available scratch.
The fused coefficient cells retain their explicitly qualified phase predicates.
When a checkpoint constant addition cannot fit its usual clean carries, an
exact controlled unit-addition identity uses a restored dirty donor instead.
These changes preserve the inherited logical widths and round schedule.

Implementation and review were performed using Codex/GPT-6 in a multi-agent
optimization campaign. The original project NOTICE and
`q834-original-NOTICE.txt` are retained verbatim, including their attribution to
Tanuj Khattar et al. and the specified upstream files. This note adds attribution
for the imported proof engine and does not assign it a new license.

`PUBLIC_SOURCE_IDENTITY.json` records the preserved Rust and required-data
hashes. It establishes source-staging identity, not a benchmark validation
result. The submission note should state the final submitted artifact's own
harness measurements separately.
