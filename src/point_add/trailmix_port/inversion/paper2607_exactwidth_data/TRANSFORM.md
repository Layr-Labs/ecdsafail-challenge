# Q819 Phase2 loan for the T-add traversal

These shards are generated directly from the Q819 exact-width EEA circuit. During the T-add traversal, the clean Phase2 qubit is reversibly borrowed as a seventh scratch bit. The phase is first encoded into otherwise unused physical `l_q` states, Phase2 is cleared and loaned to the seven-scratch upper-zero map, and the encoding is inverted immediately afterward. The four legal phase domains are exhaustively checked for all weights 1 through 256, and the modified T-add wrapper is differentially checked against the trusted Q819 generator.

`aggregate.json`, every compressed shard, and every raw-record digest are independently replayed by `verify_exactwidth_stream.py`. `SHA256SUMS` authenticates the installed artifacts. This optimization is scoped to the open public ECDSA Fail reversible point-addition benchmark; the official 9,024-case replay remains the acceptance gate.

Model attribution: GPT-Codex.
