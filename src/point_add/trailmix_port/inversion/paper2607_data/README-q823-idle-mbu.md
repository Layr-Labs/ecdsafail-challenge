# Q823 paired T-sub decoder with retained T-add

Attribution: gpt-5.

This source starts from public commit 1bb712e7f4db8a5e64df93c6e243d25389f1ff5d and preserves its complete
retained-carry T-add, R blocks, fixed 1,616-step windows, metadata encoding, dirty
passengers and arithmetic schedule. The generator SHA256 is 16e1bf06d353fe95ff8a6aad1d0e977c976b6651d8c90a0d54a3351dff179072.
Only the private T-sub unary tree uses the qualified paired compute/erase
transport. `paired_codec.py` validates the typed markers, including rejection
of unsupported annotated operations. No new nonce fitting or gate stripping
is performed.

The active P26EEA3 stream stores nine kinds. Kind8 is a paired compute and kind9
its matching erase; both Qiskit coherent definitions are CCX. In native forward
emission, compute is CCX and erase is measurement reset plus classically
conditioned CZ. In native reverse emission the record order reverses and the
roles swap once. The saved forward words must not also be pre-swapped. Existing
kind7 clean-C3X measurement cleanup is unchanged. All arithmetic/measurement
promises remain tied to the caller and paired-helper lifetime contract; the
markers are not valid arbitrary dirty-target replacements for CCX.

The complete generated stream contains 90314369 packed records. Actual
direction-aware lowering counts agree forward and reverse: 40328305 CCX and
103294673 native operations per traversal, with 4,699,696 HMR and 4,699,696 CZ.
These are raw stream counts, not a canonical whole-point-add score. The Rust
count-only stub stays disabled; the active decoder emits every stored record.
No whole benchmark result is claimed by this reproduction manifest.

The five lowering constants and 36 include paths in the integrated Rust backend
are the only differences from its qualified source snapshot. All remaining
backend bytes, including the direction-specific emitter, are preserved. The
legacy P26EEA2 streams remain unchanged and inactive for this new embedding.

For optional local reproduction install the exact versions in requirements.txt
and run the existing `reproduce_q823_idle_mbu.py` entrypoint with a fresh output
directory. Its name is retained for compatibility; its implementation now uses
the pinned typed paired codec and writes P26EEA3. The two support modules,
certified windows, original historical flatten source and license are included.
The wrapper is source-derived and has not yet undergone a separate standalone
reproduction smoke check. This does not substitute for the independently
decoded submitted streams or whole-circuit validation. Historical INERT/draft
comments in the exact codec/backend refer to their earlier preparation stage;
they are not a claim that this active embedding skips those records.

Source, counts and bounded lifetime evidence are distinct from full 9,024-shot
validation and official score acceptance. The source-ready receipt records the
actual stage without manufacturing a score.
