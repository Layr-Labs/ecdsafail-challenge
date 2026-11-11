# 648-qubit secp256k1 point addition

The two quantum coordinates occupy 512 wires. The lower arithmetic reuses seven helpers at q512 and q641–q646. The orientation wire is q647. The public Q648 construction supplies the reversible point-addition shell and the register layout. The revised upper divider and field routines run inside that shell. [Public Q648 source](https://github.com/Layr-Labs/ecdsafail-challenge/tree/c538abfa9b42aa0445a1de8e049558438da7617b/src/point_add)

The upper rows write their low coefficient as a masked payload. Keeping the flag as a control on the permanent low writes and the boundary carry avoids materializing those bits. Truncation removes the provably zero low positions of the restoring digit. Both changes work in forward and reverse gate order. Normalization in the lower multiplier stores shift information in temporarily zero positions of the shifted field word. Division and history reconstruction restore the same seven helpers. The coordinate squarer uses eight-bit limbs in 64-bit windows. [Upper rows](construction/research/q648-trim/upper/index.cjs) · [Field routines](construction/research/q648-trim/field/index.cjs) · [Squarer](construction/research/q648-trim/alternate/square.cjs)

To reproduce the native circuit, enter the extracted `src/point_add/construction` directory on a little-endian host. The 96-point fixtures include exceptional sums and infinity.

```sh
sha256sum --quiet -c SOURCE-SHA256
node -r ./research/q648-trim/refinements.cjs research/q648-trim/circuit.cjs check forward 96
node -r ./research/q648-trim/refinements.cjs research/q648-trim/circuit.cjs check reverse 96
node -r ./research/q648-trim/refinements.cjs research/q648-trim/circuit.cjs scheduled trace.u16le ranges.tsv > native.json
GIR_THREADS=3 GIR_LEVEL=18 bash codec/pack-scheduled.sh trace.u16le ranges.tsv compact
```

The refined circuit shares a coefficient word in all 126 early unit rows, uses a direct circuit for additional late sign markers, borrows a restored history bit for the subtract-by-one predicate and borrows a clean quotient position in history reconstruction. Both directions of each transformation use the same physical wire budget.

The Rust entry point is `point_add::build()`. The compact files store the input-independent trace and its lossless schedule. When selected, the additional compiler combines adjacent products and replaces a second Toffoli with a measurement and phase correction only if its target provably holds the AND of its current controls. Conditional scopes track the active branch and merge at the exit. The adjacent `selection.json` identifies the exact emitted trace, compiler, operation count and static CCX count. The stock evaluator independently measures the executed Toffolis.
