# 649-qubit secp256k1 point addition

The native source in `construction` implements point addition, multiplication, division and Euclidean history reconstruction. The 649-qubit layout has eight physical helpers and retains the orientation qubit at index 648. The Rust entry is `point_add::build()`. The stock evaluator selects its 9,024 inputs from the emitted gate stream and verifies coordinates, phase and scratch.

The upper walk drops low bits that are known zero in each enabled restoring digit. It uses clean carries in the main affine digit and the mixed-coefficient calculation. The short-field walks store normalization decisions in existing data positions for the portions of the walk where their values can be recovered. The divide, multiply and signed-history implementations use different numbers of directly available tag bits. [Upper implementation](construction/research/q649-record/upper/main.cjs) · [Normalization code](construction/research/q649-record/field/relay.cjs)

This construction uses jackylee0424's Q649 stage layout, nasqret's shortened digits and physical circuit optimizations, and a normalization construction from the published Q647 source. [Q649 donor](https://api.ecdsa.fail/api/submissions/02e0a2ac-c7d1-4727-a728-4381e1fc3aa0) · [Q650 circuit construction](https://api.ecdsa.fail/api/submissions/6aef5188-d0a9-41fe-bb3d-23de573a8a85) · [Q647 source](https://github.com/Layr-Labs/ecdsafail-challenge/tree/bf08239dfa9ce977cda5c11e62a1646125c64ac4/src/point_add)

From the extracted `src/point_add/construction` directory run the following on a little-endian machine with Node, a C++17 compiler and zstd.

```sh
sha256sum -c SOURCE-SHA256
node research/q649-record/circuit.cjs check forward 96
node research/q649-record/circuit.cjs check reverse 96
node research/q649-record/circuit.cjs scheduled trace.u16le ranges.tsv > native.json
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv compact
```

`selection.json` next to the Rust entry records the compiler used and emitted length. The graded package contains the compressed gates and their schedule.
