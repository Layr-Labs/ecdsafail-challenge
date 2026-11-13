# Public point addition on 647 qubits

From `construction/`, run the following command to emit the complete native circuit. The four record fields are little-endian 16-bit words. `sha256sum --quiet -c SOURCE-SHA256` verifies both parent arithmetic and the measured field-product overlay.

```bash
node -r ./research/q647-successor/routed-preload.cjs \
     -r ./research/q646-frontier/field/preload.cjs \
     research/q647-trim/circuit.cjs stream native.json ranges.tsv > native.bin
```

The field divider shares unchanged products in zero quotient padding and retires them by X-basis measurement with a conditioned CZ. The stock optimizer flushes outstanding parity and product operations before retirement. Its one existing reusable classical bit carries the outcome. In the complete field oracle test, all 647 wires and all independent phase coefficients matched for 512 inputs.

The native stream contains 1,330,738,568 records and has SHA-256 `82608d6c60ffa44f1f7ffce11d6568af4e8c39e75bf8c56909069e3ed65600da`. The Rust builder reconstructs this stream from the literal and schedule members. It runs the branch, affine, mirror, cache, factor and dirty-ancilla ladder passes in order. Both final passes keep a single 8,192-record window sequence across incoming chunks and flush the final partial window.

The selected circuit has 1,320,629,629 operations, 493,525,875 static Toffolis and 2,599,873 measurements. On the ordinary 192 OpenSSL fixtures the mean is 470,743,904.068 executed Toffolis. The compiled compact trace SHA-256 is `1f20d91fd60e38ca85ef91b3681fdcb7865a0a988da98c28e7465a72f041de07`. `BUILDER-SHA256` binds the Rust sources and payloads. The stock benchmark can be run from the enclosing contest root with `./setup.sh` and `./benchmark.sh`.
