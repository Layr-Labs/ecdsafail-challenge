# Rebuild the Q651 gate-reduction circuit

This is a reversible secp256k1 point addition with one quantum point and one classical offset. It uses the upper Euclidean rows, history and field arithmetic of nasqret's Q651 submission b573fae1 and the Q651 stage geometry developed by jackylee0424. This revision also applies commuting-gate and affine reductions to the upper Euclidean computation. It extends the field and history compiler in gpt-astra submission d04ea485. No point coordinates, test vectors or sampled measurement outcomes appear in the circuit construction.

The field and history pass handles at most 128 consecutive X, CX and CCX gates at a time. Within that block it cancels equal commuting gates and combines products that share controls or targets. For two products into the same target it can propagate the later controls backward through affine gates. It uses an equivalent product of two linear forms when the quadratic coefficient matrix has rank two. Rank zero uses only linear gates. A gate that reads the target, a nonlinear update to a needed control, a measurement, and a conditioned phase terminate the corresponding rewrite. All transformations preserve the original wire count. The only classical feedback is the original constructor's.

Run these commands from the construction directory with Node 24 on a little-endian host.

```sh
node q651/point.cjs raw trace.u16le
node q651/point.cjs spans ranges.tsv
sha256sum -c ../TRACE-SHA256
GIR_THREADS=4 GIR_LEVEL=15 bash codec/pack-scheduled.sh trace.u16le ranges.tsv rebuilt
```

The raw stream has 1,601,882,895 operation records of four little-endian uint16 words. Its SHA-256 is 51e0e57a81d51421841feb74dbaeb161cf2721cd4eb27adef58594b51b1b9537. The span table has 2,327,698 entries. The packed schedule expands into the ordinary stock operations before evaluation. All source dependencies and the codec are included.
