> This directory is zuiris's `lane_a_post` from ecdsa.fail submission 94ce452b, carried here unmodified. The text below is his own credits file; "our" in it means zuiris.

# lane_a_post: credits

Our own code (round 105 lane A, ported into the build by the merge lane), written from mechanism descriptions in
public submission notes, not from their code:

- Hold pass (keep a product alive on idle wires instead of rebuilding it): the value-model hold of haotang1995
  (dca38d60), its relocating form (c0bcef05), and the bounded-memory hold pass of STARKmaxUnderpants / odinfree
  (7c9d4ea6). Our version keys products by XOR-of-atoms hashes, holds in place after a measured release, and uses the
  tree's truth-table model to find more idle wires.
- Pair rules (cancel, fan-out, shared-control merge of Toffolis that commute together): the peephole of RealAdii
  (72ac5500, 6aef5188) with the Swap barrier of 5a0acc7a (STARKmaxUnderpants / odinfree).
- The truth-table model the hold pass reads (tzmodel.rs is an inline-storage port of it) is the tree's truth round
  (3d03172f, 3ccbe24c, 81864024 lineage).

The PR 419 limiting contract in `../PR419_NOTICE.md` applies unchanged: these passes are exact rewrites (no new
approximation, no change in which shots fail).
