# Exact post-pass probes on 7126dde

Baseline reproduced using the unmodified benchmark: score 889676324,
725674.057 mean executed Toffolis, width 1226, 12468502 operations.
All 9024 shots passed, with no phase or ancilla garbage.

The following standalone probes interpreted the final emitted operation stream.
They do not establish absence of opportunities in an earlier intermediate stream.

* Extending hold_pass::ctrl_peephole to conditioned CCX, preserving each
  replacement's c_condition and stack position: no extra reductions.
  A complete build/run of this modification emitted byte-identical ops.bin
  and reproduced the baseline score. The change was restored.
* Using the flat-product support model for this control query: no reductions.
* Also conjoining the classical context when testing product implication:
  no reductions.
* Exact pair cancellation across commuting target flips, with unchanged
  control versions and no intervening target reads: no pairs found, even
  when matching classical condition snapshots were permitted.
* Re-running the standard truth/product simplifier on the final stream:
  unchanged, 765107 native CCX operations before and after.
* Extending truth tables from six atoms/u64 to seven atoms/u128: unchanged.
* Extending the sparse quadratic abstraction to degree three with 32 terms:
  unchanged.
* Matching quantum control functions against live classical-bit functions in
  the flat affine/product model: no substitutions found.
* A second hold pass found 5157 duplicate loans but no extra product holds.
  A following flat late-copy pass also found no additional holds.
* Relocation of wire 1225 into the first 1225 slots failed to find sufficient
  proven-zero space, both directly and after the extra duplicate loans.
  The helper panics on a later access to a nomad after an earlier allocation
  failure; this is a failed probe, not evidence of circuit invalidity.

Research discussions are disabled for this challenge. Scratch probe code and
raw streams are outside the submission tree. No improvement has yet been
claimed or submitted from these experiments.
