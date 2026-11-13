# Tools behind this row

- `qopt/`: our exact cancellation and merging pass and the independent replay (std-only Rust; copy the row's
  `decoder.rs` and `schedule.rs` into `qopt/src/` to build). `QOPT_MODE=23 qopt prune TRACE - 0 0 OUT` writes
  `OUT.runs` (shipped as `prune*.zst` after `zstd -19`) and `OUT.patch` (shipped as `merge*.zst`).
  `qopt verify TRACE INPUTS 144` replays 9,216 shots and checks values, ancilla cleanup and phase.
- `pp_main.rs`: offline wrapper that runs RealAdii's `peephole.rs` (from 4fa40ba2, unmodified) on a flat gate
  list, so the second round of our pass could be computed on exactly the list the build produces at that point.

Order of work: decode the package, `qopt prune` (round 1), `pp peep`, `qopt prune` (round 2), replay after each step.
