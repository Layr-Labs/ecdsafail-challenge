# froghop-single — low-qubit packed-Euclid point addition (one hop per Euclid step)

Model: Claude Opus 5.5 (Claude Code).

## Result (official harness, this tree)

| peak qubits | avg executed Toffoli | score | shots |
|---|---|---|---|
| 940 | 8,738,261 | ~8.21e9 | 9024/9024 OK, 0 phase / 0 ancilla garbage |

Pareto context (official metrics, 2026-10-08): it dominates the 973-1011 qubit points (best: 974 q x 11.82M,
1011 q x 9.33M); the nearest narrower point is 838 q x 22.0M.

## Design

Extended Euclid on (p, min(dx, p - dx)) with Bezout cofactors packed next to the remainders in two W-lane
registers D, V (cross pairing (r_{i-1}, t_i) | (r_i, t_{i-1}), same bit orientation). The r/t boundary M(sigma)
is a CLASSICAL per-slot schedule (`sched.txt`), moved by free wire relabels, so every ladder runs on fixed lanes with
no per-lane masks. The cofactor update of step i-1 (bottom-up, which lets every quotient bit be erased by one
compare, the Luo et al. / gnuchev mechanism) shares the up-ramp with the alignment search of step i; the
division runs on the down-ramp and pushes quotient bits on a 24-deep LIFO stack. 900 fixed slots per traversal.

Per slot (every op provisioned on every shot), ~1,840 Toffoli:
- P1 remainder ladder: compare + conditional subtract, 3 T/lane, mid-ladder hooks write the decisions;
- P2 cofactor ladder: inverse of compare-and-conditional-subtract = conditional add whose quotient bit is erased
  mid-ladder, 3 T/lane;
- P3 turn discriminator: compare of the top 96 cofactor lanes at offset pi + 1, 2 T/lane;
- V rotation: DONE shots oscillate pi so the move is two-way: free relabel by -1 + controlled rotate-by-2 (W - 2);
- step-end role swap of D and V (W Fredkins);
- stack, counters, phase one-hot, erasures (~90).

Point addition: dx, dy; division 1 (forward traversal with dy as passenger -> inverse; lambda = inv * dy;
dy measured away (Hmr); inverse traversal with lambda as passenger); dy recomputed as lambda * dx to fix its phase and
uncomputed; dx' = lambda^2 - dx - 3 ox (multiply-accumulate); ndy = -lambda * dx'; lambda measured away; division 2
recomputes lambda = -ndy / dx' to fix its phase; x3 = dx' + ox, y3 = ndy - oy. The measurement-based erasure follows
the register-sharing EEA constructions (Luo et al., arXiv:2607.13816; gnuchev; bulengerk); the inversion core is
our own.

Products: double-and-add with folding by p = 2^256 - c (c = 2^32 + 977): mod_double 130 T, controlled modular
add 963 T, product 280k, MAC 313k. Carry headroom truncated to 32 lanes (2^-32 per operation).

Peak = 2W + 256 + 54 + 2 with W = 314 (schedule `sched.txt` fitted to 200k simulated shots).

## Failure budget (lambda)

Fresh builds fail a shot with expected count ~0.45 per 9024-shot run: register-width tail from rare large
quotients (~0.3), stack depth 24 (~0.1), slot count, first-step window, truncations (~0.05). A local diagnostic
replays the harness's Fiat-Shamir shot generation from `ops.bin` and checks every division against all limits.

## Verification

`cargo test --release --bin build_circuit` (10 tests): ladders, rotations, counters, AND/MCX, modular routines,
the gate-level traversal against the integer reference model at every slot (`refmodel.rs`), forward + inverse
identity on 384 inputs, and the end-to-end point addition on 64 random
point pairs.

## Why 940 and not ~840

A fixed boundary costs the spread of progress across shots: content-only width is ~300 fixed vs 259 per shot,
plus ~8 lanes of shift-overshoot tail from large quotients. The follow-up, froghop-double, packs per shot with
bit-reversed remainders (floating gap) and masks only in the spread band.
