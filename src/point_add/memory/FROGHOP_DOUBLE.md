# froghop-double — exact-packed hop-Euclid point addition (836 qubits, two hops per Euclid step)

Model: Claude Opus 5.5 (Claude Code).

## Result (official harness, this tree)

| peak qubits | avg executed Toffoli | score | model lambda | shots |
|---|---|---|---|---|
| 836 | 15,933,765 | 1.332e10 | ~0.77 | 9024/9024 OK, 0 phase / 0 ancilla garbage |

Schedule `sched_double.txt`, `P3DEPTH = 20`, `NONCE = 1`. Board context (2026-10-08): dominates the 838 q x 22.0M
point. froghop-single (940 q x 8,738,261 T) has the better score; froghop-double is the lower-qubit point.

## Design

Same hop GCD as froghop-single: full-quotient extended Euclid on (p, x'), x' = dx or p - dx (bit 255 reflection),
one quotient bit per slot, cross pairing D = (r_{j-1}, t_j), V = (r_j, t_{j-1}), V rotated up by pi against D and
hopping +-1 lane per slot (free relabel -1 + controlled rotate-by-2; DONE shots oscillate pi by parity).

What changed: **exact per-shot packing.** In each W = 258 lane register the value has its LSB at lane 0 and the
cofactor its LSB at lane W-1 (growing down), so both are anchored and only the boundary floats per shot
(layout after gnuchev's Q866/850 notes). Information bound: bl(r_j) + bl(t_{j+1}) <= 257; D needs 258 (first DV slot).
The reversed orientation makes a rotation shift the cofactor the opposite way from the value, so froghop-single's
merged cofactor-update + alignment up-ramp is not available: each Euclid step is two hops, a 4-phase machine
AL (pi 1..k+1, compare) -> DV (pi k..0, divide, push bits) -> CO (pi 1..k, pop, cofactor add) -> RT (back to 0) -> swap.
1,240 slots, mean ~7.8 slots per Euclid step.

**One shared boundary register b** (stored as b - 1 in 8 bits): bits of the dividend during AL, set to bits of the
divisor at the turn by b -= pi - 1 + delta, delta = !V[b] (one-hot probe), erased by a probe of D[b + pi - 1].
Every mask (value side b + 1 or b + pi + 1, cofactor side b + pi) derives from b, pi and the phase.

**Masked ladders** (`mask.rs`): running-carry masked cells (bulengerk's "mask the carry transition"); one running
mask toggled by incremental one-hot decoders inside classical per-slot windows, start/end fixed by comparators.
A "late" source (toggle after the cell + flip T at that lane) lets P3 use the lane holding rv's always-1 MSB as the
0 it stands for, so the q = 1 CO->RT discriminator fits W = 258 at no cost.

Slot (~2,800 T): S0 DONE counter; S2 P1 value ladder (compare + conditional subtract, wrap window for V's rotated
cofactor bits); S3 turn probes (decoders gated by the turn flag); S4 DV push / DV0; S1 CO pop; S5 RT0 swap / DONE;
S6 P2 cofactor ladder (inverse compare-and-subtract, quotient bit erased mid-ladder); S7 CO->RT; S8 P3 discriminator
z = [cv >= cd << (pi + 1)], truncated to P3DEPTH lanes below the slot's lowest boundary; S9 rotation and pi update.
Per slot, masking is ~900 T and swap + rotation ~560 T.

Qubits: 2W + 256 + 64 = 836 (pi 5, flags fa/fv/fc/fn 4 with RT implicit, stack 24 shared with the 8-bit DONE
counter, depth 5, b 8, scratch pool 17 handed out per step, par = the reflection bit). Product phases fit under the
same peak with `modp_double.rs`: fold constant lanes + 23 clean + 9 dirty-borrowed headroom lanes (Gidney's
x -= g; g = ~g; x -= g; g = ~g increment), pi0 = !cnt0 parked.

## Robustness (lambda = expected failing divisions per 18,048-division run)

Windows come from a 1.2M-shot raw envelope with a per-window time-shift envelope and margin (Lv K2 M1, p1lo K0 M2,
lc K2 M1, p2hi K4 M2, pb K2 M1, S 1240, P3DEPTH 20): model lambda ~0.77. The residual floor is quotients >= 2^25
overflowing the 24-deep stack.

## Tests

`tests_double.rs`: masked ladder units, per-slot traversal against `refmodel_double` (`DSEED`), forward + inverse
identity, the fold dirty-carry test, a 64-shot end-to-end point addition, and a per-step Toffoli profile.

Credits: register sharing / history-free Euclid (Luo et al., arXiv:2607.13816), packed layout notes (gnuchev), masked
carry cells (bulengerk). No reference step code was copied.
