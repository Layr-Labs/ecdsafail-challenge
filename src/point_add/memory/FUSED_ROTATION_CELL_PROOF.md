# Four-offset cell with a rotation-only overflow phase correction

Status: new baseline-derived source candidate, opt-in with
`MIDQ_FUSED_ROTATION_CELL=1`. Only forward cells use the replacement. Existing
inverse cells are unchanged. No whole-circuit Q/T result or native test result
is claimed by this document before the remote validation runs.

The numerical map is exactly the original finite-word map. The overflow phase
simplification is qualified to the exact-transition support proved in the
separate `TAIL_CANONICAL_SUPPORT_PROOF.md`; outside-support phase equivalence is
explicitly not claimed.

## Full-width rotation comparison theorem

Let `M=2^256`, `L=M/2`, `p=M-F`, `F=2^32+977`, and `K=(F-1)/2`. Let y be the
final coefficient word, eta=y[255] and x=y mod L. The source rotated double is

    D(y) = 2*((x+K*eta) mod L)+eta.

Let the pure one-bit left rotation be `rot(y)=2*x+eta`. If y is canonical, y<p,
then eta=1 implies `x<L-F`, so `x+K<L`. Therefore there is no hidden wrap:

    D(y) = rot(y) + (F-1)*eta.

For subtract flag s, complementing the whole word changes the difference's sign
but not its magnitude. Define

    A_D   = D(y)   XOR (s*(M-1)),
    A_rot = rot(y) XOR (s*(M-1)).

Then `A_D-A_rot=(1-2*s)*(F-1)*eta` as an ordinary integer difference.

Let a,b denote the original target/source coefficients and kappa the source
word-add overflow. On the certified support, the original signed-add result is
canonical and its measured comparator is correct. Direct substitution into its
actual complemented frame gives:

| s | kappa | A_D-b |
|---:|---:|---|
| 0 | 0 | a |
| 0 | 1 | a-p |
| 1 | 0 | M-1-a |
| 1 | 1 | F-1-a |

The support theorem proves `min(a,p-a)>=V>2^137`, not merely a>F. Hence every
gap has magnitude at least V-(F-1), and changing it by at most F-1 cannot change
its sign. In particular, the subtraction/borrow case requires a>2F-2; the proved
bound supplies this margin. Thus

    [A_D<b] = [A_rot<b]

on the entire certified support. Equality/tie cases cannot arise at this margin.
This proof uses the full 256-bit comparison. No high-window truncation is enabled
in the candidate.

The original HMR of kappa is still present, followed by this comparison phase.
The implementation does not simply discard kappa or omit its phase obligation.
On the support its phase factor is exactly

    (-1)^(m*kappa) * (-1)^(m*[A_rot<b]) = 1.

## Numerical implementation

The existing raw signed-frame word addition is factored into
`cell_folds::add_raw_with_overflow` without changing its operations. Let its
low word be w=2*u+c and its held overflow be kappa (including any old high input
bit if the interface has 257 bits). The desired final word is

    j = c XOR kappa XOR s,
    U = u XOR (s*(L-1)),
    delta = -(c XOR s)*K + (1-2*s)*kappa*c*F,
    y = j*L + (U+delta) mod L.

This is an identity on arbitrary finite words and arbitrary incoming overflow,
derived in the earlier four-offset analysis. It does not assume canonical input.

The code rotates the raw word right by one bit, placing c in its high wire,
complements the lower word when s is set, adds delta, and finally changes c to j.
The overflow stays live throughout. The selected delta is encoded with

    vsel = kappa AND c,
    nsel = c XOR s XOR vsel,
    joint = nsel AND vsel.

The four possibilities are:

| nsel | vsel | delta |
|---:|---:|---:|
| 0 | 0 | 0 |
| 1 | 0 | -K |
| 0 | 1 | K+1 |
| 1 | 1 | -F |

Every bit of delta is an affine function of nsel, vsel and joint, with masks
`-K`, `K+1`, and `(-K) XOR (K+1) XOR (-F)` in two's-complement form. For the real
constant, the latter two masks are `0x800001e9` and `0x1000003de`.

`Selected::with_bit` exposes one such affine function by temporary CNOT basis
changes among the three selector wires. It restores the changes after every
use. Majority generation, sum writes and phase correction use the exact exposed
bit; no independence of the three selectors is assumed.

## Carry cleanup and workspace proof

The selected-addend arithmetic uses the existing single-carry recursive cost
table and its exact split recurrence. A leaf computes fresh majority carries,
updates the target sum, and erases each carry by HMR and the polynomial

    MAJ(~sum, addend, incoming)

expressed with CZ gates. This equals the original forward carry for every input
assignment. Carry/phase replay reads the unchanged post-sum word and uses this
same recurrence. The affine selector preparation is restored around every
ordinary and phase-majority call.

At a split, one boundary wire stays live through both children, which receive
A-1 workspace. The boundary is measured and freed before its conditional replay,
so replay receives A workspace. This is the same proven measured-carry schedule
as the source's recursive constant updater. The optional outgoing carry is XORed,
not overwritten.

After the selected sum, joint is cleared with `clear_and(nsel,vsel)`, nsel is
uncomputed by CNOTs, and vsel is cleared with `clear_and(kappa,c)`. All their
original controls are still unchanged at these erasures. Only then are the high
data bit and the old overflow changed. Every new measurement therefore has its
full phase correction, including inside nested classical conditions.

Admission reserves three selector wires plus the temporary overflow if the
target has 256 bits. It rejects before arithmetic if the recursive carry plan
does not fit. For a fitting plan, its workspace plus these reserved wires is
bounded by `MIDQ_CELL_QCAP`. The old word-add helper and comparison retain their
existing cap-aware backends. The candidate has no dirty-reset shortcut.

Finally, the phase comparator uses wire refs in order

    [target[255], target[0], ..., target[254]],

which is exactly the pure rotation. All target bits are temporarily complemented
by s around the existing measured comparison helper, then restored. The original
overflow is measured and zeroed. A 257-bit interface keeps that high wire zero;
a temporary 256-bit-interface overflow is freed.

The numerical permutation with held overflow matches the old permutation on all
bit strings. Moving its overflow HMR past the data-only half permutation does
not change the old measurement instrument. The only qualified change is the
comparison phase predicate, whose equality was proved above on the support.

## Tests prepared and evidence obtained

Locally obtained:

- Rust sources parsed/formatted with rustfmt; no local native compilation or
  quantum simulation.
- Generated 512 native fixture states from 64 independently seeded trajectories
  certified by the previous support proof. Every selected input carries its
  Euclidean certificate. All 14,336 forward trajectory comparisons also verified
  the rotation-only predicate algebraically.
- The fixture is deterministic and its SHA256 and generator provenance are
  recorded in `fused_rotation_fixture_summary.json`.

Native tests prepared for the existing simulator and pre-reset auditor:

- Every small selected-addend target, sign/parity/overflow/spectator assignment,
  fitting workspace, several constants, forced/random measurement streams,
  all small measurement transcripts, and active/inactive nested conditions.
- Exact selected-adder count and cap checks.
- The 512 certified full-width states with 256/257-bit interfaces, caps
  1000/1011, multiple scratch budgets, and round trips through the old inverse.
- Full cells inside active and inactive nested classical conditions.
- Outside-support edge words, arbitrary initial overflow, and the old/new
  overflow outcome coupled explicitly. These tests assert identical finite-word
  values and each implementation's own phase formula. They deliberately require
  some differing phase coefficients, preventing a false all-input equivalence
  claim.
- Failed admission emits no arithmetic.

Remote command:

    MIDQ_CELL_FOLDS_SELFTEST=1 MIDQ_FUSED_ROTATION_CELL_SELFTEST=1 \
      ./target/release/build_circuit

Then generate with `MIDQ_FUSED_ROTATION_CELL=1` and the desired existing caps.
Run actual circuit membership/regression checks on frozen and independent
inputs, and the trusted complete benchmark. This source candidate changes the
outside-support phase channel and must remain described that way. A component
test or arithmetic certificate alone does not establish final Q/T or complete
circuit correctness.
