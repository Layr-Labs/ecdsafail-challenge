# Exact decoder/cofactor composition on official r07

This isolated lane starts from official source
`290010bf6817543805e915a4efb86f2481a2777b`, whose coordinator-retrieved
official result is Q792/T1,021,417,698. That submission was rejected because
its score did not beat the current best, not because its circuit was invalid.
No submission or push is made by this lane. Attribution: Astra, Codex;
effort is not exposed or confirmed.

The exact ESOP method was independently fully qualified on r06 and frozen
at `efa7c5c3dac76a7e987aa63972b826bc0a256f3a`. Its three production
truth tables are `080f0c0f`, `30003000`, and `80f0c0f0`, each
saving one actual Toffoli with at most two additional primitive records.
That r06 result remains separate and unsubmitted. This work composes those
three plans with three disjoint decoder predicates on the newer r07.

## Exact candidate family

The candidate generator is inspired by the exact decoder/common-cofactor
idea in Yang, Al-Bayaty and Perkowski,
[arXiv:2601.02515](https://arxiv.org/html/2601.02515v1).
It does not use approximate truth tables or the paper's different TQC metric.
All 2+3, 3+2 and 3+3 input partitions and complete row-space bases of rank
at most four are enumerated. Every product decomposition reconstructs
every full truth-table cell exactly. In the measured residual family,
64,488 checked bases over 40 predicates produced three leads.

Truth vectors use integer bit x for input assignment x, and SHA3-256 is
taken over the 32 bytes whose values are the individual truth bits.
Normalized native operation kinds are X=6, CX=8, CCX=13; absent controls
are the inherited NO_QUBIT sentinel.

The retained products, with each partition listed in increasing input order:

- `47000300`: A=[1,3], B=[0,2,4], products (0xc,0x33) XOR (0x8,0x63).
- `ec80c800`: A=[1,3], B=[0,2,4], products (0x6,0x80) XOR (0x8,0xfe).
- `ecc88000`: A=[0,2,3], B=[1,4], products (0x80,0x6) XOR (0xfe,0x8).

Small factors are exact mixed-polarity ESOPs, exhaustively found using
Dijkstra over all truth vectors for at most three inputs. For each product,
actual native emission compares both orientations and these constructions:

1. Restored dirty ABAB: d ^= g(A); out ^= d*h(B); repeat. The arbitrary
   incoming value of d cancels and d is restored.
2. Balanced decoder carrier: when g=x_i XOR u(other inputs), temporarily
   xor u into x_i, consume x_i*h(B), and append the literal reverse of u.
3. Flattened small-ESOP products, measured as actual native operations.
   In particular, ab*(x|y|z) equals ab XOR ab*!x*!y*!z. Combining this
   with the balanced-carrier term reduces the two larger leads further.

Initial native emission was respectively T7/N12, T24/N40 and T24/N40.
The flattened-product refinement is T7/N12, T21/N29 and T21/N29, compared
with r07's T10/N16, T29/N35 and T29/N35 for these same arbitrary-target
maps. All 12,288 assignments of five inputs, one target and six dirty
lenders pass output equality, zero phase and literal reverse identity.
Every non-target wire is checked, not merely the output bit.

## Production and validation boundaries

Production tries only the three qualified decoder truths on five inputs,
without a prefix, with at least three restored dirty lenders. It rejects
any duplicate ID among input, target and lenders, and does not run in passive
or rank-capture intermediate forms. It accepts only a strict actual CCX
reduction, with at most five extra primitive records per direct call.
The winning refinement in fact reduces primitive operations for all three
decoder predicates. No qubit allocation occurs.

The layer runs after the existing affine/nonlinear/beam optimizers and
the three exact ESOP replacements. All other source-default logic,
including r07 lifetime/cache choices, is preserved. Canonical trusted
input derivation, simulation, phase checking and gate accounting are not
modified. Only src/point_add is editable; all 17 protected paths are
required to remain byte-identical.

Diagnostic switches:

- `FOLD20_EXACT_ESOP_DISABLED=1`: omit only the three new ESOP candidates.
- `FOLD20_EXACT_DECODER_DISABLED=1`: omit only the three decoder candidates.
- `FOLD20_EXACT_DECODER_CALL_CENSUS=1`: compare completed calls against
  both layers disabled, binding each to the current block and j template.
- `LOWQ_Q793_NATIVE_MODE=fold20-exact-whole-count`: source-bound count
  diagnostic only; it disables frozen-count assertions through
  FOLD20_EXACT_DISCOVERY and cannot be used as canonical qualification.
- `fold20-exact-census`: all808 physical primitive templates.
- `fold20-exact-esop` and `fold20-exact-decoder`: local exhaustive maps.

Actual paired whole counts from refinement commit
`58820c71cf366064b4f02eac14dcff094506ac79`, binary SHA256
`4baa7408b639df52aaabcc3592da72e3221156a4bd8020c48998549569c679e5`:

| Layers | Q | Toffolis | Expanded operations |
| --- | ---: | ---: | ---: |
| Both disabled | 792 | 1,021,417,698 | 1,695,670,810 |
| ESOP only | 792 | 1,020,247,938 | 1,698,215,098 |
| Decoder only | 792 | 1,019,847,458 | 1,694,555,450 |
| Combined | 792 | 1,018,677,698 | 1,697,099,738 |

Combined delta is -2,740,000 Toffolis and +1,428,928 operations, and
the layers stack exactly in these actual whole counts. Ordinary payload
is 95,037,585,328 bytes, with 29,962,414,672 bytes remaining below the
working cap. These are count-only results, not correctness qualification.

Whole counts and all808 template totals must reconcile after downstream
optimization; raw accepted direct calls are not whole-circuit savings.
The ordinary 56-byte expanded payload has a hard working cap of
125,000,000,000 bytes. The measured whole constants are frozen only after
paired actual counts. Physical-step capsules, full lifecycle, independent
whole64, and canonical9024 remain separate gates; local native or count
success alone is never an official result.
