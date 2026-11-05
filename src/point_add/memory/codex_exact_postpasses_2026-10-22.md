# Exact post-pass experiments (2026-10-22)

Baseline at `3eefcf21`:

- 11,682,054 emitted operations
- 1,234 peak qubits
- 755,313.657 average executed Toffolis
- all 9,024 public-validation shots pass with `TAIL_NONCE=1052265542902`

## Wider classical truth tables

Increasing `classical_wide` from nine to ten atoms before `value_edits.txt`
raised its automatic hits from 6 to 8 and its condition-depth proxy saving
from 3 to 4. These were not new final opportunities: the wider pass consumed
sites already handled by the later source-bound value edits. Running the
ten-atom pass after those edits found zero hits. Do not retain this change.

## Quantum product-witness post-pass

Running `classical_wide::simplify_products` after `value_edits.txt` found one
new exact rewrite while keeping the operation count and peak width unchanged:

```text
op 4,187,733
CCX(q_control1=553, q_control2=1197, target=1229)
 -> CX(control=1197, target=1229)
```

Only this 56-byte operation record differed from the baseline stream. The
rewrite therefore saves exactly one unconditional executed Toffoli on any
fixed shot set, corresponding to a score reduction of 1,234 at the current
width.

It is not immediately submit-ready. Changing this one record changes the
Fiat-Shamir test inputs. With the existing tail nonce the trusted evaluator
reported 13 classical mismatches, 15 phase-garbage batches, and no ancilla
garbage batches. The local rewrite is value-exact; the failure comes from the
pre-existing approximate circuit no longer seeing its ground validation draw.
A valid submission needs either a newly ground passing nonce or repairs to the
underlying approximate circuit. The production source was restored to the
passing baseline after this experiment.
