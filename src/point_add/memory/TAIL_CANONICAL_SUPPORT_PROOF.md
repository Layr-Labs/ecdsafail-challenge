# Canonical field cells on the inherited exact-transition support

September 10, 2026. This is a qualified support theorem for the pinned Q1011
route. It is not an all-bit-pattern equivalence claim and does not certify that
a particular emitted circuit input satisfies the hypotheses. All earlier
prototypes and analyses remain frozen.

## Conclusion

On the support defined below, the original normalization halves and every
forward/backward signed-add/halve coefficient cell perform canonical field
arithmetic with zero residual measurement phase. Consequently an independently
proved canonical fused cell can replace them on that support without reproducing
their noncanonical error-phase oracle.

The proof does not require guessing which of the two handoff rows is a convergent
or bounding two or three preceding coefficients. An earlier adjacent Euclidean
pair, chosen at a remainder threshold, supplies an elementary lattice certificate.
This handles a semiconvergent handoff and a partially consumed quotient exactly.

Outside these hypotheses, the earlier counterexamples still apply. This theorem
does not authorize claiming the canonical replacement preserves every baseline
error channel or every accidentally successful input outside exact transitions.

## Explicit hypotheses

Let `p=2^256-2^32-977`, `M=2^256`, `F=M-p`, and let x be the source-normalized
nonzero input `min(x_original,p-x_original)`. Let the PZ cut be 360 microsteps.

1. The PZ state through the cut agrees with the ideal integer transition in the
   pinned model, including the quotient word, both coefficient words, roles,
   parity and swaps. The same quantum width/window/metadata implementation must
   establish this membership; the ideal model alone does not establish it.
2. Every performed quotient-bit shift is in 0 through 31. In particular, the
   first subtraction of every begun Euclidean division uses an exact five-bit
   shift. This bounds the full quotient of a begun division, not merely the
   currently retained low quotient bits.
3. At the cut both remainders a,b are positive, and `b_max=max(a,b)<2^85`.
   Terminal-zero handoffs are excluded. The pending quotient is flushed exactly.
4. Normalization uses the true powers of two in a and b, with faithful sign and
   metadata routing. The tail follows the intended odd signed recurrence with
   its source sign choice. For this theorem, exact tail value transitions and
   their storage/codec contracts are part of the support. No claim about lossy
   tail-width error states is required.

The source’s correct circuit support can be narrower for other reasons. The
theorem preserves every input satisfying these hypotheses, rather than selecting
a favorable new nonce or tightening the numeric width schedule.

## Lemma 1: an elementary short-relation exclusion

Take consecutive positive Euclidean remainders R>r for p and x. Their coefficient
magnitudes U,V are nonnegative with U<=V and

    R*V + r*U = p.

Their signs alternate. If necessary, replace x by -x for this lemma and negate
the coefficient coordinate c. This preserves the absolute-value claim and makes
the two rows `(R,-U)` and `(r,V)` a basis of

    Lambda = {(v,c) in Z^2 : v = c*x mod p}.

Their determinant is p, the same as the index of Lambda. Equivalently, Cramer's
rule gives integer coordinates for every modular relation using the displayed
congruences. No independence or probabilistic statement is needed.

Claim: if `0<|c|<V`, every representative v of that modular relation satisfies
`|v|>=R`.

Proof: change both signs so `0<c<V` and write

    (v,c) = m*(R,-U) + n*(r,V).

If m=0, then c=nV, impossible. If m>=1, positivity of
`c=-mU+nV` forces n>=1, so `v=mR+nr>=R`. If m<=-1, write m=-k with k>=1.
Then `c=kU+nV<V` forces n<=0, so `v=-kR+nr<=-R`. These exhaust the cases.

This is the required best-approximation property proved directly for the
specific lattice. It does not rely on a heuristic convergent-size estimate.

## Lemma 2: choose the threshold pair before the handoff

Set `B=2*b_max`. In the ordinary Euclidean sequence choose the first positive remainder
r<=B, with predecessor R>B. Such a pair exists because the sequence reaches 1
and B>=2, while p>B.

Its division R/r has already begun before the PZ cut. To see the indexing, during
a division phase the PZ gcd pair consists of a fixed convergent divisor b and a
partially reduced numerator `R_current-q_partial*b`. During quotient consumption
the gcd pair is stationary. A completed swap advances to the next convergent
divisor. Since the handoff has b<=b_max<B, the threshold divisor is no later than the
current divisor. If it is the current one, a<=b_max<R proves that at least one
subtraction has occurred. Otherwise that division completed earlier.

Thus hypothesis 2 applies to the first subtraction of R/r. Its leading quotient
bit has index at most 31, so the full quotient is at most `q_max=2^32-1`, even if some
of its bits remain pending or have already been consumed. Therefore

    R < (q_max+1)*r,
    p = R*V+r*U <= (R+r)*V < (q_max+2)*B*V,
    V > p/((2^32+1)*2*b_max).

For b_max<2^85 this exceeds `2^137`, whereas `F=2^32+977<2^33`.

Combining the lemmas: no nonzero signed coefficient c with `|c|<=F` can satisfy

    c*x = v mod p,  0<|v|<=2*b_max.

More precisely, any such relation's canonical coefficient has distance at least
V from zero modulo p. The large margin is a theorem under the support hypotheses,
not an observed minimum extrapolated from samples.

## Handoff and pending-quotient coefficients

In the source-local notation, write

    A = ca + q*cb,  Bcoef = cb.

The exact PZ transition preserves

    a*Bcoef + b*A = p,
    a = (-1)^parity*A*x mod p,
    b = (-1)^(parity+1)*Bcoef*x mod p.

During quotient consumption, adding a bit of q*cb to ca leaves A unchanged;
during division, reducing a by a shifted b increments A correspondingly. Thus
this relation is valid at a partial division and during partial consumption.
Flushing q restores A without dropping its record.

Positivity of a,b and these congruences imply `0<A,Bcoef<p`. The sign corrections
therefore produce canonical, nonzero coefficients. Their corresponding integer
values a,b have magnitude <=b_max, so Lemma 1 excludes both intervals within F of
zero modulo p. The flushed 257-bit addition does not overflow its word.

## Normalization, with its actual parity-erasure rule

At each active normalization half, the intended coefficient c represents a
positive integer remainder v divisible by two. Define the intended next
coefficient canonically; it represents v/2, still positive and <=b_max. The lattice
lemma therefore gives the same margin for every intermediate coefficient.

The original 257-bit normalization helper computes

    d = (c + (c mod 2)*p)/2.

There is no 257-bit overflow, and the shifted-out bit is zero. If c is even,
then d<p/2<M/2, so d's bit255 is zero. If c is odd, the margin c>F gives
`c+p>M`, hence d>M/2 and bit255 is one. Consequently the original HMR of old
parity, corrected by the active control AND d[255], has exactly zero phase defect.
This proves the original half equals the intended canonical half before using
that equality at the next step.

The inverse normalization uses that same high bit to select subtraction of p
after doubling. It returns the preceding canonical c, and c's low bit clears
the coherent parity wire. Inactive normalization branches are identity.

## Noncircular induction for the tail

Start with the intended normalized odd integers v_a,v_b and their canonical
coefficients c_a,c_b. On each step, the source sign sigma satisfies

    v_target + (-1)^sigma*v_source = 2 mod 4.

Thus the next target value is odd and nonzero, and

    |v_target_new| <= max(|v_a|,|v_b|) <= b_max.

These statements are properties of the intended integer recurrence, independently
of any implementation of its coefficient cell. Define its intended coefficients
by exact canonical field arithmetic. Every coefficient c_i then satisfies
`c_i*x=v_i mod p`, and every pre-halve residue `u=2*c_new mod p` represents
`2*v_new`, whose nonzero magnitude is <=2*b_max.

The lattice lemma consequently proves, for all these intended values,

    F < c_i < p-F,    F < u < p-F.

Now assume the original coefficient inputs equal the intended ones at one step.
The following direct source calculation proves that step's equality and clean
phase. This establishes the next induction hypothesis without presuming the
conclusion about original arithmetic.

## Original signed-add fold and phase agree on that margin

For canonical target c and source d, the source complements c when subtracting,
adds d with an overflow bit h initially zero, folds `+h*F` modulo M, and clears h
by an HMR corrected with the predicate `[folded_word<d]`.

For addition, let t=c+d and u=t mod p. If t<p, h=0 and the folded word is u.
If t>=p, the margin u>F excludes the otherwise problematic interval
`p<=t<=p+F`; hence t>M and h=1. The folded word is then t-p=u<p, without a
second wrap. For h=0 it is at least d, and for h=1 it is less than d. Therefore
the old comparison equals h in both cases, and its phase defect is zero.

For subtraction, h=[d>c]. If h=0, the folded complemented-frame word is
`M-1-c+d`, whose comparison with d is false. If h=1, it is `d-c+F-1`, with no
wrap for canonical inputs. Since c>F, that word is less than d. Again the old
comparison equals h. Complementing back gives exactly `u=c-d mod p`.

The following rotated half receives canonical u with u>F. An odd u therefore
does not underflow its low-word K subtraction, and the source result is exactly
`(u+p)/2<p`. An even u maps to u/2. Its carry cleanups are exact. This proves
both the intended output and zero residual phase of every forward cell.

## Backward cells

For any canonical c representing v, the residue `2c mod p` represents 2v with
nonzero magnitude <=2*b_max, and so it also has the required margin. The source
rotated double agrees with canonical doubling: the only possible missing
subtraction below M/2 would have `p<=2c<M`, giving a residue below F, which the
lemma excludes. Above M/2 its existing fold gives 2c-p exactly.

The backward cell next performs signed addition with the opposite sign. Its
intended result is the previous coefficient, also safely inside the margin.
The signed-add proof just given therefore applies to that step as well, with
zero phase defect. It recovers the preceding canonical state. Induction backward
proves every reverse cell, followed by the inverse normalization.

## Consequence for a canonical fused circuit

A canonical cell may use these ordinary formulas for canonical c,d:

- Addition t=c+d: if t is even, output t/2; if t is odd, output (t+p)/2 for
  t<p and (t-p)/2 otherwise.
- Subtraction t=c-d: if t is odd, output (t+p)/2; if t is even, output t/2
  when t>=0 and t/2+p otherwise.

An exact reversible implementation of these formulas with clean phase matches
the old cell on the proved support. It does not need to reproduce the old
noncanonical error oracle there, because that oracle's defect is identically
zero on the support. It still needs its own implementation/phase/ancilla proof
and actual resource measurements. This document does not claim that code or a
Q/T improvement has been implemented.

The equality is pointwise with exact phase, so it extends by linearity to any
superposition supported on these exact-transition states, with arbitrary phases
already carried by other registers.

## Independent certificates obtained

`tail_support_certificate.py` uses SHAKE256 domain
`tail-canonical-support-independent-20260910-v1:` with indices 0..1023. Every
draw is reported; no nonce search or favorable subset selection occurs.

Results:

- All 1,024 draws satisfied the classical certificate hypotheses.
- 458,752 literal forward/backward fast-cell checks passed with zero phase defect.
- 1,359 normalization halves and their inverses passed the source parity checks.
- The largest handoff remainder had 80 bits.
- The smallest certified coefficient bound and observed modular distance had
  174 bits, comfortably above F.
- All 1,024 intended tails reached signed unit endpoints.
- An additional 18,494 exhaustive small-prime cases checked Lemma 1 directly.

The per-input JSON records R,r,U,V, their Euclidean index, quotient, handoff,
pending q, maximum performed shift, and the observed margin. A checker can
verify `R*V+r*U=p`, the row congruences, `R>2*b_max>=r`, the quotient bound and V>F.

These certificates use ideal integer PZ transitions and source arithmetic
formulas. They do not establish emitted-circuit membership in the support.
Before promoting a canonical fused implementation, run actual operation-level
PZ/normalization/tail checks on frozen and independent inputs, retain existing
width/metadata requirements, then run the trusted complete quantum benchmark.
Any outside-support changes must be reported explicitly rather than described
as all-input channel equivalence.
