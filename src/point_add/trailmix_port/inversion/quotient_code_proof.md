# Pending Quotient Codec: Finite-Width Contract

Default off: `MIDQ_QUOTIENT_CODE=1`. Base `b5fd329`. This does not change
360 PZ steps, 224 tail rounds, width schedules, CLZ/rotate windows, arithmetic
truncations, nonce, or the trusted harness. No checkpoint/outer-vent work imported.

## Support and No-Overflow Lemma

The inherited promised support consists of normalized nonzero field inputs whose
PZ execution respects the existing register/quotient widths, intermediate bounds,
CLZ/rotation windows and exact branch predicates. It is NOT the Cartesian product
of all bit patterns that fit the final handoff widths. No new input filter is used.

Lift that execution to nonnegative integers A, B, ca, cb, q. At all boundaries,

    A*cb + B*(ca + q*cb) = p,  B > 0, cb > 0.

Initially (A,B,ca,cb,q)=(p,x,0,1,0). A division replaces
(A,q) by (A-2^s*B,q+2^s); the selected quotient bit is zero and A>=2^s*B.
A multiply clears q's least set bit s and adds 2^s*cb to ca. Both preserve the
identity. Role swaps occur only with q=0 and A>0; after the initial division
their old ca is positive, so both positive-denominator properties survive.
Fixed terminal padding changes nothing. These are the existing exact-transition
obligations, including the cross-gated implementation's branch predicates.

Thus 0 <= ca' = ca+q*cb <= p < 2^256 < 2^257. All positive partial sums in the
existing 257-bit flush fit too. Although its adders are modulo 2^257, their
restriction to this support is the exact integer flush. Zero-extension from
248 bits discards nothing. Restoring ca' before inverse flush restores the same
nonnegative subtractions. The codec never acts on tail-normalized coefficients.

## Quotient Recovery

For q>0 set k=ctz(q), d=floor(ca/cb). Inductively d<2^k:

1. A division can write q only while ca<cb, hence d=0.
2. A multiplication removing bit k changes d to d+2^k < 2^(k+1).
   Any remaining quotient has ctz at least k+1.
3. A role swap has q=0; terminal padding preserves the condition.

Hence D=floor(ca'/cb)=q+d, and q=(D>>k)<<k. Since q is the actual 18-bit
register and is divisible by 2^k, q<=2^18-2^k, whence D<2^18.
No separate ratio-width restriction has been added. q=0 uses code 18 and returns
zero regardless of the ratio, including ca'=3, cb=1, and ratios wider than 18 bits.

## Exact Extraction Operator

The reversible divider stores its remainder IN ca' and its decisions in an
explicit new 18-bit register t. There is no copy of ca', cb, or the remainder.
For i=17 down to 0 it computes

    t[i] ^= [zero_extend_257(ca'[i..257]) >= cb],

then conditionally subtracts cb from ca'[i..257]. This comparison is precisely
[ca' >= cb*2^i] as an integer, including when the shifted divisor exceeds 257
bits, because floor(ca'/2^i)>=cb iff ca'>=cb*2^i. The zero extension borrows
t[0..i] instead of allocating a pad. In the descending forward sweep these
bits have not been written; in the ascending reverse sweep they have already
been cleared. They are therefore zero on EVERY divider input, independently of
the PZ promise. The current decision target t[i] is disjoint from the borrowed
bits, and the compare restores every borrowed bit before its next use.
Every executed subtraction is nonnegative and fits its finite slice.
Low bits of ca' below i are untouched. The full-width comparison prevents
wrapped divisors from being treated as small. cb and the borrowed zero bits are restored
by every compare, and cb is restored by every adder.

For 0<cb and D<2^18, binary restoring division yields t=D and ca'=remainder.
For larger D it yields min(D,2^18-1); this case only matters on the sentinel
branch, where no quotient bits are copied. cb=0 deterministically produces all
ones and subtracts zero; it too is safely ignored on the sentinel branch, though
cb=0 is outside the PZ promise. No reset is used to enforce an input predicate.

XOR t[i] into q[i] iff code<=i. Reverse all division steps, in opposite order:
conditionally add using t[i], then recompute and XOR away the original decision.
This restores ca', cb and clears all t on EVERY input. The output is therefore
a clean XOR oracle for the recovered q on the promised support; arbitrary initial
output q is allowed. Temporary ANDs are explicitly uncomputed unitary ladders.

Compression computes the five-bit code from q, calls the XOR oracle (making q
zero), and releases q. Restoration allocates 18 zero bits, calls the same oracle
using restored ca',cb, XOR-clears code from the recovered q, then inverse flush
runs. Both 257-bit cofactors and their inverse-bearing tail history are retained.

All new gates are X/CX/CCX, with reset only on proved zero wires. This basis
permutation has no relative phases. On the linear span of the inherited promised
basis states it is an isometry with the stated inverse, so the proof also covers
superpositions and entanglement with arbitrary untouched passengers. It does not
claim to repair inherited approximate arithmetic outside that support.

## Why Handoff Widths Alone Are Insufficient

Take ca=0, cb=2^247. Both q=1024 and q=3072 fit q18 and have k=10; both
coefficients fit 248 bits. Their 257-bit modular flushes are BOTH zero because
q*cb is respectively 2^257 and 3*2^257. The proposed five-bit encoding would then
collide. Both satisfy d<2^k. They are NOT exact PZ states: B>=1 would force
B*(ca+q*cb)>p. This witness rules out an unconditional claim on the width cube,
not the codec on the existing exact-transition support.

## Storage Accounting

Persistent tail replacement: 18 q bits become 5 code bits, saving 13.
During extraction BOTH the original/restored q18 and the temporary t18 are live,
alongside code5. The two 257-bit cofactors remain allocated throughout. The
comparison borrows lower zero quotient bits and uses one carry, with no extra
predicate or pad register. The masked copy uses one flag plus three ladder bits.
Controlled addition uses one carry. CTZ encoding uses one flag plus
at most 16 ladder bits, without t18.

Maximum new extraction live state above the original handoff: 5+18+1+3=27,
now set by the masked-copy flag and its equality ladder. The division itself
needs only 5+18+1=24 extra bits. CTZ without the temporary quotient needs 5+1+16=22.
There is no 257-bit remainder, quotient, or divisor copy hidden in this bound.
Measured whole-circuit and component counts are recorded in the local receipt.
