# Counter / Tape Codec Contract

Opt-in `MIDQ_COUNTER_TAPE=1`, eight counter bits, unchanged 360/224 schedules.
The proof is relative to the baseline's exact-transition support, not all
bit patterns surviving its approximate width resets.

## PZ Counter and Terminal Predicate

Start with counter=0, A=p, B=x, ca=0, cb=1, q=0, 0<x<p, p prime.
The exact PZ integer transitions preserve gcd(A,B)=1, B>0, cb>0 and

    A*cb + B*(ca+q*cb) = p.

A division replaces (A,q) by (A-2^s*B,q+2^s); a multiply replaces
(ca,q) by (ca+2^s*cb,q-2^s). Both preserve that identity. The division
preserves gcd, the multiply leaves both remainders alone, and a q=0 role
swap preserves both identities. A swap has A>0, so its new B is positive;
the old ca has become positive before any swap can occur. The modular rows
`A=(-1)^parity*(ca+q*cb)*x` and `B=(-1)^(parity+1)*cb*x` are preserved
by these same updates and the parity flip on swap.

The done predicate is A=0 AND q=0. It implies B=1 by coprimality and ca=p
by the cross invariant. The adjacent-row sign invariant gives
`(-1)^(parity+1)*cb = x^-1 (mod p)` with 0<cb<p. A=0 with q>0 is NOT
terminal. A nonzero counter alone is not an unconditional terminal test.
For the upper bound, the last quotient drain has ca_old+2^s*cb=p with
ca_old>=0, hence cb<=p; cb=p is excluded by the nonzero modular inverse.

Before the first terminal event, done=0 at every completed step, so the
counter is exactly zero by induction. Once done is true, the nonzero counter
disables the arithmetic and swap; the exact padding transition changes only
the counter. Thus counter!=0 implies terminal as long as the inherited
inactive-path and no-wrap promises hold. These promises must not be inferred
from empirical counter frequencies.

The 360-step prefix is NOT shorter than the 256 counter period. After 256
done updates an eight-bit counter wraps to zero and the next PZ body becomes
active on q=0. Its active multiply requires a pending quotient, so the
stationarity proof does not extend across that next body. We do not remove
counter bits or claim to fix such an inherited out-of-support execution.
At the codec boundary itself, terminal with counter=0 is nevertheless valid,
including a just-wrapped counter: the decoder preserves all 256 encodings.

In the fixed production schedule, EVERY coefficient width in steps 0..359
is narrower than 256 bits (checked against the configured schedule in the
selftest). A true ca=p terminal therefore cannot occur in any of those
exact-width steps. Inductively done never increments the counter: it is zero
throughout the prefix, with no possibility of wrap on that support. This
discharges the no-wrap obligation for the actual route without a probability
estimate or an extra input restriction. The terminal mapping is also verified
as an explicit wider boundary extension, not advertised as repairing earlier
truncated states. Arbitrary externally supplied inactive or post-wrap states
do not inherit the PZ support promises just because they fit eight count bits.

## Terminal Mapping and Logical Tape

After the usual quotient flush, compute t=[A=0 AND q=0]. Controlled by t,
perform ca-=cb modulo 2^257 and A[0]^=1. On the terminal branch this is the
nonnegative integer map (A,B,ca,cb,q)=(0,1,p,v,0)->(1,1,p-v,v,0).
Its cross invariant is 1*v+1*(p-v)=p. The unchanged sign normalization
makes both coefficient rows equal the canonical signed inverse, while both
value rows are 1 and both CTZs are 0. Every standard ping-pong step has
sign=(A[1] XOR B[1])=0, maps (1,1)->(1,1), and maps equal normalized
coefficient rows (u,u)->(u,u). The final four-round checkpoint sees that
same stationary orbit. No rounds or coefficient updates are skipped.

This orbit is also exact for the inherited finite-width fast coefficient
cells, not just abstract modular arithmetic. Put M=2^256 and f=M-p.
For 0<u<p, if 2u<M, the add emits 2u without carry and its even halve
returns u. If 2u>=M, the add and fold emit 2u-M+f=2u-p, an odd number
strictly below p. The odd halve subtracts f, obtaining 2u-M, and shifts
with the saved high parity bit, again obtaining u. The add carry predicate
is correct: 2u>=u in the first branch and 2u-p<u in the second. Reverse
doubling recreates the same intermediate; complemented subtraction of u
with its inherited carry/fold recovers u in both branches. Thus none of the
general fast-field cancellation exceptions is newly assumed absent on the
terminal branch. Endpoint negations see positive unit values and do nothing.

The first eight physical tape wires start as the original counter wires.
XOR the actual sign into each encoded wire. On t=0 the initial counter is
zero, so this stores the real sign. On t=1 every real sign is zero, so the
entire original counter survives. The logical control is (!t AND encoded),
computed in one temporary wire and uncomputed after its last use.
Later tape wires are unchanged. This is a reversible encoding on the direct
sum of the live and terminal supports; t distinguishes the branches.

Reverse replay decodes the logical sign, reverses the coefficient and value
updates, and clears the live encoded sign from the restored value bit ones.
On the terminal orbit these bits XOR to zero, leaving the counter unchanged.
Move, do not clone/free, each shared QReg back into the counter vector in
the original little-endian order. Undo normalization, restore the quotient,
undo its flush, then reverse the terminal map and clear t from A,q before
PZ reverse replay. The quotient codec's q=0 sentinel ignores the coefficient
ratio on this branch, so mapping before compression is compatible with it.

The decoder is an X/CCX/X network. The map uses the existing exact controlled
integer adder and multi-control XOR, including their phase-corrected measured
AND cleanup (not an unqualified claim that every emitted gate is unitary).
These implement the stated basis permutations with no relative phase.
By linearity the codec preserves superpositions and entanglement with
untouched registers on its promised support. Tests inspect every reset before
execution with the real Simulator,
check phases under forced and random measurement streams, and require
counter, coefficient, and value restoration. Existing approximate arithmetic
and inactive-path CLZ promises remain explicit prerequisites.

## Budget

Eight duplicated persistent wires disappear. One terminal flag persists and
one decoder is live only during the first eight forward/reverse rounds.
The local saving is six there and seven after those rounds. Terminal-predicate
and controlled-subtraction scratch is transient and must be measured too.
The full Q peak can remain at a different phase or at the inherited vent cap;
an eight-minus-two local count is not a whole-circuit Q claim.
