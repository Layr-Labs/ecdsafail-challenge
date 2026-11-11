# M19 proof and build chain (not an evaluator receipt)

Credit: add/subtract lead from Claude's literature survey of Litinski 2024.
Biased-residue payload and W=2g+f control design are Claude's, developed at
Michelle's direction. Integration and certificates are local; no submissions.

## All-input arithmetic domains and finite schedule
The inherited M12 interface normalizes any 256-bit divisor modulo the prime,
replaces zero by one coherently, and restores the original divisor on exit.
The payload is canonical; arbitrary point exceptions use M12's unchanged
finite-exception wrapper and full field arithmetic.

Initially f=p, 1<=g<=p-1, gcd(f,g)=1. A binary-GCD row keeps f odd,
nonnegative g, gcd=1, f,g<=p. If g>0 its product decreases by at least 1/2:
for even g, fg -> fg/2; for odd g it becomes min(f,g)*|f-g|/2<=fg/2.
Thus fg<=floor(p(p-1)/2^i), and after 512 rows g=0, f=1.
If g=0, gcd=1 forces f=1 and the row is stationary. Hence cap_i=
max(1,min(p,floor(p(p-1)/2^i))) is a bound on BOTH words on every input,
not a fitted convergence claim. All guard/tail leases derive from this bound.

## W=2g+f control
f and W are odd, so g's parity equals W_1 XOR f_1 (no low-bit borrow).
If e=0, (W+f)/2=g+f, encoding f'=f,g'=g/2. If e=1,
(W-f)/2=g, and c=[g<f]; swapping f and that word exactly encodes
f'=min(f,g),g'=|g-f|/2. Therefore every recorded (e,c) equals M12's;
c=>e is exact, so the inherited 27-state tape codec remains valid.
W<=3cap; the temporary W+f<=4cap fits every chosen width (including
its guard). No carry is discarded on a reachable state. Width reduction
and tape aliasing use these all-input zero-tail bounds, not sample maxima.

## Payload change of coordinates
Let V=2u, R=w-u modulo p. M12's swap-then-subtract/half row becomes
w <- (w+(1-2e)u)/2 then controlled swap(u,w). For c=0 this follows
by substitution; for c=1 (necessarily e=1) the new pair is
((w-u)/2,u), precisely the transform of (V',R')=(R,(V-R)/2).
Start (V,R)=(0,y) means (u,w)=(0,y). Finish (V,R)=(y/eff(a),0)
means u=w; XOR clears u and exact modular doubling of w returns the result.

## Biased addition and exact h erase
Let B=2^256, A=(B-1-p)/2=2^31+488, and store x~=x+A in [A,A+p).
For e=0 the full sum is w~+u~+1=w+u+B-p; carry t=[w+u>=p].
For e=1 it is w~+NOT(u~)+1=w-u+B; carry t=[w>=u].
Let h=NOT t. Adding A if h=0 or A+p if h=1 yields the exact
canonical result plus A, with all full carries accounted for. Since
A+p=B-1-A, this conditional constant is a bitwise complement mux.
For addition, the final result z satisfies z>=u iff no reduction occurred.
For subtraction, z>=p-u iff a borrow occurred. Consequently in both cases
h=[z~ >= (u~ XOR e...e)], on EVERY canonical input, including equal words
and zero. This is a full 256-bit unsigned comparison, not a high-bit window.

## Biased half and exit
For canonical z set k=z mod2 from z~_0 XOR A_0. The constant add produces
T=(z+2A+kp) mod B. If k=0 then T=z+2A is even and rotating right gives
z/2+A. If k=1 then T=z-1 is even; the two CNOTs put k into bit zero and
clear the guard; the full cyclic rotation gives (z-1)/2+B/2=(z+p)/2+A.
Thus the old parity is exactly the output top bit, without a comparator.
For exit let t=[z~>=B/2]=[z>=(p+1)/2]. A left cyclic rotation gives
s=2(z+A)-tB+t. Subtracting (1-t)2A produces 2z-tp, canonical modular
doubling, with no dropped guard or input data.

## MBU/phase proof chain
1. The coherent Rust divide is compared gate by gate with Claude's independent
Python model after a proved reordering of ONLY the final 250 distinct X
constant-frame gates (Python ascending, Rust descending; they commute exactly); full point integration is byte-compared in BOTH
orientations (model_identity.json and sites_full.log).
2. sound_comp_mbu.rs uses syntactic all-basis adder/Bennett contracts,
Boolean expression identities, bounded exact ANF certificates, and codec
facts. It DOES NOT use M12's old absolute gate-index semantic/helper facts.
Every one of the 1,792,348 rewrites is independently replayed, including
unchanged classical preparation/inverse and zero proof epochs.
3. Predicate factorization replaces only annotated cleanups, excluding the
normalization prologue. Full remaining borrow chains are retained.
The flag is absent from every other operation of its phase-repair block.
Literal byte replay checks every unchanged gate and every phase-library
operation; inner AND MBU repairs are retained, not reversed as measurements.
4. For a known predicate flag P(x), X-measurement outcome m has amplitude
(-1)^(m P(x))/sqrt(2). Conditional exact phase evaluation cancels it.
Thus EACH Kraus branch is U/sqrt(2), including superposed inputs: outcomes
are uniform and independent of the data. No input data register is measured.
Inner AND erasure obeys the same theorem. Complete 1-bit borrow truth tables
plus induction over ALL allocated bits prove both LT and word GE, and
predicate_proof.py verifies the resulting phase programs in small complete
domains and at every selected long-borrow boundary. Random tests are only
regressions, never the proof or a bound.

## Reproduction stages
- cargo test --offline --locked --release --bin sound_addsub_unitary
- cargo build --offline --locked --release --bin sound_addsub_point_unitary --bin sound_addsub --bin sound_addsub_final --bin sound_addsub_sites
- sound_addsub_point_unitary point_m12/smoke.tsv point_m19/unitary --no-serialize
- sound_addsub --optimize point_m19/unitary point_m19/generic_mbu
- sound_addsub --proof-replay point_m19/unitary point_m19/generic_mbu
- sound_addsub_sites; python3 point_m19/resource_gate.py
- python3 point_m19/integrate.py; python3 point_m19/replay_rewrite.py
- python3 point_m19/predicate_proof.py; python3 point_m19/run_own.py
All output-producing stages require fresh destination files/directories.
The final official local evaluator receipt and verified metrics are separate;
resource projections or coherent truth-table tests alone are NOT a win.
