# Architecture, from first principles

Everything here is measured against the shipped circuit unless marked [INFERENCE].

## Layer 1 — the algorithm. Two inversions is a hard floor.

`trailmix_ludicrous/ec_add.rs::ec_add` is Roetteler-style in-place affine addition:

```
x -= x0 ;  y -= y0
lambda <- y/x                     ModDiv          (Direction::Inverse)
x += 3*x0
x -= lambda^2                     modular square
y <- lambda * x                   ModDiv reversed (Direction::Forward)
y -= y0 ; x <- x0 - x
```

The second "multiply" is a **division circuit run backwards**. In-place multiplication by a *quantum* value
`|λ⟩|x⟩ → |λx⟩|x⟩` is a permutation only because x ≠ 0, and realising it requires the division machinery — you cannot
erase λ without dividing. And you cannot avoid erasing it: after `(t_x,t_y)` are overwritten by `(R_x,R_y)`, recovering
`dx` needs to invert `R_x − Q_x`.

Priced alternatives, all losing:

| approach | cost | why dead |
|---|---|---|
| Fermat, `x^(p-2)` | ~134M CCX | 255 squarings + ~15 muls |
| Jacobian coordinates | ~5.5M CCX | no peak reduction either, and affine in/out forces a final inversion |
| Montgomery batch-invert both | n/a | data-dependent: `c = Qx − Rx` only exists AFTER Rx, which needs the first inverse |
| one-inversion point-add | n/a | `ONE_INV_DX3_AFFINE_PA_BLOCKER` — needs a second inversion to recover dx |
| Kim inversion drop-in | 2,530,240 T @ 4,102 q | dead for a ~1200q target |

## Layer 2 — the inversion

**Jump-2 binary extended Euclid (Stein/Kaliski), NOT Bernstein–Yang.** `schedule.rs`: `ITERS=258`, `JUMP=2`.

Per iteration (`gcd.rs:1162-1305`): truncate u,v to `SCHED_J2[i]`; right-shift v (unconditional for i>0, conditional on
`t1` at i=0); `s2 = (v now even)` and if so shift again; `subtracted = v[0]`; `swp = subtracted AND
truncated_lt(v,u,cmp_window(i))`; if swp swap u,v; if subtracted `v -= u`. A 3-bit symbol `(subtracted, swp, s2)` goes
to the dialog tape.

**Only 5 of 8 symbols are reachable**, and the constraint is structural: `s2=0 ⇒ subtracted=1` (if no second halving
happened, v[0] was 1), and `subtracted=0 ⇒ swp=0` (swp is ANDed with subtracted).

The preserved invariant is bilinear:
```
u*X + v*Y  ==  num*den   (mod p)
seed  (u,v,X,Y) = (p, den, 0, num)      final (1, 0, R, 0)
```
The walk applies `M = L·S·D` with `D = diag(1, 2^-(1+s2))`; the apply applies `M^-T`, whose `D^-T = diag(1, 2^(1+s2))`
IS the 1+s2 doublings. **So the s2 conditionality is load-bearing on both sides** — drop it on either and the pairing
slips by a data-dependent `2^-z`.

Bernstein–Yang would be *worse*: its proven 256-bit bounds are 590 (hddivstep) / 741 (divstep) against the 516
divsteps here. The gap to the literature is negative.

## Layer 3 — the qubit budget

```
peak = 512 (Bezout pair) + tape(i) + u(i) + v(i) + ~22 ancilla
```
Measured with the built-in B0 owner map (`B0_WIN_LO`/`B0_WIN_HI`, mod.rs:392-419) at the binding op 25841, divstep i=0:

| n | site | role |
|---|---|---|
| 256 | `trailmix_ludicrous/mod.rs:363` `y2` | Bezout accumulator X |
| 256 | `gcd.rs:1842` `tmp` | Bezout numerator Y |
| 255 | `mod.rs:362` `v` | divstep g — 255 because `v[0]≡0` is parked+loaned |
| 255 | `gcd.rs:1138` `u` | divstep f — 255 because `u[0]≡1` is parked+loaned |
| 124 | `gidney.rs:1186` `inner` | clean-carry ladder, BORROWED, fills to the cap |
| 2 | `gidney.rs:1546` `cy` | chunk-boundary carries |
| 4 | gcd.rs:1146/1148/1149/1203 | subtracted, s2, t1, swap_flag |
| **1152** | | |

**Why the peak is a flat plateau, not a spike**: `u+v` shrink at 2 qubits/step (SCHED_J2) while the tape grows at
2.333 bits/step. Net +0.33/step. The two curves nearly cancel, which is exactly what makes this circuit hard to
improve — there is no single fat moment to attack.

Tape = `dialog_tape_qubits(85,258)` = 2 + 7·85 + 5 = **602** (codec.rs:304-311, 444-474).

## Layer 4 — the Toffoli budget by primitive

Total emitted at the old head: 1,394,540 CCX + 5,341 CCZ.

| bucket | CCX | % |
|---|---|---|
| adders (GCD 300,164 + apply register 365,491) | 665,655 | 47.7 |
| controlled permutation (apply cswap 131,328 + apply fold 132,612 + GCD cswap 140,780 + GCD cond shift 141,249) | 545,969 | 39.2 |
| modular reductions | ~70,490 | 5.1 |
| square | 60,545 | 4.3 |
| comparators | ~41,500 | 3.0 |
| codec | 6,304 | 0.5 |

**The emitted→executed discount is NOT uniform.** Measured with a purpose-built profiler (`TRACE_TLM_TOF=1`):
apply register phases 13.7%, `mod_add_clean` exactly 50%, and **0.000%** on swap / gcd_forward_compare /
gcd_forward_shift / square_*_build. Anything inside a `push_condition(hmr_bit)` executes on half the shots.
Never compare an emitted delta against the executed baseline.

## Layer 5 — λ, the axis that isn't in the score

See `notes/02-lambda.md`. This is the one that actually decides what ships.
