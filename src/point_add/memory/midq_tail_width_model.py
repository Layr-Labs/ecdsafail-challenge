"""Regenerate MIDQ_TAIL_VALUE_WIDTH for a shrunken-PZ prefix cut / ping-pong tail.

Classical model, reconstructed from the in-tree references (probe-1010):
  * PZ step  = record_sample, shrunken_pz_schedule.rs:442-506 (single-q Kaliski step,
               the same model the nonce support search uses).
  * handoff  = midq_tail_forward, shrunken_pz_state_machine.rs:3272-3318: resize a,b,
               then strip the single power of two from the (at most one) even value.
  * round    = step_model, midq_odd_values_tests.rs:270-301 and midq_value_round_forward
               :3174-3211: sign = bit1(s)^bit1(t); t = (t -+ s) >> 1 on odd signed values,
               target alternates b (even rounds) / a (odd rounds).
  * table    = per-round max signed width over N random secp256k1 field elements,
               +1 bit, then made monotone non-increasing (comment at state_machine.rs:2722).
The shipped table (cut=360, 224 rounds) is reproduced in distribution by this model:
handoff 85, width-4 onset at ~217-220, but any 200k draw differs by 1-3 bits per round
(the shipped table sits between the 2nd and 3rd largest width of a fresh draw). A fresh
200k draw violates the shipped table at ~3.5e-5 per input; this is NOT modelled by
repair_sample / thin_factor_repairs_u256, so it is an unmodelled miss source for the
nonce grind.

Usage: python midq_tail_width_model.py CUT ROUNDS|auto SAMPLES [SEED] [WORKERS]
  ROUNDS=auto -> rounds = (first index where the +1/monotone width <= 4) + 4, matching
  the checkpoint invariant (midq_tail_checkpoint.rs:26,57-61: last 4 rounds at width 4).
"""
import sys, random, multiprocessing as mp
P = (1 << 256) - (1 << 32) - 977
HALF = P >> 1
def bl(x): return x.bit_length()
def sw(v):  # minimal two's-complement width
    w = 1
    while not (-(1 << (w - 1)) <= v < (1 << (w - 1))): w += 1
    return w
def pz_prefix(x_orig, cut):
    x = P - x_orig if x_orig > HALF else x_orig
    a, b, ca, cb, q = P, x, 0, 1, 0
    terminated = False
    for _ in range(cut):
        if a == 0 and b == 1 and q == 0:
            terminated = True; continue
        if a < b and q != 0:
            s2 = (q & -q).bit_length() - 1
            q ^= 1 << s2; ca += cb << s2
        if ca < cb:
            s = bl(a) - bl(b)
            if s >= 0 and a < (b << s): s -= 1
            if s >= 0:
                bsh = b << s
                if a >= bsh: a -= bsh; q ^= 1 << s
        if q == 0 and a != 0:
            a, b = b, a; ca, cb = cb, ca
    terminated = a == 0 and q == 0  # counter_tape::xor_terminal predicate
    return a, b, q, terminated
def one(args):
    seed, n, cut, rounds = args
    rng = random.Random(seed)
    maxw = [0] * (rounds + 1); maxpre = 0; term = 0; unconv = 0; drain = 0
    for _ in range(n):
        x = rng.randrange(1, P)
        a, b, q, t = pz_prefix(x, cut)
        term += t
        maxpre = max(maxpre, bl(a), bl(b))
        if t:  # counter_tape terminal branch: a forced to 1 (counter_tape.rs:prepare)
            a = 1
        elif a == 0:  # EEA done but quotient still draining (q != 0): NOT terminal per
            drain += 1  # counter_tape::xor_terminal; the tail's odd-value invariant is broken.
            a = 1
        if a and a % 2 == 0: a >>= (a & -a).bit_length() - 1
        if b and b % 2 == 0: b >>= (b & -b).bit_length() - 1
        assert a % 2 == 1 and b % 2 == 1, (hex(x), a, b)
        pair = [a, b]
        for r in range(rounds):
            maxw[r] = max(maxw[r], sw(pair[0]), sw(pair[1]))
            t_ = 1 if r % 2 == 0 else 0; s_ = 1 - t_
            sign = ((pair[s_] ^ pair[t_]) >> 1) & 1
            pair[t_] = (pair[t_] + (-pair[s_] if sign else pair[s_])) >> 1
        maxw[rounds] = max(maxw[rounds], sw(pair[0]), sw(pair[1]))
        if abs(pair[0]) != 1 or abs(pair[1]) != 1: unconv += 1
    return maxw, maxpre, term, unconv, drain
if __name__ == '__main__':
    cut, n = int(sys.argv[1]), int(sys.argv[3])
    auto = sys.argv[2] == 'auto'
    rounds = 400 if auto else int(sys.argv[2])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 2026
    workers = int(sys.argv[5]) if len(sys.argv) > 5 else 16
    per = n // workers
    with mp.Pool(workers) as pool:
        res = pool.map(one, [(seed * 1000 + i, per, cut, rounds) for i in range(workers)])
    raw = [max(r[0][i] for r in res) for i in range(rounds + 1)]
    maxpre = max(r[1] for r in res); term = sum(r[2] for r in res); unconv = sum(r[3] for r in res); drain = sum(r[4] for r in res)
    mono = [w + 1 for w in raw]
    for i in range(len(mono) - 2, -1, -1): mono[i] = max(mono[i], mono[i + 1])
    first4 = next((i for i, w in enumerate(mono) if w <= 4), None)
    if auto:
        assert first4 is not None, "never reached width 4 within 400 rounds"
        rounds = first4 + 4
        mono = mono[:rounds + 1]
    mono = [max(w, 4) for w in mono]  # floor 4: stable signed-unit orbit (comment :2723-2724)
    print(f"cut={cut} rounds={rounds} samples={per*workers} seed={seed} max_unsigned_bitlen_at_handoff={maxpre} "
          f"terminal_at_cut={term} a0_q_draining_at_cut={drain} not_at_unit_after_rounds={unconv} first_index_width<=4={first4}")
    print(f"const MIDQ_PZ_CUT: usize = {cut};")
    print(f"const MIDQ_TAIL_ROUNDS: usize = {rounds};")
    print("const MIDQ_TAIL_VALUE_WIDTH: [u8; MIDQ_TAIL_ROUNDS + 1] = [")
    for i in range(0, len(mono), 28):
        print("    " + ",".join(str(w) for w in mono[i:i + 28]) + ",")
    print("];")
    print(f"// checkpoint START must be {rounds - 4} (midq_tail_checkpoint.rs:26); tests assert [START-1]==5, len, 232/234 (midq_tail_checkpoint_tests.rs:425-433)")
