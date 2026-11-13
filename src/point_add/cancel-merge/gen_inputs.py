#!/usr/bin/env python3
"""gen_inputs.py OUT.bin NSHOTS [seed]: random secp256k1 point pairs and their sums, 6 x 32 bytes LE per shot,
skipping the same cases the official evaluator skips (equal x, either point at infinity)."""
import random, sys
p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
G = (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
     0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)
def add(P, Q):
    if P is None: return Q
    if Q is None: return P
    if P[0] == Q[0]:
        if (P[1] + Q[1]) % p == 0: return None
        l = 3 * P[0] * P[0] * pow(2 * P[1], -1, p) % p
    else:
        l = (Q[1] - P[1]) * pow(Q[0] - P[0], -1, p) % p
    x = (l * l - P[0] - Q[0]) % p
    return (x, (l * (P[0] - x) - P[1]) % p)
def mul(k, P):
    R = None
    while k:
        if k & 1: R = add(R, P)
        P = add(P, P); k >>= 1
    return R
out, shots = sys.argv[1], int(sys.argv[2])
rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 20261110)
with open(out, 'wb') as f:
    done = 0
    while done < shots:
        t = mul(rng.randrange(1, n), G); o = mul(rng.randrange(1, n), G)
        if t[0] == o[0]: continue
        e = add(t, o)
        for v in (t[0], t[1], o[0], o[1], e[0], e[1]): f.write(v.to_bytes(32, 'little'))
        done += 1
print('wrote', shots, 'shots to', out)
