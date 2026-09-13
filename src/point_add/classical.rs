use super::modular::{mod_add, mod_rsub_vented_loaded, mod_sub_vented};
use super::{Builder, N};
use crate::circuit::{BitId, QubitId};

/// secp256k1 uses `p = 2^256 - C`, so `2^256 == C (mod p)`. The same constant
/// [`super::modular::f`] derives from the modulus, in the width this file's
/// classical arithmetic works in.
const C: u128 = (1u128 << 32) + 977;
/// Width of the register holding a small multiple of `C` (`2*C < 2^34`).
const C_BITS: usize = 35;

fn zero(circ: &mut Builder, bits: &[BitId]) {
    for &b in bits {
        circ.bit_store0(b);
    }
}

fn copy_into(circ: &mut Builder, dst: &[BitId], src: &[BitId]) {
    for (&d, &s) in dst.iter().zip(src) {
        circ.bit_copy(d, s);
    }
}

/// Loads a classical coordinate into a fresh ancilla register, runs one
/// modular operation against it, then unitarily uncomputes the register back
/// to |0> and releases it. When the coordinate was *derived* here rather than
/// owned by the caller, its classical bits are returned to the pool too.
fn against_coord(
    circ: &mut Builder,
    coord: &[BitId],
    derived: bool,
    f: impl FnOnce(&mut Builder, &[QubitId]),
) {
    let temp = circ.alloc_qubits(coord.len());
    for (&q, &b) in temp.iter().zip(coord) {
        circ.x_if_bit(q, b);
    }
    f(circ, &temp);
    for (&q, &b) in temp.iter().zip(coord) {
        circ.x_if_bit(q, b);
    }
    for q in temp {
        circ.free(q);
    }
    if derived {
        zero(circ, coord);
        circ.free_bit_vec(coord);
    }
}

pub fn coord_sub(circ: &mut Builder, dst: &[QubitId], coord: &[BitId]) {
    assert_eq!(dst.len(), N);
    assert_eq!(coord.len(), N);
    against_coord(circ, coord, false, |circ, temp| {
        mod_sub_vented(circ, temp, dst);
    });
}

pub fn coord_rsub(circ: &mut Builder, x: &[QubitId], coord: &[BitId]) {
    assert_eq!(x.len(), N);
    assert_eq!(coord.len(), N);
    let coord_p1 = classical_plus1_mod_2n(circ, coord);
    against_coord(circ, &coord_p1, true, |circ, temp| {
        mod_rsub_vented_loaded(circ, temp, x);
    });
}

pub fn coord_add3x(circ: &mut Builder, dst: &[QubitId], coord: &[BitId]) {
    assert_eq!(dst.len(), N);
    assert_eq!(coord.len(), N);
    let three_coord = classical_times3_mod_q(circ, coord);
    against_coord(circ, &three_coord, true, |circ, temp| {
        mod_add(circ, temp, dst);
    });
}

/// `3 * coord mod p`, in freshly allocated classical bits.
fn classical_times3_mod_q(circ: &mut Builder, coord: &[BitId]) -> Vec<BitId> {
    assert_eq!(coord.len(), N);

    // s = 3*coord exactly, in N+2 bits.
    let s = circ.alloc_bits(N + 2);
    zero(circ, &s);
    for _ in 0..3 {
        classical_add_into(circ, &s, coord);
    }

    // Fold the overflow back in with 2^256 == C. The high part `s >> 256` is
    // 0, 1 or 2 (never 3: 3*coord < 3*2^256), so the two high bits are
    // mutually exclusive and their contributions can just be OR-ed together.
    // That leaves r = (s mod 2^256) + (s >> 256)*C < 2^256 + 2^34.
    let av = circ.alloc_bits(C_BITS);
    zero(circ, &av);
    or_const_if(circ, &av, C, s[N]);
    or_const_if(circ, &av, 2 * C, s[N + 1]);

    let r = circ.alloc_bits(N + 1);
    copy_into(circ, &r, &s[..N]);
    circ.bit_store0(r[N]);
    classical_add_into(circ, &r, &av);

    // One conditional subtraction of p, as r - p == (r + C) - 2^256. Since
    // r + C < 2^257 it still fits in N+1 bits, so its top bit is exactly the
    // "r >= p" flag and its low N bits are the reduced value.
    let tmp = circ.alloc_bits(N + 1);
    copy_into(circ, &tmp, &r);
    classical_add_const(circ, &tmp, C);

    // result = tmp[N] ? tmp : r, as r ^ (tmp[N] & (r ^ tmp)). Folding r into
    // tmp destroys tmp, which is released immediately below anyway.
    let result = circ.alloc_bits(N);
    for i in 0..N {
        circ.bit_xor_into(tmp[i], r[i]);
        circ.bit_copy(result[i], r[i]);
        circ.bit_and_xor_into(result[i], tmp[N], tmp[i]);
    }

    for reg in [&tmp, &av, &r, &s] {
        zero(circ, reg);
        circ.free_bit_vec(reg);
    }
    result
}

/// `coord + 1 mod 2^256`, in freshly allocated classical bits.
fn classical_plus1_mod_2n(circ: &mut Builder, coord: &[BitId]) -> Vec<BitId> {
    assert_eq!(coord.len(), N);
    let s = circ.alloc_bits(N);
    copy_into(circ, &s, coord);
    classical_add_const(circ, &s, 1);
    s
}

/// `dst |= k` under `gate`. `dst` must already be 0 wherever `k` has a bit.
fn or_const_if(circ: &mut Builder, dst: &[BitId], k: u128, gate: BitId) {
    for (i, &b) in dst.iter().enumerate() {
        if (k >> i) & 1 == 1 {
            circ.push_condition(gate);
            circ.bit_store1(b);
            circ.pop_condition();
        }
    }
}

/// `acc += k`, modulo `2^acc.len()`.
fn classical_add_const(circ: &mut Builder, acc: &[BitId], k: u128) {
    let w = (128 - k.leading_zeros() as usize).min(acc.len());
    let addend = circ.alloc_bits(w);
    for (i, &b) in addend.iter().enumerate() {
        if (k >> i) & 1 == 1 {
            circ.bit_store1(b);
        } else {
            circ.bit_store0(b);
        }
    }
    classical_add_into(circ, acc, &addend);
    zero(circ, &addend);
    circ.free_bit_vec(&addend);
}

/// `acc += addend`, modulo `2^acc.len()`. `addend` may be the shorter register.
fn classical_add_into(circ: &mut Builder, acc: &[BitId], addend: &[BitId]) {
    let carry = circ.alloc_bit();
    circ.bit_store0(carry);
    let newcarry = circ.alloc_bit();
    for (i, &acc_i) in acc.iter().enumerate() {
        circ.bit_store0(newcarry);
        match addend.get(i) {
            Some(&a) => {
                circ.bit_and_xor_into(newcarry, acc_i, a);
                circ.bit_and_xor_into(newcarry, acc_i, carry);
                circ.bit_and_xor_into(newcarry, a, carry);
                circ.bit_xor_into(acc_i, a);
            }
            None => circ.bit_and_xor_into(newcarry, acc_i, carry),
        }
        circ.bit_xor_into(acc_i, carry);
        circ.bit_copy(carry, newcarry);
    }
    circ.bit_store0(newcarry);
    circ.bit_store0(carry);
    circ.free_bit(newcarry);
    circ.free_bit(carry);
}
