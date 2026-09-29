//! I-2 back-seam fusion (`experiments/v026-back-seams-001`). Public ecdsa.fail reversible
//! point-add resource research; no real-world ECDSA key is targeted.
//!
//! The FD unseed ends with two `b`-conditioned truncated constant ladders on the low `fw` bits:
//! `x -= b (F+1)` (as `x[1..fw] -= (F+1)/2`) and `y -= (1-b) F`, then clears `y` against `x` and
//! erases `b` from `x[0]` (`d` is odd iff `b`). The coordinate op that follows adds a classical value
//! `A0` modulo p: `3 ox mod p` on the divide leg (`coord_add3x`), or `ox + 1` on the multiply leg's
//! reverse subtraction (`coord_rsub`).
//!
//! Fused (`BACK_SEAM_FUSE`: bit 1 = divide leg, bit 2 = multiply leg): the x ladder is dropped and
//! the y ladder becomes ONE selected ladder `y += b ? (F+1) : -F` (same width, one Toffoli per
//! position), so `y` is still cleared against the now uncorrected `x_u = d + b (F+1)`, and `x[0]`
//! still holds `b`. The coordinate op loads `temp = A0 ^ (b & D)` for bits 1.., with `D = A0 ^ A1`,
//! `A1 = A0 - (F+1) mod p` (divide) or `A1 = A0 + (F+1) mod 2^256` (multiply), taking `b` from the
//! data wire `x[0]`; the modular op then sees `x_u + A_b = d + A0` (divide) or `~x_u + A_b = ~d + A0`
//! (multiply) bit for bit as the control does: same accumulator, same vented carry, same fold. Between
//! the fold and the carry erasure `x[0] = b ^ A0_0 ^ carry`, so the loaded bits are unloaded with the
//! same Cliffords, and the erasure compares the accumulator's top window against `A0`'s top window
//! exactly as the control does. No new Toffoli, no new persistent wire; the seam is `-(fw-2)` Toffoli
//! per leg (the dropped x ladder) in the builder's own count.
//!
//! Domain: the selected classical operand must not wrap, and the FD seed's
//! truncated x ladder must not wrap at fw. The physical uncorrected word is
//! x_corrected + b*(F+1) modulo 2^fw in its low window, not necessarily a
//! full-width addition. Native fw54 seed-x wrap is an inherited approximation
//! event; small n8/fw6 tests locate new seam differences only in seed-x-wrap
//! or selected-operand-wrap lanes. They do not prove universal full-circuit
//! error containment. Outside support both value and phase may differ, while
//! tested scratch resets remain clean. Full union qualification is separate.
//! See experiments/v026-back-seams-001/certificate and RESPONSE12.
use super::builder::Builder;
use super::classical::{classical_add_const_mod2n_at, classical_add_const_mod_at};
use super::modular::{mod_addsub_with, mod_rsub_vented_loaded_with};
use crate::circuit::{BitId, QubitId};
use alloy_primitives::U256;
use std::cell::Cell;

fn mode() -> usize {
    std::env::var("BACK_SEAM_FUSE").ok().and_then(|s| s.trim().parse().ok()).unwrap_or(0)
}
pub(crate) fn div_fused() -> bool { mode() & 1 != 0 }
pub(crate) fn mul_fused() -> bool { mode() & 2 != 0 }

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Leg { Div, Mul }

pub(crate) fn fused(leg: Leg) -> bool {
    match leg { Leg::Div => div_fused(), Leg::Mul => mul_fused() }
}

thread_local! { static UNSEEDED_FUSED: Cell<bool> = const { Cell::new(false) }; }
/// The unseed just emitted left `x` uncorrected; the coordinate op that follows must consume this.
pub(crate) fn note_fused_unseed() { UNSEEDED_FUSED.with(|u| assert!(!u.replace(true), "back seam: fused unseed not consumed")); }
fn take_fused_unseed() -> bool { UNSEEDED_FUSED.with(|u| u.replace(false)) }

/// `y += b ? k1 : k0` over `y` (carry off the top dropped): one selected ladder, one Toffoli per
/// position, the same width as the control's single `-F` ladder.
pub(crate) fn selected_ladder(c: &mut Builder, y: &[QubitId], b: QubitId, k0: U256, k1: U256) {
    let one = c.alloc_qubit();
    c.x(one);
    let map: Vec<Vec<QubitId>> = (0..y.len())
        .map(|i| {
            let (p0, p1) = (k0.bit(i), k1.bit(i));
            let mut v = Vec::new();
            if p0 { v.push(one); }
            if p0 != p1 { v.push(b); }
            v
        })
        .collect();
    super::fd_coordinate::mapped(c, y, &map);
    c.x(one);
    c.release_clean(one);
}

/// `temp[i] ^= sel & d[i]` for `i >= 1` (bit 0 is never loaded: it carries the selector's recovery).
fn xor_selected(c: &mut Builder, sel: QubitId, temp: &[QubitId], d: &[BitId]) {
    for i in 1..temp.len() {
        c.push_condition(d[i]);
        c.cx(sel, temp[i]);
        c.pop_condition();
    }
}

fn zero(c: &mut Builder, bits: &[BitId]) {
    for &b in bits { c.bit_store0(b); }
}

fn modulus(n: usize, f: U256) -> U256 {
    if n == 256 {
        assert_eq!(super::modular::f(), f, "back seam: F must be the tree's fold constant at n = 256");
        super::SECP256K1_P
    } else {
        (U256::from(1u64) << n) - f
    }
}

/// Coordinate op against the classical value `a0` (freed here): `dst += a0 (mod p)` on the divide
/// leg, `dst <- a0 - dst - 1 (mod p)` on the multiply leg (`a0 = ox + 1`). `fused` expects `dst` at
/// the uncorrected unseed value `d + b (F+1)` with `dst[0] = b`; otherwise this is the control's
/// load / modular op / unload sequence.
pub(crate) fn coord_op_at(
    c: &mut Builder, dst: &[QubitId], a0: &[BitId], leg: Leg, n: usize, f: U256, fs: usize, k: usize, fused: bool,
) {
    assert_eq!(dst.len(), n);
    assert_eq!(a0.len(), n);
    assert_eq!(take_fused_unseed(), fused, "back seam: unseed / coordinate op fusion mismatch");
    let fp1 = f + U256::from(1u64);
    let temp = c.alloc_qubits(n);
    for i in 0..n { c.x_if_bit(temp[i], a0[i]); }
    let d: Option<Vec<BitId>> = fused.then(|| {
        let a1 = match leg {
            Leg::Div => classical_add_const_mod_at(c, a0, modulus(n, f) - fp1, n, f.to::<u128>()),
            Leg::Mul => classical_add_const_mod2n_at(c, a0, fp1.to::<u128>()),
        };
        let d = c.alloc_bits(n);
        for i in 0..n {
            c.bit_copy(d[i], a0[i]);
            c.bit_xor_into(d[i], a1[i]);
        }
        zero(c, &a1);
        c.free_bit_vec(&a1);
        d
    });
    if let Some(d) = &d { xor_selected(c, dst[0], &temp, d); }
    let mut hook = |c: &mut Builder, carry: QubitId| {
        if let Some(d) = &d {
            c.cx(carry, dst[0]);
            c.x_if_bit(dst[0], a0[0]);
            xor_selected(c, dst[0], &temp, d);
            c.x_if_bit(dst[0], a0[0]);
            c.cx(carry, dst[0]);
        }
    };
    let mid: Option<&mut dyn FnMut(&mut Builder, QubitId)> = if d.is_some() { Some(&mut hook) } else { None };
    match leg {
        Leg::Div => mod_addsub_with(c, false, &temp, dst, fs, k, f, mid),
        Leg::Mul => mod_rsub_vented_loaded_with(c, &temp, dst, fs, k, f, mid),
    }
    for i in 0..n { c.x_if_bit(temp[i], a0[i]); }
    c.free_vec(&temp);
    if let Some(d) = d {
        zero(c, &d);
        c.free_bit_vec(&d);
    }
    zero(c, a0);
    c.free_bit_vec(a0);
}
