//! Arithmetic modulo p = 2^256 - c (secp256k1, c = 2^32 + 977) on 256-qubit registers (LSB first).
//!
//! Values are kept in [0, 2^256); every routine is exact when inputs are reduced (< p) up to events of
//! probability <= 2^-64 per call (truncated carry propagation, lazy reduction), far below the 9024-shot budget.
//! Reductions fold the overflow back in as + c (since 2^256 = c mod p), so only ~100-lane constant adds occur.

use super::arith::{down_m, up_m, Dm};
use super::builder::B;
use crate::circuit::QubitId;

pub const C: u64 = (1u64 << 32) + 977;
/// Lanes touched by the folded constant adds (33-bit constant + 32 lanes of carry headroom).
pub const FOLD: usize = 65;
/// Lanes compared when erasing an add's overflow flag (top lanes only; differs w.p. <= 2^-32).
pub const CMPT: usize = 32;

fn bits_of(k: u64) -> Vec<usize> {
    (0..64).filter(|&i| (k >> i) & 1 == 1).collect()
}

/// Scratch for the modular routines: carry-in qubit, constant lanes, overflow flag, a |1> qubit.
pub struct Ms {
    pub c0: QubitId,
    pub s: Vec<QubitId>, // FOLD lanes
    pub k: QubitId,
    pub one: QubitId,
}

impl Ms {
    pub fn alloc(b: &mut B) -> Ms {
        let c0 = b.alloc();
        let s = b.alloc_n(FOLD);
        let k = b.alloc();
        let one = b.alloc();
        b.x(one);
        Ms { c0, s, k, one }
    }
    pub fn release(self, b: &mut B) {
        b.x(self.one);
        b.free(self.c0);
        b.free_n(&self.s);
        b.free(self.k);
        b.free(self.one);
    }
}

/// t[lo..lo+FOLD) += (ctrl ? k : 0) for a classical constant k < 2^33 (carry truncated at lane lo+FOLD).
fn add_small(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: QubitId, k: u64) {
    let bs: Vec<usize> = bits_of(k).into_iter().filter(|&j| j >= lo).map(|j| j - lo).collect();
    let n = FOLD.min(t.len() - lo);
    for &j in &bs {
        b.cx(ctrl, ms.s[j]);
    }
    let tt = &t[lo..lo + n];
    let ss = &ms.s[..n];
    let u = up_m(b, tt, ss, ms.c0, false);
    let d = down_m(b, tt, ss, ms.c0, Dm::Sum, false);
    b.play(&u, false);
    b.play(&d, false);
    for &j in &bs {
        b.cx(ctrl, ms.s[j]);
    }
}

/// t[lo..lo+FOLD) -= (ctrl ? k : 0).
fn sub_small(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: QubitId, k: u64) {
    b.begin();
    add_small(b, ms, t, lo, ctrl, k);
    let r = b.end();
    b.play(&r, true);
}

/// z <- 2 z mod p in place. The lane vector is relabelled (z[0] <- old top bit h), then h (c - 1) is added
/// (c - 1 is even, so lane 0 keeps h and the map is a bijection). ~2 * 93 Toffoli.
pub fn mod_double(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>) {
    let top = z.pop().unwrap();
    z.insert(0, top);
    let h = z[0];
    add_small(b, ms, z, 4, h, C - 1); // lowest set bit of c - 1 is bit 4
}

/// Inverse of mod_double (z <- z / 2 mod p).
pub fn mod_halve(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>) {
    let h = z[0];
    sub_small(b, ms, z, 4, h, C - 1);
    let low = z.remove(0);
    z.push(low);
}

/// z <- z + (ctl ? y : 0) mod p. Toffoli ~ 3*256 + 2*FOLD + 2*CMPT + 1.
pub fn ctrl_modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId) {
    // conditional add with the carry out captured as k = ctl & carry
    let u = up_m(b, z, y, ms.c0, false);
    let d = down_m(b, z, y, ms.c0, Dm::Cond(ctl), false);
    b.play(&u, false);
    b.and_c(ctl, y[255], ms.k);
    b.play(&d, false);
    // fold: 2^256 = c (mod p)
    add_small(b, ms, z, 0, ms.k, C);
    // erase k = ctl & [z < y] (top-lane compare)
    let zt = &z[256 - CMPT..];
    let yt = &y[256 - CMPT..];
    let u2 = up_m(b, zt, yt, ms.c0, true);
    b.play(&u2, false);
    b.and_u(ctl, yt[CMPT - 1], ms.k);
    b.play(&u2, true);
}

pub fn modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    ctrl_modadd(b, ms, z, y, ms.one);
}
pub fn modsub(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    b.begin();
    modadd(b, ms, z, y);
    let r = b.end();
    b.play(&r, true);
}

/// z <- (ctl ? p - z : z) for z in [1, p): conditional complement, then subtract c - 1.
pub fn ctrl_neg(b: &mut B, ms: &Ms, z: &[QubitId], ctl: QubitId) {
    for &q in z {
        b.cx(ctl, q);
    }
    sub_small(b, ms, z, 4, ctl, C - 1);
}

/// z = a * y mod p into a zero register z (Horner, top bit of a first).
pub fn product(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    for i in (0..256).rev() {
        if i != 255 {
            mod_double(b, ms, z);
        }
        ctrl_modadd(b, ms, z, y, a[i]);
    }
}

/// z += a * y mod p (any z), doubling y in place and restoring it; `a` must not overlap `y`.
pub fn mac(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &mut Vec<QubitId>) {
    for i in 0..256 {
        ctrl_modadd(b, ms, z, y, a[i]);
        if i != 255 {
            mod_double(b, ms, y);
        }
    }
    for _ in 0..255 {
        mod_halve(b, ms, y);
    }
}

/// Load a classical bit register into zero qubits (no Toffoli).
pub fn load_bits(b: &mut B, q: &[QubitId], bits: &[crate::circuit::BitId]) {
    for (&qq, &bb) in q.iter().zip(bits) {
        b.x_if(qq, bb);
    }
}
