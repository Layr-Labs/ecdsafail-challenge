//! Arithmetic modulo p = 2^256 - c (secp256k1, c = 2^32 + 977) for frogdrop, with a lean fold.
//!
//! Every reduction folds an overflow back in as + c (2^256 = c mod p). The fold adds the constant's low part (977,
//! or 61 << 4 for c - 1) with a short ripple over LOWL clean operand lanes, then pushes its carry through 32 lanes
//! with an increment that BORROWS dirty qubits (x -= g; g = ~g; x -= g; g = ~g is x + 1 for any g, Gidney's trick),
//! and adds the 2^32 bit as a second borrowed increment of (ctrl, lanes 32..64). Each increment drops a carry past
//! its 32 lanes w.p. ~2^-32. Only 13 clean qubits, so the product phases sit well under the traversal's peak.

use super::arith::{down_m, up_m, Dm};
use super::builder::B;
use crate::circuit::QubitId;

pub const C: u64 = (1u64 << 32) + 977;
/// clean operand lanes of the folded constants' low parts (977 < 2^10)
pub const LOWL: usize = 10;
/// carry headroom of each borrowed increment
pub const HEAD: usize = 32;
/// Lanes compared when erasing an add's overflow flag (top lanes only; differs w.p. <= 2^-32).
pub const CMPT: usize = 32;

/// Scratch: carry-in qubit, low constant lanes, overflow flag, carry-in of the borrowed increments.
pub struct Ms {
    pub c0: QubitId,
    pub s: Vec<QubitId>,
    pub k: QubitId,
    pub c1: QubitId,
}

impl Ms {
    pub fn alloc(b: &mut B) -> Ms {
        let c0 = b.alloc();
        let s = b.alloc_n(LOWL);
        let k = b.alloc();
        let c1 = b.alloc();
        Ms { c0, s, k, c1 }
    }
    /// Scratch without the constant lanes (add_small then uses signed-digit dirty increments): 3 qubits.
    /// (c1 = c0: the lean add_small only uses c1, never while c0 holds a carry): 2 qubits.
    pub fn alloc_lean(b: &mut B) -> Ms {
        let c0 = b.alloc();
        let k = b.alloc();
        Ms { c0, s: vec![], k, c1: c0 }
    }
    pub fn release(self, b: &mut B) {
        b.free(self.c0);
        b.free_n(&self.s);
        b.free(self.k);
        if self.c1 != self.c0 {
            b.free(self.c1);
        }
    }
}

/// x (LSB first) += 1 mod 2^n using n borrowed qubits g (any state, restored) and one clean c1.
pub(crate) fn inc_dirty(b: &mut B, x: &[QubitId], g: &[QubitId], c1: QubitId) {
    let n = x.len();
    let g = &g[..n];
    for _ in 0..2 {
        // x -= g
        let u = up_m(b, x, g, c1, true);
        let d = down_m(b, x, g, c1, Dm::Sum, true);
        b.play(&u, false);
        b.play(&d, false);
        for &q in g {
            b.x(q);
        }
    }
}

/// t += (ctrl ? k : 0) (ctrl None: unconditional) for k = 2^32 + (low << lo), low < 2^LOWL (c or c - 1).
/// `dirty`: >= HEAD + 1 qubits disjoint from t, ctrl and the scratch.
pub(crate) fn add_small(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId]) {
    assert!(k >> 33 == 0 && lo < 32);
    if ms.s.is_empty() {
        add_small_lean(b, ms, t, lo, ctrl, k, dirty);
        return;
    }
    let low = (k & ((1u64 << 32) - 1)) >> lo;
    assert_eq!(low << lo, k & ((1u64 << 32) - 1));
    let nl = (64 - low.leading_zeros()) as usize;
    assert!(nl <= LOWL && lo + nl + HEAD <= 32 + HEAD && 32 + HEAD <= t.len());
    if nl > 0 {
        let bs: Vec<usize> = (0..nl).filter(|&j| (low >> j) & 1 == 1).collect();
        let load = |b: &mut B| {
            for &j in &bs {
                match ctrl {
                    Some(c) => b.cx(c, ms.s[j]),
                    None => b.x(ms.s[j]),
                }
            }
        };
        load(b);
        let tt = &t[lo..lo + nl];
        let ss = &ms.s[..nl];
        let u = up_m(b, tt, ss, ms.c0, false);
        let d = down_m(b, tt, ss, ms.c0, Dm::Sum, false);
        b.play(&u, false);
        // carry out of the low part sits on ss[nl - 1]: (carry, next HEAD lanes) + 1, then flip the carry back
        let mut xr = vec![ss[nl - 1]];
        xr.extend(&t[lo + nl..lo + nl + HEAD]);
        inc_dirty(b, &xr, dirty, ms.c1);
        b.x(ss[nl - 1]);
        b.play(&d, false);
        load(b);
    }
    if (k >> 32) & 1 == 1 {
        match ctrl {
            Some(c) => {
                let mut xr = vec![c];
                xr.extend(&t[32..32 + HEAD]);
                inc_dirty(b, &xr, dirty, ms.c1);
                b.x(c);
            }
            None => inc_dirty(b, &t[32..32 + HEAD], dirty, ms.c1),
        }
    }
}

/// add_small without constant lanes: t += ctrl * k as signed-digit (NAF) controlled increments / decrements of
/// t[j .. 32 + HEAD) on borrowed lanes (`dirty` >= 33 + HEAD - lo qubits disjoint from t and ctrl), `ms.c1` clean.
fn add_small_lean(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId]) {
    let end = 32 + HEAD;
    assert!(end <= t.len());
    let low = (k & ((1u64 << 32) - 1)) >> lo;
    assert_eq!(low << lo, k & ((1u64 << 32) - 1));
    // NAF digits of low, plus the 2^32 bit
    let mut digs: Vec<(usize, bool)> = vec![]; // (absolute bit, negative)
    let mut n = low as i64;
    let mut i = 0usize;
    while n != 0 {
        if n & 1 == 1 {
            let d = 2 - (n & 3); // +1 or -1
            digs.push((lo + i, d < 0));
            n -= d;
        }
        n >>= 1;
        i += 1;
    }
    if (k >> 32) & 1 == 1 {
        digs.push((32, false));
    }
    for (j, neg) in digs {
        b.begin();
        match ctrl {
            Some(c) => {
                let mut xr = vec![c];
                xr.extend(&t[j..end]);
                inc_dirty(b, &xr, dirty, ms.c1);
                b.x(c);
            }
            None => inc_dirty(b, &t[j..end], dirty, ms.c1),
        }
        let r = b.end();
        b.play(&r, neg);
    }
}

fn sub_small(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId]) {
    b.begin();
    add_small(b, ms, t, lo, ctrl, k, dirty);
    let r = b.end();
    b.play(&r, true);
}

/// z <- 2 z mod p in place (relabel z[0] <- old top bit h, then add h (c - 1); c - 1 is even so lane 0 keeps h).
pub fn mod_double(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, dirty: &[QubitId]) {
    let top = z.pop().unwrap();
    z.insert(0, top);
    let h = z[0];
    add_small(b, ms, z, 4, Some(h), C - 1, dirty); // lowest set bit of c - 1 is bit 4
}

/// Inverse of mod_double (z <- z / 2 mod p).
pub fn mod_halve(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, dirty: &[QubitId]) {
    let h = z[0];
    sub_small(b, ms, z, 4, Some(h), C - 1, dirty);
    let low = z.remove(0);
    z.push(low);
}

/// z <- z + (ctl ? y : 0) mod p (y is restored before the fold and lends its qubits as the dirty lanes).
pub fn ctrl_modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId) {
    let u = up_m(b, z, y, ms.c0, false);
    let d = down_m(b, z, y, ms.c0, Dm::Cond(ctl), false);
    b.play(&u, false);
    b.and_c(ctl, y[255], ms.k);
    b.play(&d, false);
    add_small(b, ms, z, 0, Some(ms.k), C, y);
    // erase k = ctl & [z < y] (top-lane compare)
    let zt = &z[256 - CMPT..];
    let yt = &y[256 - CMPT..];
    let u2 = up_m(b, zt, yt, ms.c0, true);
    b.play(&u2, false);
    b.and_u(ctl, yt[CMPT - 1], ms.k);
    b.play(&u2, true);
}

pub fn modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    let one = b.alloc();
    b.x(one);
    ctrl_modadd(b, ms, z, y, one);
    b.x(one);
    b.free(one);
}
pub fn modsub(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    let one = b.alloc();
    b.x(one);
    b.begin();
    ctrl_modadd(b, ms, z, y, one);
    let r = b.end();
    b.play(&r, true);
    b.x(one);
    b.free(one);
}

/// z <- (ctl ? p - z : z) for z in [1, p) (ctl None: always): complement, then subtract c - 1.
pub fn ctrl_neg(b: &mut B, ms: &Ms, z: &[QubitId], ctl: Option<QubitId>, dirty: &[QubitId]) {
    for &q in z {
        match ctl {
            Some(c) => b.cx(c, q),
            None => b.x(q),
        }
    }
    sub_small(b, ms, z, 4, ctl, C - 1, dirty);
}

/// z = a * y mod p into a zero register z (Horner, top bit of a first).
pub fn product(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    let n = a.len();
    for i in (0..n).rev() {
        if i != n - 1 {
            mod_double(b, ms, z, y);
        }
        ctrl_modadd(b, ms, z, y, a[i]);
    }
}

/// z += a * y mod p (any z), doubling y in place and restoring it; `a` must not overlap `y`.
pub fn mac(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &mut Vec<QubitId>) {
    for i in 0..256 {
        ctrl_modadd(b, ms, z, y, a[i]);
        if i != 255 {
            mod_double(b, ms, y, a);
        }
    }
    for _ in 0..255 {
        mod_halve(b, ms, y, a);
    }
}

/// Load a classical bit register into zero qubits (no Toffoli).
pub fn load_bits(b: &mut B, q: &[QubitId], bits: &[crate::circuit::BitId]) {
    for (&qq, &bb) in q.iter().zip(bits) {
        b.x_if(qq, bb);
    }
}
