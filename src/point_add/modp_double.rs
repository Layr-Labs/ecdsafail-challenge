//! Arithmetic modulo p = 2^256 - c (secp256k1, c = 2^32 + 977) for froghop-double, with a lean fold.
//!
//! Every reduction folds an overflow back in as + c (2^256 = c mod p): a constant add over the constant's lanes
//! (clean operand lanes) whose carry then runs through HC more clean lanes and HD lanes incremented with BORROWED
//! dirty qubits (x -= g; g = ~g; x -= g; g = ~g is x + 1 for any g, Gidney's trick), truncated after HC + HD = 32
//! lanes (a carry survives that far w.p. 2^-33 per fold). The dirty lanes cost 4 Toffoli per lane instead of 2
//! but no clean qubits, which keeps the product phases under the traversal's peak.

use super::arith::{down_m, up_m, Dm};
use super::builder::B;
use crate::circuit::QubitId;

pub const C: u64 = (1u64 << 32) + 977;
/// operand lanes of the largest folded constant (c: 33 bits)
pub const CONSTL: usize = 33;
/// clean carry-headroom lanes after the constant
pub const HC: usize = 23;
/// dirty-incremented carry-headroom lanes after those (HC + HD = 32)
pub const HD: usize = 32 - HC;
/// Lanes compared when erasing an add's overflow flag (top lanes only; differs w.p. <= 2^-32).
pub const CMPT: usize = 32;

/// Scratch: carry-in qubit, constant + clean headroom lanes, overflow flag, carry-in of the dirty incrementer.
pub struct Ms {
    pub c0: QubitId,
    pub s: Vec<QubitId>,
    pub k: QubitId,
    pub c1: QubitId,
}

impl Ms {
    pub fn alloc(b: &mut B) -> Ms {
        let c0 = b.alloc();
        let s = b.alloc_n(CONSTL + HC);
        let k = b.alloc();
        let c1 = b.alloc();
        Ms { c0, s, k, c1 }
    }
    pub fn release(self, b: &mut B) {
        b.free(self.c0);
        b.free_n(&self.s);
        b.free(self.k);
        b.free(self.c1);
    }
}

/// x (LSB first) += 1 mod 2^n using n borrowed qubits g (any state, restored) and one clean c1.
fn inc_dirty(b: &mut B, x: &[QubitId], g: &[QubitId], c1: QubitId) {
    let n = x.len();
    let g = &g[..n];
    for pass in 0..2 {
        // x -= g
        let u = up_m(b, x, g, c1, true);
        let d = down_m(b, x, g, c1, Dm::Sum, true);
        b.play(&u, false);
        b.play(&d, false);
        let _ = pass;
        for &q in g {
            b.x(q);
        }
    }
}

/// t[lo..) += (ctrl ? k : 0) (ctrl None: unconditional) for a classical k < 2^33, carry truncated 32 lanes past
/// the constant. `dirty`: >= HD + 1 qubits disjoint from t, ctrl and the scratch.
pub(crate) fn add_small(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId]) {
    let kk = k >> lo;
    assert_eq!(kk << lo, k);
    let l = (64 - kk.leading_zeros()) as usize;
    let nc = l + HC;
    assert!(lo + nc + HD <= t.len() && l <= CONSTL);
    let bs: Vec<usize> = (0..l).filter(|&j| (kk >> j) & 1 == 1).collect();
    let load = |b: &mut B| {
        for &j in &bs {
            match ctrl {
                Some(c) => b.cx(c, ms.s[j]),
                None => b.x(ms.s[j]),
            }
        }
    };
    load(b);
    let tt = &t[lo..lo + nc];
    let ss = &ms.s[..nc];
    let u = up_m(b, tt, ss, ms.c0, false);
    let d = down_m(b, tt, ss, ms.c0, Dm::Sum, false);
    b.play(&u, false);
    // carry out of the clean part sits on ss[nc - 1]: increment the next HD lanes by it, (carry, lanes) + 1
    // then flip the carry wire back
    if HD > 0 {
        let mut xr = vec![ss[nc - 1]];
        xr.extend(&t[lo + nc..lo + nc + HD]);
        inc_dirty(b, &xr, dirty, ms.c1);
        b.x(ss[nc - 1]);
    }
    b.play(&d, false);
    load(b);
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
    for i in (0..256).rev() {
        if i != 255 {
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
