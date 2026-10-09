//! Arithmetic modulo p = 2^256 - c (secp256k1, c = 2^32 + 977) for frogdrop, with one clean scratch qubit.
//!
//! Every reduction folds an overflow back in as + c (2^256 = c mod p). Adds use the ancilla-free ripple
//! (`arith::ttk_add`), so the only clean scratch is the overflow flag k. The fold adds c as signed-digit (NAF)
//! controlled increments that BORROW dirty qubits (x -= g; g = ~g; x -= g; g = ~g is x + 1 for any g, Gidney's
//! trick, with ancilla-free subtractions); each increment drops a carry past its 32 headroom lanes w.p. ~2^-32.

use super::arith::{down_m, ttk_add, ttk_carry, up_m, Dm};
use super::builder::B;
use crate::circuit::QubitId;

pub const C: u64 = (1u64 << 32) + 977;
/// carry headroom of each borrowed increment
pub const HEAD: usize = 32;
/// Lanes compared when erasing an add's overflow flag (top lanes only; differs w.p. <= 2^-32).
pub const CMPT: usize = 32;

/// Scratch: the overflow flag k (|0> between operations).
pub struct Ms {
    pub k: QubitId,
}

impl Ms {
    pub fn alloc(b: &mut B) -> Ms {
        Ms { k: b.alloc() }
    }
    pub fn release(self, b: &mut B) {
        b.free(self.k);
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

/// x (LSB first) += 1 mod 2^n using n borrowed qubits g (any state, restored), no clean qubit.
pub(crate) fn inc_dirty_free(b: &mut B, x: &[QubitId], g: &[QubitId]) {
    let n = x.len();
    let g = &g[..n];
    if n == 1 {
        b.x(x[0]);
        return;
    }
    for _ in 0..2 {
        // x -= g as ~(~x + g)
        for &q in x {
            b.x(q);
        }
        ttk_add(b, g, x, None, None);
        for &q in x {
            b.x(q);
        }
        for &q in g {
            b.x(q);
        }
    }
}

/// t += (ctrl ? k : 0) (ctrl None: unconditional) for k = 2^32 + (low << lo), low < 2^32 (c or c - 1).
pub(crate) fn add_small(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId]) {
    assert!(k >> 33 == 0 && lo < 32);
    add_small_lean(b, ms, t, lo, ctrl, k, dirty);
}

/// add_small without constant lanes: t += ctrl * k as signed-digit (NAF) controlled increments / decrements of
/// t[j .. 32 + HEAD) on borrowed lanes (`dirty` >= 33 + HEAD - lo qubits disjoint from t and ctrl).
fn add_small_lean(b: &mut B, _ms: &Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId]) {
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
                inc_dirty_free(b, &xr, dirty);
                b.x(c);
            }
            None => inc_dirty_free(b, &t[j..end], dirty),
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

/// z <- z + (ctl ? y : 0) mod p (y is restored before the fold and lends its qubits as the dirty lanes). `d` is one
/// more borrowed qubit (any state, restored; not in z, y, ctl or the scratch).
pub fn ctrl_modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId, d: QubitId) {
    // z += ctl y mod 2^256, k = ctl & carry out
    ttk_add(b, y, z, Some(ctl), Some((ms.k, d)));
    add_small(b, ms, z, 0, Some(ms.k), C, y);
    // erase k = ctl & [z < y] = ctl & carry(~z_top + y_top) (top-lane compare; differs w.p. <= 2^-32)
    let zt = &z[256 - CMPT..];
    let yt = &y[256 - CMPT..];
    for &q in zt {
        b.x(q);
    }
    ttk_carry(b, yt, zt, ctl, ms.k, d);
    for &q in zt {
        b.x(q);
    }
}

pub fn modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], d: QubitId) {
    let one = b.alloc();
    b.x(one);
    ctrl_modadd(b, ms, z, y, one, d);
    b.x(one);
    b.free(one);
}
pub fn modsub(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], d: QubitId) {
    let one = b.alloc();
    b.x(one);
    b.begin();
    ctrl_modadd(b, ms, z, y, one, d);
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
        ctrl_modadd(b, ms, z, y, a[i], a[(i + 1) % n]);
    }
}

/// z += a * y mod p (any z), doubling y in place and restoring it; `a` must not overlap `y`.
pub fn mac(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &mut Vec<QubitId>) {
    for i in 0..256 {
        ctrl_modadd(b, ms, z, y, a[i], a[(i + 1) % 256]);
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
