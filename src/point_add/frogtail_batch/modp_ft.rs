//! Arithmetic modulo p = 2^256 - c (c = 2^32 + 977) for frogtail's product phase: frogdrop's ancilla-free adds and
//! overflow flag, plus a pool of clean qubits (the room under the walk's peak) for logical-AND carries (Gidney):
//! every fold of a constant (c on overflow, c - 1 for doubling / halving / negation) adds ctl * const over z's low 64
//! lanes with one AND per lane, the constant's bits taken straight from the control (credit gnuchev's carry pool);
//! a carry out of lane 63 is dropped (w.p. ~2^-32 per fold, as frogdrop's 32-lane headroom). The overflow flag's
//! erase compare runs on pool carries too.

use super::builder::B;
use crate::circuit::QubitId;

pub const C: u64 = (1u64 << 32) + 977;
/// fold register width (constant + carry headroom)
pub const RW: usize = 64;
/// Lanes compared when erasing an add's overflow flag (top lanes only; differs w.p. <= 2^-32).
pub const CMPT: usize = 32;

/// Scratch: overflow flag k and the carry pool (all |0> between operations).
pub struct Ms {
    pub k: QubitId,
    pub r: Vec<QubitId>,
}

impl Ms {
    pub fn alloc(b: &mut B) -> Ms {
        Ms {
            k: b.alloc(),
            r: b.alloc_n(RW),
        }
    }
    /// Pool as large as the room under `peak` allows (one qubit kept for modadd's constant control; at least RW
    /// lanes, at most 255).
    pub fn alloc_room(b: &mut B, peak: u64) -> Ms {
        let room = (peak.saturating_sub(b.live + 2) as usize).clamp(RW, 255);
        Ms {
            k: b.alloc(),
            r: b.alloc_n(room),
        }
    }
    pub fn release(self, b: &mut B) {
        b.free(self.k);
        b.free_n(&self.r);
    }
}

/// t += h * k mod 2^len (k constant: bit i adds into lane i; h one qubit outside t), logical-AND carries on `pool`
/// (>= len - 1 - lowest set bit of k), measurement-uncomputed. One AND per lane from k's lowest set bit up.
fn const_add_pool(b: &mut B, t: &[QubitId], h: QubitId, k: u64, pool: &[QubitId]) {
    let n = t.len();
    if k == 0 {
        return;
    }
    let i0 = k.trailing_zeros() as usize;
    let kb = |i: usize| i < 64 && (k >> i) & 1 == 1;
    // c[i] = carry into lane i (i0 < i < n) lives in pool[i - i0 - 1]
    let c = |i: usize| pool[i - i0 - 1];
    for i in i0..n - 1 {
        if i == i0 {
            b.and_c(t[i], h, c(i + 1));
        } else if kb(i) {
            b.cx(c(i), h);
            b.cx(c(i), t[i]);
            b.and_c(h, t[i], c(i + 1));
            b.cx(c(i), c(i + 1));
            b.cx(c(i), h);
        } else {
            b.and_c(t[i], c(i), c(i + 1));
        }
    }
    // top lane: sum only
    let top = n - 1;
    if top > i0 {
        b.cx(c(top), t[top]);
    }
    if kb(top) {
        b.cx(h, t[top]);
    }
    for i in (i0..n - 1).rev() {
        if i == i0 {
            b.and_u(t[i], h, c(i + 1));
            b.cx(h, t[i]);
        } else if kb(i) {
            b.cx(c(i), h);
            b.cx(c(i), c(i + 1));
            b.and_u(h, t[i], c(i + 1));
            b.cx(c(i), h);
            b.cx(h, t[i]);
        } else {
            b.and_u(t[i], c(i), c(i + 1));
            b.cx(c(i), t[i]);
        }
    }
}

/// k ^= ctl & carry_out(t + a) (carry-in 0), t and a restored, logical-AND carries on `pool` (>= n - 1).
fn carry_pool(b: &mut B, a: &[QubitId], t: &[QubitId], ctl: QubitId, k: QubitId, pool: &[QubitId]) {
    let n = t.len();
    // c[i] (carry into lane i, 1 <= i <= n): pool[i - 1]; carry out = c[n] in pool[n - 1]
    for i in 0..n {
        if i == 0 {
            b.and_c(a[0], t[0], pool[0]);
        } else {
            let ci = pool[i - 1];
            b.cx(ci, a[i]);
            b.cx(ci, t[i]);
            b.and_c(a[i], t[i], pool[i]);
            b.cx(ci, pool[i]);
        }
    }
    b.ccx(ctl, pool[n - 1], k);
    for i in (0..n).rev() {
        if i == 0 {
            b.and_u(a[0], t[0], pool[0]);
        } else {
            let ci = pool[i - 1];
            b.cx(ci, pool[i]);
            b.and_u(a[i], t[i], pool[i]);
            b.cx(ci, t[i]);
            b.cx(ci, a[i]);
        }
    }
}

/// t[lo..lo + RW) += ctl * (k >> lo) (k's low lo bits zero), carry out of the window dropped. ctl outside the window
/// (None: unconditional, the constant's lanes are X'd in place of the AND carries' source).
fn fold_add(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctl: Option<QubitId>, k: u64) {
    assert_eq!(k & ((1u64 << lo) - 1), 0);
    match ctl {
        Some(h) => const_add_pool(b, &t[lo..lo + RW], h, k >> lo, &ms.r),
        None => {
            let one = ms.r[RW - 1];
            b.x(one);
            const_add_pool(b, &t[lo..lo + RW], one, k >> lo, &ms.r[..RW - 1]);
            b.x(one);
        }
    }
}

/// t[lo..lo + RW) -= ctl * (k >> lo) as ~(~t + ctl k).
fn fold_sub(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctl: Option<QubitId>, k: u64) {
    for &q in &t[lo..lo + RW] {
        b.x(q);
    }
    fold_add(b, ms, t, lo, ctl, k);
    for &q in &t[lo..lo + RW] {
        b.x(q);
    }
}

/// z <- 2 z mod p in place (relabel z[0] <- old top bit h, then add h (c - 1); c - 1 is even so lane 0 keeps h).
pub fn mod_double(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>) {
    let top = z.pop().unwrap();
    z.insert(0, top);
    let h = z[0];
    fold_add(b, ms, z, 1, Some(h), C - 1);
}

/// Inverse of mod_double (z <- z / 2 mod p).
pub fn mod_halve(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>) {
    let h = z[0];
    fold_sub(b, ms, z, 1, Some(h), C - 1);
    let low = z.remove(0);
    z.push(low);
}

/// z += ctl y mod 2^n and k ^= ctl & carry_out (y restored). The low P lanes (P = pool size, < n) keep logical-AND
/// carries on the pool (2 Toffoli a lane: carry, controlled sum bit), the rest is a Cuccaro ladder whose carry-in is
/// the pool's top carry (3 a lane); the carry out is read between its two passes.
fn ctrl_add_flag(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId) {
    use super::arith::{down_m, up_m, Dm};
    let n = z.len();
    let pn = ms.r.len().min(n - 2);
    let c = &ms.r;
    // low part forward: c[i] = carry into lane i + 1 in pool[i]
    for i in 0..pn {
        if i == 0 {
            b.and_c(y[0], z[0], c[0]);
        } else {
            b.cx(c[i - 1], y[i]);
            b.cx(c[i - 1], z[i]);
            b.and_c(y[i], z[i], c[i]);
            b.cx(c[i - 1], c[i]);
        }
    }
    // high part: Cuccaro with carry-in c[pn - 1]
    let (th, sh) = (&z[pn..], &y[pn..]);
    let up = up_m(b, th, sh, c[pn - 1], false);
    let dn = down_m(b, th, sh, c[pn - 1], Dm::Cond(ctl), false);
    b.play(&up, false);
    b.ccx(ctl, sh[sh.len() - 1], ms.k);
    b.play(&dn, false);
    // low part backward: uncompute each carry by measurement, then the controlled sum bit
    for i in (0..pn).rev() {
        if i == 0 {
            b.and_u(y[0], z[0], c[0]);
            b.ccx(ctl, y[0], z[0]);
        } else {
            b.cx(c[i - 1], c[i]);
            b.and_u(y[i], z[i], c[i]);
            b.cx(c[i - 1], z[i]);
            b.ccx(ctl, y[i], z[i]);
            b.cx(c[i - 1], y[i]);
        }
    }
}

/// t += ctl a mod 2^n (a restored). The low lanes (as many as `pool` has, < n) keep logical-AND carries on the pool
/// (2 Toffoli a lane), the lanes above a Cuccaro ladder whose carry-in is the pool's top carry (3 a lane); the top
/// lane takes the sum bit only (1). No pool: Takahashi-Tani-Kunihiro.
pub fn ctrl_add_pool(b: &mut B, a: &[QubitId], t: &[QubitId], ctl: QubitId, pool: &[QubitId]) {
    use super::arith::{down_m, ttk_add, up_m, Dm};
    let n = t.len();
    assert!(n >= 2 && a.len() == n);
    let pn = pool.len().min(n - 1);
    if pn == 0 {
        ttk_add(b, a, t, Some(ctl), None);
        return;
    }
    let c = pool;
    for i in 0..pn {
        if i == 0 {
            b.and_c(a[0], t[0], c[0]);
        } else {
            b.cx(c[i - 1], a[i]);
            b.cx(c[i - 1], t[i]);
            b.and_c(a[i], t[i], c[i]);
            b.cx(c[i - 1], c[i]);
        }
    }
    // lanes pn..n-1: Cuccaro, the carry into the top lane ends in a[n - 2]
    let (th, sh) = (&t[pn..n - 1], &a[pn..n - 1]);
    if !th.is_empty() {
        let up = up_m(b, th, sh, c[pn - 1], false);
        b.play(&up, false);
    }
    let ct = if th.is_empty() { c[pn - 1] } else { a[n - 2] };
    b.cx(ct, a[n - 1]);
    b.ccx(ctl, a[n - 1], t[n - 1]);
    b.cx(ct, a[n - 1]);
    if !th.is_empty() {
        let dn = down_m(b, th, sh, c[pn - 1], Dm::Cond(ctl), false);
        b.play(&dn, false);
    }
    for i in (0..pn).rev() {
        if i == 0 {
            b.and_u(a[0], t[0], c[0]);
            b.ccx(ctl, a[0], t[0]);
        } else {
            b.cx(c[i - 1], c[i]);
            b.and_u(a[i], t[i], c[i]);
            b.cx(c[i - 1], t[i]);
            b.ccx(ctl, a[i], t[i]);
            b.cx(c[i - 1], a[i]);
        }
    }
}

/// z <- z + (ctl ? y : 0) mod p. `d` is one borrowed qubit (unused here; kept for the call shape).
pub fn ctrl_modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId, d: QubitId) {
    // z += ctl y mod 2^256, k = ctl & carry out
    ctrl_add_flag(b, ms, z, y, ctl);
    fold_add(b, ms, z, 0, Some(ms.k), C);
    // erase k = ctl & [z < y] = ctl & carry(~z_top + y_top) (top-lane compare; differs w.p. <= 2^-32)
    let zt = &z[256 - CMPT..];
    let yt = &y[256 - CMPT..];
    let _ = d;
    for &q in zt {
        b.x(q);
    }
    b.carry_erase(yt, zt, ctl, ms.k, &ms.r);
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
pub fn ctrl_neg(b: &mut B, ms: &Ms, z: &[QubitId], ctl: Option<QubitId>) {
    for &q in z {
        match ctl {
            Some(c) => b.cx(c, q),
            None => b.x(q),
        }
    }
    fold_sub(b, ms, z, 1, ctl, C - 1);
}

/// z = a * y mod p into a zero register z (Horner, top bit of a first).
pub fn product(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    let n = a.len();
    for i in (0..n).rev() {
        if i != n - 1 {
            mod_double(b, ms, z);
        }
        ctrl_modadd(b, ms, z, y, a[i], a[(i + 1) % n]);
    }
}

/// z += a * y mod p (any z), doubling y in place and restoring it; `a` must not overlap `y`.
pub fn mac(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &mut Vec<QubitId>) {
    for i in 0..256 {
        ctrl_modadd(b, ms, z, y, a[i], a[(i + 1) % 256]);
        if i != 255 {
            mod_double(b, ms, y);
        }
    }
    for _ in 0..255 {
        mod_halve(b, ms, y);
    }
}

/// z = y * C * 2^-tt mod p into a zero register z (relabeled in place by the halvings), C = two's complement value of
/// `c` (LSB first, top lane weighs -2^(M-1)), y in [0, p) restored. Bottom-up halving Horner over C's lanes, then
/// tt - M more halvings.
pub fn product_tail(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
) {
    let m = c.len();
    assert!(tt >= m);
    for k in 0..m {
        let d = c[(k + 1) % m];
        if k + 1 < m {
            ctrl_modadd(b, ms, z, y, c[k], d);
        } else {
            b.begin();
            ctrl_modadd(b, ms, z, y, c[k], d);
            let r = b.end();
            b.play(&r, true);
        }
        mod_halve(b, ms, z);
    }
    for _ in m..tt {
        mod_halve(b, ms, z);
    }
}
