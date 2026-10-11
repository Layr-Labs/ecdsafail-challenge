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

thread_local! {
    /// Force the hybrid (Gidney low lanes + Cuccaro) ladder: for recordings that are later played inverted, where a
    /// chunked ladder's measured carry erases would become coherent compares.
    pub static NOCHUNK: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Scratch: overflow flag k, the carry pool (all |0> between operations) and a constant |1> control.
pub struct Ms {
    pub k: QubitId,
    pub r: Vec<QubitId>,
    pub one: QubitId,
}

impl Ms {
    fn with(b: &mut B, room: usize) -> Ms {
        let k = b.alloc();
        let r = b.alloc_n(room);
        let one = b.alloc();
        b.x(one);
        Ms { k, r, one }
    }
    pub fn alloc(b: &mut B) -> Ms {
        Ms::with(b, RW)
    }
    /// Pool as large as the room under `peak` allows (one qubit kept for the constant control; at least RW
    /// lanes, at most 256).
    pub fn alloc_room(b: &mut B, peak: u64) -> Ms {
        let room = (peak.saturating_sub(b.live + 2) as usize).clamp(RW, 256);
        Ms::with(b, room)
    }
    pub fn release(self, b: &mut B) {
        b.x(self.one);
        b.free(self.one);
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
    if super::chunked::try_add(b, y, z, ctl, Some(ms.k), &ms.r) {
        return;
    }
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
    if super::chunked::try_add(b, a, t, ctl, None, pool) {
        return;
    }
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

/// add_flag_u with the low P lanes on pool carries (1 Toffoli a lane) and a Cuccaro ladder (2 a lane) above, whose
/// carry-in is the pool's top carry; the carry out is copied out between its two passes.
fn add_flag_u_hybrid(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    use super::arith::{down_m, up_m, Dm};
    let n = z.len();
    let pn = ms.r.len().min(n - 2);
    let c = &ms.r;
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
    let (th, sh) = (&z[pn..], &y[pn..]);
    let up = up_m(b, th, sh, c[pn - 1], false);
    let dn = down_m(b, th, sh, c[pn - 1], Dm::Sum, false);
    b.play(&up, false);
    b.cx(sh[sh.len() - 1], ms.k);
    b.play(&dn, false);
    for i in (0..pn).rev() {
        if i == 0 {
            b.and_u(y[0], z[0], c[0]);
            b.cx(y[0], z[0]);
        } else {
            b.cx(c[i - 1], c[i]);
            b.and_u(y[i], z[i], c[i]);
            b.cx(c[i - 1], z[i]);
            b.cx(y[i], z[i]);
            b.cx(c[i - 1], y[i]);
        }
    }
}

/// z += y mod 2^n and k ^= carry_out (y restored), uncontrolled, every lane a logical-AND carry (1 Toffoli). With a
/// pool shorter than n - 2 the ladder runs in chunks of at most P - j - 1 lanes (j = chunk index): each chunk's sums
/// are written at once and its carry out is held on a reserved pool lane as the next chunk's carry-in; after the
/// last chunk the held carries are erased top-down by X measurement, with the exact compare [z' < y + carry-in]
/// over their chunk as the phase oracle under the measured bit (half the chunk's ANDs on average).
fn add_flag_u(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    let n = z.len();
    let p = ms.r.len();
    // fewest chunks: chunk j < nch - 1 takes at most p - j - 1 lanes (j held carries plus its own carry out live
    // during its erase), the last at most p - nch + 1; the last is made maximal so that the erased chunks (half
    // their lanes on average) are as short as possible
    let mut nch = 1;
    while (0..nch - 1).map(|j| p - j - 1).sum::<usize>() + (p - (nch - 1)) < n {
        nch += 1;
    }
    let mut rest = n - (p - (nch - 1)).min(n);
    let mut bounds = vec![0usize];
    for j in 0..nch - 1 {
        let l = rest.min(p - j - 1);
        assert!(l > 0);
        bounds.push(bounds[j] + l);
        rest -= l;
    }
    bounds.push(n);
    // average Toffoli: chunked n + sum of half the erased chunks; hybrid (Gidney low lanes, Cuccaro rest) 2n - pn
    let chunked2 = 2 * n + (bounds[nch - 1] - bounds[0]);
    let pn = p.min(n - 2);
    if NOCHUNK.with(|c| c.get()) || 2 * (2 * n - pn) <= chunked2 {
        return add_flag_u_hybrid(b, ms, z, y);
    }
    let h = |j: usize| ms.r[p - j];
    for ch in 0..nch {
        let (lo, hi) = (bounds[ch], bounds[ch + 1]);
        let last = ch + 1 == nch;
        let cin = if ch == 0 { None } else { Some(h(ch)) };
        // carry into lane i (lo < i <= hi)
        let cr = |i: usize| if i == hi && !last { h(ch + 1) } else { ms.r[i - lo - 1] };
        let ci = |i: usize| if i == lo { cin } else { Some(cr(i)) };
        for i in lo..hi {
            match ci(i) {
                None => b.and_c(y[i], z[i], cr(i + 1)),
                Some(c) => {
                    b.cx(c, y[i]);
                    b.cx(c, z[i]);
                    b.and_c(y[i], z[i], cr(i + 1));
                    b.cx(c, cr(i + 1));
                }
            }
        }
        if last {
            b.cx(cr(n), ms.k);
        }
        for i in (lo..hi).rev() {
            let keep = i + 1 == hi && !last;
            match ci(i) {
                None => {
                    if !keep {
                        b.and_u(y[i], z[i], cr(i + 1));
                    }
                    b.cx(y[i], z[i]);
                }
                Some(c) => {
                    if !keep {
                        b.cx(c, cr(i + 1));
                        b.and_u(y[i], z[i], cr(i + 1));
                    }
                    b.cx(c, z[i]);
                    b.cx(y[i], z[i]);
                    b.cx(c, y[i]);
                }
            }
        }
    }
    for ch in (1..nch).rev() {
        let (lo, hi) = (bounds[ch - 1], bounds[ch]);
        let cin = if ch == 1 { None } else { Some(h(ch - 1)) };
        for &q in &z[lo..hi] {
            b.x(q);
        }
        b.carry_erase_cin(&y[lo..hi], &z[lo..hi], ms.one, h(ch), &ms.r[..hi - lo], cin);
        for &q in &z[lo..hi] {
            b.x(q);
        }
    }
}

/// z <- z + (-1)^s y mod p; `s` (a qubit outside z and y) subtracts where it is 1 (None: add). No quantum control
/// on the ladder: a subtraction runs as ~(~z + y). In the complemented domain w the overflow k of ~z + y folds +c as
/// for an add (~(~z + y - 2^256 + c) = z - y + p), and k = [w < y + s c] exactly; the 32-lane erase compares
/// w_top < y_top + s, so ties (z near 0 when subtracting) count as a borrow and the approximation misses only for z
/// within 2^-32 p of p (as an add's for z near p).
pub fn signed_modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], s: Option<QubitId>) {
    let flip = |b: &mut B| {
        if let Some(q) = s {
            for &l in z {
                b.cx(q, l);
            }
        }
    };
    flip(b);
    add_flag_u(b, ms, z, y);
    fold_add(b, ms, z, 0, Some(ms.k), C);
    let zt = &z[256 - CMPT..];
    let yt = &y[256 - CMPT..];
    for &q in zt {
        b.x(q);
    }
    b.carry_erase_cin(yt, zt, ms.one, ms.k, &ms.r, s);
    for &q in zt {
        b.x(q);
    }
    flip(b);
}

/// t += sext(a) mod 2^|t| (a two's complement, |a| <= |t|, a restored), uncontrolled: logical-AND carries on `pool`
/// (>= |t| - 1). The lanes above a take carry - sign as ~(~u + (carry ^ sign)) (complemented where the sign is set).
pub fn add_sext(b: &mut B, a: &[QubitId], t: &[QubitId], pool: &[QubitId]) {
    let (la, lt) = (a.len(), t.len());
    assert!(la >= 2 && lt >= la && pool.len() + 1 >= lt);
    let c = pool;
    let u = &t[la..];
    let sg = a[la - 1];
    for &q in u {
        b.cx(sg, q);
    }
    for i in 0..la {
        if i == 0 {
            b.and_c(a[0], t[0], c[0]);
        } else if i + 1 < la || !u.is_empty() {
            b.cx(c[i - 1], a[i]);
            b.cx(c[i - 1], t[i]);
            b.and_c(a[i], t[i], c[i]);
            b.cx(c[i - 1], c[i]);
        }
    }
    if !u.is_empty() {
        // carry-in of u: c[la - 1] ^ sign (sign = a[la - 1] ^ c[la - 2] here)
        let d = c[la - 1];
        b.cx(a[la - 1], d);
        b.cx(c[la - 2], d);
        let e = |j: usize| if j == 0 { d } else { c[la - 1 + j] };
        for j in 0..u.len() - 1 {
            b.and_c(u[j], e(j), e(j + 1));
        }
        for j in (0..u.len()).rev() {
            if j + 1 < u.len() {
                b.and_u(u[j], e(j), e(j + 1));
            }
            b.cx(e(j), u[j]);
        }
        b.cx(c[la - 2], d);
        b.cx(a[la - 1], d);
    }
    for i in (0..la).rev() {
        if i == 0 {
            b.and_u(a[0], t[0], c[0]);
            b.cx(a[0], t[0]);
        } else if i + 1 < la || !u.is_empty() {
            b.cx(c[i - 1], c[i]);
            b.and_u(a[i], t[i], c[i]);
            b.cx(c[i - 1], t[i]);
            b.cx(a[i], t[i]);
            b.cx(c[i - 1], a[i]);
        } else {
            // top lane, no carry out kept: sum only
            b.cx(c[i - 1], t[i]);
            b.cx(a[i], t[i]);
        }
    }
    for &q in u {
        b.cx(sg, q);
    }
}

/// t -= sext(a) mod 2^|t| as ~(~t + sext(a)).
pub fn sub_sext(b: &mut B, a: &[QubitId], t: &[QubitId], pool: &[QubitId]) {
    for &q in t {
        b.x(q);
    }
    add_sext(b, a, t, pool);
    for &q in t {
        b.x(q);
    }
}

/// C_T on `r` (two's complement: lo = r[0..256) unsigned, hi = r[256..) signed) -> lo' = lo + hi c, hi kept, so lo'
/// = C_T (mod p) as a 256-lane unsigned multiplier. lo' leaves [0, 2^256) only if lo is within |hi c| < 2^94 of either
/// end (~2^-160). `tq` (72 clean lanes) holds hi * 977 meanwhile.
pub fn reduce_hi(b: &mut B, r: &[QubitId], tq: &[QubitId], pool: &[QubitId]) {
    let (lo, hi) = (&r[..256], &r[256..]);
    let h = hi.len();
    assert!(h <= 62 && tq.len() == 72);
    add_sext(b, hi, &lo[32..], pool);
    b.begin();
    for j in 0..72 {
        b.cx(hi[j.min(h - 1)], tq[j]);
    }
    add_sext(b, hi, &tq[10..], pool);
    sub_sext(b, hi, &tq[5..], pool);
    sub_sext(b, hi, &tq[4..], pool);
    let r977 = b.end();
    b.play(&r977, false);
    add_sext(b, tq, lo, pool);
    b.play(&r977, true);
}

/// z <- z - ctl y mod p (inverse of ctrl_modadd).
pub fn ctrl_modsub(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId) {
    b.begin();
    ctrl_modadd(b, ms, z, y, ctl, ctl);
    let r = b.end();
    b.play(&r, true);
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
    signed_modadd(b, ms, z, y, None);
    let _ = d;
}

pub fn modsub(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], d: QubitId) {
    signed_modadd(b, ms, z, y, Some(ms.one));
    let _ = d;
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

/// z = a * y mod p into a zero register z: signed-digit Horner, top digit first. For n-bit a,
/// a = 2^(n-1) + sum_{k<n-1} (2 a_{k+1} - 1) 2^k - (1 - a_0): every step adds or subtracts y with no control on the
/// ladder, and one controlled subtraction fixes a_0. `a` must not overlap `y`.
pub fn product(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    let n = a.len();
    for i in 0..256 {
        b.cx(y[i], z[i]);
    }
    for k in (0..n - 1).rev() {
        mod_double(b, ms, z);
        b.x(a[k + 1]);
        signed_modadd(b, ms, z, y, Some(a[k + 1]));
        b.x(a[k + 1]);
    }
    b.x(a[0]);
    ctrl_modsub(b, ms, z, y, a[0]);
    b.x(a[0]);
}

/// Inverse of `product` (z = a y -> 0) built from forward operations, so its measured erases stay measured.
pub fn product_inv(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    let n = a.len();
    b.x(a[0]);
    ctrl_modadd(b, ms, z, y, a[0], a[0]);
    b.x(a[0]);
    for k in 0..n - 1 {
        signed_modadd(b, ms, z, y, Some(a[k + 1]));
        mod_halve(b, ms, z);
    }
    for i in 0..256 {
        b.cx(y[i], z[i]);
    }
}

/// z += y^2 mod p (any z), y restored: z is halved n - 1 times, then the signed-digit Horner of `product` runs on
/// z with y's own lanes as the digit signs. `tmp` is a clean qubit (holds !y_0 for the a_0 fix).
pub fn square_acc(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], tmp: QubitId) {
    let n = y.len();
    for _ in 0..n - 1 {
        mod_halve(b, ms, z);
    }
    signed_modadd(b, ms, z, y, None);
    for k in (0..n - 1).rev() {
        mod_double(b, ms, z);
        b.cx(y[k + 1], tmp);
        b.x(tmp);
        signed_modadd(b, ms, z, y, Some(tmp));
        b.x(tmp);
        b.cx(y[k + 1], tmp);
    }
    b.cx(y[0], tmp);
    b.x(tmp);
    ctrl_modsub(b, ms, z, y, tmp);
    b.x(tmp);
    b.cx(y[0], tmp);
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

/// z = -y * C * 2^-tt mod p into a zero register z (relabeled in place by the halvings), C = two's complement value
/// of `c` (LSB first, top lane weighs -2^(M-1)), y in [1, p) restored. Bottom-up halving Horner over signed digits:
/// -C = sum_{k<M-1} (1 - 2 c_{k+1}) 2^k + (2 c_{M-1} - 1) 2^(M-1) + (1 - c_0), so z starts at (1 - c_0) y and every
/// step adds or subtracts y with no control on the ladder; then tt - M more halvings. (Accumulating -C, the partial
/// sums reach 0 only by a subtraction y - y, which lands on the canonical 0; with +C an addition (p - y) + y would
/// leave the non-canonical p.)
pub fn product_tail_neg(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
) {
    product_tail_neg_s(b, ms, z, c, y, tt, true);
}

/// product_tail_neg for a two's complement (`signed`) or unsigned C (top digit -1: -C = sum_{k<M-1} (1 - 2 c_{k+1})
/// 2^k - 2^(M-1) + (1 - c_0)).
pub fn product_tail_neg_s(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
    signed: bool,
) {
    let m = c.len();
    assert!(tt >= m);
    b.x(c[0]);
    for i in 0..256 {
        b.and_c(c[0], y[i], z[i]);
    }
    b.x(c[0]);
    for k in 0..m {
        if k + 1 < m {
            signed_modadd(b, ms, z, y, Some(c[k + 1]));
        } else if signed {
            b.x(c[m - 1]);
            signed_modadd(b, ms, z, y, Some(c[m - 1]));
            b.x(c[m - 1]);
        } else {
            signed_modadd(b, ms, z, y, Some(ms.one));
        }
        mod_halve(b, ms, z);
    }
    for _ in m..tt {
        mod_halve(b, ms, z);
    }
}

/// z = y * C * 2^-tt mod p (product_tail_neg, then a negation).
pub fn product_tail(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
) {
    product_tail_neg(b, ms, z, c, y, tt);
    ctrl_neg(b, ms, z, None);
}
