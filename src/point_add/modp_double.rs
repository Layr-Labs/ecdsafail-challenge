//! Arithmetic modulo p = 2^256 - c (secp256k1, c = 2^32 + 977) for froghop-double, with a carry pool.
//!
//! Every reduction folds an overflow back in as + c (2^256 = c mod p): a constant add over the constant's lanes and
//! 32 lanes of carry headroom after it (truncated there: a carry survives that far w.p. 2^-33 per fold).
//!
//! Carries: the products run below the traversal's peak, so every routine takes the clean qubits up to that peak
//! (`super::PEAK`) as a carry pool `Ms::g`. A lane whose carry sits in the pool is a logical-AND carry (one Toffoli
//! to compute, uncomputed by an X-basis measurement and a classically controlled CZ); lanes beyond the pool keep the
//! in-place ripple (carry stored in the addend lane). Truncation points and compares are those of the dirty-lane
//! fold this replaces, so every routine computes the same function. When the pool is shorter than a constant add's
//! carry chain, the lanes past the pool are incremented by the pool's last carry with borrowed (dirty) qubits.

use super::arith::{down_m, up_m, Dm};
use super::builder::B;
use crate::circuit::QubitId;

pub const C: u64 = (1u64 << 32) + 977;
/// carry-headroom lanes after the folded constant
pub const HEAD: usize = 32;
/// Lanes compared when erasing an add's overflow flag (top lanes only; differs w.p. <= 2^-32).
pub const CMPT: usize = 32;
/// Carry-pool lanes for a full-pool constant add (a 33 + 32 lane chain).
pub const GMIN: usize = 33 + HEAD - 1;
/// Carry-pool lanes needed at least: the constant's own lanes (the head past them may go to the dirty increment).
pub const GLOW: usize = 34;

/// Scratch: carry-in qubit, overflow flag, a |1> qubit, and the carry pool (|0> between calls).
pub struct Ms {
    pub c0: QubitId,
    pub k: QubitId,
    pub one: QubitId,
    pub g: Vec<QubitId>,
}

impl Ms {
    /// Allocate the scratch and fill the carry pool up to `super::PEAK` live qubits (at most 256 pool lanes).
    /// Allocate every other register of the phase first.
    pub fn alloc(b: &mut B) -> Ms {
        let room = super::PEAK.saturating_sub(b.live + 3) as usize;
        Ms::alloc_pool(b, room.min(256))
    }
    /// Scratch with a carry pool of exactly `ng` lanes.
    pub fn alloc_pool(b: &mut B, ng: usize) -> Ms {
        let c0 = b.alloc();
        let k = b.alloc();
        let one = b.alloc();
        b.x(one);
        assert!(ng >= GLOW, "carry pool {} < {} (live {})", ng, GLOW, b.live);
        let g = b.alloc_n(ng);
        Ms { c0, k, one, g }
    }
    pub fn release(self, b: &mut B) {
        b.x(self.one);
        b.free(self.c0);
        b.free(self.k);
        b.free(self.one);
        b.free_n(&self.g);
    }
}

/// t[0..n) += a (mod 2^n), with a_i = Some(q) (q may be shared between lanes; it is restored) or None (0).
/// Logical-AND carries in g (at most n - 1 lanes, all |0> before and after). 1 Toffoli per nonzero carry.
pub fn gadd(b: &mut B, t: &[QubitId], a: &[Option<QubitId>], g: &[QubitId]) {
    let n = t.len();
    assert_eq!(a.len(), n);
    let mut carry: Vec<Option<QubitId>> = vec![None; n];
    let mut gi = 0;
    for i in 0..n.saturating_sub(1) {
        carry[i + 1] = match (a[i], carry[i]) {
            (None, None) => None,
            (Some(q), None) => {
                b.and_c(t[i], q, g[gi]);
                gi += 1;
                Some(g[gi - 1])
            }
            (None, Some(c)) => {
                b.and_c(t[i], c, g[gi]);
                gi += 1;
                Some(g[gi - 1])
            }
            (Some(q), Some(c)) => {
                // MAJ(t, q, c) = c ^ (t ^ c)(q ^ c); t keeps t ^ c until the return pass
                b.cx(c, t[i]);
                b.cx(c, q);
                b.and_c(t[i], q, g[gi]);
                b.cx(c, q);
                b.cx(c, g[gi]);
                gi += 1;
                Some(g[gi - 1])
            }
        };
    }
    for i in (0..n).rev() {
        if i + 1 < n {
            if let Some(gq) = carry[i + 1] {
                match (a[i], carry[i]) {
                    (Some(q), None) => b.and_u(t[i], q, gq),
                    (None, Some(c)) => b.and_u(t[i], c, gq),
                    (Some(q), Some(c)) => {
                        b.cx(c, gq);
                        b.cx(c, q);
                        b.and_u(t[i], q, gq);
                        b.cx(c, q);
                    }
                    (None, None) => unreachable!(),
                }
            }
        }
        match (a[i], carry[i]) {
            (None, None) => {}
            (Some(q), None) => b.cx(q, t[i]),
            (None, Some(c)) => b.cx(c, t[i]),
            (Some(q), Some(c)) => {
                if i + 1 == n {
                    b.cx(c, t[i]);
                }
                b.cx(q, t[i]);
            }
        }
    }
}

/// x += 1 mod 2^n with borrowed qubits g (any state, restored): x -= g, g = ~g, x -= g, g = ~g (x - g - ~g = x + 1).
/// c1 must be |0> (carry-in of the ripples).
fn inc_dirty(b: &mut B, x: &[QubitId], g: &[QubitId], c1: QubitId) {
    let n = x.len();
    let g = &g[..n];
    for _ in 0..2 {
        let u = up_m(b, x, g, c1, true);
        let d = down_m(b, x, g, c1, Dm::Sum, true);
        b.play(&u, false);
        b.play(&d, false);
        for &q in g {
            b.x(q);
        }
    }
}

/// gadd with a carry pool of s < n - 1 lanes: lanes [0, s) as in gadd (carries c_1 .. c_s in g), lanes [s, n) must
/// have no addend (a_i = None) and are incremented by c_s with the borrowed qubits `dirty` (n - s + 1 of them, any
/// state, restored; c1 |0>). Same function as gadd (mod 2^n).
fn gadd_split(b: &mut B, t: &[QubitId], a: &[Option<QubitId>], g: &[QubitId], s: usize, dirty: &[QubitId], c1: QubitId) {
    let n = t.len();
    assert!(s >= 1 && s < n && s <= g.len());
    assert!(a[s..].iter().all(|x| x.is_none()));
    assert!(dirty.len() >= n - s + 1, "dirty lanes {} < {}", dirty.len(), n - s + 1);
    let mut carry: Vec<Option<QubitId>> = vec![None; s + 1];
    let mut gi = 0;
    for i in 0..s {
        carry[i + 1] = match (a[i], carry[i]) {
            (None, None) => None,
            (Some(q), None) => {
                b.and_c(t[i], q, g[gi]);
                gi += 1;
                Some(g[gi - 1])
            }
            (None, Some(c)) => {
                b.and_c(t[i], c, g[gi]);
                gi += 1;
                Some(g[gi - 1])
            }
            (Some(q), Some(c)) => {
                b.cx(c, t[i]);
                b.cx(c, q);
                b.and_c(t[i], q, g[gi]);
                b.cx(c, q);
                b.cx(c, g[gi]);
                gi += 1;
                Some(g[gi - 1])
            }
        };
    }
    // lanes [s, n) += c_s: (c_s, t[s..n)) + 1, then flip c_s back
    if let Some(cs) = carry[s] {
        let mut xr = vec![cs];
        xr.extend(&t[s..n]);
        inc_dirty(b, &xr, dirty, c1);
        b.x(cs);
    }
    for i in (0..s).rev() {
        if let Some(gq) = carry[i + 1] {
            match (a[i], carry[i]) {
                (Some(q), None) => b.and_u(t[i], q, gq),
                (None, Some(c)) => b.and_u(t[i], c, gq),
                (Some(q), Some(c)) => {
                    b.cx(c, gq);
                    b.cx(c, q);
                    b.and_u(t[i], q, gq);
                    b.cx(c, q);
                }
                (None, None) => unreachable!(),
            }
        }
        match (a[i], carry[i]) {
            (None, None) => {}
            (Some(q), None) => b.cx(q, t[i]),
            (None, Some(c)) => b.cx(c, t[i]),
            (Some(q), Some(_)) => b.cx(q, t[i]),
        }
    }
}

/// t[lo..lo + l + HEAD) += (ctrl ? k : 0) (ctrl None: unconditional) for a classical k < 2^33 with k >> lo of bit
/// length l; the carry is truncated HEAD lanes past the constant. `dirty` (disjoint from t, ctrl and the scratch)
/// is borrowed only when the carry pool is shorter than the chain.
pub(crate) fn add_small(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId]) {
    let kk = k >> lo;
    assert_eq!(kk << lo, k);
    let l = (64 - kk.leading_zeros()) as usize;
    let n = l + HEAD;
    assert!(lo + n <= t.len());
    let c = ctrl.unwrap_or(ms.one);
    let a: Vec<Option<QubitId>> = (0..n).map(|j| if j < 64 && (kk >> j) & 1 == 1 { Some(c) } else { None }).collect();
    if ms.g.len() >= n - 1 {
        gadd(b, &t[lo..lo + n], &a, &ms.g);
    } else {
        gadd_split(b, &t[lo..lo + n], &a, &ms.g, ms.g.len(), dirty, ms.c0);
    }
}

fn sub_small(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId]) {
    b.begin();
    add_small(b, ms, t, lo, ctrl, k, dirty);
    let r = b.end();
    b.play(&r, true);
}

/// z += (ctl ? y : 0) (ctl = None: unconditional) over 256 lanes, and k ^= (ctl &) carry-out of z + y.
/// Lanes [0, l) ripple in place (carry in y's lane, carry-in c0), lanes [l, 256) take logical-AND carries from
/// the pool, l = 256 - min(pool, 256).
fn add_cout(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: Option<QubitId>) {
    let n = z.len();
    assert_eq!(y.len(), n);
    let na = ms.g.len().min(n);
    let l = n - na;
    let g = &ms.g[..na];
    let (zl, yl) = (&z[..l], &y[..l]);
    if l > 0 {
        let r = up_m(b, zl, yl, ms.c0, false);
        b.play(&r, false);
    }
    let cin = |i: usize| -> Option<QubitId> {
        if i == 0 {
            None
        } else if i == l {
            Some(y[l - 1])
        } else {
            Some(g[i - 1 - l])
        }
    };
    for i in l..n {
        let gq = g[i - l];
        match cin(i) {
            None => b.and_c(z[i], y[i], gq),
            Some(c) => {
                b.cx(c, z[i]);
                b.cx(c, y[i]);
                b.and_c(z[i], y[i], gq);
                b.cx(c, gq);
            }
        }
    }
    let cout = if na > 0 { g[na - 1] } else { y[n - 1] };
    match ctl {
        Some(c) => b.and_c(c, cout, ms.k),
        None => b.cx(cout, ms.k),
    }
    for i in (l..n).rev() {
        let gq = g[i - l];
        match cin(i) {
            None => {
                b.and_u(z[i], y[i], gq);
                match ctl {
                    Some(c) => b.ccx(c, y[i], z[i]),
                    None => b.cx(y[i], z[i]),
                }
            }
            Some(c) => {
                b.cx(c, gq);
                b.and_u(z[i], y[i], gq);
                match ctl {
                    Some(cc) => b.ccx(cc, y[i], z[i]),
                    None => b.cx(y[i], z[i]),
                }
                b.cx(c, z[i]);
                b.cx(c, y[i]);
            }
        }
    }
    if l > 0 {
        let mode = match ctl {
            Some(c) => Dm::Cond(c),
            None => Dm::Sum,
        };
        let r = down_m(b, zl, yl, ms.c0, mode, false);
        b.play(&r, false);
    }
}

/// Recording: complement zt and compute the logical-AND carries of ~zt + yt; returns (recording, carry-out
/// = [yt > zt]). Playing it inverted uncomputes every carry by measurement.
fn gcmp(b: &mut B, ms: &Ms, zt: &[QubitId], yt: &[QubitId]) -> (Vec<super::builder::G>, QubitId) {
    let n = zt.len();
    let g = &ms.g;
    assert!(g.len() >= n);
    b.begin();
    for &q in zt {
        b.x(q);
    }
    b.and_c(zt[0], yt[0], g[0]);
    for i in 1..n {
        let c = g[i - 1];
        b.cx(c, zt[i]);
        b.cx(c, yt[i]);
        b.and_c(zt[i], yt[i], g[i]);
        b.cx(c, g[i]);
    }
    (b.end(), g[n - 1])
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

/// z <- z + (ctl ? y : 0) mod p (ctl = None: unconditional).
fn modadd_g(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: Option<QubitId>) {
    add_cout(b, ms, z, y, ctl);
    add_small(b, ms, z, 0, Some(ms.k), C, y);
    // erase k = ctl & [z < y] (top-lane compare)
    let zt = &z[256 - CMPT..];
    let yt = &y[256 - CMPT..];
    let (r, cmp) = gcmp(b, ms, zt, yt);
    b.play(&r, false);
    match ctl {
        Some(c) => b.and_u(c, cmp, ms.k),
        None => b.cx(cmp, ms.k),
    }
    b.play(&r, true);
}

/// z <- z + (ctl ? y : 0) mod p.
pub fn ctrl_modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId) {
    modadd_g(b, ms, z, y, Some(ctl));
}

pub fn modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    modadd_g(b, ms, z, y, None);
}
pub fn modsub(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    b.begin();
    modadd(b, ms, z, y);
    let r = b.end();
    b.play(&r, true);
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
