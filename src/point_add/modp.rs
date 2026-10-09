//! Arithmetic modulo p = 2^256 - c (secp256k1, c = 2^32 + 977) on 256-qubit registers (LSB first).
//!
//! Values are kept in [0, 2^256); every routine is exact when inputs are reduced (< p) up to events of
//! probability <= 2^-32 per call (truncated carry propagation, top-lane compare), far below the 9024-shot budget.
//! Reductions fold the overflow back in as + c (since 2^256 = c mod p), so only ~65-lane constant adds occur.
//!
//! Carries: the products run below the traversal's peak, so every routine takes the clean qubits up to that peak
//! as a carry pool `Ms::g`. A lane whose carry sits in the pool is a logical-AND carry (one Toffoli to compute,
//! uncomputed by an X-basis measurement and a classically controlled CZ); lanes beyond the pool keep the in-place
//! ripple (carry stored in the addend lane). The truncation points and compares are the same as before.

use super::arith::{down_m, up_m, Dm};
use super::builder::B;
use crate::circuit::QubitId;

pub const C: u64 = (1u64 << 32) + 977;
/// Lanes touched by the folded constant adds (33-bit constant + 32 lanes of carry headroom).
pub const FOLD: usize = 65;
/// Lanes compared when erasing an add's overflow flag (top lanes only; differs w.p. <= 2^-32).
pub const CMPT: usize = 32;
/// Carry-pool lanes needed at least (a FOLD-lane constant add).
pub const GMIN: usize = FOLD - 1;

/// Scratch for the modular routines: carry-in qubit, overflow flag, a |1> qubit, and the carry pool
/// (clean qubits up to the circuit's peak, |0> between calls).
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
        assert!(ng >= GMIN, "carry pool {} < {} (live {})", ng, GMIN, b.live);
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
    // carry[i] = qubit holding c_i (None: known 0)
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
        // sum bit t ^= a ^ c (on lanes below the top with both present, t already holds t ^ c)
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

/// t[lo..lo+FOLD) += (ctrl ? k : 0) for a classical constant k < 2^33 (carry truncated at lane lo+FOLD).
fn add_small(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: QubitId, k: u64) {
    let n = FOLD.min(t.len() - lo);
    let a: Vec<Option<QubitId>> =
        (0..n).map(|j| if j + lo < 64 && (k >> (j + lo)) & 1 == 1 { Some(ctrl) } else { None }).collect();
    gadd(b, &t[lo..lo + n], &a, &ms.g);
}

/// t[lo..lo+FOLD) -= (ctrl ? k : 0).
fn sub_small(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: QubitId, k: u64) {
    b.begin();
    add_small(b, ms, t, lo, ctrl, k);
    let r = b.end();
    b.play(&r, true);
}

/// z += (ctl ? y : 0) (ctl = None: unconditional) over 256 lanes, and k ^= (ctl &) carry-out of z + y.
/// Lanes [0, l) ripple in place (carry in y's lane, carry-in c0), lanes [l, 256) take logical-AND carries from
/// the pool, l = 256 - min(pool, 256). Toffoli: controlled 3 l + 2 (256 - l) + 1, unconditional 2 l + (256 - l).
fn add_cout(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: Option<QubitId>) {
    let n = z.len();
    assert_eq!(y.len(), n);
    let na = ms.g.len().min(n);
    let l = n - na;
    let g = &ms.g[..na];
    let (zl, yl) = (&z[..l], &y[..l]);
    let rup = if l > 0 { Some(up_m(b, zl, yl, ms.c0, false)) } else { None };
    if let Some(r) = &rup {
        b.play(r, false);
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
                // z holds z ^ c, y holds y ^ c
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
        let rdn = down_m(b, zl, yl, ms.c0, mode, false);
        b.play(&rdn, false);
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

/// z <- 2 z mod p in place. The lane vector is relabelled (z[0] <- old top bit h), then h (c - 1) is added
/// (c - 1 is even, so lane 0 keeps h and the map is a bijection). 64 Toffoli.
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

/// z <- z + (ctl ? y : 0) mod p (ctl = None: unconditional).
fn modadd_g(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: Option<QubitId>) {
    // conditional add with the carry out captured as k = ctl & carry
    add_cout(b, ms, z, y, ctl);
    // fold: 2^256 = c (mod p)
    add_small(b, ms, z, 0, ms.k, C);
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
