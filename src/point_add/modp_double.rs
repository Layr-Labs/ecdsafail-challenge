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
pub const SDW_HEAD: usize = HEAD + 2;
pub const SDW_CMPT: usize = CMPT + 2;
/// Carry-pool lanes for a full-pool constant add (a 33 + 32 lane chain).
pub const GMIN: usize = 33 + HEAD - 1;
/// Carry-pool lanes needed at least. `gcmp` folds the lanes past a short pool in place and `add_small_head` adds a
/// constant's bits past the pool as separate short adds, so the floor is set by the low-Q builds actually tested
/// (pools 31 to 34 between a division's two traversals at 815 to 818 qubits).
pub const GLOW: usize = 28;

/// Scratch: carry-in qubit, overflow flag, and the carry pool (|0> between calls).
pub struct Ms {
    pub c0: QubitId,
    pub k: QubitId,
    pub g: Vec<QubitId>,
}

impl Ms {
    /// Allocate the scratch and fill the carry pool up to `super::PEAK` live qubits (at most 256 pool lanes).
    /// Allocate every other register of the phase first.
    pub fn alloc(b: &mut B) -> Ms {
        let room = (*super::PEAK).saturating_sub(b.live + 2) as usize;
        Ms::alloc_pool(b, room.min(256))
    }
    /// Scratch with a carry pool of exactly `ng` lanes.
    pub fn alloc_pool(b: &mut B, ng: usize) -> Ms {
        let c0 = b.alloc();
        let k = b.alloc();
        assert!(ng >= GLOW, "carry pool {} < {} (live {})", ng, GLOW, b.live);
        let g = b.alloc_n(ng);
        Ms { c0, k, g }
    }
    pub fn release(self, b: &mut B) {
        b.free(self.c0);
        b.free(self.k);
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

/// As `gadd`, but the two highest addend bits are zero. The last carry is
/// used once, to toggle the high target, so it need not own a clean lane.
/// This is the BB7 boundary-register case; `g` needs n-2 clean lanes.
pub fn gadd_top_zero(b: &mut B, t: &[QubitId], a: &[Option<QubitId>], g: &[QubitId]) {
    let n = t.len();
    assert!(n >= 3 && a.len() == n && g.len() >= n - 2);
    assert!(a[n - 1].is_none() && a[n - 2].is_none());
    let mut carry: Vec<Option<QubitId>> = vec![None; n];
    let mut gi = 0;
    for i in 0..n - 2 {
        carry[i + 1] = match (a[i], carry[i]) {
            (None, None) => None,
            (Some(q), None) => {
                b.and_c(t[i], q, g[gi]); gi += 1; Some(g[gi - 1])
            }
            (None, Some(c)) => {
                b.and_c(t[i], c, g[gi]); gi += 1; Some(g[gi - 1])
            }
            (Some(q), Some(c)) => {
                b.cx(c, t[i]); b.cx(c, q);
                b.and_c(t[i], q, g[gi]);
                b.cx(c, q); b.cx(c, g[gi]);
                gi += 1; Some(g[gi - 1])
            }
        };
    }
    if let Some(c) = carry[n - 2] {
        b.ccx(t[n - 2], c, t[n - 1]);
    }
    for i in (0..n - 1).rev() {
        if i + 1 < n - 1 {
            if let Some(gq) = carry[i + 1] {
                match (a[i], carry[i]) {
                    (Some(q), None) => b.and_u(t[i], q, gq),
                    (None, Some(c)) => b.and_u(t[i], c, gq),
                    (Some(q), Some(c)) => {
                        b.cx(c, gq); b.cx(c, q);
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
            (Some(q), Some(c)) => b.cx(q, t[i]),
        }
    }
}

/// Constant-addend carry chain. A first carry from a 1 bit aliases the original
/// target bit, which is still untouched when the chain is erased top-down.
/// If the pool is short, the high zero-addend suffix uses the same borrowed
/// dirty increment as gadd_split.
fn gadd_const(b: &mut B, t: &[QubitId], kbits: &[bool], g: &[QubitId], dirty: &[QubitId], c0: QubitId) {
    let n = t.len();
    assert_eq!(kbits.len(), n);
    let split = g.len() < n.saturating_sub(1);
    let s = if split { g.len() } else { n.saturating_sub(1) };
    if split {
        assert!(kbits[s..].iter().all(|&v| !v));
        assert!(dirty.len() >= n - s + 1);
    }
    let mut carry: Vec<Option<QubitId>> = vec![None; s + 1];
    let mut made = vec![false; s + 1];
    let mut gi = 0;
    for i in 0..s {
        if let Some(c) = carry[i] {
            let q = g[gi];
            if kbits[i] {
                b.x(t[i]); b.x(c);
                b.and_c(t[i], c, q);
                b.x(c); b.x(t[i]); b.x(q);
            } else {
                b.and_c(t[i], c, q);
            }
            carry[i + 1] = Some(q);
            made[i + 1] = true;
            gi += 1;
        } else if kbits[i] {
            carry[i + 1] = Some(t[i]);
        }
    }
    if split {
        if let Some(cs) = carry[s] {
            let mut xr = vec![cs];
            xr.extend_from_slice(&t[s..]);
            inc_dirty(b, &xr, dirty, c0);
            b.x(cs);
        }
    }
    let end = if split { s } else { n };
    for i in (0..end).rev() {
        if i + 1 <= s && made[i + 1] {
            let c = carry[i].expect("generated carry has an input carry");
            let q = carry[i + 1].unwrap();
            if kbits[i] {
                b.x(q); b.x(t[i]); b.x(c);
                b.and_u(t[i], c, q);
                b.x(c); b.x(t[i]);
            } else {
                b.and_u(t[i], c, q);
            }
        }
        if kbits[i] { b.x(t[i]); }
        if let Some(c) = carry[i] { b.cx(c, t[i]); }
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
    add_small_head(b, ms, t, lo, ctrl, k, dirty, HEAD);
}

fn add_small_head(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId], head: usize) {
    let kk = k >> lo;
    assert_eq!(kk << lo, k);
    let l = (64 - kk.leading_zeros()) as usize;
    let n = l + head;
    assert!(lo + n <= t.len());
    if let Some(c) = ctrl {
        let a: Vec<Option<QubitId>> = (0..n).map(|j| if j < 64 && (kk >> j) & 1 == 1 { Some(c) } else { None }).collect();
        let s = ms.g.len();
        if s >= n - 1 {
            gadd(b, &t[lo..lo + n], &a, &ms.g);
        } else if kk.checked_shr(s as u32).unwrap_or(0) == 0 {
            gadd_split(b, &t[lo..lo + n], &a, &ms.g, s, dirty, ms.c0);
        } else {
            // The pool ends below the constant's top bits (c = 2^32 + 977 on a pool of 32 or fewer lanes): add the
            // bits below the pool boundary, then each higher bit j as its own controlled add of 1 on lanes [j, n).
            // Adds commute mod 2^n, so this is the same function as the single add; truncation stays at lane n.
            let low: Vec<Option<QubitId>> = a.iter().enumerate().map(|(j, &x)| if j < s { x } else { None }).collect();
            gadd_split(b, &t[lo..lo + n], &low, &ms.g, s, dirty, ms.c0);
            for j in s..l {
                if (kk >> j) & 1 == 1 {
                    let m = n - j;
                    let mut aj: Vec<Option<QubitId>> = vec![None; m];
                    aj[0] = Some(c);
                    if s >= m - 1 {
                        gadd(b, &t[lo + j..lo + n], &aj, &ms.g);
                    } else {
                        gadd_split(b, &t[lo + j..lo + n], &aj, &ms.g, s, dirty, ms.c0);
                    }
                }
            }
        }
    } else {
        let kbits: Vec<bool> = (0..n).map(|j| j < 64 && (kk >> j) & 1 == 1).collect();
        let s = ms.g.len();
        if s < n.saturating_sub(1) && kk.checked_shr(s as u32).unwrap_or(0) != 0 {
            // Lane A1b: the pool ends below the constant's top bits (c - 1 = 2^32 + 976 at lane 4 on a pool of 28 or
            // fewer lanes): add the bits below the pool boundary, then each higher bit j as its own increment of
            // lanes [j, n). Adds commute mod 2^n, so this is the same function; truncation stays at lane n.
            let low: Vec<bool> = kbits.iter().enumerate().map(|(j, &v)| v && j < s).collect();
            gadd_const(b, &t[lo..lo + n], &low, &ms.g, dirty, ms.c0);
            for j in s..n {
                if kbits[j] && !super::froghop_one::a1b_mut("negsplit") {
                    let mut kj = vec![false; n - j];
                    kj[0] = true;
                    gadd_const(b, &t[lo + j..lo + n], &kj, &ms.g, dirty, ms.c0);
                }
            }
        } else {
            gadd_const(b, &t[lo..lo + n], &kbits, &ms.g, dirty, ms.c0);
        }
    }
}

fn sub_small(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId]) {
    sub_small_head(b, ms, t, lo, ctrl, k, dirty, HEAD);
}

fn sub_small_head(b: &mut B, ms: &Ms, t: &[QubitId], lo: usize, ctrl: Option<QubitId>, k: u64, dirty: &[QubitId], head: usize) {
    b.begin();
    add_small_head(b, ms, t, lo, ctrl, k, dirty, head);
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

/// Chunk carry oracle used after X-measuring an internal held carry.
/// The surrounding classical condition supplies the measurement receipt.
fn chunk_carry_phase(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], pool: &[QubitId], cin: Option<QubitId>) {
    let n = z.len();
    assert_eq!(y.len(), n);
    assert!(pool.len() >= n);
    for i in 0..n {
        let ci = if i == 0 { cin } else { Some(pool[i - 1]) };
        match ci {
            None => b.and_c(z[i], y[i], pool[i]),
            Some(c) => {
                b.cx(c, z[i]);
                b.cx(c, y[i]);
                b.and_c(z[i], y[i], pool[i]);
                b.cx(c, pool[i]);
            }
        }
    }
    b.z(pool[n - 1]);
    for i in (0..n).rev() {
        let ci = if i == 0 { cin } else { Some(pool[i - 1]) };
        match ci {
            None => b.and_u(z[i], y[i], pool[i]),
            Some(c) => {
                b.cx(c, pool[i]);
                b.and_u(z[i], y[i], pool[i]);
                b.cx(c, y[i]);
                b.cx(c, z[i]);
            }
        }
    }
}

/// Uncontrolled z += y mod 2^256 with a 1-Toffoli logical-AND carry per lane.
/// Short pools use held chunk carries, each erased by a receipt-conditioned
/// exact chunk comparison after its sum has been written.
fn add_cout_chunked(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    let n = z.len();
    assert_eq!(n, 256);
    assert_eq!(y.len(), n);
    let p = ms.g.len().min(n);
    assert!(p >= 2);
    let mut nch = 1;
    while (0..nch - 1).map(|j| p - j - 1).sum::<usize>() + (p - (nch - 1)) < n { nch += 1; }
    let mut rest = n - (p - (nch - 1)).min(n);
    let mut bounds = vec![0usize];
    for j in 0..nch - 1 {
        let len = rest.min(p - j - 1);
        assert!(len > 0);
        bounds.push(bounds[j] + len);
        rest -= len;
    }
    bounds.push(n);
    let held = |j: usize| ms.g[p - j];
    for ch in 0..nch {
        let (lo, hi) = (bounds[ch], bounds[ch + 1]);
        let last = ch + 1 == nch;
        let cin = if ch == 0 { None } else { Some(held(ch)) };
        let cr = |i: usize| if i == hi && !last { held(ch + 1) } else { ms.g[i - lo - 1] };
        for i in lo..hi {
            let ci = if i == lo { cin } else { Some(cr(i)) };
            match ci {
                None => b.and_c(y[i], z[i], cr(i + 1)),
                Some(c) => {
                    b.cx(c, y[i]); b.cx(c, z[i]);
                    b.and_c(y[i], z[i], cr(i + 1)); b.cx(c, cr(i + 1));
                }
            }
        }
        if last { b.cx(cr(n), ms.k); }
        for i in (lo..hi).rev() {
            let keep = i + 1 == hi && !last;
            let ci = if i == lo { cin } else { Some(cr(i)) };
            match ci {
                None => {
                    if !keep { b.and_u(y[i], z[i], cr(i + 1)); }
                    b.cx(y[i], z[i]);
                }
                Some(c) => {
                    if !keep { b.cx(c, cr(i + 1)); b.and_u(y[i], z[i], cr(i + 1)); }
                    b.cx(c, z[i]); b.cx(y[i], z[i]); b.cx(c, y[i]);
                }
            }
        }
    }
    for ch in (1..nch).rev() {
        let (lo, hi) = (bounds[ch - 1], bounds[ch]);
        let cin = if ch == 1 { None } else { Some(held(ch - 1)) };
        for &q in &z[lo..hi] { b.x(q); }
        let receipt = b.fresh_bits(1)[0];
        b.hmr_to(held(ch), receipt);
        b.push_condition(receipt);
        chunk_carry_phase(b, ms, &z[lo..hi], &y[lo..hi], &ms.g[..hi - lo], cin);
        b.pop_condition();
        for &q in &z[lo..hi] { b.x(q); }
    }
}

/// Recording: complement zt and compute the logical-AND carries of ~zt + yt; returns (recording, carry-out
/// = [yt > zt]). Playing it inverted uncomputes every carry by measurement.
///
/// A pool of f < n lanes computes carries c_1 .. c_f as logical ANDs in g[0..f) and folds every lane i >= f in place
/// onto the last carry lane c = g[f-1]: with c = c_i, after cx(c, zt[i]), cx(c, yt[i]) the gate ccx(zt[i], yt[i], c)
/// leaves c ^ (zt ^ c)(yt ^ c) = MAJ(zt[i], yt[i], c_i) = c_{i+1} there (zt[i], yt[i] keep their c_i-masked values),
/// so the carry-out is returned in g[f-1]. The map is a bijection and the recording stays exactly invertible (each
/// CCX is self-inverse and restores c_i before the lane's CXs are undone), at one extra Toffoli per in-place lane
/// per compare. Pools of n lanes or more emit the original gate list unchanged.
fn gcmp(b: &mut B, ms: &Ms, zt: &[QubitId], yt: &[QubitId]) -> (Vec<super::builder::G>, QubitId) {
    let n = zt.len();
    let g = &ms.g;
    let fresh = g.len().min(n);
    assert!(n >= 1 && fresh >= 1, "compare of {} lanes on a pool of {}", n, g.len());
    b.begin();
    for &q in zt {
        b.x(q);
    }
    b.and_c(zt[0], yt[0], g[0]);
    for i in 1..fresh {
        let c = g[i - 1];
        b.cx(c, zt[i]);
        b.cx(c, yt[i]);
        b.and_c(zt[i], yt[i], g[i]);
        b.cx(c, g[i]);
    }
    if fresh < n {
        let c = g[fresh - 1];
        for i in fresh..n {
            b.cx(c, zt[i]);
            b.cx(c, yt[i]);
            b.ccx(zt[i], yt[i], c);
        }
        return (b.end(), c);
    }
    (b.end(), g[n - 1])
}

/// z <- 2 z mod p in place (relabel z[0] <- old top bit h, then add h (c - 1); c - 1 is even so lane 0 keeps h).
pub fn mod_double(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, dirty: &[QubitId]) {
    mod_double_head(b, ms, z, dirty, HEAD);
}

fn mod_double_head(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, dirty: &[QubitId], head: usize) {
    let top = z.pop().unwrap();
    z.insert(0, top);
    let h = z[0];
    add_small_head(b, ms, z, 4, Some(h), C - 1, dirty, head);
}

pub fn mod_halve(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, dirty: &[QubitId]) {
    mod_halve_head(b, ms, z, dirty, HEAD);
}

fn mod_halve_head(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, dirty: &[QubitId], head: usize) {
    let h = z[0];
    sub_small_head(b, ms, z, 4, Some(h), C - 1, dirty, head);
    let low = z.remove(0);
    z.push(low);
}

/// z <- z + (ctl ? y : 0) mod p (ctl = None: unconditional).
/// Fold k*C + h*(C-1) once after a Horner shift and controlled add.
/// The old top bit h is saved in `one` because add_cout changes z[0].
fn merged_fold(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], h: QubitId) {
    let k = ms.k;
    let xh = ms.g[0];
    let ah = ms.g[1];
    let oh = ms.g[2];
    b.cx(k, xh);
    b.cx(h, xh);
    b.and_c(k, h, ah);
    b.cx(xh, oh);
    b.cx(ah, oh);
    let mut addend = vec![None; 66];
    addend[0] = Some(k);
    for i in [4, 6, 32] { addend[i] = Some(xh); }
    for i in [5, 10, 33] { addend[i] = Some(ah); }
    for i in [7, 8, 9] { addend[i] = Some(oh); }
    let g = &ms.g[3..];
    if g.len() >= 65 {
        gadd(b, &z[..66], &addend, g);
    } else {
        gadd_split(b, &z[..66], &addend, g, g.len(), y, ms.c0);
    }
    b.cx(ah, oh);
    b.cx(xh, oh);
    b.and_u(k, h, ah);
    b.cx(h, xh);
    b.cx(k, xh);
}

fn modadd_g(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: Option<QubitId>, horner_h: Option<QubitId>, crep: bool, marks: Option<&mut Vec<(usize, usize)>>, head: usize, cmpt: usize) {
    if let Some(h) = horner_h {
        b.x(h); // borrow a temporary |1> as a clean h register
        b.cx(z[0], h);
    }
    add_cout(b, ms, z, y, ctl);
    if let Some(h) = horner_h {
        merged_fold(b, ms, z, y, h);
        // z[0] = h ^ (ctl & y[0]) ^ k. Reconstruct h to clear the saved copy.
        b.cx(z[0], h);
        b.cx(ms.k, h);
        b.ccx(ctl.expect("Horner step has a control"), y[0], h);
        b.x(h);
    }
    else { add_small_head(b, ms, z, 0, Some(ms.k), C, y, head); }
    if crep {
        assert!(marks.is_none(), "CREP is emitted directly, not recorded");
        let receipt = b.fresh_bits(1)[0];
        b.hmr_to(ms.k, receipt);
        b.push_condition(receipt);
        let zt = &z[256 - cmpt..];
        let yt = &y[256 - cmpt..];
        let (r, cmp) = gcmp(b, ms, zt, yt);
        b.play(&r, false);
        b.cz(ctl.expect("CREP add has a control"), cmp);
        b.play(&r, true);
        b.pop_condition();
        return;
    }
    let erase_start = b.mark_pos();
    // erase k = ctl & [z < y] (top-lane compare)
    let zt = &z[256 - cmpt..];
    let yt = &y[256 - cmpt..];
    let (r, cmp) = gcmp(b, ms, zt, yt);
    b.play(&r, false);
    match ctl {
        Some(c) => b.and_u(c, cmp, ms.k),
        None => b.cx(cmp, ms.k),
    }
    b.play(&r, true);
    if let Some(marks) = marks {
        marks.push((erase_start, b.mark_pos()));
    }
}

/// z <- z + (ctl ? y : 0) mod p.
pub fn ctrl_modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId) {
    modadd_g(b, ms, z, y, Some(ctl), None, false, None, HEAD, CMPT);
}

fn ctrl_modadd_crep(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], ctl: QubitId) {
    modadd_g(b, ms, z, y, Some(ctl), None, true, None, HEAD, CMPT);
}

/// Record the k-erasure interval for a paired product's forward HMR and inverse phase repair.
pub(super) fn horner_add(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], ctl: QubitId, marks: Option<&mut Vec<(usize, usize)>>) {
    // Refuted B3 diagnostic only: its private temporary is outside Ms.
    let h = b.alloc();
    b.x(h);
    let top = z.pop().unwrap();
    z.insert(0, top);
    modadd_g(b, ms, z, y, Some(ctl), Some(h), false, marks, HEAD, CMPT);
    b.x(h);
    b.free(h);
}

fn horner_add_crep(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], ctl: QubitId) {
    let h = b.alloc();
    b.x(h);
    let top = z.pop().unwrap();
    z.insert(0, top);
    modadd_g(b, ms, z, y, Some(ctl), Some(h), true, None, HEAD, CMPT);
    b.x(h);
    b.free(h);
}

pub fn modadd(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId]) {
    modadd_g(b, ms, z, y, None, None, false, None, HEAD, CMPT);
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

fn sdw_step_chunked(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], s: QubitId) {
    for &q in z { b.cx(s, q); }
    add_cout_chunked(b, ms, z, y);
    add_small_head(b, ms, z, 0, Some(ms.k), C, y, SDW_HEAD);
    let receipt = b.fresh_bits(1)[0];
    b.hmr_to(ms.k, receipt);
    b.push_condition(receipt);
    let (r, cmp) = gcmp(b, ms, &z[256 - SDW_CMPT..], &y[256 - SDW_CMPT..]);
    b.play(&r, false);
    b.z(cmp);
    b.play(&r, true);
    b.pop_condition();
    for &q in z { b.cx(s, q); }
}

pub fn sdw_product_chunked(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    for i in 0..256 { b.cx(y[i], z[i]); }
    mod_double_head(b, ms, z, y, SDW_HEAD);
    for k in (0..255).rev() {
        b.x(a[k + 1]);
        sdw_step_chunked(b, ms, z, y, a[k + 1]);
        b.x(a[k + 1]);
        if k > 0 { mod_double_head(b, ms, z, y, SDW_HEAD); }
    }
    b.x(a[0]);
    b.begin(); modadd_g(b, ms, z, y, Some(a[0]), None, false, None, SDW_HEAD, SDW_CMPT);
    let correction = b.end(); b.play(&correction, true);
    b.x(a[0]);
}

/// Arithmetic reverse of sdw_product_chunked. Measured erases in the
/// forward product cannot be inverted as a recorded gate list.
pub fn sdw_product_inv_chunked(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    b.x(a[0]); modadd_g(b, ms, z, y, Some(a[0]), None, false, None, SDW_HEAD, SDW_CMPT); b.x(a[0]);
    for k in 0..255 {
        if k > 0 { mod_halve_head(b, ms, z, y, SDW_HEAD); }
        sdw_step_chunked(b, ms, z, y, a[k + 1]);
    }
    mod_halve_head(b, ms, z, y, SDW_HEAD);
    for i in 0..256 { b.cx(y[i], z[i]); }
}

/// One signed Horner digit. s=1 selects subtraction by complementing the
/// accumulator around the same unconditional adder. All correction windows
/// in this path are two lanes wider than the inherited binary product.
fn sdw_step(b: &mut B, ms: &Ms, z: &[QubitId], y: &[QubitId], s: QubitId,
            crep: bool, mark: Option<&mut Vec<(usize, usize)>>) {
    for &q in z { b.cx(s, q); }
    add_cout(b, ms, z, y, None);
    add_small_head(b, ms, z, 0, Some(ms.k), C, y, SDW_HEAD);
    if crep {
        let receipt = b.fresh_bits(1)[0];
        b.hmr_to(ms.k, receipt);
        b.push_condition(receipt);
        let (r, cmp) = gcmp(b, ms, &z[256 - SDW_CMPT..], &y[256 - SDW_CMPT..]);
        b.play(&r, false);
        b.z(cmp);
        b.play(&r, true);
        b.pop_condition();
    } else {
        let start = b.mark_pos();
        let (r, cmp) = gcmp(b, ms, &z[256 - SDW_CMPT..], &y[256 - SDW_CMPT..]);
        b.play(&r, false);
        b.cx(cmp, ms.k);
        b.play(&r, true);
        if let Some(marks) = mark { marks.push((start, b.mark_pos())); }
    }
    for &q in z { b.cx(s, q); }
}

fn sdw_product_impl(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId],
                    crep: bool, mut marks: Option<&mut Vec<(usize, usize)>>) {
    assert_eq!(a.len(), 256);
    assert_eq!(y.len(), 256);
    for i in 0..256 { b.cx(y[i], z[i]); }
    mod_double_head(b, ms, z, y, SDW_HEAD);
    for k in (0..255).rev() {
        b.x(a[k + 1]);
        sdw_step(b, ms, z, y, a[k + 1], crep, marks.as_mut().map(|x| &mut **x));
        b.x(a[k + 1]);
        if k > 0 { mod_double_head(b, ms, z, y, SDW_HEAD); }
    }
    // Subtract (1-a_0)*y. This is the inverse of the controlled add, with
    // the signed path's widened fold and comparison.
    b.x(a[0]);
    b.begin();
    modadd_g(b, ms, z, y, Some(a[0]), None, false, None, SDW_HEAD, SDW_CMPT);
    let correction = b.end();
    b.play(&correction, true);
    b.x(a[0]);
}

pub fn sdw_product_crep(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    sdw_product_impl(b, ms, z, a, y, true, None);
}

pub fn sdw_product_marked(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId], marks: &mut Vec<(usize, usize)>) {
    sdw_product_impl(b, ms, z, a, y, false, Some(marks));
}

/// Accumulate y^2 with one temporary digit lane and no 256-lane digit copy.
pub fn sdw_square_acc(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], tmp: QubitId) {
    for _ in 0..255 { mod_halve_head(b, ms, z, y, SDW_HEAD); }
    for k in (0..256).rev() {
        b.cx(y[k], tmp);
        modadd_g(b, ms, z, y, Some(tmp), None, true, None, SDW_HEAD, SDW_CMPT);
        b.cx(y[k], tmp);
        if k > 0 { mod_double_head(b, ms, z, y, SDW_HEAD); }
    }
}

/// z = a * y mod p into a zero register z (Horner, top bit of a first).
pub fn product(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    for i in (0..256).rev() {
        if i == 255 {
            // z is |0>: the first Horner term is a controlled copy of y.
            for j in 0..256 { b.ccx(a[i], y[j], z[j]); }
        } else {
            mod_double(b, ms, z, y);
            ctrl_modadd(b, ms, z, y, a[i]);
        }
    }
}

/// Same product with exact recording offsets of its k-erasure segments.
pub fn product_marked(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId], marks: &mut Vec<(usize, usize)>) {
    for i in (0..256).rev() {
        if i == 255 {
            for j in 0..256 { b.ccx(a[i], y[j], z[j]); }
        } else {
            mod_double(b, ms, z, y);
            modadd_g(b, ms, z, y, Some(a[i]), None, false, Some(marks), HEAD, CMPT);
        }
    }
}

/// Forward-only Horner product: measure each k and repair its phase by a receipt-conditioned
/// 32-lane compare on the product output. The classical receipt is 1 on half the shots.
pub fn product_crep(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, a: &[QubitId], y: &[QubitId]) {
    for i in (0..256).rev() {
        if i == 255 {
            for j in 0..256 { b.ccx(a[i], y[j], z[j]); }
        } else {
            mod_double(b, ms, z, y);
            ctrl_modadd_crep(b, ms, z, y, a[i]);
        }
    }
}

/// z += a * y mod p (any z), doubling y in place and restoring it; `a` must not overlap `y`.
pub fn mac(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &mut Vec<QubitId>) {
    for i in 0..256 {
        ctrl_modadd_crep(b, ms, z, y, a[i]);
        if i != 255 { mod_double(b, ms, y, a); }
    }
    for _ in 0..255 { mod_halve(b, ms, y, a); }
}

/// Load a classical bit register into zero qubits (no Toffoli).
pub fn load_bits(b: &mut B, q: &[QubitId], bits: &[crate::circuit::BitId]) {
    for (&qq, &bb) in q.iter().zip(bits) {
        b.x_if(qq, bb);
    }
}

#[cfg(test)]
mod r10_c8_one_tests {
    use super::*;
    use super::super::tests_double::run;
    use super::super::refmodel_one::{p, N};

    #[test]
    fn one_r10_c8_one_const_add_exhaustive() {
        let mut checked = 0usize;
        for n in 1..=8 {
            for k in 0..(1usize << n) {
                let bits: Vec<bool> = (0..n).map(|i| (k >> i) & 1 == 1).collect();
                let mut old = B::new();
                let ot = old.alloc_n(n);
                let og = old.alloc_n(n);
                let one = old.alloc();
                old.x(one);
                let a: Vec<Option<QubitId>> = bits.iter().map(|&bit| if bit { Some(one) } else { None }).collect();
                gadd(&mut old, &ot, &a, &og);
                old.x(one);

                let mut new = B::new();
                let nt = new.alloc_n(n);
                let ng = new.alloc_n(n);
                assert_eq!((&ot, &og), (&nt, &ng));
                let c0 = new.alloc();
                gadd_const(&mut new, &nt, &bits, &ng, &[], c0);
                for base in (0..(1usize << n)).step_by(64) {
                    let input = |words: &mut Vec<u64>| {
                        for shot in 0..64 {
                            let tv = base + shot;
                            if tv >= (1usize << n) { break; }
                            for i in 0..n {
                                if (tv >> i) & 1 == 1 { words[i] |= 1u64 << shot; }
                            }
                        }
                    };
                    let before = run(&old.ops, old.width() as usize, &input);
                    let after = run(&new.ops, new.width() as usize, &input);
                    assert_eq!(before.phase, 0, "old phase n={n} k={k} base={base}");
                    assert_eq!(after.phase, 0, "new phase n={n} k={k} base={base}");
                    assert_eq!(&before.q[..2*n], &after.q[..2*n], "all target/pool wires n={n} k={k} base={base}");
                    assert!(before.q[2*n..].iter().all(|&q| q == 0), "old one clear");
                    assert!(after.q[2*n..].iter().all(|&q| q == 0), "new carry-in clear");
                    for shot in 0..64 {
                        let tv = base + shot;
                        if tv >= (1usize << n) { break; }
                        let got = (0..n).fold(0usize, |v, i| v | ((((after.q[i] >> shot) & 1) as usize) << i));
                        assert_eq!(got, (tv + k) & ((1usize << n) - 1), "arithmetic n={n} k={k} t={tv}");
                        checked += 1;
                    }
                }
            }
        }
        assert_eq!(checked, (1..=8).map(|n| 1usize << (2*n)).sum());
        eprintln!("ONE constant add exhaustive: {checked} input/addend cases, all target/pool wires and phase");
    }

    #[test]
    fn one_r10_c8_one_neg_and_modsub_kernel() {
        let pp = p();
        let mut seed = 0xc801c801u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut zv = [N::ZERO; 64];
        let mut yv = [N::ZERO; 64];
        for shot in 0..64 {
            for limb in 0..4 {
                zv[shot] |= N::from(next()) << (64 * limb);
                yv[shot] |= N::from(next()) << (64 * limb);
            }
            zv[shot] %= pp;
            yv[shot] %= pp;
        }
        zv[0] = N::ZERO; zv[1] = N::from(1u64); zv[2] = pp - N::from(1u64);
        yv[0] = pp - N::from(1u64); yv[1] = N::ZERO; yv[2] = N::from(1u64);
        for pool in [58, 60, 73] {
            for subtract in [false, true] {
                let build = |old: bool| {
                    let mut b = B::new();
                    let z = b.alloc_n(256);
                    let y = b.alloc_n(256);
                    let dirty = b.alloc_n(256);
                    let one = if old { let q = b.alloc(); b.x(q); Some(q) } else { None };
                    let ms = Ms::alloc_pool(&mut b, pool);
                    if subtract {
                        modsub(&mut b, &ms, &z, &y);
                    } else if let Some(q) = one {
                        for &v in &z { b.x(v); }
                        b.begin();
                        let kk = (C - 1) >> 4;
                        let n = 61;
                        let a: Vec<Option<QubitId>> = (0..n).map(|j| if (kk >> j) & 1 == 1 { Some(q) } else { None }).collect();
                        if ms.g.len() >= n - 1 { gadd(&mut b, &z[4..4+n], &a, &ms.g); }
                        else { gadd_split(&mut b, &z[4..4+n], &a, &ms.g, ms.g.len(), &dirty, ms.c0); }
                        let r = b.end();
                        b.play(&r, true);
                    } else {
                        ctrl_neg(&mut b, &ms, &z, None, &dirty);
                    }
                    if let Some(q) = one { b.x(q); }
                    (b, z, y, dirty)
                };
                let (old, oz, oy, od) = build(true);
                let (new, nz, ny, nd) = build(false);
                assert_eq!((&oz, &oy, &od), (&nz, &ny, &nd));
                let mut input = |words: &mut Vec<u64>| {
                    for shot in 0..64 {
                        for i in 0..256 {
                            if zv[shot].bit(i) { words[oz[i].0 as usize] |= 1u64 << shot; }
                            if yv[shot].bit(i) { words[oy[i].0 as usize] |= 1u64 << shot; }
                        }
                    }
                    for &q in &od { words[q.0 as usize] = next(); }
                };
                // Freeze the same dirty passenger words for both simulators.
                let mut words = vec![0u64; old.width() as usize];
                input(&mut words);
                let init = |w: &mut Vec<u64>| w[..768].copy_from_slice(&words[..768]);
                let before = run(&old.ops, old.width() as usize, &init);
                let after = run(&new.ops, new.width() as usize, &init);
                assert_eq!(&before.q[..768], &after.q[..768], "all data/dirty wires pool {pool} sub {subtract}");
                assert_eq!(before.phase, after.phase, "old/new phase pool {pool} sub {subtract}");
                assert!(before.q[768..].iter().all(|&v| v == 0), "old scratch clean");
                assert!(after.q[768..].iter().all(|&v| v == 0), "new scratch clean");
                for shot in 3..64 {
                    let got = (0..256).fold(N::ZERO, |v, i| if (after.q[nz[i].0 as usize] >> shot) & 1 == 1 { v | (N::from(1u64) << i) } else { v });
                    let want = if subtract { (zv[shot] + pp - yv[shot]) % pp } else { (pp - zv[shot]) % pp };
                    assert_eq!(got % pp, want, "integer output pool {pool} sub {subtract} shot {shot}");
                }
                assert_eq!(after.phase & !0b111, 0, "random-case phase pool {pool} sub {subtract}");
            }
        }
        eprintln!("ONE ctrl_neg(None)/modsub: pools 58/60/73, 64 cases each, 256 dirty passengers, all-wire old/new and random-case phase");
    }
}

#[cfg(test)]
mod sdw_grid {
    use super::*;
    use super::super::refmodel_one::{p, N};
    use super::super::tests_double::run;
    fn put(words: &mut [u64], qs: &[QubitId], shot: usize, v: N) {
        for (i, &q) in qs.iter().enumerate() {
            if v.bit(i) { words[q.0 as usize] |= 1u64 << shot; }
        }
    }
    fn get(words: &[u64], qs: &[QubitId], shot: usize) -> N {
        let mut v = N::ZERO;
        for (i, &q) in qs.iter().enumerate() {
            if (words[q.0 as usize] >> shot) & 1 == 1 { v |= N::from(1u64) << i; }
        }
        v
    }
    #[test]
    fn one_r11_c10_signed_edge_grid() {
        let pp = p();
        let one = N::from(1u64);
        let c = N::from(C);
        let top = one << 224;
        let vals = [N::ZERO, one, one + one, c - one, c, c + one, c + c,
            top - one, top, top + one, (one << 222), pp - top - one, pp - top,
            pp - top + one, pp - c - c, pp - c, pp - one - one, pp - one];
        let low_mask: N = (one << (33 + SDW_HEAD)) - one;
        let old_low_mask: N = (one << 65usize) - one;
        let width_mask: N = (one << 256usize) - one;
        let mut seed = 0xc7c517u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        for pool in [33, 34, 58, 60, 72, 73] {
            for subtract in [false, true] {
                let build = |new: bool| {
                    let mut b = B::new();
                    let z = b.alloc_n(256);
                    let y = b.alloc_n(256);
                    let s = b.alloc();
                    let passenger = b.alloc_n(256);
                    let ms = Ms::alloc_pool(&mut b, pool);
                    if new { sdw_step(&mut b, &ms, &z, &y, s, false, None); }
                    else if subtract { modsub(&mut b, &ms, &z, &y); }
                    else { modadd(&mut b, &ms, &z, &y); }
                    (b, z, y, s, passenger, ms.k)
                };
                let old = build(false);
                let new = build(true);
                let mut old_bad = 0usize;
                let mut new_bad = 0usize;
                let mut new_only = 0usize;
                let mut fixed = 0usize;
                let pairs: Vec<_> = vals.iter().flat_map(|&z| vals.iter().map(move |&y| (z, y))).collect();
                for chunk in pairs.chunks(64) {
                    let mut input = vec![0u64; old.0.width() as usize];
                    for (shot, &(zv, yv)) in chunk.iter().enumerate() {
                        put(&mut input, &old.1, shot, zv);
                        put(&mut input, &old.2, shot, yv);
                    }
                    if subtract { input[old.3.0 as usize] = u64::MAX; }
                    for &q in &old.4 { input[q.0 as usize] = next(); }
                    let o = run(&old.0.ops, old.0.width() as usize, &|w| w.copy_from_slice(&input));
                    let n = run(&new.0.ops, new.0.width() as usize, &|w| w.copy_from_slice(&input));
                    for (shot, &(zv, yv)) in chunk.iter().enumerate() {
                        let u = if subtract { width_mask ^ zv } else { zv };
                        let wide = u + yv;
                        let carry = wide > width_mask;
                        let raw = wide & width_mask;
                        let folded = if carry { (raw & !low_mask) | (((raw & low_mask) + c) & low_mask) } else { raw };
                        let cmp = (folded >> (256 - SDW_CMPT)) < (yv >> (256 - SDW_CMPT));
                        let predicted_k = carry ^ cmp;
                        let predicted_z = if subtract { width_mask ^ folded } else { folded };
                        let want = if subtract { zv.add_mod(if yv == N::ZERO { N::ZERO } else { pp - yv }, pp) }
                                   else { zv.add_mod(yv, pp) };
                        let nk = ((n.q[new.5.0 as usize] >> shot) & 1) != 0;
                        let nv = get(&n.q, &new.1, shot);
                        assert_eq!((nv, nk), (predicted_z, predicted_k),
                            "unpredicted signed result pool {pool} subtract {subtract} z={zv} y={yv}");
                        if subtract {
                            // Inverse of the old add: compare first, undo its
                            // 65-lane fold, then undo the raw 256-lane addition.
                            let ocmp = (zv >> 224) < (yv >> 224);
                            let pre = if ocmp { (zv & !old_low_mask) | (((zv & old_low_mask) + (one << 65usize) - c) & old_low_mask) } else { zv };
                            let borrow = pre < yv;
                            let predicted_old_z = if borrow { (one << 256usize) + pre - yv } else { pre - yv };
                            let predicted_old_k = ocmp ^ borrow;
                            assert_eq!((get(&o.q, &old.1, shot), ((o.q[old.5.0 as usize] >> shot) & 1) != 0),
                                (predicted_old_z, predicted_old_k), "unpredicted old subtract z={zv} y={yv}");
                        }
                        let ob = get(&o.q, &old.1, shot) != want
                            || ((o.q[old.5.0 as usize] >> shot) & 1) != 0 || ((o.phase >> shot) & 1) != 0;
                        let nb = nv != want || nk || ((n.phase >> shot) & 1) != 0;
                        if nb { assert!(predicted_k || predicted_z != want,
                            "unpredicted phase pool {pool} subtract {subtract} z={zv} y={yv}"); }
                        old_bad += ob as usize; new_bad += nb as usize;
                        new_only += (!ob && nb) as usize; fixed += (ob && !nb) as usize;
                        for (&oq, &nq) in old.4.iter().zip(&new.4) {
                            assert_eq!((o.q[oq.0 as usize] >> shot) & 1, (n.q[nq.0 as usize] >> shot) & 1);
                        }
                    }
                }
                eprintln!("signed grid pool {pool} subtract {subtract}: old_bad {old_bad} new_bad {new_bad} new_only {new_only} fixed {fixed} / {}", pairs.len());
            }
        }
    }
    #[test]
    fn one_r11_c10_s4_signed_edge_grid() {
        let pp = p();
        let one = N::from(1u64);
        let c = N::from(C);
        let top = one << 224;
        let vals = [N::ZERO, one, one + one, c - one, c, c + one, c + c,
            top - one, top, top + one, (one << 222), pp - top - one, pp - top,
            pp - top + one, pp - c - c, pp - c, pp - one - one, pp - one];
        let low_mask: N = (one << (33 + SDW_HEAD)) - one;
        let old_low_mask: N = (one << 65usize) - one;
        let width_mask: N = (one << 256usize) - one;
        let mut seed = 0xc7c517u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        for pool in [33, 34, 58, 60, 72, 73] {
            for subtract in [false, true] {
                let build = |new: bool| {
                    let mut b = B::new();
                    let z = b.alloc_n(256);
                    let y = b.alloc_n(256);
                    let s = b.alloc();
                    let passenger = b.alloc_n(256);
                    let ms = Ms::alloc_pool(&mut b, pool);
                    if new { sdw_step_chunked(&mut b, &ms, &z, &y, s); }
                    else if subtract { modsub(&mut b, &ms, &z, &y); }
                    else { modadd(&mut b, &ms, &z, &y); }
                    (b, z, y, s, passenger, ms.k)
                };
                let old = build(false);
                let new = build(true);
                let mut old_bad = 0usize;
                let mut new_bad = 0usize;
                let mut new_only = 0usize;
                let mut fixed = 0usize;
                let pairs: Vec<_> = vals.iter().flat_map(|&z| vals.iter().map(move |&y| (z, y))).collect();
                for chunk in pairs.chunks(64) {
                    let mut input = vec![0u64; old.0.width() as usize];
                    for (shot, &(zv, yv)) in chunk.iter().enumerate() {
                        put(&mut input, &old.1, shot, zv);
                        put(&mut input, &old.2, shot, yv);
                    }
                    if subtract { input[old.3.0 as usize] = u64::MAX; }
                    for &q in &old.4 { input[q.0 as usize] = next(); }
                    let o = run(&old.0.ops, old.0.width() as usize, &|w| w.copy_from_slice(&input));
                    let n = run(&new.0.ops, new.0.width() as usize, &|w| w.copy_from_slice(&input));
                    for (shot, &(zv, yv)) in chunk.iter().enumerate() {
                        let u = if subtract { width_mask ^ zv } else { zv };
                        let wide = u + yv;
                        let carry = wide > width_mask;
                        let raw = wide & width_mask;
                        let folded = if carry { (raw & !low_mask) | (((raw & low_mask) + c) & low_mask) } else { raw };
                        let cmp = (folded >> (256 - SDW_CMPT)) < (yv >> (256 - SDW_CMPT));
                        let predicted_k = carry ^ cmp;
                        let predicted_z = if subtract { width_mask ^ folded } else { folded };
                        let want = if subtract { zv.add_mod(if yv == N::ZERO { N::ZERO } else { pp - yv }, pp) }
                                   else { zv.add_mod(yv, pp) };
                        let nk = ((n.q[new.5.0 as usize] >> shot) & 1) != 0;
                        let nv = get(&n.q, &new.1, shot);
                        assert_eq!(nv, predicted_z,
                            "unpredicted S4 residue pool {pool} subtract {subtract} z={zv} y={yv}");
                        assert!(!nk, "S4 measured top carry must reset k");
                        if subtract {
                            // Inverse of the old add: compare first, undo its
                            // 65-lane fold, then undo the raw 256-lane addition.
                            let ocmp = (zv >> 224) < (yv >> 224);
                            let pre = if ocmp { (zv & !old_low_mask) | (((zv & old_low_mask) + (one << 65usize) - c) & old_low_mask) } else { zv };
                            let borrow = pre < yv;
                            let predicted_old_z = if borrow { (one << 256usize) + pre - yv } else { pre - yv };
                            let predicted_old_k = ocmp ^ borrow;
                            assert_eq!((get(&o.q, &old.1, shot), ((o.q[old.5.0 as usize] >> shot) & 1) != 0),
                                (predicted_old_z, predicted_old_k), "unpredicted old subtract z={zv} y={yv}");
                        }
                        let ob = get(&o.q, &old.1, shot) != want
                            || ((o.q[old.5.0 as usize] >> shot) & 1) != 0 || ((o.phase >> shot) & 1) != 0;
                        let nb = nv != want || nk || ((n.phase >> shot) & 1) != 0;
                        if nb { assert!(predicted_k || predicted_z != want,
                            "unpredicted phase pool {pool} subtract {subtract} z={zv} y={yv}"); }
                        old_bad += ob as usize; new_bad += nb as usize;
                        new_only += (!ob && nb) as usize; fixed += (ob && !nb) as usize;
                        for (&oq, &nq) in old.4.iter().zip(&new.4) {
                            assert_eq!((o.q[oq.0 as usize] >> shot) & 1, (n.q[nq.0 as usize] >> shot) & 1);
                        }
                    }
                }
                eprintln!("signed grid pool {pool} subtract {subtract}: old_bad {old_bad} new_bad {new_bad} new_only {new_only} fixed {fixed} / {}", pairs.len());
            }
        }
    }
}

#[cfg(test)]
mod a1_gcmp_short_pool {
    //! A/B of `gcmp` on a pool one lane short (top majority folded in place) against the original n-lane pool:
    //! same carry-out value, same phase, every wire restored, under value, AND-compute/AND-uncompute and phase
    //! consumers. Exhaustive for n <= 5, edge plus random cases at the signed-digit width SDW_CMPT.
    use super::*;
    use super::super::tests_double::run;

    /// Build: zt, yt, ctl, k first (identical ids in both variants), then c0 and the pool.
    fn build(n: usize, pool: usize, consumer: u8) -> (B, Vec<QubitId>, Vec<QubitId>, QubitId, QubitId, Vec<QubitId>, u64) {
        let mut b = B::new();
        let zt = b.alloc_n(n);
        let yt = b.alloc_n(n);
        let ctl = b.alloc();
        let k = b.alloc();
        let c0 = b.alloc();
        let g = b.alloc_n(pool);
        let ms = Ms { c0, k, g: g.clone() };
        let (r, cmp) = gcmp(&mut b, &ms, &zt, &yt);
        assert!(!zt.contains(&cmp) && !yt.contains(&cmp) && cmp != ctl && cmp != k);
        match consumer {
            // value: k ^= cmp
            0 => { b.play(&r, false); b.cx(cmp, k); b.play(&r, true); }
            // AND compute then AND uncompute (measured) of k = ctl & cmp, as the recorded correction and its inverse
            1 => {
                b.play(&r, false); b.and_c(ctl, cmp, k); b.play(&r, true);
                b.play(&r, false); b.and_u(ctl, cmp, k); b.play(&r, true);
            }
            // phase: (-1)^(ctl & cmp)
            2 => { b.play(&r, false); b.cz(ctl, cmp); b.play(&r, true); }
            // the same compare inside a recording, played inverted (AndU -> AndC), then forward again
            _ => {
                b.begin(); b.play(&r, false); b.and_u(ctl, cmp, k); b.play(&r, true); let rr = b.end();
                b.play(&rr, true);
                b.play(&rr, false);
            }
        }
        let tof = b.tof;
        (b, zt, yt, ctl, k, g, tof)
    }

    fn check(n: usize, cases: &[(u64, u64, bool)]) -> usize {
        let mut checked = 0;
        for m in 1..n {
            if n > 8 && m > 3 && m != n - 1 { continue; }
            checked += check_m(n, m, cases);
        }
        checked
    }

    /// pool n - m (m lanes folded in place) against the original n-lane pool
    fn check_m(n: usize, m: usize, cases: &[(u64, u64, bool)]) -> usize {
        let mask = if n == 64 { u64::MAX } else { (1u64 << n) - 1 };
        let mut checked = 0;
        for consumer in 0..4u8 {
            let (old, ozt, oyt, octl, ok, og, otof) = build(n, n, consumer);
            let (new, nzt, nyt, nctl, nk, ng, ntof) = build(n, n - m, consumer);
            assert_eq!((&ozt, &oyt, octl, ok), (&nzt, &nyt, nctl, nk));
            let uses = if consumer == 1 || consumer == 3 { 2 } else { 1 };
            assert_eq!(ntof, otof + uses * m as u64, "emitted Toffoli: one extra CCX per in-place lane per compare compute");
            for chunk in cases.chunks(64) {
                let init = |w: &mut Vec<u64>| {
                    for (s, &(zv, yv, cv)) in chunk.iter().enumerate() {
                        for i in 0..n {
                            if (zv >> i) & 1 == 1 { w[ozt[i].0 as usize] |= 1 << s; }
                            if (yv >> i) & 1 == 1 { w[oyt[i].0 as usize] |= 1 << s; }
                        }
                        if cv { w[octl.0 as usize] |= 1 << s; }
                    }
                };
                let o = run(&old.ops, old.width() as usize, &init);
                let nw = run(&new.ops, new.width() as usize, &init);
                // common wires and phase identical
                for q in ozt.iter().chain(&oyt).chain([&octl, &ok]) {
                    assert_eq!(o.q[q.0 as usize], nw.q[q.0 as usize], "wire {q:?} n={n} m={m} consumer {consumer}");
                }
                assert_eq!(o.phase, nw.phase, "phase n={n} consumer {consumer}");
                for &q in og.iter().chain(&ng) {
                    let (oo, nn) = (o.q.get(q.0 as usize).copied().unwrap_or(0), nw.q.get(q.0 as usize).copied().unwrap_or(0));
                    if og.contains(&q) { assert_eq!(oo, 0, "old pool lane dirty"); }
                    if ng.contains(&q) { assert_eq!(nn, 0, "new pool lane dirty n={n} consumer {consumer}"); }
                }
                for (s, &(zv, yv, cv)) in chunk.iter().enumerate() {
                    let gt = (yv & mask) > (zv & mask);
                    let kq = (nw.q[nk.0 as usize] >> s) & 1 == 1;
                    let ph = (nw.phase >> s) & 1 == 1;
                    match consumer {
                        0 => { assert_eq!(kq, gt, "value n={n} z={zv:x} y={yv:x}"); assert!(!ph); }
                        1 | 3 => { assert!(!kq, "k cleared n={n}"); assert!(!ph, "AND pair phase n={n} z={zv:x} y={yv:x}"); }
                        _ => { assert!(!kq); assert_eq!(ph, cv && gt, "phase n={n} z={zv:x} y={yv:x}"); }
                    }
                    for i in 0..n {
                        assert_eq!((nw.q[nzt[i].0 as usize] >> s) & 1 == 1, (zv >> i) & 1 == 1, "zt restored");
                        assert_eq!((nw.q[nyt[i].0 as usize] >> s) & 1 == 1, (yv >> i) & 1 == 1, "yt restored");
                    }
                    checked += 1;
                }
            }
        }
        checked
    }

    #[test]
    fn a1_gcmp_short_pool_exhaustive_small() {
        let mut total = 0;
        for n in 2..=5usize {
            let mut cases = vec![];
            for zv in 0..(1u64 << n) { for yv in 0..(1u64 << n) { for cv in [false, true] { cases.push((zv, yv, cv)); } } }
            total += check(n, &cases);
        }
        eprintln!("a1 gcmp short pool exhaustive n=2..5, every pool 1..n-1: {total} (input, consumer, pool) cases");
    }

    #[test]
    fn a1_gcmp_short_pool_sdw_width() {
        let n = SDW_CMPT;
        let mask = (1u64 << n) - 1;
        let mut seed = 0xa1_817u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut cases = vec![];
        let edges = [0u64, 1, 2, mask, mask - 1, 1 << (n - 1), (1 << (n - 1)) - 1, (1 << (n - 1)) + 1, 0x2_aaaa_aaaa & mask, 0x1_5555_5555 & mask];
        for &a in &edges { for &c in &edges { for cv in [false, true] { cases.push((a, c, cv)); } } }
        for _ in 0..64 * 200 {
            let a = next() & mask;
            let kind = next() % 4;
            let c = match kind {
                0 => next() & mask,
                1 => a,                                  // equal: carry runs the whole width
                2 => (a + 1) & mask,                     // differ in a low lane only
                _ => a ^ (1u64 << (next() % n as u64)), // one lane differs
            };
            cases.push((a, c, next() & 1 == 1));
        }
        let checked = check(n, &cases);
        eprintln!("a1 gcmp short pool n={n}, pools n-1, n-2, n-3, 1: {checked} (input, consumer, pool) cases");
    }
}

#[cfg(test)]
mod a1_add_small_short_pool {
    //! `add_small_head` with the controlled fold constant c = 2^32 + 977 on pools 30..=33 (the split path below 33)
    //! against a full pool: identical target, control, dirty-passenger and phase on every shot, pool lanes clean.
    use super::*;
    use super::super::refmodel_one::N;
    use super::super::tests_double::run;

    fn build(pool: usize, head: usize, inverse: bool) -> (B, Vec<QubitId>, QubitId, Vec<QubitId>, Vec<QubitId>) {
        let mut b = B::new();
        let t = b.alloc_n(256);
        let ctl = b.alloc();
        let dirty = b.alloc_n(256);
        let (c0, k) = (b.alloc(), b.alloc());
        let ms = Ms { c0, k, g: b.alloc_n(pool) };
        if inverse { sub_small_head(&mut b, &ms, &t, 0, Some(ctl), C, &dirty, head); }
        else { add_small_head(&mut b, &ms, &t, 0, Some(ctl), C, &dirty, head); }
        let g = ms.g.clone();
        (b, t, ctl, dirty, g)
    }

    #[test]
    fn a1_add_small_c_short_pools() {
        let one = N::from(1u64);
        let mut seed = 0xa1_5a11u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut checked = 0usize;
        for head in [HEAD, SDW_HEAD] {
            let n = 33 + head;
            let lowmask = (one << n) - one;
            for inverse in [false, true] {
                let (full, ft, fc, fd, fg) = build(96, head, inverse);
                for pool in [26usize, 27, 28, 29, 30, 31, 32, 33] {
                    let (short, st, sc, sd, sg) = build(pool, head, inverse);
                    assert_eq!((&ft, fc, &fd), (&st, sc, &sd));
                    for batch in 0..64 {
                        let mut tv = vec![N::ZERO; 64];
                        for k in 0..64 {
                            for j in 0..4 { tv[k] |= N::from(next()) << (j * 64); }
                            match (batch * 64 + k) % 8 {
                                0 => tv[k] |= lowmask,                              // carry runs to the truncation lane
                                1 => tv[k] = (tv[k] & !lowmask) | (lowmask - N::from(C) + one),
                                2 => tv[k] = (tv[k] & !lowmask) | ((one << 32) - one), // carry from 977 into bit 32
                                3 => tv[k] = (tv[k] & !lowmask) | (lowmask ^ (one << 32)),
                                _ => {}
                            }
                        }
                        let cw = next();
                        let dw: Vec<u64> = (0..256).map(|_| next()).collect();
                        let init = |w: &mut Vec<u64>| {
                            for k in 0..64 { for i in 0..256 { if tv[k].bit(i) { w[ft[i].0 as usize] |= 1 << k; } } }
                            w[fc.0 as usize] = cw;
                            for i in 0..256 { w[fd[i].0 as usize] = dw[i]; }
                        };
                        let o = run(&full.ops, full.width() as usize, &init);
                        let s = run(&short.ops, short.width() as usize, &init);
                        for q in ft.iter().chain(&fd).chain([&fc]) {
                            assert_eq!(o.q[q.0 as usize], s.q[q.0 as usize], "wire {q:?} pool {pool} head {head} inverse {inverse}");
                        }
                        assert_eq!(o.phase, s.phase, "phase pool {pool} head {head} inverse {inverse}");
                        assert_eq!(s.phase, 0);
                        for &q in &fg { assert_eq!(o.q[q.0 as usize], 0); }
                        for &q in &sg { assert_eq!(s.q[q.0 as usize], 0, "short pool lane dirty pool {pool}"); }
                        // integer model on the full pool: t[0..n) += ctl * c (mod 2^n), or -= for the inverse
                        for k in 0..64 {
                            let mut got = N::ZERO;
                            for i in 0..256 { if (o.q[ft[i].0 as usize] >> k) & 1 == 1 { got |= one << i; } }
                            let lo = tv[k] & lowmask;
                            let add = if (cw >> k) & 1 == 1 { N::from(C) } else { N::ZERO };
                            let m = one << n;
                            let want_lo = if inverse { (lo + m - add) & lowmask } else { (lo + add) & lowmask };
                            assert_eq!(got, (tv[k] & !lowmask) | want_lo, "model pool {pool} head {head}");
                            checked += 1;
                        }
                    }
                }
            }
        }
        eprintln!("a1 add_small c short pools 30..33, heads 32/34, add and inverse: {checked} shots vs full pool");
    }
}
