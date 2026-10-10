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

/// t += A mod 2^|t| where bit i of A is the qubit add[i] (None: 0); a qubit may serve several lanes. Logical-AND
/// carries on `pool` (>= |t| - 1 - lowest used lane), measurement-uncomputed (const_add_pool with per-lane sources).
fn var_add_pool(b: &mut B, t: &[QubitId], add: &[Option<QubitId>], pool: &[QubitId]) {
    let n = t.len();
    let Some(i0) = add.iter().position(|a| a.is_some()) else {
        return;
    };
    let c = |i: usize| pool[i - i0 - 1];
    for i in i0..n - 1 {
        match add[i] {
            Some(h) if i == i0 => b.and_c(t[i], h, c(i + 1)),
            Some(h) => {
                b.cx(c(i), h);
                b.cx(c(i), t[i]);
                b.and_c(h, t[i], c(i + 1));
                b.cx(c(i), c(i + 1));
                b.cx(c(i), h);
            }
            None => b.and_c(t[i], c(i), c(i + 1)),
        }
    }
    let top = n - 1;
    if top > i0 {
        b.cx(c(top), t[top]);
    }
    if let Some(h) = add[top] {
        b.cx(h, t[top]);
    }
    for i in (i0..n - 1).rev() {
        match add[i] {
            Some(h) if i == i0 => {
                b.and_u(t[i], h, c(i + 1));
                b.cx(h, t[i]);
            }
            Some(h) => {
                b.cx(c(i), h);
                b.cx(c(i), c(i + 1));
                b.and_u(h, t[i], c(i + 1));
                b.cx(c(i), h);
                b.cx(h, t[i]);
            }
            None => {
                b.and_u(t[i], c(i), c(i + 1));
                b.cx(c(i), t[i]);
            }
        }
    }
}

/// Lanes of the 4-fold window (from lane 4): (c - 1)/16 = 61 + 2^28 times a 4-bit H, plus 32 lanes of headroom.
const W4: usize = 64;

/// t += val(vars) mod 2^|t| (sub: t -= val(vars)), val a classical table over the assignments of the few control
/// qubits `vars` (index bit i = vars[i]; val(0) = 0), the controls outside t. Each addend bit is a Boolean function of
/// the controls: its algebraic normal form's monomials of degree >= 2 are computed once (one AND each,
/// measurement-uncomputed), each bit's function is XORed into a scratch lane by CNOTs (single-variable bits use the
/// control itself), then one logical-AND carry chain adds them (var_add_pool). Scratch and carries from `pool`.
fn add_table(b: &mut B, pool: &[QubitId], t: &[QubitId], vars: &[QubitId], val: &dyn Fn(usize) -> u128, sub: bool) {
    let nv = vars.len();
    let na = 1usize << nv;
    let w = t.len();
    assert!(w <= 128 && val(0) == 0);
    let anf = |j: usize| -> Vec<usize> {
        let mut f: Vec<u8> = (0..na).map(|a| ((val(a) >> j) & 1) as u8).collect();
        for i in 0..nv {
            for m in 0..na {
                if m & (1 << i) != 0 {
                    f[m] ^= f[m ^ (1 << i)];
                }
            }
        }
        (0..na).filter(|&m| f[m] == 1).collect()
    };
    let bits: Vec<Vec<usize>> = (0..w).map(anf).collect();
    let mut pool: Vec<QubitId> = pool.to_vec();
    let mut mono: std::collections::BTreeMap<usize, QubitId> = std::collections::BTreeMap::new();
    let mut need: std::collections::BTreeSet<usize> =
        bits.iter().flatten().cloned().filter(|m| m.count_ones() >= 2).collect();
    let topbit = |m: usize| 1usize << (usize::BITS - 1 - m.leading_zeros());
    let mut stack: Vec<usize> = need.iter().cloned().collect();
    while let Some(m) = stack.pop() {
        let r = m ^ topbit(m);
        if r.count_ones() >= 2 && need.insert(r) {
            stack.push(r);
        }
    }
    let var = |m: usize, mono: &std::collections::BTreeMap<usize, QubitId>| -> QubitId {
        if m.count_ones() == 1 {
            vars[m.trailing_zeros() as usize]
        } else {
            mono[&m]
        }
    };
    let mut order: Vec<(usize, QubitId, QubitId)> = vec![];
    for &m in &need {
        let tb = topbit(m);
        let (x, y) = (var(m ^ tb, &mono), vars[tb.trailing_zeros() as usize]);
        let q = pool.pop().unwrap();
        b.and_c(x, y, q);
        mono.insert(m, q);
        order.push((m, x, y));
    }
    let mut add: Vec<Option<QubitId>> = vec![None; w];
    let mut built: Vec<(QubitId, Vec<usize>)> = vec![];
    let mut cache: std::collections::BTreeMap<Vec<usize>, QubitId> = std::collections::BTreeMap::new();
    for (j, ms_j) in bits.iter().enumerate() {
        if ms_j.is_empty() {
            continue;
        }
        assert!(!ms_j.contains(&0), "table with a constant addend bit");
        if ms_j.len() == 1 {
            add[j] = Some(var(ms_j[0], &mono));
        } else if let Some(&q) = cache.get(ms_j) {
            add[j] = Some(q);
        } else {
            let q = pool.pop().unwrap();
            for &m in ms_j {
                b.cx(var(m, &mono), q);
            }
            add[j] = Some(q);
            cache.insert(ms_j.clone(), q);
            built.push((q, ms_j.clone()));
        }
    }
    let i0 = add.iter().position(|a| a.is_some()).unwrap_or(w);
    assert!(pool.len() + i0 + 1 >= w, "add_table: pool too small for the carry chain");
    if sub {
        for &q in t {
            b.x(q);
        }
    }
    var_add_pool(b, t, &add, &pool);
    if sub {
        for &q in t {
            b.x(q);
        }
    }
    for (q, ms_j) in built.iter().rev() {
        for &m in ms_j {
            b.cx(var(m, &mono), *q);
        }
    }
    for &(m, x, y) in order.iter().rev() {
        b.and_u(x, y, mono[&m]);
    }
}

/// Adds (sub: subtracts) H (c - 1) into z[4..4 + W4), H = the 4-bit value in `hq` (LSB first, outside the window):
/// (c - 1) / 16 = 61 + 2^28, so the addend's bits are functions of H (add_table).
fn fold4(b: &mut B, ms: &Ms, z: &[QubitId], hq: [QubitId; 4], sub: bool) {
    let val = |h: usize| -> u128 { (h as u128) * ((C as u128 - 1) >> 4) };
    add_table(b, &ms.r, &z[4..4 + W4], &hq, &val, sub);
}

/// Window of the merged fold (lane 0 up): |delta| c < 2^35 plus 31 lanes of carry headroom.
const WM: usize = 66;

/// z <- (z + (-1)^s y) / 2 mod p (signed_modadd then mod_halve, one fold for both). The raw add (in the
/// complemented domain where s is set) leaves z~ (flipped back) and its carry k; the reduced sum is
/// u = z~ + (-1)^s k c, its halving (u + h p) / 2 with h = u_0 = z~_0 ^ k is (z~ + delta c) / 2 + h 2^255 with
/// delta = (-1)^s k - h in {-2..1}: one table add of delta c over lanes 0..WM (lane 0 ends 0), then the relabel puts
/// h on the freed top lane. k is erased as signed_modadd's, by the top-lane compare on u's top 32 bits = the halved
/// value's lanes 223..254 (complemented domain).
pub fn signed_modadd_halve(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], s: Option<QubitId>) {
    if ms.r.len() < TABLE_POOL {
        signed_modadd(b, ms, z, y, s);
        mod_halve(b, ms, z);
        return;
    }
    let flip = |b: &mut B, z: &[QubitId]| {
        if let Some(q) = s {
            for &l in z {
                b.cx(q, l);
            }
        }
    };
    flip(b, z);
    add_flag_u(b, ms, z, y);
    flip(b, z);
    let (hq, pool) = ms.r.split_last().unwrap();
    let hq = *hq;
    b.cx(z[0], hq);
    b.cx(ms.k, hq);
    let mut vars = vec![ms.k, hq];
    if let Some(q) = s {
        vars.push(q);
    }
    let val = |a: usize| -> u128 {
        let (k, h, sg) = ((a & 1) as i128, ((a >> 1) & 1) as i128, (a >> 2) & 1 == 1);
        let d = if sg { -k } else { k } - h;
        let m = (1u128 << WM) - 1;
        ((d * C as i128).rem_euclid(1i128 << WM) as u128) & m
    };
    add_table(b, pool, &z[..WM], &vars, &val, false);
    z.rotate_left(1);
    b.cx(hq, z[255]);
    b.cx(z[255], hq);
    // erase k: [w' < y + s] on the top 32 lanes, w' = u in the complemented domain, u's bits 224..255 = z[223..255)
    let ut: Vec<QubitId> = z[223..255].to_vec();
    let yt = &y[256 - CMPT..];
    flip(b, &ut);
    for &q in &ut {
        b.x(q);
    }
    b.carry_erase_cin(yt, &ut, ms.one, ms.k, pool, s);
    for &q in &ut {
        b.x(q);
    }
    flip(b, &ut);
}

/// z <- 16 z mod p in place: the top 4 lanes are relabeled to the bottom (16 z_low + H), then H (c - 1) is added
/// (c - 1 = 0 mod 16, so lanes 0..3 keep H). One fold for four doublings.
pub fn mod_double4(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>) {
    z.rotate_right(4);
    let hq = [z[0], z[1], z[2], z[3]];
    fold4(b, ms, z, hq, false);
}

/// Inverse of mod_double4 (z <- z / 16 mod p): c = 1 mod 16, so z + m p = 0 mod 16 for m = z mod 16; subtract
/// m (c - 1) (lanes >= 4, m's lanes kept) and relabel m's 4 lanes to the top: (z - m c) / 16 + m 2^252.
pub fn mod_halve4(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>) {
    let hq = [z[0], z[1], z[2], z[3]];
    fold4(b, ms, z, hq, true);
    z.rotate_left(4);
}

/// z <- 2 (z + (-1)^s y) mod p (signed_modadd then mod_double, one fold for both). After the raw add (z~ and its
/// carry k), the doubling's relabel moves z~'s top bit h to lane 0; the reduced sum u = z~ + (-1)^s k c doubles to
/// (2 z~_low + h) + h (c - 1) + 2 (-1)^s k c, so one table add of (-1)^s k c + h (c - 1)/2 over lanes 1..WM + 1
/// (lane 0 keeps h). h is u's top bit except w.p. ~2^-222. k is erased as signed_modadd's, on u's top 32 bits =
/// lanes 225..255 and lane 0 (complemented domain).
pub fn signed_modadd_double(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], s: Option<QubitId>) {
    if ms.r.len() < TABLE_POOL {
        signed_modadd(b, ms, z, y, s);
        mod_double(b, ms, z);
        return;
    }
    let flip = |b: &mut B, z: &[QubitId]| {
        if let Some(q) = s {
            for &l in z {
                b.cx(q, l);
            }
        }
    };
    flip(b, z);
    add_flag_u(b, ms, z, y);
    flip(b, z);
    z.rotate_right(1);
    let mut vars = vec![ms.k, z[0]];
    if let Some(q) = s {
        vars.push(q);
    }
    let val = |a: usize| -> u128 {
        let (k, h, sg) = ((a & 1) as i128, ((a >> 1) & 1) as i128, (a >> 2) & 1 == 1);
        let d = if sg { -k } else { k } * C as i128 + h * ((C as i128 - 1) >> 1);
        (d.rem_euclid(1i128 << WM) as u128) & ((1u128 << WM) - 1)
    };
    add_table(b, &ms.r, &z[1..1 + WM], &vars, &val, false);
    let mut ut: Vec<QubitId> = z[225..256].to_vec();
    ut.push(z[0]);
    let yt = &y[256 - CMPT..];
    flip(b, &ut);
    for &q in &ut {
        b.x(q);
    }
    b.carry_erase_cin(yt, &ut, ms.one, ms.k, &ms.r, s);
    for &q in &ut {
        b.x(q);
    }
    flip(b, &ut);
}

/// Pool lanes the table folds need (a 66-lane carry chain plus monomial and function scratch); smaller pools take
/// the one-fold-per-step routines.
pub const TABLE_POOL: usize = 90;

/// z <- 2^n z mod p (four at a time).
pub fn mod_double_n(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, n: usize) {
    if ms.r.len() < TABLE_POOL {
        for _ in 0..n {
            mod_double(b, ms, z);
        }
        return;
    }
    for _ in 0..n / 4 {
        mod_double4(b, ms, z);
    }
    for _ in 0..n % 4 {
        mod_double(b, ms, z);
    }
}

/// z <- 2^-n z mod p (four at a time).
pub fn mod_halve_n(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, n: usize) {
    if ms.r.len() < TABLE_POOL {
        for _ in 0..n {
            mod_halve(b, ms, z);
        }
        return;
    }
    for _ in 0..n / 4 {
        mod_halve4(b, ms, z);
    }
    for _ in 0..n % 4 {
        mod_halve(b, ms, z);
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
/// end (~2^-160). `tq` (>= |hi| + 10 clean lanes, 72 for frogtail) holds hi * 977 meanwhile.
pub fn reduce_hi(b: &mut B, r: &[QubitId], tq: &[QubitId], pool: &[QubitId]) {
    let (lo, hi) = (&r[..256], &r[256..]);
    let h = hi.len();
    assert!(h + 10 <= tq.len() && tq.len() <= 224);
    add_sext(b, hi, &lo[32..], pool);
    b.begin();
    for j in 0..tq.len() {
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
    // doublings fused with the preceding add (signed_modadd_double): D, (A D)..., A
    mod_double(b, ms, z);
    for k in (0..n - 1).rev() {
        b.x(a[k + 1]);
        if k > 0 {
            signed_modadd_double(b, ms, z, y, Some(a[k + 1]));
        } else {
            signed_modadd(b, ms, z, y, Some(a[k + 1]));
        }
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
        signed_modadd_halve(b, ms, z, y, Some(a[k + 1]));
    }
    for i in 0..256 {
        b.cx(y[i], z[i]);
    }
}

/// z += y^2 mod p (any z), y restored: z is halved n - 1 times, then the signed-digit Horner of `product` runs on
/// z with y's own lanes as the digit signs. `tmp` is a clean qubit (holds !y_0 for the a_0 fix).
pub fn square_acc(b: &mut B, ms: &Ms, z: &mut Vec<QubitId>, y: &[QubitId], tmp: QubitId) {
    let n = y.len();
    mod_halve_n(b, ms, z, n - 1);
    // each add fused with the following doubling: (A D)..., A
    signed_modadd_double(b, ms, z, y, None);
    for k in (0..n - 1).rev() {
        b.cx(y[k + 1], tmp);
        b.x(tmp);
        if k > 0 {
            signed_modadd_double(b, ms, z, y, Some(tmp));
        } else {
            signed_modadd(b, ms, z, y, Some(tmp));
        }
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
            signed_modadd_halve(b, ms, z, y, Some(c[k + 1]));
        } else if signed {
            b.x(c[m - 1]);
            signed_modadd_halve(b, ms, z, y, Some(c[m - 1]));
            b.x(c[m - 1]);
        } else {
            signed_modadd_halve(b, ms, z, y, Some(ms.one));
        }
    }
    for _ in m..tt {
        mod_halve(b, ms, z);
    }
}

/// Uncompute of product_tail_neg_s's result (z as that call left it, vector order included): the tt - m trailing
/// halvings and steps m-1..k0 run backwards as forward operations (a doubling, then the opposite signed add), so their
/// measured erases stay measured; the start and steps 0..k0-1, where a partial sum can be exactly 0 (an addition
/// would then leave the non-canonical p; a zero at step k has probability ~2^-k), run as the inverse of their
/// hybrid-ladder recording. z ends |0>, in the vector order the compute started from.
#[allow(clippy::too_many_arguments)]
pub fn product_tail_neg_s_uncompute(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
    signed: bool,
    k0: usize,
) {
    let m = c.len();
    assert!(k0 < m && tt >= m);
    for _ in m..tt {
        mod_double(b, ms, z);
    }
    // D, (A D)..., A: each add fused with the next step's doubling
    mod_double(b, ms, z);
    for k in (k0..m).rev() {
        let fused = k > k0;
        let mut add = |b: &mut B, z: &mut Vec<QubitId>, s: Option<QubitId>| {
            if fused {
                signed_modadd_double(b, ms, z, y, s);
            } else {
                signed_modadd(b, ms, z, y, s);
            }
        };
        if k + 1 < m {
            b.x(c[k + 1]);
            add(b, z, Some(c[k + 1]));
            b.x(c[k + 1]);
        } else if signed {
            add(b, z, Some(c[m - 1]));
        } else {
            add(b, z, None);
        }
    }
    let mut za = z.clone();
    za.rotate_right(k0);
    let v0 = za.clone();
    NOCHUNK.with(|f| f.set(true));
    b.begin();
    b.x(c[0]);
    for i in 0..256 {
        b.and_c(c[0], y[i], za[i]);
    }
    b.x(c[0]);
    for k in 0..k0 {
        signed_modadd_halve(b, ms, &mut za, y, Some(c[k + 1]));
    }
    let r = b.end();
    NOCHUNK.with(|f| f.set(false));
    assert_eq!(&za, z);
    b.play(&r, true);
    *z = v0;
}

/// product_tail_neg_s for an unsigned digit source `c` that is X-measured as it is used (bit c_k into `mbits[k]`
/// right after its last use, the phase left for the caller's recompute to fix): every measured lane joins the carry
/// pool of the later adds. Emitted directly (not recordable).
#[allow(clippy::too_many_arguments)]
pub fn product_tail_neg_stream(
    b: &mut B,
    ms: &Ms,
    z: &mut Vec<QubitId>,
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
    mbits: &[crate::circuit::BitId],
) {
    let m = c.len();
    assert!(tt >= m);
    let mut ms2 = Ms { k: ms.k, r: ms.r.clone(), one: ms.one };
    b.x(c[0]);
    for i in 0..256 {
        b.and_c(c[0], y[i], z[i]);
    }
    b.x(c[0]);
    b.hmr_to(c[0], mbits[0]);
    ms2.r.push(c[0]);
    for k in 0..m {
        if k + 1 < m {
            signed_modadd_halve(b, &ms2, z, y, Some(c[k + 1]));
            b.hmr_to(c[k + 1], mbits[k + 1]);
            ms2.r.push(c[k + 1]);
        } else {
            signed_modadd_halve(b, &ms2, z, y, Some(ms.one));
        }
    }
    mod_halve_n(b, &ms2, z, tt - m);
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
