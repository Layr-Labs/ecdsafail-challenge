//! frogdrop point addition: (x, y) += (ox, oy) on secp256k1, affine, in place, with the 3-of-4 Euclid traversal
//! (frogdrop_col) as the inversion core. Same outer structure as froghop-double's point addition (two divisions,
//! measurement-based erasure of dy and lambda after Luo et al. / gnuchev):
//!
//!   dx = x - ox, dy = y - oy
//!   division 1:  forward traversal on dx (passenger dy) -> inv = 1/dx;  lambda = inv * dy;  measure dy away;
//!                inverse traversal -> dx;  recompute dy = lambda * dx, fix its phase, uncompute
//!   x:  dx' = lambda^2 - dx - 3 ox;   y:  ndy = -lambda * dx';  measure lambda away
//!   division 2:  forward traversal on dx' -> inv';  recompute lambda = -ndy * inv', fix its phase, uncompute;
//!                inverse traversal -> dx'
//!   x3 = dx' + ox,  y3 = ndy - oy

use super::builder::{B, G};
use super::frogdrop_col::{column, pool_size, traversal_end, ColPar, ColScr, Fd};
use super::frogdrop_sched::{from_text, Sched, L0};
use super::modp_frogdrop::{ctrl_neg, ctrl_neg_nm, load_bits, mac, modadd, modsub, product, product_nf, Ms};
use crate::circuit::{BitId, QubitId};

pub const SCHED_FROGDROP: &str = include_str!("sched_frogdrop.txt");

/// Machine constants.
pub const N: usize = 288;
pub const NQ: usize = 138;
pub const K: usize = 29;
pub const KP: usize = 30;
pub const QB: usize = 24;
pub const TOT: usize = 83;
pub const TAIL: usize = 40;
pub const EMAX: usize = 28;
/// idle counter bits (max idle columns C - min(N - 1) ~ 103 < 2^7)
pub const CNTB: usize = 7;
/// size registers sy, sx (pair values have <= NQ < 2^8 bits)
pub const SW: usize = 8;
/// clean qubits added to the column pool for logical-AND carries in the map's adds (peak = 774 + AND_Q)
pub const AND_Q: usize = 1;
pub fn and_qubits() -> usize {
    AND_Q
}

pub(crate) fn ck(b: &B, name: &str) {
    if std::env::var("FROGDROP_CK").is_ok() {
        eprintln!("ck {:24} live {} peak {} peak_op {} ops {} tof {}", name, b.live, b.peak, b.peak_op, b.ops.len(),
                  b.tof);
    }
}

fn base_par() -> ColPar {
    ColPar { n: N, nq: NQ, h: N - 257, k: K, kp: KP, qb: QB, tot: TOT, sz: (0, 0), sy: (0, 0), smax: (0, 0), m: 0,
             tail: TAIL, emax: EMAX, hr: false, ht: false, sw: false, l0: L0, swl: (0, 0), dn: false, fin: false,
             nomap: false, tt: false }
}

/// Per-column parameters from the schedule (envelopes clamped to the machine).
pub fn col_pars(sc: &Sched) -> (Vec<ColPar>, Option<ColPar>, ColPar) {
    let cl = |r: (usize, usize), hi: usize| (r.0.min(hi), r.1.min(hi));
    let cols = sc.cols.iter().enumerate().map(|(i, e)| {
        let mut c = base_par();
        c.tt = i == 1; // j = 2: T = t = 1 when q_1 = 1 (dx > p/2, unreflected)
        c.hr = e.hr;
        c.ht = e.ht;
        c.sw = e.sw;
        c.dn = e.dn;
        c.fin = e.fin;
        c.sz = cl(e.sz, 256);
        c.sy = cl(e.sy, 255);
        c.smax = cl(e.smax, NQ);
        c.m = c.smax.1;
        c.swl = (e.swl.0.min(NQ), e.swl.1.min(NQ));
        c
    }).collect();
    let mut b0 = base_par();
    b0.smax = cl(sc.b0, NQ);
    b0.m = b0.smax.1;
    let mut last = base_par();
    last.ht = true;
    last.nomap = true;
    last.sz = cl(sc.lsz, 255);
    last.sy = (1, 1);
    (cols, Some(b0), last)
}

/// A traversal's state between its forward and inverse runs.
pub(crate) struct Trav {
    pub(crate) fd: Fd,
    pub(crate) pool: Vec<QubitId>,
    /// qubits released after the forward run (|0> for every shot), re-acquired before the inverse
    parked: Vec<QubitId>,
}

/// Every Fd/pool qubit that is |0> after the forward run's cleanup: all but ring[0..256] (t_{N-1} in [0, 255),
/// the counter's top bit parked in lane 255) and cnt[0..6].
fn parked_of(t: &Trav) -> Vec<QubitId> {
    let mut v: Vec<QubitId> = t.fd.ring[256..].to_vec();
    v.extend(&t.fd.q);
    v.extend(&t.fd.sy);
    v.extend(&t.fd.sx);
    v.push(t.fd.ph);
    v.push(t.fd.cnt[CNTB - 1]);
    v.extend(&t.pool);
    v
}

/// Final constants of every shot: ring top lane 1, sy = 1, ph = 1. Then the counter's top bit moves into ring lane
/// 255 (t_{N-1} <= p / 2 < 2^255 leaves it 0).
fn final_consts(b: &mut B, fd: &Fd) {
    b.x(fd.ring[N - 1]);
    b.x(fd.sy[0]);
    b.x(fd.ph);
    b.swap(fd.cnt[CNTB - 1], fd.ring[255]);
}

/// One column (or the end) recorded, so the inverse traversal can replay it backwards.
fn rec_col(b: &mut B, fd: &mut Fd, cp: &ColPar, pool: &[QubitId], dirty: &[QubitId]) -> Vec<G> {
    let sc = ColScr::carve(pool, &fd.sx, dirty, KP, QB, TAIL);
    b.begin();
    column(b, fd, cp, &sc);
    b.end()
}

/// Forward traversal on x' (reflected below 2^255, in `xq`): returns the traversal state and the 256 lanes holding
/// +-t_{N-1} (sign fixed by the caller).
pub(crate) fn trav_forward(b: &mut B, xq: &[QubitId], dirty: &[QubitId]) -> Trav {
    let mut ring: Vec<QubitId> = xq.to_vec();
    ring.extend(b.alloc_n(N - 256));
    let fd = Fd { ring, q: b.alloc_n(NQ), sy: b.alloc_n(SW), sx: b.alloc_n(SW), ph: b.alloc(), cnt: b.alloc_n(CNTB) };
    let pool = b.alloc_n(pool_size(KP, QB, SW));
    let mut t = Trav { fd, pool, parked: vec![] };
    // HR(1): Z = x', Q = t_0 = 0, top = t_1 = 1, sy = 1
    b.x(t.fd.ring[N - 1]);
    b.x(t.fd.sy[0]);
    ck(b, "trav pre");
    let (cols, b0, last) = col_pars(&from_text(SCHED_FROGDROP));
    for cp in &cols {
        let sc = ColScr::carve(&t.pool, &t.fd.sx, dirty, KP, QB, TAIL);
        column(b, &mut t.fd, cp, &sc);
    }
    let pool = t.pool.clone();
    let carve = |sx: &[QubitId]| ColScr::carve(&pool, sx, dirty, KP, QB, TAIL);
    traversal_end(b, &mut t.fd, b0.as_ref(), &last, &carve);
    ck(b, "trav post");
    final_consts(b, &t.fd);
    t.parked = parked_of(&t);
    b.free_n(&t.parked);
    t
}

/// Exact inverse of trav_forward (re-acquires the parked qubits, replays every column backwards, frees all).
fn trav_inverse(b: &mut B, mut t: Trav, dirty: &[QubitId]) {
    for &q in &t.parked {
        b.acquire(q);
    }
    final_consts(b, &t.fd);
    let (cols, b0, last) = col_pars(&from_text(SCHED_FROGDROP));
    // the end: forward names at its start; traversal_end swaps sy/sx once when b0 is present
    {
        let mut fd = Fd { ring: t.fd.ring.clone(), q: t.fd.q.clone(), sy: t.fd.sy.clone(), sx: t.fd.sx.clone(),
                          ph: t.fd.ph, cnt: t.fd.cnt.clone() };
        if b0.is_some() {
            std::mem::swap(&mut fd.sy, &mut fd.sx);
        }
        let start = (fd.sy.clone(), fd.sx.clone());
        let pool = t.pool.clone();
        let carve = |sx: &[QubitId]| ColScr::carve(&pool, sx, dirty, KP, QB, TAIL);
        b.begin();
        traversal_end(b, &mut fd, b0.as_ref(), &last, &carve);
        let r = b.end();
        b.play(&r, true);
        t.fd.sy = start.0;
        t.fd.sx = start.1;
    }
    for cp in cols.iter().rev() {
        // names at the column's start: every mapped column swapped them once
        if !cp.nomap {
            std::mem::swap(&mut t.fd.sy, &mut t.fd.sx);
        }
        let start = (t.fd.sy.clone(), t.fd.sx.clone());
        let r = rec_col(b, &mut t.fd, cp, &t.pool, dirty);
        b.play(&r, true);
        t.fd.sy = start.0;
        t.fd.sx = start.1;
    }
    b.x(t.fd.ring[N - 1]);
    b.x(t.fd.sy[0]);
    b.free_n(&t.fd.ring[256..]);
    b.free_n(&t.fd.q);
    b.free_n(&t.fd.sy);
    b.free_n(&t.fd.sx);
    b.free(t.fd.ph);
    b.free_n(&t.fd.cnt);
    b.free_n(&t.pool);
}

/// Everything a division needs between its forward and inverse traversal.
struct Div {
    t: Trav,
}

/// 1/dx = (-1)^N t_{N-1} with N = C + 2 - cnt (cnt = 1 + idle columns): negate iff cnt[0] ^ (C & 1). Returns the
/// control (qubit, flip) meaning "negate iff qubit ^ flip".
fn sign_ctl(t: &Trav) -> (QubitId, bool) {
    let c = from_text(SCHED_FROGDROP).cols.len();
    (t.fd.cnt[0], c % 2 == 1)
}

/// Forward traversal on dx (in `xq`): the inverse's magnitude t_{N-1} sits in xq[0..255].
fn div_forward(b: &mut B, xq: &[QubitId], dirty: &[QubitId]) -> (Div, Vec<QubitId>) {
    let t = trav_forward(b, xq, dirty);
    let inv: Vec<QubitId> = t.fd.ring[0..255].to_vec();
    ck(b, "div_forward end");
    (Div { t }, inv)
}

fn div_inverse(b: &mut B, dv: Div, dirty: &[QubitId]) {
    trav_inverse(b, dv.t, dirty);
}

/// z = a * y (mod p), negated iff neg.0 ^ neg.1 (when given), recorded.
fn rec_product_s(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &[QubitId], neg: Option<(QubitId, bool)>)
                 -> Vec<G> {
    b.begin();
    let mut zz = z.to_vec();
    product(b, ms, &mut zz, a, y);
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if let Some((c, flip)) = neg {
        if flip { b.x(c); }
        ctrl_neg(b, ms, z, Some(c), y);
        if flip { b.x(c); }
    }
    b.end()
}

/// rec_product_s with no clean scratch (flag-free modular adds): for the products made while a traversal is parked.
fn rec_product_nf(b: &mut B, z: &[QubitId], a: &[QubitId], y: &[QubitId], neg: Option<(QubitId, bool)>) -> Vec<G> {
    b.begin();
    let mut zz = z.to_vec();
    product_nf(b, &mut zz, a, y);
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if let Some((c, flip)) = neg {
        if flip { b.x(c); }
        ctrl_neg_nm(b, z, Some(c), y);
        if flip { b.x(c); }
    }
    b.end()
}

/// z = a * y (mod p) recorded, so the caller can uncompute it.
fn rec_product(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &[QubitId], negate: bool) -> Vec<G> {
    b.begin();
    let mut zz = z.to_vec();
    product(b, ms, &mut zz, a, y);
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if negate {
        ctrl_neg(b, ms, z, None, y);
    }
    b.end()
}

pub fn point_add(b: &mut B) -> (Vec<QubitId>, Vec<QubitId>) {
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    b.declare_qubits(0, &x);
    b.declare_qubits(1, &y);
    let ox: Vec<BitId> = b.declare_bits(2, 256);
    let oy: Vec<BitId> = b.declare_bits(3, 256);

    // dx, dy
    {
        let ms = Ms::alloc(b);
        let t = b.alloc_n(256);
        load_bits(b, &t, &ox);
        modsub(b, &ms, &x, &t, y[0]);
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t, x[0]);
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }

    // ---------------- division 1
    ck(b, "-- division 1");
    let (dv, inv) = div_forward(b, &x, &y);
    let sq = sign_ctl(&dv.t);
    let m1 = b.fresh_bits(256);
    {
        let z = b.alloc_n(256);
        let r = if and_qubits() == 0 {
            rec_product_nf(b, &z, &inv, &y, Some(sq))
        } else {
            let ms = Ms::alloc(b);
            let r = rec_product_s(b, &ms, &z, &inv, &y, Some(sq));
            ms.release(b);
            r
        };
        b.play(&r, false);
        ck(b, "lambda = inv * dy");
        for i in 0..256 {
            b.hmr_to(y[i], m1[i]);
        }
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }
    div_inverse(b, dv, &y);
    // dy = lambda * dx: recompute, fix the phase of the dy measurement, uncompute
    {
        let ms = Ms::alloc(b);
        let z = b.alloc_n(256);
        let r = rec_product(b, &ms, &z, &y, &x, false);
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m1[i]);
        }
        b.play(&r, true);
        b.free_n(&z);
        ms.release(b);
    }

    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    ck(b, "-- x: dx' = lambda^2 - ");
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, None, &y);
        let t = b.alloc_n(256);
        for i in 0..256 {
            b.cx(y[i], t[i]);
        }
        let mut yy = y.clone();
        mac(b, &ms, &x, &t, &mut yy);
        assert_eq!(yy, y);
        for i in 0..256 {
            b.cx(y[i], t[i]);
        }
        load_bits(b, &t, &ox);
        for _ in 0..3 {
            modsub(b, &ms, &x, &t, y[0]);
        }
        load_bits(b, &t, &ox);
        b.free_n(&t);
        ms.release(b);
    }
    // ---------------- ndy = -lambda * dx', measure lambda away
    ck(b, "-- ndy = -lambda * dx',");
    let m2 = b.fresh_bits(256);
    {
        let ms = Ms::alloc(b);
        let z = b.alloc_n(256);
        let r = rec_product(b, &ms, &z, &y, &x, true);
        b.play(&r, false);
        ms.release(b);
        for i in 0..256 {
            b.hmr_to(y[i], m2[i]);
        }
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }

    // ---------------- division 2: recompute lambda = -ndy / dx' to fix its phase
    ck(b, "-- division 2: recomput");
    let (dv, inv) = div_forward(b, &x, &y);
    let (sqq, sqf) = sign_ctl(&dv.t);
    {
        let z = b.alloc_n(256);
        if and_qubits() == 0 {
            let r = rec_product_nf(b, &z, &inv, &y, Some((sqq, !sqf)));
            b.play(&r, false);
            for i in 0..256 {
                b.z_if(z[i], m2[i]);
            }
            b.play(&r, true);
        } else {
            let ms = Ms::alloc(b);
            let r = rec_product_s(b, &ms, &z, &inv, &y, Some((sqq, !sqf)));
            b.play(&r, false);
            for i in 0..256 {
                b.z_if(z[i], m2[i]);
            }
            b.play(&r, true);
            ms.release(b);
        }
        b.free_n(&z);
    }
    div_inverse(b, dv, &y);

    // ---------------- x3 = dx' + ox, y3 = ndy - oy
    ck(b, "-- x3 = dx' + ox, y3 = ");
    {
        let ms = Ms::alloc(b);
        let t = b.alloc_n(256);
        load_bits(b, &t, &ox);
        modadd(b, &ms, &x, &t, y[0]);
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t, x[0]);
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }
    // Fiat-Shamir nonce: one X X pair (identity) on qubit NONCE; fixed op count, so a nonce scan re-hashes only
    // the tail
    b.x(QubitId(super::NONCE as u64));
    b.x(QubitId(super::NONCE as u64));
    ck(b, "end");
    (x, y)
}
