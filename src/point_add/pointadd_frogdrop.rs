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
use super::frogdrop_col::{column_pl, pool_size, traversal_end_pl, ColPar, ColScr, Fd};
use super::payload::PlCol;
use super::frogdrop_sched::{from_text, Sched, L0};
use super::modp_frogdrop::{ctrl_neg, ctrl_neg_nm, load_bits, mac, modadd, modsub, product, product_nf, Ms};
use super::field_consume_fifth::product_consume_five_high_clean;
use crate::circuit::{BitId, QubitId};

pub const SCHED_FROGDROP: &str = include_str!("sched_frogdrop.txt");

/// Machine constants.
pub const N: usize = 288;
pub const NQ: usize = 128;
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

pub(crate) fn ck(b: &B, name: &str) {
    if std::env::var("FROGDROP_CK").is_ok() {
        eprintln!("ck {:24} live {} peak {} peak_op {} ops {} tof {}", name, b.live, b.peak, b.peak_op, b.ops.len(),
                  b.tof);
    }
}

fn base_par() -> ColPar {
    ColPar { n: N, nq: NQ, h: N - 257, k: K, kp: KP, qb: QB, tot: TOT, sz: (0, 0), sy: (0, 0), smax: (0, 0), m: 0,
             tail: TAIL, emax: EMAX, hr: false, ht: false, sw: false, l0: L0, swl: (0, 0), dn: false, fin: false,
             nomap: false, tt: false, pht: false, psy: (0, 0), xw: 0, psw: false }
}

/// Per-column parameters from the schedule (envelopes clamped to the machine).
pub fn col_pars(sc: &Sched) -> (Vec<ColPar>, Option<ColPar>, ColPar) {
    let cl = |r: (usize, usize), hi: usize| (r.0.min(hi), r.1.min(hi));
    let cols: Vec<ColPar> = sc.cols.iter().enumerate().map(|(i, e)| {
        let mut c = base_par();
        if i > 0 {
            let pe = &sc.cols[i - 1];
            c.pht = pe.ht;
            c.psy = (pe.sy.0.min(255), pe.sy.1.min(255));
            c.psw = pe.sw;
        }
        c.xw = e.xw;
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
    b0.dn = true; // done shots: the map parks their counter
    b0.smax = cl(sc.b0, NQ);
    b0.m = b0.smax.1;
    let mut last = base_par();
    if let Some(pe) = sc.cols.last() {
        last.pht = pe.ht;
        last.psy = (pe.sy.0.min(255), pe.sy.1.min(255));
    }
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
    // Q keeps R (< 2^26, low lanes) and the idle counter (top lanes)
    v.extend(&t.fd.q[super::payload::KD..NQ - CNTB]);
    v.extend(&t.fd.sy);
    v.extend(&t.fd.sx);
    v.push(t.fd.ph);
    v.extend(&t.pool);
    v
}

/// Final constants of every shot: ring top lane 1, sy = 1, ph = 1. Then the counter's top bit moves into ring lane
/// 255 (t_{N-1} <= p / 2 < 2^255 leaves it 0).
fn final_consts(b: &mut B, fd: &Fd) {
    b.x(fd.ring[N - 1]);
    b.x(fd.sy[0]);
    b.x(fd.ph);
}

/// One column (or the end) recorded, so the inverse traversal can replay it backwards.
fn rec_col(b: &mut B, fd: &mut Fd, cp: &ColPar, pool: &[QubitId], dirty: &[QubitId], pl: Option<&PlCol>) -> Vec<G> {
    let sc = ColScr::carve(pool, &fd.sx, dirty, KP, QB, TAIL);
    b.begin();
    column_pl(b, fd, cp, &sc, pl);
    b.end()
}

/// Payload context on the traversal pool: digit / narrowing scratch pool[10..64] (+ sx at stage 2.5), transition
/// lanes pool[10..15] (HR, after P) and pool[11..15] (HT, unused), ring top lanes as borrowed helpers.
pub(crate) fn pl_col(p: &[QubitId], fd: &Fd, pool: &[QubitId]) -> PlCol {
    PlCol { p: p.to_vec(), free: pool[10..].to_vec(), mid_hr: pool[10..15].to_vec(), mid_ht: pool[11..15].to_vec(),
            dirty: fd.ring[N - 28..].to_vec(), obs: vec![] }
}

/// Forward traversal on x' (reflected below 2^255, in `xq`): returns the traversal state and the 256 lanes holding
/// +-t_{N-1} (sign fixed by the caller).
pub(crate) fn trav_forward(b: &mut B, xq: &[QubitId], dirty: &[QubitId]) -> Trav {
    trav_forward_pl(b, xq, dirty, None)
}

/// trav_forward with the payload register `pl` (NP lanes: d = dy, W = 0 on entry; after the end column W_{last+1}
/// in offset form, offset bit at lane 1).
pub(crate) fn trav_forward_pl(b: &mut B, xq: &[QubitId], dirty: &[QubitId], pl: Option<&[QubitId]>) -> Trav {
    let mut ring: Vec<QubitId> = xq.to_vec();
    ring.extend(b.alloc_n(N - 256));
    let q = b.alloc_n(NQ);
    let cnt = q[NQ - CNTB..].to_vec();
    let fd = Fd { ring, q, sy: b.alloc_n(SW), sx: b.alloc_n(SW), ph: b.alloc(), cnt };
    let pool = b.alloc_n(pool_size(KP, QB, SW));
    let mut t = Trav { fd, pool, parked: vec![] };
    // HR(1): Z = x', Q = t_0 = 0, top = t_1 = 1, sy = 1
    b.x(t.fd.ring[N - 1]);
    b.x(t.fd.sy[0]);
    ck(b, "trav pre");
    let (cols, b0, last) = col_pars(&from_text(SCHED_FROGDROP));
    let plc = pl.map(|p| pl_col(p, &t.fd, &t.pool));
    for cp in &cols {
        let sc = ColScr::carve(&t.pool, &t.fd.sx, dirty, KP, QB, TAIL);
        column_pl(b, &mut t.fd, cp, &sc, plc.as_ref());
    }
    let pool = t.pool.clone();
    let carve = |sx: &[QubitId]| ColScr::carve(&pool, sx, dirty, KP, QB, TAIL);
    traversal_end_pl(b, &mut t.fd, b0.as_ref(), &last, &carve, plc.as_ref());
    ck(b, "trav post");
    final_consts(b, &t.fd);
    t.parked = parked_of(&t);
    b.free_n(&t.parked);
    t
}

/// Exact inverse of trav_forward (re-acquires the parked qubits, replays every column backwards, frees all).
fn trav_inverse(b: &mut B, t: Trav, dirty: &[QubitId]) {
    trav_inverse_pl(b, t, dirty, None)
}

/// Exact inverse of trav_forward_pl (with `pl`: replays the payload too).
pub(crate) fn trav_inverse_pl(b: &mut B, mut t: Trav, dirty: &[QubitId], pl: Option<&[QubitId]>) {
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
        let plc = pl.map(|p| pl_col(p, &fd, &t.pool));
        b.begin();
        traversal_end_pl(b, &mut fd, b0.as_ref(), &last, &carve, plc.as_ref());
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
        let plc = pl.map(|p| pl_col(p, &t.fd, &t.pool));
        let r = rec_col(b, &mut t.fd, cp, &t.pool, dirty, plc.as_ref());
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

/// Parked-traversal product consuming y's top five bits in z[251..256].
/// On entry z[..251] is clean and ylow is the original y[..251]. On exit z
/// is the signed full product while ylow is preserved. Inverse replay restores
/// all five consumed top bits. The explicit clean flag is zero at both ends.
/// Sign borrows only ylow; scaling may temporarily borrow and restore source lanes.
/// The consumed top wires are outputs and are never borrowed.
fn rec_product_consume(b: &mut B, z: &[QubitId], a: &[QubitId], ylow: &[QubitId],
                       neg: Option<(QubitId, bool)>, clean: QubitId) -> Vec<G> {
    assert_eq!(z.len(), 256);
    assert_eq!(a.len(), 255);
    assert_eq!(ylow.len(), 251);
    assert!(ylow.iter().all(|q| !z.contains(q)));
    assert!(!z.contains(&clean) && !a.contains(&clean) && !ylow.contains(&clean));
    b.begin();
    let mut zz = z.to_vec();
    product_consume_five_high_clean(b, &mut zz, a, ylow, clean);
    // Modular doubling may relabel the product lanes. Restore the declared physical
    // output order before conditional sign, measurement phase, or partial transfer.
    let mut pos = zz;
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if let Some((c, flip)) = neg {
        if flip { b.x(c); }
        ctrl_neg_nm(b, z, Some(c), ylow);
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
    // The top five dy bits are reversibly consumed into the product's top wires.
    // Only the preserved low 251 dy bits need measurement erasure and phase repair.
    let m1 = b.fresh_bits(251);
    {
        let zlow = b.alloc_n(251);
        let clean = b.alloc();
        let mut z = zlow.clone();
        z.extend_from_slice(&y[251..256]);
        let r = rec_product_consume(b, &z, &inv, &y[..251], Some(sq), clean);
        b.play(&r, false);
        ck(b, "lambda = inv * dy");
        for i in 0..251 {
            b.hmr_to(y[i], m1[i]);
        }
        for i in 0..251 {
            b.swap(zlow[i], y[i]);
        }
        b.free_n(&zlow);
        b.free(clean);
    }
    div_inverse(b, dv, &y);
    // dy = lambda * dx: recompute, fix the phase of the dy measurement, uncompute
    {
        let ms = Ms::alloc(b);
        let z = b.alloc_n(256);
        let r = rec_product(b, &ms, &z, &y, &x, false);
        b.play(&r, false);
        for i in 0..251 {
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
        let zlow = b.alloc_n(251);
        let clean = b.alloc();
        let mut z = zlow.clone();
        z.extend_from_slice(&y[251..256]);
        let r = rec_product_consume(b, &z, &inv, &y[..251], Some((sqq, !sqf)), clean);
        b.play(&r, false);
        // All 256 lambda bits were measured; the consumed-input product exposes
        // all 256 recomputed bits. Its inverse then restores all five original ndy top bits.
        for i in 0..256 {
            b.z_if(z[i], m2[i]);
        }
        b.play(&r, true);
        b.free_n(&zlow);
        b.free(clean);
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

// ---------------------------------------------------------------------------------------------------------------
// Payload-division shell (no product register): four traversals.
//   T1: forward traversal on dx carrying the payload (y = dy -> W), conversion W -> lambda
//   T2: inverse traversal without payload (x back to dx)
//   x: dx' = lambda^2 - dx - 3 ox by an in-place squaring Horner (x <- -x / 2^256, then x = 2x + lambda_i lambda)
//   T3: forward traversal on dx' without payload; conversion lambda -> W (inverse)
//   T4: inverse traversal carrying the payload: y = lambda dx' (mod p) (the reversed division multiplies)
//   y3 = -lambda dx' - oy, x3 = dx' + ox

/// lambda from the final payload: W (bit i at p[NP-1-i], in [0, p)), inv = |t_last| (255 lanes), N odd iff
/// cnt0 ^ flip: lambda = N odd ? W + inv + 1 : -(W + inv) (mod p), in place on W. Recorded by the caller.
fn pl_convert(b: &mut B, p: &[QubitId], inv: &[QubitId], cnt0: QubitId, flip: bool, aux: &[QubitId]) {
    use super::payload::NP;
    use super::modp_frogdrop::add_const_exact;
    let w: Vec<QubitId> = (0..256).map(|i| p[NP - 1 - i]).collect();
    let (msk, invtop, dq, one) = (aux[0], aux[1], aux[2], aux[3]);
    let ms = Ms { k: msk };
    let mut inv2: Vec<QubitId> = inv.to_vec();
    inv2.push(invtop);
    // dq = [N odd]
    b.cx(cnt0, dq);
    if flip { b.x(dq); }
    // inv += [N odd] (inv < 2^255: no overflow); borrowed lanes: W and the zero d lane p[0]
    let mut dirt = w.clone();
    dirt.push(p[0]);
    b.begin();
    add_const_exact(b, &inv2, Some(dq), 1, &dirt);
    let incr = b.end();
    b.play(&incr, false);
    b.x(one);
    super::modp_frogdrop::ctrl_modadd(b, &ms, &w, &inv2, one, p[1]);
    b.x(one);
    b.play(&incr, true);
    // N even: negate
    b.x(dq);
    ctrl_neg(b, &ms, &w, Some(dq), &inv2);
    b.x(dq);
    if flip { b.x(dq); }
    b.cx(cnt0, dq);
}

/// x <- lambda^2 - x (mod p) in place (lambda in `lam`, untouched): x <- -x 2^-256, then 256 rounds x = 2x + lam_i lam.
fn sq_horner(b: &mut B, x: &[QubitId], lam: &[QubitId], d: QubitId) {
    let ms = Ms::alloc(b);
    let c = b.alloc();
    ctrl_neg(b, &ms, x, None, lam);
    let mut xv = x.to_vec();
    for _ in 0..256 {
        super::modp_frogdrop::mod_halve(b, &ms, &mut xv, lam);
    }
    for i in (0..256).rev() {
        super::modp_frogdrop::mod_double(b, &ms, &mut xv, lam);
        b.cx(lam[i], c);
        super::modp_frogdrop::ctrl_modadd(b, &ms, &xv, lam, c, d);
        b.cx(lam[i], c);
    }
    assert_eq!(xv, x.to_vec());
    b.free(c);
    ms.release(b);
}

pub fn point_add_pl(b: &mut B) -> (Vec<QubitId>, Vec<QubitId>) {
    use super::payload::NP;
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    b.declare_qubits(0, &x);
    b.declare_qubits(1, &y);
    let ox: Vec<BitId> = b.declare_bits(2, 256);
    let oy: Vec<BitId> = b.declare_bits(3, 256);

    // dx, dy (classical offsets loaded 128 bits at a time)
    let cl_op = |b: &mut B, z: &[QubitId], c: &[BitId], sub: bool, dirty: &[QubitId]| {
        let t = b.alloc_n(128);
        let f = b.alloc_n(3);
        modadd_cl(b, z, c, sub, &t, f[0], f[1], f[2], dirty);
        b.free_n(&f);
        b.free_n(&t);
    };
    cl_op(b, &x, &ox, true, &y);
    cl_op(b, &y, &oy, true, &x);
    // payload register: d = dy in y, W = 0 in three more lanes
    let mut p = y.clone();
    p.extend(b.alloc_n(NP - 256));
    let c = from_text(SCHED_FROGDROP).cols.len();
    let flip = c % 2 == 1;

    // ---------------- T1: forward with payload; lambda
    ck(b, "-- T1");
    // bulengerk round07c: forward row-boundary phases are deferred to the paired inverse traversal
    if std::env::var("FD_NODEFER").is_err() { b.deferred_forward(); }
    let t1 = trav_forward_pl(b, &x, &p, Some(&p));
    if std::env::var("FD_NODEFER").is_err() { b.deferred_suspend(); }
    b.x(p[1]); // offset form -> two's complement W
    {
        let aux = b.alloc_n(4);
        pl_convert(b, &p, &t1.fd.ring[0..255], t1.fd.cnt[0], flip, &aux);
        b.free_n(&aux);
    }
    // ---------------- T2: inverse without payload
    ck(b, "-- T2");
    if std::env::var("FD_NODEFER").is_err() { b.deferred_inverse(); }
    trav_inverse(b, t1, &p);
    if std::env::var("FD_NODEFER").is_err() { b.deferred_finish(); }
    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    ck(b, "-- x: lambda^2");
    let lam: Vec<QubitId> = (0..256).map(|i| p[NP - 1 - i]).collect();
    sq_horner(b, &x, &lam, p[0]);
    for _ in 0..3 {
        cl_op(b, &x, &ox, true, &lam);
    }
    // ---------------- T3: forward without payload; lambda -> W
    ck(b, "-- T3");
    if std::env::var("FD_NODEFER").is_err() { b.deferred_forward(); }
    let t3 = trav_forward_pl(b, &x, &p, None);
    if std::env::var("FD_NODEFER").is_err() { b.deferred_suspend(); }
    {
        let aux = b.alloc_n(4);
        b.begin();
        pl_convert(b, &p, &t3.fd.ring[0..255], t3.fd.cnt[0], flip, &aux);
        let r = b.end();
        b.play(&r, true);
        b.free_n(&aux);
    }
    b.x(p[1]);
    // ---------------- T4: inverse with payload: d = lambda dx'
    ck(b, "-- T4");
    if std::env::var("FD_NODEFER").is_err() { b.deferred_inverse(); }
    trav_inverse_pl(b, t3, &p, Some(&p));
    if std::env::var("FD_NODEFER").is_err() { b.deferred_finish(); }
    b.free_n(&p[256..]);
    // ---------------- y3 = -d - oy, x3 = dx' + ox
    ck(b, "-- x3, y3");
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &y, None, &x);
        ms.release(b);
    }
    cl_op(b, &x, &ox, false, &y);
    cl_op(b, &y, &oy, true, &x);
    b.x(QubitId(super::NONCE as u64));
    b.x(QubitId(super::NONCE as u64));
    ck(b, "end");
    (x, y)
}

/// z <- z - c (sub) or z + c (mod p, lazy reduction as the shell's other modular adds) for a classical 256-bit c
/// (bits of an input register), with a 128-lane loading register `t`, flags `fb` (half carry/borrow) and `fk`
/// (overflow), carry-in `c0` (all |0>), and >= 65 borrowed lanes `dirty` outside z/t/flags.
fn modadd_cl(b: &mut B, z: &[QubitId], c: &[BitId], sub: bool, t: &[QubitId], fb: QubitId, fk: QubitId, c0: QubitId,
             dirty: &[QubitId]) {
    use super::arith::{down_m, up_m, Dm};
    assert!(z.len() == 256 && c.len() == 256 && t.len() == 128);
    let (zl, zh) = (&z[..128], &z[128..]);
    let (cl, ch) = (&c[..128], &c[128..]);
    // flag ^= carry of (T~ + t + cin) (cmpl: borrow of T - t - cin) with optional write
    let half = |b: &mut B, tt: &[QubitId], cb: &[BitId], cin: QubitId, flag: QubitId, cmpl: bool, write: bool| {
        load_bits(b, t, cb);
        let u = up_m(b, tt, t, cin, cmpl);
        b.play(&u, false);
        b.cx(t[127], flag);
        let d = down_m(b, tt, t, cin, if write { Dm::Sum } else { Dm::Restore }, cmpl);
        b.play(&d, false);
        if !write && cmpl {
            // Restore mode re-complements nothing: up_m complemented tt, down_m(Restore, cmpl) undoes it
        }
        load_bits(b, t, cb);
    };
    let ms = Ms { k: fk };
    // z +-= c mod 2^256: fb = low carry/borrow, fk = overall
    half(b, zl, cl, c0, fb, sub, true);
    half(b, zh, ch, fb, fk, sub, true);
    // erase fb: add: fb = borrow(z_lo' - c_lo); sub: fb = carry(z_lo' + c_lo)
    half(b, zl, cl, c0, fb, !sub, false);
    // reduce: add C (add) / subtract C (sub) where fk
    if sub {
        b.begin();
        super::modp_frogdrop::add_small(b, &ms, z, 0, Some(fk), super::modp_frogdrop::C, dirty);
        let r = b.end();
        b.play(&r, true);
    } else {
        super::modp_frogdrop::add_small(b, &ms, z, 0, Some(fk), super::modp_frogdrop::C, dirty);
    }
    // erase fk: add: fk = borrow(z_f - c) (z_f < c); sub: fk = carry(z_f + c) (>= 2^256); both via the halves
    half(b, zl, cl, c0, fb, !sub, false);
    half(b, zh, ch, fb, fk, !sub, false);
    half(b, zl, cl, c0, fb, !sub, false);
}
