//! frogtail point addition: (x, y) += (ox, oy) on secp256k1, affine, in place, with the frogtail walk (a tape-free
//! Stehle-Zimmermann 2-adic Euclid in micro-ticks) as the inversion core. Outer structure as frogdrop's (two
//! divisions, measurement-based erasure of dy and lambda after Luo et al. / gnuchev):
//!
//!   dx = x - ox, dy = y - oy
//!   division 1:  walk on dx' (dx made odd: dx or p - dx) -> C with 1/dx = (-1)^S C 2^-T;  lambda = (-1)^S C dy 2^-T;
//!                measure dy away;  inverse walk -> dx;  recompute dy = lambda * dx, fix its phase, uncompute
//!   x:  dx' = lambda^2 - dx - 3 ox;   y:  ndy = -lambda * dx';  measure lambda away
//!   division 2:  walk on dx' -> C';  recompute lambda = -ndy (-1)^S' C' 2^-T, fix its phase, uncompute;
//!                inverse walk -> dx'
//!   x3 = dx' + ox,  y3 = ndy - oy

use super::builder::{B, G};
use super::frogtail::{unabsorb, walk_forward, walk_inverse, Sched, Scr, Walk, JB, MB, QB};
use super::modp_frogdrop::load_bits;
use super::modp_ft::{ctrl_neg, mac, modadd, modsub, product, product_tail, Ms};
use crate::circuit::{BitId, QubitId};

pub const SCHED_FROGTAIL: &str = include_str!("sched_frogtail.txt");

/// Circuit peak (set by the inverse walk); the modular routines take every qubit below it as a carry pool.
pub const PEAK: u64 = 933;

pub(crate) fn ck(b: &B, name: &str) {
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!(
            "ck {:24} live {} peak {} peak_op {} ops {} tof {}",
            name,
            b.live,
            b.peak,
            b.peak_op,
            b.ops.len(),
            b.tof
        );
    }
}

/// A division's state between its forward and inverse walk.
pub(crate) struct Div {
    pub(crate) w: Walk,
    pub(crate) sch: Sched,
    /// [dx was even] (dx' = p - dx)
    n0: QubitId,
    /// S = s ^ parity ^ 1 ^ n0: 1/dx = (-1)^S C_T 2^-T
    pub(crate) key: QubitId,
    rc: Vec<G>,
    /// C_T's lanes (B's cofactor lanes and RLEN - |B.c| lanes of A, rebuilt by `unabsorb`)
    pub(crate) inv: Vec<QubitId>,
    /// m = ticks since the absorption (kept between the walks)
    mr: Vec<QubitId>,
    /// unabsorb's temps (|0> between the walks)
    tm: Vec<QubitId>,
    /// qubits |0> between the walks (A but C_T's lanes, B.v's low lane, j)
    parked: Vec<QubitId>,
    /// the forward walk's digit measurements
    m: Vec<BitId>,
}

/// Forward walk on dx (in `xq`, value in [1, p)); `dirty` (>= 32 lanes) is borrowed.
pub(crate) fn div_forward(b: &mut B, xq: &[QubitId], dirty: &[QubitId]) -> Div {
    let sch = Sched::from_text(SCHED_FROGTAIL);
    let n0 = b.alloc();
    b.cx(xq[0], n0);
    b.x(n0);
    {
        let ms = Ms::alloc_room(b, PEAK);
        ctrl_neg(b, &ms, xq, Some(n0));
        ms.release(b);
    }
    let mut bb = xq.to_vec();
    bb.extend(b.alloc_n(sch.wb - xq.len()));
    let w = Walk {
        a: b.alloc_n(sch.wa),
        bb,
        q: vec![],
        j: b.alloc_n(JB),
        par: b.alloc(),
    };
    let room = PEAK.saturating_sub(b.live + 12) as usize;
    let sc = Scr::alloc_fwd(b, dirty, room);
    let m = walk_forward(b, &w, &sch, &sc);
    sc.release(b);
    ck(b, "walk forward end");
    let mr = b.alloc_n(MB);
    let tm = b.alloc_n(MB);
    let (inv, key, rc) = unabsorb(b, &w, &sch, &mr, &tm, dirty);
    b.free_n(&tm);
    b.cx(w.par, key);
    b.cx(n0, key);
    b.x(key);
    let mut parked: Vec<QubitId> = w.a.iter().cloned().filter(|q| !inv.contains(q)).collect();
    parked.push(w.bf(0));
    parked.extend(&w.j);
    b.free_n(&parked);
    Div {
        w,
        sch,
        n0,
        key,
        rc,
        inv,
        mr,
        tm,
        parked,
        m,
    }
}

/// Exact inverse of div_forward: dx back in `xq` (= w.bb[0..256)), everything else freed.
pub(crate) fn div_inverse(b: &mut B, dv: Div, xq: &[QubitId], dirty: &[QubitId]) {
    let Div {
        mut w,
        sch,
        n0,
        key,
        rc,
        mr,
        tm,
        parked,
        m,
        ..
    } = dv;
    for &q in parked.iter().chain(&tm) {
        b.acquire(q);
    }
    b.x(key);
    b.cx(n0, key);
    b.cx(w.par, key);
    b.play(&rc, true);
    b.free_n(&tm);
    b.free_n(&mr);
    w.q = b.alloc_n(QB);
    let mut sc = Scr::alloc(b, dirty);
    assert!(
        b.live <= PEAK,
        "inverse walk exceeds requested qubit budget"
    );
    sc.pool = b.alloc_n((PEAK - b.live) as usize);
    walk_inverse(b, &w, &sch, &sc, &m);
    ck(b, "walk inverse end");
    sc.release(b);
    b.free_n(&w.q);
    b.free_n(&w.a);
    b.free_n(&w.bb[xq.len()..]);
    b.free_n(&w.j);
    b.free(w.par);
    {
        let ms = Ms::alloc_room(b, PEAK);
        ctrl_neg(b, &ms, xq, Some(n0));
        ms.release(b);
    }
    b.x(n0);
    b.cx(xq[0], n0);
    b.free(n0);
}

/// z = y C 2^-tt (mod p), negated iff neg.0 ^ neg.1 (when given), recorded.
fn rec_product_tail_s(
    b: &mut B,
    ms: &Ms,
    z: &[QubitId],
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
    neg: Option<(QubitId, bool)>,
) -> Vec<G> {
    b.begin();
    let mut zz = z.to_vec();
    product_tail(b, ms, &mut zz, c, y, tt);
    let mut pos: Vec<QubitId> = zz.clone();
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if let Some((c, flip)) = neg {
        if flip {
            b.x(c);
        }
        ctrl_neg(b, ms, z, Some(c));
        if flip {
            b.x(c);
        }
    }
    b.end()
}

/// z = a * y (mod p) recorded, so the caller can uncompute it.
fn rec_product(
    b: &mut B,
    ms: &Ms,
    z: &[QubitId],
    a: &[QubitId],
    y: &[QubitId],
    negate: bool,
) -> Vec<G> {
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
        ctrl_neg(b, ms, z, None);
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
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(b, PEAK);
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
    let dv = div_forward(b, &x, &y);
    let sq = (dv.key, false);
    let m1 = b.fresh_bits(256);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, PEAK);
        let r = rec_product_tail_s(b, &ms, &z, &dv.inv, &y, dv.sch.t, Some(sq));
        b.play(&r, false);
        ms.release(b);
        ck(b, "lambda = inv * dy");
        for i in 0..256 {
            b.hmr_to(y[i], m1[i]);
        }
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }
    div_inverse(b, dv, &x, &y);
    // dy = lambda * dx: recompute, fix the phase of the dy measurement, uncompute
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, PEAK);
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
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(b, PEAK);
        ctrl_neg(b, &ms, &x, None);
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
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, PEAK);
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
    let dv = div_forward(b, &x, &y);
    let (sqq, sqf) = (dv.key, false);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, PEAK);
        let r = rec_product_tail_s(b, &ms, &z, &dv.inv, &y, dv.sch.t, Some((sqq, !sqf)));
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m2[i]);
        }
        b.play(&r, true);
        b.free_n(&z);
        ms.release(b);
    }
    div_inverse(b, dv, &x, &y);

    // ---------------- x3 = dx' + ox, y3 = ndy - oy
    ck(b, "-- x3 = dx' + ox, y3 = ");
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(b, PEAK);
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
