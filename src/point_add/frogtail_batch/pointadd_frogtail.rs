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
use super::frogtail::{unabsorb, walk_forward, walk_inverse_page0, Sched, Scr, Walk, JB, MB, UTM};
use super::modp_frogdrop::load_bits;
use super::modp_ft::{
    ctrl_neg, mod_double, modadd, modsub, product, product_inv, product_tail_neg_s, reduce_hi, square_acc, Ms,
    NOCHUNK,
};
use crate::circuit::{BitId, QubitId};

pub const SCHED_FROGTAIL: &str = include_str!("sched_frogtail.txt");

/// lambda is measured as lambda 2^LHAT (LHAT = T - 256), so division 2's recompute needs only the tail's own halvings.
const LHAT: usize = 300;

/// Requested page0 inverse-walk peak. The modular routines take every qubit below it as a
/// carry pool; an independently hard-coded arithmetic minimum may still
/// expose a higher global peak, which the owner ledger must report.
pub const PEAK0: u64 = 884;
pub fn peak() -> u64 {
    PEAK0
}

thread_local! {
    /// (name, op index) at every checkpoint, for the per-phase average profile in the tests.
    pub(crate) static CKS: std::cell::RefCell<Vec<(String, usize)>> = const { std::cell::RefCell::new(Vec::new()) };
}

pub(crate) fn ck(b: &B, name: &str) {
    CKS.with(|c| c.borrow_mut().push((name.to_string(), b.ops.len())));
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
    /// S = s ^ parity ^ 1 ^ n0: 1/dx = (-1)^S C_T 2^-T
    pub(crate) key: QubitId,
    rc: Vec<G>,
    /// C_T's lanes (B's cofactor lanes and RLEN - |B.c| lanes of A, rebuilt by `unabsorb`)
    pub(crate) inv: Vec<QubitId>,
    /// m = ticks since the absorption (kept between the walks)
    pub(crate) mr: Vec<QubitId>,
    /// qubits |0> between the walks (A but C_T's lanes, B.v's low lane, j)
    parked: Vec<QubitId>,
    /// the forward walk's digit measurements
    m: Vec<BitId>,
}

/// Forward walk on dx (in `xq`, value in [1, p)); `dirty` (>= 32 lanes) is borrowed.
pub(crate) fn div_forward(b: &mut B, xq: &[QubitId], dirty: &[QubitId]) -> Div {
    let sch = Sched::from_text(SCHED_FROGTAIL);
    b.owner("walk.parity+n0 frame");
    let par = b.alloc();
    b.cx(xq[0], par);
    b.x(par); // parity frame starts at n0 = !dx[0]
    {
        b.owner("div.forward.pre-neg scratch");
        let ms = Ms::alloc_room(b, peak());
        ctrl_neg(b, &ms, xq, Some(par));
        ms.release(b);
    }
    let mut bb = xq.to_vec();
    b.owner("walk.B ring extension");
    bb.extend(b.alloc_n(sch.wb - xq.len()));
    b.owner("walk.A ring");
    let a = b.alloc_n(sch.wa);
    b.owner("walk.j counter");
    let j = b.alloc_n(JB);
    let w = Walk {
        a,
        bb,
        q: vec![],
        j,
        par,
    };
    let room = peak().saturating_sub(b.live + 12) as usize;
    b.owner("walk.forward scratch+pool");
    let sc = Scr::alloc_fwd(b, dirty, room);
    let m = walk_forward(b, &w, &sch, &sc);
    sc.release(b);
    ck(b, "walk forward end");
    b.owner("walk.absorption counter");
    let mr = b.alloc_n(MB);
    // At the closed interface logical j=+1 and the stored half-counter is
    // exactly zero. Borrow three existing j lanes as unabsorb sign/prefix
    // scratch; the recording restores them before exit.
    let tm = w.j[..UTM].to_vec();
    let (inv, key, rc) = unabsorb(b, &w, &sch, &mr, &tm, dirty);
    b.cx(w.par, key);
    b.x(key);
    let mut parked: Vec<QubitId> = w.a.iter().cloned().filter(|q| !inv.contains(q)).collect();
    parked.push(w.bf(0));
    parked.extend(&w.j);
    b.free_n(&parked);
    Div {
        w,
        sch,
        key,
        rc,
        inv,
        mr,
        parked,
        m,
    }
}

/// Exact inverse of div_forward: dx back in `xq` (= w.bb[0..256)), everything else freed.
pub(crate) fn div_inverse(b: &mut B, dv: Div, xq: &[QubitId], dirty: &[QubitId]) {
    let Div {
        mut w,
        sch,
        key,
        rc,
        mr,
        parked,
        m,
        ..
    } = dv;
    for &q in &parked {
        b.acquire(q);
    }
    b.relabel(&w.a, "walk.A ring");
    b.relabel(&w.bb, "walk.B ring (256 payload + 52 extension)");
    b.relabel(&w.j, "walk.j counter");
    b.relabel(&[w.par], "walk.parity+n0 frame");
    b.x(key);
    b.cx(w.par, key);
    b.play(&rc, true);
    b.free_n(&mr);
    b.owner("walk.inverse fixed scratch");
    let mut sc = Scr::alloc(b, dirty);
    b.owner("walk.inverse carry pool");
    sc.pool = b.alloc_n(peak().saturating_sub(b.live) as usize);
    walk_inverse_page0(b, &w, &sch, &sc, &m);
    ck(b, "walk inverse end");
    sc.release(b);
    b.free_n(&w.a);
    b.free_n(&w.bb[xq.len()..]);
    b.free_n(&w.j);
    {
        let ms = Ms::alloc_room(b, peak());
        ctrl_neg(b, &ms, xq, Some(w.par));
        // The inverse walk restores the initial n0 parity-frame offset.
        b.cx(xq[0], w.par);
        b.x(w.par);
        ms.release(b);
    }
    b.free(w.par);
}

/// C_T (`inv`, 318 lanes) <-> lo' = C_T mod p on its low 256 lanes (hi kept): the tails then run 256 steps.
fn reduce_ct(b: &mut B, inv: &[QubitId], undo: bool) {
    let tq = b.alloc_n(72);
    let ms = Ms::alloc_room(b, peak());
    b.begin();
    reduce_hi(b, inv, &tq, &ms.r);
    let r = b.end();
    b.play(&r, undo);
    ms.release(b);
    b.free_n(&tq);
}

/// z = y C 2^-tt (mod p), negated iff neg.0 ^ neg.1 (when given), recorded. (product_tail_neg gives -y C 2^-tt;
/// its negation folds into the sign's.)
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
    product_tail_neg_s(b, ms, &mut zz, c, y, tt, c.len() != 256);
    let neg = neg.map(|(q, f)| (q, !f));
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
    b.owner("coordinate x / ring B payload");
    let x = b.alloc_n(256);
    b.owner("coordinate y passenger");
    let y = b.alloc_n(256);
    b.declare_qubits(0, &x);
    b.declare_qubits(1, &y);
    let ox: Vec<BitId> = b.declare_bits(2, 256);
    let oy: Vec<BitId> = b.declare_bits(3, 256);

    // dx, dy
    {
        b.owner("shell temporary coordinate");
        let t = b.alloc_n(256);
        b.owner("shell modular scratch");
        let ms = Ms::alloc_room(b, peak());
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
    reduce_ct(b, &dv.inv, false);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        let r = rec_product_tail_s(b, &ms, &z, &dv.inv[..256], &y, dv.sch.t, Some(sq));
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
    reduce_ct(b, &dv.inv, true);
    div_inverse(b, dv, &x, &y);
    ck(b, "walk inverse 1 end");
    // dy = lambda * dx: recompute, fix the phase of the dy measurement, uncompute
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        let r = rec_product(b, &ms, &z, &y, &x, false);
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m1[i]);
        }
        let mut zz = z.clone();
        product_inv(b, &ms, &mut zz, &y, &x);
        b.free_n(&z);
        ms.release(b);
    }

    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    ck(b, "-- x: dx' = lambda^2 - ");
    {
        let ms = Ms::alloc_room(b, peak());
        let tmp = b.alloc();
        ctrl_neg(b, &ms, &x, None);
        let mut xx = x.clone();
        square_acc(b, &ms, &mut xx, &y, tmp);
        assert_eq!(xx, x);
        b.free(tmp);
        ms.release(b);
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
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
        let ms = Ms::alloc_room(b, peak());
        let r = rec_product(b, &ms, &z, &y, &x, true);
        b.play(&r, false);
        // measure lambda 2^(T - 256): its recompute is then a tail without the T - 256 trailing halvings
        let mut yy = y.clone();
        for _ in 0..LHAT {
            mod_double(b, &ms, &mut yy);
        }
        ms.release(b);
        for i in 0..256 {
            b.hmr_to(yy[i], m2[i]);
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
    reduce_ct(b, &dv.inv, false);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        let tt = dv.sch.t - LHAT;
        let r = rec_product_tail_s(b, &ms, &z, &dv.inv[..256], &y, tt, Some((sqq, !sqf)));
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m2[i]);
        }
        // uncompute: the exact inverse of the same tail on the hybrid ladder (no measured carry erases to invert)
        NOCHUNK.with(|c| c.set(true));
        let r = rec_product_tail_s(b, &ms, &z, &dv.inv[..256], &y, tt, Some((sqq, !sqf)));
        NOCHUNK.with(|c| c.set(false));
        b.play(&r, true);
        b.free_n(&z);
        ms.release(b);
    }
    reduce_ct(b, &dv.inv, true);
    ck(b, "lambda fix (+ unreduce)");
    div_inverse(b, dv, &x, &y);

    // ---------------- x3 = dx' + ox, y3 = ndy - oy
    ck(b, "-- x3 = dx' + ox, y3 = ");
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
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
