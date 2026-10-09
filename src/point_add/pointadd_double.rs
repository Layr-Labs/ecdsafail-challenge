//! froghop-double point addition (exact-packed traversal): (x, y) += (ox, oy) on secp256k1, affine, in place.
//!
//!   dx = x - ox, dy = y - oy
//!   division 1:  forward traversal on dx (passenger dy) -> inv = 1/dx;  lambda = inv * dy;  measure dy away;
//!                inverse traversal (passenger lambda) -> dx;  recompute dy = lambda * dx, fix its phase, uncompute
//!   x:  dx' = lambda^2 - dx - 3 ox  (= x3 - ox)
//!   y:  ndy = -lambda * dx'         (= y3 + oy);  measure lambda away
//!   division 2:  forward traversal on dx' (passenger ndy) -> inv';  recompute lambda = -ndy * inv', fix its phase,
//!                uncompute;  inverse traversal -> dx'
//!   x3 = dx' + ox,  y3 = ndy - oy
//! Measurement-based erasure of dy and lambda (Hmr, phase fixed later against a recomputed value) follows the
//! register-sharing EEA constructions (Luo et al.; gnuchev); the inversion core is froghop-double's own.

use super::builder::B;
use super::froghop_double::{FhDouble, LayDouble, CNTB, WD};
use super::modp_double::{ctrl_neg, load_bits, mac, modadd, modsub, product, Ms};
use crate::circuit::{BitId, QubitId};

/// Controlled rotation of a lane ring, content moving DOWN by r (lane j <- lane j + r).
fn crot_down(b: &mut B, c: QubitId, v: &[QubitId], r: usize) {
    let n = v.len();
    let r = r % n;
    if r == 0 {
        return;
    }
    let g = gcd(n, r);
    for s in 0..g {
        let len = n / g;
        let cyc: Vec<usize> = (0..len).map(|k| (s + k * r) % n).collect();
        for k in 0..len - 1 {
            b.cswap(c, v[cyc[k]], v[cyc[k + 1]]);
        }
    }
}
fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// Everything a division needs between its forward and inverse traversal.
struct Div {
    f: FhDouble,
    maps: Vec<Vec<QubitId>>,
    /// clean qubits released after the forward traversal (re-acquired before the inverse)
    parked: Vec<QubitId>,
    sq: QubitId,
}

/// Forward traversal on x' (in `xq`, already reflected below 2^255), then: erase the final constants, home V,
/// sign fix. Returns the 256 lanes holding the inverse.
/// Final state of every shot: DONE, D = (R = 1, cd = p), V = (rv = 0, cv = t), b = 1, pi in {0, 1}.
fn div_forward(b: &mut B, lay: &LayDouble, xq: &[QubitId], refl: QubitId, dirty: &[QubitId]) -> (Div, Vec<QubitId>) {
    let w = WD;
    let d = b.alloc_n(w);
    let mut v = vec![];
    for j in 0..w {
        if (1..257).contains(&j) {
            v.push(xq[j - 1]);
        } else {
            v.push(b.alloc());
        }
    }
    let mut f = FhDouble::alloc(b, d, v, lay, refl);
    f.init(b);
    ck(b, "div_forward pre-traversal");
    let maps = f.forward(b, lay);
    ck(b, "div_forward post-traversal");
    final_consts(b, &f);
    // home V: V-frame lane u sits at physical lane u + pi, pi in {0, 1}
    crot_down(b, f.pi[0], &f.v, 1);
    // DONE shots oscillate pi from 1 (termination slot) once per counted slot: pi0 = !cnt0
    b.cx(f.stk[0], f.pi[0]);
    b.x(f.pi[0]);
    let inv: Vec<QubitId> = (0..256).map(|i| f.v[w - 1 - i]).collect();
    let parked = parked_of(&f);
    b.free_n(&parked);
    // sign: par started as refl, so inv = t if par else p - t; sq = !par (par's qubit, complemented until undone)
    let sq = f.par;
    b.x(sq);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &inv, Some(sq), dirty);
        ms.release(b);
    }
    ck(b, "div_forward end");
    (Div { f, maps, parked, sq }, inv)
}

/// X out the constants every finished shot shares (R = 1, cd = p, b = 1, DONE flag).
pub(crate) fn ck(b: &B, name: &str) {
    if std::env::var("FH_CK").is_ok() {
        eprintln!("ck {:24} live {} peak {} peak_op {} ops {}", name, b.live, b.peak, b.peak_op, b.ops.len());
    }
}

fn final_consts(b: &mut B, f: &FhDouble) {
    let w = WD;
    let pp = super::refmodel_double::p();
    b.x(f.d[0]);
    for i in 0..256 {
        if pp.bit(i) {
            b.x(f.d[w - 1 - i]);
        }
    }
    b.x(f.fnn); // b - 1 = 0 already
}

/// Qubits that are |0> for every shot after `final_consts`, homing and pi0's erasure (all but cv, cnt, par).
fn parked_of(f: &FhDouble) -> Vec<QubitId> {
    let mut v = f.d.clone();
    v.extend(&f.v[0..WD - 256]); // V-frame lanes below t's 256 bits
    v.extend(&f.pool);
    v.extend(&f.pi);
    v.extend([f.fa, f.fv, f.fc, f.fnn]);
    v.extend(&f.stk[CNTB..]);
    v.extend(&f.dep);
    v.extend(&f.bq);
    v
}

/// Undo div_forward's tail and run the inverse traversal; frees the whole traversal state.
fn div_inverse(b: &mut B, lay: &LayDouble, mut dv: Div, dirty: &[QubitId]) {
    let w = WD;
    {
        let inv: Vec<QubitId> = (0..256).map(|i| dv.f.v[w - 1 - i]).collect();
        let ms = Ms::alloc(b);
        b.begin();
        ctrl_neg(b, &ms, &inv, Some(dv.sq), dirty);
        let r = b.end();
        b.play(&r, true);
        ms.release(b);
    }
    b.x(dv.sq);
    for &q in &dv.parked {
        b.acquire(q);
    }
    let f = &mut dv.f;
    b.x(f.pi[0]);
    b.cx(f.stk[0], f.pi[0]);
    b.begin();
    crot_down(b, f.pi[0], &f.v, 1);
    let r = b.end();
    b.play(&r, true);
    final_consts(b, f);
    f.inverse(b, lay, &dv.maps);
    f.init(b); // clears D's constants, b, pi, AL flag
    b.free_n(&f.d);
    for j in 0..w {
        if !(1..257).contains(&j) {
            b.free(f.v[j]);
        }
    }
    let meta = f.all_meta();
    b.free_n(&meta);
}

/// z = a * y (mod p) recorded, so the caller can uncompute it.
fn rec_product(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &[QubitId], negate: bool) -> Vec<super::builder::G> {
    b.begin();
    let mut zz = z.to_vec();
    product(b, ms, &mut zz, a, y);
    // product leaves z's lanes relabelled; move the value back onto z's lane order (swaps are free)
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

pub fn point_add(b: &mut B, lay: &LayDouble) -> (Vec<QubitId>, Vec<QubitId>) {
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
        modsub(b, &ms, &x, &t);
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t);
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }

    // ---------------- division 1
    ck(b, "-- division 1");
    let refl = b.alloc();
    b.cx(x[255], refl);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, Some(refl), &y);
        ms.release(b);
    }
    let (dv, inv) = div_forward(b, lay, &x, refl, &y);
    // lambda = inv * dy, then measure dy away and move lambda into y's qubits
    let m1 = b.fresh_bits(256);
    {
        let ms = Ms::alloc(b);
        let z = b.alloc_n(256);
        let r = rec_product(b, &ms, &z, &inv, &y, false);
        b.play(&r, false);
        ms.release(b);
        for i in 0..256 {
            b.hmr_to(y[i], m1[i]);
        }
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }
    div_inverse(b, lay, dv, &y);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, Some(refl), &y);
        ms.release(b);
    }
    b.cx(x[255], refl);
    b.free(refl);
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
            modsub(b, &ms, &x, &t);
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
    let refl = b.alloc();
    b.cx(x[255], refl);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, Some(refl), &y);
        ms.release(b);
    }
    let (dv, inv) = div_forward(b, lay, &x, refl, &y);
    {
        let ms = Ms::alloc(b);
        let z = b.alloc_n(256);
        let r = rec_product(b, &ms, &z, &inv, &y, true);
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m2[i]);
        }
        b.play(&r, true);
        b.free_n(&z);
        ms.release(b);
    }
    div_inverse(b, lay, dv, &y);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, Some(refl), &y);
        ms.release(b);
    }
    b.cx(x[255], refl);
    b.free(refl);

    // ---------------- x3 = dx' + ox, y3 = ndy - oy
    ck(b, "-- x3 = dx' + ox, y3 = ");
    {
        let ms = Ms::alloc(b);
        let t = b.alloc_n(256);
        load_bits(b, &t, &ox);
        modadd(b, &ms, &x, &t);
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t);
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }
    // Fiat-Shamir nonce: X X pairs (identity, no Toffoli) re-roll the harness's test shots
    for _ in 0..super::NONCE {
        b.x(x[0]);
        b.x(x[0]);
    }
    ck(b, "end");
    (x, y)
}
