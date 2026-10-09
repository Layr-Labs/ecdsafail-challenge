//! froghop-single point addition: (x, y) += (ox, oy) on secp256k1, affine, in place.
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
//! register-sharing EEA constructions (Luo et al.; gnuchev); the inversion core is froghop-single's own.

use super::builder::B;
use super::froghop_single::{Fh, Lay};
use super::modp::{ctrl_neg, load_bits, mac, modadd, modsub, product, Ms};
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
    f: Fh,
    maps: Vec<(Vec<QubitId>, Vec<QubitId>)>,
    /// clean qubits released after the forward traversal (re-acquired before the inverse)
    parked: Vec<QubitId>,
    sq: QubitId,
}

/// Forward traversal on x' (in `xq`, already reflected), then: erase D, home V, sign fix.
/// Returns the 256 lanes holding the inverse (V lanes 0..256).
fn div_forward(b: &mut B, lay: &Lay, xq: &[QubitId], passenger: &[QubitId], refl: QubitId) -> (Div, Vec<QubitId>) {
    let w = lay.w;
    let m0 = lay.m[0];
    let d = b.alloc_n(w);
    let mut v = vec![];
    for j in 0..w {
        if j >= m0 + 1 && j < m0 + 257 {
            v.push(xq[j - m0 - 1]);
        } else {
            v.push(b.alloc());
        }
    }
    // the swap parity lives in the reflection bit: refl ^ par is what the sign fix needs
    let mut f = Fh::alloc(b, d, v, lay, passenger.to_vec(), Some(refl));
    f.init(b, lay);
    let maps = f.forward(b, lay);
    // D = (R = 1 at lane M_final, td = p): erase
    let mf = lay.m[lay.s - 1];
    let pp = super::refmodel::p();
    for i in 0..256 {
        if pp.bit(i) {
            b.x(f.d[i]);
        }
    }
    b.x(f.d[mf]);
    // home V: rotate down by pi
    for (i, &pb) in f.pi.iter().enumerate() {
        crot_down(b, pb, &f.v, 1 << i);
    }
    let inv: Vec<QubitId> = f.v[0..256].to_vec();
    // park every clean qubit of the traversal state (before the sign fix needs scratch)
    let mut parked = f.d.clone();
    parked.extend(&f.v[256..w]);
    parked.extend(f.all_meta().iter().take(super::froghop_single::POOL));
    parked.extend([f.fo, f.fd]);
    parked.extend(&f.stk[super::froghop_single::CNTB..]);
    parked.extend(&f.dep);
    b.free_n(&parked);
    // sign: inv = t_m if par ^ refl else p - t_m (sq taken after the traversal state is parked)
    let sq = b.alloc();
    b.cx(f.par, sq);
    b.x(sq);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &inv, sq);
        ms.release(b);
    }
    (Div { f, maps, parked, sq }, inv)
}

/// Undo div_forward's tail and run the inverse traversal; frees the whole traversal state.
fn div_inverse(b: &mut B, lay: &Lay, mut dv: Div, _refl: QubitId) {
    let w = lay.w;
    {
        let inv: Vec<QubitId> = dv.f.v[0..256].to_vec();
        let ms = Ms::alloc(b);
        b.begin();
        ctrl_neg(b, &ms, &inv, dv.sq);
        let r = b.end();
        b.play(&r, true);
        ms.release(b);
    }
    b.x(dv.sq);
    b.cx(dv.f.par, dv.sq);
    b.free(dv.sq);
    for &q in &dv.parked {
        b.acquire(q);
    }
    let f = &mut dv.f;
    for (i, &pb) in f.pi.iter().enumerate().rev() {
        b.begin();
        crot_down(b, pb, &f.v, 1 << i);
        let r = b.end();
        b.play(&r, true);
    }
    let mf = lay.m[lay.s - 1];
    let pp = super::refmodel::p();
    for i in 0..256 {
        if pp.bit(i) {
            b.x(f.d[i]);
        }
    }
    b.x(f.d[mf]);
    f.inverse(b, lay, &dv.maps);
    f.init(b, lay); // clears D's constants and pi/fo/f1
    let m0 = lay.m[0];
    b.free_n(&f.d);
    for j in 0..w {
        if !(j >= m0 + 1 && j < m0 + 257) {
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
        ctrl_neg(b, ms, z, ms.one);
    }
    b.end()
}

pub fn point_add(b: &mut B, lay: &Lay) -> (Vec<QubitId>, Vec<QubitId>) {
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    b.declare_qubits(0, &x);
    b.declare_qubits(1, &y);
    let ox: Vec<BitId> = b.declare_bits(2, 256);
    let oy: Vec<BitId> = b.declare_bits(3, 256);

    // dx, dy
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc(b);
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
    let refl = b.alloc();
    b.cx(x[255], refl);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, refl);
        ms.release(b);
    }
    let (dv, inv) = div_forward(b, lay, &x, &y, refl);
    // lambda = inv * dy, then measure dy away and move lambda into y's qubits
    let m1 = b.fresh_bits(256);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc(b);
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
    div_inverse(b, lay, dv, refl);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, refl);
        ms.release(b);
    }
    b.cx(x[255], refl);
    b.free(refl);
    // dy = lambda * dx: recompute, fix the phase of the dy measurement, uncompute
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc(b);
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
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, ms.one);
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
    let m2 = b.fresh_bits(256);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc(b);
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
    let refl = b.alloc();
    b.cx(x[255], refl);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, refl);
        ms.release(b);
    }
    let (dv, inv) = div_forward(b, lay, &x, &y, refl);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc(b);
        let r = rec_product(b, &ms, &z, &inv, &y, true);
        b.play(&r, false);
        for i in 0..256 {
            b.z_if(z[i], m2[i]);
        }
        b.play(&r, true);
        b.free_n(&z);
        ms.release(b);
    }
    div_inverse(b, lay, dv, refl);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, refl);
        ms.release(b);
    }
    b.cx(x[255], refl);
    b.free(refl);

    // ---------------- x3 = dx' + ox, y3 = ndy - oy
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc(b);
        load_bits(b, &t, &ox);
        modadd(b, &ms, &x, &t);
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t);
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }
    (x, y)
}
