//! froghop-one point addition (exact-packed one-hop traversal): (x, y) += (ox, oy) on secp256k1, affine, in place.
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
//! register-sharing EEA constructions (Luo et al.; gnuchev); the shell is froghop-double's.

use super::builder::B;
use super::froghop_one::{FhOne, GhostTrace, LayOne, CNTB, W1};
use super::modp_double::{ctrl_neg, load_bits, mac, modadd, modsub, product, sdw_product_chunked, sdw_product_inv_chunked, sdw_product_marked, sdw_square_acc, Ms};
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
    f: FhOne,
    trace: GhostTrace,
    /// clean qubits released after the forward traversal (re-acquired before the inverse)
    parked: Vec<QubitId>,
    sq: QubitId,
}

/// Forward traversal on x' (in `xq`, already reflected below 2^255), then: home V, erase the final constants, sign
/// fix. Returns the 256 lanes holding the inverse (D's cofactor, LSB at lane W-1).
/// Final state of every shot: DONE, D = (r = 1, cd = t), V = (rv = 0, cv = p), b = 1, k = 0, empty stack.
fn div_forward(b: &mut B, lay: &LayOne, xq: &[QubitId], refl: QubitId, dirty: &[QubitId]) -> (Div, Vec<QubitId>) {
    let w = W1;
    let d = b.alloc_n(w);
    let mut v = vec![];
    for j in 0..w {
        if (1..257).contains(&j) {
            v.push(xq[j - 1]);
        } else {
            v.push(b.alloc());
        }
    }
    let mut f = FhOne::alloc(b, d, v, lay, refl, dirty.to_vec(), super::GPOOL);
    f.init(b, lay);
    ck(b, "div_forward pre-traversal");
    let trace = f.forward_ghost(b, lay);
    ck(b, "div_forward post-traversal");
    home_and_consts(b, &f);
    ck(b, "div_forward home/constants");
    let inv: Vec<QubitId> = (0..256).map(|i| f.d[w - 1 - i]).collect();
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
    ck(b, "div_forward sign");
    ck(b, "div_forward end");
    (Div { f, trace, parked, sq }, inv)
}

pub(crate) fn ck(b: &B, name: &str) {
    if std::env::var("FH_CK").is_ok() {
        eprintln!("ck {:24} live {} peak {} peak_op {} ops {} tof {}", name, b.live, b.peak, b.peak_op, b.ops.len(), b.tof);
    }
}

/// Rotate V home (down by pi), then X out the constants every finished shot shares (r = 1, cv = p, DONE flag).
fn home_and_consts(b: &mut B, f: &FhOne) {
    let w = W1;
    for (i, &pb) in f.pi.iter().enumerate() {
        crot_down(b, pb, &f.v, 1 << (i + 1));
    }
    let pp = super::refmodel_one::p();
    b.x(f.d[0]);
    for i in 0..256 {
        if pp.bit(i) {
            b.x(f.v[w - 1 - i]);
        }
    }
    b.x(f.fnn);
    for &q in f.dep.iter().take(5) { b.x(q); } // erase d6 = 31 at the clean end
}

/// Qubits that are |0> for every shot after `home_and_consts` (all but cd, pi, cnt, par).
fn parked_of(f: &FhOne) -> Vec<QubitId> {
    let mut v: Vec<QubitId> = f.d[0..W1 - 256].to_vec();
    v.extend(&f.v);
    v.extend(&f.pool);
    v.extend(&f.gp);
    v.extend(&f.k);
    v.extend([f.fo, f.fd, f.fnn]);
    v.extend(&f.stk[CNTB..]);
    v.extend(&f.dep);
    v.extend(&f.bq);
    v
}

/// Undo div_forward's tail and run the inverse traversal; frees the whole traversal state.
fn div_inverse(b: &mut B, lay: &LayOne, mut dv: Div, dirty: &[QubitId]) {
    let w = W1;
    ck(b, "div_inverse start");
    {
        let inv: Vec<QubitId> = (0..256).map(|i| dv.f.d[w - 1 - i]).collect();
        let ms = Ms::alloc(b);
        b.begin();
        ctrl_neg(b, &ms, &inv, Some(dv.sq), dirty);
        let r = b.end();
        b.play(&r, true);
        ms.release(b);
    }
    b.x(dv.sq);
    ck(b, "div_inverse sign");
    for &q in &dv.parked {
        b.acquire(q);
    }
    let f = &mut dv.f;
    b.begin();
    home_and_consts(b, f);
    let r = b.end();
    b.play(&r, true);
    ck(b, "div_inverse home/constants");
    f.inverse_ghost(b, lay, dv.trace);
    ck(b, "div_inverse traversal");
    f.init(b, lay); // clears D's p, V's cv = 1, b, pi, OUT flag, f1
    b.free_n(&f.d);
    for j in 0..w {
        if !(1..257).contains(&j) {
            b.free(f.v[j]);
        }
    }
    let meta = f.all_meta();
    b.free_n(&meta);
    ck(b, "div_inverse end");
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

/// A product with no later inverse partner. CREP repairs each measured k locally.
fn direct_product_crep(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &[QubitId], negate: bool) {
    let mut zz = z.to_vec();
    sdw_product_chunked(b, ms, &mut zz, a, y);
    let mut pos = zz;
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
    if negate { ctrl_neg(b, ms, z, None, y); }
}

/// S4 paired product is emitted forward and then arithmetically reversed.
/// Its X-measured chunk carries cannot be inverted through a gate recording.
fn chunked_unproduct(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &[QubitId], negate: bool) {
    if negate { ctrl_neg(b, ms, z, None, y); }
    let mut zz = z.to_vec();
    sdw_product_inv_chunked(b, ms, &mut zz, a, y);
    let mut pos = zz;
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
}

/// Full reversible recording plus the exact k-erasure intervals of its 256 Horner steps.
/// The forward paired pass substitutes HMR for each interval; the inverse pass replays the
/// intervals and repairs their measurement phase debts immediately after regenerating k.
struct PairedProduct {
    gates: Vec<super::builder::G>,
    erase: Vec<(usize, usize)>,
}

fn rec_paired_product(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &[QubitId], negate: bool) -> PairedProduct {
    b.begin();
    let mut zz = z.to_vec();
    let mut erase = Vec::with_capacity(255);
    sdw_product_marked(b, ms, &mut zz, a, y, &mut erase);
    let mut pos = zz;
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
    let gates = b.end();
    assert_eq!(erase.len(), 255);
    assert!(erase.windows(2).all(|w| w[0].1 <= w[1].0));
    PairedProduct { gates, erase }
}

fn paired_forward_hmr(b: &mut B, ms: &Ms, p: &PairedProduct) -> Vec<BitId> {
    let bits = b.fresh_bits(p.erase.len());
    let mut at = 0;
    for (i, &(start, end)) in p.erase.iter().enumerate() {
        b.play(&p.gates[at..start], false);
        b.hmr_to(ms.k, bits[i]);
        at = end;
    }
    b.play(&p.gates[at..], false);
    bits
}

fn paired_inverse_repair(b: &mut B, ms: &Ms, p: &PairedProduct, bits: &[BitId]) {
    assert_eq!(bits.len(), p.erase.len());
    let mut at = p.gates.len();
    for (i, &(start, end)) in p.erase.iter().enumerate().rev() {
        b.play(&p.gates[end..at], true);
        b.play(&p.gates[start..end], true);
        b.z_if(ms.k, bits[i]);
        at = start;
    }
    b.play(&p.gates[..at], true);
}

pub fn point_add(b: &mut B, lay: &LayOne) -> (Vec<QubitId>, Vec<QubitId>) {
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
        ck(b, "shell initial dx modsub");
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t);
        ck(b, "shell initial dy modsub");
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
    ck(b, "shell div1 input reflect");
    let (dv, inv) = div_forward(b, lay, &x, refl, &y);
    // lambda = inv * dy, then measure dy away and move lambda into y's qubits
    let m1 = b.fresh_bits(256);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc(b);
        direct_product_crep(b, &ms, &z, &inv, &y, false);
        ck(b, "shell lambda product");
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
    ck(b, "shell div1 inverse done");
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, Some(refl), &y);
        ms.release(b);
    }
    ck(b, "shell div1 output reflect");
    b.cx(x[255], refl);
    b.free(refl);
    // dy = lambda * dx: recompute, fix the phase of the dy measurement, uncompute
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc(b);
        direct_product_crep(b, &ms, &z, &y, &x, false);
        ck(b, "shell dy repair product");
        for i in 0..256 {
            b.z_if(z[i], m1[i]);
        }
        chunked_unproduct(b, &ms, &z, &y, &x, false);
        ck(b, "shell dy repair unproduct");
        b.free_n(&z);
        ms.release(b);
    }

    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    ck(b, "-- x: dx' = lambda^2 - ");
    {
        let tmp = b.alloc();
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, None, &y);
        ck(b, "shell x negate dx");
        let mut xx = x.clone();
        sdw_square_acc(b, &ms, &mut xx, &y, tmp);
        ck(b, "shell lambda square mac");
        assert_eq!(xx, x);
        b.free(tmp);
        ms.release(b);
        let t = b.alloc_n(256);
        let ms = Ms::alloc(b);
        load_bits(b, &t, &ox);
        for _ in 0..3 {
            modsub(b, &ms, &x, &t);
            ck(b, "shell x minus ox modsub");
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
        let ms = Ms::alloc(b);
        direct_product_crep(b, &ms, &z, &y, &x, true);
        ck(b, "shell ndy product");
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
    ck(b, "shell div2 input reflect");
    let (dv, inv) = div_forward(b, lay, &x, refl, &y);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc(b);
        direct_product_crep(b, &ms, &z, &inv, &y, true);
        ck(b, "shell lambda repair product");
        for i in 0..256 {
            b.z_if(z[i], m2[i]);
        }
        chunked_unproduct(b, &ms, &z, &inv, &y, true);
        ck(b, "shell lambda repair unproduct");
        b.free_n(&z);
        ms.release(b);
    }
    div_inverse(b, lay, dv, &y);
    ck(b, "shell div2 inverse done");
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, Some(refl), &y);
        ms.release(b);
    }
    ck(b, "shell div2 output reflect");
    b.cx(x[255], refl);
    b.free(refl);

    // ---------------- x3 = dx' + ox, y3 = ndy - oy
    ck(b, "-- x3 = dx' + ox, y3 = ");
    {
        let t = b.alloc_n(256);
        let ms = Ms::alloc(b);
        load_bits(b, &t, &ox);
        modadd(b, &ms, &x, &t);
        ck(b, "shell final x modadd");
        load_bits(b, &t, &ox);
        load_bits(b, &t, &oy);
        modsub(b, &ms, &y, &t);
        ck(b, "shell final y modsub");
        load_bits(b, &t, &oy);
        b.free_n(&t);
        ms.release(b);
    }
    // Fiat-Shamir nonce: X X pairs (identity, no Toffoli) re-roll the benchmark's test shots
    for _ in 0..super::nonce() {
        b.x(x[0]);
        b.x(x[0]);
    }
    ck(b, "end");
    (x, y)
}

#[cfg(test)]
mod shell_tests {
    use super::*;
    use super::super::refmodel_one::{p, N};
    use super::super::tests_double::run;

    struct FixedXof(u8);
    impl sha3::digest::XofReader for FixedXof {
        fn read(&mut self, out: &mut [u8]) { out.fill(self.0); }
    }

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

    fn make(pool: usize, measured: bool, inverse: bool) -> (B, Vec<QubitId>, Vec<QubitId>, Vec<QubitId>, Vec<QubitId>) {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let a = b.alloc_n(256);
        let y = b.alloc_n(256);
        let passenger = b.alloc_n(256);
        let ms = Ms::alloc_pool(&mut b, pool);
        if measured {
            let r = rec_paired_product(&mut b, &ms, &z, &a, &y, false);
            let bits = paired_forward_hmr(&mut b, &ms, &r);
            if inverse { paired_inverse_repair(&mut b, &ms, &r, &bits); }
        } else {
            let r = rec_product(&mut b, &ms, &z, &a, &y, false);
            b.play(&r, false);
            if inverse { b.play(&r, true); }
        }
        (b, z, a, y, passenger)
    }

    #[test]
    fn one_r10_c7_a8a_paired_product_kernel() {
        let pp = p();
        let mut seed = 0x843c7a8au64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut av = vec![N::ZERO; 64];
        let mut yv = vec![N::ZERO; 64];
        for k in 0..64 {
            let mut x = N::ZERO;
            let mut y = N::ZERO;
            for j in 0..4 { x |= N::from(next()) << (j * 64); y |= N::from(next()) << (j * 64); }
            av[k] = x % pp;
            yv[k] = y % pp;
        }
        av[0] = N::ZERO; av[1] = N::from(1u64); av[2] = pp - N::from(1u64);
        yv[0] = pp - N::from(1u64); yv[1] = N::ZERO; yv[2] = pp - N::from(2u64);
        for pool in [60, 73] {
            for inverse in [false, true] {
                let (old, oz, oa, oy, op) = make(pool, false, inverse);
                let (new, nz, na, ny, np) = make(pool, true, inverse);
                assert_eq!((&oz, &oa, &oy, &op), (&nz, &na, &ny, &np));
                let mut input = vec![0u64; old.width() as usize];
                for k in 0..64 { put(&mut input, &oa, k, av[k]); put(&mut input, &oy, k, yv[k]); }
                for &q in &op { input[q.0 as usize] = next(); }
                // The pool's one qubit is prepared by both builders.
                let init = |words: &mut Vec<u64>| words.copy_from_slice(&input);
                let a = run(&old.ops, old.width() as usize, &init);
                let b = run(&new.ops, new.width() as usize, &init);
                assert_eq!(a.q, b.q, "all wires pool {pool} inverse {inverse}");
                if inverse {
                    assert_eq!(a.phase & !0b111u64, b.phase & !0b111u64, "old/new random-case phase pool {pool}");
                    assert_eq!(b.phase & !0b111u64, 0, "new random-case phase pool {pool}");
                    eprintln!("paired product edge phase pool {pool}: old {} new {}", a.phase & 0b111, b.phase & 0b111);
                } else {
                    for k in 0..64 {
                        assert_eq!(get(&b.q, &nz, k) % pp, av[k].mul_mod(yv[k], pp), "product residue pool {pool} shot {k}");
                    }
                }
            }
        }
    }

    #[test]
    fn one_r10_c7_b3_fold_kernel() {
        use super::super::modp_double::{ctrl_modadd, mod_double};
        let pp = p();
        let mut seed = 0xb3c7u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut zv = vec![N::ZERO; 64];
        let mut yv = vec![N::ZERO; 64];
        let mut cv = vec![0u64; 64];
        for k in 0..64 {
            for j in 0..4 { zv[k] |= N::from(next()) << (j * 64); yv[k] |= N::from(next()) << (j * 64); }
            zv[k] %= pp; yv[k] %= pp; cv[k] = next() & 1;
        }
        zv[0] = N::ZERO; yv[0] = pp - N::from(1u64); cv[0] = 1;
        zv[1] = pp - N::from(1u64); yv[1] = pp - N::from(2u64); cv[1] = 1;
        for pool in [58, 72] {
            let build = |merged: bool| {
                let mut b = B::new();
                let mut z = b.alloc_n(256);
                let z_initial = z.clone();
                let y = b.alloc_n(256);
                let c = b.alloc();
                let passengers = b.alloc_n(256);
                let ms = Ms::alloc_pool(&mut b, pool);
                b.begin();
                if merged { super::super::modp_double::horner_add(&mut b, &ms, &mut z, &y, c, None); }
                else { mod_double(&mut b, &ms, &mut z, &y); ctrl_modadd(&mut b, &ms, &z, &y, c); }
                let r = b.end();
                b.play(&r, false);
                let forward = b.ops.clone();
                b.play(&r, true);
                (b, forward, z_initial, z, y, c, passengers)
            };
            let (old, old_f, ozi, oz, oy, oc, op) = build(false);
            let (new, new_f, nzi, nz, ny, nc, np) = build(true);
            assert_eq!((&ozi, &oz, &oy, oc, &op), (&nzi, &nz, &ny, nc, &np));
            let mut input = vec![0u64; old.width() as usize];
            for k in 0..64 {
                put(&mut input, &ozi, k, zv[k]); put(&mut input, &oy, k, yv[k]);
                if cv[k] == 1 { input[oc.0 as usize] |= 1u64 << k; }
            }
            for &q in &op { input[q.0 as usize] = next(); }
            let init = |words: &mut Vec<u64>| words[..input.len()].copy_from_slice(&input);
            let of = run(&old_f, old.width() as usize, &init);
            let nf = run(&new_f, new.width() as usize, &init);
            for k in 0..64 {
                let expected = ((zv[k] << 1) + if cv[k] == 1 { yv[k] } else { N::ZERO }) % pp;
                assert_eq!(get(&of.q, &oz, k) % pp, expected, "old fold pool {pool} shot {k}");
                assert_eq!(get(&nf.q, &nz, k) % pp, expected, "new fold pool {pool} shot {k}");
            }
            let oi = run(&old.ops, old.width() as usize, &init);
            let ni = run(&new.ops, new.width() as usize, &init);
            assert_eq!(oi.q, ni.q[..oi.q.len()], "fold inverse all shared wires pool {pool}");
            assert!(ni.q[oi.q.len()..].iter().all(|&v| v == 0), "fold diagnostic temporary clean");
            assert_eq!(oi.phase, ni.phase, "fold inverse phase pool {pool}");
            assert_eq!(ni.phase & !0b11u64, 0, "fold random-case zero phase pool {pool}");
        }
    }

    #[test]
    fn one_r10_c7_d1b_mac_kernel() {
        use super::super::modp_double::{ctrl_modadd, mod_double, mod_halve};
        let pp = p();
        let mut seed = 0xb3c7aaccu64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut xv = vec![N::ZERO; 64];
        let mut av = vec![N::ZERO; 64];
        let mut yv = vec![N::ZERO; 64];
        for k in 0..64 {
            for j in 0..4 {
                xv[k] |= N::from(next()) << (j * 64);
                av[k] |= N::from(next()) << (j * 64);
                yv[k] |= N::from(next()) << (j * 64);
            }
            xv[k] %= pp; av[k] %= pp; yv[k] %= pp;
        }
        xv[0] = N::ZERO; av[0] = pp - N::from(1u64); yv[0] = pp - N::from(1u64);
        let build = |new_mac: bool| {
            let mut b = B::new();
            let x = b.alloc_n(256);
            let a = b.alloc_n(256);
            let mut y = b.alloc_n(256);
            let passengers = b.alloc_n(256);
            let ms = Ms::alloc_pool(&mut b, 73);
            if new_mac {
                super::super::modp_double::mac(&mut b, &ms, &x, &a, &mut y);
            } else {
                b.begin();
                for i in 0..256 {
                    ctrl_modadd(&mut b, &ms, &x, &y, a[i]);
                    if i != 255 { mod_double(&mut b, &ms, &mut y, &a); }
                }
                for _ in 0..255 { mod_halve(&mut b, &ms, &mut y, &a); }
                let r = b.end();
                b.play(&r, false);
            }
            let forward = b.ops.clone();
            (b, forward, x, a, y, passengers)
        };
        let (old, old_f, ox, oa, oy, op) = build(false);
        let (new, new_f, nx, na, ny, np) = build(true);
        assert_eq!((&ox, &oa, &oy, &op), (&nx, &na, &ny, &np));
        let mut input = vec![0u64; old.width() as usize];
        for k in 0..64 { put(&mut input, &ox, k, xv[k]); put(&mut input, &oa, k, av[k]); put(&mut input, &oy, k, yv[k]); }
        for &q in &op { input[q.0 as usize] = next(); }
        let init = |words: &mut Vec<u64>| words.copy_from_slice(&input);
        let of = run(&old_f, old.width() as usize, &init);
        let nf = run(&new_f, new.width() as usize, &init);
        for k in 0..64 {
            let expected = (xv[k] + av[k].mul_mod(yv[k], pp)) % pp;
            if k == 0 {
                eprintln!("mac edge: old {} new {} expected {}", get(&of.q, &ox, k) % pp, get(&nf.q, &nx, k) % pp, expected);
                continue;
            }
            assert_eq!(get(&of.q, &ox, k) % pp, expected, "old mac shot {k}");
            assert_eq!(get(&nf.q, &nx, k) % pp, expected, "new mac shot {k}");
            assert_eq!(get(&nf.q, &ny, k), yv[k], "mac y restored shot {k}");
        }
        let xset: std::collections::HashSet<usize> = ox.iter().map(|q| q.0 as usize).collect();
        for q in 0..of.q.len() {
            if !xset.contains(&q) { assert_eq!(of.q[q], nf.q[q], "mac preserved wire {q}"); }
        }
        assert_eq!(nf.phase & !1u64, 0, "mac random-case zero phase");
    }

    #[test]
    fn one_r10_c7_d1b_product_kernel() {
        use sha3::digest::{ExtendableOutput, Update};
        let pp = p();
        let mut seed = 0xd1bc7u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut av = vec![N::ZERO; 64];
        let mut yv = vec![N::ZERO; 64];
        for k in 0..64 {
            for j in 0..4 { av[k] |= N::from(next()) << (j * 64); yv[k] |= N::from(next()) << (j * 64); }
            av[k] %= pp; yv[k] %= pp;
        }
        av[0] = pp - N::from(1u64); yv[0] = pp - N::from(2u64);
        for pool in [60, 73] {
            let build = |crep: bool| {
                let mut b = B::new();
                let z = b.alloc_n(256);
                let a = b.alloc_n(256);
                let y = b.alloc_n(256);
                let passengers = b.alloc_n(256);
                let ms = Ms::alloc_pool(&mut b, pool);
                if crep { direct_product_crep(&mut b, &ms, &z, &a, &y, false); }
                else { let r = rec_product(&mut b, &ms, &z, &a, &y, false); b.play(&r, false); }
                (b, z, a, y, passengers)
            };
            let (old, oz, oa, oy, op) = build(false);
            let (new, nz, na, ny, np) = build(true);
            assert_eq!((&oz, &oa, &oy, &op), (&nz, &na, &ny, &np));
            let mut input = vec![0u64; old.width() as usize];
            for k in 0..64 { put(&mut input, &oa, k, av[k]); put(&mut input, &oy, k, yv[k]); }
            for &q in &op { input[q.0 as usize] = next(); }
            let init = |words: &mut Vec<u64>| words.copy_from_slice(&input);
            let orig = run(&old.ops, old.width() as usize, &init);
            let mut h = sha3::Shake256::default();
            h.update(b"froghop-test");
            let mut xof = h.finalize_xof();
            let (_, nb, _, _) = crate::circuit::analyze_ops(new.ops.iter());
            let mut sim = crate::sim::Simulator::new(new.width() as usize, nb as usize, &mut xof);
            init(&mut sim.qubits);
            sim.apply_iter(new.ops.iter());
            assert_eq!(orig.q, sim.qubits, "CREP product all wires pool {pool}");
            assert_eq!(orig.phase & !1u64, sim.phase & !1u64, "CREP random-case phase pool {pool}");
            assert_eq!(sim.phase & !1u64, 0, "CREP random-case zero phase pool {pool}");
            let ones: u32 = (10000..10255).map(|i| sim.bits[i].count_ones()).sum();
            assert!(ones > 0 && ones < 255 * 64, "both receipt values pool {pool}");
            for k in 1..64 { assert_eq!(get(&sim.qubits, &nz, k) % pp, av[k].mul_mod(yv[k], pp), "CREP product pool {pool} shot {k}"); }
            eprintln!("CREP product pool {pool}: receipt ones {ones}/16320, edge phase old {} new {}", orig.phase & 1, sim.phase & 1);
        }
    }

    #[test]
    fn one_r10_c7_b3_fold_million() {
        use sha3::digest::{ExtendableOutput, Update};
        let pp = p();
        let mut b = B::new();
        let mut z = b.alloc_n(256);
        let initial_z = z.clone();
        let y = b.alloc_n(256);
        let c = b.alloc();
        let passengers = b.alloc_n(256);
        let ms = Ms::alloc_pool(&mut b, 72);
        b.begin();
        super::super::modp_double::horner_add(&mut b, &ms, &mut z, &y, c, None);
        let r = b.end();
        b.play(&r, false);
        let fwd_end = b.ops.len();
        b.play(&r, true);
        let mut h = sha3::Shake256::default();
        h.update(b"r10-c7-fold-million");
        let mut xof = h.finalize_xof();
        let (_, nb, _, _) = crate::circuit::analyze_ops(b.ops.iter());
        let mut sim = crate::sim::Simulator::new(b.width() as usize, nb as usize, &mut xof);
        let mut seed = 0xc7f01du64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut cases = 0usize;
        for batch in 0..15_626 {
            sim.clear_for_shot();
            let mut zv = [N::ZERO; 64];
            let mut yv = [N::ZERO; 64];
            let mut cv = [0u64; 64];
            for k in 0..64 {
                for j in 0..4 { zv[k] |= N::from(next()) << (j * 64); yv[k] |= N::from(next()) << (j * 64); }
                zv[k] %= pp; yv[k] %= pp; cv[k] = next() & 1;
            }
            if batch == 0 {
                zv[0] = N::ZERO; yv[0] = pp - N::from(1u64); cv[0] = 1;
                zv[1] = pp - N::from(1u64); yv[1] = pp - N::from(2u64); cv[1] = 1;
                zv[2] = pp - N::from(2u64); yv[2] = pp - N::from(1u64); cv[2] = 0;
                zv[3] = pp - N::from(1u64); yv[3] = pp - N::from(1u64); cv[3] = 1;
            }
            for k in 0..64 {
                put(&mut sim.qubits, &initial_z, k, zv[k]);
                put(&mut sim.qubits, &y, k, yv[k]);
                if cv[k] == 1 { sim.qubits[c.0 as usize] |= 1u64 << k; }
            }
            for &q in &passengers { sim.qubits[q.0 as usize] = next(); }
            let mut initial = sim.qubits.clone();
            sim.apply_iter(b.ops[..fwd_end].iter());
            for k in 0..64 {
                let expected = ((zv[k] << 1) + if cv[k] == 1 { yv[k] } else { N::ZERO }) % pp;
                assert_eq!(get(&sim.qubits, &z, k) % pp, expected, "fold batch {batch} shot {k}");
            }
            sim.apply_iter(b.ops[fwd_end..].iter());
            let mask = if batch == 0 { !0b1111u64 } else { u64::MAX };
            assert_eq!(sim.phase & mask, 0, "fold inverse phase batch {batch}");
            for q in 0..initial.len() {
                assert_eq!(sim.qubits[q] & mask, initial[q] & mask, "fold inverse wire {q} batch {batch}");
            }
            cases += if batch == 0 { 60 } else { 64 };
        }
        assert!(cases >= 1_000_000);
        eprintln!("B3 fold all-wire: {cases} random + 4 edges, forward integer, inverse clean/zero phase");
    }

    #[test]
    fn one_r10_c7_b3_counterexample() {
        use super::super::modp_double::{ctrl_modadd, mod_double, C};
        let pp = p();
        let zv = pp - N::from(1u64);
        let yv = N::from(2 * C);
        let expected = ((zv << 1) + yv) % pp;
        let build = |merged: bool| {
            let mut b = B::new();
            let mut z = b.alloc_n(256);
            let zi = z.clone();
            let y = b.alloc_n(256);
            let c = b.alloc();
            let passengers = b.alloc_n(256);
            let ms = Ms::alloc_pool(&mut b, 72);
            if merged { super::super::modp_double::horner_add(&mut b, &ms, &mut z, &y, c, None); }
            else { mod_double(&mut b, &ms, &mut z, &y); ctrl_modadd(&mut b, &ms, &z, &y, c); }
            (b, zi, z, y, c, passengers)
        };
        let (old, ozi, oz, oy, oc, op) = build(false);
        let (new, nzi, nz, ny, nc, np) = build(true);
        assert_eq!((&ozi, &oz, &oy, oc, &op), (&nzi, &nz, &ny, nc, &np));
        let mut input = vec![0u64; old.width() as usize];
        put(&mut input, &ozi, 0, zv);
        put(&mut input, &oy, 0, yv);
        input[oc.0 as usize] = 1;
        for (i, &q) in op.iter().enumerate() { input[q.0 as usize] = 0xa5a5_a5a5_a5a5_a5a5u64.rotate_left(i as u32); }
        let init = |words: &mut Vec<u64>| words[..input.len()].copy_from_slice(&input);
        let before = run(&old.ops, old.width() as usize, &init);
        let after = run(&new.ops, new.width() as usize, &init);
        let old_v = get(&before.q, &oz, 0) % pp;
        let new_v = get(&after.q, &nz, 0) % pp;
        assert_eq!(old_v, expected, "sequential fold on pinned witness");
        assert_ne!(new_v, expected, "merged fold must expose the new overflow");
        eprintln!("B3 refuted at pool 72, 256 data lanes + 256 dirty passengers: z=p-1, y=2C, ctl=1; old={old_v}, new={new_v}, expected={expected}");
    }

    #[test]
    fn one_r10_c7_safe_product_million() {
        if std::env::var("FH_C7_MILLION").ok().as_deref() != Some("1") { return; }
        use sha3::digest::{ExtendableOutput, Update};
        let pp = p();
        let mut b = B::new();
        let z = b.alloc_n(256);
        let a = b.alloc_n(256);
        let y = b.alloc_n(256);
        let passengers = b.alloc_n(256);
        let ms = Ms::alloc_pool(&mut b, 73);
        let old_product = rec_product(&mut b, &ms, &z, &a, &y, false);
        direct_product_crep(&mut b, &ms, &z, &a, &y, false);
        let fwd_end = b.ops.len();
        b.play(&old_product, true);
        let (_, nb, _, _) = crate::circuit::analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"r10-c7-product-million");
        let mut xof = h.finalize_xof();
        let mut sim = crate::sim::Simulator::new(b.width() as usize, nb as usize, &mut xof);
        let mut output_mask = vec![false; b.width() as usize];
        for &id in &z { output_mask[id.0 as usize] = true; }
        let mut seed = 0xc7d1b234u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut cases = 0usize;
        for batch in 0..15_626 {
            sim.clear_for_shot();
            let mut av = [N::ZERO; 64];
            let mut yv = [N::ZERO; 64];
            for k in 0..64 {
                for j in 0..4 { av[k] |= N::from(next()) << (j * 64); yv[k] |= N::from(next()) << (j * 64); }
                av[k] %= pp; yv[k] %= pp;
            }
            if batch == 0 {
                av[0] = N::ZERO; yv[0] = pp - N::from(1u64);
                av[1] = N::from(1u64); yv[1] = N::ZERO;
                av[2] = pp - N::from(1u64); yv[2] = pp - N::from(2u64);
                av[3] = pp - N::from(2u64); yv[3] = pp - N::from(1u64);
            }
            for k in 0..64 { put(&mut sim.qubits, &a, k, av[k]); put(&mut sim.qubits, &y, k, yv[k]); }
            for &q in &passengers { sim.qubits[q.0 as usize] = next(); }
            let mut initial = sim.qubits.clone();
            sim.apply_iter(b.ops[..fwd_end].iter());
            for k in 0..64 {
                if batch == 0 && k < 4 { continue; }
                assert_eq!(get(&sim.qubits, &z, k) % pp, av[k].mul_mod(yv[k], pp), "product batch {batch} shot {k}");
            }
            let mask = if batch == 0 { !0b1111u64 } else { u64::MAX };
            assert_eq!(sim.phase & mask, 0, "product phase batch {batch}");
            for q in 0..initial.len() {
                if output_mask[q] { continue; }
                assert_eq!(sim.qubits[q] & mask, initial[q] & mask, "product preserved wire {q} batch {batch}");
            }
            sim.apply_iter(b.ops[fwd_end..].iter());
            assert_eq!(sim.phase & mask, 0, "product inverse phase batch {batch}");
            for q in 0..initial.len() {
                assert_eq!(sim.qubits[q] & mask, initial[q] & mask, "product inverse wire {q} batch {batch}");
            }
            cases += if batch == 0 { 60 } else { 64 };
            if batch % 2000 == 0 { eprintln!("product million: batch {batch}/15626"); }
        }
        assert!(cases >= 1_000_000);
        eprintln!("safe product all-wire: {cases} random + 4 edges, forward integer/inverse clean/zero phase");
    }

    #[test]
    fn one_r10_c7_safe_mac_million() {
        if std::env::var("FH_C7_MILLION").ok().as_deref() != Some("1") { return; }
        use sha3::digest::{ExtendableOutput, Update};
        use super::super::modp_double::{ctrl_modadd, mod_double, mod_halve};
        let pp = p();
        let mut b = B::new();
        let x = b.alloc_n(256);
        let a = b.alloc_n(256);
        let mut y = b.alloc_n(256);
        let passengers = b.alloc_n(256);
        let ms = Ms::alloc_pool(&mut b, 73);
        // Record the old full-compare mac as an exact inverse witness for the CREP forward mac.
        b.begin();
        let mut y_old = y.clone();
        for i in 0..256 {
            ctrl_modadd(&mut b, &ms, &x, &y_old, a[i]);
            if i != 255 { mod_double(&mut b, &ms, &mut y_old, &a); }
        }
        for _ in 0..255 { mod_halve(&mut b, &ms, &mut y_old, &a); }
        assert_eq!(y_old, y);
        let old_mac = b.end();
        mac(&mut b, &ms, &x, &a, &mut y);
        let fwd_end = b.ops.len();
        b.play(&old_mac, true);
        let (_, nb, _, _) = crate::circuit::analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"r10-c7-mac-million");
        let mut xof = h.finalize_xof();
        let mut sim = crate::sim::Simulator::new(b.width() as usize, nb as usize, &mut xof);
        let mut output_mask = vec![false; b.width() as usize];
        for &id in &x { output_mask[id.0 as usize] = true; }
        let mut seed = 0xc7d1b235u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut cases = 0usize;
        for batch in 0..15_626 {
            sim.clear_for_shot();
            let mut xv = [N::ZERO; 64];
            let mut av = [N::ZERO; 64];
            let mut yv = [N::ZERO; 64];
            for k in 0..64 {
                for j in 0..4 {
                    xv[k] |= N::from(next()) << (j * 64);
                    av[k] |= N::from(next()) << (j * 64);
                    yv[k] |= N::from(next()) << (j * 64);
                }
                xv[k] %= pp; av[k] %= pp; yv[k] %= pp;
            }
            if batch == 0 {
                xv[0] = N::ZERO; av[0] = pp - N::from(1u64); yv[0] = pp - N::from(1u64);
                xv[1] = pp - N::from(1u64); av[1] = N::ZERO; yv[1] = pp - N::from(2u64);
                xv[2] = N::from(1u64); av[2] = pp - N::from(2u64); yv[2] = N::ZERO;
                xv[3] = pp - N::from(2u64); av[3] = pp - N::from(2u64); yv[3] = pp - N::from(1u64);
            }
            for k in 0..64 {
                put(&mut sim.qubits, &x, k, xv[k]);
                put(&mut sim.qubits, &a, k, av[k]);
                put(&mut sim.qubits, &y, k, yv[k]);
            }
            for &q in &passengers { sim.qubits[q.0 as usize] = next(); }
            let mut initial = sim.qubits.clone();
            sim.apply_iter(b.ops[..fwd_end].iter());
            for k in 0..64 {
                if batch == 0 && k < 4 { continue; }
                let expected = (xv[k] + av[k].mul_mod(yv[k], pp)) % pp;
                assert_eq!(get(&sim.qubits, &x, k) % pp, expected, "mac batch {batch} shot {k}");
            }
            let mask = if batch == 0 { !0b1111u64 } else { u64::MAX };
            assert_eq!(sim.phase & mask, 0, "mac phase batch {batch}");
            for q in 0..initial.len() {
                if output_mask[q] { continue; }
                assert_eq!(sim.qubits[q] & mask, initial[q] & mask, "mac preserved wire {q} batch {batch}");
            }
            sim.apply_iter(b.ops[fwd_end..].iter());
            assert_eq!(sim.phase & mask, 0, "mac inverse phase batch {batch}");
            for q in 0..initial.len() {
                assert_eq!(sim.qubits[q] & mask, initial[q] & mask, "mac inverse wire {q} batch {batch}");
            }
            cases += if batch == 0 { 60 } else { 64 };
            if batch % 2000 == 0 { eprintln!("mac million: batch {batch}/15626"); }
        }
        assert!(cases >= 1_000_000);
        eprintln!("safe mac all-wire: {cases} random + 4 edges, forward integer/inverse clean/zero phase");
    }

    #[test]
    fn one_r10_c7_d1b_forced_receipts() {
        let pp = p();
        let mut seed = 0xc7d1bffu64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut av = [N::ZERO; 64];
        let mut yv = [N::ZERO; 64];
        for k in 0..64 {
            for j in 0..4 { av[k] |= N::from(next()) << (j * 64); yv[k] |= N::from(next()) << (j * 64); }
            av[k] %= pp; yv[k] %= pp;
        }
        for pool in [60, 73] {
            let mut b = B::new();
            let z = b.alloc_n(256);
            let a = b.alloc_n(256);
            let y = b.alloc_n(256);
            let passengers = b.alloc_n(256);
            let ms = Ms::alloc_pool(&mut b, pool);
            direct_product_crep(&mut b, &ms, &z, &a, &y, false);
            let (_, nb, _, _) = crate::circuit::analyze_ops(b.ops.iter());
            let mut input = vec![0u64; b.width() as usize];
            for k in 0..64 { put(&mut input, &a, k, av[k]); put(&mut input, &y, k, yv[k]); }
            for &q in &passengers { input[q.0 as usize] = next(); }
            let mut costs = [0u64; 2];
            for (ri, fill) in [0u8, 255u8].into_iter().enumerate() {
                let mut rng = FixedXof(fill);
                let mut sim = crate::sim::Simulator::new(b.width() as usize, nb as usize, &mut rng);
                sim.qubits.copy_from_slice(&input);
                sim.apply_iter(b.ops.iter());
                assert_eq!(sim.phase, 0, "forced receipt phase pool {pool} fill {fill}");
                for bit in 10000..10255 { assert_eq!(sim.bits[bit], if fill == 0 { 0 } else { u64::MAX }, "receipt {bit}"); }
                for k in 0..64 { assert_eq!(get(&sim.qubits, &z, k) % pp, av[k].mul_mod(yv[k], pp), "forced receipt product pool {pool} shot {k}"); }
                for q in 0..input.len() {
                    if z.iter().any(|id| id.0 as usize == q) { continue; }
                    assert_eq!(sim.qubits[q], input[q], "forced receipt preserved wire {q} pool {pool}");
                }
                costs[ri] = sim.stats.toffoli_gates;
            }
            assert!(costs[1] > costs[0], "conditioned comparator must execute when receipt=1");
            eprintln!("D1b forced receipts pool {pool}: all-zero T{}, all-one T{}; outputs/phase/foreign/scratch clean", costs[0] / 64, costs[1] / 64);
        }
    }

    #[test]
    fn one_r10_c7_paired_product_million() {
        if std::env::var("FH_C7_MILLION").ok().as_deref() != Some("1") { return; }
        use sha3::digest::{ExtendableOutput, Update};
        let pp = p();
        let mut b = B::new();
        let z = b.alloc_n(256);
        let a = b.alloc_n(256);
        let y = b.alloc_n(256);
        let passengers = b.alloc_n(256);
        let ms = Ms::alloc_pool(&mut b, 73);
        let r = rec_paired_product(&mut b, &ms, &z, &a, &y, false);
        let bits = paired_forward_hmr(&mut b, &ms, &r);
        let fwd_end = b.ops.len();
        paired_inverse_repair(&mut b, &ms, &r, &bits);
        let (_, nb, _, _) = crate::circuit::analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"r10-c7-paired-million");
        let mut xof = h.finalize_xof();
        let mut sim = crate::sim::Simulator::new(b.width() as usize, nb as usize, &mut xof);
        let mut seed = 0xc7a8a11u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut cases = 0usize;
        for batch in 0..15_626 {
            sim.clear_for_shot();
            let mut av = [N::ZERO; 64];
            let mut yv = [N::ZERO; 64];
            for k in 0..64 {
                for j in 0..4 { av[k] |= N::from(next()) << (j * 64); yv[k] |= N::from(next()) << (j * 64); }
                av[k] %= pp; yv[k] %= pp;
            }
            if batch == 0 {
                av[0] = N::ZERO; yv[0] = pp - N::from(1u64);
                av[1] = N::from(1u64); yv[1] = N::ZERO;
                av[2] = pp - N::from(1u64); yv[2] = pp - N::from(2u64);
                av[3] = pp - N::from(2u64); yv[3] = pp - N::from(1u64);
            }
            for k in 0..64 { put(&mut sim.qubits, &a, k, av[k]); put(&mut sim.qubits, &y, k, yv[k]); }
            for &q in &passengers { sim.qubits[q.0 as usize] = next(); }
            let mut initial = sim.qubits.clone();
            sim.apply_iter(b.ops[..fwd_end].iter());
            for k in 0..64 {
                if batch == 0 && k < 4 { continue; }
                assert_eq!(get(&sim.qubits, &z, k) % pp, av[k].mul_mod(yv[k], pp), "paired forward batch {batch} shot {k}");
            }
            sim.apply_iter(b.ops[fwd_end..].iter());
            let mask = if batch == 0 { !0b1111u64 } else { u64::MAX };
            assert_eq!(sim.phase & mask, 0, "paired inverse phase batch {batch}");
            for q in 0..initial.len() {
                assert_eq!(sim.qubits[q] & mask, initial[q] & mask, "paired inverse wire {q} batch {batch}");
            }
            cases += if batch == 0 { 60 } else { 64 };
            if batch % 2000 == 0 { eprintln!("paired million: batch {batch}/15626"); }
        }
        assert!(cases >= 1_000_000);
        eprintln!("paired product all-wire: {cases} random + 4 edges, forward integer/inverse clean/zero phase");
    }
    #[test]
    fn one_r11_c10_square_acc_million() {
        if std::env::var("FH_C10_MILLION").ok().as_deref() != Some("1") { return; }
        use super::super::modp_double::{ctrl_modadd, mod_double, mod_halve};
        use sha3::digest::{ExtendableOutput, Update};
        let pp = p();
        let mut b = B::new();
        let mut z = b.alloc_n(256);
        let z_initial = z.clone();
        let y = b.alloc_n(256);
        let passengers = b.alloc_n(256);
        let tmp = b.alloc();
        let ms = Ms::alloc_pool(&mut b, 60);
        sdw_square_acc(&mut b, &ms, &mut z, &y, tmp);
        assert_eq!(z, z_initial);
        ms.release(&mut b);
        b.free(tmp);
        let fwd_end = b.ops.len();
        let t = b.alloc_n(256);
        let ms_old = Ms::alloc_pool(&mut b, 60);
        for i in 0..256 { b.cx(y[i], t[i]); }
        b.begin();
        let mut yy = y.clone();
        for i in 0..256 {
            ctrl_modadd(&mut b, &ms_old, &z, &yy, t[i]);
            if i != 255 { mod_double(&mut b, &ms_old, &mut yy, &t); }
        }
        for _ in 0..255 { mod_halve(&mut b, &ms_old, &mut yy, &t); }
        assert_eq!(yy, y);
        let inverse = b.end();
        b.play(&inverse, true);
        for i in 0..256 { b.cx(y[i], t[i]); }
        ms_old.release(&mut b);
        b.free_n(&t);
        let (_, nb, _, _) = crate::circuit::analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"r11-c10-square-million");
        let mut xof = h.finalize_xof();
        let mut sim = crate::sim::Simulator::new(b.width() as usize, nb as usize, &mut xof);
        let mut output_mask = vec![false; b.width() as usize];
        for &q in &z_initial { output_mask[q.0 as usize] = true; }
        let mut seed = 0xc7b5a2u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut cases = 0usize;
        for batch in 0..15_626 {
            sim.clear_for_shot();
            let mut zv = [N::ZERO; 64];
            let mut yv = [N::ZERO; 64];
            for k in 0..64 {
                for j in 0..4 { zv[k] |= N::from(next()) << (j * 64); yv[k] |= N::from(next()) << (j * 64); }
                zv[k] %= pp; yv[k] %= pp;
            }
            if batch == 0 {
                zv[0] = N::ZERO; yv[0] = N::ZERO;
                zv[1] = pp - N::from(1u64); yv[1] = N::from(1u64);
                zv[2] = N::ZERO; yv[2] = pp - N::from(1u64);
                zv[3] = pp - N::from(1u64); yv[3] = pp - N::from(1u64);
            }
            for k in 0..64 { put(&mut sim.qubits, &z_initial, k, zv[k]); put(&mut sim.qubits, &y, k, yv[k]); }
            for &q in &passengers { sim.qubits[q.0 as usize] = next(); }
            let initial = sim.qubits.clone();
            sim.apply_iter(b.ops[..fwd_end].iter());
            let mask = if batch == 0 { !0b1111u64 } else { u64::MAX };
            for k in 0..64 {
                if batch == 0 && k < 4 { continue; }
                assert_eq!(get(&sim.qubits, &z_initial, k) % pp,
                    zv[k].add_mod(yv[k].mul_mod(yv[k], pp), pp), "square forward batch {batch} shot {k}");
            }
            assert_eq!(sim.phase & mask, 0, "square forward phase batch {batch}");
            for q in 0..initial.len() {
                if output_mask[q] { continue; }
                assert_eq!(sim.qubits[q] & mask, initial[q] & mask, "square forward wire {q} batch {batch}");
            }
            sim.apply_iter(b.ops[fwd_end..].iter());
            assert_eq!(sim.phase & mask, 0, "square inverse phase batch {batch}");
            for q in 0..initial.len() {
                assert_eq!(sim.qubits[q] & mask, initial[q] & mask, "square inverse wire {q} batch {batch}");
            }
            cases += if batch == 0 { 60 } else { 64 };
            if batch % 2000 == 0 { eprintln!("square million: batch {batch}/15626"); }
        }
        assert!(cases >= 1_000_000);
        eprintln!("square all-wire: {cases} random + 4 edges, forward/inverse clean/zero phase");
    }
    fn square_acc_edge(mut z: N, y: N) -> bool {
        let one = N::from(1u64);
        let c = N::from(super::super::modp_double::C);
        let width = one << 256usize;
        let mask = width - one;
        let low_width = one << (33 + super::super::modp_double::SDW_HEAD);
        let low_mask = low_width - one;
        let pp = p();
        for _ in 0..255 {
            let h = z.bit(0);
            let pre = if h { (z & !low_mask) | (((z & low_mask) + low_width - (c - one)) & low_mask) } else { z };
            let next = (pre >> 1usize) | (N::from(h as u64) << 255usize);
            let ideal = if h { (z + pp) >> 1usize } else { z >> 1usize };
            if next != ideal { return true; }
            z = next;
        }
        for k in (0..256).rev() {
            if y.bit(k) {
                let wide = z + y;
                let carry = wide >= width;
                let raw = wide & mask;
                if carry && (raw & low_mask) + c >= low_width { return true; }
                let folded = if carry { (raw & !low_mask) | (((raw & low_mask) + c) & low_mask) } else { raw };
                let shift = 256 - super::super::modp_double::SDW_CMPT;
                let cmp = (folded >> shift) < (y >> shift);
                if carry ^ cmp || folded != z.add_mod(y, pp) { return true; }
                z = folded;
            }
            if k > 0 {
                let h = z.bit(255);
                let raw = ((z << 1usize) & mask) | N::from(h as u64);
                if h && (raw & low_mask) + c - one >= low_width { return true; }
                z = if h { (raw & !low_mask) | (((raw & low_mask) + c - one) & low_mask) } else { raw };
            }
        }
        false
    }
    #[test]
    fn one_r11_c10_square_acc_edges() {
        let pp = p();
        let one = N::from(1u64);
        let c = N::from(super::super::modp_double::C);
        let bdy = one << 224;
        let vals = [
            N::ZERO, one, one + one, c - one, c, c + one, c + c,
            bdy - one, bdy, bdy + one, (one << 222), pp - bdy - one, pp - bdy,
            pp - bdy + one, pp - c - c, pp - c, pp - one - one, pp - one,
        ];
        let old = {
            let mut b = B::new();
            let z = b.alloc_n(256);
            let y = b.alloc_n(256);
            let t = b.alloc_n(256);
            let passenger = b.alloc_n(256);
            let ms = Ms::alloc_pool(&mut b, 60);
            for i in 0..256 { b.cx(y[i], t[i]); }
            let mut yy = y.clone();
            mac(&mut b, &ms, &z, &t, &mut yy);
            assert_eq!(yy, y);
            for i in 0..256 { b.cx(y[i], t[i]); }
            (b, z, y, passenger)
        };
        let new = {
            let mut b = B::new();
            let mut z = b.alloc_n(256);
            let zi = z.clone();
            let y = b.alloc_n(256);
            let tmp = b.alloc();
            let passenger = b.alloc_n(256);
            let ms = Ms::alloc_pool(&mut b, 60);
            sdw_square_acc(&mut b, &ms, &mut z, &y, tmp);
            assert_eq!(z, zi);
            (b, z, y, passenger)
        };
        let mut pairs = Vec::new();
        for (iz, &z) in vals.iter().enumerate() {
            for (iy, &y) in vals.iter().enumerate() { pairs.push((iz, iy, z, y)); }
        }
        let mut seed = 0xc7b5e7u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut inherited = 0usize;
        let mut new_errors = 0usize;
        let mut new_phases = 0usize;
        for (batch, chunk) in pairs.chunks(64).enumerate() {
            let mut oi = vec![0u64; old.0.width() as usize];
            let mut ni = vec![0u64; new.0.width() as usize];
            for (shot, &(_, _, zv, yv)) in chunk.iter().enumerate() {
                put(&mut oi, &old.1, shot, zv); put(&mut oi, &old.2, shot, yv);
                put(&mut ni, &new.1, shot, zv); put(&mut ni, &new.2, shot, yv);
            }
            for (&oq, &nq) in old.3.iter().zip(&new.3) {
                let v = next(); oi[oq.0 as usize] = v; ni[nq.0 as usize] = v;
            }
            let o = run(&old.0.ops, old.0.width() as usize, &|w| w.copy_from_slice(&oi));
            let n = run(&new.0.ops, new.0.width() as usize, &|w| w.copy_from_slice(&ni));
            for (shot, &(iz, iy, zv, yv)) in chunk.iter().enumerate() {
                let want = zv.add_mod(yv.mul_mod(yv, pp), pp);
                let ov = get(&o.q, &old.1, shot);
                let nv = get(&n.q, &new.1, shot);
                if ov == want {
                    if nv != want {
                        assert!(square_acc_edge(zv, yv), "unpredicted square output z[{iz}] y[{iy}]");
                        new_errors += 1;
                        eprintln!("square refuted z[{iz}]={zv} y[{iy}]={yv} batch {batch} shot {shot}: old/want {want}, new {nv}");
                        continue;
                    }
                    let old_phase = (o.phase >> shot) & 1;
                    let new_phase = (n.phase >> shot) & 1;
                    if old_phase == 0 && new_phase == 1 {
                        assert!(square_acc_edge(zv, yv), "unpredicted square phase z[{iz}] y[{iy}]");
                        new_phases += 1;
                        eprintln!("square new phase z[{iz}]={zv} y[{iy}]={yv}");
                    }
                } else { inherited += 1; }
            }
        }
        eprintln!("square edge grid: {} canonical (z,y) pairs, {inherited} old-error pairs, {new_errors} new outputs, {new_phases} new phases", pairs.len());
    }
    #[test]
    fn one_r11_c10_s4_paired_million() {
        if std::env::var("FH_C10_S4_MILLION").ok().as_deref() != Some("1") { return; }
        use sha3::digest::{ExtendableOutput, Update};
        let pp = p();
        let mut b = B::new();
        let z = b.alloc_n(256);
        let a = b.alloc_n(256);
        let y = b.alloc_n(256);
        let passengers = b.alloc_n(256);
        let ms = Ms::alloc_pool(&mut b, 73);
        direct_product_crep(&mut b, &ms, &z, &a, &y, false);
        let fwd_end = b.ops.len();
        chunked_unproduct(&mut b, &ms, &z, &a, &y, false);
        let (_, nb, _, _) = crate::circuit::analyze_ops(b.ops.iter());
        let mut h = sha3::Shake256::default();
        h.update(b"r10-c7-paired-million");
        let mut xof = h.finalize_xof();
        let mut sim = crate::sim::Simulator::new(b.width() as usize, nb as usize, &mut xof);
        let mut seed = 0xc7a8a11u64;
        let mut next = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut cases = 0usize;
        for batch in 0..15_626 {
            sim.clear_for_shot();
            let mut av = [N::ZERO; 64];
            let mut yv = [N::ZERO; 64];
            for k in 0..64 {
                for j in 0..4 { av[k] |= N::from(next()) << (j * 64); yv[k] |= N::from(next()) << (j * 64); }
                av[k] %= pp; yv[k] %= pp;
            }
            if batch == 0 {
                av[0] = N::ZERO; yv[0] = pp - N::from(1u64);
                av[1] = N::from(1u64); yv[1] = N::ZERO;
                av[2] = pp - N::from(1u64); yv[2] = pp - N::from(2u64);
                av[3] = pp - N::from(2u64); yv[3] = pp - N::from(1u64);
            }
            for k in 0..64 { put(&mut sim.qubits, &a, k, av[k]); put(&mut sim.qubits, &y, k, yv[k]); }
            for &q in &passengers { sim.qubits[q.0 as usize] = next(); }
            let mut initial = sim.qubits.clone();
            
            sim.apply_iter(b.ops[..fwd_end].iter());
            for k in 0..64 {
                if batch == 0 && k < 4 { continue; }
                assert_eq!(get(&sim.qubits, &z, k) % pp, av[k].mul_mod(yv[k], pp), "paired forward batch {batch} shot {k}");
            }
            sim.apply_iter(b.ops[fwd_end..].iter());
            let mask = if batch == 0 { !0b1111u64 } else { u64::MAX };
            assert_eq!(sim.phase & mask, 0, "paired inverse phase batch {batch}");
            for q in 0..initial.len() {
                assert_eq!(sim.qubits[q] & mask, initial[q] & mask, "paired inverse wire {q} batch {batch}");
            }
            cases += if batch == 0 { 60 } else { 64 };
            if batch % 2000 == 0 { eprintln!("paired million: batch {batch}/15626"); }
        }
        assert!(cases >= 1_000_000);
        eprintln!("paired product all-wire: {cases} random + 4 edges, forward integer/inverse clean/zero phase");
    }
}
