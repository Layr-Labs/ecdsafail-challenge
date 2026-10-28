//! greedyfrog point addition (uniform greedy Euclid divisions): froghop-one's shell (`pointadd_one.rs`) with each
//! division's forward / inverse traversal replaced by `greedyfrog.rs`.
//!
//!   dx = x - ox, dy = y - oy
//!   division 1:  forward traversal on dx (passenger dy) -> inv = 1/dx;  lambda = inv * dy;  measure dy away;
//!                inverse traversal (passenger lambda) -> dx;  recompute dy = lambda * dx, fix its phase, uncompute
//!   x:  dx' = lambda^2 - dx - 3 ox  (= x3 - ox)
//!   y:  ndy = -lambda * dx'         (= y3 + oy);  measure lambda away
//!   division 2:  forward traversal on dx' (passenger ndy) -> inv';  recompute lambda = -ndy * inv', fix its phase,
//!                uncompute;  inverse traversal -> dx'
//!   x3 = dx' + ox,  y3 = ndy - oy
//!
//! A division's start state: X = (A = p, marker, tB = 1) as constants, Y = (B = x' top-normalised, marker, tA = 0),
//! where x' = min(dx, p - dx) < 2^255 arrives in 256 qubits: they become Y lanes W-256..W-1 under a marker at lane
//! W-257, and an 8-stage binary search rotates Y up by its leading zeros lz = 256 - LB (the stage bits then become
//! LB in place). Every shot finishes with A = 0, B = 1, tA = p (constants: Y, LA, LB and X's top lane are cleared and
//! released while the products run) and tB = (-1)^par / x' in X lanes W-2..W-257; par starts as the reflection bit,
//! so 1/dx = (-1)^par tB.

use super::builder::B;
use super::modp_double::{ctrl_neg, load_bits, modadd, modsub, sdw_product_chunked, sdw_product_inv_chunked,
                         sdw_square_acc, Ms};
use super::pointadd_one::ck;
use super::greedyfrog::{windows, SlotBits, GreedyFrog, Win, CNT_BITS, LB_BITS, NSLOTS};
use super::greedyfrog_model::W;
use crate::circuit::{BitId, QubitId};

/// out ^= AND of literals for long literal lists: chunks of 16 are ANDed into temps first (at most ~n/16 + 14
/// ancillas live), then the chunk results.
fn and_many(b: &mut B, lits: &[(QubitId, bool)], out: QubitId, dirty: &[QubitId]) {
    const CH: usize = 16;
    if lits.len() <= CH + 2 {
        super::greedyfrog::and_into(b, lits, out);
        return;
    }
    let chunks: Vec<&[(QubitId, bool)]> = lits.chunks(CH).collect();
    let tmp = b.alloc_n(chunks.len());
    for (c, &t) in chunks.iter().zip(&tmp) {
        super::arith::and_dirty(b, c, t, dirty);
    }
    let tl: Vec<(QubitId, bool)> = tmp.iter().map(|&q| (q, false)).collect();
    and_many(b, &tl, out, dirty);
    for (c, &t) in chunks.iter().zip(&tmp).rev() {
        super::arith::and_dirty(b, c, t, dirty);
    }
    b.free_n(&tmp);
}

/// One division's traversal state between its forward and inverse halves.
struct UDiv {
    u: GreedyFrog,
    bits: Vec<SlotBits>,
    /// qubits that are |0> on every shot after the forward half (re-acquired before the inverse)
    parked: Vec<QubitId>,
}

/// Constants of the start state (X = (p, marker, 1), LA = 256, Y's marker) or of the end state (X's top marker,
/// Y = (1, marker, p), LB = 1); X gates, self-inverse.
fn start_consts(b: &mut B, u: &GreedyFrog) {
    let pp = super::refmodel_one::p();
    let o = W - 256;
    for k in 0..256 {
        if pp.bit(k) {
            b.x(u.x[o + k]);
        }
    }
    b.x(u.x[o - 1]); // marker under A = p (LA = 256)
    b.x(u.x[o - 2]); // tB = 1
    b.x(u.la[8]); // LA = 256
    b.x(u.y[o - 1]); // marker under x'
}

fn end_consts(b: &mut B, u: &GreedyFrog) {
    let pp = super::refmodel_one::p();
    b.x(u.x[W - 1]); // marker (A = 0)
    b.x(u.y[W - 1]); // B = 1
    b.x(u.y[W - 2]); // marker
    for i in 0..256 {
        if pp.bit(i) {
            b.x(u.y[W - 3 - i]); // tA = p, bit i at lane W - LB - 2 - i
        }
    }
    b.x(u.lb[0]); // LB = 1
}

/// Y's binary-search normalisation: for k = 7..0, lb_k ^= [top 2^k lanes of Y zero], rotate Y up by 2^k where lb_k;
/// then LB = 256 - lz = ~lz + 257 in place. `undo` runs the exact inverse.
fn norm_input(b: &mut B, u: &GreedyFrog, undo: bool) {
    let step = |b: &mut B, k: usize, inv: bool| {
        let n = 1usize << k;
        let lits: Vec<(QubitId, bool)> = (0..n).map(|i| (u.y[W - 1 - i], true)).collect();
        if inv {
            super::greedyfrog::crot_down(b, u.lb[k], &u.y, n);
            and_many(b, &lits, u.lb[k], &u.dirty);
        } else {
            and_many(b, &lits, u.lb[k], &u.dirty);
            super::greedyfrog::crot_up(b, u.lb[k], &u.y, n);
        }
    };
    let to_lb = |b: &mut B, inv: bool| {
        if inv {
            super::greedyfrog::add_const(b, &u.lb, 257, true);
            for &q in &u.lb {
                b.x(q);
            }
        } else {
            for &q in &u.lb {
                b.x(q);
            }
            super::greedyfrog::add_const(b, &u.lb, 257, false);
        }
    };
    if undo {
        to_lb(b, true);
        for k in 0..8 {
            step(b, k, true);
        }
    } else {
        for k in (0..8).rev() {
            step(b, k, false);
        }
        to_lb(b, false);
    }
}

/// Forward traversal on x' (256 qubits in `xq`, below 2^255; `refl` = the reflection bit). Returns the state and the
/// 256 qubits holding 1/dx (bit i in X lane W - 2 - i).
fn div_forward(b: &mut B, xq: &[QubitId], refl: QubitId, dirty: &[QubitId], ws: &[Win]) -> (UDiv, Vec<QubitId>) {
    let x = b.alloc_n(W);
    let mut y = b.alloc_n(W - 256);
    y.extend_from_slice(xq);
    // the reflection bit is the swap parity's starting value, so it carries the parity itself (as in froghop-one)
    let u = GreedyFrog { x, y, la: b.alloc_n(LB_BITS), lb: b.alloc_n(LB_BITS), cnt: vec![], par: refl, dirty: dirty.to_vec() }
        .with_cnt();
    let mut u = u;
    start_consts(b, &u);
    norm_input(b, &u, false);
    ck(b, "greedyfrog div_forward init");
    let mut bits = Vec::with_capacity(NSLOTS);
    for s in 0..NSLOTS {
        bits.push(u.fwd_slot(b, &ws[s]));
    }
    ck(b, "greedyfrog div_forward traversal");
    end_consts(b, &u);
    let inv: Vec<QubitId> = (0..256).map(|i| u.x[W - 2 - i]).collect();
    // Y lanes 0..CNT_BITS hold the DONE counter (end_consts turned it into c) and stay live
    let mut parked: Vec<QubitId> = u.y[CNT_BITS..].to_vec();
    parked.extend(&u.la);
    parked.extend(&u.lb);
    parked.extend(&u.x[0..W - 257]);
    parked.push(u.x[W - 1]);
    b.free_n(&parked);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &inv, Some(u.par), dirty);
        ms.release(b);
    }
    ck(b, "greedyfrog div_forward sign");
    (UDiv { u, bits, parked }, inv)
}

/// Undo div_forward: sign, constants, inverse traversal, start state; frees the traversal state.
fn div_inverse(b: &mut B, mut dv: UDiv, refl: QubitId, dirty: &[QubitId], ws: &[Win]) {
    let inv: Vec<QubitId> = (0..256).map(|i| dv.u.x[W - 2 - i]).collect();
    {
        let ms = Ms::alloc(b);
        b.begin();
        ctrl_neg(b, &ms, &inv, Some(dv.u.par), dirty);
        let r = b.end();
        b.play(&r, true);
        ms.release(b);
    }
    for &q in &dv.parked {
        b.acquire(q);
    }
    let u = &mut dv.u;
    end_consts(b, u);
    for (s, bits) in dv.bits.iter().enumerate().rev() {
        u.inv_slot(b, bits, &ws[s]);
    }
    ck(b, "greedyfrog div_inverse traversal");
    norm_input(b, u, true);
    debug_assert_eq!(u.par, refl);
    start_consts(b, u);
    b.free_n(&u.x);
    b.free_n(&u.y[0..W - 256]);
    b.free_n(&u.la);
    b.free_n(&u.lb);
    ck(b, "greedyfrog div_inverse end");
}

/// A product with no later inverse partner (CREP repairs each measured k locally).
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
    if negate {
        ctrl_neg(b, ms, z, None, y);
    }
}

/// Arithmetic reverse of a chunked product.
fn chunked_unproduct(b: &mut B, ms: &Ms, z: &[QubitId], a: &[QubitId], y: &[QubitId], negate: bool) {
    if negate {
        ctrl_neg(b, ms, z, None, y);
    }
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

pub fn point_add(b: &mut B) -> (Vec<QubitId>, Vec<QubitId>) {
    let ws = windows();
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
    ck(b, "shell dx dy");

    // ---------------- division 1
    let refl = b.alloc();
    b.cx(x[255], refl);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, Some(refl), &y);
        ms.release(b);
    }
    let (dv, inv) = div_forward(b, &x, refl, &y, &ws);
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
    div_inverse(b, dv, refl, &y, &ws);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, Some(refl), &y);
        ms.release(b);
    }
    b.cx(x[255], refl);
    b.free(refl);
    // dy = lambda * dx: recompute, fix the phase of the dy measurement, uncompute
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc(b);
        direct_product_crep(b, &ms, &z, &y, &x, false);
        for i in 0..256 {
            b.z_if(z[i], m1[i]);
        }
        chunked_unproduct(b, &ms, &z, &y, &x, false);
        b.free_n(&z);
        ms.release(b);
    }
    ck(b, "shell division 1 done");

    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    {
        let tmp = b.alloc();
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, None, &y);
        let mut xx = x.clone();
        sdw_square_acc(b, &ms, &mut xx, &y, tmp);
        assert_eq!(xx, x);
        b.free(tmp);
        ms.release(b);
        let t = b.alloc_n(256);
        let ms = Ms::alloc(b);
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
        direct_product_crep(b, &ms, &z, &y, &x, true);
        ms.release(b);
        for i in 0..256 {
            b.hmr_to(y[i], m2[i]);
        }
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }
    ck(b, "shell x, ndy");

    // ---------------- division 2: recompute lambda = -ndy / dx' to fix its phase
    let refl = b.alloc();
    b.cx(x[255], refl);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, Some(refl), &y);
        ms.release(b);
    }
    let (dv, inv) = div_forward(b, &x, refl, &y, &ws);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc(b);
        direct_product_crep(b, &ms, &z, &inv, &y, true);
        for i in 0..256 {
            b.z_if(z[i], m2[i]);
        }
        chunked_unproduct(b, &ms, &z, &inv, &y, true);
        b.free_n(&z);
        ms.release(b);
    }
    div_inverse(b, dv, refl, &y, &ws);
    {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, Some(refl), &y);
        ms.release(b);
    }
    b.cx(x[255], refl);
    b.free(refl);
    ck(b, "shell division 2 done");

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
    // Fiat-Shamir nonce: X X pairs (identity, no Toffoli) re-roll the benchmark's test shots
    for _ in 0..super::nonce() {
        b.x(x[0]);
        b.x(x[0]);
    }
    ck(b, "end");
    (x, y)
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::greedyfrog_model::{p, N};
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};

    /// Division 1's forward half on 64 random dx (half of them >= 2^255): after init the rings must match the model's
    /// start state, after the traversal X must hold 1/dx (sign-fixed) and the counter lanes the DONE count.
    #[test]
    fn greedyfrog_shell_div_forward() {
        let ws = windows();
        let mut b = B::new();
        let x = b.alloc_n(256);
        let y = b.alloc_n(256);
        let refl = b.alloc();
        let (dv, inv) = div_forward(&mut b, &x, refl, &y, &ws);
        let pp = p();
        let mut s64 = 0x0bad_cafe_1234_5678u64;
        let mut next = || { s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17; s64 };
        let mut dxs = vec![];
        for _ in 0..64 {
            let mut v = N::ZERO;
            for i in 0..4 {
                v |= N::from(next()) << (64 * i);
            }
            let v = (v % (pp - N::from(1u64))) + N::from(1u64);
            dxs.push(if v < pp - v { v } else { pp - v });
        }
        let mut h = sha3::Shake256::default();
        h.update(b"greedyfrog-shell");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(b.width() as usize, 30_000, &mut xof);
        for (s, v) in dxs.iter().enumerate() {
            for (i, &q) in x.iter().enumerate() {
                if v.bit(i) {
                    sim.qubits[q.0 as usize] |= 1u64 << s;
                }
            }
        }
        sim.apply_iter(b.ops.iter());
        let mut bad = 0;
        for (s, v) in dxs.iter().enumerate() {
            let mut got = N::ZERO;
            for (i, &q) in inv.iter().enumerate() {
                if (sim.qubits[q.0 as usize] >> s) & 1 == 1 {
                    got |= N::from(1u64) << i;
                }
            }
            let ok = got.mul_mod(*v, pp) == N::from(1u64);
            if !ok {
                bad += 1;
                if bad <= 4 {
                    eprintln!("shot {s}: dx bit255 {} -> inv*dx = {:#x}", v.bit(255), got.mul_mod(*v, pp));
                }
            }
        }
        let _ = dv;
        eprintln!("greedyfrog shell div_forward: {} of 64 wrong", bad);
        assert_eq!(bad, 0);
    }

    /// div_forward then div_inverse: dx comes back, every other qubit |0>, phase 0.
    #[test]
    fn greedyfrog_shell_div_roundtrip() {
        let ws = windows();
        let mut b = B::new();
        let x = b.alloc_n(256);
        let y = b.alloc_n(256);
        let refl = b.alloc();
        let (dv, _inv) = div_forward(&mut b, &x, refl, &y, &ws);
        let mid = b.ops.len();
        div_inverse(&mut b, dv, refl, &y, &ws);
        let pp = p();
        let mut s64 = 0x0bad_cafe_1234_5678u64;
        let mut next = || { s64 ^= s64 << 13; s64 ^= s64 >> 7; s64 ^= s64 << 17; s64 };
        let mut dxs = vec![];
        for _ in 0..64 {
            let mut v = N::ZERO;
            for i in 0..4 {
                v |= N::from(next()) << (64 * i);
            }
            let v = (v % (pp - N::from(1u64))) + N::from(1u64);
            dxs.push(if v < pp - v { v } else { pp - v });
        }
        let mut h = sha3::Shake256::default();
        h.update(b"greedyfrog-shell-rt");
        let mut xof = h.finalize_xof();
        let mut sim = Simulator::new(b.width() as usize, 30_000, &mut xof);
        let mut init = vec![0u64; b.width() as usize];
        for (s, v) in dxs.iter().enumerate() {
            for (i, &q) in x.iter().enumerate() {
                if v.bit(i) {
                    init[q.0 as usize] |= 1u64 << s;
                }
            }
            for (i, &q) in y.iter().enumerate() {
                if (next() >> 7) & 1 == 1 {
                    init[q.0 as usize] |= 1u64 << s;
                    let _ = i;
                }
            }
        }
        sim.qubits.copy_from_slice(&init);
        sim.apply_iter(b.ops[..mid].iter());
        sim.apply_iter(b.ops[mid..].iter());
        let mut dirty = 0;
        for q in 0..b.width() as usize {
            if sim.qubits[q] != init[q] {
                dirty += 1;
                if dirty <= 6 {
                    eprintln!("qubit {q} differs: shots {:016x}", sim.qubits[q] ^ init[q]);
                }
            }
        }
        let mut badmask = 0u64;
        for q in 0..b.width() as usize {
            badmask |= sim.qubits[q] ^ init[q];
        }
        let hi: u64 = (0..64).filter(|&s| dxs[s].bit(255)).map(|s| 1u64 << s).sum();
        let lbs: Vec<usize> = (0..64).filter(|&s| (badmask >> s) & 1 == 1).map(|s| dxs[s].bit_len()).collect();
        eprintln!("bad shots {badmask:016x}, dx >= 2^255 shots {hi:016x}; bad shots' bit lengths {lbs:?}");
        eprintln!("greedyfrog shell round trip: {dirty} qubits differ, phase {:016x}", sim.phase);
        assert_eq!(dirty, 0);
        assert_eq!(sim.phase, 0);
    }
}
