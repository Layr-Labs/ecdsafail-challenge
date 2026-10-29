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
use super::ft_adapter::{ft_call, ft_extra, Kind};
use super::modp_double::{ctrl_neg, load_bits, modadd, modsub, sdw_product_chunked, sdw_product_inv_chunked,
                         sdw_square_acc, Ms};
use super::pointadd_one::ck;
use super::greedyfrog::{windows, SlotBits, GreedyFrog, Win, cnt_bits, lb_bits, nslots};
use super::greedyfrog_model::W;
use crate::circuit::{BitId, QubitId};

/// out ^= AND of literals for long literal lists: chunks of 16 are ANDed into temps first (at most ~n/16 + 14
/// ancillas live), then the chunk results.
fn and_many(b: &mut B, lits: &[(QubitId, bool)], out: QubitId) {
    const CH: usize = 16;
    if lits.len() <= CH + 2 {
        super::greedyfrog::and_into(b, lits, out);
        return;
    }
    let chunks: Vec<&[(QubitId, bool)]> = lits.chunks(CH).collect();
    let tmp = b.alloc_n(chunks.len());
    for (c, &t) in chunks.iter().zip(&tmp) {
        super::greedyfrog::and_into(b, c, t);
    }
    let tl: Vec<(QubitId, bool)> = tmp.iter().map(|&q| (q, false)).collect();
    and_many(b, &tl, out);
    for (c, &t) in chunks.iter().zip(&tmp).rev() {
        super::greedyfrog::and_into(b, c, t);
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
fn start_consts(b: &mut B, u: &GreedyFrog, base0: usize) {
    let pp = super::refmodel_one::p();
    let o = W - 256;
    for k in 0..256 {
        if pp.bit(k) {
            b.x(u.x[o + k]);
        }
    }
    b.x(u.x[o - 1]); // marker under A = p (LA = 256)
    b.x(u.x[o - 2]); // tB = 1
    // LA = 256, held as 256 - base0 (gf G6b)
    let la0 = 256 - base0;
    assert!(la0 < (1usize << lb_bits()), "gf G6b: LA = 256 does not fit at base {base0}");
    for i in 0..lb_bits() {
        if (la0 >> i) & 1 == 1 {
            b.x(u.la[i]);
        }
    }
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
fn norm_input(b: &mut B, u: &GreedyFrog, undo: bool, base0: usize) {
    // LB - base0 = ~lz + (257 - base0) mod 2^bits (gf G6b; 257 for the submitted 9-bit registers)
    let k = (257isize - base0 as isize).rem_euclid(1isize << lb_bits()) as usize;
    let step = |b: &mut B, k: usize, inv: bool| {
        let n = 1usize << k;
        let lits: Vec<(QubitId, bool)> = (0..n).map(|i| (u.y[W - 1 - i], true)).collect();
        if inv {
            super::greedyfrog::crot_down(b, u.lb[k], &u.y, n);
            if super::greedyfrog::lean_norm() == 1 { super::arith::and_dirty(b, &lits, u.lb[k], &u.dirty) } else { and_many(b, &lits, u.lb[k]) }
        } else {
            if super::greedyfrog::lean_norm() == 1 { super::arith::and_dirty(b, &lits, u.lb[k], &u.dirty) } else { and_many(b, &lits, u.lb[k]) }
            super::greedyfrog::crot_up(b, u.lb[k], &u.y, n);
        }
    };
    let to_lb = |b: &mut B, inv: bool| {
        if inv {
            super::greedyfrog::add_const(b, &u.lb, k, true);
            for &q in &u.lb {
                b.x(q);
            }
        } else {
            for &q in &u.lb {
                b.x(q);
            }
            super::greedyfrog::add_const(b, &u.lb, k, false);
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
    let u = GreedyFrog { x, y, la: b.alloc_n(lb_bits()), lb: b.alloc_n(lb_bits()), cnt: vec![], par: refl, dirty: dirty.to_vec(),
                         cap: super::greedyfrog_peak() }
        .with_cnt();
    let mut u = u;
    super::greedyfrog::prof(b, "s.fwd_init");
    start_consts(b, &u, ws[0].base);
    norm_input(b, &u, false, ws[0].base);
    ck(b, "greedyfrog div_forward init");
    let mut bits = Vec::with_capacity(nslots());
    assert_eq!(ws[nslots() - 1].base, 0, "gf G6b: the last slot must have base 0 (LB = 1 at the end)");
    for s in 0..nslots() {
        if s > 0 {
            super::greedyfrog::prof(b, "s.rebase");
            u.rebase(b, ws[s - 1].base, ws[s].base);
        }
        bits.push(u.fwd_slot(b, &ws[s]));
    }
    ck(b, "greedyfrog div_forward traversal");
    super::greedyfrog::prof(b, "s.fwd_tail");
    end_consts(b, &u);
    let inv: Vec<QubitId> = (0..256).map(|i| u.x[W - 2 - i]).collect();
    // Y lanes 0..CNT_BITS hold the DONE counter (end_consts turned it into c) and stay live
    let mut parked: Vec<QubitId> = u.y[cnt_bits()..].to_vec();
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
    super::greedyfrog::prof(b, "s.mid_product");
    (UDiv { u, bits, parked }, inv)
}

/// Undo div_forward: sign, constants, inverse traversal, start state; frees the traversal state.
fn div_inverse(b: &mut B, mut dv: UDiv, refl: QubitId, dirty: &[QubitId], ws: &[Win]) {
    super::greedyfrog::prof(b, "s.inv_head");
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
        if s > 0 {
            super::greedyfrog::prof(b, "s.rebase");
            u.rebase(b, ws[s].base, ws[s - 1].base);
        }
    }
    ck(b, "greedyfrog div_inverse traversal");
    super::greedyfrog::prof(b, "s.inv_tail");
    norm_input(b, u, true, ws[0].base);
    debug_assert_eq!(u.par, refl);
    start_consts(b, u, ws[0].base);
    b.free_n(&u.x);
    b.free_n(&u.y[0..W - 256]);
    b.free_n(&u.la);
    b.free_n(&u.lb);
    ck(b, "greedyfrog div_inverse end");
    super::greedyfrog::prof(b, "s.post_div");
}

// ------------------------------------------------------------------ gf ft layer
// The shell's products and square on odinfree's modp_ft (Lilypad 852 tree), spliced into this builder by BitWonka's
// op-splicing adapter (e26536bc, ft_adapter.rs). Knob GF_FT: 0 keeps the sdw_* shell and its stream; 1 runs modp_ft
// at every site where a pool of at least GF_FT_MIN_ROOM lanes (default 32) fits under the cap, the sdw_* routine elsewhere.

fn ft_knob(name: &str, default: usize) -> usize {
    std::env::var(name).ok().and_then(|v| v.trim().parse().ok()).unwrap_or(default)
}

pub fn ft_shell() -> usize {
    static V: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *V.get_or_init(|| ft_knob("GF_FT", 1))
}

pub fn ft_min_room() -> usize {
    static V: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *V.get_or_init(|| ft_knob("GF_FT_MIN_ROOM", 32))
}

/// The pool modp_ft gets here: BitWonka's rule (the largest pool whose dry-built peak fits in cap - live), or None
/// when GF_FT is 0 or the pool would fall below ft_min_room() (the site then keeps its sdw_* routine).
fn ft_room(b: &B, kind: Kind, site: &str) -> Option<usize> {
    if ft_shell() == 0 {
        return None;
    }
    let free = super::greedyfrog_peak().saturating_sub(b.live) as usize;
    let mut room = free.min(256);
    let got = loop {
        if room < ft_min_room() {
            break None;
        }
        let extra = ft_extra(kind, room);
        if extra <= free {
            break Some(room);
        }
        room -= (extra - free).min(room);
    };
    if std::env::var("GF_FT_LOG").is_ok() {
        eprintln!("GF_FT site {site} {kind:?} live {} free {free} room {got:?}", b.live);
    }
    got
}

/// gf ft: z = a y mod p (negated if asked) into a zero z on modp_ft, if a pool fits; true if it ran.
fn ft_product(b: &mut B, z: &[QubitId], a: &[QubitId], y: &[QubitId], negate: bool, site: &str) -> bool {
    let Some(room) = ft_room(b, Kind::Product, site) else { return false };
    ft_call(b, Kind::Product, z, a, y, room);
    if negate {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, z, None, y);
        ms.release(b);
    }
    true
}

/// gf ft: reverse of ft_product (its pool fitted at the same live count).
fn ft_unproduct(b: &mut B, z: &[QubitId], a: &[QubitId], y: &[QubitId], negate: bool, site: &str) {
    if negate {
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, z, None, y);
        ms.release(b);
    }
    let room = ft_room(b, Kind::ProductInv, site).expect("gf ft: the unproduct's pool does not fit");
    ft_call(b, Kind::ProductInv, z, a, y, room);
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
    super::greedyfrog::prof(b, "s.dxdy_refl");
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
        if ft_product(b, &z, &inv, &y, false, "lambda1") {
            ck(b, "shell lambda product");
        } else {
            let ms = Ms::alloc(b);
            direct_product_crep(b, &ms, &z, &inv, &y, false);
            ck(b, "shell lambda product");
            ms.release(b);
        }
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
    super::greedyfrog::prof(b, "s.prod_dy");
    {
        let z = b.alloc_n(256);
        if ft_product(b, &z, &y, &x, false, "dy") {
            for i in 0..256 {
                b.z_if(z[i], m1[i]);
            }
            ft_unproduct(b, &z, &y, &x, false, "dy");
            b.free_n(&z);
        } else {
            let ms = Ms::alloc(b);
            direct_product_crep(b, &ms, &z, &y, &x, false);
            for i in 0..256 {
                b.z_if(z[i], m1[i]);
            }
            chunked_unproduct(b, &ms, &z, &y, &x, false);
            b.free_n(&z);
            ms.release(b);
        }
    }
    ck(b, "shell division 1 done");

    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    super::greedyfrog::prof(b, "s.square");
    {
        let tmp = b.alloc();
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, None, &y);
        if ft_shell() == 0 {
            let mut xx = x.clone();
            sdw_square_acc(b, &ms, &mut xx, &y, tmp);
            assert_eq!(xx, x);
            b.free(tmp);
            ms.release(b);
        } else {
            // the square's pool may use the lanes of greedyfrog's own scratch (BitWonka's site order)
            ms.release(b);
            b.free(tmp);
            if let Some(room) = ft_room(b, Kind::SquareAcc, "square") {
                ft_call(b, Kind::SquareAcc, &x, &[], &y, room);
            } else {
                let tmp = b.alloc();
                let ms = Ms::alloc(b);
                let mut xx = x.clone();
                sdw_square_acc(b, &ms, &mut xx, &y, tmp);
                assert_eq!(xx, x);
                b.free(tmp);
                ms.release(b);
            }
        }
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
    super::greedyfrog::prof(b, "s.prod_ndy");
    let m2 = b.fresh_bits(256);
    {
        let z = b.alloc_n(256);
        if !ft_product(b, &z, &y, &x, true, "ndy") {
            let ms = Ms::alloc(b);
            direct_product_crep(b, &ms, &z, &y, &x, true);
            ms.release(b);
        }
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
    super::greedyfrog::prof(b, "s.refl2");
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
        if ft_product(b, &z, &inv, &y, true, "lambda2") {
            for i in 0..256 {
                b.z_if(z[i], m2[i]);
            }
            ft_unproduct(b, &z, &inv, &y, true, "lambda2");
            b.free_n(&z);
        } else {
            let ms = Ms::alloc(b);
            direct_product_crep(b, &ms, &z, &inv, &y, true);
            for i in 0..256 {
                b.z_if(z[i], m2[i]);
            }
            chunked_unproduct(b, &ms, &z, &inv, &y, true);
            b.free_n(&z);
            ms.release(b);
        }
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
    super::greedyfrog::prof(b, "s.final");
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
    super::greedyfrog::prof(b, "end");
    ck(b, "end");
    (x, y)
}

#[cfg(test)]
mod tests {
    /// gf: builder counts of the whole point addition at the current knobs, without the post-passes or ops.bin
    /// (GF_COUNT=1). Prints GF_COUNT {ops, peak, width, builder_T (after adjacent-CCX cancellation), removed}.
    #[test]
    fn gf_count_builder() {
        if std::env::var("GF_COUNT").is_err() {
            return;
        }
        let mut b = B::new();
        point_add(&mut b);
        let removed = super::super::cancel_adjacent_ccx(&mut b.ops);
        let (_, native, expected) = super::super::counts(&b.ops);
        eprintln!("GF_COUNT {{\"ops\": {}, \"peak\": {}, \"width\": {}, \"builder_T\": {}, \"removed\": {}, \"gf_peak\": {}, \"native\": {native}, \"expected_raw\": {expected}}}",
                  b.ops.len(), b.peak, b.width(), b.tof - removed as u64, removed, super::super::greedyfrog_peak());
        super::super::greedyfrog::prof_dump();
    }

    use super::*;

    /// gf ft: 64-shot values mod p for the shell tests, sha-seeded from `tag`. edge: structured values instead (0, 1, 2,
    /// 3, p - 1, p - 2, (p - 1)/2, (p + 1)/2, 2^32, 2^64, 2^128, 2^255, c, p - c, 2^32 - 1, 2^256 - 2^224 mod p), drawn
    /// for z, a, y by fixed shot patterns; returns the values and each shot's (z, a, y) indices.
    fn ft_vals(tag: &[u8], k: usize, edge: bool) -> (Vec<Vec<N>>, Vec<[usize; 3]>) {
        let pp = p();
        let one = N::from(1u64);
        let c = N::from((1u64 << 32) + 977);
        let e: Vec<N> = vec![N::ZERO, one, N::from(2u64), N::from(3u64), pp - one, pp - N::from(2u64),
            (pp - one) >> 1, (pp + one) >> 1, one << 32, one << 64, one << 128, one << 255, c, pp - c,
            (one << 32) - one, ((one << 256) - (one << 224)) % pp];
        let idx: Vec<[usize; 3]> = (0..64).map(|s| [(3 * s + 7) % 16, s % 16, (s / 16 + 5 * s) % 16]).collect();
        let mut h = sha3::Shake256::default();
        h.update(b"gf-ft-vals");
        h.update(tag);
        let mut xof = h.finalize_xof();
        let mut out = vec![];
        for r in 0..k {
            let mut v = vec![];
            for s in 0..64 {
                let mut buf = [0u8; 40];
                sha3::digest::XofReader::read(&mut xof, &mut buf);
                let mut x = N::ZERO;
                for (i, &byte) in buf.iter().enumerate() {
                    x |= N::from(byte as u64) << (8 * i);
                }
                v.push(if edge { e[idx[s][r]] } else { x % pp });
            }
            out.push(v);
        }
        (out, idx)
    }

    fn ft_load(sim_q: &mut [u64], reg: &[QubitId], vals: &[N]) {
        for (s, v) in vals.iter().enumerate() {
            for (i, &q) in reg.iter().enumerate() {
                if v.bit(i) {
                    sim_q[q.0 as usize] |= 1u64 << s;
                }
            }
        }
    }

    fn ft_read(sim_q: &[u64], reg: &[QubitId], s: usize) -> N {
        let mut v = N::ZERO;
        for (i, &q) in reg.iter().enumerate() {
            if (sim_q[q.0 as usize] >> s) & 1 == 1 {
                v |= N::from(1u64) << i;
            }
        }
        v
    }

    /// One shell site on its own, old (sdw_*) or new (GF_FT path), with `pad` extra live qubits so the cap leaves
    /// the same free lanes as in the circuit. Returns the builder, the registers and the op index after the product.
    fn ft_site(kind: &str, pad: usize) -> (B, Vec<QubitId>, Vec<QubitId>, Vec<QubitId>, usize) {
        let mut b = B::new();
        let z = b.alloc_n(256);
        let a = b.alloc_n(256);
        let y = b.alloc_n(256);
        let _pad = b.alloc_n(pad);
        let mut mid = 0;
        match kind {
            "product" | "product_neg" => {
                let neg = kind == "product_neg";
                if !ft_product(&mut b, &z, &a, &y, neg, "test") {
                    let ms = Ms::alloc(&mut b);
                    direct_product_crep(&mut b, &ms, &z, &a, &y, neg);
                    ms.release(&mut b);
                    mid = b.ops.len();
                    let ms = Ms::alloc(&mut b);
                    chunked_unproduct(&mut b, &ms, &z, &a, &y, neg);
                    ms.release(&mut b);
                } else {
                    mid = b.ops.len();
                    ft_unproduct(&mut b, &z, &a, &y, neg, "test");
                }
            }
            "square" => {
                // z += y^2 on any z (a unused), exactly as the shell's square site after ctrl_neg
                if let Some(room) = ft_room(&b, Kind::SquareAcc, "test") {
                    ft_call(&mut b, Kind::SquareAcc, &z, &[], &y, room);
                } else {
                    let tmp = b.alloc();
                    let ms = Ms::alloc(&mut b);
                    let mut zz = z.clone();
                    sdw_square_acc(&mut b, &ms, &mut zz, &y, tmp);
                    assert_eq!(zz, z);
                    b.free(tmp);
                    ms.release(&mut b);
                }
                mid = b.ops.len();
            }
            _ => unreachable!(),
        }
        (b, z, a, y, mid)
    }

    /// gf ft: each shell site (product, negated product, their unproducts, the square) at the circuit's free lanes
    /// (GF_FT_PADS: extra live qubits beyond the three registers, so free = cap - 768 - pad), for the GF_FT setting of
    /// this process. Random mode (GF_FT_SEEDS rounds of 64 random values mod p): the product must equal a y (or -a y,
    /// mod p), the square z + y^2 mod p; after the unproduct z = 0; a, y restored; every other qubit |0>; phase 0. Run
    /// it with GF_FT=0 and GF_FT=1 and compare the printed value hashes: both shells must give the same values.
    /// Edge mode (GF_FT_EDGE=1): structured values; the wrong shots are listed, not asserted.
    #[test]
    fn gf_ft_shell_sites() {
        let Ok(pads) = std::env::var("GF_FT_PADS") else { return };
        let edge = std::env::var("GF_FT_EDGE").is_ok();
        let rounds = if edge { 1 } else { ft_knob("GF_FT_SEEDS", 1) };
        let pp = p();
        for pad in pads.split(',').map(|t| t.trim().parse::<usize>().unwrap()) {
            for kind in ["product", "product_neg", "square"] {
                let (b, z, a, y, mid) = ft_site(kind, pad);
                let mut digest = sha3::Shake256::default();
                let mut wrong: Vec<String> = vec![];
                let (mut dirty_rounds, mut phase_rounds) = (0usize, 0usize);
                for round in 0..rounds {
                    let tag = format!("{kind}-{pad}-{round}{}", if edge { "-edge" } else { "" });
                    let (vals, idx) = ft_vals(tag.as_bytes(), 3, edge);
                    let (zv, av, yv) = (&vals[0], &vals[1], &vals[2]);
                    let zv: Vec<N> = if kind == "square" { zv.clone() } else { vec![N::ZERO; 64] };
                    let av: Vec<N> = if kind == "square" { vec![N::ZERO; 64] } else { av.clone() };
                    let mut h = sha3::Shake256::default();
                    h.update(b"gf-ft-site");
                    h.update(tag.as_bytes());
                    let mut xof = h.finalize_xof();
                    let mut sim = Simulator::new(b.width() as usize, 200_000, &mut xof);
                    ft_load(&mut sim.qubits, &z, &zv);
                    ft_load(&mut sim.qubits, &a, &av);
                    ft_load(&mut sim.qubits, &y, yv);
                    sim.apply_iter(b.ops[..mid].iter());
                    for s in 0..64 {
                        let got = ft_read(&sim.qubits, &z, s);
                        let want = match kind {
                            "product" => av[s].mul_mod(yv[s], pp),
                            "product_neg" => (pp - av[s].mul_mod(yv[s], pp)) % pp,
                            _ => (zv[s] + yv[s].mul_mod(yv[s], pp)) % pp,
                        };
                        // the shell's ctrl_neg maps 0 to p (both shells share it): the negated product is checked mod p
                        let gotr = if kind == "product_neg" { got % pp } else { got };
                        if gotr != want {
                            let w = if kind == "square" { format!("z{} y{}", idx[s][0], idx[s][2]) } else { format!("a{} y{}", idx[s][1], idx[s][2]) };
                            wrong.push(if edge { w } else { format!("r{round}s{s}") });
                        }
                        for l in got.as_limbs() {
                            digest.update(&l.to_le_bytes());
                        }
                    }
                    sim.apply_iter(b.ops[mid..].iter());
                    for s in 0..64 {
                        let zr = ft_read(&sim.qubits, &z, s);
                        if (kind != "square" && zr != N::ZERO) || ft_read(&sim.qubits, &a, s) != av[s]
                            || ft_read(&sim.qubits, &y, s) != yv[s] {
                            wrong.push(format!("restore r{round}s{s}"));
                        }
                    }
                    if sim.phase != 0 {
                        phase_rounds += 1;
                    }
                    let regs: std::collections::BTreeSet<u64> = z.iter().chain(&a).chain(&y).map(|q| q.0).collect();
                    if (0..b.width()).any(|q| !regs.contains(&q) && sim.qubits[q as usize] != 0) {
                        dirty_rounds += 1;
                    }
                }
                let mut out = [0u8; 8];
                sha3::digest::XofReader::read(&mut digest.finalize_xof(), &mut out);
                let (_, _, exp) = super::super::counts(&b.ops);
                eprintln!("GF_FT_SITE {{\"kind\": \"{kind}\", \"pad\": {pad}, \"ft\": {}, \"edge\": {edge}, \"shots\": {}, \"free\": {}, \"peak\": {}, \"builder_T\": {}, \"expected_raw\": {exp}, \"values\": \"{}\", \"wrong\": {wrong:?}, \"phase_rounds\": {phase_rounds}, \"dirty_rounds\": {dirty_rounds}}}",
                          ft_shell(), 64 * rounds, super::super::greedyfrog_peak() as i64 - 768 - pad as i64, b.peak, b.tof,
                          out.iter().map(|x| format!("{x:02x}")).collect::<String>());
                if !edge {
                    assert!(wrong.is_empty() && phase_rounds == 0 && dirty_rounds == 0, "{kind} pad {pad}: {wrong:?}");
                }
            }
        }
    }

    /// gf ft: one shell block in its circuit context, on declared registers (unknown values to the post-passes) at
    /// the circuit's live count at cap GF_PEAK: lambda1 and lambda2 hold inv, y and GF_FT_MINI_PAD other live qubits
    /// (declared; default 9 = the G tree's counter and reflection bit, 8 on the idea8 trees with the 7-bit counter),
    /// dy and ndy hold y and x, the square holds x and y. Returns the block's ops.
    fn ft_block(kind: &str) -> Vec<crate::circuit::Op> {
        let mut b = B::new();
        let r0 = b.alloc_n(256);
        b.declare_qubits(0, &r0);
        let r1 = b.alloc_n(256);
        b.declare_qubits(1, &r1);
        let m = b.fresh_bits(256);
        if kind.starts_with("lambda") {
            let other = b.alloc_n(ft_knob("GF_FT_MINI_PAD", 9));
            b.declare_qubits(2, &other);
        }
        match kind {
            "lambda1" | "ndy" => {
                // lambda1: z = inv dy, then dy is measured; ndy: z = -(lambda dx'), then lambda is measured
                let (a, yy, neg) = if kind == "lambda1" { (&r0, &r1, false) } else { (&r1, &r0, true) };
                let z = b.alloc_n(256);
                if !ft_product(&mut b, &z, a, yy, neg, kind) {
                    let ms = Ms::alloc(&mut b);
                    direct_product_crep(&mut b, &ms, &z, a, yy, neg);
                    ms.release(&mut b);
                }
                let meas = &r1;
                for i in 0..256 {
                    b.hmr_to(meas[i], m[i]);
                }
                for i in 0..256 {
                    b.swap(z[i], meas[i]);
                }
                b.free_n(&z);
            }
            "dy" | "lambda2" => {
                let (a, yy, neg) = if kind == "dy" { (&r1, &r0, false) } else { (&r0, &r1, true) };
                let z = b.alloc_n(256);
                if ft_product(&mut b, &z, a, yy, neg, kind) {
                    for i in 0..256 {
                        b.z_if(z[i], m[i]);
                    }
                    ft_unproduct(&mut b, &z, a, yy, neg, kind);
                    b.free_n(&z);
                } else {
                    let ms = Ms::alloc(&mut b);
                    direct_product_crep(&mut b, &ms, &z, a, yy, neg);
                    for i in 0..256 {
                        b.z_if(z[i], m[i]);
                    }
                    chunked_unproduct(&mut b, &ms, &z, a, yy, neg);
                    b.free_n(&z);
                    ms.release(&mut b);
                }
            }
            "square" => {
                let (x, y) = (&r0, &r1);
                let tmp = b.alloc();
                let ms = Ms::alloc(&mut b);
                ctrl_neg(&mut b, &ms, x, None, y);
                if ft_shell() == 0 {
                    let mut xx = x.clone();
                    sdw_square_acc(&mut b, &ms, &mut xx, y, tmp);
                    assert_eq!(&xx, x);
                    b.free(tmp);
                    ms.release(&mut b);
                } else {
                    ms.release(&mut b);
                    b.free(tmp);
                    if let Some(room) = ft_room(&b, Kind::SquareAcc, "square") {
                        ft_call(&mut b, Kind::SquareAcc, x, &[], y, room);
                    } else {
                        let tmp = b.alloc();
                        let ms = Ms::alloc(&mut b);
                        let mut xx = x.clone();
                        sdw_square_acc(&mut b, &ms, &mut xx, y, tmp);
                        assert_eq!(&xx, x);
                        b.free(tmp);
                        ms.release(&mut b);
                    }
                }
            }
            _ => unreachable!(),
        }
        b.ops
    }

    /// gf ft: the shell's five product and square blocks, each in its circuit context (ft_block) at cap GF_PEAK, through
    /// the build's post-passes (truth tables to a fixed point, nine-atom tables, the conditional-AND pass mfsur, the
    /// catalog rewrite). Prints the expected T before and after per block (GF_FT_MINI=1). The lease pass is not run.
    #[test]
    fn gf_ft_mini_shell() {
        if std::env::var("GF_FT_MINI").is_err() {
            return;
        }
        let (mut tb, mut ta) = (0.0, 0.0);
        for kind in ["lambda1", "dy", "square", "ndy", "lambda2"] {
            let mut ops = ft_block(kind);
            let _ = super::super::cancel_adjacent_ccx(&mut ops);
            let (_, _, before) = super::super::counts(&ops);
            for _ in 1..=32 {
                let prev = super::super::counts(&ops);
                ops = super::super::truth_simplify::simplify_products(ops);
                if super::super::counts(&ops) == prev {
                    break;
                }
            }
            ops = super::super::classical_wide::simplify_products(ops);
            ops = super::super::cond_pass::run_with(ops, "mfsur");
            let (_, _, mid) = super::super::counts(&ops);
            ops = super::super::frontier_rewrite::apply(ops);
            let (_, _, after) = super::super::counts(&ops);
            tb += before;
            ta += after;
            eprintln!("GF_FT_MINI {{\"block\": \"{kind}\", \"ft\": {}, \"gf_peak\": {}, \"raw\": {before}, \"after_cond\": {mid}, \"after_all\": {after}}}",
                      ft_shell(), super::super::greedyfrog_peak());
        }
        eprintln!("GF_FT_MINI {{\"block\": \"all\", \"ft\": {}, \"gf_peak\": {}, \"raw\": {tb}, \"after_all\": {ta}, \"cut\": {}}}",
                  ft_shell(), super::super::greedyfrog_peak(), tb - ta);
    }

    /// gf ft: the whole point addition at this process's knobs on GF_WHOLE batches of 64 random secp256k1 pairs,
    /// simulated as the evaluator does (on the builder stream, before the post-passes): classical mismatches,
    /// phase-garbage and ancilla-garbage batches, the failing shots (classical, phase or ancilla, per shot) and the
    /// average executed Toffoli. GF_WHOLE_SEED salts the inputs; GF_WHOLE_SIMSALT salts only the measurement draws, so
    /// the same inputs can be re-run under new draws (per-input failure rates, not row-by-row A/B).
    #[test]
    fn gf_ft_whole_point_add() {
        use alloy_primitives::U256;
        use crate::circuit::QubitOrBit;
        let Some(nbatch) = std::env::var("GF_WHOLE").ok().and_then(|v| v.parse::<usize>().ok()) else { return };
        let salt = std::env::var("GF_WHOLE_SEED").unwrap_or_default();
        let simsalt = std::env::var("GF_WHOLE_SIMSALT").unwrap_or_default();
        let mut b = B::new();
        point_add(&mut b);
        let removed = super::super::cancel_adjacent_ccx(&mut b.ops);
        let ops = std::mem::take(&mut b.ops);
        let (total_qubits, num_bits, _, regs) = crate::circuit::analyze_ops(ops.iter());
        assert_eq!(regs.len(), 4);
        let hx = |s: &str| U256::from_str_radix(s, 16).unwrap();
        let curve = crate::weierstrass_elliptic_curve::WeierstrassEllipticCurve {
            modulus: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F"),
            a: U256::from(0),
            b: U256::from(7),
            gx: hx("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
            gy: hx("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
            order: hx("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),
        };
        let mut h = sha3::Shake256::default();
        h.update(b"gf-ft-whole");
        h.update(salt.as_bytes());
        let mut xin = h.finalize_xof();
        let mut hs = sha3::Shake256::default();
        hs.update(b"gf-ft-whole-sim");
        hs.update(salt.as_bytes());
        hs.update(simsalt.as_bytes());
        let mut xsim = hs.finalize_xof();
        let mut sim = Simulator::new(total_qubits as usize, num_bits as usize, &mut xsim);
        let (mut classical, mut phase_b, mut anc_b, mut shots) = (0usize, 0usize, 0usize, 0usize);
        let mut bad_shots: Vec<usize> = vec![];
        for batch in 0..nbatch {
            let mut ins = vec![];
            while ins.len() < 64 {
                let mut rb = [[0u8; 32]; 2];
                sha3::digest::XofReader::read(&mut xin, &mut rb[0]);
                sha3::digest::XofReader::read(&mut xin, &mut rb[1]);
                let t = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(rb[0]));
                let o = curve.mul(curve.gx, curve.gy, U256::from_le_bytes(rb[1]));
                if t.0 == o.0 || (t.0.is_zero() && t.1.is_zero()) || (o.0.is_zero() && o.1.is_zero()) {
                    continue;
                }
                let e = curve.add(t.0, t.1, o.0, o.1);
                ins.push((t, o, e));
            }
            sim.clear_for_shot();
            for (s, (t, o, _)) in ins.iter().enumerate() {
                sim.set_register(&regs[0], t.0, s);
                sim.set_register(&regs[1], t.1, s);
                sim.set_register(&regs[2], o.0, s);
                sim.set_register(&regs[3], o.1, s);
            }
            sim.apply_iter(ops.iter());
            let mut badmask = 0u64;
            for (s, (_, _, e)) in ins.iter().enumerate() {
                if sim.get_register(&regs[0], s) != e.0 || sim.get_register(&regs[1], s) != e.1 {
                    classical += 1;
                    badmask |= 1u64 << s;
                }
            }
            if sim.phase != 0 {
                phase_b += 1;
                badmask |= sim.phase;
            }
            for r in &regs {
                for qb in r {
                    if let QubitOrBit::Qubit(q) = *qb {
                        *sim.qubit_mut(q) = 0;
                    }
                }
            }
            let anc = (0..total_qubits).fold(0u64, |m, q| m | sim.qubit(crate::circuit::QubitId(q)));
            if anc != 0 {
                anc_b += 1;
                badmask |= anc;
            }
            for s in 0..64 {
                if (badmask >> s) & 1 == 1 {
                    bad_shots.push(batch * 64 + s);
                }
            }
            shots += 64;
        }
        eprintln!("GF_WHOLE {{\"gf_ft\": {}, \"gf_peak\": {}, \"qubits\": {total_qubits}, \"ops\": {}, \"removed\": {removed}, \"shots\": {shots}, \"classical_mismatches\": {classical}, \"bad_shots\": {bad_shots:?}, \"phase_garbage_batches\": {phase_b}, \"ancilla_garbage_batches\": {anc_b}, \"avg_executed_toffoli\": {}, \"salt\": \"{salt}\", \"simsalt\": \"{simsalt}\"}}",
                  ft_shell(), super::super::greedyfrog_peak(), ops.len(),
                  sim.stats.toffoli_gates as f64 / shots as f64);
    }
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
        let mut sim = Simulator::new(b.width() as usize, 80_000, &mut xof);
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
        let mut sim = Simulator::new(b.width() as usize, 80_000, &mut xof);
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
