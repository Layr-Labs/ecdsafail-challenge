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
use super::ft_adapter::{ft_call_capped, ft_call_capped_ext, native_sub_square, Kind};
use super::modp_double::{ctrl_neg, load_bits, modadd, modsub, sdw_product_chunked, sdw_product_inv_chunked,
                         sdw_square_acc, Ms};
use super::pointadd_one::ck;
use super::greedyfrog::{windows, SlotBits, GreedyFrog, Win, CNT_BITS, LB_BITS, NSLOTS};
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
            and_many(b, &lits, u.lb[k]);
        } else {
            and_many(b, &lits, u.lb[k]);
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
    let u = GreedyFrog { x, y, la: b.alloc_n(LB_BITS), lb: b.alloc_n(LB_BITS), cnt: vec![], par: refl, dirty: dirty.to_vec(),
                         cap: *super::PEAK }
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
    // CNT7-PARK (B-CRUMBS, I1-VERIFY): c = 254 - finish slot <= 100 on every shot that passes (a walk finishing before
    // the act_const slots, s + ACT_MARGIN < first_done, already fails there), so counter lane 7 is |0> here and is
    // released with the parked lanes (one more lane for the shell's pools)
    let cnt_keep = if cnt7_park() { CNT_BITS - 1 } else { CNT_BITS };
    let mut parked: Vec<QubitId> = u.y[cnt_keep..].to_vec();
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

/// CNT7-PARK (B-CRUMBS): release DONE-counter lane 7 (constant |0> on every passing shot) with the parked lanes while
/// the shell runs. Dev override `WL_CNT7_PARK=0|1`.
pub const CNT7_PARK: bool = true;
fn cnt7_park() -> bool {
    match std::env::var("WL_CNT7_PARK") { Ok(v) => v.trim() == "1", Err(_) => CNT7_PARK }
}

/// s825: the shell's products and square run on modp_ft (frogtail/Lilypad arithmetic) through ft_adapter.
pub const FT_SHELL: bool = true;
/// s825: the square runs on the Leapfrog family's closed flat square block (x -= lambda^2, then the negation).
pub const NATIVE_SQ: bool = true;

/// sz1 shell levers (compile-time switches; all exact, cap unchanged):
/// HL-001 the lambda product streams dy as its digit supplier (each digit X-measured into m1 as consumed, the lane
///        joining the carry pool); HL-002 the same for the ndy product (lambda's digits into m2);
/// HL-003 the dy recompute and division 2's lambda recompute run as one paired fix-product session (the compute's
///        measured carry erases become debts repaid by the uncompute);
/// HL-004 division 2's ctrl_neg; z_if; ctrl_neg becomes one ctrl_neg_phase oracle;
/// HL-005 -x - 3 ox after the square as one classical-operand subtraction of K' = 3 ox + c - 1 (formed classically);
/// HL-006 the four offset adds (dx, dy, x3, y3) take the classical operand directly.
pub const SZ1_HL001: bool = true;
pub const SZ1_HL002: bool = true;
pub const SZ1_HL003: bool = true;
pub const SZ1_HL004: bool = true;
pub const SZ1_HL005: bool = true;
pub const SZ1_HL006: bool = true;
/// HL-004b: y carries q = -ndy = lambda dx' (the ndy product's negation dropped), so division 2's recompute is
/// lambda = q inv' with no negation and y3 = -q - oy is one classical-operand subtraction of oy + c - 1.
pub const SZ1_HL004B: bool = true;

/// phaseprod (B-PHASEPROD): the two measurement-phase repairs as Kind::PhaseProduct (no caller z register).
/// 0 = SZ-1 FixRecompute session, 1 = OPT-014166 direct phase (identical arithmetic), 2 = direct phase + mux peel of
/// the a_0 fix. PP_D1 = division 1's dy repair, PP_D2 = division 2's lambda repair (needs HL-003 and HL-004b).
pub const PP_D1: u8 = 2;
pub const PP_D2: u8 = 2;

/// The PP mode of a site: the const, or (measurement only) `PP_MODE` = "<d1>,<d2>".
fn pp_mode(site: usize) -> u8 {
    match std::env::var("PP_MODE") {
        Ok(v) => v.split(',').nth(site - 1).and_then(|t| t.trim().parse().ok()).expect("PP_MODE=<d1>,<d2>"),
        Err(_) => if site == 1 { PP_D1 } else { PP_D2 },
    }
}

/// The lever switch: the compile-time constant, or (measurement only) `SZ1_LEVERS` = "none" or a comma list of
/// lever numbers ("1,3,6") that are on.
fn lever(n: u32) -> bool {
    let dflt = match n {
        1 => SZ1_HL001,
        2 => SZ1_HL002,
        3 => SZ1_HL003,
        4 => SZ1_HL004,
        5 => SZ1_HL005,
        6 => SZ1_HL006,
        7 => SZ1_HL004B,
        _ => unreachable!(),
    };
    match std::env::var("SZ1_LEVERS") {
        Ok(v) => v.split(',').filter_map(|t| t.trim().parse::<u32>().ok()).any(|k| k == n),
        Err(_) => dflt,
    }
}

/// z = a y mod p into a zero z (optionally negated), as direct_product_crep.
fn product_into(b: &mut B, z: &[QubitId], a: &[QubitId], y: &[QubitId], negate: bool) {
    if FT_SHELL {
        ft_call_capped(b, Kind::Product, z, a, y, *super::PEAK);
        if negate {
            let ms = Ms::alloc(b);
            ctrl_neg(b, &ms, z, None, y);
            ms.release(b);
        }
    } else {
        let ms = Ms::alloc(b);
        direct_product_crep(b, &ms, z, a, y, negate);
        ms.release(b);
    }
}

/// Reverse of product_into.
fn unproduct_from(b: &mut B, z: &[QubitId], a: &[QubitId], y: &[QubitId], negate: bool) {
    if FT_SHELL {
        if negate {
            let ms = Ms::alloc(b);
            ctrl_neg(b, &ms, z, None, y);
            ms.release(b);
        }
        ft_call_capped(b, Kind::ProductInv, z, a, y, *super::PEAK);
    } else {
        let ms = Ms::alloc(b);
        chunked_unproduct(b, &ms, z, a, y, negate);
        ms.release(b);
    }
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
    if lever(6) {
        ft_call_capped_ext(b, Kind::AddClassical { sub: true }, &x, &[], &[], *super::PEAK, &ox);
        ft_call_capped_ext(b, Kind::AddClassical { sub: true }, &y, &[], &[], *super::PEAK, &oy);
    } else {
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
        if lever(1) {
            // dy supplies the digits (product is commutative) and is X-measured into m1 as it is consumed
            ft_call_capped_ext(b, Kind::ProductStream, &z, &y, &inv, *super::PEAK, &m1);
            ck(b, "shell lambda product");
        } else {
            product_into(b, &z, &inv, &y, false);
            ck(b, "shell lambda product");
            for i in 0..256 {
                b.hmr_to(y[i], m1[i]);
            }
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
    if pp_mode(1) > 0 {
        ft_call_capped_ext(b, Kind::PhaseProduct { peel: pp_mode(1) == 2 }, &[], &y, &x, *super::PEAK, &m1);
    } else if lever(3) {
        let z = b.alloc_n(256);
        ft_call_capped_ext(b, Kind::FixRecompute { neg: 0, paired: true }, &z, &y, &x, *super::PEAK, &m1);
        b.free_n(&z);
    } else {
        let z = b.alloc_n(256);
        product_into(b, &z, &y, &x, false);
        for i in 0..256 {
            b.z_if(z[i], m1[i]);
        }
        unproduct_from(b, &z, &y, &x, false);
        b.free_n(&z);
    }
    ck(b, "shell division 1 done");

    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    {
        if NATIVE_SQ {
            // x = dx - lambda^2, then negate: lambda^2 - dx
            native_sub_square(b, &x, &y, *super::PEAK);
            if !lever(5) {
                let ms = Ms::alloc(b);
                ctrl_neg(b, &ms, &x, None, &y);
                ms.release(b);
            }
        } else {
        let tmp = b.alloc();
        let ms = Ms::alloc(b);
        ctrl_neg(b, &ms, &x, None, &y);
        if FT_SHELL {
            ms.release(b);
            b.free(tmp);
            ft_call_capped(b, Kind::SquareAcc, &x, &[], &y, *super::PEAK);
        } else {
            let mut xx = x.clone();
            sdw_square_acc(b, &ms, &mut xx, &y, tmp);
            assert_eq!(xx, x);
            b.free(tmp);
            ms.release(b);
        }
        }
        if NATIVE_SQ && lever(5) {
            // x = dx - lambda^2 here: x <- -x - 3 ox = ~x - K', K' = (3 ox + c - 1) mod p formed classically
            ft_call_capped_ext(b, Kind::NegSubClassical { mul: 3 }, &x, &[], &[], *super::PEAK, &ox);
        } else {
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
    }
    // ---------------- ndy = -lambda * dx', measure lambda away
    let m2 = b.fresh_bits(256);
    {
        let z = b.alloc_n(256);
        if lever(2) {
            // lambda supplies the digits and is X-measured into m2 as it is consumed; then the negation
            ft_call_capped_ext(b, Kind::ProductStream, &z, &y, &x, *super::PEAK, &m2);
            if !lever(7) {
                let ms = Ms::alloc(b);
                ctrl_neg(b, &ms, &z, None, &y);
                ms.release(b);
            }
        } else {
            product_into(b, &z, &y, &x, !lever(7));
            for i in 0..256 {
                b.hmr_to(y[i], m2[i]);
            }
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
    if pp_mode(2) > 0 {
        // lambda = inv' q (HL-004b: no negation), its phase by the direct phase product
        assert!(lever(7), "PP_D2 needs HL-004b (neg 0)");
        ft_call_capped_ext(b, Kind::PhaseProduct { peel: pp_mode(2) == 2 }, &[], &inv, &y, *super::PEAK, &m2);
    } else if lever(3) || (lever(4) && !lever(7)) {
        // lambda = -(inv' ndy): the phase of m2 . lambda as ctrl_neg pair (neg 1) or one ctrl_neg_phase (neg 2);
        // with HL-004b y holds q = -ndy and lambda = inv' q (neg 0)
        let z = b.alloc_n(256);
        let neg = if lever(7) { 0 } else if lever(4) { 2 } else { 1 };
        let kind = Kind::FixRecompute { neg, paired: lever(3) };
        ft_call_capped_ext(b, kind, &z, &inv, &y, *super::PEAK, &m2);
        b.free_n(&z);
    } else {
        let z = b.alloc_n(256);
        product_into(b, &z, &inv, &y, !lever(7));
        for i in 0..256 {
            b.z_if(z[i], m2[i]);
        }
        unproduct_from(b, &z, &inv, &y, !lever(7));
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
    ck(b, "shell division 2 done");

    // ---------------- x3 = dx' + ox, y3 = ndy - oy
    if lever(7) {
        // y holds q = -ndy: y3 = -q - oy
        ft_call_capped_ext(b, Kind::NegSubClassical { mul: 1 }, &y, &[], &[], *super::PEAK, &oy);
        if lever(6) {
            ft_call_capped_ext(b, Kind::AddClassical { sub: false }, &x, &[], &[], *super::PEAK, &ox);
        } else {
            let t = b.alloc_n(256);
            let ms = Ms::alloc(b);
            load_bits(b, &t, &ox);
            modadd(b, &ms, &x, &t);
            load_bits(b, &t, &ox);
            b.free_n(&t);
            ms.release(b);
        }
    } else if lever(6) {
        ft_call_capped_ext(b, Kind::AddClassical { sub: false }, &x, &[], &[], *super::PEAK, &ox);
        ft_call_capped_ext(b, Kind::AddClassical { sub: true }, &y, &[], &[], *super::PEAK, &oy);
    } else {
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
        let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0])
            .filter(|&v| v != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1; // ROLL receipts
        let mut sim = Simulator::new(b.width() as usize, nbits.max(80_000), &mut xof);
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
        let nbits = b.ops.iter().flat_map(|o| [o.c_target.0, o.c_condition.0])
            .filter(|&v| v != crate::circuit::NO_BIT.0).max().unwrap_or(0) as usize + 1; // ROLL receipts
        let mut sim = Simulator::new(b.width() as usize, nbits.max(80_000), &mut xof);
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
