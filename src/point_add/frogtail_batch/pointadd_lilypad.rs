//! Lilypad-GCD point addition: the inherited narrow MBU shell with a
//! Bernstein-Yang divstep walk.  At the public endpoint S,
//! 1/x = (-1)^key C 2^-S with C=c_f and key=[f<0].
//!
//!   dx = x - ox, dy = y - oy
//!   division 1:  walk on dx' (dx made odd: dx or p - dx) -> C with 1/dx = (-1)^S C 2^-T;  lambda = (-1)^S C dy 2^-T;
//!                measure dy away;  inverse walk -> dx;  recompute dy = lambda * dx, fix its phase, uncompute
//!   x:  dx' = lambda^2 - dx - 3 ox;   y:  ndy = -lambda * dx';  measure lambda away
//!   division 2:  walk on dx' -> C';  recompute lambda = -ndy (-1)^S' C' 2^-T, fix its phase, uncompute;
//!                inverse walk -> dx'
//!   x3 = dx' + ox,  y3 = ndy - oy

use super::builder::{B, G};
use super::lilypad::{PWalk, PSched, PScr, HB, NT, SB};
use super::lilypad_g::{endpoint_adapter_g, inverse_d_len_g, inverse_tmp_len_g, sched_g, walk_forward_g, walk_inverse_g, GScr};
use super::modp_frogdrop::load_bits;
use super::modp_ft::{
    ctrl_neg, mod_double_n, modadd, modsub, product, product_inv, product_tail_neg_s, product_tail_neg_s_uncompute, product_tail_neg_stream,
    Ms,
};
use crate::circuit::{BitId, QubitId};

pub const LILYPAD_SCHED: &str = include_str!("lilypad_sched.txt");

/// classical bound on a walk's halvings up to its absorption (the tails' exponent)
pub const H0: usize = if super::LILYPAD_G && super::lilypad_g::HALF_COFACTOR_G { 531 } else { 532 };
/// lanes of C' = C 2^(H0 - halvings)
pub const RLEN_S: usize = if super::LILYPAD_G && super::lilypad_g::HALF_COFACTOR_G { 287 } else { 288 };
/// lambda is measured as lambda 2^LHAT (LHAT = H0 - 256), so division 2's recompute needs only the tail's own
/// halvings.
const LHAT: usize = H0 - 256;
const L1_PAIRED_FIX_PRODUCTS: bool = true;
const L3_OFFSET_LAMBDA_FIX: bool = true;

#[cfg(test)]
thread_local! {
    static TEST_L1: std::cell::Cell<i8> = const { std::cell::Cell::new(-1) };
    static TEST_L3: std::cell::Cell<i8> = const { std::cell::Cell::new(-1) };
}

#[cfg(test)]
pub(crate) fn test_layer_overrides(l1: Option<bool>, l3: Option<bool>) {
    TEST_L1.with(|v| v.set(l1.map_or(-1, i8::from)));
    TEST_L3.with(|v| v.set(l3.map_or(-1, i8::from)));
}

fn l1_enabled() -> bool {
    #[cfg(test)]
    {
        return TEST_L1.with(|v| match v.get() { 0 => false, 1 => true, _ => L1_PAIRED_FIX_PRODUCTS });
    }
    #[cfg(not(test))]
    {
        L1_PAIRED_FIX_PRODUCTS
    }
}

fn l3_enabled() -> bool {
    #[cfg(test)]
    {
        return TEST_L3.with(|v| match v.get() { 0 => false, 1 => true, _ => L3_OFFSET_LAMBDA_FIX });
    }
    #[cfg(not(test))]
    {
        L3_OFFSET_LAMBDA_FIX
    }
}

/// With L3, the offset makes all tail steps eligible for forward-operation
/// uncompute. The compile-time fallback retains the inherited 48-step prefix.
fn tail_k0() -> usize {
    if l3_enabled() { 0 } else { 48 }
}

/// Circuit peak (the inverse walk needs 936); the modular routines take every qubit below it as a carry pool. 949
/// gives the inverse walk's cofactor adds enough pool for a chunk plan on every tick (best score of the sweep).
pub const PEAK0: u64 = if super::LILYPAD_G {
    // Feasibility cap only: the independently allocated inverse workspace
    // remains authoritative and may exceed this requested shell width.
    if super::lilypad_g::HALF_COFACTOR_G { 901 } else { 890 }
} else {
    892
};

#[cfg(test)]
thread_local! {
    static TEST_PEAK: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn test_peak(value: Option<u64>) {
    TEST_PEAK.with(|v| v.set(value.unwrap_or(0)));
}

pub fn peak() -> u64 {
    #[cfg(test)]
    {
        let value = TEST_PEAK.with(|v| v.get());
        if value != 0 {
            return value;
        }
    }
    PEAK0
}

fn shell_peak(_slot: usize) -> u64 {
    #[cfg(test)]
    {
        let high = std::env::var("LILYPAD_SHELL_HIGH").unwrap_or_default();
        if high.split(',').any(|v| v.parse::<usize>().ok() == Some(_slot)) {
            return std::env::var("LILYPAD_SHELL_PEAK").ok().and_then(|v| v.parse().ok()).unwrap_or(886);
        }
    }
    peak()
}

fn park_endpoint_hsign() -> bool {
    #[cfg(test)]
    if std::env::var_os("LILYPAD_NO_HPARK").is_some() {
        return false;
    }
    HB == 7
}

pub fn sched() -> PSched {
    if super::LILYPAD_G { sched_g() } else { PSched::from_text(LILYPAD_SCHED) }
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
    pub(crate) w: PWalk,
    pub(crate) sch: PSched,
    /// key=[f<0]: 1/dx = (-1)^key C 2^-S.
    pub(crate) key: QubitId,
    /// c_f at the public endpoint, LSB first.
    pub(crate) inv: Vec<QubitId>,
    parked_a: Vec<QubitId>,
    parked_b: Vec<QubitId>,
    m: Vec<BitId>,
    division: usize,
    g_adapter: Option<Vec<G>>,
}

/// Clifford endpoint adapter.  With g=0, the invariant gives f=±1 and
/// c_g=±p.  This toggles those known patterns to/from zero under `key`.
fn endpoint_adapter(b: &mut B, w: &PWalk, sch: &PSched, key: QubitId) {
    let tn = sch.s + 1;
    let cw = sch.w - sch.c[tn];
    let p = super::frogdrop_sched::p();
    let np = (!p).wrapping_add(super::frogdrop_sched::N::from(1u64));
    b.x(w.bf(0));
    b.cx(key, w.bf(1));
    for s in 0..cw {
        let pos = p.bit(s);
        let neg = np.bit(s);
        if pos {
            b.x(w.bsig(s));
        }
        if pos != neg {
            b.cx(key, w.bsig(s));
        }
    }
}

/// Forward Lilypad-GCD walk on xq.  The divstep accepts even inputs directly.
fn div_forward_d(b: &mut B, xq: &[QubitId], _dirty: &[QubitId]) -> Div {
    let sch = sched();
    let mut a = xq.to_vec();
    a.extend(b.alloc_n(sch.w - xq.len()));
    let mut w = PWalk {
        a,
        bb: b.alloc_n(sch.w),
        q: vec![],
        h: b.alloc_n(HB),
        capq: 11,
        log: b.alloc_n(8),
    };
    #[cfg(test)]
    let forward_peak = std::env::var("LILYPAD_FWD_PEAK").ok().and_then(|v| v.parse().ok()).unwrap_or_else(peak);
    #[cfg(not(test))]
    let forward_peak = peak();
    let room = forward_peak.saturating_sub(b.live + 2 + NT as u64) as usize;
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!("Lilypad forward live {} room {room}", b.live + 2 + NT as u64);
    }
    let sc = PScr::alloc_fwd(b, room);
    let division = b.new_division();
    let m = super::lilypad::walk_forward(b, &w, &sch, &sc, Some(division));
    sc.release(b);
    ck(b, "walk forward end");
    let key = b.alloc();
    b.cx(w.bf(1), key);
    endpoint_adapter(b, &w, &sch, key);
    let tn = sch.s + 1;
    let inv: Vec<QubitId> = (0..RLEN_S).map(|s| w.asig(tn, s)).collect();
    let parked_a: Vec<QubitId> = w.a.iter().copied().filter(|q| !inv.contains(q)).collect();
    let parked_b = w.bb.clone();
    b.free_n(&parked_a);
    b.free_n(&parked_b);
    Div { w, sch, key, inv, parked_a, parked_b, m, division, g_adapter: None }
}

fn div_forward_g(b: &mut B, xq: &[QubitId], _dirty: &[QubitId]) -> Div {
    let sch = sched_g();
    let mut a = xq.to_vec();
    a.extend(b.alloc_n(sch.w - xq.len()));
    let mut w = PWalk {
        a,
        bb: b.alloc_n(sch.w),
        q: vec![],
        h: b.alloc_n(HB),
        capq: 11,
        log: b.alloc_n(8),
    };
    #[cfg(test)]
    let forward_peak = std::env::var("LILYPAD_FWD_PEAK").ok().and_then(|v| v.parse().ok()).unwrap_or_else(peak);
    #[cfg(not(test))]
    let forward_peak = peak();
    let room = forward_peak.saturating_sub(b.live + 2 + NT as u64) as usize;
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!("Lilypad-G forward live {} room {room}", b.live + 2 + NT as u64);
    }
    let sc = PScr::alloc_fwd(b, room);
    let division = b.new_division();
    let m = walk_forward_g(b, &w, &sch, &sc, &GScr, Some(division));
    ck(b, "walk forward end");
    let key = w.bf(1);
    let g_adapter = endpoint_adapter_g(b, &w, &sch, &sc);
    b.play(&g_adapter, false);
    // A successful capped walk ends with h in the signed six-bit range, so
    // lane 6 is exactly the sign extension of lane 5. Clear and park it while
    // the shell runs, then reconstruct it immediately before inverse replay.
    if park_endpoint_hsign() {
        b.cx(w.h[HB - 2], w.h[HB - 1]);
        b.free(w.h[HB - 1]);
    }
    sc.release(b);
    let tn = sch.s + 1;
    let inv: Vec<QubitId> = (0..RLEN_S).map(|s| w.asig(tn, s)).collect();
    let parked_a: Vec<QubitId> = w.a.iter().copied().filter(|q| !inv.contains(q)).collect();
    let parked_b: Vec<QubitId> = w.bb.iter().copied().filter(|&q| q != key).collect();
    b.free_n(&parked_a);
    b.free_n(&parked_b);
    Div {
        w,
        sch,
        key,
        inv,
        parked_a,
        parked_b,
        m,
        division,
        g_adapter: Some(g_adapter),
    }
}

/// Forward Lilypad-GCD walk on xq. The disabled route remains byte-identical
/// to the submitted Lilypad-D circuit.
pub(crate) fn div_forward(b: &mut B, xq: &[QubitId], dirty: &[QubitId]) -> Div {
    if super::LILYPAD_G { div_forward_g(b, xq, dirty) } else { div_forward_d(b, xq, dirty) }
}

/// Exact inverse of div_forward: dx back in `xq` (= w.bb[0..256)), everything else freed.
fn div_inverse_d(b: &mut B, dv: Div, xq: &[QubitId], _dirty: &[QubitId]) {
    let Div {
        mut w,
        sch,
        key,
        parked_a,
        parked_b,
        m,
        division,
        ..
    } = dv;
    for &q in parked_a.iter().chain(&parked_b) {
        b.acquire(q);
    }
    endpoint_adapter(b, &w, &sch, key);
    b.cx(w.bf(1), key);
    b.free(key);
    w.q = b.alloc_n(13);
    let live = b.live + 3 + NT as u64 + SB as u64;
    let room = peak().saturating_sub(live) as usize;
    let sc = PScr::alloc_inv(b, room);
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!("Lilypad inverse live {live} room {room}");
    }
    super::lilypad::walk_inverse(b, &w, &sch, &sc, &m, Some(division));
    ck(b, "walk inverse end");
    sc.release(b);
    b.close_division(division);
    b.free_n(&w.q);
    b.free_n(&w.a[xq.len()..]);
    b.free_n(&w.bb);
    b.free_n(&w.h);
    b.free_n(&w.log);
}

fn div_inverse_g(b: &mut B, dv: Div, xq: &[QubitId], _dirty: &[QubitId]) {
    let Div {
        mut w,
        sch,
        key: _,
        parked_a,
        parked_b,
        m,
        division,
        g_adapter,
        ..
    } = dv;
    for &q in parked_a.iter().chain(&parked_b) {
        b.acquire(q);
    }
    if park_endpoint_hsign() {
        b.acquire(w.h[HB - 1]);
        b.cx(w.h[HB - 2], w.h[HB - 1]);
    }
    b.play(&g_adapter.expect("Lilypad-G adapter"), true);
    w.q = b.alloc_n(13);
    let live = b.live + 2 + inverse_d_len_g() as u64 + inverse_tmp_len_g() as u64 + super::lilypad_g::inverse_sp_len_g() as u64;
    #[cfg(test)]
    let inverse_peak = std::env::var("LILYPAD_INV_PEAK").ok().and_then(|v| v.parse().ok()).unwrap_or_else(peak);
    #[cfg(not(test))]
    let inverse_peak = peak();
    let room = inverse_peak.saturating_sub(live) as usize;
    let sc = PScr::alloc_inv_g(b, room);
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!("Lilypad-G inverse live {live} room {room}");
        let owned = w.a.len()+w.bb.len()+w.h.len()+w.log.len()+w.q.len()+2+sc.d.len()+sc.tmp.len()+sc.sp.len()+sc.pool.len();
        eprintln!("Q872_INVERSE_BINDER external={} rings={} h={} log={} q={} e_sg=2 d={} tmp={} sp={} pool={} live={} requested={}",
            b.live-owned as u64,w.a.len()+w.bb.len(),w.h.len(),w.log.len(),w.q.len(),
            sc.d.len(),sc.tmp.len(),sc.sp.len(),sc.pool.len(),b.live,inverse_peak);
    }
    walk_inverse_g(b, &w, &sch, &sc, &GScr, &m, Some(division));
    ck(b, "walk inverse end");
    sc.release(b);
    b.close_division(division);
    b.free_n(&w.q);
    b.free_n(&w.a[xq.len()..]);
    b.free_n(&w.bb);
    b.free_n(&w.h);
    b.free_n(&w.log);
}

pub(crate) fn div_inverse(b: &mut B, dv: Div, xq: &[QubitId], dirty: &[QubitId]) {
    if super::LILYPAD_G { div_inverse_g(b, dv, xq, dirty) } else { div_inverse_d(b, dv, xq, dirty) }
}

/// Lanes of the reduce's addend register tq = hi c (|hi| < 2^30, so |hi c| < 2^63 in two's complement).
const REDUCE_TQ: usize = 64;
/// Lanes on which hi 977 is formed before its sign extension (|hi 977| < 2^40).
const REDUCE_W977: usize = 41;

/// tq (REDUCE_TQ clean lanes) <- sext(hi) c mod 2^64, c = 2^32 + 2^10 - 2^5 - 2^4 + 1: hi 977 on 41 lanes (copy, +hi<<10,
/// -hi<<5, -hi<<4: 30 + 35 + 36 ANDs), CX sign extension to 64 lanes, + hi<<32 on lanes 32..64 (31 ANDs). Exact for
/// every 31-lane two's-complement hi. Recorded by the caller; the inverse play clears tq.
pub(crate) fn reduce_tq_build(b: &mut B, hi: &[QubitId], tq: &[QubitId], pool: &[QubitId]) {
    use super::modp_ft::{add_sext, sub_sext};
    let h = hi.len();
    // hi 977 needs |hi| + 10 lanes; 41 for the production 31-lane hi
    let w = h + 10;
    assert!(tq.len() == REDUCE_TQ && h >= 2 && h <= 32 && (h != 31 || w == REDUCE_W977));
    for j in 0..w {
        b.cx(hi[j.min(h - 1)], tq[j]);
    }
    add_sext(b, hi, &tq[10..w], pool);
    sub_sext(b, hi, &tq[5..w], pool);
    sub_sext(b, hi, &tq[4..w], pool);
    for j in w..REDUCE_TQ {
        b.cx(tq[w - 1], tq[j]);
    }
    add_sext(b, hi, &tq[32..REDUCE_TQ], pool);
}

/// lo += sext(tq) mod 2^256 (sub: lo -= sext(tq) as ~(~lo + sext(tq))): one carry chain whose addend lanes 63..256 all
/// read tq's sign lane (each lane restores its source before the next), carry-prefix recycling when the pool is short.
pub(crate) fn reduce_tq_add(b: &mut B, lo: &[QubitId], tq: &[QubitId], pool: &[QubitId], sub: bool) {
    let add: Vec<Option<QubitId>> = (0..lo.len()).map(|i| Some(tq[i.min(tq.len() - 1)])).collect();
    if sub {
        for &q in lo {
            b.x(q);
        }
    }
    super::modp_ft::var_add_pool(b, lo, &add, pool);
    if sub {
        for &q in lo {
            b.x(q);
        }
    }
}

/// C' (`inv`, RLEN_S lanes) -> lo' = C' mod p on its low 256 lanes (hi kept): the tails then run 256 steps.
/// lo' = lo + hi c mod 2^256 (c = 2^32 + 977), the same integer as the former five sign-extended adds of hi into lo:
/// tq = hi c is built once (132 ANDs), added in one 256-lane chain (255 ANDs + recycled loan), and X-measured instead
/// of unbuilt; the returned receipts are repaid by `reduce_ct_undo` on the bit-identical rebuild (hi is unchanged
/// between the two: the tails read only lo).
pub(crate) fn reduce_ct_fwd(b: &mut B, inv: &[QubitId]) -> Vec<BitId> {
    let (lo, hi) = (&inv[..256], &inv[256..]);
    let tq = b.alloc_n(REDUCE_TQ);
    let ms = Ms::alloc_room(b, peak());
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!("reduce_ct live {} pool {}", b.live, ms.r.len());
    }
    b.begin();
    reduce_tq_build(b, hi, &tq, &ms.r);
    let r = b.end();
    b.play(&r, false);
    reduce_tq_add(b, lo, &tq, &ms.r, false);
    let m = b.fresh_bits(REDUCE_TQ);
    for i in 0..REDUCE_TQ {
        b.hmr_to(tq[i], m[i]);
    }
    ms.release(b);
    b.free_n(&tq);
    m
}

/// Inverse of reduce_ct_fwd: rebuild tq = hi c, repay the forward's X-measurement phase (-1)^(m . tq), lo -= sext(tq),
/// unbuild tq.
pub(crate) fn reduce_ct_undo(b: &mut B, inv: &[QubitId], m: &[BitId]) {
    assert_eq!(m.len(), REDUCE_TQ);
    let (lo, hi) = (&inv[..256], &inv[256..]);
    let tq = b.alloc_n(REDUCE_TQ);
    let ms = Ms::alloc_room(b, peak());
    b.begin();
    reduce_tq_build(b, hi, &tq, &ms.r);
    let r = b.end();
    b.play(&r, false);
    for i in 0..REDUCE_TQ {
        b.z_if(tq[i], m[i]);
    }
    reduce_tq_add(b, lo, &tq, &ms.r, true);
    b.play(&r, true);
    ms.release(b);
    b.free_n(&tq);
}

/// z = y C 2^-tt (mod p), negated iff neg.0 ^ neg.1 (when given), recorded. (product_tail_neg gives -y C 2^-tt;
/// its negation folds into the sign's.)
pub(crate) fn rec_product_tail_s(
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

/// Uncompute of rec_product_tail_s's result in z (same arguments): its negation and lane reorder undone, then
/// product_tail_neg_s_uncompute (steps below k0 by the hybrid-ladder recording's inverse).
#[allow(clippy::too_many_arguments)]
pub(crate) fn uncompute_product_tail_s(
    b: &mut B,
    ms: &Ms,
    z: &[QubitId],
    c: &[QubitId],
    y: &[QubitId],
    tt: usize,
    neg: Option<(QubitId, bool)>,
    k0: usize,
) {
    let neg = neg.map(|(q, f)| (q, !f));
    if let Some((cq, flip)) = neg {
        if flip {
            b.x(cq);
        }
        ctrl_neg(b, ms, z, Some(cq));
        if flip {
            b.x(cq);
        }
    }
    // the compute's lane reorder (vector after tt halvings: z rotated left by tt), undone
    let mut zz: Vec<QubitId> = z.to_vec();
    zz.rotate_left(tt % 256);
    let mut pos = zz.clone();
    let mut sw = vec![];
    for i in 0..256 {
        if pos[i] != z[i] {
            let j = pos.iter().position(|&q| q == z[i]).unwrap();
            sw.push((pos[i], pos[j]));
            pos.swap(i, j);
        }
    }
    for &(a, d) in sw.iter().rev() {
        b.swap(a, d);
    }
    product_tail_neg_s_uncompute(b, ms, &mut zz, c, y, tt, c.len() != 256, k0);
    assert_eq!(zz, z);
}

fn restore_lane_order(b: &mut B, logical: &[QubitId], physical: &[QubitId]) {
    let mut pos = physical.to_vec();
    for i in 0..logical.len() {
        if pos[i] != logical[i] {
            let j = pos.iter().position(|&q| q == logical[i]).expect("lost product lane");
            b.swap(pos[i], pos[j]);
            pos.swap(i, j);
        }
    }
}

/// z = a * y (mod p) recorded, so the caller can uncompute it.
pub(crate) fn rec_product(
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

#[cfg(test)]
pub(crate) fn one_division_probe(b: &mut B, x: &[QubitId], y: &[QubitId]) {
    let dv = div_forward(b, x, y);
    let sq = (dv.key, false);
    let m1 = b.fresh_bits(256);
    let red_m = reduce_ct_fwd(b, &dv.inv);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        let mut zz = z.clone();
        product_tail_neg_stream(b, &ms, &mut zz, y, &dv.inv[..256], H0, &m1);
        let mut pos = zz.clone();
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        let (kq, flip) = (sq.0, !sq.1);
        if flip { b.x(kq); }
        ctrl_neg(b, &ms, &z, Some(kq));
        if flip { b.x(kq); }
        ms.release(b);
        for i in 0..256 { b.swap(z[i], y[i]); }
        b.free_n(&z);
    }
    reduce_ct_undo(b, &dv.inv, &red_m);
    div_inverse(b, dv, x, y);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, peak());
        let r = rec_product(b, &ms, &z, y, x, false);
        b.play(&r, false);
        for i in 0..256 { b.z_if(z[i], m1[i]); }
        let mut zz = z.clone();
        product_inv(b, &ms, &mut zz, y, x);
        b.free_n(&z);
        ms.release(b);
    }
}

/// K' = (3 ox + c - 1) mod p into fresh classical bits (LSB first), for a classical ox < p: 258-bit classical ripple
/// arithmetic on the condition stack (2 ox + ox, two conditional subtractions of p, + (c - 1), one more). 0 Toffoli.
pub(crate) fn classical_3ox_plus_cm1(b: &mut B, ox: &[BitId]) -> Vec<BitId> {
    use super::builder::CSrc;
    const W: usize = 258;
    assert_eq!(ox.len(), 256);
    let pm = super::frogdrop_sched::p();
    let pb: Vec<bool> = (0..256).map(|i| pm.bit(i)).collect();
    let a = b.fresh_bits(W);
    for i in 0..256 {
        b.cbit_xor_and(a[i + 1], &[ox[i]]);
    }
    let src: Vec<CSrc> = ox.iter().map(|&o| CSrc::Bit(o)).collect();
    b.c_add(&a, &src, false, None);
    b.c_cond_sub_const(&a, &pb);
    b.c_cond_sub_const(&a, &pb);
    let cm1 = super::modp_ft::C - 1;
    let cs: Vec<CSrc> = (0..64).map(|i| if (cm1 >> i) & 1 == 1 { CSrc::One } else { CSrc::Zero }).collect();
    b.c_add(&a, &cs, false, None);
    b.c_cond_sub_const(&a, &pb);
    a[..256].to_vec()
}

pub fn point_add(b: &mut B) -> (Vec<QubitId>, Vec<QubitId>) {
    let x = b.alloc_n(256);
    let y = b.alloc_n(256);
    b.declare_qubits(0, &x);
    b.declare_qubits(1, &y);
    let ox: Vec<BitId> = b.declare_bits(2, 256);
    let oy: Vec<BitId> = b.declare_bits(3, 256);

    // Classical offsets are consumed directly; the former operand bank becomes carry room.
    {
        let ms=Ms::alloc_room(b,shell_peak(0));
        super::modp_ft::modadd_classical(b,&ms,&x,&ox,true);
        super::modp_ft::modadd_classical(b,&ms,&y,&oy,true);
        ms.release(b);
    }

    // ---------------- division 1
    ck(b, "-- division 1");
    let dv = div_forward(b, &x, &y);
    let sq = (dv.key, false);
    let m1 = b.fresh_bits(256);
    let red_m = reduce_ct_fwd(b, &dv.inv);
    {
        // lambda = -dy C' 2^-H0 (negated by the key): dy supplies the digits and is X-measured bit by bit as the
        // tail consumes it (its phase is fixed by the dy recompute), the measured lanes joining the carry pool
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, shell_peak(1));
        let mut zz = z.clone();
        product_tail_neg_stream(b, &ms, &mut zz, &y, &dv.inv[..256], H0, &m1);
        let mut pos: Vec<QubitId> = zz.clone();
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        let (kq, flip) = (sq.0, !sq.1);
        if flip {
            b.x(kq);
        }
        ctrl_neg(b, &ms, &z, Some(kq));
        if flip {
            b.x(kq);
        }
        ms.release(b);
        ck(b, "lambda = inv * dy");
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }
    reduce_ct_undo(b, &dv.inv, &red_m);
    div_inverse(b, dv, &x, &y);
    ck(b, "walk inverse 1 end");
    // dy = lambda * dx: recompute, fix the phase of the dy measurement, uncompute
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, shell_peak(2));
        if std::env::var_os("FROGTAIL_CK").is_some() {
            eprintln!("LILYPAD_SHELL_SLOT2 live={} pool={} cap={}", b.live, ms.r.len(), shell_peak(2));
        }
        if l1_enabled() {
            super::modp_ft::fix_pair_begin_save(0);
            let mut zz = z.clone();
            product(b, &ms, &mut zz, &y, &x);
            super::modp_ft::fix_pair_end_save();
            restore_lane_order(b, &z, &zz);
        } else {
            let r = rec_product(b, &ms, &z, &y, &x, false);
            b.play(&r, false);
        }
        for i in 0..256 {
            b.z_if(z[i], m1[i]);
        }
        let mut zz = z.clone();
        if l1_enabled() {
            super::modp_ft::fix_pair_begin_repay();
        }
        product_inv(b, &ms, &mut zz, &y, &x);
        if l1_enabled() {
            super::modp_ft::fix_pair_end_repay();
        }
        b.free_n(&z);
        ms.release(b);
    }

    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    ck(b, "-- x: dx' = lambda^2 - ");
    {
        // The closed native block owns every scratch lane. No modular pool
        // co-resides. It subtracts y^2, so negate afterwards to obtain y^2-x.
        // From a 940-lane cap the Karatsuba square with retained scratch (k2r) fits and is cheaper than the flat
        // half-square (P1 flat, the only one that fits at 870): 49,984 vs 57,190 expected Toffoli at 990.
        b.native_flat_square_at_cap(&x, &y, shell_peak(3));
        // -x - 3 ox = ~x - K' (mod p) with ~x = 2^256 - 1 - x = (c - 1) - x and K' = (3 ox + c - 1) mod p, formed from
        // the classical offset bits by in-circuit classical arithmetic (0 T): one classical-operand modsub replaces the
        // negation's fold and two of the three modsubs.
        let kq = classical_3ox_plus_cm1(b, &ox);
        for &q in &x {
            b.x(q);
        }
        let ms = Ms::alloc_room(b, shell_peak(4));
        super::modp_ft::modadd_classical(b, &ms, &x, &kq, true);
        ms.release(b);
    }
    // ---------------- ndy = -lambda * dx', measure lambda away
    ck(b, "-- ndy = -lambda * dx',");
    let m2 = b.fresh_bits(256);
    {
        // lambda' = lambda 2^(H0 - 256) is what gets measured (its recompute is then a tail without the H0 - 256
        // trailing halvings): double first, then ndy = -lambda' dx' 2^-(H0 - 256) as a halving tail whose digits
        // come from lambda', each bit X-measured right after its last use (the measured lanes join the carry pool)
        // O1 U11: the doubling runs before z exists (z is clean until the tail), so its Montgomery blocks get the full
        // 256-lane pool; z and the tail's pool are allocated after it.
        let mut yy = y.clone();
        {
            let ms5a = Ms::alloc_room(b, shell_peak(5));
            mod_double_n(b, &ms5a, &mut yy, LHAT);
            ms5a.release(b);
        }
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, shell_peak(5));
        let mut zz = z.clone();
        product_tail_neg_stream(b, &ms, &mut zz, &yy, &x, LHAT, &m2);
        let mut pos: Vec<QubitId> = zz.clone();
        for i in 0..256 {
            if pos[i] != z[i] {
                let j = pos.iter().position(|&q| q == z[i]).unwrap();
                b.swap(pos[i], pos[j]);
                pos.swap(i, j);
            }
        }
        ms.release(b);
        for i in 0..256 {
            b.swap(z[i], y[i]);
        }
        b.free_n(&z);
    }

    // ---------------- division 2: recompute lambda = -ndy / dx' to fix its phase
    ck(b, "-- division 2: recomput");
    let dv = div_forward(b, &x, &y);
    let (sqq, sqf) = (dv.key, false);
    let red_m = reduce_ct_fwd(b, &dv.inv);
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, shell_peak(6));
        if std::env::var_os("FROGTAIL_CK").is_some() {
            eprintln!("LILYPAD_SHELL_SLOT6 live={} pool={} cap={}", b.live, ms.r.len(), shell_peak(6));
        }
        let tt = H0 - LHAT;
        let c = &dv.inv[..256];
        let tail_k0 = tail_k0();
        if l3_enabled() {
            super::modp_ft::fix_pair_begin_save(tail_k0);
            let mut zz = z.clone();
            super::modp_ft::product_tail_neg_s_offset(b, &ms, &mut zz, c, &y, tt);
            super::modp_ft::fix_pair_end_save();
            restore_lane_order(b, &z, &zz);
        } else if l1_enabled() {
            super::modp_ft::fix_pair_begin_save(tail_k0);
            let mut zz = z.clone();
            product_tail_neg_s(b, &ms, &mut zz, c, &y, tt, false);
            super::modp_ft::fix_pair_end_save();
            restore_lane_order(b, &z, &zz);
            ctrl_neg(b, &ms, &z, Some(sqq));
        } else {
            let r = rec_product_tail_s(b, &ms, &z, c, &y, tt, Some((sqq, !sqf)));
            b.play(&r, false);
        }
        if l3_enabled() {
            // O1 U33: ctrl_neg(z, key); z_if(z, m2); ctrl_neg(z, key) as one phase-only oracle (z never changes).
            super::modp_ft::ctrl_neg_phase(b, &ms, &z, sqq, &m2);
        } else {
            for i in 0..256 {
                b.z_if(z[i], m2[i]);
            }
        }
        // uncompute: forward operations above step TAIL_K0, the hybrid-ladder recording's inverse below it
        if l1_enabled() {
            super::modp_ft::fix_pair_begin_repay();
        }
        if l3_enabled() {
            let mut zz = z.to_vec();
            zz.rotate_left(tt % 256);
            let mut pos = zz.clone();
            let mut swaps = Vec::new();
            for i in 0..256 {
                if pos[i] != z[i] {
                    let j = pos.iter().position(|&q| q == z[i]).expect("lost offset-tail lane");
                    swaps.push((pos[i], pos[j]));
                    pos.swap(i, j);
                }
            }
            for &(a, d) in swaps.iter().rev() {
                b.swap(a, d);
            }
            super::modp_ft::product_tail_neg_s_offset_uncompute(b, &ms, &mut zz, c, &y, tt);
            assert_eq!(zz, z);
        } else {
            uncompute_product_tail_s(b, &ms, &z, c, &y, tt, Some((sqq, !sqf)), tail_k0);
        }
        if l1_enabled() {
            super::modp_ft::fix_pair_end_repay();
        }
        b.free_n(&z);
        ms.release(b);
    }
    reduce_ct_undo(b, &dv.inv, &red_m);
    ck(b, "lambda fix (+ unreduce)");
    div_inverse(b, dv, &x, &y);

    // ---------------- x3 = dx' + ox, y3 = ndy - oy
    ck(b, "-- x3 = dx' + ox, y3 = ");
    {
        let ms=Ms::alloc_room(b,shell_peak(7));
        super::modp_ft::modadd_classical(b,&ms,&x,&ox,false);
        super::modp_ft::modadd_classical(b,&ms,&y,&oy,true);
        ms.release(b);
    }
    // Fiat-Shamir nonce: one X X pair (identity) on qubit NONCE; fixed op count, so a nonce scan re-hashes only
    // the tail
    b.x(QubitId(super::NONCE as u64));
    b.x(QubitId(super::NONCE as u64));
    ck(b, "end");
    (x, y)
}
