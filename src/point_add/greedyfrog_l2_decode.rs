//! L2 in-place rho/a1 decode, adapted from row 50c3bf41.
//!
//! The forward sweep is gated off on STALL_PAIR fake slots. Its J register is
//! mapped once to t, then reused for rho and two measured residual bits. A real
//! add-back's residual is repaired two inverse slots later, across its fake
//! predecessor. The compile-time lever has an optional development override;
//! WL_L2_INPLACE_RHO=0 preserves the parent operation stream.

use super::*;
use std::cell::RefCell;
use std::collections::BTreeMap;

pub(super) const L2_INPLACE_RHO: bool = true;
/// Forward scan for the new decoder only. Off reproduces its first unary probe.
const L2_RHO_HSWEEP: bool = true;

pub(super) fn enabled() -> bool {
    static E: std::sync::LazyLock<bool> =
        std::sync::LazyLock::new(|| lever("L2_INPLACE_RHO", L2_INPLACE_RHO));
    *E
}

fn hscan_enabled() -> bool {
    static E: std::sync::LazyLock<bool> =
        std::sync::LazyLock::new(|| lever("L2_RHO_HSWEEP", L2_RHO_HSWEEP));
    *E
}

/// Test-only negative controls, one for each independent rewrite obligation.
/// 1 c measurement repair; 2 transported residual repair; 3 fake sweep gate;
/// 4 disabled t zeroing; 5 SW-CARRY reconstruction; 6 found-flag clear;
/// 7 residual due slot; 8 a1 disabled correction; 9 finished-shot exclusion;
/// 10 H-SWEEP anchor measurement repair.
fn broken(k: u32) -> bool {
    cfg!(test) && std::env::var("L2_DECODE_BREAK").map_or(false, |v| v.trim() == k.to_string())
}

#[derive(Clone, Copy)]
struct Receipt {
    m: [BitId; 2],
    /// A live measuring slot can already be finished while its consumer was
    /// the finishing step/add-back. The consumer must exclude LA_post = 0.
    finish_gate: bool,
}

thread_local! {
    static PENDING: RefCell<BTreeMap<usize, Receipt>> = RefCell::new(BTreeMap::new());
}

/// Call at an inverse traversal's entry; assert_empty at its successful exit.
pub(super) fn reset() {
    PENDING.with(|p| p.borrow_mut().clear());
}

pub(super) fn assert_empty() {
    PENDING.with(|p| assert!(p.borrow().is_empty(), "L2 rho residual receipt left unrepaired"));
}

/// The initial port uses only plain, nonparked row windows. Its two preceding
/// windows are plain too, so every phase consumer has the ordinary LA = u view.
/// The governor and two neighboring slots on either side remain on the parent.
pub(super) fn eligible(u: &GreedyFrog, b: &B, w: &Win, sy_len: usize, park: bool, masked_rows: bool) -> bool {
    eligible_at_room(w, sy_len, park, masked_rows, u.room(b))
}

/// Permit the composition dispatcher to reserve this exact path before the rows' temporary pool is allocated.
pub(super) fn eligible_at_room(w: &Win, sy_len: usize, park: bool, masked_rows: bool, room: usize) -> bool {
    if !enabled() || !stall_pair() || !sy_fold_cin() || !norm_stage0() || !sy_act_gate()
        || sy_len != 1 || park || masked_rows
        || w.mx < NB + 1 || w.slot < 42 || w.slot + 2 >= NSLOTS || room < 8
    {
        return false;
    }
    if let Some(g) = gov_cfg() {
        if w.slot + 2 >= g.slot && w.slot < g.end() + 2 {
            return false;
        }
    }
    true
}

/// Repair a receipt due at this slot while jl holds t = sX - sY - J.
/// `normalized` means fake/already-finished t was explicitly zeroed. The parent
/// path passes false and gets an explicit !ns phase literal instead.
/// Both paths still need the finishing-step exclusion for live receipts.
pub(super) fn pending_apply(u: &GreedyFrog, b: &mut B, w: &Win, jl: &[QubitId], sx: &[QubitId],
                            ns: Option<QubitId>, normalized: bool) {
    let Some(receipt) = PENDING.with(|p| p.borrow_mut().remove(&w.slot)) else { return };
    if broken(2) { return; }
    assert!(w.mx >= NB + 1, "L2 residual consumer needs the plain LA view");
    let xt = u.x[W - 1];
    let finish = if receipt.finish_gate && !broken(9) {
        // LA holds u = LA_post + sX. Equality u == sX is exactly LA_post == 0.
        for (i, &q) in sx.iter().enumerate() { b.cx(q, u.la[i]); }
        let q = b.alloc();
        let mut lits = vec![(xt, true)];
        lits.extend(u.la.iter().map(|&q| (q, true)));
        and_auto(b, u, &lits, q);
        Some((q, lits))
    } else { None };
    for (i, &m) in receipt.m.iter().enumerate() {
        let q = jl[i + RHO_BITS];
        b.push_condition(m);
        let mut a = vec![(q, false), (xt, true)];
        if !normalized { a.extend(ns.map(|n| (n, true))); }
        phase_and(b, &a);
        if let Some((f, _)) = &finish {
            let mut a = vec![(q, false), (*f, false)];
            if !normalized { a.extend(ns.map(|n| (n, true))); }
            phase_and(b, &a);
        }
        b.pop_condition();
    }
    if let Some((f, lits)) = finish {
        erase_and(b, u, f, &lits);
        b.free(f);
        for (i, &q) in sx.iter().enumerate() { b.cx(q, u.la[i]); }
    }
}

/// Exact five-bit in-place map from row 50c3bf41. Inputs t = 0..31 give
/// (rho(t), res(t), e=[t<8]); res = 0 on steps, and m-1 on the m-th add-back.
/// The measured carry's repair is part of the map, not an optional cost probe.
fn decode(b: &mut B, j: &[QubitId], e: QubitId) {
    assert_eq!(j.len(), R_BITS);
    let (l0, l1, l2, h0, h1) = (j[0], j[1], j[2], j[3], j[4]);
    let k = b.alloc();
    b.and_c(l0, h0, k);
    b.cx(h0, l0);
    b.cx(h1, l1);
    b.cx(h1, k);
    b.ccx(k, l1, h1);
    let c = b.alloc();
    b.and_c(h1, l2, c);
    b.cx(h1, l2);
    b.ccx(k, l1, h1);
    b.cx(h1, k);
    b.cx(k, l1);
    b.cx(h0, l0);
    b.and_u(l0, h0, k);
    b.cx(h0, l0);
    b.free(k);
    // End-around carry. When c=1 the low sum is at most two.
    b.ccx(c, l0, l1);
    b.cx(c, l0);
    b.x(h0);
    b.x(h1);
    b.and_c(h0, h1, e);
    b.x(h0);
    b.x(h1);
    b.cx(e, h0);
    b.x(c);
    b.x(h0);
    b.ccx(c, h0, h1);
    b.x(h0);
    b.cx(c, h0);
    b.x(c);
    let m = b.fresh_bits(1)[0];
    b.hmr_to(c, m);
    b.free(c);
    if !broken(1) {
        b.push_condition(m);
        b.cx(h1, h0);
        let tau = b.alloc();
        b.x(l2);
        b.and_c(l2, h0, tau);
        b.x(h1);
        b.x(l1);
        b.ccz(tau, h1, l1);
        b.x(l1);
        b.x(h1);
        b.cx(l1, l0);
        b.ccz(tau, h1, l0);
        b.cx(l1, l0);
        b.and_u(l2, h0, tau);
        b.x(l2);
        b.free(tau);
        b.cx(h1, h0);
        b.cz(h0, h1);
        b.pop_condition();
    }
}

/// H-SWEEP leaves h = en & [kt >= 1] & [J == 0]. Since kt=0 implies
/// J=0, h = en & [J == 0] XOR en & [kt == 0]. Measure h and repair
/// those two predicates before RUN_GUARD restores kt. Each six-literal
/// phase costs four T: eight emitted and four expected T in total.
fn clear_h(b: &mut B, h: QubitId, en: QubitId, kt: &[QubitId], j: &[QubitId]) {
    erase_mbu(b, h, |b| {
        if broken(10) { return; }
        let mut a = vec![(en, false)];
        a.extend(j.iter().map(|&q| (q, true)));
        phase_and(b, &a);
        let mut a = vec![(en, false)];
        a.extend(kt.iter().map(|&q| (q, true)));
        phase_and(b, &a);
    });
}

/// Replace the whole sweep section at an eligible site. The caller must remove
/// the returned rho lanes from its `lend` list before the undo division rows.
/// RowTmp keeps only the measured residual lanes; rho is freed by unrenorm_top.
#[allow(clippy::too_many_arguments)]
pub(super) fn sweep_section(u: &mut GreedyFrog, b: &mut B, bits: &SlotBits, w: &Win, act: Option<QubitId>,
                            rt: &mut RowTmp, sx: &[QubitId], sy: &[QubitId], produce: bool,
                            ns: Option<QubitId>) -> (Vec<QubitId>, QubitId, Option<QubitId>, bool) {
    assert!(rt.m.is_none() && rt.jl.len() == R_BITS && sy.len() >= 1);
    prof(b, "i.sweep");
    p3(b, u, "i.sweep");
    let en = b.alloc();
    let ns_gate = if broken(3) { None } else { ns };
    let en_lits: Vec<(QubitId, bool)> = act.into_iter().map(|a| (a, false))
        .chain(ns_gate.into_iter().map(|n| (n, true))).collect();
    if en_lits.is_empty() { b.x(en); } else { and_auto(b, u, &en_lits, en); }
    let kt5 = u.lb[..R_BITS].to_vec();
    let guard = if run_guard() {
        let c = b.alloc();
        lt_cin_sm(b, u, sx, &kt5, sy[0], Some(c));
        for &q in &kt5 { b.x(q); }
        inc_auto(b, u, c, &kt5);
        for &q in &kt5 { b.x(q); }
        Some(c)
    } else { None };
    let hplan = (hscan_enabled() && w.k >= 2).then(|| HPlan::new(w.k, true))
        .filter(|p| u.room(b) >= p.need.max(R_BITS - 1));
    if let Some(plan) = &hplan {
        hsweep_scan(b, u, Some(en), rt, plan, false);
        if !broken(6) { clear_h(b, rt.f, en, &kt5, &rt.jl); }
    } else {
        // The unary scan without OR lanes leaves f=[J!=0], unlike H-SWEEP's h.
        let chain = b.alloc_n(R_BITS);
        sweep_fwd_ui(b, u, Some(en), w, rt, &chain, &[]);
        b.free_n(&chain);
        if !broken(6) {
            b.x(rt.f);
            let lits: Vec<_> = rt.jl.iter().map(|&q| (q, true)).collect();
            and_auto(b, u, &lits, rt.f);
        }
    }
    zero_probe(b, &[rt.f, rt.g, rt.y]);
    // No backward scan remains, so RUN_GUARD can be restored now.
    if let Some(c) = guard {
        if !guard_break(1) { inc_auto(b, u, c, &kt5); }
        erase_mbu(b, c, |b| lt_cin_sm(b, u, sx, &kt5, sy[0], None));
        b.free(c);
    }
    p3(b, u, "i.ra1");
    let jl = rt.jl.clone();
    // J -> t = sX - sY - J, using the parent's folded carry-in map once.
    for &q in &jl { b.x(q); }
    b.cx(sy[0], rt.g);
    b.x(rt.g);
    add_on_sm(b, u, &jl, sx, false, false, rt.g, true);
    b.x(rt.g);
    b.cx(sy[0], rt.g);
    if !broken(4) {
        // On disabled shots J=sY=0, hence t=sX. Clear just those shots.
        b.x(en);
        for i in 0..R_BITS { b.ccx(en, sx[i], jl[i]); }
        b.x(en);
    }
    pending_apply(u, b, w, &jl, sx, ns, true);
    let a1 = b.alloc();
    decode(b, &jl, a1);
    let mb = b.fresh_bits(2);
    b.hmr_to(jl[3], mb[0]);
    b.hmr_to(jl[4], mb[1]);
    if !broken(8) {
        b.cx(en, a1);
        b.x(a1);
    }
    let due = w.slot - if broken(7) { 1 } else { 2 };
    let receipt = Receipt { m: [mb[0], mb[1]], finish_gate: !w.act_const };
    PENDING.with(|p| assert!(p.borrow_mut().insert(due, receipt).is_none(), "duplicate L2 residual receipt"));
    let r = jl[..RHO_BITS].to_vec();
    for i in 0..RHO_BITS { b.z_if(r[i], bits.r[i]); }
    b.z_if(a1, bits.a1);
    // On a1=1, rho=t, so sX-sY-rho is exactly J. On a1=0 the
    // reconstructed value is immaterial: the carried flag is gated off.
    let cout = if produce {
        prof(b, "i.swc");
        if !broken(5) { add_on_sm(b, u, sx, &r, false, true, sy[0], true); }
        let c = b.alloc();
        let t = rt.y;
        b.x(rt.s0);
        b.and_c(sx[0], rt.s0, t);
        b.x(rt.s0);
        let mut lits = vec![(a1, false)];
        lits.extend(sx[1..R_BITS].iter().map(|&q| (q, true)));
        lits.push((t, true));
        and_auto(b, u, &lits, c);
        b.x(rt.s0);
        b.and_u(sx[0], rt.s0, t);
        b.x(rt.s0);
        if !broken(5) { add_on_sm(b, u, sx, &r, false, false, sy[0], true); }
        Some(c)
    } else { None };
    // en's controls survive the whole section unchanged.
    if en_lits.is_empty() { b.x(en); } else { erase_and(b, u, en, &en_lits); }
    b.free(en);
    rt.jl = jl[RHO_BITS..].to_vec();
    zero_probe(b, &[rt.f, rt.g, rt.y]);
    zero_probe(b, &rt.jl);
    p3(b, u, "i.sweepb");
    (r, a1, cout, false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};

    /// The scan's outgoing support permits only J=0 when en=0, and J<=kt
    /// when en=1. Exhaust it, including kt=0 and every no-hit branch.
    #[test]
    fn l2_hscan_clear_gate_level() {
        let mut b = B::new();
        let en = b.alloc();
        let kt = b.alloc_n(R_BITS);
        let j = b.alloc_n(R_BITS);
        let hq = b.alloc();
        clear_h(&mut b, hq, en, &kt, &j);
        let nbits = b.fresh_bits(1)[0].0 as usize + 1;
        let cases: Vec<_> = (0..32).flat_map(|kt| {
            std::iter::once((false, kt, 0)).chain((0..=kt).map(move |j| (true, kt, j)))
        }).collect();
        for seed in 0u64..4 {
            for (batch, input) in cases.chunks(64).enumerate() {
                let mut h = sha3::Shake256::default();
                h.update(b"L2 h-sweep anchor channel test");
                h.update(&seed.to_le_bytes());
                h.update(&(batch as u64).to_le_bytes());
                let mut reader = h.finalize_xof();
                let mut sim = Simulator::new(b.width() as usize, nbits, &mut reader);
                for (s, &(on, kval, jval)) in input.iter().enumerate() {
                    if on { sim.qubits[en.0 as usize] |= 1u64 << s; }
                    for i in 0..R_BITS {
                        if (kval >> i) & 1 != 0 { sim.qubits[kt[i].0 as usize] |= 1u64 << s; }
                        if (jval >> i) & 1 != 0 { sim.qubits[j[i].0 as usize] |= 1u64 << s; }
                    }
                    if on && kval >= 1 && jval == 0 { sim.qubits[hq.0 as usize] |= 1u64 << s; }
                }
                let before = sim.qubits.clone();
                sim.apply_iter(b.ops.iter());
                for q in 0..b.width() {
                    let expected = if q == hq.0 { 0 } else { before[q as usize] };
                    assert_eq!(sim.qubits[q as usize], expected, "H clear q{q}, batch{batch}, seed{seed}");
                }
                assert_eq!(sim.phase, 0, "H clear phase, batch{batch}, seed{seed}");
            }
        }
    }

    /// The emitted channel, including its measured-carry phase repair, against
    /// the integer rho definition on every five-bit input. No inverse of the
    /// implementation is used as an oracle.
    #[test]
    fn l2_decode_map_gate_level() {
        let mut b = B::new();
        let j = b.alloc_n(R_BITS);
        let e = b.alloc();
        decode(&mut b, &j, e);
        let nbits = b.fresh_bits(1)[0].0 as usize + 1;
        for seed in 0u64..16 {
            let mut h = sha3::Shake256::default();
            h.update(b"L2 rho map independent channel test");
            h.update(&seed.to_le_bytes());
            let mut reader = h.finalize_xof();
            let mut sim = Simulator::new(b.width() as usize, nbits, &mut reader);
            for s in 0..64 {
                for i in 0..R_BITS {
                    if ((s % 32) >> i) & 1 != 0 { sim.qubits[j[i].0 as usize] |= 1u64 << s; }
                }
            }
            sim.apply_iter(b.ops.iter());
            for s in 0..64 {
                let t = s % 32;
                let rho = if t < 8 { t } else { ((t - 1) % 7) + 1 };
                let res = if t < 8 { 0 } else { (t - 8) / 7 };
                let expected = rho | (res << RHO_BITS);
                let got = j.iter().enumerate().fold(0usize, |v, (i, q)|
                    v | (((sim.qubits[q.0 as usize] >> s) & 1) as usize) << i);
                assert_eq!(got, expected, "rho/res at t={t}, measurement seed={seed}");
                assert_eq!((sim.qubits[e.0 as usize] >> s) & 1, (t < 8) as u64,
                           "a1 at t={t}, measurement seed={seed}");
            }
            assert_eq!(sim.phase, 0, "rho map phase, measurement seed={seed}");
            for q in 0..b.width() {
                if q != e.0 && !j.iter().any(|x| x.0 == q) {
                    assert_eq!(sim.qubits[q as usize], 0, "rho map scratch q{q}, measurement seed={seed}");
                }
            }
        }
    }
}
