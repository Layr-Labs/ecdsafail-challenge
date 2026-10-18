//! Scheme G (arch700): the column quotient without the second pipeline stage (no rho, no q0 replay).
//!
//! The stage-1 test decides one candidate of the binary search: with s = sz - K, Zh = (Z >> s) | 1 and
//! F = floor((2^(256-s) - 1) / Zh) (bl(F) = 257 - sz, p's top bits are ones), it computes
//! over(W) = [(W >> u) > (F >> u)], u = max(0, 257 - sz - TC), using only the reciprocal remainder R (K + 1 lanes):
//! F's bits stream MSB-first out of a restoring division and are subtracted from W's window in place.
use super::builder::{B, G};
use super::frogdrop::{cmp_csub_carries, inc_mixed};
use super::mask::{ge_const, mc_xor};
use crate::circuit::QubitId;

#[cfg(test)]
thread_local! {
    pub(crate) static B6_STAGE5_GATE: std::cell::RefCell<Vec<G>> = std::cell::RefCell::new(Vec::new());
}

/// F's top bits compared with W (the window has TC + 1 lanes: W's position 257 - sz, then F's TC positions)
pub const TC: usize = 32; // maximum window: low arm retains26, high arm pays32
const HEAD25_SY_MAX: usize = 112;
const HIGH_HEAD_BITS: usize = 32;
#[path = "reciprocal_signed_exact.rs"]
mod reciprocal_signed_exact;
thread_local! {
    pub(crate) static S1_HEAD_DOMAIN: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
    pub(crate) static S1_V_DOMAIN_DIRTY: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) };
    pub(crate) static S1_V_EARLY_XOR: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
    pub(crate) static S1_RAW_Y_GAP: std::cell::RefCell<Vec<QubitId>> = const { std::cell::RefCell::new(Vec::new()) };
    pub(crate) static S1_SGW_Y_GAP: std::cell::RefCell<Vec<QubitId>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// Scratch of the stage-1 test (all |0> on entry and exit except `dirty`).
#[derive(Clone)]
pub struct S1 {
    /// reciprocal remainder, K + 1 lanes
    pub r: Vec<QubitId>,
    /// quotient bit (erased by R's parity every iteration)
    pub f: QubitId,
    /// the divisor's zero top lane
    pub zero: QubitId,
    /// sign of the window difference
    pub sgn: QubitId,
    /// three temps for the early-column gates
    pub gt: Vec<QubitId>,
    /// clean increment ancillas (may be empty: dirty increments)
    pub anc: Vec<QubitId>,
    /// clean lanes for the compare's measured top carries (may be empty; disjoint from r, zh, f, zero)
    pub andc: Vec<QubitId>,
    /// comparator chain for the sz gates (>= sz lanes)
    pub chain: Vec<QubitId>,
    pub dirty: Vec<QubitId>,
}

/// window lanes from F position index m (win[m]) up to W's top position (win[0]), then the sign lane
fn seg(win: &[QubitId], m: usize, sgn: QubitId) -> Vec<QubitId> {
    let mut v: Vec<QubitId> = (0..=m).rev().map(|i| win[i]).collect();
    v.push(sgn);
    v
}

/// Recorded forward part of the test: leaves sgn = [(W >> u) - (F >> u) - 1 < 0] and the window holding the
/// difference; R, f restored by the caller's inverse play. `zh`: Z's top K lanes (zh[K-1] = MSB); `win`: TC + 1 lanes,
/// win[0] = W's position 257 - sz, win[1 + j] = position 256 - sz - j (lanes past position 0 are never touched);
/// `sz`, `szr`: the bl(Z) register and its range over the column's shots.
pub fn stage1_fwd(b: &mut B, zh: &[QubitId], win: &[QubitId], sz: &[QubitId], szr: (usize, usize), s: &S1) -> Vec<G> {
    let k = zh.len();
    assert_eq!(s.r.len(), k + 1);
    assert_eq!(win.len(), TC + 1);
    assert!(szr.1 <= 256 && szr.0 >= k + 33, "all-ones dividend needs s = sz - K >= 33");
    b.begin();
    // W - (F >> u) - 1 = W - 2^(257 - sz) + sum of F's complement bits over the valid positions (u = max(0, 257 - sz - TC))
    b.x(win[0]);
    b.cx(win[0], s.sgn);
    let mut r = s.r.clone();
    // after the K - 1 leading ones of the dividend: R = 2^(K-1) - 1 < Zh
    for &x in &r[..k - 1] { b.x(x); }
    let mut upper: Vec<QubitId> = zh[1..].to_vec();
    upper.push(s.zero);
    for j in 0..TC {
        // R <- 2R + 1 (R < 2^K: the top lane is zero), f = [R >= Zh], R -= f Zh (Zh odd: the low bit is r0 ^ f = !f)
        let top = r.pop().unwrap();
        r.insert(0, top);
        if s.r.contains(&s.zero) {
            super::frogdrop::cmp_csub_carries_vz(b, &r[1..], &upper[..upper.len() - 1], r[0], s.f, &s.andc);
        } else {
            cmp_csub_carries(b, &r[1..], &upper, r[0], s.f, &s.andc);
        }
        b.x(r[0]);
        b.cx(s.f, r[0]);
        b.cx(r[0], s.f);
        b.x(s.f);
        // W += !f 2^(256 - sz - j): valid while that position is >= 0, i.e. sz <= 256 - j
        let bits = seg(win, 1 + j, s.sgn);
        if szr.1 + j >= 257 {
            let (g0, g1) = (s.gt[0], s.gt[1]);
            let rr = super::frogdrop_col::rec(b, |b| ge_const(b, sz, 257 - j as isize - S1_ZLO.with(|z| z.get()) as isize, g0,
                                                             &s.chain));
            b.play(&rr, false);
            b.x(g0);
            b.and_c(r[0], g0, g1);
            inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
            b.and_u(r[0], g0, g1);
            b.x(g0);
            b.play(&rr, true);
        } else {
            inc_mixed(b, r[0], &bits, &s.anc, &s.dirty);
        }
    }
    b.end()
}

/// V form of the window (recorded; `window` = false: R's evolution only). With act: W += T - G, T = 2^(257 - sz),
/// G = ((F >> u) + 1) << u, i.e. F's complement bits added at their positions >= 0. For W < G (accepted values) V < T,
/// and a candidate W' < G + T is over (W' >= G) iff bit 257 - sz of V' = W' + T - G is set: the binary search reads
/// one lane per test and runs the reciprocal division twice per column. Window lanes as in `stage1_fwd` (index 0 is
/// not touched: V < T on the stepping shots; the increments wrap within positions <= 256 - sz on any other shot).
thread_local! {
    /// lowq-size: the offset sz carries while stage1_v's early-column gates are recorded (FD_MIDG_ZOFF)
    pub(crate) static S1_ZLO: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// lowq-size FD_MIDG_SGW (ported by lowq-quot): what stage1_v's early-column gates read while they are recorded
    pub(crate) static S1_GATE: std::cell::RefCell<S1Gate> = const { std::cell::RefCell::new(S1Gate::Sz) };
    /// agent_lowq_lane LANE_NOACT: stage1_v's window adds and early gates without the act control (a non-act shot's
    /// enter and leave plays then cancel exactly: same record, nothing between them touches its lanes)
    pub(crate) static S1_NOACT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// (lowq-size SGW) The early-column gate's input (the gate is [sz >= 257 - j], i.e. [s' <= j] with s' = 257 - sz =
/// g + sy on the act shots). `U8`: u = sy + g in place (8 lanes, no wrap). `UPark` (sy[7] lent to a park, sy = 128 held
/// as low7 = 0): u = (low7 + g) mod 128 in place, and an act shot's gate is [g < u <= j] (a wrapped sum or sy = 128
/// gives u <= g), computed as act & [u <= j] & [u > g] by toggling with the borrowed lane `dk` (ttk_carry of u + ~g,
/// `d2` borrowed).
#[derive(Clone)]
pub(crate) enum S1Gate {
    Sz,
    U8 { u: Vec<QubitId> },
    UPark { u: Vec<QubitId>, g: Vec<QubitId>, dk: QubitId, d2: QubitId },
}

/// target ^= [v < k] & AND(extra): v's disjoint prefix terms, exact dirty multi-control toggles
fn lt_const_and(b: &mut B, v: &[QubitId], k: usize, extra: &[(QubitId, bool)], target: QubitId, dirty: &[QubitId]) {
    if k == 0 { return; }
    if k >= 1 << v.len() { mc_xor(b, extra, target, &[], dirty); return; }
    for i in (0..v.len()).rev() {
        if (k >> i) & 1 == 0 { continue; }
        let mut lits: Vec<(QubitId, bool)> = ((i + 1)..v.len()).rev().map(|j| (v[j], (k >> j) & 1 == 0)).collect();
        lits.push((v[i], true));
        lits.extend_from_slice(extra);
        mc_xor(b, &lits, target, &[], dirty);
    }
}

/// g0 ^= the early-column gate of iteration j in the U forms (see `S1Gate`)
fn s1_gate_u(b: &mut B, gate: &S1Gate, j: usize, act: QubitId, g0: QubitId, dirty: &[QubitId]) {
    match gate {
        S1Gate::Sz => unreachable!(),
        S1Gate::U8 { u } => lt_const_and(b, u, j + 1, &[], g0, dirty),
        S1Gate::UPark { u, g, dk, d2 } => {
            let dl: Vec<QubitId> = dirty.iter().copied().filter(|q| q != dk && q != d2).collect();
            for &x in g { b.x(x); }
            let noact = S1_NOACT.with(|c| c.get());
            lt_const_and(b, u, j + 1, &[(*dk, false)], g0, &dl);
            if noact { super::arith::ttk_carry_u(b, g, &u[..g.len()], *dk, *d2); }
            else { super::arith::ttk_carry(b, g, &u[..g.len()], act, *dk, *d2); }
            lt_const_and(b, u, j + 1, &[(*dk, false)], g0, &dl);
            if noact { super::arith::ttk_carry_u(b, g, &u[..g.len()], *dk, *d2); }
            else { super::arith::ttk_carry(b, g, &u[..g.len()], act, *dk, *d2); }
            for &x in g { b.x(x); }
        }
    }
}

fn b6_route_third(b: &mut B, sy: &[QubitId], a: &[QubitId], q126: QubitId,
                  cross_col: bool, dirty: &[QubitId]) {
    // T2B: ordered gap swaps for the capacity-safe K0 repartition.
    // The public size/chunk/Y-root envelope and inverse order are checked by
    // scratch/t2b-repartition-synth-cli.py; physical gates are separate.
    // A literal (i, true) tests g[i]=0; false tests g[i]=1.
    let sy_eq = |v: usize| -> Vec<(QubitId, bool)> {
        (0..7).map(|i| (sy[i], ((v >> i) & 1) == 0)).collect()
    };
    let mut swap_third = |v: usize, gap: &[(usize, bool)], bit: usize| {
        let mut controls = sy_eq(v);
        controls.extend(gap.iter().map(|&(i, neg)| (a[i], neg)));
        super::mid2::mc_swap(b, &controls, q126, a[bit], &[], dirty);
    };
    if cross_col {
        swap_third(121, &[], 4);
        swap_third(122, &[], 4);
        swap_third(123, &[(3, false)], 2);
        swap_third(123, &[(3, true)], 4);
        swap_third(124, &[(2, true), (3, false)], 1);
        swap_third(124, &[(2, false)], 3);
        swap_third(125, &[], 4);
        swap_third(126, &[(2, false)], 1);
        swap_third(126, &[(2, true)], 4);
        swap_third(127, &[], 2);
        swap_third(128, &[(1, true)], 2);
    } else {
        swap_third(121, &[], 4);
        swap_third(122, &[], 4);
        swap_third(123, &[(0, false), (2, false)], 1);
        swap_third(123, &[(2, true)], 3);
        swap_third(123, &[(0, true), (2, false)], 4);
        swap_third(124, &[(2, false)], 1);
        swap_third(124, &[(1, false), (2, true)], 4);
        swap_third(125, &[(0, true), (2, false)], 1);
        swap_third(125, &[(0, false)], 2);
        swap_third(125, &[(0, true), (2, true)], 4);
        swap_third(126, &[], 2);
        swap_third(127, &[(1, true)], 2);
        swap_third(127, &[(0, true), (1, false)], 2);
        swap_third(128, &[(1, true)], 2);
    }
}

fn middle_record_t(record: &[G], inverse: bool) -> Option<usize> {
    record.iter().try_fold(0usize, |n, gate| Some(n + match gate {
        G::Ccx(..) => 1,
        G::AndC(..) => usize::from(!inverse),
        G::AndU(..) => usize::from(inverse),
        G::X(..) | G::Cx(..) | G::Cz(..) | G::Swap(..) | G::XIf(..) | G::ZIf(..) => 0,
        G::RowAdd(..) | G::DeferredErase(..) => return None,
    }))
}

fn head25_y_xor(b: &mut B, gate: &S1Gate, sz: &[QubitId], out: QubitId,
                dirty: &[QubitId]) {
    let (view, gap, offset) = match gate {
        S1Gate::Sz => (sz[..7].to_vec(),
            S1_RAW_Y_GAP.with(|g| g.borrow().clone()), Some(S1_ZLO.with(|z| z.get()))),
        S1Gate::U8 { u } => (u[..7].to_vec(),
            S1_SGW_Y_GAP.with(|g| g.borrow().clone()), None),
        S1Gate::UPark { u, g, .. } => (u[..7].to_vec(), g[..5].to_vec(), None),
    };
    assert!(gap.len() == 5 && dirty.len() >= 2 && !dirty.contains(&out));
    assert!(!gap.iter().any(|q| view.contains(q)));
    let pads = [dirty[0], dirty[1]];
    let mut padded = gap.clone(); padded.extend(pads);
    assert!(!padded.iter().any(|q| view.contains(q) || *q == out));
    let add_gap = rec(b, |b| {
        super::arith::ttk_add(b, &padded, &view, None, None);
        b.cx(pads[1], view[6]);
        b.cx(pads[0], view[5]);
        b.ccx(pads[0], view[5], view[6]);
    });
    let to_y = rec(b, |b| {
        if let Some(zlo) = offset {
            b.play(&add_gap, false);
            for &q in &view { b.x(q); }
            super::frogdrop::add_const_dirty_exact(b, &view, (258-zlo) % 128, dirty);
        } else {
            b.play(&add_gap, true);
        }
    });
    b.play(&to_y, false);
    lt_const_and(b, &view, HEAD25_SY_MAX + 1, &[], out, dirty);
    lt_const_and(b, &view, 1, &[], out, dirty);
    b.play(&to_y, true);
}

pub fn stage1_v(b: &mut B, zh: &[QubitId], win: &[QubitId], sz: &[QubitId], szr: (usize, usize), s: &S1, act: QubitId,
                window: bool) -> Vec<G> {
    let k = zh.len();
    assert!(s.r.len() == k + 1 || s.r.len() == k);
    assert_eq!(win.len(), TC + 1);
    assert!(szr.1 <= 256 && szr.0 >= k + 33, "all-ones dividend needs s = sz - K >= 33");
    b.begin();
    let mut r = s.r.clone();
    // The existing virtual-head and in-place-owner contract admits the
    // exact private signed H representation at either paid head width.
    // Keep every current gate/bank/selector; only the reciprocal state
    // representation and its quotient-complement wire change.
    let klane = s.r.len() == k;
    let inplace_flag = klane && s.r.contains(&s.f);
    let signed_h = (24..=32).contains(&k) && inplace_flag
        && s.r.contains(&zh[k - 1]) && S1_NOACT.with(|c| c.get());
    if signed_h {
        // H1=2^(k-1)-1-A, A=(D-1)/2; the first quotient bit is one.
        // The high two H lanes stay zero, and no flag is allocated.
        for i in 0..k - 2 { b.x(r[i]); b.cx(zh[i + 1], r[i]); }
    } else {
        for &x in &r[..k - 1] { b.x(x); }
    }
    let mut upper: Vec<QubitId> = zh[1..].to_vec();
    upper.push(s.zero);
    let clean_gate = inplace_flag && s.andc.first() == s.gt.first();
    let rounds=if k==HIGH_HEAD_BITS {32} else {26};
    for j in 0..rounds {
        if signed_h {
            if j > 0 {
                let top = r.pop().unwrap();
                r.insert(0, top);
                reciprocal_signed_exact::signed_step_vh1(b, &r, &zh[1..k - 1]);
            }
        } else if klane {
            // (agent_lowq_quot: R holding the head's top lane = the virtual leading one, jackylee0424's 693)
            if inplace_flag {
                if s.andc.len() >= 2 && std::env::var("B2_T1_CMP").as_deref() != Ok("0") {
                    super::quot_klane::cmp_csub_clean_vh1_inplace(b, &r, &zh[1..k - 1], &s.andc, &s.dirty);
                } else {
                    super::quot_klane::cmp_csub_ttk_vh1_inplace(b, &r, &zh[1..k - 1], &s.dirty[..2]);
                }
            } else if s.r.contains(&zh[k - 1]) {
                super::quot_klane::cmp_csub_ttk_vh1(b, &r, &zh[1..k - 1], s.f, &s.dirty[..2]);
            } else {
                super::quot_klane::cmp_csub_ttk_vz(b, &r, &zh[1..], s.f, s.dirty[0]);
            }
            let top = r.pop().unwrap();
            r.insert(0, top);
        } else {
            let top = r.pop().unwrap();
            r.insert(0, top);
            if s.r.contains(&s.zero) {
                super::frogdrop::cmp_csub_carries_vz(b, &r[1..], &upper[..upper.len() - 1], r[0], s.f, &s.andc);
            } else {
                cmp_csub_carries(b, &r[1..], &upper, r[0], s.f, &s.andc);
            }
        }
        if !signed_h {
            b.x(r[0]);
            if !inplace_flag {
                b.cx(s.f, r[0]);
                b.cx(r[0], s.f);
                b.x(s.f);
            }
        }
        // H's logical sign is exactly the original !quotient bit on
        // the legal reciprocal interval. First H1 has sign zero.
        let quotient_complement = if signed_h { r[k - 1] } else { r[0] };
        if !window { continue; }
        // V += act !f 2^(256 - sz - j) where that position is >= 0 (sz <= 256 - j)
        let bits: Vec<QubitId> = (1..=1 + j).rev().map(|i| win[i]).collect();
        let g0 = if inplace_flag && !clean_gate { s.dirty[0] } else { s.gt[0] };
        // Only the original S1 Q bank is globally clean here. A live
        // early predicate is excluded even if a call omits it from ctl.
        // The commutator uses its separate dirty d, leaving gt[0] idle.
        let live_early = if let Some(d) = S1_V_DOMAIN_DIRTY.with(|v| v.get()) {
            Some(d)
        } else if S1_HEAD_DOMAIN.with(|v| v.get()).is_some() || szr.1 + j >= 257 {
            Some(g0)
        } else { None };
        let window_inc = |b: &mut B, bits: &[QubitId], ctl: &[(QubitId, bool)], dirty: &[QubitId]| {
            let controls: Vec<QubitId> = ctl.iter().map(|&(q, _)| q).collect();
            let unique: std::collections::BTreeSet<_> = controls.iter().copied().collect();
            let mut bank_seen = std::collections::BTreeSet::new();
            let bank: Vec<QubitId> = s.andc.iter().copied().filter(|q| {
                !controls.contains(q) && !bits.contains(q) && !s.r.contains(q)
                    && !s.dirty.contains(q) && !dirty.contains(q)
                    && !sz.contains(q) && !zh.contains(q) && live_early != Some(*q)
                    && bank_seen.insert(*q)
            }).collect();
            // No additional clean-state assumption, retained flag or wire.
            // Preserve the old primitive exactly when the original bank
            // cannot hold every returning conjunction cell.
            if bits.is_empty() || ctl.is_empty() || unique.len() != controls.len()
                || bank.is_empty() || bank.len() < ctl.len().saturating_sub(1) {
                inc_with_controls(b, bits, ctl, dirty);
                return;
            }
            let reference = rec(b, |b| inc_with_controls(b, bits, ctl, dirty));
            let direct = rec(b, |b| {
                for &(q, neg) in ctl { if neg { b.x(q); } }
                if controls.len() == 1 {
                    inc_mixed(b, controls[0], bits, &bank, dirty);
                } else {
                    let flags = &bank[..controls.len()-1];
                    b.and_c(controls[0], controls[1], flags[0]);
                    for i in 2..controls.len() { b.and_c(flags[i-2], controls[i], flags[i-1]); }
                    inc_mixed(b, flags[flags.len()-1], bits, &bank[flags.len()..], dirty);
                    for i in (2..controls.len()).rev() { b.and_u(flags[i-2], controls[i], flags[i-1]); }
                    b.and_u(controls[0], controls[1], flags[0]);
                }
                for &(q, neg) in ctl.iter().rev() { if neg { b.x(q); } }
            });
            // The objective is Toffoli count. Exact physical metadata and
            // the complete24GiB account are checked on ROOT's new stream.
            // Require nonincrease in both literal directions and a strict
            // T saving in at least one; no N guard hides a T improvement.
            let mut improve = false;
            let take = [false, true].into_iter().all(|inverse| {
                match (middle_record_t(&reference, inverse), middle_record_t(&direct, inverse)) {
                    (Some(rt), Some(dt)) => { improve |= dt < rt; dt <= rt }
                    _ => false,
                }
            });
            b.play(if take && improve { &direct } else { &reference }, false);
        };
        if let Some(d) = S1_V_DOMAIN_DIRTY.with(|v| v.get()) {
            let high = S1_HEAD_DOMAIN.with(|v| v.get()).expect("domain-controlled V needs split head");
            assert!(signed_h && inplace_flag && s.gt.len() == 1 && S1_NOACT.with(|c| c.get()));
            assert!(!s.dirty.contains(&d) && !s.r.contains(&d) && !win.contains(&d));
            let subtract = rec(b, |b| {
                if high && S1_V_EARLY_XOR.with(|v| v.get()) && szr.1 + j >= 257 {
                    let sgate = S1_GATE.with(|g| g.borrow().clone());
                    let rr = rec(b, |b| {
                        if !matches!(sgate, S1Gate::Sz) {
                            return s1_gate_u(b, &sgate, j, act, d, &s.dirty);
                        }
                        let zl = S1_ZLO.with(|z| z.get());
                        let szv = if zl > 0 { &sz[..7] } else { sz };
                        super::frogdrop_col::ge_const_compact(b, szv,
                            257-j as isize-zl as isize, d, &s.chain, &s.dirty);
                    });
                    // d is an arbitrary dirty XOR target, never a clean
                    // flag. This directly selects d XOR early with one
                    // word update, then returns d before the next R cell.
                    b.play(&rr, false);
                    window_inc(b, &bits,
                        &[(d, false), (quotient_complement, false)], &s.dirty);
                    b.play(&rr, true);
                } else {
                    window_inc(b, &bits,
                        &[(d, false), (quotient_complement, false)], &s.dirty);
                }
            });
            b.play(&subtract, true);
            continue;
        }
        if let Some(high) = S1_HEAD_DOMAIN.with(|d| d.get()) {
            assert!(inplace_flag && S1_NOACT.with(|c| c.get()));
            // Original Q-bank lanes are globally returned zero owners,
            // even when this reciprocal's extra R donor is conditional.
            // The shared clean_gate contract also excludes g0 from chain.
            let domain_clean_gate = clean_gate;
            let g0 = if domain_clean_gate { s.gt[0] } else { s.dirty[0] };
            let gate_dirty = &s.dirty[2..];
            let sgate = S1_GATE.with(|g| g.borrow().clone());
            // Query raw SY in1..119, temporarily reconstructing it from
            // only the low5 gap bits. Every size/R owner is returned before
            // the next reciprocal cell, and no high compressed bit is read.
            let y_query = |b: &mut B, extra: &[(QubitId, bool)], out: QubitId| {
                let (view, gap, offset) = match &sgate {
                    S1Gate::Sz => (sz[..7].to_vec(),
                        S1_RAW_Y_GAP.with(|g| g.borrow().clone()), Some(S1_ZLO.with(|z| z.get()))),
                    S1Gate::U8 { u } => (u[..7].to_vec(),
                        S1_SGW_Y_GAP.with(|g| g.borrow().clone()), None),
                    S1Gate::UPark { u, g, .. } => (u[..7].to_vec(), g[..5].to_vec(), None),
                };
                assert_eq!(gap.len(), 5);
                assert!(!gap.iter().any(|q| view.contains(q)));
                // Exact low5-source add with two arbitrary dirty pads.
                // TTK first adds their high contributions, then the three
                // returning gates subtract pad0*32+pad1*64 mod128.
                // No pad is required to be zero or kept across the query.
                assert!(gate_dirty.len() >= 2);
                let pads = [gate_dirty[0], gate_dirty[1]];
                let mut padded = gap.clone();
                padded.extend(pads);
                assert!(!padded.iter().any(|q| view.contains(q)));
                let add_gap = rec(b, |b| {
                    super::arith::ttk_add(b, &padded, &view, None, None);
                    b.cx(pads[1], view[6]);
                    b.cx(pads[0], view[5]);
                    b.ccx(pads[0], view[5], view[6]);
                });
                let to_y = rec(b, |b| {
                    if let Some(zlo) = offset {
                        // offset SZ -> (257-zlo-offsetSZ-gap) mod128.
                        b.play(&add_gap, false);
                        for &q in &view { b.x(q); }
                        super::frogdrop::add_const_dirty_exact(b, &view, (258-zlo) % 128, gate_dirty);
                    } else {
                        // SGW U -> (U-gap) mod128; zero represents SY128.
                        b.play(&add_gap, true);
                    }
                });
                b.play(&to_y, false);
                lt_const_and(b, &view, HEAD25_SY_MAX + 1, extra, out, gate_dirty);
                lt_const_and(b, &view, 1, extra, out, gate_dirty);
                b.play(&to_y, true);
            };
            let early = |b: &mut B, out: QubitId| {
                if matches!(sgate, S1Gate::Sz) {
                    let zl = S1_ZLO.with(|z| z.get());
                    let szv = if zl > 0 { &sz[..7] } else { sz };
                    super::frogdrop_col::ge_const_compact(b, szv,
                        257-j as isize-zl as isize, out, &s.chain, gate_dirty);
                } else {
                    s1_gate_u(b, &sgate, j, act, out, gate_dirty);
                }
            };
            let rr = rec(b, |b| {
                // On every legal active V state, early_j means
                // SY+gap<=j<=25, hence1<=SY<=25<=119. Therefore early
                // implies Y: low suppress=Y; high suppress=!Y XOR early.
                // Off-active DATA need no arithmetic interpretation: each
                // private V record returns its R/helpers and is paired with
                // its own inverse around an activity-zero returning body.
                y_query(b, &[], g0);
                if high {
                    b.x(g0);
                    if szr.1 + j >= 257 { early(b, g0); }
                }
            });
            if domain_clean_gate {
                // With g0 initially zero, rr leaves exactly suppression
                // in g0. One increment with !g0 equals the old arbitrary-
                // dirty echo on every raw selector predicate, then rr^-1
                // returns g0 and every query helper before the next cell.
                b.play(&rr, false);
                window_inc(b, &bits, &[(quotient_complement, false), (g0, true)], gate_dirty);
                b.play(&rr, true);
                continue;
            }
            // Exact dirty-control word identity. rr returns both borrowed
            // selector lanes; neither is measured as a clean flag.
            let ctl = [(quotient_complement, false), (g0, false)];
            window_inc(b, &bits, &ctl, gate_dirty);
            for &bit in &bits { b.cx(g0, bit); }
            b.x(g0);
            b.play(&rr, false);
            window_inc(b, &bits, &ctl, gate_dirty);
            b.play(&rr, true);
            b.x(g0);
            for &bit in &bits { b.cx(g0, bit); }
            continue;
        }
        if szr.1 + j >= 257 {
            let sgate = S1_GATE.with(|g| g.borrow().clone());
            let gate_dirty = if inplace_flag && !clean_gate { &s.dirty[1..] } else { &s.dirty[..] };
            let rr = super::frogdrop_col::rec(b, |b| {
                if !matches!(sgate, S1Gate::Sz) { return s1_gate_u(b, &sgate, j, act, g0, gate_dirty); }
                // (offset form: sz - lo < 128, so its top lane is |0> and stays out of the literals)
                let zl = S1_ZLO.with(|z| z.get());
                let szv = if zl > 0 { &sz[..7] } else { sz };
                super::frogdrop_col::ge_const_compact(b, szv, 257 - j as isize - zl as isize, g0, &s.chain, gate_dirty)
            });
            if inplace_flag && !clean_gate && std::env::var("T2_WORD_ECHO").as_deref() != Ok("0") {
                // Dirty-control word identity: INC^d, complement^d,
                // INC^(d xor !predicate), complement^d = INC^(!predicate).
                // The threshold record toggles d by predicate and is played
                // only once per word instead of once per descending bit.
                let noact = S1_NOACT.with(|c| c.get());
                let mut ctl = if noact { vec![(quotient_complement, false)] }
                              else { vec![(act, false), (quotient_complement, false)] };
                ctl.push((g0, false));
                window_inc(b, &bits, &ctl, gate_dirty);
                for &bit in &bits { b.cx(g0, bit); }
                b.x(g0);
                b.play(&rr, false);
                window_inc(b, &bits, &ctl, gate_dirty);
                b.play(&rr, true);
                b.x(g0);
                for &bit in &bits { b.cx(g0, bit); }
            } else if inplace_flag && !clean_gate {
                // Echo a threshold held on arbitrary dirty payload without a
                // clean flag lane. Each descending bit uses the original lower
                // window prefix and returns g0 before the next bit.
                let noact = S1_NOACT.with(|c| c.get());
                for i in (0..bits.len()).rev() {
                    let mut ctl = if noact { vec![(quotient_complement, false)] } else { vec![(act, false), (quotient_complement, false)] };
                    ctl.extend(bits[..i].iter().copied().map(|q| (q, false)));
                    super::mask::mc_xor(b, &ctl, bits[i], &[], gate_dirty);
                    ctl.push((g0, false));
                    super::mask::mc_xor(b, &ctl, bits[i], &[], gate_dirty);
                    b.play(&rr, false);
                    super::mask::mc_xor(b, &ctl, bits[i], &[], gate_dirty);
                    b.play(&rr, true);
                }
            } else {
            b.play(&rr, false);
            if s.gt.len() == 1 && S1_NOACT.with(|c| c.get()) {
                window_inc(b, &bits, &[(quotient_complement, false), (g0, true)], &s.dirty);
            } else if s.gt.len() == 1 {
                window_inc(b, &bits, &[(act, false), (quotient_complement, false), (g0, true)], &s.dirty);
            } else if s.gt.len() >= 3 {
                let g1 = s.gt[1];
                let g2 = s.gt[2];
                b.x(g0);
                b.and_c(act, g0, g2);
                b.and_c(quotient_complement, g2, g1);
                inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
                b.and_u(quotient_complement, g2, g1);
                b.and_u(act, g0, g2);
                b.x(g0);
            } else {
                let g1 = s.gt[1];
                // g1 = act & r0 & !g0 (dirty three-control toggles)
                mc_xor(b, &[(act, false), (quotient_complement, false), (g0, true)], g1, &[], &s.dirty);
                inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
                mc_xor(b, &[(act, false), (quotient_complement, false), (g0, true)], g1, &[], &s.dirty);
            }
            b.play(&rr, true);
            }
        } else if s.gt.len() == 1 && S1_NOACT.with(|c| c.get()) {
            window_inc(b, &bits, &[(quotient_complement, false)], &s.dirty);
        } else if s.gt.len() == 1 {
            window_inc(b, &bits, &[(act, false), (quotient_complement, false)], &s.dirty);
        } else {
            let g1 = s.gt[1];
            b.and_c(quotient_complement, act, g1);
            inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
            b.and_u(quotient_complement, act, g1);
        }
    }
    b.end()
}

// A V-form whose quotient reserve occupies every possible clean gate lane
// uses the dirty-lane multi-control primitive directly. Visit high bits
// first so each prefix sees the original lower bits of the window.
fn inc_with_controls(b: &mut B, bits: &[QubitId], ctl: &[(QubitId, bool)], dirty: &[QubitId]) {
    if bits.is_empty() { return; }
    if std::env::var("T2_LINEAR_INC").as_deref() == Ok("0")
        || (std::env::var("T2_LINEAR_INC").as_deref() != Ok("1")
            && (bits.len() <= 3 || (bits.len() == 4 && ctl.len() == 1))) {
        for i in (0..bits.len()).rev() {
            let mut lits = ctl.to_vec();
            lits.extend(bits[..i].iter().copied().map(|q| (q, false)));
            mc_xor(b, &lits, bits[i], &[], dirty);
        }
        return;
    }
    let controls: Vec<QubitId> = ctl.iter().map(|&(q, _)| q).collect();
    assert!(dirty.len() >= controls.len() + bits.len());
    assert!(!controls.iter().any(|q| bits.contains(q) || dirty.contains(q)));
    assert!(!bits.iter().any(|q| dirty.contains(q)));
    // The full-word carry enters bits exactly when every low control is one.
    // Undo the low-word increment to return the controls and dirty passengers.
    for &(q, neg) in ctl { if neg { b.x(q); } }
    let fix = rec(b, |b| super::modp_frogdrop::inc_dirty_free(b, &controls, dirty));
    let mut word = controls.clone();
    word.extend_from_slice(bits);
    super::modp_frogdrop::inc_dirty_free(b, &word, dirty);
    b.play(&fix, true);
    for &(q, neg) in ctl.iter().rev() { if neg { b.x(q); } }
}

#[cfg(test)]
#[test]
fn t2_linear_increment_matches_prefix_flips() {
    use super::tests_frogdrop::run;
    for len in 1..=TC {
        for nctl in 1..=3 {
            let build = |linear: bool| {
                let mut b = B::new();
                let ctrl = b.alloc_n(nctl);
                let bits = b.alloc_n(len);
                let dirty = b.alloc_n(40);
                let ctl: Vec<(QubitId, bool)> = ctrl.iter().enumerate()
                    .map(|(i, &q)| (q, i % 2 == 1)).collect();
                if linear { std::env::set_var("T2_LINEAR_INC", "1"); }
                else { std::env::set_var("T2_LINEAR_INC", "0"); }
                b.begin();
                inc_with_controls(&mut b, &bits, &ctl, &dirty);
                let rec = b.end();
                b.play(&rec, false);
                let forward = b.ops.len();
                b.play(&rec, true);
                std::env::remove_var("T2_LINEAR_INC");
                (b, forward, ctrl, bits, dirty)
            };
            let old = build(false);
            let new = build(true);
            assert_eq!(old.0.width(), new.0.width());
            let mut input = vec![0u64; old.0.width() as usize];
            for (i, &q) in old.2.iter().enumerate() {
                input[q.0 as usize] = 0x6996_5aa5_0ff0_f00fu64.rotate_left((i * 11) as u32);
            }
            for (i, &q) in old.3.iter().enumerate() {
                input[q.0 as usize] = 0xf0a5_9669_cc33_5a5au64.rotate_left((i * 7) as u32);
            }
            for (i, &q) in old.4.iter().enumerate() {
                input[q.0 as usize] = 0x1357_9bdf_2468_ace0u64.rotate_left((i * 13) as u32);
            }
            let fo = run(&old.0.ops[..old.1], input.len(), &|q| *q = input.clone());
            let fnw = run(&new.0.ops[..new.1], input.len(), &|q| *q = input.clone());
            assert_eq!(fo.phase, 0, "old forward phase len={len} nctl={nctl}");
            assert_eq!(fnw.phase, 0, "new forward phase len={len} nctl={nctl}");
            assert_eq!(fo.q, fnw.q, "forward len={len} nctl={nctl}");
            for (label, b) in [("old", &old.0), ("new", &new.0)] {
                let inv = run(&b.ops, input.len(), &|q| *q = input.clone());
                assert_eq!(inv.phase, 0, "{label} inverse phase len={len} nctl={nctl}");
                assert_eq!(inv.q, input, "{label} inverse len={len} nctl={nctl}");
            }
        }
    }
}

/// t ^= AND(ctl) & over(W) (`over` = true) or AND(ctl) & !over(W) (see `stage1_fwd`); everything else restored.
pub fn stage1_test(b: &mut B, fwd: &[G], s: &S1, t: QubitId, ctl: &[(QubitId, bool)], temps: &[QubitId], over: bool) {
    b.play(fwd, false);
    let mut lits = ctl.to_vec();
    lits.push((s.sgn, over));
    mc_xor(b, &lits, t, temps, &s.dirty);
    b.play(fwd, true);
}

// ------------------------------------------------------------------------------------------------ the middle
use super::builder::G as Gate;
use super::frogdrop::rot_by_range_care;
use super::frogdrop_col::{mc_xor_dn, rec, ring_cadd2_loan, ColPar, ColScr, Fd};
use super::payload::{read_lane, ripple, PlCol, L0P, NP};
mod b8b_cross;

// Diagnostic only: emitted-op boundaries of the three V-form park windows.
// The packed replay consumes this with its actual 64-shot simulator state.
#[cfg(test)]
thread_local! {
    pub(crate) static D4B_WINDOWS: std::cell::RefCell<Vec<(usize, usize, u8, QubitId)>> = const { std::cell::RefCell::new(Vec::new()) };
}

#[cfg(test)]
fn d4b_window(start: usize, end: usize, kind: u8, act: QubitId) {
    if std::env::var_os("D4B_PARK_AUDIT").is_some() {
        D4B_WINDOWS.with(|w| w.borrow_mut().push((start, end, kind, act)));
    }
}

/// Borrow sy's high bit while parking on the model-clean domain 1..=128.
/// Low seven bits encode 128 as zero; the high bit can therefore join the
/// quotient cycle after this normalization has cleared it.
pub(crate) fn borrowed_sy_normal(b: &mut B, sy: &[QubitId], dirty: &[QubitId]) -> Vec<Gate> {
    assert_eq!(sy.len(), 8);
    rec(b, |b| {
        let zero: Vec<(QubitId, bool)> = sy[..7].iter().copied().map(|q| (q, true)).collect();
        mc_xor(b, &zero, sy[7], &[], dirty);
    })
}

/// Rotate the augmented Q cycle down by sy without reading the borrowed bit.
pub(crate) fn borrowed_sy_rotate(b: &mut B, cycle: &[QubitId], sy: &[QubitId], temp: QubitId,
                                 dirty: &[QubitId]) -> Vec<Gate> {
    assert_eq!(sy.len(), 8);
    assert!(cycle.len() >= 129 && cycle.contains(&sy[7]) && !cycle.contains(&temp));
    rec(b, |b| {
        super::frogdrop::rot_by(b, cycle, &sy[..7], true);
        let zero: Vec<(QubitId, bool)> = sy[..7].iter().copied().map(|q| (q, true)).collect();
        mc_xor(b, &zero, temp, &[], dirty);
        super::frogdrop::crot_up(b, temp, cycle, cycle.len() - 128);
        mc_xor(b, &zero, temp, &[], dirty);
    })
}

/// Place q19 into the Q-cycle position that rotates to lane 19. This clears
/// its SX owner during the HT payload park whenever the position is in range.
pub(crate) fn preposition_q19(b: &mut B, cycle: &[QubitId], sy: &[QubitId], q19: QubitId,
                             act: QubitId, range: (usize, usize), dirty: &[QubitId]) -> Vec<Gate> {
    preposition_qk(b, cycle, sy, q19, 19, act, range, dirty)
}
/// agent_lowq_quot: preposition_q19 for the first external bit kb0 = K + 1
#[allow(clippy::too_many_arguments)]
pub(crate) fn preposition_qk(b: &mut B, cycle: &[QubitId], sy: &[QubitId], q19: QubitId, kb0: usize,
                             act: QubitId, range: (usize, usize), dirty: &[QubitId]) -> Vec<Gate> {
    assert!(cycle.len() > kb0 && cycle.last() == Some(&q19));
    rec(b, |b| {
        let lane = |v: usize| {
            let idx = v + kb0;
            if idx < cycle.len() && cycle[idx] != q19 { Some(cycle[idx]) } else { None }
        };
        super::mid2::dec_swap(b, sy, range.0, range.1, &lane, q19, &[(act, false)], &[], &[], dirty);
    })
}

/// agent_lowq_quot: the K-lane reciprocal remainder (24 lanes; QUOT_KLANE=0 restores the 25-lane form)
pub const KLANE_R: bool = true;
pub fn klane_r() -> bool {
    std::env::var("QUOT_KLANE").map(|v| v != "0").unwrap_or(KLANE_R)
}

/// agent_lowq_quot: chunked q sessions, C0 = bits [0, QCH) and C1 = [QCH, kmax), at most one chunk stored per loop
/// and per park (bit kb of chunk [a, b) in slot kb - a, cycle index kb - a); QUOT_CHUNKED=0 restores one session
pub const CHUNKED: bool = true;
pub const QCH: usize = 6;
/// agent_lowq_quot: C0's length at ring K: C1 (bits [qch, 23)) must fit the K + 6 slots (headroom 0..=K, sx[1..=5])
pub fn qch() -> usize { QCH.max(super::mid2::QF.saturating_sub(super::pointadd_frogdrop::K + 6)) }
/// lowq_cross N chunks (ported by lowq-quot): the chunk cuts of a column, chunks C_i = [bd[i], bd[i + 1]) with
/// bd = [0, cuts.., kmax]. QUOT_CUTS_WIDE = "a,b,..": the cuts in the wide columns (sz envelope >= 128 lanes, no sz
/// offset; R takes a park lane there below K11); [qch()] elsewhere
pub fn chunk_cuts_wide(wide: bool) -> Vec<usize> {
    // (QUOT_CUTS_NARROW: the narrow columns' cuts)
    if let Some(v) = std::env::var(if wide { "QUOT_CUTS_WIDE" } else { "QUOT_CUTS_NARROW" }).ok() {
        return v.split(',').filter_map(|x| x.trim().parse().ok()).collect();
    }
    vec![qch()]
}
pub fn chunked() -> bool {
    std::env::var("QUOT_CHUNKED").map(|v| v != "0").unwrap_or(CHUNKED)
}

/// mid2's trans_masked (private there), for the IP5-split payload: t += s (positions k.. of the post region) on shots
/// with c, writing only positions pos <= 258 - 2^sh (sy >> sh); the mask g grows and ends as g = c, then g ^= c.
#[allow(clippy::too_many_arguments)]
fn trans_masked_q(b: &mut B, t: &[QubitId], s: &[QubitId], k: usize, c: QubitId, sy: &[QubitId], sh: usize,
                  sylo: usize, syhi: usize, g: QubitId, c0: QubitId, pre: &[QubitId], temps: &[QubitId],
                  dirty: &[QubitId]) {
    let bits = &sy[sh..];
    let (alo, ahi) = (sylo >> sh, syhi >> sh);
    let mut dec = super::mask::Dec::new(bits, pre);
    let mut next = alo;
    let mut mid = |_b: &mut B| {};
    let mut gate = |b: &mut B, i: Option<usize>| -> Option<QubitId> {
        let lim = match i { Some(i) => (258 - (k + i) as isize).div_euclid(1 << sh), None => isize::MAX };
        while next <= ahi && (next as isize) <= lim {
            let mut ct = dec.ctrls(b, next);
            ct.push((c, false));
            mc_xor(b, &ct, g, temps, dirty);
            next += 1;
        }
        match i {
            Some(_) => Some(g),
            None => {
                dec.clear(b);
                b.cx(c, g);
                None
            }
        }
    };
    ripple(b, t, s, c0, false, &mut mid, &mut gate);
}

/// B8B prototype: full Y-source prefix mask. Dirty parked Q above the true
/// length must not participate in the up pass: its next cell would overwrite
/// the carry lane that the comparator reads after the pass.
#[allow(clippy::too_many_arguments)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn b7b_masked_cmp_y(b: &mut B, t: &[QubitId], s: &[QubitId], sy: &[QubitId],
    sylo: usize, syhi: usize, ak: QubitId, c: QubitId, c0: QubitId,
    mask: QubitId, pre: &[QubitId], dirty: &[QubitId], cmpl: bool) {
    assert_eq!(t.len(), s.len());
    assert!(syhi < t.len());
    // In a full Cuccaro up pass, a higher source cell changes its previous
    // source lane. Thus s[sy] is *not* the carry at the usual mid hook when
    // quotient garbage occupies higher lanes. Undo higher cells first; when
    // the reverse sweep reaches i == sy, s[i] is the desired carry.
    if cmpl { for &x in t { b.x(x); } }
    for i in 0..t.len() {
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(x, t[i], s[i]);
    }
    // The decision c is zero until the reverse sweep reaches this shot's
    // boundary, then equals the write mask. The former separate mask lane
    // can serve as one more clean decoder prefix instead.
    let mut dec_pre = pre.to_vec();
    dec_pre.push(mask);
    let mut dec = super::mask::Dec::new(sy, &dec_pre);
    for i in (0..t.len()).rev() {
        if (sylo..=syhi).contains(&i) {
            let eq = dec.ctrls(b, i);
            let mut controls = eq.clone();
            controls.extend([(s[i], true), (ak, false)]);
            mc_xor(b, &controls, c, &[], dirty);
        }
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.ccx(x, t[i], s[i]);
        b.cx(s[i], x);
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(c, x, t[i]);
        b.cx(s[i], x);
    }
    dec.clear(b);
    if cmpl { for &x in t { b.x(x); } }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn b7b_masked_add_y(b: &mut B, t: &[QubitId], s: &[QubitId], sy: &[QubitId],
    sylo: usize, syhi: usize, ctl: QubitId, c0: QubitId, mask: QubitId,
    pre: &[QubitId], dirty: &[QubitId], sub: bool) {
    assert_eq!(t.len(), s.len());
    assert!(syhi < t.len());
    if sub { for &x in t { b.x(x); } }
    for i in 0..t.len() {
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(x, t[i], s[i]);
    }
    let mut dec = super::mask::Dec::new(sy, pre);
    for i in (0..t.len()).rev() {
        if (sylo..=syhi).contains(&i) {
            let mut eq = dec.ctrls(b, i);
            eq.push((ctl, false));
            mc_xor(b, &eq, mask, &[], dirty);
        }
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.ccx(x, t[i], s[i]);
        b.cx(s[i], x);
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(mask, x, t[i]);
        b.cx(s[i], x);
    }
    b.cx(ctl, mask);
    dec.clear(b);
    if sub { for &x in t { b.x(x); } }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn b7b_v_bit(b: &mut B, t: &[QubitId], s: &[QubitId], sy: &[QubitId],
    sylo: usize, syhi: usize, ak: QubitId, top: QubitId, c: QubitId, c0: QubitId,
    pre: &[QubitId], dirty: &[QubitId]) {
    assert_eq!(t.len(), s.len());
    assert!(pre.len() >= sy.len() - 1);
    // A top-lane quotient reads the carry at sy-1, every lower lane at sy.
    // Shift the size temporarily and use one carry read for both cases.
    let shift = rec(b, |b| super::arith::dec(b, top, sy, pre));
    b.play(&shift, false);
    let rd = s.to_vec();
    let mut mid = |b: &mut B| {
        let lane = |v: usize| rd.get(v).copied();
        read_lane(b, sy, sylo.saturating_sub(1), syhi, &lane, true,
                  &[(ak, false)], c, &pre[..2], &[], dirty);
    };
    let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| c);
    ripple(b, t, s, c0, false, &mut mid, &mut gate);
    b.play(&shift, true);
    b7b_store_v_bit(b, t, sy, sylo, syhi, ak, top, c, dirty);
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn b7b_store_v_bit(b: &mut B, t: &[QubitId], sy: &[QubitId],
    sylo: usize, syhi: usize, ak: QubitId, top: QubitId, c: QubitId,
    dirty: &[QubitId]) {
    let leaves: Vec<(usize, QubitId)> = (sylo..=syhi).map(|v| (v, t[v])).collect();
    let mut swaps = vec![];
    let root = swap_tree(sy, &leaves, sy.len(), &mut swaps);
    for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
    mc_xor(b, &[(ak, false), (top, true)], root, &[], dirty);
    super::mid2::mc_swap(b, &[(ak, false)], root, c, &[], dirty);
    for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn b7b_move_q0(b: &mut B, q: &[QubitId], x128: QubitId, sy: &[QubitId],
    sylo: usize, syhi: usize, slot: QubitId, act: QubitId, _pre: &[QubitId], dirty: &[QubitId]) {
    let lane = |v: usize| if v < q.len() { Some(q[v]) }
                           else if v == q.len() { Some(x128) } else { None };
    let leaves: Vec<(usize, QubitId)> = (sylo..=syhi).filter_map(|v| lane(v).map(|x| (v,x))).collect();
    let mut swaps = vec![];
    let root = swap_tree(sy, &leaves, sy.len(), &mut swaps);
    for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
    super::mid2::mc_swap(b, &[(act, false)], root, slot, &[], dirty);
    for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn b7b_extract_v_bit(b: &mut B, t: &[QubitId], sy: &[QubitId],
    sylo: usize, syhi: usize, ak: QubitId, top: QubitId, c: QubitId,
    dirty: &[QubitId]) {
    let leaves: Vec<(usize, QubitId)> = (sylo..=syhi).map(|v| (v, t[v])).collect();
    let mut swaps = vec![];
    let root = swap_tree(sy, &leaves, sy.len(), &mut swaps);
    for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
    super::mid2::mc_swap(b, &[(ak, false)], root, c, &[], dirty);
    mc_xor(b, &[(ak, false), (top, true)], root, &[], dirty);
    for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn b7b_erase_park_bit(b: &mut B, cycle: &[QubitId], sy: &[QubitId],
    sylo: usize, syhi: usize, kb: usize, c: QubitId) {
    let leaves: Vec<(usize, QubitId)> = (sylo..=syhi)
        .filter_map(|v| cycle.get(v + kb).copied().map(|x| (v, x))).collect();
    assert!(!leaves.is_empty());
    let mut swaps = vec![];
    let root = swap_tree(sy, &leaves, sy.len(), &mut swaps);
    for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
    b.cx(c, root);
    for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn b7b_take_park_bit(b: &mut B, cycle: &[QubitId], sy: &[QubitId],
    sylo: usize, syhi: usize, kb: usize, flight: QubitId, act: QubitId,
    dirty: &[QubitId]) {
    let leaves: Vec<(usize, QubitId)> = (sylo..=syhi)
        .filter_map(|v| cycle.get(v + kb).copied().map(|x| (v, x))).collect();
    assert!(!leaves.is_empty());
    let mut swaps = vec![];
    let root = swap_tree(sy, &leaves, sy.len(), &mut swaps);
    for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
    super::mid2::mc_swap(b, &[(act, false)], root, flight, &[], dirty);
    for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
}

/// Swap two distinct byte values with no persistent scratch. The Gray-path
/// transpositions restore every intermediate state, including dirty shots.
fn b8b_transpose_const(b: &mut B, bits: &[QubitId], a: u8, z: u8, dirty: &[QubitId]) {
    assert_eq!(bits.len(), 8);
    let mut path = vec![a];
    let mut cur = a;
    for bit in 0..8 {
        if ((a ^ z) >> bit) & 1 != 0 {
            cur ^= 1 << bit;
            path.push(cur);
        }
    }
    assert_eq!(cur, z);
    let step = |b: &mut B, u: u8, v: u8| {
        let bit = (u ^ v).trailing_zeros() as usize;
        assert_eq!((u ^ v).count_ones(), 1);
        let ctl: Vec<(QubitId, bool)> = (0..8).filter(|&i| i != bit)
            .map(|i| (bits[i], (u >> i) & 1 == 0)).collect();
        mc_xor(b, &ctl, bits[bit], &[], dirty);
    };
    for p in path.windows(2) { step(b, p[0], p[1]); }
    for i in (1..path.len() - 1).rev() { step(b, path[i - 1], path[i]); }
}

/// O3 tb-frame. The ring view is relabelled by +22, so an UP rotation by
/// tb sends natural kk=tb-j to fixed frame kk'=22-j. The record inverse
/// restores sz, ring and dirty passengers exactly.
fn b8b_tb_frame(b: &mut B, ring: &[QubitId], sz: &[QubitId], sy: &[QubitId],
                dirty: &[QubitId]) -> Vec<G> {
    assert_eq!(sz.len(), 8);
    assert_eq!(sy.len(), 8);
    assert_eq!(ring.len(), 259);
    rec(b, |b| {
        super::arith::ttk_add(b, sy, sz, None, None);
        for &q in sz { b.x(q); }
        super::modp_frogdrop::inc_dirty_free(b, &sz[1..], dirty);
        for (a, z) in [(23, 54), (24, 86), (25, 118)] {
            b8b_transpose_const(b, sz, a, z, dirty);
        }
        // `rot_by_range_care` specifies the UP source support (the DOWN
        // destinations). Natural kk is in 0..=22, with at most 129 target
        // cells, hence old ring indices 108..=258.
        let care: std::collections::BTreeSet<usize> = (108..=258).collect();
        rot_by_range_care(b, ring, &sz[..5], 0, 31, false, dirty, &care);
    })
}

/// O3 top/middle/bottom parked-play route records. Each tuple is
/// (family, sy, owner, gap target, gap mask, required-one mask), in the
/// synthesized forward order; reverse playback restores every owner.
const B8B_ROUTES: &[(u8, u8, u8, u8, u8, u8)] = &[
    (0, 123, 2, 4, 0, 0),
    (0, 125, 2, 3, 0, 0),
    (0, 126, 1, 4, 0, 0),
    (0, 126, 2, 3, 0, 0),
    (0, 127, 0, 4, 8, 0),
    (0, 127, 1, 2, 8, 0),
    (0, 127, 2, 3, 0, 0),
    (0, 128, 0, 1, 16, 0),
    (0, 128, 1, 4, 0, 0),
    (0, 128, 2, 3, 0, 0),
    (1, 121, 2, 4, 0, 0),
    (1, 123, 2, 4, 0, 0),
    (1, 124, 2, 4, 0, 0),
    (1, 125, 1, 3, 0, 0),
    (1, 125, 2, 4, 0, 0),
    (1, 126, 0, 3, 2, 0),
    (1, 126, 1, 4, 0, 0),
    (1, 126, 2, 3, 2, 2),
    (1, 126, 2, 1, 4, 4),
    (1, 127, 0, 4, 1, 1),
    (1, 127, 1, 3, 4, 0),
    (1, 127, 2, 2, 0, 0),
    (1, 128, 0, 2, 11, 1),
    (1, 128, 1, 4, 0, 0),
    (1, 128, 2, 1, 8, 0),
    (2, 117, 2, 3, 16, 16),
    (2, 118, 2, 3, 17, 17),
    (2, 119, 1, 2, 19, 19),
    (2, 119, 2, 3, 16, 16),
    (2, 120, 2, 2, 25, 17),
    (2, 121, 2, 4, 2, 2),
    (2, 122, 1, 4, 5, 5),
    (2, 122, 2, 1, 12, 12),
    (2, 123, 2, 4, 14, 10),
    (2, 124, 0, 1, 25, 9),
    (2, 124, 1, 2, 8, 8),
    (2, 124, 2, 4, 0, 0),
    (2, 125, 1, 3, 1, 1),
    (2, 125, 2, 4, 4, 4),
    (2, 126, 2, 3, 19, 1),
    (2, 127, 2, 3, 4, 0),
    (2, 128, 1, 1, 24, 0),
    (2, 128, 2, 3, 16, 0),
];

fn b8b_route_family(b: &mut B, family: u8, sy: &[QubitId], gap: &[QubitId],
                    owners: [QubitId; 3], sw: Option<QubitId>, hr_ph: Option<QubitId>, dirty: &[QubitId]) {
    assert!(family < 3 && sy.len() == 8 && gap.len() >= 5);
    for &(fam, size, owner, target, mask, ones) in B8B_ROUTES {
        if fam != family { continue; }
        // The parked SGW wrapper normalizes sy=128 to low-seven zero;
        // sy[7] is an R owner and must never be read by this route.
        let mut ctl: Vec<(QubitId, bool)> = (0..7)
            .map(|i| (sy[i], ((size >> i) & 1) == 0)).collect();
        if let Some(sw) = sw { ctl.push((sw, true)); }
        if let Some(ph) = hr_ph { ctl.push((ph, true)); }
        for i in 0..5 {
            if (mask >> i) & 1 != 0 { ctl.push((gap[i], ((ones >> i) & 1) == 0)); }
        }
        super::mid2::mc_swap(b, &ctl, owners[owner as usize], gap[target as usize], &[], dirty);
    }
}

#[allow(clippy::too_many_arguments)]
fn b8b_make_raw_parked_forms(b: &mut B, prot: &[G], sg_p: &[G], u_p: &[G],
    fvp: &[G], fr: &[G], vh1: Option<QubitId>, sy: &[QubitId], gap: &[QubitId],
    owners: [QubitId; 3], sw: Option<QubitId>, hr_old: Option<(&[G], QubitId, QubitId, QubitId)>,
    dirty: &[QubitId]) -> Vec<Vec<G>> {
    (0..3).map(|family| {
        let route = rec(b, |b| b8b_route_family(b, family, sy, gap, owners, sw,
            hr_old.map(|(_, ph, _, _)| ph), dirty));
        let old_inv = hr_old.map(|(old, _, _, _)| rec(b, |b| b.play(old, true)));
        let old_play = |b: &mut B, r: &[G]| {
            if let Some((_, ph, selector, helper)) = hr_old {
                if let Some(sw) = sw {
                    // The ordinary V form retains today's route on inactive
                    // switch shots. Select it on ph OR sw, complementing the
                    // three-band route's !ph AND !sw control.
                    b.cx(ph, selector);
                    b.cx(sw, selector);
                    b.ccx(ph, sw, selector);
                    b.play_ctrl_full(r, selector, helper);
                    b.ccx(ph, sw, selector);
                    b.cx(sw, selector);
                    b.cx(ph, selector);
                } else { b.play_ctrl_full(r, ph, selector); }
            }
        };
        rec(b, |b| {
            b.play(prot, false);
            b.play(sg_p, false);
            b.play(&route, false);
            if let Some((old, _, _, _)) = hr_old { old_play(b, old); }
            b.play(u_p, false);
            if let Some(q) = vh1 { b.x(q); }
            b.play(fvp, false);
            b.play(fr, true);
            if let Some(q) = vh1 { b.x(q); }
            b.play(u_p, true);
            if let Some(inv) = &old_inv { old_play(b, inv); }
            b.play(&route, true);
            b.play(sg_p, false);
            b.play(prot, true);
        })
    }).collect()
}

fn b8b_ripple_masked_source(b: &mut B, t: &[QubitId], s: &[QubitId], sy: &[QubitId], syhi: usize,
                            ak: QubitId, c0: QubitId, m: QubitId, temps: &[QubitId],
                            dirty: &[QubitId], mid: &mut dyn FnMut(&mut B)) {
    assert_eq!(t.len(), s.len());
    let mut mask = super::payload::Mask::new(sy, syhi, false, vec![], m, temps, dirty);
    for &q in t { b.x(q); }
    for i in 0..t.len() {
        mask.goto(b, Some(i as isize));
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.ccx(m, s[i], t[i]);
        b.ccx(m, s[i], x);
        mc_xor(b, &[(m, false), (x, false), (t[i], false)], s[i], temps, dirty);
    }
    mid(b);
    for i in (0..t.len()).rev() {
        mask.goto(b, Some(i as isize));
        let x = if i == 0 { c0 } else { s[i - 1] };
        mc_xor(b, &[(m, false), (x, false), (t[i], false)], s[i], temps, dirty);
        b.ccx(m, s[i], x);
        b.ccx(m, s[i], t[i]);
        b.ccx(m, s[i], x);
        mc_xor(b, &[(m, false), (ak, false), (x, false)], t[i], temps, dirty);
        b.ccx(m, s[i], x);
    }
    mask.goto(b, None);
    for &q in t { b.x(q); }
}

/// B8B prototype: leave the full up pass intact, but capture each carry at
/// its true Y boundary before a dirty higher source cell can overwrite it.
/// Mask only the down-pass writes. The selected carry is XORed into `cmp`.
#[allow(clippy::too_many_arguments)]
fn b8b_ripple_early_carry(b: &mut B, t: &[QubitId], s: &[QubitId], sy: &[QubitId],
                          sylo: usize, syhi: usize, ak: QubitId, c0: QubitId, cmp: QubitId,
                          m: QubitId, pre: &[QubitId], temps: &[QubitId], dirty: &[QubitId],
                          cmpl: bool, prior_gate: Option<QubitId>) {
    assert_eq!(t.len(), s.len());
    let mut dec = super::mask::Dec::new(sy, pre);
    if cmpl { for &q in t { b.x(q); } }
    for i in 0..t.len() {
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(x, t[i], s[i]);
        if (sylo..=syhi).contains(&i) {
            let mut controls = dec.ctrls(b, i);
            controls.push((s[i], true));
            controls.push((ak, false));
            mc_xor(b, &controls, cmp, temps, dirty);
            // Cell i itself may still change s[i-1]. The carry at sy-1
            // therefore becomes stable at the same boundary as s[sy].
            if let Some(pg) = prior_gate {
                if i > 0 {
                    let mut controls = dec.ctrls(b, i);
                    controls.extend([(s[i - 1], false), (ak, false), (pg, false)]);
                    mc_xor(b, &controls, cmp, temps, dirty);
                }
            }
        }
    }
    dec.clear(b);
    let down_cell = |b: &mut B, i: usize| {
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.ccx(x, t[i], s[i]);
        b.cx(s[i], x);
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        mc_xor(b, &[(m, false), (cmp, false), (x, false)], t[i], temps, dirty);
        if let Some(pg) = prior_gate {
            // At the special V-search boundary kb=g, all higher quotient
            // decisions were zero, so high Q is clean and the full ripple's
            // carry into the high target must be retained.
            mc_xor(b, &[(pg, false), (m, true), (cmp, false), (x, false)],
                   t[i], temps, dirty);
        }
        b.cx(s[i], x);
    };
    if pre.len() == 7 {
        // The same seven clean prefixes can stream the monotone threshold
        // through the down pass. Each descending equality toggles m once.
        let mut dec = super::mask::Dec::new(sy, pre);
        for i in (0..t.len()).rev() {
            let controls = dec.ctrls(b, i);
            assert_eq!(controls.len(), 1);
            b.cx(controls[0].0, m);
            down_cell(b, i);
        }
        dec.clear(b);
        // m = [sy <= syhi] after i=0; clear on every 8-bit sy value.
        b.x(m);
        super::mask::ge_const(b, sy, (syhi + 1) as isize, m, pre);
    } else {
        let mut mask = super::payload::Mask::new(sy, syhi, false, vec![], m, temps, dirty);
        for i in (0..t.len()).rev() {
            mask.goto(b, Some(i as isize));
            down_cell(b, i);
        }
        mask.goto(b, None);
    }
    if cmpl { for &q in t { b.x(q); } }
}

/// Swap tree over `reg`'s low `level` bits for sorted leaves (value, lane): after the swaps (in order), the first
/// leaf's lane holds the lane of the register's value (if it is a leaf value); returns that root lane.
fn swap_tree(reg: &[QubitId], leaves: &[(usize, QubitId)], level: usize,
             swaps: &mut Vec<(QubitId, QubitId, QubitId)>) -> QubitId {
    assert!(!leaves.is_empty());
    if level == 0 { assert_eq!(leaves.len(), 1); return leaves[0].1; }
    let bit = level - 1;
    let split = leaves.partition_point(|&(v, _)| (v >> bit) & 1 == 0);
    if split == 0 || split == leaves.len() { return swap_tree(reg, leaves, bit, swaps); }
    let left = swap_tree(reg, &leaves[..split], bit, swaps);
    let right = swap_tree(reg, &leaves[split..], bit, swaps);
    swaps.push((reg[bit], left, right));
    left
}

/// Scheme G: lanes appended to the column pool (FD_MIDG; the lean middle uses none of them)
pub const EXTRA: usize = 0;

/// Scheme G replaces the rho middle (FD_MIDG=1 / MIDG_ON)
pub const MIDG_ON: bool = true;
pub fn enabled() -> bool {
    MIDG_ON || std::env::var("FD_MIDG").is_ok()
}

/// Stage 5 (HT division) in place on the 13 lanes and sx (false: the headroom division)
pub const G_IP5: bool = true;

/// crossing reserve: lanes of the parking cycle beyond Q + x128 (MIDG_RES overrides; fewer if the pool lacks them)
/// Direct-control V-form increments allow sx[1] to join the HT payload cycle after q19 is positioned.
pub const PARK_RES: usize = 7;
pub fn park_reserve() -> usize {
    std::env::var("MIDG_RES").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(PARK_RES)
}

/// Gate register v = (sz + sy + 38) mod 64 = s9 - 218 for s9 = sz + sy in [218, 281]: bit kb of q can be set only if
/// kb < 258 - s9, i.e. v <= 39 - kb (a shot with s9 < 218 has q >= 2^40: a capped failure either way).
const VB: usize = 6;
const VOFF: usize = 38;

/// lowq-size FD_MID_CHAIN: sx lanes for the IP5 block's sw-toggle comparator chain (short: the exact compact form)
fn mid_chain() -> usize { std::env::var("FD_MID_CHAIN").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(7) }

/// act ^= the HT stepping flag: ph & not done (done derived), in dq columns & !(sz < sy) (a delayed shot's no-step
/// column; the in-place compare on `c0`)
#[allow(clippy::too_many_arguments)]
fn ht_act(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, act: QubitId, temps: &[QubitId], c0: QubitId,
          dirty: &[QubitId]) {
    let mut lits = vec![(fd.ph, false)];
    let lt = if cp.dq {
        let lt = super::arith::up_m(b, &sc.sz, &fd.sy, c0, true);
        b.play(&lt, false);
        lits.push((fd.sy[fd.sy.len() - 1], true));
        Some(lt)
    } else { None };
    if cp.dn { mc_xor_dn(b, &lits, act, temps, dirty, fd, cp.l0, false); }
    else { mc_xor(b, &lits, act, temps, dirty); }
    if let Some(lt) = lt { b.play(&lt, true); }
}

/// The Scheme G middle (stages 3-7). Pool lanes: sz, sw and mid2's nine single roles (bq, the P zero / cmpc, P f / g
/// / c0, the two old stored-quotient lanes, mz); sx is scratch (gate register, decoder prefixes, compare chains).
/// q's bits live in the ring headroom (X's positions 258 - sz + .., ring[sz + kb]; no add carries there) and,
/// while the V form is entered or left (R needs the headroom), in Q above Y (Q + bq as lane 128 + the crossing
/// reserve). HR: binary search in the V form, V -= qY, leave, D^-1. HT: trial-subtract division, X += qY, enter,
/// reverse search, leave.
#[allow(clippy::too_many_arguments)]
pub(crate) fn middle(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, pl: Option<&PlCol>, _swap: &[Gate],
                     stage: &mut dyn FnMut(&mut B) -> bool) {
    let n = cp.n;
    let compact675 = n == 258;
    let window_base = cp.h - 1;
    let ring = fd.ring.clone();
    let q = fd.q.clone();
    let nq = q.len();
    let ph = fd.ph;
    let (k, kp, tot) = (cp.k, cp.kp, cp.tot);
    let dirty = sc.dirty.clone();
    let _ = tot;
    let qf = super::mid2::QF;
    let pclo = cp.sz.0 + cp.h;
    let mt = (n - pclo + 1).min(nq.max(cp.xw) + 1);
    let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
    let loan_end = nq - if cp.dn { fd.cnt.len() } else { 0 };
    assert!(cp.h >= k + 1, "the window starts at lane K + 1 of the test frame: ring headroom K + 2");
    let sx = fd.sx.clone();
    assert!(sx.len() >= 8);
    // pool roles: act, c0 (carries), bq (adder h / bank lane, and Q's lane 128 while q is parked above Y), the P zero
    // (the adders' zero source); sx: the gate register v, ak (gated act), c (gate temp, decision / bit in flight)
    // the 13-lane layout (sz, sw, bq, cmpc, f, g): act on g, the adders' carry c0 on f, Q's lane 128 on bq, the
    // zero source (sc.zeros) on cmpc
    let (act, c0, x128, pzero) = (sc.g, sc.f, sc.bq, sc.cmpc);
    assert_eq!(sc.zeros, vec![pzero]);
    let (ak, c) = (sx[VB], sx[VB + 1]);
    let bmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0).min(qf);
    let kmax = bmax.min(mt);
    let precision24 = (0..=17).contains(&k) && (n == 259 + k || (compact675 && k == 0)) && nq == 128 && sx.len() == 8
        && dirty.len() == 259 && (cp.h == k + 2 || (compact675 && cp.h == 1))
        && cp.sz.0 >= 57 && cp.sz.1 <= 256;
    let fixed_hr = precision24 && k == 0 && cp.hr && cp.sy.1 <= if compact675 {116_usize.saturating_sub(qf)} else {102}
        && !(cp.sw || cp.psw || cp.dl || cp.dq)
        && std::env::var_os("B7A_A_HR").is_some();
    let fixed_ht = precision24 && k == 0 && cp.ht && cp.sy.1 <= if compact675 {116_usize.saturating_sub(qf)} else {102}
        && !(cp.sw || cp.psw || cp.dl || cp.dq)
        && std::env::var_os("B7A_A_HT").is_some();
    let b8b_cross = !compact675 && precision24 && k == 0 && (cp.sw || cp.psw || cp.dl || cp.dq)
        && std::env::var("B8B_O3").as_deref() == Ok("1");
    // Vform may run with quotient bits parked above Y. The exact paired
    // care rotation maps every parked Q bit back to index sy + kb, for
    // kb < kmax; reserve bits above Q remain outside this bank. Keep the
    // entire public support, the old Y/done support and the live counter.
    // At each V play, only one chunk is parked; the refined K0 cuts still
    // assert that every chunk fits K+6 physical slots. Stage 5 has no V play.
    let parked_v_len = if fixed_hr || fixed_ht || b8b_cross { kmax + 1 }
        else if precision24 && chunked() { kmax.min(k + 6) } else { kmax };
    let p_bank_lo = lsb.max(cp.sy.1.min(nq) + parked_v_len);
    // Q[127] is the K1 reciprocal's second routed owner, so it cannot also
    // be returned comparator scratch during that same V play.
    let p_bank: Vec<QubitId> = if p_bank_lo < loan_end {
        q[p_bank_lo..loan_end].iter().copied().filter(|&lane| (k > 1 || lane != q[127]) && (k != 0 || lane != q[126]) && (!compact675 || lane != q[125])).collect()
    } else { vec![] };
    assert!(!p_bank.iter().any(|q| dirty.contains(q) || ring.contains(q) || sx.contains(q)
        || sc.sz.contains(q) || [act, c0, x128, pzero, ph, sc.sw].contains(q)));
    let fixed_ht_bank = if fixed_ht { p_bank.clone() } else { vec![] };
    // N277 has physical K18 and h20. Keep the 24-bit head and 25-lane remainder:
    // ring[0..19] plus sx[1..5]. The divisor's high zero is virtual, so
    // ring[19] serves R and the V window's unused top position. External
    // q19..q23 live in returned SX owners between V calls and park before R.
    // sx[0] (the quotient lane) is returned before each stage1_v geometry
    // query, so it can hold gt0 until that query is inverted. This alias is
    // exclusive to stage1_v; stage1_fwd keeps its original distinct gt0.
    // agent_lowq_quot: N = 259 + K (K 0..=17, h = K + 2) with the K-lane remainder (24 lanes)
    // The physical window starts at K+1=19, but the reciprocal reads the top 24 ring
    // lanes. The care rotation must preserve all 24 destination lanes.
    if std::env::var_os("QUOT_MIDDBG").is_some() {
        eprintln!("MIDDBG n {} k {} h {} sz {:?} sy {:?} kmax {} mt {} p24 {} hr {} ht {} sw {} dl {} dq {} dn {} tt {}",
                  n, k, cp.h, cp.sz, cp.sy, kmax, mt, precision24, cp.hr, cp.ht, cp.sw, cp.dl, cp.dq, cp.dn, cp.tt);
    }
    let top_head = if precision24 { HIGH_HEAD_BITS } else { k };
    // ---- recordings
    let dest_r: std::collections::BTreeSet<usize> = (0..window_base + 1 + TC).chain(n - top_head..n).collect();
    // lowq-size FD_MIDG_ZOFF: across the middle sz holds sz - lo (lo = the column's smallest sz, every column's range
    // < 128), so sz[7] is |0>. Rotations by sz rotate by lo and then by the offset, v's constant absorbs lo, and the
    // few in-place sz/sy compares (sw toggles, the dq act, the in-place division's size gates) run on the restored sz.
    // stage1_v reads sz only for its early-column gates (sz + j >= 257), so the offset is off where those exist.
    // Exactly these public columns can park a K2 quotient bit at x128.
    // Use SGW there so gap[4] is an available, paired alternate owner.
    let route_x128 = precision24 && ((k == 2 && (35..=116).contains(&cp.col))
        || (k <= 1 && (32..=121).contains(&cp.col)));
    if precision24 && k <= 1 && !route_x128 {
        // A seven-bit K1 chunk parks no higher than sy+6. The source Y-root
        // tree cannot move data into Q[127] below sy=128 either.
        assert!(cp.sy.1 <= 120, "unrouted K1 column lacks a public top-Q bound");
    }
    let zoff_on = precision24 && !route_x128 && std::env::var("FD_MIDG_ZOFF").map(|v| v == "1").unwrap_or(false)
        && cp.sz.1 - cp.sz.0 < 128 && (sc.sz.len() == 8 || (k <= 6 && sc.sz.len() == 9));
    let zlo = if zoff_on { cp.sz.0 } else { 0 };
    let zshift = rec(b, |b| if zoff_on { super::frogdrop::add_const_dirty_exact(b, &sc.sz, zlo, &dirty); });
    let rot_sz = |b: &mut B, d: &std::collections::BTreeSet<usize>| {
        if zoff_on { super::frogdrop::rot_by_off_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, d); }
        else { rot_by_range_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty, d); }
    };
    let prot = rec(b, |b| rot_sz(b, &dest_r));
    // ring down by sz caring for the P-frame lanes `d` (24 = X's position 257 - sz, kb < 24 = headroom bit kb)
    let rotz = |b: &mut B, d: &[usize]| -> Vec<Gate> {
        let ds: std::collections::BTreeSet<usize> = d.iter().copied().collect();
        rec(b, |b| rot_sz(b, &ds))
    };
    // the V form's scratch: sx[0], sx[1..5]; the divisor's zero top lane is the window top (X's position 257 - sz:
    // 0 on the act shots on entry and exit, never written by the V form; other shots replay consistently).
    // sx[6..8], c0 and the P zero may hold parked bits while
    // stage1_v runs; only sx[0] is borrowed for the size threshold.
    // Carry summaries return before window gating. The first bank lane then
    // holds the optional third gt; increments exclude it until that gt is
    // erased. Threshold prefixes return before gt is computed and are used
    // again only after gt is erased, so they may reuse the complete bank.
    let ycomp_on = precision24 && klane_r() && std::env::var("FD_MIDG_YCOMP").map(|v| v == "1").unwrap_or(false);
    // agent_lowq_quot: below K14 the YCOMP lanes sy[5], sy[6] are R's own (every V-form play is compressed), so the
    // V-form recording is not remapped and the P zero stays R-free
    let ycomp_r = ycomp_on && k <= 13;
    // lowq-size FD_MIDG_SGW (ported): in the columns the offset can't take (sz range >= 128), sz holds g = (1 - sz - sy)
    // mod 256 while R is live (after prot, before prot^-1) instead of compressing sy: g <= bl(q + 1) + 1 <= 23 on the
    // act shots, so sz[5], sz[6], sz[7] are |0> there and serve as R's lanes in place of sy[5], sy[6] (R tolerates other
    // values on the shots without act)
    let sgw_on = precision24 && klane_r() && ycomp_r && std::env::var("FD_MIDG_SGW").map(|v| v == "1").unwrap_or(false)
        && sc.sz.len() == 8 && !zoff_on;
    assert!(!route_x128 || sgw_on, "routed K1/K2 columns require SGW size form");
    let (r5, r6) = if sgw_on { (sc.sz[5], sc.sz[6]) } else { (fd.sy[5], fd.sy[6]) };
    assert!(!precision24 || k >= 13 || ycomp_r, "K12 needs FD_MIDG_YCOMP=1 (R's off-ring lanes sy[5], sy[6])");
    // K11: the P zero joins R as its last off-ring lane (the parks then reserve ph, sw, sy7)
    // (agent_lowq_lane: K5 = ring 264 takes the 17th off-ring lane from Y's leading one, LANE_YROOT)
    let inplace_ab = k == 4 && std::env::var("B2_INPLACE_AB").as_deref() == Ok("1");
    let inplace_r = k <= 3 || inplace_ab;
    // K8: the aligned divisor head's top lane ring[n - 1] (1 on every act shot) is flipped to 0 around each
    // reciprocal and lent to R; the comparator takes that bit as a virtual one (jackylee0424's 693, sub 261d4e06)
    let vh1_r = precision24 && klane_r() && ycomp_r && k <= 8;
    let pzero_r = precision24 && klane_r() && (if ycomp_r { k <= 11 } else { k <= 13 });
    // K10: R's 12th lane is sz7 where sz is in offset form (|0> at every middle instant), else ph (0 on HR act shots;
    // the HT plays flip it, the parked ones already do; the parks then keep sw, sy7)
    // (QUOT_NO_SZ7R=1: ph in every column, the wide-column chunk cuts everywhere)
    let no_sz7r = std::env::var_os("QUOT_NO_SZ7R").is_some();
    let sz7_r = precision24 && klane_r() && ycomp_r && k <= 10 && (zoff_on || sgw_on) && !no_sz7r;
    let ph_r = precision24 && klane_r() && ycomp_r && (k <= 9 || (k <= 10 && !sz7_r));
    // K9: R's 13th lane is ph (narrow columns) or sw (wide: 0 on every V-form play's act shots), the parks keep sw, sy7
    // (RES 2) / sy7 (RES 1)
    // (a 9-lane sz holds sw: col 0, HR only with sy < 128 and no crossing, so its parks need no reserve and sy7 is |0>)
    // K7 (agent_lowq_quot, ring 266): R's 15th lane is sw in every column (0 on the act shots of every V-form play:
    // act is g there; a switch column's sw marks switching shots, which never act), or sy7 where sw is an sz lane
    let k7 = k <= 7;
    // K6 (ring 265): R's 16th lane is sy7 in every column, cleared around each V-form play (sy7 ^= [sy mod 128 == 0]:
    // every stepping shot has 1 <= sy <= 128, so the low seven lanes give sy; the plays read only those: SGW columns
    // play the parked form); the V-form parks then keep no reserve (RES 0)
    let k6 = k <= 6;
    let sy7n_r = precision24 && klane_r() && ycomp_r && k6;
    let sy7_r = precision24 && klane_r() && ycomp_r && ((k <= 9 && (!sz7_r || k7) && sc.sz.contains(&sc.sw)) || k6);
    assert!(sy7n_r || !sy7_r || (!cp.ht && cp.sy.1 < 128), "sy7 joins R only in an HR column with sy < 128");
    let sw_r = precision24 && klane_r() && ycomp_r && k <= 9 && (!sz7_r || k7) && !sc.sz.contains(&sc.sw);
    // K6 in col 0 (9-lane sz in offset form, sz - zlo < 64): sw is sz[8], |0> on the act shots
    let swz_r = precision24 && klane_r() && ycomp_r && k6 && zoff_on && sz7_r && sc.sz.len() == 9 && sc.sz[8] == sc.sw;
    // K7 in a column whose sz holds sw and no sz7 lane (col 0: 9-lane sz, HR only): Q's lane 128 (x128), which no
    // park reaches there (sy + kmax <= 127: every parked bit stays in Q, the cycle's lane 128 is 0)
    let x128_r = precision24 && klane_r() && ycomp_r &&
        (k <= 2 || (k7 && !k6 && !sz7_r && sy7_r && !cp.ht && cp.sy.1 + kmax <= 127));
    let q127_r = precision24 && klane_r() && ycomp_r && k <= 1;
    let q126_r = precision24 && klane_r() && ycomp_r && k == 0;
    // agent_lowq_lane (LANE_YROOT=1, K <= 6): Y's leading one. Every stepping shot has 1 <= sy <= 128 and Q[sy - 1] = 1
    // (sy = bl(Y)); a swap tree on sy brings that lane to Q[ylo - 1] around each V-form play, where it is flipped to |0>
    // on the act shots and lent to R (other shots: dirt, restored). K6: in place of sy7 (A/B); K5: R's 17th lane.
    let (ylo, yhi) = (cp.sy.0.max(1), cp.sy.1.min(nq));
    // agent_lowq_lane LANE_ACTR=1 (default at K4): act uncomputed around each V-form play and lent to R (the window
    // adds and gates run without it, LANE_NOACT); at K5 in place of the Y root (A/B), at K4 R's 18th lane
    let actr = precision24 && klane_r() && ycomp_r && k <= 5
        && (k <= 4 || std::env::var("LANE_ACTR").map(|v| v == "1").unwrap_or(false));
    let yroot_r = precision24 && klane_r() && ycomp_r && k6 && ylo <= yhi && !inplace_ab
        && ((k <= 5 && !(actr && k == 5)) || std::env::var("LANE_YROOT").map(|v| v == "1").unwrap_or(false));
    assert!(!precision24 || k >= 6 || yroot_r || actr, "K5 needs Y's leading one (sy range {:?})", cp.sy);
    assert!(!precision24 || k >= 5 || ((yroot_r || inplace_ab) && actr), "K4 needs Y's leading one or the in-place flag, and act");
    assert!(!precision24 || k >= 4 || (yroot_r && actr && inplace_r), "K3 needs Y's leading one, act, and the in-place flag");
    assert!(!precision24 || k >= 3 || (x128_r && (!route_x128 || sgw_on)),
            "K2/K1 requires x128 and SGW when routed");
    assert!(!precision24 || k >= 2 || (q127_r && yroot_r && actr && inplace_r && q[127] != q[(ylo - 1).min(nq - 1)]),
            "K1 requires Q[127] distinct from the Y-root and all prior loans");
    assert!(!precision24 || k >= 1 || (q126_r && q[126] != q[127] && q[126] != q[(ylo - 1).min(nq - 1)]),
            "K0 requires Q[126] distinct from Q[127] and the Y-root");
    let yroot = q[(ylo - 1).min(nq - 1)];
    let mut reciprocal_r = ring[0..k + 1].to_vec();
    if precision24 && klane_r() {
        // agent_lowq_quot: 24 lanes, ring[0..=K+1] (the window top shared as in the virtual zero) + sx[1..] (+ c0
        // below K15): sx[6], sx[7] and c0 are idle while the V form is entered or left, so the park's reserve is
        // R-free there (QUOT_RES_A)
        if !compact675 { reciprocal_r.push(ring[window_base]); }
        let tail: Vec<QubitId> = if ycomp_r {
            let mut t = vec![c0, r5, r6, pzero];
            if sz7_r { t.push(sc.sz[7]); }
            if ph_r { t.push(ph); }
            if sw_r || swz_r { t.push(sc.sw); }
            if sy7_r && !(yroot_r && k == 6) { t.push(fd.sy[7]); }
            if x128_r { t.push(x128); }
            if vh1_r { t.push(ring[n - 1]); }
            if yroot_r { t.push(yroot); }
            if actr { t.push(act); }
            if q127_r { t.push(q[127]); }
            if q126_r { t.push(q[126]); }
            if inplace_r { t.push(sx[0]); }
            if compact675 { t.push(q[125]); }
            t
        } else { vec![c0, pzero] };
        reciprocal_r.extend(sx[1..8].iter().copied().chain(tail).take(22 + usize::from(compact675) - k));
    } else if precision24 {
        assert_eq!(k, 17, "the 25-lane remainder is the N276 form");
        if !compact675 { reciprocal_r.push(ring[window_base]); } reciprocal_r.extend([sx[1], sx[2], sx[3], sx[4], sx[5]]);
    }
    // The returned Q bank can hold the early threshold while the comparator
    // and each window gate run, then is returned before the next V play.
    let clean_gate_lane = if precision24 && inplace_r { p_bank.first().copied() } else { None };
    let mut p_gt = if precision24 { vec![clean_gate_lane.unwrap_or(if inplace_r { sc.sz[0] } else { sx[0] })] }
                   else { sx[2..4].to_vec() };
    if !precision24 { if let Some(&third) = p_bank.first() { p_gt.push(third); } }
    let zh: Vec<QubitId> = if precision24 { ring[n - 24..n].to_vec() } else { ring[n - k..n].to_vec() };
    if precision24 {
        assert_eq!(reciprocal_r.len(), if klane_r() { 24 } else { 25 });
        let unique: std::collections::BTreeSet<QubitId> = reciprocal_r.iter().copied().collect();
        assert_eq!(unique.len(), reciprocal_r.len());
        assert!(!reciprocal_r.iter().any(|q| (zh.contains(q) && !(vh1_r && *q == ring[n - 1]))
            || p_gt.contains(q) || (!actr && *q == act)
            || dirty.contains(q) || p_bank.contains(q) || (sc.sz.contains(q) && !(sz7_r && *q == sc.sz[7])
                && !(sgw_on && (*q == sc.sz[5] || *q == sc.sz[6])) && !(swz_r && *q == sc.sw))
            || (!x128_r && *q == x128) || (!sw_r && !swz_r && *q == sc.sw) || (!ph_r && *q == ph) || (k >= 15 && *q == c0) || (!pzero_r && *q == pzero)
            || (!ycomp_r && fd.sy.contains(q)) || fd.sy[..5].contains(q) || (!sy7_r && fd.sy[7] == *q)
            || sx.iter().enumerate().any(|(i, x)| !(i == 0 && inplace_r) && !(1..=22 - k.min(17)).contains(&i) && x == q)));
        assert_eq!(p_gt[0], clean_gate_lane.unwrap_or(if inplace_r { sc.sz[0] } else { sx[0] }));
        assert!(!zh.iter().any(|q| sx.contains(q) || sc.sz.contains(q)
            || [ring[window_base], act, c0, x128, pzero, ph, sc.sw].contains(q)
            || dirty.contains(q) || p_bank.contains(q)));
    }
    let s1 = S1 { r: reciprocal_r, f: sx[0], zero: ring[window_base], sgn: sx[0], gt: p_gt,
                  anc: p_bank.iter().skip(1).copied().collect(),
                  andc: p_bank.clone(), chain: if clean_gate_lane.is_some() { p_bank[1..].to_vec() } else { p_bank },
                  dirty: dirty.clone() };
    // An unparked SGW play has no quotient chunk in Q. The K0 and K1
    // reciprocal owners remain excluded from the returned bank.
    let unpark_lo = lsb.max(cp.sy.1.min(nq));
    let unpark_bank: Vec<QubitId> = if unpark_lo < loan_end {
        q[unpark_lo..loan_end].iter().copied().filter(|&lane| (k > 1 || lane != q[127]) && (k != 0 || lane != q[126]) && (!compact675 || lane != q[125])).collect()
    } else { vec![] };
    let mut s1u = s1.clone();
    if sgw_on && inplace_r && unpark_bank.len() > s1.andc.len() {
        assert!(!unpark_bank.iter().any(|q| dirty.contains(q) || s1.r.contains(q)
            || ring.contains(q) || sx.contains(q) || sc.sz.contains(q)
            || [act, c0, x128, pzero, ph, sc.sw].contains(q)));
        s1u.gt = vec![unpark_bank[0]];
        s1u.anc = unpark_bank[1..].to_vec();
        s1u.andc = unpark_bank.clone();
        s1u.chain = unpark_bank[1..].to_vec();
    }
    let win: Vec<QubitId> = ring[window_base..window_base + 1 + TC].to_vec();
    let mut b8b_forms:Vec<Vec<G>>=vec![];
    let mut b8b_forms_ht:Vec<Vec<G>>=vec![];
    let mut make_vforms=|b:&mut B,zh:Vec<QubitId>,mut s1:S1,mut s1u:S1,
                         head_domain:Option<bool>,clip_high_tree:bool| {
        S1_HEAD_DOMAIN.with(|v|v.set(head_domain));
        let domain_d=head_domain.map(|_|s1.dirty[0]);
        if let Some(d)=domain_d {s1.dirty.retain(|&q|q!=d);s1u.dirty.retain(|&q|q!=d);}
        S1_V_DOMAIN_DIRTY.with(|v|v.set(domain_d));
        S1_V_EARLY_XOR.with(|v|v.set(true));
        S1_RAW_Y_GAP.with(|v|*v.borrow_mut()=fd.sy[..5].to_vec());
        S1_SGW_Y_GAP.with(|v|*v.borrow_mut()=sc.sz[..5].to_vec());
    let szr = (cp.sz.0, cp.sz.1);
    let record_inverse=|b:&mut B,state:&S1| {
        if domain_d.is_some() {
            S1_V_EARLY_XOR.with(|v|v.set(false));
            let r=stage1_v(b,&zh,&win,&sc.sz,szr,state,act,true);
            S1_V_EARLY_XOR.with(|v|v.set(true));r
        } else {stage1_v(b,&zh,&win,&sc.sz,szr,state,act,false)}
    };
    S1_ZLO.with(|z| z.set(zlo));
    S1_NOACT.with(|c| c.set(precision24 && (actr || std::env::var("LANE_NOACT").map(|v| v == "1").unwrap_or(false))));
    let fv = stage1_v(b, &zh, &win, &sc.sz, szr, &s1, act, true);
    let fr = record_inverse(b,&s1);
    S1_ZLO.with(|z| z.set(0));
    // enter / leave the V form on the act shots: X += T - G (R cleared by its own replay); v must be clear (sx)
    let selected_v=|b:&mut B,fv:&[Gate],frx:&[Gate],gate:&S1Gate,dirty:&[QubitId]| {
        if let Some(d)=domain_d {
            let qp=rec(b,|b|{
                S1_ZLO.with(|v|v.set(zlo));
                head25_y_xor(b,gate,&sc.sz,d,dirty);
                S1_ZLO.with(|v|v.set(0));
                if head_domain==Some(false){b.x(d);}
            });
            for &q in &win[1..]{b.cx(d,q);}
            b.play(fv,false);b.play(&qp,false);b.play(frx,true);b.play(&qp,true);
            for &q in &win[1..]{b.cx(d,q);}
        } else {b.play(fv,false);b.play(frx,true);}
    };
    let vform = rec(b, |b| {
        b.play(&prot, false);
        if vh1_r { b.x(ring[n - 1]); }
        selected_v(b,&fv,&fr,&S1Gate::Sz,&s1.dirty);
        if vh1_r { b.x(ring[n - 1]); }
        b.play(&prot, true);
    });
    // lowq-size FD_MIDG_YCOMP: inside the parked V-form windows (between park and unpark) sy is not read, so its low
    // seven lanes (sy mod 128; sy[7] is a park lane there) hold g = (1 - sz - sy) mod 128 = 257 - sz - sy (< 32 on
    // every kind), leaving sy[5], sy[6] |0>. They replace sx[6], sx[7] as R's off-ring lanes in a second V-form
    // recording played only there. f(y) = 1 - sz - y is an involution: one ancilla-free record (TTK add,
    // complement, +2 by a dirty increment) enters and leaves the compressed form.
    let ycomp_on = ycomp_on && !sgw_on;
    let ycomp = rec(b, |b| {
        if !ycomp_on { return; }
        super::arith::ttk_add(b, &sc.sz[..7], &fd.sy[..7], None, None);
        for &y in &fd.sy[..7] { b.x(y); }
        if zoff_on { super::frogdrop::add_const_dirty_exact(b, &fd.sy[..7], (130 - zlo % 128) % 128, &dirty); }
        else { super::modp_frogdrop::inc_dirty_free(b, &fd.sy[1..7], &dirty); }
    });
    let vform_p = if !ycomp_on || ycomp_r { vform.clone() } else {
        let rc: Vec<QubitId> = s1.r.iter().map(|&q| if q == sx[6] { fd.sy[5] } else if q == sx[7] { fd.sy[6] } else { q })
            .collect();
        let s1c = S1 { r: rc, f: s1.f, zero: s1.zero, sgn: s1.sgn, gt: s1.gt.clone(), anc: s1.anc.clone(),
                       andc: s1.andc.clone(), chain: s1.chain.clone(), dirty: s1.dirty.clone() };
        S1_ZLO.with(|z| z.set(zlo));
        let fvc = stage1_v(b, &zh, &win, &sc.sz, szr, &s1c, act, true);
        let frc = record_inverse(b,&s1c);
        S1_ZLO.with(|z| z.set(0));
        rec(b, |b| { b.play(&prot, false); selected_v(b,&fvc,&frc,&S1Gate::Sz,&s1c.dirty); b.play(&prot,true); })
    };
    // every V-form play (parked or not) runs in the compressed form: nothing inside reads sy
    let vform = if !ycomp_on { vform } else {
        rec(b, |b| { b.play(&ycomp, false); b.play(&vform_p, false); b.play(&ycomp, false); })
    };
    // (lowq-size FD_MIDG_SGW, ported) separate recordings for the unparked plays (sy whole) and the parked ones (sy[7]
    // lent, low7 = 0 = 128)
    let (vform, vform_pk) = if !sgw_on {
        (vform.clone(), vform)
    } else {
        let a = &sc.sz;
        let sy = &fd.sy;
        assert!(sy.len() == 8 && !dirty.iter().any(|q| a.contains(q) || sy.contains(q) || *q == sx[7] || *q == act));
        // A := 1 - A - sy (an involution); the parked form adds 128 where low7 = 0, zero-extending low7 by sx[7]
        // (an R lane: |0> on the act shots before fv and after fr^-1; the transform is an involution on every shot)
        let sg_u = rec(b, |b| {
            super::arith::ttk_add(b, &sy[..8], &a[..8], None, None);
            for &x in a.iter() { b.x(x); }
            super::modp_frogdrop::inc_dirty_free(b, &a[1..], &dirty);
        });
        let sg_p = rec(b, |b| {
            let mut ax: Vec<QubitId> = sy[..7].to_vec();
            ax.push(sx[7]);
            super::arith::ttk_add(b, &ax, &a[..8], None, None);
            let zero: Vec<(QubitId, bool)> = sy[..7].iter().map(|&q| (q, true)).collect();
            mc_xor(b, &zero, a[7], &[], &dirty);
            for &x in a.iter() { b.x(x); }
            super::modp_frogdrop::inc_dirty_free(b, &a[1..], &dirty);
        });
        // the gates' u: sy += A (8 lanes) / low7 += A[..7] (mod 128); undone after fr^-1, when A[5..8] are R-free again
        let u_u = rec(b, |b| super::arith::ttk_add(b, &a[..8], &sy[..8], None, None));
        let u_p = rec(b, |b| super::arith::ttk_add(b, &a[..7], &sy[..7], None, None));
        // The V-time order sz>=sy makes g[4]=0 whenever a K2 park can
        // occupy x128: sy+offset=128 with offset<=7 gives sy>=121 and g<=15.
        // The four disjoint prefixes select sy low7 in {0,121..127}, i.e.
        // the active range 121..128. U forms run after this swap. On selected
        // shots with a parked 1, the routed gap may gain 16, but both U8 and
        // UPark early gates still return false for every j<=25.
        let route = if compact675 {
            super::lowq675_routes::record(b,cp.col,-1,-1,sy,a,[x128,q[127],q[126],q[125]],c0,&dirty)
        } else { rec(b, |b| if route_x128 {
            let prefixes: [&[(usize, bool)]; 4] = [
                &[(6, true), (5, true), (4, true), (3, true), (2, true), (1, true), (0, true)],
                &[(6, false), (5, false), (4, false), (3, false), (2, true), (1, true), (0, false)],
                &[(6, false), (5, false), (4, false), (3, false), (2, true), (1, false)],
                &[(6, false), (5, false), (4, false), (3, false), (2, false)],
            ];
            for p in prefixes {
                let controls: Vec<(QubitId, bool)> = p.iter().map(|&(i, neg)| (sy[i], neg)).collect();
                super::mid2::mc_swap(b, &controls, x128, a[4], &[], &dirty);
            }
            if q127_r {
                let sy_eq = |v: usize| -> Vec<(QubitId, bool)> {
                    (0..7).map(|i| (sy[i], ((v >> i) & 1) == 0)).collect()
                };
                let mut swap_q = |controls: Vec<(QubitId, bool)>, bit: usize| {
                    super::mid2::mc_swap(b, &controls, q[127], a[bit], &[], &dirty);
                };
                let cross_col = cp.sw || cp.psw || cp.dl || cp.dq;
                if !cross_col && cp.sy.0 <= 124 && cp.sy.1 >= 122 {
                    assert!(257usize.saturating_sub(cp.sz.0 + 122) <= 7,
                            "K1 noncrossing Q[127] route requires g<=7 at sy>=122");
                }
                // sy=125; sy=126/127 share a six-bit prefix; sy=128 is
                // low-seven zero. These controls remain stable through V.
                swap_q(sy_eq(125), 3);
                swap_q((1..7).map(|i| (sy[i], false)).collect(), 3);
                swap_q(sy_eq(128), 3);
                if cross_col {
                    // At sy=122, g=12/13 may park both Q[127] and x128;
                    // g[1] is then zero, while g[3:2] stay unchanged.
                    let mut exceptional = sy_eq(122);
                    exceptional.extend([(a[3], false), (a[2], false)]);
                    swap_q(exceptional, 1);
                    for v in [121, 123, 124] { swap_q(sy_eq(v), 4); }
                    let mut low = sy_eq(122);
                    low.push((a[3], true));
                    swap_q(low, 4);
                    let mut mid = sy_eq(122);
                    mid.extend([(a[3], false), (a[2], true)]);
                    swap_q(mid, 4);
                } else {
                    swap_q(sy_eq(121), 4);
                    // sy=122/123 share the high six low-seven bits.
                    swap_q((1..7).map(|i| (sy[i], ((122 >> i) & 1) == 0)).collect(), 3);
                    swap_q(sy_eq(124), 3);
                }
            }
            if q126_r { b6_route_third(b, sy, a, q[126], cp.sw || cp.psw || cp.dl || cp.dq, &dirty); }
        })
        };
        let (dk, d2) = (dirty[dirty.len() - 1], dirty[dirty.len() - 2]);
        S1_GATE.with(|g| *g.borrow_mut() = S1Gate::U8 { u: sy[..8].to_vec() });
        let fvu = stage1_v(b, &zh, &win, &sc.sz, szr, &s1u, act, true);
        let fru = if s1u.andc == s1.andc { fr.clone() }
                  else { record_inverse(b,&s1u) };
        S1_GATE.with(|g| *g.borrow_mut() = S1Gate::UPark { u: sy[..7].to_vec(), g: a[..5].to_vec(), dk, d2 });
        let fvp = stage1_v(b, &zh, &win, &sc.sz, szr, &s1, act, true);
        let fvp_u = if sy7n_r && s1u.andc != s1.andc {
            stage1_v(b, &zh, &win, &sc.sz, szr, &s1u, act, true)
        } else { fvp.clone() };
        S1_GATE.with(|g| *g.borrow_mut() = S1Gate::Sz);
        if b8b_cross {
            b8b_forms = b8b_make_raw_parked_forms(b, &prot, &sg_p, &u_p, &fvp, &fr,
                vh1_r.then_some(ring[n - 1]), sy, a, [x128, q[127], q[126]],
                cp.sw.then_some(sc.sw), Some((&route, ph, pzero, c0)), &dirty);
            b8b_forms_ht = b8b_make_raw_parked_forms(b, &prot, &sg_p, &u_p, &fvp, &fr,
                vh1_r.then_some(ring[n - 1]), sy, a, [x128, q[127], q[126]],
                cp.sw.then_some(sc.sw), Some((&route, ph, pzero, c0)), &dirty);
        }
        let mk = |b: &mut B, sg: &[Gate], u: &[Gate], fv: &[Gate], frx: &[Gate], query_gate:&S1Gate, query_dirty:&[QubitId]| rec(b, |b| {
            b.play(&prot, false);
            b.play(sg, false);
            b.play(&route, false);
            b.play(u, false);
            if vh1_r { b.x(ring[n - 1]); }
            selected_v(b,fv,frx,query_gate,query_dirty);
            if vh1_r { b.x(ring[n - 1]); }
            b.play(u, true);
            b.play(&route, true);
            b.play(sg, false);
            b.play(&prot, true);
        });
        let query_u=S1Gate::U8{u:sy[..8].to_vec()};
        let query_p=S1Gate::UPark{u:sy[..7].to_vec(),g:a[..5].to_vec(),dk,d2};
        if sy7n_r { (mk(b,&sg_p,&u_p,&fvp_u,&fru,&query_p,&s1u.dirty),mk(b,&sg_p,&u_p,&fvp,&fr,&query_p,&s1.dirty)) }
        else { (mk(b,&sg_u,&u_u,&fvu,&fru,&query_u,&s1u.dirty),mk(b,&sg_p,&u_p,&fvp,&fr,&query_p,&s1.dirty)) }
    };
    S1_NOACT.with(|c| c.set(false));
    // K6: sy7 cleared around every V-form play (an R lane inside)
    let (vform, vform_pk) = if !sy7n_r { (vform, vform_pk) } else {
        let zero: Vec<(QubitId, bool)> = fd.sy[..7].iter().map(|&q| (q, true)).collect();
        let n7 = rec(b, |b| mc_xor(b, &zero, fd.sy[7], &[], &dirty));
        let w = |b: &mut B, r: &[Gate]| rec(b, |b| { b.play(&n7, false); b.play(r, false); b.play(&n7, false); });
        if b8b_cross {
            b8b_forms = b8b_forms.iter().map(|r| w(b, r)).collect();
            b8b_forms_ht = b8b_forms_ht.iter().map(|r| w(b, r)).collect();
        }
        (w(b, &vform), w(b, &vform_pk))
    };
    // agent_lowq_lane LANE_YROOT: the tree on sy (outside n7 / ycomp / sgw: sy whole there), Y's top to yroot, flipped
    let (vform, vform_pk) = if !yroot_r { (vform, vform_pk) } else {
        let tree_hi=if clip_high_tree {yhi.min(HEAD25_SY_MAX)}else{yhi};
        assert!(ylo<=tree_hi);
        let leaves:Vec<(usize,QubitId)>=(ylo..=tree_hi).map(|v|(v,q[v-1])).collect();
        let mut swaps = vec![];
        let root = swap_tree(&fd.sy, &leaves, fd.sy.len(), &mut swaps);
        assert_eq!(root, yroot);
        let tr = rec(b, |b| { for &(bit, l, r) in &swaps { b.cswap(bit, l, r); } });
        let w = |b: &mut B, r: &[Gate]| rec(b, |b| {
            // (LANE_YROOT_BAD=1: negative control, no flip)
            let flip = std::env::var_os("LANE_YROOT_BAD").is_none();
            b.play(&tr, false); if flip { b.x(yroot); } b.play(r, false); if flip { b.x(yroot); } b.play(&tr, true);
        });
        if b8b_cross {
            b8b_forms = b8b_forms.iter().map(|r| w(b, r)).collect();
            b8b_forms_ht = b8b_forms_ht.iter().map(|r| w(b, r)).collect();
        }
        (w(b, &vform), w(b, &vform_pk))
    };
    S1_HEAD_DOMAIN.with(|v|v.set(None));
    S1_V_DOMAIN_DIRTY.with(|v|v.set(None));
    S1_V_EARLY_XOR.with(|v|v.set(true));
    S1_RAW_Y_GAP.with(|v|v.borrow_mut().clear());
    S1_SGW_Y_GAP.with(|v|v.borrow_mut().clear());
    (vform,vform_pk)
    };
    // Q117..Q124 are zero on SY<=112: Y ends at111, a <=5-bit
    // chunk ends at116, and fixed parks are publicly bounded below117.
    // The high Y-root tree never touches any of these eight owners.
    let loans:Vec<QubitId>=q[117..125].to_vec();
    assert!(loans.iter().all(|q|!s1.r.contains(q)&&!dirty.contains(q)));
    let extend=|old:&S1| {
        let mut next=old.clone();next.r.extend(loans.iter().copied());
        assert_eq!(next.r.len(),HIGH_HEAD_BITS);
        let bank:Vec<_>=old.andc.iter().copied().filter(|q|!loans.contains(q)).collect();
        next.gt=vec![bank.first().copied().unwrap_or(sc.sz[0])];
        next.anc=bank.iter().skip(1).copied().collect();
        next.chain=bank.iter().skip(1).copied().collect();next.andc=bank;next
    };
    let (vform,vform_pk)=if ylo>HEAD25_SY_MAX {
        make_vforms(b,zh.clone(),s1.clone(),s1u.clone(),None,false)
    } else if yhi<=HEAD25_SY_MAX {
        make_vforms(b,ring[n-HIGH_HEAD_BITS..n].to_vec(),extend(&s1),extend(&s1u),None,true)
    } else {
        let low=make_vforms(b,zh.clone(),s1.clone(),s1u.clone(),Some(false),false);
        let high=make_vforms(b,ring[n-HIGH_HEAD_BITS..n].to_vec(),extend(&s1),extend(&s1u),Some(true),true);
        let join=|b:&mut B,l:&[Gate],h:&[Gate]|rec(b,|b|{b.play(l,false);b.play(h,false);});
        (join(b,&low.0,&high.0),join(b,&low.1,&high.1))
    };
    let lowq675_forms:Vec<Vec<G>>=super::lowq675_routes::bounds(cp.col,kmax).windows(2).map(|_|vform_pk.clone()).collect();
    assert!(!b8b_cross || (b8b_forms.len() == 3 && b8b_forms_ht.len() == 3));
    // q19..q23 occupy sx[1..5] between V calls. Form v in SZ for each
    // threshold query, restoring SZ before any arithmetic or rotation.
    let external_q = |kb: usize| if compact675 && kb < 5 { Some(sx[kb+1]) }
        else if !compact675 && precision24 && (k + 1..=k + 5).contains(&kb) { Some(sx[kb - k]) } else { None };
    assert!(!precision24 || kmax <= if compact675 { super::mid2::QF } else {23});
    // one session stores all of q in the headroom and sx[1..5]
    assert!(!precision24 || chunked() || kmax <= k + 6);
    let qloc = |kb: usize| external_q(kb).unwrap_or(ring[kb]);
    assert!((0..kmax).all(|kb| qloc(kb) != ring[window_base]));
    // v = (sz + sy + VOFF) mod 2^VB, in SZ only during ge_k.
    let v: Vec<QubitId> = sc.sz[..VB].to_vec();
    let vg = rec(b, |b| {
        super::frogdrop::reg_add_into(b, &v, &fd.sy[..VB], &[], c0);
        let voff = (VOFF + zlo) % (1 << VB);
        for i in 0..VB {
            if (voff >> i) & 1 == 1 { super::modp_frogdrop::inc_dirty_free(b, &v[i..], &dirty); }
        }
    });
    // These adder helpers are clean at every gate_on/off boundary: the
    // reciprocal/parking records have returned before vg is live, and each
    // ring add returns c0, pzero and x128 before the next predicate. Both
    // exact comparator forms return the entire bank before the body.
    let gate_chain = [c0, pzero, x128];
    assert_eq!(gate_chain.iter().copied().collect::<std::collections::BTreeSet<_>>().len(), gate_chain.len());
    assert!(!gate_chain.iter().any(|q| v.contains(q) || *q == ak || *q == c));
    // tmp ^= [kb >= 258 - s9] = [v >= 40 - kb]
    let ge_k = |b: &mut B, kb: usize, t: QubitId| {
        b.play(&vg, false);
        super::frogdrop_col::ge_cd(b, &v, (40 - kb) as isize, t, &gate_chain, &dirty);
        b.play(&vg, true);
    };
    // ak = a & [kb < 258 - s9] (tmp = c clear again)
    let gate_on = |b: &mut B, kb: usize, a: QubitId| {
        let f1 = b.tof;
        b.play(&vg, false);
        super::frogdrop_col::ge_cd(b, &v, (40 - kb) as isize, c, &gate_chain, &dirty);
        b.x(c);
        b.and_c(a, c, ak);
        b.x(c);
        super::frogdrop_col::ge_cd(b, &v, (40 - kb) as isize, c, &gate_chain, &dirty);
        b.play(&vg, true);
        super::f1_profile("midg.gate_on", f1, b.tof);
    };
    let gate_off = |b: &mut B, kb: usize, a: QubitId| {
        let f1 = b.tof;
        b.play(&vg, false);
        super::frogdrop_col::ge_cd(b, &v, (40 - kb) as isize, c, &gate_chain, &dirty);
        b.x(c);
        b.and_u(a, c, ak);
        b.x(c);
        super::frogdrop_col::ge_cd(b, &v, (40 - kb) as isize, c, &gate_chain, &dirty);
        b.play(&vg, true);
        super::f1_profile("midg.gate_off", f1, b.tof);
    };
    let add = |b: &mut B, kb: usize, ctl: QubitId, sub: bool| {
        let f1 = b.tof;
        ring_cadd2_loan(b, &ring, &q, kb, mt - kb, ctl, sub, &sc.zeros, c0, x128, &dirty, lsb, loan_end, x128);
        super::f1_profile("midg.ring_add", f1, b.tof);
    };
    // the bit in flight: c <-> headroom lane kb on the shots with AND(extra)
    let fetch = |b: &mut B, kb: usize, extra: &[(QubitId, bool)]| {
        let f1 = b.tof;
        let r = if external_q(kb).is_some() { vec![] } else { rotz(b, &[kb]) };
        b.play(&r, false);
        let qb = qloc(kb);
        let mut ct = extra.to_vec();
        ct.push((qb, false));
        b.cx(c, qb);
        mc_xor(b, &ct, c, &[], &dirty);
        b.cx(c, qb);
        b.play(&r, true);
        super::f1_profile("midg.fetch", f1, b.tof);
    };
    // one search / division step's decision after the trial add: t2 = ak & s, headroom bit kb = ak & !s (s = bit
    // 257 - sz: over in the V form, negative in the division, where the borrow also ran through the headroom);
    // `undo` erases t2 after the revert. t2 is a gate temp (idle between the gate's compares).
    let rv = c;
    let decide = |b: &mut B, kb: usize, undo: bool| {
        let f1 = b.tof;
        let r = rotz(b, &[window_base, kb]);
        b.play(&r, false);
        if undo {
            mc_xor(b, &[(ak, false), (qloc(kb), true)], rv, &[], &dirty);
        } else {
            mc_xor(b, &[(ak, false), (ring[window_base], false)], rv, &[], &dirty);
            mc_xor(b, &[(ak, false), (ring[window_base], true)], qloc(kb), &[], &dirty);
        }
        b.play(&r, true);
        super::f1_profile("midg.decide", f1, b.tof);
    };
    // headroom (P-frame lane kb) <-> Q above Y (Q + x128 + the crossing reserve, down by sy: lane kb) where bit kb can
    // be set; v live
    // Q's extension beyond lane 128 (the crossing step's bits): the lanes idle while the V form is entered or left
    // (c0, the P zero and sx[6..8]), then the park's own flag lanes that are constant on its act shots (`extra`: ph,
    // and sw or g, whichever does not hold act; ph reads 1 on HT act shots and is flipped around the window), then
    // the pool past the 13-lane layout; MIDG_RES lanes in all
    let nres = park_reserve();
    let d24: std::collections::BTreeSet<usize> = (0..kmax).collect();
    // agent_lowq_quot: QUOT_RES_A=n gives the chunked parks (cycle a) n lanes from the R-free set (P zero above K13,
    // ph, sw, sy7) instead of the MIDG_RES list (c0, sx[6], sx[7] belong to R at ring 273); `low` takes `extra` only
    let res_a: Option<usize> = std::env::var("QUOT_RES_A").ok().and_then(|v| v.parse().ok())
        .or(if precision24 && k < 17 { Some(if sy7_r { 0 } else if sw_r { 1 } else if ph_r { 2 } else if pzero_r { 3 } else { 4 }) } else { None });
    // below N276, R holds sx[6] (K <= 16), sx[7] (K <= 15) and c0 (K = 14) while the V form is entered or left
    assert!(!precision24 || k == 17 || (chunked() && res_a.is_some_and(|r| r <= 4)),
            "below N276 the parks need the chunked sessions and an R-free reserve");
    let mk_cycle = |b: &mut B, extra: &[QubitId], ht: bool, low: Option<usize>| -> (Vec<QubitId>, Vec<Gate>) {
        let mut q129: Vec<QubitId> = q.clone();
        q129.push(x128);
        let mut reserve: Vec<QubitId> = if low.is_some() { vec![] } else { vec![c0, pzero, sx[6], sx[7]] };
        reserve.extend(extra.iter().copied());
        if low.is_none() { reserve.extend(&sc.gx); }
        let nres = low.unwrap_or(nres);
        reserve.truncate(nres);
        assert_eq!(reserve.iter().copied().collect::<std::collections::BTreeSet<_>>().len(), reserve.len());
        // (an HR park needs no reserve: sy + bl(q) <= 129 there)
        assert!(!MIDG_ON || !ht || reserve.len() == nres, "crossing reserve: {} of {} lanes", reserve.len(), nres);
        q129.extend(&reserve);
        let rq = if reserve.contains(&fd.sy[7]) {
            // On every model-clean stepping shot, 1 <= sy <= 128. The low
            // seven bits therefore determine sy exactly: zero means 128.
            // This record never reads sy[7], which the cycle may carry.
            borrowed_sy_rotate(b, &q129, &fd.sy, sx[0], &dirty)
        } else {
            rec(b, |b| rot_by_range_care(b, &q129, &fd.sy, cp.sy.0.min(128), cp.sy.1.min(128), true, &dirty, &d24))
        };
        (q129, rq)
    };
    // HR block and HT block (act on g): ph and sw are 0 / (1, 0) on their act shots; HT division (act on sw): ph, g
    // (the P zero joins R at K13: the R-free V-form park lanes are then ph, sw, sy7)
    let ra: Vec<QubitId> = if res_a.is_some() && sy7_r { vec![] }
                           else if res_a.is_some() && sw_r { vec![fd.sy[7]] }
                           else if res_a.is_some() && ph_r { vec![sc.sw, fd.sy[7]] }
                           else if res_a.is_some() && pzero_r { vec![ph, sc.sw, fd.sy[7]] }
                           else if res_a.is_some() { vec![pzero, ph, sc.sw, fd.sy[7]] } else { vec![ph, sc.sw, fd.sy[7]] };
    let (q129a, rqa) = mk_cycle(b, &ra, cp.ht, res_a);
    let (q129b, rqb) = mk_cycle(b, &[ph, act, sx[1]], cp.ht, None);
    // (lowq_cross) only a cycle that borrows sy7 needs it normalized: around a sy7-free cycle the normalization would
    // clear sy7 at sy = 128 and the rotation, which reads all of sy, would see 0
    let sy7_normal = if q129a.contains(&fd.sy[7]) { borrowed_sy_normal(b, &fd.sy, &dirty) } else { vec![] };
    // a bit at Q-cycle index sy + kb >= its length would wrap onto Y: such a bit (a crossing step beyond the reserve)
    // stays in the headroom (a failure if set), so the swap is also gated by sy <= len - 1 - kb
    // (no bit gate: for kb >= B both lanes are zero on the act shots; v must be clear: sx holds the wrap flag)
    let wf = sx[0];
    let wrap_flag = |b: &mut B, kb: usize, qlen: usize, borrow_sy7: bool| {
        let threshold = qlen - kb;
        if borrow_sy7 {
            if threshold <= 128 {
                super::frogdrop_col::ge_const_compact(b, &fd.sy[..7], threshold as isize, wf, &[], &dirty);
                let zero: Vec<(QubitId, bool)> = fd.sy[..7].iter().copied().map(|q| (q, true)).collect();
                mc_xor(b, &zero, wf, &[], &dirty);
            }
        } else {
            super::frogdrop_col::ge_const_compact(b, &fd.sy, threshold as isize, wf, &[], &dirty);
        }
    };
    // slots 0..nb <-> cycle indices 0..nb (nb = kmax: one session; a chunk's length: chunk-relative indices)
    // (agent_lowq_quot: park_for_off: slots base.. <-> cycle indices off.., for a park staged in batches)
    let park_for_off = |b: &mut B, a: QubitId, q129: &[QubitId], rq: &[Gate], relocated19: bool, nb: usize, base: usize,
                        off: usize|
    rec(b, |b| {
        let qlen = q129.len();
        let rz = rotz(b, &(base..base + nb).collect::<Vec<_>>());
        b.play(&rz, false);
        b.play(rq, false);
        for i in 0..nb {
            let kb = off + i;
            if relocated19 && kb == k + 1 { continue; }
            if cp.sy.1.min(128) + kb >= qlen {
                wrap_flag(b, kb, qlen, q129.contains(&fd.sy[7]));
                if q129.contains(&sx[1]) || precision24 {
                    super::mid2::mc_swap(b, &[(a, false), (wf, true)], qloc(base + i), q129[kb], &[], &dirty);
                } else {
                    let akp = sx[1];
                    mc_xor(b, &[(a, false), (wf, true)], akp, &[], &dirty);
                    super::mid2::mc_swap(b, &[(akp, false)], qloc(base + i), q129[kb], &[], &dirty);
                    mc_xor(b, &[(a, false), (wf, true)], akp, &[], &dirty);
                }
                wrap_flag(b, kb, qlen, q129.contains(&fd.sy[7]));
            } else {
                super::mid2::mc_swap(b, &[(a, false)], qloc(base + i), q129[kb], &[], &dirty);
            }
        }
        b.play(rq, true);
        b.play(&rz, true);
    });
    let park_for = |b: &mut B, a: QubitId, q129: &[QubitId], rq: &[Gate], relocated19: bool, nb: usize, base: usize|
        park_for_off(b, a, q129, rq, relocated19, nb, base, 0);
    let park = park_for(b, act, &q129a, &rqa, false, kmax, 0);
    let hr_lits = { let mut l = vec![(ph, true)]; if cp.sw { l.push((sc.sw, true)); } l };
    // ---------------- agent_lowq_quot: chunked sessions (C0 = bits [0, QCH), C1 = [QCH, kmax)). At every loop
    // instant and park at most one chunk is in its slots (bit kb of [a, b) at slot kb - a, park index kb - a); C1 is
    // consumed into X between the sessions (D^-1) and rebuilt by an in-place division (q_kk at X-index sy + kk, zero
    // while X < 2^kk Y). HR: S1 finds C1, D^-1 C1, S2 finds C0, divide >= QCH, one D^-1 of all bits with the payload.
    // HT: D^-1 C1, X += C0 Y, S1 erases C0, divide >= QCH and rebuild C1 into its slots, S2 erases C1.
    // (lowq_cross) N chunks: 0 = bd[0] < bd[1] < .. < bd[nch] = kmax; the HR sessions run C_{nch-1} .. C_0, the HT
    // sessions C_0 .. C_{nch-1}; the cut list [qch()] is the two-chunk form above
    let bd: Vec<usize> = { let mut v = vec![0];
                           // (QUOT_CUTS_CROSS_ONLY=1: the extra chunks only where a crossing step can park, i.e. a
                           // switch / delayed / no-step column or the one after a switch; elsewhere no park needs the
                           // reserve and two chunks fit the slots)
                           let cross_col = cp.sw || cp.psw || cp.dl || cp.dq;
                           let cuts = if !cross_col && std::env::var("QUOT_CUTS_CROSS_ONLY").map(|v| v == "1").unwrap_or(false) {
                               // (agent_lowq_lane QUOT_CUTS_NONCROSS=a,b: K5 needs 3 chunks of <= K + 6 bits there)
                               std::env::var("QUOT_CUTS_NONCROSS").ok()
                                   .map(|v| v.split(',').filter_map(|x| x.trim().parse().ok()).collect())
                                   .unwrap_or(vec![qch()])
                           } else { chunk_cuts_wide(!zoff_on || no_sz7r) };
                           v.extend(cuts.into_iter().filter(|&x| x > 0 && x < kmax));
                           if compact675 { v=super::lowq675_routes::bounds(cp.col,kmax);v.pop(); }
                           if !compact675 && k == 0 && (36..=113).contains(&cp.col) {
                               v = vec![0];
                               v.extend([1, 3, 6, 11, 17].into_iter().filter(|&x| x < kmax));
                           }
                           if !compact675 && k == 0 && cp.col == 115 {
                               v = vec![0];
                               v.extend([5, 11, 17].into_iter().filter(|&x| x < kmax));
                           }
                           v.sort_unstable(); v.dedup();
                           v.push(kmax); v };
    assert!(bd.windows(2).all(|w| w[0] < w[1]), "chunk cuts must ascend");
    let nch = bd.len() - 1;
    let chunk = chunked() && nch > 1;
    let qch = if chunk { bd[1] } else { qch() };
    assert!(!chunk || bd.windows(2).all(|w| w[1] - w[0] <= k + 6 - usize::from(compact675)), "a chunk exceeds the K + 6 slots");
    let (sylo_c, syhi_c) = (cp.sy.0.max(1), cp.sy.1.min(nq));
    // decoder prefixes: sx[0..6) less the chunk slots, and the P zero
    let pre_c: Vec<QubitId> = {
        let longest = bd.windows(2).map(|w| w[1] - w[0]).max().unwrap_or(0).max(qch);
        let slots: Vec<QubitId> = (0..longest.max(kmax.saturating_sub(qch))).map(|s| qloc(s)).collect();
        let mut v: Vec<QubitId> = sx[..VB].iter().copied().filter(|x| !slots.contains(x)).collect();
        v.push(pzero);
        // lowq-size FD_LOOP_PRE: lane budget of the loops' sy decoders (shorter: dirty toggles, more T)
        if let Some(k) = std::env::var("FD_LOOP_PRE").ok().and_then(|x| x.parse::<usize>().ok()) { v.truncate(k); }
        v
    };
    // gate_t with v already in SZ (vg played: loops that neither rotate by sz nor read it)
    let gate_v = |b: &mut B, kk: usize, a: QubitId, t: QubitId, on: bool| {
        let f1 = b.tof;
        super::frogdrop_col::ge_cd(b, &v, (40 - kk) as isize, t, &gate_chain, &dirty);
        b.x(t);
        if on { b.and_c(a, t, ak); } else { b.and_u(a, t, ak); }
        b.x(t);
        super::frogdrop_col::ge_cd(b, &v, (40 - kk) as isize, t, &gate_chain, &dirty);
        super::f1_profile(if on { "midg.gate_v_on" } else { "midg.gate_v_off" }, f1, b.tof);
    };
    // gate_v with v formed before and returned after (no rotation by sz in between)
    let gate_x = |b: &mut B, kk: usize, a: QubitId, t: QubitId, on: bool| {
        if on {
            b.play(&vg, false);
            gate_v(b, kk, a, t, true);
        } else {
            gate_v(b, kk, a, t, false);
            b.play(&vg, true);
        }
    };
    // c ^= ak & [X >= 2^kk Y] (X < 2^(kk+1) Y: the carry out of the shot's relative position sy); `sub` (c |0> on
    // entry): also X -= 2^kk Y where it holds, one step of the restoring division
    let cmp_y = |b: &mut B, kk: usize, sub: bool, pre: &[QubitId]| {
        let span = (syhi_c + 1).min(n - kk);
        let tl: Vec<QubitId> = (0..span).map(|i| ring[n - 1 - kk - i]).collect();
        let mut s: Vec<QubitId> = q.iter().copied().take(span).collect();
        if s.len() < span { s.push(x128); }
        assert_eq!(s.len(), span);
        let rd = s.clone();
        let mut mid = |b: &mut B| {
            let lane = |vv: usize| if vv < rd.len() { Some(rd[vv]) } else { None };
            read_lane(b, &fd.sy, sylo_c, syhi_c, &lane, true, &[(ak, false)], c, pre, &[], &dirty);
        };
        let mut gate = |_b: &mut B, i: Option<usize>| if sub { i.map(|_| c) } else { None };
        ripple(b, &tl, &s, c0, true, &mut mid, &mut gate);
    };
    // The inverse of a restoring-division ripple consumes its saved bit in c,
    // restores the corresponding multiple of Y, and clears c. Recording does
    // not emit the forward gates; only the inverse is played into the circuit.
    let mul_back = |b: &mut B, kk: usize| {
        let round = rec(b, |b| cmp_y(b, kk, true, &pre_c));
        b.play(&round, true);
    };
    // V search uses D = ~V on the active region. The carry out of V + Y
    // is the complement of [D >= Y]; with no carry, the gated down pass
    // updates V to the accepted candidate. A saved bit goes to the existing
    // chunk slot; the slot's old value may be dirty on inactive shots.
    let cmp_v = |b: &mut B, kk: usize| {
        let span = (syhi_c + 1).min(n - kk);
        let tl: Vec<QubitId> = (0..span).map(|i| ring[n - 1 - kk - i]).collect();
        let mut s: Vec<QubitId> = q.iter().copied().take(span).collect();
        if s.len() < span { s.push(x128); }
        assert_eq!(s.len(), span);
        let rd = s.clone();
        // When sy + kk = 257 - sz, the high compare lane is the zero
        // headroom bit rather than a complemented V-region one. On a gate_v
        // shot this is exactly v = 39 - kk; use the carry *into* that lane.
        super::frogdrop_col::ge_cd(b, &v, (39 - kk) as isize, sx[0], &gate_chain, &dirty);
        let read_pre: Vec<QubitId> = pre_c.iter().copied().filter(|&x| x != sx[0]).collect();
        let mut mid = |b: &mut B| {
            let lane = |vv: usize| if vv < rd.len() { Some(rd[vv]) } else { None };
            read_lane(b, &fd.sy, sylo_c, syhi_c, &lane, true, &[(ak, false)], c, &read_pre, &[], &dirty);
            let prior = |vv: usize| if vv >= 1 && vv - 1 < rd.len() { Some(rd[vv - 1]) } else { None };
            read_lane(b, &fd.sy, sylo_c, syhi_c, &prior, false,
                      &[(ak, false), (sx[0], false)], c, &read_pre, &[], &dirty);
        };
        let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| c);
        ripple(b, &tl, &s, c0, false, &mut mid, &mut gate);
        super::frogdrop_col::ge_cd(b, &v, (39 - kk) as isize, sx[0], &gate_chain, &dirty);
    };
    // c <-> X-index sy + kk (the in-place lane) on the ak shots: a swap tree on sy's bits brings the shot's lane to
    // the range's first lane (any sy in [sylo, syhi]; an ak shot's sy is in range), one controlled swap, the tree back
    // (QUOT_INPLACE_DEC=1: the one-hot decoder)
    let tree_inplace = std::env::var_os("QUOT_INPLACE_DEC").is_none();
    let inplace_by = |b: &mut B, kk: usize, ctl: QubitId, pre: &[QubitId]| {
        let f1 = b.tof;
        let lane = |vv: usize| {
            let i = n as isize - 1 - vv as isize - kk as isize;
            if i >= 0 { Some(ring[i as usize]) } else { None }
        };
        if tree_inplace {
            let leaves: Vec<(usize, QubitId)> = (sylo_c..=syhi_c).filter_map(|v| lane(v).map(|l| (v, l))).collect();
            let mut swaps = vec![];
            let root = swap_tree(&fd.sy, &leaves, fd.sy.len(), &mut swaps);
            for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
            super::mid2::mc_swap(b, &[(ctl, false)], root, c, &[], &dirty);
            for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
        } else {
            super::mid2::dec_swap(b, &fd.sy, sylo_c, syhi_c, &lane, c, &[(ctl, false)], pre, &[], &dirty);
        }
        super::f1_profile("midg.inplace", f1, b.tof);
    };
    let inplace = |b: &mut B, kk: usize, pre: &[QubitId]| inplace_by(b, kk, ak, pre);
    // one park per chunk (slot s <-> cycle index s), recorded top chunk first
    let parks: Vec<Vec<Gate>> = if chunk {
        let mut v: Vec<Vec<Gate>> = vec![vec![]; nch];
        for i in (0..nch).rev() { v[i] = park_for(b, act, &q129a, &rqa, false, bd[i + 1] - bd[i], 0); }
        v
    } else { vec![] };
    // (lowq_cross) the in-place division of X = r + q_{>=lo} Y back to r for the bits >= lo (q_kk at X-index sy + kk,
    // on the act shots; v formed around it)
    let div_inplace = |b: &mut B, lo: usize| {
        b.play(&vg, false);
        for kk in (lo..kmax).rev() {
            gate_v(b, kk, act, sx[0], true);
            cmp_y(b, kk, true, &pre_c);
            inplace(b, kk, &pre_c);
            gate_v(b, kk, act, sx[0], false);
        }
        b.play(&vg, true);
    };
    let xl: Vec<QubitId> = (0..mt).map(|m| ring[n - 1 - m]).collect();
    // agent_lowq_lane: V-form play marks for the lane census (FD_MARK only): 33x1 starts a play of kind x, 3300 ends it
    let vmark = |b: &B, code: usize| {
        if std::env::var_os("FD_MARK").is_none() { return; }
        if code != 3300 {
            super::frogdrop_col::VINFO.with(|v| v.borrow_mut().push(super::frogdrop_col::VInfo {
                at: b.ops.len(), code, col: cp.col, zlo, zoff: zoff_on, sgw: sgw_on, kmax, sy: fd.sy.clone(),
                sz: sc.sz.clone(), sx: sx.clone(), q: q.clone(), r: s1.r.clone(), ring: ring.clone(), act, x128, ph,
                sw: sc.sw, pzero, c0 }));
        }
        super::frogdrop_col::mark(b, code);
    };
    // agent_lowq_lane LANE_ACTR: act off before / on after each V-form play (HR: !ph & !sw; HT: ht_act with ph in its
    // column-time form, `flipped` = ph is inverted around the play; the dq compare's carry is c0, x128 may be parked)
    let act_hr = |b: &mut B| if actr { mc_xor(b, &hr_lits, act, &[], &dirty); };
    let act_ht = |b: &mut B, flipped: bool| if actr {
        if flipped { b.x(ph); }
        if zoff_on && cp.dq { b.play(&zshift, false); }
        ht_act(b, fd, cp, sc, act, &sx[..1], c0, &dirty);
        if zoff_on && cp.dq { b.play(&zshift, true); }
        if flipped { b.x(ph); }
    };
    b.play(&zshift, true);
    let b8b: Option<b8b_cross::Cross<'_>> = b8b_cross.then(|| b8b_cross::Cross {
        fd, cp, sc, pl, vform: &vform, parked: &b8b_forms, parked_ht: &b8b_forms_ht, vg: &vg,
        zshift: &zshift, zoff_on, kmax, mt,
    });
    if cp.hr { if let Some(cross) = &b8b { cross.hr_pre(b); } }
    let fixed_park: Vec<QubitId> = if fixed_hr || fixed_ht {
        assert_eq!(kmax, 25);
        assert!(cp.sy.1 + kmax < 117);
        (0..kmax).map(|kk| q[cp.sy.1 + 1 + kk]).collect()
    } else { vec![] };
    if fixed_hr {
        mc_xor(b, &hr_lits, act, &[], &dirty);
        let f1 = b.tof;
        vmark(b, 3331);
        act_hr(b);
        b.play(&vform, false);
        act_hr(b);
        vmark(b, 3300);
        super::f1_profile("midg.vform", f1, b.tof);
        b.play(&vg, false);
        for kk in (0..kmax).rev() {
            gate_v(b, kk, act, sx[0], true);
            cmp_v(b, kk);
            // On done shots the fixed Q lane may hold a counter bit.
            super::mid2::mc_swap(b, &[(ak, false)], c, fixed_park[kk], &[], &dirty);
            gate_v(b, kk, act, sx[0], false);
        }
        b.play(&vg, true);
        let f1 = b.tof;
        vmark(b, 3341);
        act_hr(b);
        b.play(&vform_pk, true);
        act_hr(b);
        vmark(b, 3300);
        super::f1_profile("midg.vform", f1, b.tof);
        mc_xor(b, &hr_lits, act, &[], &dirty);
    }
    if cp.hr && chunk && !fixed_hr && !b8b_cross {
        // tt: the D^-1 runs on X - 1
        let dec1 = if cp.tt { Some(rec(b, |b| super::modp_frogdrop::inc_dirty(b, &xl, &dirty, c0))) } else { None };
        mc_xor(b, &hr_lits, act, &[], &dirty);
        for i in (0..nch).rev() {
            let (lo, hi) = (bd[i], bd[i + 1]);
            if i + 1 < nch {
                // D^-1 of C_{i+1} = [hi, h2) (no payload): X = t_{j-1} + q_{>=h2} Y -> t_{j-1} + q_{>=hi} Y, its slots
                // cleared. (lowq_cross) For h2 < kmax the chunks above are divided out in place around it: X_low =
                // t_{j-1} + q_[hi, kk] Y < 2^h2 Y stays below their lanes.
                let h2 = bd[i + 2];
                if let Some(d) = &dec1 { b.play(d, true); }
                let up = if h2 < kmax { Some(rec(b, |b| div_inplace(b, h2))) } else { None };
                if let Some(u) = &up { b.play(u, false); }
                for kk in hi..h2 {
                    fetch(b, kk - hi, &[(act, false)]);
                    add(b, kk, c, false);
                    gate_x(b, kk, act, sx[0], true);
                    cmp_y(b, kk, false, &pre_c);
                    gate_x(b, kk, act, sx[0], false);
                }
                if let Some(u) = &up { b.play(u, true); }
                if let Some(d) = &dec1 { b.play(d, false); }
            }
            let f1 = b.tof;
            vmark(b, 3311);
            act_hr(b);
            b.play(&vform, false);
            act_hr(b);
            vmark(b, 3300);
            super::f1_profile("midg.vform", f1, b.tof);
            if std::env::var_os("B7A_VSEARCH").is_some() {
                b.play(&vg, false);
                for kb in (lo..hi).rev() {
                    gate_v(b, kb, act, sx[0], true);
                    cmp_v(b, kb);
                    if kb == lo {
                        b.play(&vg, true);
                        let r = rotz(b, &[kb - lo]);
                        b.play(&r, false);
                        b.cx(c, qloc(kb - lo));
                        mc_xor(b, &[(ak, false), (qloc(kb - lo), false)], c, &[], &dirty);
                        b.play(&r, true);
                        b.play(&vg, false);
                    } else {
                        b.cx(c, qloc(kb - lo));
                        mc_xor(b, &[(ak, false), (qloc(kb - lo), false)], c, &[], &dirty);
                    }
                    gate_v(b, kb, act, sx[0], false);
                }
                b.play(&vg, true);
            } else {
                for kb in (lo..hi).rev() {
                    gate_on(b, kb, act);
                    add(b, kb, ak, false);
                    decide(b, kb - lo, false);
                    add(b, kb, rv, true);
                    decide(b, kb - lo, true);
                    gate_off(b, kb, act);
                }
            }
            if std::env::var_os("B7A_VSEARCH_DEBUG").is_some() { super::frogdrop_col::mark(b, 2000 + i); }
            for kb in lo..hi {
                fetch(b, kb - lo, &[(act, false)]);
                add(b, kb, c, true);
                fetch(b, kb - lo, &[(act, false)]);
            }
            let pk = &parks[i];
            b.play(&sy7_normal, false);
            b.play(pk, false);
            #[cfg(test)] let d4b_start = b.ops.len();
            let f1 = b.tof;
            super::frogdrop_col::mark(b, 3101);
            vmark(b, 3321);
            act_hr(b);
            b.play(if compact675 { &lowq675_forms[i] } else { &vform_pk }, true);
            act_hr(b);
            vmark(b, 3300);
            super::frogdrop_col::mark(b, 3102);
            super::f1_profile("midg.vform", f1, b.tof);
            #[cfg(test)] d4b_window(d4b_start, b.ops.len(), if lo == 0 { 3 } else { 0 }, act);
            b.play(pk, false);
            b.play(&sy7_normal, false);
        }
        mc_xor(b, &hr_lits, act, &[], &dirty);
    }
    // ---------------- HR: binary search in the V form, q's bits parked in the ring headroom
    if cp.hr && !chunk && !fixed_hr {
        mc_xor(b, &hr_lits, act, &[], &dirty);
        let f1 = b.tof;
        vmark(b, 3331);
        act_hr(b);
        b.play(&vform, false);
        act_hr(b);
        vmark(b, 3300);
        super::f1_profile("midg.vform", f1, b.tof);
        for kb in (0..kmax).rev() {
            gate_on(b, kb, act);
            add(b, kb, ak, false);
            decide(b, kb, false);
            add(b, kb, rv, true);
            decide(b, kb, true);
            gate_off(b, kb, act);
        }
        // V -= qY: V = t_{j-1} + T - G
        for kb in 0..kmax {
            fetch(b, kb, &[(act, false)]);
            add(b, kb, c, true);
            fetch(b, kb, &[(act, false)]);
        }
        // leave the V form with q above Y, then q back to the headroom
        b.play(&sy7_normal, false);
        b.play(&park, false);
        #[cfg(test)] let d4b_start = b.ops.len();
        let f1 = b.tof;
        vmark(b, 3341);
        act_hr(b);
        b.play(&vform_pk, true);
        act_hr(b);
        vmark(b, 3300);
        super::f1_profile("midg.vform", f1, b.tof);
        #[cfg(test)] d4b_window(d4b_start, b.ops.len(), 0, act);
        b.play(&park, false);
        b.play(&sy7_normal, false);
        mc_xor(b, &hr_lits, act, &[], &dirty);
    }
    if !stage(b) { return; } // 3
    if cp.hr { if let Some(cross) = &b8b { cross.hr_stage4(b); } }
    if fixed_hr {
        let dec1 = if cp.tt { Some(rec(b, |b| super::modp_frogdrop::inc_dirty(b, &xl, &dirty, c0))) } else { None };
        if let Some(d) = &dec1 { b.play(d, true); }
        let wtop = 259 - (L0P + 1);
        let pads = vec![x128, pzero];
        let nopad = std::env::var("FD_DINV_NOPAD").map(|v| v == "1").unwrap_or(false);
        let slen = if nopad { wtop.min(nq) } else { wtop.min(nq + pads.len()) };
        let src = if pl.is_some() { if nopad { fd.q[..slen].to_vec() } else { super::payload::pad(&fd.q, &pads, slen) } }
                  else { vec![] };
        mc_xor(b, &hr_lits, act, &[], &dirty);
        // X = t_{j+1}; regenerate each q bit in X's free high lane and
        // erase the fixed Q park before the payload uses Q as its source.
        b.play(&vg, false);
        for kk in (0..kmax).rev() {
            gate_v(b, kk, act, sx[0], true);
            cmp_y(b, kk, true, &pre_c);
            mc_xor(b, &[(ak, false), (c, false)], fixed_park[kk], &[], &dirty);
            inplace(b, kk, &pre_c);
            gate_v(b, kk, act, sx[0], false);
        }
        b.play(&vg, true);
        b.play(&vg, false);
        for kk in 0..kmax {
            gate_v(b, kk, act, sx[0], true);
            inplace(b, kk, &pre_c);
            if let Some(pl) = pl {
                let t: Vec<QubitId> = (kk..wtop).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                let sl = (wtop - kk).min(slen);
                super::payload::trans_one(b, &t, &src[..sl], kk, false, vec![(c, false)], None, sx[0], c0, &[],
                                          &pl.dirty);
                super::frogdrop_col::mark(b, 1000 + kk);
            }
            mul_back(b, kk);
            gate_v(b, kk, act, sx[0], false);
        }
        b.play(&vg, true);
        mc_xor(b, &hr_lits, act, &[], &dirty);
        if let Some(d) = &dec1 { b.play(d, false); }
    }
    if cp.hr && chunk && !fixed_hr && !b8b_cross {
        let dec1 = if cp.tt { Some(rec(b, |b| super::modp_frogdrop::inc_dirty(b, &xl, &dirty, c0))) } else { None };
        if let Some(d) = &dec1 { b.play(d, true); }
        let wtop = 259 - if cp.dl { cp.dlr.min(L0P + 1) } else { L0P + 1 };
        let pads: Vec<QubitId> = if cp.dl { vec![x128, pzero, sx[1], sx[6], sc.sw, ph] }
                                 else { vec![x128, pzero] };
        // FD_DINV_NOPAD: the transition's source is Q alone (trans_one adds the carry out of Q's top lane into the
        // rest of the target by an increment), so the zero pads are not held
        let nopad = std::env::var("FD_DINV_NOPAD").map(|v| v == "1").unwrap_or(false);
        let slen = if nopad { wtop.min(nq) } else { wtop.min(nq + pads.len()) };
        let src = if pl.is_some() { if nopad { fd.q[..slen].to_vec() } else { super::payload::pad(&fd.q, &pads, slen) } }
                  else { vec![] };
        mc_xor(b, &hr_lits, act, &[], &dirty);
        // in-place division for the bits >= QCH: X = t_{j-1} + q_{>=QCH} Y -> t_{j-1}, q_kk at X-index sy + kk
        b.play(&vg, false);
        for kk in (qch..kmax).rev() {
            gate_v(b, kk, act, sx[0], true);
            cmp_y(b, kk, true, &pre_c);
            inplace(b, kk, &pre_c);
            gate_v(b, kk, act, sx[0], false);
        }
        b.play(&vg, true);
        // D^-1 of all bits LSB first, the payload fused (C0 from its slots, C1 from X's lanes): X = t_{j+1}
        for kk in 0..kmax {
            // v stays in SZ from bit QCH on (no rotation by sz there)
            if kk == qch { b.play(&vg, false); }
            if kk < qch {
                fetch(b, kk, &[(act, false)]);
            } else {
                gate_v(b, kk, act, sx[0], true);
                inplace(b, kk, &pre_c);
                // sx[6] (ak) is a payload pad in dl columns
                if cp.dl { gate_v(b, kk, act, sx[0], false); }
            }
            if let Some(pl) = pl {
                let t: Vec<QubitId> = (kk..wtop).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                let sl = (wtop - kk).min(slen);
                super::payload::trans_one(b, &t, &src[..sl], kk, false, vec![(c, false)], None, sx[0], c0, &[],
                                          &pl.dirty);
                super::frogdrop_col::mark(b, 1000 + kk);
            }
            if kk < qch { add(b, kk, c, false); }
            if kk < qch {
                gate_x(b, kk, act, sx[0], true);
                cmp_y(b, kk, false, &pre_c);
                gate_x(b, kk, act, sx[0], false);
            } else {
                if cp.dl { gate_v(b, kk, act, sx[0], true); }
                mul_back(b, kk);
                gate_v(b, kk, act, sx[0], false);
            }
        }
        if kmax > qch { b.play(&vg, true); }
        mc_xor(b, &hr_lits, act, &[], &dirty);
        if let Some(d) = &dec1 { b.play(d, false); }
    }
    if cp.hr && !chunk {
        // D^-1: X = t_{j-1} < t_j grows to t_{j+1}, consuming q's bits LSB first (tt: run on X - 1)
        let dec1 = if cp.tt { Some(rec(b, |b| super::modp_frogdrop::inc_dirty(b, &xl, &dirty, c0))) } else { None };
        if let Some(d) = &dec1 { b.play(d, true); }
        let (sylo, syhi) = (cp.sy.0.max(1), cp.sy.1.min(nq));
        // the post region's positions [0, 259 - bl(r_j)): a delayed shot's r_j < 2^l0 widens it to 259 - dlr; Q's
        // pad: lanes zero on the written (HR stepping) shots, the carry past them by trans_one's increment
        let wtop = 259 - if cp.dl { cp.dlr.min(L0P + 1) } else { L0P + 1 };
        let pads: Vec<QubitId> = if cp.dl { vec![x128, pzero, sx[1], sx[6], sc.sw, ph] }
                                 else { vec![x128, pzero] };
        // FD_DINV_NOPAD: the transition's source is Q alone (trans_one adds the carry out of Q's top lane into the
        // rest of the target by an increment), so the zero pads are not held
        let nopad = std::env::var("FD_DINV_NOPAD").map(|v| v == "1").unwrap_or(false);
        let slen = if nopad { wtop.min(nq) } else { wtop.min(nq + pads.len()) };
        let src = if pl.is_some() { if nopad { fd.q[..slen].to_vec() } else { super::payload::pad(&fd.q, &pads, slen) } }
                  else { vec![] };
        mc_xor(b, &hr_lits, act, &[], &dirty);
        for kk in 0..kmax {
            fetch(b, kk, &[(act, false)]);
            if std::env::var_os("D3_TRACE_PHASE").is_some() && kk + 1 == kmax { super::frogdrop_col::mark(b, 1400); }
            if let Some(pl) = pl {
                let t: Vec<QubitId> = (kk..wtop).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                let sl = (wtop - kk).min(slen);
                super::payload::trans_one(b, &t, &src[..sl], kk, false, vec![(c, false)], None, sx[0], c0, &[],
                                          &pl.dirty);
                super::frogdrop_col::mark(b, 1000 + kk);
            }
            add(b, kk, c, false);
            if std::env::var_os("D3_TRACE_PHASE").is_some() && kk + 1 == kmax { super::frogdrop_col::mark(b, 1402); }
            if precision24 {
                ge_k(b, kk, sx[0]);
                b.x(sx[0]);
                b.and_c(act, sx[0], ak);
                b.x(sx[0]);
                ge_k(b, kk, sx[0]);
            }
            // c ^= act & [X >= 2^kk Y]: carry out of the shot's top relative position sy (X < 2^(kk+1) Y)
            let span = (syhi + 1).min(n - kk);
            let tl: Vec<QubitId> = (0..span).map(|i| ring[n - 1 - kk - i]).collect();
            let mut s: Vec<QubitId> = q.iter().copied().take(span).collect();
            if s.len() < span { s.push(x128); }
            assert_eq!(s.len(), span);
            let rd = s.clone();
            let mut mid = |b: &mut B| {
                let lane = |vv: usize| if vv < rd.len() { Some(rd[vv]) } else { None };
                let mut read_pre = if precision24 { vec![sx[0], pzero] }
                               else { vec![sx[0], sx[1], sx[2], sx[6], pzero] };
                if let Some(k) = std::env::var("FD_DINV_PRE").ok().and_then(|v| v.parse::<usize>().ok()) {
                    read_pre.truncate(k);
                }
                if std::env::var_os("D3_TRACE_PHASE").is_some() && kk + 1 == kmax { super::frogdrop_col::mark(b, 1404); }
                read_lane(b, &fd.sy, sylo, syhi, &lane, true, &[(if precision24 { ak } else { act }, false)], c, &read_pre, &[], &dirty);
                if std::env::var_os("D3_TRACE_PHASE").is_some() && kk + 1 == kmax { super::frogdrop_col::mark(b, 1405); }
            };
            let mut gate = |_b: &mut B, _i: Option<usize>| None;
            ripple(b, &tl, &s, c0, true, &mut mid, &mut gate);
            if precision24 {
                ge_k(b, kk, sx[0]);
                b.x(sx[0]);
                b.and_u(act, sx[0], ak);
                b.x(sx[0]);
                ge_k(b, kk, sx[0]);
            }
            if std::env::var_os("D3_TRACE_PHASE").is_some() && kk + 1 == kmax { super::frogdrop_col::mark(b, 1403); }
        }
        mc_xor(b, &hr_lits, act, &[], &dirty);
        if let Some(d) = &dec1 { b.play(d, false); }
    }
    if !stage(b) { return; } // 4
    #[cfg(test)]
    let b6_capture_stage5 = std::env::var_os("B6_STAGE5_INSTANT").is_some() && cp.col == 68;
    #[cfg(test)]
    if b6_capture_stage5 { b.begin(); }
    // ---------------- HT: in-place restoring division (mid2): q_k at X-index sy + k, X = r_{j+1}, the payload add
    // U += q |t_j| fused per bit (FD_MIDG_OLD5=1: the headroom division and the parked payload add)
    // agent_lowq_quot: QUOT_GIP5=1 runs the in-place division (with lowq_cross's repair)
    let old5 = (!G_IP5 && std::env::var_os("QUOT_GIP5").is_none()) || std::env::var("FD_MIDG_OLD5").is_ok();
    // agent_lowq_quot IP5-split (chunked sessions): the in-place division without the fused payload. The fused
    // payload's masked source reaches X-index K + sy, so an in-place bit kb' >= K would be read as |t_j| (q >= 2^K):
    // the bits >= K move to slots QCH.. and park in the Q cycle at kb - K for the payload, the bits < K stay in place.
    // Hand-off: bits < K in place, bits >= K in slots QCH + kb - K. QUOT_IP5_FUSED=1: ht_div_inplace.
    let split5 = chunk && !old5 && std::env::var_os("QUOT_IP5_FUSED").is_none();
    let res_s: usize = std::env::var("QUOT_RES_S").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    if cp.ht && !old5 {
        // (lowq_cross repair, copied for the chunked hand-off test: the crossing form choice is ported: sw marks only
        // the switching shots in dl columns, and act excludes a delayed shot's no-step column)
        // in place on the 13 lanes (the stepping flag on sw; act idle) and sx; s = sz + sy is formed as s - 2 on sz
        // (every shot's s in [228, 257]); the division's Q pad past lane 127 is sv (clean outside the size gates)
        let actl = sc.sw;
        let ds = super::payload::DigScr { e: vec![], sa: sc.sz.clone(), sb: fd.sy.clone(), sv: x128, fa: sx[0], g: act,
                                          c0, tmp: vec![pzero, sx[1]], pre1: vec![], pre2: vec![], zeros: vec![],
                                          dirty: dirty.clone(), smin: 2 };
        let sw_toggle = |b: &mut B| {
            if !cp.sw { return; }
            if zoff_on { b.play(&zshift, false); }
            super::frogdrop_col::ge_cd(b, &sc.sz, cp.l0 as isize + 1, ds.fa, &sx[1..1 + mid_chain().min(7)], &dirty);
            if cp.dl {
                let gt = super::arith::up_m(b, &fd.sy, &sc.sz, x128, true);
                b.play(&gt, false);
                mc_xor(b, &[(ds.fa, true), (ph, true), (sc.sz[sc.sz.len() - 1], true)], sc.sw, &[], &dirty);
                b.play(&gt, true);
            } else {
                mc_xor(b, &[(ds.fa, true), (ph, true)], sc.sw, &[], &dirty);
            }
            super::frogdrop_col::ge_cd(b, &sc.sz, cp.l0 as isize + 1, ds.fa, &sx[1..1 + mid_chain().min(7)], &dirty);
            if zoff_on { b.play(&zshift, true); }
        };
        let set_act = |b: &mut B| { if zoff_on && cp.dq { b.play(&zshift, false); } ht_act(b, fd, cp, sc, actl, &sx[..2], x128, &dirty); if zoff_on && cp.dq { b.play(&zshift, true); } };
        sw_toggle(b);
        set_act(b);
        if split5 {
            let kin = k.min(kmax);
            // the division in place, every bit (no payload): X = r_{j-1} -> r_{j+1}, q_kk at X-index sy + kk
            b.play(&vg, false);
            for kk in (0..kmax).rev() {
                gate_v(b, kk, actl, sx[0], true);
                cmp_y(b, kk, true, &pre_c);
                inplace(b, kk, &pre_c);
                gate_v(b, kk, actl, sx[0], false);
            }
            b.play(&vg, true);
            if let Some(pl) = pl {
                // the payload: the bits >= K parked above Y (the headroom clean), control per bit on c
                // (lowq_cross direct park, replacing the staged two-batch park, whose batch-B gates ran on the cycle
                // lanes pzero / x128 while batch A was parked there): the cycle is rotated down by sy once; each bit
                // kb >= K goes from its in-place lane through c straight to cycle index kb - K and back after the
                // payload, so no staging slots at any K; stage 6 reads every bit in place
                // (agent_lowq_lane: a 5th lane sx[3] for QUOT_RES_S=5 at K5; idle in the split stage 5)
                let s5gap=rec(b,|b|{
                    super::arith::ttk_add(b,&fd.sy,&sc.sz[..8],None,None);
                    for &q in &sc.sz[..8]{b.x(q);}
                    super::modp_frogdrop::inc_dirty_free(b,&sc.sz[1..8],&dirty);
                });
                if zoff_on {b.play(&zshift,false);}
                b.play(&s5gap,false);
                let (q129s,rqs)=mk_cycle(b,&[pzero,ph,sx[1],sx[2],sx[3],sx[4],sx[5],sx[6],sc.sz[5],sc.sz[6],sc.sz[7]],cp.ht,Some(res_s));
                let qlen = q129s.len();
                // agent_lowq_lane LANE_S5_YTOP: after the rotation down by sy, the cycle's last lane holds Y's top
                // (cycle index sy - 1, 1 on the actl shots): flipped to 0 it takes bit kin, the bit kin + i the lane
                // i - 1: one more slot (wrap at sy + idx >= qlen + 1) without a lane. The rotation then cares for
                // that last position too (mk_cycle's cares only for 0..kmax).
                let s5y = std::env::var("LANE_S5_YTOP").map(|v| v == "1").unwrap_or(false);
                let rqs = if !s5y { rqs } else {
                    assert!(!q129s.contains(&fd.sy[7]));
                    let care: std::collections::BTreeSet<usize> = (0..kmax).chain([qlen - 1]).collect();
                    rec(b, |b| rot_by_range_care(b, &q129s, &fd.sy, cp.sy.0.min(128), cp.sy.1.min(128), true, &dirty,
                                                 &care))
                };
                let slot = |idx: usize| if s5y { q129s[(idx + qlen - 1) % qlen] } else { q129s[idx] };
                let wlen = if s5y { qlen + 1 } else { qlen };
                let (sylo5, syhi5) = (cp.sy.0.max(1), cp.sy.1.min(L0P));
                let pre5:[QubitId;0]=[];
                // the direct park's gate compares on [c0, sx4, sx5] (clean here: no slots in this stage), never on a
                // cycle lane; a bit that would wrap onto Y stays in c (a counted failure)
                let chain5 = [c0];
                assert!(!chain5.iter().any(|x| q129s.contains(x) || v.contains(x) || *x == ak || *x == c || *x == wf));
                assert!(tree_inplace, "the direct park's in-place swaps must not use pre_c (it holds pzero)");
                let gate5=|b:&mut B,kk:usize,on:bool|{
                    super::frogdrop_col::ge_cd(b,&sc.sz[..5],kk as isize,sx[0],&chain5,&dirty);
                    if on {b.and_c(actl,sx[0],act);}else{b.and_u(actl,sx[0],act);}
                    super::frogdrop_col::ge_cd(b,&sc.sz[..5],kk as isize,sx[0],&chain5,&dirty);
                };
                let dpark = |b: &mut B, kb: usize, fwd: bool| {
                    let idx = kb - kin;
                    let wrap = cp.sy.1.min(128) + idx >= wlen;
                    gate5(b, kb, true);
                    if fwd { inplace_by(b,kb,act,&[]); }
                    if wrap { wrap_flag(b, idx, wlen, false); }
                    let ct: Vec<(QubitId, bool)> = if wrap { vec![(actl, false), (wf, true)] } else { vec![(actl, false)] };
                    super::mid2::mc_swap(b, &ct, c, slot(idx), &[], &dirty);
                    if wrap { wrap_flag(b, idx, wlen, false); }
                    if !fwd { inplace_by(b,kb,act,&[]); }
                    gate5(b, kb, false);
                };
                b.x(ph);
                b.play(&rqs, false);
                if s5y { b.x(q129s[qlen - 1]); }
                for kb in kin..kmax { dpark(b, kb, true); }
                for kb in 0..kmax.min(NP) {
                    let ctl = |b: &mut B| {
                        if kb < kin {
                            inplace_by(b, kb, actl, &pre_c);
                        } else {
                            let idx = kb - kin;
                            let wrap = cp.sy.1.min(128) + idx >= wlen;
                            let mut ct = vec![(actl, false), (slot(idx), false)];
                            if wrap { wrap_flag(b, idx, wlen, false); ct.push((wf, true)); }
                            mc_xor(b, &ct, c, &[], &dirty);
                            if wrap { wrap_flag(b, idx, wlen, false); }
                        }
                    };
                    ctl(b);
                    // N258 has one less source guard. For k>0, choose
                    // 2^sh<=k, making every written source index <N-sy.
                    let sh = if compact675 && kb>0 { ((usize::BITS-1-kb.leading_zeros()) as usize).min(4) }
                        else { ((usize::BITS - 1 - (kb + 1).leading_zeros()) as usize).min(4) };
                    let tt: Vec<QubitId> = (kb..NP).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                    // N258 keeps the full NP259 payload. Its one high zero
                    // source is virtual: wf is returned before this addition
                    // and before the following park control, outside pre5.
                    let source=super::payload::pad(&fd.ring,&[wf],NP-kb);
                    trans_masked_q(b, &tt, &source, kb, c, &fd.sy, sh, sylo5, syhi5, act, c0, &pre5,
                                   &[], &pl.dirty);
                    if compact675 && kb==0 {
                        // At k=0 the exact mask admits precisely one extra
                        // source bit: ring[N-sy]. It contributes only to the
                        // most significant written target p[sy], modulo the
                        // post-region width. XOR removes that term exactly;
                        // all carry cells and every original target stay.
                        let mut boundary=super::mask::Dec::new(&fd.sy,&pre5);
                        for size in sylo5..=syhi5 {
                            let mut ct=boundary.ctrls(b,size);
                            ct.extend([(c,false),(fd.ring[n-size],false)]);
                            let dirt:Vec<_>=pl.dirty.iter().copied().filter(|q|!ct.iter().any(|(x,_)|x==q)).collect();
                            mc_xor(b,&ct,pl.p[size],&[c0,act],&dirt);
                        }
                        boundary.clear(b);
                    }
                    ctl(b);
                }
                for kb in (kin..kmax).rev() { dpark(b, kb, false); }
                if s5y { b.x(q129s[qlen - 1]); }
                b.play(&rqs, true);
                b.x(ph);
                b.play(&s5gap,false);
                if zoff_on {b.play(&zshift,true);}
            }
        } else {
            // c, q's top bit, then the sy decoder's prefixes
            let l5: Vec<QubitId> = sx[2..].to_vec();
            if zoff_on { b.play(&zshift, false); }
            super::mid2::ht_div_inplace(b, fd, cp, actl, &ds, l5[0], l5[1], &l5[2..], &[], &[], pl, &dirty);
            if zoff_on { b.play(&zshift, true); }
        }
        set_act(b);
        sw_toggle(b);
    }
    // ---------------- HT: restoring division (q's bits to the headroom), X = r_{j+1}
    if cp.ht && old5 {
        let actl = sc.sw;
        // dl columns: sw marks the switching shots only (& [sz <= sy], the in-place compare on x128)
        let sw_toggle = |b: &mut B| {
            if !cp.sw { return; }
            if zoff_on { b.play(&zshift, false); }
            let switch_pre: Vec<QubitId> = sx[1..].iter().copied().filter(|q| !sx[1..=5].contains(q)).collect();
            super::frogdrop_col::ge_const_compact(b, &sc.sz, cp.l0 as isize + 1, sx[0], &switch_pre, &dirty);
            if cp.dl {
                let gt = super::arith::up_m(b, &fd.sy, &sc.sz, x128, true);
                b.play(&gt, false);
                mc_xor(b, &[(sx[0], true), (ph, true), (sc.sz[sc.sz.len() - 1], true)], sc.sw, &[], &dirty);
                b.play(&gt, true);
            } else {
                mc_xor(b, &[(sx[0], true), (ph, true)], sc.sw, &[], &dirty);
            }
            super::frogdrop_col::ge_const_compact(b, &sc.sz, cp.l0 as isize + 1, sx[0], &switch_pre, &dirty);
            if zoff_on { b.play(&zshift, true); }
        };
        let set_act = |b: &mut B| { if zoff_on && cp.dq { b.play(&zshift, false); } ht_act(b, fd, cp, sc, actl, &sx[..1], x128, &dirty); if zoff_on && cp.dq { b.play(&zshift, true); } };
        sw_toggle(b);
        set_act(b);
        let syhi = cp.sy.1.min(L0P);
        for kb in (0..kmax).rev() {
            gate_on(b, kb, actl);
            // X -= 2^kb Y; negative iff bit 257 - sz is set (X < 2^(257 - sz), 2^kb Y < 2^(257 - sz))
            add(b, kb, ak, true);
            decide(b, kb, false);
            add(b, kb, rv, false);
            decide(b, kb, true);
            gate_off(b, kb, actl);
        }
        if let Some(pl) = pl {
            // the payload transition reads the ring below its top (the headroom must be clean): q above Y, then
            // Q down by sy puts bit kb on lane kb
            let park5 = park_for(b, actl, &q129b, &rqb, precision24, kmax, 0);
            let qlen = q129b.len();
            let pre19 = if precision24 {
                Some(preposition_qk(b, &q129b, &fd.sy, sx[1], k + 1, actl,
                                     (cp.sy.0.max(1), cp.sy.1.min(128)), &dirty))
            } else { None };
            super::frogdrop_col::mark(b, 1501);
            b.x(ph);
            if let Some(p) = &pre19 { b.play(p, false); }
            super::frogdrop_col::mark(b, 1502);
            b.play(&park5, false);
            super::frogdrop_col::mark(b, 1503);
            #[cfg(test)] let d4b_start = b.ops.len();
            b.play(&rqb, false);
            for kb in 0..kmax.min(NP) {
                let t: Vec<QubitId> = (kb..NP).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                // a wrapped index holds Y, not bit kb (left in the headroom): wf = [sy >= len - kb] masks it
                let wrap = cp.sy.1.min(128) + kb >= qlen;
                let mut base = vec![(q129b[kb], false), (actl, false)];
                if wrap {
                    wrap_flag(b, kb, qlen, false);
                    base.push((wf, true));
                }
                super::payload::trans_one_guard(b, &t, &fd.ring[..NP - kb], kb, false, base,
                                                Some((&fd.sy[4..], syhi >> 4)), sx[2], sx[3], &[], &pl.dirty,
                                                (n - 16) as isize);
                if wrap { wrap_flag(b, kb, qlen, false); }
            }
            b.play(&rqb, true);
            #[cfg(test)] d4b_window(d4b_start, b.ops.len(), 1, actl);
            b.play(&park5, false);
            super::frogdrop_col::mark(b, 1504);
            if let Some(p) = &pre19 { b.play(p, false); }
            b.x(ph);
            super::frogdrop_col::mark(b, 1505);
        }
        set_act(b);
        sw_toggle(b);
    }
    #[cfg(test)]
    if b6_capture_stage5 {
        let gate = b.end();
        B6_STAGE5_GATE.with(|v| *v.borrow_mut() = gate.clone());
        b.play(&gate, false);
    }
    if !stage(b) { return; } // 5
    if cp.ht { if let Some(cross) = &b8b { cross.ht_stage6(b); } }
    if fixed_ht {
        let set_act = |b: &mut B| { if zoff_on && cp.dq { b.play(&zshift, false); } ht_act(b, fd, cp, sc, act, &sx[..1], x128, &dirty); if zoff_on && cp.dq { b.play(&zshift, true); } };
        // The fixed park occupies Q above the public Y span. The ordinary
        // loan adder treats those zero Q lanes as a carry bank, so use its
        // exact short-source/tail form while the park is live.
        let parked_source: Vec<QubitId> = q[..syhi_c].iter().copied()
            .chain(fixed_ht_bank.iter().copied()).collect();
        let add_parked = |b: &mut B, kb: usize, ctl: QubitId, sub: bool| {
            super::frogdrop_col::ring_cadd2_loan(b, &ring, &parked_source, kb, mt - kb, ctl, sub,
                                                 &sc.zeros, c0, x128, &dirty, syhi_c,
                                                 parked_source.len(), x128);
        };
        set_act(b);
        // Stage 5 left q in X's free high lanes. Multiply it back exactly,
        // copying each bit to the fixed Q park before the parked V enter.
        b.play(&vg, false);
        for kk in 0..kmax {
            gate_v(b, kk, act, sx[0], true);
            inplace(b, kk, &pre_c);
            mc_xor(b, &[(ak, false), (c, false)], fixed_park[kk], &[], &dirty);
            mul_back(b, kk);
            gate_v(b, kk, act, sx[0], false);
        }
        b.play(&vg, true);
        b.x(ph);
        b.play(&sy7_normal, false);
        let f1 = b.tof;
        vmark(b, 3371);
        act_ht(b, true);
        b.play(&vform_pk, false);
        act_ht(b, true);
        vmark(b, 3300);
        super::f1_profile("midg.vform", f1, b.tof);
        b.play(&sy7_normal, false);
        b.x(ph);
        // Today's bottom-up reverse search remains exact on g_ht_ok failures.
        for kb in 0..kmax {
            gate_on(b, kb, act);
            super::mid2::mc_swap(b, &[(ak, false)], c, fixed_park[kb], &[], &dirty);
            b.cx(c, ak);
            add_parked(b, kb, ak, false);
            b.cx(c, ak);
            let r = rotz(b, &[window_base]);
            b.play(&r, false);
            mc_xor(b, &[(ak, false), (ring[window_base], true)], c, &[], &dirty);
            b.play(&r, true);
            add_parked(b, kb, ak, true);
            gate_off(b, kb, act);
        }
        let f1 = b.tof;
        if ph_r { b.x(ph); }
        vmark(b, 3381);
        act_ht(b, ph_r);
        b.play(&vform, true);
        act_ht(b, ph_r);
        vmark(b, 3300);
        if ph_r { b.x(ph); }
        super::f1_profile("midg.vform", f1, b.tof);
        set_act(b);
    }
    if cp.ht && chunk && !fixed_ht && !b8b_cross {
        let set_act = |b: &mut B| { if zoff_on && cp.dq { b.play(&zshift, false); } ht_act(b, fd, cp, sc, act, &sx[..1], x128, &dirty); if zoff_on && cp.dq { b.play(&zshift, true); } };
        set_act(b);
        // D^-1 of C1 (X = r_{j+1} -> r_{j+1} + q_{>=QCH} Y), then X += C0 Y keeping C0. old5: q in the slots; in
        // place (G_IP5): q at X-index sy + kb, C0 first moved to its slots (X < Y leaves those lanes alone)
        if old5 {
            let pre_abs = vec![sx[0], pzero];
            for kk in qch..kmax {
                fetch(b, kk, &[(act, false)]);
                add(b, kk, c, false);
                gate_x(b, kk, act, sx[0], true);
                cmp_y(b, kk, false, &pre_abs);
                gate_x(b, kk, act, sx[0], false);
            }
        } else {
            for kb in 0..qch {
                gate_x(b, kb, act, sx[0], true);
                inplace(b, kb, &pre_c);
                gate_x(b, kb, act, sx[0], false);
                fetch(b, kb, &[(act, false)]);
            }
            // IP5-split: the bits >= K come from slots QCH + kk - K
            let kin = kmax;
            b.play(&vg, false);
            for kk in qch..kin {
                gate_v(b, kk, act, sx[0], true);
                inplace(b, kk, &pre_c);
                mul_back(b, kk);
                gate_v(b, kk, act, sx[0], false);
            }
            b.play(&vg, true);
            for kk in kin..kmax {
                fetch(b, qch + kk - kin, &[(act, false)]);
                add(b, kk, c, false);
                gate_x(b, kk, act, sx[0], true);
                cmp_y(b, kk, false, &pre_c);
                gate_x(b, kk, act, sx[0], false);
            }
        }
        for kb in 0..qch {
            fetch(b, kb, &[(act, false)]);
            add(b, kb, c, false);
            fetch(b, kb, &[(act, false)]);
        }
        // S1 erases C0 (X = r_{j-1} -> r_{j+1} + q_{>=QCH} Y); then the in-place division for the bits >= QCH and
        // each bit back to its C1 slot while X regains it; S2 erases C1
        for i in 0..nch {
            let (lo, hi) = (bd[i], bd[i + 1]);
            if i > 0 {
                div_inplace(b, lo);
                if hi == kmax {
                    for kk in lo..kmax {
                        gate_x(b, kk, act, sx[0], true);
                        inplace(b, kk, &pre_c);
                        add(b, kk, c, false);
                        gate_x(b, kk, act, sx[0], false);
                        fetch(b, kk - lo, &[(act, false)]);
                    }
                } else {
                    // (lowq_cross) a middle chunk: to its slots, the bits >= hi multiplied back by D^-1 (X = r_{j+1} +
                    // q_[hi, kk] Y < 2^(kk+1) Y: each erased by [X >= 2^kk Y]), then X += C_i Y keeping C_i
                    for kk in lo..hi {
                        gate_x(b, kk, act, sx[0], true);
                        inplace(b, kk, &pre_c);
                        gate_x(b, kk, act, sx[0], false);
                        fetch(b, kk - lo, &[(act, false)]);
                    }
                    b.play(&vg, false);
                    for kk in hi..kmax {
                        gate_v(b, kk, act, sx[0], true);
                        inplace(b, kk, &pre_c);
                mul_back(b, kk);
                        gate_v(b, kk, act, sx[0], false);
                    }
                    b.play(&vg, true);
                    for kk in lo..hi {
                        fetch(b, kk - lo, &[(act, false)]);
                        add(b, kk, c, false);
                        fetch(b, kk - lo, &[(act, false)]);
                    }
                }
            }
            let pk = &parks[i];
            b.x(ph);
            b.play(&sy7_normal, false);
            b.play(pk, false);
            #[cfg(test)] let d4b_start = b.ops.len();
            let f1 = b.tof;
            super::frogdrop_col::mark(b, 3121);
            vmark(b, 3351);
            act_ht(b, true);
            b.play(if compact675 { &lowq675_forms[i] } else { &vform_pk }, false);
            act_ht(b, true);
            vmark(b, 3300);
            super::frogdrop_col::mark(b, 3122);
            super::f1_profile("midg.vform", f1, b.tof);
            #[cfg(test)] d4b_window(d4b_start, b.ops.len(), if lo == 0 { 2 } else { 4 }, act);
            b.play(pk, false);
            b.play(&sy7_normal, false);
            b.x(ph);
            for kb in lo..hi {
                gate_on(b, kb, act);
                fetch(b, kb - lo, &[(ak, false)]);
                b.cx(c, ak);
                add(b, kb, ak, false);
                b.cx(c, ak);
                let r = rotz(b, &[window_base]);
                b.play(&r, false);
                mc_xor(b, &[(ak, false), (ring[window_base], true)], c, &[], &dirty);
                b.play(&r, true);
                add(b, kb, ak, true);
                gate_off(b, kb, act);
            }
            let f1 = b.tof;
            if ph_r { b.x(ph); }
            vmark(b, 3361);
            act_ht(b, ph_r);
            b.play(&vform, true);
            act_ht(b, ph_r);
            vmark(b, 3300);
            if ph_r { b.x(ph); }
            super::f1_profile("midg.vform", f1, b.tof);
        }
        set_act(b);
    }
    if cp.ht && !chunk && !fixed_ht {
        let set_act = |b: &mut B| { if zoff_on && cp.dq { b.play(&zshift, false); } ht_act(b, fd, cp, sc, act, &sx[..1], x128, &dirty); if zoff_on && cp.dq { b.play(&zshift, true); } };
        set_act(b);
        // X += qY (back to r_{j-1}), q's bits from their in-place lanes (X-index sy + kb, free while
        // X < 2^kb Y) to the headroom
        let (sylo, syhi) = (cp.sy.0.max(1), cp.sy.1.min(nq));
        for kb in 0..kmax {
            if old5 {
                fetch(b, kb, &[(act, false)]);
            } else {
                let lane = |vv: usize| { let i = n as isize - 1 - vv as isize - kb as isize;
                                         if i >= 0 { Some(ring[i as usize]) } else { None } };
                super::mid2::dec_swap(b, &fd.sy, sylo, syhi, &lane, c, &[(act, false)], &sx[..VB], &[], &dirty);
            }
            add(b, kb, c, false);
            fetch(b, kb, &[(act, false)]);
        }
        b.x(ph);
        b.play(&sy7_normal, false);
        b.play(&park, false);
        #[cfg(test)] let d4b_start = b.ops.len();
        let f1 = b.tof;
        vmark(b, 3371);
        act_ht(b, true);
        b.play(&vform_pk, false);
        act_ht(b, true);
        vmark(b, 3300);
        super::f1_profile("midg.vform", f1, b.tof);
        #[cfg(test)] d4b_window(d4b_start, b.ops.len(), 2, act);
        b.play(&park, false);
        b.play(&sy7_normal, false);
        b.x(ph);
        for kb in 0..kmax {
            gate_on(b, kb, act);
            fetch(b, kb, &[(ak, false)]);
            // trial X += 2^kb Y where ak & !c (X = r_{j+1} + (q_{>kb} + 2^kb) Y either way): c = 1 only where ak
            b.cx(c, ak);
            add(b, kb, ak, false);
            b.cx(c, ak);
            // c ^= ak & !over = q_kb: erased
            let r = rotz(b, &[window_base]);
            b.play(&r, false);
            mc_xor(b, &[(ak, false), (ring[window_base], true)], c, &[], &dirty);
            b.play(&r, true);
            add(b, kb, ak, true);
            gate_off(b, kb, act);
        }
        let f1 = b.tof;
        if ph_r { b.x(ph); }
        vmark(b, 3381);
        act_ht(b, ph_r);
        b.play(&vform, true);
        act_ht(b, ph_r);
        vmark(b, 3300);
        if ph_r { b.x(ph); }
        super::f1_profile("midg.vform", f1, b.tof);
        set_act(b);
    }
    if !stage(b) { return; } // 6
    b.play(&zshift, false);
    let _ = stage(b); // 7
}

/// Old dirty echo, word echo and returned-bank threshold must implement the
/// same reciprocal/window map, restore dirty passengers, and leave zero phase.
#[cfg(test)]
#[test]
fn t2_clean_early_gate_matches_dirty_echo() {
    use super::tests_frogdrop::run;
    for parked in [false, true] {
        for noact in [false, true] {
            let build = |mode: usize| {
                let clean = mode == 2;
                let mut b = B::new();
                let zh = b.alloc_n(24);
                let win = b.alloc_n(TC + 1);
                let sz = b.alloc_n(8);
                let sy = b.alloc_n(8);
                let gap = b.alloc_n(5);
                let r = b.alloc_n(24);
                let bank = b.alloc_n(8);
                let dirty = b.alloc_n(40);
                let act = b.alloc();
                let s = S1 { r: r.clone(), f: r[23], zero: win[0], sgn: win[0],
                    gt: vec![if clean { bank[0] } else { sz[0] }],
                    anc: bank[1..].to_vec(), andc: bank.clone(),
                    chain: if clean { bank[1..].to_vec() } else { bank.clone() },
                    dirty: dirty.clone() };
                S1_GATE.with(|g| *g.borrow_mut() = if parked {
                    S1Gate::UPark { u: sy[..7].to_vec(), g: gap.clone(), dk: dirty[39], d2: dirty[38] }
                } else { S1Gate::U8 { u: sy.clone() } });
                S1_NOACT.with(|c| c.set(noact));
                std::env::set_var("T2_WORD_ECHO", if mode == 0 { "0" } else { "1" });
                let rec = stage1_v(&mut b, &zh, &win, &sz, (231, 256), &s, act, true);
                std::env::remove_var("T2_WORD_ECHO");
                b.play(&rec, false);
                let forward = b.ops.len();
                b.play(&rec, true);
                S1_GATE.with(|g| *g.borrow_mut() = S1Gate::Sz);
                S1_NOACT.with(|c| c.set(false));
                (b, forward, zh, win, sz, sy, gap, r, bank, dirty, act)
            };
            let old = build(0);
            let new = build(1);
            let clean = build(2);
            assert_eq!(old.0.width(), new.0.width());
            assert_eq!(old.0.width(), clean.0.width());
            let mut input = vec![0u64; old.0.width() as usize];
            for (i, &q) in old.2.iter().enumerate() {
                input[q.0 as usize] = if i == 23 { u64::MAX } else {
                    0x96e5_a4c3_7d18_b20fu64.rotate_left((i * 9) as u32) };
            }
            for (i, &q) in old.3.iter().enumerate() {
                input[q.0 as usize] = 0x517c_8ba6_d3e0_29f4u64.rotate_left((i * 11) as u32);
            }
            for (i, &q) in old.4.iter().enumerate() {
                input[q.0 as usize] = 0xa5a5_5a5a_cc33_33ccu64.rotate_left((i * 7) as u32);
            }
            for (i, &q) in old.5.iter().enumerate() {
                input[q.0 as usize] = if parked && i == 7 { 0 } else {
                    0x8102_0408_1020_4081u64.rotate_left((i * 3) as u32) };
            }
            for (i, &q) in old.6.iter().enumerate() {
                input[q.0 as usize] = 0x0482_1904_8219_0482u64.rotate_left((i * 5) as u32);
            }
            for (i, &q) in old.9.iter().enumerate() {
                input[q.0 as usize] = 0xf00f_0ff0_a55a_5aa5u64.rotate_left((i * 13) as u32);
            }
            input[old.10.0 as usize] = 0x5a69_a596_9669_6996;
            let fo = run(&old.0.ops[..old.1], input.len(), &|q| *q = input.clone());
            let fnw = run(&new.0.ops[..new.1], input.len(), &|q| *q = input.clone());
            let fc = run(&clean.0.ops[..clean.1], input.len(), &|q| *q = input.clone());
            assert_eq!(fo.phase, 0, "old forward parked={parked} noact={noact}");
            assert_eq!(fnw.phase, 0, "new forward parked={parked} noact={noact}");
            assert_eq!(fc.phase, 0, "clean forward parked={parked} noact={noact}");
            assert_eq!(fo.q, fnw.q, "forward parked={parked} noact={noact}");
            assert_eq!(fo.q, fc.q, "clean forward parked={parked} noact={noact}");
            for (label, b) in [("old", &old.0), ("new", &new.0), ("clean", &clean.0)] {
                let inv = run(&b.ops, input.len(), &|q| *q = input.clone());
                assert_eq!(inv.phase, 0, "{label} phase parked={parked} noact={noact}");
                assert_eq!(inv.q, input, "{label} inverse parked={parked} noact={noact}");
            }
        }
    }
}

/// Exhaust the eight-bit size and single parked-bit part of the K2 V wrapper.
/// This records the same SGW arithmetic, four route controls, U forms and
/// early gate primitive used by `middle`; the 256-bit reciprocal is exercised
/// separately by the full-column packed replays.
#[cfg(test)]
#[test]
fn b3_routed_v_size_gate_exhaustive() {
    use super::tests_frogdrop::run;
    use super::frogdrop_col::rec;
    let mut cases = Vec::<(usize, usize, usize, bool)>::new();
    for syv in 1..=128usize {
        for gap in 0..=23usize {
            if 2 * syv + gap > 257 { continue; }
            let szv = 257 - syv - gap;
            if szv > 256 { continue; }
            cases.push((szv, syv, gap, false));
            if (121..=128).contains(&syv) && gap <= 15 {
                cases.push((szv, syv, gap, true));
            }
        }
    }
    for parked in [false, true] {
        let mut b = B::new();
        let a = b.alloc_n(8);
        let sy = b.alloc_n(8);
        let sx7 = b.alloc();
        let x128 = b.alloc();
        let act = b.alloc();
        let out = b.alloc_n(26);
        let dirty = b.alloc_n(24);
        let (dk, d2) = (dirty[23], dirty[22]);
        let sg = rec(&mut b, |b| {
            if parked {
                let mut ax = sy[..7].to_vec(); ax.push(sx7);
                super::arith::ttk_add(b, &ax, &a[..8], None, None);
                let zero: Vec<(QubitId, bool)> = sy[..7].iter().map(|&q| (q, true)).collect();
                mc_xor(b, &zero, a[7], &[], &dirty);
            } else {
                super::arith::ttk_add(b, &sy[..8], &a[..8], None, None);
            }
            for &x in &a { b.x(x); }
            super::modp_frogdrop::inc_dirty_free(b, &a[1..], &dirty);
        });
        let route = rec(&mut b, |b| {
            let prefixes: [&[(usize, bool)]; 4] = [
                &[(6, true), (5, true), (4, true), (3, true), (2, true), (1, true), (0, true)],
                &[(6, false), (5, false), (4, false), (3, false), (2, true), (1, true), (0, false)],
                &[(6, false), (5, false), (4, false), (3, false), (2, true), (1, false)],
                &[(6, false), (5, false), (4, false), (3, false), (2, false)],
            ];
            for p in prefixes {
                let controls: Vec<(QubitId, bool)> = p.iter().map(|&(i, neg)| (sy[i], neg)).collect();
                super::mid2::mc_swap(b, &controls, x128, a[4], &[], &dirty);
            }
        });
        let u = rec(&mut b, |b| {
            if parked { super::arith::ttk_add(b, &a[..7], &sy[..7], None, None); }
            else { super::arith::ttk_add(b, &a[..8], &sy[..8], None, None); }
        });
        let gate = if parked { S1Gate::UPark { u: sy[..7].to_vec(), g: a[..5].to_vec(), dk, d2 } }
                   else { S1Gate::U8 { u: sy.clone() } };
        let wrapper = rec(&mut b, |b| {
            b.play(&sg, false);
            b.play(&route, false);
            b.play(&u, false);
            for j in 0..26 { s1_gate_u(b, &gate, j, act, out[j], &dirty); }
            b.play(&u, true);
            b.play(&route, true);
            b.play(&sg, false);
        });
        b.play(&wrapper, false);
        let forward = b.ops.len();
        b.play(&wrapper, true);
        let width = b.width() as usize;
        for chunk in cases.chunks(64) {
            let mut input = vec![0u64; width];
            input[act.0 as usize] = (1u64 << chunk.len().min(63)) - 1;
            if chunk.len() == 64 { input[act.0 as usize] = u64::MAX; }
            for (shot, &(szv, syv, _, bit)) in chunk.iter().enumerate() {
                for i in 0..8 {
                    if (szv >> i) & 1 != 0 { input[a[i].0 as usize] |= 1 << shot; }
                    if (syv >> i) & 1 != 0 && !(parked && i == 7) {
                        input[sy[i].0 as usize] |= 1 << shot;
                    }
                }
                if bit { input[x128.0 as usize] |= 1 << shot; }
            }
            for (i, &lane) in dirty.iter().enumerate() {
                input[lane.0 as usize] = 0xa5a5_5a5a_f0f0_0f0fu64.rotate_left((i * 7) as u32);
            }
            let f = run(&b.ops[..forward], width, &|q| *q = input.clone());
            assert_eq!(f.phase, 0, "forward phase parked={parked}");
            for (shot, &(_, syv, gap, bit)) in chunk.iter().enumerate() {
                let mut want = input.clone();
                for j in 0..26 {
                    let predicate = syv + gap <= j;
                    if predicate { want[out[j].0 as usize] |= 1 << shot; }
                }
                for j in 0..26 {
                    assert_eq!((f.q[out[j].0 as usize] >> shot) & 1,
                               (want[out[j].0 as usize] >> shot) & 1,
                               "gate parked={parked} sy={syv} gap={gap} bit={bit} j={j}");
                }
                for &lane in a.iter().chain(sy.iter()).chain(std::iter::once(&x128)).chain(dirty.iter()) {
                    assert_eq!((f.q[lane.0 as usize] >> shot) & 1,
                               (input[lane.0 as usize] >> shot) & 1,
                               "restoration parked={parked} sy={syv} gap={gap} bit={bit}");
                }
            }
            let both = run(&b.ops, width, &|q| *q = input.clone());
            assert_eq!(both.phase, 0, "round-trip phase parked={parked}");
            assert_eq!(both.q, input, "round-trip all lanes parked={parked}");
        }
        eprintln!("B3_ROUTED_V_SIZE_GATE parked={parked} cases={} width={width} forward_ops={forward}", cases.len());
    }
}

/// Finite circuit check of both K1 routed owners, including the sy122
/// crossing corner, both SGW forms, the unchanged U gate, and inverse phase.
#[cfg(test)]
#[test]
fn b5_two_owner_v_size_gate_exhaustive() {
    use super::tests_frogdrop::run;
    use super::frogdrop_col::rec;
    for cross in [false, true] {
        for parked in [false, true] {
            let mut b = B::new();
            let a = b.alloc_n(8);
            let sy = b.alloc_n(8);
            let sx7 = b.alloc();
            let x128 = b.alloc();
            let q127 = b.alloc();
            let act = b.alloc();
            let loan = b.alloc_n(2);
            let out = b.alloc_n(26);
            let dirty = b.alloc_n(24);
            let (dk, d2) = (dirty[23], dirty[22]);
            let sg = rec(&mut b, |b| {
                if parked {
                    let mut ax = sy[..7].to_vec(); ax.push(sx7);
                    super::arith::ttk_add(b, &ax, &a[..8], None, None);
                    let zero: Vec<(QubitId, bool)> = sy[..7].iter().map(|&q| (q, true)).collect();
                    mc_xor(b, &zero, a[7], &[], &dirty);
                } else { super::arith::ttk_add(b, &sy[..8], &a[..8], None, None); }
                for &x in &a { b.x(x); }
                super::modp_frogdrop::inc_dirty_free(b, &a[1..], &dirty);
            });
            let route = rec(&mut b, |b| {
                let prefixes: [&[(usize, bool)]; 4] = [
                    &[(6, true), (5, true), (4, true), (3, true), (2, true), (1, true), (0, true)],
                    &[(6, false), (5, false), (4, false), (3, false), (2, true), (1, true), (0, false)],
                    &[(6, false), (5, false), (4, false), (3, false), (2, true), (1, false)],
                    &[(6, false), (5, false), (4, false), (3, false), (2, false)],
                ];
                for p in prefixes {
                    let ct: Vec<(QubitId, bool)> = p.iter().map(|&(i, neg)| (sy[i], neg)).collect();
                    super::mid2::mc_swap(b, &ct, x128, a[4], &[], &dirty);
                }
                let sy_eq = |v: usize| -> Vec<(QubitId, bool)> {
                    (0..7).map(|i| (sy[i], ((v >> i) & 1) == 0)).collect()
                };
                let mut sq = |ct: Vec<(QubitId, bool)>, bit: usize| {
                    super::mid2::mc_swap(b, &ct, q127, a[bit], &[], &dirty);
                };
                sq(sy_eq(125), 3);
                sq((1..7).map(|i| (sy[i], false)).collect(), 3);
                sq(sy_eq(128), 3);
                if cross {
                    let mut ct = sy_eq(122); ct.extend([(a[3], false), (a[2], false)]);
                    sq(ct, 1);
                    for v in [121, 123, 124] { sq(sy_eq(v), 4); }
                    let mut ct = sy_eq(122); ct.push((a[3], true)); sq(ct, 4);
                    let mut ct = sy_eq(122); ct.extend([(a[3], false), (a[2], true)]); sq(ct, 4);
                } else {
                    sq(sy_eq(121), 4);
                    sq((1..7).map(|i| (sy[i], ((122 >> i) & 1) == 0)).collect(), 3);
                    sq(sy_eq(124), 3);
                }
            });
            let u = rec(&mut b, |b| {
                if parked { super::arith::ttk_add(b, &a[..7], &sy[..7], None, None); }
                else { super::arith::ttk_add(b, &a[..8], &sy[..8], None, None); }
            });
            let gate = if parked { S1Gate::UPark { u: sy[..7].to_vec(), g: a[..5].to_vec(), dk, d2 } }
                       else { S1Gate::U8 { u: sy.clone() } };
            let wrapper = rec(&mut b, |b| {
                b.play(&sg, false);
                b.play(&route, false);
                b.cx(loan[0], x128); b.cx(loan[1], q127);
                b.play(&u, false);
                for j in 0..26 { s1_gate_u(b, &gate, j, act, out[j], &dirty); }
                b.play(&u, true);
                b.play(&route, true);
                b.play(&sg, false);
            });
            b.play(&wrapper, false);
            let forward = b.ops.len();
            b.play(&wrapper, true);
            let width = b.width() as usize;
            let mut cases = Vec::new();
            for syv in 121..=128usize {
                for g in 0..=15usize {
                    let szv = 257 - syv - g;
                    if szv < syv || szv > 256 || (!cross && (122..=124).contains(&syv) && g > 7) { continue; }
                    let bd: &[usize] = if cross { &[0, 1, 3, 7, 14, 21, 23] }
                                       else { &[0, 7, 14, 21, 23] };
                    for w in bd.windows(2) {
                        let xb = 128usize.saturating_sub(syv) + w[0];
                        let qb = 127usize.saturating_sub(syv) + w[0];
                        let cx = syv <= 128 && syv + (xb - w[0]) == 128
                            && xb < w[1] && xb <= g.min(22);
                        let cq = syv == 128 || (syv <= 127 && syv + (qb - w[0]) == 127
                            && qb < w[1] && qb <= g.min(22));
                        for xv in 0..=usize::from(cx) {
                            for qv in 0..=usize::from(cq) { cases.push((szv, syv, g, xv, qv)); }
                        }
                    }
                }
            }
            for chunk in cases.chunks(64) {
                let mut input = vec![0u64; width];
                input[act.0 as usize] = if chunk.len() == 64 { u64::MAX } else { (1u64 << chunk.len()) - 1 };
                for (shot, &(szv, syv, _, xv, qv)) in chunk.iter().enumerate() {
                    for i in 0..8 {
                        if (szv >> i) & 1 != 0 { input[a[i].0 as usize] |= 1 << shot; }
                        if (syv >> i) & 1 != 0 && !(parked && i == 7) { input[sy[i].0 as usize] |= 1 << shot; }
                    }
                    if xv != 0 { input[x128.0 as usize] |= 1 << shot; }
                    if qv != 0 { input[q127.0 as usize] |= 1 << shot; }
                }
                for (i, &lane) in dirty.iter().enumerate() {
                    input[lane.0 as usize] = 0xa5a5_5a5a_f0f0_0f0fu64.rotate_left((i * 7) as u32);
                }
                let f = run(&b.ops[..forward], width, &|q| *q = input.clone());
                assert_eq!(f.phase, 0, "forward phase cross={cross} parked={parked}");
                for (shot, &(szv, syv, g, xv, qv)) in chunk.iter().enumerate() {
                    for &lane in &loan {
                        assert_eq!((f.q[lane.0 as usize] >> shot) & 1, 0,
                                   "R not zero cross={cross} parked={parked} sz={szv} sy={syv} g={g} x={xv} q={qv}");
                    }
                    for j in 0..26 {
                        assert_eq!((f.q[out[j].0 as usize] >> shot) & 1, u64::from(syv + g <= j),
                                   "gate cross={cross} parked={parked} sz={szv} sy={syv} g={g} x={xv} q={qv} j={j}");
                    }
                    for &lane in a.iter().chain(sy.iter()).chain([&x128, &q127]).chain(dirty.iter()) {
                        assert_eq!((f.q[lane.0 as usize] >> shot) & 1, (input[lane.0 as usize] >> shot) & 1,
                                   "restore cross={cross} parked={parked} sz={szv} sy={syv} g={g} x={xv} q={qv}");
                    }
                }
                let both = run(&b.ops, width, &|q| *q = input.clone());
                assert_eq!(both.phase, 0);
                assert_eq!(both.q, input, "round trip cross={cross} parked={parked}");
            }
            eprintln!("B5_TWO_OWNER_GATE cross={cross} parked={parked} cases={} width={width} forward_ops={forward}", cases.len());
        }
    }
}

/// Physical finite K0 gate: the production Q126 route is exercised after the
/// B5 swaps, with arbitrary supported owner values and dirty passengers.
/// Each case is derived from the full public-envelope screen, then deduplicated.
#[cfg(test)]
#[test]
fn b6_three_owner_v_size_gate_exhaustive() {
    use super::tests_frogdrop::run;
    use super::frogdrop_col::rec;
    let cases: Vec<[usize; 7]> = include_str!("b6_route_cases.txt").lines().map(|line| {
        let v: Vec<usize> = line.split_whitespace().map(|s| s.parse().unwrap()).collect();
        v.try_into().unwrap()
    }).collect();
    assert_eq!(cases.len(), 326);
    for cross in [false, true] {
        for parked in [false, true] {
            let mut b = B::new();
            let a = b.alloc_n(8);
            let sy = b.alloc_n(8);
            let sx7 = b.alloc();
            let x128 = b.alloc();
            let q127 = b.alloc();
            let q126 = b.alloc();
            let act = b.alloc();
            let obs = b.alloc_n(3);
            let out = b.alloc_n(26);
            let dirty = b.alloc_n(24);
            let (dk, d2) = (dirty[23], dirty[22]);
            let third = rec(&mut b, |b| b6_route_third(b, &sy, &a, q126, cross, &dirty));
            let sg = rec(&mut b, |b| {
                if parked {
                    let mut ax = sy[..7].to_vec(); ax.push(sx7);
                    super::arith::ttk_add(b, &ax, &a[..8], None, None);
                    let zero: Vec<(QubitId, bool)> = sy[..7].iter().map(|&q| (q, true)).collect();
                    mc_xor(b, &zero, a[7], &[], &dirty);
                } else { super::arith::ttk_add(b, &sy[..8], &a[..8], None, None); }
                for &x in &a { b.x(x); }
                super::modp_frogdrop::inc_dirty_free(b, &a[1..], &dirty);
            });
            let route = rec(&mut b, |b| {
                let prefixes: [&[(usize, bool)]; 4] = [
                    &[(6, true), (5, true), (4, true), (3, true), (2, true), (1, true), (0, true)],
                    &[(6, false), (5, false), (4, false), (3, false), (2, true), (1, true), (0, false)],
                    &[(6, false), (5, false), (4, false), (3, false), (2, true), (1, false)],
                    &[(6, false), (5, false), (4, false), (3, false), (2, false)],
                ];
                for p in prefixes {
                    let ct: Vec<(QubitId, bool)> = p.iter().map(|&(i, neg)| (sy[i], neg)).collect();
                    super::mid2::mc_swap(b, &ct, x128, a[4], &[], &dirty);
                }
                let sy_eq = |v: usize| -> Vec<(QubitId, bool)> {
                    (0..7).map(|i| (sy[i], ((v >> i) & 1) == 0)).collect()
                };
                let mut sq = |ct: Vec<(QubitId, bool)>, bit: usize| {
                    super::mid2::mc_swap(b, &ct, q127, a[bit], &[], &dirty);
                };
                sq(sy_eq(125), 3);
                sq((1..7).map(|i| (sy[i], false)).collect(), 3);
                sq(sy_eq(128), 3);
                if cross {
                    let mut ct = sy_eq(122); ct.extend([(a[3], false), (a[2], false)]);
                    sq(ct, 1);
                    for v in [121, 123, 124] { sq(sy_eq(v), 4); }
                    let mut ct = sy_eq(122); ct.push((a[3], true)); sq(ct, 4);
                    let mut ct = sy_eq(122); ct.extend([(a[3], false), (a[2], true)]); sq(ct, 4);
                } else {
                    sq(sy_eq(121), 4);
                    sq((1..7).map(|i| (sy[i], ((122 >> i) & 1) == 0)).collect(), 3);
                    sq(sy_eq(124), 3);
                }
                b.play(&third, false);
            });
            let mut route_cost = B::new();
            route_cost.alloc_n(b.width() as usize);
            route_cost.play(&route, false);
            let route_t = route_cost.tof;
            let route_ops = route_cost.ops.len();
            let mut third_cost = B::new();
            third_cost.alloc_n(b.width() as usize);
            third_cost.play(&third, false);
            let third_t = third_cost.tof;
            let third_ops = third_cost.ops.len();
            eprintln!("B6_ROUTE_COST cross={cross} forward_t={route_t} forward_ops={route_ops} third_t={third_t} third_ops={third_ops}");
            let u = rec(&mut b, |b| {
                if parked { super::arith::ttk_add(b, &a[..7], &sy[..7], None, None); }
                else { super::arith::ttk_add(b, &a[..8], &sy[..8], None, None); }
            });
            let gate = if parked { S1Gate::UPark { u: sy[..7].to_vec(), g: a[..5].to_vec(), dk, d2 } }
                       else { S1Gate::U8 { u: sy.clone() } };
            let wrapper = rec(&mut b, |b| {
                b.play(&sg, false);
                b.play(&route, false);
                b.cx(x128, obs[0]); b.cx(q127, obs[1]); b.cx(q126, obs[2]);
                b.play(&u, false);
                for j in 0..26 { s1_gate_u(b, &gate, j, act, out[j], &dirty); }
                b.play(&u, true);
                b.play(&route, true);
                b.play(&sg, false);
            });
            b.play(&wrapper, false);
            let forward = b.ops.len();
            b.play(&wrapper, true);
            let width = b.width() as usize;
            let selected: Vec<[usize; 7]> = cases.iter().copied().filter(|r| r[0] == usize::from(cross)).collect();
            for chunk in selected.chunks(64) {
                let mut input = vec![0u64; width];
                input[act.0 as usize] = if chunk.len() == 64 { u64::MAX } else { (1u64 << chunk.len()) - 1 };
                for (shot, &[_, szv, syv, _, xv, qv, rv]) in chunk.iter().enumerate() {
                    for i in 0..8 {
                        if (szv >> i) & 1 != 0 { input[a[i].0 as usize] |= 1 << shot; }
                        if (syv >> i) & 1 != 0 && !(parked && i == 7) { input[sy[i].0 as usize] |= 1 << shot; }
                    }
                    if xv != 0 { input[x128.0 as usize] |= 1 << shot; }
                    if qv != 0 { input[q127.0 as usize] |= 1 << shot; }
                    if rv != 0 { input[q126.0 as usize] |= 1 << shot; }
                }
                for (i, &lane) in dirty.iter().enumerate() {
                    input[lane.0 as usize] = 0xa5a5_5a5a_f0f0_0f0fu64.rotate_left((i * 7) as u32);
                }
                let f = run(&b.ops[..forward], width, &|q| *q = input.clone());
                assert_eq!(f.phase, 0, "forward phase cross={cross} parked={parked}");
                for (shot, &[_, szv, syv, g, xv, qv, rv]) in chunk.iter().enumerate() {
                    for &lane in &obs {
                        assert_eq!((f.q[lane.0 as usize] >> shot) & 1, 0,
                                   "R owner occupied cross={cross} parked={parked} sz={szv} sy={syv} g={g} x={xv} q={qv} r={rv}");
                    }
                    for j in 0..26 {
                        assert_eq!((f.q[out[j].0 as usize] >> shot) & 1, u64::from(syv + g <= j),
                                   "U gate cross={cross} parked={parked} sy={syv} g={g} j={j}");
                    }
                    for &lane in a.iter().chain(sy.iter()).chain([&x128, &q127, &q126]).chain(dirty.iter()) {
                        assert_eq!((f.q[lane.0 as usize] >> shot) & 1, (input[lane.0 as usize] >> shot) & 1,
                                   "restoration cross={cross} parked={parked} sy={syv} g={g}");
                    }
                }
                let both = run(&b.ops, width, &|q| *q = input.clone());
                assert_eq!(both.phase, 0, "round-trip phase cross={cross} parked={parked}");
                assert_eq!(both.q, input, "round trip cross={cross} parked={parked}");
            }
            eprintln!("B6_THREE_OWNER_GATE cross={cross} parked={parked} cases={} width={width} forward_ops={forward}", selected.len());
        }
    }
}

/// B8B: a parked band may dirty Q above the true Y length. The masked
/// full-width ripple must equal a clean short-source ripple on every wire.
#[cfg(test)]
#[test]
fn b8b_masked_ripple_variants_match_short_source() {
    use super::frogdrop_col::rec;
    use super::tests_frogdrop::run;
    for syv in [1usize, 16, 116, 119, 121, 125, 128] {
        let build = |mode: u8| {
            let mut b = B::new();
            let t = b.alloc_n(129);
            let s = b.alloc_n(129);
            let sy = b.alloc_n(8);
            let ak = b.alloc();
            let c0 = b.alloc();
            let cmp = b.alloc();
            let g = b.alloc();
            let pre = b.alloc_n(8);
            let dirty = b.alloc_n(24);
            let fwd = rec(&mut b, |b| {
                let mut mid = |b: &mut B| {
                    b.x(s[syv]); b.ccx(ak, s[syv], cmp); b.x(s[syv]);
                };
                if mode == 1 {
                    b8b_ripple_masked_source(b, &t, &s, &sy, 128, cmp, c0, g,
                                             &pre[..1], &dirty, &mut mid);
                } else if mode == 2 || mode == 3 || mode == 4 {
                    let h = if mode == 2 { 2 } else { 7 };
                    b8b_ripple_early_carry(b, &t, &s, &sy, 1, 128, ak, c0, cmp, g,
                                           &pre[..h], if mode == 4 { &[] } else { &pre[h..h + 1] }, &dirty,
                                           true, None);
                } else {
                    let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| cmp);
                    super::payload::ripple(b, &t[..=syv], &s[..=syv], c0, true, &mut mid, &mut gate);
                }
            });
            b.play(&fwd, false);
            let forward = b.ops.len();
            b.play(&fwd, true);
            (b, forward, t, s, sy, ak, dirty)
        };
        let (old, old_forward, t, s, sy, ak, dirty) = build(0);
        let (new, new_forward, _, _, _, _, _) = build(1);
        let (early, early_forward, _, _, _, _, _) = build(2);
        let (early7, early7_forward, _, _, _, _, _) = build(3);
        let (early7_no_temp, early7_no_temp_forward, _, _, _, _, _) = build(4);
        let width = old.width() as usize;
        assert_eq!(width, new.width() as usize);
        assert_eq!(width, early.width() as usize);
        assert_eq!(width, early7.width() as usize);
        assert_eq!(width, early7_no_temp.width() as usize);
        let mut input = vec![0u64; width];
        for (i, &q) in t.iter().chain(s.iter()).chain(dirty.iter()).enumerate() {
            input[q.0 as usize] = 0x9e37_79b9_7f4a_7c15u64
                .rotate_left(((i * 11) % 64) as u32) ^ (i as u64).wrapping_mul(0xa076_1d64_78bd_642f);
        }
        input[ak.0 as usize] = 0xa5a5_f0f0_6699_33cc;
        for (i, &q) in sy.iter().enumerate() {
            input[q.0 as usize] = if (syv >> i) & 1 != 0 { u64::MAX } else { 0 };
        }
        let a = run(&old.ops[..old_forward], width, &|q| *q = input.clone());
        let b = run(&new.ops[..new_forward], width, &|q| *q = input.clone());
        let c = run(&early.ops[..early_forward], width, &|q| *q = input.clone());
        let d = run(&early7.ops[..early7_forward], width, &|q| *q = input.clone());
        let e = run(&early7_no_temp.ops[..early7_no_temp_forward], width, &|q| *q = input.clone());
        assert_eq!(a.phase, 0, "old forward phase sy={syv}");
        assert_eq!(b.phase, 0, "masked forward phase sy={syv}");
        assert_eq!(c.phase, 0, "early forward phase sy={syv}");
        assert_eq!(d.phase, 0, "early7 forward phase sy={syv}");
        assert_eq!(e.phase, 0, "early7 no-temp forward phase sy={syv}");
        for (label, got) in [("full", &b.q), ("early", &c.q), ("early7", &d.q),
                             ("early7-no-temp", &e.q)] {
            if a.q.as_slice() != got.as_slice() {
                let pos = a.q.iter().zip(got).position(|(x, y)| x != y).unwrap();
                panic!("{label}/short forward mismatch sy={syv} lane={pos} old={:#018x} new={:#018x} input={:#018x}",
                       a.q[pos], got[pos], input[pos]);
            }
        }
        for (label, circuit) in [("short", &old), ("full", &new), ("early", &early),
                                 ("early7", &early7), ("early7-no-temp", &early7_no_temp)] {
            let rt = run(&circuit.ops, width, &|q| *q = input.clone());
            assert_eq!(rt.phase, 0, "round-trip phase {label} sy={syv}");
            assert_eq!(rt.q, input, "round-trip state {label} sy={syv}");
        }
        eprintln!("B8B_MASKED_RIPPLE sy={syv} width={width} old_t={} full_t={} early_t={} early7_t={} early7_no_temp_t={}",
                  old.tof, new.tof, early.tof, early7.tof, early7_no_temp.tof);
    }
}

/// B8B cost binding: compare the production-style dynamic-sy comparator with
/// clean high Q against the repaired dynamic-sy ripple with dirty high Q.
#[cfg(test)]
#[test]
fn b8b_masked_cmp_dynamic_sy_cost_and_dirty_equivalence() {
    use super::frogdrop_col::rec;
    use super::tests_frogdrop::run;
    let build = |masked: bool| {
        let mut b = B::new();
        let t = b.alloc_n(129);
        let s = b.alloc_n(129);
        let sy = b.alloc_n(8);
        let ak = b.alloc();
        let c0 = b.alloc();
        let cmp = b.alloc();
        let m = b.alloc();
        let pre = b.alloc_n(8);
        let dirty = b.alloc_n(24);
        let fwd = rec(&mut b, |b| {
            if masked {
                b8b_ripple_early_carry(b, &t, &s, &sy, 1, 128, ak, c0, cmp, m,
                                       &pre[..7], &[], &dirty, true, None);
            } else {
                let rd = s.clone();
                let mut mid = |b: &mut B| {
                    let lane = |v: usize| rd.get(v).copied();
                    read_lane(b, &sy, 1, 128, &lane, true, &[(ak, false)], cmp,
                              &pre[..7], &[], &dirty);
                };
                let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| cmp);
                ripple(b, &t, &s, c0, true, &mut mid, &mut gate);
            }
        });
        b.play(&fwd, false);
        let forward = b.ops.len();
        b.play(&fwd, true);
        (b, forward, t, s, sy, ak, dirty)
    };
    let (old, old_forward, t, s, sy, ak, dirty) = build(false);
    let (new, new_forward, _, _, _, _, _) = build(true);
    let width = old.width() as usize;
    assert_eq!(width, new.width() as usize);
    for syv in [1usize, 16, 116, 119, 121, 125, 128] {
        let mut clean = vec![0u64; width];
        for (i, &q) in t.iter().chain(dirty.iter()).enumerate() {
            clean[q.0 as usize] = 0x6295_c58d_62b8_2175u64.rotate_left(((i * 9) % 64) as u32)
                                  ^ (i as u64).wrapping_mul(0x94d0_49bb_1331_11eb);
        }
        for (i, &q) in s.iter().take(syv + 1).enumerate() {
            clean[q.0 as usize] = 0xa076_1d64_78bd_642fu64.rotate_left(((i * 7) % 64) as u32);
        }
        clean[ak.0 as usize] = 0x69a5_c3f0_5969_a5c3;
        for (i, &q) in sy.iter().enumerate() {
            clean[q.0 as usize] = if (syv >> i) & 1 != 0 { u64::MAX } else { 0 };
        }
        let mut parked = clean.clone();
        for (i, &q) in s.iter().enumerate().skip(syv + 1) {
            parked[q.0 as usize] = 0x9e37_79b9_7f4a_7c15u64.rotate_left(((i * 13) % 64) as u32);
        }
        let a = run(&old.ops[..old_forward], width, &|q| *q = clean.clone());
        let b = run(&new.ops[..new_forward], width, &|q| *q = parked.clone());
        assert_eq!((a.phase, b.phase), (0, 0), "forward phase sy={syv}");
        for &q in t.iter().chain(s[..=syv].iter()) {
            assert_eq!(a.q[q.0 as usize], b.q[q.0 as usize], "data sy={syv} lane={}", q.0);
        }
        let cmp = (129 + 129 + 8 + 2) as usize;
        assert_eq!(a.q[cmp], b.q[cmp], "compare sy={syv}");
        for (label, circuit, input) in [("clean", &old, clean), ("parked", &new, parked)] {
            let rt = run(&circuit.ops, width, &|q| *q = input.clone());
            assert_eq!(rt.phase, 0, "round-trip phase {label} sy={syv}");
            assert_eq!(rt.q, input, "round-trip state {label} sy={syv}");
        }
    }
    eprintln!("B8B_DYNAMIC_CMP width={width} clean_t={} parked_t={} clean_ops={} parked_ops={}",
              old.tof, new.tof, old_forward, new_forward);
}

/// B8B V-form search uses the carry at sy, plus the carry at sy-1 on
/// the zero-headroom boundary. Both must be captured before dirty Q above Y.
#[cfg(test)]
#[test]
fn b8b_masked_v_compare_dynamic_sy_dirty_equivalence() {
    use super::frogdrop_col::rec;
    use super::tests_frogdrop::run;
    let build = |masked: bool| {
        let mut b = B::new();
        let t = b.alloc_n(129);
        let s = b.alloc_n(129);
        let sy = b.alloc_n(8);
        let ak = b.alloc();
        let pg = b.alloc();
        let c0 = b.alloc();
        let cmp = b.alloc();
        let m = b.alloc();
        let pre = b.alloc_n(7);
        let dirty = b.alloc_n(24);
        let fwd = rec(&mut b, |b| {
            if masked {
                b8b_ripple_early_carry(b, &t, &s, &sy, 1, 128, ak, c0, cmp, m,
                                       &pre, &[], &dirty, false, Some(pg));
            } else {
                let rd = s.clone();
                let mut mid = |b: &mut B| {
                    let lane = |v: usize| rd.get(v).copied();
                    read_lane(b, &sy, 1, 128, &lane, true, &[(ak, false)], cmp,
                              &pre, &[], &dirty);
                    let prior = |v: usize| v.checked_sub(1).and_then(|j| rd.get(j).copied());
                    read_lane(b, &sy, 1, 128, &prior, false, &[(ak, false), (pg, false)], cmp,
                              &pre, &[], &dirty);
                };
                let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| cmp);
                ripple(b, &t, &s, c0, false, &mut mid, &mut gate);
            }
        });
        b.play(&fwd, false);
        let forward = b.ops.len();
        b.play(&fwd, true);
        (b, forward, t, s, sy, ak, pg, cmp, dirty)
    };
    let (old, old_forward, t, s, sy, ak, pg, cmp, dirty) = build(false);
    let (new, new_forward, _, _, _, _, _, _, _) = build(true);
    let width = old.width() as usize;
    assert_eq!(width, new.width() as usize);
    for syv in [1usize, 16, 116, 119, 121, 125, 128] {
        let mut clean = vec![0u64; width];
        for (i, &q) in t.iter().chain(dirty.iter()).enumerate() {
            clean[q.0 as usize] = 0x6295_c58d_62b8_2175u64.rotate_left(((i * 9) % 64) as u32)
                                  ^ (i as u64).wrapping_mul(0x94d0_49bb_1331_11eb);
        }
        for (i, &q) in s.iter().take(syv + 1).enumerate() {
            clean[q.0 as usize] = 0xa076_1d64_78bd_642fu64.rotate_left(((i * 7) % 64) as u32);
        }
        clean[ak.0 as usize] = 0x69a5_c3f0_5969_a5c3;
        clean[pg.0 as usize] = 0xf0f0_a5a5_33cc_6699;
        for (i, &q) in sy.iter().enumerate() {
            clean[q.0 as usize] = if (syv >> i) & 1 != 0 { u64::MAX } else { 0 };
        }
        let mut parked = clean.clone();
        for (i, &q) in s.iter().enumerate().skip(syv + 1) {
            parked[q.0 as usize] = 0x9e37_79b9_7f4a_7c15u64.rotate_left(((i * 13) % 64) as u32)
                                  & !clean[pg.0 as usize];
        }
        let a = run(&old.ops[..old_forward], width, &|q| *q = clean.clone());
        let b = run(&new.ops[..new_forward], width, &|q| *q = parked.clone());
        assert_eq!((a.phase, b.phase), (0, 0), "forward phase sy={syv}");
        for &q in t.iter().chain(s[..=syv].iter()).chain([cmp].iter()) {
            assert_eq!(a.q[q.0 as usize], b.q[q.0 as usize], "data sy={syv} lane={}", q.0);
        }
        for (label, circuit, input) in [("clean", &old, clean), ("parked", &new, parked)] {
            let rt = run(&circuit.ops, width, &|q| *q = input.clone());
            assert_eq!(rt.phase, 0, "round-trip phase {label} sy={syv}");
            assert_eq!(rt.q, input, "round-trip state {label} sy={syv}");
        }
    }
    eprintln!("B8B_DYNAMIC_V_CMP width={width} clean_t={} parked_t={} clean_ops={} parked_ops={}",
              old.tof, new.tof, old_forward, new_forward);
}

/// Exact V-search counterexample: the special prior-carry branch requires a
/// write above sy even when every high source bit is clean zero.
#[cfg(test)]
#[test]
fn b8b_v_low_write_counterexample() {
    use super::frogdrop_col::rec;
    use super::tests_frogdrop::run;
    let build = |low_only: bool| {
        let mut b = B::new();
        let t = b.alloc_n(3);
        let s = b.alloc_n(3);
        let c0 = b.alloc();
        let cmp = b.alloc();
        let fwd = rec(&mut b, |b| {
            let mut mid = |b: &mut B| {
                b.x(s[1]); b.cx(s[1], cmp); b.x(s[1]);
                b.cx(s[0], cmp);
            };
            let mut gate = |_b: &mut B, i: Option<usize>| {
                i.and_then(|j| if !low_only || j <= 1 { Some(cmp) } else { None })
            };
            ripple(b, &t, &s, c0, false, &mut mid, &mut gate);
        });
        b.play(&fwd, false);
        let forward = b.ops.len();
        b.play(&fwd, true);
        (b, forward, t, s, cmp)
    };
    let (old, old_fwd, t, s, cmp) = build(false);
    let (masked, masked_fwd, _, _, _) = build(true);
    let width = old.width() as usize;
    let mut input = vec![0u64; width];
    input[t[1].0 as usize] = u64::MAX;
    input[s[1].0 as usize] = u64::MAX;
    let a = run(&old.ops[..old_fwd], width, &|q| *q = input.clone());
    let b = run(&masked.ops[..masked_fwd], width, &|q| *q = input.clone());
    assert_eq!((a.phase, b.phase), (0, 0));
    assert_eq!((a.q[t[0].0 as usize], a.q[t[1].0 as usize], a.q[t[2].0 as usize]),
               (0, 0, u64::MAX));
    assert_eq!((b.q[t[0].0 as usize], b.q[t[1].0 as usize], b.q[t[2].0 as usize]),
               (0, 0, 0));
    assert_eq!(a.q[cmp.0 as usize], u64::MAX);
    assert_eq!(b.q[cmp.0 as usize], u64::MAX);
    for &q in &s { assert_eq!(a.q[q.0 as usize], b.q[q.0 as usize]); }
    for circuit in [&old, &masked] {
        let rt = run(&circuit.ops, width, &|q| *q = input.clone());
        assert_eq!(rt.phase, 0);
        assert_eq!(rt.q, input);
    }
    eprintln!("B8B_V_LOW_WRITE_REFUTED sy=1 t=010 s=010 ak=1 prior=1 target_high_lane={} full={} low_only={}",
              t[2].0, a.q[t[2].0 as usize], b.q[t[2].0 as usize]);
}

/// Wide-band bridge: a reversible one-lane left shift in the sy-relative Q
/// window, with L=7 or 8 selected per shot. This is only the park boundary.
#[cfg(test)]
#[test]
fn b8b_wide_q_one_lane_bridge_dirty_passengers() {
    use super::frogdrop_col::rec;
    use super::tests_frogdrop::run;
    use std::collections::BTreeSet;
    let mut b = B::new();
    let q = b.alloc_n(128);
    let sy = b.alloc_n(8);
    let act = b.alloc();
    let l8 = b.alloc();
    let dirty = b.alloc_n(24);
    let care: BTreeSet<usize> = (0..=8).collect();
    let rot = rec(&mut b, |b| rot_by_range_care(b, &q, &sy, 1, 119, true, &dirty, &care));
    let fwd = rec(&mut b, |b| {
        b.play(&rot, false);
        for j in 0..7 { b.cswap(act, q[j], q[j + 1]); }
        super::mid2::mc_swap(b, &[(act, false), (l8, false)], q[7], q[8], &[], &dirty);
        b.play(&rot, true);
    });
    b.play(&fwd, false);
    let forward = b.ops.len();
    let forward_t = b.tof;
    b.play(&fwd, true);
    let width = b.width() as usize;
    let mut input = vec![0u64; width];
    let mut expected = vec![0u64; width];
    for shot in 0..64 {
        let syv = [96usize, 104, 110, 116, 117, 118, 119][shot % 7];
        let len = if syv <= 117 && shot % 3 == 0 { 8 } else { 7 };
        let active = shot % 5 != 0;
        for i in 0..128 {
            let bit = if i == syv || i == syv + len { false }
                      else { ((i * 0x9e37 + shot * 0x79b9 + (i ^ shot) * 13) >> 3) & 1 != 0 };
            if bit { input[q[i].0 as usize] |= 1 << shot; }
        }
        for i in 0..8 {
            if (syv >> i) & 1 != 0 { input[sy[i].0 as usize] |= 1 << shot; }
        }
        if len == 8 { input[l8.0 as usize] |= 1 << shot; }
        if active { input[act.0 as usize] |= 1 << shot; }
        for (i, &d) in dirty.iter().enumerate() {
            if (i * 17 + shot * 23) & 4 != 0 { input[d.0 as usize] |= 1 << shot; }
        }
    }
    expected.clone_from(&input);
    for shot in 0..64 {
        if (input[act.0 as usize] >> shot) & 1 == 0 { continue; }
        let syv: usize = (0..8).map(|i| (((input[sy[i].0 as usize] >> shot) & 1) as usize) << i).sum();
        let len = if (input[l8.0 as usize] >> shot) & 1 != 0 { 8 } else { 7 };
        for j in 0..len {
            let target = q[syv + j].0 as usize;
            let source = q[syv + j + 1].0 as usize;
            let bit = (input[source] >> shot) & 1;
            expected[target] = (expected[target] & !(1 << shot)) | (bit << shot);
        }
        expected[q[syv + len].0 as usize] &= !(1 << shot);
    }
    let out = run(&b.ops[..forward], width, &|v| *v = input.clone());
    assert_eq!(out.phase, 0);
    assert_eq!(out.q, expected);
    let rt = run(&b.ops, width, &|v| *v = input.clone());
    assert_eq!(rt.phase, 0);
    assert_eq!(rt.q, input);
    eprintln!("B8B_WIDE_Q_BRIDGE width={width} forward_t={forward_t} forward_ops={forward} shots=64");
}

/// Exact full-size threshold for L(g), including g>=32 where the six-bit V
/// gate register aliases and must not be used as the session selector.
#[cfg(test)]
#[test]
fn b8b_full_size_band_thresholds() {
    use super::frogdrop_col::rec;
    use super::tests_frogdrop::run;
    for threshold in [3usize, 6, 9, 12, 15, 18, 21] {
        let mut b = B::new();
        let sz = b.alloc_n(9);
        let sy = b.alloc_n(8);
        let zero = b.alloc();
        let carry = b.alloc();
        let flag = b.alloc();
        let dirty = b.alloc_n(24);
        let add = rec(&mut b, |b| super::frogdrop::reg_add_into(b, &sz, &sy, &[zero], carry));
        let sel = rec(&mut b, |b| {
            b.play(&add, false);
            b.x(flag);
            super::frogdrop_col::ge_const_compact(b, &sz, (258 - threshold) as isize,
                                                   flag, &[], &dirty);
            b.play(&add, true);
        });
        b.play(&sel, false);
        let forward = b.ops.len();
        let forward_t = b.tof;
        b.play(&sel, true);
        let width = b.width() as usize;
        let pairs: Vec<(usize, usize)> = (1..=128).flat_map(|syv| (syv..=256).map(move |szv| (syv, szv))).collect();
        for chunk in pairs.chunks(64) {
            let mut input = vec![0u64; width];
            let mut expected = vec![0u64; width];
            for (shot, &(syv, szv)) in chunk.iter().enumerate() {
                for i in 0..9 { if szv >> i & 1 != 0 { input[sz[i].0 as usize] |= 1 << shot; } }
                for i in 0..8 { if syv >> i & 1 != 0 { input[sy[i].0 as usize] |= 1 << shot; } }
                if szv + syv <= 257 && 257 - szv - syv >= threshold {
                    expected[flag.0 as usize] |= 1 << shot;
                }
            }
            for (i, &q) in dirty.iter().enumerate() {
                input[q.0 as usize] = 0x9e37_79b9_7f4a_7c15u64.rotate_left((i * 7) as u32);
            }
            for &q in sz.iter().chain(sy.iter()).chain(dirty.iter()) {
                expected[q.0 as usize] = input[q.0 as usize];
            }
            let out = run(&b.ops[..forward], width, &|q| *q = input.clone());
            assert_eq!(out.phase, 0, "forward phase threshold={threshold}");
            assert_eq!(out.q, expected, "forward all wires threshold={threshold}");
            let rt = run(&b.ops, width, &|q| *q = input.clone());
            assert_eq!(rt.phase, 0, "round-trip phase threshold={threshold}");
            assert_eq!(rt.q, input, "round-trip all wires threshold={threshold}");
        }
        eprintln!("B8B_BAND_THRESHOLD g>={threshold} states={} width={width} forward_t={forward_t} forward_ops={forward}", pairs.len());
    }
}

#[test]
fn b8b_tb_frame_round_and_all_wire_inverse() {
    use super::tests_frogdrop::run;
    for &(syv, g, j) in &[(1usize, 22usize, 0usize), (16, 15, 4),
                          (116, 23, 0), (117, 22, 4), (119, 19, 7),
                          (121, 15, 9), (124, 9, 3), (125, 7, 1),
                          (126, 5, 0), (127, 3, 1), (128, 1, 0)] {
        let tb = g.min(22);
        assert!(j <= tb);
        let kk = tb - j;
        let kf = 22 - j;
        let szv = 257 - syv - g;
        let mut a = B::new();
        let ar = a.alloc_n(259); let aq = a.alloc_n(129);
        let asz = a.alloc_n(8); let asy = a.alloc_n(8);
        let ac0 = a.alloc(); let ac = a.alloc(); let aak = a.alloc();
        let adirty = a.alloc_n(24);
        let mut b = B::new();
        let br = b.alloc_n(259); let bq = b.alloc_n(129);
        let bsz = b.alloc_n(8); let bsy = b.alloc_n(8);
        let bc0 = b.alloc(); let bc = b.alloc(); let bak = b.alloc();
        let bdirty = b.alloc_n(24);
        let frame = b8b_tb_frame(&mut b, &br, &bsz, &bsy, &bdirty);
        let span = 129;
        let t0: Vec<QubitId> = (0..span).map(|i| ar[258 - kk - i]).collect();
        let s0 = aq[..span].to_vec();
        let rd0 = s0.clone();
        let mut mid0 = |b: &mut B| {
            let lane = |v: usize| rd0.get(v).copied();
            read_lane(b, &asy, syv, syv, &lane, true, &[(aak, false)], ac, &[], &[], &adirty);
        };
        let mut gate0 = |_b: &mut B, i: Option<usize>| i.map(|_| ac);
        a.begin();
        ripple(&mut a, &t0, &s0, ac0, true, &mut mid0, &mut gate0);
        let ai = a.end();
        a.play(&ai, false);
        b.begin();
        b.play(&frame, false);
        let view: Vec<QubitId> = (0..259).map(|i| br[(i + 22) % 259]).collect();
        let t1: Vec<QubitId> = (0..span).map(|i| view[258 - kf - i]).collect();
        let s1 = bq[..span].to_vec();
        let rd1 = s1.clone();
        let mut mid1 = |b: &mut B| {
            let lane = |v: usize| rd1.get(v).copied();
            read_lane(b, &bsy, syv, syv, &lane, true, &[(bak, false)], bc, &[], &[], &bdirty);
        };
        let mut gate1 = |_b: &mut B, i: Option<usize>| i.map(|_| bc);
        ripple(&mut b, &t1, &s1, bc0, true, &mut mid1, &mut gate1);
        b.play(&frame, true);
        let bi = b.end();
        b.play(&bi, false);
        let af = a.ops.len(); let bf = b.ops.len();
        a.play(&ai, true); b.play(&bi, true);
        let width = a.width() as usize;
        assert_eq!(width, b.width() as usize);
        let mut input = vec![0u64; width];
        for (i, q) in ar.iter().chain(aq.iter()).chain(adirty.iter()).enumerate() {
            input[q.0 as usize] = 0x9e37_79b9_7f4a_7c15u64.rotate_left((i * 11 % 64) as u32);
        }
        for (i, &q) in aq.iter().enumerate() {
            if i >= syv { input[q.0 as usize] = 0; }
        }
        for (i, &q) in asz.iter().enumerate() { if (szv >> i) & 1 != 0 { input[q.0 as usize] = !0; } }
        for (i, &q) in asy.iter().enumerate() { if (syv >> i) & 1 != 0 { input[q.0 as usize] = !0; } }
        input[aak.0 as usize] = !0;
        let oa = run(&a.ops[..af], width, &|q| *q = input.clone());
        let ob = run(&b.ops[..bf], width, &|q| *q = input.clone());
        assert_eq!(oa.phase, 0, "natural phase sy={syv} g={g} j={j}");
        assert_eq!(ob.phase, 0, "frame phase sy={syv} g={g} j={j}");
        if oa.q != ob.q {
            let diff: Vec<_> = oa.q.iter().zip(ob.q.iter()).enumerate()
                .filter(|(_, (x, y))| x != y).map(|(i, (x, y))| (i, *x, *y)).take(8).collect();
            panic!("frame division sy={syv} g={g} j={j} first differences={diff:?}");
        }
        let ra = run(&a.ops, width, &|q| *q = input.clone());
        let rb = run(&b.ops, width, &|q| *q = input.clone());
        assert_eq!(ra.phase, 0); assert_eq!(rb.phase, 0);
        assert_eq!(ra.q, input); assert_eq!(rb.q, input);
        eprintln!("B8B_TB_FRAME sy={syv} g={g} j={j} T={} ops={}", b.tof, b.ops.len());
    }
}

#[test]
fn b8b_tb_code_exact_forward_inverse() {
    use super::tests_frogdrop::run;
    let mut b = B::new();
    let sz = b.alloc_n(8); let sy = b.alloc_n(8); let dirty = b.alloc_n(24);
    let code = rec(&mut b, |b| {
        super::arith::ttk_add(b, &sy, &sz, None, None);
        for &q in &sz { b.x(q); }
        super::modp_frogdrop::inc_dirty_free(b, &sz[1..], &dirty);
        for (a, z) in [(23, 54), (24, 86), (25, 118)] {
            b8b_transpose_const(b, &sz, a, z, &dirty);
        }
    });
    b.play(&code, false); let n = b.ops.len(); b.play(&code, true);
    for syv in [1usize, 16, 116, 128] {
        for g in 0..=25usize {
            let szv = 257 - syv - g;
            if szv > 255 { continue; }
            let mut input = vec![0u64; b.width() as usize];
            for (i, &q) in sz.iter().enumerate() { if szv >> i & 1 != 0 { input[q.0 as usize] = !0; } }
            for (i, &q) in sy.iter().enumerate() { if syv >> i & 1 != 0 { input[q.0 as usize] = !0; } }
            for (i, &q) in dirty.iter().enumerate() {
                input[q.0 as usize] = 0x9e37_79b9_7f4a_7c15u64.rotate_left((i * 9) as u32);
            }
            let out = run(&b.ops[..n], b.width() as usize, &|q| *q = input.clone());
            let got: usize = sz.iter().enumerate().map(|(i, &q)| ((out.q[q.0 as usize] & 1) as usize) << i).sum();
            let want = if g <= 22 { g } else { 22 + 32 * (g - 22) };
            assert_eq!(got, want, "sy={syv} g={g} sz={szv}");
            assert_eq!(out.phase, 0);
            let rt = run(&b.ops, b.width() as usize, &|q| *q = input.clone());
            assert_eq!(rt.q, input, "inverse sy={syv} g={g}");
            assert_eq!(rt.phase, 0);
        }
    }
}

#[test]
fn b8b_three_family_routes_early_gates_all_wire() {
    use super::tests_frogdrop::run;
    let cases: Vec<[usize; 6]> = include_str!("b8b_route_physical.tsv")
        .lines().map(|line| {
            let a: Vec<usize> = line.split_whitespace().map(|x| x.parse().unwrap()).collect();
            a.try_into().unwrap()
        }).collect();
    assert_eq!(cases.len(), 138);
    for family in 0..3u8 {
        let mut b = B::new();
        let a = b.alloc_n(8); let sy = b.alloc_n(8); let sx7 = b.alloc();
        let owners = [b.alloc(), b.alloc(), b.alloc()];
        let act = b.alloc(); let obs = b.alloc_n(3); let out = b.alloc_n(26);
        let dirty = b.alloc_n(24);
        let sg = rec(&mut b, |b| {
            let mut ax = sy[..7].to_vec(); ax.push(sx7);
            super::arith::ttk_add(b, &ax, &a, None, None);
            let zero: Vec<(QubitId, bool)> = sy[..7].iter().map(|&q| (q, true)).collect();
            mc_xor(b, &zero, a[7], &[], &dirty);
            for &q in &a { b.x(q); }
            super::modp_frogdrop::inc_dirty_free(b, &a[1..], &dirty);
        });
        let route = rec(&mut b, |b| b8b_route_family(b, family, &sy, &a, owners, None, None, &dirty));
        let u = rec(&mut b, |b| super::arith::ttk_add(b, &a[..7], &sy[..7], None, None));
        let gate = S1Gate::UPark { u: sy[..7].to_vec(), g: a[..5].to_vec(),
                                  dk: dirty[23], d2: dirty[22] };
        let wrapper = rec(&mut b, |b| {
            b.play(&sg, false);
            b.play(&route, false);
            for i in 0..3 { b.cx(owners[i], obs[i]); }
            b.play(&u, false);
            for j in 0..26 { s1_gate_u(b, &gate, j, act, out[j], &dirty); }
            b.play(&u, true);
            b.play(&route, true);
            b.play(&sg, false);
        });
        b.play(&wrapper, false); let forward = b.ops.len(); b.play(&wrapper, true);
        let width = b.width() as usize;
        for chunk in cases.iter().filter(|c| c[0] == family as usize).collect::<Vec<_>>().chunks(64) {
            let mut input = vec![0u64; width];
            for (shot, c) in chunk.iter().enumerate() {
                let (_, syv, g, x, q127, q126) = (c[0], c[1], c[2], c[3], c[4], c[5]);
                let szv = 257 - syv - g;
                for i in 0..8 {
                    if (szv >> i) & 1 != 0 { input[a[i].0 as usize] |= 1 << shot; }
                    if i < 7 && (syv >> i) & 1 != 0 { input[sy[i].0 as usize] |= 1 << shot; }
                }
                for (i, bit) in [x, q127, q126].into_iter().enumerate() {
                    if bit != 0 { input[owners[i].0 as usize] |= 1 << shot; }
                }
                input[act.0 as usize] |= 1 << shot;
            }
            for (i, &q) in dirty.iter().enumerate() {
                input[q.0 as usize] = 0x9e37_79b9_7f4a_7c15u64.rotate_left((i * 7) as u32);
            }
            let f = run(&b.ops[..forward], width, &|q| *q = input.clone());
            assert_eq!(f.phase, 0, "route forward phase family={family}");
            assert_eq!(f.q, input, "route owners/gates/restore family={family}");
            let rt = run(&b.ops, width, &|q| *q = input.clone());
            assert_eq!(rt.phase, 0);
            assert_eq!(rt.q, input, "route inverse family={family}");
        }
        eprintln!("B8B_ROUTE family={family} cases={} width={width} T={} ops={forward}",
                  cases.iter().filter(|c| c[0] == family as usize).count(), b.tof);
    }
}
