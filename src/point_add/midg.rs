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

/// F's top bits compared with W (the window has TC + 1 lanes: W's position 257 - sz, then F's TC positions)
pub const TC: usize = 32;

/// Paid head for the shared high-Z (SZ>=128) V form.
pub(crate) const HIGH_Z_K: usize = 30;

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
        cmp_csub_carries(b, &r[1..], &upper, r[0], s.f, &s.andc);
        b.x(r[0]);
        b.cx(s.f, r[0]);
        b.cx(r[0], s.f);
        b.x(s.f);
        // W += !f 2^(256 - sz - j): valid while that position is >= 0, i.e. sz <= 256 - j
        let bits = seg(win, 1 + j, s.sgn);
        if szr.1 + j >= 257 {
            let (g0, g1) = (s.gt[0], s.gt[1]);
            let rr = super::frogdrop_col::rec(b, |b| ge_const(b, sz, 257 - j as isize, g0, &s.chain));
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
pub fn stage1_v(b: &mut B, zh: &[QubitId], win: &[QubitId], sz: &[QubitId], szr: (usize, usize), s: &S1, act: QubitId,
                window: bool) -> Vec<G> {
    if s.r.len() == zh.len() {
        return stage1_v_compact(b, zh, win, sz, szr, s, act, window);
    }
    stage1_v_wide(b, zh, win, sz, szr, s, act, window)
}

/// Original official wide V form, retained unchanged for disjoint R/zero layouts.
pub(crate) fn stage1_v_wide(b: &mut B, zh: &[QubitId], win: &[QubitId], sz: &[QubitId], szr: (usize, usize), s: &S1, act: QubitId,
                window: bool) -> Vec<G> {
    let k = zh.len();
    assert_eq!(s.r.len(), k + 1);
    assert_eq!(win.len(), TC + 1);
    assert!(szr.1 <= 256 && szr.0 >= k + 33, "all-ones dividend needs s = sz - K >= 33");
    b.begin();
    let mut r = s.r.clone();
    for &x in &r[..k - 1] { b.x(x); }
    let mut upper: Vec<QubitId> = zh[1..].to_vec();
    upper.push(s.zero);
    for j in 0..TC {
        let top = r.pop().unwrap();
        r.insert(0, top);
        cmp_csub_carries(b, &r[1..], &upper, r[0], s.f, &s.andc);
        b.x(r[0]);
        b.cx(s.f, r[0]);
        b.cx(r[0], s.f);
        b.x(s.f);
        if !window { continue; }
        // V += act !f 2^(256 - sz - j) where that position is >= 0 (sz <= 256 - j)
        let bits: Vec<QubitId> = (1..=1 + j).rev().map(|i| win[i]).collect();
        let g0 = s.gt[0];
        if szr.1 + j >= 257 {
            let rr = super::frogdrop_col::rec(b, |b| {
                super::frogdrop_col::ge_const_compact(b, sz, 257 - j as isize, g0, &s.chain, &s.dirty)
            });
            b.play(&rr, false);
            if s.gt.len() == 1 {
                inc_with_controls(b, &bits, &[(act, false), (r[0], false), (g0, true)], &s.dirty);
            } else if s.gt.len() >= 3 {
                let g1 = s.gt[1];
                let g2 = s.gt[2];
                b.x(g0);
                b.and_c(act, g0, g2);
                b.and_c(r[0], g2, g1);
                inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
                b.and_u(r[0], g2, g1);
                b.and_u(act, g0, g2);
                b.x(g0);
            } else {
                let g1 = s.gt[1];
                // g1 = act & r0 & !g0 (dirty three-control toggles)
                mc_xor(b, &[(act, false), (r[0], false), (g0, true)], g1, &[], &s.dirty);
                inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
                mc_xor(b, &[(act, false), (r[0], false), (g0, true)], g1, &[], &s.dirty);
            }
            b.play(&rr, true);
        } else if s.gt.len() == 1 {
            inc_with_controls(b, &bits, &[(act, false), (r[0], false)], &s.dirty);
        } else {
            let g1 = s.gt[1];
            b.and_c(r[0], act, g1);
            inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
            b.and_u(r[0], act, g1);
        }
    }
    b.end()
}

/// Exact K-lane restoring recurrence. Win0/s.zero is not read here.
fn stage1_v_compact(b: &mut B, zh: &[QubitId], win: &[QubitId], sz: &[QubitId], szr: (usize, usize), s: &S1,
                    act: QubitId, window: bool) -> Vec<G> {
    let k = zh.len();
    assert_eq!(s.r.len(), k);
    assert!(k >= 2);
    assert_eq!(win.len(), TC + 1);
    assert!(szr.1 <= 256 && szr.0 >= k + 33, "all-ones dividend needs s = sz - K >= 33");
    b.begin();
    let mut r = s.r.clone();
    for &x in &r[..k - 1] { b.x(x); }
    for j in 0..TC {
        let top = r.pop().unwrap();
        b.cx(top, s.f);
        b.cx(s.f, top);
        r.insert(0, top);
        // New r[0] is zero. cmp_csub_carries XORs its compare into f,
        // then subtracts the high divisor iff the resulting f is set.
        // It permits a pre-existing f: no carry helper depends on f.
        cmp_csub_carries(b, &r[1..], &zh[1..], r[0], s.f, &s.andc);
        b.x(r[0]);
        b.cx(s.f, r[0]);
        b.cx(r[0], s.f);
        b.x(s.f);
        if !window { continue; }
        let bits: Vec<QubitId> = (1..=1 + j).rev().map(|i| win[i]).collect();
        let g0 = s.gt[0];
        if szr.1 + j >= 257 {
            let rr = super::frogdrop_col::rec(b, |b| {
                super::frogdrop_col::ge_const_compact(b, sz, 257 - j as isize, g0, &s.chain, &s.dirty)
            });
            b.play(&rr, false);
            if s.gt.len() == 1 {
                inc_with_controls(b, &bits, &[(act, false), (r[0], false), (g0, true)], &s.dirty);
            } else if s.gt.len() >= 3 {
                let (g1, g2) = (s.gt[1], s.gt[2]);
                b.x(g0);
                b.and_c(act, g0, g2);
                b.and_c(r[0], g2, g1);
                inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
                b.and_u(r[0], g2, g1);
                b.and_u(act, g0, g2);
                b.x(g0);
            } else {
                let g1 = s.gt[1];
                mc_xor(b, &[(act, false), (r[0], false), (g0, true)], g1, &[], &s.dirty);
                inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
                mc_xor(b, &[(act, false), (r[0], false), (g0, true)], g1, &[], &s.dirty);
            }
            b.play(&rr, true);
        } else if s.gt.len() == 1 {
            inc_with_controls(b, &bits, &[(act, false), (r[0], false)], &s.dirty);
        } else {
            let g1 = s.gt[1];
            b.and_c(r[0], act, g1);
            inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
            b.and_u(r[0], act, g1);
        }
    }
    b.end()
}

/// Same exact compact recurrence, with extra quantum literals only on
/// window increments. FV/FR use identical unconditional R evolution, so
/// paired playback returns arbitrary R DATA when the predicate is false.
pub(crate) fn stage1_v_compact_controlled(b: &mut B, zh: &[QubitId], win: &[QubitId], sz: &[QubitId], szr: (usize, usize), s: &S1,
                    act: QubitId, window: bool, extra: &[(QubitId, bool)]) -> Vec<G> {
    let k = zh.len();
    assert_eq!(s.r.len(), k);
    assert!(k >= 2);
    assert_eq!(win.len(), TC + 1);
    assert!(szr.1 <= 256 && szr.0 >= k + 33, "all-ones dividend needs s = sz - K >= 33");
    assert_eq!(s.gt.len(), 1, "controlled Q695 compact form uses the returned SX0 flag");
    assert!(!extra.iter().any(|(q, _)| s.r.contains(q) || zh.contains(q)
        || win.contains(q) || *q == s.f || *q == act || s.andc.contains(q)
        || s.chain.contains(q) || s.anc.contains(q) || s.dirty.contains(q)));
    b.begin();
    let mut r = s.r.clone();
    for &x in &r[..k - 1] { b.x(x); }
    for j in 0..TC {
        let top = r.pop().unwrap();
        b.cx(top, s.f);
        b.cx(s.f, top);
        r.insert(0, top);
        // New r[0] is zero. cmp_csub_carries XORs its compare into f,
        // then subtracts the high divisor iff the resulting f is set.
        // It permits a pre-existing f: no carry helper depends on f.
        cmp_csub_carries(b, &r[1..], &zh[1..], r[0], s.f, &s.andc);
        b.x(r[0]);
        b.cx(s.f, r[0]);
        b.cx(r[0], s.f);
        b.x(s.f);
        if !window { continue; }
        let bits: Vec<QubitId> = (1..=1 + j).rev().map(|i| win[i]).collect();
        let mut controls = vec![(act, false), (r[0], false)];
        controls.extend_from_slice(extra);
        if szr.1 + j >= 257 {
            let g0 = s.gt[0];
            let rr = super::frogdrop_col::rec(b, |b| {
                super::frogdrop_col::ge_const_compact(b, sz, 257 - j as isize, g0, &s.chain, &s.dirty)
            });
            b.play(&rr, false);
            controls.push((g0, true));
            inc_with_controls(b, &bits, &controls, &s.dirty);
            b.play(&rr, true);
        } else {
            inc_with_controls(b, &bits, &controls, &s.dirty);
        }
    }
    b.end()
}

// A V-form whose quotient reserve occupies every possible clean gate lane
// uses the dirty-lane multi-control primitive directly. Visit high bits
// first so each prefix sees the original lower bits of the window.
fn inc_with_controls(b: &mut B, bits: &[QubitId], ctl: &[(QubitId, bool)], dirty: &[QubitId]) {
    for i in (0..bits.len()).rev() {
        let mut lits = ctl.to_vec();
        lits.extend(bits[..i].iter().copied().map(|q| (q, false)));
        mc_xor(b, &lits, bits[i], &[], dirty);
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

/// Scheme G: lanes appended to the column pool (FD_MIDG; the lean middle uses none of them)
pub const EXTRA: usize = 0;

/// Scheme G replaces the rho middle (FD_MIDG=1 / MIDG_ON)
pub const MIDG_ON: bool = true;
pub fn enabled() -> bool {
    MIDG_ON || std::env::var("FD_MIDG").is_ok()
}

/// Stage 5 (HT division) in place on the 13 lanes and sx (false: the headroom division)
pub const G_IP5: bool = false;

/// crossing reserve: lanes of the parking cycle beyond Q + x128 (MIDG_RES overrides; fewer if the pool lacks them)
/// The V-form increments directly under its controls, freeing sx[1] for the crossing cycle.
pub const PARK_RES: usize = 8;
pub fn park_reserve() -> usize {
    std::env::var("MIDG_RES").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(PARK_RES)
}

/// Gate register v = (sz + sy + 38) mod 64 = s9 - 218 for s9 = sz + sy in [218, 281]: bit kb of q can be set only if
/// kb < 258 - s9, i.e. v <= 39 - kb (a shot with s9 < 218 has q >= 2^40: a capped failure either way).
const VB: usize = 6;
const VOFF: usize = 38;

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

/// Exact production quotient park, including arbitrary inactive and wrapped DATA.
#[allow(clippy::too_many_arguments)]
pub(crate) fn park_quotient_record(b: &mut B, ring: &[QubitId], sz: &[QubitId], szr: (usize, usize),
    sy: &[QubitId], syhi: usize, a: QubitId, qloc: &[QubitId], q129: &[QubitId], rq: &[Gate],
    wf: QubitId, dirty: &[QubitId]) -> Vec<Gate> {
    assert!(!qloc.contains(&wf) && !q129.contains(&wf) && !ring.contains(&wf));
    let ds = (0..qloc.len()).collect();
    let rz = rec(b, |b| rot_by_range_care(b, ring, sz, szr.0, szr.1, true, dirty, &ds));
    rec(b, |b| {
        b.play(&rz, false);
        b.play(rq, false);
        for kb in 0..qloc.len() {
            if syhi.min(128) + kb >= q129.len() {
                let wrap = |b: &mut B| super::frogdrop_col::ge_const_compact(b, sy,
                    (q129.len() - kb) as isize, wf, &[], dirty);
                wrap(b);
                // Exact dirty-lane guarded swap: no clean conjunction owner.
                super::mid2::mc_swap(b, &[(a, false), (wf, true)],
                    qloc[kb], q129[kb], &[], dirty);
                wrap(b);
            } else {
                super::mid2::mc_swap(b, &[(a, false)], qloc[kb], q129[kb], &[], dirty);
            }
        }
        b.play(rq, true);
        b.play(&rz, true);
    })
}

/// Exact [SY < bound] controlled swap with no clean wrap flag. The
/// disjoint most-significant-difference prefixes implement the inequality
/// on every basis value, including inactive arbitrary DATA and SY0.
pub(crate) fn swap_sy_lt(b: &mut B, sy: &[QubitId], bound: usize, act: QubitId,
    x: QubitId, y: QubitId, dirty: &[QubitId]) {
    assert!(!sy.contains(&act) && !sy.contains(&x) && !sy.contains(&y));
    if bound == 0 { return; }
    if bound >= 1usize << sy.len() {
        super::mid2::mc_swap(b, &[(act, false)], x, y, &[], dirty);
        return;
    }
    for i in (0..sy.len()).rev() {
        if bound >> i & 1 == 0 { continue; }
        let mut ct = vec![(act, false)];
        for j in (i + 1..sy.len()).rev() { ct.push((sy[j], bound >> j & 1 == 0)); }
        ct.push((sy[i], true));
        super::mid2::mc_swap(b, &ct, x, y, &[], dirty);
    }
}

/// Exact leading-one loan during the production park. On active shots SY is
/// the bit length of nonzero Y in Q, so its leading bit Q[SY-1] is known one.
/// Toggle that bit to zero, then park at SY-1 rather than SY. This frees one
/// place without adding a wire or changing the reciprocal precision/reserve.
/// The returned record is NOT an involution: the caller must replay its true
/// inverse after the parked body. Inactive arbitrary DATA is unchanged.
#[allow(clippy::too_many_arguments)]
pub(crate) fn park_quotient_normalized_record(b: &mut B, ring: &[QubitId], sz: &[QubitId],
    szr: (usize, usize), sy: &[QubitId], syhi: usize, a: QubitId,
    qloc: &[QubitId], q129: &[QubitId], rq: &[Gate], wf: QubitId,
    dirty: &[QubitId]) -> Vec<Gate> {
    assert!(q129.len() > 128 && qloc.len() < q129.len());
    // wf is retained as an API identity only. SX0 now stores q23 outside
    // paired V forms; the exact inequality swaps use no wrap scratch.
    assert!(!q129.contains(&wf) && !ring.contains(&wf));
    assert!(!q129.contains(&a) && !sy.contains(&a) && a != wf);
    assert!(!qloc.iter().any(|q| q129.contains(q)));
    assert!(!ring.iter().any(|q| q129.contains(q)));
    assert!(!sz.iter().any(|q| q129.contains(q)));
    assert!(!sy.iter().any(|q| q129.contains(q) || qloc.contains(q)));
    let ds = (0..qloc.len()).collect();
    let rz = rec(b, |b| rot_by_range_care(b, ring, sz, szr.0, szr.1, true, dirty, &ds));
    let qlen = q129.len();
    rec(b, |b| {
        b.play(&rz, false);
        b.play(rq, false);
        // RQ's protected last target is original Q[SY-1]. All active
        // parks have 1<=SY<=128 and nonzero Y, so this leading bit is1.
        // First-HT stage2 has already probed current Y, not old X.
        // Done/delayed no-step shots have a=0; their DATA is untouched.
        b.cx(a, q129[qlen - 1]);
        for kb in 0..qloc.len() {
            let target = q129[(kb + qlen - 1) % qlen];
            if syhi.min(128) + kb >= qlen + 1 {
                swap_sy_lt(b, sy, qlen + 1 - kb, a, qloc[kb], target, dirty);
            } else {
                super::mid2::mc_swap(b, &[(a, false)], qloc[kb], target, &[], dirty);
            }
        }
        b.play(rq, true);
        b.play(&rz, true);
    })
}

/// Shared HR/HT high-Z precision without a public-bank owner. On active
/// SZ>=128, eligible normalized q storage has index<=256-SZ<=128. The six
/// reserve owners at indices129..134 are returned before each paired V body:
/// SX1/SX5/SX6/SX7 and the C0/PZERO adder roles. Low-Z shots retain their
/// original bank-funded R24/R25. FV/FR returns arbitrary low/inactive DATA.
#[allow(clippy::too_many_arguments)]
pub(crate) fn highz_vform_record(b: &mut B, ring: &[QubitId], sz: &[QubitId],
    szr: (usize, usize), win: &[QubitId], base: &S1, act: QubitId,
    sx: &[QubitId], prot: &[Gate], extra_r: &[QubitId]) -> Vec<Gate> {
    assert_eq!(ring.len(), 279);
    assert_eq!(sx.len(), 8);
    assert!((24..=25).contains(&base.r.len()));
    assert_eq!(extra_r.len(), HIGH_Z_K - 24);
    assert_eq!(&extra_r[..4], &[sx[1], sx[5], sx[6], sx[7]]);
    assert!(!extra_r[4..].iter().any(|q| sx.contains(q)));
    let base_zh = &ring[ring.len() - base.r.len()..];
    if szr.1 < 128 {
        let fv = stage1_v(b, base_zh, win, sz, szr, base, act, true);
        let fr = stage1_v(b, base_zh, win, sz, szr, base, act, false);
        return rec(b, |b| {
            b.play(prot, false); b.play(&fv, false); b.play(&fr, true); b.play(prot, true);
        });
    }
    let split = szr.0 < 128;
    assert!(!split || (sz.len() == 8 && szr.1 <= 255), "only the public eight-bit SZ interval crosses128");
    let high_ctl = if split { vec![(sz[7], false)] } else { vec![] };
    let low_ctl = if split { vec![(sz[7], true)] } else { vec![] };
    let mut high = base.clone();
    high.r = ring[..22].to_vec();
    high.r.extend([sx[2], sx[3]]);
    high.r.extend_from_slice(extra_r);
    let high_zh = &ring[ring.len() - HIGH_Z_K..];
    assert_eq!(high.r.len(), HIGH_Z_K);
    assert_eq!(high.r.iter().copied().collect::<std::collections::BTreeSet<_>>().len(), HIGH_Z_K);
    assert!(!high.r.iter().any(|q| high_zh.contains(q) || win[1..].contains(q)
        || *q == act || high.gt.contains(q) || high.andc.contains(q)
        || high.chain.contains(q) || high.anc.contains(q) || high.dirty.contains(q)
        || sz.contains(q)));
    assert!(high.r.contains(&win[0]));
    let fh = stage1_v_compact_controlled(b, high_zh, win, sz, szr, &high, act, true, &high_ctl);
    let rh = stage1_v_compact_controlled(b, high_zh, win, sz, szr, &high, act, false, &high_ctl);
    let low = if split {
        Some((stage1_v_compact_controlled(b, base_zh, win, sz, szr, base, act, true, &low_ctl),
              stage1_v_compact_controlled(b, base_zh, win, sz, szr, base, act, false, &low_ctl)))
    } else { None };
    rec(b, |b| {
        b.play(prot, false);
        if let Some((fl, rl)) = &low { b.play(fl, false); b.play(rl, true); }
        b.play(&fh, false);
        b.play(&rh, true);
        b.play(prot, true);
    })
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
    assert!(cp.h >= k + 2, "the window starts at lane K + 1 of the test frame: ring headroom K + 2");
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
    // Vform may run with quotient bits parked above Y. The exact paired
    // care rotation maps parked Q bits back to index sy-1+kb; the old
    // public bank bound sy+kb stays conservative, for
    // kb < kmax; reserve bits above Q remain outside this bank. Keep the
    // entire public support, the old Y/done support and the live counter.
    // Preserve the original public clean bank. The normalized extra
    // q23 slot SY+22 lies below the old conservative SYhi+23 boundary.
    let bank_kmax = bmax.min(super::pointadd_frogdrop::QB).min(mt);
    let p_bank_lo = lsb.max(cp.sy.1.min(nq) + bank_kmax);
    let mut p_bank = if p_bank_lo < loan_end { q[p_bank_lo..loan_end].to_vec() } else { vec![] };
    assert!(!p_bank.iter().any(|q| dirty.contains(q) || ring.contains(q) || sx.contains(q)
        || sc.sz.contains(q) || [act, c0, x128, pzero, ph, sc.sw].contains(q)));
    // N279/pool12 retains the base K24 head and pays for a TC32 window.
    // Compact R24 leases ring[0..22], including Win0=ring21, plus SX2/3.
    // FV only increments Win[1..]; paired FV/FR returns arbitrary inactive
    // Win0/R DATA exactly. Act stays on SX4, outside R and every reserve.
    let precision24 = k == 20 && n == 279 && nq == 128 && sx.len() == 8
        && dirty.len() == 259 && cp.h == 22
        && cp.sz.0 >= 57 && cp.sz.1 <= 256;
    assert!(!MIDG_ON || precision24, "official696 K24 geometry with paid TC32 window must be retained");
    assert!(!precision24 || sc.g == sx[4], "Q695 middle requires the pool12 SX4 act carve");
    // Paid precision uses one globally returned Q-bank owner whenever
    // the existing public-support bank is nonempty. It becomes R's25th
    // lane and leaves every clean compare/decoder/increment bank until
    // paired FV/FR returns it. Empty banks keep exactly the K24 path.
    // This policy uses only source geometry, never a shot/nonce/outcome.
    let paid_r = if precision24 { p_bank.pop() } else { None };
    if let Some(rq) = paid_r {
        assert!(q.contains(&rq) && (!cp.dn || !fd.cnt.contains(&rq))
            && !p_bank.contains(&rq) && !ring.contains(&rq) && !sx.contains(&rq)
            && !dirty.contains(&rq) && !sc.sz.contains(&rq)
            && ![act, c0, x128, pzero, ph, sc.sw].contains(&rq));
    }
    let top_head = if precision24 { 24 + usize::from(paid_r.is_some()) } else { k };
    // High-Z HR/HT leases six returned reserve owners for its30-bit head.
    // Protect the union
    // of that head and the unchanged low-Z K24/K25 destinations.
    let protect_head = if (cp.hr || cp.ht) && cp.sz.1 >= 128 { top_head.max(HIGH_Z_K) } else { top_head };

    // ---- recordings
    let dest_r: std::collections::BTreeSet<usize> = (0..k + 2 + TC).chain(n - protect_head..n).collect();
    let prot = rec(b, |b| rot_by_range_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty, &dest_r));
    // ring down by sz caring for the P-frame lanes `d` (24 = X's position 257 - sz, kb < 24 = headroom bit kb)
    let rotz = |b: &mut B, d: &[usize]| -> Vec<Gate> {
        let ds: std::collections::BTreeSet<usize> = d.iter().copied().collect();
        rec(b, |b| rot_by_range_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty, &ds))
    };
    // Win0 is a returned R owner only inside paired FV/FR. It is zero
    // on active V entry/exit; inactive arbitrary DATA cancels in that pair.
    // The six extra high-Z R owners are returned inside each paired body.
    // They stay outside the external quotient owners. The reserve, carry,
    // HR read/pad and HT decision roles use them only between completed
    // FV/FR pairs. HT's final inverse V requires the exact reverse search
    // to have erased its in-flight c/SX7 before that owner joins R.
    let high_r_extra = [sx[1], sx[5], sx[6], sx[7], c0, pzero];
    assert!(!high_r_extra.iter().any(|q| sc.sz.contains(q) || *q == act
        || *q == ph || *q == x128 || dirty.contains(q)));
    let mut reciprocal_r = ring[0..k + 1 + usize::from(precision24)].to_vec();
    if precision24 { reciprocal_r.extend([sx[2], sx[3]]); }
    if let Some(rq) = paid_r { reciprocal_r.push(rq); }
    let mut p_gt = if precision24 { vec![sx[0]] } else { sx[2..4].to_vec() };
    if !precision24 { if let Some(&third) = p_bank.first() { p_gt.push(third); } }
    let zh: Vec<QubitId> = ring[n - top_head..n].to_vec();
    if precision24 {
        assert!((24..=25).contains(&top_head));
        assert_eq!(reciprocal_r.len(), top_head);
        let unique: std::collections::BTreeSet<QubitId> = reciprocal_r.iter().copied().collect();
        assert_eq!(unique.len(), reciprocal_r.len());
        assert!(!reciprocal_r.iter().any(|q| zh.contains(q)
            || p_gt.contains(q) || *q == act
            || dirty.contains(q) || p_bank.contains(q) || sc.sz.contains(q)
            || [c0, x128, pzero, ph, sc.sw].contains(q)
            || sx.iter().enumerate().any(|(i, x)| i != 2 && i != 3 && x == q)));
        assert_eq!(p_gt[0], sx[0]);
        assert!(!zh.iter().any(|q| sx.contains(q) || sc.sz.contains(q)
            || [ring[k + 1], act, c0, x128, pzero, ph, sc.sw].contains(q)
            || dirty.contains(q) || p_bank.contains(q)));
        assert_eq!(k + 1, 21);
        assert!(reciprocal_r.contains(&ring[k + 1]));
        assert!(!reciprocal_r.iter().any(|q| ring[k + 2..k + 2 + TC].contains(q)));
        assert!(!paid_r.is_some_and(|rq| p_bank.contains(&rq)
            || zh.contains(&rq) || p_gt.contains(&rq)));
    }
    let s1 = S1 { r: reciprocal_r, f: sx[0], zero: ring[k + 1], sgn: sx[0], gt: p_gt,
                  anc: p_bank.iter().skip(1).copied().collect(),
                  andc: p_bank.clone(), chain: p_bank,
                  dirty: dirty.clone() };
    let win: Vec<QubitId> = ring[k + 1..k + 2 + TC].to_vec();
    let szr = (cp.sz.0, cp.sz.1);
    // Enter / leave the shared high/low V form on the act shots. Every
    // FV/FR pair returns R before the next size predicate or park helper.
    let vform = highz_vform_record(b, &ring, &sc.sz, szr, &win, &s1, act, &sx, &prot, &high_r_extra);
    // The three physical quotient donors are globally returned before R
    // reclaims them; no live donor enters a clean decoder/helper bank.
    let external_q = |kb: usize| if precision24 && kb == k + 1 { Some(sx[3]) }
                         else if precision24 && kb == k + 2 { Some(sx[2]) }
                         else if precision24 && kb == k + 3 { Some(sx[0]) } else { None };
    assert!(!precision24 || (k + 1 == 21 && qf == 24 && kmax <= 24));
    let external_owners: std::collections::BTreeSet<QubitId> =
        (0..qf).filter_map(external_q).collect();
    assert!(!external_owners.contains(&act) && !external_owners.contains(&sx[5]));
    let qloc = |kb: usize| external_q(kb).unwrap_or(ring[kb]);
    assert!((0..kmax).all(|kb| qloc(kb) != ring[k + 1]));
    // Paid extra quotient bit only for SZ>=128. Low-Z retains the
    // original23-bit license and delayed-half139 bound. C0's9-bit
    // interval is public fixed high; all split intervals end at255.
    let extra_q_high = cp.sz.0 < 128;
    assert!(!extra_q_high || (sc.sz.len() == 8 && cp.sz.1 <= 255));
    let actor_temps: Vec<QubitId> = sx[..2].iter().copied()
        .filter(|q| !external_owners.contains(q)).collect();
    // v = (sz + sy + VOFF) mod 2^VB, in SZ only during ge_k.
    let v: Vec<QubitId> = sc.sz[..VB].to_vec();
    let vg = rec(b, |b| {
        super::frogdrop::reg_add_into(b, &v, &fd.sy[..VB], &[], c0);
        for i in 0..VB {
            if (VOFF >> i) & 1 == 1 { super::modp_frogdrop::inc_dirty_free(b, &v[i..], &dirty); }
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
        ge_k(b, kb, c);
        b.x(c);
        if kb == 23 && extra_q_high {
            mc_xor(b, &[(a, false), (c, false), (sc.sz[7], false)], ak, &[], &dirty);
        } else { b.and_c(a, c, ak); }
        b.x(c);
        ge_k(b, kb, c);
        super::f1_profile("midg.gate_on", f1, b.tof);
    };
    let gate_off = |b: &mut B, kb: usize, a: QubitId| {
        let f1 = b.tof;
        ge_k(b, kb, c);
        b.x(c);
        if kb == 23 && extra_q_high {
            mc_xor(b, &[(a, false), (c, false), (sc.sz[7], false)], ak, &[], &dirty);
        } else { b.and_u(a, c, ak); }
        b.x(c);
        ge_k(b, kb, c);
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
        let r = rotz(b, &[k + 1, kb]);
        b.play(&r, false);
        if undo {
            mc_xor(b, &[(ak, false), (qloc(kb), true)], rv, &[], &dirty);
        } else {
            mc_xor(b, &[(ak, false), (ring[k + 1], false)], rv, &[], &dirty);
            mc_xor(b, &[(ak, false), (ring[k + 1], true)], qloc(kb), &[], &dirty);
        }
        b.play(&r, true);
        super::f1_profile("midg.decide", f1, b.tof);
    };
    // headroom (P-frame lane kb) <-> Q above Y (Q + x128 + the crossing reserve, down by sy: lane kb) where bit kb can
    // be set; v live
    // Q's extension beyond lane 128 (the crossing step's bits): the lanes idle while the V form is entered or left
    // (c0, the P zero, sx[1] and sx[6..8]), then the park's own flag lanes that are constant on its act shots (`extra`: ph,
    // and sw or g, whichever does not hold act; ph reads 1 on HT act shots and is flipped around the window), then
    // the pool past the 13-lane layout; MIDG_RES lanes in all
    let nres = park_reserve();
    let mk_cycle = |b: &mut B, extra: &[QubitId], ht: bool| -> (Vec<QubitId>, Vec<Gate>) {
        let mut q129: Vec<QubitId> = q.clone();
        q129.push(x128);
        let mut reserve: Vec<QubitId> = vec![c0, pzero, sx[1], sx[5], sx[6], sx[7]];
        reserve.extend(extra.iter().copied().filter(|x| !sc.sz.contains(x)));
        reserve.extend(&sc.gx);
        reserve.truncate(nres);
        // (an HR park needs no reserve: sy + bl(q) <= 129 there)
        assert!(!MIDG_ON || !ht || reserve.len() == nres, "crossing reserve: {} of {} lanes", reserve.len(), nres);
        q129.extend(&reserve);
        // The normalized park reads target kb-1 (including the last lane
        // for q0), so its care rotation must protect those exact targets.
        let d24: std::collections::BTreeSet<usize> = (0..kmax)
            .map(|kb| (kb + q129.len() - 1) % q129.len()).collect();
        let rq = rec(b, |b| rot_by_range_care(b, &q129, &fd.sy, cp.sy.0.min(128), cp.sy.1.min(128), true, &dirty, &d24));
        (q129, rq)
    };
    // HR block and HT block (act on g): ph and sw are 0 / (1, 0) on their act shots; HT division (act on sw): ph, g
    let (q129a, rqa) = mk_cycle(b, &[ph, sc.sw], cp.ht);
    let (q129b, rqb) = mk_cycle(b, &[ph, act], cp.ht);
    // Normalized Q-cycle index sy-1+kb can wrap onto Y. Such a bit beyond
    // the reserve stays in headroom; the swap is gated by sy <= len-kb.
    // For kb >= B both lanes are zero on licensed act shots. The park
    // uses exact SY-prefix guards, so SX0 can carry q23 outside the park.
    // During a payload park it has returned and may own the read-wrap flag.
    let wf = sx[0];
    let wrap_flag = |b: &mut B, kb: usize, qlen: usize| {
        super::frogdrop_col::ge_const_compact(b, &fd.sy, (qlen + 1 - kb) as isize, wf, &[], &dirty);
    };
    let quotient_locs: Vec<QubitId> = (0..kmax).map(qloc).collect();
    let park_for = |b: &mut B, a: QubitId, q129: &[QubitId], rq: &[Gate]|
        park_quotient_normalized_record(b, &ring, &sc.sz, cp.sz, &fd.sy, cp.sy.1, a,
            &quotient_locs, q129, rq, wf, &dirty);
    let park = park_for(b, act, &q129a, &rqa);
    let hr_lits = { let mut l = vec![(ph, true)]; if cp.sw { l.push((sc.sw, true)); } l };
    // ---------------- HR: binary search in the V form, q's bits parked in the ring headroom
    if cp.hr {
        mc_xor(b, &hr_lits, act, &[], &dirty);
        let f1 = b.tof;
        b.play(&vform, false);
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
        b.play(&park, false);
        let f1 = b.tof;
        b.play(&vform, true);
        super::f1_profile("midg.vform", f1, b.tof);
        b.play(&park, true);
        mc_xor(b, &hr_lits, act, &[], &dirty);
    }
    if !stage(b) { return; } // 3
    if cp.hr {
        // D^-1: X = t_{j-1} < t_j grows to t_{j+1}, consuming q's bits LSB first (tt: run on X - 1)
        let xl: Vec<QubitId> = (0..mt).map(|m| ring[n - 1 - m]).collect();
        let dec1 = if cp.tt { Some(rec(b, |b| super::modp_frogdrop::inc_dirty(b, &xl, &dirty, c0))) } else { None };
        if let Some(d) = &dec1 { b.play(d, true); }
        let (sylo, syhi) = (cp.sy.0.max(1), cp.sy.1.min(nq));
        // the post region's positions [0, 259 - bl(r_j)): a delayed shot's r_j < 2^l0 widens it to 259 - dlr; Q's
        // pad: lanes zero on the written (HR stepping) shots, the carry past them by trans_one's increment
        let wtop = 259 - if cp.dl { cp.dlr.min(L0P + 1) } else { L0P + 1 };
        // SX5 is now the globally returned payload/read helper. Shorten
        // the known-zero source padding by one lane; trans_one propagates
        // the exact carry through the unchanged longer target tail.
        let pads: Vec<QubitId> = if cp.dl { vec![x128, pzero, sx[1], sx[6], sc.sw, ph] }
                                 else { vec![x128, pzero] };
        let slen = wtop.min(nq + pads.len());
        let src = if pl.is_some() { super::payload::pad(&fd.q, &pads, slen) } else { vec![] };
        mc_xor(b, &hr_lits, act, &[], &dirty);
        for kk in 0..kmax {
            fetch(b, kk, &[(act, false)]);
            if std::env::var_os("D3_TRACE_PHASE").is_some() && kk + 1 == kmax { super::frogdrop_col::mark(b, 1400); }
            if let Some(pl) = pl {
                let t: Vec<QubitId> = (kk..wtop).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                let sl = (wtop - kk).min(slen);
                super::payload::trans_one(b, &t, &src[..sl], kk, false, vec![(c, false)], None, sx[5], c0, &[],
                                          &pl.dirty);
                super::frogdrop_col::mark(b, 1000 + kk);
            }
            add(b, kk, c, false);
            if std::env::var_os("D3_TRACE_PHASE").is_some() && kk + 1 == kmax { super::frogdrop_col::mark(b, 1402); }
            if precision24 {
                ge_k(b, kk, sx[5]);
                b.x(sx[5]);
                b.and_c(act, sx[5], ak);
                b.x(sx[5]);
                ge_k(b, kk, sx[5]);
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
                let read_pre = if precision24 { vec![sx[5], sx[1], pzero] }
                               else { vec![sx[0], sx[1], sx[2], sx[6], pzero] };
                assert!(!read_pre.iter().any(|q| external_owners.contains(q) || *q == act || *q == ak));
                if std::env::var_os("D3_TRACE_PHASE").is_some() && kk + 1 == kmax { super::frogdrop_col::mark(b, 1404); }
                read_lane(b, &fd.sy, sylo, syhi, &lane, true, &[(if precision24 { ak } else { act }, false)], c, &read_pre, &[], &dirty);
                if std::env::var_os("D3_TRACE_PHASE").is_some() && kk + 1 == kmax { super::frogdrop_col::mark(b, 1405); }
            };
            let mut gate = |_b: &mut B, _i: Option<usize>| None;
            ripple(b, &tl, &s, c0, true, &mut mid, &mut gate);
            if precision24 {
                ge_k(b, kk, sx[5]);
                b.x(sx[5]);
                b.and_u(act, sx[5], ak);
                b.x(sx[5]);
                ge_k(b, kk, sx[5]);
            }
            if std::env::var_os("D3_TRACE_PHASE").is_some() && kk + 1 == kmax { super::frogdrop_col::mark(b, 1403); }
        }
        mc_xor(b, &hr_lits, act, &[], &dirty);
        if let Some(d) = &dec1 { b.play(d, false); }
    }
    if !stage(b) { return; } // 4
    // ---------------- HT: in-place restoring division (mid2): q_k at X-index sy + k, X = r_{j+1}, the payload add
    // U += q |t_j| fused per bit (FD_MIDG_OLD5=1: the headroom division and the parked payload add)
    let old5 = !G_IP5 || std::env::var("FD_MIDG_OLD5").is_ok();
    if cp.ht && !old5 {
        assert!(!cp.dl && !cp.dq, "the crossing form choice runs on the headroom division");
        // in place on the 13 lanes (the stepping flag on sw; act idle) and sx; s = sz + sy is formed as s - 2 on sz
        // (every shot's s in [228, 257]); the division's Q pad past lane 127 is sv (clean outside the size gates)
        let actl = sc.sw;
        let ds = super::payload::DigScr { e: vec![], sa: sc.sz.clone(), sb: fd.sy.clone(), sv: x128, fa: sx[0], g: act,
                                          c0, tmp: vec![pzero, sx[1]], pre1: vec![], pre2: vec![], zeros: vec![],
                                          dirty: dirty.clone(), smin: 2 };
        let sw_toggle = |b: &mut B| {
            if !cp.sw { return; }
            let pre: Vec<QubitId> = sx[1..].iter().copied().filter(|q| !external_owners.contains(q) && *q != act).collect();
            super::frogdrop_col::ge_cd(b, &sc.sz, cp.l0 as isize + 1, ds.fa, &pre, &dirty);
            mc_xor(b, &[(ds.fa, true), (ph, true)], sc.sw, &[], &dirty);
            let pre: Vec<QubitId> = sx[1..].iter().copied().filter(|q| !external_owners.contains(q) && *q != act).collect();
            super::frogdrop_col::ge_cd(b, &sc.sz, cp.l0 as isize + 1, ds.fa, &pre, &dirty);
        };
        let set_act = |b: &mut B| {
            if cp.dn { mc_xor_dn(b, &[(ph, false)], actl, &actor_temps, &dirty, fd, cp.l0, false); }
            else { mc_xor(b, &[(ph, false)], actl, &actor_temps, &dirty); }
        };
        sw_toggle(b);
        set_act(b);
        // c, q's top bit, then the sy decoder's prefixes
        let l5: Vec<QubitId> = sx[2..].iter().copied().filter(|q| !external_owners.contains(q) && *q != act).collect();
        super::mid2::ht_div_inplace(b, fd, cp, actl, &ds, l5[0], l5[1], &l5[2..], &[], &[], pl, &dirty);
        set_act(b);
        sw_toggle(b);
    }
    // ---------------- HT: restoring division (q's bits to the headroom), X = r_{j+1}
    if cp.ht && old5 {
        let actl = sc.sw;
        // dl columns: sw marks the switching shots only (& [sz <= sy], the in-place compare on x128)
        let sw_toggle = |b: &mut B| {
            if !cp.sw { return; }
            let switch_pre: Vec<QubitId> = sx[1..].iter().copied().filter(|q| !external_owners.contains(q) && *q != act && *q != sx[5]).collect();
            super::frogdrop_col::ge_const_compact(b, &sc.sz, cp.l0 as isize + 1, sx[5], &switch_pre, &dirty);
            if cp.dl {
                let gt = super::arith::up_m(b, &fd.sy, &sc.sz, x128, true);
                b.play(&gt, false);
                mc_xor(b, &[(sx[5], true), (ph, true), (sc.sz[sc.sz.len() - 1], true)], sc.sw, &[], &dirty);
                b.play(&gt, true);
            } else {
                mc_xor(b, &[(sx[5], true), (ph, true)], sc.sw, &[], &dirty);
            }
            super::frogdrop_col::ge_const_compact(b, &sc.sz, cp.l0 as isize + 1, sx[5], &switch_pre, &dirty);
        };
        let set_act = |b: &mut B| ht_act(b, fd, cp, sc, actl, &actor_temps, x128, &dirty);
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
            let park5 = park_for(b, actl, &q129b, &rqb);
            let qlen = q129b.len();
            b.x(ph);
            b.play(&park5, false);
            b.play(&rqb, false);
            // The known Y leading-one loan shifts quotient storage down
            // one slot. On the licensed payload boundary all set bits fit,
            // or wrapped bits are zero. Thus SX2/3
            // have returned globally before trans_one_guard uses them.
            // HR already consumed its q bits; other shots started SX clear.
            for kb in 0..kmax.min(NP) {
                let t: Vec<QubitId> = (kb..NP).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                // A wrapped shifted target holds Y DATA, not q_kb: mask
                // it with wf = [sy >= len+1-kb], including zero q bits.
                let wrap = cp.sy.1.min(128) + kb >= qlen + 1;
                let mut base = vec![(q129b[(kb + qlen - 1) % qlen], false), (actl, false)];
                if wrap {
                    wrap_flag(b, kb, qlen);
                    base.push((wf, true));
                }
                super::payload::trans_one_guard(b, &t, &fd.ring[..NP - kb], kb, false, base,
                                                Some((&fd.sy[4..], syhi >> 4)), sx[2], sx[3], &[], &pl.dirty,
                                                (n - 16) as isize);
                if wrap { wrap_flag(b, kb, qlen); }
            }
            b.play(&rqb, true);
            b.play(&park5, true);
            b.x(ph);
        }
        set_act(b);
        sw_toggle(b);
    }
    if !stage(b) { return; } // 5
    if cp.ht {
        let set_act = |b: &mut B| ht_act(b, fd, cp, sc, act, &actor_temps, x128, &dirty);
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
                let pre: Vec<QubitId> = sx[..VB].iter().copied().filter(|q| !external_owners.contains(q) && *q != act).collect();
                super::mid2::dec_swap(b, &fd.sy, sylo, syhi, &lane, c, &[(act, false)], &pre, &[], &dirty);
            }
            add(b, kb, c, false);
            fetch(b, kb, &[(act, false)]);
        }
        b.x(ph);
        b.play(&park, false);
        let f1 = b.tof;
        b.play(&vform, false);
        super::f1_profile("midg.vform", f1, b.tof);
        b.play(&park, true);
        b.x(ph);
        for kb in 0..kmax {
            gate_on(b, kb, act);
            fetch(b, kb, &[(ak, false)]);
            // trial X += 2^kb Y where ak & !c (X = r_{j+1} + (q_{>kb} + 2^kb) Y either way): c = 1 only where ak
            b.cx(c, ak);
            add(b, kb, ak, false);
            b.cx(c, ak);
            // c ^= ak & !over = q_kb: erased
            let r = rotz(b, &[k + 1]);
            b.play(&r, false);
            mc_xor(b, &[(ak, false), (ring[k + 1], true)], c, &[], &dirty);
            b.play(&r, true);
            add(b, kb, ak, true);
            gate_off(b, kb, act);
        }
        let f1 = b.tof;
        b.play(&vform, true);
        super::f1_profile("midg.vform", f1, b.tof);
        set_act(b);
    }
    if !stage(b) { return; } // 6
    let _ = stage(b); // 7
}

#[cfg(test)]
#[path = "tests_lowq695.rs"]
mod lowq695_native;
