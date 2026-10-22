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

#[cfg(test)]
thread_local! {
    pub(crate) static P1_DEBUG_TAG: std::cell::Cell<Option<QubitId>> = const { std::cell::Cell::new(None) };
}

/// F's top bits compared with W (the window has TC + 1 lanes: W's position 257 - sz, then F's TC positions)
pub const TC: usize = 32;
/// Paid Cross-only reciprocal window. Fixed HR25/HT24 retain TC32.
/// The head32 and original dirty Q catalyst are unchanged; the extra
/// window bit refines the same B12A floor/carry predicate.
pub(super) const CROSS_TC: usize = 33;

/// Crossing P1's catalytic reciprocal head. The extra remainder lane is
/// borrowed from Y's low word; window precision and quotient width stay fixed.
const P1_HEAD: usize = 32;

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
    /// lowq-672: one more literal on every window add of stage1_v (the precision tier of a two-engine V form)
    pub(crate) static S1_TIER: std::cell::Cell<Option<(QubitId, bool)>> = const { std::cell::Cell::new(None) };
}

/// `ctl` with the lowq-672 tier literal (S1_TIER) appended when one is set
fn tier_ctl(mut ctl: Vec<(QubitId, bool)>) -> Vec<(QubitId, bool)> {
    if let Some(t) = S1_TIER.with(|c| c.get()) { ctl.push(t); }
    ctl
}

/// lowq-672 L672_TIER=1: the crossing columns' V forms run two reciprocal engines. Tier A: precision L672_KA (19) on
/// R less the L672_RDROP lanes, window adds on h = [sy > L672_TH] (h in lane L672_H, one of the dropped lanes, set
/// by the play around the form); tier B: precision 24 on that R plus Q[L672_E0 ..) (|0> on the act shots with
/// sy <= TH: the parked band ends at sy + 10), window adds on !h. HR's tier A adds the even-head margin.
/// the O3 band tables (b8b_cross::t1 / t2) for the predictor
pub(crate) fn b8b_t1(sy: usize) -> usize { b8b_cross::t1(sy) }
pub(crate) fn b8b_t2(sy: usize) -> usize { b8b_cross::t2(sy) }
fn q_all_pos(q: &[QubitId], x: QubitId) -> Option<usize> { q.iter().position(|&y| y == x) }
fn t_len_ok(t: &[QubitId]) -> bool { t.len() == 15 }
/// lowq-672 pool9: a non-crossing column that runs the crossing sessions and tiers: every column past the fixed
/// form (the chunked one-session V form stores q's bits 1..5 in sx[1..6), the pool9 middle's x128 / pzero / c0 / act
/// lanes; L672_BIGY overrides the bound)
pub(crate) fn l672_bigy(cp: &ColPar) -> bool {
    let y = std::env::var("L672_BIGY").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or_else(fixed_symax);
    super::frogdrop_col::pool9() && cp.sy.1.min(128) > y && (cp.hr || cp.ht)
}
/// the one-session (fixed park) columns' largest sy: the park Q[sy + 1 .. sy + 24) leaves Q[122..126) to R under pool9
fn fixed_symax() -> usize {
    // (lowq-671 ring 258: the non-tier R takes Q[121..126) instead of ring[1])
    if r258() { if std::env::var("B12A_P1").as_deref() == Ok("1") { 96 } else { 97 } }
    else if super::frogdrop_col::pool9() { 98 } else { 102 }
}
/// Low-margin K0 geometry retains the 258-lane tier and Q extension layout.
pub(crate) fn r258() -> bool { super::pointadd_frogdrop::N <= 258 }
/// the first Q lane of the non-tier R's public extension (Q[P9LO..126))
fn p9lo() -> usize { if r258() { 121 } else { 122 } }

/// lowq-672 L672_MID8=1 (see b8b_cross: the crossing middle on sx0, sx1, sx6, sx7 of the spare register)
pub(crate) fn mid8() -> bool { std::env::var("L672_MID8").map(|v| v == "1").unwrap_or(false) }
pub(crate) fn l672_tier() -> bool { std::env::var("L672_TIER").map(|v| v == "1").unwrap_or(false) }
/// the remainder lanes common to both engines (R less L672_RDROP)
pub(crate) fn l672_kc() -> usize {
    std::env::var("L672_KC").ok().and_then(|v| v.parse().ok()).unwrap_or(if r258() { 18 } else { 19 })
}
/// L672_SYA=1 (default): tier A also takes sy[5], sy[6]: every tier-A shot has 112 <= sy <= 128, so the low seven
/// lanes of sy + 16 (u_p undone around that engine) are < 32 there
pub(crate) fn l672_sya() -> bool { std::env::var("L672_SYA").map(|v| v != "0").unwrap_or(true) }
pub(crate) fn l672_ka() -> usize { l672_kc() + if l672_sya() { l672_sya_n() } else { 0 } }
/// tier A's sy lanes: sy[5], sy[6] (sy + 16 over 112..=128), and at ring 258 also sy[4] (sy + 15 over 113..=128:
/// the predictor finds no tier-A session below 113 with E0 = 120)
pub(crate) fn l672_sya_n() -> usize { if r258() { 3 } else { 2 } }
/// tier B's Q lanes start here: Q[E0..126) (Q[126], Q[127], x128 are routed R lanes)
pub(crate) fn l672_e0() -> usize {
    std::env::var("L672_E0").ok().and_then(|v| v.parse().ok()).unwrap_or(126 - (24 - l672_kc()))
}
/// a named small lane of the middle (sx0..sx7, c0, pzero)
fn l672_lane(name: &str, sx: &[QubitId], c0: QubitId, pzero: QubitId) -> QubitId {
    match name {
        "c0" => c0, "pzero" => pzero,
        _ => { let i: usize = name.strip_prefix("sx").and_then(|v| v.parse().ok()).expect("L672 lane name"); sx[i] }
    }
}
pub(crate) fn l672_h_name() -> String { std::env::var("L672_H").unwrap_or("sx6".into()) }
fn l672_drop_names() -> Vec<String> {
    // (pool9: R is already the 20 lanes without sx2..sx5; only the flag lane leaves)
    let dflt = if super::frogdrop_col::pool9() { "sx6" } else { "sx6,sx2,sx3,sx4,sx5" };
    std::env::var("L672_RDROP").unwrap_or(dflt.into()).split(',').map(|x| x.trim().to_string()).collect()
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
    /// Normalized prefix rank; gap=31-code after the inherited sg_p flip.
    /// `carry` is returned after each comparator and before every query.
    Joint { view: joint_size::View, gap: Vec<QubitId>, carry: QubitId },
    /// E=Y-1, gap=31-S; one returned clean threshold carry.
    Direct { size: super::sum_size::SumSize, carry: QubitId },
    /// The complete reciprocal core retains E.low5+gap and its sixth bit.
    DirectLatched { size: super::sum_size::SumSize, carry: QubitId },
    /// Exact E+gap threshold with only restored dirty donors. Metadata is
    /// returned after each query; no sixth sum bit or clean carry is held.
    DirectNoCarry { size: super::sum_size::SumSize },
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
        S1Gate::Direct { size, carry } => {
            super::direct_frame::v_gate(b,size,j,g0,*carry,dirty);
        }
        S1Gate::DirectLatched { size, carry } => {
            super::direct_frame::v_gate_latched(b,size,j,g0,*carry,dirty);
        }
        S1Gate::DirectNoCarry { size } => {
            super::direct_frame::v_gate_no_carry(b,size,j,g0,dirty);
        }
        S1Gate::Joint { view, gap, carry } => {
            assert!(view.normalized && gap.len()==5 && j<=TC);
            let ports=view.ports();
            assert!(!ports.contains(carry) && !gap.contains(carry) && *carry!=g0);
            let bank:Vec<_>=dirty.iter().copied()
                .filter(|q|!ports.contains(q) && !gap.contains(q) && *q!=*carry && *q!=g0).collect();
            let word:Vec<_>=view.low.iter().copied().chain([*carry]).collect();
            let add=rec(b,|b|sumframe::add_zero_extended(b,gap,&word,&bank));
            b.play(&add,false);
            // j<=31 implies SY<=31; precisely this interval has H=0
            // and SY=L+1. Carry bit prevents a modular low-word wrap.
            let low_class:Vec<_>=view.high[..5].iter().map(|&q|(q,true)).collect();
            lt_const_and(b,&word,j,&low_class,g0,&bank);
            b.play(&add,true);
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

pub fn stage1_v(b: &mut B, zh: &[QubitId], win: &[QubitId], sz: &[QubitId], szr: (usize, usize), s: &S1, act: QubitId,
                window: bool) -> Vec<G> {
    stage1_v_impl(b, zh, win, sz, szr, s, act, window, None)
}

// Only the P1 pair passes its already-proved clean SX0 threshold owner.
// Ordinary/fixed callers retain the original comparator-selection contract.
fn stage1_v_impl(b: &mut B, zh: &[QubitId], win: &[QubitId], sz: &[QubitId], szr: (usize, usize), s: &S1, act: QubitId,
                window: bool, clean_echo: Option<QubitId>) -> Vec<G> {
    stage1_v_window(b, zh, win, sz, szr, s, act, window, clean_echo, TC)
}

/// Explicit window precision for the direct Cross pair. Legacy/fixed
/// callers enter through stage1_v_impl and keep exactly TC iterations.
fn stage1_v_window(b: &mut B, zh: &[QubitId], win: &[QubitId], sz: &[QubitId], szr: (usize, usize), s: &S1, act: QubitId,
                window: bool, clean_echo: Option<QubitId>, window_bits: usize) -> Vec<G> {
    assert!(window_bits == TC || window_bits == CROSS_TC);
    if window_bits != TC {
        assert_eq!(zh.len(), 32);
        assert!(clean_echo.is_some());
        assert!(S1_GATE.with(|g| matches!(&*g.borrow(), S1Gate::Direct { .. }
            | S1Gate::DirectLatched { .. } | S1Gate::DirectNoCarry { .. })));
    }
    if let Some(d) = clean_echo {
        assert_eq!(s.andc, vec![d]);
        assert_eq!(s.gt, vec![d]);
        assert!(!s.r.contains(&d) && !zh.contains(&d) && !win.contains(&d) && !s.dirty.contains(&d));
        if !s.anc.is_empty() {
            assert_eq!(s.anc.len(), 2);
            assert_ne!(s.anc[0], s.anc[1]);
            assert!(!s.anc.iter().any(|q| *q == d || s.r.contains(q) || zh.contains(q)
                || win.contains(q) || s.dirty.contains(q)));
        }
    }
    let k = zh.len();
    assert!(s.r.len() == k + 1 || s.r.len() == k);
    assert_eq!(win.len(), window_bits + 1);
    assert!(szr.1 <= 256 && szr.0 >= k + window_bits + 1, "all-ones dividend needs sz - K >= window_bits + 1");
    b.begin();
    let mut r = s.r.clone();
    for &x in &r[..k - 1] { b.x(x); }
    let mut upper: Vec<QubitId> = zh[1..].to_vec();
    upper.push(s.zero);
    // agent_lowq_quot: a K-lane remainder (s.r.len() == K) compares first and rotates after (quot_klane)
    let klane = s.r.len() == k;
    let inplace_flag = klane && s.r.contains(&s.f);
    let clean_gate = inplace_flag && s.andc.first() == s.gt.first();
    for j in 0..window_bits {
        if klane {
            // (agent_lowq_quot: R holding the head's top lane = the virtual leading one, jackylee0424's 693)
            if inplace_flag {
                if s.andc.len() >= 2 && std::env::var("B2_T1_CMP").as_deref() != Ok("0") {
                    super::quot_klane::cmp_csub_clean_vh1_inplace(b, &r, &zh[1..k - 1], &s.andc, &s.dirty);
                } else if let Some(d) = clean_echo {
                    if s.anc.is_empty() {
                        super::quot_klane::cmp_csub_ttk_vh1_inplace_clean(b, &r, &zh[1..k - 1], d);
                    } else {
                        super::quot_klane::cmp_csub_ttk_vh1_inplace_clean_cached(b, &r, &zh[1..k - 1], d, &s.anc);
                    }
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
        b.x(r[0]);
        if !inplace_flag {
            b.cx(s.f, r[0]);
            b.cx(r[0], s.f);
            b.x(s.f);
        }
        if !window { continue; }
        // V += act !f 2^(256 - sz - j) where that position is >= 0 (sz <= 256 - j)
        let bits: Vec<QubitId> = (1..=1 + j).rev().map(|i| win[i]).collect();
        let g0 = if inplace_flag && !clean_gate { s.dirty[0] } else { s.gt[0] };
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
                let mut ctl = if noact { vec![(r[0], false)] }
                              else { vec![(act, false), (r[0], false)] };
                ctl.push((g0, false));
                let ctl = tier_ctl(ctl);
                inc_with_controls(b, &bits, &ctl, gate_dirty);
                for &bit in &bits { b.cx(g0, bit); }
                b.x(g0);
                b.play(&rr, false);
                inc_with_controls(b, &bits, &ctl, gate_dirty);
                b.play(&rr, true);
                b.x(g0);
                for &bit in &bits { b.cx(g0, bit); }
            } else if inplace_flag && !clean_gate {
                // Echo a threshold held on arbitrary dirty payload without a
                // clean flag lane. Each descending bit uses the original lower
                // window prefix and returns g0 before the next bit.
                let noact = S1_NOACT.with(|c| c.get());
                for i in (0..bits.len()).rev() {
                    let mut ctl = tier_ctl(if noact { vec![(r[0], false)] } else { vec![(act, false), (r[0], false)] });
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
                inc_with_controls(b, &bits, &tier_ctl(vec![(r[0], false), (g0, true)]), &s.dirty);
            } else if s.gt.len() == 1 {
                inc_with_controls(b, &bits, &tier_ctl(vec![(act, false), (r[0], false), (g0, true)]), &s.dirty);
            } else if s.gt.len() >= 3 {
                assert!(S1_TIER.with(|c| c.get()).is_none(), "lowq-672 tier: three-gate window form");
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
                assert!(S1_TIER.with(|c| c.get()).is_none(), "lowq-672 tier: two-gate window form");
                let g1 = s.gt[1];
                // g1 = act & r0 & !g0 (dirty three-control toggles)
                mc_xor(b, &[(act, false), (r[0], false), (g0, true)], g1, &[], &s.dirty);
                inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
                mc_xor(b, &[(act, false), (r[0], false), (g0, true)], g1, &[], &s.dirty);
            }
            b.play(&rr, true);
            }
        } else if s.gt.len() == 1 && S1_NOACT.with(|c| c.get()) {
            inc_with_controls(b, &bits, &tier_ctl(vec![(r[0], false)]), &s.dirty);
        } else if s.gt.len() == 1 {
            inc_with_controls(b, &bits, &tier_ctl(vec![(act, false), (r[0], false)]), &s.dirty);
        } else {
            assert!(S1_TIER.with(|c| c.get()).is_none(), "lowq-672 tier: AND-gated window form");
            let g1 = s.gt[1];
            b.and_c(r[0], act, g1);
            inc_mixed(b, g1, &bits, &s.anc, &s.dirty);
            b.and_u(r[0], act, g1);
        }
    }
    b.end()
}

// B12A: two restoring passes on a K-lane catalytic remainder. The first
// pass sees R0 = (2^(K-1) - 1) - D through stage1_v's own low-bit X prefix.
// For the zero-input pass, C = Zh - 1 - D obeys
// 2C + 1 - f' Zh = Zh - 1 - (2D - f Zh), with f' = 1 - f.
// Reversing the ordinary window play subtracts f = !f'. Both records return
// every remainder lane, including dirty D, before the caller touches Y.
// TTK add with a virtual one in bit 0. The physical low Z lane may be even;
// the V comparator deliberately ignores it. This specializes only the two
// gates that touch a[0], so its Toffoli count equals the ordinary add.
fn b12a_add_virtual_odd(b: &mut B, zh: &[QubitId], r: &[QubitId]) {
    let k = zh.len();
    assert!(k >= 4);
    assert_eq!(r.len(), k);
    for i in 1..k { b.cx(zh[i], r[i]); }
    for i in (1..k - 1).rev() { b.cx(zh[i], zh[i + 1]); }
    b.cx(r[0], zh[1]);
    for i in 1..k - 1 { b.ccx(r[i], zh[i], zh[i + 1]); }
    for i in (1..k).rev() {
        b.cx(zh[i], r[i]);
        if i == 1 { b.cx(r[0], zh[1]); }
        else { b.ccx(r[i - 1], zh[i - 1], zh[i]); }
    }
    for i in 1..k - 1 { b.cx(zh[i], zh[i + 1]); }
    b.x(r[0]);
    for i in 1..k { b.cx(zh[i], r[i]); }
}

/// Add the same odd K-bit head, with both endpoint ones virtual. The
/// physical leading-head cell may itself be R's top cell. Only zh[1..K-1)
/// is read; the all-data carry hook completes a K-1-bit TTK addition into
/// that top cell. No measured AND and no clean helper are needed.
/// Cost is 2*K-5 CCX, one less than b12a_add_virtual_odd.
fn b12a_add_virtual_endpoints(b: &mut B, zh: &[QubitId], r: &[QubitId]) {
    let k = zh.len();
    assert!(k >= 4 && r.len() == k);
    let l = k - 1;
    let top = r[l];
    let ports: Vec<_> = zh[1..l].iter().chain(r).copied().collect();
    assert_eq!(ports.iter().collect::<std::collections::BTreeSet<_>>().len(), ports.len());
    // Carry out = original source MSB XOR the peak source/target product.
    b.cx(zh[l - 1], top);
    for i in 1..l { b.cx(zh[i], r[i]); }
    for i in (1..l - 1).rev() { b.cx(zh[i], zh[i + 1]); }
    b.cx(r[0], zh[1]);
    for i in 1..l - 1 { b.ccx(r[i], zh[i], zh[i + 1]); }
    b.ccx(zh[l - 1], r[l - 1], top);
    for i in (1..l).rev() {
        b.cx(zh[i], r[i]);
        if i == 1 { b.cx(r[0], zh[1]); }
        else { b.ccx(r[i - 1], zh[i - 1], zh[i]); }
    }
    for i in 1..l - 1 { b.cx(zh[i], zh[i + 1]); }
    b.x(r[0]);
    for i in 1..l { b.cx(zh[i], r[i]); }
    b.x(top); // the virtual leading one, modulo 2^K
}

fn b12a_dirty_v_pair(b: &mut B, zh: &[QubitId], win: &[QubitId], sz: &[QubitId],
    szr: (usize, usize), s: &S1, act: QubitId, n257_top_zero: bool) -> Vec<G> {
    let k = zh.len();
    assert!(k >= 4);
    assert_eq!(s.r.len(), k);
    assert_eq!(s.r[k - 1], s.f);
    let clean_echo = if super::frogdrop_col::c666_pool5() && s.andc.len() == 1
        && s.gt == s.andc { Some(s.andc[0]) } else { None };
    let fv = stage1_v_impl(b, zh, win, sz, szr, s, act, true, clean_echo);
    let fr = stage1_v_impl(b, zh, win, sz, szr, s, act, false, clean_echo);
    let convert = super::frogdrop_col::rec(b, |b| {
        for &q in &s.r { b.x(q); }
        // N257's span frame holds the physical top Z lane at zero during
        // the play. The virtual Zh has a one there on both ring widths.
        if s.r[k - 1] == zh[k - 1] {
            assert!(n257_top_zero);
            b12a_add_virtual_endpoints(b, zh, &s.r);
        } else {
            if n257_top_zero { b.x(zh[k - 1]); }
            b12a_add_virtual_odd(b, zh, &s.r);
            if n257_top_zero { b.x(zh[k - 1]); }
        }
        for &q in &s.r[..k - 1] { b.x(q); }
    });
    super::frogdrop_col::rec(b, |b| {
        #[cfg(test)]
        P1_DEBUG_TAG.with(|tag| { if let Some(q) = tag.get() { b.x(q); } });
        b.play(&fv, false);
        b.play(&fr, true);
        b.play(&convert, false);
        b.play(&fr, false);
        b.play(&fv, true);
        b.play(&convert, true);
        #[cfg(test)]
        P1_DEBUG_TAG.with(|tag| { if let Some(q) = tag.get() { b.x(q); } });
    })
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
pub(crate) mod joint_size;
mod joint_frame;
pub(crate) mod direct_v;
pub(crate) mod direct_native_ring_v;
pub(crate) mod direct_fixed_middle;
mod sumframe;

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
pub fn qch() -> usize { QCH.max(23usize.saturating_sub(super::pointadd_frogdrop::K + 6)) }
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
fn trans_masked_q(b: &mut B, t: &[QubitId], s: &[QubitId], n: usize, k: usize, c: QubitId, sy: &[QubitId], sh: usize,
                  sylo: usize, syhi: usize, g: QubitId, c0: QubitId, pre: &[QubitId], temps: &[QubitId],
                  dirty: &[QubitId]) {
    // (lowq-671, after nasqret/odinfree's 675: at ring 258 the coarse boundary's source cell may be the opposite ring
    // operand's live bit; add only the carry into that boundary)
    assert!(n >= 257 && t.len() == s.len() && s.len() <= n);
    if n <= 258 {
        trans_carry_boundary(b, t, s, if n == 257 { n + 1 - k } else { n - k }, 1 << sh, c, &sy[sh..], sylo >> sh, syhi >> sh, g, c0, pre, temps, dirty);
        return;
    }
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

/// Add the low source prefix and its boundary carry, restoring arbitrary source cells at and above the boundary
/// (boundary = top - stride * value(sy)). On entry g, pre, c0 are zero; c and sy are not changed; active sy in
/// [lo, hi]. (Ported from submission 7379f521, Q675, GPT-6 Astra / Codex.)
#[allow(clippy::too_many_arguments)]
fn trans_carry_boundary(b: &mut B, t: &[QubitId], s: &[QubitId], top: usize, stride: usize, c: QubitId,
                        sy: &[QubitId], lo: usize, hi: usize, g: QubitId, c0: QubitId, pre: &[QubitId],
                        temps: &[QubitId], dirty: &[QubitId]) {
    assert_eq!(t.len(), s.len());
    assert!(stride > 0 && lo <= hi && hi * stride <= top);
    assert!(!t.contains(&g) && !s.contains(&g) && !sy.contains(&g) && g != c && g != c0);
    assert!(!pre.contains(&g) && !temps.contains(&g) && !dirty.contains(&g));
    // Above the largest possible boundary the running gate is still zero.
    // Every upper MAJ is undone before the first masked write: delete that
    // paired identity, retaining the boundary cell and its incoming carry.
    // This is exact for arbitrary upper data and arbitrary restored c0.
    let funded = super::frogdrop_col::c665_pool4();
    let span = if funded { t.len().min(top - lo * stride + 1) } else { t.len() };
    let (t, s) = (&t[..span], &s[..span]);
    for i in 0..t.len() {
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.cx(s[i], t[i]); b.cx(s[i], x); b.ccx(x, t[i], s[i]);
    }
    let mut dec = super::mask::Dec::new(sy, pre);
    let mut next = lo;
    // At margin zero the first boundary can be virtual, just beyond the
    // physical slice. Those shots add every source bit modulo the slice;
    // initialize the running gate before the reverse sweep.
    while next <= hi && top - next * stride >= t.len() {
        let mut ct = dec.ctrls(b, next);
        ct.push((c, false));
        mc_xor(b, &ct, g, temps, dirty);
        next += 1;
    }
    for i in (0..t.len()).rev() {
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.ccx(x, t[i], s[i]); b.cx(s[i], x); b.cx(s[i], t[i]);
        // the old g selects strictly interior source bits; the new g also the boundary, so the second toggle adds
        // only its incoming carry
        let boundary_here = next <= hi
            && (next as isize) <= (top as isize - i as isize).div_euclid(stride as isize);
        if boundary_here || !funded {
            b.ccx(g, s[i], t[i]);
            while next <= hi && (next as isize) <= (top as isize - i as isize).div_euclid(stride as isize) {
                let mut ct = dec.ctrls(b, next);
                ct.push((c, false));
                mc_xor(b, &ct, g, temps, dirty);
                next += 1;
            }
            b.ccx(g, x, t[i]);
        } else {
            // g is unchanged between the two toggles: g*s_i xor g*x
            // equals g*(s_i xor x). The two CNOTs restore the source.
            b.cx(x, s[i]); b.ccx(g, s[i], t[i]); b.cx(x, s[i]);
        }
    }
    assert_eq!(next, hi + 1);
    dec.clear(b);
    b.cx(c, g);
}

/// The same complete source-prefix/carry-boundary transition, reading a
/// normalized joint size. The ring source is disjoint from metadata, so
/// every size query sees its unchanged code even during the MAJ sweep.
/// PH may be payload here: normalized size queries never read its tag bit.
#[allow(clippy::too_many_arguments)]
fn trans_carry_boundary_joint(b:&mut B,t:&[QubitId],s:&[QubitId],top:usize,
    c:QubitId,view:&joint_size::View,range:(usize,usize),g:QubitId,c0:QubitId,
    clean:&[QubitId],dirty:&[QubitId]) {
    let (lo,hi)=range;
    assert!(view.normalized && t.len()==s.len() && 1<=lo && lo<=hi && hi<=top);
    let metadata=view.low.iter().chain(&view.high[..5]).copied().collect::<Vec<_>>();
    assert!(t.iter().chain(s).all(|q|!metadata.contains(q)));
    assert!(!t.contains(&g)&&!s.contains(&g)&&g!=c&&g!=c0);
    let span=t.len().min(top-lo+1);
    let (t,s)=(&t[..span],&s[..span]);
    // A size query reads only the unchanged packet and held control c.
    // Between complete MAJ cells its arithmetic target/source are arbitrary
    // restored donors, including live carries. Do not discard the entire
    // source when the long span consumes the usual ring-tail donor bank.
    // Keep every packet port (also normalized PH), clean prefix, held
    // control, query target and carry-in outside this temporary loan.
    let excluded:std::collections::BTreeSet<_>=view.ports().into_iter()
        .chain(clean.iter().copied()).chain([c,g,c0]).collect();
    let mut seen=std::collections::BTreeSet::new();
    let bank:Vec<_>=dirty.iter().chain(t).chain(s).copied()
        .filter(|q|!excluded.contains(q)&&seen.insert(*q)).collect();
    let query=|b:&mut B,size:usize|view.xor_eq(b,size,g,&[(c,false)],clean,&bank);
    for i in 0..span {
        let x=if i==0 {c0}else{s[i-1]};
        b.cx(s[i],t[i]);b.cx(s[i],x);b.ccx(x,t[i],s[i]);
    }
    let mut next=lo;
    while next<=hi && top-next>=span {query(b,next);next+=1;}
    for i in (0..span).rev() {
        let x=if i==0 {c0}else{s[i-1]};
        b.ccx(x,t[i],s[i]);b.cx(s[i],x);b.cx(s[i],t[i]);
        if next<=hi && next<=top-i {
            b.ccx(g,s[i],t[i]);
            while next<=hi && next<=top-i {query(b,next);next+=1;}
            b.ccx(g,x,t[i]);
        } else {
            b.cx(x,s[i]);b.ccx(g,s[i],t[i]);b.cx(x,s[i]);
        }
    }
    assert_eq!(next,hi+1);
    b.cx(c,g);
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

/// Pool4's returned query owners must be globally clean, including extra-off
/// shots. The act-as-carry lane is deliberately excluded from this bank.
/// Whole public data slices are excluded from dirty donors before any query.
fn b7b_pool4_query_donors(t: &[QubitId], s: &[QubitId], sy: &[QubitId],
    ports: &[QubitId], clean: &[QubitId], dirty: &[QubitId]) -> Vec<QubitId> {
    let mut seen = std::collections::BTreeSet::new();
    for &q in clean {
        assert!(seen.insert(q.0) && !t.contains(&q) && !s.contains(&q)
            && !sy.contains(&q) && !ports.contains(&q));
    }
    super::mask::R11O11_DECCC.with(|cc| {
        assert!(clean.iter().all(|q| !cc.borrow().contains(q)));
    });
    let mut used = std::collections::BTreeSet::new();
    let d: Vec<_> = dirty.iter().copied().filter(|q| !t.contains(q)
        && !s.contains(q) && !sy.contains(q) && !ports.contains(q)
        && !clean.contains(q) && used.insert(q.0)).collect();
    assert!(d.len() >= 9);
    d
}

/// Same MAJ/restore/write permutation as b7b_masked_cmp_y. The caller's
/// existing ak implies raw SY in [sylo,syhi] subset [1,128]. Low seven bits
/// therefore distinguish every active address, including 128 encoded as0.
/// On ak=0 every changed boundary query is identity for arbitrary size/data;
/// both decoder and clean AND work are returned before the next MAJ cell.
/// Keep the original generic entry point for callers without this contract.
#[allow(clippy::too_many_arguments)]
pub(crate) fn b7b_masked_cmp_y_pool4(b: &mut B, t: &[QubitId], s: &[QubitId], sy: &[QubitId],
    sylo: usize, syhi: usize, ak: QubitId, c: QubitId, c0: QubitId,
    mask: QubitId, pre: &[QubitId], dirty: &[QubitId], cmpl: bool) {
    assert_eq!(t.len(), s.len());
    assert!(super::frogdrop_col::c665_pool4());
    assert_eq!(sy.len(), 8);
    assert!(pre.len() == 1 || (c660_flight_sel() && pre.is_empty()));
    assert!(1 <= sylo && sylo <= syhi && syhi <= 128);
    let clean: Vec<_> = pre.iter().copied().chain([mask]).collect();
    let donors = b7b_pool4_query_donors(t, s, sy, &[ak,c,c0], &clean, dirty);
    let dirty = donors.as_slice();
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
    // Hold one decoder prefix; the returned former mask is the clean
    // conjunction temp. No arithmetic control or carry is repurposed.
    let mut dec = super::mask::Dec::new(&sy[..7], pre);
    for i in (0..t.len()).rev() {
        if (sylo..=syhi).contains(&i) {
            let eq = dec.ctrls(b, i & 127);
            let mut controls = eq.clone();
            controls.extend([(s[i], true), (ak, false)]);
            mc_xor(b, &controls, c, &[mask], dirty);
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

/// Same masked add permutation, using ctl => raw SY in [1,128]. ctl is the
/// returned quotient flight, hence implies the existing active phase. On
/// ctl=0 the MAJ/inverse pair restores arbitrary carry and data; the decoder
/// and clean conjunction temp also return exactly. The running mask retains
/// its original role, including its terminal CX(ctl,mask).
#[allow(clippy::too_many_arguments)]
pub(crate) fn b7b_masked_add_y_pool4(b: &mut B, t: &[QubitId], s: &[QubitId], sy: &[QubitId],
    sylo: usize, syhi: usize, ctl: QubitId, ak: QubitId, top: QubitId, c0: QubitId, mask: QubitId,
    pre: &[QubitId], dirty: &[QubitId], sub: bool) {
    assert_eq!(t.len(), s.len());
    assert!(super::frogdrop_col::c665_pool4());
    assert_eq!(sy.len(), 8);
    assert!(pre.len() == 1 || (c660_flight_sel() && pre.is_empty()));
    assert!(1 <= sylo && sylo <= syhi && syhi <= 128);
    let mut ports = vec![ctl,c0,mask];
    if c660_flight_sel() { ports.extend([ak,top]); }
    let donors = b7b_pool4_query_donors(t, s, sy, &ports, pre, dirty);
    let dirty = donors.as_slice();
    assert!(syhi < t.len());
    if sub { for &x in t { b.x(x); } }
    for i in 0..t.len() {
        let x = if i == 0 { c0 } else { s[i - 1] };
        b.cx(s[i], t[i]);
        b.cx(s[i], x);
        b.ccx(x, t[i], s[i]);
    }
    // The former sole prefix is now the returned clean AND temp.
    let mut dec = super::mask::Dec::new(&sy[..7], &[]);
    for i in (0..t.len()).rev() {
        if (sylo..=syhi).contains(&i) {
            let mut eq = dec.ctrls(b, i & 127);
            if c660_flight_sel() {
                // Flight starts at zero and receives its quotient bit only
                // under held ak. Hence ctl=>ak throughout this whole add.
                // On bottom ak also implies vprime<32, so top=0. On
                // top replay top is still zero before its later top_flag.
                // Return both borrowed owners before the next ripple cell.
                // Retain ctl in every final gate. No clean-prefix claim.
                assert!(pre.is_empty());
                super::mask::mc_xor_implied_pair(b,ctl,ak,top,&eq,mask,dirty);
            } else {
                eq.push((ctl, false));
                mc_xor(b, &eq, mask, pre, dirty);
            }
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
    assert!(pre.len() >= sy.len() - 1 || (mid8() && !pre.is_empty()));
    // A top-lane quotient reads the carry at sy-1, every lower lane at sy.
    // Shift the size temporarily and use one carry read for both cases.
    // (lowq-672 MID8: a short bank shifts by the exact dirty constant adder, sy += top ? -1 : 0)
    let shift = rec(b, |b| if pre.len() >= sy.len() - 1 { super::arith::dec(b, top, sy, pre) }
                           else { super::modp_frogdrop::add_const_exact(b, sy, Some(top), (1u64 << sy.len()) - 1, dirty) });
    b.play(&shift, false);
    let rd = s.to_vec();
    let mut mid = |b: &mut B| {
        let lane = |v: usize| rd.get(v).copied();
        read_lane(b, sy, sylo.saturating_sub(1), syhi, &lane, true,
                  &[(ak, false)], c, &pre[..pre.len().min(2)], &[], dirty);
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

/// O3 tb-frame. The ring view is relabelled by +qtop, so an UP rotation by
/// tb sends natural kk=tb-j to fixed frame kk'=qtop-j. The record inverse
/// restores sz, ring and dirty passengers exactly.
fn b8b_tb_frame(b: &mut B, ring: &[QubitId], sz: &[QubitId], sy: &[QubitId],
                dirty: &[QubitId]) -> Vec<G> {
    b8b_tb_frame_with_flag(b, ring, sz, sy, dirty, None)
}

fn b8b_tb_frame_with_flag(b: &mut B, ring: &[QubitId], sz: &[QubitId], sy: &[QubitId],
                         dirty: &[QubitId], clean_flag: Option<QubitId>) -> Vec<G> {
    assert_eq!(sz.len(), 8);
    assert_eq!(sy.len(), 8);
    assert!((257..=259).contains(&ring.len()));
    let qtop = super::pointadd_frogdrop::QB - 1;
    assert!(qtop <= 29);
    rec(b, |b| {
        if super::frogdrop_col::c666_pool5() {
            // Keep the complete gap in five bits. The old byte's three
            // clamp flags alias ordinary middle roles in the pool5 layout.
            let gap = &sz[..5];
            for &q in gap { b.x(q); }
            super::frogdrop::rot_by(b, ring, gap, false);
            if let Some(flag) = clean_flag {
                assert!(!ring.contains(&flag) && !gap.contains(&flag) && !sy.contains(&flag));
                // Raw-size owners 5..7 are returned roles in this five-bit frame.
                let bank: Vec<_> = dirty.iter().copied().filter(|&q| q != flag).collect();
                // The returned ripple carry holds each bit of the exact
                // correction max(g-qtop,0). Single-control rotations
                // replace the per-value, multi-control cycle swaps.
                let correction_bits = (usize::BITS - (31 - qtop).leading_zeros()) as usize;
                for bit in 0..correction_bits {
                    let query = rec(b, |b| {
                        for value in qtop + 1..32usize {
                            if ((value - qtop) >> bit) & 1 == 0 { continue; }
                            let ctl: Vec<_> = gap.iter().enumerate()
                                .map(|(i, &q)| (q, (value >> i) & 1 == 0)).collect();
                            mc_xor(b, &ctl, flag, &[], &bank);
                        }
                    });
                    b.play(&query, false);
                    super::frogdrop::crot_up(b, flag, ring, ring.len() - (1 << bit));
                    b.play(&query, true);
                }
            } else {
                for value in qtop + 1..32usize {
                    let ctl: Vec<_> = gap.iter().enumerate()
                        .map(|(i, &q)| (q, (value >> i) & 1 == 0)).collect();
                    sumframe::rot_up_const_controlled(b, ring, ring.len() - (value - qtop), &ctl, dirty);
                }
            }
            return;
        }
        super::arith::ttk_add(b, sy, sz, None, None);
        for &q in sz { b.x(q); }
        super::modp_frogdrop::inc_dirty_free(b, &sz[1..], dirty);
        for value in qtop + 1..32usize {
            b8b_transpose_const(b, sz, value as u8,
                (qtop + 32 * (value - qtop)) as u8, dirty);
        }
        // `rot_by_range_care` specifies the UP source support (the DOWN
        // destinations). Natural kk is in 0..=qtop, with at most129
        // target cells; extend the care support with the paid top index.
        let care: std::collections::BTreeSet<usize> = (ring.len() - (qtop + 129)..ring.len()).collect();
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
/// Source-only owner-sharing experiment; the complete physical reduction
/// remains gated on raw-size/digit/map lifetime integration.
pub(super) fn c660_flight_sel() -> bool {
    std::env::var("C660_FLIGHT_SEL").as_deref() == Ok("1")
}

fn route_free_phase_ports(forms: &[Vec<G>], ph: QubitId, act: QubitId) -> bool {
    forms.iter().flatten().all(|g| match *g {
        G::X(a) => ![ph,act].contains(&a),
        G::Cx(a,t) | G::Swap(a,t) | G::AndC(a,t,_) | G::AndU(a,t,_) => {
            // The full three-port cases are handled separately below.
            ![ph,act].contains(&a) && ![ph,act].contains(&t)
                && match *g { G::AndC(_,_,z) | G::AndU(_,_,z) => ![ph,act].contains(&z), _ => true }
        },
        G::Ccx(a,c,t) => ![a,c,t].iter().any(|q| [ph,act].contains(q)),
        _ => false,
    })
}

fn b8b_make_raw_parked_forms(b: &mut B, prot: &[G], sg_p: &[G], u_p: &[G],
    fvp: &[G], fr: &[G], p1_swap: Option<&[G]>, vh1: Option<QubitId>, sy: &[QubitId], gap: &[QubitId],
    owners: [QubitId; 3], sw: Option<QubitId>, hr_old: Option<(&[G], QubitId, QubitId, QubitId)>,
    dirty: &[QubitId]) -> Vec<Vec<G>> {
    let route_free_p1 = super::frogdrop_col::c665_pool4() && p1_swap.is_some();
    if route_free_p1 { assert!(P1_HEAD <= 32 && TC <= 32); }
    (0..3).map(|family| {
        let route = rec(b, |b| if !route_free_p1 {
            b8b_route_family(b, family, sy, gap, owners, sw,
                hr_old.map(|(_, ph, _, _)| ph), dirty);
        });
        let old_inv = hr_old.map(|(old, _, _, _)| rec(b, |b| b.play(old, true)));
        let old_play = |b: &mut B, r: &[G]| {
            // Route-free P1's controlled empty tape is the identity. Removing
            // this whole conjugation returns its otherwise-read w selector.
            if c660_flight_sel() && route_free_p1 {
                assert!(r.is_empty());
                return;
            }
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
            if let Some(r) = p1_swap { b.play(r, false); }
            b.play(u_p, false);
            if let Some(q) = vh1 { b.x(q); }
            b.play(fvp, false);
            b.play(fr, true);
            if let Some(q) = vh1 { b.x(q); }
            b.play(u_p, true);
            if let Some(r) = p1_swap { b.play(r, true); }
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
pub(crate) fn swap_tree(reg: &[QubitId], leaves: &[(usize, QubitId)], level: usize,
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

/// Gather the phase-specific exact-zero payload lane into R's fixed root.
/// The inverse returns every payload bit, including an arbitrary old root.
fn c42_payload_gather(b: &mut B, p: &[QubitId], sy: &[QubitId], root: QubitId,
                      lo: usize, hi: usize, ht: bool) -> Vec<G> {
    assert!(lo >= 1 && lo <= hi && hi <= 128 && p.len() >= 259);
    let leaves: Vec<(usize, QubitId)> = (lo..=hi)
        .map(|v| (v, p[if ht { v } else { 257 - v }])).collect();
    let mut swaps = vec![];
    let selected = swap_tree(sy, &leaves, sy.len(), &mut swaps);
    assert_ne!(selected, root);
    rec(b, |b| {
        for &(bit, left, right) in &swaps { b.cswap(bit, left, right); }
        b.swap(selected, root);
    })
}

/// On an offset HT state the two top bits differ; this controlled XOR makes
/// the selected lower top lane zero and is undone after all HT V plays.
fn c42_ht_partial_narrow(b: &mut B, p: &[QubitId], sy: &[QubitId],
                         lo: usize, hi: usize, dirty: &[QubitId]) -> Vec<G> {
    assert!(lo >= 1 && lo <= hi && hi <= 128 && p.len() >= 259);
    rec(b, |b| {
        for v in lo..=hi {
            let eq: Vec<(QubitId, bool)> = (0..sy.len())
                .map(|i| (sy[i], (v >> i) & 1 == 0)).collect();
            let mut with_next = eq.clone();
            with_next.push((p[v + 1], false));
            let loan: Vec<QubitId> = dirty.iter().copied()
                .filter(|&q| q != p[v] && q != p[v + 1]).collect();
            mc_xor(b, &with_next, p[v], &[], &loan);
            mc_xor(b, &eq, p[v], &[], &loan);
        }
    })
}

/// Scheme G: lanes appended to the column pool (FD_MIDG; the lean middle uses none of them)
pub const EXTRA: usize = 0;

/// Scheme G replaces the rho middle (FD_MIDG=1 / MIDG_ON)
pub const MIDG_ON: bool = true;
pub fn enabled() -> bool {
    MIDG_ON || std::env::var("FD_MIDG").is_ok()
}

/// Shared eligibility for the fixed raw-size epoch. The column caller may
/// keep a boundary packet only when this is the exact middle dispatch.
pub(crate) fn joint_fixed_boundary_epoch(fd:&Fd,cp:&ColPar)->bool {
    let eligible=joint_size::enabled()&&fd.sy.len()==5&&cp.sy.1<=fixed_symax()
        &&!(cp.sw||cp.psw||cp.dl||cp.dq);
    if eligible {
        assert!(fd.sx.len()==7&&cp.n==257&&cp.sy.1<=96);
        assert!((cp.hr&&std::env::var_os("B7A_A_HR").is_some())
            ||(cp.ht&&std::env::var_os("B7A_A_HT").is_some()));
    }
    eligible
}

/// Fixed columns keep their inherited raw size readers for one complete
/// middle epoch. Three zero Q suffix owners receive SY5..7; only the
/// reciprocal's temporary owner assignment changes inside that epoch.
fn joint_fixed_middle(b:&mut B,fd:&Fd,cp:&ColPar,sc:&ColScr,pl:Option<&PlCol>,
    swap:&[Gate],stage:&mut dyn FnMut(&mut B)->bool,boundary_epoch:bool) {
    assert!(joint_fixed_boundary_epoch(fd,cp));
    let hi=cp.sy.1;
    let suffix=&fd.q[hi+24..hi+27];
    let temporary:Vec<_>=fd.sy.iter().chain(fd.sx[..3].iter()).copied().collect();
    let (done,branch,case)=(fd.sx[3],fd.sx[5],fd.sx[6]);
    let helper=*sc.dirty.iter().find(|q|!fd.sy.contains(q)&&!fd.sx.contains(q)
        &&!fd.q.contains(q)&&!sc.sz.contains(q)&&**q!=fd.ph).expect("fixed codec dirty helper");
    let codec=if boundary_epoch {
        // Q=Y and no incoming escape/switch tag exists in a fixed column.
        // Decode the normal boundary packet directly into the same raw ABI.
        super::joint_prefix::boundary_record(b,&temporary,&fd.q[123..128],
            fd.ph,done,branch,case,helper,&sc.dirty,false)
    } else {
        super::joint_prefix::global_record(b,&temporary,&fd.q[123..128],
            fd.ph,done,branch,case,helper,&sc.dirty)
    };
    b.play(&codec,true);
    let mut raw=Fd {ring:fd.ring.clone(),q:fd.q.clone(),sy:temporary.clone(),
        sx:fd.sx.clone(),ph:fd.ph,cnt:fd.cnt.clone()};
    let counter_passengers=cp.col==139;
    if counter_passengers {
        assert!(cp.dn&&cp.ht&&!cp.hr&&hi==96&&cp.cntmax<64);
        // The codec reconstructed D. Counter bit6 is still globally zero,
        // so Q127 carries D throughout this fixed epoch. Two low counter
        // bits share q21/q22's park on mutually exclusive DONE/active shots.
        b.swap(done,fd.q[127]);
        for (a,z) in [(fd.q[121],fd.q[118]),(fd.q[122],fd.q[119])] {
            b.cx(a,z);b.cx(z,a);
        }
    } else {
        assert!(!suffix.iter().any(|q|fd.cnt.contains(q))||!cp.dn);
        super::frogdrop_col::map_done_flag(b,&raw,cp,done,&sc.dirty);
    }
    for i in 0..3 {b.cx(fd.sx[i],suffix[i]);b.cx(suffix[i],fd.sx[i]);}
    raw.sy=fd.sy.iter().copied().chain(suffix.iter().copied()).collect();
    super::frogdrop_col::with_fixed_done_override(b,
        counter_passengers.then_some(fd.q[127]),|b|middle(b,&raw,cp,sc,pl,swap,stage));
    for i in 0..3 {b.cx(suffix[i],fd.sx[i]);b.cx(fd.sx[i],suffix[i]);}
    raw.sy=temporary;
    if counter_passengers {
        for (a,z) in [(fd.q[121],fd.q[118]),(fd.q[122],fd.q[119])] {
            b.cx(z,a);b.cx(a,z);
        }
        b.swap(done,fd.q[127]);
    } else {super::frogdrop_col::map_done_flag(b,&raw,cp,done,&sc.dirty);}
    if boundary_epoch {
        // The raw epoch and counter transport are complete. Encode directly
        // for the PRE-map capacity class while Q still equals Y. DONE uses
        // the same binary packet in both classes and does not flip phase.
        let pre=super::joint_prefix::boundary_record(b,&raw.sy,&fd.q[123..128],
            fd.ph,done,branch,case,helper,&sc.dirty,true);
        b.play(&pre,false);
    } else {b.play(&codec,false);}
}

/// Complete-column-only entry: normal boundary packet in, PRE-map boundary
/// packet out. Partial column captures retain `middle`'s middle-packet ABI.
pub(crate) fn middle_fixed_boundary(b:&mut B,fd:&Fd,cp:&ColPar,sc:&ColScr,
    pl:Option<&PlCol>,swap:&[Gate],stage:&mut dyn FnMut(&mut B)->bool) {
    joint_fixed_middle(b,fd,cp,sc,pl,swap,stage,true);
}

/// Complete the P258 HR splice after every natural quotient bit and
/// exact payload transition has returned its flight. Move retained act to
/// Pzero while the raw size reclaims SX5/SX6/SX1; SX0 and SX2 are returned
/// decoder roles. PH is payload until compression, and is not a predicate.
pub(super) fn p258_finish_hr(b:&mut B,fd:&Fd,cp:&ColPar,sc:&ColScr,
    mut session:super::payload::splice258::PhaseTransition,dirty:&[QubitId]) {
    use super::payload::splice258;
    assert!(splice258::enabled() && !session.ht);
    if joint_size::enabled() && fd.sy.len()==5 {
        super::payload::finish_joint_phase(b,fd,cp,sc,&session,fd.sx[0],
            &session.raw.dirty);
        return;
    }
    let (old_act,raw_act,flag,pre)=(session.act,fd.sx[3],fd.sx[2],fd.sx[0]);
    assert_eq!(old_act,fd.sx[5]);
    b.cx(old_act,raw_act);b.cx(raw_act,old_act);
    session.act=raw_act;
    let frame=sumframe::record(b,&sc.sz,&fd.sy,dirty);
    b.play(&frame,true);
    let mut raw_size=sc.sz.clone();
    let top=rec(b,|b|if cp.col==0 {
        let zero:Vec<_>=sc.sz.iter().map(|&q|(q,true)).collect();
        mc_xor(b,&zero,fd.q[118],&[],dirty);
    });
    if cp.col==0 {raw_size.push(fd.q[118]);}
    b.play(&top,false);
    splice258::finish_phase(b,&session,&raw_size,(cp.sz.0.max(1),cp.sz.1.min(256)),
        flag,&[pre],&[],&session.raw.dirty);
    b.play(&top,true);
    b.play(&frame,false);
    b.cx(raw_act,old_act);b.cx(old_act,raw_act);
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
fn mid_chain() -> usize {
    let v = std::env::var("FD_MID_CHAIN").ok().and_then(|v| v.parse::<usize>().ok()).unwrap_or(7);
    // (lowq-672 MID8: the chain sx[1..1 + n] stays on sx1)
    if mid8() { v.min(1) } else { v }
}

/// act ^= the HT stepping flag: ph & not done (done derived), in dq columns & !(sz < sy) (a delayed shot's no-step
/// column; the in-place compare on `c0`)
#[allow(clippy::too_many_arguments)]
fn ht_act(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr, act: QubitId, temps: &[QubitId], c0: QubitId,
          dirty: &[QubitId]) {
    let mut lits = vec![(fd.ph, false)];
    if super::frogdrop_col::c666_pool5() {
        if cp.dq {
            sumframe::xor_raw_lt_sy(b, &sc.sz[..5], &fd.sy, c0, &[], dirty);
            lits.push((c0, true));
        }
        if cp.dn { mc_xor_dn(b, &lits, act, temps, dirty, fd, cp.l0, false); }
        else { mc_xor(b, &lits, act, temps, dirty); }
        if cp.dq { sumframe::xor_raw_lt_sy(b, &sc.sz[..5], &fd.sy, c0, &[], dirty); }
        return;
    }
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

/// Caller-owned post-stage-2 size frame. Play before moving outside SW to
/// the middle's SX5 role, and invert only after that role is returned.
/// The middle's complete physical-owner integration is still required;
/// recording this primitive alone does not make C666_POOL5 runnable.
pub(crate) fn pool5_sumframe_record(b: &mut B, fd: &Fd, cp: &ColPar, sc: &ColScr) -> Vec<G> {
    assert!(super::frogdrop_col::c666_pool5());
    assert_eq!(sc.sz.len(), 8);
    // Bias226 covers the inherited active QB23 domain and the idle
    // endpoint KD26 domain; no Q payload/counter host is required.
    let frame = sumframe::record(b, &sc.sz, &fd.sy, &sc.dirty);
    rec(b, |b| {
        if cp.col == 0 {
            // The existing column-0 eight-bit view carries raw SZ - 217.
            super::frogdrop::add_const_dirty_exact(b, &sc.sz, 217, &sc.dirty);
        }
        b.play(&frame, false);
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
    if joint_fixed_boundary_epoch(fd,cp) {
        joint_fixed_middle(b,fd,cp,sc,pl,_swap,stage,false);
        return;
    }
    let n = cp.n;
    let pool5 = super::frogdrop_col::c666_pool5();
    let pool4 = super::frogdrop_col::c665_pool4();
    let sx7_retired = super::frogdrop_col::c660_sx7_raw();
    let payload258 = super::payload::splice258::enabled();
    if payload258 {assert!(sx7_retired && pool4);}
    if sx7_retired {
        assert!(pool4 && c660_flight_sel(), "seven SX requires the scoped P1 flight layout");
    }
    if pool5 {
        assert_eq!(n, 257);
        assert!(mid8() && super::frogdrop_col::c55_pool8() && super::frogdrop_col::pool9());
        assert_eq!(std::env::var("B12A_P1").as_deref(), Ok("1"));
        assert_eq!(std::env::var("S5_NOPARK").as_deref(), Ok("1"));
        assert_ne!(std::env::var("L671_HRFIX").as_deref(), Ok("1"),
                   "pool5 retains the official P1 path, not the unbaked allocating repair");
    }
    let ring = fd.ring.clone();
    let q = fd.q.clone();
    let nq = q.len();
    let ph = fd.ph;
    let (k, kp, tot) = (cp.k, cp.kp, cp.tot);
    // C42: the payload root is unavailable as an arbitrary dirty helper while
    // it is lent to R. In no-payload traversals this is p[0]; payload
    // traversals gather their exact-zero leaf to the same root around plays.
    let payload_root = pl.map(|p| p.p[0]).unwrap_or(sc.dirty[0]);
    if n == 257 { assert!(sc.dirty.contains(&payload_root)); }
    let dirty: Vec<QubitId> = if n == 257 && !payload258 {
        sc.dirty.iter().copied().filter(|&q| q != payload_root).collect()
    } else { sc.dirty.clone() };
    let _ = tot;
    let pclo = cp.sz.0 + cp.h;
    let mt = (n - pclo + 1).min(nq.max(cp.xw) + 1);
    let lsb = if cp.dn { cp.sy.1.max(28) } else { cp.sy.1 };
    let inherited_loan_end = nq - if cp.dn { fd.cnt.len() } else { 0 };
    // Joint metadata keeps Q127 as an encoded owner. From public column159
    // the counter's seventh bit instead occupies Q120, outside all data
    // and scratch banks. Its old fixed-R role moves to Q119 for this epoch.
    let joint_late_counter = joint_size::enabled() && super::frogdrop_col::q_data_end(fd)==120;
    let loan_end = if joint_late_counter { inherited_loan_end.min(120) }
                   else { inherited_loan_end };
    let fixed_r_extra = if joint_late_counter { 119 } else { 120 };
    // (lowq-671 ring 258: headroom 1, the window and the divisor's zero lane start at ring[0])
    let r258c = (n == 258 || n == 257) && k == 0 && cp.h <= 1;
    assert!(cp.h >= k + 2 || r258c, "the window starts at lane K + 1 of the test frame: ring headroom K + 2");
    let ws = if r258c { 0 } else { k + 1 };
    let sx = fd.sx.clone();
    assert!(if sx7_retired { sx.len() == 7 } else { sx.len() >= 8 });
    // pool roles: act, c0 (carries), bq (adder h / bank lane, and Q's lane 128 while q is parked above Y), the P zero
    // (the adders' zero source); sx: the gate register v, ak (gated act), c (gate temp, decision / bit in flight)
    // the 13-lane layout (sz, sw, bq, cmpc, f, g): act on g, the adders' carry c0 on f, Q's lane 128 on bq, the
    // zero source (sc.zeros) on cmpc
    let (act, c0, x128, pzero) = (sc.g, sc.f, sc.bq, sc.cmpc);
    assert_eq!(sc.zeros, vec![pzero]);
    // The retired physical SX7 is replaced by SX1 only between complete
    // predicates/V calls. Every decoder below excludes the held flight.
    let (ak, mut c) = (sx[VB], if sx7_retired { sx[1] } else { sx[VB + 1] });
    let precision24 = (0..=17).contains(&k) && (n == 259 + k || r258c) && nq == 128 && sx.len() == (if sx7_retired { 7 } else { 8 })
        && dirty.len() >= 258 && (cp.h == k + 2 || r258c)
        && cp.sz.0 >= 57 && cp.sz.1 <= 256;
    let fixed_hr = precision24 && k == 0 && cp.hr && cp.sy.1 <= fixed_symax()
        && !(cp.sw || cp.psw || cp.dl || cp.dq)
        && std::env::var_os("B7A_A_HR").is_some();
    let fixed_ht = precision24 && k == 0 && cp.ht && cp.sy.1 <= fixed_symax()
        && !(cp.sw || cp.psw || cp.dl || cp.dq)
        && std::env::var_os("B7A_A_HT").is_some();
    let direct_fixed=direct_fixed_middle::current();
    if q.contains(&x128) {
        assert!(direct_fixed.is_some() && (fixed_hr || fixed_ht));
        assert!(sx7_retired && pool4 && payload258 && precision24 && k==0 && n==257);
        assert_eq!(x128,q[cp.sy.1]);
    }
    let joint_fixed=(joint_size::enabled()||direct_fixed.is_some())&&(fixed_hr||fixed_ht);
    // Paid accuracy for the complete direct fixed-HR family.  This is a
    // public architecture/phase selection, never an input/quotient test.
    // Crossing P1 retains its existing head policy.
    let paid_fixed_hr = direct_fixed.is_some() && fixed_hr;
    // Pay the same extra head bit for the complete fixed HT family. Low
    // public Y lends a suffix; high public Y uses the same bounded repark
    // extended below with its existing done/counter guard.
    let paid_fixed_ht = direct_fixed.is_some() && fixed_ht;
    let paid_fixed_head = paid_fixed_hr || paid_fixed_ht;
    if paid_fixed_ht {
        assert!(pool4 && payload258 && sx7_retired && n == 257 && k == 0);
        assert!(cp.ht && !cp.hr && !(cp.sw || cp.psw || cp.dl || cp.dq));
        assert!(klane_r() && cp.sz.0 >= 25 + 33);
    }
    if paid_fixed_hr {
        assert!(pool4 && payload258 && sx7_retired && n == 257 && k == 0);
        assert!(cp.hr && !cp.ht && !cp.dn && !(cp.sw || cp.psw || cp.dl || cp.dq));
        assert!(klane_r() && cp.sz.0 >= 25 + 33);
    }
    let fixed_size_loans:Vec<QubitId>=if joint_fixed {
        assert_eq!(fd.sy.len(),8);
        let owners=direct_fixed.as_ref().map(|l|l.reserved_size.to_vec())
            .unwrap_or_else(||q[cp.sy.1+24..cp.sy.1+27].to_vec());
        assert_eq!(&fd.sy[5..8],owners.as_slice());owners
    } else {vec![]};
    // (lowq-672 pool9: the non-crossing columns whose Y reaches past 116 bits have no public Q room for R's four
    // extra lanes: they run the crossing sessions and the two-engine tiers too)
    let b8b_cross = precision24 && k == 0 && (cp.sw || cp.psw || cp.dl || cp.dq || l672_bigy(cp))
        && std::env::var("B8B_O3").as_deref() == Ok("1");
    let p1_cross = b8b_cross && std::env::var("B12A_P1").as_deref() == Ok("1");
    let joint_p1 = joint_size::enabled() && fd.sy.len()==5 && p1_cross;
    let flight_sel = c660_flight_sel() && p1_cross;
    if flight_sel { assert!(pool4 && mid8()); c = sx[1]; }
    let flight_shared = flight_sel || sx7_retired;
    // Paid crossing width; fixed paths retain their explicit inherited23
    // policy and original park/R geometry. Payload KE is globally30.
    let qf = if pool4 && (fixed_hr || fixed_ht) { 23 } else { super::mid2::QF };
    let bmax = 258usize.saturating_sub(cp.sz.0 + cp.sy.0).min(qf);
    let kmax = bmax.min(mt);
    if pool4 {
        assert!(fixed_hr || fixed_ht || p1_cross, "pool4 requires the inherited fixed/P1 schedule");
        assert_eq!(std::env::var("FD_DINV_NOPAD").as_deref(), Ok("1"));
        assert_eq!(sc.sz[4], sx[4]);
    }
    // Complete V boundaries return flight SX7. It is never borrowed while
    // an arithmetic decision is held there; code bit4 remains untouched.
    let boundary_tmp = if pool4 { c } else { c0 };
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
    // (lowq-672 pool9: Q[122..126) are R lanes outside the tier columns)
    // The fourth lost raw-size owner is funded by a full-lifetime Q loan.
    // For SYhi<96 it is beyond the entire park; at SYhi=96 the four high
    // quotient cells are reparked below Y's public head (see fixed_repark).
    // One additional clean remainder owner buys the 25th HR head bit.
    // Low public Y uses an unparked suffix.  Higher Y lends one additional
    // fixed quotient slot around COMPLETE parked V forms only; the old
    // six/nine-owner R ordering and its raw-size remaps stay unchanged.
    // Start repark at public hi85: lending suffix Q118 there would shrink
    // the two-owner clean comparator bank to one and change its family.
    let paid_hr_repark: Option<(usize,usize,usize)> = if !paid_fixed_head || cp.sy.1 <= 83 {None}
        else if cp.sy.1 < 94 {
            assert!(cp.sz.0 + cp.sy.1 >= 248);
            Some((16,cp.sy.1+17,cp.sy.1-7))
        } else {
            assert!(cp.sz.0 + cp.sy.1 >= 254);
            Some((13,cp.sy.1+14,cp.sy.1-10))
        };
    let paid_hr_owner = paid_fixed_head.then(|| {
        let index = paid_hr_repark.map(|(_,source,_)|source).unwrap_or(cp.sy.1+33);
        assert!(index < 120 && index < loan_end && !fd.cnt.contains(&q[index]));
        q[index]
    });
    let mut fixed_r_loans: Vec<QubitId> = if let Some(layout)=&direct_fixed {
        assert!(pool5&&(fixed_hr||fixed_ht)&&kmax==23);
        layout.reciprocal_loans.clone()
    } else if pool5 && (fixed_hr || fixed_ht) {
        assert_eq!(kmax, 23);
        assert!(cp.sz.0 + cp.sy.1 >= 239);
        assert!(cp.sy.1 >= 28 && cp.sy.1 + 23 < 120);
        if joint_fixed {
            assert!(payload258);
            if cp.sy.1<=87 {q[cp.sy.1+27..cp.sy.1+33].to_vec()}
            else {
                assert!(cp.sz.0+cp.sy.1>=if cp.sy.1>=94 {244}else{241});
                let mut owners:Vec<_>=(17..23).map(|kb|q[cp.sy.1+1+kb]).collect();
                if cp.sy.1>=94 {owners.extend((14..17).map(|kb|q[cp.sy.1+1+kb]));}
                owners
            }
        } else if payload258 {
            // Low public Y has six globally zero cells beyond the entire
            // fixed park. Do not repark into low Y/data on done branches.
            // Only the high-Y columns need the six-source repark.
            if cp.sy.1<=90 {
                assert!(cp.sy.1+29<120 && cp.sy.1+24>=26);
                q[cp.sy.1+24..cp.sy.1+30].to_vec()
            } else {
                assert!(cp.sz.0+cp.sy.1>=241 && cp.sy.1>=91);
                (17..23).map(|kb|q[cp.sy.1+1+kb]).collect()
            }
        } else if sx7_retired {
            // One additional complete-V loan replaces the physical SX7 R
            // slot. q_k is reparked to SYhi+17-k below, outside the whole
            // Y-root/SGW wrapper; all five remain excluded from both banks.
            assert!(cp.sz.0 + cp.sy.1 >= 240);
            (18..23).map(|kb| q[cp.sy.1 + 1 + kb]).collect()
        } else if pool4 && cp.sy.1 == 96 {
            (19..23).map(|kb| q[cp.sy.1 + 1 + kb]).collect()
        } else {
            let mut owners: Vec<_> = (20..23).map(|kb| q[cp.sy.1 + 1 + kb]).collect();
            if pool4 { owners.push(q[cp.sy.1 + 24]); }
            owners
        }
    } else { vec![] };
    if let Some(owner)=paid_hr_owner {
        assert!(!fixed_r_loans.contains(&owner) && !fixed_size_loans.contains(&owner));
        fixed_r_loans.push(owner);
    }
    let fixed_r_owner=|lane:QubitId|->QubitId {
        if let Some(layout)=&direct_fixed{return layout.reciprocal_owner(&q,lane);}
        if joint_fixed&&cp.sy.1>=94 {
            for (i,old) in [120usize,121,122].into_iter().enumerate() {
                if lane==q[old]&&fixed_size_loans.contains(&lane) {return fixed_r_loans[6+i];}
            }
        }
        lane
    };
    let p9_ext = |lane: QubitId| super::frogdrop_col::pool9() && q[p9lo()..126].contains(&lane);
    let p_bank: Vec<QubitId> = if p_bank_lo < loan_end {
        q[p_bank_lo..loan_end].iter().copied().filter(|&lane| (k > 1 || lane != q[127]) && (k != 0 || lane != q[126])
            && !sx.contains(&lane)
            && !p9_ext(lane) && !fixed_r_loans.contains(&lane)&&!fixed_size_loans.contains(&lane)
            && !(n == 257 && (fixed_hr || fixed_ht)
                && std::env::var("B12A_P1").as_deref() == Ok("1") && lane == q[fixed_r_extra])).collect()
    } else { vec![] };
    assert!(!p_bank.iter().any(|q| dirty.contains(q) || ring.contains(q) || sx.contains(q)
        || sc.sz.contains(q) || [act, c0, x128, pzero, ph, sc.sw].contains(q)));
    // Releasing the old unparked fourth loan can grow the threshold bank.
    // Preserve the parent's comparator family on arbitrary inactive R,
    // especially counter-bearing fixed HT: clean compare and TTK have
    // different joint maps when the residual top is nonzero. Extra clean
    // owners may fund thresholds, but must not silently change that map.
    let mut p_andc = p_bank.clone();
    if sx7_retired && (fixed_hr || fixed_ht) {
        let old_loans: Vec<_> = if cp.sy.1 == 96 {
            (19..23).map(|kb| q[cp.sy.1 + 1 + kb]).collect()
        } else {
            (20..23).map(|kb| q[cp.sy.1 + 1 + kb])
                .chain(std::iter::once(q[cp.sy.1 + 24])).collect()
        };
        let old_count = if p_bank_lo < inherited_loan_end {
            q[p_bank_lo..inherited_loan_end].iter().filter(|&&lane| lane != q[127] && lane != q[126]
                && !p9_ext(lane) && !old_loans.contains(&lane) && lane != q[120]).count()
        } else { 0 };
        if old_count < 2 { p_andc.truncate(1); }
    }
    let fixed_ht_bank = if fixed_ht {
        // The extra low-Y R owner is beyond every quotient park and is
        // returned by the complete V pair. Restore its ORIGINAL position
        // in the later HT adder bank; it is never lent while R is live.
        if paid_fixed_ht && cp.sy.1<=83 {
            let extra=paid_hr_owner.unwrap();
            q.iter().copied().filter(|v|p_bank.contains(v)||*v==extra).collect()
        }else{p_bank.clone()}
    } else { vec![] };
    // N277 has physical K18 and h20. Keep the 24-bit head and 25-lane remainder:
    // ring[0..19] plus sx[1..5]. The divisor's high zero is virtual, so
    // ring[19] serves R and the V window's unused top position. External
    // q19..q23 live in returned SX owners between V calls and park before R.
    // sx[0] (the quotient lane) is returned before each stage1_v geometry
    // query, so it can hold gt0 until that query is inverted. This alias is
    // exclusive to stage1_v; stage1_fwd keeps its original distinct gt0.
    // agent_lowq_quot: N = 259 + K (K 0..=17, h = K + 2) with the K-lane remainder (24 lanes)
    // The physical window starts at K+1=19 in that legacy geometry. Preserve
    // the entire selected head, including P1's additional low head lane.
    if std::env::var_os("QUOT_MIDDBG").is_some() {
        eprintln!("MIDDBG n {} k {} h {} sz {:?} sy {:?} kmax {} mt {} p24 {} hr {} ht {} sw {} dl {} dq {} dn {} tt {}",
                  n, k, cp.h, cp.sz, cp.sy, kmax, mt, precision24, cp.hr, cp.ht, cp.sw, cp.dl, cp.dq, cp.dn, cp.tt);
    }
    let top_head = if p1_cross { P1_HEAD } else if paid_fixed_head { 25 } else if precision24 { 24 } else { k };
    // ---- recordings
    let dest_r: std::collections::BTreeSet<usize> = (0..ws + 1 + TC).chain(n - top_head..n).collect();
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
    // (lowq-672: the b8b sessions run on the SGW forms)
    let zoff_on = !pool5 && precision24 && !route_x128 && !(b8b_cross && l672_tier()) && std::env::var("FD_MIDG_ZOFF").map(|v| v == "1").unwrap_or(false)
        && cp.sz.1 - cp.sz.0 < 128 && (sc.sz.len() == 8 || (k <= 6 && sc.sz.len() == 9));
    let zlo = if zoff_on { cp.sz.0 } else { 0 };
    let zshift = rec(b, |b| if zoff_on {
        // Col 0's pool8 code is sz - 217.  Its P frame is still sz - zlo.
        let add = zlo - if super::frogdrop_col::c55_pool8() && cp.col == 0 { 217 } else { 0 };
        super::frogdrop::add_const_dirty_exact(b, &sc.sz, add, &dirty);
    });
    let rot_sz = |b: &mut B, d: &std::collections::BTreeSet<usize>| {
        if joint_p1 {
            let view=joint_size::View::from_fd(fd,true);
            joint_frame::rotate(b,&ring,&sc.sz[..5],&view,[sx[0],c,pzero,ak],
                true,cp.sz,d,&dirty);
        } else if pool5 {
            // Retain the official frame's public range and exact DOWN
            // support. New size arithmetic only borrows restored dirt;
            // it does not add a ring read/write to the intervening body.
            if cp.sz.0 >= 1 && cp.sz.0 <= cp.sz.1 && cp.sz.1 <= 256 {
                sumframe::rot_raw_clean_care(b, &ring, &sc.sz[..5], &fd.sy,
                    true, &dirty, boundary_tmp, cp.sz.0, cp.sz.1, d);
            } else {
                sumframe::rot_raw_clean(b, &ring, &sc.sz[..5], &fd.sy, true, &dirty, boundary_tmp);
            }
        }
        else if zoff_on { super::frogdrop::rot_by_off_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, d); }
        else { rot_by_range_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty, d); }
    };
    let prot = rec(b, |b| rot_sz(b, &dest_r));
    // At N257 Z's leading one is also the window zero. Flip the decoded
    // leading lane in natural coordinates for the entire V stay.
    let zflip = if n == 257 {
        if joint_p1 {
            let view=joint_size::View::from_fd(fd,true);
            rec(b,|b|joint_frame::lane_query(b,&ring,&sc.sz[..5],&view,
                [sx[0],c,pzero,ak],cp.sz,n-1,None,&dirty))
        } else if pool5 && cp.sz.0 >= 1 && cp.sz.0 <= cp.sz.1 && cp.sz.1 <= 256 {
            rec(b, |b| sumframe::raw_lane_query(b, &ring, &sc.sz[..5], &fd.sy,
                boundary_tmp, cp.sz.0, cp.sz.1, n - 1, None, &dirty))
        } else {
            rec(b, |b| { b.play(&prot, false); b.x(ring[n - 1]); b.play(&prot, true); })
        }
    } else { vec![] };
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
    assert!(!pool5 || sgw_on, "pool5 requires the five-bit gap V view");
    let (r5, r6) = if !fixed_r_loans.is_empty() { (fixed_r_loans[0], fixed_r_loans[1]) }
        else if sgw_on { (sc.sz[5], sc.sz[6]) } else { (fd.sy[5], fd.sy[6]) };
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
    let sw_r = precision24 && klane_r() && ycomp_r && k <= 9 && (!sz7_r || k7)
        && (!sc.sz.contains(&sc.sw) || !fixed_r_loans.is_empty());
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
    let wzero = if n == 257 { ring[n - 1] } else { ring[ws] };
    let zero_pos = if n == 257 { n - 1 } else { ws };
    // P1 crossing plays use their own dirty pair over Y's low P1_HEAD-1
    // lanes and a returned top owner (SX7 under pool5).
    // The legacy reciprocal is never played there and would reserve lanes
    // across the middle switch witness for no executed record.
    let mut reciprocal_r = if p1_cross { vec![] } else { ring[0..ws].to_vec() };
    if !p1_cross && precision24 && klane_r() {
        // agent_lowq_quot: 24 lanes, ring[0..=K+1] (the window top shared as in the virtual zero) + sx[1..] (+ c0
        // below K15): sx[6], sx[7] and c0 are idle while the V form is entered or left, so the park's reserve is
        // R-free there (QUOT_RES_A)
        reciprocal_r.push(wzero);
        let tail: Vec<QubitId> = if ycomp_r {
            let rcarry = if pool4 { assert_eq!(fixed_r_loans.len(), (if joint_fixed&&cp.sy.1>=94 {9} else if payload258 {6} else if sx7_retired { 5 } else { 4 }) + usize::from(paid_fixed_head)); fixed_r_loans[3] } else { c0 };
            let mut t = vec![rcarry, r5, r6, pzero];
            if sz7_r { t.push(if !fixed_r_loans.is_empty() { fixed_r_loans[2] } else { sc.sz[7] }); }
            if ph_r { t.push(ph); }
            // Fixed columns end their parked Y band below Q[120]. At N257
            // P1, Q[120] replaces the old sw R slot; column 138 is BIGY.
            if sw_r || swz_r {
                let fixed_p1 = n == 257 && (fixed_hr || fixed_ht)
                    && std::env::var("B12A_P1").as_deref() == Ok("1");
                if fixed_p1 { assert!(cp.sy.1 + kmax + 1 <= fixed_r_extra); }
                t.push(if fixed_p1 { fixed_r_owner(q[fixed_r_extra]) } else { sc.sw });
            }
            if sy7_r && !(yroot_r && k == 6) { t.push(fd.sy[7]); }
            if x128_r { t.push(x128); }
            if vh1_r { t.push(if payload258 { fixed_r_loans[5] } else if n == 257 { payload_root } else { ring[n - 1] }); }
            if yroot_r { t.push(yroot); }
            if actr { t.push(act); }
            if q127_r { t.push(q[127]); }
            if q126_r { t.push(q[126]); }
            if inplace_r { t.push(sx[0]); }
            t
        } else { vec![c0, pzero] };
        if super::frogdrop_col::pool9() {
            // lowq-672 pool9: sx[2..6] are bq / cmpc / f / g here; R = ring[0..2) + sx1, sx6, sx7 + the tail (20
            // lanes). The tier columns run their engines on it (less h); every other column takes four Q lanes
            // above its public park extent (Q[122..126): fixed sy <= 98, chunked sy <= 116)
            assert!(k == 0 && ycomp_r && t_len_ok(&tail), "lowq-672 pool9 R: K0 only");
            reciprocal_r.extend([sx[1], sx[6], if sx7_retired { fixed_r_loans[4] } else { sx[7] }]);
            reciprocal_r.extend(&tail);
            // (a tier column's 24-lane R serves only its unplayed legacy forms; its engines take R less these lanes)
            if !(b8b_cross && l672_tier()) {
                let ext_ok = if fixed_hr || fixed_ht { cp.sy.1 + kmax + 1 <= p9lo() } else { cp.sy.1.min(nq) + 6 <= p9lo() };
                assert!(ext_ok, "lowq-672 pool9: column {} (sy {:?}) has no public Q room for R", cp.col, cp.sy);
            }
            reciprocal_r.extend(q[p9lo()..126].iter().copied().map(fixed_r_owner));
        } else {
            reciprocal_r.extend(sx[1..8].iter().copied().chain(tail).take(22 - k));
        }
        if std::env::var_os("L672_RDBG").is_some() {
            let nm = |q: QubitId| -> String {
                if let Some(i) = sx.iter().position(|&x| x == q) { return format!("sx{i}"); }
                if let Some(i) = sc.sz.iter().position(|&x| x == q) { return format!("sz{i}"); }
                if let Some(i) = fd.sy.iter().position(|&x| x == q) { return format!("sy{i}"); }
                if let Some(i) = q_all_pos(&fd.q, q) { return format!("Q{i}"); }
                if let Some(i) = ring.iter().position(|&x| x == q) { return format!("r{i}"); }
                if q == ph { return "ph".into(); } if q == sc.sw { return "sw".into(); }
                format!("?{}", q.0)
            };
            let names: Vec<String> = reciprocal_r.iter().map(|&q| nm(q)).collect();
            let uniq: std::collections::BTreeSet<QubitId> = reciprocal_r.iter().copied().collect();
            eprintln!("L672_RDBG col {} b8b {} sgw {} zoff {} len {} uniq {} {:?}", cp.col, b8b_cross, sgw_on, zoff_on,
                      reciprocal_r.len(), uniq.len(), names);
        }
    } else if !p1_cross && precision24 {
        assert_eq!(k, 17, "the 25-lane remainder is the N276 form");
        reciprocal_r.push(ring[k + 1]); reciprocal_r.extend([sx[1], sx[2], sx[3], sx[4], sx[5]]);
    }
    if let Some(owner)=paid_hr_owner {
        // Append at the high end of the K-lane residual.  stage1_v and its
        // virtual-leading-one compare use zh.len()/R.len() throughout;
        // the old low R ordering and the in-place flight owner are retained.
        assert!(precision24 && klane_r() && !p1_cross && reciprocal_r.len()==24);
        assert!(!reciprocal_r.contains(&owner));
        reciprocal_r.push(owner);
    }
    // The returned Q bank can hold the early threshold while the comparator
    // and each window gate run, then is returned before the next V play.
    let clean_gate_lane = if precision24 && inplace_r { p_bank.first().copied() } else { None };
    let mut p_gt = if precision24 { vec![clean_gate_lane.unwrap_or(if inplace_r { sc.sz[0] } else { sx[0] })] }
                   else { sx[2..4].to_vec() };
    if !precision24 { if let Some(&third) = p_bank.first() { p_gt.push(third); } }
    let zh: Vec<QubitId> = ring[n - top_head..n].to_vec();
    if precision24 && !p1_cross {
        assert_eq!(reciprocal_r.len(), if klane_r() { top_head } else { top_head + 1 });
        let unique: std::collections::BTreeSet<QubitId> = reciprocal_r.iter().copied().collect();
        assert_eq!(unique.len(), reciprocal_r.len());
        assert!(!reciprocal_r.iter().any(|q| (zh.contains(q) && !(vh1_r && *q == ring[n - 1]))
            || p_gt.contains(q) || (!actr && *q == act)
            || dirty.contains(q) || p_bank.contains(q) || (sc.sz.contains(q) && !(sz7_r && *q == sc.sz[7])
                && !(sgw_on && (*q == sc.sz[5] || *q == sc.sz[6])) && !(swz_r && *q == sc.sw))
            || (!x128_r && *q == x128) || (!sw_r && !swz_r && *q == sc.sw) || (!ph_r && *q == ph) || (k >= 15 && *q == c0) || (!pzero_r && *q == pzero)
            || (!ycomp_r && fd.sy.contains(q)) || fd.sy[..5].contains(q) || (!sy7_r && fd.sy[7] == *q)
            || (!super::frogdrop_col::pool9() && sx.iter().enumerate().any(|(i, x)| !(i == 0 && inplace_r) && !(1..=22 - k.min(17)).contains(&i) && x == q))));
        assert_eq!(p_gt[0], clean_gate_lane.unwrap_or(if inplace_r { sc.sz[0] } else { sx[0] }));
        assert!(!zh.iter().any(|q| sx.contains(q) || sc.sz.contains(q)
            || (n != 257 && *q == wzero) || [act, c0, x128, pzero, ph, sc.sw].contains(q)
            || dirty.contains(q) || p_bank.contains(q)));
    }
    let s1 = S1 { r: reciprocal_r, f: sx[0], zero: wzero, sgn: sx[0], gt: p_gt,
                  anc: p_bank.iter().skip(1).copied().collect(),
                  andc: p_andc, chain: if clean_gate_lane.is_some() { p_bank[1..].to_vec() } else { p_bank },
                  dirty: dirty.clone() };
    // An unparked SGW play has no quotient chunk in Q. The K0/K1 and
    // pool5 fixed reciprocal owners remain excluded from the returned bank.
    let unpark_lo = lsb.max(cp.sy.1.min(nq));
    // (lowq-672 tier columns: Q above Y down to E0 is tier B's R; no returned bank)
    let unpark_bank: Vec<QubitId> = if b8b_cross && l672_tier() { vec![] } else if unpark_lo < loan_end {
        q[unpark_lo..loan_end].iter().copied().filter(|&lane| (k > 1 || lane != q[127]) && (k != 0 || lane != q[126])
            && !sx.contains(&lane)
            && !p9_ext(lane) && !fixed_r_loans.contains(&lane)&&!fixed_size_loans.contains(&lane)
            && !(n == 257 && (fixed_hr || fixed_ht)
                && std::env::var("B12A_P1").as_deref() == Ok("1") && lane == q[fixed_r_extra])).collect()
    } else { vec![] };
    let mut s1u = s1.clone();
    if !p1_cross && sgw_on && inplace_r && unpark_bank.len() > s1.andc.len() {
        assert!(!unpark_bank.iter().any(|q| dirty.contains(q) || s1.r.contains(q)
            || ring.contains(q) || sx.contains(q) || sc.sz.contains(q)
            || [act, c0, x128, pzero, ph, sc.sw].contains(q)));
        s1u.gt = vec![unpark_bank[0]];
        s1u.anc = unpark_bank[1..].to_vec();
        s1u.andc = unpark_bank.clone();
        s1u.chain = unpark_bank[1..].to_vec();
        // Preserve the parked comparator's all-data permutation. An idle
        // counter can occupy R's top lane, outside the clean comparator's
        // residual-top-zero contract. The returned bank still funds the
        // clean threshold, but must not switch a TTK pair to clean compare.
        if s1.andc.len() < 2 { s1u.andc.truncate(1); }
    }
    if joint_fixed&&cp.col==139 {
        assert!(s1.andc.len()<2&&s1u.andc.len()<2,
            "counter-passenger V pair must retain the parent's all-data TTK family");
        assert!(s1.r.contains(&q[127])&&s1u.r.contains(&q[127]));
    }
    let win: Vec<QubitId> = if n == 257 {
        std::iter::once(wzero).chain(ring[..TC].iter().copied()).collect()
    } else { ring[ws..ws + 1 + TC].to_vec() };
    let szr = (cp.sz.0, cp.sz.1);
    S1_ZLO.with(|z| z.set(zlo));
    S1_NOACT.with(|c| c.set(precision24 && (actr || std::env::var("LANE_NOACT").map(|v| v == "1").unwrap_or(false))));
    let fv = if p1_cross { vec![] } else { stage1_v(b, &zh, &win, &sc.sz, szr, &s1, act, true) };
    let fr = if p1_cross { vec![] } else { stage1_v(b, &zh, &win, &sc.sz, szr, &s1, act, false) };
    S1_ZLO.with(|z| z.set(0));
    // enter / leave the V form on the act shots: X += T - G (R cleared by its own replay); v must be clear (sx)
    let vform = if p1_cross { vec![] } else { rec(b, |b| {
        b.play(&prot, false);
        if vh1_r && n != 257 { b.x(ring[n - 1]); }
        b.play(&fv, false);
        b.play(&fr, true);
        if vh1_r && n != 257 { b.x(ring[n - 1]); }
        b.play(&prot, true);
    }) };
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
    let vform_p = if p1_cross || !ycomp_on || ycomp_r { vform.clone() } else {
        let rc: Vec<QubitId> = s1.r.iter().map(|&q| if q == sx[6] { fd.sy[5] } else if q == sx[7] { fd.sy[6] } else { q })
            .collect();
        let s1c = S1 { r: rc, f: s1.f, zero: s1.zero, sgn: s1.sgn, gt: s1.gt.clone(), anc: s1.anc.clone(),
                       andc: s1.andc.clone(), chain: s1.chain.clone(), dirty: s1.dirty.clone() };
        S1_ZLO.with(|z| z.set(zlo));
        let fvc = stage1_v(b, &zh, &win, &sc.sz, szr, &s1c, act, true);
        let frc = stage1_v(b, &zh, &win, &sc.sz, szr, &s1c, act, false);
        S1_ZLO.with(|z| z.set(0));
        rec(b, |b| { b.play(&prot, false); b.play(&fvc, false); b.play(&frc, true); b.play(&prot, true); })
    };
    // every V-form play (parked or not) runs in the compressed form: nothing inside reads sy
    let vform = if p1_cross || !ycomp_on { vform } else {
        rec(b, |b| { b.play(&ycomp, false); b.play(&vform_p, false); b.play(&ycomp, false); })
    };
    // (lowq-size FD_MIDG_SGW, ported) separate recordings for the unparked plays (sy whole) and the parked ones (sy[7]
    // lent, low7 = 0 = 128)
    let mut b8b_forms: Vec<Vec<G>> = vec![];
    let mut b8b_forms_ht: Vec<Vec<G>> = vec![];
    // lowq-672: the HT plays' own unparked form (two-engine tiers: no margin)
    let mut vform_ht: Option<Vec<G>> = None;
    let (vform, vform_pk) = if joint_p1 {
        assert!(pool4 && n==257 && P1_HEAD==32 && TC==32);
        let view=joint_size::View::from_fd(fd,true);
        let flag=rec(b,|b|view.xor_range(b,1,31,ak,&[],&[],&dirty));
        let swap=rec(b,|b|for i in 0..P1_HEAD-1 {b.cswap(ak,q[i],q[64+i]);});
        let gap=rec(b,|b|for &q in &sc.sz[..5] {b.x(q);});
        let mut rp=q[..P1_HEAD-1].to_vec();rp.push(wzero);
        let sp=S1 {r:rp,f:wzero,zero:wzero,sgn:wzero,gt:vec![sx[0]],
            anc:vec![pzero,c],andc:vec![sx[0]],chain:vec![],dirty:dirty.clone()};
        S1_GATE.with(|g|*g.borrow_mut()=S1Gate::Joint {
            view:view.clone(),gap:sc.sz[..5].to_vec(),carry:pzero});
        let noact=S1_NOACT.with(|g|g.replace(true));
        let core=b12a_dirty_v_pair(b,&zh,&win,&sc.sz,szr,&sp,act,true);
        S1_NOACT.with(|g|g.set(noact));
        S1_GATE.with(|g|*g.borrow_mut()=S1Gate::Sz);
        // The complete raw-address bridge returns its four owners before
        // P1's dirty reciprocal borrows them. Encoded metadata survives the
        // core; early gates read it directly with no U-word mutation.
        let form=rec(b,|b| {
            b.play(&prot,false);b.play(&gap,false);
            b.play(&flag,false);b.play(&swap,false);
            b.play(&core,false);
            b.play(&swap,true);b.play(&flag,true);
            b.play(&gap,true);b.play(&prot,true);
        });
        assert!(route_free_phase_ports(&[form.clone()],ph,act));
        b8b_forms=vec![form.clone();3];
        b8b_forms_ht=vec![form.clone();3];
        vform_ht=Some(form.clone());
        (form,vec![])
    } else if !sgw_on { (vform.clone(), vform) } else {
        let a = &sc.sz;
        let sy = &fd.sy;
        assert!(sy.len() == 8 && !dirty.iter().any(|q| a.contains(q) || sy.contains(q) || *q == c || *q == act));
        // A := 1 - A - sy (an involution); the parked form adds 128 where low7 = 0, zero-extending low7 by sx[7]
        // (an R lane: |0> on the act shots before fv and after fr^-1; the transform is an involution on every shot)
        let sg_u = rec(b, |b| {
            if pool5 { for &q in &a[..5] { b.x(q); } return; }
            super::arith::ttk_add(b, &sy[..8], &a[..8], None, None);
            for &x in a.iter() { b.x(x); }
            super::modp_frogdrop::inc_dirty_free(b, &a[1..], &dirty);
        });
        let sg_p = rec(b, |b| {
            if pool5 { for &q in &a[..5] { b.x(q); } return; }
            let mut ax: Vec<QubitId> = sy[..7].to_vec();
            ax.push(sx[7]);
            super::arith::ttk_add(b, &ax, &a[..8], None, None);
            let zero: Vec<(QubitId, bool)> = sy[..7].iter().map(|&q| (q, true)).collect();
            mc_xor(b, &zero, a[7], &[], &dirty);
            for &x in a.iter() { b.x(x); }
            super::modp_frogdrop::inc_dirty_free(b, &a[1..], &dirty);
        });
        // the gates' u: sy += A (8 lanes) / low7 += A[..7] (mod 128); undone after fr^-1, when A[5..8] are R-free again
        let u_u = rec(b, |b| if pool5 { sumframe::add_zero_extended(b, &a[..5], &sy[..8], &dirty); }
            else { super::arith::ttk_add(b, &a[..8], &sy[..8], None, None); });
        let u_p = rec(b, |b| if pool5 { sumframe::add_zero_extended(b, &a[..5], &sy[..7], &dirty); }
            else { super::arith::ttk_add(b, &a[..7], &sy[..7], None, None); });
        // The V-time order sz>=sy makes g[4]=0 whenever a K2 park can
        // occupy x128: sy+offset=128 with offset<=7 gives sy>=121 and g<=15.
        // The four disjoint prefixes select sy low7 in {0,121..127}, i.e.
        // the active range 121..128. U forms run after this swap. On selected
        // shots with a parked 1, the routed gap may gain 16, but both U8 and
        // UPark early gates still return false for every j<=25.
        let route = rec(b, |b| if route_x128 && !(pool4 && p1_cross) {
            // Pool4 P1 uses Q0..30 and ring256, never these high-Q owners.
            // Its route-free counterpart below preserves raw gap exactly.

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
        });
        let (dk, d2) = (dirty[dirty.len() - 1], dirty[dirty.len() - 2]);
        let p1 = p1_cross;
        S1_GATE.with(|g| *g.borrow_mut() = S1Gate::U8 { u: sy[..8].to_vec() });
        let fvu = if p1 { vec![] } else { stage1_v(b, &zh, &win, &sc.sz, szr, &s1u, act, true) };
        let fru = if p1 { vec![] } else if s1u.andc == s1.andc { fr.clone() }
                  else { stage1_v(b, &zh, &win, &sc.sz, szr, &s1u, act, false) };
        S1_GATE.with(|g| *g.borrow_mut() = S1Gate::UPark { u: sy[..7].to_vec(), g: a[..5].to_vec(), dk, d2 });
        let fvp = if p1 { vec![] } else { stage1_v(b, &zh, &win, &sc.sz, szr, &s1, act, true) };
        let fvp_u = if p1 { vec![] } else if sy7n_r && s1u.andc != s1.andc {
            stage1_v(b, &zh, &win, &sc.sz, szr, &s1u, act, true)
        } else { fvp.clone() };
        // B12A: swap Y's low P1_HEAD-1 bits into Q[64..) only when sy <32.
        // These alternate lanes precede the counter and lie above Y plus
        // every quotient park on that branch (sy+29 <=60).
        // sg_p and route leave sy raw; u_p changes it, so the swap brackets u_p.
        let p1_swap = if p1 { Some(rec(b, |b| {
            assert!(P1_HEAD <= 32 && 64 + P1_HEAD - 1 <= 121);
            for i in 0..P1_HEAD - 1 { b.cswap(sx[6], q[i], q[64+i]); }
        })) } else { None };
        // The ordinary two-engine tiers are retained only when P1 is off.
        let tier = b8b_cross && (l672_tier() || p1);
        let (eng_hr, eng_ht): (Vec<Gate>, Vec<Gate>) = if !tier { (vec![], vec![]) } else if p1 {
            // The high SZ owner aliases act/w; the returned flight owns
            // the complete dirty reciprocal's top lane instead.
            let rtop = if pool4 { wzero } else if pool5 { sx[7] } else { a[5] };
            let mut rp = q[..P1_HEAD - 1].to_vec(); rp.push(rtop);
            assert_eq!(zh.len(), P1_HEAD);
            assert_eq!(rp.iter().copied().collect::<std::collections::BTreeSet<_>>().len(), P1_HEAD);
            assert!(!rp.iter().any(|q| dirty.contains(q)
                || ((zh.contains(q) || win.contains(q)) && !(pool4 && *q == wzero))));
            if pool4 { assert_eq!(zh[P1_HEAD-1], wzero); assert_eq!(win[0], wzero); }
            // Every complete crossing V boundary returns SX0, including
            // the paired q0 moves and top-bit queries. The SGW/U/route/P1
            // wrappers do not use it. A singleton bank only enables the
            // existing clean threshold; the fused TTK comparator remains
            // unchanged because its clean-bank alternative requires >=2.
            assert!(!rp.contains(&sx[0]) && !dirty.contains(&sx[0]));
            let sp = S1 { r: rp, f: rtop, zero: wzero, sgn: rtop, gt: vec![sx[0]],
                // Cross predicates, prot and parked wrappers return pzero/c0
                // before every engine. Cache two carry products only during
                // each comparator, returning both before the threshold query.
                // The gt.len()==1 window path never otherwise reads anc.
                anc: if pool5 { vec![pzero, if pool4 { c } else { c0 }] } else { vec![] },
                andc: if pool5 { vec![sx[0]] } else { vec![] },
                chain: vec![], dirty: dirty.clone() };
            S1_ZLO.with(|z| z.set(zlo));
            let noact = S1_NOACT.with(|c| c.replace(true));
            let ep = b12a_dirty_v_pair(b, &zh, &win, &sc.sz, szr, &sp, act, n == 257);
            S1_NOACT.with(|c| c.set(noact));
            S1_ZLO.with(|z| z.set(0));
            (ep.clone(), ep)
        } else {
            assert!(sy7n_r && s1u.andc == s1.andc, "lowq-672 tier: crossing forms share fvp / fr");
            let (kc, ka) = (l672_kc(), l672_ka());
            assert!((13..24).contains(&ka) && kc <= ka);
            let names = l672_drop_names();
            let hname = l672_h_name();
            assert!(names.contains(&hname), "L672_H must be one of L672_RDROP");
            let h = l672_lane(&hname, &sx, c0, pzero);
            let drop: Vec<QubitId> = names.iter().map(|x| l672_lane(x, &sx, c0, pzero)).collect();
            let p9q: Vec<QubitId> = if super::frogdrop_col::pool9() { q[p9lo()..126].to_vec() } else { vec![] };
            let rc: Vec<QubitId> = s1.r.iter().copied().filter(|x| !drop.contains(x) && !p9q.contains(x)).collect();
            assert_eq!(rc.len(), kc, "lowq-672 common remainder: {} lanes after L672_RDROP", rc.len());
            assert!(rc.contains(&sx[0]), "tier A keeps the in-place flag sx0");
            let e0 = l672_e0();
            let ext: Vec<QubitId> = q[e0..e0 + 24 - kc].to_vec();
            assert!(e0 + 24 - kc <= 126 && !ext.iter().any(|x| rc.contains(x) || dirty.contains(x) || *x == yroot));
            let mut ra = rc.clone();
            if l672_sya() {
                assert!(!rc.contains(&fd.sy[5]) && !rc.contains(&fd.sy[6]));
                if r258c { assert!(!rc.contains(&fd.sy[4])); ra.push(fd.sy[4]); }
                ra.extend([fd.sy[5], fd.sy[6]]);
            }
            let mut rb = rc.clone();
            rb.extend(&ext);
            let s1a = S1 { r: ra, ..s1.clone() };
            let s1b = S1 { r: rb, ..s1.clone() };
            let zha: Vec<QubitId> = ring[n - ka..n].to_vec();
            // tier A's act shots have sz <= 257 - E0: its engine has no early-column gates (it reads no sy, sz)
            let szra = (szr.0, szr.1.min(257 - e0));
            assert!(szra.1 + TC < 257);
            S1_ZLO.with(|z| z.set(zlo));
            S1_TIER.with(|t| t.set(Some((h, false))));
            let fva = stage1_v(b, &zha, &win, &sc.sz, szra, &s1a, act, true);
            S1_TIER.with(|t| t.set(Some((h, true))));
            let fvb = stage1_v(b, &zh, &win, &sc.sz, szr, &s1b, act, true);
            S1_TIER.with(|t| t.set(None));
            let fra = stage1_v(b, &zha, &win, &sc.sz, szra, &s1a, act, false);
            let frb = stage1_v(b, &zh, &win, &sc.sz, szr, &s1b, act, false);
            S1_ZLO.with(|z| z.set(0));
            // HR tier A: V -= M 2^u (u = win[TC]'s position) on the even heads, M = 2^(TC + 1 - KA) + 1
            let m: u64 = (1u64 << (TC + 1 - ka)) + 1;
            let wbits: Vec<QubitId> = (1..=TC).rev().map(|i| win[i]).collect();
            let margin = rec(b, |b| {
                // (the one-sided margin only feeds the HR repair: without L671_HRFIX tier A stays two-sided)
                if std::env::var_os("L672_NOMARGIN").is_some() || std::env::var("L671_HRFIX").as_deref() != Ok("1") { return; }
                let ctl = [(h, false), (zha[0], true)];
                for i in 0..TC {
                    if (m >> i) & 1 == 0 { continue; }
                    for &x in &wbits[i..] { b.x(x); }
                    inc_with_controls(b, &wbits[i..], &ctl, &dirty);
                    for &x in &wbits[i..] { b.x(x); }
                }
            });
            // around tier A's engine sy's low seven lanes hold (sy + 16) mod 128 (u_p undone): every tier-A act shot
            // has 112 <= sy <= 128, so sy[5], sy[6] are |0> there (u itself carries the routed parks in its gap)
            let u7 = rec(b, |b| if l672_sya() {
                b.play(&u_p, true);
                super::modp_frogdrop::add_const_exact(b, &fd.sy[..7], None, if r258c { 15 } else { 16 }, &dirty);
            });
            let eh = rec(b, |b| { b.play(&u7, false); b.play(&fva, false); b.play(&fra, true); b.play(&margin, false);
                                  b.play(&u7, true); b.play(&fvb, false); b.play(&frb, true); });
            let et = rec(b, |b| { b.play(&u7, false); b.play(&fva, false); b.play(&fra, true); b.play(&u7, true);
                                  b.play(&fvb, false); b.play(&frb, true); });
            (eh, et)
        };
        let none: Vec<Gate> = vec![];
        let (fv_hr, fr_hr, fv_ht, fr_ht): (&[Gate], &[Gate], &[Gate], &[Gate]) =
            if tier { (&eng_hr, &none, &eng_ht, &none) } else { (&fvp, &fr, &fvp, &fr) };
        S1_GATE.with(|g| *g.borrow_mut() = S1Gate::Sz);
        if b8b_cross {
            b8b_forms = b8b_make_raw_parked_forms(b, &prot, &sg_p, &u_p, fv_hr, fr_hr, p1_swap.as_deref(),
                (vh1_r && n != 257 && !p1).then_some(ring[n - 1]), sy, a, [x128, q[127], q[126]],
                cp.sw.then_some(sc.sw), Some((&route, ph, pzero, boundary_tmp)), &dirty);
            b8b_forms_ht = b8b_make_raw_parked_forms(b, &prot, &sg_p, &u_p, fv_ht, fr_ht, p1_swap.as_deref(),
                (vh1_r && n != 257 && !p1).then_some(ring[n - 1]), sy, a, [x128, q[127], q[126]],
                cp.sw.then_some(if super::frogdrop_col::c55_pool8() { sx[1] } else { sc.sw }),
                Some((&route, ph, pzero, boundary_tmp)), &dirty);
        }
        let mk = |b: &mut B, sg: &[Gate], u: &[Gate], fv: &[Gate], frx: &[Gate]| rec(b, |b| {
            b.play(&prot, false);
            b.play(sg, false);
            b.play(&route, false);
            if let Some(r) = &p1_swap { b.play(r, false); }
            b.play(u, false);
            if vh1_r && n != 257 && !p1 { b.x(ring[n - 1]); }
            b.play(fv, false);
            b.play(frx, true);
            if vh1_r && n != 257 && !p1 { b.x(ring[n - 1]); }
            b.play(u, true);
            if let Some(r) = &p1_swap { b.play(r, true); }
            b.play(&route, true);
            b.play(sg, false);
            b.play(&prot, true);
        });
        if tier { vform_ht = Some(mk(b, &sg_p, &u_p, fv_ht, fr_ht));
            (mk(b, &sg_p, &u_p, fv_hr, fr_hr), if p1 { vec![] } else { mk(b, &sg_p, &u_p, &fvp, &fr) }) }
        else if sy7n_r { (mk(b, &sg_p, &u_p, &fvp_u, &fru), mk(b, &sg_p, &u_p, &fvp, &fr)) }
        else { (mk(b, &sg_u, &u_u, &fvu, &fru), mk(b, &sg_p, &u_p, &fvp, &fr)) }
    };
    S1_NOACT.with(|c| c.set(false));
    // K6: sy7 cleared around every V-form play (an R lane inside)
    let (vform, vform_pk) = if joint_p1 || !sy7n_r { (vform, vform_pk) } else {
        let zero: Vec<(QubitId, bool)> = fd.sy[..7].iter().map(|&q| (q, true)).collect();
        let n7 = rec(b, |b| mc_xor(b, &zero, fd.sy[7], &[], &dirty));
        // P1's sy<32 flag must be formed before n7 erases sy[7] at sy=128.
        let p1_flag = rec(b, |b| if b8b_cross && std::env::var("B12A_P1").as_deref() == Ok("1") {
            mc_xor(b, &[(fd.sy[5], true), (fd.sy[6], true), (fd.sy[7], true)], sx[6], &[], &dirty);
        });
        let w = |b: &mut B, r: &[Gate]| rec(b, |b| {
            b.play(&p1_flag, false);
            b.play(&n7, false); b.play(r, false); b.play(&n7, false);
            b.play(&p1_flag, true);
        });
        if b8b_cross {
            b8b_forms = b8b_forms.iter().map(|r| w(b, r)).collect();
            b8b_forms_ht = b8b_forms_ht.iter().map(|r| w(b, r)).collect();
        }
        vform_ht = vform_ht.map(|r| w(b, &r));
        (w(b, &vform), if p1_cross { vec![] } else { w(b, &vform_pk) })
    };
    // agent_lowq_lane LANE_YROOT: the tree on sy (outside n7 / ycomp / sgw: sy whole there), Y's top to yroot, flipped
    let (vform, vform_pk) = if joint_p1 || !yroot_r { (vform, vform_pk) } else {
        // lowq-672 tiers: the tree only over sy <= 119 and a transposition Q[sy - 1] <-> root for sy >= 120, so the
        // gather never moves a Y / parked bit into tier B's lanes Q[E0..126) (a full tree permutes every leaf lane)
        let tier_tree = b8b_cross && l672_tier();
        let tmax = if tier_tree { yhi.min(119) } else { yhi };
        let leaves: Vec<(usize, QubitId)> = (ylo..=tmax).map(|v| (v, q[v - 1])).collect();
        let mut swaps = vec![];
        let root = swap_tree(&fd.sy, &leaves, fd.sy.len(), &mut swaps);
        assert_eq!(root, yroot);
        let tr = rec(b, |b| {
            for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
            if tier_tree {
                for v in (tmax + 1)..=yhi {
                    let eq: Vec<(QubitId, bool)> = (0..8).map(|i| (fd.sy[i], (v >> i) & 1 == 0)).collect();
                    super::mid2::mc_swap(b, &eq, q[v - 1], root, &[], &dirty);
                }
            }
        });
        let w = |b: &mut B, r: &[Gate]| rec(b, |b| {
            // (LANE_YROOT_BAD=1: negative control, no flip)
            let flip = std::env::var_os("LANE_YROOT_BAD").is_none();
            b.play(&tr, false); if flip { b.x(yroot); } b.play(r, false); if flip { b.x(yroot); } b.play(&tr, true);
        });
        // P1 borrows Q[0..P1_HEAD-1) as D. The old Y-root tree permutes those
        // lanes before the play, so it must leave with the clean-R tier.
        let p1_cross = b8b_cross && std::env::var("B12A_P1").as_deref() == Ok("1");
        if b8b_cross && !p1_cross {
            b8b_forms = b8b_forms.iter().map(|r| w(b, r)).collect();
            b8b_forms_ht = b8b_forms_ht.iter().map(|r| w(b, r)).collect();
        }
        if !p1_cross { vform_ht = vform_ht.map(|r| w(b, &r)); }
        (if p1_cross { vform } else { w(b, &vform) },
         if p1_cross { vec![] } else { w(b, &vform_pk) })
    };
    assert!(!b8b_cross || (b8b_forms.len() == 3 && b8b_forms_ht.len() == 3));
    // q19..q23 occupy sx[1..5] between V calls. Form v in SZ for each
    // threshold query, restoring SZ before any arithmetic or rotation.
    // (ring 258: the frame starts at ring[0], so bits 0..5 are the sx[1..6) slots; only the one-session and chunked
    // searches read them, and at ring 258 every column is fixed or b8b)
    let external_q = |kb: usize| if precision24 && (ws..ws + 5).contains(&kb) { Some(sx[kb - ws + 1]) } else { None };
    assert!(!precision24 || kmax <= if pool4 && p1_cross { super::pointadd_frogdrop::QB } else { 23 });
    // one session stores all of q in the headroom and sx[1..5]
    assert!(!precision24 || chunked() || kmax <= k + 6);
    let qloc = |kb: usize| external_q(kb).unwrap_or(ring[kb]);
    assert!((0..kmax).all(|kb| qloc(kb) != wzero));
    // v = (sz + sy + VOFF) mod 2^VB, in SZ only during ge_k.
    let vbits = if pool5 { 5 } else { VB };
    let vlimit = if pool5 { 32 } else { 40 };
    let v: Vec<QubitId> = sc.sz[..vbits].to_vec();
    let vg = rec(b, |b| {
        if pool5 { return; }
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
    let gate_chain = if pool4 { vec![pzero, x128] } else { vec![c0, pzero, x128] };
    assert_eq!(gate_chain.iter().copied().collect::<std::collections::BTreeSet<_>>().len(), gate_chain.len());
    assert!(!gate_chain.iter().any(|q| v.contains(q) || *q == ak || *q == c));
    // tmp ^= [kb >= 258 - s9] = [v >= 40 - kb]
    let ge_k = |b: &mut B, kb: usize, t: QubitId| {
        b.play(&vg, false);
        super::frogdrop_col::ge_cd(b, &v, (vlimit - kb) as isize, t, &gate_chain, &dirty);
        b.play(&vg, true);
    };
    // ak = a & [kb < 258 - s9] (tmp = c clear again)
    let gate_on = |b: &mut B, kb: usize, a: QubitId| {
        let f1 = b.tof;
        b.play(&vg, false);
        super::frogdrop_col::ge_cd(b, &v, (vlimit - kb) as isize, c, &gate_chain, &dirty);
        b.x(c);
        b.and_c(a, c, ak);
        b.x(c);
        super::frogdrop_col::ge_cd(b, &v, (vlimit - kb) as isize, c, &gate_chain, &dirty);
        b.play(&vg, true);
        super::f1_profile("midg.gate_on", f1, b.tof);
    };
    let gate_off = |b: &mut B, kb: usize, a: QubitId| {
        let f1 = b.tof;
        b.play(&vg, false);
        super::frogdrop_col::ge_cd(b, &v, (vlimit - kb) as isize, c, &gate_chain, &dirty);
        b.x(c);
        b.and_u(a, c, ak);
        b.x(c);
        super::frogdrop_col::ge_cd(b, &v, (vlimit - kb) as isize, c, &gate_chain, &dirty);
        b.play(&vg, true);
        super::f1_profile("midg.gate_off", f1, b.tof);
    };
    let add = |b: &mut B, kb: usize, ctl: QubitId, sub: bool| {
        // A three-owner fixed bridge aliases x128 with the public zero
        // Q[Yhi]. Its fixed HT route uses add_parked's explicit short
        // source; fixed HR uses cmp_y and exact payload carry tails. Do
        // not silently put that role into this generic source/loan bank.
        assert!(!q.contains(&x128), "borrowed fixed x128 reached generic Q adder");
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
        let r = rotz(b, &[zero_pos, kb]);
        b.play(&r, false);
        if undo {
            mc_xor(b, &[(ak, false), (qloc(kb), true)], rv, &[], &dirty);
        } else {
            mc_xor(b, &[(ak, false), (wzero, false)], rv, &[], &dirty);
            mc_xor(b, &[(ak, false), (wzero, true)], qloc(kb), &[], &dirty);
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
    let ra: Vec<QubitId> = if joint_p1 || (res_a.is_some() && sy7_r) { vec![] }
                           else if res_a.is_some() && sw_r { vec![fd.sy[7]] }
                           else if res_a.is_some() && ph_r { vec![sc.sw, fd.sy[7]] }
                           else if res_a.is_some() && pzero_r { vec![ph, sc.sw, fd.sy[7]] }
                           else if res_a.is_some() { vec![pzero, ph, sc.sw, fd.sy[7]] } else { vec![ph, sc.sw, fd.sy[7]] };
    // These generic chunk parks are never played by fixed/P1 nor by
    // N257 S5_NOPARK. Do not construct their obsolete eight-SX reserve.
    let ((q129a, rqa), (q129b, rqb)) = if sx7_retired {
        assert!(fixed_hr || fixed_ht || p1_cross);
        assert_eq!(res_a, Some(0));
        let mut cycle = q.clone(); cycle.push(x128);
        ((cycle.clone(), vec![]), (cycle, vec![]))
    } else {
        (mk_cycle(b, &ra, cp.ht, res_a), mk_cycle(b, &[ph, act, sx[1]], cp.ht, None))
    };
    // (lowq_cross) only a cycle that borrows sy7 needs it normalized: around a sy7-free cycle the normalization would
    // clear sy7 at sy = 128 and the rotation, which reads all of sy, would see 0
    let sy7_normal = if !joint_p1 && q129a.contains(&fd.sy[7]) { borrowed_sy_normal(b, &fd.sy, &dirty) } else { vec![] };
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
    let park = if sx7_retired { vec![] } else { park_for(b, act, &q129a, &rqa, false, kmax, 0) };
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
                           if k == 0 && (36..=113).contains(&cp.col) {
                               v = vec![0];
                               v.extend([1, 3, 6, 11, 17, 23, 29].into_iter().filter(|&x| x < kmax));
                           }
                           if k == 0 && cp.col == 115 {
                               v = vec![0];
                               v.extend([5, 11, 17, 23, 29].into_iter().filter(|&x| x < kmax));
                           }
                           if pool4 && p1_cross {
                               // Legacy chunk records are still constructed below; no
                               // widened residual chunk may exceed the original six slots.
                               v.extend([23, 29].into_iter().filter(|&x| x < kmax));
                           }
                           v.sort_unstable(); v.dedup();
                           v.push(kmax); v };
    assert!(bd.windows(2).all(|w| w[0] < w[1]), "chunk cuts must ascend");
    let nch = bd.len() - 1;
    let chunk = chunked() && nch > 1;
    if n == 257 {
        assert!(!cp.hr || fixed_hr || b8b_cross, "N257 HR requires fixed or crossing route");
        assert!(!cp.ht || fixed_ht || b8b_cross, "N257 HT requires fixed or crossing route");
        assert!(!cp.ht || chunk, "N257 HT requires split stage 5");
    }
    let qch = if chunk { bd[1] } else { qch() };
    assert!(!chunk || bd.windows(2).all(|w| w[1] - w[0] <= k + 6), "a chunk exceeds the K + 6 slots");
    let (sylo_c, syhi_c) = (cp.sy.0.max(1), cp.sy.1.min(nq));
    // decoder prefixes: sx[0..6) less the chunk slots, and the P zero
    let pre_c: Vec<QubitId> = {
        let longest = bd.windows(2).map(|w| w[1] - w[0]).max().unwrap_or(0).max(qch);
        let slots: Vec<QubitId> = (0..longest.max(kmax.saturating_sub(qch))).map(|s| qloc(s)).collect();
        let mut v: Vec<QubitId> = sx[..VB].iter().copied().filter(|x| !slots.contains(x)
            && !(pool4 && (*x == sx[4] || *x == act))
            && !(flight_shared && *x == c)).collect();
        v.push(pzero);
        // lowq-size FD_LOOP_PRE: lane budget of the loops' sy decoders (shorter: dirty toggles, more T)
        if let Some(k) = std::env::var("FD_LOOP_PRE").ok().and_then(|x| x.parse::<usize>().ok()) { v.truncate(k); }
        if flight_shared { assert!(!v.contains(&c)); }
        v
    };
    if q.contains(&x128) {
        // cmp_y/cmp_v use Q[Yhi] as the restored physical source pad.
        // Their interior metadata decoder cannot borrow it concurrently.
        assert!(!pre_c.contains(&x128), "fixed zero source pad is a decoder prefix");
    }
    if super::frogdrop_col::c55_pool8() && cp.ht {
        assert!(!pre_c.contains(&sx[5]), "C55 S3: sx5 stage-5 actl is a decoder prefix");
    }
    // gate_t with v already in SZ (vg played: loops that neither rotate by sz nor read it)
    let gate_v = |b: &mut B, kk: usize, a: QubitId, t: QubitId, on: bool| {
        let f1 = b.tof;
        super::frogdrop_col::ge_cd(b, &v, (vlimit - kk) as isize, t, &gate_chain, &dirty);
        b.x(t);
        if on { b.and_c(a, t, ak); } else { b.and_u(a, t, ak); }
        b.x(t);
        super::frogdrop_col::ge_cd(b, &v, (vlimit - kk) as isize, t, &gate_chain, &dirty);
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
    // Toggle the selected natural top lane exactly when sz+sy+kk=N. The
    // existing six-bit vg form aliases later-column size pairs, so restore
    // the size register and compare the full nine-bit sum for this selector.
    let top_eq_root = |b: &mut B, kk: usize, ctl: QubitId, root: QubitId| {
        if n != 257 { return; }
        let sum = n - kk;
        if pool5 {
            sumframe::xor_sum_eq(b, &v, sum, root, &[(ctl, false)], &dirty);
            return;
        }
        if sum < cp.sz.0 + cp.sy.0 || sum > cp.sz.1 + cp.sy.1 { return; }
        let mut sumreg = sc.sz.clone();
        if sumreg.len() == 8 { sumreg.push(sx[0]); }
        assert_eq!(sumreg.len(), 9);
        let exact = rec(b, |b| {
            b.play(&vg, true);
            super::frogdrop::reg_add_into(b, &sumreg, &fd.sy, &[pzero], c0);
        });
        b.play(&exact, false);
        let value = sum - zlo;
        let mut lits: Vec<(QubitId, bool)> = (0..sumreg.len())
            .map(|i| (sumreg[i], (value >> i) & 1 == 0)).collect();
        lits.push((ctl, false));
        let helpers: Vec<QubitId> = dirty.iter().copied()
            .filter(|&q| q != root && q != ctl && !sumreg.contains(&q)).collect();
        mc_xor(b, &lits, root, &[], &helpers);
        b.play(&exact, true);
    };
    let top_virtual = |b: &mut B, kk: usize| {
        if n != 257 { return; }
        let leaves: Vec<(usize, QubitId)> = (sylo_c..=syhi_c)
            .filter_map(|sy| {
                let i = n as isize - 1 - sy as isize - kk as isize;
                if i >= 0 { Some((sy, ring[i as usize])) } else { None }
            }).collect();
        let mut swaps = vec![];
        let root = swap_tree(&fd.sy, &leaves, fd.sy.len(), &mut swaps);
        for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
        top_eq_root(b, kk, ak, root);
        for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
    };
    // c ^= ak & [X >= 2^kk Y] (X < 2^(kk+1) Y: the carry out of the shot's relative position sy); `sub` (c |0> on
    // entry): also X -= 2^kk Y where it holds, one step of the restoring division
    let c42_nat_stage = std::cell::Cell::new(false);
    let cmp_y_flight = |b: &mut B, kk: usize, sub: bool, pre: &[QubitId], flight: QubitId| {
        if c42_nat_stage.get() { top_virtual(b, kk); }
        let span = (syhi_c + 1).min(n - kk);
        let tl: Vec<QubitId> = (0..span).map(|i| ring[n - 1 - kk - i]).collect();
        if joint_p1 {
            assert!(sub,"joint S5 only calls the complete restoring-subtract form");
            let view=joint_size::View::from_fd(fd,true);
            let source=view.masked_source(&q,x128,span);
            b.x(act);
            joint_size::clean_query(b,&view,&tl,&source,(sylo_c,syhi_c),ak,
                flight,act,pzero,None,&q[112..120],&dirty,true);
            b.x(act);
            if c42_nat_stage.get() {top_virtual(b,kk);}
            return;
        }
        let mut s: Vec<QubitId> = q.iter().copied().take(span).collect();
        if s.len() < span { s.push(x128); }
        assert_eq!(s.len(), span);
        let rd = s.clone();
        let mut mid = |b: &mut B| {
            let lane = |vv: usize| if vv < rd.len() { Some(rd[vv]) } else { None };
            read_lane(b, &fd.sy, sylo_c, syhi_c, &lane, true, &[(ak, false)], flight, pre, &[], &dirty);
        };
        let mut gate = |_b: &mut B, i: Option<usize>| if sub { i.map(|_| flight) } else { None };
        // ak and flight imply the original act=1. With act=0 the body is
        // the identity for either carry value; the bracket restores act.
        if pool4 { b.x(act); }
        ripple(b, &tl, &s, if pool4 { act } else { c0 }, true, &mut mid, &mut gate);
        if pool4 { b.x(act); }
        if c42_nat_stage.get() { top_virtual(b, kk); }
    };
    let cmp_y = |b: &mut B, kk: usize, sub: bool, pre: &[QubitId]|
        cmp_y_flight(b, kk, sub, pre, c);
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
        super::frogdrop_col::ge_cd(b, &v, (vlimit - 1 - kk) as isize, sx[0], &gate_chain, &dirty);
        let read_pre: Vec<QubitId> = pre_c.iter().copied().filter(|&x| x != sx[0]).collect();
        let mut mid = |b: &mut B| {
            let lane = |vv: usize| if vv < rd.len() { Some(rd[vv]) } else { None };
            read_lane(b, &fd.sy, sylo_c, syhi_c, &lane, true, &[(ak, false)], c, &read_pre, &[], &dirty);
            let prior = |vv: usize| if vv >= 1 && vv - 1 < rd.len() { Some(rd[vv - 1]) } else { None };
            read_lane(b, &fd.sy, sylo_c, syhi_c, &prior, false,
                      &[(ak, false), (sx[0], false)], c, &read_pre, &[], &dirty);
        };
        let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| c);
        if pool4 { b.x(act); }
        ripple(b, &tl, &s, if pool4 { act } else { c0 }, false, &mut mid, &mut gate);
        if pool4 { b.x(act); }
        super::frogdrop_col::ge_cd(b, &v, (vlimit - 1 - kk) as isize, sx[0], &gate_chain, &dirty);
    };
    // c <-> X-index sy + kk (the in-place lane) on the ak shots: a swap tree on sy's bits brings the shot's lane to
    // the range's first lane (any sy in [sylo, syhi]; an ak shot's sy is in range), one controlled swap, the tree back
    // (QUOT_INPLACE_DEC=1: the one-hot decoder)
    let tree_inplace = std::env::var_os("QUOT_INPLACE_DEC").is_none();
    let inplace_by_flight = |b: &mut B, kk: usize, ctl: QubitId, pre: &[QubitId], top_mode: u8, flight: QubitId| {
        let f1 = b.tof;
        let lane = |vv: usize| {
            let i = n as isize - 1 - vv as isize - kk as isize;
            if i >= 0 { Some(ring[i as usize]) } else { None }
        };
        if joint_p1 {
            assert_eq!(top_mode,0,"joint natural stage uses the explicit top-lane bracket");
            let view=joint_size::View::from_fd(fd,true);
            let leaves:Vec<_>=(sylo_c..=syhi_c).filter_map(|size|lane(size).map(|q|(size,q))).collect();
            view.gathered_at(b,&leaves,pzero,&dirty,|b,root,member,bank| {
                super::mid2::mc_swap(b,&[(ctl,false),(member,false)],root,flight,&[],bank);
            });
            super::f1_profile("midg.inplace",f1,b.tof);
            return;
        }
        if tree_inplace {
            let leaves: Vec<(usize, QubitId)> = (sylo_c..=syhi_c).filter_map(|v| lane(v).map(|l| (v, l))).collect();
            let mut swaps = vec![];
            let root = swap_tree(&fd.sy, &leaves, fd.sy.len(), &mut swaps);
            for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
            // Clear the leading one before quotient storage and restore it
            // after retrieval, using the same exact selector as cmp_y.
            if top_mode == 1 { top_eq_root(b, kk, ctl, root); }
            super::mid2::mc_swap(b, &[(ctl, false)], root, flight, &[], &dirty);
            if top_mode == 2 { top_eq_root(b, kk, ctl, root); }
            for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
        } else {
            assert_eq!(top_mode, 0, "N257 fixed top repair requires tree in-place swap");
            super::mid2::dec_swap(b, &fd.sy, sylo_c, syhi_c, &lane, flight, &[(ctl, false)], pre, &[], &dirty);
        }
        super::f1_profile("midg.inplace", f1, b.tof);
    };
    let inplace_by = |b: &mut B, kk: usize, ctl: QubitId, pre: &[QubitId], top_mode: u8|
        inplace_by_flight(b, kk, ctl, pre, top_mode, c);
    let inplace = |b: &mut B, kk: usize, pre: &[QubitId]| inplace_by(b, kk, ak, pre, 0);
    // one park per chunk (slot s <-> cycle index s), recorded top chunk first
    let parks: Vec<Vec<Gate>> = if chunk && !sx7_retired {
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
        ht_act(b, fd, cp, sc, act, &sx[..1], boundary_tmp, &dirty);
        if zoff_on && cp.dq { b.play(&zshift, true); }
        if flipped { b.x(ph); }
    };
    b.play(&zshift, true);
    let vform_ht = vform_ht.unwrap_or_else(|| vform.clone());
    let p1_cross = b8b_cross && std::env::var("B12A_P1").as_deref() == Ok("1");
    let c42_gather = |b: &mut B, ht: bool| -> Vec<G> {
        if n != 257 || p1_cross || pl.is_none() || payload258 { return vec![]; }
        let p = &pl.unwrap().p;
        let lo = cp.sy.0.max(1);
        let hi = cp.sy.1.min(128);
        assert!(lo <= hi);
        c42_payload_gather(b, p, &fd.sy, payload_root, lo, hi, ht)
    };
    let hr_gather = c42_gather(b, false);
    let ht_gather = c42_gather(b, true);
    let c42_wrap = |b: &mut B, form: &[G], gather: &[G]| -> Vec<G> {
        if gather.is_empty() { return form.to_vec(); }
        rec(b, |b| { b.play(gather, false); b.play(form, false); b.play(gather, true); })
    };
    if n == 257 {
        b8b_forms = b8b_forms.iter().map(|f| c42_wrap(b, f, &hr_gather)).collect();
        b8b_forms_ht = b8b_forms_ht.iter().map(|f| c42_wrap(b, f, &ht_gather)).collect();
    }
    if flight_sel {
        // This admission guard covers both phases and every public column,
        // not only switching HT. A newly introduced opaque record fails
        // closed until its port contract is proved explicitly.
        assert!(route_free_phase_ports(&b8b_forms, ph, act));
        assert!(route_free_phase_ports(&b8b_forms_ht, ph, act));
        assert!(route_free_phase_ports(&[vform.clone(),vform_ht.clone()], ph, act));
    }
    if super::frogdrop_col::c55_pool8() && b8b_cross && cp.sw {
        let writes = |gate: &Gate, lane: QubitId| match *gate {
            Gate::X(t) | Gate::Cx(_, t) | Gate::Ccx(_, _, t) |
            Gate::AndC(_, _, t) | Gate::AndU(_, _, t) |
            Gate::XIf(t, _) => t == lane,
            Gate::Swap(a, b) => a == lane || b == lane,
            _ => false,
        };
        let control_only = |forms: &[Vec<Gate>], lane: QubitId, name: &str| {
            for (fi, form) in forms.iter().enumerate() {
                if let Some((gi, gate)) = form.iter().enumerate().find(|(_, g)|
                    writes(g, lane) && !matches!(g, Gate::X(t) if *t == lane)) {
                    panic!("C55 {name}: form {fi} gate {gi} changes w: {gate:?}");
                }
                let flips = form.iter().filter(|g| matches!(g, Gate::X(t) if *t == lane)).count();
                assert_eq!(flips % 2, 0, "C55 {name}: form {fi} has unpaired negative-control X");
            }
        };
        control_only(&b8b_forms, sx[5], "S1");
        if !flight_sel { control_only(&b8b_forms_ht, sx[1], "S2"); }
        assert!(!vform.iter().any(|g| writes(g, sx[5])), "C55 S1: plain HR V form changes w");
        if !flight_sel {
            assert!(!vform_ht.iter().any(|g| writes(g, sx[1])), "C55 S2: plain HT V form changes w");
        }
    }
    // Repark high quotient bits around each complete fixed V. The seven-SX
    // layout uses k18..22, sources Q[SYhi+1+k], targets Q[SYhi+17-k].
    // q_k can be one only when gap>=k; then SY<=257-SZlo-k<=target
    // follows from SZlo+SYhi>=240. Thus the destination is beyond Y.
    // Off-selector each source is already zero. Potentially done columns
    // have every target >=KD26; lower targets occur only before done is
    // possible. Sources stay <120, below the counter starting at121.
    // Repark is outside the entire Y-root/SGW wrapper and is inverted
    // before metadata can change. Logical R order and comparator family
    // are retained; only their proved-clean physical owners change.
    let inherited_fixed_repark = if joint_fixed {cp.sy.1>87} else {!payload258||cp.sy.1>90};
    let fixed_repark = rec(b, |b| if !fixed_r_loans.is_empty()
        && (inherited_fixed_repark || paid_hr_repark.is_some()) {
        let code = &sc.sz[..5];
        if inherited_fixed_repark {
        let first = if joint_fixed&&cp.sy.1>=94 {14} else if payload258 {17} else if sx7_retired { 18 } else if pool4 && cp.sy.1 == 96 { 19 } else { 20 };
        for kb in first..23usize {
            let bound = 32 - kb;
            let target = if joint_fixed&&cp.sy.1>=94 {cp.sy.1+13-kb}
                else if payload258 {cp.sy.1+16-kb} else if sx7_retired { cp.sy.1 + 17 - kb }
                else if first == 19 { cp.sy.1 + 18 - kb } else { cp.sy.1 - 2 + kb - 20 };
            assert!(target <= cp.sy.1);
            // Early fixed HR is pre-done; every potentially done fixed
            // column keeps all targets above the inherited KD26 data.
            assert!(!cp.dn || target >= 26);
            if sx7_retired {
                assert!(!s1.r.contains(&q[target]), "repark target must stay outside R/Y-root");
                assert!(!s1u.anc.contains(&q[target]) && !s1u.andc.contains(&q[target])
                    && !s1u.gt.contains(&q[target]) && !s1u.chain.contains(&q[target]));
                assert!(!fd.cnt.contains(&q[target]));
            }
            for bit in (0..5).rev() {
                if (bound >> bit) & 1 == 0 { continue; }
                let mut ctl: Vec<_> = (bit + 1..5)
                    .map(|i| (code[i], (bound >> i) & 1 == 0)).collect();
                ctl.push((code[bit], true));
                if joint_fixed&&cp.col==139 {ctl.push((q[127],true));}
                let owner=if joint_fixed&&cp.sy.1>=94 {
                    if kb>=17 {fixed_r_loans[kb-17]} else {fixed_r_loans[6+kb-14]}
                } else {fixed_r_loans[kb-first]};
                super::mid2::mc_swap(b, &ctl, owner, q[target], &[], &dirty);
            }
        }
        }
        if let Some((kb,source,target))=paid_hr_repark {
            // q_k=>gap>=k=>Y<=257-Zlo-k<=target.  Thus the destination
            // is zero on its selector and beyond Y's leading-one owner.
            // The original repark occupies hi-1..hi-6 (or hi-1..hi-9);
            // this new target is the next lane below that complete set.
            assert!(paid_fixed_head && (!cp.dn || target >= 26) && target < cp.sy.1);
            assert_eq!(paid_hr_owner,Some(q[source]));
            assert!(!s1.r.contains(&q[target]) && !fixed_size_loans.contains(&q[target]));
            assert!(!fd.cnt.contains(&q[target]));
            assert!(!s1u.anc.contains(&q[target]) && !s1u.andc.contains(&q[target])
                && !s1u.gt.contains(&q[target]) && !s1u.chain.contains(&q[target]));
            let bound=32-kb;
            for bit in (0..5).rev() {
                if (bound>>bit)&1==0 {continue;}
                let mut ctl:Vec<_>=(bit+1..5)
                    .map(|i|(code[i],(bound>>i)&1==0)).collect();
                ctl.push((code[bit],true));
                if joint_fixed&&cp.col==139 {ctl.push((q[127],true));}
                super::mid2::mc_swap(b,&ctl,q[source],q[target],&[],&dirty);
            }
        }
    });
    let vform_pk = if fixed_repark.is_empty() { vform_pk } else {
        rec(b, |b| { b.play(&fixed_repark, false); b.play(&vform_pk, false); b.play(&fixed_repark, true); })
    };
    let vform_pk_ht = c42_wrap(b, &vform_pk, &ht_gather);
    let vform_pk = c42_wrap(b, &vform_pk, &hr_gather);
    let vform_ht = c42_wrap(b, &vform_ht, &ht_gather);
    let vform = c42_wrap(b, &vform, &hr_gather);
    let tier_flag = (b8b_cross && l672_tier() && std::env::var("B12A_P1").as_deref() != Ok("1")).then(|| (l672_lane(&l672_h_name(), &sx, c0, pzero), l672_e0()));
    let b8b: Option<b8b_cross::Cross<'_>> = b8b_cross.then(|| b8b_cross::Cross {
        fd, cp, sc, pl, vform: &vform, vform_ht: &vform_ht, parked: &b8b_forms, parked_ht: &b8b_forms_ht, vg: &vg,
        zshift: &zshift, zflip: &zflip, zoff_on, kmax, mt, tier: tier_flag,
    });
    if cp.hr { if let Some(cross) = &b8b { cross.hr_pre(b); } }
    let fixed_park: Vec<QubitId> = if fixed_hr || fixed_ht {
        assert_eq!(kmax, 23);
        assert!(cp.sy.1 + 1 + kmax <= 126);
        (0..kmax).map(|kk| q[cp.sy.1 + 1 + kk]).collect()
    } else { vec![] };
    if fixed_hr {
        mc_xor(b, &hr_lits, act, &[], &dirty);
        let f1 = b.tof;
        vmark(b, 3331);
        act_hr(b);
        if n == 257 { b.play(&zflip, false); }
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
        assert!(!p1_cross, "legacy vform_pk reached a P1 crossing column");
        b.play(&vform_pk, true);
        if n == 257 { b.play(&zflip, false); }
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
            if n == 257 { b.play(&zflip, false); }
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
            assert!(!p1_cross, "legacy vform_pk reached a P1 crossing column");
            b.play(&vform_pk, true);
        if n == 257 { b.play(&zflip, false); }
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
        if n == 257 { b.play(&zflip, false); }
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
        assert!(!p1_cross, "legacy vform_pk reached a P1 crossing column");
        b.play(&vform_pk, true);
        if n == 257 { b.play(&zflip, false); }
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
        let mut payload_session:Option<super::payload::splice258::PhaseTransition>=None;
        c42_nat_stage.set(true);
        let dec1 = if cp.tt { Some(rec(b, |b| super::modp_frogdrop::inc_dirty(b, &xl, &dirty, if pool4 { sx[0] } else { c0 }))) } else { None };
        if let Some(d) = &dec1 { b.play(d, true); }
        let wtop = 259 - (L0P + 1);
        let pads = vec![x128, pzero];
        let nopad = std::env::var("FD_DINV_NOPAD").map(|v| v == "1").unwrap_or(false);
        let slen = if nopad { wtop.min(nq) } else { wtop.min(nq + pads.len()) };
        // Persistent raw SY occupies Q above the complete public Y span.
        // Only the known-zero source suffix is omitted; trans_one retains
        // the original full target and exact carry propagation tail.
        let slen=if joint_fixed {slen.min(cp.sy.1)} else {slen};
        let src = if pl.is_some() { if nopad { fd.q[..slen].to_vec() } else { super::payload::pad(&fd.q, &pads, slen) } }
                  else { vec![] };
        mc_xor(b, &hr_lits, act, &[], &dirty);
        // X = t_{j+1}; regenerate each q bit in X's free high lane and
        // erase the fixed Q park before the payload uses Q as its source.
        b.play(&vg, false);
        for kk in (0..kmax).rev() {
            gate_v(b, kk, act, sx[0], true);
            #[cfg(test)] if kk < 2 { super::frogdrop_col::mark(b, 39800 + kk * 10); }
            cmp_y(b, kk, true, &pre_c);
            #[cfg(test)] if kk < 2 { super::frogdrop_col::mark(b, 39801 + kk * 10); }
            mc_xor(b, &[(ak, false), (c, false)], fixed_park[kk], &[], &dirty);
            #[cfg(test)] if kk < 2 { super::frogdrop_col::mark(b, 39802 + kk * 10); }
            inplace_by(b, kk, ak, &pre_c, if n == 257 { 1 } else { 0 });
            #[cfg(test)] if kk < 2 { super::frogdrop_col::mark(b, 39803 + kk * 10); }
            gate_v(b, kk, act, sx[0], false);
            #[cfg(test)] if kk < 2 { super::frogdrop_col::mark(b, 39804 + kk * 10); }
            #[cfg(test)] super::frogdrop_col::mark(b, 39910 + kk);
        }
        b.play(&vg, true);
        // The fixed Q park has now been erased. The delayed HR digit may use
        // those Q lanes as clean scratch; its ring source needs the Z-top
        // shuttle while the in-place quotient remains in the ring.
        #[cfg(test)] super::frogdrop_col::mark(b, 39900);
        if n == 257 {
            if let Some(pl) = pl {
                b.play(&zshift, false);
                if pool5 {
                    // Every quotient flight is returned at this boundary.
                    // Carry the fixed HR act on the returned P-zero while
                    // the full raw size temporarily owns SX5..7.
                    b.cx(act, pzero); b.cx(pzero, act);
                    let frame = sumframe::record(b, &sc.sz, &fd.sy, &dirty);
                    b.play(&frame, true);
                    let mut raw = sc.clone();
                    raw.sw = pzero;
                    let col0_top = rec(b, |b| if cp.col == 0 {
                        let zero: Vec<_> = sc.sz.iter().map(|&q| (q, true)).collect();
                        mc_xor(b, &zero, fd.q[118], &[], &dirty);
                    });
                    if cp.col == 0 { raw.sz.push(fd.q[118]); }
                    b.play(&col0_top, false);
                    if payload258 {
                        let exit=super::payload::col_digit_phase_splice(b,fd,cp,&raw,pl,false,super::payload::HrDigit::Fixed);
                        b.play(&col0_top,true);
                        b.play(&frame,false);
                        payload_session=Some(super::payload::splice258::retain_phase_digit(b,fd,pl,exit,act));
                    } else {
                        super::payload::col_digit_phase_hr(b, fd, cp, &raw, pl, Some(false), super::payload::HrDigit::Fixed);
                        b.play(&col0_top, true);
                        b.play(&frame, false);
                        b.cx(pzero, act); b.cx(act, pzero);
                    }
                } else if super::frogdrop_col::c55_pool8() && cp.col == 0 {
                    let mut raw = sc.clone();
                    raw.sz.push(fd.q[118]);
                    let decode = rec(b, |b| super::frogdrop::add_const_dirty_exact(b, &raw.sz, 217, &dirty));
                    b.play(&decode, false);
                    super::payload::col_digit_phase_hr(b, fd, cp, &raw, pl, Some(false), super::payload::HrDigit::Fixed);
                    b.play(&decode, true);
                } else {
                    super::payload::col_digit_phase_hr(b, fd, cp, sc, pl, Some(false), super::payload::HrDigit::Fixed);
                }
                b.play(&zshift, true);
            }
        }
        #[cfg(test)] super::frogdrop_col::mark(b, 39901);
        b.play(&vg, false);
        for kk in 0..kmax {
            gate_v(b, kk, act, sx[0], true);
            inplace_by(b, kk, ak, &pre_c, if n == 257 { 2 } else { 0 });
            if let Some(pl) = payload_session.as_ref().map(|s|&s.raw).or(pl) {
                let t: Vec<QubitId> = (kk..wtop).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                let sl = (wtop - kk).min(slen);
                if pool4 { b.x(act); }
                // Raw payload cells outside the complete transition target
                // are arbitrary restored donors, including when inactive.
                // They fund the full carry tail created by the shorter Y
                // source; raw PH=P258 belongs to t and is never borrowed.
                let mut carry_dirty=pl.dirty.clone();
                if joint_fixed {
                    let mut seen:std::collections::BTreeSet<_>=carry_dirty.iter().copied().collect();
                    carry_dirty.extend(pl.p.iter().copied().filter(|q|!t.contains(q)
                        &&!src[..sl].contains(q)&&![c,sx[0],act,c0].contains(q)&&seen.insert(*q)));
                }
                super::payload::trans_one(b, &t, &src[..sl], kk, false, vec![(c, false)], None, sx[0],
                                          if pool4 { act } else { c0 }, &[], &carry_dirty);
                if pool4 { b.x(act); }
                super::frogdrop_col::mark(b, 1000 + kk);
            }
            mul_back(b, kk);
            gate_v(b, kk, act, sx[0], false);
        }
        b.play(&vg, true);
        if let Some(session)=payload_session.take() {p258_finish_hr(b,fd,cp,sc,session,&dirty);}
        mc_xor(b, &hr_lits, act, &[], &dirty);
        if let Some(d) = &dec1 { b.play(d, false); }
        c42_nat_stage.set(false);
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
    if pool4 {
        // SX4 is the live fifth code bit. Only the inherited N257 nopark
        // production route below has the returned-owner schedule proved here.
        assert!(pool5 && n == 257 && k == 0 && chunk && !old5 && split5);
        assert_eq!(std::env::var("S5_NOPARK").as_deref(), Ok("1"));
        assert!(super::frogdrop_col::c55_pool8());
    }
    let res_s: usize = std::env::var("QUOT_RES_S").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    if cp.ht && !old5 {
        // (lowq_cross repair, copied for the chunked hand-off test: the crossing form choice is ported: sw marks only
        // the switching shots in dl columns, and act excludes a delayed shot's no-step column)
        // in place on the 13 lanes (the stepping flag on sw; act idle) and sx; s = sz + sy is formed as s - 2 on sz
        // (every shot's s in [228, 257]); the division's Q pad past lane 127 is sv (clean outside the size gates)
        let actl = sc.sw;
        let ds = super::payload::DigScr { e: vec![], sa: sc.sz.clone(), sb: fd.sy.clone(), sv: x128, fa: sx[0], g: act,
                                          c0: if pool4 { ph } else { c0 }, tmp: vec![pzero, sx[1]], pre1: vec![], pre2: vec![], zeros: vec![],
                                          dirty: dirty.clone(), smin: 2 };
        let sw_toggle = |b: &mut B| {
            if !cp.sw { return; }
            if joint_p1 {
                // Erase the retained HR switching witness directly from
                // the unnormalized rank. H5 is an encoded tag here, not PH.
                // Z=226+C-SY: Z<=128 iff SY>=98+C. In DL the stronger
                // Z<=SY gives SY>=ceil((226+C)/2), which implies Z<=128
                // on the unchanged SY<=128 domain. Restrict to HR ranks;
                // neither HT nor the binary done packet contributes.
                let view=joint_size::View::from_fd(fd,false);
                let word=view.word();
                let code=&sc.sz[..5];
                let bank:Vec<_>=dirty.iter().copied().filter(|q|
                    !word.contains(q)&&!code.contains(q)&&*q!=sc.sw).collect();
                for value in 0..32usize {
                    let lower=if cp.dl {(227+value)/2} else {98+value};
                    if lower>128 {continue;}
                    let start=joint_size::View::active_interval(lower).0;
                    for mut term in joint_size::View::interval_terms(&word,start,672) {
                        term.extend(code.iter().enumerate()
                            .map(|(i,&q)|(q,(value>>i)&1==0)));
                        mc_xor(b,&term,sc.sw,&[],&bank);
                    }
                }
                return;
            }
            if pool5 {
                assert_eq!(cp.l0, 128);
                if cp.dl {
                    // The original branch below uses fa and x128 as its
                    // clean size-comparator owners at this same boundary.
                    // Both return before set_act and the stage-5 ripple.
                    sumframe::xor_raw_le_sy_clean(b, &sc.sz[..5], &fd.sy, sc.sw,
                        &[(ph, true)], ds.fa, x128, &dirty);
                } else {
                    sumframe::xor_raw_ge(b, &sc.sz[..5], &fd.sy, 129, ds.fa, &[], &dirty);
                    mc_xor(b, &[(ds.fa, true), (ph, true)], sc.sw, &[], &dirty);
                    sumframe::xor_raw_ge(b, &sc.sz[..5], &fd.sy, 129, ds.fa, &[], &dirty);
                }
                return;
            }
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
        let set_act = |b: &mut B| {
            if joint_p1 {
                joint_size::View::from_fd(fd,false)
                    .xor_ht_active(b,&sc.sz[..5],cp.dq,actl,&dirty);
                return;
            }
            if zoff_on && cp.dq { b.play(&zshift, false); }
            if pool5 && cp.dq {
                // sw_toggle returned both owners; stage5 has not yet
                // parked a quotient or opened a ripple/size decoder.
                let query = |b: &mut B| sumframe::xor_raw_lt_sy_clean(b,
                    &sc.sz[..5], &fd.sy, x128, &[], sx[0], pzero, &dirty);
                query(b);
                let lits = [(ph, false), (x128, true)];
                if cp.dn { mc_xor_dn(b, &lits, actl, &sx[..2], &dirty, fd, cp.l0, false); }
                else { mc_xor(b, &lits, actl, &sx[..2], &dirty); }
                query(b);
            } else { ht_act(b, fd, cp, sc, actl, &sx[..2], x128, &dirty); }
            if zoff_on && cp.dq { b.play(&zshift, true); }
        };
        let mut payload_session:Option<super::payload::splice258::PhaseTransition>=None;
        let mut joint_phase= None;
        if payload258 && pl.is_some() {
            if joint_p1 {
                // Keep complete HT activity separate from the encoded
                // tag before H5 becomes the payload's physical extra.
                sw_toggle(b);set_act(b);
                assert_eq!(actl,act);
                b.cx(actl,pzero);b.cx(pzero,actl);
                let mut session=super::payload::col_digit_phase_joint(
                    b,fd,cp,sc,pl.unwrap(),pzero,true,
                    [sx[0],sx[1],sx[2],sx[5]],None);
                assert_eq!(session.act,pzero);
                b.cx(pzero,actl);b.cx(actl,pzero);
                session.act=actl;
                payload_session=Some(session);
            } else {
            // No V form is entered after this boundary until PH is
            // restored below. Move the outside switch witness away from
            // raw SZ, then establish exactly the old complete HT act in
            // the digit wrapper. Its PH-extra stays payload throughout S5.
            let compact_pl=pl.unwrap();
            assert_eq!(actl,act);
            b.cx(actl,pzero);b.cx(pzero,actl);
            let frame=sumframe::record(b,&sc.sz,&fd.sy,&dirty);
            b.play(&frame,true);
            let mut raw=sc.clone();raw.sw=pzero;
            let exit=super::payload::col_digit_phase_splice(b,fd,cp,&raw,compact_pl,true,
                super::payload::HrDigit::None);
            b.play(&frame,false);
            payload_session=Some(super::payload::splice258::retain_phase_digit(b,fd,compact_pl,exit,actl));
            }
        } else {
            sw_toggle(b);set_act(b);
            if joint_p1 {
                let phase=joint_size::View::from_fd(fd,false)
                    .ht_phase_record(b,actl,&dirty);
                b.play(&phase,true);
                joint_phase=Some(phase);
            }
        }
        let stage5_pl=payload_session.as_ref().map(|s|&s.raw).or(pl);
        if n == 257 { assert!(split5, "N257 HT requires split stage 5"); }
        if split5 {
            let kin = k.min(kmax);
            // the division in place, every bit (no payload): X = r_{j-1} -> r_{j+1}, q_kk at X-index sy + kk
            if n == 257 { b.play(&zflip, false); }
            // The persistent low-five-bit size frame leaves SX7 free
            // throughout stage5, so retain the original flight and decoder.
            b.play(&vg, false);
            for kk in (0..kmax).rev() {
                gate_v(b, kk, actl, sx[0], true);
                cmp_y(b, kk, true, &pre_c);
                inplace(b, kk, &pre_c);
                gate_v(b, kk, actl, sx[0], false);
            }
            b.play(&vg, true);
            let s5np = kin == 0 && std::env::var("S5_NOPARK").map(|v| v == "1").unwrap_or(false);
            if let (Some(pl), true) = (stage5_pl, s5np) {
                // lowq-671 S5_NOPARK: no park. The payload transitions run with every quotient bit in place. During
                // transition kb (exact sy mask) a bit kk > kb at ring lane 258 - sy - kk adds q_kb q_kk 2^(258 - sy
                // - kk + kb); the bits kk < kb land above the mask. That term depends on q alone, so a second sweep
                // subtracts it in a frame where the ring and the payload's W are both down by sz + 1: the q block
                // then sits at lanes [0, g] (g = 257 - sz - sy, bit kk at g - kk) with Z out of the window, and the
                // write mask is P' <= g.
                let (sylo5, syhi5) = (cp.sy.0.max(1), cp.sy.1.min(L0P));
                // A seven-SX layout holds the flight on SX1, so no prefix
                // or comparator chain may also borrow it. The legacy path
                // keeps its original SX7 flight and two-prefix bank. SX0 is
                // returned by gate_u before the affine equality query.
                let pre5: Vec<QubitId> = if flight_shared { vec![sx[6]] }
                    else if mid8() { vec![sx[1], sx[6]] } else { vec![sx[5], sx[6]] };
                // to_pzero below returns SX5 globally before the first
                // gate_u. Every transition uses it as a running mask and
                // returns it before the next complete predicate epoch.
                let chain5: Vec<QubitId> = if flight_shared { vec![act] }
                    else if pool4 { vec![act, sx[1]] }
                    else if mid8() { vec![c0, sx[1]] } else { vec![c0, sx[5]] };
                let transition_carry = if payload258 {pzero} else if pool4 { ph } else { c0 };
                // every model-clean act shot has s = sz + sy >= 256 - bl(q) >= 256 - QF (r_{j-1} |t_j| > p / 2)
                let s_base = (cp.sz.0 + cp.sy.0).max(256 - qf);
                let gmax = 257usize.saturating_sub(s_base);
                assert!(gmax + 1 <= (1 << vbits));
                let kend = kmax.min(gmax + 1);
                // u = s - s_base (mod 2^VB) in v's lanes
                let ucon = if pool5 { ((1 << vbits) - ((s_base - sumframe::BIAS) % (1 << vbits))) % (1 << vbits) }
                    else { ((1 << VB) - ((s_base + VOFF) % (1 << VB))) % (1 << VB) };
                let ug = rec(b, |b| {
                    b.play(&vg, false);
                    for i in 0..vbits {
                        if (ucon >> i) & 1 == 1 { super::modp_frogdrop::inc_dirty_free(b, &v[i..], &dirty); }
                    }
                });
                // C-2: keep q_g outside Z while the first sweep reads Z's
                // real leading one. The save is restored before stage 6.
                let qg_save = sx[2];
                // gate_u returns sx0 before ak guards the in-place handoff.
                // The affine sum query below needs no ninth size owner.
                let qg_eq = sx[0];
                assert!(qg_save != ak && qg_save != c && qg_eq != ak && qg_eq != c);
                let pool8_s5 = super::frogdrop_col::c55_pool8();
                let to_pzero = |b: &mut B| if pool8_s5 {
                    b.cx(sx[5], pzero);
                    b.cx(pzero, sx[5]);
                };
                let to_act = |b: &mut B| if pool8_s5 {
                    b.cx(pzero, sx[5]);
                    b.cx(sx[5], pzero);
                };
                let s5_act = if pool8_s5 { pzero } else { actl };
                if pool4 {
                    assert!(pool8_s5);
                    assert_eq!(actl, sx[5]);
                    assert_eq!(act, sx[5]);
                    assert_eq!(pzero, sx[3]);
                    assert!(!chain5.iter().any(|q| v.contains(q) || *q == s5_act
                        || *q == ak || *q == c || *q == sx[0]));
                    assert!(!pre5.contains(&ph) && !pl.dirty.contains(&ph));
                    assert!(!fd.sy.contains(&ph) && !ring.contains(&ph));
                    assert_eq!(pl.p.contains(&ph),payload258);
                    if payload258 {
                        assert_eq!(transition_carry,s5_act);
                        assert!(!pl.dirty.contains(&transition_carry) && !pre5.contains(&transition_carry));
                    }
                }
                let save_top = rec(b, |b| {
                    b.play(&prot, false);
                    super::mid2::mc_swap(b, &[(actl, false)], ring[n - 1], qg_save, &[], &dirty);
                    b.play(&prot, true);
                });
                b.play(&save_top, false);
                b.play(&zflip, false);
                to_pzero(b);
                let inplace_s5 = |b: &mut B, kb: usize| {
                    let leaves: Vec<(usize, QubitId)> = (sylo_c..=syhi_c).filter_map(|sy| {
                        let i = n as isize - 1 - sy as isize - kb as isize;
                        if i >= 0 { Some((sy, ring[i as usize])) } else { None }
                    }).collect();
                    if joint_p1 {
                        let view=joint_size::View::from_fd(fd,true);
                        view.gathered_at(b,&leaves,pzero,&dirty,|b,root,member,bank| {
                            let value=n.checked_sub(kb+s_base).expect("joint stage5 sum threshold");
                            assert!(value<(1usize<<vbits));
                            let mut literals:Vec<_>=v.iter().enumerate()
                                .map(|(i,&q)|(q,(value>>i)&1==0)).collect();
                            literals.extend([(ak,false),(member,false)]);
                            mc_xor(b,&literals,qg_eq,&[],bank);
                            b.cswap(qg_eq,root,qg_save);
                            super::mid2::mc_swap(b,&[(ak,false),(member,false)],root,c,&[],bank);
                            b.cswap(qg_eq,root,qg_save);
                            mc_xor(b,&literals,qg_eq,&[],bank);
                        });
                        return;
                    }
                    let mut swaps = vec![];
                    let root = swap_tree(&fd.sy, &leaves, fd.sy.len(), &mut swaps);
                    for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
                    // ug is held here: v = sz + sy - s_base (mod 64).
                    // ak implies a stepping shot and kb <= 257-s_base.
                    // Its unchanged arithmetic bounds give
                    // s_base <= sz+sy <= 257, an interval shorter than 64.
                    // Thus this affine equality is the full raw-size
                    // equality, without reconstructing a ninth size bit.
                    let value = n.checked_sub(kb + s_base).expect("stage5 sum threshold");
                    assert!(value < (1usize << vbits));
                    let mut lits: Vec<(QubitId, bool)> = v.iter().enumerate()
                        .map(|(i, &q)| (q, (value >> i) & 1 == 0)).collect();
                    lits.push((ak, false));
                    let eq_helpers: Vec<QubitId> = dirty.iter().copied()
                        .filter(|&q| q != root && q != qg_save && q != qg_eq && !v.contains(&q)).collect();
                    mc_xor(b, &lits, qg_eq, &[], &eq_helpers);
                    b.cswap(qg_eq, root, qg_save);
                    super::mid2::mc_swap(b, &[(ak, false)], root, c, &[], &dirty);
                    b.cswap(qg_eq, root, qg_save);
                    mc_xor(b, &lits, qg_eq, &[], &eq_helpers);
                    for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
                };
                let inplace_s5_hop = |b: &mut B, kb: usize| {
                    to_act(b);
                    inplace_s5(b, kb);
                    to_pzero(b);
                };
                // ak = actl & [kk <= g] = actl & [u < 258 - s_base - kk]
                let gate_u = |b: &mut B, kk: usize, on: bool| {
                    let lim = (258 - s_base - kk) as isize;
                    super::frogdrop_col::ge_cd(b, &v, lim, sx[0], &chain5, &dirty);
                    b.x(sx[0]);
                    if on { b.and_c(s5_act, sx[0], ak); } else { b.and_u(s5_act, sx[0], ak); }
                    b.x(sx[0]);
                    super::frogdrop_col::ge_cd(b, &v, lim, sx[0], &chain5, &dirty);
                };
                // 1. the transitions, every bit in place (bit kb in c, its lane zero)
                b.play(&ug, false);
                for kb in 0..kend {
                    gate_u(b, kb, true);
                    inplace_s5_hop(b, kb);
                    gate_u(b, kb, false);
                    // (ring 258, kb 0: the NP-lane source slice would pass the ring's end)
                    let span = (NP - kb).min(n);
                    let tt: Vec<QubitId> = (kb..kb + span).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                    // c=1 implies the retained HT enable and PH=1.
                    // At c=0 the write mask is zero and the MAJ ladder is
                    // exactly undone for either carry value. No measured
                    // AND owns PH; restore it before any predicate reads it.
                    if payload258 {
                        assert!(!tt.contains(&transition_carry) && !fd.ring[..span].contains(&transition_carry));
                        assert!(![c,act].contains(&transition_carry));
                    }
                    if pool4 {b.x(transition_carry);}
                    if payload258 {super::mask::R11O11_DECCC.with(|cc|cc.borrow_mut().push(transition_carry));}
                    if joint_p1 {
                        trans_carry_boundary_joint(b,&tt,&fd.ring[..span],n+1-kb,c,
                            &joint_size::View::from_fd(fd,true),(sylo5,syhi5),act,
                            transition_carry,&pre5,&pl.dirty);
                    } else {
                        trans_masked_q(b, &tt, &fd.ring[..span], n, kb, c, &fd.sy, 0, sylo5, syhi5, act, transition_carry, &pre5,
                                       &[], &pl.dirty);
                    }
                    if payload258 {super::mask::R11O11_DECCC.with(|cc|assert_eq!(cc.borrow_mut().pop(),Some(transition_carry)));}
                    if pool4 {b.x(transition_carry);}
                    gate_u(b, kb, true);
                    inplace_s5_hop(b, kb);
                    gate_u(b, kb, false);
                }
                b.play(&ug, true);
                if joint_p1 {
                    // The enable is now retained on pzero, with SX5
                    // returned. Use this epoch's four available owners.
                    joint_frame::lane_query(b,&ring,&sc.sz[..5],&joint_size::View::from_fd(fd,true),
                        [sx[0],c,act,ak],cp.sz,n-1,None,&dirty);
                } else {b.play(&zflip, false);}
                // 2. the q block's term, subtracted with the ring and W down by sz + 1
                if std::env::var_os("S5_NOCOMP").is_none() {
                // (lowq-671: the q block sits at ring lane n - 1 - sy - kk; with the frame down by sz, bit kk is at
                // frame lane (n - 259) + 1 + g - kk, so dl = n - 258 is the frame's first source lane: 1 at ring 259,
                // 0 at ring 258, where q_g reaches lane sz)
                let dl = n as isize - 258;
                let destc_ring: std::collections::BTreeSet<usize> = (0..=gmax)
                    .map(|j| (dl + j as isize).rem_euclid(n as isize) as usize).collect();
                let destc_prev: std::collections::BTreeSet<usize> = (0..=gmax)
                    .map(|j| (dl + j as isize).rem_euclid(NP as isize) as usize).collect();
                let prev: Vec<QubitId> = pl.p.iter().rev().copied().collect();
                let pr = rec(b, |b| {
                    // gate_u and the equality gather have returned SX0;
                    // q_g stays on SX2 and the retained enable on pzero.
                    if joint_p1 {
                        joint_frame::rotate_full(b,&prev,&sc.sz[..5],&joint_size::View::from_fd(fd,true),
                            [sx[0],c,act,ak],true,&pl.dirty);
                    } else if pool5 { sumframe::rot_raw_clean(b, &prev, &sc.sz[..5], &fd.sy, true, &pl.dirty,
                        if pool4 { sx[0] } else { c0 }); }
                    else if zoff_on { super::frogdrop::rot_by_off_care(b, &prev, &sc.sz, cp.sz.0, cp.sz.1, true, &destc_prev); }
                    else { rot_by_range_care(b, &prev, &sc.sz, cp.sz.0, cp.sz.1, true, &pl.dirty, &destc_prev); }
                });
                let rr = rec(b, |b| if joint_p1 {
                    joint_frame::rotate(b,&ring,&sc.sz[..5],&joint_size::View::from_fd(fd,true),
                        [sx[0],c,act,ak],true,cp.sz,&destc_ring,&dirty);
                } else {rot_sz(b, &destc_ring)});
                b.play(&pr, false);
                b.play(&rr, false);
                b.play(&ug, false);
                for kb in 0..kend {
                    let l = 258 - s_base - kb;
                    // c <-> q_kb at ring[257 + dl - s - kb] (s = s_base + u) on the ak shots
                    let leaves: Vec<(usize, QubitId)> = (0..=gmax - kb).map(|u| {
                        let f = 257 + dl - s_base as isize - u as isize - kb as isize;
                        // The first sweep reads q_{g-1} next to Z. Pair its
                        // cross term by fetching the saved q_g at u=gmax-kb.
                        (u, if n == 257 && u == gmax - kb { qg_save }
                            else { fd.ring[f.rem_euclid(n as isize) as usize] })
                    }).collect();
                    let swap_c = |b: &mut B| {
                        let mut swaps = vec![];
                        let root = swap_tree(&v, &leaves, v.len(), &mut swaps);
                        for &(bit, l0, r0) in &swaps { b.cswap(bit, l0, r0); }
                        super::mid2::mc_swap(b, &[(ak, false)], root, c, &[], &dirty);
                        for &(bit, l0, r0) in swaps.iter().rev() { b.cswap(bit, l0, r0); }
                    };
                    gate_u(b, kb, true);
                    swap_c(b);
                    // W' -= c ring[dl..dl + l) at P' = kb + i (W' position P' on lane prev[P' + dl]), written where P' <= g
                    if dl <= 0 {
                        // (ring 258: the mask's boundary P' = g + 1 is the first sweep's last written position, and its
                        // source cell holds q_{kb-1} or X's top bit: subtract through it with only the incoming borrow,
                        // ~(~W' + c ring_low))
                        let t: Vec<QubitId> = (0..=l).map(|i| prev[(kb as isize + dl + i as isize)
                            .rem_euclid(NP as isize) as usize]).collect();
                        let s: Vec<QubitId> = (0..=l).map(|i| fd.ring[(dl + i as isize)
                            .rem_euclid(n as isize) as usize]).collect();
                        for &x in &t { b.x(x); }
                        // The saved flight c is still HT-only. The
                        // same arbitrary-carry restore proof applies to
                        // this exact boundary-only subtraction.
                        if payload258 {
                            assert!(!t.contains(&transition_carry) && !s.contains(&transition_carry));
                            assert!(![c,act].contains(&transition_carry) && !v.contains(&transition_carry));
                        }
                        if pool4 {b.x(transition_carry);}
                        if payload258 {super::mask::R11O11_DECCC.with(|cc|cc.borrow_mut().push(transition_carry));}
                        trans_carry_boundary(b, &t, &s, if n == 257 { l + 1 } else { l }, 1, c, &v, 0, gmax - kb, act, transition_carry, &[], &[], &pl.dirty);
                        if payload258 {super::mask::R11O11_DECCC.with(|cc|assert_eq!(cc.borrow_mut().pop(),Some(transition_carry)));}
                        if pool4 {b.x(transition_carry);}
                        for &x in &t { b.x(x); }
                        swap_c(b);
                        gate_u(b, kb, false);
                        continue;
                    }
                    let t: Vec<QubitId> = (0..l).map(|i| prev[(kb as isize + dl + i as isize)
                        .rem_euclid(NP as isize) as usize]).collect();
                    let s: Vec<QubitId> = (0..l).map(|i| fd.ring[(dl + i as isize)
                        .rem_euclid(n as isize) as usize]).collect();
                    {
                        let mut mk = super::payload::Mask::new(&v, gmax, true, vec![(c, false)], act, &[], &pl.dirty);
                        let mut gate = |b: &mut B, i: Option<usize>| match i {
                            Some(i) => { mk.goto(b, Some((258 - s_base - kb - i) as isize)); Some(act) }
                            None => { mk.goto(b, None); None }
                        };
                        super::payload::ripple(b, &t, &s, c0, true, &mut |_b: &mut B| {}, &mut gate);
                    }
                    swap_c(b);
                    gate_u(b, kb, false);
                }
                b.play(&ug, true);
                b.play(&rr, true);
                b.play(&pr, true);
                }
                to_act(b);
                b.play(&save_top, true);
            } else if let Some(pl) = stage5_pl {
                // the payload: the bits >= K parked above Y (the headroom clean), control per bit on c
                // (lowq_cross direct park, replacing the staged two-batch park, whose batch-B gates ran on the cycle
                // lanes pzero / x128 while batch A was parked there): the cycle is rotated down by sy once; each bit
                // kb >= K goes from its in-place lane through c straight to cycle index kb - K and back after the
                // payload, so no staging slots at any K; stage 6 reads every bit in place
                // (agent_lowq_lane: a 5th lane sx[3] for QUOT_RES_S=5 at K5; idle in the split stage 5)
                let (q129s, rqs) = mk_cycle(b, &[pzero, ph, sx[1], sx[2], sx[3], sx[4]], cp.ht, Some(res_s));
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
                let pre5 = [sx[5], sx[6]];
                // the direct park's gate compares on [c0, sx4, sx5] (clean here: no slots in this stage), never on a
                // cycle lane; a bit that would wrap onto Y stays in c (a counted failure)
                let chain5 = [c0, sx[5]];
                assert!(!chain5.iter().any(|x| q129s.contains(x) || v.contains(x) || *x == ak || *x == c || *x == wf));
                assert!(tree_inplace, "the direct park's in-place swaps must not use pre_c (it holds pzero)");
                let gate5 = |b: &mut B, kk: usize, on: bool| {
                    if on { b.play(&vg, false); }
                    super::frogdrop_col::ge_cd(b, &v, (vlimit - kk) as isize, sx[0], &chain5, &dirty);
                    b.x(sx[0]);
                    if on { b.and_c(actl, sx[0], ak); } else { b.and_u(actl, sx[0], ak); }
                    b.x(sx[0]);
                    super::frogdrop_col::ge_cd(b, &v, (vlimit - kk) as isize, sx[0], &chain5, &dirty);
                    if !on { b.play(&vg, true); }
                };
                let dpark = |b: &mut B, kb: usize, fwd: bool| {
                    let idx = kb - kin;
                    let wrap = cp.sy.1.min(128) + idx >= wlen;
                    gate5(b, kb, true);
                    if fwd { inplace(b, kb, &pre_c); }
                    if wrap { wrap_flag(b, idx, wlen, false); }
                    let ct: Vec<(QubitId, bool)> = if wrap { vec![(actl, false), (wf, true)] } else { vec![(actl, false)] };
                    super::mid2::mc_swap(b, &ct, c, slot(idx), &[], &dirty);
                    if wrap { wrap_flag(b, idx, wlen, false); }
                    if !fwd { inplace(b, kb, &pre_c); }
                    gate5(b, kb, false);
                };
                b.x(ph);
                b.play(&rqs, false);
                if s5y { b.x(q129s[qlen - 1]); }
                for kb in kin..kmax { dpark(b, kb, true); }
                for kb in 0..kmax.min(NP) {
                    let ctl = |b: &mut B| {
                        if kb < kin {
                            inplace_by(b, kb, actl, &pre_c, 0);
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
                    let sh = ((usize::BITS - 1 - (kb + 1).leading_zeros()) as usize).min(4);
                    let span = (NP - kb).min(n);
                    let tt: Vec<QubitId> = (kb..kb + span).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                    trans_masked_q(b, &tt, &fd.ring[..span], n, kb, c, &fd.sy, sh, sylo5, syhi5, act, c0, &pre5,
                                   &[], &pl.dirty);
                    ctl(b);
                }
                for kb in (kin..kmax).rev() { dpark(b, kb, false); }
                if s5y { b.x(q129s[qlen - 1]); }
                b.play(&rqs, true);
                b.x(ph);
            }
        } else {
            // c, q's top bit, then the sy decoder's prefixes
            let l5: Vec<QubitId> = sx[2..].to_vec();
            if zoff_on { b.play(&zshift, false); }
            super::mid2::ht_div_inplace(b, fd, cp, actl, &ds, l5[0], l5[1], &l5[2..], &[], &[], pl, &dirty);
            if zoff_on { b.play(&zshift, true); }
        }
        if let Some(session)=payload_session.take() {
            // Both complete sweeps and all payload/ring rotations have
            // returned. PH is restored here before activity cleanup or V.
            if joint_p1 {
                super::payload::finish_joint_phase(b,fd,cp,sc,&session,sx[0],
                    &session.raw.dirty);
            } else {
                super::payload::splice258::finish_phase(b,&session,&fd.sy,
                    (cp.sy.0.max(1),cp.sy.1.min(128)),sx[0],&[c,x128,ak],&[],&session.raw.dirty);
            }
        }
        if let Some(phase)=joint_phase {b.play(&phase,false);}
        set_act(b);
        if !super::frogdrop_col::c55_pool8() { sw_toggle(b); }
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
                super::payload::trans_one_guard(b, &t, &fd.ring[..(NP - kb).min(n)], kb, false, base,
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
        if !super::frogdrop_col::c55_pool8() { sw_toggle(b); }
    }
    #[cfg(test)]
    if b6_capture_stage5 {
        let gate = b.end();
        B6_STAGE5_GATE.with(|v| *v.borrow_mut() = gate.clone());
        b.play(&gate, false);
    }
    if !stage(b) { return; } // 5
    let ht_narrow = if n == 257 && cp.ht && !p1_cross && !payload258 {
        if let Some(pl) = pl {
            let lo = cp.sy.0.max(1);
            let hi = cp.sy.1.min(128);
            assert!(lo <= hi);
            c42_ht_partial_narrow(b, &pl.p, &fd.sy, lo, hi, &dirty)
        } else { vec![] }
    } else { vec![] };
    b.play(&ht_narrow, false);
    if cp.ht { if let Some(cross) = &b8b { cross.ht_stage6(b); } }
    if fixed_ht {
        let set_act = |b: &mut B| { if zoff_on && cp.dq { b.play(&zshift, false); } ht_act(b, fd, cp, sc, act, &sx[..1], x128, &dirty); if zoff_on && cp.dq { b.play(&zshift, true); } };
        // The fixed park occupies Q above the public Y span. The ordinary
        // loan adder treats those zero Q lanes as a carry bank, so use its
        // exact short-source/tail form while the park is live.
        let parked_source: Vec<QubitId> = q[..syhi_c].iter().copied()
            .chain(fixed_ht_bank.iter().copied()).collect();
        // gate_on returns its whole predicate bank before each add;
        // SX0 is not the retained ak or flight c. It is globally clean,
        // including skipped shots, so all inherited measured-row contracts
        // and the existing loan-bank/dispatch choice remain unchanged.
        let parked_carry = if pool4 { sx[0] } else { c0 };
        if pool4 {
            assert!(!parked_source.contains(&parked_carry));
            assert!(!sc.zeros.contains(&parked_carry) && !dirty.contains(&parked_carry));
            assert!(![ak, c, act, x128].contains(&parked_carry));
            assert!(!v.contains(&parked_carry));
        }
        let add_parked = |b: &mut B, kb: usize, ctl: QubitId, sub: bool| {
            super::frogdrop_col::ring_cadd2_loan(b, &ring, &parked_source, kb, mt - kb, ctl, sub,
                                                 &sc.zeros, parked_carry, x128, &dirty, syhi_c,
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
        assert!(!p1_cross, "legacy vform_pk_ht reached a P1 crossing column");
        b.play(&vform_pk_ht, false);
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
            if pool5 && cp.sz.0 >= 1 && cp.sz.0 <= cp.sz.1 && cp.sz.1 <= 256 {
                // add_parked returned its carry; preserve ak/c and
                // restore SY before the inverse add and next size gate.
                sumframe::raw_lane_query(b, &ring, &sc.sz[..5], &fd.sy,
                    parked_carry, cp.sz.0, cp.sz.1, zero_pos, Some((ak, c)), &dirty);
            } else {
                let r = rotz(b, &[zero_pos]);
                b.play(&r, false);
                mc_xor(b, &[(ak, false), (wzero, true)], c, &[], &dirty);
                b.play(&r, true);
            }
            add_parked(b, kb, ak, true);
            gate_off(b, kb, act);
        }
        let f1 = b.tof;
        if ph_r { b.x(ph); }
        vmark(b, 3381);
        act_ht(b, ph_r);
        b.play(&vform_ht, true);
        if n == 257 { b.play(&zflip, false); }
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
            if n == 257 { b.play(&zflip, false); }
        assert!(!p1_cross, "legacy vform_pk_ht reached a P1 crossing column");
        b.play(&vform_pk_ht, false);
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
                let r = rotz(b, &[zero_pos]);
                b.play(&r, false);
                mc_xor(b, &[(ak, false), (wzero, true)], c, &[], &dirty);
                b.play(&r, true);
                add(b, kb, ak, true);
                gate_off(b, kb, act);
            }
            let f1 = b.tof;
            if ph_r { b.x(ph); }
            vmark(b, 3361);
            act_ht(b, ph_r);
            b.play(&vform_ht, true);
        if n == 257 { b.play(&zflip, false); }
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
        if n == 257 { b.play(&zflip, false); }
        assert!(!p1_cross, "legacy vform_pk_ht reached a P1 crossing column");
        b.play(&vform_pk_ht, false);
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
            let r = rotz(b, &[zero_pos]);
            b.play(&r, false);
            mc_xor(b, &[(ak, false), (wzero, true)], c, &[], &dirty);
            b.play(&r, true);
            add(b, kb, ak, true);
            gate_off(b, kb, act);
        }
        let f1 = b.tof;
        if ph_r { b.x(ph); }
        vmark(b, 3381);
        act_ht(b, ph_r);
        b.play(&vform_ht, true);
        if n == 257 { b.play(&zflip, false); }
        act_ht(b, ph_r);
        vmark(b, 3300);
        if ph_r { b.x(ph); }
        super::f1_profile("midg.vform", f1, b.tof);
        set_act(b);
    }
    b.play(&ht_narrow, true);
    if !stage(b) { return; } // 6
    b.play(&zshift, false);
    // lowq-671 L671_HRFIX=1: HR overshoot repair in the crossing columns. The search's q^ = q + 1 leaves
    // X = t_{j+1} + t_j; the map then gives r_{j+1} - r_j < 0, whose sign sits at ring[258 - bl(X)]. A detour to the
    // map layout reads it into f (plain HR shots: not switching, not delayed), X -= f Y and W -= f |t_j| repair the
    // step, and f is erased by the reciprocal test of the candidate X + Y (accepted iff the search had overshot).
    let hrfix = cp.hr && std::env::var("L671_HRFIX").map(|v| v == "1").unwrap_or(false)
        && !super::frogdrop_col::is_map_ctrl(cp);
    if let (true, Some(cross)) = (hrfix, &b8b) {
        let (wide_swap, probe_z) = super::frogdrop_col::L671_DETOUR.with(|d| d.borrow().clone()).expect("detour records");
        let (ghr, fl, t1) = (b.alloc(), b.alloc(), b.alloc());
        // (prototype: own gate and carry lanes; sx[0] / c0 may hold scratch here in dl columns)
        let (gq, cq) = (b.alloc(), b.alloc());
        // g_hr = !ph & !sw & !(delayed), delayed = [sz <= l0] & [sz > sy] (dl columns)
        let gh = rec(b, |b| {
            let mut lits = vec![(ph, true)];
            if cp.sw { lits.push((sc.sw, true)); }
            mc_xor(b, &lits, ghr, &[], &dirty);
            if cp.dl {
                super::frogdrop_col::ge_cd(b, &sc.sz, cp.l0 as isize + 1, t1, &[], &dirty);
                let gt = super::frogdrop_col::sz_gt_sy(b, fd, sc);
                let mut l2 = lits.clone();
                l2.push((t1, true));
                l2.push((sc.sz[sc.sz.len() - 1], false));
                mc_xor(b, &l2, ghr, &[], &dirty);
                b.play(&gt, true);
                super::frogdrop_col::ge_cd(b, &sc.sz, cp.l0 as isize + 1, t1, &[], &dirty);
            }
        });
        b.play(&gh, false);
        if std::env::var("L671_HRFIX_STEP").as_deref() == Ok("0") {
            b.play(&gh, true); b.free(cq); b.free(gq); b.free(t1); b.free(fl); b.free(ghr); let _ = stage(b); return;
        }
        // the detour: map layout, map, f ^= g_hr & sign, back (unitary AND uncomputes throughout: an overshot X or a
        // delayed shot's pre-stage-8 layout breaks the measured-uncompute invariants of the map and the size probe)
        let fu = b.force_unitary_and;
        b.force_unitary_and = true;
        b.play(&wide_swap, false);
        b.play(&probe_z, true);
        // (no signed-binary rows: their measured phases are not undone by an inverse play)
        let (booth, rows) = (b.allow_booth, b.no_rows);
        b.allow_booth = false;
        b.no_rows = true;
        let (ms_rec, ms_ctl) = super::frogdrop_col::map_stage_ex(b, fd, cp, sc);
        b.allow_booth = booth;
        b.no_rows = rows;
        assert!(ms_ctl.is_none());
        if std::env::var_os("L671_DBG").is_some() && cp.col == 72 {
            let cnt = |r: &[G]| { let mut m = std::collections::BTreeMap::new();
                for g in r { *m.entry(format!("{:?}", g).split('(').next().unwrap().to_string()).or_insert(0usize) += 1; } m };
            eprintln!("L671_DBG recs col {}: map {:?} probe {:?} swap {:?}", cp.col, cnt(&ms_rec), cnt(&probe_z), cnt(&wide_swap));
        }
        let step: usize = std::env::var("L671_HRFIX_STEP").ok().and_then(|v| v.parse().ok()).unwrap_or(9);
        b.play(&ms_rec, false);
        if step >= 2 {
            let (vlo, vhi) = (cp.smax.0.max(1), cp.smax.1.min(257));
            let leaves: Vec<(usize, QubitId)> = (vlo..=vhi).map(|v| (v, ring[258 - v])).collect();
            let mut swaps = vec![];
            let root = swap_tree(&fd.sx, &leaves, fd.sx.len(), &mut swaps);
            for &(bit, l0, r0) in &swaps { b.cswap(bit, l0, r0); }
            mc_xor(b, &[(ghr, false), (root, false)], fl, &[], &dirty);
            for &(bit, l0, r0) in swaps.iter().rev() { b.cswap(bit, l0, r0); }
        }
        if std::env::var_os("L671_DBG").is_some() {
            eprintln!("L671_DBG col {} fl {} ghr {} sx {:?} smax {:?} q0 {} q127 {} x128 {} ring0 {} ringtop {}", cp.col, fl.0, ghr.0, fd.sx.iter().map(|x| x.0).collect::<Vec<_>>(), cp.smax, q[0].0, q[127].0, x128.0, ring[0].0, ring[n-1].0);
            super::frogdrop_col::mark(b, 9101);
        }
        b.play(&ms_rec, true);
        if std::env::var_os("L671_DBG").is_some() { super::frogdrop_col::mark(b, 9105); }
        b.play(&probe_z, false);
        b.play(&wide_swap, true);
        b.force_unitary_and = fu;
        if std::env::var_os("L671_DBG").is_some() { super::frogdrop_col::mark(b, 9106); }
        if step < 3 { b.play(&gh, true); b.free(cq); b.free(gq); b.free(t1); b.free(fl); b.free(ghr); let _ = stage(b); return; }
        // the repair
        if step != 5 {
            // X -= f Y: a plain ripple over X-index [0, syhi] (X^ >= Y: the borrow stops at X^'s top bit, below 2^128)
            let syhi = cp.sy.1.min(nq);
            let span = (syhi + 1).min(n);
            let tl: Vec<QubitId> = (0..span).map(|i| ring[n - 1 - i]).collect();
            let mut sv: Vec<QubitId> = q.iter().copied().take(span).collect();
            if sv.len() < span { sv.push(x128); }
            let mut gate = |_b: &mut B, i: Option<usize>| i.map(|_| fl);
            ripple(b, &tl, &sv, cq, true, &mut |_b: &mut B| {}, &mut gate);
        }
        if std::env::var_os("L671_DBG").is_some() { super::frogdrop_col::mark(b, 9102); }
        if step == 3 { b.play(&gh, true); b.free(cq); b.free(gq); b.free(t1); b.free(fl); b.free(ghr); let _ = stage(b); return; }
        if let Some(pl) = pl {
            let wtop = 259 - if cp.dl { cp.dlr.min(L0P + 1) } else { L0P + 1 };
            let t: Vec<QubitId> = (0..wtop).map(|pos| super::payload::wl(&pl.p, pos)).collect();
            let sl = wtop.min(nq);
            let tr = rec(b, |b| super::payload::trans_one(b, &t, &q[..sl], 0, false, vec![(fl, false)], None, gq, cq,
                                                          &[], &pl.dirty));
            b.play(&tr, true);
        }
        if std::env::var_os("L671_DBG").is_some() { super::frogdrop_col::mark(b, 9103); }
        if step == 4 || step == 5 { b.play(&gh, true); b.free(cq); b.free(gq); b.free(t1); b.free(fl); b.free(ghr); let _ = stage(b); return; }
        // the erase: in the V form V = X + T - G with T - V < 2 Y; the candidate X + Y is accepted iff the carry out
        // of V's low sy + 1 bits plus Y is 0
        cross.toggle_hr_act(b);
        cross.play_hr(b, None, false, 3);
        {
            // g = 0 (sz + sy = 257, v = 39): T's bit is position sy itself, so the carry into sy decides
            let g0 = rec(b, |b| {
                b.play(&vg, false);
                let lits: Vec<(QubitId, bool)> = (0..VB).map(|i| (v[i], (39 >> i) & 1 == 0)).collect();
                mc_xor(b, &lits, t1, &[], &dirty);
                b.play(&vg, true);
            });
            b.play(&g0, false);
            let (sylo, syhi) = (cp.sy.0.max(1), cp.sy.1.min(nq));
            let span = (syhi + 1).min(n);
            let tl: Vec<QubitId> = (0..span).map(|i| ring[n - 1 - i]).collect();
            let mut sv: Vec<QubitId> = q.iter().copied().take(span).collect();
            if sv.len() < span { sv.push(x128); }
            let rd = sv.clone();
            let mut mid = |b: &mut B| {
                let lane = |v: usize| rd.get(v).copied();
                read_lane(b, &fd.sy, sylo, syhi, &lane, true, &[(ghr, false), (t1, true)], fl, &[], &[], &dirty);
                let lane0 = |v: usize| if v >= 1 { rd.get(v - 1).copied() } else { None };
                read_lane(b, &fd.sy, sylo, syhi, &lane0, true, &[(ghr, false), (t1, false)], fl, &[], &[], &dirty);
            };
            let mut gate = |_b: &mut B, _i: Option<usize>| None;
            ripple(b, &tl, &sv, cq, false, &mut mid, &mut gate);
            b.play(&g0, true);
        }
        cross.play_hr(b, None, true, 3);
        cross.toggle_hr_act(b);
        if std::env::var_os("L671_DBG").is_some() { super::frogdrop_col::mark(b, 9104); }
        b.play(&gh, true);
        b.free(cq); b.free(gq); b.free(t1); b.free(fl); b.free(ghr);
    }
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

/// C42: a live source cell adjacent to the mask boundary contributes only its
/// incoming carry at N257. Check all wires, including arbitrary passengers,
/// for a small support that exercises both boundary positions.
#[cfg(test)]
#[test]
fn c42_n257_transition_boundary_dirty_all_wire() {
    use super::frogdrop_col::rec;
    use super::tests_frogdrop::run;
    for top in [8, 9] {
    let mut b = B::new();
    let t = b.alloc_n(8);
    let s = b.alloc_n(8);
    let sy = b.alloc_n(8);
    let c = b.alloc();
    let g = b.alloc();
    let c0 = b.alloc();
    let pre = b.alloc_n(4);
    let temps = b.alloc_n(4);
    let dirty = b.alloc_n(16);
    let fwd = rec(&mut b, |b| trans_masked_q(
        b, &t, &s, 257, 258 - top, c, &sy, 0, 1, 2, g, c0, &pre, &temps, &dirty));
    b.play(&fwd, false);
    let forward = b.ops.len();
    b.play(&fwd, true);
    let width = b.width() as usize;
    let mut input = vec![0u64; width];
    let mut expected = vec![0u64; width];
    for (i, &q) in dirty.iter().enumerate() {
        input[q.0 as usize] = 0x9e37_79b9_7f4a_7c15u64.rotate_left((i * 7) as u32);
    }
    let mut seed = 0xc42_257_5eed_u64;
    for shot in 0..64 {
        seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
        let tv = (seed & 255) as u16;
        let sv = ((seed >> 13) & 255) as u16;
        let yv = 1 + (shot & 1);
        let cv = (shot >> 1) & 1;
        let boundary = top - yv;
        // The boundary kernel changes only bits 0..=boundary; the live
        // upper target passenger is deliberately preserved.
        let mask = (1 << (boundary + 1)) - 1;
        let sum = if cv != 0 {
            (tv & !mask) | ((tv + (sv & ((1 << boundary) - 1))) & mask)
        } else { tv };
        for bit in 0..8 {
            input[t[bit].0 as usize] |= (((tv >> bit) & 1) as u64) << shot;
            input[s[bit].0 as usize] |= (((sv >> bit) & 1) as u64) << shot;
            input[sy[bit].0 as usize] |= (((yv >> bit) & 1) as u64) << shot;
            expected[t[bit].0 as usize] |= (((sum >> bit) & 1) as u64) << shot;
        }
        input[c.0 as usize] |= (cv as u64) << shot;
    }
    for &q in t.iter() { expected[q.0 as usize] |= 0; }
    for i in 0..width {
        if !t.iter().any(|q| q.0 as usize == i) { expected[i] = input[i]; }
    }
    let got = run(&b.ops[..forward], width, &|q| *q = input.clone());
    assert_eq!(got.phase, 0);
    assert_eq!(got.q, expected, "N257 boundary forward all-wire");
    let round = run(&b.ops, width, &|q| *q = input.clone());
    assert_eq!(round.phase, 0);
    assert_eq!(round.q, input, "N257 boundary inverse all-wire");
    }
}

/// C42: the candidate window zero is Z's decoded leading lane before the
/// middle rotation. This checks the conjugated flip on all wires and phases.
#[cfg(test)]
#[test]
fn c42_n257_decoded_zflip_all_wire() {
    use super::frogdrop_col::rec;
    use super::tests_frogdrop::run;
    let mut b = B::new();
    let ring = b.alloc_n(257);
    let sz = b.alloc_n(8);
    let dirty = b.alloc_n(16);
    let care: std::collections::BTreeSet<usize> = (0..25).chain(233..257).collect();
    let prot = rec(&mut b, |b| rot_by_range_care(b, &ring, &sz, 57, 60, true, &dirty, &care));
    let flip = rec(&mut b, |b| {
        b.play(&prot, false); b.x(ring[256]); b.play(&prot, true);
    });
    b.play(&flip, false);
    let forward = b.ops.len();
    b.play(&flip, true);
    let width = b.width() as usize;
    let mut input = vec![0u64; width];
    let mut seed = 0x42_257_0dd_u64;
    for (i, &q) in ring.iter().chain(dirty.iter()).enumerate() {
        seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
        input[q.0 as usize] = seed.rotate_left((i % 64) as u32);
    }
    let mut expected = input.clone();
    for shot in 0..64 {
        let value = 57 + (shot % 4);
        for bit in 0..8 {
            input[sz[bit].0 as usize] |= (((value >> bit) & 1) as u64) << shot;
        }
        // DOWN by sz brings natural Z's high bit (sz-1) to frame 256:
        // UP maps frame 256 back to (256+sz) mod 257 = sz-1.
        expected[ring[value - 1].0 as usize] ^= 1u64 << shot;
    }
    for &q in &sz { expected[q.0 as usize] = input[q.0 as usize]; }
    let got = run(&b.ops[..forward], width, &|q| *q = input.clone());
    assert_eq!(got.phase, 0);
    assert_eq!(got.q, expected, "decoded Z-top target");
    let round = run(&b.ops, width, &|q| *q = input.clone());
    assert_eq!(round.phase, 0);
    assert_eq!(round.q, input, "decoded Z-top inverse");
}

/// Packed HR and HT payload loans, including arbitrary old root and dirty
/// passengers. The offset HT inputs satisfy the two-top-bit source contract.
#[cfg(test)]
#[test]
fn c42_n257_payload_loan_all_wire() {
    use super::tests_frogdrop::run;
    for ht in [false, true] {
        let mut b = B::new();
        let p = b.alloc_n(259);
        let sy = b.alloc_n(8);
        let cargo = b.alloc_n(16);
        let dirty: Vec<QubitId> = p[1..].iter().copied().chain(cargo.iter().copied()).collect();
        let narrow = if ht { c42_ht_partial_narrow(&mut b, &p, &sy, 1, 128, &dirty) } else { vec![] };
        let gather = c42_payload_gather(&mut b, &p, &sy, p[0], 1, 128, ht);
        b.play(&narrow, false);
        b.play(&gather, false);
        let forward = b.ops.len();
        b.play(&gather, true);
        b.play(&narrow, true);
        let width = b.width() as usize;
        let mut input = vec![0u64; width];
        let mut seed = 0xc42_10a0_u64 + ht as u64;
        for &q in p.iter().chain(cargo.iter()) {
            seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
            input[q.0 as usize] = seed;
        }
        for shot in 0..64 {
            let v = 1 + ((shot * 37) % 128);
            for bit in 0..8 { input[sy[bit].0 as usize] |= (((v >> bit) & 1) as u64) << shot; }
            let selected = if ht { v } else { 257 - v };
            let mask = 1u64 << shot;
            if ht {
                // Offset contract: p[v] and p[v+1] differ before narrowing.
                input[p[v].0 as usize] = (input[p[v].0 as usize] & !mask)
                    | ((!input[p[v + 1].0 as usize]) & mask);
            } else { input[p[selected].0 as usize] &= !mask; }
        }
        let got = run(&b.ops[..forward], width, &|q| *q = input.clone());
        assert_eq!(got.phase, 0, "payload loan forward phase ht={ht}");
        assert_eq!(got.q[p[0].0 as usize], 0, "selected R root is zero ht={ht}");
        for &q in sy.iter().chain(cargo.iter()) {
            assert_eq!(got.q[q.0 as usize], input[q.0 as usize], "cargo ht={ht} q={:?}", q);
        }
        let round = run(&b.ops, width, &|q| *q = input.clone());
        assert_eq!(round.phase, 0, "payload loan round-trip phase ht={ht}");
        assert_eq!(round.q, input, "payload loan all-wire round-trip ht={ht}");
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

#[cfg(test)]
#[test]
fn b12a_dirty_v_kernel_all_wire() {
    use super::tests_frogdrop::run;
    let mut cases = vec![
        ("HR-sy31", 31usize, 226usize, 0x8a5bcd_u64, 0x13579b_u64, true),
        ("HT-sy32", 32, 225, 0xb4d211, 0x2468ad, true),
        ("HR-trunc", 1, 232, 1, 0x345671, true),
        ("HT-sy128", 128, 129, 0x123456, 0x56789b, true),
        ("HR-inactive", 31, 226, 0x321abc, 0x123457, false),
    ];
    for syv in [32usize, 33, 64, 96, 113, 127, 128] {
        for g in [0usize, 1, 7, 15, 23] {
            let szv = 257usize.saturating_sub(syv + g);
            if szv < syv || szv > 256 { continue; }
            let d = (0x2345ab_u64.wrapping_mul((syv * 33 + g + 1) as u64)) & ((1 << 23) - 1);
            let zh = (0x1379bd_u64.wrapping_mul((syv * 7 + g + 1) as u64)) & ((1 << 23) - 1);
            cases.push(("screen", syv, szv, d, zh, true));
        }
    }
    for (label, syv, szv, d, zhval, active) in cases {
        let zhval = zhval | (1 << 23) | 1;
        let mut b = B::new();
        let q = b.alloc_n(128);
        let top = b.alloc();
        let zh = b.alloc_n(24);
        let win = b.alloc_n(TC + 1);
        let sy = b.alloc_n(8);
        let sz = b.alloc_n(8);
        let flag = b.alloc();
        let act = b.alloc();
        let gate_tmp = b.alloc();
        let dirty = b.alloc_n(32);
        let mut r = q[..23].to_vec(); r.push(top);
        let s1 = S1 { r, f: top, zero: flag, sgn: flag, gt: vec![gate_tmp],
            anc: vec![], andc: vec![], chain: vec![], dirty: dirty.clone() };
        let v = b12a_dirty_v_pair(&mut b, &zh, &win, &sz, (57, 256), &s1, act, false);
        let wrapper = super::frogdrop_col::rec(&mut b, |b| {
            mc_xor(b, &[(sy[5], true), (sy[6], true), (sy[7], true)], flag, &[], &dirty);
            for i in 0..23 { b.cswap(flag, q[i], q[64+i]); }
            b.play(&v, false);
            for i in 0..23 { b.cswap(flag, q[i], q[64+i]); }
            mc_xor(b, &[(sy[5], true), (sy[6], true), (sy[7], true)], flag, &[], &dirty);
        });
        b.play(&wrapper, false);
        let forward = b.ops.len();
        b.x(win[0]); b.x(win[7]); b.x(win[13]);
        b.play(&wrapper, true);
        let width = b.width() as usize;
        let mut input = vec![0u64; width];
        let set = |input: &mut Vec<u64>, lanes: &[QubitId], value: u64| {
            for (i, &lane) in lanes.iter().enumerate() {
                if (value >> i) & 1 != 0 { input[lane.0 as usize] = u64::MAX; }
            }
        };
        set(&mut input, &q[..23], d);
        if syv > 23 { input[q[syv - 1].0 as usize] = u64::MAX; }
        for i in 64..87 {
            if i < syv && i % 3 == 0 { input[q[i].0 as usize] = u64::MAX; }
        }
        set(&mut input, &zh, zhval);
        set(&mut input, &sy, syv as u64);
        set(&mut input, &sz, szv as u64);
        if active { input[act.0 as usize] = u64::MAX; }
        else { input[top.0 as usize] = u64::MAX; }
        for (i, &lane) in dirty.iter().enumerate() {
            input[lane.0 as usize] = 0xa5a5_5a5a_f0f0_0f0fu64.rotate_left((i * 7) as u32);
        }
        let f = run(&b.ops[..forward], width, &|q| *q = input.clone());
        assert_eq!(f.phase, 0, "{label} forward phase");
        for &lane in q.iter().chain(zh.iter()).chain(sy.iter()).chain(sz.iter())
            .chain([&top, &flag, &act, &gate_tmp]).chain(dirty.iter()) {
            assert_eq!(f.q[lane.0 as usize], input[lane.0 as usize],
                "{label} dirty passenger lane {}", lane.0);
        }
        let dused = if syv < 32 { 0 } else { d & ((1u64 << 23) - 1) };
        let mut ra = ((1u64 << 23) - 1) - dused;
        let mut rb = dused;
        let mut fa = 0u64; let mut fb = 0u64;
        for _ in 0..TC {
            ra = 2*ra + 1;
            let a = u64::from(ra >= zhval); if a != 0 { ra -= zhval; }
            fa = 2*fa + a;
            rb *= 2;
            let c = u64::from(rb >= zhval); if c != 0 { rb -= zhval; }
            fb = 2*fb + c;
        }
        let skipped = szv.saturating_add(TC).saturating_sub(257);
        let valid = TC - skipped;
        let mask = (1u64 << valid) - 1;
        let expected = if active { (mask.wrapping_sub(fa >> skipped).wrapping_sub(fb >> skipped)) & mask }
                       else { 0 };
        for j in 0..TC {
            let actual = f.q[win[1+j].0 as usize];
            let want = if j < valid && (expected >> (valid - 1 - j)) & 1 != 0 { u64::MAX } else { 0 };
            assert_eq!(actual, want, "{label} window j={j} sy={syv} sz={szv} D={dused} Zh={zhval}");
        }
        assert_eq!(f.q[win[0].0 as usize], 0, "{label} top window");
        let flips = (1u64 << (valid - 7)) | (1u64 << (valid - 13));
        let after = ((expected ^ flips).wrapping_sub(expected)) & mask;
        let mut edited = input.clone();
        edited[win[0].0 as usize] = u64::MAX;
        for j in 0..TC {
            edited[win[1+j].0 as usize] = if j < valid && (after >> (valid - 1 - j)) & 1 != 0
                { u64::MAX } else { 0 };
        }
        let both = run(&b.ops, width, &|q| *q = input.clone());
        assert_eq!(both.phase, 0, "{label} round trip phase");
        for (lane, (&got, &want)) in both.q.iter().zip(edited.iter()).enumerate() {
            assert_eq!(got, want, "{label} enter/edit/leave lane={lane}");
        }
        eprintln!("B12A_KERNEL {label} forward_ops={forward} delta={expected} valid={valid}");
    }
}

#[cfg(test)]
#[test]
fn b12a_dirty_v_kernel_virtual_zh() {
    use super::tests_frogdrop::run;
    // Every case is a physical Z representation of the same virtual odd Zh.
    // In the N257 frame the top lane aliases the window's zero lane and is
    // held at zero; the convert brackets it while it adds Zh into R.
    let cases = [
        ("sy31", 31usize, 226usize, 0x234567u64, false, 0usize),
        ("sy32", 32, 225, 0x654321, false, 0),
        ("sy128-park", 128, 129, 0x123457, true, 0),
        ("trunc232", 16, 238, 0x3579bd, true, 0),
        ("trunc241", 16, 241, 0x2468ac, true, 117),
        ("col26-sy44", 44, 210, 0x4d3c2b, true, 117),
    ];
    let mut checked = 0usize;
    for &(label, syv, szv, d, park, zlo) in &cases {
        let gval = 257 - syv - szv;
        for &top_zero in &[false, true] {
            for &low_odd in &[false, true] {
                let mut b = B::new();
                let q = b.alloc_n(128);
                let mut zh = b.alloc_n(if top_zero { 23 } else { 24 });
                let win = b.alloc_n(TC + 1);
                if top_zero { zh.push(win[0]); }
                let sz = b.alloc_n(8);
                let u = b.alloc_n(7);
                let gap = b.alloc_n(5);
                let top = b.alloc();
                let act = b.alloc();
                let gate_tmp = b.alloc();
                let dirty = b.alloc_n(32);
                let mut r = q[..23].to_vec(); r.push(top);
                let s1 = S1 { r, f: top, zero: zh[23], sgn: top, gt: vec![gate_tmp],
                    anc: vec![], andc: vec![], chain: vec![], dirty: dirty.clone() };
                S1_NOACT.with(|c| c.set(true));
                S1_ZLO.with(|c| c.set(zlo));
                if park {
                    S1_GATE.with(|c| *c.borrow_mut() = S1Gate::UPark {
                        u: u.clone(), g: gap.clone(), dk: dirty[31], d2: dirty[30] });
                } else { S1_GATE.with(|c| *c.borrow_mut() = S1Gate::Sz); }
                let v = b12a_dirty_v_pair(&mut b, &zh, &win, &sz,
                    (if zlo == 0 { 57 } else { zlo }, 256), &s1, act, top_zero);
                S1_GATE.with(|c| *c.borrow_mut() = S1Gate::Sz);
                S1_ZLO.with(|c| c.set(0));
                S1_NOACT.with(|c| c.set(false));
                b.play(&v, false);
                let forward = b.ops.len();
                b.play(&v, true);
                let width = b.width() as usize;
                let mut input = vec![0u64; width];
                let set = |input: &mut Vec<u64>, lanes: &[QubitId], value: u64| {
                    for (i, &lane) in lanes.iter().enumerate() {
                        if value >> i & 1 != 0 { input[lane.0 as usize] = u64::MAX; }
                    }
                };
                let dused = if syv < 32 { 0 } else { d & ((1 << 23) - 1) };
                set(&mut input, &q[..23], dused);
                if syv >= 32 {
                    for i in 64..87 { if i % 3 == 0 { input[q[i].0 as usize] = u64::MAX; } }
                }
                let physical_zh = 0x345670u64 | u64::from(low_odd)
                    | if top_zero { 0 } else { 1 << 23 };
                set(&mut input, &zh, physical_zh);
                set(&mut input, &sz, (szv - zlo) as u64);
                set(&mut input, &u, ((syv + gval) % 128) as u64);
                set(&mut input, &gap, gval as u64);
                input[act.0 as usize] = u64::MAX;
                for (i, &lane) in dirty.iter().enumerate() {
                    input[lane.0 as usize] = 0xa5a5_5a5a_f0f0_0f0fu64.rotate_left((i * 7) as u32);
                }
                let out = run(&b.ops[..forward], width, &|v| *v = input.clone());
                assert_eq!(out.phase, 0, "{label} phase top_zero={top_zero} odd={low_odd}");
                let virtual_zh = (1u64 << 23) | (physical_zh & ((1 << 23) - 2)) | 1;
                let mut ra = (1u64 << 23) - 1 - dused;
                let mut rb = dused;
                let mut fa = 0u64; let mut fb = 0u64;
                for _ in 0..TC {
                    ra = 2*ra + 1;
                    let a = u64::from(ra >= virtual_zh);
                    if a != 0 { ra -= virtual_zh; }
                    fa = 2*fa + a;
                    rb *= 2;
                    let c = u64::from(rb >= virtual_zh);
                    if c != 0 { rb -= virtual_zh; }
                    fb = 2*fb + c;
                }
                let valid = TC.min(257 - szv);
                let mask = (1u64 << valid) - 1;
                let expected = (mask.wrapping_sub(fa >> (TC - valid))
                    .wrapping_sub(fb >> (TC - valid))) & mask;
                for j in 0..TC {
                    let want = j < valid && (expected >> (valid - 1 - j)) & 1 != 0;
                    assert_eq!(out.q[win[1+j].0 as usize], if want { u64::MAX } else { 0 },
                        "{label} window j={j} top_zero={top_zero} odd={low_odd}");
                }
                for &lane in q.iter().chain(zh.iter()).chain(sz.iter()).chain(u.iter())
                    .chain(gap.iter()).chain([&top, &act, &gate_tmp]).chain(dirty.iter()) {
                    assert_eq!(out.q[lane.0 as usize], input[lane.0 as usize],
                        "{label} passenger lane {}", lane.0);
                }
                let rt = run(&b.ops, width, &|v| *v = input.clone());
                assert_eq!(rt.phase, 0, "{label} inverse phase");
                assert_eq!(rt.q, input, "{label} inverse all-wire");
                checked += 1;
            }
        }
    }
    eprintln!("B12A_VIRTUAL_ZH_KERNEL cases={checked} window_mismatches=0");
}
#[cfg(test)]
#[test]
fn b12a_yroot_dirty_counterexample() {
    use super::tests_frogdrop::run;
    let y = 0xd4c52f130ed_u64;
    let syv = 44usize;
    let szv = 210usize;
    let zhval = 0xbdf043_u64;
    let mut b = B::new();
    let q = b.alloc_n(128);
    let sy = b.alloc_n(8);
    let sz = b.alloc_n(8);
    let zh = b.alloc_n(24);
    let win = b.alloc_n(TC + 1);
    let top = b.alloc();
    let flag = b.alloc();
    let act = b.alloc();
    let gate_tmp = b.alloc();
    let dirty = b.alloc_n(32);
    let mut r = q[..23].to_vec(); r.push(top);
    let s1 = S1 { r, f: top, zero: flag, sgn: flag, gt: vec![gate_tmp],
        anc: vec![], andc: vec![], chain: vec![], dirty: dirty.clone() };
    let v = b12a_dirty_v_pair(&mut b, &zh, &win, &sz, (155, 241), &s1, act, false);
    let leaves: Vec<(usize, QubitId)> = (13..=99).map(|i| (i, q[i - 1])).collect();
    let mut swaps = vec![];
    let root = swap_tree(&sy, &leaves, sy.len(), &mut swaps);
    assert_eq!(root, q[12]);
    let wrapped = super::frogdrop_col::rec(&mut b, |b| {
        for &(bit, l, r) in &swaps { b.cswap(bit, l, r); }
        b.x(root);
        b.play(&v, false);
        b.x(root);
        for &(bit, l, r) in swaps.iter().rev() { b.cswap(bit, l, r); }
    });
    b.play(&wrapped, false);
    let width = b.width() as usize;
    let mut input = vec![0u64; width];
    for (i, &lane) in q.iter().enumerate() {
        if i < 64 && (y >> i) & 1 != 0 { input[lane.0 as usize] = u64::MAX; }
    }
    for (lanes, value) in [(&sy, syv as u64), (&sz, szv as u64), (&zh, zhval)] {
        for (i, &lane) in lanes.iter().enumerate() {
            if (value >> i) & 1 != 0 { input[lane.0 as usize] = u64::MAX; }
        }
    }
    input[act.0 as usize] = u64::MAX;
    for (i, &lane) in dirty.iter().enumerate() {
        input[lane.0 as usize] = 0xa5a5_5a5a_f0f0_0f0fu64.rotate_left((i * 7) as u32);
    }
    let f = run(&b.ops, width, &|v| *v = input.clone());
    assert_eq!(f.phase, 0);
    for &lane in q.iter().chain(sy.iter()).chain(sz.iter()).chain(zh.iter())
        .chain([&top, &flag, &act, &gate_tmp]).chain(dirty.iter()) {
        assert_eq!(f.q[lane.0 as usize], input[lane.0 as usize],
            "passenger lane {}", lane.0);
    }
    let mut actual = 0u64;
    for j in 0..TC {
        actual = (actual << 1) | u64::from(f.q[win[1 + j].0 as usize] != 0);
    }
    let d_predict = y & ((1 << 23) - 1);
    let d_circuit = d_predict & !(1 << 12);
    let model = |d: u64| {
        let ra0 = (1 << 23) - 1 - d;
        let ra = ((ra0 << TC) + (1 << TC) - 1) % zhval;
        let rb = (d << TC) % zhval;
        let e = u64::from(ra + rb >= zhval);
        let fw = ((1u64 << (23 + TC)) - 1) / zhval;
        (e, ((1 << TC) - 1 - fw + e) & ((1 << TC) - 1))
    };
    let (e_predict, v_predict) = model(d_predict);
    let (e_circuit, v_circuit) = model(d_circuit);
    assert_eq!((e_predict, e_circuit), (0, 1));
    assert_eq!(actual, v_circuit);
    assert_ne!(actual, v_predict);
    eprintln!("B12A_YROOT_REFUTED col=26 class=HR sy=44 sz=210 lane=Q[12] physical=529 D_predict={d_predict:#x} D_circuit={d_circuit:#x} e_predict={e_predict} e_circuit={e_circuit} V_actual={actual:#x} V_predict={v_predict:#x} phase={}", f.phase);
}
