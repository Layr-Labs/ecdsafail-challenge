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
pub const TC: usize = 25;

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
pub const PARK_RES: usize = 7;
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
    // care rotation maps every parked Q bit back to index sy + kb, for
    // kb < kmax; reserve bits above Q remain outside this bank. Keep the
    // entire public support, the old Y/done support and the live counter.
    let p_bank_lo = lsb.max(cp.sy.1.min(nq) + kmax);
    let p_bank = if p_bank_lo < loan_end { q[p_bank_lo..loan_end].to_vec() } else { vec![] };
    assert!(!p_bank.iter().any(|q| dirty.contains(q) || ring.contains(q) || sx.contains(q)
        || sc.sz.contains(q) || [act, c0, x128, pzero, ph, sc.sw].contains(q)));
    // N279 has physical K20 and h22. Keep the 24-bit head and 25-lane remainder:
    // ring[0..20] plus sx[2..5]. External q21/q22/q23 live in returned
    // SX owners between V calls, then park before R reclaims those lanes.
    // sx[0] (the quotient lane) is returned before each stage1_v geometry
    // query, so it can hold gt0 until that query is inverted. This alias is
    // exclusive to stage1_v; stage1_fwd keeps its original distinct gt0.
    let precision24 = k == 20 && n == 279 && nq == 128 && sx.len() == 8
        && dirty.len() == 259 && cp.h == 22
        && cp.sz.0 >= 57 && cp.sz.1 <= 256;
    // The physical window uses K21, but the reciprocal reads the top 24 ring
    // lanes. The care rotation must preserve all 24 destination lanes.
    let top_head = if precision24 { 24 } else { k };
    // ---- recordings
    let dest_r: std::collections::BTreeSet<usize> = (0..k + 2 + TC).chain(n - top_head..n).collect();
    let prot = rec(b, |b| rot_by_range_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty, &dest_r));
    // ring down by sz caring for the P-frame lanes `d` (24 = X's position 257 - sz, kb < 24 = headroom bit kb)
    let rotz = |b: &mut B, d: &[usize]| -> Vec<Gate> {
        let ds: std::collections::BTreeSet<usize> = d.iter().copied().collect();
        rec(b, |b| rot_by_range_care(b, &ring, &sc.sz, cp.sz.0, cp.sz.1, true, &dirty, &ds))
    };
    // the V form's scratch: sx[0], sx[2..5]; the divisor's zero top lane is the window top (X's position 257 - sz:
    // 0 on the act shots on entry and exit, never written by the V form; other shots replay consistently).
    // sx[1], sx[6..8], c0 and the P zero may hold parked bits while
    // stage1_v runs; only sx[0] is borrowed for the size threshold.
    // Carry summaries return before window gating. The first bank lane then
    // holds the optional third gt; increments exclude it until that gt is
    // erased. Threshold prefixes return before gt is computed and are used
    // again only after gt is erased, so they may reuse the complete bank.
    let mut reciprocal_r = ring[0..k + 1].to_vec();
    if precision24 { reciprocal_r.extend([sx[2], sx[3], sx[4], sx[5]]); }
    let mut p_gt = if precision24 { vec![sx[0]] } else { sx[2..4].to_vec() };
    if !precision24 { if let Some(&third) = p_bank.first() { p_gt.push(third); } }
    let zh: Vec<QubitId> = if precision24 { ring[n - 24..n].to_vec() } else { ring[n - k..n].to_vec() };
    if precision24 {
        assert_eq!(reciprocal_r.len(), 25);
        let unique: std::collections::BTreeSet<QubitId> = reciprocal_r.iter().copied().collect();
        assert_eq!(unique.len(), reciprocal_r.len());
        assert!(!reciprocal_r.iter().any(|q| zh.contains(q)
            || p_gt.contains(q) || [ring[k + 1], act].contains(q)
            || dirty.contains(q) || p_bank.contains(q) || sc.sz.contains(q)
            || [c0, x128, pzero, ph, sc.sw].contains(q)
            || sx.iter().enumerate().any(|(i, x)| !(2..=5).contains(&i) && x == q)));
        assert_eq!(p_gt[0], sx[0]);
        assert!(!zh.iter().any(|q| sx.contains(q) || sc.sz.contains(q)
            || [ring[k + 1], act, c0, x128, pzero, ph, sc.sw].contains(q)
            || dirty.contains(q) || p_bank.contains(q)));
        assert_eq!(k + 1, 21);
    }
    let s1 = S1 { r: reciprocal_r, f: sx[0], zero: ring[k + 1], sgn: sx[0], gt: p_gt,
                  anc: p_bank.iter().skip(1).copied().collect(),
                  andc: p_bank.clone(), chain: p_bank,
                  dirty: dirty.clone() };
    let win: Vec<QubitId> = ring[k + 1..k + 2 + TC].to_vec();
    let szr = (cp.sz.0, cp.sz.1);
    let fv = stage1_v(b, &zh, &win, &sc.sz, szr, &s1, act, true);
    let fr = stage1_v(b, &zh, &win, &sc.sz, szr, &s1, act, false);
    // enter / leave the V form on the act shots: X += T - G (R cleared by its own replay); v must be clear (sx)
    let vform = rec(b, |b| {
        b.play(&prot, false);
        b.play(&fv, false);
        b.play(&fr, true);
        b.play(&prot, true);
    });
    // q21/q22/q23 occupy sx[3]/sx[4]/sx[5] between V calls. Form v in SZ for each
    // threshold query, restoring SZ before any arithmetic or rotation.
    let external_q = |kb: usize| if precision24 && kb == k + 1 { Some(sx[3]) }
                         else if precision24 && kb == k + 2 { Some(sx[4]) }
                         else if precision24 && kb == k + 3 { Some(sx[5]) } else { None };
    assert!(!precision24 || (k + 1 == 21 && kmax <= 24));
    let qloc = |kb: usize| external_q(kb).unwrap_or(ring[kb]);
    assert!((0..kmax).all(|kb| qloc(kb) != ring[k + 1]));
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
        b.and_c(a, c, ak);
        b.x(c);
        ge_k(b, kb, c);
        super::f1_profile("midg.gate_on", f1, b.tof);
    };
    let gate_off = |b: &mut B, kb: usize, a: QubitId| {
        let f1 = b.tof;
        ge_k(b, kb, c);
        b.x(c);
        b.and_u(a, c, ak);
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
    let d24: std::collections::BTreeSet<usize> = (0..kmax).collect();
    let mk_cycle = |b: &mut B, extra: &[QubitId], ht: bool| -> (Vec<QubitId>, Vec<Gate>) {
        let mut q129: Vec<QubitId> = q.clone();
        q129.push(x128);
        let mut reserve: Vec<QubitId> = vec![c0, pzero, sx[1], sx[6], sx[7]];
        reserve.extend(extra.iter().copied().filter(|x| !sc.sz.contains(x)));
        reserve.extend(&sc.gx);
        reserve.truncate(nres);
        // (an HR park needs no reserve: sy + bl(q) <= 129 there)
        assert!(!MIDG_ON || !ht || reserve.len() == nres, "crossing reserve: {} of {} lanes", reserve.len(), nres);
        q129.extend(&reserve);
        let rq = rec(b, |b| rot_by_range_care(b, &q129, &fd.sy, cp.sy.0.min(128), cp.sy.1.min(128), true, &dirty, &d24));
        (q129, rq)
    };
    // HR block and HT block (act on g): ph and sw are 0 / (1, 0) on their act shots; HT division (act on sw): ph, g
    let (q129a, rqa) = mk_cycle(b, &[ph, sc.sw], cp.ht);
    let (q129b, rqb) = mk_cycle(b, &[ph, act], cp.ht);
    // a bit at Q-cycle index sy + kb >= its length would wrap onto Y: such a bit (a crossing step beyond the reserve)
    // stays in the headroom (a failure if set), so the swap is also gated by sy <= len - 1 - kb
    // (no bit gate: for kb >= B both lanes are zero on the act shots; v must be clear: sx holds the wrap flag)
    let wf = sx[0];
    let wrap_flag = |b: &mut B, kb: usize, qlen: usize| {
        super::frogdrop_col::ge_const_compact(b, &fd.sy, (qlen - kb) as isize, wf, &[], &dirty);
    };
    let park_for = |b: &mut B, a: QubitId, q129: &[QubitId], rq: &[Gate]| rec(b, |b| {
        let qlen = q129.len();
        let rz = rotz(b, &(0..kmax).collect::<Vec<_>>());
        b.play(&rz, false);
        b.play(rq, false);
        for kb in 0..kmax {
            if cp.sy.1.min(128) + kb >= qlen {
                let akp = sx[2];
                wrap_flag(b, kb, qlen);
                mc_xor(b, &[(a, false), (wf, true)], akp, &[], &dirty);
                super::mid2::mc_swap(b, &[(akp, false)], qloc(kb), q129[kb], &[], &dirty);
                mc_xor(b, &[(a, false), (wf, true)], akp, &[], &dirty);
                wrap_flag(b, kb, qlen);
            } else {
                super::mid2::mc_swap(b, &[(a, false)], qloc(kb), q129[kb], &[], &dirty);
            }
        }
        b.play(rq, true);
        b.play(&rz, true);
    });
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
        b.play(&park, false);
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
        let pads: Vec<QubitId> = if cp.dl { vec![x128, pzero, sx[1], sx[2], sx[6], sc.sw, ph] }
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
                let read_pre = if precision24 { vec![sx[0], sx[1], sx[2], pzero] }
                               else { vec![sx[0], sx[1], sx[2], sx[6], pzero] };
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
            super::frogdrop_col::ge_cd(b, &sc.sz, cp.l0 as isize + 1, ds.fa, &sx[1..], &dirty);
            mc_xor(b, &[(ds.fa, true), (ph, true)], sc.sw, &[], &dirty);
            super::frogdrop_col::ge_cd(b, &sc.sz, cp.l0 as isize + 1, ds.fa, &sx[1..], &dirty);
        };
        let set_act = |b: &mut B| {
            if cp.dn { mc_xor_dn(b, &[(ph, false)], actl, &sx[..2], &dirty, fd, cp.l0, false); }
            else { mc_xor(b, &[(ph, false)], actl, &sx[..2], &dirty); }
        };
        sw_toggle(b);
        set_act(b);
        // c, q's top bit, then the sy decoder's prefixes
        let l5: Vec<QubitId> = sx[2..].to_vec();
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
            let switch_pre: Vec<QubitId> = sx[1..].iter().copied().filter(|q| *q != sx[3] && *q != sx[4] && *q != sx[5]).collect();
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
        };
        let set_act = |b: &mut B| ht_act(b, fd, cp, sc, actl, &sx[..2], x128, &dirty);
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
            for kb in 0..kmax.min(NP) {
                let t: Vec<QubitId> = (kb..NP).map(|pos| super::payload::wl(&pl.p, pos)).collect();
                // a wrapped index holds Y, not bit kb (left in the headroom): wf = [sy >= len - kb] masks it
                let wrap = cp.sy.1.min(128) + kb >= qlen;
                let mut base = vec![(q129b[kb], false), (actl, false)];
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
            b.play(&park5, false);
            b.x(ph);
        }
        set_act(b);
        sw_toggle(b);
    }
    if !stage(b) { return; } // 5
    if cp.ht {
        let set_act = |b: &mut B| ht_act(b, fd, cp, sc, act, &sx[..2], x128, &dirty);
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
        b.play(&park, false);
        let f1 = b.tof;
        b.play(&vform, false);
        super::f1_profile("midg.vform", f1, b.tof);
        b.play(&park, false);
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
