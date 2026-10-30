//! Lilypad-G (r6_tick): the Lilypad walk in G-coordinates G = 2g - f, C_G = 2c_g - c_f (C_F = c_f).
//! Same decisions, same Q words, same eraser as lilypad.rs; the tick is
//!   e ^= 1 ^ X.v[1] ^ Y.v[1] ^ rho                (e = g mod 2 of the Lilypad state; Clifford)
//!   sigma = e & [h >= 0]
//!   X.v += (-1)^(1+e+rho) Y.v ; Y.c += (-1)^(1+e+rho) X.c      (UNCONTROLLED signed adds: forced digit)
//!   halve (relabel), then in frame t+1: cswap(X, Y) on sigma (no negation; signs float), rho ^= sigma
//!   h ^= sigma, h += 1, cap, sigma ^= X.c[1]
//! Rings: X = (G | C_F), Y = (F | C_G); G, F odd; C_F, C_G even. Signs of the four fields float; only rho = swap
//! parity is tracked. The eraser reads c_g through an in-place window conversion Y.c <- X.c + (-1)^rho Y.c
//! (= 2 d c_g, d = sign of the stored C_F) and an offset view (bsig + 1).
use super::builder::{B, G, ONE};
use super::chunked::AddRole;
use super::frogstrip::{sec, SEC_INV};
use super::modp_ft::ctrl_add_pool;
use super::lilypad::{
    cap_logic, eraser, fix_boundary, inc_unctl, inc_unctl_m, inc_unctl_short, inc_unctl_short2, lsc, mclear, win_len, ParityCtl, PSched, PScr, PWalk, HB,
};
use crate::circuit::{BitId, QubitId};

pub const LILYPAD_G_SCHED: &str = include_str!("lilypad_g_sched.txt");
/// Exact representation change: both stored cofactors are always even, so
/// store U=C_F/2 and V=C_G/2 and remove their constant-zero low lanes.
pub const HALF_COFACTOR_G: bool = true;
const L2_CONVERSION_FREE_ERASER: bool = true;
const L5_PRE_SWAP_Q12_ERASER: bool = true;

#[cfg(test)]
thread_local! {
    static TEST_L2: std::cell::Cell<i8> = const { std::cell::Cell::new(-1) };
    static TEST_L5: std::cell::Cell<i8> = const { std::cell::Cell::new(-1) };
    static TEST_DELAY_SIGMA: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
}

#[cfg(test)]
pub(crate) fn test_delay_sigma(value: bool) {
    TEST_DELAY_SIGMA.with(|v| v.set(value));
}

fn delay_sigma() -> bool {
    #[cfg(test)]
    { return TEST_DELAY_SIGMA.with(|v| v.get()); }
    #[cfg(not(test))]
    { true }
}

#[cfg(test)]
pub(crate) fn test_l2_override(value: Option<bool>) {
    TEST_L2.with(|v| v.set(value.map_or(-1, i8::from)));
}

#[cfg(test)]
pub(crate) fn test_l5_override(value: Option<bool>) {
    TEST_L5.with(|v| v.set(value.map_or(-1, i8::from)));
}

fn l2_enabled() -> bool {
    #[cfg(test)]
    {
        return TEST_L2.with(|v| match v.get() { 0 => false, 1 => true, _ => L2_CONVERSION_FREE_ERASER });
    }
    #[cfg(not(test))]
    {
        L2_CONVERSION_FREE_ERASER
    }
}

fn l5_enabled() -> bool {
    #[cfg(test)]
    {
        return TEST_L5.with(|v| match v.get() { 0 => false, 1 => true, _ => L5_PRE_SWAP_Q12_ERASER });
    }
    #[cfg(not(test))]
    {
        L5_PRE_SWAP_Q12_ERASER
    }
}

pub(crate) fn inverse_tmp_len_g() -> usize {
    #[cfg(test)]
    if let Ok(v) = std::env::var("LILYPAD_INV_TMP") {
        return v.parse().expect("LILYPAD_INV_TMP");
    }
    if l5_enabled() && HALF_COFACTOR_G { 0 } else { super::lilypad::NT }
}

pub(crate) fn inverse_d_len_g() -> usize { 0 }

pub(crate) fn inverse_sp_len_g() -> usize {
    if l5_enabled() && HALF_COFACTOR_G { 0 } else { super::lilypad::SB }
}

pub(crate) fn rho_stable(w: &PWalk, completed_ticks: usize) -> ParityCtl {
    if neg("norho") {
        return ParityCtl { qs: vec![], flip: false };
    }
    let mut qs = vec![w.h[0]];
    if w.log.len() >= 5 {
        qs.extend([w.log[0], w.log[4]]);
    } else if w.log.len()==4 || w.log.len()==3 {
        qs.push(w.log[0]);
    }
    ParityCtl { qs, flip: completed_ticks & 1 == 1 }
}

fn rho_pre_swap(w: &PWalk, t: usize, sigma: QubitId) -> ParityCtl {
    let mut rho = rho_stable(w, t);
    rho.qs.push(sigma);
    rho
}

thread_local! {
    /// frame846 O1b: the walk is in the cut geometry (ticks <= O1B_LAST and their target frames).
    static O1B_CUT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}
pub(crate) fn o1b_geom_cut() -> bool { O1B_CUT.with(|c| c.get()) }
fn o1b_set_cut(v: bool) { O1B_CUT.with(|c| c.set(v)); }
/// frame846 O1b: production schedule (cached) and the rule-v cut schedule (frames 1..=O1B_LAST+1: c - 1, kv <= c, w - 1).
fn sched_g_prod_ref() -> &'static PSched {
    static P: std::sync::OnceLock<PSched> = std::sync::OnceLock::new();
    P.get_or_init(sched_g_prod)
}
fn sched_g_cut_ref() -> &'static PSched {
    static C: std::sync::OnceLock<PSched> = std::sync::OnceLock::new();
    C.get_or_init(|| {
        let mut s = sched_g_prod();
        let last = super::pointadd_lilypad::O1B_LAST;
        s.w -= 1;
        for t in 1..=last + 1 {
            s.c[t] -= 1;
            s.kv[t] = s.kv[t].min(s.c[t]);
            assert!(s.kc[t] <= s.w + super::pointadd_lilypad::XC_CUT - s.c[t] && s.c[t] >= 3 && s.kv[t] >= 2 && s.kc[t] >= 3, "O1b cut sched t{t}");
        }
        s
    })
}
pub(crate) fn sched_g_cut() -> PSched { sched_g_cut_ref().clone() }
pub fn sched_g() -> PSched {
    if super::pointadd_lilypad::O1B && o1b_geom_cut() { sched_g_cut_ref().clone() } else { sched_g_prod_ref().clone() }
}
/// frame846 O1b: the production rings (287 lanes each) that agree with the cut rings (`ac`, `bc`, 286 each) at frame
/// O1B_LAST + 1 with E_X as X's value lane c' and E_Y as Y's value lane c' - 1 (c' = the cut frame's split).
pub(crate) fn o1b_prod_rings(sch: &PSched, ac: &[QubitId], bc: &[QubitId], ex: [QubitId; 2]) -> (Vec<QubitId>, Vec<QubitId>) {
    let fr = super::pointadd_lilypad::O1B_LAST + 1;
    let cut = sched_g_cut_ref();
    let (wp, wc) = (sch.w, cut.w);
    assert!(ac.len() == wc && bc.len() == wc && wp == wc + 1);
    let (cc, cp) = (cut.c[fr], sch.c[fr]);
    assert_eq!(cc + 1, cp);
    let mut a: Vec<Option<QubitId>> = vec![None; wp];
    let mut put = |i: usize, q: QubitId| { assert!(a[i].is_none(), "O1b X ring slot {i}"); a[i] = Some(q); };
    for f in 0..cc { put((f + fr - 1) % wp, ac[(f + fr - 1) % wc]); }
    put((cc + fr - 1) % wp, ex[0]);
    for s in 0..wp - cp { put((wp - 1 - s + fr - 1) % wp, ac[(wc - 1 - s + fr - 1) % wc]); }
    let a: Vec<QubitId> = a.into_iter().map(|x| x.expect("O1b X ring hole")).collect();
    // Y: bf(f) = bb[f], bsig(s) = bb[len - 1 - s]; insert E_Y at index cc - 1 (Y's cut value region is cc - 1 lanes).
    let k = cc - 1;
    let mut bb: Vec<QubitId> = bc[..k].to_vec();
    bb.push(ex[1]);
    bb.extend(&bc[k..]);
    assert_eq!(bb.len(), wp);
    (a, bb)
}
fn sched_g_prod() -> PSched {
    let mut sched = PSched::from_text(LILYPAD_G_SCHED);
    if HALF_COFACTOR_G {
        sched.w -= 1;
        for t in 1..=sched.s + 1 {
            sched.kc[t] -= 1;
        }
    }
    // Lane LILY-R: ring width cut with gnuchev's 856 transform (W -= WCUT, kc <= W - c, one value lane moved to the
    // cofactor from tick 450). WCUT = 0 leaves the schedule unchanged.
    let wcut = super::pointadd_lilypad::WCUT;
    if wcut > 0 {
        sched.w -= wcut;
        for t in 1..=sched.s + 1 {
            sched.kc[t] = sched.kc[t].min(sched.w - sched.c[t]);
        }
        if super::pointadd_lilypad::WTAIL {
            for t in 450..=sched.s + 1 {
                sched.c[t] -= 1;
                sched.kv[t] = sched.kv[t].min(sched.c[t]);
                sched.kc[t] = (sched.kc[t] + 1).min(sched.w - sched.c[t]);
            }
        }
    }
    // Schlussgang: the X ring loses its cofactor top lane (sched.w = X ring = 287); kc keeps bounding Y's cofactor
    // (<= 288 - c), X's is min(kc, 287 - c). At the endpoint frame S+1 X's value region drops 3 -> 2 lanes so X's
    // cofactor regains its 285th lane there (G = +-1 on the success support).
    let xc = super::pointadd_lilypad::XC_CUT;
    if xc > 0 {
        let e = sched.s + 1;
        assert_eq!((sched.w, sched.c[e], sched.kv[e], sched.kc[e]), (288, 3, 3, 285), "Schlussgang endpoint frame");
        for t in 1..=e {
            assert!(sched.kc[t] <= sched.w - sched.c[t] && sched.c[t] >= 3, "Schlussgang sched t{t}");
        }
        sched.c[e] -= 1;
        sched.kv[e] = sched.kv[e].min(sched.c[e]);
        sched.w -= xc;
        assert!(sched.kc[e] <= sched.w - sched.c[e] && sched.kv[e] == 2 && sched.c[e] == 2);
    }
    sched
}

/// Schlussgang: Y's value cut at frame `fr` (Y value region = c[fr] - cut): 1 on frames 1..S, 0 at the endpoint
/// frame S+1 where both rings are (2 | 285).
pub(crate) fn ycut_at(fr: usize) -> usize {
    static E: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    let e = *E.get_or_init(|| sched_g().s + 1);
    assert!(fr >= 1 && fr <= e, "ycut_at frame {fr}");
    if super::pointadd_lilypad::XC_CUT > 0 && fr == e { 0 } else { super::pointadd_lilypad::YV_CUT }
}

/// Schlussgang: X's cofactor region of frame `fr` (X ring = sched.w lanes).
fn sg_xreg(sch: &PSched, fr: usize) -> usize {
    sch.w - sch.c[fr]
}

/// Schlussgang: same-width tick into a zero-slack frame: X's boundary fix takes its cofactor top P while Y's cofactor
/// region keeps a top lane T without an X partner (kc[t+1] = 288 - c).
fn sg_gadget(sch: &PSched, t: usize) -> bool {
    t < sch.s && sch.c[t] == sch.c[t + 1] && sch.kc[t + 1] > sg_xreg(sch, t + 1)
}

/// Schlussgang: X's boundary fix of the halve of tick t (frame t+1), with the commute gadget on zero-slack same-width
/// ticks. P = X cofactor top (becomes X's value top), P' below it, T = Y cofactor top, T' below it.
///   cx(P'->P) [fix_boundary's first CNOT], cx(T'->T), cswap(sigma; P, T), cx(X value lane c-2 -> P) [its second].
/// No swap: P ^ P' = 0 (next tick's X cofactor check), T ^ T' restored after the role swap.
/// Swap: T ^ T' = 0 (midc fits X's region, next tick's check); T carries X's top residual P ^ P' through the swap and
/// cx(T'->T) after the clipped role swap restores old X's top lane in Y.
fn sg_xfix(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sg: QubitId) {
    if !sg_gadget(sch, t) {
        fix_boundary(b, &|f| w.af(t + 1, f), sch.c[t] - 1, sch.c[t + 1]);
        return;
    }
    let c = sch.c[t + 1];
    let xr = sg_xreg(sch, t + 1);
    assert_eq!(sch.kc[t + 1], xr + 1, "Schlussgang gadget kc t{t}");
    assert!(c >= 3 && sch.c[t] == c);
    let (p, pp) = (w.af(t + 1, c - 1), w.af(t + 1, c));
    assert!(p == w.asig(t + 1, xr) && pp == w.asig(t + 1, xr - 1), "Schlussgang gadget P t{t}");
    let (tt, tp) = (w.bsig(xr), w.bsig(xr - 1));
    assert!(tt == w.bf(c - 1) && tp == w.bf(c), "Schlussgang gadget T t{t}");
    assert!(![p, pp, tt, tp].contains(&sg), "Schlussgang gadget sigma t{t}");
    b.cx(pp, p);
    b.cx(tp, tt);
    b.cswap(sg, p, tt);
    b.cx(w.af(t + 1, c - 2), p);
}

/// Schlussgang: the cofactor role swap of frame t+1 over s in lo..kc, clipped to X's region. On zero-slack frames Y's
/// top lane T has no X partner: T ^= T' before (unless the gadget already did) and after the clipped loop.
fn sg_cswap_cof(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sg: QubitId, lo: usize, skip: &dyn Fn(usize) -> bool) {
    let kc = sch.kc[t + 1];
    let xr = sg_xreg(sch, t + 1);
    let top = kc > xr;
    if top {
        assert!(kc == xr + 1 && t < sch.s && xr >= 8, "Schlussgang role swap top t{t}");
        if !sg_gadget(sch, t) { b.cx(w.bsig(xr - 1), w.bsig(xr)); }
    }
    for s in lo..kc.min(xr) {
        if skip(s) { continue; }
        b.cswap(sg, w.asig(t + 1, s), w.bsig(s));
    }
    if top { b.cx(w.bsig(xr - 1), w.bsig(xr)); }
}

#[cfg(test)]
thread_local! {
    static G_TEST_NEG: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn g_test_neg(mode: u8) {
    G_TEST_NEG.with(|m| m.set(mode));
}

/// Test-only negative controls. Production builds are source-pinned and have
/// no environment-controlled circuit selectors.
#[cfg(test)]
fn neg(k: &str) -> bool {
    let code = match k {
        "norho" => 1,
        "flipsign" => 2,
        "noconvrho" => 3,
        "nofix" => 4,
        "noz" => 5,
        "noadrho" => 6,
        _ => 0,
    };
    code != 0 && G_TEST_NEG.with(|m| m.get() == code)
}

#[cfg(not(test))]
fn neg(_k: &str) -> bool {
    false
}

#[cfg(test)]
thread_local! {static C43_LOW_LOAN:std::cell::Cell<bool>=const{std::cell::Cell::new(true)};}
#[cfg(test)]
pub(crate) fn test_low_loan(v:bool){C43_LOW_LOAN.with(|c|c.set(v));}
fn low_loan_enabled()->bool {
    #[cfg(test)] {return C43_LOW_LOAN.with(|c|c.get());}
    #[cfg(not(test))] {true}
}

// C49 source defaults; standalone variants bake their own choices.
const C49_THIRD: bool = true;
const C49_LOW2: bool = true;
const C49_EARLY: bool = true;
#[cfg(test)]
thread_local! { static C49_REFERENCE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
#[cfg(test)]
pub(crate) fn c49_reference(v: bool) { C49_REFERENCE.with(|x|x.set(v)); }
fn c49_enabled(v: bool) -> bool {
    #[cfg(test)] { if C49_REFERENCE.with(|x|x.get()) { return false; } }
    v
}

/// Local G-coordinate wrapper: the incoming carry and low-window shape are
/// semantic parts of a pair, independent of relocated physical wire IDs.
#[allow(clippy::too_many_arguments)]
fn digit_add(b: &mut B, src: &[QubitId], tgt: &[QubitId], cin: Option<QubitId>,
    pool: &[QubitId], pairing: Option<(usize,bool)>, tick: usize, role: AddRole) {
    use super::chunked::{self, Pair, PairKey};
    if src.len() + 1 == tgt.len() && role == AddRole::Cofactor {
        // Schlussgang: tgt += sext(src). The sign-extension bit is a top-lane XOR (mod 2^n); the add itself runs on a
        // zero top source lane (paired chunks), or on one pool lane holding the sign copy (unpaired fallback).
        assert!(cin.is_none() && src.len() >= 2, "Schlussgang short cofactor add t{tick}");
        let (stop, ttop) = (*src.last().unwrap(), *tgt.last().unwrap());
        assert!(!pool.contains(&stop) && !pool.contains(&ttop));
        let mut a = src.to_vec(); a.push(chunked::ZERO_TOP);
        if let Some((division, inverse)) = pairing {
            let key = PairKey { division, tick, role };
            if !inverse || b.has_chunk_debts(key) {
                let pair = if inverse { Pair::Inverse(key) } else { Pair::Forward(key) };
                if chunked::try_add_paired_cin(b, &a, tgt, ONE, None, None, pool, Some(pair)) {
                    b.cx(stop, ttop);
                    return;
                }
                assert!(!inverse, "paired inverse must expose every carry position");
            }
        }
        assert!(!pool.is_empty(), "Schlussgang short cofactor add t{tick}: unpaired with an empty pool");
        let (l, rest) = pool.split_last().unwrap();
        let mut a2 = src.to_vec(); a2.push(*l);
        b.cx(stop, *l);
        ctrl_add_pool(b, &a2, tgt, ONE, rest);
        b.cx(stop, *l);
        return;
    }
    if src.len() + 1 == tgt.len() {
        assert!(cin.is_some() && !pool.is_empty() && role == AddRole::ValueHi2);
        b.cx(src.last().copied().or(cin).unwrap(), *tgt.last().unwrap());
        let mut a = src.to_vec(); a.push(chunked::ZERO_TOP);
        let pair = pairing.map(|(division, inverse)| {
            let key = PairKey { division, tick, role };
            if inverse { Pair::Inverse(key) } else { Pair::Forward(key) }
        });
        assert!(chunked::try_add_paired_cin(b, &a, tgt, ONE, None, cin, pool, pair));
        return;
    }
    assert_eq!(src.len(), tgt.len());
    if tgt.len()==1 {
        b.cx(src[0],tgt[0]);
        if let Some(q)=cin { b.cx(q,tgt[0]); }
        return;
    }
    if let Some((division,inverse))=pairing {
        let key=PairKey {division,tick,role};
        if !inverse || b.has_chunk_debts(key) {
            let pair=if inverse {Pair::Inverse(key)} else {Pair::Forward(key)};
            if chunked::try_add_paired_cin(b,src,tgt,ONE,None,cin,pool,Some(pair)) {return;}
            assert!(!inverse,"paired inverse must expose every carry position");
        }
    }
    if cin.is_some() {
        assert!(chunked::try_add_paired_cin(b,src,tgt,ONE,None,cin,pool,None));
    } else { ctrl_add_pool(b,src,tgt,ONE,pool); }
}

/// target += (-1)^(XOR negs ^ inv) source (mod 2^len), uncontrolled; paired chunks when `pairing` is set.
#[allow(clippy::too_many_arguments)]
/// Lane LILY-A: V3 is released in regenerated ticks >= 3 below 861 (at tick 2 the cofactor window is 4 lanes and its
/// sign compression reads Y.c lane 3 as the sign owner).
pub(crate) fn v3_virtual(t: usize) -> bool {
    !super::pointadd_lilypad::INV_V3_LANE && t >= 3
}

/// Lane LILY-A: the page relation mod 16, V = (G U + sp) F^-1 (mod 16), sp = 15 / 1.
fn page_v16(g: usize, f: usize, u: usize, rho: usize) -> usize {
    let sp = if rho == 0 { 15 } else { 1 };
    let fi = (1..16).step_by(2).find(|z| (f * z) % 16 == 1).unwrap();
    ((g * u + sp) * fi) % 16
}

/// Lane LILY-A: target ^= V3 at a consistent tick-boundary state of frame `fr`. vars: u0..u3 g1..g3 f1..f3 rho.
pub(crate) fn v3_chart_xor(b: &mut B, w: &PWalk, fr: usize, rho: &ParityCtl, target: QubitId) {
    static M: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    let masks = M.get_or_init(|| anf_masks(11, &|a| {
        let bit = |i: usize| (a >> i) & 1;
        let u = bit(0) + 2 * bit(1) + 4 * bit(2) + 8 * bit(3);
        let g = 1 + 2 * bit(4) + 4 * bit(5) + 8 * bit(6);
        let f = 1 + 2 * bit(7) + 4 * bit(8) + 8 * bit(9);
        (page_v16(g, f, u, bit(10)) >> 3) & 1 == 1
    }));
    let vars = [Cv::L(w.asig(fr, 0)), Cv::L(w.asig(fr, 1)), Cv::L(w.asig(fr, 2)), Cv::L(w.asig(fr, 3)),
        Cv::L(w.xv(fr, 1)), Cv::L(w.xv(fr, 2)), Cv::L(w.xv(fr, 3)), Cv::L(w.bf(1)), Cv::L(w.yv(fr, 2)), Cv::L(w.yv(fr, 3)), Cv::Rho];
    let dirty: Vec<QubitId> = (120..130).map(|k| w.af(fr, k)).collect();
    anf_xor(b, &vars, masks, rho, target, &dirty);
}

/// Lane LILY-A: V3 just before / after the inverse cofactor add (G' = 2 mod 4 in place). vars: u0..u3 g'2 g'3 f1..f3 e rho.
fn v3_add_masks(post: bool) -> &'static Vec<usize> {
    static PRE: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    static POST: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    let f = move |a: usize| {
        let bit = |i: usize| (a >> i) & 1;
        let u = bit(0) + 2 * bit(1) + 4 * bit(2) + 8 * bit(3);
        let gp = 2 + 4 * bit(4) + 8 * bit(5);
        let f = 1 + 2 * bit(6) + 4 * bit(7) + 8 * bit(8);
        let (e, rho) = (bit(9), bit(10));
        let s = 1 ^ e ^ rho;
        let g = if s == 0 { (gp + 16 - f) % 16 } else { (gp + f) % 16 };
        let v = if post { page_v16(gp, f, u, rho) } else { page_v16(g, f, u, rho) };
        (v >> 3) & 1 == 1
    };
    if post { POST.get_or_init(|| anf_masks(11, &f)) } else { PRE.get_or_init(|| anf_masks(11, &f)) }
}

/// Lane LILY-A: carries c_p (p <= 4) of t_fl + U at the inverse cofactor add, mod 16 model (vars as v3_add_masks).
fn add_carry_masks16(p: usize) -> Vec<usize> {
    anf_masks(11, &|a| {
        let bit = |i: usize| (a >> i) & 1;
        let u = bit(0) + 2 * bit(1) + 4 * bit(2) + 8 * bit(3);
        let gp = 2 + 4 * bit(4) + 8 * bit(5);
        let f = 1 + 2 * bit(6) + 4 * bit(7) + 8 * bit(8);
        let (e, rho) = (bit(9), bit(10));
        let s = 1 ^ e ^ rho;
        let g = if s == 0 { (gp + 16 - f) % 16 } else { (gp + f) % 16 };
        let tf = page_v16(g, f, u, rho) ^ if s == 1 { 15 } else { 0 };
        let mut cc = 0usize;
        for i in 0..p {
            let (ti, ui) = ((tf >> i) & 1, (u >> i) & 1);
            cc = (ti & ui) | (ti & cc) | (ui & cc);
        }
        cc == 1
    })
}

/// Lane LILY-A: pre-swap lane-3 role exchange with V3 charted: U3 ^= sigma D3, D3 = U3 ^ V3 (pre-swap U0 = 0),
/// rho' := 1 ^ P. vars: u1 u2 u3 g1 g2 g3 f1 f2 f3 rho'. Emitted before the lane-2 and lane-1 toggles.
/// v3r846: Some(c) when tick tn - 1 ran yv_boundary_residual into the frame tn of value width c <= 4 (t = 530, 531):
/// between that residual and the role swap, under sigma = 1, G fits c - 1 lanes and old F's lane c - 1 sits in X's top
/// lane as F_{c-1} ^ F_{c-2} ^ X_{c-2}; the xv / yv views alias the wrong lanes there.
pub(crate) fn v3r_narrow(tn: usize) -> Option<usize> {
    let sch = if super::pointadd_lilypad::O1B && o1b_geom_cut() { sched_g_cut_ref() } else { sched_g_prod_ref() };
    if tn < 2 || tn > sch.s { return None; }
    let (t, c) = (tn - 1, sch.c[tn]);
    let yres = super::pointadd_lilypad::YV_CUT == 1 && t < sch.s && sch.c[t] == c + 1 && sch.kv[tn] == c;
    if yres && c <= 4 { assert!(c >= 3); Some(c) } else { None }
}

fn v3_swap_u3(b: &mut B, w: &PWalk, t: usize, sg: QubitId) {
    static M: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    let masks = M.get_or_init(|| anf_masks(10, &|a| {
        let bit = |i: usize| (a >> i) & 1;
        let u = 2 * bit(0) + 4 * bit(1) + 8 * bit(2);
        let g = 1 + 2 * bit(3) + 4 * bit(4) + 8 * bit(5);
        let f = 1 + 2 * bit(6) + 4 * bit(7) + 8 * bit(8);
        ((page_v16(g, f, u, bit(9)) >> 3) & 1) ^ bit(2) == 1
    }));
    let fr = t + 1;
    let p = rho_stable(w, t);
    let rp = ParityCtl { qs: p.qs.clone(), flip: !p.flip };
    let u3 = w.asig(fr, 3);
    // v3r846 repair 1a: at the narrow residual frames read G and F as they are under sigma = 1.
    let narrow = v3r_narrow(fr);
    let (gl, fl, fix) = if let Some(c) = narrow {
        let (top, xs, ys) = (w.af(fr, c - 1), w.af(fr, c - 2), w.bf(c - 2));
        let gl: Vec<QubitId> = (1..4).map(|k| w.af(fr, k.min(c - 2))).collect();
        let fl: Vec<QubitId> = (1..4).map(|k| if k <= c - 2 { w.bf(k) } else { top }).collect();
        assert!(![top, xs, ys].contains(&sg) && ![top, xs, ys].contains(&u3) && p.qs.iter().all(|q| ![top, xs, ys].contains(q)));
        (gl, fl, Some((top, xs, ys)))
    } else {
        (vec![w.xv(fr, 1), w.xv(fr, 2), w.xv(fr, 3)], vec![w.bf(1), w.yv(fr, 2), w.yv(fr, 3)], None)
    };
    if let Some((top, xs, ys)) = fix { b.cx(xs, top); b.cx(ys, top); }
    let gl8 = [w.asig(fr, 1), w.asig(fr, 2), u3, gl[0], gl[1], fl[0], fl[1], fl[2]];
    let fact = V3R_STAGE >= 1 && !p.qs.is_empty() && {
        let mut all: Vec<QubitId> = gl8.to_vec(); all.push(sg); all.extend(p.qs.iter().copied()); v3r_distinct(&all)
    };
    if fact {
        v3r_swap_fact(b, gl8, &p.qs, !p.flip, sg);
    } else {
        if std::env::var_os("FROGTAIL_CK").is_some() { eprintln!("V3R swap ANF fallback t{t}"); }
        let mut vars = vec![Cv::L(w.asig(fr, 1)), Cv::L(w.asig(fr, 2)), Cv::L(w.asig(fr, 3)), Cv::L(gl[0]), Cv::L(gl[1]),
            Cv::L(gl[2]), Cv::L(fl[0]), Cv::L(fl[1]), Cv::L(fl[2]), Cv::Rho];
        vars.push(Cv::L(sg));
        let sgm: Vec<usize> = masks.iter().map(|&m| m | (1 << 10)).collect();
        let dirty: Vec<QubitId> = (120..130).map(|k| w.af(fr, k)).collect();
        anf_xor(b, &vars, &sgm, &rp, u3, &dirty);
    }
    if let Some((top, xs, ys)) = fix { b.cx(ys, top); b.cx(xs, top); }
}

/// Lane LILY-A: V2 is released in regenerated ticks >= 2 below 862.
pub(crate) fn v2_virtual(t: usize) -> bool {
    !super::pointadd_lilypad::INV_V2_LANE && t >= 2
}

/// Lane LILY-A: chart variables (a qubit, or the parity rho of a ParityCtl).
#[derive(Clone, Copy)]
pub(crate) enum Cv { L(QubitId), Rho }

/// ANF monomial masks (bit i = variable i) of a Boolean function of nv variables (Moebius transform).
pub(crate) fn anf_masks(nv: usize, f: &dyn Fn(usize) -> bool) -> Vec<usize> {
    let mut tt: Vec<u8> = (0..1usize << nv).map(|a| u8::from(f(a))).collect();
    for k in 0..nv {
        for m in 0..1usize << nv {
            if m & (1 << k) != 0 { tt[m] ^= tt[m ^ (1 << k)]; }
        }
    }
    tt.into_iter().enumerate().filter_map(|(m, c)| (c != 0).then_some(m)).collect()
}

/// target ^= f(vars) from its ANF: Rho expands into rho's lanes (and its flip); duplicate monomials cancel. Every
/// monomial is one multi-controlled toggle on restored dirty loans (lanes outside the monomial and the target).
pub(crate) fn anf_xor(b: &mut B, vars: &[Cv], masks: &[usize], rho: &ParityCtl, target: QubitId, dirty: &[QubitId]) {
    // Lane cloud-lily852 (in-place rho): fold rho into its first lane, chart on that one literal, unfold.
    let uses_rho = masks.iter().any(|&m| vars.iter().enumerate().any(|(i, v)| m >> i & 1 == 1 && matches!(v, Cv::Rho)));
    if uses_rho && !rho.qs.is_empty() && rho.qs.len() + usize::from(rho.flip) >= 2 {
        let r0 = rho.qs[0];
        let distinct = rho.qs.iter().enumerate().all(|(i, q)| !rho.qs[..i].contains(q));
        let clash = rho.qs.iter().any(|&r| r == target || dirty.contains(&r)
            || vars.iter().any(|v| matches!(v, Cv::L(q) if *q == r)));
        if distinct && !clash {
            for &r in &rho.qs[1..] { b.cx(r, r0); }
            if rho.flip { b.x(r0); }
            anf_xor_expand(b, vars, masks, &ParityCtl { qs: vec![r0], flip: false }, target, dirty);
            if rho.flip { b.x(r0); }
            for &r in rho.qs[1..].iter().rev() { b.cx(r, r0); }
            return;
        }
        if std::env::var_os("FROGTAIL_CK").is_some() { eprintln!("RHOIP fallback distinct={distinct} clash={clash}"); }
    }
    anf_xor_expand(b, vars, masks, rho, target, dirty);
}

fn anf_xor_expand(b: &mut B, vars: &[Cv], masks: &[usize], rho: &ParityCtl, target: QubitId, dirty: &[QubitId]) {
    use std::collections::BTreeMap;
    let mut terms: BTreeMap<Vec<u64>, bool> = BTreeMap::new();
    let mut flip = |k: Vec<u64>, terms: &mut BTreeMap<Vec<u64>, bool>| { let e = terms.entry(k).or_insert(false); *e = !*e; };
    for &m in masks {
        let mut base: Vec<u64> = vec![];
        let mut has_rho = false;
        for (i, v) in vars.iter().enumerate() {
            if m >> i & 1 == 1 {
                match v { Cv::L(q) => base.push(q.0), Cv::Rho => has_rho = true }
            }
        }
        let norm = |mut v: Vec<u64>| { v.sort_unstable(); v.dedup(); v };
        if has_rho {
            for &r in &rho.qs { let mut k = base.clone(); k.push(r.0); flip(norm(k), &mut terms); }
            if rho.flip { flip(norm(base.clone()), &mut terms); }
        } else {
            flip(norm(base), &mut terms);
        }
    }
    for (k, on) in terms {
        if !on { continue; }
        assert!(!k.contains(&target.0), "chart target among its controls");
        if k.is_empty() { b.x(target); continue; }
        let lits: Vec<(QubitId, bool)> = k.iter().map(|&q| (QubitId(q), false)).collect();
        let dl: Vec<QubitId> = dirty.iter().copied().filter(|d| *d != target && !k.contains(&d.0)).collect();
        super::mask::mc_xor(b, &lits, target, &[], &dl);
    }
}

/// Lane cloud-lily852: a chart's monomials with the rho fold of anf_xor: (fold lanes, flip, monomials).
fn anf_plan(vars: &[Cv], masks: &[usize], rho: &ParityCtl, target: QubitId, dirty: &[QubitId]) -> (Vec<QubitId>, bool, Vec<Vec<QubitId>>) {
    use std::collections::BTreeMap;
    let uses_rho = masks.iter().any(|&m| vars.iter().enumerate().any(|(i, v)| m >> i & 1 == 1 && matches!(v, Cv::Rho)));
    let (mut fold, mut fl, mut eff) = (vec![], false, ParityCtl { qs: rho.qs.clone(), flip: rho.flip });
    if uses_rho && !rho.qs.is_empty() && rho.qs.len() + usize::from(rho.flip) >= 2 {
        let distinct = rho.qs.iter().enumerate().all(|(i, q)| !rho.qs[..i].contains(q));
        let clash = rho.qs.iter().any(|&r| r == target || dirty.contains(&r)
            || vars.iter().any(|v| matches!(v, Cv::L(q) if *q == r)));
        if distinct && !clash {
            fold = rho.qs.clone(); fl = rho.flip; eff = ParityCtl { qs: vec![rho.qs[0]], flip: false };
        }
    }
    let mut terms: BTreeMap<Vec<u64>, bool> = BTreeMap::new();
    let flip = |k: Vec<u64>, terms: &mut BTreeMap<Vec<u64>, bool>| { let e = terms.entry(k).or_insert(false); *e = !*e; };
    for &m in masks {
        let mut base: Vec<u64> = vec![];
        let mut has_rho = false;
        for (i, v) in vars.iter().enumerate() {
            if m >> i & 1 == 1 {
                match v { Cv::L(q) => base.push(q.0), Cv::Rho => has_rho = true }
            }
        }
        let norm = |mut v: Vec<u64>| { v.sort_unstable(); v.dedup(); v };
        if has_rho {
            for &r in &eff.qs { let mut k = base.clone(); k.push(r.0); flip(norm(k), &mut terms); }
            if eff.flip { flip(norm(base.clone()), &mut terms); }
        } else {
            flip(norm(base), &mut terms);
        }
    }
    let out = terms.into_iter().filter(|(_, on)| *on).map(|(k, _)| {
        assert!(!k.contains(&target.0), "chart target among its controls");
        k.into_iter().map(QubitId).collect()
    }).collect();
    (fold, fl, out)
}

/// Lane cloud-lily852: target (|0>) ^= chart as a spec call; mode 0 compute, 1 measurement erase, 2 phase under `cond`.
fn anf_spec_g(b: &mut B, vars: &[Cv], masks: &[usize], rho: &ParityCtl, target: QubitId, dirty: &[QubitId], mode: u8, cond: BitId) {
    let (fold, flip, terms) = anf_plan(vars, masks, rho, target, dirty);
    let id = b.anf_spec(super::builder::AnfCall { fold, flip, terms, target, dirty: dirty.to_vec(), cond });
    b.g(match mode { 0 => G::AnfC(id), 1 => G::AnfU(id), _ => G::AnfP(id) });
}

/// Lane LILY-A: the page relation at a consistent state, V = (G U + sp) F^-1 = (G U + sp) F (mod 8), sp = 7 / 1.
fn page_v(g: usize, f: usize, u: usize, rho: usize) -> usize {
    let sp = if rho == 0 { 7 } else { 1 };
    ((g * u + sp) * f) % 8
}

/// Lane LILY-A: target ^= V2 at a consistent tick-boundary state of frame `fr`.
pub(crate) fn v2_chart_xor(b: &mut B, w: &PWalk, fr: usize, rho: &ParityCtl, target: QubitId) {
    // vars: u0 u1 u2 g1 g2 f1 f2 rho
    static M: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    let masks = M.get_or_init(|| anf_masks(8, &|a| {
        let bit = |i: usize| (a >> i) & 1;
        let (u, g, f) = (bit(0) + 2 * bit(1) + 4 * bit(2), 1 + 2 * bit(3) + 4 * bit(4), 1 + 2 * bit(5) + 4 * bit(6));
        (page_v(g, f, u, bit(7)) >> 2) & 1 == 1
    }));
    let vars = [Cv::L(w.asig(fr, 0)), Cv::L(w.asig(fr, 1)), Cv::L(w.asig(fr, 2)), Cv::L(w.xv(fr, 1)), Cv::L(w.xv(fr, 2)),
        Cv::L(w.bf(1)), Cv::L(w.yv(fr, 2)), Cv::Rho];
    let dirty: Vec<QubitId> = (120..128).map(|k| w.af(fr, k)).collect();
    anf_xor(b, &vars, masks, rho, target, &dirty);
}

/// Lane LILY-A: V2 just before / after the inverse cofactor add of tick t (G' = G +- F with G' = 2 mod 4 already in
/// place, s = 1 ^ e ^ rho the add sign). vars: u0 u1 u2 g'2 f1 f2 e rho.
fn v2_add_masks(post: bool) -> &'static Vec<usize> {
    static PRE: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    static POST: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    let f = move |a: usize| {
        let bit = |i: usize| (a >> i) & 1;
        let (u, gp, f) = (bit(0) + 2 * bit(1) + 4 * bit(2), 2 + 4 * bit(3), 1 + 2 * bit(4) + 4 * bit(5));
        let (e, rho) = (bit(6), bit(7));
        let s = 1 ^ e ^ rho;
        let g = if s == 0 { (gp + 8 - f) % 8 } else { (gp + f) % 8 };
        let v = if post { page_v(gp, f, u, rho) } else { page_v(g, f, u, rho) };
        (v >> 2) & 1 == 1
    };
    if post { POST.get_or_init(|| anf_masks(8, &f)) } else { PRE.get_or_init(|| anf_masks(8, &f)) }
}

/// tsave848 rank 3 (factored carry chart): the carries c1..c3 of the zero-slack shifted cofactor add without the
/// 35-monomial ANF. E = e ^ rho on rho's first lane, X1 = F1 ^ e ^ U0 E on F1, Y1 = U1 ^ U0 ^ U0 E on U1, P = X1 Y1
/// on the clean carry lane k; then c1 = U0 ^ U0 E, c2 = Y1 ^ P ^ U0 ^ U0 E, c3 = U2 ^ X2 Y2 with Y2 = U2 ^ c2 (on U2)
/// and X2 = F2 ^ e ^ P ^ U0 W, W = 1 ^ G'2 ^ e ^ E (on G'2). erase = false: z (|0>) ^= c3, the debt phases
/// (-1)^c_p (p <= 3) under their bits as Z / CZ on these lanes; erase = true: z (= c3) -> |0> by X measurement.
/// 10 / 9 Toffoli; every other lane restored, k returns |0>. verify_c3.py checks both blocks exhaustively.
#[allow(clippy::too_many_arguments)]
fn t3_c3_block(b: &mut B, l: &[QubitId; 6], e: QubitId, rho: &ParityCtl, z: QubitId, k: QubitId, erase: bool, debts: &[(usize, BitId)]) {
    let [u0, u1, u2, gp2, f1, f2] = *l;
    let r0 = rho.qs[0];
    for &r in &rho.qs[1..] { b.cx(r, r0); }
    if rho.flip { b.x(r0); }
    b.cx(e, r0);
    b.cx(e, f1); b.ccx(u0, r0, f1);
    b.cx(u0, u1); b.ccx(u0, r0, u1);
    b.and_c(f1, u1, k);
    for &(p, bit) in debts {
        let terms: Vec<Vec<QubitId>> = match p {
            1 => vec![vec![u0], vec![u0, r0]],
            2 => vec![vec![u1], vec![k], vec![u0], vec![u0, r0]],
            3 => continue,
            _ => panic!("t3 c3 chart: debt position {p}"),
        };
        let id = b.anf_spec(super::builder::AnfCall { fold: vec![], flip: false, terms, target: crate::circuit::NO_QUBIT,
            dirty: vec![], cond: bit });
        b.g(G::AnfP(id));
    }
    b.cx(u2, z);
    b.cx(u1, u2); b.cx(k, u2); b.cx(u0, u2); b.ccx(u0, r0, u2);
    b.cx(e, f2); b.cx(k, f2); b.cx(e, gp2); b.cx(r0, gp2); b.x(gp2); b.ccx(u0, gp2, f2);
    if erase {
        assert!(debts.is_empty());
        b.and_u(f2, u2, z);
    } else {
        b.ccx(f2, u2, z);
        for &(p, bit) in debts { if p == 3 { b.z_if(z, bit); } }
    }
    b.ccx(u0, gp2, f2); b.x(gp2); b.cx(r0, gp2); b.cx(e, gp2); b.cx(k, f2); b.cx(e, f2);
    b.ccx(u0, r0, u2); b.cx(u0, u2); b.cx(k, u2); b.cx(u1, u2);
    b.and_u(f1, u1, k);
    b.ccx(u0, r0, u1); b.cx(u0, u1);
    b.ccx(u0, r0, f1); b.cx(e, f1);
    b.cx(e, r0);
    if rho.flip { b.x(r0); }
    for &r in rho.qs[1..].iter().rev() { b.cx(r, r0); }
}

/// v3r846: factored V3 gadget stage (1 swap, 2 + hosted pre-add, 3 + mask term, 4 + 4-bit carry, 5 + post-add erase).
pub(crate) const V3R_STAGE: u8 = 5;

pub(crate) fn v3r_distinct(l: &[QubitId]) -> bool {
    l.iter().enumerate().all(|(i, q)| !l[..i].contains(q))
}

/// v3r846 G1: U3 ^= sg D3 (pre-swap, U0 = 0), rho' = parity(rq) ^ rflip folded on rq[0]. 11 Toffoli, lanes restored.
/// l = [u1, u2, u3, g1, g2, f1, f2, f3]. verify_v3r.py g1_swap.
fn v3r_swap_fact(b: &mut B, l: [QubitId; 8], rq: &[QubitId], rflip: bool, sg: QubitId) {
    let [u1, u2, u3, g1, g2, f1, f2, f3] = l;
    let r = rq[0];
    for &x in &rq[1..] { b.cx(x, r); }
    if rflip { b.x(r); }
    b.cx(f1, f2);
    b.cx(r, g1); b.x(g1);
    b.cx(r, g2); b.x(g2); b.cx(f2, g2); b.ccx(u2, g1, g2); b.ccx(f2, g1, g2);
    b.cx(f2, f3); b.ccx(f2, u2, f3); b.cx(r, f3); b.x(f3); b.ccx(u2, g1, f3); b.ccx(u1, g2, f3);
    b.ccx(sg, f3, u3);
    b.ccx(u1, g2, f3); b.ccx(u2, g1, f3); b.x(f3); b.cx(r, f3); b.ccx(f2, u2, f3); b.cx(f2, f3);
    b.ccx(f2, g1, g2); b.ccx(u2, g1, g2); b.cx(f2, g2); b.x(g2); b.cx(r, g2);
    b.x(g1); b.cx(r, g1);
    b.cx(f1, f2);
    if rflip { b.x(r); }
    for &x in rq[1..].iter().rev() { b.cx(x, r); }
}

/// v3r846 P gadget: tt ^= P ^ f3 (f3 = None) or tt ^= P (f3 = Some), P = V3_post = bit 3 of (G' U + sp) F^-1 mod 16 with
/// G' = 2 mod 4: P = 1 ^ f3 ^ u2 ^ r ^ u0 ^ u1 ^ c ^ u0 [g3 ^ r ^ u1 ^ A B] ^ u1 (A ^ c), c = f1 ^ f2, A = g2 ^ r, B = u1 ^ c.
/// r = rho on lane `r` (folded). 4 Toffoli, every other lane restored. verify_v3r.py p_gadget.
#[allow(clippy::too_many_arguments)]
fn v3r_p(b: &mut B, tt: QubitId, u0: QubitId, u1: QubitId, u2: QubitId, g2: QubitId, g3: QubitId, f1: QubitId, f2: QubitId,
    r: QubitId, f3: Option<QubitId>) {
    b.x(tt); b.cx(u2, tt); b.cx(r, tt); b.cx(u0, tt); b.cx(u1, tt); b.cx(f1, tt); b.cx(f2, tt);
    if let Some(q) = f3 { b.cx(q, tt); }
    b.cx(r, g2);
    b.cx(f1, u1); b.cx(f2, u1);
    b.ccx(g2, u1, g3);
    b.cx(r, g3); b.cx(u1, g3); b.cx(f1, g3); b.cx(f2, g3);
    b.ccx(u0, g3, tt);
    b.cx(f2, g3); b.cx(f1, g3); b.cx(u1, g3); b.cx(r, g3);
    b.ccx(g2, u1, g3);
    b.cx(f2, u1); b.cx(f1, u1);
    b.cx(f1, g2); b.cx(f2, g2);
    b.ccx(u1, g2, tt);
    b.cx(f2, g2); b.cx(f1, g2); b.cx(r, g2);
}

fn v3r_fold(b: &mut B, rho: &ParityCtl) {
    let r0 = rho.qs[0];
    for &r in &rho.qs[1..] { b.cx(r, r0); }
    if rho.flip { b.x(r0); }
}

fn v3r_unfold(b: &mut B, rho: &ParityCtl) {
    let r0 = rho.qs[0];
    if rho.flip { b.x(r0); }
    for &r in rho.qs[1..].iter().rev() { b.cx(r, r0); }
}

/// v3r846 G2: host3 (|0>) <- V3_pre before the hosted cofactor add: V3_pre = V3_post ^ U3 ^ c3 (peak846 v3gad.py G2),
/// c3 = U2 ^ X2 Y2 (tsave848 t3 chain: E = e ^ rho, X1 = F1 ^ e ^ U0 E, Y1 = U1 ^ U0 ^ U0 E, P' = X1 Y1 on the clean lane
/// k or toggled twice without it, Y2 = U2 ^ Y1 ^ P' ^ U0 ^ U0 E, X2 = F2 ^ e ^ P' ^ U0 (1 ^ G'2 ^ rho)), V3_post = P.
/// l = [u0, u1, u2, u3, g2, g3, f1, f2, f3]. 14 Toffoli recorded with k, 17 without. verify_v3r.py g2_pre.
fn v3r_pre(b: &mut B, host3: QubitId, k: Option<QubitId>, l: [QubitId; 9], e: QubitId, rho: &ParityCtl) {
    let [u0, u1, u2, u3, g2, g3, f1, f2, f3] = l;
    v3r_fold(b, rho);
    let r = rho.qs[0];
    b.cx(e, r);
    b.cx(e, f1); b.ccx(u0, r, f1);
    b.cx(u0, u1); b.ccx(u0, r, u1);
    if let Some(k) = k { b.and_c(f1, u1, k); }
    b.cx(u1, u2);
    if let Some(k) = k { b.cx(k, u2); } else { b.ccx(f1, u1, u2); }
    b.cx(u0, u2); b.ccx(u0, r, u2);
    b.cx(e, f2);
    if let Some(k) = k { b.cx(k, f2); } else { b.ccx(f1, u1, f2); }
    b.cx(e, g2); b.cx(r, g2); b.x(g2); b.ccx(u0, g2, f2);
    b.and_c(f2, u2, host3);
    b.ccx(u0, g2, f2); b.x(g2); b.cx(r, g2); b.cx(e, g2);
    if let Some(k) = k { b.cx(k, f2); } else { b.ccx(f1, u1, f2); }
    b.cx(e, f2);
    b.ccx(u0, r, u2); b.cx(u0, u2);
    if let Some(k) = k { b.cx(k, u2); } else { b.ccx(f1, u1, u2); }
    b.cx(u1, u2);
    if let Some(k) = k { b.and_u(f1, u1, k); }
    b.ccx(u0, r, u1); b.cx(u0, u1);
    b.ccx(u0, r, f1); b.cx(e, f1);
    b.cx(e, r);
    b.cx(u3, host3);
    v3r_p(b, host3, u0, u1, u2, g2, g3, f1, f2, r, Some(f3));
    b.cx(u2, host3);
    v3r_unfold(b, rho);
}

/// v3r846 G5: host3 (= V3_post = P after the hosted add) -> |0>: the same 4-Toffoli P gadget. verify_v3r.py g5_post.
fn v3r_post(b: &mut B, host3: QubitId, l: [QubitId; 9], rho: &ParityCtl) {
    let [u0, u1, u2, _u3, g2, g3, f1, f2, f3] = l;
    v3r_fold(b, rho);
    v3r_p(b, host3, u0, u1, u2, g2, g3, f1, f2, rho.qs[0], Some(f3));
    v3r_unfold(b, rho);
}

#[derive(Clone, Copy)]
enum V3rOp { Fold, Unfold, Pf3, Cx(QubitId, QubitId), X(QubitId), Ccx(QubitId, QubitId, QubitId), AndC(QubitId, QubitId, QubitId),
    AndU(QubitId, QubitId, QubitId), D12, D3, D4 }

/// v3r846 G4: the zero-slack kk = 4 carry chart. erase = false: zero (|0>) <- c4 = U3 ^ X3 Y3 (X3 = P ^ s ^ c3 on F3,
/// Y3 = U3 ^ c3 on U3, c3 = U2 ^ X2 Y2 held on `one`), the debt phases (-1)^{c_p} (p <= 4) under their bits; one, k-lanes
/// and every other lane restored. erase = true: the exact inverse without debts (zero = c4 -> |0>).
/// l = [u0, u1, u2, u3, g2, g3, f1, f2, f3]. 31 / 30 Toffoli recorded. verify_v3r.py g4_block.
fn v3r_c4_block(b: &mut B, l: [QubitId; 9], e: QubitId, rho: &ParityCtl, zero: QubitId, one: QubitId, erase: bool,
    debts: &[(usize, BitId)]) {
    use V3rOp::*;
    let [u0, u1, u2, u3, g2, g3, f1, f2, f3] = l;
    let r = rho.qs[0];
    let mut ops: Vec<V3rOp> = vec![Fold, Pf3, Cx(e, r),
        Cx(e, f1), Ccx(u0, r, f1), Cx(u0, u1), Ccx(u0, r, u1),
        AndC(f1, u1, zero), D12,
        Cx(u1, u2), Cx(zero, u2), Cx(u0, u2), Ccx(u0, r, u2),
        Cx(e, f2), Cx(zero, f2), Cx(e, g2), Cx(r, g2), X(g2), Ccx(u0, g2, f2),
        AndC(f2, u2, one),
        Ccx(u0, g2, f2), X(g2), Cx(r, g2), Cx(e, g2), Cx(zero, f2), Cx(e, f2),
        Ccx(u0, r, u2), Cx(u0, u2), Cx(zero, u2), Cx(u1, u2),
        AndU(f1, u1, zero),
        Ccx(u0, r, u1), Cx(u0, u1), Ccx(u0, r, f1), Cx(e, f1),
        Cx(u2, one), D3,
        Cx(one, f3), Cx(r, f3), X(f3), Cx(one, u3),
        AndC(f3, u3, zero), Cx(u3, zero), Cx(one, zero), D4,
        Cx(one, u3), X(f3), Cx(r, f3), Cx(one, f3),
        Cx(u2, one),
        Cx(e, f1), Ccx(u0, r, f1), Cx(u0, u1), Ccx(u0, r, u1),
        Cx(u1, u2), Ccx(f1, u1, u2), Cx(u0, u2), Ccx(u0, r, u2),
        Cx(e, f2), Ccx(f1, u1, f2), Cx(e, g2), Cx(r, g2), X(g2), Ccx(u0, g2, f2),
        AndU(f2, u2, one),
        Ccx(u0, g2, f2), X(g2), Cx(r, g2), Cx(e, g2), Ccx(f1, u1, f2), Cx(e, f2),
        Ccx(u0, r, u2), Cx(u0, u2), Ccx(f1, u1, u2), Cx(u1, u2),
        Ccx(u0, r, u1), Cx(u0, u1), Ccx(u0, r, f1), Cx(e, f1),
        Cx(e, r), Pf3, Unfold];
    if erase { ops.reverse(); }
    for op in ops {
        match op {
            Fold => if erase { v3r_unfold(b, rho) } else { v3r_fold(b, rho) },
            Unfold => if erase { v3r_fold(b, rho) } else { v3r_unfold(b, rho) },
            Pf3 => v3r_p(b, f3, u0, u1, u2, g2, g3, f1, f2, r, None),
            Cx(a, t) => b.cx(a, t),
            X(t) => b.x(t),
            Ccx(a, c, t) => b.ccx(a, c, t),
            AndC(a, c, t) => if erase { b.and_u(a, c, t) } else { b.and_c(a, c, t) },
            AndU(a, c, t) => if erase { b.and_c(a, c, t) } else { b.and_u(a, c, t) },
            D12 => if !erase {
                for &(p, bit) in debts {
                    let terms: Vec<Vec<QubitId>> = match p {
                        1 => vec![vec![u0], vec![u0, r]],
                        2 => vec![vec![u1], vec![zero], vec![u0], vec![u0, r]],
                        3 | 4 => continue,
                        _ => panic!("v3r c4 chart: debt position {p}"),
                    };
                    let id = b.anf_spec(super::builder::AnfCall { fold: vec![], flip: false, terms, target: crate::circuit::NO_QUBIT,
                        dirty: vec![], cond: bit });
                    b.g(G::AnfP(id));
                }
            },
            D3 => if !erase { for &(p, bit) in debts { if p == 3 { b.z_if(one, bit); } } },
            D4 => if !erase { for &(p, bit) in debts { if p == 4 { b.z_if(zero, bit); } } },
        }
    }
}

/// Lane LILY-A: carries c_p (p = 1, 2, 3) into bit p of t_fl + U at the inverse cofactor add (t_fl = V ^ (s ? 7 : 0)).
fn add_carry_masks(p: usize) -> Vec<usize> {
    anf_masks(8, &|a| {
        let bit = |i: usize| (a >> i) & 1;
        let (u, gp, f) = (bit(0) + 2 * bit(1) + 4 * bit(2), 2 + 4 * bit(3), 1 + 2 * bit(4) + 4 * bit(5));
        let (e, rho) = (bit(6), bit(7));
        let s = 1 ^ e ^ rho;
        let g = if s == 0 { (gp + 8 - f) % 8 } else { (gp + f) % 8 };
        let tf = page_v(g, f, u, rho) ^ if s == 1 { 7 } else { 0 };
        let mut cc = 0usize;
        for i in 0..p {
            let (ti, ui) = ((tf >> i) & 1, (u >> i) & 1);
            cc = (ti & ui) | (ti & cc) | (ui & cc);
        }
        cc == 1
    })
}

/// Lane LILY-A: pre-swap lane-2 role exchange with V2 charted: U2 ^= sigma & D2, D2 = U2 ^ V2 (pre-swap, U0 = 0),
/// rho' := 1 ^ P as for lane 1. vars: u1 u2 g1 g2 f1 f2 rho'. Emitted before the lane-1 toggle (D2 reads U1).
fn v2_swap_u2(b: &mut B, w: &PWalk, t: usize, sg: QubitId) {
    static M: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    let masks = M.get_or_init(|| anf_masks(7, &|a| {
        let bit = |i: usize| (a >> i) & 1;
        let (u, g, f) = (2 * bit(0) + 4 * bit(1), 1 + 2 * bit(2) + 4 * bit(3), 1 + 2 * bit(4) + 4 * bit(5));
        ((page_v(g, f, u, bit(6)) >> 2) & 1) ^ bit(1) == 1
    }));
    let fr = t + 1;
    let p = rho_stable(w, t);
    {
        // tsave848 rank 3 (factored chart): D2 = 1 ^ f2 ^ rho' ^ u1 (1 ^ g1 ^ rho') = A ^ U1 B, A = F2 ^ P,
        // B = G1 ^ P (P = the stable parity incl. its flip). Fold P into its first lane, build A on F2 and B on that
        // lane in place, then U2 ^= sigma (A ^ U1 B): 3 Toffoli instead of the 11-Toffoli ANF; every lane restored.
        let (u1, u2, g1, f2) = (w.asig(fr, 1), w.asig(fr, 2), w.xv(fr, 1), w.yv(fr, 2));
        let lanes = [u1, u2, g1, f2, sg];
        let ok = !p.qs.is_empty()
            && lanes.iter().enumerate().all(|(i, q)| !lanes[..i].contains(q))
            && p.qs.iter().enumerate().all(|(i, q)| !p.qs[..i].contains(q) && !lanes.contains(q));
        if ok {
            let r0 = p.qs[0];
            for &r in &p.qs[1..] { b.cx(r, r0); }
            b.cx(r0, f2); if p.flip { b.x(f2); }
            b.cx(g1, r0); if p.flip { b.x(r0); }
            b.ccx(u1, r0, f2);
            b.ccx(sg, f2, u2);
            b.ccx(u1, r0, f2);
            if p.flip { b.x(r0); }
            b.cx(g1, r0);
            if p.flip { b.x(f2); }
            b.cx(r0, f2);
            for &r in p.qs[1..].iter().rev() { b.cx(r, r0); }
            return;
        }
        if std::env::var_os("FROGTAIL_CK").is_some() { eprintln!("T3 v2_swap_u2 fallback t{t}"); }
    }
    // rho' = 1 ^ P: one more flip of the stable parity
    let rp = ParityCtl { qs: p.qs.clone(), flip: !p.flip };
    // U2 ^= sg & D2: every monomial gains the control sg
    let u2 = w.asig(fr, 2);
    let vars = [Cv::L(w.asig(fr, 1)), Cv::L(w.asig(fr, 2)), Cv::L(w.xv(fr, 1)), Cv::L(w.xv(fr, 2)), Cv::L(w.bf(1)), Cv::L(w.yv(fr, 2)), Cv::Rho];
    let sgm: Vec<usize> = masks.iter().map(|&m| m | (1 << 7)).collect();
    let mut v8 = vars.to_vec(); v8.push(Cv::L(sg));
    let dirty: Vec<QubitId> = (120..128).map(|k| w.af(fr, k)).collect();
    anf_xor(b, &v8, &sgm, &rp, u2, &dirty);
}

/// Lane LILY-A: V1 is released in regenerated ticks >= 2 below 863.
pub(crate) fn v1_virtual(t: usize) -> bool {
    !super::pointadd_lilypad::INV_V1_LANE && t >= 2
}

/// Lane LILY-A: target ^= V1 at a consistent tick-boundary state of frame `fr` (G odd, U0 = the last sigma):
/// V1 = U1 ^ U0 (G1 ^ F1 ^ 1) ^ F1 ^ 1 ^ rho, from f*V = G*U + sp (mod 4), sp1 = !rho.
pub(crate) fn v1_chart_xor(b: &mut B, w: &PWalk, fr: usize, rho: &ParityCtl, target: QubitId) {
    let (u0, u1, g1, f1) = (w.asig(fr, 0), w.asig(fr, 1), w.af(fr, 1), w.bf(1));
    b.cx(u1, target);
    b.ccx(u0, g1, target);
    b.cx(u0, target);
    b.ccx(u0, f1, target);
    b.cx(f1, target);
    b.x(target);
    rho.xor_into(b, target);
}

/// Lane LILY-A: pre-swap lane-1 role exchange with V1 charted: U1 ^= sigma & (U1 ^ V1) = sigma & (F1 ^ P), P = the
/// stable parity h0 ^ log0 ^ log4 ^ (t & 1) of the current h/log lanes (pre-swap U0 = 0; F1 before the value swaps).
fn v1_swap_u1(b: &mut B, w: &PWalk, t: usize, sg: QubitId) {
    let u1 = w.asig(t + 1, 1);
    let p = rho_stable(w, t);
    b.ccx(sg, w.bf(1), u1);
    for &x in &p.qs { b.ccx(sg, x, u1); }
    if p.flip { b.cx(sg, u1); }
}

/// Lane LILY-A: V0 is released in regenerated ticks >= 2 below 864.
pub(crate) fn v0_virtual(t: usize) -> bool {
    !super::pointadd_lilypad::INV_V0_LANE && t >= 2
}

/// Lane LILY-A: F0 is released in regenerated ticks >= 2 below 865.
fn f0_absent(pairing: Option<(usize, bool)>, t: usize) -> bool {
    !super::pointadd_lilypad::INV_F0_LANE && t >= 2 && matches!(pairing, Some((_, true)))
}

fn sadd(
    b: &mut B,
    src: &[QubitId],
    tgt: &[QubitId],
    negs: &[QubitId],
    inv: bool,
    pool: &[QubitId],
    pairing: Option<(usize, bool)>,
    t: usize,
    role: AddRole,
) {
    // On the forced-add support N = G1 xor F1. Conjugation of the
    // high target gives an ordinary high addition with carry-in F1.
    // G'0=0 and G'1=1; the following Clifford map is reversible even
    // off support, while lending requires the stated odd/forced invariant.
    let low2 = c49_enabled(C49_LOW2) && role==AddRole::Value && t>1;
    let low_map = |b: &mut B| {
        b.x(tgt[0]); b.x(tgt[1]); b.cx(src[1],tgt[1]);
        for &n in negs { b.cx(n,tgt[1]); }
        if inv {b.x(tgt[1]);}
    };
    let high = if low2 { &tgt[2..] } else { tgt };
    if low2 { low_map(b); }
    let flip = |b: &mut B| {
        for &q in high {
            for &n in negs { b.cx(n, q); }
            if inv { b.x(q); }
        }
    };
    flip(b);
    if low2 {
        let f0a = f0_absent(pairing, t);
        let mut pl=pool.to_vec();
        for q in [src[0],tgt[0],tgt[1]] {
            if f0a && q == src[0] { continue; }
            assert!(!pl.contains(&q) && !negs.contains(&q)); pl.push(q);
        }
        if !f0a { b.x(src[0]); }
        b.x(tgt[1]);
        digit_add(b,&src[2..],high,Some(src[1]),&pl,pairing,t,AddRole::ValueHi2);
        b.x(tgt[1]);
        if !f0a { b.x(src[0]); }
    } else {digit_add(b,src,tgt,None,pool,pairing,t,role);}
    flip(b);
}

/// Initial state: X.v = 2x - p (x shifted up one lane by swaps, then the uncontrolled subtract of Y.v = p),
/// Y = (p | C_G = 2), X.c = 0. Recorded so the inverse walk can unplay it.
pub fn init_g(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr) {
    if k8_enabled() {
        // U13 K8: init keeps only the shift (X.v = 2x). The subtract, the p-load
        // and V = 1 move into tick 1 (k8_fused_tick1), where bb is still clean.
        for f in (0..256).rev() {
            b.swap(w.af(1, f), w.af(1, f + 1));
        }
        return;
    }
    let p = super::frogdrop_sched::p();
    for f in 0..256 {
        if p.bit(f) {
            b.x(w.bf(f));
        }
    }
    b.x(w.bsig(usize::from(!HALF_COFACTOR_G)));
    for f in (0..256).rev() {
        b.swap(w.af(1, f), w.af(1, f + 1));
    }
    let kv = sch.kv[1];
    let av: Vec<QubitId> = (0..kv).map(|f| w.af(1, f)).collect();
    let bv: Vec<QubitId> = (0..kv).map(|f| w.bf(f)).collect();
    let mut pl = sc.pool.clone();
    pl.extend(&sc.tmp);
    // 2x - p = ~(~X + Y) with Y = p; X lanes above 257 are 0 (sign extension of 2x >= 0 -> of 2x - p by the add)
    sadd(b, &bv, &av, &[], true, &pl, None, 0, AddRole::Value);
    // sign-extend X.v to its region (lanes kv..c are |0> before; the circuit keeps them sign copies)
    for f in kv..sch.c[1] {
        b.cx(w.af(1, kv - 1), w.af(1, f));
    }
}

/// U13 K8: init fused into tick 1. With G = 2x - p, F = p (p = 3 mod 4) and rho = 0,
/// tick 1 has e = x0 and X.v = G + (-1)^(1+e) F = 2x - 2p*!e. One constant add replaces
/// the init subtract and the tick-1 value add; the 291 bb lanes are its carry bank
/// because F = p and V = 1 are loaded only after it. Exact on all inputs.
const K8_FUSED_INIT: bool = true;

#[cfg(test)]
thread_local! {static O2_K8:std::cell::Cell<bool>=const{std::cell::Cell::new(K8_FUSED_INIT)};}
#[cfg(test)]
pub(crate) fn test_k8(v: bool) { O2_K8.with(|c| c.set(v)); }
pub(crate) fn k8_enabled() -> bool {
    #[cfg(test)] { return O2_K8.with(|c| c.get()); }
    #[cfg(not(test))] { K8_FUSED_INIT }
}

/// Tick-1 value block under K8: X.v[1..kv] -= p * !e (lane 0 stays 0 = bit 0 of 2p),
/// then load Y = (F = p | V = 1). Precondition: X.v = 2x (x < 2^256), e = x0, bb all |0>.
fn k8_fused_tick1(b: &mut B, w: &PWalk, sch: &PSched, e: QubitId) {
    let p = super::frogdrop_sched::p();
    let kv = sch.kv[1];
    let a: Vec<QubitId> = (1..kv).map(|f| w.af(1, f)).collect();
    let k: Vec<bool> = (0..a.len()).map(|i| p.bit(i)).collect();
    assert!(!w.bb.contains(&e) && !a.contains(&e));
    // a - K = ~(~a + K): ~a has lane 0 = !x0 = !e and lanes 256.. = 1.
    for &q in &a {
        b.x(q);
    }
    k8_add_kne(b, &a, e, &k, 256, &w.bb);
    for &q in &a {
        b.x(q);
    }
    for f in 0..256 {
        if p.bit(f) {
            b.x(w.bf(f));
        }
    }
    b.x(w.bsig(0));
}

#[derive(Clone, Copy)]
enum K8c {
    NotE,
    Lane(QubitId),
}

/// a += K * !e (mod 2^n) with classical K, as a recorded Gidney add (AndC carries, AndU
/// erase). Preconditions, exact at the K8 site: k[0] = 1 and lane a[0] holds !e (so c1 = !e
/// and s0 = 0); lanes a[m..] hold |1> and k[m..] = 0 (so c_i = c_m for i >= m).
/// Carries c_{i+1} = MAJ(a_i, k_i !e, c_i) cost one AND each once they leave the !e class.
pub(crate) fn k8_add_kne(b: &mut B, a: &[QubitId], e: QubitId, k: &[bool], m: usize, bank: &[QubitId]) {
    let n = a.len();
    assert!(k.len() == n && k[0] && m >= 2 && m <= n);
    assert!(k[m..].iter().all(|&x| !x));
    let mut cs: Vec<K8c> = vec![K8c::NotE]; // cs[j] = c_{j+1}
    let mut used = 0;
    for i in 1..m {
        let next = match (k[i], cs[i - 1]) {
            (true, K8c::NotE) => K8c::NotE,
            (false, K8c::NotE) => {
                let t = bank[used];
                used += 1;
                b.x(e);
                b.and_c(a[i], e, t);
                b.x(e);
                K8c::Lane(t)
            }
            (false, K8c::Lane(c)) => {
                let t = bank[used];
                used += 1;
                b.and_c(a[i], c, t);
                K8c::Lane(t)
            }
            (true, K8c::Lane(c)) => {
                let t = bank[used];
                used += 1;
                b.cx(c, a[i]);
                b.cx(c, e);
                b.x(e);
                b.and_c(a[i], e, t);
                b.x(e);
                b.cx(c, e);
                b.cx(c, t);
                K8c::Lane(t)
            }
        };
        cs.push(next);
    }
    // a[m..] = 1, k = 0: c_i = c_m and s_i = !c_m.
    let cm = cs[m - 1];
    for &q in &a[m..] {
        match cm {
            K8c::NotE => {
                b.cx(e, q);
                b.x(q);
            }
            K8c::Lane(c) => b.cx(c, q),
        }
    }
    for i in (1..m).rev() {
        match (k[i], cs[i - 1], cs[i]) {
            (true, K8c::NotE, _) => {}
            (false, K8c::NotE, K8c::Lane(t)) => {
                b.x(e);
                b.and_u(a[i], e, t);
                b.x(e);
                b.cx(e, a[i]);
                b.x(a[i]);
            }
            (false, K8c::Lane(c), K8c::Lane(t)) => {
                b.and_u(a[i], c, t);
                b.cx(c, a[i]);
            }
            (true, K8c::Lane(c), K8c::Lane(t)) => {
                b.cx(c, t);
                b.cx(c, e);
                b.x(e);
                b.and_u(a[i], e, t);
                b.x(e);
                b.cx(c, e);
                b.cx(e, a[i]);
                b.x(a[i]);
            }
            _ => unreachable!("K8 carry class"),
        }
    }
    // s0 = !e ^ !e ^ 0 = 0.
    b.cx(e, a[0]);
    b.x(a[0]);
}


/// hose847b G1: sigma = e & !(h4 & (h3 | h2)), both parities, Z-free. Every A state (h in -11..-1) has h4 = 1 and
/// h3 | h2 = 1; e = 1 in B-high only from h in 16..19 (c4 table), where h3 = h2 = 0. Z (b ^ L ^ m) is never read.
fn hose_sigma(b:&mut B,w:&PWalk,t:usize,e:QubitId,sg:QubitId) {
    let q=w.qfr(t); let (h2,h3,h4)=(w.h[2],w.h[3],w.h[4]);
    b.cx(e,sg); b.ccx(e,h4,sg);
    b.x(h3); b.x(h2);
    super::mask::mcx_dirty(b,&[e,h4,h3,h2],sg,&q[1..3]);
    b.x(h2); b.x(h3);
}
/// H5Q even-tick sigma. Q0 may contain a deferred marker only when h=0.
/// e & (!h4 | host) is independent of that marker; h4=1 distinguishes b.
fn h5q_sigma(b:&mut B,w:&PWalk,t:usize,e:QubitId,sg:QubitId) {
    let q=w.qfr(t); let h4=w.h[4];
    b.cx(e,sg); b.x(q[0]);
    super::mask::mcx_dirty(b,&[e,h4,q[0]],sg,&q[1..2]); b.x(q[0]);
}
/// Even update: complement leaves b=h4^h5 unchanged. Increment toggles b
/// only on c4 & !h4, so a pending marker at h=0 is never read or changed.
fn h5q_inc(b:&mut B,w:&PWalk,t:usize,tmp:&[QubitId]) {
    let q=w.qfr(t); let h=&w.h;
    let mut ctl:Vec<_>=h[..4].iter().map(|&x|(x,false)).collect(); ctl.push((h[4],true));
    let qd: Vec<QubitId> = if super::pointadd_lilypad::O1B_C { q[1..].iter().copied().filter(|x| !tmp.contains(x)).take(3).collect() } else { q[1..4].to_vec() };
    super::mask::mc_xor(b,&ctl,q[0],tmp,&qd);
    inc_bounded_h(b,h,tmp,t,&qd);
}
fn h5q_view(w:&PWalk,t:usize)->PWalk {
    let mut h=w.h.clone();h.push(w.qfr(t)[0]);
    PWalk{a:w.a.clone(),bb:w.bb.clone(),q:w.q.clone(),h,capq:w.capq,log:w.log.clone()}
}


/// Restore Q0 as a clean odd-tick carry owner without losing b or the oldest
/// digit. Q1 can be nonzero only at h=-1. Encode that one case in the unused
/// low-h code17 (bits1..3 cleared), retaining h0 and therefore rho unchanged.
/// b=0 has no ordinary h codes16..20; b=1 distinguishes positive16..31.
fn h5q_odd_loan(b:&mut B,w:&PWalk,t:usize,enter:bool) {
    let q=w.qfr(t);let h=&w.h;let g0=w.af(t,0);
    if enter { b.cx(h[4],q[0]); } // decoded h5 -> b
    if t>16 {
        if enter { for &x in &h[1..4] { b.cx(q[1],x); } }
        else { b.swap(q[0],q[1]); }
        if enter { b.x(g0); } // G0=1 before the odd+odd value add; zero after it.
        super::mask::mc_xor(b,&[(q[0],true),(h[4],false),(h[2],true),(h[3],true)],q[1],&[g0],&q[2..4]);
        if enter { b.x(g0); }
        if enter { b.swap(q[0],q[1]); }
        else { for &x in &h[1..4] { b.cx(q[1],x); } }
    }
    if !enter { b.cx(h[4],q[0]); } // b -> decoded h5, before sigma reads it.
}

/// Step of tick t up to the halve: e computed into `e` (|0> forward; Q's lane in the regenerating walk), sigma, adds.
pub fn step_core_g(
    b: &mut B,
    w: &PWalk,
    t: usize,
    sch: &PSched,
    sc: &PScr,
    rho: &ParityCtl,
    e: QubitId,
    extra: &[QubitId],
    pairing: Option<(usize, bool)>,
) {
    let (c, kv, kc) = (sch.c[t], sch.kv[t], sch.kc[t]);
    let sg = sc.sg;
    let h5 = *w.h.last().unwrap();
    let loan = delay_sigma();
    let h5q_borrow=t%2==1 && w.h.len()==6 && w.q.contains(&w.h[5]) && w.log.len()!=3;
    if h5q_borrow { assert!(loan); h5q_odd_loan(b,w,t,true); }
    // U13 K8: at t = 1, rho = 0 (h, log are |0>) and F1 = p1 = 1, so e = x0.
    let fused = t == 1 && k8_enabled();
    sec(b, "lilyg.ctl", |b| {
        b.cx(w.af(t, 1), e);
        if fused {
            assert!(!rho.flip);
        } else {
            b.cx(w.bf(1), e);
            b.x(e);
        }
        rho.xor_into(b, e);
        if !loan {
            if w.log.len()==3 { hose_sigma(b,w,t,e,sg); } else if w.h.len()==5 { h5q_sigma(b,w,t,e,sg); } else {
            b.x(h5);
            b.and_c(e, h5, sg);
            b.x(h5);
            }
        }
    });
    let mut pl = lsc(b, w, t, c, kv, kc);
    pl.extend(&sc.pool);
    pl.extend(&sc.tmp);
    pl.extend(extra);
    // Sigma is not read by either signed add or by LSC. Their control
    // inputs e and h[HB-1] are unchanged, so defer its AND until the carry
    // workspace is returned clean. In inverse replay the AND is erased
    // first, providing the same clean lane before either inverse add.
    if loan && sg != w.af(t, 0) {
        assert!(!pl.contains(&sg) && sg != e && sg != h5 && !rho.qs.contains(&sg));
        pl.push(sg);
    }
    // Before tick t, |h|<=t-1. Retain the minimal signed window and
    // its top sign owner; redundant high copies can be zeroed for p1.
    // No cap has touched log before t<=q. rho reads log0/log4 only.
    let mut early=Vec::new();
    let mut hn=2usize;
    while hn<w.h.len() && (1usize<<(hn-1))-1<t-1 {hn+=1;}
    if c49_enabled(C49_EARLY) {
        for &q in &w.h[hn.min(w.h.len()-1)..w.h.len()-1] { b.cx(w.h[hn-1],q); early.push(q); }
        if t<=w.capq && w.log.len()==8 {
            early.extend([w.log[1],w.log[2],w.log[3],w.log[5],w.log[6],w.log[7]]);
        } else if t<=w.capq && w.log.len()==7 {
            early.extend([w.log[1],w.log[2],w.log[3],w.log[5],w.log[6]]);
        } else if t<=w.capq && w.log.len()==6 {
            early.extend([w.log[1],w.log[2],w.log[3],w.log[5]]);
        } else if t<=w.capq && (w.log.len()==5 || w.log.len()==4) {
            early.extend([w.log[1],w.log[2],w.log[3]]);
        } else if t<=w.capq && w.log.len()==3 {
            early.extend([w.log[1],w.log[2]]);
        }
        for &q in &early { assert!(!pl.contains(&q) && !rho.qs.contains(&q) && q!=e && q!=h5); }
        pl.extend(&early);
    }
    let av: Vec<QubitId> = (0..kv).map(|f| w.af(t, f)).collect();
    let bv: Vec<QubitId> = (0..kv.min(c - ycut_at(t))).map(|f| w.bf(f)).collect();
    let sinv = !neg("flipsign") ^ rho.flip;
    let mut negs = vec![e];
    negs.extend(&rho.qs);
    // Stable low-cofactor parity is U0 xor V0=1. The preceding
    // tick's halve injects G'0=0 and V0 is1 before its role swap.
    // Neither cofactor is read by the value add; clean one affine owner.
    let four=t != 1 && c49_enabled(C49_LOW2) && !(matches!(pairing, Some((_, true))) && v0_virtual(t));
    let (u0,v0)=(w.asig(t,0),w.bsig(0));
    let mut vp=pl.clone();
    if four {
        assert!(HALF_COFACTOR_G, "C49 fourth loan requires half-cofactor parity");
        assert!(!vp.contains(&v0) && !negs.contains(&v0) && !av.contains(&v0) && !bv.contains(&v0));
        b.cx(u0,v0);b.x(v0);vp.push(v0);
    }
    if fused {
        // K8 owns tick 1: Y and its cofactor lenders are still clean until this block.
        sec(b, "lilyg.addv", |b| k8_fused_tick1(b, w, sch, e));
    } else {
        sec(b, "lilyg.addv", |b| sadd(b, &bv, &av, &negs, sinv, &vp, pairing, t, AddRole::Value));
    }
    if four {b.x(v0);b.cx(u0,v0);}
    // In the half-cofactor representation every physical cofactor lane is
    // live; in the legacy representation sig0 is the constant-zero lane.
    let c0 = usize::from(!HALF_COFACTOR_G);
    // Schlussgang: X's cofactor region is sch.w - c; on zero-slack frames (kc = Y's region) the source is one lane
    // shorter and sign-extends into Y's top lane.
    let ac: Vec<QubitId> = (c0..kc.min(sg_xreg(sch, t))).map(|s| w.asig(t, s)).collect();
    let bc: Vec<QubitId> = (c0..kc).map(|s| w.bsig(s)).collect();
    assert!(ac.len() == bc.len() || ac.len() + 1 == bc.len(), "Schlussgang cofactor add t{t}");
    sec(b, "lilyg.addc", |b| {
        if !low_loan_enabled() {
            sadd(b,&ac,&bc,&negs,sinv,&pl,pairing,t,AddRole::Cofactor);
            return;
        }
        // F remains odd: the role exchange omits lane zero. This block
        // touches only cofactors and e/rho, so the F LSB is an idle |1> owner.
        let donor=w.bf(0);
        assert!(f0_absent(pairing, t) || (!pl.contains(&donor) && !ac.contains(&donor) && !bc.contains(&donor)
            && !negs.contains(&donor)));
        // The preceding signed value add has two odd inputs, so its
        // target low lane is now |0>. It too is idle throughout this block.
        let zero=w.af(t,0);
        assert!(zero!=donor && !pl.contains(&zero) && !ac.contains(&zero)
            && !bc.contains(&zero) && !negs.contains(&zero));
        let third = c49_enabled(C49_THIRD);
        let one=w.af(t,1);
        let f0a = f0_absent(pairing, t);
        let mut cp=pl.clone();
        if !f0a { cp.push(donor); }
        let v1a = matches!(pairing, Some((_, true))) && v1_virtual(t);
        if !v1a { cp.push(zero); }
        let v0a = matches!(pairing, Some((_, true))) && v0_virtual(t) && !v1a;
        let mut bc_own = bc.clone();
        if third && !v0a && !v1a {
            assert!(!cp.contains(&one) && !ac.contains(&one) && !bc.contains(&one) && !negs.contains(&one));
            cp.push(one); b.x(one);
        }
        if v0a {
            // Lane LILY-A: V0 is not held. At a tick boundary V0 = !U0, so the G'1 lane (= 1 here) carries it through
            // the add: CX(U0) gives !U0; the add leaves lane 0 = V0 ^ U0 = 1 = G'1, so nothing to restore.
            assert!(third && HALF_COFACTOR_G && bc[0] == w.bsig(0) && ac[0] == w.asig(t, 0));
            assert!(!cp.contains(&one) && !ac.contains(&one) && !negs.contains(&one));
            b.cx(w.asig(t, 0), one);
            bc_own[0] = one;
        }
        if v1a {
            // Lane LILY-A: V0 and V1 are not held. Pre-add (G already updated, G' = 2 mod 4): V0 = !U0 goes onto the
            // zero lane (G'0 = 0); V1 = U1 ^ F1 ^ 1 ^ rho ^ U0 (e ^ rho) onto the one lane (G'1 = 1). After the add
            // V0' = 1 and V1' = U0 ^ F1 ^ 1 ^ rho, so both lanes return to G'0 = 0, G'1 = 1 by the same toggles.
            assert!(third && HALF_COFACTOR_G && bc[0] == w.bsig(0) && bc[1] == w.bsig(1) && ac[0] == w.asig(t, 0));
            assert!(!cp.contains(&one) && !cp.contains(&zero) && !negs.contains(&one) && !negs.contains(&zero));
            let (u0, u1, f1) = (w.asig(t, 0), w.asig(t, 1), w.bf(1));
            b.x(zero); b.cx(u0, zero);
            b.cx(u1, one); b.cx(f1, one); rho.xor_into(b, one);
            b.ccx(u0, e, one);
            for &r in &rho.qs { b.ccx(u0, r, one); }
            if rho.flip { b.cx(u0, one); }
            bc_own[0] = zero; bc_own[1] = one;
        }
        let v2a = v1a && v2_virtual(t);
        let cvars = |b_e: QubitId| [Cv::L(w.asig(t, 0)), Cv::L(w.asig(t, 1)), Cv::L(w.asig(t, 2)), Cv::L(w.af(t, 2)),
            Cv::L(w.bf(1)), Cv::L(w.yv(t, 2)), Cv::L(b_e), Cv::Rho];
        let cdirty: Vec<QubitId> = (120..128).map(|k| w.af(t, k)).collect();
        let mut shifted = false;
        let v3a = v2a && v3_virtual(t);
        let cvars16 = |b_e: QubitId| [Cv::L(w.asig(t, 0)), Cv::L(w.asig(t, 1)), Cv::L(w.asig(t, 2)), Cv::L(w.asig(t, 3)),
            Cv::L(w.af(t, 2)), Cv::L(w.xv(t, 3)), Cv::L(w.bf(1)), Cv::L(w.yv(t, 2)), Cv::L(w.yv(t, 3)), Cv::L(b_e), Cv::Rho];
        let need = if v3a { 2 } else { 1 };
        if v2a {
            if cp.len() >= need {
                // V2 (and V3) hosted on clean carry lanes for the add (pre-add chart in, post-add chart out).
                let host = cp.pop().unwrap();
                let host3 = if v3a { Some(cp.pop().unwrap()) } else { None };
                anf_spec_g(b, &cvars(e), v2_add_masks(false), rho, host, &cdirty, 0, crate::circuit::NO_BIT);
                bc_own[2] = host;
                let l9 = [w.asig(t, 0), w.asig(t, 1), w.asig(t, 2), w.asig(t, 3), w.af(t, 2), w.xv(t, 3), w.bf(1), w.yv(t, 2), w.yv(t, 3)];
                let v3k = cp.last().copied();
                let l9ok = |h3: QubitId, k: Option<QubitId>| -> bool {
                    let mut all: Vec<QubitId> = l9.to_vec(); all.extend([e, h3]); all.extend(k); all.extend(rho.qs.iter().copied());
                    !rho.qs.is_empty() && v3r_distinct(&all)
                };
                if let Some(h3) = host3 {
                    if V3R_STAGE >= 2 && l9ok(h3, v3k) {
                        v3r_pre(b, h3, v3k, l9, e, rho);
                    } else {
                        if std::env::var_os("FROGTAIL_CK").is_some() { eprintln!("V3R pre-add ANF fallback t{t}"); }
                        anf_spec_g(b, &cvars16(e), v3_add_masks(false), rho, h3, &cdirty, 0, crate::circuit::NO_BIT);
                    }
                    bc_own[3] = h3;
                }
                if !f0a { b.x(donor); }
                sadd(b, &ac, &bc_own, &negs, sinv, &cp, pairing, t, AddRole::Cofactor);
                if !f0a { b.x(donor); }
                anf_spec_g(b, &cvars(e), v2_add_masks(true), rho, host, &cdirty, 1, crate::circuit::NO_BIT);
                if let Some(h3) = host3 {
                    if V3R_STAGE >= 5 && l9ok(h3, None) {
                        v3r_post(b, h3, l9, rho);
                    } else {
                        anf_spec_g(b, &cvars16(e), v3_add_masks(true), rho, h3, &cdirty, 1, crate::circuit::NO_BIT);
                    }
                }
                shifted = true;
            } else {
                // No clean lane (even zero-slack ticks): V0..V2 stay virtual. The add runs on lanes 3.. with
                // carry-in c3 (charted onto the zero lane); the one lane becomes its carry lane; the forward add's
                // receipts at positions 1..3 are repaid on the charted carries, the rest shifted by 3.
                let (pr, _) = pairing.expect("inverse pairing");
                let key = super::chunked::PairKey { division: pr, tick: t, role: AddRole::Cofactor };
                let debts = if b.has_chunk_debts(key) { b.take_chunk_debts(key, kc, false, false) } else { vec![] };
                // return the V0/V1 hosts to G'0 = 0 / G'1 = 1, then make the one lane a clean carry lane
                let (u0, u1, f1) = (w.asig(t, 0), w.asig(t, 1), w.bf(1));
                b.cx(u0, zero); b.x(zero);
                b.cx(u1, one); b.cx(f1, one); rho.xor_into(b, one);
                b.ccx(u0, e, one);
                for &r in &rho.qs { b.ccx(u0, r, one); }
                if rho.flip { b.cx(u0, one); }
                b.x(one);
                let kk = if v3a { 4 } else { 3 };
                let cmasks = |p: usize| if kk == 3 { add_carry_masks(p) } else { add_carry_masks16(p) };
                let cv: Vec<Cv> = if kk == 3 { cvars(e).to_vec() } else { cvars16(e).to_vec() };
                let mut high = vec![];
                // tsave848 rank 3 (factored carry chart): kk = 3 charts c1..c3 on in-place lanes (t3_c3_block).
                let fcl = [w.asig(t, 0), w.asig(t, 1), w.asig(t, 2), w.af(t, 2), w.bf(1), w.yv(t, 2)];
                let fc = {
                    let mut all: Vec<QubitId> = fcl.to_vec();
                    all.extend([e, zero, one]);
                    all.extend(rho.qs.iter().copied());
                    kk == 3 && !rho.qs.is_empty() && all.iter().enumerate().all(|(i, q)| !all[..i].contains(q))
                };
                // v3r846 G4: kk = 4 factored carry chart on in-place lanes (zero = c4, one = c3 / clean around the add).
                let fcl4 = [w.asig(t, 0), w.asig(t, 1), w.asig(t, 2), w.asig(t, 3), w.af(t, 2), w.xv(t, 3), w.bf(1), w.yv(t, 2), w.yv(t, 3)];
                let fc4 = V3R_STAGE >= 4 && kk == 4 && !rho.qs.is_empty() && {
                    let mut all: Vec<QubitId> = fcl4.to_vec(); all.extend([e, zero, one]); all.extend(rho.qs.iter().copied());
                    v3r_distinct(&all)
                };
                if !fc && !fc4 && std::env::var_os("FROGTAIL_CK").is_some() { eprintln!("T3 c3 chart fallback t{t}"); }
                let mut low_debts: Vec<(usize, BitId)> = vec![];
                for d in debts {
                    if d.position <= kk {
                        if fc || fc4 { low_debts.push((d.position, d.bit)); continue; }
                        let cm = cmasks(d.position);
                        anf_spec_g(b, &cv, &cm, rho, crate::circuit::NO_QUBIT, &cdirty, 2, d.bit);
                    } else {
                        high.push(super::chunked::Debt { position: d.position - kk, bit: d.bit });
                    }
                }
                let ck = cmasks(kk);
                if fc { t3_c3_block(b, &fcl, e, rho, zero, one, false, &low_debts); }
                else if fc4 { v3r_c4_block(b, fcl4, e, rho, zero, one, false, &low_debts); }
                else { anf_spec_g(b, &cv, &ck, rho, zero, &cdirty, 0, crate::circuit::NO_BIT); }
                let (ah, th) = (&ac[kk..], &bc[kk..]);
                // Schlussgang: short X source on zero-slack frames: sign bit as a top-lane XOR, zero top source lane.
                let short = ah.len() + 1 == th.len();
                assert!(short || ah.len() == th.len());
                let mut ahz = ah.to_vec();
                if short { ahz.push(super::chunked::ZERO_TOP); }
                let flipt = |b: &mut B| { for &q in th { for &n in &negs { b.cx(n, q); } if sinv { b.x(q); } } };
                flipt(b);
                if short { b.cx(*ah.last().unwrap(), *th.last().unwrap()); }
                let mut hpool = vec![one];
                hpool.extend(cp.iter().copied());
                super::chunked::add_with_debts(b, &ahz, th, ONE, zero, &hpool, high);
                flipt(b);
                if fc { t3_c3_block(b, &fcl, e, rho, zero, one, true, &[]); }
                else if fc4 { v3r_c4_block(b, fcl4, e, rho, zero, one, true, &[]); }
                else { anf_spec_g(b, &cv, &ck, rho, zero, &cdirty, 1, crate::circuit::NO_BIT); }
                // leave the post-add hosted values (V0' = 1, V1' = U0 ^ F1 ^ 1 ^ rho) for the common restore below
                b.x(zero);
                b.x(one); b.cx(u0, one); b.cx(f1, one); rho.xor_into(b, one);
                shifted = true;
            }
        }
        if !shifted {
        if !f0a { b.x(donor); }
        sadd(b, &ac, &bc_own, &negs, sinv, &cp, pairing, t, AddRole::Cofactor);
        if !f0a { b.x(donor); }
        }
        if v1a {
            let (u0, f1) = (w.asig(t, 0), w.bf(1));
            b.x(zero);
            b.cx(u0, one); b.cx(f1, one); rho.xor_into(b, one);
        }
        if third && !v0a && !v1a {b.x(one);}
    });
    if c49_enabled(C49_EARLY) {
        for &q in &w.h[hn.min(w.h.len()-1)..w.h.len()-1] { b.cx(w.h[hn-1],q); }
    }
    lsc(b, w, t, c, kv, kc);
    if h5q_borrow { h5q_odd_loan(b,w,t,false); }
    if loan {
        sec(b, "lilyg.ctl", |b| {
            if w.log.len()==3 { hose_sigma(b,w,t,e,sg); } else if w.h.len()==5 { h5q_sigma(b,w,t,e,sg); } else {
            b.x(h5);
            b.and_c(e, h5, sg);
            b.x(h5);
            }
        });
    }
    #[cfg(test)]
    if std::env::var_os("LILYPAD_POOL_PROFILE").is_some() {
        eprintln!("POOL loan={loan} pair={pairing:?} tick={t} room={} value={kv} cofactor={} value_plan={:?} cofactor_plan={:?}",
            pl.len(), ac.len(), super::chunked::plan(kv, pl.len(), false),
            super::chunked::plan(ac.len(), pl.len(), false));
    }
}

/// U15 K9: the cofactor lane-0 role exchange is two CX. Before every swap
/// U0 = 0 (the halve moves the even value lane 0 of G +- F into U0) and V0 = 1
/// (U0 ^ V0 = 1 from init U = 0, V = 1; the add sets V0 ^= U0; the swap
/// permutes the pair). On that support cswap(s, U0, V0) = (s, !s) = CX(s,U0); CX(s,V0).
const K9_LANE0_CX: bool = true;

#[cfg(test)]
thread_local! {static O2_K9:std::cell::Cell<bool>=const{std::cell::Cell::new(K9_LANE0_CX)};}
#[cfg(test)]
pub(crate) fn test_k9(v: bool) { O2_K9.with(|c| c.set(v)); }
fn k9_enabled() -> bool {
    #[cfg(test)] { return O2_K9.with(|c| c.get()); }
    #[cfg(not(test))] { K9_LANE0_CX }
}

fn k9_lane0_swap(b: &mut B, sg: QubitId, u0: QubitId, v0: QubitId) {
    assert!(HALF_COFACTOR_G && sg != u0 && sg != v0 && u0 != v0);
    b.cx(sg, u0);
    b.cx(sg, v0);
}

/// patchF: h += 1 (uncontrolled, two's complement) on the six-lane h with two clean temps and no dirty lane: 5 Toffoli
/// (inc_unctl: 4 temps, 4 Toffoli). c2 is uncomputed once c3 is held, and recomputed for c3's uncompute; every AndU
/// target equals its AND at that point (py/inc2t_check.py, exhaustive 64/64).
fn inc_unctl_2t(b: &mut B, h: &[QubitId], tmp: &[QubitId]) {
    assert!(h.len() == 6 && tmp.len() == 2);
    let (t0, t1) = (tmp[0], tmp[1]);
    b.and_c(h[0], h[1], t0); // c2
    b.and_c(t0, h[2], t1); // c3
    b.and_u(h[0], h[1], t0);
    b.and_c(t1, h[3], t0); // c4
    b.ccx(t0, h[4], h[5]); // h5 ^= c5
    b.cx(t0, h[4]); // h4 ^= c4
    b.and_u(t1, h[3], t0);
    b.cx(t1, h[3]); // h3 ^= c3
    b.and_c(h[0], h[1], t0); // c2 again
    b.and_u(t0, h[2], t1);
    b.cx(t0, h[2]); // h2 ^= c2
    b.and_u(h[0], h[1], t0);
    b.cx(h[0], h[1]); // h1 ^= h0
    b.x(h[0]);
}

/// Exact early counter range: before the increment h is in [-t,t-1].
/// Upper lanes are sign copies. Return them as sign copies of the new h.
fn inc_bounded_h(b:&mut B,h:&[QubitId],tmp:&[QubitId],t:usize,dirty:&[QubitId]) {
    let mut n=2usize;
    while n<h.len() && (1usize<<(n-1))-1<t {n+=1;}
    for &q in &h[n..] {b.cx(h[n-1],q);}
    if n >= 5 && tmp.len() + 4 < n { inc_unctl_m(b,&h[..n],tmp,dirty); }
    else if n >= 4 && tmp.len() + 3 < n { inc_unctl_short2(b,&h[..n],tmp,dirty); }
    else if n >= 3 && tmp.len() + 2 < n { inc_unctl_short(b,&h[..n],tmp); } else { inc_unctl(b,&h[..n],tmp); }
    for &q in &h[n..] {b.cx(h[n-1],q);}
}

/// Ringli-Diät: commute the disappearing Y value bit through the role swap.
/// With sigma=1, old G fits the new short Y region, so its top residual is 0.
/// Exchange that residual with old F's before retiring Y's physical top lane.
/// The later unequal swap restores X's top from the saved residual and new sign.
/// This is the post-swap Y boundary fix, factored around the pre-swap eraser.
fn yv_boundary_residual(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sg: QubitId) {
    let c = sch.c[t + 1];
    if super::pointadd_lilypad::YV_CUT == 0 || t >= sch.s || sch.c[t] != c + 1 || sch.kv[t + 1] != c { return; }
    let (x, y) = (w.af(t + 1, c - 1), w.bf(c - 1));
    let (xs, ys) = (w.af(t + 1, c - 2), w.bf(c - 2));
    b.cx(xs, x); b.cx(ys, y);
    b.cswap(sg, x, y);
    b.cx(ys, y); b.cx(xs, x);
}

/// Halve of tick t (relabel + boundary fixes), the deferred-to-frame-t+1 cswap, rho/delta update, cap, sigma decode.
pub fn halve_g(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr) {
    halve_g_x(b, w, t, sch, sc, None)
}

/// patchF: halve_g; with `fd` (forward t = S-1 and S, two-temp view) the six-lane h increment is inc_unctl_2t and
/// the cap is cap_logic_fwd2 on the two temps plus dirty lanes `fd`.
pub fn halve_g_x(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr, fd: Option<&[QubitId]>) {
    sec(b, "lilyg.hv", |b| {
        if !neg("nofix") {
            sg_xfix(b, w, t, sch, sc.sg);
        }
        yv_boundary_residual(b, w, t, sch, sc.sg);
        fix_boundary(b, &|f| w.bf(f), sch.c[t] - ycut_at(t), sch.c[t + 1] - ycut_at(t + 1));
    });
    let (c, kv, kc) = (sch.c[t + 1], sch.kv[t + 1], sch.kc[t + 1]);
    let sg = sc.sg;
    let k9 = HALF_COFACTOR_G && k9_enabled();
    let v1s = sg == w.asig(t + 1, 0) && v1_virtual(t);
    sec(b, "lilyg.swap", |b| {
        lsc(b, w, t + 1, c, kv, kc);
        if v1s && v3_virtual(t) { v3_swap_u3(b, w, t, sg); }
        if v1s && v2_virtual(t) {
            if super::pointadd_lilypad::YV_CUT == 1 && t < sch.s && sch.c[t] == c + 1 && c == 3 && kv == c {
                b.ccx(sg, w.af(t + 1, 2), w.asig(t + 1, 2));
                b.ccx(sg, w.af(t + 1, 1), w.asig(t + 1, 2));
            }
            v2_swap_u2(b, w, t, sg);
        }
        if v1s { v1_swap_u1(b, w, t, sg); }
        let ky = kv.min(c - ycut_at(t + 1));
        // On swap support the incoming Y value (old X) fits ky. Preserve
        // X's top residual across the lower swap; the new top becomes Y's sign.
        if ky < kv { b.cx(w.af(t + 1, ky - 1), w.af(t + 1, ky)); }
        for f in 1..ky {
            b.cswap(sg, w.af(t + 1, f), w.bf(f));
        }
        if ky < kv { b.cx(w.af(t + 1, ky - 1), w.af(t + 1, ky)); }
        if k9 && sg == w.asig(t + 1, 0) {
            // Lane LILY-A: sigma is hosted in U0 (= 0 before the swap), so the lane-0 swap is V0 ^= sigma.
            if !v0_virtual(t) { b.cx(sg, w.bsig(0)); }
        } else if k9 {
            k9_lane0_swap(b, sg, w.asig(t + 1, 0), w.bsig(0));
        }
        let _ = kc;
        sg_cswap_cof(b, w, t, sch, sg, usize::from(!HALF_COFACTOR_G).max(usize::from(k9)),
            &|s| (v1s && s == 1) || (v1s && s == 2 && v2_virtual(t)) || (v1s && s == 3 && v3_virtual(t)));
        lsc(b, w, t + 1, c, kv, kc);
    });
    let v0=w.bsig(0);let vloan=sc.sp.contains(&v0);
    if vloan { b.x(v0); b.cx(sg,v0); }
    sec(b, "lilyg.hv", |b| {
        for &x in &w.h {
            b.cx(sg, x);
        }
        let mut htmp = sc.tmp.clone();
        // Inverse-only: the recorded digit lives in Q, so sc.e is clean.
        if sc.tmp.is_empty() && sc.e != super::lilypad::NO_E { htmp.push(sc.e); }
        htmp.extend(&sc.sp);
        let hd:Vec<_>=w.q.iter().copied().filter(|x|!w.h.contains(x)).take(3).collect();
        if fd.is_some() {
            // patchF: at t >= 32 inc_bounded_h is inc_unctl on all six lanes; same map on two temps.
            assert!(t + 1 >= sch.s && t >= 32 && w.h.len() == 6 && htmp.len() == 2 && w.q.is_empty(), "patchF late-tick increment");
            inc_unctl_2t(b, &w.h, &htmp);
        } else if w.h.len()==5 { h5q_inc(b,w,t,&htmp); } else { inc_bounded_h(b, &w.h, &htmp, t, &hd); }
    });
    if w.capq > 0 && t > w.capq && t < sch.s {
        sec(b, "lilyg.cap", |b| {
            if let Some(fd) = fd {
                assert!(w.h.len() == 6);
                super::lilypad::cap_logic_fwd2(b, w, sc, fd);
            } else if w.h.len()==5 {
                let host=w.qfr(t)[0]; b.cx(w.h[4],host);
                super::lilypad::h5q_cap(b,&h5q_view(w,t),sc);
                b.cx(w.h[4],host);
            } else { cap_logic(b,w,sc); }
        });
    }
    if vloan { b.cx(sg,v0); b.x(v0); }
    if sg != w.asig(t + 1, usize::from(!HALF_COFACTOR_G)) {
        b.cx(w.asig(t + 1, usize::from(!HALF_COFACTOR_G)), sg);
    }
}


/// tsave848 rank 4 (odd-tick Grenzgänger): halve_g for regenerating odd ticks 11 < t < S with the h/cap update ahead
/// of the role swap (as halve_g_pre_erase: the swap reads rho only under sigma, sigma (P ^ sigma ^ 1) = sigma P) and
/// the boundary sign copy left by fix_boundary cleared and lent to the h increment and the cap as one more clean lane.
/// The lane is restored before the swap and never enters rec_regen_g's scratch view.
pub fn halve_g_odd_gg(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr) {
    let c0 = sch.c[t];
    let c1 = sch.c[t + 1];
    assert!(c0 == c1 || c0 == c1 + 1);
    assert!(t % 2 == 1 && t > 11 && t < sch.s && l5_enabled() && HALF_COFACTOR_G);
    let (gg_src, gg_lane) = if c0 == c1 {
        assert!(c1 >= 3);
        (w.af(t + 1, c1 - 2), w.af(t + 1, c1 - 1))
    } else {
        let ycut = ycut_at(t);
        assert!(ycut == 1 && ycut_at(t + 1) == 1 && c1 > ycut);
        (w.bf(c0 - ycut), w.bf(c0 - ycut - 1))
    };
    assert!(gg_src != gg_lane && gg_lane != sc.sg && gg_lane != sc.e);
    assert!(!sc.tmp.contains(&gg_lane) && !sc.sp.contains(&gg_lane)
        && !sc.pool.contains(&gg_lane) && !sc.d.contains(&gg_lane)
        && !w.h.contains(&gg_lane) && (!w.q.contains(&gg_lane) || (super::pointadd_lilypad::O1B_C && t > super::pointadd_lilypad::O1B_LAST && w.q[..2].contains(&gg_lane)))
        && !w.log.contains(&gg_lane));
    assert!(!sc.sp.contains(&w.bsig(0)), "odd Grenzgänger: V0 is virtual at t >= 2");
    let mut gg_sp = sc.sp.clone();
    gg_sp.push(gg_lane);
    let gg_view = PScr { e: sc.e, sg: sc.sg, d: sc.d.clone(), tmp: sc.tmp.clone(), sp: gg_sp, pool: sc.pool.clone() };
    sec(b, "lilyg.hv", |b| {
        if !neg("nofix") {
            sg_xfix(b, w, t, sch, sc.sg);
        }
        yv_boundary_residual(b, w, t, sch, sc.sg);
        fix_boundary(b, &|f| w.bf(f), sch.c[t] - ycut_at(t), sch.c[t + 1] - ycut_at(t + 1));
        b.cx(gg_src, gg_lane);
        for &x in &w.h {
            b.cx(sc.sg, x);
        }
        let mut htmp = sc.tmp.clone();
        if sc.tmp.is_empty() && sc.e != super::lilypad::NO_E { htmp.push(sc.e); }
        htmp.extend(&gg_view.sp);
        let hd:Vec<_>=w.q.iter().copied().filter(|x|!w.h.contains(x)).take(3).collect();
        if w.h.len()==5 { h5q_inc(b,w,t,&htmp); } else { inc_bounded_h(b, &w.h, &htmp, t, &hd); }
    });
    if w.capq > 0 && t > w.capq && t < sch.s {
        sec(b, "lilyg.cap", |b| {
            if w.h.len()==5 {
                let host=w.qfr(t)[0]; b.cx(w.h[4],host);
                super::lilypad::h5q_cap(b,&h5q_view(w,t),&gg_view);
                b.cx(w.h[4],host);
            } else { cap_logic(b,w,&gg_view); }
        });
    }
    b.cx(gg_src, gg_lane);
    let (c, kv, kc) = (sch.c[t + 1], sch.kv[t + 1], sch.kc[t + 1]);
    let sg = sc.sg;
    let k9 = HALF_COFACTOR_G && k9_enabled();
    let v1s = sg == w.asig(t + 1, 0) && v1_virtual(t);
    sec(b, "lilyg.swap", |b| {
        lsc(b, w, t + 1, c, kv, kc);
        if v1s && v3_virtual(t) { v3_swap_u3(b, w, t, sg); }
        if v1s && v2_virtual(t) {
            if super::pointadd_lilypad::YV_CUT == 1 && t < sch.s && sch.c[t] == c + 1 && c == 3 && kv == c {
                b.ccx(sg, w.af(t + 1, 2), w.asig(t + 1, 2));
                b.ccx(sg, w.af(t + 1, 1), w.asig(t + 1, 2));
            }
            v2_swap_u2(b, w, t, sg);
        }
        if v1s { v1_swap_u1(b, w, t, sg); }
        let ky = kv.min(c - ycut_at(t + 1));
        // On swap support the incoming Y value (old X) fits ky. Preserve
        // X's top residual across the lower swap; the new top becomes Y's sign.
        if ky < kv { b.cx(w.af(t + 1, ky - 1), w.af(t + 1, ky)); }
        for f in 1..ky {
            b.cswap(sg, w.af(t + 1, f), w.bf(f));
        }
        if ky < kv { b.cx(w.af(t + 1, ky - 1), w.af(t + 1, ky)); }
        if k9 && sg == w.asig(t + 1, 0) {
            // Lane LILY-A: sigma is hosted in U0 (= 0 before the swap), so the lane-0 swap is V0 ^= sigma.
            if !v0_virtual(t) { b.cx(sg, w.bsig(0)); }
        } else if k9 {
            k9_lane0_swap(b, sg, w.asig(t + 1, 0), w.bsig(0));
        }
        let _ = kc;
        sg_cswap_cof(b, w, t, sch, sg, usize::from(!HALF_COFACTOR_G).max(usize::from(k9)),
            &|s| (v1s && s == 1) || (v1s && s == 2 && v2_virtual(t)) || (v1s && s == 3 && v3_virtual(t)));
        lsc(b, w, t + 1, c, kv, kc);
    });
    if sg != w.asig(t + 1, usize::from(!HALF_COFACTOR_G)) {
        b.cx(w.asig(t + 1, usize::from(!HALF_COFACTOR_G)), sg);
    }
}

/// L5 inverse-regeneration ordering. The h/cap update commutes ahead of the
/// role swap; the conversion-free 12-lane eraser runs while sigma and rho are
/// still in the pre-swap frame, then the role swap and rho toggle complete the
/// tick.
pub fn halve_g_pre_erase(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr) {
    // Grenzgänger: fix_boundary leaves exactly one adjacent sign copy.
    // Keep this loan local: rec_regen_g's scratch view MUST NOT contain it.
    // A same-width tick grows X's value boundary by one; a shrink tick
    // grows Y's cofactor boundary by one. Clear only after both fixes.
    let c0 = sch.c[t];
    let c1 = sch.c[t + 1];
    assert!(c0 == c1 || c0 == c1 + 1);
    // Schlussgang: no Grenzgänger loan at the endpoint tick S (X shrinks into the endpoint shift, Y keeps its width).
    let gg_on = t < sch.s;
    let (gg_src, gg_lane) = if !gg_on {
        (super::lilypad::NO_E, super::lilypad::NO_E)
    } else if c0 == c1 {
        assert!(c1 >= 3);
        (w.af(t + 1, c1 - 2), w.af(t + 1, c1 - 1))
    } else {
        // Ringli-Diät: Y's physical boundary is c - ycut (explicit frame cut).
        // yv_boundary_residual runs before the fix and this local clear.
        let ycut = ycut_at(t);
        assert!(ycut == 1 && ycut_at(t + 1) == 1 && c1 > ycut);
        (w.bf(c0 - ycut), w.bf(c0 - ycut - 1))
    };
    let gg_h = gg_on && t > 11;
    // Exactly the zero-slack, one-owner layout that otherwise uses eraser_tf (Y's cofactor region 288 - c).
    let gg_er = gg_on && sc.e == super::lilypad::NO_E && sc.tmp.is_empty()
        && sc.sp.len() == 1 && sch.kv[t + 1] == c1
        && sch.kc[t + 1] == sch.w + super::pointadd_lilypad::XC_CUT - c1;
    assert!(t % 2 == 0 && l5_enabled() && HALF_COFACTOR_G);
    if gg_on {
    assert!(gg_src != gg_lane && gg_lane != sc.sg && gg_lane != sc.e);
    assert!(!sc.tmp.contains(&gg_lane) && !sc.sp.contains(&gg_lane)
        && !sc.pool.contains(&gg_lane) && !sc.d.contains(&gg_lane)
        && !w.h.contains(&gg_lane) && !w.q.contains(&gg_lane)
        && !w.log.contains(&gg_lane));
    }
    let mut gg_hsp = sc.sp.clone();
    if gg_h { gg_hsp.push(gg_lane); }
    let gg_hview = PScr { e: sc.e, sg: sc.sg, d: sc.d.clone(),
        tmp: sc.tmp.clone(), sp: gg_hsp, pool: sc.pool.clone() };
    let v0=w.bsig(0);let vloan=sc.sp.contains(&v0);
    if vloan { b.x(v0); } // V0=1 before the low swap.
    sec(b, "lilyg.hv", |b| {
        if !neg("nofix") {
            sg_xfix(b, w, t, sch, sc.sg);
        }
        yv_boundary_residual(b, w, t, sch, sc.sg);
        fix_boundary(b, &|f| w.bf(f), sch.c[t] - ycut_at(t), sch.c[t + 1] - ycut_at(t + 1));
        if gg_h { b.cx(gg_src, gg_lane); }
        for &x in &w.h {
            b.cx(sc.sg, x);
        }
        let mut htmp = sc.tmp.clone();
        // Inverse-only: the recorded digit lives in Q, so sc.e is clean.
        if sc.tmp.is_empty() && sc.e != super::lilypad::NO_E { htmp.push(sc.e); }
        htmp.extend(&gg_hview.sp);
        let hd:Vec<_>=w.q.iter().copied().filter(|x|!w.h.contains(x)).take(3).collect();
        if w.h.len()==5 { h5q_inc(b,w,t,&htmp); } else { inc_bounded_h(b, &w.h, &htmp, t, &hd); }
    });
    if w.capq > 0 && t > w.capq && t < sch.s {
        sec(b, "lilyg.cap", |b| {
            if w.h.len()==5 {
                let host=w.qfr(t)[0]; b.cx(w.h[4],host);
                super::lilypad::h5q_cap(b,&h5q_view(w,t),&gg_hview);
                b.cx(w.h[4],host);
            } else { cap_logic(b,w,&gg_hview); }
        });
    }
    if gg_h { b.cx(gg_src, gg_lane); }
    // On the same support used by the existing terminal sigma decode,
    // the post-swap low cofactor equals sigma. Move only this swap ahead
    // of the pre-swap eraser; neither low cofactor is an eraser operand.
    if vloan { b.x(v0); }
    let loan = sc.tmp.is_empty();
    let low = w.asig(t + 1, 0);
    let u0_sigma = sc.sg == low;
    if loan && u0_sigma {
        // Lane LILY-A: sigma is hosted in U0 (= 0 before the swap): the low swap is V0 ^= sigma; no lane to clear.
        assert!(HALF_COFACTOR_G && l5_enabled() && k9_enabled());
        if !v0_virtual(t) { b.cx(low, w.bsig(0)); }
    } else if loan {
        assert!(HALF_COFACTOR_G && l5_enabled());
        if k9_enabled() {
            k9_lane0_swap(b, sc.sg, low, w.bsig(0));
        } else {
            b.cswap(sc.sg, low, w.bsig(0));
        }
        b.cx(low, sc.sg);
    }
    if vloan { b.x(v0); b.cx(low,v0); } // V0=1 xor sigma after low swap.
    // This is a nonowning view: never release it. The old sigma lane is
    // clean scratch; the low cofactor supplies the unchanged sigma value.
    let mut gg_esp = sc.sp.clone();
    if gg_er {
        b.cx(gg_src, gg_lane);
        gg_esp.push(gg_lane); // G0 + this lane selects hosted_e && sp2.
    }
    let view = PScr { e: sc.e, sg: if loan { low } else { sc.sg },
        d: sc.d.clone(), tmp: if loan && !u0_sigma { vec![sc.sg] } else { sc.tmp.clone() },
        sp: gg_esp, pool: sc.pool.clone() };
    // h=32 is low5=0, host=1, sigma=0. A pending marker at low5=0
    // has sigma=1; one at low5=1 has h0=1. Hide only the wrap from pq.
    let terminal_guard=|b:&mut B| {
        if w.h.len()==5 && t==sch.s && w.log.len()==3 {
            // hose847b G8: Z = b ^ L ^ m no longer separates h'=32 from h'=0; the X cofactor does (U1..U28 = 0).
            let q=w.qfr(t);
            let mut lits=vec![(w.h[0],true),(w.h[2],true),(w.h[3],true),(w.h[4],true),(view.sg,true)];
            lits.extend((1..=28).map(|s| (w.asig(t+1,s),true)));
            let mut dirty: Vec<QubitId> = q.to_vec();
            dirty.extend((100..140).map(|k| w.af(t+1,k)));
            let dirty: Vec<QubitId> = dirty.into_iter().filter(|x| *x!=w.h[1] && !lits.iter().any(|l| l.0==*x)).collect();
            super::mask::mc_xor(b,&lits,w.h[1],&[],&dirty);
        } else if w.h.len()==5 && t==sch.s {
            let q=w.qfr(t);
            super::mask::mc_xor(b,&[(q[0],false),(w.h[0],true),(view.sg,true)],w.h[1],&[],&q[1..2]);
        }
    };
    terminal_guard(b);
    let rho = rho_pre_swap(w, t, view.sg);
    let o1b_br = super::pointadd_lilypad::O1B_C && t == sch.s;
    if o1b_br { o1b_bracket(b, w, sch, view.sg); }
    eraser(
        b,
        w,
        t,
        sch,
        &view,
        usize::from(!HALF_COFACTOR_G),
        t == sch.s,
        Some(&rho),
        true,
        HALF_COFACTOR_G,
    );
    if o1b_br { o1b_bracket(b, w, sch, view.sg); }
    if gg_er { b.cx(gg_src, gg_lane); }
    terminal_guard(b);
    if vloan { b.cx(low,v0); b.x(v0); }
    if loan && !u0_sigma { b.cx(low, sc.sg); }
    let (c, kv, kc) = (sch.c[t + 1], sch.kv[t + 1], sch.kc[t + 1]);
    let sg = sc.sg;
    let v1s = u0_sigma && v1_virtual(t);
    sec(b, "lilyg.swap", |b| {
        lsc(b, w, t + 1, c, kv, kc);
        if v1s && v3_virtual(t) { v3_swap_u3(b, w, t, sg); }
        if v1s && v2_virtual(t) {
            if super::pointadd_lilypad::YV_CUT == 1 && t < sch.s && sch.c[t] == c + 1 && c == 3 && kv == c {
                b.ccx(sg, w.af(t + 1, 2), w.asig(t + 1, 2));
                b.ccx(sg, w.af(t + 1, 1), w.asig(t + 1, 2));
            }
            v2_swap_u2(b, w, t, sg);
        }
        if v1s { v1_swap_u1(b, w, t, sg); }
        let ky = kv.min(c - ycut_at(t + 1));
        // On swap support the incoming Y value (old X) fits ky. Preserve
        // X's top residual across the lower swap; the new top becomes Y's sign.
        if ky < kv { b.cx(w.af(t + 1, ky - 1), w.af(t + 1, ky)); }
        for f in 1..ky {
            b.cswap(sg, w.af(t + 1, f), w.bf(f));
        }
        if ky < kv { b.cx(w.af(t + 1, ky - 1), w.af(t + 1, ky)); }
        let _ = kc;
        sg_cswap_cof(b, w, t, sch, sg, usize::from(!HALF_COFACTOR_G).max(usize::from(loan)),
            &|s| (v1s && s == 1) || (v1s && s == 2 && v2_virtual(t)) || (v1s && s == 3 && v3_virtual(t)));
        lsc(b, w, t + 1, c, kv, kc);
    });
    if !u0_sigma {
        b.cx(w.asig(t + 1, usize::from(!HALF_COFACTOR_G)), sg);
    }
}

/// Window conversion for the eraser (frame t+1): Y.c[0..L] <- X.c[0..L] + (-1)^rho Y.c[0..L] (mod 2^L), so that
/// Y.c sig k+1 = bit k of d*c_g. Recording (unplay to restore).
fn conv_len(b: &mut B, w: &PWalk, t: usize, l: usize, rho: &ParityCtl, pool: &[QubitId]) -> Vec<G> {
    let start = usize::from(!HALF_COFACTOR_G);
    let xs: Vec<QubitId> = (start..l).map(|k| w.asig(t + 1, k)).collect();
    let ys: Vec<QubitId> = (start..l).map(|k| w.bsig(k)).collect();
    b.begin();
    // rho = 1: Y <- X - Y = ~(Y + ~X)
    let nr = neg("noconvrho");
    for &q in &xs {
        if !nr { rho.xor_into(b, q); }
    }
    ctrl_add_pool(b, &xs, &ys, ONE, pool);
    for &q in &ys {
        if !nr { rho.xor_into(b, q); }
    }
    for &q in &xs {
        if !nr { rho.xor_into(b, q); }
    }
    b.end()
}

fn conv(b: &mut B, w: &PWalk, t: usize, sch: &PSched, rho: &ParityCtl, pool: &[QubitId]) -> Vec<G> {
    let qb = w.q.len();
    let l = (qb.max(win_len(qb)) + 3).min(sch.w - sch.c[t + 1]);
    conv_len(b, w, t, l, rho, pool)
}

/// Record the public-end bridge from Lilypad-G's stored coordinates to the
/// shell interface. It leaves only key=[F<0], C_F, h and the cap log live:
/// C_G is converted to signed 2p and cleared, G and rho are cleared by their
/// audited invariants, and F is reduced to its sign key.
pub fn endpoint_adapter_g(
    b: &mut B,
    w: &PWalk,
    sch: &PSched,
    sc: &PScr,
) -> Vec<G> {
    let t = sch.s + 1;
    let value_len = sch.c[t];
    let cofactor_len = sch.w - value_len;
    if c1_enabled() {
        return c1_endpoint_adapter_g(b, w, sch);
    }
    let mut pool = sc.pool.clone();
    pool.extend(&sc.tmp);
    pool.extend(&sc.sp);
    pool.extend(&sc.d);
    pool.push(sc.e);
    pool.push(sc.sg);
    let rho = if neg("noadrho") {
        ParityCtl { qs: vec![], flip: false }
    } else {
        rho_stable(w, sch.s)
    };
    let cv = conv_len(b, w, sch.s, cofactor_len, &rho, &pool);
    let sign_f = w.bf(1);
    let endpoint_constant = if HALF_COFACTOR_G {
        super::frogdrop_sched::p()
    } else {
        super::frogdrop_sched::p() << 1usize
    };
    let endpoint_negative = (!endpoint_constant).wrapping_add(super::frogdrop_sched::N::from(1u64));

    b.begin();
    b.play(&cv, false);
    for s in usize::from(!HALF_COFACTOR_G)..cofactor_len {
        let pos = endpoint_constant.bit(s);
        let neg = endpoint_negative.bit(s);
        if pos {
            b.x(w.bsig(s));
        }
        if pos != neg {
            b.cx(sign_f, w.bsig(s));
        }
    }
    // G = -(-1)^rho F at a successful endpoint.
    b.x(w.af(t, 0));
    for f in 1..value_len {
        b.x(w.af(t, f));
        rho.xor_into(b, w.af(t, f));
        b.cx(sign_f, w.af(t, f));
    }
    // F is +/-1: retain its sign in lane 1 as the shell key.
    b.x(w.bf(0));
    for f in 2..value_len - ycut_at(t) {
        b.cx(sign_f, w.bf(f));
    }
    b.end()
}

/// U16 C1: the endpoint adapter with an out-of-place carry-to-sum regeneration of
/// V = C_G/2 instead of the in-place 287-lane conversion add plus pattern clear.
/// On the endpoint support (the relation the old pattern clear already assumes)
///   V = (-1)^rho (P(key) - U) mod 2^L,  P(key) = (-1)^key p,  i.e.  V = S ^ rho,
///   S = P + ~U + !rho,  P_0 = 1,  P_i = p_i ^ key (i >= 1).
/// `c1_regen_v` writes V from clean lanes (each V lane holds a carry until the next carry
/// is formed, then becomes its sum bit). The adapter plays it inverted: every carry is
/// erased by AndU (0 T). The inverse adapter replays it forward: L - 1 AndC.
const C1_SUM_ERASE_ADAPTER: bool = true;

#[cfg(test)]
thread_local! {static O2_C1:std::cell::Cell<bool>=const{std::cell::Cell::new(C1_SUM_ERASE_ADAPTER)};}
#[cfg(test)]
pub(crate) fn test_c1(v: bool) { O2_C1.with(|c| c.set(v)); }
fn c1_enabled() -> bool {
    #[cfg(test)] { return O2_C1.with(|c| c.get()); }
    #[cfg(not(test))] { C1_SUM_ERASE_ADAPTER }
}

/// V (clean on entry) := S ^ rho, S = P + ~U + !rho (mod 2^L), P_0 = 1, P_i = p_i ^ key.
/// `key` and the U lanes are borrowed as CX-trick operands and restored.
pub(crate) fn c1_regen_v(b: &mut B, us: &[QubitId], vs: &[QubitId], key: QubitId, p: &[bool], rho: &ParityCtl) {
    let l = vs.len();
    assert!(l >= 2 && us.len() == l && p.len() == l && p[0]);
    assert!(!us.contains(&key) && !vs.contains(&key) && us.iter().all(|q| !vs.contains(q)));
    assert!(rho.qs.iter().all(|q| *q != key && !us.contains(q) && !vs.contains(q)));
    // c0 = !rho
    rho.xor_into(b, vs[0]);
    b.x(vs[0]);
    for i in 0..l - 1 {
        let (u, c, nx) = (us[i], vs[i], vs[i + 1]);
        // u <- (!u ^ c) = a_i ^ c_i
        b.cx(c, u);
        b.x(u);
        if i == 0 {
            // b_0 = 1: (b_0 ^ c_0) = !c_0, held in c's own lane while it is flipped.
            b.x(c);
            b.and_c(u, c, nx);
            b.x(c);
        } else {
            // b_i ^ c_i = key ^ p_i ^ c_i, held in the key lane.
            b.cx(c, key);
            if p[i] {
                b.x(key);
            }
            b.and_c(u, key, nx);
            if p[i] {
                b.x(key);
            }
            b.cx(c, key);
        }
        b.cx(c, nx); // c_{i+1} = c_i ^ (a_i ^ c_i)(b_i ^ c_i) = MAJ(a_i, b_i, c_i)
        b.x(u);
        b.cx(c, u);
        c1_sum(b, i, u, c, key, p[i]);
    }
    let i = l - 1;
    c1_sum(b, i, us[i], vs[i], key, p[i]);
    for &v in vs {
        rho.xor_into(b, v);
    }
}

/// lane c (holding c_i) <- s_i = !u ^ P_i ^ c_i.
fn c1_sum(b: &mut B, i: usize, u: QubitId, c: QubitId, key: QubitId, p: bool) {
    b.cx(u, c);
    if i == 0 {
        // !u ^ 1 ^ c = u ^ c
        return;
    }
    b.cx(key, c);
    if !p {
        b.x(c);
    }
}

fn c1_endpoint_adapter_g(b: &mut B, w: &PWalk, sch: &PSched) -> Vec<G> {
    assert!(HALF_COFACTOR_G);
    let t = sch.s + 1;
    let value_len = sch.c[t];
    let cofactor_len = sch.w - value_len;
    let rho = if neg("noadrho") {
        ParityCtl { qs: vec![], flip: false }
    } else {
        rho_stable(w, sch.s)
    };
    let sign_f = w.bf(1);
    let p = super::frogdrop_sched::p();
    let us: Vec<QubitId> = (0..cofactor_len).map(|s| w.asig(t, s)).collect();
    let vs: Vec<QubitId> = (0..cofactor_len).map(|s| w.bsig(s)).collect();
    let pb: Vec<bool> = (0..cofactor_len).map(|s| p.bit(s)).collect();
    b.begin();
    c1_regen_v(b, &us, &vs, sign_f, &pb, &rho);
    let vc = b.end();
    b.begin();
    b.play(&vc, true);
    // G = -(-1)^rho F at a successful endpoint (unchanged).
    b.x(w.af(t, 0));
    for f in 1..value_len {
        b.x(w.af(t, f));
        rho.xor_into(b, w.af(t, f));
        b.cx(sign_f, w.af(t, f));
    }
    // F is +/-1: retain its sign in lane 1 as the shell key (unchanged).
    b.x(w.bf(0));
    for f in 2..value_len - ycut_at(t) {
        b.cx(sign_f, w.bf(f));
    }
    b.end()
}

pub struct GScr;

/// Forward walk: init, ticks 1..=S, e X-measured each tick. Returns the measurement bits (index t).
pub fn walk_forward_g(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr, _g: &GScr, division: Option<usize>) -> Vec<BitId> {
    walk_forward_g_x(b, w, sch, sc, _g, division, None).0
}

/// patchF: walk_forward_g; with `fd` (dirty lanes of an idle external register) ticks S-1 and S run on a non-owning
/// scratch view with tmp = sc.tmp[..2], so from the start of tick S-1 on no op names sc.tmp[2..]. Returns the
/// measurement bits and the op index where tick S-1 starts (usize::MAX without `fd`). With `fd` None the emission is
/// walk_forward_g's.
pub fn walk_forward_g_x(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr, _g: &GScr, division: Option<usize>, fd: Option<&[QubitId]>) -> (Vec<BitId>, usize) {
    init_g(b, w, sch, sc);
    let m = b.fresh_bits(sch.s + 1);
    let mut s0 = usize::MAX;
    let view = fd.map(|_| {
        assert!(sc.tmp.len() == 4 && sc.sp.is_empty() && sc.d.is_empty() && w.q.is_empty(), "patchF forward scratch shape");
        PScr { e: sc.e, sg: sc.sg, d: sc.d.clone(), tmp: sc.tmp[..2].to_vec(), sp: sc.sp.clone(), pool: sc.pool.clone() }
    });
    for t in 1..=sch.s {
        let rho = rho_stable(w, t - 1);
        let lent = fd.is_some() && t + 1 >= sch.s;
        if fd.is_some() && t + 1 == sch.s {
            s0 = b.ops.len();
        }
        let sct = if lent { view.as_ref().unwrap() } else { sc };
        step_core_g(b, w, t, sch, sct, &rho, sct.e, &[], division.map(|d| (d, false)));
        halve_g_x(b, w, t, sch, sct, if lent { fd } else { None });
        b.hmr_to(sct.e, m[t]);
    }
    (m, s0)
}

/// Regenerating tick t as two recordings: (step core, halve + marker clear / converted eraser).
pub fn rec_regen_g(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr, _g: &GScr, division: Option<usize>) -> (Vec<G>, Vec<G>) {
    // Lane LILY-A: without a sigma lane, tick t hosts sigma in af(t, 0): the value add's low target lane, |0> after
    // both signed adds, and U0 = asig(t + 1, 0) of the next frame, where the role swap leaves sigma anyway.
    let sc_own;
    let sc = if sc.sg == super::lilypad::NO_SG {
        sc_own = PScr { e: sc.e, sg: w.af(t, 0), d: sc.d.clone(), tmp: sc.tmp.clone(), sp: sc.sp.clone(), pool: sc.pool.clone() };
        &sc_own
    } else {
        sc
    };
    let qe = w.qfr(t)[w.q.len() - 1];
    let mut extra = if sc.e == super::lilypad::NO_E { vec![] } else { vec![sc.e] };
    extra.extend(&sc.d);
    extra.extend(&sc.sp);
    // O6 QLEND-odd: at odd t, Q frame 0 is qfr(t+1)[QB-1], the lane that p1 of tick t+1 writes its
    // digit into. On the success support it is |0> from p1(t) entry through p3(t) (where it is only a
    // restored borrow or a clean AND lane), so it joins the carry pool of both signed adds.
    if t % 2 == 1 && super::lilypad::o6_enabled(1) && w.log.len()!=3 {
        let qb = w.q.len();
        let q0 = w.qfr(t)[0];
        assert!(qb >= 2 && q0 == w.qfr(t + 1)[qb - 1] && q0 != qe && q0 != sc.sg);
        assert!(!extra.contains(&q0) && !sc.pool.contains(&q0) && !sc.tmp.contains(&q0));
        extra.push(q0);
    }
    let h5q = w.h.len()==5;
    let odd_view;
    let w = if h5q && t%2==1 { odd_view=h5q_view(w,t); &odd_view } else { w };
    b.begin();
    if h5q && t%2==1 { b.cx(w.h[4],w.h[5]); }
    let rho_before = rho_stable(w, t - 1);
    step_core_g(b, w, t, sch, sc, &rho_before, qe, &extra, division.map(|d| (d, true)));
    let p1 = b.end();
    // Y's fixed value lane zero is the odd F LSB. Source additions restore
    // it, value swaps start at lane one, and all cofactor windows exclude it.
    // Loan |1> as a fourth clean normalizer lane only for the complete p3;
    // the owning scratch contains only the three separately allocated lanes.
    let width_g0 = sc.sp.len() <= 2;
    let width_v0 = sc.sp.len() <= 1;
    let g0 = w.af(t+1,0);
    let v0 = w.bsig(0);
    let f0_held = super::pointadd_lilypad::INV_F0_LANE || t == 1;
    let odd_lsb_loan = sc.sp.len() <= 3;
    let donor = w.bf(0);
    let mut sp = sc.sp.clone();
    if odd_lsb_loan {
        assert!(sc.tmp.is_empty() && l5_enabled() && HALF_COFACTOR_G);
        assert!(![sc.e,sc.sg].contains(&donor));
        assert!(!sc.d.contains(&donor) && !sc.tmp.contains(&donor));
        assert!(!sc.pool.contains(&donor) && !sp.contains(&donor));
        assert!((!super::pointadd_lilypad::INV_F0_LANE || !w.q.contains(&donor)) && (!f0_held || !w.h.contains(&donor)) && !w.log.contains(&donor));
        assert!(super::pointadd_lilypad::INV_V0_LANE || t == 1 || !sp.contains(&v0));
        assert!(!w.a.contains(&donor) && donor != w.bsig(0));
        assert!(sch.c[t+1]>=2 && sch.kv[t+1]>=2 && sch.kc[t+1]>=2);
        if f0_held { sp.push(donor); }
        if width_g0 { assert!(!sp.contains(&g0)); sp.push(g0); }
        if width_v0 && !v0_virtual(t) { assert!(!sp.contains(&v0)); sp.push(v0); }
        assert!((3..=4).contains(&sp.len()) || (!f0_held && sp.len() == 2) || (!f0_held && v0_virtual(t) && sp.len() == 1));
        #[cfg(test)]
        if std::env::var_os("LILYPAD_NORMALIZER_AUDIT").is_some() {
            eprintln!("NORMALIZER_LOAN tick={t} donor={} xlow={} ylow={} owned_sp={:?} mapped_sp={:?} division={:?}",
                donor.0,w.asig(t+1,0).0,w.bsig(0).0,sc.sp,sp,division);
        }
    }
    let view=PScr {e:sc.e,sg:sc.sg,d:sc.d.clone(),tmp:sc.tmp.clone(),sp,pool:sc.pool.clone()};
    let sc=&view;
    b.begin();
    if odd_lsb_loan && f0_held { b.x(donor); }
    if width_g0 { b.x(g0); }
    if t % 2 == 0 && l5_enabled() {
        halve_g_pre_erase(b, w, t, sch, sc);
        if odd_lsb_loan && f0_held { b.x(donor); }
    if width_g0 { b.x(g0); }
        if h5q { let q=w.qfr(t); if super::pointadd_lilypad::O1B_C && t==sch.s { } else if t==sch.s || w.log.len()==3 { b.swap(q[0],q[1]); } else { b.cswap(w.h[4],q[0],q[1]); } }
        let p3 = b.end();
        return (p1, p3);
    }
    if !h5q && t%2==1 && super::lilypad::c50_enabled(16) {
        b.begin();halve_g(b,w,t,sch,sc);let hv=b.end();
        let fused=super::lilypad::inc_mclear_fused(b,w,t,sc,&hv,HALF_COFACTOR_G);
        b.play(&fused,false);
    }else if h5q && t%2==1 && t>11 && t<sch.s {halve_g_odd_gg(b, w, t, sch, sc);}else{halve_g(b, w, t, sch, sc);}
    if t % 2 == 1 {
        if h5q {
            let q=w.qfr(t);
            let mut lits:Vec<_>=w.h[..5].iter().map(|&x|(x,true)).collect();
            lits.push((w.asig(t+1,0),false));
            // V0 is restored to 1 XOR sigma by halve_g, unlike the other p3 loans.
            let v0=w.bsig(0);let vloan=sc.sp.contains(&v0);
            if vloan { assert_eq!(sc.sg,w.asig(t+1,0)); b.x(v0); b.cx(sc.sg,v0); }
            super::mask::mc_xor(b,&lits,q[12],&sc.sp,&q[1..6]);
            if vloan { b.cx(sc.sg,v0); b.x(v0); }
        } else if !super::lilypad::c50_enabled(16) {mclear(b, w, t, sc, HALF_COFACTOR_G);}
    } else {
        let mut cp: Vec<QubitId> = sc.pool.clone();
        cp.extend(&sc.tmp);
        cp.extend(&sc.sp);
        cp.push(sc.e);
        if l2_enabled() {
            let rho = rho_stable(w, t);
            eraser(
                b,
                w,
                t,
                sch,
                sc,
                usize::from(!HALF_COFACTOR_G),
                t == sch.s,
                Some(&rho),
                false,
                HALF_COFACTOR_G,
            );
        } else {
            let rho = rho_stable(w, t);
            let cv = conv(b, w, t, sch, &rho, &cp);
            sec(b, "er.conv", |b| b.play(&cv, false));
            eraser(b, w, t, sch, sc, 1, t == sch.s, None, false, false);
            sec(b, "er.conv", |b| b.play(&cv, true));
        }
    }
    let hose_odd = h5q && t%2==1 && w.log.len()==3;
    if hose_odd {
        // hose847b G6: re-encode Z = b ^ L, then (Z, q1) = (b ^ L, m) -> (0, b ^ L ^ m). q0 holds m after the two
        // CNOTs; m = [phys h = 0][U0..U10 = 0] (the deferred 12-digit word), erased with the clean G0 loan.
        let q=w.qfr(t);
        b.cx(w.h[4],w.h[5]);
        b.cx(q[0],q[1]); b.cx(q[1],q[0]);
        if t >= 23 && t < sch.s {
            assert!(width_g0 && sc.sp.contains(&g0));
            let mut lits: Vec<(QubitId,bool)> = w.h[..5].iter().map(|&x| (x,true)).collect();
            lits.extend((0..11).map(|s| (w.asig(t+1,s),true)));
            let mut dirty: Vec<QubitId> = q[2..].to_vec();
            dirty.extend((100..120).map(|k| w.af(t+1,k)));
            let dirty: Vec<QubitId> = dirty.into_iter().filter(|x| *x!=q[0] && *x!=g0 && !lits.iter().any(|l| l.0==*x)).collect();
            super::mask::mc_xor(b,&lits,q[0],&[g0],&dirty);
        }
    }
    if odd_lsb_loan && f0_held { b.x(donor); }
    if width_g0 { b.x(g0); }
    if h5q && !hose_odd {
        let q=w.qfr(t);
        if t%2==1 { b.cx(w.h[4],w.h[5]); }
        if super::pointadd_lilypad::O1B_C && t==sch.s { } else if t==sch.s || w.log.len()==3 { b.swap(q[0],q[1]); } else { b.cswap(w.h[4],q[0],q[1]); }
    }
    let p3 = b.end();
    (p1, p3)
}

/// frame846 O1b: X.v / Y.v extension at frame O1B_LAST + 1: E_X = sign copy of X's value lane c' - 1, E_Y = sign copy of
/// Y's value lane c' - 2 (production view `wp`; exact on the O1V success support). Self-inverse.
fn o1b_extend(b: &mut B, wp: &PWalk, sch: &PSched) {
    let fr = super::pointadd_lilypad::O1B_LAST + 1;
    let cc = sched_g_cut_ref().c[fr];
    assert_eq!(cc + 1, sch.c[fr]);
    b.cx(wp.af(fr, cc - 1), wp.af(fr, cc));
    b.cx(wp.bf(cc - 2), wp.bf(cc - 1));
}

/// frame846 O1b: forward walk with ticks 1..=O1B_LAST on the cut rings `wc` (cut schedule) and the rest on `wp`.
pub fn walk_forward_g_o1b(b: &mut B, wc: &PWalk, wp: &PWalk, sch: &PSched, sc: &PScr, _g: &GScr, division: Option<usize>, fd: Option<&[QubitId]>) -> Vec<BitId> {
    let last = super::pointadd_lilypad::O1B_LAST;
    let sc_cut = sched_g_cut();
    assert!(fd.is_none() || (last + 2 == sch.s && sc.tmp.len() == 4), "O1b gate C: patchF view covers ticks S-1, S");
    let view = fd.map(|_| PScr { e: sc.e, sg: sc.sg, d: sc.d.clone(), tmp: sc.tmp[..2].to_vec(), sp: sc.sp.clone(), pool: sc.pool.clone() });
    o1b_set_cut(true);
    init_g(b, wc, &sc_cut, sc);
    let m = b.fresh_bits(sch.s + 1);
    for t in 1..=sch.s {
        if t == last + 1 { o1b_set_cut(false); o1b_extend(b, wp, sch); }
        let (w, s) = if t <= last { (wc, &sc_cut) } else { (wp, sch) };
        let lent = fd.is_some() && t > last;
        let sct = if lent { view.as_ref().unwrap() } else { sc };
        let rho = rho_stable(w, t - 1);
        step_core_g(b, w, t, s, sct, &rho, sct.e, &[], division.map(|d| (d, false)));
        halve_g_x(b, w, t, s, sct, if lent { fd } else { None });
        b.hmr_to(sct.e, m[t]);
    }
    o1b_set_cut(false);
    m
}

/// frame846 O1b: inverse of walk_forward_g_o1b.
pub fn walk_inverse_g_o1b(b: &mut B, wc: &PWalk, wp: &PWalk, sch: &PSched, sc: &PScr, g: &GScr, m: &[BitId], division: Option<usize>) {
    let last = super::pointadd_lilypad::O1B_LAST;
    let sc_cut = sched_g_cut();
    SEC_INV.with(|c| c.set(true));
    o1b_set_cut(false);
    for t in (1..=sch.s).rev() {
        let (w, s) = if t <= last { (wc, &sc_cut) } else { (wp, sch) };
        if t == 2 && !super::pointadd_lilypad::INV_V3_LANE {
            assert!(w.q[8] == w.bsig(3));
            v3_chart_xor(b, w, 3, &rho_stable(w, 2), w.bsig(3));
        }
        if t == 1 && !super::pointadd_lilypad::INV_V2_LANE {
            assert!(w.q[9] == w.bsig(2));
            v2_chart_xor(b, w, 2, &rho_stable(w, 1), w.bsig(2));
        }
        if t == 1 && !super::pointadd_lilypad::INV_V1_LANE {
            assert!(w.q[10] == w.bsig(1));
            v1_chart_xor(b, w, 2, &rho_stable(w, 1), w.bsig(1));
        }
        if t == 1 && !super::pointadd_lilypad::INV_V0_LANE {
            assert!(w.q[11] == w.bsig(0));
            b.cx(w.asig(2, 0), w.bsig(0));
            b.x(w.bsig(0));
        }
        if t == 1 && !super::pointadd_lilypad::INV_F0_LANE {
            assert!(w.q[12] == w.bf(0));
            b.x(w.bf(0));
        }
        let (p1, p3) = rec_regen_g(b, w, t, s, sc, g, division);
        b.play(&p3, true);
        if !neg("noz") {
            b.z_if(w.qfr(t)[w.q.len() - 1], m[t]);
        }
        b.play(&p1, true);
        if t == last + 1 { o1b_extend(b, wp, sch); o1b_set_cut(true); }
    }
    b.begin();
    init_g(b, wc, &sc_cut, sc);
    let ir = b.end();
    b.play(&ir, true);
    o1b_set_cut(false);
    SEC_INV.with(|c| c.set(false));
}

/// frame846 O1b gate C: at the pre-swap eraser of tick S (frame S+1) the extension lanes are functions of the
/// endpoint state (C1 adapter support, py/bracket_check.py): E_X = X.v lane 1 = Y1 ^ 1 ^ R and E_Y = Y.c lane 284 =
/// F(X.c[283], X.c[284], Y.c[283], Y1, R, sigma) (degree 2, 13 monomials), R = rho_stable(w, S). Self-inverse: called
/// before the eraser (clears E_X, E_Y so they act as the empty Q slots 0/1) and after it (restores them).
fn o1b_bracket(b: &mut B, w: &PWalk, sch: &PSched, sg: QubitId) {
    let tn = sch.s + 1;
    let (ex, ey) = (w.q[0], w.q[1]);
    let cl = sch.w - sch.c[tn];
    assert!(cl == 285 && ex == w.af(tn, 1) && ey == w.bsig(cl - 1) && sch.c[tn] == 2, "O1b bracket frame");
    let rho = rho_stable(w, sch.s);
    let vars = [Cv::L(w.asig(tn, cl - 2)), Cv::L(w.asig(tn, cl - 1)), Cv::L(w.bsig(cl - 2)), Cv::L(w.bf(1)), Cv::Rho, Cv::L(sg)];
    static M: std::sync::OnceLock<Vec<usize>> = std::sync::OnceLock::new();
    let masks = M.get_or_init(|| anf_masks(6, &|a| {
        let bit = |i: usize| (a >> i) & 1;
        let (xa, xb, y, y1, r, s) = (bit(0), bit(1), bit(2), bit(3), bit(4), bit(5));
        let key = y1 ^ (s & (1 ^ r));
        let aa = (1 ^ xa) ^ (r & s);
        let yp = y ^ (r & (1 ^ s));
        let c = yp ^ key ^ aa;
        let m = (key & aa) | (key & c) | (aa & c);
        key ^ (1 ^ xb) ^ r ^ m == 1
    }));
    let used: Vec<QubitId> = vars.iter().filter_map(|v| if let Cv::L(q) = v { Some(*q) } else { None }).chain(rho.qs.iter().copied()).collect();
    let dirty: Vec<QubitId> = (100..140).map(|k| w.af(tn, k)).filter(|q| !used.contains(q) && *q != ey && *q != ex).collect();
    anf_xor(b, &vars, masks, &rho, ey, &dirty);
    b.cx(w.bf(1), ex);
    b.x(ex);
    rho.xor_into(b, ex);
}

/// Inverse of walk_forward_g (Q clean in w.q; clean again afterwards).
pub fn walk_inverse_g(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr, g: &GScr, m: &[BitId], division: Option<usize>) {
    SEC_INV.with(|c| c.set(true));
    for t in (1..=sch.s).rev() {
        if t == 2 && !super::pointadd_lilypad::INV_V3_LANE {
            // Lane LILY-A: Q lane 8 becomes V3 again for ticks 2 and 1 (post-tick-2 state, frame 3).
            assert!(w.q[8] == w.bsig(3));
            v3_chart_xor(b, w, 3, &rho_stable(w, 2), w.bsig(3));
        }
        if t == 1 && !super::pointadd_lilypad::INV_V2_LANE {
            // Lane LILY-A: Q lane 9 becomes V2 again for tick 1 (post-tick-1 state, frame 2).
            assert!(w.q[9] == w.bsig(2));
            v2_chart_xor(b, w, 2, &rho_stable(w, 1), w.bsig(2));
        }
        if t == 1 && !super::pointadd_lilypad::INV_V1_LANE {
            // Lane LILY-A: Q lane 10 becomes V1 again for tick 1 (post-tick-1 state, frame 2).
            assert!(w.q[10] == w.bsig(1));
            v1_chart_xor(b, w, 2, &rho_stable(w, 1), w.bsig(1));
        }
        if t == 1 && !super::pointadd_lilypad::INV_V0_LANE {
            // Lane LILY-A: Q lane 11 becomes V0 = !U0 again for tick 1.
            assert!(w.q[11] == w.bsig(0));
            b.cx(w.asig(2, 0), w.bsig(0));
            b.x(w.bsig(0));
        }
        if t == 1 && !super::pointadd_lilypad::INV_F0_LANE {
            // Lane LILY-A: tick 1 (the fused K8 step) reloads F = p: Q lane 12 becomes F0 = 1 again.
            assert!(w.q[12] == w.bf(0));
            b.x(w.bf(0));
        }
        let (p1, p3) = rec_regen_g(b, w, t, sch, sc, g, division);
        b.play(&p3, true);
        if !neg("noz") {
            b.z_if(w.qfr(t)[w.q.len() - 1], m[t]);
        }
        b.play(&p1, true);
    }
    b.begin();
    init_g(b, w, sch, sc);
    let ir = b.end();
    b.play(&ir, true);
    SEC_INV.with(|c| c.set(false));
}

#[cfg(test)]
mod c49_exact_tests {
    use super::*;
    use crate::{circuit::analyze_ops,sim::Simulator};
    use sha3::digest::XofReader;
    struct Fixed(u8);
    impl XofReader for Fixed {fn read(&mut self,out:&mut[u8]){out.fill(self.0);}}
    fn put(sim:&mut Simulator<Fixed>,qs:&[QubitId],lane:usize,v:u64) {
        for(i,q)in qs.iter().enumerate(){if v>>i&1!=0{sim.qubits[q.0 as usize]|=1<<lane;}}
    }
    fn get(sim:&Simulator<Fixed>,qs:&[QubitId],lane:usize)->u64 {
        qs.iter().enumerate().map(|(i,q)|((sim.qubits[q.0 as usize]>>lane)&1)<<i).sum()
    }
    #[test]
    fn c49_lowbits_exhaustive() {
        let mut checked=0;
        for n in 3..=7 {for room in 1..=8 {
            let mut b=B::new();let a=b.alloc_n(n);let t=b.alloc_n(n);let sg=b.alloc();let pool=b.alloc_n(room);
            b.begin();sadd(&mut b,&a,&t,&[sg],false,&pool,None,1,AddRole::Value);let r=b.end();
            b.play(&r,false);let split=b.ops.len();b.play(&r,true);
            let(nq,nb,_,_)=analyze_ops(b.ops.iter());let mask=(1u64<<n)-1;
            let cases:Vec<_>=(1..1u64<<n).step_by(2).flat_map(|a|(1..1u64<<n).step_by(2).map(move|t|(a,t))).collect();
            for fb in [0u8,255,170,85] {for ib in [0u8,255,170,85] {for batch in cases.chunks(64) {
                let mut tape=Fixed(fb);let mut sim=Simulator::new((nq as usize).max(b.width() as usize),nb as usize,&mut tape);
                for(i,&(av,tv))in batch.iter().enumerate(){put(&mut sim,&a,i,av);put(&mut sim,&t,i,tv);
                    if (av^tv)&2!=0{sim.qubits[sg.0 as usize]|=1<<i;}}
                let init=sim.qubits.clone();sim.apply_iter(b.ops[..split].iter());
                for(i,&(av,tv))in batch.iter().enumerate(){let want=if(av^tv)&2!=0{tv.wrapping_sub(av)}else{tv+av};
                    assert_eq!(get(&sim,&t,i),want&mask);assert_eq!(get(&sim,&a,i),av);}
                for q in &pool{assert_eq!(sim.qubits[q.0 as usize],0);}
                sim.xof.0=ib;sim.apply_iter(b.ops[split..].iter());assert_eq!(sim.qubits,init);
                assert_eq!(sim.phase,0,"low2 phase n{n} room{room} HMR{fb}/{ib}");checked+=batch.len();
            }}}
        }}
        eprintln!("C49_LOWBITS_EXHAUSTIVE {checked} lanes");
    }
}
