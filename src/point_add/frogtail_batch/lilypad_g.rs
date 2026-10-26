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
    if w.log.len() >= 8 {
        qs.extend([w.log[0], w.log[4]]);
    }
    ParityCtl { qs, flip: completed_ticks & 1 == 1 }
}

fn rho_pre_swap(w: &PWalk, t: usize, sigma: QubitId) -> ParityCtl {
    let mut rho = rho_stable(w, t);
    rho.qs.push(sigma);
    rho
}

pub fn sched_g() -> PSched {
    let mut sched = PSched::from_text(LILYPAD_G_SCHED);
    if HALF_COFACTOR_G {
        sched.w -= 1;
        for t in 1..=sched.s + 1 {
            sched.kc[t] -= 1;
        }
    }
    sched
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
        Cv::L(w.af(fr, 1)), Cv::L(w.af(fr, 2)), Cv::L(w.af(fr, 3)), Cv::L(w.bf(1)), Cv::L(w.bf(2)), Cv::L(w.bf(3)), Cv::Rho];
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
    let mut vars = vec![Cv::L(w.asig(fr, 1)), Cv::L(w.asig(fr, 2)), Cv::L(w.asig(fr, 3)), Cv::L(w.af(fr, 1)), Cv::L(w.af(fr, 2)),
        Cv::L(w.af(fr, 3)), Cv::L(w.bf(1)), Cv::L(w.bf(2)), Cv::L(w.bf(3)), Cv::Rho];
    vars.push(Cv::L(sg));
    let sgm: Vec<usize> = masks.iter().map(|&m| m | (1 << 10)).collect();
    let dirty: Vec<QubitId> = (120..130).map(|k| w.af(fr, k)).collect();
    anf_xor(b, &vars, &sgm, &rp, u3, &dirty);
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
    let vars = [Cv::L(w.asig(fr, 0)), Cv::L(w.asig(fr, 1)), Cv::L(w.asig(fr, 2)), Cv::L(w.af(fr, 1)), Cv::L(w.af(fr, 2)),
        Cv::L(w.bf(1)), Cv::L(w.bf(2)), Cv::Rho];
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
    // rho' = 1 ^ P: one more flip of the stable parity
    let rp = ParityCtl { qs: p.qs.clone(), flip: !p.flip };
    // U2 ^= sg & D2: every monomial gains the control sg
    let u2 = w.asig(fr, 2);
    let vars = [Cv::L(w.asig(fr, 1)), Cv::L(w.asig(fr, 2)), Cv::L(w.af(fr, 1)), Cv::L(w.af(fr, 2)), Cv::L(w.bf(1)), Cv::L(w.bf(2)), Cv::Rho];
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
    let h5 = w.h[HB - 1];
    let loan = delay_sigma();
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
            b.x(h5);
            b.and_c(e, h5, sg);
            b.x(h5);
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
    while hn<HB && (1usize<<(hn-1))-1<t-1 {hn+=1;}
    if c49_enabled(C49_EARLY) {
        for &q in &w.h[hn.min(HB-1)..HB-1] { b.cx(w.h[hn-1],q); early.push(q); }
        if t<=w.capq && w.log.len()==8 {
            early.extend([w.log[1],w.log[2],w.log[3],w.log[5],w.log[6],w.log[7]]);
        }
        for &q in &early { assert!(!pl.contains(&q) && !rho.qs.contains(&q) && q!=e && q!=h5); }
        pl.extend(&early);
    }
    let av: Vec<QubitId> = (0..kv).map(|f| w.af(t, f)).collect();
    let bv: Vec<QubitId> = (0..kv).map(|f| w.bf(f)).collect();
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
    let ac: Vec<QubitId> = (c0..kc).map(|s| w.asig(t, s)).collect();
    let bc: Vec<QubitId> = (c0..kc).map(|s| w.bsig(s)).collect();
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
            Cv::L(w.bf(1)), Cv::L(w.bf(2)), Cv::L(b_e), Cv::Rho];
        let cdirty: Vec<QubitId> = (120..128).map(|k| w.af(t, k)).collect();
        let mut shifted = false;
        let v3a = v2a && v3_virtual(t);
        let cvars16 = |b_e: QubitId| [Cv::L(w.asig(t, 0)), Cv::L(w.asig(t, 1)), Cv::L(w.asig(t, 2)), Cv::L(w.asig(t, 3)),
            Cv::L(w.af(t, 2)), Cv::L(w.af(t, 3)), Cv::L(w.bf(1)), Cv::L(w.bf(2)), Cv::L(w.bf(3)), Cv::L(b_e), Cv::Rho];
        let need = if v3a { 2 } else { 1 };
        if v2a {
            if cp.len() >= need {
                // V2 (and V3) hosted on clean carry lanes for the add (pre-add chart in, post-add chart out).
                let host = cp.pop().unwrap();
                let host3 = if v3a { Some(cp.pop().unwrap()) } else { None };
                anf_xor(b, &cvars(e), v2_add_masks(false), rho, host, &cdirty);
                bc_own[2] = host;
                if let Some(h3) = host3 {
                    anf_xor(b, &cvars16(e), v3_add_masks(false), rho, h3, &cdirty);
                    bc_own[3] = h3;
                }
                if !f0a { b.x(donor); }
                sadd(b, &ac, &bc_own, &negs, sinv, &cp, pairing, t, AddRole::Cofactor);
                if !f0a { b.x(donor); }
                anf_xor(b, &cvars(e), v2_add_masks(true), rho, host, &cdirty);
                if let Some(h3) = host3 {
                    anf_xor(b, &cvars16(e), v3_add_masks(true), rho, h3, &cdirty);
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
                for d in debts {
                    if d.position <= kk {
                        let cm = cmasks(d.position);
                        anf_xor(b, &cv, &cm, rho, one, &cdirty);
                        b.z_if(one, d.bit);
                        anf_xor(b, &cv, &cm, rho, one, &cdirty);
                    } else {
                        high.push(super::chunked::Debt { position: d.position - kk, bit: d.bit });
                    }
                }
                let ck = cmasks(kk);
                anf_xor(b, &cv, &ck, rho, zero, &cdirty);
                let (ah, th) = (&ac[kk..], &bc[kk..]);
                let flipt = |b: &mut B| { for &q in th { for &n in &negs { b.cx(n, q); } if sinv { b.x(q); } } };
                flipt(b);
                let mut hpool = vec![one];
                hpool.extend(cp.iter().copied());
                super::chunked::add_with_debts(b, ah, th, ONE, zero, &hpool, high);
                flipt(b);
                anf_xor(b, &cv, &ck, rho, zero, &cdirty);
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
        for &q in &w.h[hn.min(HB-1)..HB-1] { b.cx(w.h[hn-1],q); }
    }
    lsc(b, w, t, c, kv, kc);
    if loan {
        sec(b, "lilyg.ctl", |b| {
            b.x(h5);
            b.and_c(e, h5, sg);
            b.x(h5);
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

/// Halve of tick t (relabel + boundary fixes), the deferred-to-frame-t+1 cswap, rho/delta update, cap, sigma decode.
pub fn halve_g(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr) {
    sec(b, "lilyg.hv", |b| {
        if !neg("nofix") {
            fix_boundary(b, &|f| w.af(t + 1, f), sch.c[t] - 1, sch.c[t + 1]);
        }
        fix_boundary(b, &|f| w.bf(f), sch.c[t], sch.c[t + 1]);
    });
    let (c, kv, kc) = (sch.c[t + 1], sch.kv[t + 1], sch.kc[t + 1]);
    let sg = sc.sg;
    let k9 = HALF_COFACTOR_G && k9_enabled();
    let v1s = sg == w.asig(t + 1, 0) && v1_virtual(t);
    sec(b, "lilyg.swap", |b| {
        lsc(b, w, t + 1, c, kv, kc);
        if v1s && v3_virtual(t) { v3_swap_u3(b, w, t, sg); }
        if v1s && v2_virtual(t) { v2_swap_u2(b, w, t, sg); }
        if v1s { v1_swap_u1(b, w, t, sg); }
        for f in 1..kv {
            b.cswap(sg, w.af(t + 1, f), w.bf(f));
        }
        if k9 && sg == w.asig(t + 1, 0) {
            // Lane LILY-A: sigma is hosted in U0 (= 0 before the swap), so the lane-0 swap is V0 ^= sigma.
            if !v0_virtual(t) { b.cx(sg, w.bsig(0)); }
        } else if k9 {
            k9_lane0_swap(b, sg, w.asig(t + 1, 0), w.bsig(0));
        }
        for s in usize::from(!HALF_COFACTOR_G).max(usize::from(k9))..kc {
            if v1s && s == 1 { continue; }
            if v1s && s == 2 && v2_virtual(t) { continue; }
            if v1s && s == 3 && v3_virtual(t) { continue; }
            b.cswap(sg, w.asig(t + 1, s), w.bsig(s));
        }
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
        inc_bounded_h(b, &w.h, &htmp, t, &w.q[..w.q.len().min(3)]);
    });
    if w.capq > 0 && t > w.capq {
        sec(b, "lilyg.cap", |b| cap_logic(b, w, sc));
    }
    if vloan { b.cx(sg,v0); b.x(v0); }
    if sg != w.asig(t + 1, usize::from(!HALF_COFACTOR_G)) {
        b.cx(w.asig(t + 1, usize::from(!HALF_COFACTOR_G)), sg);
    }
}

/// L5 inverse-regeneration ordering. The h/cap update commutes ahead of the
/// role swap; the conversion-free 12-lane eraser runs while sigma and rho are
/// still in the pre-swap frame, then the role swap and rho toggle complete the
/// tick.
pub fn halve_g_pre_erase(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr) {
    let v0=w.bsig(0);let vloan=sc.sp.contains(&v0);
    if vloan { b.x(v0); } // V0=1 before the low swap.
    sec(b, "lilyg.hv", |b| {
        if !neg("nofix") {
            fix_boundary(b, &|f| w.af(t + 1, f), sch.c[t] - 1, sch.c[t + 1]);
        }
        fix_boundary(b, &|f| w.bf(f), sch.c[t], sch.c[t + 1]);
        for &x in &w.h {
            b.cx(sc.sg, x);
        }
        let mut htmp = sc.tmp.clone();
        // Inverse-only: the recorded digit lives in Q, so sc.e is clean.
        if sc.tmp.is_empty() && sc.e != super::lilypad::NO_E { htmp.push(sc.e); }
        htmp.extend(&sc.sp);
        inc_bounded_h(b, &w.h, &htmp, t, &w.q[..w.q.len().min(3)]);
    });
    if w.capq > 0 && t > w.capq {
        sec(b, "lilyg.cap", |b| cap_logic(b, w, sc));
    }
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
    let view = PScr { e: sc.e, sg: if loan { low } else { sc.sg },
        d: sc.d.clone(), tmp: if loan && !u0_sigma { vec![sc.sg] } else { sc.tmp.clone() },
        sp: sc.sp.clone(), pool: sc.pool.clone() };
    let rho = rho_pre_swap(w, t, view.sg);
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
    if vloan { b.cx(low,v0); b.x(v0); }
    if loan && !u0_sigma { b.cx(low, sc.sg); }
    let (c, kv, kc) = (sch.c[t + 1], sch.kv[t + 1], sch.kc[t + 1]);
    let sg = sc.sg;
    let v1s = u0_sigma && v1_virtual(t);
    sec(b, "lilyg.swap", |b| {
        lsc(b, w, t + 1, c, kv, kc);
        if v1s && v3_virtual(t) { v3_swap_u3(b, w, t, sg); }
        if v1s && v2_virtual(t) { v2_swap_u2(b, w, t, sg); }
        if v1s { v1_swap_u1(b, w, t, sg); }
        for f in 1..kv {
            b.cswap(sg, w.af(t + 1, f), w.bf(f));
        }
        for s in usize::from(!HALF_COFACTOR_G).max(usize::from(loan))..kc {
            if v1s && s == 1 { continue; }
            if v1s && s == 2 && v2_virtual(t) { continue; }
            if v1s && s == 3 && v3_virtual(t) { continue; }
            b.cswap(sg, w.asig(t + 1, s), w.bsig(s));
        }
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
    for f in 2..value_len {
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
    for f in 2..value_len {
        b.cx(sign_f, w.bf(f));
    }
    b.end()
}

pub struct GScr;

/// Forward walk: init, ticks 1..=S, e X-measured each tick. Returns the measurement bits (index t).
pub fn walk_forward_g(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr, _g: &GScr, division: Option<usize>) -> Vec<BitId> {
    init_g(b, w, sch, sc);
    let m = b.fresh_bits(sch.s + 1);
    for t in 1..=sch.s {
        let rho = rho_stable(w, t - 1);
        step_core_g(b, w, t, sch, sc, &rho, sc.e, &[], division.map(|d| (d, false)));
        halve_g(b, w, t, sch, sc);
        b.hmr_to(sc.e, m[t]);
    }
    m
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
    if t % 2 == 1 && super::lilypad::o6_enabled(1) {
        let qb = w.q.len();
        let q0 = w.qfr(t)[0];
        assert!(qb >= 2 && q0 == w.qfr(t + 1)[qb - 1] && q0 != qe && q0 != sc.sg);
        assert!(!extra.contains(&q0) && !sc.pool.contains(&q0) && !sc.tmp.contains(&q0));
        extra.push(q0);
    }
    b.begin();
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
        assert!((!super::pointadd_lilypad::INV_F0_LANE || !w.q.contains(&donor)) && !w.h.contains(&donor) && !w.log.contains(&donor));
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
        let p3 = b.end();
        return (p1, p3);
    }
    if t%2==1 && super::lilypad::c50_enabled(16) {
        b.begin();halve_g(b,w,t,sch,sc);let hv=b.end();
        let fused=super::lilypad::inc_mclear_fused(b,w,t,sc,&hv,HALF_COFACTOR_G);
        b.play(&fused,false);
    }else{halve_g(b, w, t, sch, sc);}
    if t % 2 == 1 {
        if !super::lilypad::c50_enabled(16) {mclear(b, w, t, sc, HALF_COFACTOR_G);}
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
    if odd_lsb_loan && f0_held { b.x(donor); }
    if width_g0 { b.x(g0); }
    let p3 = b.end();
    (p1, p3)
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
