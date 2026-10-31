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
pub const RLEN_S: usize = if super::LILYPAD_G && super::lilypad_g::HALF_COFACTOR_G { if WCUT == 0 { 287 } else if WTAIL { 288 - WCUT } else { 287 - WCUT } } else { 288 };
/// Lane LILY-R: lanes cut from each walk ring (W = 291 - WCUT), with gnuchev's 856 schedule transform.
pub const WCUT: usize = 3;
/// Lane LILY-R: with the cut, move one value lane to the cofactor from tick 450 (gnuchev's 856 transform).
pub const WTAIL: bool = true;
/// Lane LILY-R: the LILY-A width dial measured in the uncut geometry (one ring lane = two qubits).
/// Lane LILY-R: cap-log lanes (8 in the 867 tree; 7 = the 856 tree's compressed second slot).
pub const LOGN: usize = 4;
pub const YV_CUT: usize = 1;
/// Schlussgang: X ring one lane shorter (cofactor side on frames 1..S; the endpoint shift gives it back at S+1).
pub const XC_CUT: usize = 1;
/// hose847b (HOSE847): the inverse walk hosts log[3] in Q frame 0; the forward walk keeps LOGN lanes.
pub const HOSE: usize = 1;
/// frame846 O1b (gate B): rule-v ring cut on ticks <= O1B_LAST, two extension lanes from frame O1B_LAST + 1.
pub const O1B: bool = true;
pub const O1B_LAST: usize = 530;
/// frame846 route B: second value-side cut on both rings on ticks <= O1B2_LAST (0 = off).
pub const O1B2_LAST: usize = 480;
/// frame846 route B: V5 is paged only on inverse ticks > V5_WIN (0 = the parent: ticks >= 5).
pub const V5_WIN: usize = 480;
/// cut1233 (route B): the idle E2 lane(s) on even ticks <= O1B2_LAST join the inverse eraser's pool (a0, multiply
/// pool, normalizer and flag temps, mask pool). Exact; off = unchanged emission.
pub const RB_ERPOOL: bool = true;
/// frame846 route B: the idle E2 lanes on ticks <= O1B2_LAST join the signed adds' carry pool.
pub const RB_POOL: bool = true;
/// frame846 O1b keep ranges (inclusive frames): c unchanged, the cofactor side carries the cut there.
pub const O1B_KEEP: &[(usize, usize)] = &[(1, 350)];
/// frame846 O1b gate C: width 844 (E_X/E_Y = forward sc.tmp[2..4] on ticks <= O1B_LAST, inverse Q slots 0/1 there).
pub const O1B_C: bool = true;
/// patchF (rl-c9): from the start of the forward walk's tick S-1 through sc.release, sc.tmp[2..4] stay idle: ticks
/// S-1 and S run on tmp[0..2] (two-temp carry pools, inc_unctl_2t, cap_logic_fwd2 with dirty lanes from the external
/// register), the HOSE G9 junction on tmp[0..2] + e + sg. Off = byte-identical emission.
pub const PATCHF_LAST2: bool = true;
const DIAL: u64 = PEAK0 + 2 * WCUT as u64 + (8 - LOGN) as u64 + 1 + YV_CUT as u64 + XC_CUT as u64 + HOSE as u64 + 2 * O1B_C as u64;
// Schlussgang keeps the 849 dial: V3 must stay held (INV_V3_LANE), everything below it unchanged.
// v3r846: PEAK0 846 releases V3 (INV_V3_LANE false below 861).
// v2r845: PEAK0 845 (V4 paged in the inverse walk, sigma hosted forward).
// retake852: PEAK0 842 (V5 paged in the inverse walk, FWD_NT 3).
const _: () = assert!(DIAL == 858);
/// Lane LILY-ABER: terminal h range cut (W288 + tail only, below the 865 dial).
pub const TERMH: bool = WTAIL && DIAL <= 864;
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
    if super::lilypad_g::HALF_COFACTOR_G { if O1B_C { 842 } else { 845 } } else { 890 }
} else {
    892
};

/// Lane LILY-A: the inverse walk owns a sigma lane only at the parent width; below it sigma is hosted in U0.
pub const INV_SG_LANE: bool = DIAL >= 867;
/// Lane LILY-A: the inverse walk owns an e lane only down to 866; below it the eraser flag is hosted per tick.
pub const INV_E_LANE: bool = DIAL >= 866;
/// Lane LILY-A: below 865 the inverse walk releases F0 (Y.v lane 0, |1> on every shot) for ticks S..2.
pub const INV_F0_LANE: bool = DIAL >= 865;
/// Lane LILY-A: below 864 the inverse walk also releases V0 (Y.c lane 0, = !U0 at every tick boundary) for ticks S..2.
pub const INV_V0_LANE: bool = DIAL >= 864;
/// Lane LILY-A: below 863 the inverse walk also releases V1 (Y.c lane 1) for ticks S..2: at a tick boundary
/// V1 = U1 ^ U0 (G1 ^ F1 ^ 1) ^ F1 ^ 1 ^ rho (page relation mod 4).
pub const INV_V1_LANE: bool = DIAL >= 863;
/// Lane LILY-A: below 862 the inverse walk also releases V2 (Y.c lane 2) for ticks S..2 (page relation mod 8).
pub const INV_V2_LANE: bool = DIAL >= 862;
/// Lane LILY-A: below 861 the inverse walk also releases V3 (Y.c lane 3) for ticks S..3 (page relation mod 16).
pub const INV_V3_LANE: bool = DIAL >= 861;
/// v2r845: below 860 the inverse walk also releases V4 (Y.c lane 4) for ticks S..4 (page relation mod 32).
pub const INV_V4_LANE: bool = DIAL >= 860;
/// retake852 V5P: the inverse walk also releases V5 (Y.c lane 5) for ticks S..5 (page relation mod 64).
pub const INV_V5_LANE: bool = DIAL >= 859;
/// retake852 V5P: request the inverse walk one lane below the shell peak.
pub const V5_INV_LOWER: bool = false;
/// Lane LILY-A: forward-walk temporaries: one fewer per qubit below 862 (the forward fixed set was 862).
pub const FWD_NT: usize = 3; // frame846 Melchstüeli II: 3 -> 2 (o1b_m2_patch).
/// frame846: no cap on ticks t >= S - CAP_TAIL (forward and inverse; exact on the TERMH support, see o1b_m2_patch.py).
pub const CAP_TAIL: usize = 10;
// retake852: 4 -> 3 at 842 (fwd3_patch).
/// retake852: request the forward walk one lane below the shell peak (prices the 842 forward inside 843).
pub const FWD_LOWER: bool = false;
// v3r846: forward room is 0 at 847 -> 4 temps at 846 (inc_unctl on 6-lane h needs 4).
#[allow(dead_code)]
const FWD_NT_847: usize = 5; // H5Q + hose847b: forward room is 0 at 848, so one fewer temp at 847.

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
    /// frame846 O1b: cut rings (X 286, Y 286) and the extension lanes [E_X, E_Y].
    o1b: Option<(Vec<QubitId>, Vec<QubitId>, [QubitId; 2])>,
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
        log: b.alloc_n(LOGN),
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
    Div { w, sch, key, inv, parked_a, parked_b, m, division, g_adapter: None, o1b: None }
}

fn div_forward_g(b: &mut B, xq: &[QubitId], _dirty: &[QubitId]) -> Div {
    if PATCHF_LAST2 {
        assert!(_dirty.len() >= 2 && _dirty.iter().all(|q| !xq.contains(q)), "patchF: the dirty pool is the external register");
    }
    let sch = sched_g();
    let mut a = xq.to_vec();
    let mut o1b_cut: Option<(Vec<QubitId>, Vec<QubitId>, [QubitId; 2])> = None;
    let mut w = if O1B {
        // frame846 O1b: cut rings (286 lanes each) + the two extension lanes; w is the production view.
        let bc = if O1B2_LAST > 0 {
            // frame846 route B: the second-cut rings hold x on frame 1; the cut rings are their frame-(O1B2_LAST+1)
            // widening by the two E2 lanes.
            a.extend(b.alloc_n(sch.w - 2 - xq.len()));
            let bc2 = b.alloc_n(sch.w + XC_CUT - YV_CUT - 2);
            let ex2 = [b.alloc(), b.alloc()];
            let (a1, bc1) = super::lilypad_g::o1b_rings_up(super::lilypad_g::sched_g_cut2_ref(), super::lilypad_g::sched_g_cut_ref(), O1B2_LAST + 1, &a, &bc2, ex2);
            a = a1;
            bc1
        } else {
            a.extend(b.alloc_n(sch.w - 1 - xq.len()));
            b.alloc_n(sch.w + XC_CUT - YV_CUT - 1)
        };
        let ex = [b.alloc(), b.alloc()];
        let (ap, bp) = super::lilypad_g::o1b_prod_rings(&sch, &a, &bc, ex);
        o1b_cut = Some((a, bc, ex));
        PWalk { a: ap, bb: bp, q: vec![], h: b.alloc_n(HB), capq: 11, log: b.alloc_n(LOGN) }
    } else {
        a.extend(b.alloc_n(sch.w - xq.len()));
        PWalk {
            a,
            bb: b.alloc_n(sch.w + XC_CUT - YV_CUT),
            q: vec![],
            h: b.alloc_n(HB),
            capq: 11,
            log: b.alloc_n(LOGN),
        }
    };
    #[cfg(test)]
    let forward_peak = std::env::var("LILYPAD_FWD_PEAK").ok().and_then(|v| v.parse().ok()).unwrap_or_else(peak);
    #[cfg(not(test))]
    let forward_peak = peak() - u64::from(FWD_LOWER);
    // frame846 O1b gate C: the extension lanes are already live; they are the forward temps 2 and 3.
    let fwd_extra = if O1B_C { FWD_NT as u64 - 2 } else { FWD_NT as u64 };
    let room = forward_peak.saturating_sub(b.live + 1 + fwd_extra) as usize;
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!("Lilypad-G forward live {} room {room}", b.live + 1 + fwd_extra);
    }
    let sc = if O1B_C {
        let ex = o1b_cut.as_ref().unwrap().2;
        let e = b.alloc();
        let mut tmp = b.alloc_n(FWD_NT - 2); tmp.extend(ex);
        PScr { e, sg: super::lilypad::NO_SG, d: vec![], tmp, sp: vec![], pool: b.alloc_n(room) }
    } else { PScr { e: b.alloc(), sg: super::lilypad::NO_SG, d: vec![], tmp: b.alloc_n(FWD_NT), sp: vec![], pool: b.alloc_n(room) } };
    let division = b.new_division();
    let (m, patchf_s0) = if let Some((ac, bc, _)) = &o1b_cut {
        // frame846 O1b gate C: ticks <= O1B_LAST on the cut rings, then the rings take sc.tmp[2..4] (E_X, E_Y) and
        // ticks S-1, S run on patchF's two-temp view with dirty lanes from the external register.
        assert!(PATCHF_LAST2 && sc.tmp.len() == FWD_NT && o1b_cut.as_ref().unwrap().2 == [sc.tmp[FWD_NT - 2], sc.tmp[FWD_NT - 1]]);
        assert!(_dirty.iter().all(|q| !w.a.contains(q) && !w.bb.contains(q) && !w.h.contains(q) && !w.log.contains(q)
            && !sc.tmp.contains(q) && *q != sc.e && *q != sc.sg && !sc.pool.contains(q)), "O1b: dirty pool overlaps the walk");
        let wc = PWalk { a: ac.clone(), bb: bc.clone(), q: vec![], h: w.h.clone(), capq: w.capq, log: w.log.clone() };
        (super::lilypad_g::walk_forward_g_o1b(b, &wc, &w, &sch, &sc, &GScr, Some(division), Some(&_dirty[..if FWD_NT <= 3 { 4 } else { 2 }])), usize::MAX)
    } else if PATCHF_LAST2 {
        assert!(_dirty.iter().all(|q| !w.a.contains(q) && !w.bb.contains(q) && !w.h.contains(q) && !w.log.contains(q)
            && !sc.tmp.contains(q) && *q != sc.e && *q != sc.sg && !sc.pool.contains(q)), "patchF: dirty pool overlaps the walk");
        super::lilypad_g::walk_forward_g_x(b, &w, &sch, &sc, &GScr, Some(division), Some(&_dirty[..2]))
    } else {
        (walk_forward_g(b, &w, &sch, &sc, &GScr, Some(division)), usize::MAX)
    };
    ck(b, "walk forward end");
    // HOSE847 G9: move L = log[3] into the h5 lane (Z = h4 ^ h5 ^ L after div_inverse_g's cx), free log[3].
    if HOSE == 1 {
        assert!(w.log.len() == 4 && w.h.len() == 6);
        let (l3, h5) = (w.log[3], w.h[5]);
        b.cx(l3, h5);
        b.cx(h5, l3);
        let tn = sch.s + 1;
        let mut lits: Vec<(QubitId, bool)> = w.h[..5].iter().map(|&x| (x, true)).collect();
        lits.extend((0..12).map(|s| (w.asig(tn, s), true)));
        // patchF: with PATCHF_LAST2 the junction leaves tmp[2..4] idle (two more controls on the dirty V-chain).
        let mut temps: Vec<QubitId> = if PATCHF_LAST2 { assert_eq!(sc.tmp.len(), FWD_NT); sc.tmp[..FWD_NT - 2].to_vec() } else { sc.tmp.clone() };
        temps.push(sc.e);
        if sc.sg != super::lilypad::NO_SG { temps.push(sc.sg); }
        temps.extend(&sc.pool);
        let dirty: Vec<QubitId> = (100..140).map(|k| w.af(tn, k)).filter(|q| !lits.iter().any(|l| l.0 == *q) && !temps.contains(q) && *q != l3).collect();
        super::mask::mc_xor(b, &lits, l3, &temps, &dirty);
        b.free(l3);
        w.log.truncate(3);
    }
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
    if PATCHF_LAST2 && patchf_s0 != usize::MAX {
        patchf_assert(b, &sc, patchf_s0, division);
    }
    // frame846 O1b gate C: sc.tmp[2..4] are ring lanes now (freed with the parked rings).
    let sc = if O1B_C { assert_eq!(sc.tmp.len(), FWD_NT); PScr { e: sc.e, sg: sc.sg, d: sc.d.clone(), tmp: sc.tmp[..FWD_NT - 2].to_vec(), sp: sc.sp.clone(), pool: sc.pool.clone() } } else { sc };
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
        o1b: o1b_cut,
    }
}

/// patchF gate (4): no op emitted from the start of forward tick S-1 (before step_core_g(S-1)) up to here
/// (div_forward_g, just before sc.release) names sc.tmp[2] or sc.tmp[3] as target or control. Emission-time check.
fn patchf_assert(b: &B, sc: &PScr, s0: usize, division: usize) {
    assert!(sc.tmp.len() == 4 && s0 <= b.ops.len());
    let lent = [sc.tmp[2], sc.tmp[3]];
    let hit = |op: &crate::circuit::Op| lent.contains(&op.q_target) || lent.contains(&op.q_control1) || lent.contains(&op.q_control2);
    let touches = b.ops[s0..].iter().filter(|&op| hit(op)).count();
    let last_before = b.ops[..s0].iter().rposition(|op| hit(op));
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!(
            "PATCHF div={division} window=[{s0},{}) ops={} tmp2=q{} tmp3=q{} touches={touches} last_touch_before={:?} ({} ops before tick S-1)",
            b.ops.len(),
            b.ops.len() - s0,
            lent[0].0,
            lent[1].0,
            last_before,
            last_before.map_or(0, |i| s0 - i)
        );
    }
    assert_eq!(touches, 0, "patchF: sc.tmp[2..4] touched between forward tick S-1 and sc.release");
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
        o1b,
        ..
    } = dv;
    for &q in parked_a.iter().chain(&parked_b) {
        b.acquire(q);
    }
    // H5Q: retain the forward h5 owner through the shell, then reuse it as Q0.
    // This also preserves the parent's conservative final-tick HRange false positive.
    assert_eq!(w.h.len(), 6);
    let h5q_owner = w.h.pop().unwrap();
    b.play(&g_adapter.expect("Lilypad-G adapter"), true);
    if !INV_F0_LANE {
        // F is odd at every tick boundary and no regenerated tick >= 2 reads its lane 0 as data (value swaps start at
        // lane 1, cofactor windows exclude it); its loans drop out. Clear it: the lane serves as Q lane 12 for ticks
        // S..2 (that lane carries digits of ticks = 0 mod 13 only, so it is |0> again before tick 1 on the success
        // support), and tick 1 sets it back to F0 = 1.
        b.x(w.bf(0));
    }
    if !INV_V0_LANE {
        // V0 = !U0 at the walk's end (post-swap): clear it; its lane serves as Q lane 11 for ticks S..2 (digits of
        // ticks = 12 mod 13 only, |0> before tick 1 on the success support); tick 1 sets it back to !U0.
        b.cx(w.asig(sch.s + 1, 0), w.bsig(0));
        b.x(w.bsig(0));
    }
    if !INV_V1_LANE {
        // V1 at the walk's end (consistent post-tick state): clear it; its lane serves as Q lane 10 for ticks S..2
        // (digits of ticks = 11 mod 13 only, |0> before tick 1 on the success support); tick 1 sets it back.
        super::lilypad_g::v1_chart_xor(b, &w, sch.s + 1, &super::lilypad_g::rho_stable(&w, sch.s), w.bsig(1));
    }
    if !INV_V2_LANE {
        // V2 at the walk's end: clear it; its lane serves as Q lane 9 for ticks S..2 (digits of ticks = 10 mod 13
        // only, |0> before tick 1 on the success support); tick 1 sets it back.
        super::lilypad_g::v2_chart_xor(b, &w, sch.s + 1, &super::lilypad_g::rho_stable(&w, sch.s), w.bsig(2));
    }
    if !INV_V3_LANE {
        // V3 at the walk's end: clear it; its lane serves as Q lane 8 for ticks S..3 (digits of ticks = 9 mod 13 only,
        // |0> before tick 2 on the success support); tick 2 sets it back.
        super::lilypad_g::v3_chart_xor(b, &w, sch.s + 1, &super::lilypad_g::rho_stable(&w, sch.s), w.bsig(3));
    }
    if !INV_V4_LANE {
        // v2r845: V4 at the walk's end: clear it; its lane serves as Q lane 7 for ticks S..4 (digits of ticks = 8 mod 13
        // only, |0> before tick 3 on the success support); tick 3 sets it back.
        super::lilypad_g::v4_chart_xor(b, &w, sch.s + 1, &super::lilypad_g::rho_stable(&w, sch.s), w.bsig(4));
    }
    if !INV_V5_LANE {
        // retake852 V5P: V5 at the walk's end: clear it; its lane serves as Q lane 6 for ticks S..5 (digits of ticks = 7
        // mod 13 only, |0> before tick 4 on the success support); tick 4 sets it back.
        super::lilypad_g::v5_chart_xor(b, &w, sch.s + 1, &super::lilypad_g::rho_stable(&w, sch.s), w.bsig(5));
    }
    assert!(!INV_F0_LANE && !INV_V0_LANE && !INV_V1_LANE && !INV_V2_LANE && !INV_V3_LANE && !INV_V4_LANE);
    assert_eq!((sch.s + 1) % 13, 0, "H5Q endpoint Q owner frame");
    if O1B_C {
        // frame846 O1b gate C: Q slots 0/1 are E_X/E_Y (ring lanes on ticks S-1, S; own lanes below); Z = b ^ L lives in
        // the cleared F0 lane (Q lane 12 = frame 0 of tick S; the t = S frame swap is dropped); the owner is slot 2.
        let ex = o1b.as_ref().unwrap().2;
        b.cx(h5q_owner, w.bf(0)); b.cx(w.bf(0), h5q_owner);
        w.q = vec![ex[0], ex[1], h5q_owner];
        if INV_V5_LANE {
            w.q.extend(b.alloc_n(4));
            w.q.extend([w.bsig(4), w.bsig(3), w.bsig(2), w.bsig(1), w.bsig(0), w.bf(0)]);
        } else {
            // retake852 V5P: bsig(5) serves as Q lane 6.
            w.q.extend(b.alloc_n(3));
            w.q.extend([w.bsig(5), w.bsig(4), w.bsig(3), w.bsig(2), w.bsig(1), w.bsig(0), w.bf(0)]);
        }
        b.cx(w.h[4], w.bf(0)); // h5 -> b = h4 XOR h5 on Z's lane.
    } else {
    w.q = vec![h5q_owner];
    // v3r846: V3 released (cleared above by its chart): bsig(3) serves as Q lane 8.
    // v2r845: V4 released as well: bsig(4) serves as Q lane 7.
    if INV_V5_LANE {
        w.q.extend(b.alloc_n(6));
        w.q.extend([w.bsig(4), w.bsig(3), w.bsig(2), w.bsig(1), w.bsig(0), w.bf(0)]);
    } else {
        // retake852 V5P: bsig(5) serves as Q lane 6.
        w.q.extend(b.alloc_n(5));
        w.q.extend([w.bsig(5), w.bsig(4), w.bsig(3), w.bsig(2), w.bsig(1), w.bsig(0), w.bf(0)]);
    }
    b.cx(w.h[4],h5q_owner); // h5 -> b=h4 XOR h5 in endpoint frame zero.
    }
    let live = b.live + u64::from(INV_E_LANE) + u64::from(INV_SG_LANE) + inverse_d_len_g() as u64 + inverse_tmp_len_g() as u64 + super::lilypad_g::inverse_sp_len_g() as u64;
    #[cfg(test)]
    let inverse_peak = std::env::var("LILYPAD_INV_PEAK").ok().and_then(|v| v.parse().ok()).unwrap_or_else(peak);
    #[cfg(not(test))]
    // retake852 V5P: the inverse walk requests one lane less than the shell / forward peak (V5_INV_LOWER): at 845 the
    // forward walk still binds, so the 844-lane inverse layout is measured inside an 845 circuit.
    let inverse_peak = peak() - u64::from(!INV_V5_LANE && V5_INV_LOWER);
    let room = inverse_peak.saturating_sub(live) as usize;
    let sc = PScr::alloc_inv_g(b, room, INV_SG_LANE, INV_E_LANE);
    if std::env::var("FROGTAIL_CK").is_ok() {
        eprintln!("Lilypad-G inverse live {live} room {room}");
        let owned = w.a.len()+w.bb.len()+w.h.len()+w.log.len()+w.q.len()+2+sc.d.len()+sc.tmp.len()+sc.sp.len()+sc.pool.len();
        eprintln!("Q872_INVERSE_BINDER external={} rings={} h={} log={} q={} e_sg=2 d={} tmp={} sp={} pool={} live={} requested={}",
            b.live-owned as u64,w.a.len()+w.bb.len(),w.h.len(),w.log.len(),w.q.len(),
            sc.d.len(),sc.tmp.len(),sc.sp.len(),sc.pool.len(),b.live,inverse_peak);
    }
    if let Some((ac, bc, _)) = &o1b {
        let wc = PWalk { a: ac.clone(), bb: bc.clone(), q: w.q.clone(), h: w.h.clone(), capq: w.capq, log: w.log.clone() };
        super::lilypad_g::walk_inverse_g_o1b(b, &wc, &w, &sch, &sc, &GScr, &m, Some(division));
    } else {
        walk_inverse_g(b, &w, &sch, &sc, &GScr, &m, Some(division));
    }
    ck(b, "walk inverse end");
    sc.release(b);
    b.close_division(division);
    if INV_F0_LANE { b.free_n(&w.q); } else if INV_V0_LANE { b.free_n(&w.q[..12]); }
    else if INV_V1_LANE { b.free_n(&w.q[..11]); } else if INV_V2_LANE { b.free_n(&w.q[..10]); } else if INV_V3_LANE { b.free_n(&w.q[..9]); } else if INV_V4_LANE { b.free_n(&w.q[..8]); } else if INV_V5_LANE { b.free_n(&w.q[..7]); } else { b.free_n(&w.q[..6]); }
    if let Some((ac, bc, ex)) = &o1b {
        // frame846 O1b: the walk ends in the cut geometry; the extension lanes are |0> (gate B: own lanes).
        if O1B2_LAST > 0 {
            // frame846 route B: x sits in the second-cut rings' frame-1 lanes; the cut rings are a permutation of them.
            let rest: Vec<QubitId> = ac.iter().copied().filter(|q| !xq.contains(q)).collect();
            assert_eq!(rest.len() + xq.len(), ac.len());
            b.free_n(&rest);
        } else {
            assert_eq!(&ac[..xq.len()], xq);
            b.free_n(&ac[xq.len()..]);
        }
        b.free_n(bc);
        if !O1B_C { b.free_n(ex); }
    } else {
        b.free_n(&w.a[xq.len()..]);
        b.free_n(&w.bb);
    }
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
    // dy = lambda * dx: recompute, fix the phase, and uncompute.
    {
        let z = b.alloc_n(256);
        let ms = Ms::alloc_room(b, shell_peak(2));
        let mut zz = z.clone();
        if l1_enabled() {
            let pair = super::modp_ft::product_lazy(b, &ms, &mut zz, &y, &x);
            for i in 0..256 { b.z_if(zz[i], m1[i]); }
            super::modp_ft::product_inv_lazy(b, &mut zz, &y, &x, pair);
        } else {
            let r = rec_product(b, &ms, &z, &y, &x, false);
            b.play(&r, false);
            for i in 0..256 { b.z_if(z[i], m1[i]); }
            product_inv(b, &ms, &mut zz, &y, &x);
        }
        b.free_n(&z);
        ms.release(b);
    }

    // ---------------- x: dx' = lambda^2 - dx - 3 ox
    ck(b, "-- x: dx' = lambda^2 - ");
    {
        // The closed native block owns every scratch lane. No modular pool
        // co-resides. It subtracts y^2, so negate afterwards to obtain y^2-x.
        // The Karatsuba square with retained scratch (k2r) needs a 940-lane cap; at 867 the flat
        // half-square (P1 flat) is the one that fits.
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
