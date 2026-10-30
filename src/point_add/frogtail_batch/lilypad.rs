//! Lilypad-GCD audit build (resources lens, lilypad_r2): Bernstein-Yang divsteps with delta0 = 1/2 in Frogtail-style cross
//! rings, one public halving per tick, built only from in-tree primitives so the Toffoli count is the real one.
//!
//! Rings (frogtail layout): X = (g ascending from frame 0 | c_f descending from the top), relabeled every tick
//! (frame offset t: g/2 and 2 c_f in one go); Y = (f | c_g), fixed. Shared public split c(t), per-tick compressed
//! widths kv(t), kc(t) (lsc: sign-extension lanes cleared into the carry pool). h = delta - 1/2 (6-bit two's
//! complement). Tick t:
//!   e <- X.v[0] (moved out; X.v[0] = 0 afterwards, which is c_f''s new sig-0 lane);  sigma = e & [h >= 0]
//!   cswap(X, Y) on sigma (value lanes 1..kv, cofactor lanes 1..kc; cofactor lane 0 by one CNOT)
//!   value lanes 1..kv:  sigma: X.v <- g - f = ~(T + ~A);  no swap: X.v <- g + f + 1 = ~(~T + ~A)   (add ctrl e)
//!   cofactor lanes 1..kc: sigma: Y.c <- c_g - c_f = ~(T + ~A);  no swap: Y.c <- c_g + c_f            (add ctrl e)
//!   halve (relabel + boundary sign fixes), h ^= sigma, h += 1, sigma ^= X.c[1] (swap decode -> 0)
//! Forward walk: e is X-measured (e = g_0 of the pre-state; on swap ticks it is the run marker 1).
//! Regenerating tick (inverse walk, played backwards): e is Q's frame lane QB-1 (ring layout, one frame down per
//! tick), so a run's word W = 1 + 2q (marker + digits) sits top-aligned at its completion. Completions:
//!   swap with delta = 1/2 -> ic = 0 word (marker only): cleared every tick by M = [h=0] & X.c[1].
//!   r-run completion (post h = 0, no swap): W u = c_g mod 2^(ic+1), u = c_f >> (ic+1). Erased on even ticks only:
//!   Fd = [h=0] & !cf1 (this tick), deferred ones from the previous (odd) tick: Fn = [h=1] & !cf1 & !cf2 (no swap
//!   since), Fs = [h=0] & cf1 & !(cf2 ^ cg1) (swap since: window <- (X.c/2 - Y.c) in place). Eraser = frogstrip's
//!   (normalizer, radix-4 multiply, rot4 rotation, lent mask) on the window X.c sig 2.., with D = Fs|Fn pre-rotating
//!   Q up one lane and decrementing the shift.
use super::builder::{B, G};
use super::chunked::{AddRole, Pair, PairKey};
use super::frogdrop::crot_up;
use super::frogstrip::{
    clear_decode2_onehot_shared, clear_decode5_high_shared, decode2_onehot_shared, decode5_high_shared,
    radix4_finish_mul, sec, SEC_INV,
};
use super::frogtail::rot4_unit;
use super::arith::{dec, dec_topless, rot4_up};
use super::modp_ft::ctrl_add_pool;
use crate::circuit::{BitId, QubitId};

// C50 cut bits: CAP-K4=1, X10=2, X04=4, X11=8, X08=16, early-h=32, radix rows=64.
const C50_MASK: u32 = 251; // WQ1/WQ2 reserve G0; U07 is excluded.
thread_local! {
    // Forward cap measurements are consumed in reverse tick order by p3.
    // Each division closes before the next division opens; no quantum owner is retained.
    static C50_CAP_TAPES: std::cell::RefCell<Vec<BitId>> = const { std::cell::RefCell::new(Vec::new()) };
}
#[cfg(test)]
pub(crate) fn c50_cap_tape_depth()->usize {C50_CAP_TAPES.with(|v|v.borrow().len())}
#[cfg(test)]
thread_local! { static C50_TEST_MASK: std::cell::Cell<Option<u32>> = const { std::cell::Cell::new(None) }; }
#[cfg(test)]
pub(crate) fn c50_test_mask(mask: Option<u32>) { C50_TEST_MASK.with(|v| v.set(mask)); }
pub(crate) fn c50_enabled(bit:u32)->bool {
    #[cfg(test)] { return C50_TEST_MASK.with(|v| v.get().unwrap_or(C50_MASK)&bit!=0); }
    #[cfg(not(test))] { C50_MASK&bit!=0 }
}

// O6 (R24) inverse-walk levers: QLEND-odd=1, EARLYNARROW=2, QLEND-E=4, P3 clean temp=8.
const O6_MASK: u32 = 15;
#[cfg(test)]
thread_local! { static O6_TEST_MASK: std::cell::Cell<Option<u32>> = const { std::cell::Cell::new(None) }; }
#[cfg(test)]
pub(crate) fn o6_test_mask(mask: Option<u32>) { O6_TEST_MASK.with(|v| v.set(mask)); }
pub(crate) fn o6_enabled(bit: u32) -> bool {
    #[cfg(test)] {
        let env = || std::env::var("O6_TEST_MASK").ok().and_then(|s| s.parse().ok()).unwrap_or(O6_MASK);
        return O6_TEST_MASK.with(|v| v.get().unwrap_or_else(env) & bit != 0);
    }
    #[cfg(not(test))] { O6_MASK & bit != 0 }
}

// Test-only op-index marks for the O6 z3 export (eraser stage boundaries).
#[cfg(test)]
thread_local! { pub(crate) static O6_MARKS: std::cell::RefCell<Vec<(&'static str, usize)>> = const { std::cell::RefCell::new(Vec::new()) }; }
#[cfg(test)]
fn o6_mark(b: &B, name: &'static str) { O6_MARKS.with(|m| m.borrow_mut().push((name, b.ops.len()))); }
#[cfg(not(test))]
fn o6_mark(_b: &B, _name: &'static str) {}

const L4_REPAIRED_CAP: bool = true;

#[cfg(test)]
thread_local! {
    static TEST_L4: std::cell::Cell<i8> = const { std::cell::Cell::new(-1) };
    static L4_TEST_NEG: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn test_l4_override(value: Option<bool>) {
    TEST_L4.with(|v| v.set(value.map_or(-1, i8::from)));
}

#[cfg(test)]
pub(crate) fn l4_test_neg(mode: u8) {
    L4_TEST_NEG.with(|m| m.set(mode));
}

fn l4_enabled() -> bool {
    #[cfg(test)]
    {
        return TEST_L4.with(|v| match v.get() { 0 => false, 1 => true, _ => L4_REPAIRED_CAP });
    }
    #[cfg(not(test))]
    {
        L4_REPAIRED_CAP
    }
}

fn l4_neg(mode: u8) -> bool {
    #[cfg(test)]
    {
        return L4_TEST_NEG.with(|m| m.get() == mode);
    }
    #[cfg(not(test))]
    {
        let _ = mode;
        false
    }
}

#[cfg(test)]
thread_local! {
    static L2_TEST_NEG: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
    static L5_TEST_NEG: std::cell::Cell<u8> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn l2_test_neg(mode: u8) {
    L2_TEST_NEG.with(|m| m.set(mode));
}

#[cfg(test)]
pub(crate) fn l5_test_neg(mode: u8) {
    L5_TEST_NEG.with(|m| m.set(mode));
}

#[cfg(test)]
fn l2_neg(mode: u8) -> bool {
    L2_TEST_NEG.with(|m| m.get() == mode)
}

#[cfg(test)]
fn l5_neg(mode: u8) -> bool {
    L5_TEST_NEG.with(|m| m.get() == mode)
}

#[cfg(not(test))]
fn l5_neg(_mode: u8) -> bool {
    false
}

#[cfg(not(test))]
fn l2_neg(_mode: u8) -> bool {
    false
}

/// C50 K10: HB6 only after the pinned C37 h_end32 failure fixture and same-input gates.
pub const HB: usize = 6;
/// The 12-lane L5 word has shifts 0..11, so four binary shift lanes are
/// sufficient.  The former fifth lane was identically zero.
pub const SB: usize = 4;
pub const NT: usize = 8;
/// Lilypad-G L5 keeps two universally-live inverse temporaries. The persistent
/// deferral flag is restored and used only as dirty mask workspace.
pub const G_INV_NT: usize = 1;
/// Lane LILY-A: placeholder sigma owner of an inverse Lilypad-G walk that owns no sigma lane. Each regenerated
/// tick hosts sigma in its own U0 lane (af(t, 0) = asig(t + 1, 0)) instead; see `rec_regen_g`.
pub const NO_SG: QubitId = QubitId(u64::MAX);
/// Lane LILY-A: placeholder e owner of an inverse Lilypad-G walk that owns no e lane (its eraser flag then lives on a
/// cleared sign lane, the terminal endpoint copy, or the donor lane; see `eraser`).
pub const NO_E: QubitId = QubitId(u64::MAX - 1);
/// Lane LILY-A: placeholder for a charted (not held) V1 in an eraser source view.
pub const NO_V1: QubitId = QubitId(u64::MAX - 2);
/// Lane LILY-A: placeholder for a charted V2 in an eraser source view.
pub const NO_V2: QubitId = QubitId(u64::MAX - 3);
/// Lane LILY-A: placeholder for a charted V3 in an eraser source view.
pub const NO_V3: QubitId = QubitId(u64::MAX - 4);

fn mterm(b: &mut B, f: QubitId, src: QubitId, t: QubitId) {
    if src != NO_V2 && src != NO_V3 { b.ccx(f, src, t); }
}

/// Lane LILY-A: the l = 1 mask term with V3 charted: q1 ^= e [g' > 1] (V3 ^ rho'). With U1 = U2 = 0 (g > 1),
/// V3 ^ rho' = 1 ^ U3 ^ F1 ^ F2 ^ F3 (mod 16 page relation), and U3 = [g = 2] = !D [g' = 2]:
/// q1 ^= e (1 ^ F1 ^ F2 ^ F3) [g' >= 2] ^ e !D [g' = 2]. At the public end F1 = F2 = F3.
fn v3_mask_term(b: &mut B, w: &PWalk, tn: usize, e: QubitId, d: QubitId, g: &[QubitId], target: QubitId, terminal: bool, sg: QubitId) {
    let dirty: Vec<QubitId> = (120..130).map(|k| w.af(tn, k)).collect();
    // v3r846 repair 1b: at tn = 531 (yv_boundary_residual into c = 4) F2 ^ F3 = sigma (X3 ^ X2) on every state.
    let narrow = !terminal && super::lilypad_g::v3r_narrow(tn) == Some(4);
    let (top, xs) = (w.af(tn, 3), w.af(tn, 2));
    if narrow {
        assert!(sg != super::lilypad::NO_SG && ![top, xs].contains(&sg) && ![top, xs].contains(&e) && ![top, xs].contains(&d)
            && ![top, xs].contains(&target) && g.iter().all(|x| ![top, xs].contains(x)));
        b.cx(xs, top);
    }
    // v3r846 G3: fold A = 1 ^ F1 ^ F2 ^ F3 onto the F3 lane: e A, e A [g1..=0], e !D [g' = 2] (3 toggles instead of 9).
    {
        let (f1, f2, f3) = (w.bf(1), w.yv(tn, 2), w.yv(tn, 3));
        let mut ls = vec![e, d, f1, f2, f3, target];
        ls.extend(g.iter().copied());
        if super::lilypad_g::V3R_STAGE >= 3 && !narrow && !terminal && g.len() >= 2 && super::lilypad_g::v3r_distinct(&ls)
            && dirty.iter().all(|q| !ls.contains(q)) {
            b.cx(f1, f3); b.cx(f2, f3); b.x(f3);
            let mut a2 = vec![(e, false), (f3, false)];
            let mut toggles: Vec<Vec<(QubitId, bool)>> = vec![a2.clone()];
            a2.extend(g[1..].iter().map(|&x| (x, true)));
            toggles.push(a2);
            let mut eq2 = vec![(e, false), (d, true), (g[0], true), (g[1], false)];
            for &x in &g[2..] { eq2.push((x, true)); }
            toggles.push(eq2);
            for lits in &toggles {
                let dl: Vec<QubitId> = dirty.iter().copied().filter(|q| *q != target && !lits.iter().any(|l| l.0 == *q)).collect();
                super::mask::mc_xor(b, lits, target, &[], &dl);
            }
            b.x(f3); b.cx(f2, f3); b.cx(f1, f3);
            return;
        }
    }
    let fs: Vec<Vec<(QubitId, bool)>> = if terminal { vec![vec![(w.bf(1), false)]] } else if narrow {
        vec![vec![(w.bf(1), false)], vec![(sg, false), (top, false)]]
    } else { [w.bf(1), w.yv(tn, 2), w.yv(tn, 3)].iter().map(|&f| vec![(f, false)]).collect() };
    let lo: Vec<(QubitId, bool)> = g[1..].iter().map(|&x| (x, true)).collect();
    let mut toggles: Vec<Vec<(QubitId, bool)>> = vec![];
    // e A [g' >= 2] = e A ^ e A !g1 .. !gk, A = 1 ^ sum F
    let mut a_terms: Vec<Vec<(QubitId, bool)>> = vec![vec![]];
    for f in &fs { a_terms.push(f.clone()); }
    for at in &a_terms {
        let mut x = vec![(e, false)]; x.extend(at.iter().copied()); toggles.push(x.clone());
        x.extend(lo.iter().copied()); toggles.push(x);
    }
    // e !D [g' = 2]: !g0 g1 !g2 ..
    let mut eq2 = vec![(e, false), (d, true), (g[0], true), (g[1], false)];
    for &x in &g[2..] { eq2.push((x, true)); }
    toggles.push(eq2);
    for lits in &toggles {
        let dl: Vec<QubitId> = dirty.iter().copied().filter(|q| *q != target && !lits.iter().any(|l| l.0 == *q)).collect();
        super::mask::mc_xor(b, lits, target, &[], &dl);
    }
    if narrow { b.cx(xs, top); }
}

/// Lane LILY-A: the l = 0 mask term with V2 charted, at the mask: q0 ^= e [g' > 0] (V2 ^ rho'), where g' = g - D is
/// the mask's shift (after the D decrement). Pre-swap with U0 = 0 and U1 = 0 (g > 0), V2 ^ rho' = 1 ^ U2 ^ F2, and the
/// normalizer shift g counts the window's trailing zeros from U1: g = 1 means U2 = 1, g >= 2 means U2 = 0. With
/// g = g' + D this gives q0 ^= e (!F2 [g' >= 1] ^ !D [g' = 1]).
fn v2_mask_term(b: &mut B, w: &PWalk, tn: usize, e: QubitId, d: QubitId, g: &[QubitId], target: QubitId, terminal: bool) {
    // At the public end F = +-1, so F2 = F1; there Y.v lane 2 may be lent as a cleared copy of lane 1.
    let f2 = if terminal { w.bf(1) } else { w.yv(tn, 2) };
    let dirty: Vec<QubitId> = (120..128).map(|k| w.af(tn, k)).collect();
    {
        // tsave848 rank 3 (factored chart): e !F2 ^ e Z' (g0 ? !D : !F2), Z' = prod_{i>=1} !g_i. One
        // cswap(g0; F2, D) selects the operand on F2's lane: 1 + 2 + 4 (len(g) - 1) Toffoli instead of 1 + 8 len(g).
        let mut lanes = vec![e, d, f2, target];
        lanes.extend(g.iter().copied());
        let ok = g.len() >= 2 && lanes.iter().enumerate().all(|(i, q)| !lanes[..i].contains(q));
        if ok {
            let a = [(e, false), (f2, true)];
            let mut zl = vec![(e, false), (f2, true)];
            for &x in &g[1..] { zl.push((x, true)); }
            let dl = |lits: &[(QubitId, bool)]| -> Vec<QubitId> {
                dirty.iter().copied().filter(|q| *q != target && *q != d && *q != g[0] && !lits.iter().any(|l| l.0 == *q)).collect()
            };
            super::mask::mc_xor(b, &a, target, &[], &dl(&a));
            b.cswap(g[0], f2, d);
            super::mask::mc_xor(b, &zl, target, &[], &dl(&zl));
            b.cswap(g[0], f2, d);
            return;
        }
        if std::env::var_os("FROGTAIL_CK").is_some() { eprintln!("T3 v2_mask_term fallback tn{tn}"); }
    }
    let a = vec![(e, false), (f2, true)];
    let mut bz = vec![(e, false), (f2, true)];
    let mut c1 = vec![(e, false), (d, true), (g[0], false)];
    for &x in g { bz.push((x, true)); }
    for &x in &g[1..] { c1.push((x, true)); }
    for lits in [&a, &bz, &c1] {
        let dl: Vec<QubitId> = dirty.iter().copied().filter(|q| *q != target && !lits.iter().any(|l| l.0 == *q)).collect();
        super::mask::mc_xor(b, lits, target, &[], &dl);
    }
}

/// Lane LILY-A: V1 is charted at this pre-swap eraser (PEAK0 < 863, tick >= 2).
fn v1_charted(t: usize) -> bool {
    super::lilypad_g::v1_virtual(t)
}

/// Lane LILY-A: target ^= e & (V1 ^ rho') at a pre-swap eraser (U0 = 0 pre-swap): V1 ^ rho' = U1 ^ F1 ^ 1.
fn v1_mask_toggle(b: &mut B, w: &PWalk, tn: usize, e: QubitId, target: QubitId) {
    b.ccx(e, w.asig(tn, 1), target);
    b.ccx(e, w.bf(1), target);
    b.cx(e, target);
}

#[derive(Clone, Debug)]
pub struct PSched {
    pub w: usize,
    pub s: usize,
    pub c: Vec<usize>,
    pub kv: Vec<usize>,
    pub kc: Vec<usize>,
}

impl PSched {
    pub fn from_text(txt: &str) -> PSched {
        let v: Vec<usize> = txt
            .lines()
            .filter(|l| !l.trim_start().starts_with('#'))
            .flat_map(|l| l.split_whitespace())
            .map(|x| x.parse().unwrap())
            .collect();
        let (w, s) = (v[0], v[1]);
        let (mut c, mut kv, mut kc) = (vec![0], vec![0], vec![0]);
        for t in 0..=s {
            c.push(v[2 + 3 * t]);
            kv.push(v[3 + 3 * t]);
            kc.push(v[4 + 3 * t]);
        }
        for t in 1..=s + 1 {
            assert!(kv[t] >= 2 && kv[t] <= c[t] && kc[t] >= 3 && kc[t] <= w - c[t], "sched t {t}");
        }
        PSched { w, s, c, kv, kc }
    }
}

pub struct PWalk {
    pub a: Vec<QubitId>,
    pub bb: Vec<QubitId>,
    pub q: Vec<QubitId>,
    pub h: Vec<QubitId>,
    /// run cap q (0 = off) and its overflow log (2 slots x 4 bits, a stack: push = cswap + write slot 0)
    pub capq: usize,
    pub log: Vec<QubitId>,
}

impl PWalk {
    pub fn af(&self, t: usize, f: usize) -> QubitId {
        let w = self.a.len();
        self.a[(f + t - 1) % w]
    }
    pub fn asig(&self, t: usize, s: usize) -> QubitId {
        self.af(t, self.a.len() - 1 - s)
    }
    pub fn bf(&self, f: usize) -> QubitId {
        self.bb[f]
    }
    /// Read-only Y value view: late absent sign copies alias the retained sign.
    pub fn yv(&self, fr: usize, f: usize) -> QubitId {
        let c = super::lilypad_g::sched_g().c[fr] - super::lilypad_g::ycut_at(fr);
        self.bf(f.min(c - 1))
    }
    /// Schlussgang: read-only X value view; lanes above the frame's value region alias its sign lane (the endpoint
    /// frame S+1 holds G in two lanes, its lane 2 is the X cofactor top).
    pub fn xv(&self, fr: usize, f: usize) -> QubitId {
        let c = super::lilypad_g::sched_g().c[fr];
        self.af(fr, f.min(c - 1))
    }
    pub fn bsig(&self, s: usize) -> QubitId {
        self.bb[self.bb.len() - 1 - s]
    }
    pub fn qfr(&self, t: usize) -> Vec<QubitId> {
        let n = self.q.len();
        (0..n).map(|f| self.q[(f + t) % n]).collect()
    }
}

/// e: forward digit / eraser flag; sg: sigma; d: deferral flag (inverse); sp: normalizer shift (inverse).
pub struct PScr {
    pub e: QubitId,
    pub sg: QubitId,
    pub d: Vec<QubitId>,
    pub tmp: Vec<QubitId>,
    pub sp: Vec<QubitId>,
    pub pool: Vec<QubitId>,
}

#[derive(Clone)]
pub struct ParityCtl {
    pub qs: Vec<QubitId>,
    pub flip: bool,
}

impl ParityCtl {
    pub fn xor_into(&self, b: &mut B, target: QubitId) {
        for &q in &self.qs {
            b.cx(q, target);
        }
        if self.flip {
            b.x(target);
        }
    }
}

impl PScr {
    /// Lane LILY-A: forward scratch with `nt` temporaries.
    pub fn alloc_fwd_n(b: &mut B, room: usize, nt: usize) -> PScr {
        PScr { e: b.alloc(), sg: b.alloc(), d: vec![], tmp: b.alloc_n(nt), sp: vec![], pool: b.alloc_n(room) }
    }
    pub fn alloc_fwd(b: &mut B, room: usize) -> PScr {
        PScr { e: b.alloc(), sg: b.alloc(), d: vec![], tmp: b.alloc_n(NT), sp: vec![], pool: b.alloc_n(room) }
    }
    pub fn alloc_inv(b: &mut B, room: usize) -> PScr {
        PScr {
            e: b.alloc(),
            sg: b.alloc(),
            d: b.alloc_n(1),
            tmp: b.alloc_n(NT),
            sp: b.alloc_n(SB),
            pool: b.alloc_n(room),
        }
    }
    pub fn alloc_inv_g(b: &mut B, room: usize, with_sg: bool, with_e: bool) -> PScr {
        PScr {
            e: if with_e { b.alloc() } else { NO_E },
            sg: if with_sg { b.alloc() } else { NO_SG },
            d: b.alloc_n(super::lilypad_g::inverse_d_len_g()),
            tmp: b.alloc_n(super::lilypad_g::inverse_tmp_len_g()),
            sp: b.alloc_n(super::lilypad_g::inverse_sp_len_g()),
            pool: b.alloc_n(room),
        }
    }
    pub fn release(self, b: &mut B) {
        if self.e != NO_E {
            b.free(self.e);
        }
        if self.sg != NO_SG {
            b.free(self.sg);
        }
        b.free_n(&self.d);
        b.free_n(&self.tmp);
        b.free_n(&self.sp);
        b.free_n(&self.pool);
    }
}

/// Initial state: X = (x | 0) (x = the caller's lanes a[0..256)), Y = (p | 1), h = 0.
pub fn init(b: &mut B, w: &PWalk) {
    let p = super::frogdrop_sched::p();
    for f in 0..256 {
        if p.bit(f) {
            b.x(w.bf(f));
        }
    }
    b.x(w.bsig(0));
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lsc_from(
    b: &mut B,
    w: &PWalk,
    t: usize,
    c: usize,
    kv: usize,
    kc: usize,
    a_lo: usize,
    b_lo: usize,
) -> Vec<QubitId> {
    let wd = w.a.len();
    let mut z = vec![];
    // Schlussgang: explicit Y value cut of this frame; X's cofactor region is wd - c, Y's is bb.len() - cy.
    let cy = c - super::lilypad_g::ycut_at(t);
    let yd = w.bb.len() - cy;
    let ky = kv.min(cy);
    for f in kv..c {
        b.cx(w.af(t, kv - 1), w.af(t, f));
        z.push(w.af(t, f));
        if f < cy {
            b.cx(w.bf(ky - 1), w.bf(f));
            z.push(w.bf(f));
        }
    }
    for s in kc.max(a_lo)..wd - c {
        b.cx(w.asig(t, kc - 1), w.asig(t, s));
        z.push(w.asig(t, s));
    }
    for s in kc.max(b_lo)..yd {
        b.cx(w.bsig(kc - 1), w.bsig(s));
        z.push(w.bsig(s));
    }
    z
}

pub(super) fn lsc(b: &mut B, w: &PWalk, t: usize, c: usize, kv: usize, kc: usize) -> Vec<QubitId> {
    lsc_from(b, w, t, c, kv, kc, 0, 0)
}

/// frogstrip's paired digit add (same key scheme).
#[allow(clippy::too_many_arguments)]
pub(super) fn digit_add(
    b: &mut B,
    source: &[QubitId],
    target: &[QubitId],
    ctl: QubitId,
    pool: &[QubitId],
    pairing: Option<(usize, bool)>,
    tick: usize,
    role: AddRole,
) {
    if target.len() == 1 {
        b.ccx(ctl, source[0], target[0]);
        return;
    }
    if let Some((division, inverse)) = pairing {
        let key = PairKey { division, tick, role };
        if !inverse || b.has_chunk_debts(key) {
            let pair = if inverse { Pair::Inverse(key) } else { Pair::Forward(key) };
            if super::chunked::try_add_paired(b, source, target, ctl, None, pool, Some(pair)) {
                return;
            }
            assert!(!inverse, "paired inverse must expose every carry position");
        }
    }
    ctrl_add_pool(b, source, target, ctl, pool);
}

/// Step of tick t up to (not including) the halve. `e` = |0> lane that receives g_0.
pub fn step_core(
    b: &mut B,
    w: &PWalk,
    t: usize,
    sch: &PSched,
    sc: &PScr,
    e: QubitId,
    extra: &[QubitId],
    pairing: Option<(usize, bool)>,
) {
    let (c, kv, kc) = (sch.c[t], sch.kv[t], sch.kc[t]);
    let sg = sc.sg;
    let h5 = w.h[HB - 1];
    sec(b, "lily.ctl", |b| {
        b.cx(w.af(t, 0), e);
        b.cx(e, w.af(t, 0));
        b.x(h5);
        b.and_c(e, h5, sg);
        b.x(h5);
    });
    sec(b, "lily.swap", |b| {
        lsc(b, w, t, c, kv, kc);
        for f in 1..kv {
            b.cswap(sg, w.af(t, f), w.bf(f));
        }
        for s in 1..kc {
            b.cswap(sg, w.asig(t, s), w.bsig(s));
        }
        b.cx(sg, w.asig(t, 0));
        lsc(b, w, t, c, kv, kc);
    });
    let mut pl = lsc(b, w, t, c, kv, kc);
    pl.extend(&sc.pool);
    pl.extend(&sc.tmp);
    pl.extend(extra);
    let av: Vec<QubitId> = (1..kv).map(|f| w.af(t, f)).collect();
    let bv: Vec<QubitId> = (1..kv).map(|f| w.bf(f)).collect();
    sec(b, "lily.addv", |b| {
        for &x in &bv {
            b.x(x);
        }
        for &x in &av {
            b.cx(e, x);
            b.cx(sg, x);
        }
        digit_add(b, &bv, &av, e, &pl, pairing, t, AddRole::Value);
        for &x in &av {
            b.cx(e, x);
        }
        for &x in &bv {
            b.x(x);
        }
    });
    let ac: Vec<QubitId> = (1..kc).map(|s| w.asig(t, s)).collect();
    let bc: Vec<QubitId> = (1..kc).map(|s| w.bsig(s)).collect();
    sec(b, "lily.addc", |b| {
        for &x in &ac {
            b.cx(sg, x);
        }
        digit_add(b, &ac, &bc, e, &pl, pairing, t, AddRole::Cofactor);
        for &x in &bc {
            b.cx(sg, x);
        }
        for &x in &ac {
            b.cx(sg, x);
        }
    });
    lsc(b, w, t, c, kv, kc);
}

pub(super) fn fix_boundary(b: &mut B, lane: &dyn Fn(usize) -> QubitId, c0: usize, c1: usize) {
    if c1 > c0 {
        for l in c0..c1 {
            b.cx(lane(c1), lane(l));
            b.cx(lane(l - 1), lane(l));
        }
    } else if c1 < c0 {
        for l in (c1..c0).rev() {
            b.cx(lane(c1 - 1), lane(l));
            b.cx(lane(c0), lane(l));
        }
    }
}

/// h += 1 (uncontrolled, two's complement), n - 2 Toffoli on `tmp`.
pub(super) fn inc_unctl(b: &mut B, h: &[QubitId], tmp: &[QubitId]) {
    let n = h.len();
    if n == 1 {
        b.x(h[0]);
        return;
    }
    let mut cs = vec![h[0]];
    for i in 1..n - 1 {
        b.and_c(cs[i - 1], h[i], tmp[i - 1]);
        cs.push(tmp[i - 1]);
    }
    for i in (1..n).rev() {
        b.cx(cs[i - 1], h[i]);
        if i >= 2 {
            b.and_u(cs[i - 2], h[i - 1], cs[i - 1]);
        }
    }
    b.x(h[0]);
}

/// Lane LILY-A: h += 1 (uncontrolled) with n - 3 temporaries (n >= 3): the top bit is flipped by one Toffoli on the
/// last stored carry, so the n - 2 carries of `inc_unctl` need one lane fewer at the same Toffoli count.
pub(super) fn inc_unctl_short(b: &mut B, h: &[QubitId], tmp: &[QubitId]) {
    let n = h.len();
    assert!(n >= 3 && tmp.len() + 3 >= n);
    let mut cs = vec![h[0]];
    for i in 1..n - 2 {
        b.and_c(cs[i - 1], h[i], tmp[i - 1]);
        cs.push(tmp[i - 1]);
    }
    b.ccx(cs[n - 3], h[n - 2], h[n - 1]);
    for i in (1..n - 1).rev() {
        b.cx(cs[i - 1], h[i]);
        if i >= 2 {
            b.and_u(cs[i - 2], h[i - 1], cs[i - 1]);
        }
    }
    b.x(h[0]);
}

/// Lane LILY-A: h += 1 with n - 4 temporaries (n >= 4): the top two bits by a three-control toggle (one dirty loan)
/// and one Toffoli on the last stored carry.
pub(super) fn inc_unctl_short2(b: &mut B, h: &[QubitId], tmp: &[QubitId], dirty: &[QubitId]) {
    let n = h.len();
    assert!(n >= 4 && tmp.len() + 4 >= n && !dirty.is_empty());
    let mut cs = vec![h[0]];
    for i in 1..n - 3 {
        b.and_c(cs[i - 1], h[i], tmp[i - 1]);
        cs.push(tmp[i - 1]);
    }
    super::mask::mcx_dirty(b, &[cs[n - 4], h[n - 3], h[n - 2]], h[n - 1], &dirty[..1]);
    b.ccx(cs[n - 4], h[n - 3], h[n - 2]);
    for i in (1..n - 2).rev() {
        b.cx(cs[i - 1], h[i]);
        if i >= 2 {
            b.and_u(cs[i - 2], h[i - 1], cs[i - 1]);
        }
    }
    b.x(h[0]);
}

/// Share the increment's AND prefix with the odd-tick marker. The caller provides
/// the complete halve recording; matching the exact increment trace makes source drift fail closed.
pub(super) fn inc_mclear_fused(b:&mut B,w:&PWalk,t:usize,sc:&PScr,r:&[G],half:bool)->Vec<G> {
    let mut n=2usize;while n<HB && (1usize<<(n-1))-1<t {n+=1;}
    let mut tmp=sc.tmp.clone();if tmp.is_empty() && sc.e != NO_E {tmp.push(sc.e);}tmp.extend(&sc.sp);
    let short = n >= 3 && tmp.len() + 2 < n;
    let gen = n >= 5 && tmp.len() + 4 < n;
    let short2 = !gen && n >= 4 && tmp.len() + 3 < n;
    b.begin();
    if gen {inc_unctl_m(b,&w.h[..n],&tmp,&w.q[..3]);} else if short2 {inc_unctl_short2(b,&w.h[..n],&tmp,&w.q[..1]);} else if short {inc_unctl_short(b,&w.h[..n],&tmp);} else {inc_unctl(b,&w.h[..n],&tmp);}
    let inc=b.end();
    let starts:Vec<_>=r.windows(inc.len()).enumerate().filter(|(_,x)|*x==&inc[..]).map(|(i,_)|i).collect();
    assert_eq!(starts.len(),1,"increment/mclear source match tick{t}");
    if gen {
        // Lane LILY-A: m stored carries: all = c_(m+2) on Q frame 0, the marker toggle with dirty Q loans, the top
        // flips from all, all erased, the stored chain as before.
        assert!(sc.d.is_empty() && o6_enabled(8));
        let m = tmp.len().min(n - 2);
        let cf1=w.asig(t+1,1-usize::from(half));let q=w.qfr(t);
        let all = q[0];
        let h = &w.h[..n];
        assert!(all != q[q.len()-1] && all != cf1 && !tmp.contains(&all) && !w.h.contains(&all));
        assert!(q[1..4].iter().all(|&x| x != cf1 && x != q[q.len() - 1]));
        b.begin();
        let mut cs = vec![h[0]];
        for i in 1..=m { b.and_c(cs[i - 1], h[i], tmp[i - 1]); cs.push(tmp[i - 1]); }
        b.and_c(cs[m], h[m + 1], all);
        let mut mk = vec![all];
        mk.extend(&h[m + 2..n]);
        mk.push(cf1);
        super::mask::mcx_dirty(b, &mk, q[q.len() - 1], &q[1..4]);
        for j in (m + 3..n).rev() {
            let mut ctl = vec![all];
            ctl.extend(&h[m + 2..j]);
            super::mask::mcx_dirty(b, &ctl, h[j], &q[1..4]);
        }
        b.cx(all, h[m + 2]);
        b.and_u(cs[m], h[m + 1], all);
        for i in (1..=m + 1).rev() {
            b.cx(cs[i - 1], h[i]);
            if i >= 2 { b.and_u(cs[i - 2], h[i - 1], cs[i - 1]); }
        }
        b.x(h[0]);
        let fused = b.end();
        let mut out = r[..starts[0]].to_vec();
        out.extend(fused);
        out.extend_from_slice(&r[starts[0] + inc.len()..]);
        return out;
    }
    if short2 {
        // Lane LILY-A: replace the whole short2 increment by its fused form. all = c_(n-2) on the clean Q frame 0,
        // the marker toggle Q[QB-1] ^= all & h_(n-2) & h_(n-1) & X.c[1] (two dirty Q loans), then the top flips
        // h_(n-1) ^= all & h_(n-2), h_(n-2) ^= all, all erased, and the remaining carries as before.
        assert!(sc.d.is_empty() && o6_enabled(8));
        let cf1=w.asig(t+1,1-usize::from(half));let q=w.qfr(t);
        let all = q[0];
        let h = &w.h[..n];
        assert!(all != q[q.len()-1] && all != cf1 && !tmp.contains(&all) && !w.h.contains(&all) && q[1] != cf1 && q[2] != cf1);
        b.begin();
        let mut cs = vec![h[0]];
        for i in 1..n - 3 { b.and_c(cs[i - 1], h[i], tmp[i - 1]); cs.push(tmp[i - 1]); }
        b.and_c(cs[n - 4], h[n - 3], all);
        super::mask::mcx_dirty(b, &[all, h[n - 2], h[n - 1], cf1], q[q.len() - 1], &q[1..3]);
        b.ccx(all, h[n - 2], h[n - 1]);
        b.cx(all, h[n - 2]);
        b.and_u(cs[n - 4], h[n - 3], all);
        for i in (1..n - 2).rev() {
            b.cx(cs[i - 1], h[i]);
            if i >= 2 { b.and_u(cs[i - 2], h[i - 1], cs[i - 1]); }
        }
        b.x(h[0]);
        let fused = b.end();
        let mut out = r[..starts[0]].to_vec();
        out.extend(fused);
        out.extend_from_slice(&r[starts[0] + inc.len()..]);
        return out;
    }
    if short {
        // Lane LILY-A: the short increment has no stored top carry. all = c_(n-2) on the clean Q frame 0, the marker
        // toggle Q[QB-1] ^= all & h_(n-1) & X.c[1] with one dirty loan, and the top flip by CX from all.
        assert!(sc.d.is_empty() && o6_enabled(8));
        let at = starts[0] + (n - 3);
        let cs = if n == 3 { w.h[0] } else { tmp[n - 4] };
        assert!(r[at] == G::Ccx(cs, w.h[n - 2], w.h[n - 1]), "short increment top step tick{t}");
        let cf1=w.asig(t+1,1-usize::from(half));let q=w.qfr(t);
        let all = q[0];
        assert!(all != q[q.len()-1] && all != cs && all != cf1 && !tmp.contains(&all) && !w.h.contains(&all) && q[1] != cf1);
        let mut out = r[..at].to_vec();
        out.push(G::AndC(cs, w.h[n - 2], all));
        b.begin();
        super::mask::mc_xor(b, &[(all, false), (w.h[n - 1], false), (cf1, false)], q[q.len() - 1], &[], &q[1..2]);
        let mark = b.end();
        out.extend(mark);
        out.push(G::Cx(all, w.h[n - 1]));
        out.push(G::AndU(cs, w.h[n - 2], all));
        out.extend_from_slice(&r[at + 1..]);
        return out;
    }
    let at=starts[0]+n.saturating_sub(2);
    let prefix=if n==2 {w.h[0]}else{tmp[n-3]};
    let cf1=w.asig(t+1,1-usize::from(half));let q=w.qfr(t);let mut out=r[..at].to_vec();
    if sc.d.is_empty() && o6_enabled(8) {
        // O6 p3 add-on: Q frame 0 at odd t is qfr(t+1)[QB-1], the next tick's digit lane. On the
        // success support it is |0> here, so it serves as the clean AND lane of the direct marker clear.
        let all=q[0];
        assert!(all!=q[q.len()-1] && all!=prefix && all!=w.h[n-1] && all!=cf1 && !tmp.contains(&all) && !w.h.contains(&all));
        out.extend([G::AndC(prefix,w.h[n-1],all),G::Ccx(all,cf1,q[q.len()-1]),G::AndU(prefix,w.h[n-1],all)]);
    } else if sc.d.is_empty() {
        b.begin();super::mask::mc_xor(b,&[(prefix,false),(w.h[n-1],false),(cf1,false)],q[q.len()-1],&[],&q[..1]);let direct=b.end();out.extend(direct);
    }else{let all=sc.d[0];out.extend([G::AndC(prefix,w.h[n-1],all),G::Ccx(all,cf1,q[q.len()-1]),G::AndU(prefix,w.h[n-1],all)]);}
    out.extend_from_slice(&r[at..]);out
}

/// out ^= [u < k] (u unsigned, LSB first) via the carry chain of u + (2^n - k); chain on `tmp`, uncomputed.
fn lt_const(b: &mut B, u: &[QubitId], k: u64, out: QubitId, tmp: &[QubitId]) {
    let n = u.len();
    let c = ((1u64 << n) - k) & ((1u64 << n) - 1);
    b.begin();
    let mut carry: Option<QubitId> = None;
    let mut ti = 0;
    for i in 0..n {
        let ci = (c >> i) & 1 == 1;
        match (ci, carry) {
            (true, None) => carry = Some(u[i]),
            (false, None) => {}
            (false, Some(cq)) => {
                b.and_c(u[i], cq, tmp[ti]);
                carry = Some(tmp[ti]);
                ti += 1;
            }
            (true, Some(cq)) => {
                b.x(u[i]);
                b.x(cq);
                b.and_c(u[i], cq, tmp[ti]);
                b.x(u[i]);
                b.x(cq);
                b.x(tmp[ti]);
                carry = Some(tmp[ti]);
                ti += 1;
            }
        }
    }
    let chain = b.end();
    b.play(&chain, false);
    match carry {
        Some(cq) => b.cx(cq, out),
        None => {}
    }
    b.x(out);
    b.play(&chain, true);
}

/// ChäsSchublädli: pack two cap overflows into five lanes. Logical a=old single, b=incoming.
/// Support: a=0,b<16; a=1,b<8; a=2,b<4; a=3,b<2; a=4/5,b=0 (32 states).
/// Packed pairs have log4=1; singles are direct o in log0..3. Rho remains log0 XOR log4.
/// The full gate map is a permutation, including excluded states. Dirty Q loans are restored.
fn prefix5_cswap(b: &mut B, ctl: &[QubitId], x: QubitId, y: QubitId, dirty: &[QubitId]) {
    b.cx(x,y);
    let mut cc=ctl.to_vec(); cc.push(y);
    super::mask::mcx_dirty(b,&cc,x,dirty);
    b.cx(x,y);
}
fn prefix5_reflect(b: &mut B, h: &[QubitId]) {
    // h -> 5-h (mod 16), an involution: one Toffoli and three Clifford gates.
    b.ccx(h[1],h[2],h[3]); b.cx(h[1],h[2]); b.x(h[2]); b.x(h[0]);
}
pub(super) fn prefix5_push(b: &mut B, h: &[QubitId], log: &[QubitId], ee: QubitId, dirty: &[QubitId]) {
    assert!(h.len()>=4 && log.len()==5 && dirty.len()>=2);
    let (a0,a1,a2)=(log[0],log[1],log[2]);
    prefix5_reflect(b,h);
    // Convert a=4/5,b=0 into a=3,b=3/2, then pack a=2/3 into the top b prefix.
    prefix5_cswap(b,&[ee,a2],a0,h[0],dirty);
    b.ccx(ee,a2,h[0]); b.ccx(ee,a2,a0); b.ccx(ee,a2,a1);
    prefix5_cswap(b,&[ee,a0,a1],a2,h[1],dirty);
    b.x(a0); super::mask::mcx_dirty(b,&[ee,a1,a0],h[0],dirty); b.x(a0);
    prefix5_cswap(b,&[ee,a1],a0,h[2],dirty);
    b.ccx(ee,a1,a0);
    prefix5_cswap(b,&[ee,a0],a1,h[3],dirty);
    // a is now 0 or 1 on support. The old pair flag and a's upper bits land in h.
    b.cswap(ee,log[0],log[4]);
    for i in 0..4 { b.cswap(ee,h[i],log[i]); }
    prefix5_reflect(b,h);
}

/// ChäsRaffeli: 16-state cap log, all retained singles direct in four lanes.
/// Support (old,incoming)->code: (0,0..8)->0..8; (1,0)->9; (1,1)->10;
/// (1,2)->11; (2,0)->12; (2,1)->13; (3,0)->15; (4,0)->14.
/// Code bit 0 is the sum of overflow parities. Full map is reversible on all inputs.
/// Two external dirty loans and log3 are restored before the final nibble swap.
/// Cost: 48 Toffoli, including the two reflect gates and four controlled swaps.
pub(super) fn prefix4_push(b: &mut B, h: &[QubitId], log: &[QubitId], ee: QubitId, dirty: &[QubitId]) {
    assert!(h.len()>=4 && log.len()==4 && dirty.len()>=2);
    let (a0,a1,a2,a3)=(log[0],log[1],log[2],log[3]);
    let (c0,c1,c2,c3)=(h[0],h[1],h[2],h[3]);
    prefix5_reflect(b,h);
    // Encode: c0=b0^a0, c1=b1^a2^(a0*(a1^b0)), c2=b2^a1^a2,
    // c3=b3^a0^a1^a2^(a0*a1). On support a3=0 and a2 excludes a0/a1.
    b.cx(a1,c0); super::mask::mcx_dirty(b,&[ee,a0,c0],c1,dirty); b.cx(a1,c0);
    b.ccx(ee,a2,c1);
    b.cx(a1,a2); b.ccx(ee,a2,c2); b.cx(a1,a2);
    b.ccx(ee,a0,c0);
    b.cx(a0,a2); b.cx(a1,a2); b.ccx(a0,a1,a2);
    b.ccx(ee,a2,c3);
    b.ccx(a0,a1,a2); b.cx(a1,a2); b.cx(a0,a2);
    // Decode a0 from c: c3 * ((c0^c1)*!c2 ^ c0*c1).
    b.cx(c0,c1); b.x(c2);
    super::mask::mcx_dirty(b,&[ee,c3,c1,c2],a0,dirty);
    b.x(c2); b.cx(c0,c1);
    super::mask::mcx_dirty(b,&[ee,c3,c0,c1],a0,dirty);
    // Decode a2=[c=14], a1=c3*c2^[c=14], sharing the five-control toggle.
    let ds=[dirty[0],dirty[1],a3];
    b.cx(a2,a1); b.x(c0);
    super::mask::mcx_dirty(b,&[ee,c3,c2,c1,c0],a2,&ds);
    b.x(c0); b.cx(a2,a1);
    super::mask::mcx_dirty(b,&[ee,c3,c2],a1,dirty);
    for i in 0..4 { b.cswap(ee,h[i],log[i]); }
    prefix5_reflect(b,h);
}


/// hose847b G2: prefix4_push with log[3] hosted in the decoded Q0 lane z. a3 = 0 on support (old L at a cap), its
/// dirty-loan role goes to dirty[2]; the final cswap(ee, h3, log3) becomes the L write (z, h3) = (1, c3) ->
/// (1 ^ c3, 0) under ee (z = h5 ^ L_old ^ m = 1 at every event). +1 Toffoli.
pub(super) fn prefix4_push_hose(b: &mut B, h: &[QubitId], log: &[QubitId], ee: QubitId, dirty: &[QubitId], z: QubitId) {
    assert!(h.len()>=4 && log.len()==3 && dirty.len()>=3);
    let (a0,a1,a2)=(log[0],log[1],log[2]);
    let (c0,c1,c2,c3)=(h[0],h[1],h[2],h[3]);
    prefix5_reflect(b,h);
    b.cx(a1,c0); super::mask::mcx_dirty(b,&[ee,a0,c0],c1,&dirty[..2]); b.cx(a1,c0);
    b.ccx(ee,a2,c1);
    b.cx(a1,a2); b.ccx(ee,a2,c2); b.cx(a1,a2);
    b.ccx(ee,a0,c0);
    b.cx(a0,a2); b.cx(a1,a2); b.ccx(a0,a1,a2);
    b.ccx(ee,a2,c3);
    b.ccx(a0,a1,a2); b.cx(a1,a2); b.cx(a0,a2);
    b.cx(c0,c1); b.x(c2);
    super::mask::mcx_dirty(b,&[ee,c3,c1,c2],a0,&dirty[..2]);
    b.x(c2); b.cx(c0,c1);
    super::mask::mcx_dirty(b,&[ee,c3,c0,c1],a0,&dirty[..2]);
    let ds=[dirty[0],dirty[1],dirty[2]];
    b.cx(a2,a1); b.x(c0);
    super::mask::mcx_dirty(b,&[ee,c3,c2,c1,c0],a2,&ds);
    b.x(c0); b.cx(a2,a1);
    super::mask::mcx_dirty(b,&[ee,c3,c2],a1,&dirty[..2]);
    for i in 0..3 { b.cswap(ee,h[i],log[i]); }
    b.ccx(ee,h[3],z); b.x(z); b.ccx(ee,z,h[3]); b.x(z);
    prefix5_reflect(b,h);
}

/// Even-tick marker-blind cap, using Q0 temporarily decoded as h5.
/// On admitted inputs h' >= -26. The fictitious negative h=0/1 from a pending
/// marker is excluded by (h4 | h3 | h2). After clamping, E requires h2=1.
pub(super) fn h5q_cap(b: &mut B, w: &PWalk, sc: &PScr) {
    let q = w.capq;
    let h = &w.h;
    // frame846 O1b gate C: a Q slot lent as a clean lane (E_Y at t = S-1) is not also a dirty loan.
    let lent = |x: &QubitId| super::pointadd_lilypad::O1B_C && (sc.tmp.contains(x) || sc.sp.contains(x) || sc.pool.contains(x) || sc.d.contains(x));
    let qdirty:Vec<_>=w.q.iter().copied().filter(|x|!h.contains(x) && !lent(x)).collect();
    if q==11 && (HB==6 || HB==7) && c50_enabled(1) {
        let mut work=sc.tmp.clone();work.extend(&sc.sp);work.extend(&sc.pool);work.extend(&sc.d);
        if sc.tmp.is_empty() && sc.e != NO_E { work.push(sc.e); }
        let three = work.len() == 3;
        let two = work.len() == 2;
        let one = work.len() == 1;
        assert!(work.len()>=4 || three || two || one);
        let hose = w.log.len() == 3;
        assert!(!hose || two, "hose847b: the hosted cap needs the two-lane layout");
        if one {
            // Lane LILY-A: one clean lane. E = h5 ^ h5h4h3 ^ h5h4h1h2 ^ h5h4h1h2h3 and the clamp
            // h4 ^= E (h3 ^ h1h2 ^ h1h2h3) as multi-control toggles on dirty Q loans; E erased coherently.
            let ee = work[0];
            let (h1, h2, h3, h4, h5) = (h[1], h[2], h[3], h[4], h[HB - 1]);
            b.cx(h5, ee);
            for ctl in [vec![h5, h4, h3], vec![h5, h4, h1, h2], vec![h5, h4, h1, h2, h3]] {
                super::mask::mcx_dirty(b, &ctl, ee, &qdirty[..3]);
            }
            b.ccx(ee, h3, h4);
            super::mask::mcx_dirty(b, &[ee, h1, h2], h4, &qdirty[..1]);
            super::mask::mcx_dirty(b, &[ee, h1, h2, h3], h4, &qdirty[..2]);
            let marker_temps:Vec<_>=work.iter().copied().filter(|&x|x!=ee).collect();
            // Clamp never touches a fictitious marker (h=0/1), while every
            // real event now has h4=1. Correct E after releasing its chain.
            super::mask::mc_xor(b,&[(h[HB-1],false),(h[4],true),(h[3],true),(h[2],true)],ee,&marker_temps,&qdirty[..2]);
            if w.log.len()==3 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(3).collect(); prefix4_push_hose(b,h,&w.log,ee,&loans,h[HB-1]); } else if w.log.len()==4 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix4_push(b,h,&w.log,ee,&loans); } else if w.log.len()==5 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix5_push(b,h,&w.log,ee,&loans); } else {
            if w.log.len()==8 {for i in 0..4 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==7 {for i in 0..3 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==6 {for i in 0..2 {b.cswap(ee,w.log[i],w.log[4+i]);}}
            if w.log.len()==6 {b.cx(h[1],h[2]);} for i in 0..4 {b.cswap(ee,h[i],w.log[i]);} if w.log.len()==6 {b.cx(h[1],h[2]);}
            for j in [0usize,2] {b.cx(ee,h[j]);b.cx(ee,w.log[j]);}
            }
            assert!(sc.tmp.is_empty());
            if c50_enabled(128) {
                let receipt=C50_CAP_TAPES.with(|v|v.borrow_mut().pop().expect("inverse cap without forward E receipt"));
                b.z_if(ee,receipt);
            }
            super::mask::mc_xor(b, &[(h5, false), (h3, true), (h1, true), (h2,false)], ee, &[], &qdirty[..2]);
            return;
        }
        if two {
            // Lane LILY-A: two clean lanes. E = h5 & !(h4 & (h3 | c3)), c3 = h1 h2, by disjoint multi-control
            // toggles on dirty Q loans; the upper clamp h4 ^= E & (h3 | c3) likewise.
            let (ee, c3) = (work[0], work[1]);
            b.and_c(h[2],h[1],c3);
            if hose {
                // hose847b G2: E = sigma & (h4 ^ (h3 | h1 h2)) = [h' <= -11] on every post-update state; reads no h5.
                b.ccx(sc.sg, h[4], ee); b.ccx(sc.sg, h[3], ee); b.ccx(sc.sg, c3, ee);
                super::mask::mcx_dirty(b, &[sc.sg, h[3], c3], ee, &qdirty[..1]);
            } else {
            b.cx(h[HB - 1], ee);
            for ctl in [vec![h[HB - 1], h[4], h[3]], vec![h[HB - 1], h[4], c3], vec![h[HB - 1], h[4], h[3], c3]] {
                super::mask::mcx_dirty(b, &ctl, ee, &qdirty[..2]);
            }
            }
            b.ccx(ee, h[3], h[4]);
            b.ccx(ee, c3, h[4]);
            super::mask::mcx_dirty(b, &[ee, h[3], c3], h[4], &qdirty[..1]);
            b.and_u(h[2],h[1],c3);
            let marker_temps:Vec<_>=work.iter().copied().filter(|&x|x!=ee).collect();
            // Clamp never touches a fictitious marker (h=0/1), while every
            // real event now has h4=1. Correct E after releasing its chain.
            if !hose { super::mask::mc_xor(b,&[(h[HB-1],false),(h[4],true),(h[3],true),(h[2],true)],ee,&marker_temps,&qdirty[..2]); }
            if w.log.len()==3 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(3).collect(); prefix4_push_hose(b,h,&w.log,ee,&loans,h[HB-1]); } else if w.log.len()==4 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix4_push(b,h,&w.log,ee,&loans); } else if w.log.len()==5 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix5_push(b,h,&w.log,ee,&loans); } else {
            if w.log.len()==8 {for i in 0..4 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==7 {for i in 0..3 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==6 {for i in 0..2 {b.cswap(ee,w.log[i],w.log[4+i]);}}
            if w.log.len()==6 {b.cx(h[1],h[2]);} for i in 0..4 {b.cswap(ee,h[i],w.log[i]);} if w.log.len()==6 {b.cx(h[1],h[2]);}
            for j in [0usize,2] {b.cx(ee,h[j]);b.cx(ee,w.log[j]);}
            }
            assert!(sc.tmp.is_empty());
            if c50_enabled(128) {
                let receipt=C50_CAP_TAPES.with(|v|v.borrow_mut().pop().expect("inverse cap without forward E receipt"));
                b.z_if(ee,receipt);
            }
            let etop = if hose { sc.sg } else { h[HB - 1] };
            super::mask::mc_xor(b,&[(etop,false),(h[3],true),(h[1],true),(h[2],false)],ee,&[c3],&qdirty[..2]);
            return;
        }
        if three {
            // Lane LILY-A: three clean lanes. E = h5 & !(h4 & (h3 | h1 h2)) formed directly on its lane (one
            // three-control toggle on a dirty Q loan), the upper clamp h4 ^= E & (h3 | h1 h2) by one Toffoli.
            let (ee, c3, c4) = (work[0], work[1], work[2]);
            b.and_c(h[2],h[1],c3);
            b.x(h[3]);b.x(c3);b.and_c(h[3],c3,c4);b.x(c3);b.x(h[3]);b.x(c4);
            b.cx(h[HB - 1], ee);
            super::mask::mc_xor(b, &[(h[HB - 1], false), (h[4], false), (c4, false)], ee, &[], &qdirty[..1]);
            b.ccx(ee, c4, h[4]);
            b.x(c4);b.x(h[3]);b.x(c3);b.and_u(h[3],c3,c4);b.x(c3);b.x(h[3]);
            b.and_u(h[2],h[1],c3);
            let marker_temps:Vec<_>=work.iter().copied().filter(|&x|x!=ee).collect();
            // Clamp never touches a fictitious marker (h=0/1), while every
            // real event now has h4=1. Correct E after releasing its chain.
            super::mask::mc_xor(b,&[(h[HB-1],false),(h[4],true),(h[3],true),(h[2],true)],ee,&marker_temps,&qdirty[..2]);
            if w.log.len()==3 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(3).collect(); prefix4_push_hose(b,h,&w.log,ee,&loans,h[HB-1]); } else if w.log.len()==4 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix4_push(b,h,&w.log,ee,&loans); } else if w.log.len()==5 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix5_push(b,h,&w.log,ee,&loans); } else {
            if w.log.len()==8 {for i in 0..4 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==7 {for i in 0..3 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==6 {for i in 0..2 {b.cswap(ee,w.log[i],w.log[4+i]);}}
            if w.log.len()==6 {b.cx(h[1],h[2]);} for i in 0..4 {b.cswap(ee,h[i],w.log[i]);} if w.log.len()==6 {b.cx(h[1],h[2]);}
            for j in [0usize,2] {b.cx(ee,h[j]);b.cx(ee,w.log[j]);}
            }
            assert!(sc.tmp.is_empty());
            if c50_enabled(128) {
                let receipt=C50_CAP_TAPES.with(|v|v.borrow_mut().pop().expect("inverse cap without forward E receipt"));
                b.z_if(ee,receipt);
            }
            b.mbu_erase(ee,&[(h[HB - 1],false),(h[3],true),(h[1],true),(h[2],false)],&[c3,c4]);
            return;
        }
        // c5 was erased before gated is formed, so both values share a lane.
        let (c3,c4,c5,ee,gated)=(work[0],work[1],work[2],work[3],if work.len()>=5{work[4]}else{work[2]});
        // Carry chain shared by threshold and upper clamp; erase before low payload exchange.
        b.and_c(h[2],h[1],c3);
        b.x(h[3]);b.x(c3);b.and_c(h[3],c3,c4);b.x(c3);b.x(h[3]);b.x(c4);
        b.and_c(h[4],c4,c5);
        b.x(c5);b.and_c(h[HB - 1],c5,ee);b.x(c5);
        b.and_u(h[4],c4,c5);
        b.x(c4);b.and_c(ee,c4,gated);b.x(c4);
        b.cx(gated,h[4]);b.cx(ee,h[4]);
        b.x(c4);b.and_u(ee,c4,gated);b.x(c4);
        b.x(c4);b.x(h[3]);b.x(c3);b.and_u(h[3],c3,c4);b.x(c3);b.x(h[3]);
        b.and_u(h[2],h[1],c3);
        let marker_temps:Vec<_>=work.iter().copied().filter(|&x|x!=ee).collect();
            // Clamp never touches a fictitious marker (h=0/1), while every
            // real event now has h4=1. Correct E after releasing its chain.
            super::mask::mc_xor(b,&[(h[HB-1],false),(h[4],true),(h[3],true),(h[2],true)],ee,&marker_temps,&qdirty[..2]);
            if w.log.len()==3 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(3).collect(); prefix4_push_hose(b,h,&w.log,ee,&loans,h[HB-1]); } else if w.log.len()==4 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix4_push(b,h,&w.log,ee,&loans); } else if w.log.len()==5 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix5_push(b,h,&w.log,ee,&loans); } else {
        if w.log.len()==8 {for i in 0..4 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==7 {for i in 0..3 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==6 {for i in 0..2 {b.cswap(ee,w.log[i],w.log[4+i]);}}
        if w.log.len()==6 {b.cx(h[1],h[2]);} for i in 0..4 {b.cswap(ee,h[i],w.log[i]);} if w.log.len()==6 {b.cx(h[1],h[2]);}
        for j in [0usize,2] {b.cx(ee,h[j]);b.cx(ee,w.log[j]);}
        }
        // E=[h_new=-11] on the old empty-slot success support.
        if c50_enabled(128) && !sc.tmp.is_empty() {
            // Forward-only, outside all recordings: defer the E phase to its inverse cap.
            let receipt=b.fresh_bits(1)[0];b.hmr_to(ee,receipt);
            C50_CAP_TAPES.with(|v|v.borrow_mut().push(receipt));
        }else{
            if c50_enabled(128) {
                let receipt=C50_CAP_TAPES.with(|v|v.borrow_mut().pop().expect("inverse cap without forward E receipt"));
                // In inverse playback MbuC runs first, then this phase is repaid.
                b.z_if(ee,receipt);
            }
            b.mbu_erase(ee,&[(h[HB - 1],false),(h[3],true),(h[1],true),(h[2],false)],&[c3,c4]);
        }
        return;
    }
    unreachable!("H5Q cap requires q11");
}

/// patchF: the forward cap on two clean lanes (sc.tmp = [ee, c4]) plus two dirty lanes `fd` of an idle external
/// register: the same E = h5 & !(h4 & (h3 | h1 h2)), upper clamp h4 ^= E & (h3 | h1 h2), prefix4_push and forward E
/// receipt as cap_logic's >= 4-lane forward path (py/cap2_check.py, exhaustive 64/64 up to the shared push).
pub(super) fn cap_logic_fwd2(b: &mut B, w: &PWalk, sc: &PScr, fd: &[QubitId]) {
    let h = &w.h;
    assert!(w.capq == 11 && HB == 6 && h.len() == HB && w.log.len() == 4 && c50_enabled(1) && c50_enabled(128));
    assert!(sc.tmp.len() == 2 && sc.sp.is_empty() && sc.pool.is_empty() && sc.d.is_empty() && w.q.is_empty() && fd.len() >= 2);
    let (ee, c4) = (sc.tmp[0], sc.tmp[1]);
    assert!(fd.iter().all(|q| !h.contains(q) && !w.log.contains(q) && *q != ee && *q != c4));
    // c3 = h1 h2 (on ee), c4 = h3 | c3, c3 erased (h1, h2 unchanged).
    b.and_c(h[2], h[1], ee);
    b.x(h[3]); b.x(ee); b.and_c(h[3], ee, c4); b.x(ee); b.x(h[3]); b.x(c4);
    b.and_u(h[2], h[1], ee);
    // E = h5 ^ h5 h4 c4 on ee (pre-clamp h4), then the upper clamp.
    b.cx(h[HB - 1], ee);
    super::mask::mcx_dirty(b, &[h[HB - 1], h[4], c4], ee, &fd[..1]);
    b.ccx(ee, c4, h[4]);
    // c4 = h3 ^ h1 h2 ^ h1 h2 h3 cleared (h1..h3 unchanged by the clamp).
    b.cx(h[3], c4);
    b.ccx(h[1], h[2], c4);
    super::mask::mcx_dirty(b, &[h[1], h[2], h[3]], c4, &fd[..1]);
    prefix4_push(b, h, &w.log, ee, &fd[..2]);
    // Forward-only, outside all recordings: defer the E phase to its inverse cap (as cap_logic's forward path).
    let receipt = b.fresh_bits(1)[0];
    b.hmr_to(ee, receipt);
    C50_CAP_TAPES.with(|v| v.borrow_mut().push(receipt));
}

/// Run cap (after h' is formed, sigma live): E = sigma & [h' <= -q]; push o = -q - h' (4 bits) on the log, h' <- -q.
pub(super) fn cap_logic(b: &mut B, w: &PWalk, sc: &PScr) {
    let q = w.capq;
    let h = &w.h;
    let qdirty:Vec<_>=w.q.iter().copied().filter(|x|!h.contains(x)).collect();
    if q==11 && (HB==6 || HB==7) && c50_enabled(1) {
        let mut work=sc.tmp.clone();work.extend(&sc.sp);work.extend(&sc.pool);work.extend(&sc.d);
        if sc.tmp.is_empty() && sc.e != NO_E { work.push(sc.e); }
        let three = work.len() == 3;
        let two = work.len() == 2;
        let one = work.len() == 1;
        assert!(work.len()>=4 || three || two || one);
        let hose = w.log.len() == 3;
        assert!(!hose || two, "hose847b: the hosted cap needs the two-lane layout");
        if one {
            // Lane LILY-A: one clean lane. E = h5 ^ h5h4h3 ^ h5h4h1h2 ^ h5h4h1h2h3 and the clamp
            // h4 ^= E (h3 ^ h1h2 ^ h1h2h3) as multi-control toggles on dirty Q loans; E erased coherently.
            let ee = work[0];
            let (h1, h2, h3, h4, h5) = (h[1], h[2], h[3], h[4], h[HB - 1]);
            b.cx(h5, ee);
            for ctl in [vec![h5, h4, h3], vec![h5, h4, h1, h2], vec![h5, h4, h1, h2, h3]] {
                super::mask::mcx_dirty(b, &ctl, ee, &qdirty[..3]);
            }
            b.ccx(ee, h3, h4);
            super::mask::mcx_dirty(b, &[ee, h1, h2], h4, &qdirty[..1]);
            super::mask::mcx_dirty(b, &[ee, h1, h2, h3], h4, &qdirty[..2]);
            if w.log.len()==3 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(3).collect(); prefix4_push_hose(b,h,&w.log,ee,&loans,h[HB-1]); } else if w.log.len()==4 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix4_push(b,h,&w.log,ee,&loans); } else if w.log.len()==5 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix5_push(b,h,&w.log,ee,&loans); } else {
            if w.log.len()==8 {for i in 0..4 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==7 {for i in 0..3 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==6 {for i in 0..2 {b.cswap(ee,w.log[i],w.log[4+i]);}}
            if w.log.len()==6 {b.cx(h[1],h[2]);} for i in 0..4 {b.cswap(ee,h[i],w.log[i]);} if w.log.len()==6 {b.cx(h[1],h[2]);}
            for j in [0usize,2] {b.cx(ee,h[j]);b.cx(ee,w.log[j]);}
            }
            assert!(sc.tmp.is_empty());
            if c50_enabled(128) {
                let receipt=C50_CAP_TAPES.with(|v|v.borrow_mut().pop().expect("inverse cap without forward E receipt"));
                b.z_if(ee,receipt);
            }
            super::mask::mc_xor(b, &[(h5, false), (h3, true), (h1, true)], ee, &[], &qdirty[..1]);
            return;
        }
        if two {
            // Lane LILY-A: two clean lanes. E = h5 & !(h4 & (h3 | c3)), c3 = h1 h2, by disjoint multi-control
            // toggles on dirty Q loans; the upper clamp h4 ^= E & (h3 | c3) likewise.
            let (ee, c3) = (work[0], work[1]);
            b.and_c(h[2],h[1],c3);
            if hose {
                // hose847b G2: E = sigma & (h4 ^ (h3 | h1 h2)) = [h' <= -11] on every post-update state; reads no h5.
                b.ccx(sc.sg, h[4], ee); b.ccx(sc.sg, h[3], ee); b.ccx(sc.sg, c3, ee);
                super::mask::mcx_dirty(b, &[sc.sg, h[3], c3], ee, &qdirty[..1]);
            } else {
            b.cx(h[HB - 1], ee);
            for ctl in [vec![h[HB - 1], h[4], h[3]], vec![h[HB - 1], h[4], c3], vec![h[HB - 1], h[4], h[3], c3]] {
                super::mask::mcx_dirty(b, &ctl, ee, &qdirty[..2]);
            }
            }
            b.ccx(ee, h[3], h[4]);
            b.ccx(ee, c3, h[4]);
            super::mask::mcx_dirty(b, &[ee, h[3], c3], h[4], &qdirty[..1]);
            b.and_u(h[2],h[1],c3);
            if w.log.len()==3 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(3).collect(); prefix4_push_hose(b,h,&w.log,ee,&loans,h[HB-1]); } else if w.log.len()==4 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix4_push(b,h,&w.log,ee,&loans); } else if w.log.len()==5 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix5_push(b,h,&w.log,ee,&loans); } else {
            if w.log.len()==8 {for i in 0..4 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==7 {for i in 0..3 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==6 {for i in 0..2 {b.cswap(ee,w.log[i],w.log[4+i]);}}
            if w.log.len()==6 {b.cx(h[1],h[2]);} for i in 0..4 {b.cswap(ee,h[i],w.log[i]);} if w.log.len()==6 {b.cx(h[1],h[2]);}
            for j in [0usize,2] {b.cx(ee,h[j]);b.cx(ee,w.log[j]);}
            }
            assert!(sc.tmp.is_empty());
            if c50_enabled(128) {
                let receipt=C50_CAP_TAPES.with(|v|v.borrow_mut().pop().expect("inverse cap without forward E receipt"));
                b.z_if(ee,receipt);
            }
            if hose { super::mask::mc_xor(b,&[(sc.sg,false),(h[3],true),(h[1],true),(h[2],false)],ee,&[c3],&qdirty[..2]); }
            else { b.mbu_erase(ee,&[(h[HB - 1],false),(h[3],true),(h[1],true)],&[c3]); }
            return;
        }
        if three {
            // Lane LILY-A: three clean lanes. E = h5 & !(h4 & (h3 | h1 h2)) formed directly on its lane (one
            // three-control toggle on a dirty Q loan), the upper clamp h4 ^= E & (h3 | h1 h2) by one Toffoli.
            let (ee, c3, c4) = (work[0], work[1], work[2]);
            b.and_c(h[2],h[1],c3);
            b.x(h[3]);b.x(c3);b.and_c(h[3],c3,c4);b.x(c3);b.x(h[3]);b.x(c4);
            b.cx(h[HB - 1], ee);
            super::mask::mc_xor(b, &[(h[HB - 1], false), (h[4], false), (c4, false)], ee, &[], &qdirty[..1]);
            b.ccx(ee, c4, h[4]);
            b.x(c4);b.x(h[3]);b.x(c3);b.and_u(h[3],c3,c4);b.x(c3);b.x(h[3]);
            b.and_u(h[2],h[1],c3);
            if w.log.len()==3 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(3).collect(); prefix4_push_hose(b,h,&w.log,ee,&loans,h[HB-1]); } else if w.log.len()==4 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix4_push(b,h,&w.log,ee,&loans); } else if w.log.len()==5 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix5_push(b,h,&w.log,ee,&loans); } else {
            if w.log.len()==8 {for i in 0..4 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==7 {for i in 0..3 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==6 {for i in 0..2 {b.cswap(ee,w.log[i],w.log[4+i]);}}
            if w.log.len()==6 {b.cx(h[1],h[2]);} for i in 0..4 {b.cswap(ee,h[i],w.log[i]);} if w.log.len()==6 {b.cx(h[1],h[2]);}
            for j in [0usize,2] {b.cx(ee,h[j]);b.cx(ee,w.log[j]);}
            }
            assert!(sc.tmp.is_empty());
            if c50_enabled(128) {
                let receipt=C50_CAP_TAPES.with(|v|v.borrow_mut().pop().expect("inverse cap without forward E receipt"));
                b.z_if(ee,receipt);
            }
            b.mbu_erase(ee,&[(h[HB - 1],false),(h[3],true),(h[1],true)],&[c3]);
            return;
        }
        // c5 was erased before gated is formed, so both values share a lane.
        let (c3,c4,c5,ee,gated)=(work[0],work[1],work[2],work[3],if work.len()>=5{work[4]}else{work[2]});
        // Carry chain shared by threshold and upper clamp; erase before low payload exchange.
        b.and_c(h[2],h[1],c3);
        b.x(h[3]);b.x(c3);b.and_c(h[3],c3,c4);b.x(c3);b.x(h[3]);b.x(c4);
        b.and_c(h[4],c4,c5);
        b.x(c5);b.and_c(h[HB - 1],c5,ee);b.x(c5);
        b.and_u(h[4],c4,c5);
        b.x(c4);b.and_c(ee,c4,gated);b.x(c4);
        b.cx(gated,h[4]);b.cx(ee,h[4]);
        b.x(c4);b.and_u(ee,c4,gated);b.x(c4);
        b.x(c4);b.x(h[3]);b.x(c3);b.and_u(h[3],c3,c4);b.x(c3);b.x(h[3]);
        b.and_u(h[2],h[1],c3);
        if w.log.len()==3 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(3).collect(); prefix4_push_hose(b,h,&w.log,ee,&loans,h[HB-1]); } else if w.log.len()==4 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix4_push(b,h,&w.log,ee,&loans); } else if w.log.len()==5 { let loans:Vec<_>=qdirty.iter().chain(work.iter()).copied().filter(|&q|q!=ee).take(2).collect(); prefix5_push(b,h,&w.log,ee,&loans); } else {
        if w.log.len()==8 {for i in 0..4 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==7 {for i in 0..3 {b.cswap(ee,w.log[i],w.log[4+i]);}} else if w.log.len()==6 {for i in 0..2 {b.cswap(ee,w.log[i],w.log[4+i]);}}
        if w.log.len()==6 {b.cx(h[1],h[2]);} for i in 0..4 {b.cswap(ee,h[i],w.log[i]);} if w.log.len()==6 {b.cx(h[1],h[2]);}
        for j in [0usize,2] {b.cx(ee,h[j]);b.cx(ee,w.log[j]);}
        }
        // E=[h_new=-11] on the old empty-slot success support.
        if c50_enabled(128) && !sc.tmp.is_empty() {
            // Forward-only, outside all recordings: defer the E phase to its inverse cap.
            let receipt=b.fresh_bits(1)[0];b.hmr_to(ee,receipt);
            C50_CAP_TAPES.with(|v|v.borrow_mut().push(receipt));
        }else{
            if c50_enabled(128) {
                let receipt=C50_CAP_TAPES.with(|v|v.borrow_mut().pop().expect("inverse cap without forward E receipt"));
                // In inverse playback MbuC runs first, then this phase is repaid.
                b.z_if(ee,receipt);
            }
            b.mbu_erase(ee,&[(h[HB - 1],false),(h[3],true),(h[1],true)],&[c3]);
        }
        return;
    }
    let mut work = sc.tmp.clone();
    work.extend(&sc.sp);
    work.extend(&sc.pool);
    // In inverse regeneration the deferral flag is still clean here; its
    // eraser lifetime starts only after the cap update.
    work.extend(&sc.d);
    // Empty tmp is the inverse G layout; its digit is in Q, leaving e clean.
    if sc.tmp.is_empty() {
        assert_eq!(sc.sp.len(), SB);
        assert_eq!(sc.d.len(), 1);
        work.push(sc.e);
    }
    assert!(work.len() >= 6, "cap logic needs six clean work lanes");
    assert!(w.log.len() >= 7, "LILY-ABER: the 6-lane log exists only on the q == 11 cap path");
    let compact = work.len() < NT;
    let tm = &work[..work.len().min(NT)];
    let (ee, lt) = if compact { (tm[5], tm[0]) } else { (tm[0], tm[1]) };
    let s0 = &w.log[0..4];
    b.begin();
    // The cap itself keeps negative h in the audited six-bit range.  Clamp
    // those low six bits exactly as before, but guard with the true seventh
    // sign bit so large positive h is never mistaken for a negative value.
    if compact {
        b.cmp_compute(&h[..5], (33 - q) as u64, lt, &tm[1..5]);
        super::mask::mc_xor(
            b,
            &[(sc.sg, false), (h[HB - 1], false), (lt, false)],
            ee,
            &[],
            &[w.log[w.log.len() - 1]],
        );
        b.cmp_erase(&h[..5], (33 - q) as u64, lt, &tm[1..5]);
    } else {
        let sh = tm[6];
        b.cmp_compute(&h[..5], (33 - q) as u64, lt, &tm[2..6]);
        b.and_c(sc.sg, h[HB - 1], sh);
        b.and_c(sh, lt, ee);
    }
    let er = b.end();
    b.play(&er, false);
    if w.log.len() == 8 {
        for i in 0..4 {
            b.cswap(ee, w.log[i], w.log[4 + i]);
        }
    } else if w.log.len() == 7 {
        for i in 0..3 {
            b.cswap(ee, w.log[i], w.log[4 + i]);
        }
    }
    if l4_enabled() {
        // Store low4(h') by a controlled swap, then clamp h' to -q using
        // Clifford fixes and one [low4(h') <= low4(-q)] comparison.
        for i in 0..4 {
            if !l4_neg(2) {
                b.cswap(ee, h[i], s0[i]);
            }
        }
        let modulus = 1i64 << HB;
        let cq = ((-(q as i64)) % modulus + modulus) % modulus;
        let upper = |low: i64| {
            (((-(q as i64) - ((-(q as i64) - low) % 16 + 16) % 16) % modulus + modulus) % modulus) >> 4
        };
        let (upper_a, upper_b) = (upper(0), upper(15));
        let low_const = cq & 15;
        let fixed = (upper_b << 4) ^ cq;
        for j in 0..HB {
            if (fixed >> j) & 1 == 1 {
                b.cx(ee, h[j]);
            }
        }
        if upper_a != upper_b && !l4_neg(3) {
            let (flag, gated, ctemps) = if compact {
                (tm[0], tm[1], &tm[2..5])
            } else {
                (tm[7], tm[5], &tm[2..5])
            };
            b.begin();
            b.cmp_compute(s0, (low_const + 1) as u64, flag, ctemps);
            b.and_c(ee, flag, gated);
            let fix = b.end();
            b.play(&fix, false);
            for j in 4..HB {
                if ((upper_a ^ upper_b) >> (j - 4)) & 1 == 1 {
                    b.cx(gated, h[j]);
                }
            }
            b.play(&fix, true);
        }
        // Mandatory parity/empty-slot repair: store low4(h') xor low4(-q).
        // Without this, odd-q pushes flip the endpoint rho invariant and a
        // benign third push no longer leaves an empty log slot.
        if !l4_neg(1) {
            for j in 0..4 {
                if (low_const >> j) & 1 == 1 {
                    b.cx(ee, s0[j]);
                }
            }
        }
        b.play(&er, true);
        return;
    }
    assert!(!compact, "legacy cap fallback needs the eight-lane workspace");
    // o = (-q - h') mod 16 = (~h' + 1 - q) mod 16 on tm[2..6]
    let o = &tm[2..6];
    let k = ((17 - (q % 16)) % 16) as u64;
    let mut carries = vec![tm[7]];
    carries.extend(&sc.pool);
    b.begin();
    for i in 0..4 {
        b.cx(h[i], o[i]);
        b.x(o[i]);
    }
    for j in 0..4 {
        if (k >> j) & 1 == 1 {
            inc_unctl(b, &o[j..], &carries);
        }
    }
    let orc = b.end();
    b.play(&orc, false);
    for i in 0..4 {
        b.ccx(ee, o[i], s0[i]);
    }
    b.play(&orc, true);
    // h' += o under E (source = slot 0 zero-extended)
    let mut a: Vec<QubitId> = s0.to_vec();
    a.extend([tm[2], tm[3]]);
    let mut pl: Vec<QubitId> = tm[4..6].to_vec();
    pl.push(tm[7]);
    pl.extend(&sc.pool);
    ctrl_add_pool(b, &a, &h[..6], ee, &pl);
    b.play(&er, true);
}

/// Halve of tick t, the delta update and the sigma decode (sigma -> |0>).
pub fn halve_h(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr) {
    sec(b, "lily.hv", |b| {
        fix_boundary(b, &|f| w.af(t + 1, f), sch.c[t] - 1, sch.c[t + 1]);
        fix_boundary(b, &|f| w.bf(f), sch.c[t], sch.c[t + 1]);
        for &x in &w.h {
            b.cx(sc.sg, x);
        }
        inc_unctl(b, &w.h, &sc.tmp);
    });
    if w.capq > 0 {
        sec(b, "lily.cap", |b| cap_logic(b, w, sc));
    }
    b.cx(w.asig(t + 1, 1), sc.sg);
}

/// ic = 0 marker clear (odd ticks): Q[QB-1] ^= [h = 0] & X.c[1].
pub(super) fn mclear(b: &mut B, w: &PWalk, t: usize, sc: &PScr, half_cofactor: bool) {
    let q = w.qfr(t);
    let qb = q.len();
    let lits: Vec<(QubitId, bool)> = w.h.iter().map(|&x| (x, true)).collect();
    let cf1 = w.asig(t + 1, 1 - usize::from(half_cofactor));
    if sc.tmp.len() <= 1 {
        // halve_g has already decoded and cleared sigma on this odd tick.
        let z0 = sc.tmp.first().copied().unwrap_or(sc.sg);
        let y = sc.d[0];
        sec(b, "lily.mclr", |b| {
            let mut temps = sc.sp.clone();
            temps.push(sc.e);
            b.mbu_compute(z0, &lits, &temps);
            b.and_c(z0, cf1, y);
            b.cx(y, q[qb - 1]);
            b.and_u(z0, cf1, y);
            b.mbu_erase(z0, &lits, &temps);
        });
        return;
    }
    let (z0, y) = (sc.tmp[0], sc.tmp[1]);
    sec(b, "lily.mclr", |b| {
        let mut temps = sc.tmp[2..].to_vec();
        temps.extend(&sc.sp);
        temps.extend(&sc.pool);
        temps.extend(&sc.d);
        b.mbu_compute(z0, &lits, &temps);
        b.and_c(z0, cf1, y);
        b.cx(y, q[qb - 1]);
        b.and_u(z0, cf1, y);
        b.mbu_erase(z0, &lits, &temps);
    });
}

fn norm_need(qb: usize, k: usize) -> usize {
    let rest = |gp: usize| if k >= 2 { gp & ((1 << k) - 1) } else { gp & 3 };
    (0..qb - 1).filter(|&gp| k < 2 || (gp >> k) & 1 == 1).map(|gp| gp + 2 + rest(gp)).max().unwrap_or(0)
}

/// Lanes of the eraser window (X.c sig 2..) the normalizer can read.
pub fn win_len(qb: usize) -> usize {
    let mut m = norm_need(qb, 1);
    for k in 2..SB {
        let n = norm_need(qb, k);
        if n > 0 {
            m = m.max(n + (1 << k));
        }
    }
    m.max(qb)
}

/// Decode the only three high groups reachable by a 12-lane completing word.
///
/// `out[d] = e & [g4:g3:g2 = d]` for `d = 0..3`.  The fourth lane is the
/// decision-tree witness `w`; all four lanes start and end clean.  Groups 3
/// and 4 from the generic decoder cannot be consumed by `finish_mask` when
/// `q.len() == 12`, so synthesizing them would only lengthen the live scratch
/// set at the inverse-walk peak.
pub(crate) fn decode3_high_lilypad(
    b: &mut B,
    g2: QubitId,
    g3: QubitId,
    g4: QubitId,
    e: QubitId,
    out: &[QubitId],
    w: QubitId,
) {
    assert_eq!(out.len(), 3);
    // p=e&!g4, u=p&g2, v=p&g3, w=u&g3.
    b.x(g4);
    b.and_c(e, g4, out[0]);
    b.x(g4);
    b.and_c(out[0], g2, out[1]);
    b.and_c(out[0], g3, out[2]);
    b.and_c(out[1], g3, w);

    // H0=p^u^v^w, H1=u^w, H2=v^w.
    b.cx(out[1], out[0]);
    b.cx(out[2], out[0]);
    b.cx(w, out[0]);
    b.cx(w, out[1]);
    b.cx(w, out[2]);
}

pub(crate) fn clear_decode3_high_lilypad(
    b: &mut B,
    g2: QubitId,
    g3: QubitId,
    g4: QubitId,
    e: QubitId,
    out: &[QubitId],
    w: QubitId,
) {
    assert_eq!(out.len(), 3);
    b.cx(w, out[2]);
    b.cx(w, out[1]);
    b.cx(w, out[0]);
    b.cx(out[2], out[0]);
    b.cx(out[1], out[0]);
    b.and_u(out[1], g3, w);
    b.and_u(out[0], g3, out[2]);
    b.and_u(out[0], g2, out[1]);
    b.x(g4);
    b.and_u(e, g4, out[0]);
    b.x(g4);
}

fn low_eq_lilypad(b: &mut B, g0: QubitId, g1: QubitId, digit: usize, out: QubitId, compute: bool) {
    if digit & 1 == 0 {
        b.x(g0);
    }
    if digit & 2 == 0 {
        b.x(g1);
    }
    if compute {
        b.and_c(g0, g1, out);
    } else {
        b.and_u(g0, g1, out);
    }
    if digit & 2 == 0 {
        b.x(g1);
    }
    if digit & 1 == 0 {
        b.x(g0);
    }
}

/// target ^= a & b & c with one borrowed dirty lane, restored exactly.
fn three_lit_toggle_dirty(
    b: &mut B,
    target: QubitId,
    lits: &[(QubitId, bool); 3],
    dirty: QubitId,
) {
    for &(q, neg) in lits {
        if neg {
            b.x(q);
        }
    }
    b.ccx(lits[0].0, lits[1].0, dirty);
    b.ccx(dirty, lits[2].0, target);
    b.ccx(lits[0].0, lits[1].0, dirty);
    b.ccx(dirty, lits[2].0, target);
    for &(q, neg) in lits.iter().rev() {
        if neg {
            b.x(q);
        }
    }
}

/// Four-bit controlled decrement with no clean carry lanes.  The two borrowed
/// dirty lanes are restored by the Barenco controls.
fn dec4_dirty(b: &mut B, ctl: QubitId, bits: &[QubitId], dirty: &[QubitId]) {
    assert_eq!(bits.len(), 4);
    super::mask::mc_xor(
        b,
        &[(ctl, false), (bits[0], true), (bits[1], true), (bits[2], true)],
        bits[3],
        &[],
        dirty,
    );
    super::mask::mc_xor(
        b,
        &[(ctl, false), (bits[0], true), (bits[1], true)],
        bits[2],
        &[],
        dirty,
    );
    b.x(bits[0]);
    b.ccx(ctl, bits[0], bits[1]);
    b.x(bits[0]);
    b.cx(ctl, bits[0]);
}

/// Running-mask toggle using low one-hot values held as affine views of
/// the original data owners: g0=L1, g1=L2, low=L3, L0=1^L1^L2^L3.
fn toggle_low_view(b:&mut B,hi:QubitId,g:&[QubitId],low:QubitId,f:QubitId,digit:usize) {
    match digit {
        0=>{
            b.x(low);b.cx(g[0],low);b.cx(g[1],low);
            b.ccx(hi,low,f);
            b.cx(g[1],low);b.cx(g[0],low);b.x(low);
        },
        1=>b.ccx(hi,g[0],f),
        2=>b.ccx(hi,g[1],f),
        3=>b.ccx(hi,low,f),
        _=>unreachable!(),
    }
}

/// Completing word's mask.  L5's 12-lane core has only high groups H0..H2,
/// so the exact three-high decoder needs one clean pool lane instead of the
/// generic five-high decoder's six.
#[allow(clippy::too_many_arguments)]
pub(super) fn finish_mask(
    b: &mut B,
    q: &[QubitId],
    bsig: &[QubitId],
    g: &[QubitId],
    e: QubitId,
    tmp: &[QubitId],
    pool: &[QubitId],
    dirty: Option<QubitId>,
) {
    let qb = q.len();
    assert!(qb <= 21);
    b.cx(e, q[qb - 2]);
    if bsig[1] != NO_V1 {
        b.ccx(e, bsig[1], q[qb - 1]);
    }
    let compact = qb == 12;
    let one_temp = compact && tmp.len() == 1;
    if one_temp && pool.len() >= 4 {
        let f=tmp[0];
        let (p,qh,w,loan)=(pool[0],pool[1],pool[2],pool[3]);
        assert!(![p,qh,w,loan].contains(&f));
        // Three exact high groups: H0=e*!g2*!g3, H1=e*g2*!g3,
        // H2=e*!g2*g3. Keep their shared p and q witnesses in-place.
        b.x(g[2]); b.and_c(e,g[2],p); b.x(g[2]);
        b.x(g[3]); b.and_c(e,g[3],qh); b.and_c(p,g[3],w); b.x(g[3]);
        b.cx(w,p); b.cx(w,qh);
        let high=[w,qh,p];
        b.and_c(g[0],g[1],loan);
        b.cx(loan,g[0]);b.cx(loan,g[1]);
        b.cx(e,f);
        for c in 0..3 {
            for l in 4*c..(4*c+4).min(qb-1) {
                toggle_low_view(b,high[c],g,loan,f,l&3);
                if l+2<qb {mterm(b,f,bsig[l+2],q[l]);}
            }
        }
        b.cx(loan,g[1]);b.cx(loan,g[0]);
        b.and_u(g[0],g[1],loan);
        b.cx(w,qh); b.cx(w,p);
        b.x(g[3]); b.and_u(p,g[3],w); b.and_u(e,g[3],qh); b.x(g[3]);
        b.x(g[2]); b.and_u(e,g[2],p); b.x(g[2]);
        return;
    }
    if one_temp && pool.len() == 3 {
        let (f,p,hi,loan)=(tmp[0],pool[0],pool[1],pool[2]);
        // Share e*!g3 across H0 and H1; recycle its lane for H2's MBU prefix.
        b.x(g[3]); b.and_c(e,g[3],p); b.x(g[3]);
        b.x(g[2]); b.and_c(p,g[2],hi); b.x(g[2]);
        b.and_c(g[0],g[1],loan);
        b.cx(loan,g[0]);b.cx(loan,g[1]);
        b.cx(e,f);
        for c in 0..2 {
            for l in 4*c..4*c+4 {
                toggle_low_view(b,hi,g,loan,f,l&3);
                mterm(b,f,bsig[l+2],q[l]);
            }
            if c==0 {b.cx(p,hi);}
        }
        b.and_u(p,g[2],hi);
        b.x(g[3]); b.and_u(e,g[3],p); b.x(g[3]);
        let high=[(e,false),(g[2],true),(g[3],false)];
        b.mbu_compute(hi,&high,&[p]);
        for l in 8..qb-1 {
            toggle_low_view(b,hi,g,loan,f,l&3);
            if l+2<qb {mterm(b,f,bsig[l+2],q[l]);}
        }
        b.mbu_erase(hi,&high,&[p]);
        b.cx(loan,g[1]);b.cx(loan,g[0]);
        b.and_u(g[0],g[1],loan);
        return;
    }
    if one_temp && pool.len() >= 2 {
        let (f, hi) = (tmp[0], pool[0]);
        // MbuC and MbuU return their prefix temp clean. Between those calls,
        // loan that same temp to each low toggle, returning it after each use.
        let loan = pool[1];
        assert!(loan != f && loan != hi && loan != e
            && !g.contains(&loan) && !q.contains(&loan) && !bsig.contains(&loan),
            "mask prefix loan aliases a live port");
        b.cx(e, f);
        for c in 0..3 {
            let high = [
                (e, false),
                (g[2], c & 1 == 0),
                (g[3], c & 2 == 0),
            ];
            b.mbu_compute(hi, &high, &pool[1..2]);
            for l in 4 * c..(4 * c + 4).min(qb - 1) {
                let low = [
                    (hi, false),
                    (g[0], l & 1 == 0),
                    (g[1], l & 2 == 0),
                ];
                super::mask::mc_xor(b, &low, f, &pool[1..2], &q[..1]);
                if l + 2 < qb {
                    mterm(b, f, bsig[l + 2], q[l]);
                }
            }
            b.mbu_erase(hi, &high, &pool[1..2]);
        }
        return;
    }
    if one_temp && pool.len() == 1 {
        let (f, lo) = (tmp[0], pool[0]);
        b.cx(e, f);
        for l in 0..qb - 1 {
            let c = l >> 2;
            low_eq_lilypad(b, g[0], g[1], l & 3, lo, true);
            let controls = [
                (e, false),
                (g[2], c & 1 == 0),
                (g[3], c & 2 == 0),
                (lo, false),
            ];
            super::mask::mc_xor(b, &controls, f, &[], &q[..2]);
            low_eq_lilypad(b, g[0], g[1], l & 3, lo, false);
            if l + 2 < qb {
                mterm(b, f, bsig[l + 2], q[l]);
            }
        }
        return;
    }
    let hosted = one_temp;
    let f = tmp[0];
    if hosted {
        b.cx(e, f);
        for l in 0..qb - 1 {
            let c = l >> 2;
            let controls = [
                (e, false),
                (g[2], c & 1 == 0),
                (g[3], c & 2 == 0),
                (g[0], l & 1 == 0),
                (g[1], l & 2 == 0),
            ];
            super::mask::mc_xor(b, &controls, f, &[], &q[..3]);
            if l + 2 < qb {
                mterm(b, f, bsig[l + 2], q[l]);
            }
        }
        return;
    }
    if !compact {
        assert!(pool.len() >= 6 && tmp.len() >= NT);
        let lo = &tmp[4..8];
        decode2_onehot_shared(b, g[0], g[1], lo);
        let (hi, hq) = (pool[..5].to_vec(), pool[5]);
        decode5_high_shared(b, g[2], g[3], g[4], e, &hi, hq);
        b.cx(e, f);
        for l in 0..qb - 1 {
            let c = l >> 2;
            b.ccx(hi[c], lo[l & 3], f);
            if l + 2 < qb {
                mterm(b, f, bsig[l + 2], q[l]);
            }
        }
        clear_decode5_high_shared(b, g[2], g[3], g[4], e, &hi, hq);
        clear_decode2_onehot_shared(b, g[0], g[1], lo);
        return;
    }
    assert!(!pool.is_empty() && tmp.len() >= 2);
    let hi = tmp[1];
    let borrowed_high = pool.len() == 1;
    let lo = pool[0];
    let high_temps = if borrowed_high { vec![] } else { pool[..2].to_vec() };
    b.cx(e, f);
    for c in 0..3 {
        let high_lits = [
            (e, false),
            (g[2], c & 1 == 0),
            (g[3], c & 2 == 0),
        ];
        if borrowed_high {
            three_lit_toggle_dirty(b, hi, &high_lits, dirty.expect("one-lane mask needs dirty host"));
        } else {
            b.mbu_compute(hi, &high_lits, &high_temps);
        }
        for l in 4 * c..(4 * c + 4).min(qb - 1) {
            low_eq_lilypad(b, g[0], g[1], l & 3, lo, true);
            b.ccx(hi, lo, f);
            low_eq_lilypad(b, g[0], g[1], l & 3, lo, false);
            if l + 2 < qb {
                mterm(b, f, bsig[l + 2], q[l]);
            }
        }
        if borrowed_high {
            three_lit_toggle_dirty(b, hi, &high_lits, dirty.unwrap());
        } else {
            b.mbu_erase(hi, &high_lits, &high_temps);
        }
    }
}

/// Even-tick eraser of tick t (after the halve; X at frame t + 1, Q at frame t).
/// Lane LILY-A: h += 1 with m < n - 4 stored carries: h_j ^= c_j by multi-control toggles on dirty loans for
/// j > m + 1, then the stored chain as in `inc_unctl`.
pub(super) fn inc_unctl_m(b: &mut B, h: &[QubitId], tmp: &[QubitId], dirty: &[QubitId]) {
    let n = h.len();
    let m = tmp.len().min(n - 2);
    assert!(n >= 3 && m + 4 < n);
    let mut cs = vec![h[0]];
    for i in 1..=m {
        b.and_c(cs[i - 1], h[i], tmp[i - 1]);
        cs.push(tmp[i - 1]);
    }
    for j in (m + 2..n).rev() {
        let mut ctl = vec![cs[m]];
        ctl.extend(&h[m + 1..j]);
        super::mask::mcx_dirty(b, &ctl, h[j], dirty);
    }
    for i in (1..=m + 1).rev() {
        b.cx(cs[i - 1], h[i]);
        if i >= 2 {
            b.and_u(cs[i - 2], h[i - 1], cs[i - 1]);
        }
    }
    b.x(h[0]);
}

/// Lane LILY-A: Fredkin with two controls (one dirty loan).
fn ccswap(b: &mut B, c1: QubitId, c2: QubitId, x: QubitId, y: QubitId, dirty: &[QubitId]) {
    let d = *dirty.iter().find(|&&q| q != c1 && q != c2 && q != x && q != y).expect("ccswap dirty loan");
    b.cx(y, x);
    super::mask::mcx_dirty(b, &[c1, c2, x], y, &[d]);
    b.cx(y, x);
}

/// Lane LILY-A: crot_up with two controls.
fn ccrot_up(b: &mut B, c1: QubitId, c2: QubitId, v: &[QubitId], r: usize, dirty: &[QubitId]) {
    let n = v.len();
    let r = r % n;
    if r == 0 {
        return;
    }
    let gg = { let (mut a, mut bb) = (n, r); while bb != 0 { let t = a % bb; a = bb; bb = t; } a };
    for s0 in 0..gg {
        let len = n / gg;
        let cyc: Vec<usize> = (0..len).map(|k| (s0 + k * r) % n).collect();
        for k in (1..len).rev() {
            ccswap(b, c1, c2, v[cyc[k]], v[cyc[k - 1]], dirty);
        }
    }
}

/// Lane LILY-A: Takahashi-Tani-Kunihiro add t += a under c1 & c2 (the sum writes as three-control toggles).
fn ttk_add2(b: &mut B, a: &[QubitId], t: &[QubitId], c1: QubitId, c2: QubitId, dirty: &[QubitId]) {
    let n = t.len();
    assert!(n >= 2 && a.len() == n);
    let wr = |b: &mut B, i: usize| super::mask::mc_xor(b, &[(c1, false), (c2, false), (a[i], false)], t[i], &[], dirty);
    for i in 1..n { b.cx(a[i], t[i]); }
    for i in (1..n - 1).rev() { b.cx(a[i], a[i + 1]); }
    for i in 0..n - 1 { b.ccx(t[i], a[i], a[i + 1]); }
    for i in (1..n).rev() {
        wr(b, i);
        b.ccx(t[i - 1], a[i - 1], a[i]);
    }
    for i in 1..n - 1 { b.cx(a[i], a[i + 1]); }
    wr(b, 0);
    for i in 1..n { b.cx(a[i], t[i]); }
}

/// Lane LILY-A: radix4_finish_mul's binary rows (empty pool) with the row control e & q_i held by no lane.
fn radix4_finish_mul_tf(b: &mut B, a: &[QubitId], q: &[QubitId], e: QubitId, dirty: &[QubitId]) {
    assert!(q.len() >= 2 && a.len() >= q.len() - 1);
    let row = |b: &mut B, i: usize, negative: bool| {
        let start = i + 1;
        if start >= q.len() { return; }
        let target = &q[start..];
        if negative { for &x in target { b.x(x); } }
        if target.len() == 1 {
            super::mask::mc_xor(b, &[(e, false), (q[i], false), (a[0], false)], target[0], &[], dirty);
        } else {
            ttk_add2(b, &a[..target.len()], target, e, q[i], dirty);
        }
        if negative { for &x in target { b.x(x); } }
    };
    for j in (0..q.len() / 2).rev() {
        let lo = 2 * j;
        let hi = lo + 1;
        let n = q.len() - hi;
        if n == 1 && c50_enabled(64) {
            if lo > 0 { b.cx(q[lo - 1], q[lo]); }
            super::mask::mc_xor(b, &[(e, false), (q[lo], false), (a[0], false)], q[hi], &[], dirty);
            if lo > 0 { b.cx(q[lo - 1], q[lo]); }
            continue;
        }
        row(b, 2 * j + 1, true);
        for i in (0..=2 * j).rev() { row(b, i, false); }
        break;
    }
}

/// Lane LILY-A: ANF monomials (bit masks over g0..g3) of [g > l] for 4-bit g.
fn gt_anf(l: usize) -> Vec<usize> {
    let mut f: Vec<u8> = (0..16usize).map(|x| u8::from(x > l)).collect();
    for k in 0..4 {
        for mask in 0..16usize {
            if mask & (1 << k) != 0 { f[mask] ^= f[mask ^ (1 << k)]; }
        }
    }
    f.into_iter().enumerate().filter_map(|(m, c)| (c != 0).then_some(m)).collect()
}

/// hose847b G4c: after er.dec (g = g' = n - 2), with D on lane `d` (h0 ^ s): for a deferred word move Z out of
/// q_core: ccswap(e, D; q0, q12); restore a 12-digit word's bit 0 (g' = 10 = 1010b) and pull L off it.
/// Every completing word then has q_core[0] = its own bit and q12 = L.
fn hose_extract(b: &mut B, q: &[QubitId], e: QubitId, d: QubitId, g: &[QubitId], dirty: &[QubitId]) {
    assert!(q.len() == 13 && g.len() >= 4);
    let dl: Vec<QubitId> = dirty.iter().copied().filter(|x| *x != q[0] && *x != q[12] && *x != e && *x != d && !g.contains(x)).collect();
    ccswap(b, e, d, q[0], q[12], &dl);
    super::mask::mc_xor(b, &[(e, false), (d, false), (g[0], true), (g[1], false), (g[2], true), (g[3], false)], q[0], &[], &dl);
    super::mask::mc_xor(b, &[(e, false), (d, false), (q[0], false)], q[12], &[], &dl);
}

/// Lane LILY-A: the pre-swap L5 eraser with no temporary (PEAK0 < 864, zero-slack non-terminal even ticks). e lives
/// on G0, all four normalizer bits in h1/h2/h3/h5 and D in h4 (each |0> whenever e = 1 off the terminal tick); every
/// e-AND the inherited eraser held on its temporary becomes a multi-controlled form on dirty loans (value lanes of X
/// and Y, untouched by the eraser, and Q frames where Q is idle), all restored.
fn eraser_tf(b: &mut B, w: &PWalk, t: usize, e: QubitId, s: QubitId, rho: &ParityCtl, xdirty: &[QubitId]) {
    let tn = t + 1;
    let q = w.qfr(t);
    let qb = q.len();
    let wl = win_len(qb);
    assert!(qb == 13 && w.capq + 2 == qb && HB == 6 && xdirty.len() >= 6);
    let hose = w.log.len() == 3;
    // hose847b G4: D inlined on the h0 lane (D = e & (h0 ^ s) on the e = 1 support), g3 hosted in h4, q12 free for L.
    let d = if hose { w.h[0] } else { w.h[HB - 2] };
    let dw = |b: &mut B| if hose { b.cx(s, w.h[0]); };
    let cf2 = w.asig(tn, 1);
    let g = [w.h[1], w.h[2], w.h[3], if w.h.len()==5 { if hose { w.h[4] } else { q[12] } } else { w.h[HB - 1] }];
    let mut hn = w.h.len();
    if c50_enabled(32) { hn = 2; while hn < w.h.len() && (1usize << (hn - 1)) - 1 < t { hn += 1; } }
    assert!(hn == w.h.len());
    let hl: Vec<(QubitId, bool)> = w.h[1..hn].iter().map(|&x| (x, true)).collect();
    // flags: e = pq (!h0 !s ^ !h0 s !cf2 ^ h0 !cf2), Q[QB-1] ^= pq !h0 s, pq = [h1..h5 = 0]
    b.begin();
    for x in [vec![(w.h[0], true), (s, true)], vec![(w.h[0], true), (s, false), (cf2, true)], vec![(w.h[0], false), (cf2, true)]] {
        let mut l = hl.clone();
        l.extend(x);
        super::mask::mc_xor(b, &l, e, &[], &q[1..9]);
    }
    let fe = b.end();
    sec(b, "er.flags", |b| {
        b.play(&fe, false);
        let mut l = hl.clone();
        l.extend([(w.h[0], true), (s, false)]);
        super::mask::mc_xor(b, &l, q[qb - 1], &[], &q[1..9]);
    });
    // D = e & !h5 & (h0 | s) toggled into h4
    let dtog = |b: &mut B| {
        for x in [vec![(e, false), (w.h[0], false)], vec![(e, false), (s, false)],
                  vec![(e, false), (w.h[0], false), (s, false)]] {
            super::mask::mc_xor(b, &x, d, &[], &q[1..4]);
        }
    };
    if !hose { dtog(b); }
    // non-deferred completions: rotate the full Q word by QB-1 under e & !D
    sec(b, "er.qrot", |b| {
        crot_up(b, e, &q, qb - 1);
        dw(b); ccrot_up(b, e, d, &q, 1, xdirty); dw(b);
    });
    let q_core: Vec<QubitId> = q[..qb - 1].to_vec();
    let core_bits = q_core.len();
    let win: Vec<QubitId> = (0..wl).map(|k| w.asig(tn, 1 + k)).collect();
    // normalizer, every bit hosted and e-qualified
    b.begin();
    for k in (0..SB).rev() {
        let sz = 1usize << k;
        if k >= 2 && norm_need(qb, k) == 0 { continue; }
        let mut lits: Vec<(QubitId, bool)> = win[..sz].iter().map(|&x| (x, true)).collect();
        lits.push((e, false));
        super::mask::mc_xor(b, &lits, g[k], &[], &q[1..8]);
        if k == 1 {
            // g0 = !w0 & !(g1 & w2) = !w0 ^ (!w0 & g1 & w2)
            super::mask::mc_xor(b, &[(win[0], true)], g[0], &[], &[]);
            super::mask::mc_xor(b, &[(win[0], true), (g[1], false), (win[2], false)], g[0], &[], &q[1..2]);
            let rv: Vec<QubitId> = win[..norm_need(qb, 1)].iter().rev().cloned().collect();
            rot4_up(b, g[0], g[1], &rv);
            break;
        }
        for x in 0..norm_need(qb, k) {
            ccswap(b, e, g[k], win[x], win[x + sz], xdirty);
        }
    }
    let nr = b.end();
    sec(b, "er.norm", |b| b.play(&nr, false));
    // g -= D under e
    b.begin();
    dw(b);
    super::mask::mc_xor(b, &[(e, false), (d, false), (g[0], true), (g[1], true), (g[2], true)], g[3], &[], &q_core[..3]);
    super::mask::mc_xor(b, &[(e, false), (d, false), (g[0], true), (g[1], true)], g[2], &[], &q_core[..3]);
    super::mask::mc_xor(b, &[(e, false), (d, false), (g[0], true)], g[1], &[], &q_core[..3]);
    b.ccx(e, d, g[0]);
    dw(b);
    let dr = b.end();
    sec(b, "er.dec", |b| b.play(&dr, false));
    if hose { sec(b, "er.hose", |b| { dw(b); hose_extract(b, &q, e, d, &g, &q[2..10]); dw(b); }); }
    sec(b, "er.mul", |b| radix4_finish_mul_tf(b, &win[1..core_bits], &q_core, e, xdirty));
    b.cx(e, q_core[core_bits - 1]);
    dw(b); b.ccx(e, d, q_core[core_bits - 1]); dw(b);
    sec(b, "er.rot", |b| {
        for k in [0usize, 2] {
            ccrot_up(b, g[k], e, &q_core, 1 << k, xdirty);
            ccrot_up(b, g[k + 1], e, &q_core, 2 << k, xdirty);
        }
    });
    sec(b, "er.mask", |b| {
        let mut bsig: Vec<QubitId> = (0..core_bits).map(|k| w.bsig(k)).collect();
        if v1_charted(t) { bsig[1] = NO_V1; }
        if super::lilypad_g::v2_virtual(t) { bsig[2] = NO_V2; }
        if super::lilypad_g::v3_virtual(t) { bsig[3] = NO_V3; }
        let conj = |b: &mut B| { for &x in &bsig[1..] { if x != NO_V1 && x != NO_V2 && x != NO_V3 { rho.xor_into(b, x); } } };
        conj(b);
        b.cx(e, q_core[core_bits - 2]);
        if bsig[1] != NO_V1 { b.ccx(e, bsig[1], q_core[core_bits - 1]); }
        if bsig[2] == NO_V2 { dw(b); v2_mask_term(b, w, tn, e, d, &g, q_core[0], false); dw(b); }
        if bsig[3] == NO_V3 { dw(b); v3_mask_term(b, w, tn, e, d, &g, q_core[1], false, s); dw(b); }
        for l in 0..core_bits - 2 {
            if l == 0 && bsig[2] == NO_V2 { continue; }
            if l == 1 && bsig[3] == NO_V3 { continue; }
            for mono in gt_anf(l) {
                let mut ctl = vec![(e, false), (bsig[l + 2], false)];
                ctl.extend((0..4).filter(|k| mono & (1 << k) != 0).map(|k| (g[k], false)));
                super::mask::mc_xor(b, &ctl, q_core[l], &[], xdirty);
            }
        }
        conj(b);
    });
    if hose { b.cswap(e, q[12], q[0]); }
    sec(b, "er.undo", |b| {
        b.play(&dr, true);
        b.play(&nr, true);
        // Lane LILY-A: the charted V1 mask term, read once U1 is back in place (the normalizer permutes U lanes).
        if v1_charted(t) { v1_mask_toggle(b, w, tn, e, q_core[core_bits - 1]); }
        if !hose { dtog(b); }
        b.play(&fe, true);
    });
}

pub(super) fn eraser(
    b: &mut B,
    w: &PWalk,
    t: usize,
    sch: &PSched,
    sc: &PScr,
    boff: usize,
    terminal: bool,
    g_rho: Option<&ParityCtl>,
    pre_swap: bool,
    half_cofactor: bool,
) {
    // Lane LILY-ABER: under TERMH the inverse walk's terminal eraser admits only h in {0, 1} when e = 1, so every
    // terminal-only term, repair and endpoint-copy layout below is off (`terminal`), while the public-end lane choices of
    // the charted mask terms and the Q-frame loan audit keep the true flag (`terminal_v`).
    let termh = terminal && pre_swap && half_cofactor && super::pointadd_lilypad::TERMH;
    let terminal_v = terminal;
    let terminal = terminal && !termh;
    // O6 EARLYNARROW: even ticks t <= 22 erase words of at most t/2 lanes.
    if o6_enabled(2) && pre_swap && half_cofactor && !terminal && t % 2 == 0 && t <= 2 * (w.q.len().saturating_sub(2)) {
        if let Some(rho) = g_rho {
            if eraser_early(b, w, t, sch, sc, boff, rho) { return; }
        }
    }
    let tn = t + 1;
    let q = w.qfr(t);
    let qb = q.len();
    let wl = win_len(qb);
    let (cz, kv, kc) = (sch.c[tn], sch.kv[tn], sch.kc[tn]);
    // In the conversion-free G path, both raw source windows through the
    // eraser span remain live sign copies and cannot be lent.
    let cofactor_shift = usize::from(half_cofactor);
    let a_span = 2 + wl - cofactor_shift;
    let b_span = 2 + wl + boff - cofactor_shift;
    let blo = if g_rho.is_some() { b_span } else if boff > 0 { w.bb.len() } else { b_span };
    let zl0 = lsc_from(b, w, tn, cz, kv, kc, a_span, blo);
    // window / source lanes past a ring's cofactor region are value lanes: never lend them to the pools
    let busy: Vec<QubitId> = (0..a_span)
        .map(|k| w.asig(tn, k))
        .chain((0..b_span).map(|k| w.bsig(k)))
        .collect();
    let mut zl: Vec<QubitId> = zl0.iter().copied().filter(|x| !busy.contains(x)).collect();
    // Raw pre-swap G0=1 and V0=1 xor sigma. Restore them before returning.
    let donor_view=pre_swap && half_cofactor && c50_enabled(4);
    let (v0,g0)=(w.bsig(0),w.af(tn,0));
    if donor_view {
        assert!(!zl.contains(&v0)&&!zl.contains(&g0));
        b.x(g0);b.x(v0);b.cx(sc.sg,v0);
        zl.splice(0..0,[v0,g0]);
    }
    let hold=pre_swap && c50_enabled(8) && zl.len()>=8;
    let held=if hold {zl.drain(..3).collect::<Vec<_>>()}else{vec![]};
    // Lane LILY-A: a view without temporaries (inverse walk with sigma hosted in U0). Take the temporary from the
    // cleared sign lanes when there is one; at the public end, from the endpoint value G = +-1 (lane 2 is a copy of
    // lane 1 on the success support); otherwise use the hosted layout: V0 is the temporary and normalizer bit 2 is
    // hosted in h3, which is |0> whenever e = 1 (e implies [h1..h5 = 0] off the terminal tick).
    // Without an e lane (PEAK0 < 866) the flag takes the same sources first; with neither a sign lane nor the endpoint
    // copy it lives on the donor lane, normalizer bit 0 moves into h1 and the flags are formed without temporaries.
    let mut tm_own = sc.tmp.clone();
    let mut sp_own = sc.sp.clone();
    let mut e_own = sc.e;
    let mut hosted_mode = false;
    let mut hosted_e = false;
    let mut loans: Vec<(QubitId, QubitId)> = vec![];
    // sp2: F0 released (PEAK0 < 865), the normalizer owners are G0 and V0 only. With three or more cleared sign
    // lanes the third owner is one of them (the 865 layout); with two the hosted layout; with none the fully hosted one.
    if e_own == NO_E && sp_own.len() == 2 && zl.len() >= 3 {
        let x = zl.pop().unwrap();
        sp_own.push(x);
    } else if e_own == NO_E && sp_own.len() == 2 && zl.is_empty() && terminal {
        // At the public end h may be negative with e = 1, so h3 cannot host: F = +-1 there as well (pre-swap Y.v is
        // +-1 whether or not the last role swap fires), so Y.v lane 2 is a copy of lane 1 on the success support.
        let (src, ln) = (w.bf(1), w.bf(2));
        assert!(pre_swap && half_cofactor && cz >= 3 && !sp_own.contains(&ln));
        b.cx(src, ln);
        sp_own.push(ln);
        loans.push((src, ln));
    }
    // sp1: V0 also released (PEAK0 < 864): G0 is the only normalizer owner.
    let sp1 = e_own == NO_E && sp_own.len() == 1;
    if sp1 && zl.len() >= 4 {
        let x = zl.pop().unwrap();
        let y = zl.pop().unwrap();
        sp_own.push(x);
        sp_own.push(y);
    } else if sp1 && zl.is_empty() && terminal {
        // F = +-1 at the public end: Y.v lanes 2 and 3 copy lane 1 on the success support.
        for k in [2usize, 3] {
            let (src, ln) = (w.bf(1), w.bf(k));
            assert!(pre_swap && half_cofactor && cz >= 4 && !sp_own.contains(&ln));
            b.cx(src, ln);
            sp_own.push(ln);
            loans.push((src, ln));
        }
    } else if sp1 && zl.is_empty() {
        // no clean lane but G0: the eraser without temporaries
        assert!(pre_swap && half_cofactor && no_temp_view_ok(sc));
        let rho = g_rho.expect("L5 eraser rho");
        let mut xdirty: Vec<QubitId> = (1..cz).map(|f| w.af(tn, f)).collect();
        xdirty.extend((1..cz - super::lilypad_g::ycut_at(tn)).map(|f| w.bf(f)));
        if xdirty.len() < 6 {
            // Lane LILY-ABER: the 3-lane terminal frame lends 4 value lanes; add deep X cofactor lanes (the lanes the
            // v2/v3 mask terms lend; not operands of this eraser) up to the six dirty loans eraser_tf needs.
            assert!(pre_swap && half_cofactor && cz <= 4);
            let need = 6 - xdirty.len();
            xdirty.extend((120..120 + need).map(|k| w.af(tn, k)));
        }
        eraser_tf(b, w, t, sp_own[0], sc.sg, rho, &xdirty);
        if donor_view {b.cx(sc.sg,v0);b.x(v0);b.x(g0);}
        lsc_from(b, w, tn, cz, kv, kc, a_span, blo);
        return;
    }
    let sp1h = e_own == NO_E && sp_own.len() == 1;
    let sp2 = e_own == NO_E && sp_own.len() == 2;
    let yv_one = sp1h && zl.len() == 1 && !terminal;
    if yv_one {
        assert!(pre_swap && half_cofactor && HB == 6);
        e_own = sp_own[0];
        tm_own.push(zl.pop().unwrap());
        hosted_e = true;
        hosted_mode = true;
    }
    if e_own == NO_E {
        if let Some(x) = zl.pop() {
            e_own = x;
        } else if terminal {
            // Lane LILY-R: a 3-lane terminal value region has no G lane 3; F's lane 2 copies its lane 1 there.
            let (src, ln) = if cz >= 4 { (w.af(tn, 1), w.af(tn, 3)) } else { (w.bf(1), w.bf(2)) };
            assert!(pre_swap && half_cofactor && cz >= 3 && !sp_own.contains(&ln) && (cz >= 4 || sp_own.len() >= 3));
            b.cx(src, ln);
            e_own = ln;
            loans.push((src, ln));
        } else {
            assert!(pre_swap && half_cofactor && HB == 6 && (sp_own.len() == 3 || sp2) && !w.h.contains(&sp_own[0]));
            hosted_e = true;
            e_own = sp_own[0];
        }
    }
    if tm_own.is_empty() {
        if hosted_e {
            tm_own.push(*sp_own.last().unwrap());
            hosted_mode = true;
        } else if let Some(x) = zl.pop() {
            tm_own.push(x);
            if sp2 || sp1h { hosted_mode = true; }
        } else if terminal {
            let (src, ln) = (w.af(tn, 1), w.af(tn, 2));
            assert!(pre_swap && half_cofactor && cz >= 3 && !sp_own.contains(&ln) && ln != e_own);
            b.cx(src, ln);
            tm_own.push(ln);
            loans.push((src, ln));
            if sp2 { hosted_mode = true; }
        } else {
            assert!(pre_swap && half_cofactor && HB == 6 && sp_own.len() == 3 && !w.h.contains(&sp_own[2]));
            tm_own.push(sp_own[2]);
            hosted_mode = true;
        }
    }
    // Normalizer bits g (hosted ones live in h lanes, |0> whenever e = 1) and the clean normalizer owners.
    let hose = w.log.len() == 3 && w.h.len() == 5;
    let g3h = if hose { w.h[4] } else { q[12] };
    let mut g_own: Vec<QubitId> = vec![];
    let mut ghost = [false; 4];
    if yv_one {
        g_own = vec![w.h[1], w.h[2], w.h[3], if w.h.len()==5 { g3h } else { w.h[HB - 1] }];
        ghost = [true, true, true, true];
        sp_own.clear();
    } else if hosted_mode && sp1h {
        g_own = vec![sp_own[0], w.h[2], w.h[3], if w.h.len()==5 { g3h } else { w.h[HB - 1] }];
        ghost = [false, true, true, true];
    } else if hosted_e && sp2 {
        g_own = vec![w.h[1], w.h[2], w.h[3], if w.h.len()==5 { g3h } else { w.h[HB - 1] }];
        ghost = [true, true, true, true];
        sp_own = vec![];
    } else if hosted_e {
        g_own = vec![w.h[1], sp_own[1], w.h[3], if w.h.len()==5 { g3h } else { w.h[HB - 1] }];
        ghost = [true, false, true, true];
        sp_own = vec![sp_own[1]];
    } else if hosted_mode && sp2 {
        g_own = vec![sp_own[0], sp_own[1], w.h[3], if w.h.len()==5 { g3h } else { w.h[HB - 1] }];
        ghost = [false, false, true, true];
    } else if hosted_mode {
        g_own = vec![sp_own[0], sp_own[1], w.h[3], if w.h.len()==5 { g3h } else { w.h[HB - 1] }];
        ghost = [false, false, true, true];
        sp_own.truncate(2);
    }
    let tf_flags = hosted_e || (hosted_mode && sp1h);
    let view_own = PScr { e: e_own, sg: sc.sg, d: sc.d.clone(), tmp: tm_own, sp: sp_own, pool: sc.pool.clone() };
    let sc = &view_own;
    let tm = &sc.tmp;
    let e = sc.e;
    let (cf1, cf2, cg1) = (
        w.asig(tn, 1 - cofactor_shift),
        w.asig(tn, 2 - cofactor_shift),
        w.bsig(boff + 1 - cofactor_shift),
    );
    let a0_from_pool = half_cofactor && !sc.pool.is_empty();
    let a0 = if a0_from_pool {
        sc.pool[0]
    } else if half_cofactor {
        assert!(tm.len() == 1, "zero-pool eraser needs its sole temporary after flag cleanup");
        tm[0]
    } else {
        w.asig(tn, 0)
    };
    let free_pool = if a0_from_pool { &sc.pool[1..] } else { &sc.pool[..] };
    let low_scratch = pre_swap && half_cofactor && tm.len() == 1 && (sc.sp.len() >= 3 || hosted_mode);
    let no_d=sc.d.is_empty();
    assert!(!hose || (no_d && pre_swap && !terminal));
    // hose847b G4: D inlined on the h0 lane (D = e & (h0 ^ s) on the e = 1 support); h4 hosts g3, q12 is free for L.
    let d=if hose{w.h[0]}else if no_d{w.h[HB-2]}else{sc.d[0]};
    let mut flag_tmp = tm.clone();
    if flag_tmp.len() < 5 {
        flag_tmp.extend(sc.sp.iter().copied().take(5-flag_tmp.len()));
        // Pre-swap wn is unused. HB6's five-literal pq needs only three
        // clean intermediates, so the e output is only a syntactic wn alias.
        if pre_swap && flag_tmp.len()==4 {flag_tmp.push(e);}
    }
    let (pq, z0, z1, y, wn) = if tf_flags {
        // roles unused: the hosted-e flags below need no temporaries
        (tm[0], tm[0], tm[0], tm[0], e)
    } else if hosted_mode {
        // pq and y share the donor lane: pq = z0 ^ z1 is cleared before y is formed.
        (sc.sp[0], sc.sp[1], tm[0], sc.sp[0], e)
    } else if hold {
        (flag_tmp[0],held[0],held[1],held[2],flag_tmp[4])
    }else{(flag_tmp[0],flag_tmp[1],flag_tmp[2],flag_tmp[3],flag_tmp[4])};
    let mut hn=w.h.len();
    if c50_enabled(32) {hn=2;while hn<w.h.len() && (1usize<<(hn-1))-1<t {hn+=1;}}
    let hl: Vec<(QubitId, bool)> = w.h[1..hn].iter().map(|&x| (x, true)).collect();
    // These four flag outputs are still clean while pq is synthesized and
    // are restored by the MBU compute before they receive their own values.
    let htemps = if wn==e {vec![z0,z1,y]}else{vec![z0,z1,y,wn]};
    // flags
    b.begin();
    if tf_flags {
        // nothing: fe forms e directly
    } else if hosted_mode {
        // pq = [h1..h5 = 0] on two clean temps and Q-frame dirty loans, z0 = pq & !h0, z1 = pq & h0, pq cleared.
        super::mask::mc_xor(b, &hl, pq, &[z0, z1], &q[1..4]);
        b.x(w.h[0]);
        b.and_c(pq, w.h[0], z0);
        b.x(w.h[0]);
        b.cx(pq, z1);
        b.cx(z0, z1);
        b.cx(z0, pq);
        b.cx(z1, pq);
    } else {
    b.mbu_compute(pq, &hl, &htemps);
    b.x(w.h[0]);
    b.and_c(pq, w.h[0], z0);
    b.x(w.h[0]);
    if c50_enabled(2) {b.cx(pq,z1);b.cx(z0,z1);}else{b.and_c(pq, w.h[0], z1);}
    }
    if pre_swap {
        if !tf_flags {
            b.and_c(z0, sc.sg, y);
        }
    } else {
        b.and_c(z0, cf1, y);
        b.x(cf1);
        b.and_c(z1, cf1, wn);
        b.x(cf1);
    }
    let ft = b.end();
    b.begin();
    if pre_swap && !no_d {
        // D = (y | [h=1]) & !X.c2; y and z1 are exclusive.
        b.cx(z1, y);
        b.x(cf2);
        b.and_c(y, cf2, d);
        b.x(cf2);
        b.cx(z1, y);
    } else if !pre_swap && g_rho.is_some() {
        // In raw stored-G coordinates, Y.c sig2 is c_f(pre-swap) bit1.
        // Its zero value distinguishes an Fs completion at h=0.
        let yc2 = w.bsig(2 - cofactor_shift);
        b.x(yc2);
        b.and_c(y, yc2, d);
        b.x(yc2);
    } else if !pre_swap {
        b.cx(cg1, cf2);
        b.x(cf2);
        b.and_c(y, cf2, d);
        b.x(cf2);
        b.cx(cg1, cf2);
    }
    if !pre_swap {
        b.x(cf2);
        b.ccx(wn, cf2, d);
        b.x(cf2);
    }
    let fd = b.end();
    // hosted-e flag terms: e = pq (!h0 !s ^ !h0 s !cf2 ^ h0 !cf2), pq = [h1..h(hn-1) = 0]; y = pq !h0 s
    let he_temps = if tf_flags { let mut v = vec![tm[0]]; v.extend(&sc.sp); v } else { vec![] };
    let he_terms: Vec<Vec<(QubitId, bool)>> = if tf_flags {
        [vec![(w.h[0], true), (sc.sg, true)], vec![(w.h[0], true), (sc.sg, false), (cf2, true)], vec![(w.h[0], false), (cf2, true)]]
            .into_iter().map(|x| { let mut l = hl.clone(); l.extend(x); l }).collect()
    } else { vec![] };
    b.begin();
    if tf_flags {
        assert!(no_d && pre_swap && !terminal);
        for l in &he_terms {
            super::mask::mc_xor(b, l, e, &he_temps, &q[1..9]);
        }
    } else {
    b.cx(z0, e);
    b.cx(y, e);
    if no_d {
        assert!(pre_swap && HB==6);
        b.cx(z1,y);b.x(cf2);b.ccx(y,cf2,e);b.x(cf2);b.cx(z1,y);
    }else{b.cx(d,e);}
    }
    let neg = |name: &str| match name {
        "noFt" => l2_neg(8),
        "noFm" => l2_neg(9),
        "noFsfix" => l2_neg(10),
        _ => false,
    };
    let swap_flag = if pre_swap && !l5_neg(2) { sc.sg } else { cf1 };
    if terminal && !neg("noFt") {
        assert_eq!(w.h.len(),6,"H5Q requires TERMH");
        b.x(swap_flag);
        b.ccx(w.h[HB - 1], swap_flag, e);
        b.x(swap_flag);
    }
    let fe = b.end();
    sec(b, "er.flags", |b| {
        b.play(&ft, false);
        b.play(&fd, false);
        b.play(&fe, false);
        if tf_flags {
            let mut l = hl.clone();
            l.extend([(w.h[0], true), (sc.sg, false)]);
            super::mask::mc_xor(b, &l, q[qb - 1], &he_temps, &q[1..9]);
        } else {
            b.cx(y, q[qb - 1]);
        }
        if terminal && !neg("noFm") {
            b.ccx(w.h[HB - 1], swap_flag, q[qb - 1]);
        }
        if hold {b.cx(z0,pq);b.cx(z1,pq);}else{b.play(&ft, true);}
    });
    // D = e & !sign(h) & (h0 OR sigma) on the admitted eraser support.
    // h4 is known zero on this active support; outside it, retain its dirty
    // value and qualify every D use by e. No host is ever measured.
    let d_host_toggle=|b:&mut B| {
        if sc.sp.is_empty() {
            // Lane LILY-A (all normalizer bits hosted): D ^= e !h5 (h0 | s) as three disjoint-term toggles.
            for x in [vec![(e,false),(w.h[0],false)], vec![(e,false),(sc.sg,false)],
                      vec![(e,false),(w.h[0],false),(sc.sg,false)]] {
                super::mask::mc_xor(b, &x, d, &[], &q[1..4]);
            }
            return;
        }
        let a=tm[0];let u=sc.sp[0];
        b.and_c(w.h[0],sc.sg,a);b.cx(w.h[0],a);b.cx(sc.sg,a);
        b.and_c(e,a,u);b.cx(u,d);
        b.and_u(e,a,u);b.cx(sc.sg,a);b.cx(w.h[0],a);b.and_u(w.h[0],sc.sg,a);
    };
    let d_terminal_repair=|b:&mut B| {
        b.ccx(e,w.h[2],d);b.ccx(e,w.h[3],d);
        b.and_c(w.h[2],w.h[3],tm[0]);b.ccx(e,tm[0],d);b.and_u(w.h[2],w.h[3],tm[0]);
    };
    o6_mark(b, "flags");
    if no_d && !hose {if terminal{d_terminal_repair(b);}d_host_toggle(b);}
    o6_mark(b, "dflag");
    let narrow_core = pre_swap;
    if narrow_core {
        assert_eq!(w.capq + 2, qb, "L5 12-lane eraser needs run cap q = QB - 2");
        sec(b, "er.qrot", |b| {
            if hose{b.cx(sc.sg,w.h[0]);}
            if no_d{b.and_c(e,d,a0);}
            let dq=if no_d{a0}else{d};
            b.cx(dq, e);crot_up(b,e,&q,qb-1);b.cx(dq,e);
            if no_d{b.and_u(e,d,a0);}
            if hose{b.cx(sc.sg,w.h[0]);}
        });
    } else {
        sec(b, "er.qrot", |b| crot_up(b, d, &q, 1));
    }
    let q_core: Vec<QubitId> = if narrow_core {
        if l5_neg(1) {
            q[1..].to_vec()
        } else {
            q[..qb - 1].to_vec()
        }
    } else {
        q.clone()
    };
    let q_core = &q_core;
    let core_bits = q_core.len();
    // Fs: window X.c sig 2.. <- (X.c >> 1) - Y.c, in place, under fs = D & cf1
    let win: Vec<QubitId> = (0..wl).map(|k| w.asig(tn, 2 - cofactor_shift + k)).collect();
    let src: Vec<QubitId> = (0..wl).map(|k| w.bsig(boff + 1 - cofactor_shift + k)).collect();
    let fsq = tm[0];
    let mut fpool: Vec<QubitId> = tm[1..]
        .iter()
        .copied()
        .filter(|&q| q != a0)
        .collect();
    fpool.push(a0);
    fpool.extend(&sc.sp);
    fpool.extend(free_pool);
    fpool.extend(&zl);
    b.begin();
    if !pre_swap {
        b.and_c(d, cf1, fsq);
    }
    if pre_swap {
        // The role swap has not happened, so no Fs window conversion is needed.
    } else if g_rho.is_some() {
        // For Fs, raw X.c/2 is c_g(pre-swap) and raw Y.c/2 is -c_f(pre-swap)
        // up to the tracked rho sign. A lane-for-lane role exchange supplies
        // the same window without an arithmetic conversion.
        for k in 0..wl {
            if !l2_neg(1) {
                let yoff = if l2_neg(5) { 3 } else { 2 };
                b.cswap(
                    fsq,
                    w.asig(tn, 2 - cofactor_shift + k),
                    w.bsig(yoff - cofactor_shift + k),
                );
            }
        }
    } else {
        for &x in &win {
            b.cx(fsq, x);
        }
        ctrl_add_pool(b, &src, &win, fsq, &fpool);
        for &x in &win {
            b.cx(fsq, x);
        }
    }
    if !pre_swap {
        b.and_u(d, cf1, fsq);
    }
    let fs = b.end();
    if !neg("noFsfix") {
        sec(b, "er.fsub", |b| b.play(&fs, false));
    }
    // normalizer (frogstrip's, window from X.c sig 2)
    // C58: the top normalizer predicate uses an e-conditioned sign host.
    // e=1 gives h=0/1, except the admitted negative terminal [-11,-1].
    // Repair that terminal sign locally and restore it after all g uses.
    let high_host=sc.sp.len()==3 || hosted_mode;
    let host=if w.h.len()==5 { g3h } else { w.h[HB-1] };
    let repair_host=|b:&mut B| {
        b.ccx(e,w.h[2],host);b.ccx(e,w.h[3],host);
        let tmp=a0;
        b.and_c(w.h[2],w.h[3],tmp);b.ccx(e,tmp,host);b.and_u(w.h[2],w.h[3],tmp);
    };
    if high_host && terminal {repair_host(b);}
    let hosted_g = if hosted_mode { g_own.clone() } else { let mut v = sc.sp.clone(); if high_host { v.push(host); } v };
    let ghost = if hosted_mode { ghost } else { [false, false, false, high_host] };
    let g=&hosted_g[..SB];
    // O6 QLEND-E: the normalizer is recorded twice. The er.undo copy (its compute play in the
    // inverse walk, at the start of the un-eraser) adds Q frames 0 and 1 as clean temps of the
    // hosted k = 3 toggle: no live word reaches them there [Lean L3]. Both copies compute the
    // same shift lanes and window, so either inverts the other on clean temps.
    let rec_norm=|b:&mut B,xt:&[QubitId]|->Vec<G> {
        b.begin();
        for k in (0..SB).rev() {
            let s = 1usize << k;
            if k >= 2 && norm_need(qb, k) == 0 {
                continue;
            }
            let mut lits: Vec<(QubitId, bool)> = win[..s].iter().map(|&x| (x, true)).collect();
            let hosted=ghost[k];
            if hosted {lits.push((e,false));}
            let mut temps: Vec<QubitId> = sc
                .tmp
                .iter()
                .copied()
                .filter(|&q| q != a0)
                .collect();
            temps.push(a0);
            temps.extend((0..k).filter(|&i| !ghost[i]).map(|i| g[i]));
            temps.extend(free_pool);
            temps.extend(&zl);
            if hosted {temps.extend(xt);}
            if hosted {
                super::mask::mc_xor(b,&lits,g[k],&temps,if xt.is_empty(){&q[1..8]}else{&q[2..9]});
            } else if temps.len() + 2 >= s {
                b.mbu_compute(g[k], &lits, &temps);
            } else {
                let (pq, rest) = temps.split_last().unwrap();
                b.mbu_compute(*pq, &lits[..s / 2], rest);
                let mut l2 = vec![(*pq, false)];
                l2.extend(&lits[s / 2..]);
                b.mbu_compute(g[k], &l2, rest);
                b.mbu_erase(*pq, &lits[..s / 2], rest);
            }
            if k == 1 {
                let tt = sc.tmp[0];
                b.and_c(g[1], win[2], tt);
                if ghost[0] {
                    super::mask::mc_xor(b, &[(win[0], true), (tt, true)], g[0], &[], &[]);
                } else {
                    b.mbu_compute(g[0], &[(win[0], true), (tt, true)], &[]);
                }
                b.and_u(g[1], win[2], tt);
                let rv: Vec<QubitId> = win[..norm_need(qb, 1)].iter().rev().cloned().collect();
                rot4_up(b, g[0], g[1], &rv);
                break;
            }
            if hosted {b.and_c(e,g[k],a0);}
            for x in 0..norm_need(qb, k) {
                b.cswap(if hosted{a0}else{g[k]}, win[x], win[x + s]);
            }
            if hosted {b.and_u(e,g[k],a0);}
        }
        b.end()
    };
    let nr = rec_norm(b,&[]);
    let qlend_e = o6_enabled(4) && pre_swap && high_host && !terminal_v;
    if qlend_e { assert!(q.len()==13 && !temps_conflict(&q[1..2], sc, &zl, a0)); }
    let nr_undo = if qlend_e { rec_norm(b,&q[1..2]) } else { nr.clone() };
    sec(b, "er.norm", |b| b.play(&nr, false));
    b.begin();
    let mut dtmp: Vec<QubitId> = sc
        .tmp
        .iter()
        .copied()
        .filter(|&q| q != a0)
        .collect();
    dtmp.push(a0);
    dtmp.extend(free_pool);
    dtmp.extend(&zl);
    if no_d {
        if hose{b.cx(sc.sg,w.h[0]);}
        b.and_c(e,d,a0);dec4_dirty(b,a0,g,&q_core[..2]);b.and_u(e,d,a0);
        if hose{b.cx(sc.sg,w.h[0]);}
    }else if dtmp.len() < SB - 2 {
        dec4_dirty(b, d, g, &q_core[..2]);
    } else if dtmp.len() >= SB - 1 {
        dec(b, d, g, &dtmp[..SB - 1]);
    } else {
        dec_topless(b, d, g, &dtmp[..SB - 2]);
    }
    let dr = b.end();
    sec(b, "er.dec", |b| b.play(&dr, false));
    if hose {
        let gq: Vec<QubitId> = g.to_vec();
        sec(b, "er.hose", |b| { b.cx(sc.sg,w.h[0]); hose_extract(b, &q, e, d, &gq, &q[2..10]); b.cx(sc.sg,w.h[0]); });
    }
    let mut pool: Vec<QubitId> = if low_scratch {
        vec![]
    } else {
        sc.tmp.iter().copied().filter(|&q| q != a0).collect()
    };
    pool.push(a0);
    pool.extend(free_pool);
    pool.extend(&zl);
    sec(b, "er.mul", |b| radix4_finish_mul(b, &win[1..core_bits], q_core, e, a0, &pool));
    if g_rho.is_some() && !l2_neg(4) {
        // Fd and the shared C6 endpoint-open word require the word's top bit
        // flipped by e xor d. This must happen after multiply, before rotate.
        b.cx(e, q_core[core_bits - 1]);
        if no_d{ if hose{b.cx(sc.sg,w.h[0]);} b.ccx(e,d,q_core[core_bits-1]); if hose{b.cx(sc.sg,w.h[0]);} }else{b.cx(d,q_core[core_bits-1]);}
    }
    sec(b, "er.rot", |b| {
        if let Some(&loan) = zl.first() {
            let (c1, c2) = (a0, loan);
            super::frogtail::c58_rot16(b,&g[..4],e,q_core,c1,c2);
        } else if low_scratch {
            for k in [0usize, 2] {
                b.and_c(g[k], e, a0);
                crot_up(b, a0, q_core, 1 << k);
                b.and_u(g[k], e, a0);
                b.and_c(g[k + 1], e, a0);
                crot_up(b, a0, q_core, 2 << k);
                b.and_u(g[k + 1], e, a0);
            }
        } else {
            let (c1, c2) = (sc.tmp[0], sc.tmp[1]);
            for k in [0usize, 2] {
                b.and_c(g[k], e, c1);
                b.and_c(g[k + 1], e, c2);
                rot4_unit(b, c1, c2, q_core, 1 << k);
                b.and_u(g[k + 1], e, c2);
                b.and_u(g[k], e, c1);
            }
            if core_bits >= 18 {
                b.and_c(g[4], e, c1);
                crot_up(b, c1, q_core, 16);
                b.and_u(g[4], e, c1);
            }
        }
    });
    let mut mp: Vec<QubitId> = sc.pool.clone();
    if !half_cofactor {
        mp.push(a0);
    }
    mp.extend(&zl);
    sec(b, "er.mask", |b| {
        let mut bsig: Vec<QubitId> = (0..core_bits).map(|k| w.bsig(boff + k)).collect();
        if pre_swap && half_cofactor && boff == 0 && v1_charted(t) { bsig[1] = NO_V1; }
        if pre_swap && half_cofactor && boff == 0 && super::lilypad_g::v2_virtual(t) { bsig[2] = NO_V2; }
        if pre_swap && half_cofactor && boff == 0 && super::lilypad_g::v3_virtual(t) { bsig[3] = NO_V3; }
        let conjugate_sources = |b: &mut B| {
            if let Some(rho) = g_rho {
                // Raw source bit 0 is constant; bits 1.. are conjugated by
                // phi = rho xor cf1. In physical lanes these are sig2..QB.
                for &x in &bsig[1..] {
                    if x == NO_V1 || x == NO_V2 || x == NO_V3 { continue; }
                    if l2_neg(7) {
                        b.cx(w.h[0], x);
                    } else if !(l2_neg(2) || (pre_swap && (l2_neg(1) || l2_neg(3) || l2_neg(5)))) {
                        rho.xor_into(b, x);
                    }
                    if !pre_swap && !l2_neg(3) {
                        b.cx(cf1, x);
                    }
                }
            }
        };
        conjugate_sources(b);
        let mut mask_tmp = sc.tmp.clone();
        if !narrow_core {
            mask_tmp.extend(&sc.sp);
        }
        if bsig[2] == NO_V2 { if hose{b.cx(sc.sg,w.h[0]);} v2_mask_term(b, w, tn, e, d, g, q_core[0], terminal_v); if hose{b.cx(sc.sg,w.h[0]);} }
        if bsig[3] == NO_V3 { if hose{b.cx(sc.sg,w.h[0]);} v3_mask_term(b, w, tn, e, d, g, q_core[1], terminal_v, sc.sg); if hose{b.cx(sc.sg,w.h[0]);} }
        finish_mask(b, q_core, &bsig, g, e, &mask_tmp, &mp, Some(d));
        conjugate_sources(b);
    });
    let v1c = pre_swap && half_cofactor && boff == 0 && v1_charted(t);
    // hose847b G4d: L back to Q frame 0 (E = 1: q_core is clear, q12 = L).
    if hose { b.cswap(e, q[12], q[0]); }
    sec(b, "er.undo", |b| {
        b.play(&dr, true);
        b.play(&nr_undo, true);
        // Lane LILY-A: the charted V1 mask term, read once U1 is back in place (the normalizer permutes U lanes).
        if v1c { v1_mask_toggle(b, w, tn, e, q_core[core_bits - 1]); }
        if !neg("noFsfix") {
            b.play(&fs, true);
        }
        if no_d && !hose {
            if high_host && terminal{repair_host(b);}
            d_host_toggle(b);if terminal{d_terminal_repair(b);}
        }
        if hold {b.cx(z0,pq);b.cx(z1,pq);}else{b.play(&ft, false);}
        b.play(&fe, true);
        b.play(&fd, true);
        b.play(&ft, true);
    });
    if !no_d && high_host && terminal {repair_host(b);}
    if donor_view {b.cx(sc.sg,v0);b.x(v0);b.x(g0);}
    lsc_from(b, w, tn, cz, kv, kc, a_span, blo);
    for &(src, ln) in loans.iter().rev() { b.cx(src, ln); }
}

/// O6 QLEND-E owner audit: the lent Q frames are not scratch, pool or sign lanes of the eraser.
fn no_temp_view_ok(sc: &PScr) -> bool {
    sc.tmp.is_empty() && sc.pool.is_empty() && sc.d.is_empty() && sc.sp.len() == 1
}

fn temps_conflict(lent: &[QubitId], sc: &PScr, zl: &[QubitId], a0: QubitId) -> bool {
    lent.iter().any(|x| *x == a0 || *x == sc.e || *x == sc.sg || sc.tmp.contains(x) || sc.sp.contains(x)
        || sc.pool.contains(x) || sc.d.contains(x) || zl.contains(x))
}

/// O6 EARLYNARROW (R24): the pre-swap L5 eraser at an even tick t <= 22, on an m = t/2 lane core.
/// h starts at 0 and moves by one per tick, so a run completing at tc has ic <= (tc-1)/2: before
/// the eraser of tick t every live Q bit is at most m ticks old (frames QB-1-m..QB-1) and every word
/// erased at t, marker included, has at most m bits [Lean L1]. Flags, D, the frame-down rotation, the
/// normalizer (shifts <= m-1), multiply, rotation (<= m-2) and mask act on that span only; frames
/// below it are |0> on the success support and join the clean lanes. Exact on the success support.
/// Returns false (emitting nothing) when the narrowed layout lacks clean lanes.
#[allow(clippy::too_many_arguments)]
fn eraser_early(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr, boff: usize, rho: &ParityCtl) -> bool {
    let bits = |x: usize| (usize::BITS - x.leading_zeros()) as usize;
    let tn = t + 1;
    let q = w.qfr(t);
    let qb = q.len();
    let m = t / 2;
    assert!(qb == 13 && w.capq + 2 == qb && t % 2 == 0 && (1..qb - 1).contains(&m) && t < sch.s);
    let qn = m + 1;
    let span: Vec<QubitId> = q[qb - 1 - m..].to_vec();
    let mut lo: Vec<QubitId> = q[usize::from(w.h.len()==5)..qb - 1 - m].to_vec();
    if !super::pointadd_lilypad::INV_V3_LANE && !super::lilypad_g::v3_virtual(t) { lo.retain(|&x| x != w.bsig(3)); }
    let wl = win_len(qn);
    let (cz, kv, kc) = (sch.c[tn], sch.kv[tn], sch.kc[tn]);
    let a_span = 1 + wl;
    let b_span = 1 + wl + boff;
    let busy: Vec<QubitId> = (0..a_span).map(|k| w.asig(tn, k)).chain((0..b_span).map(|k| w.bsig(k))).collect();
    // Dry run of the sign-lane clear to size the clean lanes before emitting anything.
    b.begin();
    let zl0 = lsc_from(b, w, tn, cz, kv, kc, a_span, b_span);
    let _ = b.end();
    let mut zl: Vec<QubitId> = zl0.iter().copied().filter(|x| !busy.contains(x)).collect();
    let zl_full = zl.clone();
    let tm_own: Vec<QubitId> = if sc.tmp.is_empty() {
        match zl.pop() { Some(x) => vec![x], None => return false }
    } else {
        sc.tmp.clone()
    };
    let tm = &tm_own;
    let e = if sc.e == NO_E { match zl.pop() { Some(x) => x, None => return false } } else { sc.e };
    let mut sp_e = sc.sp.clone();
    while sp_e.len() < 3 { match zl.pop() { Some(x) => sp_e.push(x), None => return false } }
    let view_e = PScr { e: sc.e, sg: sc.sg, d: sc.d.clone(), tmp: sc.tmp.clone(), sp: sp_e, pool: sc.pool.clone() };
    let sc = &view_e;
    assert!(tm.len() == 1 && sc.sp.len() >= 3, "early eraser: L5 inverse view");
    let kn = bits(m - 1).max(2);
    let lo_for_g = kn.saturating_sub(sc.sp.len());
    if lo.len() < lo_for_g { return false; } // H5Q: Q0 is no longer a clean early owner.
    let spare_sp = sc.sp.len().saturating_sub(kn);
    let hold = c50_enabled(8) && zl.len() >= 8;
    let free = sc.pool.len().saturating_sub(1) + zl.len() - if hold { 3 } else { 0 } + spare_sp + lo.len() - lo_for_g;
    if m >= 2 && free < 6 {
        return false;
    }
    let zl0 = lsc_from(b, w, tn, cz, kv, kc, a_span, b_span);
    assert_eq!(zl0.iter().copied().filter(|x| !busy.contains(x)).collect::<Vec<_>>(), zl_full);
    let donor_view = c50_enabled(4);
    let (v0, g0l) = (w.bsig(0), w.af(tn, 0));
    if donor_view {
        assert!(!zl.contains(&v0) && !zl.contains(&g0l));
        b.x(g0l); b.x(v0); b.cx(sc.sg, v0);
        zl.splice(0..0, [v0, g0l]);
    }
    let held = if hold { zl.drain(..3).collect::<Vec<_>>() } else { vec![] };
    let cf2 = w.asig(tn, 1);
    let a0 = if sc.pool.is_empty() { tm[0] } else { sc.pool[0] };
    let free_pool: &[QubitId] = if sc.pool.is_empty() { &sc.pool[..] } else { &sc.pool[1..] };
    let no_d = sc.d.is_empty();
    let d = if no_d { w.h[HB - 2] } else { sc.d[0] };
    let mut flag_tmp = tm.clone();
    if flag_tmp.len() < 5 {
        flag_tmp.extend(sc.sp.iter().copied().take(5 - flag_tmp.len()));
        if flag_tmp.len() == 4 { flag_tmp.push(e); }
    }
    let (pq, z0, z1, y, wn) = if hold {
        (flag_tmp[0], held[0], held[1], held[2], flag_tmp[4])
    } else {
        (flag_tmp[0], flag_tmp[1], flag_tmp[2], flag_tmp[3], flag_tmp[4])
    };
    let mut hn = w.h.len();
    if c50_enabled(32) { hn = 2; while hn < w.h.len() && (1usize << (hn - 1)) - 1 < t { hn += 1; } }
    let hl: Vec<(QubitId, bool)> = w.h[1..hn].iter().map(|&x| (x, true)).collect();
    let htemps = if wn == e { vec![z0, z1, y] } else { vec![z0, z1, y, wn] };
    b.begin();
    b.mbu_compute(pq, &hl, &htemps);
    b.x(w.h[0]);
    b.and_c(pq, w.h[0], z0);
    b.x(w.h[0]);
    if c50_enabled(2) { b.cx(pq, z1); b.cx(z0, z1); } else { b.and_c(pq, w.h[0], z1); }
    b.and_c(z0, sc.sg, y);
    let ft = b.end();
    if m == 1 {
        // t = 2: every word is the swap-and-complete marker (e = 0 on the success support).
        sec(b, "er.flags", |b| {
            b.play(&ft, false);
            b.cx(y, q[qb - 1]);
            b.play(&ft, true);
        });
        if donor_view { b.cx(sc.sg, v0); b.x(v0); b.x(g0l); }
        lsc_from(b, w, tn, cz, kv, kc, a_span, b_span);
        return true;
    }
    b.begin();
    if !no_d {
        // D = (y | [h=1]) & !X.c2; y and z1 are exclusive.
        b.cx(z1, y);
        b.x(cf2);
        b.and_c(y, cf2, d);
        b.x(cf2);
        b.cx(z1, y);
    }
    let fd = b.end();
    b.begin();
    b.cx(z0, e);
    b.cx(y, e);
    if no_d {
        b.cx(z1, y); b.x(cf2); b.ccx(y, cf2, e); b.x(cf2); b.cx(z1, y);
    } else {
        b.cx(d, e);
    }
    let fe = b.end();
    sec(b, "er.flags", |b| {
        b.play(&ft, false);
        b.play(&fd, false);
        b.play(&fe, false);
        b.cx(y, q[qb - 1]);
        if hold { b.cx(z0, pq); b.cx(z1, pq); } else { b.play(&ft, true); }
    });
    // D = e & !sign(h) & (h0 OR sigma), hosted in h4 (as in `eraser`).
    let d_host_toggle = |b: &mut B| {
        let a = tm[0];
        let u = sc.sp[0];
        b.and_c(w.h[0], sc.sg, a); b.cx(w.h[0], a); b.cx(sc.sg, a);
        b.and_c(e, a, u); b.cx(u, d);
        b.and_u(e, a, u); b.cx(sc.sg, a); b.cx(w.h[0], a); b.and_u(w.h[0], sc.sg, a);
    };
    o6_mark(b, "flags");
    if no_d { d_host_toggle(b); }
    o6_mark(b, "dflag");
    // Non-deferred completions move down one frame inside the span; frame QB-1-m is clean.
    sec(b, "er.qrot", |b| {
        if no_d { b.and_c(e, d, a0); }
        let dq = if no_d { a0 } else { d };
        b.cx(dq, e);
        crot_up(b, e, &span, m);
        b.cx(dq, e);
        if no_d { b.and_u(e, d, a0); }
    });
    let q_core: Vec<QubitId> = span[..m].to_vec();
    let win: Vec<QubitId> = (0..wl).map(|k| w.asig(tn, 1 + k)).collect();
    // Shift lanes: the view's normalizer lanes, then (c58 layout, m >= 9) one clean low Q frame.
    let mut g: Vec<QubitId> = sc.sp.iter().copied().take(kn).collect();
    while g.len() < kn { g.push(lo.remove(0)); }
    let mut extra: Vec<QubitId> = free_pool.to_vec();
    extra.extend(&zl);
    extra.extend(sc.sp.iter().copied().skip(kn));
    extra.extend(&lo);
    let tmp_rest: Vec<QubitId> = tm.iter().copied().filter(|&x| x != a0).collect();
    {
        // Owner audit: shift lanes and clean lanes are pairwise distinct and disjoint from every
        // live operand of the narrowed eraser.
        let mut lanes: Vec<QubitId> = g.iter().chain(&extra).chain(&tmp_rest).copied().collect();
        lanes.push(a0);
        let n0 = lanes.len();
        lanes.sort_unstable_by_key(|x| x.0);
        lanes.dedup();
        assert_eq!(lanes.len(), n0, "early eraser lane alias t{t}");
        for x in &lanes {
            assert!(*x != e && *x != d && *x != sc.sg && !held.contains(x) && !w.h.contains(x) && !w.log.contains(x));
            // Y.c sig0 (V0) may be a normalizer loan of the view; the mask reads sig1.. only.
            assert!(!span.contains(x) && !win.contains(x) && !(1..b_span).any(|k| w.bsig(k) == *x && !(k == 1 && v1_charted(t)) && !(k == 2 && super::lilypad_g::v2_virtual(t)) && !(k == 3 && super::lilypad_g::v3_virtual(t))));
        }
        assert!(extra.len() >= 6, "early eraser needs six clean lanes t{t}");
    }
    let tt = tm[0];
    b.begin();
    for k in (0..kn).rev() {
        let s = 1usize << k;
        if k >= 2 && norm_need(qn, k) == 0 {
            continue;
        }
        let lits: Vec<(QubitId, bool)> = win[..s].iter().map(|&x| (x, true)).collect();
        let mut temps: Vec<QubitId> = tmp_rest.clone();
        temps.push(a0);
        temps.extend(&g[..k]);
        temps.extend(&extra);
        if temps.len() + 2 >= s {
            b.mbu_compute(g[k], &lits, &temps);
        } else {
            let (pq2, rest) = temps.split_last().unwrap();
            b.mbu_compute(*pq2, &lits[..s / 2], rest);
            let mut l2 = vec![(*pq2, false)];
            l2.extend(&lits[s / 2..]);
            b.mbu_compute(g[k], &l2, rest);
            b.mbu_erase(*pq2, &lits[..s / 2], rest);
        }
        if k == 1 {
            b.and_c(g[1], win[2], tt);
            b.mbu_compute(g[0], &[(win[0], true), (tt, true)], &[]);
            b.and_u(g[1], win[2], tt);
            let rv: Vec<QubitId> = win[..norm_need(qn, 1)].iter().rev().cloned().collect();
            rot4_up(b, g[0], g[1], &rv);
            break;
        }
        for x in 0..norm_need(qn, k) {
            b.cswap(g[k], win[x], win[x + s]);
        }
    }
    let nr = b.end();
    sec(b, "er.norm", |b| b.play(&nr, false));
    b.begin();
    {
        let ctl = if no_d { b.and_c(e, d, a0); a0 } else { d };
        let mut anc: Vec<QubitId> = tmp_rest.clone();
        if ctl != a0 { anc.push(a0); }
        anc.extend(&extra);
        dec(b, ctl, &g, &anc[..kn - 1]);
        if no_d { b.and_u(e, d, a0); }
    }
    let dr = b.end();
    sec(b, "er.dec", |b| b.play(&dr, false));
    let mut pool: Vec<QubitId> = tmp_rest.clone();
    pool.push(a0);
    pool.extend(&extra);
    sec(b, "er.mul", |b| radix4_finish_mul(b, &win[1..m], &q_core, e, a0, &pool));
    if !l2_neg(4) {
        // Fd and the shared endpoint-open word: flip the word's top bit by e xor D.
        b.cx(e, q_core[m - 1]);
        if no_d { b.ccx(e, d, q_core[m - 1]); } else { b.cx(d, q_core[m - 1]); }
    }
    // After the D decrement g <= m-2 on the success support: rotate the core up by e*g with
    // kr+1 controlled reflections (the C58 16-way network on kr bits).
    let kr = bits(m - 2);
    // Test-only mutant (O6 bit 64): one rotation bit short; the z3 gate must reject it.
    #[cfg(test)]
    let kr = if o6_enabled(64) && kr > 1 { kr - 1 } else { kr };
    sec(b, "er.rot", |b| {
        if kr == 0 { return; }
        let n = q_core.len();
        let reflect = |b: &mut B, c: QubitId, axis: isize| {
            for i in 0..n {
                let j = (axis - i as isize).rem_euclid(n as isize) as usize;
                if i < j { b.cswap(c, q_core[n - 1 - i], q_core[n - 1 - j]); }
            }
        };
        let (mut cur, mut prev) = (a0, extra[0]);
        b.and_c(e, g[0], cur);
        reflect(b, cur, 1);
        let mut axis = 1isize;
        for j in 1..kr {
            axis -= 1 << (j - 1);
            std::mem::swap(&mut cur, &mut prev);
            b.and_c(e, g[j], cur);
            b.cx(prev, cur);
            reflect(b, cur, axis);
            b.cx(prev, cur);
            b.and_u(e, g[j - 1], prev);
        }
        axis -= 1 << (kr - 1);
        reflect(b, cur, axis);
        b.and_u(e, g[kr - 1], cur);
    });
    sec(b, "er.mask", |b| {
        let mut bsig: Vec<QubitId> = (0..m).map(|k| w.bsig(boff + k)).collect();
        if boff == 0 && v1_charted(t) { bsig[1] = NO_V1; }
        if boff == 0 && m >= 3 && super::lilypad_g::v2_virtual(t) { bsig[2] = NO_V2; }
        if boff == 0 && m >= 4 && super::lilypad_g::v3_virtual(t) { bsig[3] = NO_V3; }
        let conjugate_sources = |b: &mut B| {
            for &x in &bsig[1..] {
                if x == NO_V1 || x == NO_V2 || x == NO_V3 { continue; }
                if l2_neg(7) {
                    b.cx(w.h[0], x);
                } else if !(l2_neg(2) || l2_neg(1) || l2_neg(3) || l2_neg(5)) {
                    rho.xor_into(b, x);
                }
            }
        };
        conjugate_sources(b);
        b.cx(e, q_core[m - 2]);
        if bsig[1] != NO_V1 { b.ccx(e, bsig[1], q_core[m - 1]); }
        if m >= 3 && bsig[2] == NO_V2 { v2_mask_term(b, w, tn, e, d, &g, q_core[0], false); }
        if m >= 4 && bsig[3] == NO_V3 { v3_mask_term(b, w, tn, e, d, &g, q_core[1], false, sc.sg); }
        if m == 3 {
            // One masked lane: f = e & [g >= 1] = e & g0 on the support g <= 1.
            let f = extra[0];
            b.and_c(e, g[0], f);
            mterm(b, f, bsig[2], q_core[0]);
            b.and_u(e, g[0], f);
        } else if m >= 4 {
            // f = e & [l < g]: toggled off at l = g (one high group per four lanes, low pair view).
            let (f, loan) = (extra[0], extra[1]);
            let ng = ((m - 2) >> 2) + 1;
            let hl3 = [extra[2], extra[3], extra[4]];
            let high: Vec<QubitId> = match ng {
                1 => vec![e],
                2 => {
                    b.and_c(e, g[2], hl3[1]);
                    b.cx(e, hl3[0]);
                    b.cx(hl3[1], hl3[0]);
                    vec![hl3[0], hl3[1]]
                }
                _ => {
                    let (p, qh, wq) = (hl3[0], hl3[1], hl3[2]);
                    b.x(g[2]); b.and_c(e, g[2], p); b.x(g[2]);
                    b.x(g[3]); b.and_c(e, g[3], qh); b.and_c(p, g[3], wq); b.x(g[3]);
                    b.cx(wq, p); b.cx(wq, qh);
                    vec![wq, qh, p]
                }
            };
            b.and_c(g[0], g[1], loan);
            b.cx(loan, g[0]);
            b.cx(loan, g[1]);
            b.cx(e, f);
            for l in 0..m - 1 {
                toggle_low_view(b, high[l >> 2], &g, loan, f, l & 3);
                if l + 2 < m {
                    mterm(b, f, bsig[l + 2], q_core[l]);
                }
            }
            b.cx(loan, g[1]);
            b.cx(loan, g[0]);
            b.and_u(g[0], g[1], loan);
            match ng {
                1 => {}
                2 => {
                    b.cx(hl3[1], hl3[0]);
                    b.cx(e, hl3[0]);
                    b.and_u(e, g[2], hl3[1]);
                }
                _ => {
                    let (p, qh, wq) = (hl3[0], hl3[1], hl3[2]);
                    b.cx(wq, qh); b.cx(wq, p);
                    b.x(g[3]); b.and_u(p, g[3], wq); b.and_u(e, g[3], qh); b.x(g[3]);
                    b.x(g[2]); b.and_u(e, g[2], p); b.x(g[2]);
                }
            }
        }
        conjugate_sources(b);
    });
    sec(b, "er.undo", |b| {
        b.play(&dr, true);
        b.play(&nr, true);
        // Lane LILY-A: the charted V1 mask term, read once U1 is back in place (the normalizer permutes U lanes).
        if boff == 0 && v1_charted(t) { v1_mask_toggle(b, w, tn, e, q_core[m - 1]); }
        if no_d { d_host_toggle(b); }
        if hold { b.cx(z0, pq); b.cx(z1, pq); } else { b.play(&ft, false); }
        b.play(&fe, true);
        b.play(&fd, true);
        b.play(&ft, true);
    });
    if donor_view { b.cx(sc.sg, v0); b.x(v0); b.x(g0l); }
    lsc_from(b, w, tn, cz, kv, kc, a_span, b_span);
    true
}

/// At S, an otherwise successful walk can have g=0 while its last digit run
/// is still open (h<0).  Such a word uses the direct c_f window beginning at
/// sig1, unlike the deferred even-tick eraser above which begins at sig2.
pub(crate) fn terminal_eraser(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr) -> [usize; 4] {
    let n0 = b.ops.len();
    let t = sch.s;
    let tn = t + 1;
    let q = w.qfr(t);
    let qb = q.len();
    let lv = usize::BITS as usize - (qb + 1).leading_zeros() as usize;
    let nt = (1usize << lv) - 1;
    let wl = nt + qb + 1;
    let (cz, kv, kc) = (sch.c[tn], sch.kv[tn], sch.kc[tn]);
    let zl0 = lsc_from(b, w, tn, cz, kv, kc, 1 + wl, 1 + wl);
    let busy: Vec<QubitId> = (0..1 + wl)
        .map(|k| w.asig(tn, k))
        .chain((0..1 + wl).map(|k| w.bsig(k)))
        .collect();
    let zl: Vec<QubitId> = zl0.iter().copied().filter(|x| !busy.contains(x)).collect();
    let e = sc.e;
    let a0 = w.asig(tn, 0);

    // Lilypad-GCD records original e (not gatesim's r=e^sigma).  Therefore
    // c_f bit1 is not a valid terminal-open discriminator: an unfinished run
    // is exactly h<0 at the public end.
    b.cx(w.h[HB - 1], e);

    let a: Vec<QubitId> = (0..wl).map(|k| w.asig(tn, 1 + k)).collect();
    let u = &a[..qb + 1];
    let g = &sc.sp[..lv];
    b.begin();
    for k in (0..lv).rev() {
        let s = 1usize << k;
        let lits: Vec<(QubitId, bool)> = a[..s].iter().map(|&x| (x, true)).collect();
        let mut temps = sc.tmp.clone();
        temps.push(a0);
        temps.extend(&sc.sp[..k]);
        temps.extend(&sc.pool);
        temps.extend(&zl);
        b.mbu_compute(sc.sp[k], &lits, &temps);
        for x in 0..wl - s {
            b.cswap(sc.sp[k], a[x], a[x + s]);
        }
    }
    let nr = b.end();
    sec(b, "er.term.norm", |b| b.play(&nr, false));

    let from_pool = nt.min(sc.pool.len());
    let from_tmp = nt - from_pool;
    assert!(sc.tmp.len() >= from_tmp, "terminal eraser needs {nt} thermometer lanes");
    let mut th = sc.pool[..from_pool].to_vec();
    th.extend_from_slice(&sc.tmp[..from_tmp]);
    let rest = &zl[..];
    let bv: Vec<QubitId> = (0..qb + 1).map(|k| w.bsig(k)).collect();
    b.begin();
    // Thermometer of the normalizer shift.
    for j in 0..lv {
        let r = 1usize << j;
        for k in (0..nt - r).rev() {
            b.cswap(g[j], th[k], th[k + r]);
        }
        for &x in &th[..r] {
            b.cx(g[j], x);
        }
    }
    // B <- B - u, temporarily.
    let mut apool = sc.tmp[from_tmp..].to_vec();
    apool.extend(&sc.pool[from_pool..]);
    apool.extend(rest);
    b.begin();
    for &x in &bv {
        b.x(x);
    }
    b.x(a0);
    ctrl_add_pool(b, u, &bv, a0, &apool);
    b.x(a0);
    for &x in &bv {
        b.x(x);
    }
    let dsub = b.end();
    b.play(&dsub, false);
    let cc = sc.tmp[from_tmp];
    for k in 0..qb.min(nt) {
        b.and_c(e, bv[k + 1], cc);
        b.ccx(cc, th[k], q[k]);
        b.and_u(e, bv[k + 1], cc);
    }
    b.play(&dsub, true);
    for j in (0..lv).rev() {
        let r = 1usize << j;
        for &x in &th[..r] {
            b.cx(g[j], x);
        }
        for k in 0..nt - r {
            b.cswap(g[j], th[k], th[k + r]);
        }
    }
    let mid = b.end();
    sec(b, "er.term.word", |b| b.play(&mid, false));
    let nword = b.ops.len();

    let c1 = sc.tmp[0];
    sec(b, "er.term.rot", |b| {
        // Exact gatesim.py qrot convention in qfr(t) coordinates.  A bit
        // starting at lane 0 moves through the cycle to lane QB-r.
        for k in 0..lv {
            let r = (1usize << k) % qb;
            b.and_c(g[k], e, c1);
            let mut seen = vec![false; qb];
            for s0 in 0..qb {
                if seen[s0] {
                    continue;
                }
                let mut cyc = vec![];
                let mut j = s0;
                while !seen[j] {
                    seen[j] = true;
                    cyc.push(j);
                    j = (j + r) % qb;
                }
                for i in 0..cyc.len().saturating_sub(1) {
                    b.cswap(c1, q[cyc[i]], q[cyc[i + 1]]);
                }
            }
            b.and_u(g[k], e, c1);
        }
    });
    let nrot = b.ops.len();
    // Literal inverse of gatesim.py's triangular F-gated multiply.  The
    // deferred eraser's radix-4 shortcut is not equivalent for every direct
    // terminal word.
    b.begin();
    let mc_mul = sc.tmp[0];
    let mut mpool = sc.tmp[1..].to_vec();
    mpool.push(a0);
    mpool.extend(&sc.pool);
    mpool.extend(rest);
    for i in (0..qb - 1).rev() {
        let nn = qb - 1 - i;
        b.and_c(e, q[i], mc_mul);
        if nn == 1 {
            b.ccx(mc_mul, u[1], q[i + 1]);
        } else {
            ctrl_add_pool(b, &u[1..1 + nn], &q[i + 1..i + 1 + nn], mc_mul, &mpool);
        }
        b.and_u(e, q[i], mc_mul);
    }
    let direct_mul = b.end();
    sec(b, "er.term.mul", |b| b.play(&direct_mul, true));
    // gatesim records r=e^sigma; Lilypad-GCD records the original e and must
    // additionally regenerate the swap marker.  Add it after the digit
    // decoder so it is not transformed by the inverse multiply.  The unary
    // thermometer boundary k marks ic=k+1, hence lane QB-2-k.
    sec(b, "er.term.marker", |b| {
        for j in 0..lv {
            let r = 1usize << j;
            for k in (0..nt - r).rev() {
                b.cswap(g[j], th[k], th[k + r]);
            }
            for &x in &th[..r] {
                b.cx(g[j], x);
            }
        }
        // ic=0: no thermometer lane is set, so the marker stays at the top.
        let mz = sc.tmp[from_tmp + 1];
        let mlits: Vec<(QubitId, bool)> = g.iter().map(|&x| (x, true)).collect();
        b.mbu_compute(mz, &mlits, &sc.tmp[from_tmp + 2..]);
        b.ccx(e, mz, q[qb - 1]);
        b.mbu_erase(mz, &mlits, &sc.tmp[from_tmp + 2..]);
        let mc = sc.tmp[from_tmp];
        for k in 0..(qb - 1).min(nt - 1) {
            b.and_c(e, th[k], mc);
            b.x(th[k + 1]);
            b.ccx(mc, th[k + 1], q[qb - 2 - k]);
            b.x(th[k + 1]);
            b.and_u(e, th[k], mc);
        }
        for j in (0..lv).rev() {
            let r = 1usize << j;
            for &x in &th[..r] {
                b.cx(g[j], x);
            }
            for k in 0..nt - r {
                b.cswap(g[j], th[k], th[k + r]);
            }
        }
    });
    let nmul = b.ops.len();
    sec(b, "er.term.undo", |b| b.play(&nr, true));

    b.cx(w.h[HB - 1], e);
    lsc_from(b, w, tn, cz, kv, kc, 1 + wl, 1 + wl);
    [n0, nword, nrot, nmul]
}

/// Forward walk: init, ticks 1..=S, e X-measured each tick. Returns the measurement bits (index t).
pub fn walk_forward(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr, division: Option<usize>) -> Vec<BitId> {
    init(b, w);
    let m = b.fresh_bits(sch.s + 1);
    for t in 1..=sch.s {
        step_core(b, w, t, sch, sc, sc.e, &[], division.map(|d| (d, false)));
        halve_h(b, w, t, sch, sc);
        b.hmr_to(sc.e, m[t]);
    }
    m
}

/// Regenerating tick t as two recordings: (step core, halve + marker clear / eraser).
pub fn rec_regen(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr, division: Option<usize>) -> (Vec<G>, Vec<G>) {
    let qe = w.qfr(t)[w.q.len() - 1];
    let mut extra = vec![sc.e];
    extra.extend(&sc.d);
    extra.extend(&sc.sp);
    b.begin();
    step_core(b, w, t, sch, sc, qe, &extra, division.map(|d| (d, true)));
    let p1 = b.end();
    b.begin();
    halve_h(b, w, t, sch, sc);
    if t % 2 == 1 {
        mclear(b, w, t, sc, false);
    } else {
        eraser(b, w, t, sch, sc, 0, false, None, false, false);
        if t == sch.s {
            // `terminal_eraser` emits the inverse-walk un-eraser U.  This
            // function is recording the forward regeneration block p3,
            // which walk_inverse later reverses, so record U^-1 here.
            b.begin();
            let _ = terminal_eraser(b, w, sch, sc);
            let term_unerase = b.end();
            b.play(&term_unerase, true);
        }
    }
    let p3 = b.end();
    (p1, p3)
}

/// Inverse of walk_forward (Q clean in w.q; clean again afterwards).
pub fn walk_inverse(b: &mut B, w: &PWalk, sch: &PSched, sc: &PScr, m: &[BitId], division: Option<usize>) {
    SEC_INV.with(|c| c.set(true));
    for t in (1..=sch.s).rev() {
        let (p1, p3) = rec_regen(b, w, t, sch, sc, division);
        b.play(&p3, true);
        b.z_if(w.qfr(t)[w.q.len() - 1], m[t]);
        b.play(&p1, true);
    }
    init(b, w);
    SEC_INV.with(|c| c.set(false));
}
