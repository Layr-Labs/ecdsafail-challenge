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
use super::builder::{B, G, ONE};
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

const L4_REPAIRED_CAP: bool = true;

/// R4-ERASE switch (false = the R2-LANES tree, byte-identical): the L5 eraser multiplies on the full 13-lane Q frame
/// with uncontrolled signed-digit rows (`r4e_sdm_mul`) instead of e-controlled binary/Booth rows on 12 lanes.
pub(crate) const R4E_SDM: bool = true;
#[cfg(test)]
thread_local! { static R4E_SDM_TEST: std::cell::Cell<i8> = const { std::cell::Cell::new(-1) }; }
#[cfg(test)]
pub(crate) fn r4e_sdm_override(v: Option<bool>) { R4E_SDM_TEST.with(|c| c.set(v.map_or(-1, i8::from))); }
/// Test-only negative controls (0 = none): 1 = skip the D-word up-rotation, 2 = mask on q[..12] (frame off by one),
/// 3 = drop the merged row 0 (closing subtract) of the signed rows.
#[cfg(test)]
thread_local! { static R4E_NEG: std::cell::Cell<u8> = const { std::cell::Cell::new(0) }; }
#[cfg(test)]
pub(crate) fn r4e_neg_set(m: u8) { R4E_NEG.with(|c| c.set(m)); }
fn r4e_neg(m: u8) -> bool {
    #[cfg(test)]
    { return R4E_NEG.with(|c| c.get() == m); }
    #[cfg(not(test))]
    { let _ = m; false }
}
/// R4-ERASE switch (false = byte-identical): the L5 normalizer cswaps only the lanes a completing L5 word can read
/// (`norm_need_l5`, one fewer at the k=3 and rot4 levels, window 23 lanes instead of 24).
pub(crate) const R4E_NORM_TRIM: bool = true;
#[cfg(test)]
thread_local! { static R4E_TRIM_TEST: std::cell::Cell<i8> = const { std::cell::Cell::new(-1) }; }
#[cfg(test)]
pub(crate) fn r4e_trim_override(v: Option<bool>) { R4E_TRIM_TEST.with(|c| c.set(v.map_or(-1, i8::from))); }
fn r4e_trim_enabled() -> bool {
    #[cfg(test)]
    { return R4E_TRIM_TEST.with(|c| match c.get() { 0 => false, 1 => true, _ => R4E_NORM_TRIM }); }
    #[cfg(not(test))]
    { R4E_NORM_TRIM }
}
/// R4-ERASE switch (8 = byte-identical): smallest lend list that holds the L5 flags (z0, z1, y) across the eraser
/// instead of recomputing them in the undo (C50 "hold" took 8).
pub(crate) const R4E_HOLD_MIN: usize = 3;
#[cfg(test)]
thread_local! { static R4E_HOLD_TEST: std::cell::Cell<usize> = const { std::cell::Cell::new(usize::MAX) }; }
#[cfg(test)]
pub(crate) fn r4e_hold_override(v: Option<usize>) { R4E_HOLD_TEST.with(|c| c.set(v.unwrap_or(usize::MAX))); }
fn r4e_hold_min() -> usize {
    #[cfg(test)]
    { let v = R4E_HOLD_TEST.with(|c| c.get()); if v != usize::MAX { return v; } }
    R4E_HOLD_MIN
}
fn r4e_sdm_enabled() -> bool {
    #[cfg(test)]
    { return R4E_SDM_TEST.with(|c| match c.get() { 0 => false, 1 => true, _ => R4E_SDM }); }
    #[cfg(not(test))]
    { R4E_SDM }
}

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
    pub fn alloc_inv_g(b: &mut B, room: usize) -> PScr {
        PScr {
            e: b.alloc(),
            sg: b.alloc(),
            d: b.alloc_n(super::lilypad_g::inverse_d_len_g()),
            tmp: b.alloc_n(super::lilypad_g::inverse_tmp_len_g()),
            sp: b.alloc_n(super::lilypad_g::inverse_sp_len_g()),
            pool: b.alloc_n(room),
        }
    }
    pub fn release(self, b: &mut B) {
        b.free(self.e);
        b.free(self.sg);
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
    for f in kv..c {
        b.cx(w.af(t, kv - 1), w.af(t, f));
        b.cx(w.bf(kv - 1), w.bf(f));
        z.extend([w.af(t, f), w.bf(f)]);
    }
    for s in kc.max(a_lo)..wd - c {
        b.cx(w.asig(t, kc - 1), w.asig(t, s));
        z.push(w.asig(t, s));
    }
    for s in kc.max(b_lo)..wd - c {
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

/// Share the increment's AND prefix with the odd-tick marker. The caller provides
/// the complete halve recording; matching the exact increment trace makes source drift fail closed.
pub(super) fn inc_mclear_fused(b:&mut B,w:&PWalk,t:usize,sc:&PScr,r:&[G],half:bool)->Vec<G> {
    let mut n=2usize;while n<HB && (1usize<<(n-1))-1<t {n+=1;}
    let mut tmp=sc.tmp.clone();if tmp.is_empty(){tmp.push(sc.e);}tmp.extend(&sc.sp);
    b.begin();inc_unctl(b,&w.h[..n],&tmp);let inc=b.end();
    let starts:Vec<_>=r.windows(inc.len()).enumerate().filter(|(_,x)|*x==&inc[..]).map(|(i,_)|i).collect();
    assert_eq!(starts.len(),1,"increment/mclear source match tick{t}");
    let at=starts[0]+n.saturating_sub(2);
    let prefix=if n==2 {w.h[0]}else{tmp[n-3]};let all=sc.d[0];
    let cf1=w.asig(t+1,1-usize::from(half));let q=w.qfr(t);let mut out=r[..at].to_vec();
    out.extend([G::AndC(prefix,w.h[n-1],all),G::Ccx(all,cf1,q[q.len()-1]),G::AndU(prefix,w.h[n-1],all)]);
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

/// R7-WALK switch (env R7W_CAP2 unset = byte-identical): the run cap runs only on even ticks. A swap on an odd tick
/// t-1 is clamped at tick t (h = -h_old + 1 -> -10, same h as today's clamp-then-increment); a swap on an even tick is
/// clamped at its own tick as before. E = [h <= -11 + !sigma], target -11 + !sigma, slot0 = low4(h') ^ low4(target).
/// Decisions, rho, h after every even tick and both log bit0s are identical to today's (R7-WALK/captree.py).
pub(crate) fn r7w_cap2() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("R7W_CAP2").map_or(true, |v| v != "0")) // R8-PACK: default on; R7W_CAP2=0 = off
}

pub(super) fn cap_logic_r7w(b: &mut B, w: &PWalk, sc: &PScr) {
    let h = &w.h;
    assert!(w.capq == 11 && HB == 6 && c50_enabled(1) && c50_enabled(128) && w.log.len() == 8);
    let mut work=sc.tmp.clone();work.extend(&sc.sp);work.extend(&sc.pool);work.extend(&sc.d);
    if sc.tmp.is_empty() { work.push(sc.e); }
    assert!(work.len()>=7);
    let (c3,c4,c5,ee,gated,xa,xb)=(work[0],work[1],work[2],work[3],work[4],work[5],work[6]);
    let sg = sc.sg;
    // xa = sg | h0; c3 = h2 & h1 & xa (sigma: low5 >= 22 <=> h > -11; no sigma: low5 >= 23 <=> h > -10)
    b.x(sg);b.x(h[0]);b.and_c(sg,h[0],xa);b.x(h[0]);b.x(sg);b.x(xa);
    b.and_c(h[2],h[1],xb);
    b.and_c(xb,xa,c3);
    b.x(h[3]);b.x(c3);b.and_c(h[3],c3,c4);b.x(c3);b.x(h[3]);b.x(c4);
    b.and_c(h[4],c4,c5);
    b.x(c5);b.and_c(h[HB - 1],c5,ee);b.x(c5);
    b.and_u(h[4],c4,c5);
    b.x(c4);b.and_c(ee,c4,gated);b.x(c4);
    b.cx(gated,h[4]);b.cx(ee,h[4]);
    b.x(c4);b.and_u(ee,c4,gated);b.x(c4);
    b.x(c4);b.x(h[3]);b.x(c3);b.and_u(h[3],c3,c4);b.x(c3);b.x(h[3]);
    b.and_u(xb,xa,c3);
    b.and_u(h[2],h[1],xb);
    b.x(xa);b.x(sg);b.x(h[0]);b.and_u(sg,h[0],xa);b.x(h[0]);b.x(sg);
    for i in 0..4 {b.cswap(ee,w.log[i],w.log[4+i]);}
    for i in 0..4 {b.cswap(ee,h[i],w.log[i]);}
    for j in [0usize,2] {b.cx(ee,h[j]);b.cx(ee,w.log[j]);}
    // no sigma: target -10 (low4 0110) instead of -11 (0101): flip bits 0 and 1 of h and of the slot code
    b.x(sg);b.and_c(ee,sg,gated);b.x(sg);
    for j in [0usize,1] {b.cx(gated,h[j]);b.cx(gated,w.log[j]);}
    b.x(sg);b.and_u(ee,sg,gated);b.x(sg);
    if !sc.tmp.is_empty() {
        let receipt=b.fresh_bits(1)[0];b.hmr_to(ee,receipt);
        C50_CAP_TAPES.with(|v|v.borrow_mut().push(receipt));
    } else {
        let receipt=C50_CAP_TAPES.with(|v|v.borrow_mut().pop().expect("inverse cap without forward E receipt"));
        b.z_if(ee,receipt);
        // E = h5 & !h3 & (h0 ^ h1) & !(h0 ^ sigma) on the post-cap support (both sigma cases)
        b.cx(h[0],h[1]);b.cx(h[0],sg);
        b.mbu_erase(ee,&[(h[HB - 1],false),(h[3],true),(h[1],false),(sg,true)],&[c3,c4]);
        b.cx(h[0],sg);b.cx(h[0],h[1]);
    }
}

/// R8-TRIM switch (env R8T_CAPK=k, unset = byte-identical): the run cap runs only on ticks t > 11 with t % k == 0 or
/// t == S. d = ticks since the last swap, saturated at k-1, is read as a thermometer from sigma and U = C_F/2's low
/// lanes (tz(U) = d: U is odd after a swap and doubles by relabel otherwise); h <- h - d (= the swap's h');
/// today's C50 kernel unchanged on h'; h <- h + d. Slot code and inverse predicate are today's (R8-TRIM/capk_automaton.py).
pub(crate) fn r8t_capk() -> usize {
    static K: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *K.get_or_init(|| std::env::var("R8T_CAPK").ok().map(|v| v.parse().expect("R8T_CAPK")).unwrap_or(11)) // R8-PACK: default 11; R8T_CAPK=0 = off
}
pub(crate) fn r8t_cap_tick(t: usize, s: usize, k: usize) -> bool { t % k == 0 || t == s }
/// Thermometer length at a check tick: k on the grid; at the off-grid end tick, the gap since the last grid check.
pub(crate) fn r8t_cap_k(t: usize, k: usize) -> usize { if t % k == 0 { k } else { t % k } }

/// h (6 lanes) += d (lanes low first, 1..=4) mod 64; c: 5 clean carry lanes (and_c / measured and_u).
fn r8t_add6(b: &mut B, h: &[QubitId], d: &[QubitId], c: &[QubitId]) {
    let n = d.len();
    assert!(h.len() == 6 && (1..=4).contains(&n) && c.len() >= 5);
    b.and_c(h[0], d[0], c[0]);
    for i in 1..5 {
        if i < n { b.cx(c[i-1], h[i]); b.cx(c[i-1], d[i]); b.and_c(h[i], d[i], c[i]); b.cx(c[i-1], c[i]); }
        else { b.and_c(h[i], c[i-1], c[i]); }
    }
    b.cx(c[4], h[5]);
    for i in (1..5).rev() {
        if i < n { b.cx(c[i-1], c[i]); b.and_u(h[i], d[i], c[i]); b.cx(c[i-1], d[i]); b.cx(d[i], h[i]); }
        else { b.and_u(h[i], c[i-1], c[i]); b.cx(c[i-1], h[i]); }
    }
    b.and_u(h[0], d[0], c[0]); b.cx(d[0], h[0]);
}

pub(super) fn cap_logic_r8t(b: &mut B, w: &PWalk, sc: &PScr, t: usize, sch: &PSched, k: usize) {
    let h = &w.h;
    assert!(w.capq == 11 && HB == 6 && c50_enabled(1) && c50_enabled(128) && w.log.len() == 8 && (2..=12).contains(&k));
    assert!(sch.kc[t + 1] > k - 2, "R8T_CAPK: cofactor lanes");
    let u: Vec<QubitId> = (0..k - 1).map(|j| w.asig(t + 1, j)).collect();
    let nt = k - 1; // D0, T2..T_{k-1}
    assert!(sc.pool.len() >= nt, "R8T_CAPK: pool {} < {}", sc.pool.len(), nt);
    let (keep, mine) = sc.pool.split_at(sc.pool.len() - nt);
    let view = PScr { e: sc.e, sg: sc.sg, d: sc.d.clone(), tmp: sc.tmp.clone(), sp: sc.sp.clone(), pool: keep.to_vec() };
    let mut work = view.tmp.clone(); work.extend(&view.sp); work.extend(&view.pool); work.extend(&view.d);
    if view.tmp.is_empty() { work.push(view.e); }
    assert!(work.len() >= 5);
    let c = &work[..5];
    let sg = sc.sg;
    let d0 = mine[0];
    let tl = |j: usize| mine[j - 1]; // T_j, j in 2..k
    for &q in u[1..].iter().chain(std::iter::once(&sg)) {
        assert!(!mine.contains(&q) && !work.contains(&q) && !h.contains(&q) && !w.log.contains(&q));
    }
    b.begin();
    if k > 2 { b.x(sg); b.x(u[1]); b.and_c(sg, u[1], tl(2)); b.x(u[1]); b.x(sg); }
    for j in 3..k { b.x(u[j-1]); b.and_c(tl(j-1), u[j-1], tl(j)); b.x(u[j-1]); }
    b.cx(sg, d0); b.x(d0);
    for j in 2..k { b.cx(tl(j), d0); }
    let mut i = 1;
    while (1usize << i) <= k - 1 {
        let p = 1usize << i;
        let mut j = 2 * p;
        while j < k { b.cx(tl(j), tl(p)); j += p; }
        i += 1;
    }
    let th = b.end();
    b.play(&th, false);
    let mut dl = vec![d0];
    let mut i = 1;
    while (1usize << i) <= k - 1 { dl.push(tl(1 << i)); i += 1; }
    for &q in h.iter() { b.x(q); }
    r8t_add6(b, h, &dl, c);
    for &q in h.iter() { b.x(q); }
    cap_logic(b, w, &view);
    r8t_add6(b, h, &dl, c);
    b.play(&th, true);
}

/// Run cap (after h' is formed, sigma live): E = sigma & [h' <= -q]; push o = -q - h' (4 bits) on the log, h' <- -q.
pub(super) fn cap_logic(b: &mut B, w: &PWalk, sc: &PScr) {
    let q = w.capq;
    let h = &w.h;
    if q==11 && (HB==6 || HB==7) && c50_enabled(1) {
        let mut work=sc.tmp.clone();work.extend(&sc.sp);work.extend(&sc.pool);work.extend(&sc.d);
        if sc.tmp.is_empty() { work.push(sc.e); }
        assert!(work.len()>=5);
        let (c3,c4,c5,ee,gated)=(work[0],work[1],work[2],work[3],work[4]);
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
        if w.log.len()==8 {for i in 0..4 {b.cswap(ee,w.log[i],w.log[4+i]);}}
        for i in 0..4 {b.cswap(ee,h[i],w.log[i]);}
        for j in [0usize,2] {b.cx(ee,h[j]);b.cx(ee,w.log[j]);}
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
            &[w.log[7]],
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

/// R4-ERASE: the L5 normalizer need. A completing L5 word has at most QB-1 lanes (m <= QB-2 digits) and its shift
/// gp is m-1 (Fd, terminal open word) or m (D), so the multiply reads u bits 0..min(gp+1, QB-2), one fewer than
/// `norm_need` assumes at gp = QB-2.
fn norm_need_l5(qb: usize, k: usize) -> usize {
    let rest = |gp: usize| if k >= 2 { gp & ((1 << k) - 1) } else { gp & 3 };
    (0..qb - 1)
        .filter(|&gp| k < 2 || (gp >> k) & 1 == 1)
        .map(|gp| (gp + 1).min(qb - 2) + 1 + rest(gp))
        .max()
        .unwrap_or(0)
}

fn win_len_l5(qb: usize) -> usize {
    let mut m = norm_need_l5(qb, 1);
    for k in 2..SB {
        let n = norm_need_l5(qb, k);
        if n > 0 {
            m = m.max(n + (1 << k));
        }
    }
    m.max(qb)
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
    b.ccx(e, bsig[1], q[qb - 1]);
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
                if l+2<qb {b.ccx(f,bsig[l+2],q[l]);}
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
                b.ccx(f,bsig[l+2],q[l]);
            }
            if c==0 {b.cx(p,hi);}
        }
        b.and_u(p,g[2],hi);
        b.x(g[3]); b.and_u(e,g[3],p); b.x(g[3]);
        let high=[(e,false),(g[2],true),(g[3],false)];
        b.mbu_compute(hi,&high,&[p]);
        for l in 8..qb-1 {
            toggle_low_view(b,hi,g,loan,f,l&3);
            if l+2<qb {b.ccx(f,bsig[l+2],q[l]);}
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
                    b.ccx(f, bsig[l + 2], q[l]);
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
                b.ccx(f, bsig[l + 2], q[l]);
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
                b.ccx(f, bsig[l + 2], q[l]);
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
                b.ccx(f, bsig[l + 2], q[l]);
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
                b.ccx(f, bsig[l + 2], q[l]);
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
    let tn = t + 1;
    let q = w.qfr(t);
    let qb = q.len();
    // R4-ERASE: words are multiplied top-aligned in the full 13-lane frame, so D words (top at QB-2) move up one lane
    // instead of Fd words moving down; every completing word then has lane 0 clear (see r4e_sdm_mul).
    let sdm = pre_swap && half_cofactor && g_rho.is_some() && qb == 13 && r4e_sdm_enabled();
    let trim = pre_swap && half_cofactor && g_rho.is_some() && qb == 13 && w.capq + 2 == qb && r4e_trim_enabled();
    let nn = |k: usize| if trim { norm_need_l5(qb, k) } else { norm_need(qb, k) };
    let wl = if trim { win_len_l5(qb) } else { win_len(qb) };
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
    let hold=pre_swap && c50_enabled(8) && zl.len()>=r4e_hold_min();
    let held=if hold {zl.drain(..3).collect::<Vec<_>>()}else{vec![]};
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
        assert!(tm.len() == 1 && !sc.d.is_empty(), "zero-pool eraser needs its sole temporary after flag cleanup");
        tm[0]
    } else {
        w.asig(tn, 0)
    };
    let free_pool = if a0_from_pool { &sc.pool[1..] } else { &sc.pool[..] };
    let low_scratch = pre_swap && half_cofactor && tm.len() == 1 && sc.sp.len() == 4;
    let d = sc.d[0];
    let mut flag_tmp = tm.clone();
    if flag_tmp.len() < 5 {
        flag_tmp.extend_from_slice(&sc.sp[..5 - flag_tmp.len()]);
    }
    let (pq, z0, z1, y, wn) = if hold {
        (flag_tmp[0],held[0],held[1],held[2],flag_tmp[4])
    }else{(flag_tmp[0],flag_tmp[1],flag_tmp[2],flag_tmp[3],flag_tmp[4])};
    let mut hn=HB;
    if c50_enabled(32) {hn=2;while hn<HB && (1usize<<(hn-1))-1<t {hn+=1;}}
    let hl: Vec<(QubitId, bool)> = w.h[1..hn].iter().map(|&x| (x, true)).collect();
    // These four flag outputs are still clean while pq is synthesized and
    // are restored by the MBU compute before they receive their own values.
    let htemps = vec![z0, z1, y, wn];
    // flags
    b.begin();
    b.mbu_compute(pq, &hl, &htemps);
    b.x(w.h[0]);
    b.and_c(pq, w.h[0], z0);
    b.x(w.h[0]);
    if c50_enabled(2) {b.cx(pq,z1);b.cx(z0,z1);}else{b.and_c(pq, w.h[0], z1);}
    if pre_swap {
        b.and_c(z0, sc.sg, y);
    } else {
        b.and_c(z0, cf1, y);
        b.x(cf1);
        b.and_c(z1, cf1, wn);
        b.x(cf1);
    }
    let ft = b.end();
    b.begin();
    if pre_swap {
        // D = (y | [h=1]) & !X.c2; y and z1 are exclusive.
        b.cx(z1, y);
        b.x(cf2);
        b.and_c(y, cf2, d);
        b.x(cf2);
        b.cx(z1, y);
    } else if g_rho.is_some() {
        // In raw stored-G coordinates, Y.c sig2 is c_f(pre-swap) bit1.
        // Its zero value distinguishes an Fs completion at h=0.
        let yc2 = w.bsig(2 - cofactor_shift);
        b.x(yc2);
        b.and_c(y, yc2, d);
        b.x(yc2);
    } else {
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
    b.begin();
    b.cx(z0, e);
    b.cx(y, e);
    b.cx(d, e);
    let neg = |name: &str| match name {
        "noFt" => l2_neg(8),
        "noFm" => l2_neg(9),
        "noFsfix" => l2_neg(10),
        _ => false,
    };
    let swap_flag = if pre_swap && !l5_neg(2) { sc.sg } else { cf1 };
    if terminal && !neg("noFt") {
        b.x(swap_flag);
        b.ccx(w.h[HB - 1], swap_flag, e);
        b.x(swap_flag);
    }
    let fe = b.end();
    sec(b, "er.flags", |b| {
        b.play(&ft, false);
        b.play(&fd, false);
        b.play(&fe, false);
        b.cx(y, q[qb - 1]);
        if terminal && !neg("noFm") {
            b.ccx(w.h[HB - 1], swap_flag, q[qb - 1]);
        }
        if hold {b.cx(z0,pq);b.cx(z1,pq);}else{b.play(&ft, true);}
    });
    let narrow_core = pre_swap;
    if narrow_core {
        assert_eq!(w.capq + 2, qb, "L5 12-lane eraser needs run cap q = QB - 2");
        sec(b, "er.qrot", |b| {
            if sdm {
                if !r4e_neg(1) {
                    crot_up(b, d, &q, 1);
                }
                return;
            }
            b.cx(d, e);
            crot_up(b, e, &q, qb - 1);
            b.cx(d, e);
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
    let g = &sc.sp[..SB];
    b.begin();
    for k in (0..SB).rev() {
        let s = 1usize << k;
        if k >= 2 && nn(k) == 0 {
            continue;
        }
        let lits: Vec<(QubitId, bool)> = win[..s].iter().map(|&x| (x, true)).collect();
        let mut temps: Vec<QubitId> = sc
            .tmp
            .iter()
            .copied()
            .filter(|&q| q != a0)
            .collect();
        temps.push(a0);
        temps.extend(&sc.sp[..k]);
        temps.extend(free_pool);
        temps.extend(&zl);
        if temps.len() + 2 >= s {
            b.mbu_compute(sc.sp[k], &lits, &temps);
        } else {
            let (pq, rest) = temps.split_last().unwrap();
            b.mbu_compute(*pq, &lits[..s / 2], rest);
            let mut l2 = vec![(*pq, false)];
            l2.extend(&lits[s / 2..]);
            b.mbu_compute(sc.sp[k], &l2, rest);
            b.mbu_erase(*pq, &lits[..s / 2], rest);
        }
        if k == 1 {
            let tt = sc.tmp[0];
            b.and_c(sc.sp[1], win[2], tt);
            b.mbu_compute(sc.sp[0], &[(win[0], true), (tt, true)], &[]);
            b.and_u(sc.sp[1], win[2], tt);
            let rv: Vec<QubitId> = win[..nn(1)].iter().rev().cloned().collect();
            rot4_up(b, sc.sp[0], sc.sp[1], &rv);
            break;
        }
        for x in 0..nn(k) {
            b.cswap(sc.sp[k], win[x], win[x + s]);
        }
    }
    let nr = b.end();
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
    if dtmp.len() < SB - 2 {
        dec4_dirty(b, d, g, &q_core[..2]);
    } else if dtmp.len() >= SB - 1 {
        dec(b, d, g, &dtmp[..SB - 1]);
    } else {
        dec_topless(b, d, g, &dtmp[..SB - 2]);
    }
    let dr = b.end();
    sec(b, "er.dec", |b| b.play(&dr, false));
    let mut pool: Vec<QubitId> = if low_scratch {
        vec![]
    } else {
        sc.tmp.iter().copied().filter(|&q| q != a0).collect()
    };
    pool.push(a0);
    pool.extend(free_pool);
    pool.extend(&zl);
    sec(b, "er.mul", |b| {
        if sdm {
            r4e_sdm_mul(b, &win[1..qb], &q, e, &pool);
        } else {
            radix4_finish_mul(b, &win[1..core_bits], q_core, e, a0, &pool);
        }
    });
    // The SDM word sits one lane higher (top at QB-1) and never reaches lane 0 (word length <= QB-1), so rotate, top
    // fix and mask run on the 12-lane ring q[1..], in exactly the old core layout.
    let rq: Vec<QubitId> = if sdm { q[1..].to_vec() } else { q_core.clone() };
    let rq = &rq;
    if g_rho.is_some() && !l2_neg(4) {
        // Fd and the shared C6 endpoint-open word require the word's top bit
        // flipped by e xor d. This must happen after multiply, before rotate.
        b.cx(e, rq[rq.len() - 1]);
        b.cx(d, rq[rq.len() - 1]);
    }
    sec(b, "er.rot", |b| {
        if let Some(&loan) = zl.first() {
            let (c1, c2) = (a0, loan);
            for k in [0usize, 2] {
                b.and_c(g[k], e, c1);
                b.and_c(g[k + 1], e, c2);
                rot4_unit(b, c1, c2, rq, 1 << k);
                b.and_u(g[k + 1], e, c2);
                b.and_u(g[k], e, c1);
            }
        } else if low_scratch {
            for k in [0usize, 2] {
                b.and_c(g[k], e, a0);
                crot_up(b, a0, rq, 1 << k);
                b.and_u(g[k], e, a0);
                b.and_c(g[k + 1], e, a0);
                crot_up(b, a0, rq, 2 << k);
                b.and_u(g[k + 1], e, a0);
            }
        } else {
            let (c1, c2) = (sc.tmp[0], sc.tmp[1]);
            for k in [0usize, 2] {
                b.and_c(g[k], e, c1);
                b.and_c(g[k + 1], e, c2);
                rot4_unit(b, c1, c2, rq, 1 << k);
                b.and_u(g[k + 1], e, c2);
                b.and_u(g[k], e, c1);
            }
            if core_bits >= 18 {
                b.and_c(g[4], e, c1);
                crot_up(b, c1, rq, 16);
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
        let bsig: Vec<QubitId> = (0..core_bits).map(|k| w.bsig(boff + k)).collect();
        let conjugate_sources = |b: &mut B| {
            if let Some(rho) = g_rho {
                // Raw source bit 0 is constant; bits 1.. are conjugated by
                // phi = rho xor cf1. In physical lanes these are sig2..QB.
                for &x in &bsig[1..] {
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
        let mview: Vec<QubitId> = if sdm && r4e_neg(2) { q[..qb - 1].to_vec() } else { rq.clone() };
        finish_mask(b, &mview, &bsig, g, e, &mask_tmp, &mp, Some(d));
        conjugate_sources(b);
    });
    sec(b, "er.undo", |b| {
        b.play(&dr, true);
        b.play(&nr, true);
        if !neg("noFsfix") {
            b.play(&fs, true);
        }
        if hold {b.cx(z0,pq);b.cx(z1,pq);}else{b.play(&ft, false);}
        b.play(&fe, true);
        b.play(&fd, true);
        b.play(&ft, true);
    });
    if donor_view {b.cx(sc.sg,v0);b.x(v0);b.x(g0);}
    lsc_from(b, w, tn, cz, kv, kc, a_span, blo);
}

/// R4-ERASE signed-digit eraser multiply: q <- q (1 + 2 e a) mod 2^n (n = |q|, |a| = n - 1), exact when e = 0 (any q)
/// or e = 1 with q[0] = 0. Row p (p = n-2 down to 1) adds s_p a to q[p+1..] (uncontrolled, sign by X conjugation) with
/// s_p = 2 (e & q[p+1]) - 1, s_{n-2} = +1. With s_0 defined the same way, Sum_p s_p 2^p = e q + 1 (mod 2^(n-1)): the
/// signed rows add 2a (e q + 1), so row 0 and the closing -2a merge into one row that subtracts 4a from q[2..] when
/// s_0 = -1. Rows are top-down, so q[p+1] is still original when row p reads it; each row-p sign snapshot is erased
/// by measurement because the row leaves q[p+1] = old ^ a[0]. Toffoli: (n-2)(n-3)/2 + (n-3) carries for rows n-3..1,
/// n-2 sign ANDs, 2(n-2)-1 for the controlled row 0; versus ~(n-1)^2 for e-controlled binary rows.
pub(super) fn r4e_sdm_mul(b: &mut B, a: &[QubitId], q: &[QubitId], e: QubitId, pool: &[QubitId]) {
    let n = q.len();
    assert!(n >= 3 && a.len() == n - 1 && pool.len() >= 2);
    let (sgn, carries) = (pool[0], &pool[1..]);
    assert!(!q.contains(&sgn) && !a.contains(&sgn) && sgn != e && !q.contains(&e) && !a.contains(&e));
    assert!(carries.iter().all(|x| !q.contains(x) && !a.contains(x) && *x != e));
    b.cx(a[0], q[n - 1]); // row n-2: +a 2^(n-1) mod 2^n
    for p in (1..n - 2).rev() {
        let t = &q[p + 1..];
        b.and_c(e, q[p + 1], sgn);
        for &x in t {
            b.cx(sgn, x);
            b.x(x);
        }
        if t.len() == 1 {
            b.cx(a[0], t[0]);
        } else {
            ctrl_add_pool(b, &a[..t.len()], t, ONE, carries);
        }
        for &x in t {
            b.x(x);
            b.cx(sgn, x);
        }
        b.cx(a[0], q[p + 1]);
        b.and_u(e, q[p + 1], sgn);
        b.cx(a[0], q[p + 1]);
    }
    if r4e_neg(3) {
        return;
    }
    // row 0 + closing subtract: q[2..] -= 4a when !(e & q[1]); q[1] is untouched, so the snapshot erases directly.
    let t = &q[2..];
    b.and_c(e, q[1], sgn);
    b.x(sgn);
    for &x in t {
        b.x(x);
    }
    if t.len() == 1 {
        b.ccx(sgn, a[0], t[0]);
    } else {
        ctrl_add_pool(b, &a[..t.len()], t, sgn, carries);
    }
    for &x in t {
        b.x(x);
    }
    b.x(sgn);
    b.and_u(e, q[1], sgn);
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
