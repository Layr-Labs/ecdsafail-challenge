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

const L4_REPAIRED_CAP: bool = true;
/// Lane LILY-B: cap-log slots hold o directly (see cap_logic_q_direct).
const LILYB_DIRECT_O_LOG: bool = true;

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

/// Six-bit signed delta. The q=11 cap keeps clean modeled walks in [-32, 31];
/// this cut is population-gated under the inherited lambda contract.
pub const HB: usize = 6;
/// The 12-lane L5 word has shifts 0..11, so four binary shift lanes are
/// sufficient.  The former fifth lane was identically zero.
pub const SB: usize = 4;
pub const NT: usize = 8;
/// Lilypad-G L5 uses the idle affine coordinate as restored dirty workspace;
/// the inverse walk therefore needs no persistent clean temporary lane.
pub const G_INV_NT: usize = 0;
/// Lane LILY-B: placeholder sigma owner of an inverse Lilypad-G walk that owns no sigma lane (each regenerated tick
/// hosts sigma in af(t, 0) = U0 of the next frame; see rec_regen_g).
pub const NO_SG: QubitId = QubitId(u64::MAX);

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
    pub fn alloc_fwd_g(b: &mut B, room: usize) -> PScr {
        PScr {
            e: b.alloc(),
            sg: b.alloc(),
            d: vec![],
            tmp: b.alloc_n(super::lilypad_g::forward_tmp_len_g()),
            sp: vec![],
            pool: b.alloc_n(room),
        }
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
    /// Lane LILY-B: inverse scratch without a sigma lane.
    pub fn alloc_inv_g_nosg(b: &mut B, room: usize) -> PScr {
        PScr {
            e: b.alloc(),
            sg: NO_SG,
            d: b.alloc_n(super::lilypad_g::inverse_d_len_g()),
            tmp: b.alloc_n(super::lilypad_g::inverse_tmp_len_g()),
            sp: b.alloc_n(super::lilypad_g::inverse_sp_len_g()),
            pool: b.alloc_n(room),
        }
    }
    pub fn release(self, b: &mut B) {
        b.free(self.e);
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

/// Increment a little-endian register with no clean carry chain. Borrowed
/// dirty lanes are restored by each multi-controlled toggle.
pub(crate) fn inc_unctl_dirty(b: &mut B, u: &[QubitId], dirty: &[QubitId]) {
    assert!(!u.is_empty());
    assert!(dirty.len() + 2 >= u.len() - 1);
    for i in (1..u.len()).rev() {
        let controls: Vec<(QubitId, bool)> = u[..i].iter().copied().map(|q| (q, false)).collect();
        super::mask::mc_xor(b, &controls, u[i], &[], dirty);
    }
    b.x(u[0]);
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

/// Run cap (after h' is formed, sigma live): E = sigma & [h' <= -q]; push o = -q - h' (4 bits) on the log, h' <- -q.
pub(super) fn cap_logic(b: &mut B, w: &PWalk, sc: &PScr) {
    let q = w.capq;
    let h = &w.h;
    #[cfg(test)]
    let direct_cap = std::env::var_os("LILYPAD_DIRECT_CAP").is_some();
    #[cfg(not(test))]
    let direct_cap = sc.tmp.len() < 6;
    if matches!(q, 10 | 11) && matches!(w.log.len(), 6..=8) && direct_cap {
        if w.q.len() >= 4 {
            // In regenerating ticks the digit is hosted in qe. sc.e is
            // clean after page3 arithmetic and before eraser flags begin.
            let event = sc.tmp.first().or_else(|| sc.d.first()).copied()
                .unwrap_or_else(||sc.sp.first().copied().unwrap_or(sc.e));
            if q == 11 {
                cap_logic_q11_direct(b, h, &w.log, sc.sg, event, &w.q[..4]);
            } else {
                cap_logic_q_direct(b, h, &w.log, sc.sg, event, &w.q[..4], q);
            }
            return;
        }
        if sc.tmp.len() >= 5 {
            if q == 11 {
                cap_logic_q11_direct(b, h, &w.log, sc.sg, sc.tmp[0], &sc.tmp[1..5]);
            } else {
                cap_logic_q_direct(b, h, &w.log, sc.sg, sc.tmp[0], &sc.tmp[1..5], q);
            }
            return;
        }
    }
    let mut work = sc.tmp.clone();
    work.extend(&sc.sp);
    work.extend(&sc.pool);
    // In inverse regeneration the deferral flag is still clean here; its
    // eraser lifetime starts only after the cap update.
    work.extend(&sc.d);
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
        lt_const(b, &h[..5], (33 - q) as u64, lt, &tm[1..5]);
        super::mask::mc_xor(
            b,
            &[(sc.sg, false), (h[h.len() - 1], false), (lt, false)],
            ee,
            &[],
            &[w.log[7]],
        );
        lt_const(b, &h[..5], (33 - q) as u64, lt, &tm[1..5]);
    } else {
        let sh = tm[6];
        lt_const(b, &h[..5], (33 - q) as u64, lt, &tm[2..6]);
        b.and_c(sc.sg, h[h.len() - 1], sh);
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
            lt_const(b, s0, (low_const + 1) as u64, flag, ctemps);
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

/// Exact q=11 cap with one clean event lane and arbitrary restored dirty
/// loans. This is the source-shaped low-width replacement for the two
/// comparator chains in `cap_logic`.
pub(crate) fn cap_logic_q11_direct(
    b: &mut B,
    h: &[QubitId],
    log: &[QubitId],
    sigma: QubitId,
    event: QubitId,
    dirty: &[QubitId],
) {
    assert!(h.len() >= 6);
    assert_eq!(log.len(), 8);
    assert!(dirty.len() >= 4);
    let toggle_event = |b: &mut B| {
        // [low5(h) < 22] = 1 ^ h1*h2*h4 ^ h3*h4 ^ h1*h2*h3*h4.
        for controls in [
            vec![(sigma, false), (h[h.len() - 1], false)],
            vec![(sigma, false), (h[h.len() - 1], false), (h[1], false), (h[2], false), (h[4], false)],
            vec![(sigma, false), (h[h.len() - 1], false), (h[3], false), (h[4], false)],
            vec![
                (sigma, false),
                (h[h.len() - 1], false),
                (h[1], false),
                (h[2], false),
                (h[3], false),
                (h[4], false),
            ],
        ] {
            super::mask::mc_xor(b, &controls, event, &[], dirty);
        }
    };

    toggle_event(b);
    for i in 0..4 {
        b.cswap(event, log[i], log[4 + i]);
        b.cswap(event, h[i], log[i]);
    }

    // q=11: low4(-q)=5. The fixed branch writes -11 assuming the high
    // nibble is 6, then [saved low4(h) < 6] toggles h4 to select nibble 7.
    for j in [0usize, 2, 4] {
        b.cx(event, h[j]);
    }
    b.cx(event, h[4]);
    super::mask::mc_xor(b, &[(event, false), (log[1], false), (log[2], false)], h[4], &[], dirty);
    b.ccx(event, log[3], h[4]);
    super::mask::mc_xor(
        b,
        &[(event, false), (log[1], false), (log[2], false), (log[3], false)],
        h[4],
        &[],
        dirty,
    );

    // Mandatory rho/empty-slot repair: saved low4(h) xor 5.
    b.cx(event, log[0]);
    b.cx(event, log[2]);
    toggle_event(b);
}

/// Exact no-clean-work cap for nearby q values. Boolean thresholds are
/// emitted as ANFs over the low h/log bits; the event lane is restored and
/// the four arbitrary dirty loans are unchanged.
pub(crate) fn cap_logic_q_direct(
    b: &mut B,
    h: &[QubitId],
    log: &[QubitId],
    sigma: QubitId,
    event: QubitId,
    dirty: &[QubitId],
    q: usize,
) {
    assert!(h.len() >= 6 && matches!(log.len(), 6..=8) && dirty.len() >= 4);
    assert!((9..=11).contains(&q));
    let anf_masks = |bits: usize, threshold: usize| {
        let mut f: Vec<u8> = (0..1usize << bits).map(|x| u8::from(x < threshold)).collect();
        for k in 0..bits {
            for mask in 0..1usize << bits {
                if mask & (1 << k) != 0 { f[mask] ^= f[mask ^ (1 << k)]; }
            }
        }
        f.into_iter().enumerate().filter_map(|(m, c)| (c != 0).then_some(m)).collect::<Vec<_>>()
    };
    let event_anf = anf_masks(5, 33 - q);
    let toggle_event = |b: &mut B| {
        // The widest threshold monomial has seven controls (sigma, h5,
        // h0..h4), so it needs five restored dirty loans.  The cap's saved
        // log lane is arbitrary state at both event boundaries and is not an
        // event control; it is therefore a valid fifth loan alongside the
        // four caller-provided lanes.
        let mut event_dirty = dirty.to_vec();
        event_dirty.push(log[0]);
        for &mask in &event_anf {
            let mut controls = vec![(sigma, false), (h[h.len() - 1], false)];
            controls.extend((0..5).filter(|k| mask & (1 << k) != 0).map(|k| (h[k], false)));
            super::mask::mc_xor(b, &controls, event, &[], &event_dirty);
        }
    };

    toggle_event(b);
    if LILYB_DIRECT_O_LOG && q == 10 && log.len() == 7 {
        // Lane LILY-B: before the push, transpose the two log states (slot1, slot0) = (1, 0) and (0, 7) under the
        // event. A push survives only from (0, s0 < 8); (1, 0) (older o = 1, newer o = 0) is 1.5x more frequent at a
        // push than (0, 7), and the parity log[0] ^ log[4] read by rho_stable is 1 on both. Conjugating by
        // log0 -> {log1, log2, log4} makes the pair differ in log0 only; the 4-control toggle also transposes
        // (2m+1, a) <-> (2m, a+7) for (m, a) != (0, 0), a in {0, 8}: both sides already fail the push, so the
        // success set changes by exactly the one pair. Played in reverse by the regenerating walk.
        for &j in &[1usize, 2, 4] { b.cx(log[0], log[j]); }
        super::mask::mc_xor(b, &[(event, false), (log[1], true), (log[2], true), (log[4], false)], log[0], &[], dirty);
        for &j in &[1usize, 2, 4] { b.cx(log[0], log[j]); }
    }
    for i in 0..4 {
        // The six-lane encoding omits bits 2 and 3 of the older slot.  Its
        // promoted support requires those bits to be zero at a second push.
        if 4 + i < log.len() { b.cswap(event, log[i], log[4 + i]); }
        b.cswap(event, h[i], log[i]);
    }

    let modulus = 1i64 << h.len();
    let cq = ((-(q as i64)) % modulus + modulus) % modulus;
    let low_const = cq as usize & 15;
    let upper = |low: i64| (((-(q as i64) - ((-(q as i64) - low).rem_euclid(16))).rem_euclid(modulus)) >> 4) as usize;
    let (upper_a, upper_b) = (upper(0), upper(15));
    let fixed = (upper_b << 4) ^ cq as usize;
    for j in 0..h.len() {
        if fixed & (1 << j) != 0 { b.cx(event, h[j]); }
    }
    if upper_a != upper_b {
        let cmp_anf = anf_masks(4, low_const + 1);
        for mask in cmp_anf {
            let mut controls = vec![(event, false)];
            controls.extend((0..4).filter(|k| mask & (1 << k) != 0).map(|k| (log[k], false)));
            for j in 4..h.len() {
                if (upper_a ^ upper_b) & (1 << (j - 4)) != 0 {
                    super::mask::mc_xor(b, &controls, h[j], &[], dirty);
                }
            }
        }
    }
    for j in 0..4 {
        if low_const & (1 << j) != 0 { b.cx(event, log[j]); }
    }
    if LILYB_DIRECT_O_LOG && q == 10 {
        // Lane LILY-B: store the overflow o = -q - h' itself in slot 0 instead of e = low4(h') ^ low4(-q).
        // For q = 10 (low4(-q) = 6), e = o for even o and e = o + 2 (mod 16) for odd o, so o = e - 2 [e odd]: a
        // 3-bit decrement of e[1..4] under event & e[0]. Bit 0 (the rho-invariant lane log[0], and log[4] after a
        // push) is unchanged. The compressed older slot of the 7-lane log keeps bits 0..2, so a second push now
        // fails only for an older o >= 8 (before: o in 7..14). Played in reverse by the regenerating walk.
        super::mask::mc_xor(b, &[(event, false), (log[0], false), (log[1], true), (log[2], true)], log[3], &[], dirty);
        super::mask::mc_xor(b, &[(event, false), (log[0], false), (log[1], true)], log[2], &[], dirty);
        b.ccx(event, log[0], log[1]);
    }
    toggle_event(b);
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
pub(super) fn mclear(
    b: &mut B,
    w: &PWalk,
    t: usize,
    sc: &PScr,
    half_cofactor: bool,
    external_dirty: &[QubitId],
) {
    let q = w.qfr(t);
    let qb = q.len();
    let lits: Vec<(QubitId, bool)> = w.h.iter().map(|&x| (x, true)).collect();
    let cf1 = w.asig(t + 1, 1 - usize::from(half_cofactor));
    #[cfg(test)]
    let direct = std::env::var_os("LILYPAD_DIRECT_FLAGS").is_some()
        || std::env::var_os("LILYPAD_DIRECT_MCLEAR").is_some();
    #[cfg(not(test))]
    let direct = sc.tmp.is_empty();
    if direct {
        let target = q[qb - 1];
        let dirty = if external_dirty.len() >= 6 { &external_dirty[..6] } else { &q[..6] };
        assert!(!dirty.contains(&target), "marker target aliases framed dirty loans");
        let mut marker = lits;
        marker.push((cf1, false));
        sec(b, "lily.mclr", |b| super::mask::mc_xor(b, &marker, target, &[], dirty));
        return;
    }
    if sc.tmp.len() == 1 {
        let (z0, y) = (sc.tmp[0], sc.d[0]);
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
    if one_temp && pool.len() >= 2 {
        let (f, hi) = (tmp[0], pool[0]);
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
                super::mask::mc_xor(b, &low, f, &[], &q[..1]);
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

fn ttk_add_ctrl2_dirty(
    b: &mut B,
    a: &[QubitId],
    t: &[QubitId],
    c1: QubitId,
    c2: QubitId,
    dirty: &[QubitId],
) {
    let n = t.len();
    assert_eq!(a.len(), n);
    assert!(n >= 2);
    let wr = |b: &mut B, i: usize| {
        super::mask::mc_xor(b, &[(c1, false), (c2, false), (a[i], false)], t[i], &[], dirty);
    };
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

pub(super) fn finish_mul_no_tmp(b: &mut B, a: &[QubitId], q: &[QubitId], e: QubitId, dirty: &[QubitId]) {
    for i in (0..q.len() - 1).rev() {
        let target = &q[i + 1..];
        if target.len() == 1 {
            super::mask::mc_xor(
                b,
                &[(e, false), (q[i], false), (a[0], false)],
                target[0],
                &[],
                dirty,
            );
        } else {
            ttk_add_ctrl2_dirty(b, &a[..target.len()], target, e, q[i], dirty);
        }
    }
}

pub(super) fn crot_up2_dirty(
    b: &mut B,
    c1: QubitId,
    c2: QubitId,
    v: &[QubitId],
    r: usize,
    dirty: &[QubitId],
) {
    let n = v.len();
    let r = r % n;
    if r == 0 { return; }
    let gcd = |mut a: usize, mut d: usize| {
        while d != 0 { (a, d) = (d, a % d); }
        a
    };
    for s in 0..gcd(n, r) {
        let len = n / gcd(n, r);
        let cyc: Vec<usize> = (0..len).map(|k| (s + k * r) % n).collect();
        for k in (1..len).rev() {
            let (a, c) = (v[cyc[k]], v[cyc[k - 1]]);
            b.cx(c, a);
            super::mask::mc_xor(b, &[(c1, false), (c2, false), (a, false)], c, &[], dirty);
            b.cx(c, a);
        }
    }
}

/// Completing-word mask with no clean flag lane.  Each output bit is toggled
/// directly for every gap value above its position.  Borrowed dirty lanes are
/// restored by `mc_xor`.
pub(super) fn finish_mask_no_tmp(
    b: &mut B,
    q: &[QubitId],
    bsig: &[QubitId],
    g: &[QubitId],
    e: QubitId,
    dirty: &[QubitId],
) {
    if threshold_mask_enabled() {
        finish_mask_threshold(b,q,bsig,g,e,dirty);
        return;
    }
    let qb = q.len();
    assert_eq!(g.len(), 4);
    assert!(qb >= 2 && qb <= 16);
    assert!(bsig.len() >= qb);
    assert!(dirty.len() >= 4);
    b.cx(e, q[qb - 2]);
    b.ccx(e, bsig[1], q[qb - 1]);
    for l in 0..qb - 2 {
        for value in l + 1..16usize {
            let mut controls = vec![(e, false), (bsig[l + 2], false)];
            controls.extend((0..4).map(|k| (g[k], value & (1 << k) == 0)));
            super::mask::mc_xor(b, &controls, q[l], &[], &dirty[..4]);
        }
    }
}

fn finish_mask_no_tmp_tail(
    b: &mut B,
    q: &[QubitId],
    bsig: &[QubitId],
    g: &[QubitId],
    e: QubitId,
    dirty: &[QubitId],
) {
    finish_mask_no_tmp_tail_from(b, q, bsig, g, e, dirty, 0);
}

fn finish_mask_no_tmp_tail_from(
    b: &mut B,
    q: &[QubitId],
    bsig: &[QubitId],
    g: &[QubitId],
    e: QubitId,
    dirty: &[QubitId],
    start: usize,
) {
    let qb = q.len();
    for l in start..qb - 2 {
        if threshold_mask_enabled(){
            for j in 0..4 {if l&(1<<j)!=0{continue;}let mut ctl=vec![(e,false),(bsig[l+2],false),(g[j],false)];ctl.extend((j+1..4).map(|k|(g[k],l&(1<<k)==0)));super::mask::mc_xor(b,&ctl,q[l],&[],dirty);}continue;
        }
        for value in l + 1..16usize {
            let mut controls = vec![(e, false), (bsig[l + 2], false)];
            controls.extend((0..4).map(|k| (g[k], value & (1 << k) == 0)));
            super::mask::mc_xor(b, &controls, q[l], &[], &dirty[..4]);
        }
    }
}

/// Prefix decomposition of e * bsig[l+2] * [g > l]. The MSB position at
/// which g first exceeds public l partitions the comparison into disjoint
/// terms, so OR equals XOR. This is symbolic constant-threshold synthesis,
/// independent of the cofactor's values, normalizer frame or rho encoding.
fn finish_mask_threshold(b:&mut B,q:&[QubitId],bsig:&[QubitId],g:&[QubitId],e:QubitId,dirty:&[QubitId]) {
    let qb=q.len();assert_eq!(g.len(),4);assert!(qb>=2&&qb<=16);
    assert!(bsig.len()>=qb&&dirty.len()>=4);
    b.cx(e,q[qb-2]);b.ccx(e,bsig[1],q[qb-1]);
    for l in 0..qb-2 {
        for j in 0..4 {
            if l&(1<<j)!=0 {continue;}
            let mut controls=vec![(e,false),(bsig[l+2],false),(g[j],false)];
            controls.extend((j+1..4).map(|k|(g[k],l&(1<<k)==0)));
            super::mask::mc_xor(b,&controls,q[l],&[],dirty);
        }
    }
}

/// One word lane of the threshold mask: q[l] ^= e & src & [g > l].
fn mask_threshold_term(b: &mut B, q: &[QubitId], src: QubitId, g: &[QubitId], e: QubitId, dirty: &[QubitId], l: usize) {
    assert_eq!(g.len(), 4);
    for j in 0..4 {
        if l & (1 << j) != 0 {
            continue;
        }
        let mut controls = vec![(e, false), (src, false), (g[j], false)];
        controls.extend((j + 1..4).map(|k| (g[k], l & (1 << k) == 0)));
        super::mask::mc_xor(b, &controls, q[l], &[], dirty);
    }
}

/// Q852 page: the threshold mask's word lanes start.. except lane 1 (its V3 source is applied by the caller).
fn finish_mask_lq_from(b: &mut B, q: &[QubitId], bsig: &[QubitId], g: &[QubitId], e: QubitId, dirty: &[QubitId], start: usize) {
    assert!(threshold_mask_enabled());
    let qb = q.len();
    assert!(qb >= 4 && qb <= 16 && bsig.len() >= qb && dirty.len() >= 4);
    for l in start..qb - 2 {
        if l == 1 || (l == 2 && super::lilypad_g::LQ_PAGE5) {
            continue;
        }
        mask_threshold_term(b, q, bsig[l + 2], g, e, dirty, l);
    }
}

fn threshold_mask_enabled() -> bool {
    #[cfg(test)]
    {
        std::env::var_os("LILYPAD_THRESHOLD_MASK").is_some()
    }
    #[cfg(not(test))]
    {
        true
    }
}

/// Temporarily zero the two leased high sign lanes on the exact terminal
/// SP0 branch. For an open negative terminal word, e=1 and h is in -10..-1:
/// h[5:4]=11 while h[2] OR h[3]=1. Completed h=0/1 has high 00 and a false
/// predicate. Applying this before and after the loan is an exact involution.
pub(super) fn toggle_terminal_sp0_high_h_leases(
    b: &mut B,
    h: &[QubitId],
    e: QubitId,
    dirty: &[QubitId],
) {
    assert_eq!(h.len(), 6);
    assert!(dirty.len() >= 3);
    for &target in &h[4..6] {
        b.ccx(e, h[2], target);
        b.ccx(e, h[3], target);
        super::mask::mc_xor(
            b,
            &[(e, false), (h[2], false), (h[3], false)],
            target,
            &[],
            dirty,
        );
    }
}

/// target ^= B_eff, where B_eff is the terminal no-D reconstruction bit.
/// `include_high_or=false` is the inherited low4-zero predicate used by all
/// other geometries; true adds the reviewed SP0 negative-terminal term.
pub(super) fn toggle_terminal_sp0_b_eff(
    b: &mut B,
    h: &[QubitId],
    sigma: QubitId,
    target: QubitId,
    dirty: &[QubitId],
    low_bits: usize,
    include_high_or: bool,
) {
    assert_eq!(h.len(), 6);
    let mut low_zero_nsigma: Vec<(QubitId, bool)> =
        h[..low_bits].iter().copied().map(|q| (q, true)).collect();
    low_zero_nsigma.push((sigma, true));
    super::mask::mc_xor(b, &low_zero_nsigma, target, &[], dirty);
    if include_high_or {
        super::mask::mc_xor(b, &[(sigma, true), (h[2], false)], target, &[], dirty);
        super::mask::mc_xor(b, &[(sigma, true), (h[3], false)], target, &[], dirty);
        super::mask::mc_xor(
            b,
            &[(sigma, true), (h[2], false), (h[3], false)],
            target,
            &[],
            dirty,
        );
    }
}

/// target ^= E * B_eff. The target must be distinct from E.
pub(super) fn toggle_terminal_sp0_e_b_eff(
    b: &mut B,
    h: &[QubitId],
    e: QubitId,
    sigma: QubitId,
    target: QubitId,
    dirty: &[QubitId],
    low_bits: usize,
    include_high_or: bool,
) {
    assert!(target != e);
    let mut e_low_zero_nsigma = vec![(e, false)];
    e_low_zero_nsigma.extend(h[..low_bits].iter().copied().map(|q| (q, true)));
    e_low_zero_nsigma.push((sigma, true));
    super::mask::mc_xor(b, &e_low_zero_nsigma, target, &[], dirty);
    if include_high_or {
        for &hq in &[h[2], h[3]] {
            super::mask::mc_xor(
                b,
                &[(e, false), (sigma, true), (hq, false)],
                target,
                &[],
                dirty,
            );
        }
        super::mask::mc_xor(
            b,
            &[(e, false), (sigma, true), (h[2], false), (h[3], false)],
            target,
            &[],
            dirty,
        );
    }
}

#[cfg(test)]
#[path="tests_threshold_mask.rs"]
mod tests_threshold_mask;

#[cfg(test)]
#[path="tests_nosp_cap.rs"]
mod tests_nosp_cap;

#[cfg(test)]
#[path="tests_terminal_high_h.rs"]
mod tests_terminal_high_h;

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
    external_dirty: &[QubitId],
) {
    let tn = t + 1;
    let q = w.qfr(t);
    let qb = q.len();
    let wl = win_len(qb);
    let (cz, kv, kc) = (sch.c[tn], sch.kv[tn], sch.kc[tn]);
    let a_lane=|k|w.asig(tn,k);
    let b_lane=|k|w.bsig(k);
    // In the conversion-free G path, both raw source windows through the
    // eraser span remain live sign copies and cannot be lent.
    let cofactor_shift = usize::from(half_cofactor);
    let a_span = 2 + wl - cofactor_shift;
    let b_span = 2 + wl + boff - cofactor_shift;
    let blo = if g_rho.is_some() { b_span } else if boff > 0 { w.bb.len() } else { b_span };
    let zl0 = lsc_from(b, w, tn, cz, kv, kc, a_span, blo);
    // window / source lanes past a ring's cofactor region are value lanes: never lend them to the pools
    let busy: Vec<QubitId> = (0..a_span)
        .map(a_lane)
        .chain((0..b_span).map(b_lane))
        .collect();
    let mut zl: Vec<QubitId> = zl0.iter().copied()
        .filter(|x| !busy.contains(x) && !q.contains(x))
        .collect();
    let gap_need = SB.saturating_sub(sc.sp.len());
    let lent_gap = gap_need.min(zl.len());
    let missing_gap = gap_need - lent_gap;
    let loanless_gap = missing_gap > 0;
    assert!(missing_gap <= 4, "tick {t}: direct gap fallback supports at most four missing lanes");
    let mut hosted_gap = sc.sp.clone();
    if lent_gap > 0 {
        hosted_gap.extend(zl.drain(..lent_gap));
    }
    let tm = &sc.tmp;
    let hosted_h_count = if tm.is_empty() { missing_gap.saturating_sub(2) } else { usize::from(missing_gap == 4) };
    let conditional_gap = hosted_h_count > 0;
    let e = sc.e;
    let no_d = super::lilypad_g::test_no_d();
    let terminal_sp0_high_h_scope = terminal
        && pre_swap
        && half_cofactor
        && tm.is_empty()
        && no_d
        && w.capq == 10
        && HB == 6
        && sc.sp.is_empty();
    if terminal_sp0_high_h_scope {
        assert_eq!(
            (tn, cz, kv, kc, missing_gap, hosted_h_count),
            (sch.s + 1, 3, 3, sch.w - 3, 4, 2),
            "terminal SP0 high-h repair is proved only for the canonical W288/S532 frame"
        );
    }
    let terminal_sp0_high_h_fix = terminal_sp0_high_h_scope;
    let (cf1, cf2, cg1) = (
        a_lane(1 - cofactor_shift),
        a_lane(2 - cofactor_shift),
        b_lane(boff + 1 - cofactor_shift),
    );
    #[cfg(test)]
    let direct_flags = std::env::var_os("LILYPAD_DIRECT_FLAGS").is_some()
        || std::env::var_os("LILYPAD_DIRECT_ERFLAGS").is_some();
    #[cfg(not(test))]
    let direct_flags = (pre_swap && half_cofactor && tm.is_empty());
    let no_tmp_page = pre_swap && half_cofactor && tm.is_empty() && direct_flags;
    let direct_body = no_tmp_page || loanless_gap;
    let a0_from_pool = half_cofactor && !sc.pool.is_empty();
    let a0 = if a0_from_pool {
        sc.pool[0]
    } else if half_cofactor {
        assert!(tm.len() == 1 || no_tmp_page, "zero-pool eraser needs one hosted temporary");
        tm.first().or_else(|| sc.d.first()).copied().unwrap_or(e)
    } else {
        w.asig(tn, 0)
    };
    let scratch_ok=|x:QubitId|x!=a0 && !q.contains(&x);

    let free_pool: Vec<QubitId> = sc.pool.iter().copied().filter(|&q| scratch_ok(q)).collect();
    let low_scratch = pre_swap && half_cofactor && tm.len() == 1 && sc.sp.len() <= 4 && !direct_body;
    let d = sc.d.first().copied().unwrap_or(e);
    let mut flag_tmp = if direct_flags { vec![d; 5] } else { tm.clone() };
    if !direct_flags && flag_tmp.len() < 5 {
        flag_tmp.extend_from_slice(&sc.sp[..5 - flag_tmp.len()]);
    }
    let (pq, z0, z1, y, wn) = (flag_tmp[0], flag_tmp[1], flag_tmp[2], flag_tmp[3], flag_tmp[4]);
    let hl: Vec<(QubitId, bool)> = w.h[1..].iter().map(|&x| (x, true)).collect();
    // These four flag outputs are still clean while pq is synthesized and
    // are restored by the MBU compute before they receive their own values.
    let htemps = vec![z0, z1, y, wn];
    assert!(!direct_flags || pre_swap, "direct flags are specialized to the pre-swap L5 eraser");
    let neg = |name: &str| match name {
        "noFt" => l2_neg(8),
        "noFm" => l2_neg(9),
        "noFsfix" => l2_neg(10),
        _ => false,
    };
    let swap_flag = if pre_swap && !l5_neg(2) { sc.sg } else { cf1 };
    let direct_dirty: &[QubitId] = if external_dirty.len() >= 7 { &external_dirty[..7] } else { &q[..7] };
    let direct_h0: Vec<(QubitId, bool)> = w.h.iter().copied().map(|x| (x, true)).collect();
    let toggle_direct_d = |b: &mut B, target: QubitId| {
        let mut yd = direct_h0.clone();
        yd.extend([(sc.sg, false), (cf2, true)]);
        super::mask::mc_xor(b, &yd, target, &[], direct_dirty);
        let mut h1d = direct_h0.clone();
        h1d[0].1 = false;
        h1d.push((cf2, true));
        super::mask::mc_xor(b, &h1d, target, &[], direct_dirty);
    };
    let toggle_direct_base = |b: &mut B, target: QubitId| {
        let mut base = direct_h0.clone();
        super::mask::mc_xor(b, &base, target, &[], direct_dirty);
        let mut ye = direct_h0.clone();
        ye.push((sc.sg, false));
        super::mask::mc_xor(b, &ye, target, &[], direct_dirty);
        if terminal && !neg("noFt") {
            let mut ft = vec![(w.h[HB - 1], false), (sc.sg, true)];
                super::mask::mc_xor(b, &ft, target, &[], direct_dirty);
        }
    };
    let (ft, fd, fe) = if direct_flags {
        let target = q[qb - 1];
        assert!(!direct_dirty.contains(&target), "terminal marker target aliases framed dirty loans");
        b.begin();
        if !no_d { toggle_direct_d(b, d); }
        let fd = b.end();
        b.begin();
        toggle_direct_base(b, e);
        if no_d { toggle_direct_d(b, e); } else { b.cx(d, e); }
        let fe = b.end();
        (vec![], fd, fe)
    } else {
        // flags
        b.begin();
        b.mbu_compute(pq, &hl, &htemps);
        b.x(w.h[0]);
        b.and_c(pq, w.h[0], z0);
        b.x(w.h[0]);
        b.and_c(pq, w.h[0], z1);
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
            let yc2 = b_lane(2 - cofactor_shift);
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
        if terminal && !neg("noFt") {
            b.x(swap_flag);
            b.ccx(w.h[HB - 1], swap_flag, e);
            b.x(swap_flag);
        }
        let fe = b.end();
        (ft, fd, fe)
    };
    sec(b, "er.flags", |b| {
        b.play(&ft, false);
        b.play(&fd, false);
        b.play(&fe, false);
        if direct_flags {
            let target = q[qb - 1];
            let mut marker: Vec<(QubitId, bool)> = w.h.iter().copied().map(|x| (x, true)).collect();
            marker.push((sc.sg, false));
                let marker_dirty = if external_dirty.len() >= 6 { &external_dirty[..6] } else { &q[..6] };
            super::mask::mc_xor(b, &marker, target, &[], marker_dirty);
            if terminal && !neg("noFm") {
                // The marker uses the positive swap flag.  Only the terminal
                // contribution to e above uses its complement.
                let mut fm = vec![(w.h[HB - 1], false), (sc.sg, false)];
                        super::mask::mc_xor(b, &fm, target, &[], direct_dirty);
            }
        } else {
            b.cx(y, q[qb - 1]);
            if terminal && !neg("noFm") {
                b.ccx(w.h[HB - 1], swap_flag, q[qb - 1]);
            }
            b.play(&ft, true);
        }
    });
    let narrow_core = pre_swap;
    if narrow_core {
        assert_eq!(w.capq + 2, qb, "L5 12-lane eraser needs run cap q = QB - 2");
        sec(b, "er.qrot", |b| {
            if no_d { toggle_direct_d(b, e); } else { b.cx(d, e); }
            crot_up(b, e, &q, qb - 1);
            if no_d { toggle_direct_d(b, e); } else { b.cx(d, e); }
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
    let win: Vec<QubitId> = (0..wl).map(|k| a_lane(2 - cofactor_shift + k)).collect();
    let src: Vec<QubitId> = (0..wl).map(|k| b_lane(boff + 1 - cofactor_shift + k)).collect();
    let fsq = tm.first().copied().unwrap_or(a0);
    let mut fpool: Vec<QubitId> = tm.get(1..).unwrap_or(&[])
        .iter()
        .copied()
        .filter(|&q| scratch_ok(q))
        .collect();
    fpool.push(a0);
    fpool.extend(&sc.sp);
    fpool.extend(free_pool.iter().copied());
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
                    a_lane(2 - cofactor_shift + k),
                    b_lane(yoff - cofactor_shift + k),
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
    let stream_page = pre_swap && half_cofactor && super::lilypad_g::test_stream_page3_sources();
    let (borrowed_page, gap_extra) = if stream_page {
        assert!(external_dirty.len() >= 4);
        let g0 = w.af(tn, 0);
        let f0 = w.bf(0);
        if tm.is_empty() {
            if missing_gap == 0 {
                b.x(g0);
                b.x(f0);
                super::lilypad_g::page3_sources_xor_direct_rho(
                    b,
                    w,
                    tn,
                    g_rho.expect("streamed page sources need pre-swap rho"),
                    g0,
                    f0,
                    &external_dirty[..4],
                );
                (Some((Some(g0), Some(f0), true, true)), vec![])
            } else if missing_gap == 1 {
                b.x(g0);
                b.x(f0);
                super::lilypad_g::page3_source_bit_controlled_xor_direct_rho(
                    b,
                    w,
                    tn,
                    g_rho.expect("streamed page sources need pre-swap rho"),
                    2,
                    None,
                    f0,
                    &external_dirty[..5],
                );
                (Some((None, Some(f0), false, true)), vec![g0])
            } else {
                b.x(g0);
                b.x(f0);
                let mut gap = vec![g0, f0];
                if missing_gap >= 3 { gap.push(w.h[HB - 1]); }
                if missing_gap >= 4 { gap.push(w.h[HB - 2]); }
                (Some((None, None, false, false)), gap)
            }
        } else if missing_gap == 4 {
            b.x(g0);
            b.x(f0);
            (Some((None, None, false, false)), vec![g0, f0, tm[0], w.h[HB - 1]])
        } else if missing_gap == 3 {
            b.x(g0);
            b.x(f0);
            (Some((None, None, false, false)), vec![g0, f0, tm[0]])
        } else if missing_gap == 2 {
            b.x(g0);
            b.x(f0);
            let v2 = tm[0];
            super::lilypad_g::page3_source_bit_controlled_xor_direct_rho(
                b,
                w,
                tn,
                g_rho.expect("streamed page sources need pre-swap rho"),
                2,
                None,
                v2,
                &external_dirty[..5],
            );
            (Some((None, Some(v2), false, false)), vec![g0, f0])
        } else if missing_gap == 1 {
            b.x(g0);
            b.x(f0);
            let v1 = tm[0];
            super::lilypad_g::page3_sources_xor_direct_rho(
                b,
                w,
                tn,
                g_rho.expect("streamed page sources need pre-swap rho"),
                v1,
                f0,
                &external_dirty[..4],
            );
            (Some((Some(v1), Some(f0), false, true)), vec![g0])
        } else {
            b.x(g0);
            b.x(f0);
            super::lilypad_g::page3_sources_xor_direct_rho(
                b,
                w,
                tn,
                g_rho.expect("streamed page sources need pre-swap rho"),
                g0,
                f0,
                &external_dirty[..4],
            );
            (Some((Some(g0), Some(f0), true, true)), vec![])
        }
    } else {
        (None, vec![])
    };
    // Q852 page: V3 (bsig 3) is not stored. Its one mask read (word lane 1) is applied twice through the borrowed
    // lane lq_d, once holding d0 ^ V3 ^ rho and once d0; V3 is toggled into lq_d where the window holds U.
    let lq4 = super::lilypad_g::LQ_PAGE4 && stream_page;
    let lq_d = if lq4 { Some(external_dirty[7]) } else { None };
    // Q851 page: V4 (bsig 4) is read the same way, by word lane 2 through the borrowed lane lq_d2.
    let lq5 = super::lilypad_g::LQ_PAGE5 && stream_page;
    let lq_d2 = if lq5 { assert!(external_dirty.len() >= 9); Some(external_dirty[8]) } else { None };
    let lq_missing_v2 = borrowed_page.is_some_and(|(_, v2, _, _)| v2.is_none());
    let lq_toggle = |b: &mut B| {
        assert!(sc.sg == w.asig(tn, 0), "Q852 page needs the hosted sigma");
        if lq5 {
            super::lilypad_g::lq5_eraser_toggle(
                b,
                w,
                sch,
                tn,
                g_rho.expect("Q851 page needs pre-swap rho"),
                lq_d.unwrap(),
                lq_d2.unwrap(),
                &external_dirty[..7],
            );
            return;
        }
        super::lilypad_g::lq_v3_xor(
            b,
            w,
            sch,
            tn,
            true,
            g_rho.expect("Q852 page needs pre-swap rho"),
            g_rho,
            lq_d.unwrap(),
            &external_dirty[..7],
        );
    };
    if lq4 && !lq_missing_v2 {
        lq_toggle(b);
    }
    if terminal_sp0_high_h_fix {
        assert_eq!(gap_extra.len(), 4);
        assert_eq!(gap_extra[2], w.h[HB - 1]);
        assert_eq!(gap_extra[3], w.h[HB - 2]);
        toggle_terminal_sp0_high_h_leases(b, &w.h, e, external_dirty);
    }
    // normalizer (frogstrip's, window from X.c sig 2)
    hosted_gap.extend(&gap_extra);
    let g: &[QubitId] = if hosted_gap.is_empty() { &sc.sp[..SB] } else { &hosted_gap };
    assert_eq!(g.len(), SB);
    b.begin();
    for k in (0..SB).rev() {
        let s = 1usize << k;
        if k >= 2 && norm_need(qb, k) == 0 {
            continue;
        }
        let mut lits: Vec<(QubitId, bool)> = win[..s].iter().map(|&x| (x, true)).collect();
        let conditional_host = conditional_gap && w.h.contains(&g[k]);
        if conditional_host { lits.push((e, false)); }
        if direct_body {
            // `a0` aliases the live completion flag `d` in the zero-tmp
            // route, so it is not a clean prefix ancilla.  Build each
            // normalizer predicate directly while restoring the external
            // dirty loans.
            super::mask::mc_xor(b, &lits, g[k], &[], external_dirty);
        } else {
            let mut temps: Vec<QubitId> = sc
                .tmp
                .iter()
                .copied()
                .filter(|&q| scratch_ok(q))
                .collect();
            temps.push(a0);
            temps.extend(&g[..k]);
            temps.extend(free_pool.iter().copied());
            temps.extend(&zl);
            if temps.len() + 2 >= s {
                b.mbu_compute(g[k], &lits, &temps);
            } else {
                let (pq, rest) = temps.split_last().unwrap();
                b.mbu_compute(*pq, &lits[..s / 2], rest);
                let mut l2 = vec![(*pq, false)];
                l2.extend(&lits[s / 2..]);
                b.mbu_compute(g[k], &l2, rest);
                b.mbu_erase(*pq, &lits[..s / 2], rest);
            }
        }
        if k == 1 {
            if direct_body {
                b.x(g[0]);
                b.cx(win[0], g[0]);
                b.ccx(g[1], win[2], g[0]);
                super::mask::mc_xor(
                    b,
                    &[(win[0], false), (g[1], false), (win[2], false)],
                    g[0],
                    &[],
                    external_dirty,
                );
            } else {
                let tt = sc.tmp[0];
                b.and_c(g[1], win[2], tt);
                b.mbu_compute(g[0], &[(win[0], true), (tt, true)], &[]);
                b.and_u(g[1], win[2], tt);
            }
            let rv: Vec<QubitId> = win[..norm_need(qb, 1)].iter().rev().cloned().collect();
            rot4_up(b, g[0], g[1], &rv);
            break;
        }
        for x in 0..norm_need(qb, k) {
            if conditional_host {
                b.cx(win[x + s], win[x]);
                super::mask::mc_xor(
                    b,
                    &[(e, false), (g[k], false), (win[x], false)],
                    win[x + s],
                    &[],
                    external_dirty,
                );
                b.cx(win[x + s], win[x]);
            } else {
                b.cswap(g[k], win[x], win[x + s]);
            }
        }
    }
    let nr = b.end();
    sec(b, "er.norm", |b| b.play(&nr, false));
    b.begin();
    let mut dtmp: Vec<QubitId> = sc
        .tmp
        .iter()
        .copied()
        .filter(|&q| scratch_ok(q))
        .collect();
    if !direct_body {
        dtmp.push(a0);
    }
    dtmp.extend(free_pool.iter().copied());
    dtmp.extend(&zl);
    if conditional_gap && no_d {
        if tm.is_empty() {
            toggle_terminal_sp0_b_eff(
                b,
                &w.h,
                sc.sg,
                e,
                external_dirty,
                HB - hosted_h_count,
                terminal_sp0_high_h_fix,
            );
            dec4_dirty(b, e, g, &q_core[..2]);
            toggle_terminal_sp0_b_eff(
                b,
                &w.h,
                sc.sg,
                e,
                external_dirty,
                HB - hosted_h_count,
                terminal_sp0_high_h_fix,
            );
        } else {
            let mut base: Vec<(QubitId, bool)> = w.h[..HB - 1].iter().copied().map(|q| (q, true)).collect();
            base.push((sc.sg, true));
            super::mask::mc_xor(b, &base, e, &[], external_dirty);
            dec4_dirty(b, e, g, &q_core[..2]);
            super::mask::mc_xor(b, &base, e, &[], external_dirty);
        }
    } else {
        if no_d { toggle_direct_base(b, e); }
        let dec_ctl = if no_d { e } else { d };
        if dtmp.len() < SB - 2 {
            dec4_dirty(b, dec_ctl, g, &q_core[..2]);
        } else if dtmp.len() >= SB - 1 {
            dec(b, dec_ctl, g, &dtmp[..SB - 1]);
        } else {
            dec_topless(b, dec_ctl, g, &dtmp[..SB - 2]);
        }
        if no_d { toggle_direct_base(b, e); }
    }
    let dr = b.end();
    sec(b, "er.dec", |b| b.play(&dr, false));
    let mut pool: Vec<QubitId> = if low_scratch {
        vec![]
    } else {
        sc.tmp.iter().copied().filter(|&q| scratch_ok(q)).collect()
    };
    pool.push(a0);
    pool.extend(free_pool.iter().copied());
    pool.extend(&zl);
    sec(b, "er.mul", |b| {
        if direct_body {
            finish_mul_no_tmp(b, &win[1..core_bits], q_core, e, external_dirty);
        } else {
            radix4_finish_mul(b, &win[1..core_bits], q_core, e, a0, &pool);
        }
    });
    if g_rho.is_some() && !l2_neg(4) {
        // Fd and the shared C6 endpoint-open word require the word's top bit
        // flipped by e xor d. This must happen after multiply, before rotate.
        if no_d {
            if conditional_gap {
                if tm.is_empty() {
                    toggle_terminal_sp0_e_b_eff(
                        b,
                        &w.h,
                        e,
                        sc.sg,
                        q_core[core_bits - 1],
                        external_dirty,
                        HB - hosted_h_count,
                        terminal_sp0_high_h_fix,
                    );
                } else {
                    super::mask::mc_xor(
                        b,
                        &[(e, false), (w.h[0], true), (sc.sg, true)],
                        q_core[core_bits - 1],
                        &[],
                        external_dirty,
                    );
                }
            } else {
                toggle_direct_base(b, q_core[core_bits - 1]);
            }
        } else {
            b.cx(e, q_core[core_bits - 1]);
            b.cx(d, q_core[core_bits - 1]);
        }
    }
    sec(b, "er.rot", |b| {
        if direct_body {
            for k in [0usize, 2] {
                crot_up2_dirty(b, g[k], e, q_core, 1 << k, external_dirty);
                crot_up2_dirty(b, g[k + 1], e, q_core, 2 << k, external_dirty);
            }
        } else if let Some(&loan) = zl.first() {
            let (c1, c2) = (a0, loan);
            for k in [0usize, 2] {
                b.and_c(g[k], e, c1);
                b.and_c(g[k + 1], e, c2);
                rot4_unit(b, c1, c2, q_core, 1 << k);
                b.and_u(g[k + 1], e, c2);
                b.and_u(g[k], e, c1);
            }
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
    let mut mp: Vec<QubitId> = sc.pool.iter().copied().filter(|&q| scratch_ok(q)).collect();
    if !half_cofactor {
        mp.push(a0);
    }
    mp.extend(&zl);
    sec(b, "er.mask", |b| {
        let missing_v1 = borrowed_page.is_some_and(|(v1, _, _, _)| v1.is_none());
        let missing_v2 = borrowed_page.is_some_and(|(_, v2, _, _)| v2.is_none());
        let bsig: Vec<QubitId> = if let Some((v1, v2, _, _)) = borrowed_page {
            let fallback = v1.or(v2).unwrap_or(b_lane(boff + 3));
            let v1 = v1.unwrap_or(fallback);
            let v2 = v2.unwrap_or(fallback);
            let mut v = vec![v1, v1, v2];
            v.extend((3..core_bits).map(|k| b_lane(boff + k)));
            if lq4 {
                // index 3 (V3) is read only through lq_d
                v[3] = lq_d.unwrap();
            }
            if lq5 {
                // index 4 (V4) is read only through lq_d2
                v[4] = lq_d2.unwrap();
            }
            v
        } else {
            (0..core_bits).map(|k| b_lane(boff + k)).collect()
        };
        let lq_term1 = |b: &mut B| {
            if lq4 {
                mask_threshold_term(b, q_core, lq_d.unwrap(), g, e, external_dirty, 1);
            }
            if lq5 {
                mask_threshold_term(b, q_core, lq_d2.unwrap(), g, e, external_dirty, 2);
            }
        };
        let conjugate_sources = |b: &mut B| {
            if let Some(rho) = g_rho {
                // Raw source bit 0 is constant; bits 1.. are conjugated by
                // phi = rho xor cf1. In physical lanes these are sig2..QB.
                let first = if missing_v2 { 3 } else if missing_v1 { 2 } else { 1 };
                for (k, &x) in bsig.iter().enumerate().skip(first) {
                    if (lq4 && k == 3) || (lq5 && k == 4) {
                        continue;
                    }
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
        let mut mask_tmp: Vec<QubitId> = sc.tmp.iter().copied().filter(|&q| scratch_ok(q)).collect();
        if !narrow_core {
            mask_tmp.extend(&sc.sp);
        }
        if missing_v2 {
            let (h1, h2) = (external_dirty[0], external_dirty[1]);
            let dirty = &external_dirty[2..7];
            let top = q_core[core_bits - 1];
            let low = q_core[0];
            let toggle_nonzero = |b: &mut B, src: QubitId| {
                b.ccx(e, src, low);
                let mut zero = vec![(e, false), (src, false)];
                zero.extend(g.iter().copied().map(|q| (q, true)));
                super::mask::mc_xor(b, &zero, low, &[], dirty);
            };
            let toggle_nonzero_one = |b: &mut B| {
                b.cx(e, low);
                let mut zero = vec![(e, false)];
                zero.extend(g.iter().copied().map(|q| (q, true)));
                super::mask::mc_xor(b, &zero, low, &[], dirty);
            };
            let apply_hosts = |b: &mut B| {
                b.ccx(e, h1, top);
                toggle_nonzero(b, h2);
                lq_term1(b);
            };

            apply_hosts(b);
            b.play(&dr, true);
            b.play(&nr, true);
            super::lilypad_g::page3_sources_xor_direct_rho(
                b,
                w,
                tn,
                g_rho.unwrap(),
                h1,
                h2,
                &external_dirty[2..6],
            );
            if lq4 {
                lq_toggle(b);
            }
            b.play(&nr, false);
            b.play(&dr, false);
            apply_hosts(b);
            b.play(&dr, true);
            b.play(&nr, true);
            super::lilypad_g::page3_sources_xor_direct_rho(
                b,
                w,
                tn,
                g_rho.unwrap(),
                h1,
                h2,
                &external_dirty[2..6],
            );
            if lq4 {
                lq_toggle(b);
            }
            b.play(&nr, false);
            b.play(&dr, false);

            if l2_neg(7) {
                b.ccx(e, w.h[0], top);
                toggle_nonzero(b, w.h[0]);
            } else if !(l2_neg(2) || (pre_swap && (l2_neg(1) || l2_neg(3) || l2_neg(5)))) {
                let rho = g_rho.unwrap();
                if lq4 && !rho.qs.is_empty() {
                    let super::lilypad_g::PL::Q(rq) = super::lilypad_g::lq_fold(b, rho) else { unreachable!() };
                    b.ccx(e, rq, top);
                    toggle_nonzero(b, rq);
                    super::lilypad_g::lq_unfold(b, rho);
                } else {
                    for &rq in &rho.qs {
                        b.ccx(e, rq, top);
                        toggle_nonzero(b, rq);
                    }
                    if rho.flip {
                        b.cx(e, top);
                        toggle_nonzero_one(b);
                    }
                }
            }
            b.cx(e, q_core[core_bits - 2]);
            if lq4 {
                finish_mask_lq_from(b, q_core, &bsig, g, e, external_dirty, 2);
            } else {
                finish_mask_no_tmp_tail_from(b, q_core, &bsig, g, e, external_dirty, 1);
            }
        } else if missing_v1 {
            let target = q_core[core_bits - 1];
            // V1 was deliberately not stored. Restore the raw determinant
            // sources around this one toggle, then replay the normalizer and
            // gap decrement before consuming the remaining mask bits.
            lq_term1(b);
            b.play(&dr, true);
            b.play(&nr, true);
            if lq4 {
                lq_toggle(b);
            }
            super::lilypad_g::page3_source_bit_controlled_xor_direct_rho(
                b,
                w,
                tn,
                g_rho.unwrap(),
                1,
                Some(e),
                target,
                &external_dirty[..5],
            );
            if l2_neg(7) {
                b.ccx(e, w.h[0], target);
            } else if !(l2_neg(2) || (pre_swap && (l2_neg(1) || l2_neg(3) || l2_neg(5)))) {
                let rho = g_rho.unwrap();
                if lq4 && !rho.qs.is_empty() {
                    let super::lilypad_g::PL::Q(rq) = super::lilypad_g::lq_fold(b, rho) else { unreachable!() };
                    b.ccx(e, rq, target);
                    super::lilypad_g::lq_unfold(b, rho);
                } else {
                    for &rq in &rho.qs { b.ccx(e, rq, target); }
                    if rho.flip { b.cx(e, target); }
                }
            }
            b.play(&nr, false);
            b.play(&dr, false);
            b.cx(e, q_core[core_bits - 2]);
            if lq4 {
                lq_term1(b);
                finish_mask_lq_from(b, q_core, &bsig, g, e, external_dirty, 0);
            } else {
                finish_mask_no_tmp_tail(b, q_core, &bsig, g, e, external_dirty);
            }
        } else if direct_body && lq4 {
            lq_term1(b);
            b.play(&dr, true);
            b.play(&nr, true);
            lq_toggle(b);
            b.play(&nr, false);
            b.play(&dr, false);
            lq_term1(b);
            let qb = q_core.len();
            b.cx(e, q_core[qb - 2]);
            b.ccx(e, bsig[1], q_core[qb - 1]);
            finish_mask_lq_from(b, q_core, &bsig, g, e, external_dirty, 0);
        } else if direct_body {
            finish_mask_no_tmp(b, q_core, &bsig, g, e, external_dirty);
        } else {
            finish_mask(b, q_core, &bsig, g, e, &mask_tmp, &mp, Some(d));
        }
        conjugate_sources(b);
    });
    sec(b, "er.undo", |b| {
        b.play(&dr, true);
        b.play(&nr, true);
        if !neg("noFsfix") {
            b.play(&fs, true);
        }
        if let Some((v1, v2, flip1, flip2)) = borrowed_page {
            if let (Some(v1), Some(v2)) = (v1, v2) {
                super::lilypad_g::page3_sources_xor_direct_rho(
                    b,
                    w,
                    tn,
                    g_rho.unwrap(),
                    v1,
                    v2,
                    &external_dirty[..4],
                );
            } else if let Some(v2) = v2 {
                super::lilypad_g::page3_source_bit_controlled_xor_direct_rho(
                    b,
                    w,
                    tn,
                    g_rho.unwrap(),
                    2,
                    None,
                    v2,
                    &external_dirty[..5],
                );
            }
            if flip2 { b.x(v2.unwrap()); }
            if flip1 { b.x(v1.unwrap()); }
        }
        for &gap in &gap_extra {
            if !tm.contains(&gap) && !w.h.contains(&gap) { b.x(gap); }
        }
        if terminal_sp0_high_h_fix {
            // Restore the leased sign lanes after normalizer/decrement and
            // gap-source restoration, while e and h[2:3] still hold the same
            // predicate. `fe` runs next and may clear e/read the high sign.
            toggle_terminal_sp0_high_h_leases(b, &w.h, e, external_dirty);
        }
        b.play(&ft, false);
        b.play(&fe, true);
        b.play(&fd, true);
        b.play(&ft, true);
    });
    lsc_from(b, w, tn, cz, kv, kc, a_span, blo);
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
        mclear(b, w, t, sc, false, &[]);
    } else {
        eraser(b, w, t, sch, sc, 0, false, None, false, false, &[]);
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
