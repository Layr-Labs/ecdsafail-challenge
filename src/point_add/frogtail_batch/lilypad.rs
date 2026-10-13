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
use super::arith::{dec, rot4_up};
use super::modp_ft::ctrl_add_pool;
use crate::circuit::{BitId, QubitId};

/// Seven bits avoid the rare signed-delta wrap observed with the six-bit audit build.
pub const HB: usize = 7;
pub const SB: usize = 5;
pub const NT: usize = 8;

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
    let tm = &sc.tmp;
    let (ee, lt, sh) = (tm[0], tm[1], tm[6]);
    let s0 = &w.log[0..4];
    b.begin();
    // The cap itself keeps negative h in the audited six-bit range.  Clamp
    // those low six bits exactly as before, but guard with the true seventh
    // sign bit so large positive h is never mistaken for a negative value.
    lt_const(b, &h[..5], (33 - q) as u64, lt, &tm[2..6]);
    b.and_c(sc.sg, h[6], sh);
    b.and_c(sh, lt, ee);
    let er = b.end();
    b.play(&er, false);
    if w.log.len() == 8 {
        for i in 0..4 {
            b.cswap(ee, w.log[i], w.log[4 + i]);
        }
    }
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
pub(super) fn mclear(b: &mut B, w: &PWalk, t: usize, sc: &PScr) {
    let q = w.qfr(t);
    let qb = q.len();
    let (z0, y) = (sc.tmp[0], sc.tmp[1]);
    let lits: Vec<(QubitId, bool)> = w.h.iter().map(|&x| (x, true)).collect();
    let cf1 = w.asig(t + 1, 1);
    sec(b, "lily.mclr", |b| {
        b.mbu_compute(z0, &lits, &sc.tmp[2..]);
        b.and_c(z0, cf1, y);
        b.cx(y, q[qb - 1]);
        b.and_u(z0, cf1, y);
        b.mbu_erase(z0, &lits, &sc.tmp[2..]);
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

/// Completing word's mask (frogstrip's finish_mask_lent, QB-generic, pool >= 6 mapping).
#[allow(clippy::too_many_arguments)]
pub(super) fn finish_mask(
    b: &mut B,
    q: &[QubitId],
    bsig: &[QubitId],
    g: &[QubitId],
    e: QubitId,
    tmp: &[QubitId],
    pool: &[QubitId],
) {
    let qb = q.len();
    assert!(pool.len() >= 6 && qb <= 21);
    b.cx(e, q[qb - 2]);
    b.ccx(e, bsig[1], q[qb - 1]);
    let f = tmp[0];
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
}

/// Even-tick eraser of tick t (after the halve; X at frame t + 1, Q at frame t).
pub(super) fn eraser(b: &mut B, w: &PWalk, t: usize, sch: &PSched, sc: &PScr, boff: usize, terminal: bool) {
    let tn = t + 1;
    let q = w.qfr(t);
    let qb = q.len();
    let wl = win_len(qb);
    let (cz, kv, kc) = (sch.c[tn], sch.kv[tn], sch.kc[tn]);
    // With boff > 0, Y.c temporarily holds the converted c_g window. Its
    // extension lanes are not sign copies and therefore cannot be lent.
    let blo = if boff > 0 { w.bb.len() } else { 2 + wl };
    let zl0 = lsc_from(b, w, tn, cz, kv, kc, 2 + wl, blo);
    // window / source lanes past a ring's cofactor region are value lanes: never lend them to the pools
    let busy: Vec<QubitId> = (0..2 + wl)
        .map(|k| w.asig(tn, k))
        .chain((0..2 + wl + boff).map(|k| w.bsig(k)))
        .collect();
    let zl: Vec<QubitId> = zl0.iter().copied().filter(|x| !busy.contains(x)).collect();
    let tm = &sc.tmp;
    let (pq, z0, z1, y, wn) = (tm[0], tm[1], tm[2], tm[3], tm[4]);
    let (e, d) = (sc.e, sc.d[0]);
    let (cf1, cf2, cg1) = (w.asig(tn, 1), w.asig(tn, 2), w.bsig(boff + 1));
    let a0 = w.asig(tn, 0);
    // flags
    b.begin();
    let hl: Vec<(QubitId, bool)> = w.h[1..].iter().map(|&x| (x, true)).collect();
    let mut htemps = tm[5..8].to_vec();
    htemps.push(a0);
    b.mbu_compute(pq, &hl, &htemps);
    b.x(w.h[0]);
    b.and_c(pq, w.h[0], z0);
    b.x(w.h[0]);
    b.and_c(pq, w.h[0], z1);
    b.and_c(z0, cf1, y);
    b.x(cf1);
    b.and_c(z1, cf1, wn);
    b.x(cf1);
    let ft = b.end();
    b.begin();
    b.cx(cg1, cf2);
    b.x(cf2);
    b.and_c(y, cf2, d);
    b.x(cf2);
    b.cx(cg1, cf2);
    b.x(cf2);
    b.ccx(wn, cf2, d);
    b.x(cf2);
    b.cx(z0, e);
    b.cx(y, e);
    b.cx(d, e);
    let neg = |name: &str| std::env::var("AUD_NEG").is_ok_and(|v| v == name);
    if terminal && !neg("noFt") {
        b.x(cf1);
        b.ccx(w.h[HB - 1], cf1, e);
        b.x(cf1);
    }
    let fo = b.end();
    sec(b, "er.flags", |b| {
        b.play(&ft, false);
        b.play(&fo, false);
        b.cx(y, q[qb - 1]);
        if terminal && !neg("noFm") {
            b.ccx(w.h[HB - 1], cf1, q[qb - 1]);
        }
        b.play(&ft, true);
    });
    // deferred words: Q up one lane
    sec(b, "er.qrot", |b| crot_up(b, d, &q, 1));
    // Fs: window X.c sig 2.. <- (X.c >> 1) - Y.c, in place, under fs = D & cf1
    let win: Vec<QubitId> = (0..wl).map(|k| w.asig(tn, 2 + k)).collect();
    let src: Vec<QubitId> = (0..wl).map(|k| w.bsig(boff + 1 + k)).collect();
    let fsq = tm[0];
    let mut fpool: Vec<QubitId> = tm[1..].to_vec();
    fpool.push(a0);
    fpool.extend(&sc.sp);
    fpool.extend(&sc.pool);
    fpool.extend(&zl);
    b.begin();
    b.and_c(d, cf1, fsq);
    for &x in &win {
        b.cx(fsq, x);
    }
    ctrl_add_pool(b, &src, &win, fsq, &fpool);
    for &x in &win {
        b.cx(fsq, x);
    }
    b.and_u(d, cf1, fsq);
    let fs = b.end();
    if !neg("noFsfix") {
        sec(b, "er.fsub", |b| b.play(&fs, false));
    }
    // normalizer (frogstrip's, window from X.c sig 2)
    let g = &sc.sp[..SB];
    b.begin();
    for k in (0..SB).rev() {
        let s = 1usize << k;
        if k >= 2 && norm_need(qb, k) == 0 {
            continue;
        }
        let lits: Vec<(QubitId, bool)> = win[..s].iter().map(|&x| (x, true)).collect();
        let mut temps = sc.tmp.clone();
        temps.push(a0);
        temps.extend(&sc.sp[..k]);
        temps.extend(&sc.pool);
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
            let rv: Vec<QubitId> = win[..norm_need(qb, 1)].iter().rev().cloned().collect();
            rot4_up(b, sc.sp[0], sc.sp[1], &rv);
            break;
        }
        for x in 0..norm_need(qb, k) {
            b.cswap(sc.sp[k], win[x], win[x + s]);
        }
    }
    let nr = b.end();
    sec(b, "er.norm", |b| b.play(&nr, false));
    b.begin();
    dec(b, d, g, &sc.tmp[..SB - 1]);
    let dr = b.end();
    sec(b, "er.dec", |b| b.play(&dr, false));
    let mut pool: Vec<QubitId> = sc.tmp.clone();
    pool.push(a0);
    pool.extend(&sc.pool);
    pool.extend(&zl);
    sec(b, "er.mul", |b| radix4_finish_mul(b, &win[1..qb], &q, e, a0, &pool));
    let (c1, c2) = (sc.tmp[0], sc.tmp[1]);
    sec(b, "er.rot", |b| {
        for k in [0usize, 2] {
            b.and_c(g[k], e, c1);
            b.and_c(g[k + 1], e, c2);
            rot4_unit(b, c1, c2, &q, 1 << k);
            b.and_u(g[k + 1], e, c2);
            b.and_u(g[k], e, c1);
        }
        if qb >= 18 {
            b.and_c(g[4], e, c1);
            crot_up(b, c1, &q, 16);
            b.and_u(g[4], e, c1);
        }
    });
    let mut mp: Vec<QubitId> = sc.pool.clone();
    mp.push(a0);
    mp.extend(&zl);
    sec(b, "er.mask", |b| {
        let bsig: Vec<QubitId> = (0..qb).map(|k| w.bsig(boff + k)).collect();
        finish_mask(b, &q, &bsig, g, e, &sc.tmp, &mp);
    });
    sec(b, "er.undo", |b| {
        b.play(&dr, true);
        b.play(&nr, true);
        if !neg("noFsfix") {
            b.play(&fs, true);
        }
        b.play(&ft, false);
        b.play(&fo, true);
        b.play(&ft, true);
    });
    lsc_from(b, w, tn, cz, kv, kc, 2 + wl, blo);
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
        mclear(b, w, t, sc);
    } else {
        eraser(b, w, t, sch, sc, 0, false);
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
