//! greedyfrog: the uniform greedy Euclid traversal circuit. Reference: `greedyfrog_model.rs` (layout, slot order, decode).
//!
//! Registers: rings X (target) and Y (source), W lanes each; bit lengths LA, LB (9 bits); DONE counter cnt (8 bits);
//! swap parity par. Every slot is uniform. The forward slot X-measures its decisions (d, r, sw); the inverse slot
//! recomputes them from the post-state (sw and r from the cofactor windows, d from the wrapped lane 0) and repairs
//! their phases.
//!
//! Masked ladders (mask.rs) get their running-mask toggle from a counter whose bits are XORed with the DONE flag z0
//! while the ladder runs: a finished shot then shows 510/511, which matches no lane, so its mask stays off.

use super::builder::B;
use super::mask::{mdown, mup, top_carry, Lad, Mscr, Src, ALWAYS};
use super::greedyfrog_model::W;
use crate::circuit::{BitId, QubitId};

pub const LB_BITS: usize = 9;
pub const CNT_BITS: usize = 8;
pub const R_BITS: usize = 5;
/// bits of a slot's renormalisation rotation rho <= RCAP = 7 (3-stage barrel)
pub const RHO_BITS: usize = 3;
/// lanes of the top-window compares (F2, F9): exact unless the two values agree on all of them (~2^-40)
pub const WC: usize = 28;
/// lanes added on each side of the measured per-slot envelopes
pub const MARGIN: usize = 2;
/// slots per traversal: steps plus stall slots (200k walks: 8 need >= 257, 4 need 258)
pub const NSLOTS: usize = 254;

/// Classical per-slot windows of the active shots' data-dependent boundaries (greedyfrog_data/env.txt plus MARGIN). Lanes
/// on the far side of a window are classically on or off, so only the window's lanes pay for the running mask.
#[derive(Clone, Debug)]
pub struct Win {
    /// LB range (value chain mask, top compares)
    pub lb: (usize, usize),
    /// LA - d range (cofactor chain mask)
    pub lad: (usize, usize),
    /// lower bound of the bit length of X's cofactor in the post-state, before / after the decode's un-swap
    pub mxp: usize,
    pub mx: usize,
    /// division rows
    pub k: usize,
}

impl Win {
    /// No classical knowledge: every boundary anywhere (masks everywhere, all rows).
    pub fn full() -> Win {
        Win { lb: (1, 256), lad: (0, 256), mxp: 0, mx: 0, k: KROWS }
    }
}

/// walks behind greedyfrog_data/env.txt
const ENV_WALKS: f64 = 200_000.0;

/// The traversal's windows, slot by slot.
pub fn windows() -> Vec<Win> {
    let txt = include_str!("greedyfrog_data/env.txt");
    let mut v = vec![];
    for line in txt.lines().filter(|l| !l.starts_with('#')) {
        let c: Vec<isize> = line.split_whitespace().map(|t| t.parse().unwrap()).collect();
        // s n lb_min lb_max lad_min lad_max cof_min r_max mxp_min mx_min kt_max rows_max slack_max
        let m = MARGIN as isize;
        let lb = ((c[2] - m).max(1) as usize, (c[3] + m).min(256) as usize);
        let lad = ((c[4] - m).max(0) as usize, (c[5] + m).min(256) as usize);
        let mxp = (c[8] - m).max(0) as usize;
        let mx = (c[9] - m).max(0) as usize;
        // rows: the big-quotient tail (P(rows > k) ~ 2^-k per step) is the same at every slot, so a slot holding a
        // fraction f of the shots active keeps the run's expected failures flat with k = KROWS - floor(log2(1/f));
        // slot 0's quotient is a single power of two
        let f = c[1] as f64 / ENV_WALKS;
        let k = if c[0] == 0 { 4 } else { (KROWS as f64 - (1.0 / f).log2().floor()).clamp(8.0, KROWS as f64) as usize };
        v.push(Win { lb, lad, mxp, mx, k });
    }
    while v.len() < NSLOTS {
        v.push(v.last().unwrap().clone());
    }
    v.truncate(NSLOTS);
    v
}

pub struct GreedyFrog {
    pub x: Vec<QubitId>,
    pub y: Vec<QubitId>,
    pub la: Vec<QubitId>,
    pub lb: Vec<QubitId>,
    pub cnt: Vec<QubitId>,
    pub par: QubitId,
}

/// Measurement record of one forward slot.
#[derive(Clone, Debug)]
pub struct SlotBits {
    pub d: BitId,
    pub r: Vec<BitId>,
    pub sw: BitId,
    pub a1: BitId,
}


thread_local! {
    static PROF: std::cell::RefCell<(u64, &'static str, Vec<(&'static str, u64, u64)>, u64)> =
        std::cell::RefCell::new((0, "", vec![], 0));
}
/// GREEDYFROG_PROF=1: accumulate Toffoli per named section and the peak reached inside it (debug aid, no effect on gates).
pub fn prof(b: &B, name: &'static str) {
    if std::env::var_os("GREEDYFROG_PROF").is_none() { return; }
    PROF.with(|p| {
        let mut p = p.borrow_mut();
        if !p.1.is_empty() {
            let (prev, t0) = (p.1, p.0);
            let pk = if b.peak > p.3 { b.peak } else { 0 };
            if let Some(e) = p.2.iter_mut().find(|e| e.0 == prev) {
                e.1 += b.tof - t0;
                e.2 = e.2.max(pk);
            } else {
                p.2.push((prev, b.tof - t0, pk));
            }
        }
        p.3 = b.peak;
        p.0 = b.tof;
        p.1 = if name == "end" { "" } else { name };
    });
}
pub fn prof_dump() {
    PROF.with(|p| {
        for (n, t, pk) in p.borrow().2.iter() {
            eprintln!("GREEDYFROG_PROF {n:16} {t:8} {}", if *pk > 0 { format!("new peak {pk}") } else { String::new() });
        }
    });
    PROF.with(|p| p.borrow_mut().2.clear());
}

// ------------------------------------------------------------------ small helpers

/// out ^= AND of literals (qubit, negated), transient ancillas, n - 1 Toffoli (n >= 1).
pub fn and_into(b: &mut B, lits: &[(QubitId, bool)], out: QubitId) {
    let n = lits.len();
    assert!(n >= 1);
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
    if n == 1 {
        b.cx(lits[0].0, out);
    } else if n == 2 {
        b.ccx(lits[0].0, lits[1].0, out);
    } else {
        let anc = b.alloc_n(n - 2);
        b.and_c(lits[0].0, lits[1].0, anc[0]);
        for i in 2..n - 1 {
            b.and_c(anc[i - 2], lits[i].0, anc[i - 1]);
        }
        b.ccx(anc[n - 3], lits[n - 1].0, out);
        for i in (2..n - 1).rev() {
            b.and_u(anc[i - 2], lits[i].0, anc[i - 1]);
        }
        b.and_u(lits[0].0, lits[1].0, anc[0]);
        b.free_n(&anc);
    }
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
}

/// out ^= [v == 0]
pub fn zero_into(b: &mut B, v: &[QubitId], out: QubitId) {
    let lits: Vec<(QubitId, bool)> = v.iter().map(|&q| (q, true)).collect();
    and_into(b, &lits, out);
}

/// Controlled rotation of a lane ring, content moving UP by k (lane j -> lane j + k mod n).
pub fn crot_up(b: &mut B, c: QubitId, v: &[QubitId], k: usize) {
    let n = v.len();
    let k = k % n;
    if k == 0 {
        return;
    }
    // content moves up by k == content moves down by n - k; crot_down(r): lane j <- lane j + r
    crot_down(b, c, v, n - k);
}

/// Controlled rotation, content moving DOWN by k (lane j <- lane j + k mod n).
pub fn crot_down(b: &mut B, c: QubitId, v: &[QubitId], k: usize) {
    let n = v.len();
    let k = k % n;
    if k == 0 {
        return;
    }
    let g = gcd(n, k);
    for s in 0..g {
        let len = n / g;
        let cyc: Vec<usize> = (0..len).map(|i| (s + i * k) % n).collect();
        for i in 0..len - 1 {
            b.cswap(c, v[cyc[i]], v[cyc[i + 1]]);
        }
    }
}

fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// t -= s (little-endian, len(s) <= len(t)), in place, Cuccaro; zero-extends s with transient ancillas.
pub fn sub_small(b: &mut B, t: &[QubitId], s: &[QubitId]) {
    let n = t.len();
    let pad = b.alloc_n(n - s.len());
    let mut ss: Vec<QubitId> = s.to_vec();
    ss.extend(&pad);
    let c0 = b.alloc();
    let ru = super::arith::up_m(b, t, &ss, c0, true);
    b.play(&ru, false);
    let rd = super::arith::down_m(b, t, &ss, c0, super::arith::Dm::Sum, true);
    b.play(&rd, false);
    b.free(c0);
    b.free_n(&pad);
}

/// t += s (little-endian, len(s) <= len(t)), in place.
pub fn add_small(b: &mut B, t: &[QubitId], s: &[QubitId]) {
    let n = t.len();
    let pad = b.alloc_n(n - s.len());
    let mut ss: Vec<QubitId> = s.to_vec();
    ss.extend(&pad);
    let c0 = b.alloc();
    let ru = super::arith::up_m(b, t, &ss, c0, false);
    b.play(&ru, false);
    let rd = super::arith::down_m(b, t, &ss, c0, super::arith::Dm::Sum, false);
    b.play(&rd, false);
    b.free(c0);
    b.free_n(&pad);
}

/// out ^= [a < b] for equal-length little-endian registers (borrow of a - b), registers restored.
pub fn lt_into(b: &mut B, a: &[QubitId], bb: &[QubitId], out: QubitId) {
    // up(t = a, s = bb) complements a and leaves [bb > a] on bb[L-1]
    let c0 = b.alloc();
    let ru = super::arith::up(b, a, bb, c0);
    b.play(&ru, false);
    b.cx(bb[a.len() - 1], out);
    b.play(&ru, true);
    b.free(c0);
}

/// out ^= [a == b] (equal length), registers restored.
pub fn eq_into(b: &mut B, a: &[QubitId], bb: &[QubitId], out: QubitId) {
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
    zero_into(b, a, out);
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
}

/// Where g = 0, flip the top bit of a length register: v >= 257 or v == 0 then (LB <= 256), which no top-compare
/// window matches.
fn mark_msb(b: &mut B, g: QubitId, v: &[QubitId]) {
    b.x(g);
    b.cx(g, v[v.len() - 1]);
    b.x(g);
}

/// XOR z0 into every bit of v (a finished shot's counter reads as all ones).
fn mark_done(b: &mut B, z0: QubitId, v: &[QubitId]) {
    for &q in v {
        b.cx(z0, q);
    }
}

// ------------------------------------------------------------------ masked ladders

struct Masked {
    f: QubitId,
    t: QubitId,
    gf: QubitId,
    chain: Vec<QubitId>,
    pre: Vec<QubitId>,
    c0: QubitId,
}

impl Masked {
    fn alloc(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: b.alloc_n(LB_BITS - 1), pre: b.alloc_n(LB_BITS - 1), c0: b.alloc() }
    }
    /// For the decode's masks on the 7-bit u' (prefix 6, chain 5).
    fn alloc_small(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: b.alloc_n(5), pre: b.alloc_n(6), c0: b.alloc() }
    }
    fn sc(&self) -> Mscr {
        Mscr { f: self.f, t: self.t, gf: self.gf, chain: self.chain.clone() }
    }
    fn free(self, b: &mut B) {
        b.free(self.f);
        b.free(self.t);
        b.free_n(&self.chain);
        b.free_n(&self.pre);
        b.free(self.c0);
    }
}

/// Lanes of the value chain: physical lanes W-hi..W-1 (hi = the window's largest LB; lanes below are off for every
/// active shot); f turns on at physical lane W - LB, ladder lanes 0 ..= hi - lo; above the window the lanes are
/// ordinary. The chain's carry out of lane W-1 is d (the borrow that clears A's MSB wrapped into lane 0 where d = 1,
/// or the carry that restores it); `value_pass` applies it to lane 0 explicitly, since lane 0 holds a cofactor bit
/// where d = 0.
fn value_ladder(u: &GreedyFrog, w: &Win) -> (Vec<QubitId>, Vec<QubitId>) {
    let hi = w.lb.1;
    (u.x[W - hi..].to_vec(), u.y[W - hi..].to_vec())
}

/// F4 (cmpl: X -= Y where a1) or I10 (X += Y where a1, and d ^= the carry); X lane 0 ^= a1 & carry out.
fn value_pass(b: &mut B, u: &GreedyFrog, w: &Win, cmpl: bool, a1: QubitId, d: Option<QubitId>) {
    let m = Masked::alloc(b);
    let (t, s) = value_ladder(u, w);
    let srcs = [value_src(u, &m, w)];
    let sc = m.sc();
    let ld = Lad { t: &t, s: &s, c0: m.c0, srcs: &srcs, f0: false, cmpl, sc: &sc, g: &[] };
    let ru = mup(b, &ld);
    b.play(&ru, false);
    let tc = top_carry(&ld);
    b.ccx(a1, tc, u.x[0]);
    if let Some(d) = d {
        b.ccx(a1, tc, d);
    }
    let rd = mdown(b, &ld, Some(a1));
    b.play(&rd, false);
    m.free(b);
}

fn value_src(u: &GreedyFrog, m: &Masked, w: &Win) -> Src {
    // ladder lane l <-> physical W - hi + l; toggle where LB == hi - l
    let (lo, hi) = w.lb;
    Src { lo: 0, hi: hi - lo + 1, v: u.lb.clone(), a: hi as isize, d: -1, pre: m.pre.clone(), late: false }
}

/// Cofactor chain: target Y, source X, physical lanes W-2-lo down to 0 (lo = the window's smallest LA - d);
/// f turns on at physical lane W - LA - 2. X lane 0's source is `x0` = X[0] & !d (A's MSB sits there where d = 1).
fn cof_ladder(u: &GreedyFrog, w: &Win, x0: QubitId) -> (Vec<QubitId>, Vec<QubitId>) {
    let lo = w.lad.0;
    let t: Vec<QubitId> = (0..=W - 2 - lo).rev().map(|j| u.y[j]).collect();
    let s: Vec<QubitId> = (0..=W - 2 - lo).rev().map(|j| if j == 0 { x0 } else { u.x[j] }).collect();
    (t, s)
}

/// x0 ^= X[0] & !d
fn lane0_src(b: &mut B, u: &GreedyFrog, d: QubitId, x0: QubitId) {
    b.x(d);
    b.ccx(d, u.x[0], x0);
    b.x(d);
}

fn cof_src(u: &GreedyFrog, m: &Masked, w: &Win) -> Src {
    // ladder lane k <-> physical W - 2 - lo - k; toggle where LA == lo + k
    let (lo, hi) = w.lad;
    Src { lo: 0, hi: hi - lo + 1, v: u.la.clone(), a: lo as isize, d: 1, pre: m.pre.clone(), late: false }
}

/// Plain (unmasked) compare of equal-length ladders: out ^= [gate] & [s > t] (cmpl form), registers restored.
fn plain_compare(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, sc: &Mscr, out: QubitId,
                 gate: Option<(QubitId, bool)>) {
    let ld = Lad { t, s, c0, srcs: &[], f0: false, cmpl: true, sc, g: &[] };
    let ru = mup(b, &ld);
    b.play(&ru, false);
    let tc = top_carry(&ld);
    match gate {
        Some((g, neg)) => {
            if neg {
                b.x(g);
            }
            b.ccx(g, tc, out);
            if neg {
                b.x(g);
            }
        }
        None => b.cx(tc, out),
    }
    b.play(&ru, true);
}

/// Run a masked ladder pair. `cmpl`: subtract/compare form. `write`: Some(g) writes the masked sum where g = 1;
/// None only computes the top carry, XORs it into `carry_out`, and restores.
fn masked_pass(b: &mut B, t: &[QubitId], s: &[QubitId], src: Src, m: &Masked, cmpl: bool, write: Option<QubitId>,
               carry_out: Option<QubitId>) {
    let srcs = [src];
    let sc = m.sc();
    let ld = Lad { t, s, c0: m.c0, srcs: &srcs, f0: false, cmpl, sc: &sc, g: &[] };
    let ru = mup(b, &ld);
    b.play(&ru, false);
    if let Some(co) = carry_out {
        let tc = top_carry(&ld);
        b.cx(tc, co);
    }
    match write {
        Some(g) => {
            let rd = mdown(b, &ld, Some(g));
            b.play(&rd, false);
        }
        None => b.play(&ru, true),
    }
}

/// out ^= act & [Y[W-L..W) > X[W-L..W)] on the top WC lanes (L = LB, already done-marked by the caller). When the
/// slot's window has every active LB >= WC the compare is unmasked and `gate` (the done flag, negated) keeps
/// finished shots at 0; `gate` None leaves finished shots' bit arbitrary (callers that mask it themselves).
fn top_compare(b: &mut B, u: &GreedyFrog, out: QubitId, w: &Win, gate: Option<(QubitId, bool)>) {
    if w.lb.0 >= WC {
        let t: Vec<QubitId> = u.x[W - WC..].to_vec();
        let s: Vec<QubitId> = u.y[W - WC..].to_vec();
        let c0 = b.alloc();
        let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
        plain_compare(b, &t, &s, c0, &sc, out, gate);
        b.free(c0);
        return;
    }
    let m = Masked::alloc(b);
    top_compare_masked(b, u, &m, out);
    m.free(b);
}

fn top_compare_masked(b: &mut B, u: &GreedyFrog, m: &Masked, out: QubitId) {
    // ladder over physical lanes W-WC .. W-1; ladder l <-> physical W - WC + l; f on where LB == WC - l
    let t: Vec<QubitId> = u.x[W - WC..].to_vec();
    let s: Vec<QubitId> = u.y[W - WC..].to_vec();
    // shots with LB >= WC start active at lane 0 (f0 = 1 would be wrong for done shots): toggle at l = 0 for any
    // LB >= WC is not expressible as one equality, so the window starts at the lane where LB == WC (l = 0) and
    // shots with LB > WC get an extra toggle source below via the "active from the start" flag.
    let big = b.alloc();
    // big = [LB > WC] & not done-marked (LB <= 256 < 510); LB == WC toggles at ladder lane 0
    {
        let tmp = b.alloc();
        super::mask::ge_const(b, &u.lb, WC as isize + 1, tmp, &m.chain);
        // done-marked LB (>= 510) also passes; exclude it with [LB < 257]
        let lt = b.alloc();
        super::mask::ge_const(b, &u.lb, 257, lt, &m.chain);
        b.x(lt);
        b.ccx(tmp, lt, big);
        b.x(lt);
        super::mask::ge_const(b, &u.lb, 257, lt, &m.chain);
        super::mask::ge_const(b, &u.lb, WC as isize + 1, tmp, &m.chain);
        b.free(lt);
        b.free(tmp);
    }
    // f starts at `big`: emulate f0 = big by toggling f before the ladder; sources toggle where LB == WC - l (l >= 1)
    b.cx(big, m.f);
    let srcs = [Src { lo: 0, hi: WC, v: u.lb.clone(), a: WC as isize, d: -1, pre: m.pre.clone(), late: false }];
    let sc = m.sc();
    let ld = Lad { t: &t, s: &s, c0: m.c0, srcs: &srcs, f0: false, cmpl: true, sc: &sc, g: &[] };
    let ru = super::mask::mup_mid(b, &ld);
    b.play(&ru, false);
    let tc = top_carry(&ld);
    b.cx(tc, out);
    b.play(&ru, true);
    b.cx(big, m.f);
    // recompute big to clear it
    {
        let tmp = b.alloc();
        super::mask::ge_const(b, &u.lb, WC as isize + 1, tmp, &m.chain);
        let lt = b.alloc();
        super::mask::ge_const(b, &u.lb, 257, lt, &m.chain);
        b.x(lt);
        b.ccx(tmp, lt, big);
        b.x(lt);
        super::mask::ge_const(b, &u.lb, 257, lt, &m.chain);
        super::mask::ge_const(b, &u.lb, WC as isize + 1, tmp, &m.chain);
        b.free(lt);
        b.free(tmp);
    }
    b.free(big);
}

/// out ^= AND of literals with caller-given |0> ancillas (len >= n - 2); n - 1 Toffoli; usable in a recording.
fn and_into_t(b: &mut B, lits: &[(QubitId, bool)], out: QubitId, anc: &[QubitId]) {
    let n = lits.len();
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
    if n == 1 {
        b.cx(lits[0].0, out);
    } else if n == 2 {
        b.ccx(lits[0].0, lits[1].0, out);
    } else {
        b.and_c(lits[0].0, lits[1].0, anc[0]);
        for i in 2..n - 1 {
            b.and_c(anc[i - 2], lits[i].0, anc[i - 1]);
        }
        b.ccx(anc[n - 3], lits[n - 1].0, out);
        for i in (2..n - 1).rev() {
            b.and_u(anc[i - 2], lits[i].0, anc[i - 1]);
        }
        b.and_u(lits[0].0, lits[1].0, anc[0]);
    }
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
}

/// Literals of [v == j] on the low v.len() bits.
fn eq_lits(v: &[QubitId], j: usize) -> Vec<(QubitId, bool)> {
    v.iter().enumerate().map(|(i, &q)| (q, (j >> i) & 1 == 0)).collect()
}

/// t += s + cin (cin classical), in place.
fn add_c(b: &mut B, t: &[QubitId], s: &[QubitId], cin: bool, sub: bool) {
    let n = t.len();
    let pad = b.alloc_n(n - s.len());
    let mut ss: Vec<QubitId> = s.to_vec();
    ss.extend(&pad);
    let c0 = b.alloc();
    if cin {
        b.x(c0);
    }
    let ru = super::arith::up_m(b, t, &ss, c0, sub);
    b.play(&ru, false);
    let rd = super::arith::down_m(b, t, &ss, c0, super::arith::Dm::Sum, sub);
    b.play(&rd, false);
    if cin {
        b.x(c0);
    }
    b.free(c0);
    b.free_n(&pad);
}

/// v += k (sub: v -= k) for a classical k, in place (transient constant register).
pub fn add_const(b: &mut B, v: &[QubitId], k: usize, sub: bool) {
    let c = b.alloc_n(v.len());
    for (i, &q) in c.iter().enumerate() {
        if (k >> i) & 1 == 1 {
            b.x(q);
        }
    }
    add_c(b, v, &c, false, sub);
    for (i, &q) in c.iter().enumerate() {
        if (k >> i) & 1 == 1 {
            b.x(q);
        }
    }
    b.free_n(&c);
}

/// F6-F8 by binary search: for k = 2..0, r_k ^= act & [top 2^k lanes of X all zero], then X rotates up by 2^k where
/// r_k. r = min(leading zeros of X, 7) (the marker stops the count when A' = 0); the rest is left to stall slots.
fn renorm_top(b: &mut B, x: &[QubitId], act: QubitId, r: &[QubitId]) {
    for k in (0..r.len()).rev() {
        let n = 1usize << k;
        let mut lits = vec![(act, false)];
        lits.extend((0..n).map(|i| (x[W - 1 - i], true)));
        let anc = b.alloc_n(lits.len().saturating_sub(2));
        and_into_t(b, &lits, r[k], &anc);
        b.free_n(&anc);
        crot_up(b, r[k], x, n);
    }
}

/// Inverse of renorm_top: stage by stage, rotate back and erase r_k.
fn unrenorm_top(b: &mut B, x: &[QubitId], act: QubitId, r: &[QubitId]) {
    for k in 0..r.len() {
        let n = 1usize << k;
        crot_down(b, r[k], x, n);
        let mut lits = vec![(act, false)];
        lits.extend((0..n).map(|i| (x[W - 1 - i], true)));
        let anc = b.alloc_n(lits.len().saturating_sub(2));
        and_into_t(b, &lits, r[k], &anc);
        b.free_n(&anc);
    }
}

impl GreedyFrog {
    /// The DONE counter c lives complemented in Y lanes 0..CNT_BITS: a finished shot's Y is the constant
    /// (B = 1, marker, tA = p), whose lowest lanes hold p's top bits (all ones), so c = !Y[0..8] with c = 0 at the
    /// finish; active shots never touch it.
    pub fn with_cnt(mut self) -> GreedyFrog {
        self.cnt = self.y[..CNT_BITS].to_vec();
        self
    }
    /// c += ctrl
    fn cnt_inc(&self, b: &mut B, ctrl: QubitId) {
        let anc = b.alloc_n(CNT_BITS - 1);
        super::arith::dec(b, ctrl, &self.cnt, &anc);
        b.free_n(&anc);
    }
    /// c -= ctrl
    fn cnt_dec(&self, b: &mut B, ctrl: QubitId) {
        let anc = b.alloc_n(CNT_BITS - 1);
        super::arith::inc(b, ctrl, &self.cnt, &anc);
        b.free_n(&anc);
    }
    /// out ^= [c == 0] (all counter lanes one)
    fn cnt_zero_into(&self, b: &mut B, out: QubitId) {
        let lits: Vec<(QubitId, bool)> = self.cnt.iter().map(|&q| (q, false)).collect();
        and_into(b, &lits, out);
    }

    pub fn alloc(b: &mut B) -> GreedyFrog {
        GreedyFrog { x: b.alloc_n(W), y: b.alloc_n(W), la: b.alloc_n(LB_BITS), lb: b.alloc_n(LB_BITS),
              cnt: vec![], par: b.alloc() }.with_cnt()
    }

    /// sw ^= act & [LA != 0] & X[W-1] & (LA < LB | LA == LB & Y top > X top)   (F9). The top compare is unmasked even
    /// when LB < WC: with LA == LB the values differ inside their top LB lanes unless A' == B, and A' == B forces
    /// B = gcd = 1, so LB == 1 is excluded instead (A' == B == 1 never swaps).
    fn swap_flag_into(&self, b: &mut B, z0: QubitId, sw: QubitId, w: &Win) {
        let lt = b.alloc();
        let eq = b.alloc();
        let cmp = b.alloc();
        let nz = b.alloc();
        lt_into(b, &self.la, &self.lb, lt);
        eq_into(b, &self.la, &self.lb, eq);
        let cmp_into = |b: &mut B, u: &GreedyFrog, cmp: QubitId| {
            let t: Vec<QubitId> = u.x[W - WC..].to_vec();
            let s: Vec<QubitId> = u.y[W - WC..].to_vec();
            let c0 = b.alloc();
            let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
            if w.lb.0 <= 1 {
                let ne1 = b.alloc();
                and_into(b, &eq_lits(&u.lb, 1), ne1);
                b.x(ne1);
                plain_compare(b, &t, &s, c0, &sc, cmp, Some((ne1, false)));
                b.x(ne1);
                and_into(b, &eq_lits(&u.lb, 1), ne1);
                b.free(ne1);
            } else {
                plain_compare(b, &t, &s, c0, &sc, cmp, None);
            }
            b.free(c0);
        };
        cmp_into(b, self, cmp);
        zero_into(b, &self.la, nz); // nz = [LA == 0]
        // sw ^= !z0 & !nz & X[W-1] & (lt | eq & cmp)  (no swap while renormalisation lanes are still owed)
        let ec = b.alloc();
        b.and_c(eq, cmp, ec);
        let or = b.alloc();
        // or = lt | ec = !(!lt & !ec)
        b.x(lt);
        b.x(ec);
        b.and_c(lt, ec, or);
        b.x(or);
        b.x(ec);
        b.x(lt);
        and_into(b, &[(z0, true), (nz, true), (self.x[W - 1], false), (or, false)], sw);
        b.x(lt);
        b.x(ec);
        b.x(or);
        b.and_u(lt, ec, or);
        b.x(ec);
        b.x(lt);
        b.free(or);
        b.and_u(eq, cmp, ec);
        b.free(ec);
        zero_into(b, &self.la, nz);
        cmp_into(b, self, cmp);
        eq_into(b, &self.la, &self.lb, eq);
        lt_into(b, &self.la, &self.lb, lt);
        b.free_n(&[lt, eq, cmp, nz]);
    }

    /// One forward slot (F1..F11). Returns the measurement record.
    pub fn fwd_slot(&mut self, b: &mut B, w: &Win) -> SlotBits {
        prof(b, "f.z0");
        // F1
        let z0 = b.alloc();
        zero_into(b, &self.la, z0);
        self.cnt_inc(b, z0);
        // a1 = act & X[W-1]: the slot steps (else it is a stall that only renormalises, or finished)
        let a1 = b.alloc();
        b.x(z0);
        b.ccx(z0, self.x[W - 1], a1);
        b.x(z0);
        prof(b, "f.dcmp");
        // F2: d = a1 & [B > A >> e] (top window)
        let d = b.alloc();
        mark_msb(b, a1, &self.lb);
        top_compare(b, self, d, w, Some((a1, false)));
        mark_msb(b, a1, &self.lb);
        prof(b, "f.drot");
        // F3
        crot_up(b, d, &self.x, 1);
        prof(b, "f.value");
        // F4: value chain, subtract where a1
        b.x(z0); // z0 now holds act
        mark_done_inv(b, z0, &self.lb);
        value_pass(b, self, w, true, a1, None);
        mark_done_inv(b, z0, &self.lb);
        prof(b, "f.cof");
        // F5: LA -= d; cofactor chain, add where a1
        {
            let anc = b.alloc_n(LB_BITS - 1);
            super::arith::dec(b, d, &self.la, &anc);
            b.free_n(&anc);
        }
        mark_done_inv(b, z0, &self.la);
        {
            let m = Masked::alloc(b);
            let x0 = b.alloc();
            lane0_src(b, self, d, x0);
            let (t, s) = cof_ladder(self, w, x0);
            let src = cof_src(self, &m, w);
            masked_pass(b, &t, &s, src, &m, false, Some(a1), None);
            lane0_src(b, self, d, x0);
            b.free(x0);
            m.free(b);
        }
        mark_done_inv(b, z0, &self.la);
        prof(b, "f.renorm");
        // F6, F7, F8 (every active shot: a step's renormalisation, or a stall's)
        let r = b.alloc_n(RHO_BITS);
        renorm_top(b, &self.x, z0, &r);
        b.x(z0); // back to z0
        sub_small(b, &self.la, &r);
        prof(b, "f.swap");
        // F9, F10
        let sw = b.alloc();
        self.swap_flag_into(b, z0, sw, w);
        super::arith::cswap_regs(b, sw, &self.x, &self.y);
        super::arith::cswap_regs(b, sw, &self.la, &self.lb);
        b.cx(sw, self.par);
        prof(b, "f.ghost");
        // F11: ghost d, r, sw, a1; erase z0 = [LA == 0] & [cnt != 0]
        let bits = SlotBits { d: b.fresh_bits(1)[0], r: b.fresh_bits(RHO_BITS), sw: b.fresh_bits(1)[0],
                              a1: b.fresh_bits(1)[0] };
        b.hmr_to(d, bits.d);
        for i in 0..RHO_BITS {
            b.hmr_to(r[i], bits.r[i]);
        }
        b.hmr_to(sw, bits.sw);
        b.hmr_to(a1, bits.a1);
        b.free(d);
        b.free_n(&r);
        b.free(sw);
        b.free(a1);
        {
            let cz = b.alloc();
            self.cnt_zero_into(b, cz); // cz = [cnt == 0]
            let lz = b.alloc();
            zero_into(b, &self.la, lz);
            and_into(b, &[(lz, false), (cz, true)], z0);
            zero_into(b, &self.la, lz);
            self.cnt_zero_into(b, cz);
            b.free(lz);
            b.free(cz);
        }
        b.free(z0);
        prof(b, "end");
        bits
    }
}


// ------------------------------------------------------------------ inverse slot (decode + undo)

/// window bits of the decode (cofactor top bits kept after normalisation)
pub const NB: usize = 28;
/// division rows (capacity; per-slot counts come from the envelope)
pub const KROWS: usize = 21;
/// Offset of the divisor-length register while the decode's masks run: LA holds u' = LA + sX - UOFF, so the divisor's
/// bit length is mX = NB - u'. Mask-relevant shots have u' in [0, NB] (bits 0..5); u' < 0 (bit 8) means mX > NB.
const UOFF: usize = W - 1 - NB;

/// The masks' 7-bit view of u': bits 0..5 and the sign bit (values below 64 match only shots with u' >= 0).
fn ubits(la: &[QubitId]) -> Vec<QubitId> {
    let mut v = la[..6].to_vec();
    v.push(la[LB_BITS - 1]);
    v
}

/// Bottom-normalise a ring's cofactor window by binary search: for k = 4..0, s_k ^= [lanes 0..2^k all zero], then the
/// lanes shift down by 2^k where s_k. Funnel: stage k swaps (i, i + 2^k) for i < NB + 2^k - 1 only (the lanes the
/// window still needs), a rotation of lanes 0 .. NB + 2^(k+1) - 2. s fresh |0>; slack <= 31.
fn norm_bottom(b: &mut B, ring: &[QubitId], s: &[QubitId]) {
    for k in (0..R_BITS).rev() {
        let n = 1usize << k;
        let lits: Vec<(QubitId, bool)> = (0..n).map(|i| (ring[i], true)).collect();
        let anc = b.alloc_n(n.saturating_sub(2));
        and_into_t(b, &lits, s[k], &anc);
        b.free_n(&anc);
        for i in 0..NB + n - 1 {
            b.cswap(s[k], ring[i], ring[i + n]);
        }
    }
}

/// Inverse of norm_bottom (erases s).
fn denorm_bottom(b: &mut B, ring: &[QubitId], s: &[QubitId]) {
    for k in 0..R_BITS {
        let n = 1usize << k;
        for i in (0..NB + n - 1).rev() {
            b.cswap(s[k], ring[i], ring[i + n]);
        }
        let lits: Vec<(QubitId, bool)> = (0..n).map(|i| (ring[i], true)).collect();
        let anc = b.alloc_n(n.saturating_sub(2));
        and_into_t(b, &lits, s[k], &anc);
        b.free_n(&anc);
    }
}

/// |0> scratch of the division rows and the last-row sweep (allocated outside their recordings). The sweep's running
/// OR f and one-hot y are |0> while rows run, so they double as the rows' carry-in and top-lane zero source; masked
/// rows lend their idle mask-decoder prefix to the sweep's jl.
struct RowTmp {
    /// sign lane above Y lane 0 (row 0's result)
    s0: QubitId,
    /// act & [kt >= j] while the sweep visits row j
    g: QubitId,
    f: QubitId,
    y: QubitId,
    jl: Vec<QubitId>,
    chain: Vec<QubitId>,
    m: Option<Masked>,
}

impl RowTmp {
    fn alloc(b: &mut B, masked: bool) -> RowTmp {
        let (s0, g, y) = (b.alloc(), b.alloc(), b.alloc());
        if masked {
            let m = Masked::alloc_small(b);
            RowTmp { s0, g, f: m.c0, y, jl: m.pre[..R_BITS].to_vec(), chain: m.chain.clone(), m: Some(m) }
        } else {
            RowTmp { s0, g, f: b.alloc(), y, jl: b.alloc_n(R_BITS), chain: b.alloc_n(R_BITS - 1), m: None }
        }
    }
    fn free(self, b: &mut B) {
        b.free_n(&[self.s0, self.g, self.y]);
        match self.m {
            Some(m) => m.free(b),
            None => {
                b.free(self.f);
                b.free_n(&self.jl);
                b.free_n(&self.chain);
            }
        }
    }
    /// carry-in of the rows' adders
    fn c0(&self) -> QubitId {
        self.f
    }
    /// source of each row's top lane (D_j's sign extension)
    fn zero(&self) -> QubitId {
        self.y
    }
    /// rem lane i (i = -1 is s0)
    fn rem(&self, u: &GreedyFrog, i: isize) -> QubitId {
        if i < 0 { self.s0 } else { u.y[i as usize] }
    }
}

/// Non-restoring division rows on the normalised windows: rem = Y[0..NB) (MSB at lane 0, sign lane s0 above it) and
/// div = X[0..NB). LA holds u = LA + sX (the divisor's bit length is mX = W - 1 - u). Row j (j < w.k), with
/// D_j = div >> j: r_{j+1} = r_j - D_j where r_j >= 0, r_j + D_j where r_j < 0, computed mod 2^(NB - j + 1) over rem
/// lanes j-1 .. NB-1. |r_{j+1}| <= D_j < 2^(NB - j), so r_{j+1}'s sign lands in lane j - 1 and the quotient bit is
/// q_j = [r_{j+1} >= 0] = !lane(j - 1); r_j's sign (lane j - 2, r_0 >= 0) picks the sign of the step and stays put.
/// Rows whose window has an active mX < NB - j + 1 are masked so they start at the divisor's LSB lane mX + j - 1
/// (rem's lower bits are untouched there, which is the exact arithmetic). No gating and no allocation: the caller
/// records this and undoes it by playing the recording inverted.
fn division_rows(b: &mut B, u: &GreedyFrog, w: &Win, rt: &RowTmp) {
    for j in 0..w.k {
        let lo = j as isize - 1;
        let t: Vec<QubitId> = (lo..NB as isize).rev().map(|i| rt.rem(u, i)).collect();
        let s: Vec<QubitId> = (lo..NB as isize).rev()
            .map(|i| if i >= j as isize { u.x[i as usize - j] } else { rt.zero() }).collect();
        // m = 1 subtracts: source ^= m, carry-in m. Row 0 always subtracts; row j >= 1 subtracts where lane j - 2 is 0.
        let sign = if j == 0 { None } else { Some(rt.rem(u, j as isize - 2)) };
        let flip = |b: &mut B| {
            for &q in s.iter().chain(std::iter::once(&rt.c0())) {
                if let Some(sg) = sign {
                    b.cx(sg, q);
                }
                b.x(q);
            }
        };
        flip(b);
        if w.mx >= NB - j + 1 {
            let ru = super::arith::up_m(b, &t, &s, rt.c0(), false);
            b.play(&ru, false);
            let rd = super::arith::down_m(b, &t, &s, rt.c0(), super::arith::Dm::Sum, false);
            b.play(&rd, false);
        } else {
            // LA holds u' (mX = NB - u'): the mask turns on at ladder lane l where mX == NB - j - l, i.e. u' == j + l,
            // and is on from the start where mX >= NB - j + 1, i.e. u' < j: big = u'_sign | ![u'_6 >= j] (tmp = g,
            // idle while rows run)
            // the mask flag f starts as big (computed straight into it; the row pair hands it back unchanged)
            let m = rt.m.as_ref().expect("masked row needs mask scratch");
            let (big, tmp, sg) = (m.f, rt.g, u.la[LB_BITS - 1]);
            let big_flip = |b: &mut B, undo: bool| {
                if !undo {
                    super::mask::ge_const(b, &u.la[..6], j as isize, tmp, &m.chain);
                }
                b.x(sg);
                if undo {
                    b.x(big);
                    b.and_u(sg, tmp, big);
                } else {
                    b.and_c(sg, tmp, big);
                    b.x(big);
                }
                b.x(sg);
                if undo {
                    super::mask::ge_const(b, &u.la[..6], j as isize, tmp, &m.chain);
                }
            };
            big_flip(b, false);
            let srcs = [Src { lo: 0, hi: t.len(), v: ubits(&u.la), a: j as isize, d: 1, pre: m.pre.clone(), late: false }];
            let sc = m.sc();
            let ld = Lad { t: &t, s: &s, c0: rt.c0(), srcs: &srcs, f0: false, cmpl: false, sc: &sc, g: &[] };
            let ru = super::mask::mup_mid(b, &ld);
            b.play(&ru, false);
            let rd = super::mask::mdown_mid(b, &ld, Some(ALWAYS));
            b.play(&rd, false);
            big_flip(b, true);
        }
        flip(b);
    }
}

/// jl ^= the last row with q_j = 1 (rem lane j - 1 clear) among the rows j <= kt of active shots, scanning
/// j = k-1 .. 1 with a running OR f: y = q_j & g_j & !f, jl ^= j y, f ^= y, then y = q_j & [jl == j] is erased (jl == j
/// only where row j fired). Row 0 never changes jl (0 is the default), so it is not visited. g_j = act & [kt >= j];
/// g = 0 on entry and exit. No allocation (recorded and undone like the rows).
fn last_row_sweep(b: &mut B, u: &GreedyFrog, act: QubitId, w: &Win, rt: &RowTmp) {
    let (jl, f, y) = (&rt.jl[..], rt.f, rt.y);
    let kt5 = &u.lb[..R_BITS];
    let k = w.k;
    let chain = &rt.chain[..R_BITS - 1];
    // g = act & [kt >= k - 1]
    {
        let ge = y;
        super::mask::ge_const(b, kt5, k as isize - 1, ge, chain);
        b.ccx(act, ge, rt.g);
        super::mask::ge_const(b, kt5, k as isize - 1, ge, chain);
    }
    for j in (1..k).rev() {
        if j + 1 < k {
            let mut lits = vec![(act, false)];
            lits.extend(eq_lits(kt5, j));
            and_into_t(b, &lits, rt.g, chain);
        }
        let lane = rt.rem(u, j as isize - 1);
        and_into_t(b, &[(lane, true), (rt.g, false), (f, true)], y, chain);
        for (i, &bit) in jl.iter().enumerate() {
            if (j >> i) & 1 == 1 {
                b.cx(y, bit);
            }
        }
        b.cx(y, f);
        let mut lits = vec![(lane, true)];
        lits.extend(eq_lits(jl, j));
        and_into_t(b, &lits, y, chain);
    }
    // g = act & [kt >= 1] -> act -> 0
    let mut lits = vec![(act, false)];
    lits.extend(eq_lits(kt5, 0));
    and_into_t(b, &lits, rt.g, chain);
    b.cx(act, rt.g);
}

/// gt ^= [Y window > X window] over the cofactor lanes [0, mX) (LA holds u = LA + sX, mX = W - 1 - u).
fn window_gt(b: &mut B, u: &GreedyFrog, gt: QubitId, w: &Win) {
    let t: Vec<QubitId> = (0..NB).rev().map(|i| u.x[i]).collect();
    let sv: Vec<QubitId> = (0..NB).rev().map(|i| u.y[i]).collect();
    if w.mxp >= NB + 1 {
        let c0 = b.alloc();
        let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
        plain_compare(b, &t, &sv, c0, &sc, gt, None);
        b.free(c0);
        return;
    }
    // LA holds u (mX = W - 1 - u): offset it to u' = u - UOFF (mX = NB - u'). The mask turns on at ladder lane l where
    // mX == NB - l, i.e. u' == l, and is on from the start where mX >= NB + 1, i.e. u' < 0 (its sign bit).
    add_const(b, &u.la, UOFF, true);
    let m = Masked::alloc_small(b);
    let sg = u.la[LB_BITS - 1];
    b.cx(sg, m.f);
    let srcs = [Src { lo: 0, hi: NB, v: ubits(&u.la), a: 0, d: 1, pre: m.pre.clone(), late: false }];
    let sc = m.sc();
    let ld = Lad { t: &t, s: &sv, c0: m.c0, srcs: &srcs, f0: false, cmpl: true, sc: &sc, g: &[] };
    let ru = super::mask::mup_mid(b, &ld);
    b.play(&ru, false);
    let tc = top_carry(&ld);
    b.cx(tc, gt);
    b.play(&ru, true);
    b.cx(sg, m.f);
    m.free(b);
    add_const(b, &u.la, UOFF, false);
}

impl GreedyFrog {
    /// One inverse slot: undo `fwd_slot`, repairing its measurement phases with `bits`.
    pub fn inv_slot(&mut self, b: &mut B, bits: &SlotBits, w: &Win) {
        prof(b, "i.z0");
        // I1: z0 = [LA == 0] & [cnt != 0]
        let z0 = b.alloc();
        {
            let cz = b.alloc();
            self.cnt_zero_into(b, cz);
            let lz = b.alloc();
            zero_into(b, &self.la, lz);
            and_into(b, &[(lz, false), (cz, true)], z0);
            zero_into(b, &self.la, lz);
            self.cnt_zero_into(b, cz);
            b.free(lz);
            b.free(cz);
        }
        // z0 holds act = !z0 except around I5 and at the end
        let act = z0;
        b.x(z0);
        prof(b, "i.prep");
        // decode prep: normalised cofactor windows (slacks sX, sY)
        let sx = b.alloc_n(R_BITS);
        let sy = b.alloc_n(R_BITS);
        norm_bottom(b, &self.x, &sx);
        norm_bottom(b, &self.y, &sy);
        prof(b, "i.swdec");
        // I2: u = LA + sX, v = LB + sY (cofactor bit lengths mX = W - 1 - u, mY = W - 1 - v):
        // sw = act & (mY < mX | mY == mX & winY <= winX)
        add_small(b, &self.la, &sx);
        add_small(b, &self.lb, &sy);
        let sw = b.alloc();
        {
            let lt = b.alloc();
            let eq = b.alloc();
            let gt = b.alloc();
            lt_into(b, &self.la, &self.lb, lt);
            eq_into(b, &self.la, &self.lb, eq);
            window_gt(b, self, gt, w);
            let le = b.alloc();
            b.x(gt);
            b.and_c(eq, gt, le);
            b.x(gt);
            let v = b.alloc();
            b.x(lt);
            b.x(le);
            b.and_c(lt, le, v);
            b.x(v);
            b.ccx(act, v, sw);
            b.x(v);
            b.and_u(lt, le, v);
            b.x(le);
            b.x(lt);
            b.free(v);
            b.x(gt);
            b.and_u(eq, gt, le);
            b.x(gt);
            b.free(le);
            window_gt(b, self, gt, w);
            eq_into(b, &self.la, &self.lb, eq);
            lt_into(b, &self.la, &self.lb, lt);
            b.free_n(&[lt, eq, gt]);
        }
        sub_small(b, &self.lb, &sy);
        sub_small(b, &self.la, &sx);
        prof(b, "i.unswap");
        // I3, I4
        b.z_if(sw, bits.sw);
        super::arith::cswap_regs(b, sw, &self.x, &self.y);
        super::arith::cswap_regs(b, sw, &self.la, &self.lb);
        super::arith::cswap_regs(b, sw, &sx, &sy);
        b.cx(sw, self.par);
        prof(b, "i.swerase");
        // I5: erase sw with the forward's F9 logic
        b.x(z0);
        self.swap_flag_into(b, z0, sw, w);
        b.x(z0);
        b.free(sw);
        prof(b, "i.rows");
        // I6: u = LA + sX in LA, kt = u - (LB + sY) = mY - mX in LB; rows; r = act & (sX - sY - j_last)
        add_small(b, &self.la, &sx);
        add_small(b, &self.lb, &sy);
        for &q in &self.lb {
            b.x(q);
        }
        add_c(b, &self.lb, &self.la, true, false);
        let masked_rows = w.mx < NB + 1;
        if masked_rows {
            add_const(b, &self.la, UOFF, true);
        }
        let rt = RowTmp::alloc(b, masked_rows);
        let r = b.alloc_n(RHO_BITS);
        let a1 = b.alloc();
        b.begin();
        division_rows(b, self, w, &rt);
        let rows = b.end();
        b.play(&rows, false);
        prof(b, "i.sweep");
        b.begin();
        last_row_sweep(b, self, act, w, &rt);
        let sweep = b.end();
        b.play(&sweep, false);
        // jl <- sX - sY - jl in place: the rotation since the last step (rho_of in greedyfrog_model). This slot's rotation
        // rho = act & ((jl mod 8) + #{8, 15, 22, 29 <= jl}) mod 8 and a1 = act & [jl < 8] (the slot was a step).
        // Temps: y and g (|0> after the sweep) and the sweep chain.
        let jl = rt.jl.clone();
        for &q in &jl {
            b.x(q);
        }
        add_c(b, &jl, &sx, true, false);
        add_c(b, &jl, &sy, false, true);
        {
            for i in 0..RHO_BITS {
                b.ccx(act, jl[i], r[i]);
            }
            let (t, c) = (rt.y, rt.g);
            let chain = &rt.chain[..R_BITS - 1];
            for cst in [8isize, 15, 22, 29] {
                super::mask::ge_const(b, &jl, cst, t, chain);
                b.and_c(act, t, c);
                super::arith::inc(b, c, &r, &chain[..RHO_BITS - 1]);
                b.and_u(act, t, c);
                super::mask::ge_const(b, &jl, cst, t, chain);
            }
            and_into_t(b, &[(act, false), (jl[3], true), (jl[4], true)], a1, chain);
        }
        add_c(b, &jl, &sy, false, false);
        add_c(b, &jl, &sx, true, true);
        for &q in &jl {
            b.x(q);
        }
        for i in 0..RHO_BITS {
            b.z_if(r[i], bits.r[i]);
        }
        b.z_if(a1, bits.a1);
        b.play(&sweep, true);
        prof(b, "i.rows_rev");
        b.play(&rows, true);
        rt.free(b);
        if masked_rows {
            add_const(b, &self.la, UOFF, false);
        }
        add_c(b, &self.lb, &self.la, true, true);
        for &q in &self.lb {
            b.x(q);
        }
        sub_small(b, &self.lb, &sy);
        sub_small(b, &self.la, &sx);
        prof(b, "i.denorm");
        denorm_bottom(b, &self.y, &sy);
        denorm_bottom(b, &self.x, &sx);
        b.free_n(&sx);
        b.free_n(&sy);
        prof(b, "i.unrenorm");
        // I7, I8, I9
        add_small(b, &self.la, &r);
        unrenorm_top(b, &self.x, act, &r);
        b.free_n(&r);
        prof(b, "i.value");
        // I10: value add-back where a1; d = a1 & the chain's carry out of lane W-1
        mark_done_inv(b, act, &self.lb);
        let d = b.alloc();
        value_pass(b, self, w, false, a1, Some(d));
        mark_done_inv(b, act, &self.lb);
        b.z_if(d, bits.d);
        prof(b, "i.cof");
        // I11: cofactor undo (LA = LA_pre - d here)
        mark_done_inv(b, act, &self.la);
        {
            let m = Masked::alloc(b);
            let x0 = b.alloc();
            lane0_src(b, self, d, x0);
            let (t, s) = cof_ladder(self, w, x0);
            let src = cof_src(self, &m, w);
            masked_pass(b, &t, &s, src, &m, true, Some(a1), None);
            lane0_src(b, self, d, x0);
            b.free(x0);
            m.free(b);
        }
        mark_done_inv(b, act, &self.la);
        prof(b, "i.dundo");
        // I12, I13, I14
        {
            let anc = b.alloc_n(LB_BITS - 1);
            super::arith::inc(b, d, &self.la, &anc);
            b.free_n(&anc);
        }
        crot_down(b, d, &self.x, 1);
        mark_msb(b, a1, &self.lb);
        top_compare(b, self, d, w, Some((a1, false)));
        mark_msb(b, a1, &self.lb);
        b.free(d);
        prof(b, "i.end15");
        // I15: a1 = act & X[W-1] on the restored pre-state
        b.ccx(act, self.x[W - 1], a1);
        b.free(a1);
        b.x(z0); // z0 = done flag again
        self.cnt_dec(b, z0);
        zero_into(b, &self.la, z0);
        b.free(z0);
        prof(b, "end");
    }
}

/// While z0 holds act (= !done), XOR !act into the counter: finished shots read all ones.
fn mark_done_inv(b: &mut B, act: QubitId, v: &[QubitId]) {
    b.x(act);
    for &q in v {
        b.cx(act, q);
    }
    b.x(act);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::Simulator;
    use super::super::greedyfrog_model::{Lanes, Spec, N};
    use sha3::digest::{ExtendableOutput, Update};

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn input(&mut self) -> N {
            let pp = super::super::greedyfrog_model::p();
            loop {
                let mut v = N::ZERO;
                for i in 0..4 {
                    v |= N::from(self.next()) << (64 * i);
                }
                if v != N::ZERO && v < pp {
                    // the shell reflects dx below p/2: x > p/2 makes the first quotient 1 and the second level start
                    // with equal cofactors (tA = tB = 1), which the decode's floor(tA / tB) cannot read
                    let w = pp - v;
                    return if v < w { v } else { w };
                }
            }
        }
    }

    fn load<R: sha3::digest::XofReader>(sim: &mut Simulator<'_, R>, u: &GreedyFrog, shot: usize, st: &Lanes) {
        let bit = 1u64 << shot;
        let mut set = |q: QubitId, v: bool| {
            if v {
                sim.qubits[q.0 as usize] |= bit;
            }
        };
        for j in 0..W {
            set(u.x[j], st.x[j] == 1);
            // finished shots: Y lanes 0..8 are all ones in the model, the circuit's counter is their complement
            let flip = j < CNT_BITS && (st.cnt >> j) & 1 == 1;
            set(u.y[j], (st.y[j] == 1) != flip);
        }
        for i in 0..LB_BITS {
            set(u.la[i], (st.la >> i) & 1 == 1);
            set(u.lb[i], (st.lb >> i) & 1 == 1);
        }
        set(u.par, st.par == 1);
    }

    fn read<R: sha3::digest::XofReader>(sim: &Simulator<'_, R>, u: &GreedyFrog, shot: usize) -> Lanes {
        let g = |q: QubitId| ((sim.qubits[q.0 as usize] >> shot) & 1) as u8;
        let num = |v: &[QubitId]| v.iter().enumerate().map(|(i, &q)| (g(q) as usize) << i).sum::<usize>();
        let mut y: Vec<u8> = u.y.iter().map(|&q| g(q)).collect();
        let la = num(&u.la);
        let cnt = if la == 0 { (!num(&u.cnt)) & ((1 << CNT_BITS) - 1) } else { 0 };
        if la == 0 {
            for v in y.iter_mut().take(CNT_BITS) {
                *v = 1;
            }
        }
        Lanes { x: u.x.iter().map(|&q| g(q)).collect(), y, la, lb: num(&u.lb), cnt, par: g(u.par) }
    }

    /// One forward slot, 64 shots at random slots (including finished shots), against the lane model.
    #[test]
    fn greedyfrog_fwd_slot_gate_level() {
        let mut b = B::new();
        let mut u = GreedyFrog::alloc(&mut b);
        let start = b.ops.len();
        let _bits = u.fwd_slot(&mut b, &Win::full());
        eprintln!("greedyfrog fwd slot: {} ops, {} Toffoli, live {} peak {}", b.ops.len() - start, b.tof, b.live, b.peak);
        let mut rng = Rng(0xfeed_beef_0101_2323);
        for round in 0..4 {
            let mut states = vec![];
            for _ in 0..64 {
                let x = rng.input();
                let mut sp = Spec::new(x);
                let slot = (rng.next() % 260) as usize;
                for _ in 0..slot {
                    sp.fwd();
                }
                states.push(Lanes::from_spec(&sp));
            }
            let mut h = sha3::Shake256::default();
            h.update(b"greedyfrog-fwd-slot");
            h.update(&[round as u8]);
            let mut xof = h.finalize_xof();
            let nbits = 20_000 + 64;
            let mut sim = Simulator::new(b.width() as usize, nbits, &mut xof);
            for (s, st) in states.iter().enumerate() {
                load(&mut sim, &u, s, st);
            }
            sim.apply_iter(b.ops.iter());
            for (s, st) in states.iter().enumerate() {
                let mut want = st.clone();
                want.fwd();
                let got = read(&sim, &u, s);
                assert_eq!(got, want, "round {round} shot {s}: slot mismatch (la {} lb {} cnt {})", st.la, st.lb, st.cnt);
            }
        }
    }

    /// Forward slot then inverse slot on 64 shots (random slots, finished shots included): the state, the phase and
    /// every scratch qubit must come back to their starting values.
    #[test]
    fn greedyfrog_fwd_inv_roundtrip_gate_level() {
        let mut b = B::new();
        let mut u = GreedyFrog::alloc(&mut b);
        let t0 = b.tof;
        let bits = u.fwd_slot(&mut b, &Win::full());
        let t1 = b.tof;
        u.inv_slot(&mut b, &bits, &Win::full());
        eprintln!("greedyfrog slot pair: fwd {} T, inv {} T, peak {}", t1 - t0, b.tof - t1, b.peak);
        prof_dump();
        let mut regs: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
        for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par)) {
            regs.insert(q.0);
        }
        let mut rng = Rng(0x1357_9bdf_2468_ace0);
        let rounds: usize = std::env::var("GREEDYFROG_ROUNDS").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
        for round in 0..rounds {
            let mut states = vec![];
            for _ in 0..64 {
                let x = rng.input();
                let mut sp = Spec::new(x);
                let slot = (rng.next() % 260) as usize;
                for _ in 0..slot {
                    sp.fwd();
                }
                states.push(Lanes::from_spec(&sp));
            }
            let mut h = sha3::Shake256::default();
            h.update(b"greedyfrog-roundtrip");
            h.update(&[round as u8]);
            let mut xof = h.finalize_xof();
            let mut sim = Simulator::new(b.width() as usize, 20_000 + 64, &mut xof);
            for (s, st) in states.iter().enumerate() {
                load(&mut sim, &u, s, st);
            }
            sim.apply_iter(b.ops.iter());
            assert_eq!(sim.phase, 0, "round {round}: phase garbage {:016x}", sim.phase);
            for q in 0..b.width() {
                if !regs.contains(&q) {
                    assert_eq!(sim.qubits[q as usize], 0, "round {round}: scratch qubit {q} dirty");
                }
            }
            for (s, st) in states.iter().enumerate() {
                assert_eq!(&read(&sim, &u, s), st, "round {round} shot {s}: state not restored (la {} lb {} cnt {})",
                           st.la, st.lb, st.cnt);
            }
        }
    }

    /// Windowed slots: for each listed slot s, forward then inverse slot with the slot's windows on 64 shots that
    /// are at slot s of their walks (forward result checked against the lane model, then the round trip).
    #[test]
    fn greedyfrog_windowed_slots_gate_level() {
        let list: Vec<usize> = std::env::var("GREEDYFROG_SLOTS").ok()
            .map(|v| v.split(',').map(|t| t.parse().unwrap()).collect())
            .unwrap_or(vec![0, 1, 3, 12, 30, 45, 80, 140, 200, 225, 245, NSLOTS - 1]);
        let ws = windows();
        let rounds: usize = std::env::var("GREEDYFROG_ROUNDS").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        let mut rng = Rng(0x7777_1234_5678_9abc);
        for &slot in &list {
            let w = &ws[slot];
            let mut b = B::new();
            let mut u = GreedyFrog::alloc(&mut b);
            let t0 = b.tof;
            let bits = u.fwd_slot(&mut b, w);
            let mid = b.ops.len();
            let t1 = b.tof;
            u.inv_slot(&mut b, &bits, w);
            eprintln!("greedyfrog slot {slot} {:?}: fwd {} T, inv {} T, peak {}", w, t1 - t0, b.tof - t1, b.peak);
            prof_dump();
            let mut regs: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
            for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par)) {
                regs.insert(q.0);
            }
            for round in 0..rounds {
                let mut states = vec![];
                for _ in 0..64 {
                    let x = rng.input();
                    let mut sp = Spec::new(x);
                    for _ in 0..slot {
                        sp.fwd();
                    }
                    states.push(Lanes::from_spec(&sp));
                }
                let mut h = sha3::Shake256::default();
                h.update(b"greedyfrog-windowed");
                h.update(&[round as u8, slot as u8]);
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(b.width() as usize, 20_000 + 64, &mut xof);
                for (sh, st) in states.iter().enumerate() {
                    load(&mut sim, &u, sh, st);
                }
                sim.apply_iter(b.ops[..mid].iter());
                for (sh, st) in states.iter().enumerate() {
                    let mut want = st.clone();
                    want.fwd();
                    assert_eq!(read(&sim, &u, sh), want, "slot {slot} round {round} shot {sh}: forward mismatch");
                }
                sim.apply_iter(b.ops[mid..].iter());
                assert_eq!(sim.phase, 0, "slot {slot} round {round}: phase garbage {:016x}", sim.phase);
                for q in 0..b.width() {
                    if !regs.contains(&q) {
                        assert_eq!(sim.qubits[q as usize], 0, "slot {slot} round {round}: scratch qubit {q} dirty");
                    }
                }
                for (sh, st) in states.iter().enumerate() {
                    assert_eq!(&read(&sim, &u, sh), st, "slot {slot} round {round} shot {sh}: state not restored");
                }
            }
        }
    }

    /// Full traversal: 300 forward slots (final state checked against the model: A = 0, B = 1, tA = p,
    /// tB = +-1/x), then 300 inverse slots back to the start (phase 0, scratch clean). 64 shots.
    #[test]
    fn greedyfrog_traversal_gate_level() {
        if std::env::var("GREEDYFROG_TRAV").is_err() {
            return;
        }
        const NS: usize = NSLOTS;
        let ws = windows();
        let mut b = B::new();
        let mut u = GreedyFrog::alloc(&mut b);
        let mut all_bits = vec![];
        let t0 = b.tof;
        for s in 0..NS {
            all_bits.push(u.fwd_slot(&mut b, &ws[s]));
        }
        let mid_ops = b.ops.len();
        let t1 = b.tof;
        let peak_fwd = b.peak;
        for (s, bits) in all_bits.iter().enumerate().rev() {
            u.inv_slot(&mut b, bits, &ws[s]);
        }
        eprintln!("greedyfrog traversal: forward {} T, inverse {} T, ops {} (+{}), peak {} (forward {})", t1 - t0, b.tof - t1,
                  mid_ops, b.ops.len() - mid_ops, b.peak, peak_fwd);
        prof_dump();
        let mut regs: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
        for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par)) {
            regs.insert(q.0);
        }
        let mut rng = Rng(0x2468_1357_aaaa_5555);
        let mut starts = vec![];
        let mut finals = vec![];
        let mut xs = vec![];
        for _ in 0..64 {
            let x = rng.input();
            let mut sp = Spec::new(x);
            starts.push(Lanes::from_spec(&sp));
            for _ in 0..NS {
                sp.fwd();
            }
            finals.push(Lanes::from_spec(&sp));
            xs.push(x);
        }
        // forward half
        let mut h = sha3::Shake256::default();
        h.update(b"greedyfrog-traversal");
        let mut xof = h.finalize_xof();
        let nbits = 10_000 + 8 * NS + 64;
        let mut sim = Simulator::new(b.width() as usize, nbits, &mut xof);
        for (s, st) in starts.iter().enumerate() {
            load(&mut sim, &u, s, st);
        }
        sim.apply_iter(b.ops[..mid_ops].iter());
        for s in 0..64 {
            let got = read(&sim, &u, s);
            assert_eq!(got, finals[s], "shot {s}: final state differs from the model");
            let sp = got.to_spec();
            let pp = super::super::greedyfrog_model::p();
            assert!(sp.a == N::ZERO && sp.b == N::from(1u64) && sp.ta == pp);
            let t = sp.tb.mul_mod(xs[s], pp);
            assert!(t == N::from(1u64) || t == pp - N::from(1u64), "shot {s}: tB is not +-1/x");
        }
        sim.apply_iter(b.ops[mid_ops..].iter());
        assert_eq!(sim.phase, 0, "phase garbage {:016x}", sim.phase);
        for q in 0..b.width() {
            if !regs.contains(&q) {
                assert_eq!(sim.qubits[q as usize], 0, "scratch qubit {q} dirty");
            }
        }
        for s in 0..64 {
            assert_eq!(read(&sim, &u, s), starts[s], "shot {s}: start not restored");
        }
        eprintln!("greedyfrog traversal: 64 shots exact, round trip clean");
    }
}
