//! greedyfrog: the uniform greedy Euclid traversal circuit. Reference: `greedyfrog_model.rs` (layout, slot order, decode).
//!
//! Registers: rings X (target) and Y (source), W lanes each; bit lengths LA, LB (9 bits); DONE counter cnt (8 bits);
//! swap parity par. Every slot is uniform. The forward slot X-measures its decisions (d, r, sw); the inverse slot
//! recomputes them from the post-state (sw and r from the cofactor windows, d from the wrapped lane 0) and repairs
//! their phases.
//!
//! Masked ladders (mask.rs) get their running-mask toggle from a counter whose bits are XORed with the DONE flag z0
//! while the ladder runs: a finished shot then shows 510/511, which matches no lane, so its mask stays off.

use super::arith::{and_dirty, inc_dirty};
use super::builder::B;
use super::mask::{mdown, mup, top_carry, Lad, Mscr, Src, ALWAYS};
use super::greedyfrog_model::W;
use crate::circuit::{BitId, QubitId};

pub const LB_BITS: usize = 9;
pub const CNT_BITS: usize = 6;
pub const R_BITS: usize = 5;
/// bits of a slot's renormalisation rotation rho <= RCAP = 7 (3-stage barrel)
pub const RHO_BITS: usize = 3;
/// lanes of the top-window compares (F2, F9): exact unless the two values agree on all of them (~2^-40)
pub const WC: usize = 28;
/// lanes added on each side of the measured per-slot envelopes
pub const MARGIN: usize = 2;
/// slots per traversal: steps plus stall slots (200k walks: 8 need >= 257, 4 need 258)
pub const NSLOTS: usize = 254;
/// borrowed lanes the gate tests hand a slot (random contents, checked restored); the shell lends its 256-lane passenger
pub const TEST_DIRTY: usize = 24;

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
    /// no shot can have finished by this slot (the envelope's walks all run 40+ slots longer), so act = 1 classically
    pub act_const: bool,
}

impl Win {
    /// No classical knowledge: every boundary anywhere (masks everywhere, all rows).
    pub fn full() -> Win {
        Win { lb: (1, 256), lad: (0, 256), mxp: 0, mx: 0, k: KROWS, act_const: false }
    }
}

/// slots between the last act-constant slot and the first slot where an envelope walk finished
const ACT_MARGIN: usize = 40;

/// walks behind greedyfrog_data/env.txt
const ENV_WALKS: f64 = 200_000.0;

/// The traversal's windows, slot by slot.
pub fn windows() -> Vec<Win> {
    let (mut first_done, mut all_active_upto) = (usize::MAX, 0usize);
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
        v.push(Win { lb, lad, mxp, mx, k, act_const: false });
        if c[1] as f64 == ENV_WALKS {
            all_active_upto = c[0] as usize;
        } else {
            first_done = first_done.min(c[0] as usize);
        }
    }
    while v.len() < NSLOTS {
        v.push(v.last().unwrap().clone());
    }
    let _ = all_active_upto;
    for (s, w) in v.iter_mut().enumerate() {
        w.act_const = s + ACT_MARGIN < first_done;
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
    /// lanes in an unknown state that the slots borrow as AND-chain ancillas and restore (the shell's idle passenger)
    pub dirty: Vec<QubitId>,
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
    static PROF: std::cell::RefCell<(u64, &'static str, Vec<(&'static str, u64, u64, u64)>, u64)> =
        std::cell::RefCell::new((0, "", vec![], 0));
}
/// GREEDYFROG_PROF=1: accumulate Toffoli per named section, the peak reached inside it and the section's highest live
/// count (debug aid, no effect on gates).
pub fn prof(b: &B, name: &'static str) {
    if std::env::var_os("GREEDYFROG_PROF").is_none() { return; }
    let sp = b.take_sect_peak();
    PROF.with(|p| {
        let mut p = p.borrow_mut();
        if !p.1.is_empty() {
            let (prev, t0) = (p.1, p.0);
            let pk = if b.peak > p.3 { b.peak } else { 0 };
            if let Some(e) = p.2.iter_mut().find(|e| e.0 == prev) {
                e.1 += b.tof - t0;
                e.2 = e.2.max(pk);
                e.3 = e.3.max(sp);
            } else {
                p.2.push((prev, b.tof - t0, pk, sp));
            }
        }
        p.3 = b.peak;
        p.0 = b.tof;
        p.1 = if name == "end" { "" } else { name };
    });
}
pub fn prof_dump() {
    PROF.with(|p| {
        for (n, t, pk, sp) in p.borrow().2.iter() {
            eprintln!("GREEDYFROG_PROF {n:16} {t:8} max live {sp:4} {}", if *pk > 0 { format!("new peak {pk}") } else { String::new() });
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

/// Exact short-register add/sub with arbitrary borrowed padding. The second
/// ripple cancels the borrowed high addend, so no zero-extension pad is needed.
fn short_add_dirty(b: &mut B, t: &[QubitId], s: &[QubitId], sub: bool, dirty: &[QubitId]) {
    let h = t.len() - s.len();
    let mut ss=s.to_vec(); ss.extend_from_slice(&dirty[..h]);
    let c0=b.alloc();
    let up=super::arith::up_m(b,t,&ss,c0,sub); b.play(&up,false);
    let down=super::arith::down_m(b,t,&ss,c0,super::arith::Dm::Sum,sub); b.play(&down,false);
    let up=super::arith::up_m(b,&t[s.len()..],&dirty[..h],c0,!sub); b.play(&up,false);
    let down=super::arith::down_m(b,&t[s.len()..],&dirty[..h],c0,super::arith::Dm::Sum,!sub); b.play(&down,false);
    b.free(c0);
}

fn short_add_c_on(b:&mut B,t:&[QubitId],s:&[QubitId],cin:bool,sub:bool,c0:QubitId,dirty:&[QubitId]) {
    let h=t.len()-s.len();let mut ss=s.to_vec();ss.extend_from_slice(&dirty[..h]);
    if cin {b.x(c0);}
    let up=super::arith::up_m(b,t,&ss,c0,sub);b.play(&up,false);
    let down=super::arith::down_m(b,t,&ss,c0,super::arith::Dm::Sum,sub);b.play(&down,false);
    if cin {b.x(c0);}
    let up=super::arith::up_m(b,&t[s.len()..],&dirty[..h],c0,!sub);b.play(&up,false);
    let down=super::arith::down_m(b,&t[s.len()..],&dirty[..h],c0,super::arith::Dm::Sum,!sub);b.play(&down,false);
}

/// sub_small with part of the zero-extension on given |0> lanes (restored |0>)
fn sub_small_pad(b: &mut B, t: &[QubitId], s: &[QubitId], given: &[QubitId]) {
    let n = t.len();
    let pad = b.alloc_n(n - s.len() - given.len());
    let mut ss: Vec<QubitId> = s.to_vec();
    ss.extend(&pad);
    ss.extend(given);
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
/// out ^= [v == 0] with borrowed lanes for the AND.
fn zero_into_d(b: &mut B, v: &[QubitId], out: QubitId, dirty: &[QubitId]) {
    let lits: Vec<(QubitId, bool)> = v.iter().map(|&q| (q, true)).collect();
    and_dirty(b, &lits, out, dirty);
}

/// eq_into with borrowed lanes for the AND.
fn eq_into_d(b: &mut B, a: &[QubitId], bb: &[QubitId], out: QubitId, dirty: &[QubitId]) {
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
    zero_into_d(b, a, out, dirty);
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
}

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
        // the comparator chain is only read by the ladder's end-of-pass mask cleanup (mask::f_end), where every
        // decoder prefix lane is |0> again (cleared when its source window ends): the chain runs on the prefix lanes
        let f = b.alloc();
        let t = b.alloc();
        let pre = b.alloc_n(LB_BITS - 2);
        let mut chain=pre.clone(); chain.push(t);
        Masked { f, t, gf: f, chain, pre, c0: b.alloc() }
    }
    /// The 9-bit decoder without a comparator chain: its comparators borrow lanes (`ge_const_dirty`, `in_range`).
    fn alloc_lean(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: vec![], pre: b.alloc_n(LB_BITS - 3), c0: b.alloc() }
    }
    /// For the decode's masks on the 6-bit u' (prefix 5; comparators borrow lanes) with a given AND temp.
    fn alloc_small_on(b: &mut B, t: QubitId) -> Masked {
        let f = b.alloc();
        Masked { f, t, gf: f, chain: vec![], pre: b.alloc_n(2), c0: b.alloc() }
    }
    /// For the decode's masks on the 6-bit u' (prefix 5; comparators borrow lanes).
    fn alloc_small(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: vec![], pre: b.alloc_n(5), c0: b.alloc() }
    }
    fn sc(&self) -> Mscr {
        Mscr { f: self.f, t: self.t, gf: self.gf, chain: self.chain.clone() }
    }
    fn free(self, b: &mut B) {
        b.free(self.f);
        b.free(self.t);
        if self.chain.first() != self.pre.first() || self.chain.is_empty() {
            b.free_n(&self.chain);
        }
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
    top_compare_masked(b, u, out);
}

/// big ^= [LB > WC] & [LB < 257] (done-marked LB >= 510 excluded), comparators on a clean chain held only meanwhile.
fn big_lb_flip(b: &mut B, u: &GreedyFrog, big: QubitId) {
    // [LB >= WC+1] XOR [LB >=257] is exactly the interval indicator.
    let chain = b.alloc_n(LB_BITS - 1);
    super::mask::ge_const(b, &u.lb, WC as isize + 1, big, &chain);
    super::mask::ge_const(b, &u.lb, 257, big, &chain);
    b.free_n(&chain);
}

fn top_compare_masked(b: &mut B, u: &GreedyFrog, out: QubitId) {
    // ladder over physical lanes W-WC .. W-1; ladder l <-> physical W - WC + l; f on where LB == WC - l
    let t: Vec<QubitId> = u.x[W - WC..].to_vec();
    let s: Vec<QubitId> = u.y[W - WC..].to_vec();
    // shots with LB >= WC start active at lane 0 (f0 = 1 would be wrong for done shots): toggle at l = 0 for any
    // LB >= WC is not expressible as one equality, so the window starts at the lane where LB == WC (l = 0) and
    // shots with LB > WC get an extra toggle source below via the "active from the start" flag `big`, computed
    // before the mask scratch exists (its comparator chain and the ladder's scratch never coexist).
    let big = b.alloc();
    big_lb_flip(b, u, big);
    let m = Masked::alloc_lean(b);
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
    m.free(b);
    big_lb_flip(b, u, big);
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
    let c0 = b.alloc();
    add_c_on(b, t, s, cin, sub, c0);
    b.free(c0);
}

/// add_c with the carry-in on a given |0> lane (restored).
fn add_c_on(b: &mut B, t: &[QubitId], s: &[QubitId], cin: bool, sub: bool, c0: QubitId) {
    let n = t.len();
    let pad = b.alloc_n(n - s.len());
    let mut ss: Vec<QubitId> = s.to_vec();
    ss.extend(&pad);
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
    b.free_n(&pad);
}

/// v += k (sub: v -= k) for a classical k, in place (transient constant register).
/// v += k (or -= k) mod 2^n with borrowed lanes and no constant register: one increment of v[i..] per set bit i of k
/// (a decrement is an increment conjugated by NOT on every bit).
fn add_const_dirty(b: &mut B, v: &[QubitId], k: usize, sub: bool, dirty: &[QubitId]) {
    for i in 0..v.len() {
        if (k >> i) & 1 == 1 {
            if sub {
                for &q in &v[i..] {
                    b.x(q);
                }
            }
            let w = &v[i..];
            for h in (1..w.len()).rev() {
                let lits: Vec<(QubitId, bool)> = w[..h].iter().map(|&q| (q, false)).collect();
                and_dirty(b, &lits, w[h], dirty);
            }
            b.x(w[0]);
            if sub {
                for &q in &v[i..] {
                    b.x(q);
                }
            }
        }
    }
}

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
fn renorm_top(b: &mut B, x: &[QubitId], act: Option<QubitId>, r: &[QubitId]) {
    for k in (0..r.len()).rev() {
        let n = 1usize << k;
        let mut lits = act_lits(act);
        lits.extend((0..n).map(|i| (x[W - 1 - i], true)));
        let anc = b.alloc_n(lits.len().saturating_sub(2));
        and_into_t(b, &lits, r[k], &anc);
        b.free_n(&anc);
        crot_up(b, r[k], x, n);
    }
}

/// Inverse of renorm_top: stage by stage, rotate back and erase r_k.
fn unrenorm_top(b: &mut B, x: &[QubitId], act: Option<QubitId>, r: &[QubitId]) {
    for k in 0..r.len() {
        let n = 1usize << k;
        crot_down(b, r[k], x, n);
        let mut lits = act_lits(act);
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
              dirty: b.alloc_n(TEST_DIRTY),
              cnt: vec![], par: b.alloc() }.with_cnt()
    }

    /// sw ^= act & [LA != 0] & X[W-1] & (LA < LB | LA == LB & Y top > X top)   (F9). The top compare is unmasked even
    /// when LB < WC: with LA == LB the values differ inside their top LB lanes unless A' == B, and A' == B forces
    /// B = gcd = 1, so LB == 1 is excluded instead (A' == B == 1 never swaps).
    fn swap_flag_into(&self, b: &mut B, z0: Option<QubitId>, sw: QubitId, w: &Win) {
        let cmp = b.alloc();
        let cmp_into = |b: &mut B, u: &GreedyFrog, cmp: QubitId| {
            let t: Vec<QubitId> = u.x[W - WC..].to_vec();
            let s: Vec<QubitId> = u.y[W - WC..].to_vec();
            let c0 = b.alloc();
            let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
            if w.lb.0 <= 1 {
                let ne1 = b.alloc();
                and_dirty(b, &eq_lits(&u.lb, 1), ne1, &u.dirty);
                b.x(ne1);
                plain_compare(b, &t, &s, c0, &sc, cmp, Some((ne1, false)));
                b.x(ne1);
                and_dirty(b, &eq_lits(&u.lb, 1), ne1, &u.dirty);
                b.free(ne1);
            } else {
                plain_compare(b, &t, &s, c0, &sc, cmp, None);
            }
            b.free(c0);
        };
        cmp_into(b, self, cmp);
        let lt = b.alloc();
        lt_into(b, &self.la, &self.lb, lt);
        let eq = b.alloc();
        eq_into_d(b, &self.la, &self.lb, eq, &self.dirty);
        let nz = b.alloc();
        zero_into_d(b, &self.la, nz, &self.dirty); // nz = [LA == 0]
        // sw ^= !z0 & !nz & X[W-1] & (lt | eq & cmp)  (no swap while renormalisation lanes are still owed)
        let mut common: Vec<(QubitId,bool)>=z0.map(|z|vec![(z,true)]).unwrap_or_default();
        common.extend([(nz,true),(self.x[W-1],false)]);
        let mut lterm=common.clone(); lterm.push((lt,false));
        and_dirty(b,&lterm,sw,&self.dirty);
        common.extend([(eq,false),(cmp,false)]);
        and_dirty(b,&common,sw,&self.dirty);
        zero_into_d(b, &self.la, nz, &self.dirty);
        b.free(nz);
        eq_into_d(b, &self.la, &self.lb, eq, &self.dirty);
        b.free(eq);
        lt_into(b, &self.la, &self.lb, lt);
        b.free(lt);
        cmp_into(b, self, cmp);
        b.free(cmp);
    }

    /// One forward slot (F1..F11). Returns the measurement record.
    pub fn fwd_slot(&mut self, b: &mut B, w: &Win) -> SlotBits {
        super::mask::set_borrowed(&self.dirty);
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
        mark_done_inv(b, Some(z0), &self.lb);
        value_pass(b, self, w, true, a1, None);
        mark_done_inv(b, Some(z0), &self.lb);
        prof(b, "f.cof");
        // F5: LA -= d; cofactor chain, add where a1
        {
            let anc = b.alloc_n(LB_BITS - 1);
            super::arith::dec(b, d, &self.la, &anc);
            b.free_n(&anc);
        }
        mark_done_inv(b, Some(z0), &self.la);
        {
            let m = Masked::alloc(b);
            let x0 = self.x[0];
            let (t, s) = cof_ladder(self, w, x0);
            let src = cof_src(self, &m, w);
            masked_pass(b, &t, &s, src, &m, false, Some(a1), None);
            m.free(b);
        }
        mark_done_inv(b, Some(z0), &self.la);
        prof(b, "f.renorm");
        // F6, F7, F8 (every active shot: a step's renormalisation, or a stall's)
        let r = b.alloc_n(RHO_BITS);
        renorm_top(b, &self.x, Some(z0), &r);
        b.x(z0); // back to z0
        sub_small(b, &self.la, &r);
        prof(b, "f.swap");
        // F9, F10
        let sw = b.alloc();
        self.swap_flag_into(b, Some(z0), sw, w);
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

/// The masks' 6-bit view of u': bits 0..4 and the sign bit (values below 32 match only shots with u' >= 0; active
/// shots have u' = NB - mX <= NB - 1).
fn ubits(la: &[QubitId]) -> Vec<QubitId> {
    let mut v = la[..5].to_vec();
    v.push(la[LB_BITS - 1]);
    v
}

/// Bottom-normalise a ring's cofactor window by binary search: for k = 4..0, s_k ^= [lanes 0..2^k all zero], then the
/// lanes shift down by 2^k where s_k. Funnel: stage k swaps (i, i + 2^k) for i < NB + 2^k - 1 only (the lanes the
/// window still needs), a rotation of lanes 0 .. NB + 2^(k+1) - 2. s fresh |0>; slack <= 31.
fn norm_bottom(b: &mut B, ring: &[QubitId], s: &[QubitId], dirty: &[QubitId]) {
    for k in (0..R_BITS).rev() {
        let n = 1usize << k;
        let lits: Vec<(QubitId, bool)> = (0..n).map(|i| (ring[i], true)).collect();
        and_dirty(b, &lits, s[k], dirty);
        for i in 0..NB + n - 1 {
            b.cswap(s[k], ring[i], ring[i + n]);
        }
    }
}

fn norm_bottom_active(b: &mut B, ring: &[QubitId], s: &[QubitId], dirty: &[QubitId], act: Option<QubitId>) {
    for k in (0..R_BITS).rev() {
        let n = 1usize << k;
        let mut lits = act_lits(act);
        lits.extend((0..n).map(|i| (ring[i], true)));
        and_dirty(b, &lits, s[k], dirty);
        for i in 0..NB + n - 1 {
            b.cswap(s[k], ring[i], ring[i + n]);
        }
    }
}

/// Inverse of norm_bottom (erases s).
fn denorm_bottom(b: &mut B, ring: &[QubitId], s: &[QubitId], dirty: &[QubitId]) {
    for k in 0..s.len() {
        let n = 1usize << k;
        for i in (0..NB + n - 1).rev() {
            b.cswap(s[k], ring[i], ring[i + n]);
        }
        let lits: Vec<(QubitId, bool)> = (0..n).map(|i| (ring[i], true)).collect();
        and_dirty(b, &lits, s[k], dirty);
    }
}

fn denorm_bottom_active(b: &mut B, ring: &[QubitId], s: &[QubitId], dirty: &[QubitId], act: Option<QubitId>) {
    for k in 0..s.len() {
        let n = 1usize << k;
        for i in (0..NB + n - 1).rev() {
            b.cswap(s[k], ring[i], ring[i + n]);
        }
        let mut lits = act_lits(act);
        lits.extend((0..n).map(|i| (ring[i], true)));
        and_dirty(b, &lits, s[k], dirty);
    }
}

/// |0> scratch of the division rows and the last-row sweep (allocated outside their recordings). The sweep's running
/// OR f and one-hot y are |0> while rows run, so they double as the rows' carry-in and top-lane zero source; masked
/// rows lend their idle mask-decoder prefix to the sweep's jl.
struct RowTmp {
    /// y is a borrowed |0> lane (not freed here)
    ybor: bool,
    sbor: bool,
    /// sign lane above Y lane 0 (row 0's result)
    s0: QubitId,
    /// act & [kt >= j] while the sweep visits row j
    g: QubitId,
    f: QubitId,
    y: QubitId,
    jl: Vec<QubitId>,
    m: Option<Masked>,
}

impl RowTmp {
    #[allow(dead_code)]
    fn alloc(b: &mut B, masked: bool) -> RowTmp {
        RowTmp::alloc_y(b, masked, None, None)
    }
    fn alloc_y(b: &mut B, masked: bool, yb: Option<QubitId>, sb: Option<QubitId>) -> RowTmp {
        let s0 = sb.unwrap_or_else(||b.alloc());
        let sbor=sb.is_some();
        let y = match yb { Some(q) => q, None => b.alloc() };
        let ybor = yb.is_some();
        if masked {
            let g = b.alloc();
            let m = Masked::alloc_small_on(b, g);
            // Decoder prefixes and the running mask are zero after the rows,
            // and are reused for the five-bit jl register.
            let mut jl = m.pre.clone(); jl.extend([m.f,m.c0,g]);
            RowTmp { ybor, sbor, s0, g, f: m.c0, y, jl, m: Some(m) }
        } else {
            // jl is zero while rows run; the sweep derives !f from jl==0.
            let jl = b.alloc_n(R_BITS);
            RowTmp { ybor, sbor, s0, g: y, f: jl[R_BITS-1], y, jl, m: None }
        }
    }
    fn free(self, b: &mut B) {
        if !self.sbor {b.free(self.s0);}
        if !self.ybor {
            b.free(self.y);
        }
        match self.m {
            // the mask scratch's AND temp is g
            Some(m) => m.free(b),
            None => {
                b.free_n(&self.jl);
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
    let masked_row = |j: usize| w.mx < NB - j + 1;
    let sg = u.la[LB_BITS - 1];
    // The masked rows' flag f holds big_j = u'_sign | ![u'_5 >= j] while row j runs (the row pair hands it back
    // unchanged): big_0 = u'_sign, big_j ^ big_(j+1) = !u'_sign & [u'_5 == j], and after the last masked row it is
    // cleared with the comparator. The masked rows are the first ones (j < NB + 1 - mX).
    if masked_row(0) {
        b.cx(sg, rt.m.as_ref().expect("masked row needs mask scratch").f);
    }
    for j in 0..w.k {
        let lo = j as isize - 1;
        let t: Vec<QubitId> = (lo..NB as isize).rev().map(|i| rt.rem(u, i)).collect();
        let s: Vec<QubitId> = (lo..NB as isize).rev()
            .map(|i| if i >= j as isize { u.x[i as usize - j] } else { rt.zero() }).collect();
        // m = 1 subtracts: source ^= m, carry-in m. Row 0 always subtracts; row j >= 1 subtracts where lane j - 2 is 0.
        let sign = if j == 0 { None } else { Some(rt.rem(u, j as isize - 2)) };
        let flip = |b: &mut B| {
            let ns=if w.mx>=NB+1 {s.len()-1} else {s.len()};
            for &q in s[..ns].iter().chain(std::iter::once(&rt.c0())) {
                if let Some(sg) = sign {
                    b.cx(sg, q);
                }
                b.x(q);
            }
        };
        flip(b);
        if w.mx >= NB + 1 {
            let n=t.len()-1;
            let ru=super::arith::up_m(b,&t[..n],&s[..n],rt.c0(),false);
            b.play(&ru,false);
            b.cx(s[n-1],t[n]);
            b.x(t[n]);
            if let Some(sg)=sign {b.cx(sg,t[n]);}
            let rd=super::arith::down_m(b,&t[..n],&s[..n],rt.c0(),super::arith::Dm::Sum,false);
            b.play(&rd,false);
        } else if w.mx >= NB - j + 1 {
            let ru = super::arith::up_m(b, &t, &s, rt.c0(), false);
            b.play(&ru, false);
            let rd = super::arith::down_m(b, &t, &s, rt.c0(), super::arith::Dm::Sum, false);
            b.play(&rd, false);
        } else {
            // LA holds u' (mX = NB - u'): the mask turns on at ladder lane l where mX == NB - j - l, i.e. u' == j + l,
            // and is on from the start where mX >= NB - j + 1, i.e. u' < j: f holds big_j (top of the function)
            let m = rt.m.as_ref().expect("masked row needs mask scratch");
            // big = !(!sign & [u'_5 >= j]), computed straight into the flag (the sign literal gates every comparator
            // cube), so no temporary is held across the ladder and g serves as the masked cells' AND temp
            let big = m.f;
            let srcs = [Src { lo: 0, hi: t.len(), v: ubits(&u.la), a: j as isize, d: 1, pre: m.pre.clone(), late: false }];
            let sc = m.sc();
            let ld = Lad { t: &t, s: &s, c0: rt.c0(), srcs: &srcs, f0: false, cmpl: false, sc: &sc, g: &[] };
            let ru = super::mask::mup_mid(b, &ld);
            b.play(&ru, false);
            let rd = super::mask::mdown_mid(b, &ld, Some(ALWAYS));
            b.play(&rd, false);
            if j + 1 < w.k && masked_row(j + 1) {
                let mut lits = vec![(sg, true)];
                lits.extend(eq_lits(&u.la[..5], j));
                and_dirty(b, &lits, big, &u.dirty);
            } else {
                b.x(big);
                super::mask::ge_const_dirty_gated(b, &u.la[..5], j as isize, big, &[(sg, true)], &u.dirty);
            }
        }
        flip(b);
    }
}

/// The literal list of an optional act flag (None: act = 1 classically).
fn act_lits(act: Option<QubitId>) -> Vec<(QubitId, bool)> {
    act.map(|a| vec![(a, false)]).unwrap_or_default()
}

/// t ^= act & c
fn act_cx(b: &mut B, act: Option<QubitId>, c: QubitId, t: QubitId) {
    match act {
        Some(a) => b.ccx(a, c, t),
        None => b.cx(c, t),
    }
}

/// AND / comparator on a clean chain (`clean`) or on borrowed lanes.
fn and_any(b: &mut B, clean: bool, lits: &[(QubitId, bool)], out: QubitId, chain: &[QubitId]) {
    if clean { and_into_t(b, lits, out, chain) } else { and_dirty(b, lits, out, chain) }
}
fn ge_any(b: &mut B, v: &[QubitId], k: isize, t: QubitId, chain: &[QubitId], clean: bool) {
    if clean { super::mask::ge_const(b, v, k, t, chain) } else { super::mask::ge_const_dirty(b, v, k, t, chain) }
}

/// jl ^= the last row with q_j = 1 (rem lane j - 1 clear) among the rows j <= kt of active shots, scanning
/// j = k-1 .. 1 with a running OR f: y = q_j & g_j & !f, jl ^= j y, f ^= y, then y = q_j & [jl == j] is erased (jl == j
/// only where row j fired). Row 0 never changes jl (0 is the default), so it is not visited. g_j = act & [kt >= j];
/// g = 0 on entry and exit. No allocation (recorded and undone like the rows).
/// A short clean prefix factors shared controls before a borrowed-lane AND.
fn and_prefix(b:&mut B,lits:&[(QubitId,bool)],out:QubitId,clean:&[QubitId],dirty:&[QubitId]) {
    if clean.is_empty() || lits.len()<3 { and_dirty(b,lits,out,dirty); return; }
    let np=clean.len().min(lits.len()-2);
    b.begin();
    for i in 0..np {
        let (a,na)=if i==0 {lits[0]} else {(clean[i-1],false)};
        let (c,nc)=lits[i+1];
        if na {b.x(a);} if nc {b.x(c);}
        b.and_c(a,c,clean[i]);
        if nc {b.x(c);} if na {b.x(a);}
    }
    let rec=b.end();b.play(&rec,false);
    let mut rest=vec![(clean[np-1],false)];rest.extend_from_slice(&lits[np+1..]);
    and_dirty(b,&rest,out,dirty);b.play(&rec,true);
}
fn ge_prefix(b:&mut B,v:&[QubitId],k:usize,out:QubitId,gate:&[(QubitId,bool)],clean:&[QubitId],dirty:&[QubitId]) {
    let eq=|i:usize|(v[i],(k>>i)&1==0);
    for i in (0..v.len()).rev() {if (k>>i)&1==0 {
        let mut lits=gate.to_vec();lits.extend((i+1..v.len()).map(eq));lits.push((v[i],false));
        and_prefix(b,&lits,out,clean,dirty);
    }}
    let mut lits=gate.to_vec();lits.extend((0..v.len()).map(eq));and_prefix(b,&lits,out,clean,dirty);
}

// SnehalRaj e2a4ddad's still-searching sweep, adapted to the existing
// y lane and prefix allocator. Clear its final found flag from jl so that
// the old arithmetic and inverse-recording interface remains unchanged.
fn last_row_sweep(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, clean: Option<&[QubitId]>) {
    let jl=&rt.jl[..]; let search=rt.y;
    let spare=if rt.m.is_some() && !rt.jl.contains(&rt.g) {vec![rt.g]} else {vec![]};
    let clean=clean.unwrap_or(&spare);
    let kt=&u.lb[..R_BITS];let gate=act_lits(act);
    ge_prefix(b,kt,w.k-1,search,&gate,clean,&u.dirty);
    for j in (1..w.k).rev() {
        if j+1<w.k {
            let mut lits=gate.clone();lits.extend(eq_lits(kt,j));
            and_prefix(b,&lits,search,clean,&u.dirty);
        }
        let lane=rt.rem(u,j as isize-1);b.x(lane);
        for (i,&q) in jl.iter().enumerate() {if (j>>i)&1==1 {b.ccx(lane,search,q);}}
        b.x(lane);
        and_prefix(b,&eq_lits(jl,j),search,clean,&u.dirty);
    }
    let mut lits=gate.clone();lits.extend(eq_lits(kt,0));
    and_prefix(b,&lits,search,clean,&u.dirty);
    match act {Some(a)=>b.cx(a,search),None=>b.x(search)}
    // search now equals [jl !=0].
    b.x(search);
    and_prefix(b,&eq_lits(jl,0),search,clean,&u.dirty);
}

/// gt ^= [Y window > X window] over the cofactor lanes [0, mX) (LA holds u = LA + sX, mX = W - 1 - u).
fn window_gt(b: &mut B, u: &GreedyFrog, gt: QubitId, w: &Win) {
    window_gt_on(b, u, gt, w, None)
}

/// window_gt with an optional |0> lane for the masked cells' AND temp
fn window_gt_on(b: &mut B, u: &GreedyFrog, gt: QubitId, w: &Win, tmp: Option<QubitId>) {
    let t: Vec<QubitId> = (0..NB).rev().map(|i| u.x[i]).collect();
    let sv: Vec<QubitId> = (0..NB).rev().map(|i| u.y[i]).collect();
    if w.mxp >= NB + 1 {
        // Normalized X[0] is one; active Y[0] is also one. Omit both
        // equal high bits, and borrow the complemented X[0] as carry-in.
        // Finished Y is unnormalized, but swap is gated by act.
        let c0 = u.x[0]; b.x(c0);
        let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
        plain_compare(b, &t[..NB-1], &sv[..NB-1], c0, &sc, gt, None);
        b.x(c0);
        return;
    }
    // LA holds u (mX = W - 1 - u): offset it to u' = u - UOFF (mX = NB - u'). The mask turns on at ladder lane l where
    // mX == NB - l, i.e. u' == l, and is on from the start where mX >= NB + 1, i.e. u' < 0 (its sign bit).
    add_const_dirty(b, &u.la, UOFF, true, &u.dirty);
    let swla = w.act_const;
    if swla {
        b.cx(u.la[LB_BITS - 1], u.la[LB_BITS - 2]);
    }
    let m = {
        let f = b.alloc();
        let t = match tmp { Some(t) => t, None => super::mask::DIRTY_T };
        let c0 = if swla { u.la[LB_BITS - 2] } else { b.alloc() };
        Masked { f, t, gf: f, chain: vec![], pre: vec![], c0 }
    };
    let own_t = false;
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
    b.free(m.f);
    b.free_n(&m.pre);
    if own_t { b.free(m.t); }
    if swla {
        b.cx(u.la[LB_BITS - 1], u.la[LB_BITS - 2]);
    } else {
        b.free(m.c0);
    }
    add_const_dirty(b, &u.la, UOFF, false, &u.dirty);
}

impl GreedyFrog {
    /// One inverse slot: undo `fwd_slot`, repairing its measurement phases with `bits`.
    pub fn inv_slot(&mut self, b: &mut B, bits: &SlotBits, w: &Win) {
        super::mask::set_borrowed(&self.dirty);
        prof(b, "i.z0");
        // I1: z0 = [LA == 0] & [cnt != 0]; on slots where no shot can have finished, act = 1 classically and the
        // flag (and the DONE bookkeeping) is skipped
        let z0 = if w.act_const { None } else { Some(b.alloc()) };
        if let Some(z0) = z0 {
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
        if let Some(z0) = z0 {
            b.x(z0);
        }
        prof(b, "i.prep");
        // decode prep: normalised cofactor windows (slacks sX, sY)
        let sx = b.alloc_n(R_BITS);
        let mut sy = b.alloc_n(R_BITS);
        norm_bottom(b, &self.x, &sx, &self.dirty);
        norm_bottom_active(b, &self.y, &sy, &self.dirty, act);
        prof(b, "i.swdec");
        // I2: u = LA + sX, v = LB + sY (cofactor bit lengths mX = W - 1 - u, mY = W - 1 - v):
        // sw = act & (mY < mX | mY == mX & winY <= winX)
        short_add_dirty(b, &self.la, &sx, false, &self.dirty);
        short_add_dirty(b, &self.lb, &sy, false, &self.dirty);
        let sw = b.alloc();
        {
            // The lt and equality terms are disjoint; write them to sw separately.
            let c0=b.alloc();
            let less=super::arith::up(b,&self.la,&self.lb,c0);
            b.play(&less,false);
            act_cx(b,act,self.lb[LB_BITS-1],sw);
            b.play(&less,true);
            b.free(c0);
            let gt=b.alloc();
            window_gt_on(b,self,gt,w,None);
            // Equality contributes directly; its flag need not coexist with gt.
            for i in 0..LB_BITS {b.cx(self.lb[i],self.la[i]);}
            let mut lits=act_lits(act);lits.push((gt,true));
            lits.extend(self.la.iter().map(|&q|(q,true)));
            and_dirty(b,&lits,sw,&self.dirty);
            for i in 0..LB_BITS {b.cx(self.lb[i],self.la[i]);}
            window_gt_on(b,self,gt,w,None);
            b.free(gt);
        }
        short_add_dirty(b, &self.lb, &sy, true, &self.dirty);
        short_add_dirty(b, &self.la, &sx, true, &self.dirty);
        prof(b, "i.unswap");
        // I3, I4
        b.z_if(sw, bits.sw);
        super::arith::cswap_regs(b, sw, &self.x, &self.y);
        super::arith::cswap_regs(b, sw, &self.la, &self.lb);
        super::arith::cswap_regs(b, sw, &sx, &sy);
        b.cx(sw, self.par);
        // Finished Y is not normalized; active post-unswap sY must be <4.
        b.free(sy.pop().unwrap());
        b.free(sy.pop().unwrap());
        b.free(sy.pop().unwrap());
        prof(b, "i.swerase");
        // I5: erase sw with the forward's F9 logic
        if let Some(z0) = z0 {
            b.x(z0);
        }
        self.swap_flag_into(b, z0, sw, w);
        if let Some(z0) = z0 {
            b.x(z0);
        }
        b.free(sw);
        prof(b, "i.rows");
        // I6: u = LA + sX in LA, kt = u - (LB + sY) = mY - mX in LB; rows; r = act & (sX - sY - j_last)
        short_add_dirty(b, &self.la, &sx, false, &self.dirty);
        short_add_dirty(b, &self.lb, &sy, false, &self.dirty);
        for &q in &self.lb {
            b.x(q);
        }
        add_c(b, &self.lb, &self.la, true, false);
        let masked_rows = w.mx < NB + 1;
        if masked_rows {
            add_const_dirty(b, &self.la, UOFF, true, &self.dirty);
        }
        // (masked rows occur only on act-constant slots of the real windows; Win::full keeps the plain allocation)
        let lahi_early = masked_rows && w.act_const;
        if lahi_early {
            b.cx(self.la[LB_BITS - 1], self.la[LB_BITS - 2]);
        }
        let yb = if lahi_early { Some(self.la[LB_BITS - 2]) } else if !masked_rows && act.is_some() { Some(self.la[LB_BITS - 1]) } else { None };
        // Plain rows need no top zero source. Their sign uses the admitted u<256
        // high lane, and the sweep borrows the normalized divisor's leading one.
        let rt = if !masked_rows {
            RowTmp::alloc_y(b,false,Some(self.x[0]),Some(self.la[LB_BITS-1]))
        } else { RowTmp::alloc_y(b,true,yb,None) };
        b.begin();
        division_rows(b, self, w, &rt);
        let rows = b.end();
        b.play(&rows, false);
        prof(b, "i.sweep");
        if !masked_rows { b.x(rt.y); }
        let fin_fix = |b: &mut B, u: &GreedyFrog, undo: bool| {
            if let Some(a) = act {
                b.x(a);
                for i in 0..LB_BITS - R_BITS {
                    if undo { b.cx(a, u.lb[R_BITS + i]); }
                    b.cswap(a, u.lb[R_BITS + i], u.y[W - 1 - i]);
                    if !undo { b.cx(a, u.lb[R_BITS + i]); }
                }
                b.x(a);
            }
        };
        fin_fix(b, self, false);
        // The sweep runs on a clean 4-lane chain; its inverse runs later beside r and a1, so it is re-recorded on
        // borrowed lanes (the same function) and played inverted.
        // LB holds kt = mY - mX here (0 <= kt < 32 on every decodable shot; finished shots: 256 - bl(tB)) and the rows
        // and the sweep read only kt's low five bits: LB's top four lanes are |0>. They carry the sweep's clean chain,
        // then r and a1 until the rows are undone.
        let ch: Vec<QubitId> = self.lb[R_BITS..].to_vec();
        b.begin();
        last_row_sweep(b, self, act, w, &rt, Some(&ch));
        let sweep = b.end();
        b.play(&sweep, false);
        let r: Vec<QubitId> = self.lb[R_BITS..R_BITS + RHO_BITS].to_vec();
        let a1 = self.lb[LB_BITS - 1];
        // jl <- sX - sY - jl in place: the rotation since the last step (rho_of in greedyfrog_model). This slot's rotation
        // rho = act & ((jl mod 8) + #{8, 15, 22, 29 <= jl}) mod 8 and a1 = act & [jl < 8] (the slot was a step).
        // Temps: y and g (|0> after the sweep) and the sweep chain.
        let jl = rt.jl.clone();
        for &q in &jl {
            b.x(q);
        }
        add_c_on(b, &jl, &sx, true, false, rt.y);
        short_add_c_on(b, &jl, &sy, false, true, rt.y, &self.dirty);
        {
            for i in 0..RHO_BITS {
                act_cx(b, act, jl[i], r[i]);
            }
            let t = rt.y;
            let chain = &self.dirty[..];
            for cst in [8isize, 15, 22, 29] {
                super::mask::ge_const_dirty(b, &jl, cst, t, chain);
                for i in (0..r.len()).rev() {
                    let mut gate=act_lits(act); gate.push((t,false));
                    gate.extend(r[..i].iter().map(|&q| (q,false)));
                    and_dirty(b,&gate,r[i],chain);
                }
                super::mask::ge_const_dirty(b, &jl, cst, t, chain);
            }
            let mut lits = act_lits(act);
            lits.extend([(jl[3], true), (jl[4], true)]);
            and_dirty(b, &lits, a1, chain);
        }
        short_add_c_on(b, &jl, &sy, false, false, rt.y, &self.dirty);
        add_c_on(b, &jl, &sx, true, true, rt.y);
        for &q in &jl {
            b.x(q);
        }
        for i in 0..RHO_BITS {
            b.z_if(r[i], bits.r[i]);
        }
        b.z_if(a1, bits.a1);
        b.begin();
        last_row_sweep(b, self, act, w, &rt, None);
        let unsweep = b.end();
        b.play(&unsweep, true);
        if !masked_rows { b.x(rt.y); }
        prof(b, "i.rows_rev");
        b.play(&rows, true);
        rt.free(b);
        if lahi_early {
            b.cx(self.la[LB_BITS - 1], self.la[LB_BITS - 2]);
        }
        if masked_rows {
            add_const_dirty(b, &self.la, UOFF, false, &self.dirty);
        }
        // r and a1 leave LB's top lanes by SWAP into fresh |0> lanes
        let r2 = b.alloc_n(RHO_BITS);
        let a2 = b.alloc();
        for i in 0..RHO_BITS {
            b.swap(r[i], r2[i]);
        }
        b.swap(a1, a2);
        let (r, a1) = (r2, a2);
        fin_fix(b, self, true);
        add_c(b, &self.lb, &self.la, true, true);
        for &q in &self.lb {
            b.x(q);
        }
        short_add_dirty(b, &self.lb, &sy, true, &self.dirty);
        short_add_dirty(b, &self.la, &sx, true, &self.dirty);
        prof(b, "i.denorm");
        denorm_bottom_active(b, &self.y, &sy, &self.dirty, act);
        denorm_bottom(b, &self.x, &sx, &self.dirty);
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
            b.cx(d, self.x[0]);
            let x0 = self.x[0];
            let (t, s) = cof_ladder(self, w, x0);
            let src = cof_src(self, &m, w);
            masked_pass(b, &t, &s, src, &m, true, Some(a1), None);
            b.cx(d, self.x[0]);
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
        act_cx(b, act, self.x[W - 1], a1);
        b.free(a1);
        if let Some(z0) = z0 {
            b.x(z0); // z0 = done flag again
            self.cnt_dec(b, z0);
            zero_into(b, &self.la, z0);
            b.free(z0);
        }
        prof(b, "end");
    }
}

/// While z0 holds act (= !done), XOR !act into the counter: finished shots read all ones.
fn mark_done_inv(b: &mut B, act: Option<QubitId>, v: &[QubitId]) {
    let Some(act) = act else { return };
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
        for (i, &q) in u.dirty.iter().enumerate() {
            set(q, dirty_bit(shot, i));
        }
    }

    /// the random contents the tests load into the borrowed lanes
    fn dirty_bit(shot: usize, lane: usize) -> bool {
        let h = (shot as u64 + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ (lane as u64 + 7).wrapping_mul(0xc2b2_ae3d_27d4_eb4f);
        (h ^ (h >> 29)) & 1 == 1
    }

    fn check_dirty<R: sha3::digest::XofReader>(sim: &Simulator<'_, R>, u: &GreedyFrog, shots: usize) {
        for s in 0..shots {
            for (i, &q) in u.dirty.iter().enumerate() {
                assert_eq!((sim.qubits[q.0 as usize] >> s) & 1 == 1, dirty_bit(s, i), "shot {s}: borrowed lane {i} not restored");
            }
        }
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

    /// and_dirty on every literal count 1..=8 with random negations: out flips iff the AND holds, every control and
    /// borrowed lane comes back unchanged (64 random shots per count, 4 rounds).
    #[test]
    fn greedyfrog_and_dirty_exact() {
        let mut rng = Rng(0xd1d1_7777_0000_1111);
        for n in 1..=8usize {
            for round in 0..4 {
                let mut b = B::new();
                let c = b.alloc_n(n);
                let out = b.alloc();
                let d = b.alloc_n(n.saturating_sub(2));
                let neg: Vec<bool> = (0..n).map(|_| rng.next() & 1 == 1).collect();
                let lits: Vec<(QubitId, bool)> = c.iter().zip(&neg).map(|(&q, &g)| (q, g)).collect();
                and_dirty(&mut b, &lits, out, &d);
                let mut h = sha3::Shake256::default();
                h.update(b"greedyfrog-and-dirty");
                h.update(&[n as u8, round as u8]);
                let mut xof = h.finalize_xof();
                let mut sim = Simulator::new(b.width() as usize, 64, &mut xof);
                let init: Vec<u64> = (0..b.width()).map(|_| rng.next()).collect();
                for (q, &v) in init.iter().enumerate() {
                    sim.qubits[q] = v;
                }
                sim.apply_iter(b.ops.iter());
                let mut want = init[out.0 as usize];
                let mut all = !0u64;
                for (i, &q) in c.iter().enumerate() {
                    all &= if neg[i] { !init[q.0 as usize] } else { init[q.0 as usize] };
                }
                want ^= all;
                assert_eq!(sim.qubits[out.0 as usize], want, "n {n} round {round}: wrong AND");
                for &q in c.iter().chain(&d) {
                    assert_eq!(sim.qubits[q.0 as usize], init[q.0 as usize], "n {n} round {round}: lane not restored");
                }
                assert_eq!(sim.phase, 0);
            }
        }
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
            check_dirty(&sim, &u, 64);
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
        for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par)).chain(&u.dirty) {
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
            check_dirty(&sim, &u, 64);
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
            for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par)).chain(&u.dirty) {
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
                check_dirty(&sim, &u, 64);
                for (sh, st) in states.iter().enumerate() {
                    let mut want = st.clone();
                    want.fwd();
                    assert_eq!(read(&sim, &u, sh), want, "slot {slot} round {round} shot {sh}: forward mismatch");
                }
                sim.apply_iter(b.ops[mid..].iter());
                check_dirty(&sim, &u, 64);
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
        for q in u.x.iter().chain(&u.y).chain(&u.la).chain(&u.lb).chain(&u.cnt).chain(std::iter::once(&u.par)).chain(&u.dirty) {
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
        check_dirty(&sim, &u, 64);
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
        check_dirty(&sim, &u, 64);
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
