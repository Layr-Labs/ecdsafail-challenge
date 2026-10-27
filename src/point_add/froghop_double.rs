//! froghop-double: bit-serial 4-phase extended Euclid on exact-packed registers (W = 258), two hops per Euclid step,
//! with lean bookkeeping (quotient bits in V's gap, 6-bit offset boundary, 3-bit phase code).
//!
//! D and V each hold a value (LSB at lane 0, growing up) and a cofactor (LSB at lane W-1, growing down). V is
//! rotated up by pi relative to D. One shared boundary register b (bits of the current dividend during AL, of the
//! divisor afterwards; stored as b - 1 in 8 bits) gives every per-shot mask; ladders mask only inside classical
//! per-slot windows.
//!
//! Slot order: S0 frozen counter; S2 value ladder P1 (mask [pi <= lane <= b + [DV] pi]); S3 turn: probe, b update,
//! probe erase; S4 DV push / DV0 bit 0, AL->DV and DV0->CO moves; S1 CO pop (shots that were CO at slot start);
//! S5 RT0 swap, RT0->AL / DONE; S6 cofactor ladder P2 (COEF, mask lane >= b + pi); S7 CO->RT; S8 discriminator
//! ladder P3; S9 rotation and pi update.
//!
//! Scratch: one pool of POOL_D qubits, all |0> between slots, handed out per step (`Pl`).

use super::arith::{and_lits, cswap_regs, rot2_up, ttk_add};
use super::builder::{B, G};
use super::mask::{mc_xor, mcx_dirty, mdown, mdown_t, mdown_tl, mup, mup_t, onehot_scan, top_a, top_carry, Lad, Mscr, Src};
use crate::circuit::{BitId, QubitId, NO_QUBIT};

pub const WD: usize = 258;
/// pi is stored as h = pi >> 1 (PIB bits); pi's low bit is classical per slot: pi moves by exactly +-1 on every
/// slot for every shot and pi = 1 at slot 0, so pi is odd at the start of even slots
pub const PIB: usize = 4;
/// Lane FHD-789 (L1-8 joint code): 4 depth lanes. h and depth share the code space of the 8 lanes pi + dep:
/// normal shots (depth <= 15) store H = h (<= 11) and Dd = depth; exception shots (DV / CO with depth 16..23, so
/// h <= 3 on every on-model shot) store H = 12 + h and Dd = depth - 8 (Dd3 = 1, so [depth == 0 / 1 / <= 1] stay exact
/// on Dd). Resting basis: pi lanes (H0, H1, G = H2 ^ H3, H3), dep lanes (Dd0..Dd3). Shots with a quotient of >= 24
/// bits (pi >= 24 somewhere) collide and leave the model: the measured error trade of this row.
pub const DEPB: usize = 4;
/// Lane FHD-789: stored (pi lanes, dep lanes) of a shot with h = pi >> 1 and stack depth d (resting basis)
pub fn l18_encode(h: u64, d: u64) -> (u64, u64) {
    let (hh, dd) = if d >= 16 { (12 + h, d - 8) } else { (h, d) };
    let (hh, dd) = (hh & 15, dd & 15);
    let g = ((hh >> 2) ^ (hh >> 3)) & 1;
    ((hh & 3) | (g << 2) | ((hh >> 3) << 3), dd)
}
/// b (1..=256) is stored as the offset u = (b - 1) - base(sigma) mod 2^BB, base a per-slot classical constant
pub const BB: usize = 6;
pub const CNTB: usize = 8;
/// Lane FHD-SHIFT: with the L1-8 code (4 depth lanes) and the par qubit the traversal is 790 + POOL_D wide, so a row
/// at Q runs POOL_D = Q - 790 (one pool lane more than the 5-depth-lane tree at the same Q). The products stay at 790.
pub const POOL_D: usize = 3;
/// Development override (BW_POOL_D); inert when the environment is empty, as the grader builds.
pub fn pool_d() -> usize {
    std::env::var("BW_POOL_D").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(POOL_D)
}
/// Lane FHD-LEFT (PLAN-T), pool 0 only: no swap-parity qubit. The parity lives in a free gap lane chosen per phase
/// (AL: V-frame b; DV: V-frame b + max(k, 1); CO: D lane b + max(k, 1) - 1; RT: D lane b; DONE: V-frame 1, k = the
/// current quotient's length - 1) and is moved at the turn (M1), at DV0 -> CO (M2) and at the CO -> RT marker (M3,
/// which also flips it: one marker and one swap per Euclid step). `BW_PARV=0` restores the par qubit (development A/B
/// only; the graded build has an empty environment).
pub const PARV: bool = false;
pub fn parv() -> bool {
    std::env::var("BW_PARV").map(|v| v != "0").unwrap_or(PARV) && pool_d() == 0
}
/// Lane A4: the three ladders run as masked Takahashi-Tani-Kunihiro ripples (no carry wire, `mask::mup_t`), the
/// only way the traversal fits a 1-qubit pool. Always on below a 2-qubit pool; `A4_TTK` forces it at any pool
/// (development A/B only: the graded build runs in an empty environment).
/// Masked TTK ladders up to a 6-qubit pool, the parent's Cuccaro ladders above (lane G1: with the measured flags
/// Cuccaro is the cheaper form at pools 7..12). BW_CUCCARO=1 / BW_TTK=1 force either form (development A/B only).
pub fn ttk_on() -> bool {
    if std::env::var_os("BW_CUCCARO").is_some() {
        return false;
    }
    if std::env::var_os("BW_TTK").is_some() {
        return true;
    }
    pool_d() <= 6
}
/// Lane G1: measured flags. The forward traversal X-measures a flag (Hmr into a fresh receipt bit) where the plain
/// slot erases it by recomputation; the inverse traversal, which regenerates the flag anyway (it plays the plain
/// erase inverted), repairs the phase (-1)^(receipt * flag) right after the regeneration. Exact: no new
/// approximation. `BW_GHOST=0` restores the plain traversal (development A/B only; the graded build has an empty
/// environment).
pub fn ghost_on() -> bool {
    std::env::var("BW_GHOST").map(|v| v != "0").unwrap_or(true)
}
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ghost {
    Plain,
    /// forward traversal: measure, record the receipt
    Fwd,
    /// slot recorded for the inverse traversal: phase repair under the forward receipt
    Inv,
}
/// receipt sites per traversal slot: 0 S8 CO -> RT marker, 1 S3 probe dl, 2 SC gate, 3 S4 turn tt, 4 S5 rt0,
/// 5 S4 push gate upq, 6 S4 dv0, 7 S3 gate g. Site 8 (no forward receipt): in the inverse traversal the probe dl
/// is uncomputed by an X measurement plus its phase oracle under the fresh outcome (the probe scan with CZ in
/// place of its CCX writes, executed only where the outcome is 1).
pub const NRC: usize = 8;
/// lane G1 site 8: the inverse slot's probe uncompute, cut out of the slot recording
struct D1 {
    cut: usize,
    free: Vec<QubitId>,
    dl: QubitId,
    g: QubitId,
    u: Vec<QubitId>,
    cc: Vec<QubitId>,
    lo: usize,
    hi: usize,
    off: isize,
    vref: Vec<QubitId>,
    /// gated_scan0 form (every decoder level XOR-held in cc); otherwise gated_scan with clean levels
    held: bool,
}
/// Development ablation (BW_GHOST_MASK, a bit per site); inert in an empty environment (every site on).
pub fn site_on(k: usize) -> bool {
    std::env::var("BW_GHOST_MASK").ok().and_then(|v| u64::from_str_radix(v.trim(), 16).ok()).map_or(true, |m| (m >> k) & 1 == 1)
}
thread_local! { pub static STEP: std::cell::Cell<&'static str> = std::cell::Cell::new(""); }
/// Lane A4b negative controls (unit tests only): `A4B_MUT=<name>` breaks one pool-0 construction so the traversal
/// tests can show they detect it. Outside `cfg(test)` this is a constant false: the graded build reads no environment.
#[cfg(test)]
fn mutant(k: &str) -> bool {
    std::env::var("A4B_MUT").map_or(false, |v| v == k)
}
#[cfg(not(test))]
#[inline(always)]
fn mutant(_k: &str) -> bool {
    false
}
/// P3 compares only lanes within this depth below the lowest shot boundary of the slot
pub const P3DEPTH: usize = 20;

/// Toffoli of a recording played once forward and once inverted (AND compute = 1, its measured uncompute = 0)
fn rec_cost(r: &[G]) -> u64 {
    r.iter().map(|g| match g { G::Ccx(..) => 2, G::AndC(..) | G::AndU(..) => 1, _ => 0 }).sum()
}

#[derive(Clone)]
pub struct LayDouble {
    pub w: usize,
    pub s: usize,
    /// per slot: Lv jw p1lo lc p2hi pb0 pb1 pe0 pe1 sc0 sc1
    pub rows: Vec<[usize; 11]>,
    /// per slot: base of the offset boundary register (non-increasing, 0 from before the first DONE)
    pub base: Vec<usize>,
    pub smax: usize,
}

impl LayDouble {
    pub fn from_text(txt: &str, smax: usize) -> LayDouble {
        let mut lines = txt.lines();
        let hdr: Vec<usize> = lines.next().unwrap().split_whitespace().map(|t| t.parse().unwrap()).collect();
        let mut base = vec![];
        let rows: Vec<[usize; 11]> = lines
            .filter(|l| !l.trim().is_empty())
            .map(|l| {
                let v: Vec<usize> = l.split_whitespace().map(|t| t.parse().unwrap()).collect();
                let (s0, s1) = if v.len() >= 11 { (v[9], v[10]) } else { (0, hdr[0]) };
                base.push(if v.len() >= 12 { v[11] } else { 0 });
                [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], s0, s1]
            })
            .collect();
        assert_eq!(rows.len(), hdr[1]);
        LayDouble { w: hdr[0], s: hdr[1], rows, base, smax }
    }
}

/// Scratch hand-out for one slot (LIFO). Every qubit goes back |0>. `dirty`: borrowed qubits (any state, restored)
/// for multi-controlled gates when the pool is short.
struct Pl {
    free: Vec<QubitId>,
    pub low: usize,
    dirty: Vec<QubitId>,
}

impl Pl {
    fn new(pool: &[QubitId], dirty: &[QubitId]) -> Pl {
        let mut free = pool.to_vec();
        free.reverse();
        let low = free.len();
        Pl { free, low, dirty: dirty.to_vec() }
    }
    fn get(&mut self) -> QubitId {
        let q = match self.free.pop() { Some(q) => q, None => panic!("froghop-double scratch pool exhausted in {}", STEP.with(|c| c.get())) };
        self.low = self.low.min(self.free.len());
        q
    }
    fn get_n(&mut self, n: usize) -> Vec<QubitId> {
        (0..n).map(|_| self.get()).collect()
    }
    fn put(&mut self, q: QubitId) {
        debug_assert!(!self.free.contains(&q));
        self.free.push(q);
    }
    fn put_n(&mut self, qs: &[QubitId]) {
        for &q in qs.iter().rev() {
            self.put(q);
        }
    }
    /// claim specific (currently free) qubits again
    fn take(&mut self, qs: &[QubitId]) {
        for q in qs {
            let i = self.free.iter().position(|x| x == q).expect("take of a busy scratch qubit");
            self.free.remove(i);
        }
        self.low = self.low.min(self.free.len());
    }
}

/// t += (ctl ? k0 + 2 h : 0) mod 2^n, n = len(t) = len(h) + 1, k0 a classical bit: `ttk_add` with the addend's bit 0
/// the constant k0 (its two bit-0 carry Toffolis become CNOTs or vanish, its bit-0 write an X / CNOT or nothing)
fn ttk_add_k0(b: &mut B, k0: bool, h: &[QubitId], t: &[QubitId], ctl: Option<QubitId>, flag: Option<(QubitId, QubitId)>) {
    let n = t.len();
    assert_eq!(h.len() + 1, n);
    assert!(n >= 2);
    let a = |i: usize| h[i - 1]; // i >= 1
    for i in 1..n {
        b.cx(a(i), t[i]);
    }
    if let Some((k, _)) = flag {
        match ctl {
            Some(c) => b.ccx(c, a(n - 1), k),
            None => b.cx(a(n - 1), k),
        }
    }
    for i in (1..n - 1).rev() {
        b.cx(a(i), a(i + 1));
    }
    if k0 {
        b.cx(t[0], a(1));
    }
    for i in 1..n - 1 {
        b.ccx(t[i], a(i), a(i + 1));
    }
    if let Some((k, d)) = flag {
        match ctl {
            Some(c) => {
                b.ccx(a(n - 1), d, k);
                b.ccx(c, t[n - 1], d);
                b.ccx(a(n - 1), d, k);
                b.ccx(c, t[n - 1], d);
            }
            None => b.ccx(t[n - 1], a(n - 1), k),
        }
    }
    for i in (1..n).rev() {
        match ctl {
            Some(c) => b.ccx(c, a(i), t[i]),
            None => b.cx(a(i), t[i]),
        }
        if i >= 2 {
            b.ccx(t[i - 1], a(i - 1), a(i));
        } else if k0 {
            b.cx(t[0], a(1));
        }
    }
    for i in 1..n - 1 {
        b.cx(a(i), a(i + 1));
    }
    if k0 {
        match ctl {
            Some(c) => b.cx(c, t[0]),
            None => b.x(t[0]),
        }
    }
    for i in 1..n {
        b.cx(a(i), t[i]);
    }
}

/// target ^= AND of literals, chained through as many free pool qubits as help, the rest as a dirty-borrowed MCX
fn xand(b: &mut B, pl: &mut Pl, lits: &[(QubitId, bool)], target: QubitId) {
    let k = pl.free.len().min(lits.len().saturating_sub(2));
    let temps = pl.get_n(k);
    let dirty = std::mem::take(&mut pl.dirty);
    mc_xor(b, lits, target, &temps, &dirty);
    pl.dirty = dirty;
    pl.put_n(&temps);
}

/// out ^= AND of literals (qubit, negated?), transient chain from the pool (n >= 2). `undo`: measurement-uncompute
/// (out must hold exactly that AND). Falls back to `xand` when the pool cannot hold the chain.
fn and_into(b: &mut B, pl: &mut Pl, lits: &[(QubitId, bool)], out: QubitId, undo: bool) {
    let n = lits.len();
    assert!(n >= 2);
    let (q, neg) = lits[n - 1];
    if n == 2 {
        let (p, ng) = lits[0];
        if ng {
            b.x(p);
        }
        if neg {
            b.x(q);
        }
        if undo { b.and_u(p, q, out) } else { b.and_c(p, q, out) }
        if neg {
            b.x(q);
        }
        if ng {
            b.x(p);
        }
        return;
    }
    if pl.free.len() < n - 2 {
        xand(b, pl, lits, out);
        return;
    }
    let m = pl.get();
    let anc = pl.get_n(n.saturating_sub(3));
    let r = and_lits(b, &lits[..n - 1], m, &anc);
    b.play(&r, false);
    if neg {
        b.x(q);
    }
    if undo { b.and_u(m, q, out) } else { b.and_c(m, q, out) }
    if neg {
        b.x(q);
    }
    b.play(&r, true);
    pl.put_n(&anc);
    pl.put(m);
}

/// bits += ctrl with the pool's free qubits as carry chain (n - 2 suffice: the top carry is a Toffoli), any top bits
/// beyond the chain as dirty-borrowed MCX
fn incp(b: &mut B, pl: &mut Pl, ctrl: QubitId, bits: &[QubitId]) {
    let n = bits.len();
    if n == 0 {
        return;
    }
    let l = pl.free.len().min(n.saturating_sub(2));
    let anc = pl.get_n(l);
    let mut prev = ctrl;
    for i in 1..=l {
        b.and_c(prev, bits[i - 1], anc[i - 1]);
        prev = anc[i - 1];
    }
    for i in (l + 1..n).rev() {
        let mut lits = vec![(prev, false)];
        lits.extend(bits[l..i].iter().map(|&q| (q, false)));
        mc_xor(b, &lits, bits[i], &[], &pl.dirty);
    }
    for i in (1..=l).rev() {
        b.cx(anc[i - 1], bits[i]);
        let p = if i == 1 { ctrl } else { anc[i - 2] };
        b.and_u(p, bits[i - 1], anc[i - 1]);
    }
    b.cx(ctrl, bits[0]);
    pl.put_n(&anc);
}

fn decp(b: &mut B, pl: &mut Pl, ctrl: QubitId, bits: &[QubitId]) {
    for &q in bits {
        b.x(q);
    }
    incp(b, pl, ctrl, bits);
    for &q in bits {
        b.x(q);
    }
}

#[derive(Clone, Copy)]
enum GC {
    Lit(usize),
    Q(QubitId),
}

struct GLevel {
    q: QubitId,
    xor: bool,
    a: GC,
    b: GC,
    /// deepest literal index the level depends on
    d: usize,
}

/// For j in [lo, hi): per(b, j, o) with o = g & [u == j + off] in a clean qubit. Top decoder levels (ANDs of u's
/// top bits) are XOR-held in `cc`, qubits known |0> whenever g = 1 (garbage elsewhere, restored); g enters the first
/// clean level, so every clean level is exact for every shot.
fn gated_scan(b: &mut B, pl: &mut Pl, u: &[QubitId], g: QubitId, cc: &[QubitId], lo: usize, hi: usize, off: isize,
              mut per: impl FnMut(&mut B, usize, QubitId)) {
    let n = u.len();
    let avail = pl.free.len();
    let kc = if n <= avail { 0 } else { n - avail };
    assert!(kc <= cc.len() && kc < n, "gated_scan: pool too small");
    let clean = pl.get_n(n - kc);
    let mut lv: Vec<GLevel> = vec![];
    if kc == 0 {
        lv.push(GLevel { q: clean[0], xor: false, a: GC::Q(g), b: GC::Lit(0), d: 0 });
        for k in 1..n {
            lv.push(GLevel { q: clean[k], xor: false, a: GC::Q(clean[k - 1]), b: GC::Lit(k), d: k });
        }
    } else {
        lv.push(GLevel { q: cc[0], xor: true, a: GC::Lit(0), b: GC::Lit(1), d: 1 });
        for c in 1..kc {
            lv.push(GLevel { q: cc[c], xor: true, a: GC::Q(cc[c - 1]), b: GC::Lit(c + 1), d: c + 1 });
        }
        lv.push(GLevel { q: clean[0], xor: false, a: GC::Q(cc[kc - 1]), b: GC::Q(g), d: kc });
        for k in 1..n - kc {
            lv.push(GLevel { q: clean[k], xor: false, a: GC::Q(clean[k - 1]), b: GC::Lit(kc + k), d: kc + k });
        }
    }
    let apply = |b: &mut B, l: &GLevel, j: usize, undo: bool| {
        let get = |c: GC| match c {
            GC::Lit(i) => (u[n - 1 - i], (j >> (n - 1 - i)) & 1 == 0),
            GC::Q(q) => (q, false),
        };
        let (qa, na) = get(l.a);
        let (qb, nb) = get(l.b);
        if na {
            b.x(qa);
        }
        if nb {
            b.x(qb);
        }
        if l.xor {
            b.ccx(qa, qb, l.q)
        } else if undo {
            b.and_u(qa, qb, l.q)
        } else {
            b.and_c(qa, qb, l.q)
        }
        if nb {
            b.x(qb);
        }
        if na {
            b.x(qa);
        }
    };
    let mut cur: Option<usize> = None;
    for j in lo..hi {
        let val = j as isize + off;
        if val < 0 || val as usize >= (1usize << n) {
            continue;
        }
        let val = val as usize;
        let first = match cur {
            None => 0,
            Some(c) if c == val => n,
            Some(c) => n - 1 - (usize::BITS - 1 - (c ^ val).leading_zeros()) as usize,
        };
        if let Some(c) = cur {
            // a refreshed level whose only changing input is a literal (the other input unchanged) is updated in
            // place: A & !L = (A & L) ^ A, one CX from A instead of an uncompute + recompute
            let bit = |i: usize, j: usize| (j >> (n - 1 - i)) & 1;
            let refreshed = |q: QubitId| lv.iter().any(|m| m.q == q && m.d >= first);
            let stable = |x: GC| match x { GC::Lit(i) => bit(i, c) == bit(i, val), GC::Q(q) => !refreshed(q) };
            let flips = |x: GC| match x { GC::Lit(i) => bit(i, c) != bit(i, val), GC::Q(_) => false };
            let cxin = |l: &GLevel| -> Option<GC> {
                if stable(l.a) && flips(l.b) {
                    Some(l.a)
                } else if stable(l.b) && flips(l.a) {
                    Some(l.b)
                } else {
                    None
                }
            };
            for l in lv.iter().rev() {
                if l.d >= first && cxin(l).is_none() {
                    apply(b, l, c, true);
                }
            }
            for l in lv.iter() {
                if l.d >= first {
                    match cxin(l) {
                        Some(x) => {
                            let (q, ng) = match x { GC::Lit(i) => (u[n - 1 - i], bit(i, val) == 0), GC::Q(q) => (q, false) };
                            if ng {
                                b.x(q);
                            }
                            b.cx(q, l.q);
                            if ng {
                                b.x(q);
                            }
                        }
                        None => apply(b, l, val, false),
                    }
                }
            }
        } else {
            for l in lv.iter() {
                apply(b, l, val, false);
            }
        }
        cur = Some(val);
        per(b, j, lv.last().unwrap().q);
    }
    if let Some(c) = cur {
        for l in lv.iter().rev() {
            apply(b, l, c, true);
        }
    }
    pl.put_n(&clean);
}

/// bits += AND(lits) (mod 2^n): bit i flips where lits and bits 0..i are all 1, top bit first
fn inc_lits(b: &mut B, pl: &mut Pl, lits: &[(QubitId, bool)], bits: &[QubitId]) {
    for i in (0..bits.len()).rev() {
        let mut l = lits.to_vec();
        l.extend(bits[..i].iter().map(|&q| (q, false)));
        xand(b, pl, &l, bits[i]);
    }
}

/// bits -= AND(lits) (mod 2^n)
fn dec_lits(b: &mut B, pl: &mut Pl, lits: &[(QubitId, bool)], bits: &[QubitId]) {
    for &q in bits {
        b.x(q);
    }
    inc_lits(b, pl, lits, bits);
    for &q in bits {
        b.x(q);
    }
}

/// bits += 1 (unconditional): the upper lanes take bit 0 as their carry, then bit 0 flips
fn inc_uncond(b: &mut B, pl: &mut Pl, bits: &[QubitId]) {
    if bits.len() > 1 {
        incp(b, pl, bits[0], &bits[1..]);
    }
    b.x(bits[0]);
}

/// target ^= CO & !A & !(B & e) with A = AND(negpi) (pi == 0), B = AND(negdep) (depth == 0), e an optional extra
/// literal: the XOR of the four AND terms CO, CO A, CO B e, CO A B e
fn po_terms(b: &mut B, pl: &mut Pl, target: QubitId, co: &[(QubitId, bool)], negpi: Option<&[(QubitId, bool)]>,
            negdep: &[(QubitId, bool)], e: Option<(QubitId, bool)>) {
    let mut cb = co.to_vec();
    cb.extend_from_slice(negdep);
    if let Some(x) = e {
        cb.push(x);
    }
    xand(b, pl, co, target);
    xand(b, pl, &cb, target);
    // A = [pi == 0] is classically 0 on even slots (None)
    if let Some(np) = negpi {
        let mut ca = co.to_vec();
        ca.extend_from_slice(np);
        let mut cab = ca.clone();
        cab.extend_from_slice(&cb[co.len()..]);
        xand(b, pl, &ca, target);
        xand(b, pl, &cab, target);
    }
}

/// z0 = [pi == 0] in a pool qubit, or None where it is classically 0 (pi odd)
thread_local! { static Z0C: std::cell::Cell<Option<QubitId>> = std::cell::Cell::new(None); }
/// [pi == 0] is held from S4 to the end of S7 on odd slots when the scratch pool has at least Z0_MIN qubits
const Z0_MIN: usize = 8;
fn z0_hold(pool: usize) -> bool {
    pool >= Z0_MIN
}
fn z0_get(b: &mut B, pl: &mut Pl, npi: &Option<Vec<(QubitId, bool)>>) -> Option<QubitId> {
    if npi.is_some() {
        if let Some(z) = Z0C.with(|c| c.get()) {
            return Some(z);
        }
    }
    npi.as_ref().map(|np| {
        let z = pl.get();
        and_into(b, pl, np, z, false);
        z
    })
}

fn z0_put(b: &mut B, pl: &mut Pl, npi: &Option<Vec<(QubitId, bool)>>, z0: Option<QubitId>) {
    if z0.is_some() && z0 == Z0C.with(|c| c.get()) {
        return;
    }
    if let Some(z) = z0 {
        and_into(b, pl, npi.as_ref().unwrap(), z, true);
        pl.put(z);
    }
}

/// base + [!z0] (the literal is always true where z0 is classically 0)
fn with_nz0(base: &[(QubitId, bool)], z0: Option<QubitId>) -> Vec<(QubitId, bool)> {
    let mut l = base.to_vec();
    if let Some(z) = z0 {
        l.push((z, true));
    }
    l
}

/// Lane FHD-LEFT: swap a <-> t under the AND of `lits` (CX, multi-controlled X on borrowed dirty lanes, CX)
fn fredkin_l(b: &mut B, lits: &[(QubitId, bool)], a: QubitId, t: QubitId, dirty: &[QubitId]) {
    b.cx(t, a);
    let mut l = lits.to_vec();
    l.push((a, false));
    mc_xor(b, &l, t, &[], dirty);
    b.cx(t, a);
}

/// Lane FHD-LEFT: `gated_scan0` with one decoder level fewer (cc.len() >= u.len() - 2): the levels decode u's top
/// n - 1 bits and the low bit enters `per` as an extra literal, so c & lit & g = g & [u == j + off]
fn gated_scan0x(b: &mut B, u: &[QubitId], g: QubitId, cc: &[QubitId], lo: usize, hi: usize, off: isize,
                mut per: impl FnMut(&mut B, usize, QubitId, QubitId, (QubitId, bool))) {
    let nf = u.len();
    let uh = &u[1..];
    let n = uh.len();
    assert!(n >= 2 && cc.len() >= n - 1);
    let apply = |b: &mut B, c: usize, j: usize| {
        let lit = |i: usize| (uh[n - 1 - i], (j >> (n - 1 - i)) & 1 == 0);
        let (qa, na) = if c == 0 { lit(0) } else { (cc[c - 1], false) };
        let (qb, nb) = lit(c + 1);
        if na {
            b.x(qa);
        }
        if nb {
            b.x(qb);
        }
        b.ccx(qa, qb, cc[c]);
        if nb {
            b.x(qb);
        }
        if na {
            b.x(qa);
        }
    };
    let mut cur: Option<usize> = None;
    for j in lo..hi {
        let full = j as isize + off;
        if full < 0 || full as usize >= (1usize << nf) {
            continue;
        }
        let low = (full as usize) & 1;
        let val = (full as usize) >> 1;
        // incremental refresh as in gated_scan0 (a level whose only changing input is a literal: one CX)
        let first = match cur {
            None => 0,
            Some(c) if c == val => n,
            Some(c) => n - 1 - (usize::BITS - 1 - (c ^ val).leading_zeros()) as usize,
        };
        if let Some(c) = cur {
            let bit = |i: usize, j: usize| (j >> (n - 1 - i)) & 1;
            let lit = |i: usize| (uh[n - 1 - i], bit(i, val) == 0);
            let cxin = |l: usize| -> Option<(QubitId, bool)> {
                let a_stable = if l == 0 { bit(0, c) == bit(0, val) } else { l < first };
                let a_flips = l == 0 && bit(0, c) != bit(0, val);
                let b_flips = bit(l + 1, c) != bit(l + 1, val);
                if a_stable && b_flips {
                    Some(if l == 0 { lit(0) } else { (cc[l - 1], false) })
                } else if a_flips && !b_flips {
                    Some(lit(1))
                } else {
                    None
                }
            };
            for l in (0..n - 1).rev() {
                if l + 1 >= first && cxin(l).is_none() {
                    apply(b, l, c);
                }
            }
            for l in 0..n - 1 {
                if l + 1 >= first {
                    match cxin(l) {
                        Some((q, ng)) => {
                            if ng {
                                b.x(q);
                            }
                            b.cx(q, cc[l]);
                            if ng {
                                b.x(q);
                            }
                        }
                        None => apply(b, l, val),
                    }
                }
            }
        } else {
            for l in 0..n - 1 {
                apply(b, l, val);
            }
        }
        cur = Some(val);
        per(b, j, cc[n - 2], g, (u[0], low == 0));
    }
    if let Some(c) = cur {
        for l in (0..n - 1).rev() {
            apply(b, l, c);
        }
    }
}

/// For j in [lo, hi): per(b, j, c, g) where c & g = g & [u == j + off]. Every decoder level is XOR-held in `cc`
/// (len >= u.len() - 1), qubits known |0> whenever g = 1 (garbage elsewhere, restored), so c = [u == j + off]
/// exactly when g = 1; the caller folds g into its own multi-controlled gate. No clean qubit.
fn gated_scan0(b: &mut B, u: &[QubitId], g: QubitId, cc: &[QubitId], lo: usize, hi: usize, off: isize,
               mut per: impl FnMut(&mut B, usize, QubitId, QubitId)) {
    let n = u.len();
    assert!(n >= 2 && cc.len() >= n - 1);
    // level c (0..n-1): cc[c] ^= (c == 0 ? lit0 : cc[c-1]) & lit_{c+1}; depends on literals 0..=c+1
    let apply = |b: &mut B, c: usize, j: usize| {
        let lit = |i: usize| (u[n - 1 - i], (j >> (n - 1 - i)) & 1 == 0);
        let (qa, na) = if c == 0 { lit(0) } else { (cc[c - 1], false) };
        let (qb, nb) = lit(c + 1);
        if na {
            b.x(qa);
        }
        if nb {
            b.x(qb);
        }
        b.ccx(qa, qb, cc[c]);
        if nb {
            b.x(qb);
        }
        if na {
            b.x(qa);
        }
    };
    let mut cur: Option<usize> = None;
    for j in lo..hi {
        let val = j as isize + off;
        if val < 0 || val as usize >= (1usize << n) {
            continue;
        }
        let val = val as usize;
        // first literal index whose value changes
        let first = match cur {
            None => 0,
            Some(c) if c == val => n,
            Some(c) => n - 1 - (usize::BITS - 1 - (c ^ val).leading_zeros()) as usize,
        };
        if let Some(c) = cur {
            // level l = (a & lit_{l+1}) with a = lit_0 (l = 0) or cc[l-1] (refreshed iff l >= first): when only one
            // input is a flipping literal and the other is unchanged, A & !L = (A & L) ^ A is one CX from A
            let bit = |i: usize, j: usize| (j >> (n - 1 - i)) & 1;
            let lit = |i: usize| (u[n - 1 - i], bit(i, val) == 0);
            let cxin = |l: usize| -> Option<(QubitId, bool)> {
                let a_stable = if l == 0 { bit(0, c) == bit(0, val) } else { l < first };
                let a_flips = l == 0 && bit(0, c) != bit(0, val);
                let b_flips = bit(l + 1, c) != bit(l + 1, val);
                if a_stable && b_flips {
                    Some(if l == 0 { lit(0) } else { (cc[l - 1], false) })
                } else if a_flips && !b_flips {
                    Some(lit(1))
                } else {
                    None
                }
            };
            for l in (0..n - 1).rev() {
                if l + 1 >= first && cxin(l).is_none() {
                    apply(b, l, c);
                }
            }
            for l in 0..n - 1 {
                if l + 1 >= first {
                    match cxin(l) {
                        Some((q, ng)) => {
                            if ng {
                                b.x(q);
                            }
                            b.cx(q, cc[l]);
                            if ng {
                                b.x(q);
                            }
                        }
                        None => apply(b, l, val),
                    }
                }
            }
        } else {
            for l in 0..n - 1 {
                apply(b, l, val);
            }
        }
        cur = Some(val);
        per(b, j, cc[n - 2], g);
    }
    if let Some(c) = cur {
        for l in (0..n - 1).rev() {
            apply(b, l, c);
        }
    }
}

/// Lane A4b E2 (S2, P1): AL 100 -> 001 (swap p0, p2 where p1 = 0), then CO 110 -> 100 (p1 ^= p0 & !p2). DV 010
/// and RT / DONE 000 are fixed points. `dec` plays the inverse (the same two involutions in reverse order).
fn e2_code(b: &mut B, p0: QubitId, p1: QubitId, p2: QubitId, dec: bool) {
    let sw = |b: &mut B| {
        b.cx(p2, p0);
        b.x(p1);
        b.ccx(p1, p0, p2);
        b.x(p1);
        b.cx(p2, p0);
    };
    let fl = |b: &mut B| {
        b.x(p2);
        b.ccx(p0, p2, p1);
        b.x(p2);
    };
    if dec {
        fl(b);
        sw(b);
    } else {
        sw(b);
        fl(b);
    }
}

pub struct FhDouble {
    pub d: Vec<QubitId>,
    pub v: Vec<QubitId>,
    /// h = pi >> 1 (pi's low bit is the classical slot parity `pk`)
    pub pi: Vec<QubitId>,
    /// pi odd at the start of the current slot (sigma even)
    pub pk: bool,
    /// phase code p0 p1 p2: AL 001 (p0), DV 010 (p1), CO 011, RT 000, DONE 100 (p2); p0 = AL|CO = rotate up,
    /// p1 = DV|CO
    pub p0: QubitId,
    pub p1: QubitId,
    pub p2: QubitId,
    /// quotient-bit stack depth (counts the never-stored top bit c_k); the bits live in V's gap
    pub dep: Vec<QubitId>,
    /// b - 1
    pub bq: Vec<QubitId>,
    /// swap parity (starts at whatever the caller put there, e.g. the reflection bit)
    pub par: QubitId,
    pub pool: Vec<QubitId>,
    /// borrowed qubits (the idle passenger register): any state, always restored
    pub dirty: Vec<QubitId>,
    pub marks: Vec<(&'static str, usize)>,
    pub peaks: std::collections::BTreeMap<&'static str, usize>,
    pub cur_step: &'static str,
    /// lane G1: measured-flag mode of the slot being emitted, its receipts, and the forward traversal's receipts
    pub ghost: Ghost,
    pub rc: [Option<BitId>; NRC],
    pub rc_used: [bool; NRC],
    pub rcs: Vec<[Option<BitId>; NRC]>,
    d1: Option<D1>,
    /// lane FHD-LEFT: PLAN-T (no par qubit; the parity lives in a gap lane)
    pub parv: bool,
}

impl FhDouble {
    pub fn alloc(b: &mut B, d: Vec<QubitId>, v: Vec<QubitId>, lay: &LayDouble, par: QubitId, dirty: Vec<QubitId>) -> FhDouble {
        let mut q = || b.alloc();
        let (p0, p1, p2) = (q(), q(), q());
        let pi = b.alloc_n(PIB);
        let dep = b.alloc_n(DEPB);
        let bq = b.alloc_n(BB);
        let pool = b.alloc_n(pool_d());
        FhDouble { d, v, pi, pk: true, p0, p1, p2, dep, bq, par, pool, dirty, marks: vec![], peaks: Default::default(), cur_step: "S0",
                   ghost: Ghost::Plain, rc: [None; NRC], rc_used: [false; NRC], rcs: vec![], d1: None, parv: parv() }
    }

    /// every qubit the traversal allocated (not D, V or par)
    pub fn all_meta(&self) -> Vec<QubitId> {
        let mut v = self.pool.clone();
        v.extend(&self.pi);
        v.extend([self.p0, self.p1, self.p2]);
        v.extend(&self.dep);
        v.extend(&self.bq);
        v
    }

    /// lane G1: a fresh receipt for flag site k of this forward slot
    fn rc_fwd(&mut self, b: &mut B, k: usize) -> BitId {
        assert_eq!(self.ghost, Ghost::Fwd);
        assert!(self.rc[k].is_none(), "receipt {k} written twice in one slot");
        let r = b.fresh_bits(1)[0];
        self.rc[k] = Some(r);
        r
    }
    /// lane G1: the forward receipt of flag site k (inverse slot recording)
    fn rc_inv(&mut self, k: usize) -> BitId {
        assert_eq!(self.ghost, Ghost::Inv);
        assert!(!self.rc_used[k], "receipt {k} read twice in one slot");
        self.rc_used[k] = true;
        self.rc[k].expect("inverse slot needs a receipt its forward slot did not write")
    }

    /// lane G1, before the erase of flag q (q holds exactly the value the erase recomputes). Forward: X-measure q
    /// into receipt k and return true (the caller skips the erase). Inverse recording: the phase repair in source
    /// order before the erase, so the inverse playback applies it right after the erase has regenerated q.
    fn ghost_pre(&mut self, b: &mut B, k: usize, q: QubitId) -> bool {
        if !site_on(k) {
            return false;
        }
        match self.ghost {
            Ghost::Fwd => {
                let r = self.rc_fwd(b, k);
                b.hmr_to(q, r);
                true
            }
            Ghost::Inv => {
                let r = self.rc_inv(k);
                b.z_if(q, r);
                false
            }
            Ghost::Plain => false,
        }
    }

    /// DONE counter: D lanes holding p's top bits (all 1 while a shot is DONE, D = (1, p)); bit j = lane ^ 1
    pub fn cnt_lanes(&self) -> Vec<QubitId> {
        (0..CNTB).map(|j| self.d[WD - 256 + j]).collect()
    }

    /// Initial state: D = (R = p, cd = 1), V = (rv = x' already in V lanes [1, 257), cv = 0), b = 256, pi = 1, AL.
    pub fn init(&mut self, b: &mut B, lay: &LayDouble) {
        let w = WD;
        let pp = super::refmodel_double::p();
        for i in 0..256 {
            if pp.bit(i) {
                b.x(self.d[i]);
            }
        }
        b.x(self.d[w - 1]);
        let u0 = (255 - lay.base[0]) & ((1 << BB) - 1); // b - 1 = 255
        for (i, &q) in self.bq.iter().enumerate() {
            if (u0 >> i) & 1 == 1 {
                b.x(q);
            }
        }
        // pi = 1: h = 0, low bit classical
        b.x(self.p0); // AL
    }

    /// bq += pi (sub = false) or bq -= pi (sub = true), mod 2^BB, everywhere (g = None) or where g = 1.
    /// `inverse` plays the exact inverse. Scratch is transient.
    fn bq_pi(&self, b: &mut B, _pl: &mut Pl, g: Option<QubitId>, sub: bool, inverse: bool) {
        // pi = pk + 2 h: the TTK ripple with addend bit 0 the classical pk
        let t = self.bq.clone();
        let d = self.dirty[0];
        b.begin();
        // lane FHD-789: adds pk + 2 H (H = h + 12 E): exception shots get +24, corrected by the callers that read it
        self.h_plain(b);
        if sub {
            for &q in &t {
                b.x(q);
            }
        }
        ttk_add_k0(b, self.pk, &self.pi, &t[..BB - 1], g, Some((t[BB - 1], d)));
        if sub {
            for &q in &t {
                b.x(q);
            }
        }
        self.h_plain(b);
        let rec = b.end();
        b.play(&rec, inverse);
    }

    fn bq_add(&self, b: &mut B, pl: &mut Pl, a: &[QubitId], g: Option<QubitId>, sub: bool, inverse: bool) {
        let t = self.bq.clone();
        self.reg_add(b, pl, &t, a, g, sub, inverse);
    }

    /// t += a (sub = false) or t -= a, a = PIB-bit register (pi or dep); mod 2^len(t); g as in bq_pi.
    fn reg_add(&self, b: &mut B, _pl: &mut Pl, t: &[QubitId], a: &[QubitId], g: Option<QubitId>, sub: bool,
               inverse: bool) {
        let na = a.len();
        assert_eq!(t.len(), na + 1);
        // ancilla-free ripple on the low PIB lanes; its carry out is XORed into the top lane (t mod 2^(PIB + 1));
        // the flag's helper is a borrowed passenger qubit
        let d = self.dirty[0];
        b.begin();
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        ttk_add(b, a, &t[..na], g, Some((t[na], d)));
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        let rec = b.end();
        b.play(&rec, inverse);
    }

    /// bq += c (classical, mod 2^BB), as one increment per set bit of c
    fn u_add_const(&self, b: &mut B, pl: &mut Pl, c: usize) {
        let c = c & ((1 << BB) - 1);
        if c == 0 {
            return;
        }
        for i in 0..BB {
            if (c >> i) & 1 == 1 {
                let bits = self.bq[i..].to_vec();
                inc_uncond(b, pl, &bits);
            }
        }
    }

    /// u -= po with po = CO & !z0 & [depth != 0] (a popping CO shot). With three free qubits po is computed through
    /// z0 and nz and erased in place; otherwise u -= CO - CO A - CO B + CO A B (A = [pi == 0], B = [depth == 0];
    /// neither involves u) as four literal-controlled steps, no clean qubit
    fn po_dec_u(&self, b: &mut B, pl: &mut Pl, lit_co: &[(QubitId, bool)], npi: &Option<Vec<(QubitId, bool)>>,
                negdep: &[(QubitId, bool)]) {
        if pl.free.len() >= 3 {
            let z0 = z0_get(b, pl, npi);
            let nz = pl.get();
            and_into(b, pl, negdep, nz, false);
            let mut lpo = with_nz0(lit_co, z0);
            lpo.push((nz, true));
            let po = pl.get();
            and_into(b, pl, &lpo, po, false);
            decp(b, pl, po, &self.bq);
            and_into(b, pl, &lpo, po, true);
            pl.put(po);
            and_into(b, pl, negdep, nz, true);
            pl.put(nz);
            z0_put(b, pl, npi, z0);
            return;
        }
        let bq = self.bq.clone();
        let co = lit_co.to_vec();
        let mut cb = co.clone();
        cb.extend_from_slice(negdep);
        dec_lits(b, pl, &co, &bq);
        if let Some(np) = npi {
            let mut ca = co.clone();
            ca.extend_from_slice(np);
            inc_lits(b, pl, &ca, &bq);
        }
        inc_lits(b, pl, &cb, &bq);
        if let Some(np) = npi {
            // lane FHD-LEFT (PARV): the CO A B term is left out, which raises the k = 0 just-converted CO shot's P2
            // boundary by one lane (its parity sits in D lane b); undone after the ladder
            if !self.parv || mutant("bias") {
                let mut cab = co.clone();
                cab.extend_from_slice(np);
                cab.extend_from_slice(negdep);
                dec_lits(b, pl, &cab, &bq);
            }
        }
    }

    fn negdep(&self) -> Vec<(QubitId, bool)> {
        self.dep.iter().map(|&q| (q, true)).collect()
    }

    /// lane FHD-789: G -> H2 (plain h basis, H = h + 12 E) and back; one CX, self-inverse
    fn h_plain(&self, b: &mut B) {
        b.cx(self.pi[3], self.pi[2]);
    }
    /// lane FHD-789: dep3 ^= H3. Then (Dd0, Dd1, Dd2, dep3, H3) is a 5-bit counter equal to the true depth on every
    /// on-model shot with h < 8 (depth + 24 when h >= 8), and 15 -> 16 lands on the exception code. Self-inverse
    fn dep_x(&self, b: &mut B) {
        b.cx(self.pi[3], self.dep[3]);
    }
    /// lane FHD-789: the 5-bit depth vector of the `dep_x` basis
    fn dep5(&self) -> Vec<QubitId> {
        let mut v = self.dep.clone();
        v.push(self.pi[3]);
        v
    }
    /// lane FHD-789: [pi == 0] (odd slots) = !H0 & !H1 & !G, exact on every on-model shot (exceptions: H = 1100)
    fn npi_lits(&self) -> Vec<(QubitId, bool)> {
        if mutant("z04") {
            return self.pi.iter().map(|&q| (q, true)).collect();
        }
        self.pi[..3].iter().map(|&q| (q, true)).collect()
    }
    /// lane FHD-789: the exception detector E = H3 & H2 = H3 & !G (resting basis)
    fn e_lits(&self) -> Vec<(QubitId, bool)> {
        vec![(self.pi[3], false), (self.pi[2], true)]
    }
    /// lane FHD-789: bq += c AND(lits) mod 2^BB, c a multiple of 8 (an increment of bq[3 + i..] per set bit of c / 8)
    fn bq_corr(&self, b: &mut B, pl: &mut Pl, c: isize, lits: &[(QubitId, bool)]) {
        assert_eq!(c.rem_euclid(8), 0);
        let m = (c.rem_euclid(1 << BB) as usize) >> 3;
        for i in 0..BB - 3 {
            if (m >> i) & 1 == 1 {
                let bits = self.bq[3 + i..].to_vec();
                inc_lits(b, pl, lits, &bits);
            }
        }
    }
    /// lane FHD-789: t += the 5-bit depth vector (`dep_x` basis; = depth + 24 [h >= 8]); `inverse` subtracts
    fn add_dep5(&self, b: &mut B, pl: &mut Pl, t: &[QubitId], inverse: bool) {
        self.dep_x(b);
        let d5 = self.dep5();
        self.reg_add(b, pl, t, &d5, None, false, inverse);
        self.dep_x(b);
    }

    /// S6 deferred depth decrement for po = CO & !z0 & depth != 0 (pre) and po's erase from the post state, with
    /// `ct` the literal [cd << pi > cv'] (P2's top carry), or !m before the ladder (lane A4: for every CO shot the
    /// COEF erase invariant gives ct = !m, m the popped bit, and the ladder reads neither depth nor po)
    #[allow(clippy::too_many_arguments)]
    fn s6_depth_dec(&self, b: &mut B, pl: &mut Pl, npi: &Option<Vec<(QubitId, bool)>>, negdep: &[(QubitId, bool)],
                    lit_co: &[(QubitId, bool)], dep: &[QubitId], ct: (QubitId, bool)) {
        let (p0, p1) = (self.p0, self.p1);
        let negdep = negdep.to_vec();
        let lit_co = lit_co.to_vec();
        let npi = npi.clone();
        let dep = dep.to_vec();
        let pl = pl;
        if pl.free.len() >= 4 {
            // deferred depth decrement for po = CO & !z0 & depth != 0 (pre)
            let z0 = z0_get(b, pl, &npi);
            let po = pl.get();
            {
                let dz = pl.get();
                and_into(b, pl, &negdep, dz, false);
                let mut l = with_nz0(&[(p0, false), (p1, false)], z0);
                l.push((dz, true));
                and_into(b, pl, &l, po, false);
                and_into(b, pl, &negdep, dz, true);
                pl.put(dz);
            }
            // lane FHD-SHIFT: depth -= 1 on the 5-bit vector of the dep_x basis (as the pool-0 form)
            let _ = &dep;
            self.dep_x(b);
            let d5 = if mutant("p6x") { self.dep.clone() } else { self.dep5() };
            decp(b, pl, po, &d5);
            self.dep_x(b);
            // erase po = CO & !z0 & !([depth == 0] & ct) from the post state
            {
                let dz = pl.get();
                and_into(b, pl, &negdep, dz, false);
                let h = pl.get();
                if ct.1 { b.x(ct.0); }
                b.and_c(dz, ct.0, h);
                if ct.1 { b.x(ct.0); }
                let mut l = with_nz0(&[(p0, false), (p1, false)], z0);
                l.push((h, true));
                and_into(b, pl, &l, po, true);
                if ct.1 { b.x(ct.0); }
                b.and_u(dz, ct.0, h);
                if ct.1 { b.x(ct.0); }
                pl.put(h);
                and_into(b, pl, &negdep, dz, true);
                pl.put(dz);
            }
            pl.put(po);
            z0_put(b, pl, &npi, z0);
        } else if pl.free.len() >= 1 {
            // deferred depth decrement for po = CO & !z0 & depth != 0 (pre), po as the XOR of four AND terms
            let po = pl.get();
            po_terms(b, pl, po, &lit_co, npi.as_deref(), &negdep, None);
            // lane FHD-SHIFT: depth -= 1 on the 5-bit vector of the dep_x basis (as the pool-0 form)
            let _ = &dep;
            self.dep_x(b);
            let d5 = if mutant("p6x") { self.dep.clone() } else { self.dep5() };
            decp(b, pl, po, &d5);
            self.dep_x(b);
            // erase po = CO & !z0 & !([depth == 0] & ct) from the post state
            po_terms(b, pl, po, &lit_co, npi.as_deref(), &negdep, Some(ct));
            pl.put(po);
        } else {
            // deferred depth decrement for po = CO & !z0 & depth != 0 (pre). Lane FHD-789 (4 depth lanes: a wrap to
            // 2^DEPB - 1 = 15 would collide with a reachable depth): first the CO !A shots at depth 0 go to depth 1,
            // flagged by ct & [Dd1..3 == 0] (a CO !A shot at depth <= 1 has ct = [depth == 0]; the flag does not read
            // Dd0, so Dd0 ^= flag is a valid gate; (depth 1, ct = 1) is unreachable), then depth -= CO !A on the 5-bit
            // vector of the dep_x basis (no wrap: every decremented shot now has depth >= 1)
            let _ = dep;
            let d123: Vec<(QubitId, bool)> = self.dep[1..].iter().map(|&q| (q, true)).collect();
            let mut t1 = lit_co.to_vec();
            t1.push(ct);
            t1.extend(d123.iter().cloned());
            let s6f = mutant("s6f");
            if !s6f {
                xand(b, pl, &t1, self.dep[0]);
            }
            if let Some(np) = npi.as_ref().filter(|_| !s6f) {
                let mut t2 = lit_co.to_vec();
                t2.extend(np.iter().cloned());
                t2.push(ct);
                t2.extend(d123.iter().cloned());
                xand(b, pl, &t2, self.dep[0]);
            }
            self.dep_x(b);
            let d5 = self.dep5();
            dec_lits(b, pl, &lit_co, &d5);
            if let Some(np) = &npi {
                let mut ca = lit_co.to_vec();
                ca.extend(np.iter().cloned());
                inc_lits(b, pl, &ca, &d5);
            }
            self.dep_x(b);
            let _ = &negdep;
        }
    }

    /// Lane A4b E3 (S3 entry, standard encoding): CO 110:d -> 001:d, then the non-turning AL 100:0 -> 000:2, so that
    /// p0 = AL & tt exactly (turning AL 100:8, lane FHD-789). Uses only that p2 = 0 on CO and AL shots here, AL depth is 0 (dep3
    /// the turn bit) and 000:2 is unused (RT 000:0, DONE parked 000:1, DV 01x). `dec` plays the inverse.
    fn e3_code(&self, b: &mut B, dec: bool) {
        let (p0, p1, p2) = (self.p0, self.p1, self.p2);
        let dp = self.dep.clone();
        let dirty = self.dirty.clone();
        let mut gs: Vec<Box<dyn Fn(&mut B)>> = vec![];
        // CO 110 -> 111 -> 101 -> 001
        gs.push(Box::new(move |b: &mut B| b.ccx(p0, p1, p2)));
        gs.push(Box::new(move |b: &mut B| b.ccx(p0, p2, p1)));
        gs.push(Box::new(move |b: &mut B| { b.x(p1); b.ccx(p2, p1, p0); b.x(p1); }));
        // AL 100:0 -> 100:2 -> 000:2 (the turning AL has the turn bit dep3 = 1; lane FHD-789: 4 depth lanes)
        let d = dp.clone();
        let m3 = mutant("e3");
        gs.push(Box::new(move |b: &mut B| if !m3 { b.x(d[3]); b.ccx(p0, d[3], d[1]); b.x(d[3]); }));
        let d = dp.clone();
        gs.push(Box::new(move |b: &mut B| {
            let l = [(p1, true), (p2, true), (d[1], false), (d[0], true), (d[2], true), (d[3], true)];
            mc_xor(b, &l, p0, &[], &dirty);
        }));
        if dec {
            for g in gs.iter().rev() {
                g(b);
            }
        } else {
            for g in gs.iter() {
                g(b);
            }
        }
    }

    /// Lane A4b E6 (S6 ladder entry, standard encoding): AL 100:0 -> 100:2 -> 000:2, then CO 11m -> 10m. Uses that AL
    /// depth is 0, 000:2 is unused (RT 000:0, DONE parked 000:1, DV 010) and CO is the only class with p0 = p1 = 1.
    fn e6_code(&self, b: &mut B, dec: bool) {
        let (p0, p1, p2) = (self.p0, self.p1, self.p2);
        let d = self.dep.clone();
        let dirty = self.dirty.clone();
        let g1 = |b: &mut B| { b.x(p1); b.ccx(p0, p1, d[1]); b.x(p1); };
        let g2 = |b: &mut B| {
            let l = [(p1, true), (p2, true), (d[1], false), (d[0], true), (d[2], true), (d[3], true)];
            mc_xor(b, &l, p0, &[], &dirty);
        };
        let g3 = |b: &mut B| b.cx(p0, p1);
        let m6 = mutant("e6");
        if dec {
            g3(b);
            if !m6 {
                g2(b);
                g1(b);
            }
        } else {
            if !m6 {
                g1(b);
                g2(b);
            }
            g3(b);
        }
    }

    /// Lane A4b E8 (S8 ladder entry, standard encoding): AL 100:0 -> 100:2, then the basis (p0^p1, p1^p2, p2) the flip
    /// lives in. There the marked CO shot (111) and RT (000) have p0 = 0 (the running mask) and are exactly the shots
    /// with p1 = dep0 = dep1 = 0 (AL now has dep1, DONE parked dep0, DV and CO p1 = 1).
    fn e8_code(&self, b: &mut B, dec: bool) {
        let (p0, p1, p2) = (self.p0, self.p1, self.p2);
        let d1 = self.dep[1];
        let g1 = |b: &mut B| { b.x(p1); b.ccx(p0, p1, d1); b.x(p1); };
        if dec {
            b.cx(p2, p1);
            b.cx(p1, p0);
            g1(b);
        } else {
            g1(b);
            b.cx(p1, p0);
            b.cx(p2, p1);
        }
    }

    pub fn slot(&mut self, b: &mut B, lay: &LayDouble, sigma: usize) {
        let w = WD;
        let row = lay.rows[sigma];
        let (lv, jw, p1lo, lc, p2hi, pb0, pb1, pe0, pe1, sc0, sc1) =
            (row[0], row[1], row[2], row[3], row[4], row[5], row[6].min(w), row[7], row[8].min(w), row[9], row[10].min(w));
        let base = lay.base[sigma] as isize;
        let next_base = if sigma + 1 < lay.s { lay.base[sigma + 1] as isize } else { 0 };
        assert!(next_base <= base);
        let mut pl = Pl::new(&self.pool, &self.dirty);
        let (p0, p1, p2) = (self.p0, self.p1, self.p2);
        let lit_al = [(p0, false), (p1, true)];
        let lit_dv = [(p1, false), (p0, true)];
        let lit_co = [(p0, false), (p1, false)];
        let negdep = self.negdep();
        // pi = pk + 2 h with pk = [sigma even] classical: [pi == 0] is 0 on even slots (npi None), [h == 0] on odd
        self.pk = sigma % 2 == 0;
        let pk = self.pk;
        // lane FHD-789: [pi == 0] = !H0 & !H1 & !G (3 literals, exact on exception shots too)
        let npi: Option<Vec<(QubitId, bool)>> = if pk { None } else { Some(self.npi_lits()) };
        let cnt: Vec<QubitId> = self.cnt_lanes();

        // S0 frozen counter
        self.marks.push(("S0", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S0"; STEP.with(|c| c.set("S0")); }
        {
            for &q in &cnt {
                b.x(q);
            }
            incp(b, &mut pl, p2, &cnt);
            for &q in &cnt {
                b.x(q);
            }
        }

        // DONE parking (S2 .. S8 end): DONE shots move p2 into depth bit 0 (they have depth 0), so that p2 = m, the
        // moving DIV / COEF bit, for every DV / CO shot and 0 elsewhere (RT = 000 with dep0 = 0)
        let dep0 = self.dep[0];
        b.cx(p2, dep0);
        xand(b, &mut pl, &[(p0, true), (p1, true), (dep0, false)], p2);

        // S2 value ladder P1 over lanes [0, lv): p2 ^= DIV bit (DV shots); the AL turn bit is parked in the top depth
        // lane (AL shots have depth 0; lane FHD-789: dep3, code 8) until the AL -> DV move in S4
        self.marks.push(("S2", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S2"; STEP.with(|c| c.set("S2")); }
        let tt4 = self.dep[DEPB - 1];
        if lv > 0 {
            self.bq_pi(b, &mut pl, Some(p1), false, false); // DV (and CO, whose P1 result is unused)
            // lane FHD-789: exception shots (H = h + 12) got pi + 24
            let el = self.e_lits();
            if !mutant("c2") {
                self.bq_corr(b, &mut pl, -24, &el);
            }
            // lane A4b, no pool qubit: E2 re-encoding of the phase lanes (p2 = 0 on every shot here). AL 100 -> 001,
            // CO 110 -> 100 (DV 010, RT / DONE 000 stay): p0 = 0 on every AL and DV shot holds the running mask, p1 =
            // DV, AL = !p1 & p2, and P1's write gate DV & DIV is p1 & p2. p0 starts at 1 on CO shots, whose P1 result
            // is unused: the passes still undo each other there (no write fires)
            let p0mode = self.pool.is_empty();
            if p0mode {
                e2_code(b, p0, p1, p2, false);
            }
            // lane FHD-789: the h sources decode the plain H (restored after the down pass)
            self.h_plain(b);
            let ttk = ttk_on();
            let c0 = if ttk { NO_QUBIT } else { pl.get() };
            let mf = if p0mode { vec![p0] } else if pl.free.len() >= 2 { pl.get_n(2) } else { pl.get_n(1) };
            let tq = if p0mode { NO_QUBIT } else { mf.get(1).copied().unwrap_or(NO_QUBIT) };
            let (ldv, lal): (Vec<(QubitId, bool)>, Vec<(QubitId, bool)>) =
                if p0mode {
                    let lal = if mutant("e2") { vec![(p2, false)] } else { vec![(p1, true), (p2, false)] };
                    (vec![(p1, false)], lal)
                } else {
                    (lit_dv.to_vec(), lit_al.to_vec())
                };
            let gl: Vec<(QubitId, bool)> = if p0mode { vec![(p1, false), (p2, false)] } else { vec![(p2, false)] };
            let np = pl.free.len();
            let pp = pl.get_n(np);
            // lane FHD-789: the plain h source stops below lane 24 (h <= 11); exception DV shots (H = 12 + h, pi <= 7)
            // match the second h source (value (l + 24 - pk) / 2 at lane l in [0, 8))
            let pihi = jw.min(lv).min(24);
            let t: Vec<QubitId> = self.d[0..lv].to_vec();
            let s: Vec<QubitId> = self.v[0..lv].to_vec();
            let ms = Mscr { f: mf[0], t: tq, gf: tq, chain: pp.clone(), dirty: self.dirty.clone() };
            let (piv, bqv) = (self.pi.clone(), self.bq.clone());
            let hs = |lo: usize, hi: usize, pre: &[QubitId]| Src { lo, hi, v: piv.clone(), a: 0, d: 1, pre: pre.to_vec(), late: false, hk: Some(pk as usize) };
            let bs = |lo: usize, hi: usize, pre: &[QubitId]| Src { lo, hi, v: bqv.clone(), a: -2 - base, d: 1, pre: pre.to_vec(), late: false, hk: None };
            let overlap = p1lo < lv && pihi > p1lo;
            // decoder prefixes: shared when the two windows are disjoint; when they overlap, the cheapest (Toffoli of
            // the up and down passes) of every split at k (h gets k, b the rest) and of the windows recut at the lanes
            // where each decoder can actually be queried
            let orig = |k: usize| -> Vec<Src> {
                let (pa, pre) = if overlap { (&pp[..k], &pp[k..]) } else { (&pp[..], &pp[..]) };
                let mut v = vec![hs(0, pihi, pa)];
                if p1lo < lv { v.push(bs(p1lo, lv, pre)); }
                v
            };
            let mut cands: Vec<Vec<Src>> = vec![orig(np / 2)];
            if overlap {
                for k in 0..=np { if k != np / 2 { cands.push(orig(k)); } }
                {
                    // lanes where each decoder can be queried: h (pi = pk + 2h, h < 2^PIB) and b (offset in [0, 2^BB));
                    // the union of the windows (the masked lanes) stays [0, lv) in every candidate
                    let pku = pk as usize;
                    let hq_end = (0..pihi).rev().find(|&l| l >= pku && (l - pku) % 2 == 0 && (l - pku) / 2 < (1 << PIB)).map_or(0, |l| l + 1);
                    let bq_start = (p1lo..lv).find(|&l| { let j = l as isize - 2 - base; j >= 0 && j < (1 << BB) }).unwrap_or(lv);
                    if bq_start >= hq_end {
                        // the two decoders are never live together: cut the union at hq_end, share every prefix
                        cands.push(vec![hs(0, hq_end, &pp[..]), bs(hq_end, lv, &pp[..])]);
                    } else {
                        // live together only on [bq_start, hq_end): split there, optionally full prefixes outside
                        for k in 0..=np {
                            for sh in [false, true] {
                                for sb in [false, true] {
                                    let mut v = vec![];
                                    if sh && bq_start > 0 { v.push(hs(0, bq_start, &pp[..])); v.push(hs(bq_start, hq_end, &pp[..k])); }
                                    else { v.push(hs(0, hq_end, &pp[..k])); }
                                    if sb && lv > hq_end { v.push(bs(bq_start, hq_end, &pp[k..])); v.push(bs(hq_end, lv, &pp[..])); }
                                    else { v.push(bs(bq_start, lv, &pp[k..])); }
                                    cands.push(v);
                                }
                            }
                        }
                    }
                }
            }
            let exc = Src { lo: 0, hi: 8usize.min(lv), v: piv.clone(), a: 24, d: 1, pre: vec![], late: false, hk: Some(pk as usize) };
            for c in cands.iter_mut() {
                if !mutant("pexc") {
                    c.push(exc.clone());
                }
            }
            let mut best: Option<(u64, Vec<Src>, Vec<G>, Vec<G>)> = None;
            // TTK top: p2 ^= DV & T and tt4 ^= AL & T at the top cell (ct = A ^ T, see mask::mup_t)
            let dirty_t = self.dirty.clone();
            let top_p1 = |b: &mut B, terms: &[Vec<(QubitId, bool)>]| {
                for tm in terms {
                    let mut l = ldv.clone();
                    l.extend(tm.iter().cloned());
                    mc_xor(b, &l, p2, &[], &dirty_t);
                    let mut l = lal.clone();
                    l.extend(tm.iter().cloned());
                    mc_xor(b, &l, tt4, &[], &dirty_t);
                }
            };
            for c in cands {
                let ld = Lad { t: &t, s: &s, c0, srcs: &c, f0: false, cmpl: true, sc: &ms, keep_f: true };
                let (ru, rd) = if ttk {
                    (mup_t(b, &ld, Some(&top_p1)), mdown_tl(b, &ld, Some(&gl)))
                } else {
                    (mup(b, &ld), mdown(b, &ld, Some(p2)))
                };
                let cost = rec_cost(&ru) + rec_cost(&rd);
                if best.as_ref().map_or(true, |x| cost < x.0) {
                    best = Some((cost, c, ru, rd));
                }
            }
            let (_, srcs, ru, rd) = best.unwrap();
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: false, cmpl: true, sc: &ms, keep_f: true };
            if ttk {
                // DIV bit p2 = DV & !ct = DV ^ DV&A ^ DV&T, AL turn tt4 = AL & ct = AL&A ^ AL&T (p2 = 0 on every shot
                // here and tt4 = 0 on every AL shot); A = V[lv - 1] as it is now, T inside `ru`
                if let Some(a) = top_a(&ld) {
                    let mut l = ldv.clone();
                    l.push((a, false));
                    xand(b, &mut pl, &l, p2);
                    let mut l = lal.clone();
                    l.push((a, false));
                    xand(b, &mut pl, &l, tt4);
                }
                b.play(&ru, false);
                xand(b, &mut pl, &ldv, p2);
                b.play(&rd, false);
                pl.put_n(&pp);
                if !p0mode {
                    pl.put_n(&mf);
                }
            } else {
            b.play(&ru, false);
            let ct = top_carry(&ld); // [rv<<pi > R]
            // decoders are cleared at the top: lend the prefix qubits (and the cell temp) to the two flag writes
            pl.put_n(&pp);
            pl.put_n(&mf[1..]);
            let mut ldv = lit_dv.to_vec();
            ldv.push((ct, true));
            xand(b, &mut pl, &ldv, p2); // DIV bit (p2 = 0 for every shot here)
            let mut lal = lit_al.to_vec();
            lal.push((ct, false));
            xand(b, &mut pl, &lal, tt4); // AL turn
            pl.take(&mf[1..]);
            pl.take(&pp);
            b.play(&rd, false);
            pl.put_n(&pp);
            pl.put_n(&mf);
            pl.put(c0);
            }
            self.h_plain(b);
            if p0mode {
                e2_code(b, p0, p1, p2, true);
            }
            if !mutant("c2") {
                self.bq_corr(b, &mut pl, 24, &el);
            }
            self.bq_pi(b, &mut pl, Some(p1), false, true);
        }

        // S3 turn: dl = tt & !V[b]; b <- b - pi + 1 - dl; erase dl with D[b + pi - 1]. tt = AL & turn bit; the
        // decoders' top levels live in depth bits 0..3 (|0> for every AL shot)
        self.marks.push(("S3", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S3"; STEP.with(|c| c.set("S3")); }
        let ltt = [(p0, false), (p1, true), (tt4, false)];
        if pl.free.len() >= 4 {
            let dl = pl.get();
            let g = pl.get();
            let ltt = [(p0, false), (p1, true), (tt4, false)];
            xand(b, &mut pl, &ltt, g);
            // lane FHD-SHIFT: 4 depth lanes; the 4th XOR-held decoder level is p1 (|0> on every gated shot: AL = 100)
            let cc: Vec<QubitId> = if mutant("s3l") { self.dep[..DEPB - 1].to_vec() } else { vec![self.dep[0], self.dep[1], self.dep[2], p1] };
            if pb1 > pb0 {
                let vref = self.v.clone();
                let u = self.bq.clone();
                if self.ghost == Ghost::Inv && site_on(8) && b.rec_depth() == 1 {
                    // lane G1 site 8: cut here; `inverse` uncomputes dl by measurement + phase oracle
                    assert!(self.d1.is_none());
                    self.d1 = Some(D1 { cut: b.rec_len(), free: pl.free.clone(), dl, g, u, cc: cc.clone(), lo: pb0,
                                        hi: pb1, off: -1 - base, vref, held: false });
                } else {
                gated_scan(b, &mut pl, &u, g, &cc, pb0, pb1, -1 - base, |b, j, o| {
                    b.x(vref[j]);
                    b.ccx(o, vref[j], dl);
                    b.x(vref[j]);
                });
                }
            }
            self.marks.push(("S3 bupd", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S3 bupd"; STEP.with(|c| c.set("S3 bupd")); }
            {
                self.bq_pi(b, &mut pl, Some(g), true, false);
                let h = pl.get();
                b.x(dl);
                b.and_c(g, dl, h);
                b.x(dl);
                let bq = self.bq.clone();
                incp(b, &mut pl, h, &bq);
                b.x(dl);
                b.and_u(g, dl, h);
                b.x(dl);
                pl.put(h);
            }
            if pe1 > pe0 {
                self.marks.push(("S3 erase", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S3 erase"; STEP.with(|c| c.set("S3 erase")); }
                // lane G1: measured probe; the inverse traversal regenerates dl with the erase scan below
                if !self.ghost_pre(b, 1, dl) {
                self.bq_pi(b, &mut pl, None, false, false); // bq = b + pi - 1 = e
                let dref = self.d.clone();
                let u = self.bq.clone();
                gated_scan(b, &mut pl, &u, g, &cc, pe0, pe1, -base, |b, j, o| b.ccx(o, dref[j], dl));
                self.bq_pi(b, &mut pl, None, false, true);
                }
            }
            if !self.ghost_pre(b, 7, g) {
                xand(b, &mut pl, &ltt, g);
            }
            pl.put(g);
            pl.put(dl);
        } else {
            // lane A4: with one free qubit dl lives in p2, which is |0> on every AL shot here (S2's DIV write is
            // DV-gated) and is only written under g = AL & tt (its X's below come in pairs)
            // lane A4b, no pool qubit: E3 re-encoding puts g = AL & tt in p0 (CO 110 -> 001, the non-turning AL 100:0
            // -> 000:2), with p1, p2, dep0..3 still |0> on every turning AL shot
            let p0mode = self.pool.is_empty();
            if p0mode {
                self.e3_code(b, false);
                if self.parv {
                    // lane FHD-LEFT: after E3 p0 = 1 exactly on the turning AL shot (100:8 with 4 depth lanes), whose tt
                    // bit (dep3) is redundant with g = p0: clear it so dep3 is a clean temp for the parity move M1
                    b.cx(p0, tt4);
                }
            }
            let dl_own = pl.free.len() >= 2;
            let dl = if dl_own { pl.get() } else { p2 };
            let g = if p0mode { p0 } else { pl.get() };
            let ltt = [(p0, false), (p1, true), (tt4, false)];
            if !p0mode {
                xand(b, &mut pl, &ltt, g);
                // lane FHD-SHIFT: g = AL & tt exactly, so the turn bit (dep3) is redundant on the gated shots: clear it
                // there, so dep3 is |0> on every gated shot and can serve as a decoder level (restored before g's erase)
                if !mutant("s3c") {
                    b.cx(g, tt4);
                }
            } else if !self.parv && !mutant("s3c") {
                // lane FHD-SHIFT (pool 0, par qubit): the same clear under g = p0 as the PARV path's
                b.cx(p0, tt4);
            }
            // lane FHD-789: 4 depth lanes. After E3 and the tt clear the turning AL has dep0..dep3 and p1 at |0>: the probe
            // and erase scans keep 5 levels; the parity moves M1a / M1b use dep3 as the temp and 4 levels
            // (`gated_scan0x`), and M1b runs before the erase scan so dep3 is clear again there
            let mut cc: Vec<QubitId> = self.dep.clone();
            cc.push(p1);
            let cc4: Vec<QubitId> = vec![self.dep[0], self.dep[1], self.dep[2], p1];
            let dirty_s3 = self.dirty.clone();
            if pb1 > pb0 {
                let vref = self.v.clone();
                let u = self.bq.clone();
                if dl_own && self.ghost == Ghost::Inv && site_on(8) && b.rec_depth() == 1 {
                    // lane G1 site 8 (dl in its own pool qubit only)
                    assert!(self.d1.is_none());
                    self.d1 = Some(D1 { cut: b.rec_len(), free: pl.free.clone(), dl, g, u, cc: cc.clone(), lo: pb0,
                                        hi: pb1, off: -1 - base, vref, held: true });
                } else {
                gated_scan0(b, &u, g, &cc, pb0, pb1, -1 - base, |b, j, c, gg| {
                    b.x(vref[j]);
                    mcx_dirty(b, &[c, gg, vref[j]], dl, &dirty_s3);
                    b.x(vref[j]);
                });
                }
            }
            // lane FHD-LEFT M1a: the turning AL's parity, at V-frame b_A = physical b_A + pi, into the temp (dep3).
            // Window: b_A within the probe window or the P1 b window (mask end b_A + 1), pi in [1, pihi)
            let (ba_lo, ba_hi) = (pb0.min(p1lo.saturating_sub(1)), pb1.max(lv + 1));
            let pihi_s3 = jw.min(lv);
            if p0mode && self.parv {
                self.bq_pi(b, &mut pl, None, false, false); // bq = b_A + pi - 1 - base
                let vref = self.v.clone();
                let u = self.bq.clone();
                // V-frame u sits at physical (u + pi) mod W: positions past the top wrap to low lanes
                let lo = ba_lo + 1;
                let hi = (ba_hi + pihi_s3).saturating_sub(1).min(lo + w);
                if hi > lo && !mutant("m1a") {
                    gated_scan0x(b, &u, g, &cc4, lo, hi, -1 - base, |b, j, c, gg, lit| {
                        fredkin_l(b, &[(c, false), (gg, false), lit], vref[j % w], tt4, &dirty_s3);
                    });
                }
                self.bq_pi(b, &mut pl, None, false, true);
            }
            self.marks.push(("S3 bupd", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S3 bupd"; STEP.with(|c| c.set("S3 bupd")); }
            {
                self.bq_pi(b, &mut pl, Some(g), true, false);
                // bq += g & !dl: a g-controlled increment of the register (!dl, bq) adds !dl into bq and flips !dl
                b.x(dl);
                let mut r = vec![dl];
                r.extend(&self.bq);
                incp(b, &mut pl, g, &r);
                b.cx(g, dl);
                b.x(dl);
            }
            if p0mode && self.parv {
                // lane FHD-LEFT M1b: temp (dep3) -> the DV lane V-frame b' + max(k, 1), k = pi - 1, at physical
                // b' + 2 pi - 1 (pi >= 2) or b' + 2 (pi = 1): bq + 2 pi + [pi == 1] (+ base). Lane FHD-789: before the
                // erase scan (V lanes only; bq restored), so the erase keeps its 5 clean levels
                self.bq_pi(b, &mut pl, None, false, false);
                self.bq_pi(b, &mut pl, None, false, false);
                let bqr = self.bq.clone();
                let h1: Vec<(QubitId, bool)> = self.npi_lits();
                if pk {
                    inc_lits(b, &mut pl, &h1, &bqr); // pi odd: pi == 1 <=> h == 0
                }
                let vref = self.v.clone();
                let lo = ba_lo + 1;
                let hi = (ba_hi + pihi_s3).min(lo + w);
                if hi > lo && !mutant("m1b") {
                    gated_scan0x(b, &bqr, g, &cc4, lo, hi, -base, |b, j, c, gg, lit| {
                        fredkin_l(b, &[(c, false), (gg, false), lit], vref[j % w], tt4, &dirty_s3);
                    });
                }
                if pk {
                    dec_lits(b, &mut pl, &h1, &bqr);
                }
                self.bq_pi(b, &mut pl, None, false, true);
                self.bq_pi(b, &mut pl, None, false, true);
            }
            if pe1 > pe0 {
                self.marks.push(("S3 erase", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S3 erase"; STEP.with(|c| c.set("S3 erase")); }
                // lane G1: measured probe (only when dl owns a pool qubit; in p2 it shares the lane with m)
                if !(dl_own && self.ghost_pre(b, 1, dl)) {
                self.bq_pi(b, &mut pl, None, false, false); // bq = b + pi - 1 = e
                let dref = self.d.clone();
                let u = self.bq.clone();
                gated_scan0(b, &u, g, &cc, pe0, pe1, -base, |b, j, c, gg| mcx_dirty(b, &[c, gg, dref[j]], dl, &dirty_s3));
                self.bq_pi(b, &mut pl, None, false, true);
                }
            }
            if p0mode {
                // lane FHD-SHIFT: with and without PARV (dep3 is a decoder level in both)
                if self.parv || !mutant("s3c") {
                    b.cx(p0, tt4);
                }
                self.e3_code(b, true);
            } else {
                if !mutant("s3c") {
                    b.cx(g, tt4);
                }
                if !self.ghost_pre(b, 7, g) {
                    xand(b, &mut pl, &ltt, g);
                }
                pl.put(g);
            }
            if dl_own {
                pl.put(dl);
            }
        }

        // S4 DV bit bookkeeping (m = p2): the first DV slot's c_k is always 1 and never stored; depth += 1 for DV at
        // pi > 0; moves DV0 -> CO (p2 keeps DV0's bit 0 as the COEF bit) and AL -> DV (turn bit cleared)
        if npi.is_some() && z0_hold(self.pool.len()) {
            let z = z0_get(b, &mut pl, &npi);
            Z0C.with(|c| c.set(z));
        }
        self.marks.push(("S4", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S4"; STEP.with(|c| c.set("S4")); }
        if self.pool.is_empty() {
            // lane A4b, no pool qubit: every step as literal-controlled flips and increments; z0 = [pi == 0] enters as
            // the four negated h literals (odd slots; classically 0 on even slots)
            let dv = [(p1, false), (p0, true)];
            {
                // virtual c_k: p2 ^= DV & !z0 & [depth == 0]
                let mut l = dv.to_vec();
                l.extend(negdep.iter().cloned());
                xand(b, &mut pl, &l, p2);
                if let Some(np) = &npi {
                    let mut l = dv.to_vec();
                    l.extend(np.iter().cloned());
                    l.extend(negdep.iter().cloned());
                    xand(b, &mut pl, &l, p2);
                }
            }
            {
                // depth += DV & !z0 = DV - DV z0. Lane FHD-789: on the 5-bit vector of the dep_x basis (a DV shot going
                // 15 -> 16 has h <= 3 and lands on the exception code; h >= 8 shots have depth <= 7, no carry out)
                self.dep_x(b);
                let dep = if mutant("dx4") { self.dep.clone() } else { self.dep5() };
                inc_lits(b, &mut pl, &dv, &dep);
                if let Some(np) = &npi {
                    let mut lz = dv.to_vec();
                    lz.extend(np.iter().cloned());
                    dec_lits(b, &mut pl, &lz, &dep);
                }
                self.dep_x(b);
            }
            if let Some(np) = &npi {
                // DV0 -> CO: p0 ^= p1 & z0 (no CO shot has pi = 0 here, as in the pool forms)
                let mut l = vec![(p1, false)];
                l.extend(np.iter().cloned());
                xand(b, &mut pl, &l, p0);
                if self.parv && lc < w {
                    // lane FHD-LEFT M2: the just-converted CO shot (CO & z0) moves its parity from the DV lane V-frame
                    // b + max(k, 1) to the CO lane D b + max(k, 1) - 1 (pi = 0: physical V[j + 1] -> D[j]),
                    // j = b - 1 + depth + [depth == 0] (k = depth here). No clean gate: the swap (an involution) runs
                    // twice under a borrowed passenger lane z with z ^= CO & z0 in between and after. Window: j is
                    // this shot's P2 boundary lane at S6 (biased by one for k = 0), so P2's source window covers it.
                    let z = *self.dirty.last().unwrap();
                    let dirty_x: Vec<QubitId> = self.dirty[..self.dirty.len() - 1].to_vec();
                    let mut plz = Pl::new(&[], &dirty_x);
                    let bx = self.bq.clone();
                    // lane FHD-789: the gated shot has pi = 0 (h < 8), so the 5-bit depth vector is exact there
                    self.add_dep5(b, &mut pl, &bx, false);
                    inc_lits(b, &mut plz, &negdep, &bx);
                    let (dd, vv) = (self.d.clone(), self.v.clone());
                    let hi = (p2hi + 1).min(w - 1);
                    // decoder levels XOR-held in H0, H1, G and p0 ^ p1, |0> on every gated shot (pi = 0, so H is 0000 or
                    // the exception's 1100; CO has p0 = p1): on the other shots both rounds apply the same
                    // garbage-controlled swaps (z unchanged between them), which cancel
                    let hl = if mutant("m2l") { self.pi.clone() } else { vec![self.pi[0], self.pi[1], self.pi[2], p0] };
                    b.cx(p1, p0);
                    let round = |b: &mut B| {
                        if hi > lc {
                            gated_scan0x(b, &bx, z, &hl, lc, hi, -base, |b, j, c, g, lit| {
                                fredkin_l(b, &[(c, false), (g, false), lit], vv[j + 1], dd[j], &dirty_x);
                            });
                        }
                    };
                    // CO & z0 in the p0 ^= p1 basis: !p0 & p1
                    let mut lz = vec![(p0, true), (p1, false)];
                    lz.extend(np.iter().cloned());
                    round(b);
                    if !mutant("m2") {
                        xand(b, &mut plz, &lz, z);
                    }
                    round(b);
                    xand(b, &mut plz, &lz, z);
                    b.cx(p1, p0);
                    dec_lits(b, &mut plz, &negdep, &bx);
                    self.add_dep5(b, &mut pl, &bx, true);
                }
            }
            self.marks.push(("S4 aldv", b.ops.len()));
            {
                // AL -> DV as the transposition 100:8 <-> 010:0 (lane FHD-789: turn bit dep3; no DV shot has depth 0
                // here: DV at pi > 0 was just pushed, DV0 moved to CO, exception DV shots have Dd >= 8; the pool forms'
                // erase of tt from "DV, empty stack (post)" uses the same fact). Conjugated by p1 ^= p0, dep3 ^= p0 the
                // two codes differ only in p0: one 6-literal flip
                let d = self.dep.clone();
                b.cx(p0, p1);
                b.cx(p0, d[3]);
                let l = [(p1, false), (d[3], true), (p2, !mutant("s4")), (d[0], true), (d[1], true), (d[2], true)];
                xand(b, &mut pl, &l, p0);
                b.cx(p0, d[3]);
                b.cx(p0, p1);
            }
        } else if pl.free.len() >= 3 {
            {
                let z0 = z0_get(b, &mut pl, &npi);
                {
                    let nz = pl.get();
                    and_into(b, &mut pl, &negdep, nz, false);
                    let mut l = with_nz0(&[(p1, false), (p0, true)], z0);
                    l.push((nz, false));
                    xand(b, &mut pl, &l, p2); // virtual c_k
                    and_into(b, &mut pl, &negdep, nz, true);
                    pl.put(nz);
                }
                {
                    let upq = pl.get();
                    let lpush = with_nz0(&[(p1, false), (p0, true)], z0);
                    and_into(b, &mut pl, &lpush, upq, false);
                    // lane FHD-SHIFT: depth += 1 on the 5-bit vector of the dep_x basis (as the pool-0 form)
                    self.dep_x(b);
                    let dep = if mutant("p4x") { self.dep.clone() } else { self.dep5() };
                    incp(b, &mut pl, upq, &dep);
                    self.dep_x(b);
                    if !self.ghost_pre(b, 5, upq) {
                        and_into(b, &mut pl, &lpush, upq, true);
                    }
                    pl.put(upq);
                }
                if let Some(z0) = z0 {
                    let dv0 = pl.get();
                    and_into(b, &mut pl, &[(p1, false), (p0, true), (z0, false)], dv0, false);
                    b.cx(dv0, p0); // DV0 -> CO: 010 -> 011
                    if !self.ghost_pre(b, 6, dv0) {
                        and_into(b, &mut pl, &[(p1, false), (p0, false), (z0, false)], dv0, true); // = CO & z0 (post)
                    }
                    pl.put(dv0);
                }
                {
                    let tt = pl.get();
                    and_into(b, &mut pl, &ltt, tt, false);
                    b.cx(tt, p0); // AL -> DV: 001 -> 010
                    b.cx(tt, p1);
                    b.cx(tt, tt4);
                    if !self.ghost_pre(b, 3, tt) {
                        let nz = pl.get();
                        and_into(b, &mut pl, &negdep, nz, false);
                        and_into(b, &mut pl, &[(p1, false), (p0, true), (nz, false)], tt, true); // DV, empty stack (post)
                        and_into(b, &mut pl, &negdep, nz, true);
                        pl.put(nz);
                    }
                    pl.put(tt);
                }
                z0_put(b, &mut pl, &npi, z0);
            }
        } else if npi.is_some() && pl.free.len() < 2 {
            // lane A4, one free qubit on an odd slot: z0 = [pi == 0] = AND(npi) is never materialised; !z0 terms are
            // split as X ^ X z0, and z0 enters as the four negated h literals
            let np = npi.clone().unwrap();
            let dv = [(p1, false), (p0, true)];
            {
                // virtual c_k: p2 ^= DV & !z0 & [depth == 0]
                let mut l = dv.to_vec();
                l.extend(negdep.iter().cloned());
                xand(b, &mut pl, &l, p2);
                let mut l = dv.to_vec();
                l.extend(np.iter().cloned());
                l.extend(negdep.iter().cloned());
                xand(b, &mut pl, &l, p2);
            }
            {
                // depth += DV & !z0
                let upq = pl.get();
                let mut lz = dv.to_vec();
                lz.extend(np.iter().cloned());
                xand(b, &mut pl, &dv, upq);
                xand(b, &mut pl, &lz, upq);
                // lane FHD-SHIFT: depth += 1 on the 5-bit vector of the dep_x basis (as the pool-0 form)
                self.dep_x(b);
                let dep = if mutant("p4x") { self.dep.clone() } else { self.dep5() };
                incp(b, &mut pl, upq, &dep);
                self.dep_x(b);
                if !self.ghost_pre(b, 5, upq) {
                    xand(b, &mut pl, &lz, upq);
                    xand(b, &mut pl, &dv, upq);
                }
                pl.put(upq);
            }
            {
                // DV0 -> CO: p0 ^= p1 & z0 (no CO shot has pi = 0 here: the erase below the held form, CO & z0 (post),
                // relies on the same fact)
                let mut l = vec![(p1, false)];
                l.extend(np.iter().cloned());
                xand(b, &mut pl, &l, p0);
            }
            self.marks.push(("S4 aldv", b.ops.len()));
            {
                let tt = pl.get();
                and_into(b, &mut pl, &ltt, tt, false);
                b.cx(tt, p0); // AL -> DV: 001 -> 010
                b.cx(tt, p1);
                b.cx(tt, tt4);
                let mut l = vec![(p1, false), (p0, true)];
                l.extend(negdep.iter().cloned());
                if !self.ghost_pre(b, 3, tt) {
                    xand(b, &mut pl, &l, tt); // DV, empty stack (post)
                }
                pl.put(tt);
            }
        } else {
            {
                let z0 = z0_get(b, &mut pl, &npi);
                {
                    let mut l = with_nz0(&[(p1, false), (p0, true)], z0);
                    l.extend(negdep.iter().cloned());
                    xand(b, &mut pl, &l, p2); // virtual c_k
                }
                {
                    let upq = pl.get();
                    let lpush = with_nz0(&[(p1, false), (p0, true)], z0);
                    and_into(b, &mut pl, &lpush, upq, false);
                    // lane FHD-SHIFT: depth += 1 on the 5-bit vector of the dep_x basis (as the pool-0 form)
                    self.dep_x(b);
                    let dep = if mutant("p4x") { self.dep.clone() } else { self.dep5() };
                    incp(b, &mut pl, upq, &dep);
                    self.dep_x(b);
                    if !self.ghost_pre(b, 5, upq) {
                        and_into(b, &mut pl, &lpush, upq, true);
                    }
                    pl.put(upq);
                }
                if let Some(z0) = z0 {
                    let dv0 = pl.get();
                    and_into(b, &mut pl, &[(p1, false), (p0, true), (z0, false)], dv0, false);
                    b.cx(dv0, p0); // DV0 -> CO: 010 -> 011
                    if !self.ghost_pre(b, 6, dv0) {
                        and_into(b, &mut pl, &[(p1, false), (p0, false), (z0, false)], dv0, true); // = CO & z0 (post)
                    }
                    pl.put(dv0);
                }
                self.marks.push(("S4 aldv", b.ops.len()));
                {
                    let tt = pl.get();
                    and_into(b, &mut pl, &ltt, tt, false);
                    b.cx(tt, p0); // AL -> DV: 001 -> 010
                    b.cx(tt, p1);
                    b.cx(tt, tt4);
                    let mut l = vec![(p1, false), (p0, true)];
                    l.extend(negdep.iter().cloned());
                    if !self.ghost_pre(b, 3, tt) {
                        xand(b, &mut pl, &l, tt); // DV, empty stack (post)
                    }
                    pl.put(tt);
                }
                z0_put(b, &mut pl, &npi, z0);
            }
        }

        // SC stack scan: DV pushes m and CO pops into m at physical lane b + k = (b - 1) + depth + pi (DV depth
        // already incremented; CO depth is decremented only at P2's top), gated by (DV | CO) & !z0 & depth >= 2
        self.marks.push(("SC", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "SC"; STEP.with(|c| c.set("SC")); }
        if sc1 > sc0 && self.pool.is_empty() {
            // lane A4b, no pool qubit: the gate gq = p1 & !z0 & !(depth <= 1) is never held clean. The scan is a
            // one-hot sequence of controlled swaps p2 <-> V[j] (an involution per shot), so it runs twice under a
            // borrowed passenger lane z, with z ^= gq in between and after: swap^(z ^ (z ^ gq)) = swap^gq
            let z = *self.dirty.last().unwrap();
            let dirty_x: Vec<QubitId> = self.dirty[..self.dirty.len() - 1].to_vec();
            let hi: Vec<(QubitId, bool)> = self.dep[1..].iter().map(|&q| (q, true)).collect();
            let bx = self.bq.clone();
            // lane FHD-789: depth vector + plain H read depth + pi + 24 H3 (h >= 8: the depth vector's +24; exception:
            // H's +24); corrected under H3
            self.add_dep5(b, &mut pl, &bx, false);
            self.bq_pi(b, &mut pl, None, false, false);
            let h3 = [(self.pi[3], false)];
            let csc = mutant("csc");
            if !csc {
                self.bq_corr(b, &mut pl, -24, &h3);
            }
            let vref = self.v.clone();
            let round = |b: &mut B| {
                onehot_scan(b, &bx, &[], sc0, sc1, -base, |b, j, c| {
                    let mut l = c.to_vec();
                    l.push((z, false));
                    l.push((p2, false));
                    b.cx(vref[j], p2);
                    mc_xor(b, &l, vref[j], &[], &dirty_x);
                    b.cx(vref[j], p2);
                });
            };
            let mut plz = Pl::new(&[], &dirty_x);
            round(b);
            if !mutant("sc") {
                po_terms(b, &mut plz, z, &[(p1, false)], npi.as_deref(), &hi, None);
            }
            round(b);
            po_terms(b, &mut plz, z, &[(p1, false)], npi.as_deref(), &hi, None);
            if !csc {
                self.bq_corr(b, &mut pl, 24, &h3);
            }
            self.bq_pi(b, &mut pl, None, false, true);
            self.add_dep5(b, &mut pl, &bx, true);
        } else if sc1 > sc0 {
            let gq = pl.get();
            let hi: Vec<(QubitId, bool)> = self.dep[1..].iter().map(|&q| (q, true)).collect();
            // gq = p1 & !(pi == 0) & !(depth <= 1): with two free qubits an AND chain through z0 and d01, otherwise
            // the XOR of the AND terms p1, p1 A, p1 D, p1 A D
            let gate = |b: &mut B, pl: &mut Pl, undo: bool| {
                if pl.free.len() >= 2 {
                    let z0 = z0_get(b, pl, &npi);
                    let d01 = pl.get();
                    and_into(b, pl, &hi, d01, false); // [depth <= 1]
                    let mut l = with_nz0(&[(p1, false)], z0);
                    l.push((d01, true));
                    and_into(b, pl, &l, gq, undo);
                    and_into(b, pl, &hi, d01, true);
                    pl.put(d01);
                    z0_put(b, pl, &npi, z0);
                } else {
                    po_terms(b, pl, gq, &[(p1, false)], npi.as_deref(), &hi, None);
                }
            };
            gate(b, &mut pl, false);
            let bx = self.bq.clone();
            // lane FHD-SHIFT: depth vector + plain H, corrected under H3 (as the pool-0 form, lane FHD-789)
            self.add_dep5(b, &mut pl, &bx, false);
            self.bq_pi(b, &mut pl, None, false, false);
            let h3 = [(self.pi[3], false)];
            let psc = mutant("psc");
            if !psc {
                self.bq_corr(b, &mut pl, -24, &h3);
            }
            let mut bg = bx.clone();
            bg.push(gq);
            let npre = pl.free.len().min(BB);
            let pre = pl.get_n(npre);
            let vref = self.v.clone();
            let dirty = self.dirty.clone();
            onehot_scan(b, &bg, &pre, sc0, sc1, (1isize << BB) - base, |b, j, c| {
                let mut l = c.to_vec();
                l.push((p2, false));
                b.cx(vref[j], p2);
                mc_xor(b, &l, vref[j], &[], &dirty);
                b.cx(vref[j], p2);
            });
            pl.put_n(&pre);
            if !psc {
                self.bq_corr(b, &mut pl, 24, &h3);
            }
            self.bq_pi(b, &mut pl, None, false, true);
            self.add_dep5(b, &mut pl, &bx, true);
            if !self.ghost_pre(b, 2, gq) {
                gate(b, &mut pl, true);
            }
            pl.put(gq);
        }

        // S1 CO pop for shots that were CO at slot start (CO & !z0): the scan left the popped bit in m; at depth 1 the
        // virtual c_k = 1 is popped. The depth decrement is deferred to P2's top.
        self.marks.push(("S1", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S1"; STEP.with(|c| c.set("S1")); }
        if pl.free.len() >= 3 {
            {
                let z0 = z0_get(b, &mut pl, &npi);
                let lco = with_nz0(&lit_co, z0);
                let co = pl.get();
                and_into(b, &mut pl, &lco, co, false);
                let d1: Vec<(QubitId, bool)> = self.dep.iter().enumerate().map(|(i, &q)| (q, i != 0)).collect();
                let one = pl.get();
                and_into(b, &mut pl, &d1, one, false); // [depth == 1]
                b.ccx(co, one, p2); // virtual c_k
                and_into(b, &mut pl, &d1, one, true);
                pl.put(one);
                and_into(b, &mut pl, &lco, co, true);
                pl.put(co);
                z0_put(b, &mut pl, &npi, z0);
            }
        } else {
            {
                // p2 ^= CO & !(pi == 0) & [depth == 1] = CO E ^ CO A E
                let d1: Vec<(QubitId, bool)> = self.dep.iter().enumerate().map(|(i, &q)| (q, i != 0)).collect();
                let mut t1 = lit_co.to_vec();
                t1.extend(d1.iter().cloned());
                xand(b, &mut pl, &t1, p2);
                if let Some(np) = &npi {
                    let mut t2 = lit_co.to_vec();
                    t2.extend(np.iter().cloned());
                    t2.extend(d1.iter().cloned());
                    xand(b, &mut pl, &t2, p2);
                }
            }
        }

        // S5 RT0: swap; RT0 -> AL, or DONE (parked: dep0 = 1) when b == 1
        self.marks.push(("S5", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S5"; STEP.with(|c| c.set("S5")); }
        // pi = 1 at slot 0 and moves by +-1 on every shot every slot: pi == 0 (and so rt0) only on odd slots
        let negpi: Vec<(QubitId, bool)> = npi.clone().unwrap_or_default();
        if sigma % 2 == 0 {
        } else if self.pool.is_empty() {
            // lane A4b, no pool qubit. rt0 = RT & z0 = !p0 & !p1 & !dep0 & [h == 0] is never held clean: the swap of
            // D and V and the parity flip (an involution, reading none of rt0's literals) run twice under a borrowed
            // passenger lane z with z ^= rt0 in between and after
            let z = *self.dirty.last().unwrap();
            let dirty_x: Vec<QubitId> = self.dirty[..self.dirty.len() - 1].to_vec();
            let mut plz = Pl::new(&[], &dirty_x);
            let mut l5 = vec![(p0, true), (p1, true), (dep0, true)];
            l5.extend(negpi.iter().cloned());
            let (dd, vv, par) = (self.d.clone(), self.v.clone(), self.par);
            let parv = self.parv;
            let blk = |b: &mut B| {
                cswap_regs(b, z, &dd, &vv);
                if !parv {
                    b.cx(z, par);
                }
            };
            blk(b);
            xand(b, &mut plz, &l5, z);
            blk(b);
            xand(b, &mut plz, &l5, z);
            // RT0 -> AL: p0 ^= !p1 & !dep0 & z0, the transposition 000:0 <-> 100:0 at pi = 0 (no AL shot has pi = 0)
            let mut l1 = vec![(p1, true), (dep0, true)];
            l1.extend(negpi.iter().cloned());
            xand(b, &mut plz, &l1, p0);
            if base == 0 {
                // b == 1: the new AL0 shot -> DONE (parked), (p0, dep0) = (1, 0) -> (0, 1) under !p1 & z0 & [bq == 0]
                // & [cnt == 0]; conjugated by dep0 ^= p0 the two codes differ only in p0. After the swap a finishing
                // shot holds D = (1, p), so cnt == 0; no older DONE shot has cnt == 0 (the pool forms' rt0 erase uses
                // the same two facts)
                b.cx(p0, dep0);
                let mut l2 = vec![(dep0, false), (p1, true)];
                l2.extend(negpi.iter().cloned());
                l2.extend(self.bq.iter().map(|&q| (q, true)));
                if !mutant("s5") {
                    l2.extend(cnt.iter().map(|&q| (q, false)));
                }
                xand(b, &mut plz, &l2, p0);
                b.cx(p0, dep0);
            }
        } else if pl.free.len() >= 4 {
            {
                let z0 = z0_get(b, &mut pl, &npi).unwrap();
                let rt0 = pl.get();
                let l5 = [(p0, true), (p1, true), (dep0, true), (z0, false)];
                and_into(b, &mut pl, &l5, rt0, false); // RT at pi = 0
                let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&q| (q, true)).collect();
                let b1 = pl.get();
                if base == 0 {
                    and_into(b, &mut pl, &bz, b1, false); // b == 1; no shot can finish while base > 0
                }
                let dn = pl.get();
                b.and_c(rt0, b1, dn);
                cswap_regs(b, rt0, &self.d, &self.v);
                b.cx(rt0, self.par);
                b.cx(dn, dep0); // RT0 -> DONE (parked)
                b.cx(rt0, p0); // RT0 -> AL: 000 -> 001
                b.cx(dn, p0);
                b.and_u(rt0, b1, dn);
                pl.put(dn);
                if base == 0 {
                    and_into(b, &mut pl, &bz, b1, true);
                }
                pl.put(b1);
                // rt0 = (AL & z0) ^ (DONE & z0 & [cnt == 0])
                if !self.ghost_pre(b, 4, rt0) {
                    let mut lu = vec![(dep0, false)];
                    lu.extend(cnt.iter().map(|&q| (q, false)));
                    if pl.free.len() >= lu.len() {
                        // AL (p0 & !p1) and DONE (!p0 & !p1 & dep0) are disjoint: rt0 ^= z0 & !p1 & (p0 | u), u = dep0 &
                        // [cnt == 0] held on its AND chain while it is used, then the chain is measured away
                        let u = pl.get();
                        let anc = pl.get_n(lu.len() - 2);
                        let r = and_lits(b, &lu, u, &anc);
                        b.play(&r, false);
                        let v = pl.get();
                        b.x(p0);
                        b.x(u);
                        b.and_c(p0, u, v); // v = !(p0 | u)
                        b.x(u);
                        b.x(p0);
                        xand(b, &mut pl, &[(z0, false), (p1, true), (v, true)], rt0);
                        b.x(p0);
                        b.x(u);
                        b.and_u(p0, u, v);
                        b.x(u);
                        b.x(p0);
                        pl.put(v);
                        b.play(&r, true);
                        pl.put_n(&anc);
                        pl.put(u);
                    } else if pl.free.len() >= lu.len() - 1 {
                        // AL (p0 & !p1) and DONE (!p0 & !p1 & dep0) are disjoint: rt0 ^= z0 & !p1 & (p0 | u), u = dep0 & [cnt == 0]
                        let u = pl.get();
                        and_into(b, &mut pl, &lu, u, false);
                        let v = pl.get();
                        b.x(p0);
                        b.x(u);
                        b.and_c(p0, u, v); // v = !(p0 | u)
                        b.x(u);
                        b.x(p0);
                        xand(b, &mut pl, &[(z0, false), (p1, true), (v, true)], rt0);
                        b.x(p0);
                        b.x(u);
                        b.and_u(p0, u, v);
                        b.x(u);
                        b.x(p0);
                        pl.put(v);
                        and_into(b, &mut pl, &lu, u, true);
                        pl.put(u);
                    } else {
                        {
                            let mut la = lit_al.to_vec();
                            la.push((z0, false));
                            let w2 = pl.get();
                            and_into(b, &mut pl, &la, w2, false);
                            b.cx(w2, rt0);
                            and_into(b, &mut pl, &la, w2, true);
                            pl.put(w2);
                        }
                        let mut ldn = vec![(p0, true), (p1, true), (dep0, false), (z0, false)];
                        ldn.extend(cnt.iter().map(|&q| (q, false)));
                        xand(b, &mut pl, &ldn, rt0);
                    }
                }
                pl.put(rt0);
                z0_put(b, &mut pl, &npi, Some(z0));
            }
        } else {
            {
                let rt0 = pl.get();
                let mut l5 = vec![(p0, true), (p1, true), (dep0, true)];
                l5.extend(negpi.iter().cloned());
                xand(b, &mut pl, &l5, rt0); // RT at pi = 0
                // dn = rt0 & [b == 1] (no shot can finish while base > 0), used as literals
                let mut ldn1 = vec![(rt0, false)];
                ldn1.extend(self.bq.iter().map(|&q| (q, true)));
                cswap_regs(b, rt0, &self.d, &self.v);
                b.cx(rt0, self.par);
                if base == 0 {
                    xand(b, &mut pl, &ldn1, dep0); // RT0 -> DONE (parked)
                }
                b.cx(rt0, p0); // RT0 -> AL: 000 -> 001
                if base == 0 {
                    xand(b, &mut pl, &ldn1, p0);
                }
                // rt0 = (AL & z0) ^ (DONE & z0 & [cnt == 0])
                if !self.ghost_pre(b, 4, rt0) {
                    let mut la = lit_al.to_vec();
                    la.extend(negpi.iter().cloned());
                    xand(b, &mut pl, &la, rt0);
                    let mut ldn = vec![(p0, true), (p1, true), (dep0, false)];
                    ldn.extend(negpi.iter().cloned());
                    ldn.extend(cnt.iter().map(|&q| (q, false)));
                    xand(b, &mut pl, &ldn, rt0);
                }
                pl.put(rt0);
            }
        }

        // S6 cofactor ladder P2 (COEF, g = m = p2). Boundary u + pi + depth - po (po = popping CO shot, transient;
        // the depth decrement happens at P2's top), ladder lane l <-> phys W-1-l over phys [lc, W)
        self.marks.push(("S6", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S6"; STEP.with(|c| c.set("S6")); }
        self.bq_pi(b, &mut pl, None, false, false);
        let dep = self.dep.clone();
        // lane FHD-789: + depth vector, corrected under H3 as at SC (the S8 end undoes it with the post-decrement H3)
        {
            let bqv = self.bq.clone();
            self.add_dep5(b, &mut pl, &bqv, false);
            let h3 = [(self.pi[3], false)];
            if !mutant("c6") {
                self.bq_corr(b, &mut pl, -24, &h3);
            }
        }
        self.po_dec_u(b, &mut pl, &lit_co, &npi, &negdep);
        if lc < w {
            let n = w - lc;
            let ttk = ttk_on();
            if ttk {
                self.s6_depth_dec(b, &mut pl, &npi, &negdep, &lit_co, &dep, (p2, true));
            }
            self.marks.push(("S6 lad", b.ops.len()));
            // lane A4b, no pool qubit: E6 re-encoding, AL 100:0 -> 000:2 and CO 11m -> 10m (DV 010, RT 000:0, DONE
            // parked 000:1 stay): p1 = 0 on every CO shot holds the running mask, p0 = CO, and m = p2 is 0 elsewhere
            let p0mode = self.pool.is_empty();
            if p0mode {
                self.e6_code(b, false);
            }
            let lco: Vec<(QubitId, bool)> = if p0mode { vec![(p0, false)] } else { lit_co.to_vec() };
            let c0 = if ttk { NO_QUBIT } else { pl.get() };
            let mf = if p0mode { vec![p1] } else if pl.free.len() >= 2 { pl.get_n(2) } else { pl.get_n(1) };
            let tq = if p0mode { NO_QUBIT } else { mf.get(1).copied().unwrap_or(NO_QUBIT) };
            let np = pl.free.len();
            let pre = pl.get_n(np);
            let t: Vec<QubitId> = (0..n).map(|l| self.v[w - 1 - l]).collect();
            let s: Vec<QubitId> = (0..n).map(|l| self.d[w - 1 - l]).collect();
            let mut srcs = vec![];
            if p2hi > lc {
                // lane FHD-LEFT (PARV): one more lane at the top for the biased k = 0 just-converted CO boundary
                let p2top = if self.parv { (p2hi + 1).min(w) } else { p2hi };
                srcs.push(Src { lo: w - p2top, hi: w - lc, v: self.bq.clone(), a: w as isize - 1 - base, d: -1,
                                pre: pre.clone(), late: false, hk: None });
            }
            let ms = Mscr { f: mf[0], t: tq, gf: tq, chain: pre.clone(), dirty: self.dirty.clone() };
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &ms, keep_f: true };
            if ttk {
                // m ^= CO & cmp, cmp = !ct = 1 ^ A ^ T: T at the top (inside ru, played inverted), then A = D[lc]'s
                // value (restored by ru^-1) and the constant; m is not read by ru^-1
                let dirty_t = self.dirty.clone();
                let top_p2 = |b: &mut B, terms: &[Vec<(QubitId, bool)>]| {
                    for tm in terms {
                        let mut l = lco.clone();
                        l.extend(tm.iter().cloned());
                        mc_xor(b, &l, p2, &[], &dirty_t);
                    }
                };
                let ru = mup_t(b, &ld, Some(&top_p2));
                let rd = mdown_t(b, &ld, Some(p2));
                b.play(&rd, true);
                b.play(&ru, true);
                if let Some(a) = top_a(&ld) {
                    let mut l = lco.clone();
                    l.push((a, false));
                    xand(b, &mut pl, &l, p2);
                }
                xand(b, &mut pl, &lco, p2);
                pl.put_n(&pre);
                if p0mode {
                    self.e6_code(b, true);
                } else {
                    pl.put_n(&mf);
                }
            } else {
            let ru = mup(b, &ld);
            let rd = mdown(b, &ld, Some(p2));
            b.play(&rd, true);
            // decoder prefixes and the cell temp are |0> here (c0 holds a carry, f the mask): lend them out
            pl.put_n(&pre);
            pl.put_n(&mf[1..]);
            let ct = top_carry(&ld); // [cd<<pi > cv']; cmp = !ct
            // m ^= CO & cmp (a CO shot that has finished popping has ct = 1)
            xand(b, &mut pl, &[(p0, false), (p1, false), (ct, true)], p2);
            self.s6_depth_dec(b, &mut pl, &npi, &negdep, &lit_co, &dep, (ct, false));
            pl.take(&mf[1..]);
            pl.take(&pre);
            b.play(&ru, true);
            pl.put_n(&pre);
            pl.put_n(&mf);
            pl.put(c0);
            }
        }

        if self.parv {
            if let Some(np) = &npi {
                // lane FHD-LEFT: undo the P2 bias (bq -= CO & z0 & [depth == 0]; the k = 0 just-converted shot kept depth 0)
                let mut cab = lit_co.to_vec();
                cab.extend_from_slice(np);
                cab.extend_from_slice(&negdep);
                let bq = self.bq.clone();
                dec_lits(b, &mut pl, &cab, &bq);
            }
        }

        // S7 CO -> RT marker: a CO shot (pi > 0) whose stack is now empty gets p2 = 1 (011 -> 111); P3 completes the
        // move
        self.marks.push(("S7", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S7"; STEP.with(|c| c.set("S7")); }
        if pl.free.len() >= 2 {
            {
                let z0 = z0_get(b, &mut pl, &npi);
                let nz = pl.get();
                and_into(b, &mut pl, &negdep, nz, false);
                let mut l = with_nz0(&[(p0, false), (p1, false)], z0);
                l.push((nz, false));
                xand(b, &mut pl, &l, p2);
                and_into(b, &mut pl, &negdep, nz, true);
                pl.put(nz);
                z0_put(b, &mut pl, &npi, z0);
            }
        } else {
            {
                // p2 ^= CO & !(pi == 0) & [depth == 0] = CO B ^ CO A B
                let mut t1 = lit_co.to_vec();
                t1.extend(negdep.iter().cloned());
                xand(b, &mut pl, &t1, p2);
                if let Some(np) = &npi {
                    let mut t2 = lit_co.to_vec();
                    t2.extend(np.iter().cloned());
                    t2.extend(negdep.iter().cloned());
                    xand(b, &mut pl, &t2, p2);
                }
            }
            if self.parv && lc < w && p2hi > lc {
                // lane FHD-LEFT M3: p2 = [marked] exactly here (the S8 fact lane G1's pool-0 marker uses). The marked
                // shot (depth 0) moves its parity from the CO lane D b + pi - 1 = D[bq + base] (bq = b + pi - 1 - base:
                // S6's offsets are still applied) through dep3 (flipped there: one marker and one swap per Euclid
                // step) to the RT lane D b. Decoder levels in dep0, dep1, dep2, p0 ^ p2 (|0> on every marked shot).
                // Windows: the CO lane is the shot's own P2 boundary lane (P2's source window); b = that - pi + 1.
                // lane FHD-789: 4 depth lanes; the 4th level is p0 ^ p2 (the marked shot is 111, every other shot has
                // p2 = 0 here, so p0 ^= p2 touches the marked shots only)
                let m3l = mutant("m3l");
                if !m3l {
                    b.cx(p2, p0);
                }
                let cc4 = [self.dep[0], self.dep[1], self.dep[2], p0];
                let d3 = self.dep[3];
                let dd = self.d.clone();
                let dirty_m = self.dirty.clone();
                let bqm = self.bq.clone();
                let hia = (p2hi + 1).min(w);
                gated_scan0x(b, &bqm, p2, &cc4, lc, hia, -base, |b, j, c, g, lit| {
                    fredkin_l(b, &[(c, false), (g, false), lit], dd[j], d3, &dirty_m);
                });
                if !mutant("m3") {
                    b.cx(p2, d3);
                }
                self.bq_pi(b, &mut pl, None, true, false); // bq = b - 1 - base
                let pihi8 = jw.min(lv);
                let lob = (lc + 1).saturating_sub(pihi8);
                let hib = if mutant("m3b") { lob } else { hia };
                gated_scan0x(b, &bqm, p2, &cc4, lob, hib, -1 - base, |b, j, c, g, lit| {
                    fredkin_l(b, &[(c, false), (g, false), lit], dd[j], d3, &dirty_m);
                });
                self.bq_pi(b, &mut pl, None, true, true);
                if !m3l {
                    b.cx(p2, p0);
                }
            }
        }

        // S8 discriminator P3: z = [cv >= cd << (pi_pre + 1)] (= model's pi_post + 2). Marked shots (111) have
        // ct = !z = 1 and move to RT; RT shots (000, not a parked DONE) have ct = 0
        if let Some(z) = Z0C.with(|c| c.take()) {
            z0_put(b, &mut pl, &npi, Some(z));
        }
        self.marks.push(("S8", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S8"; STEP.with(|c| c.set("S8")); }
        if lc >= w {
            // degenerate (no cofactor lanes, early slots): every RT shot here is a marked one, ct = 1
            b.cx(p1, p0);
            b.cx(p2, p1);
            xand(b, &mut pl, &[(p0, true), (p1, true), (dep0, true)], p2);
            b.cx(p2, p1);
            b.cx(p1, p0);
        } else if self.ghost == Ghost::Fwd && site_on(0) {
            // lane G1: measured CO -> RT marker. On every on-model shot the ladder's ct equals the marker
            // mk = [code 111 & !dep0] (marked shots have ct = 1, RT shots ct = 0, nothing else passes the gate), so the
            // move 111 -> 000 is three mk-controlled flips and mk is X-measured. The inverse traversal regenerates the
            // marker with the ladder and repairs (-1)^(r mk) under the receipt r.
            let r = self.rc_fwd(b, 0);
            if self.pool.is_empty() {
                // lane FHD-LEFT, no pool qubit: at S8 entry p2 = [marked] exactly on every on-model shot (DV pushed m at
                // SC, CO's m was erased by P2, DONE is parked in dep0, only S7 sets p2), so the marker itself is the flag:
                // 111 -> 001 by two p2-controlled flips, then p2 is X-measured (111 -> 000), no Toffoli
                b.cx(p2, p0);
                b.cx(p2, p1);
                b.hmr_to(p2, r);
            } else {
            let mk = pl.get();
            and_into(b, &mut pl, &[(p0, false), (p1, false), (p2, false), (dep0, true)], mk, false);
            b.cx(mk, p0);
            b.cx(mk, p1);
            b.cx(mk, p2);
            b.hmr_to(mk, r);
            pl.put(mk);
            }
        } else {
            if self.ghost == Ghost::Inv && site_on(0) {
                // lane G1 repair, source order before the ladder: the inverse playback applies it after the ladder has
                // restored the marked shots' code 111; phase (-1)^(r [111 & !dep0]) only where the receipt is 1
                let r = self.rc_inv(0);
                if self.pool.is_empty() {
                    // lane FHD-LEFT, no pool qubit: p2 = [111 & !dep0] here (S8 entry), so the repair is one Z on p2
                    b.z_if(p2, r);
                } else {
                let t = pl.get();
                b.ccx_if(p0, p1, t, r);
                b.x(dep0);
                b.ccz_if(t, p2, dep0, r);
                b.x(dep0);
                b.ccx_if(p0, p1, t, r);
                pl.put(t);
                }
            }
            // truncated compare: only ladder lanes >= cut (P3DEPTH below the lowest shot boundary; lane 0 never
            // carries since cd << 1 has bit 0 = 0); highest differing lane <= 25 below a boundary in 6e7 samples
            let cut = if p2hi > lc { (w - p2hi).saturating_sub(P3DEPTH) } else { 0 }.max(1);
            let n = w - lc - cut;
            let ttk = ttk_on();
            // lane A4b, no pool qubit: E8 re-encoding (AL 100:0 -> 100:2, then the flip's basis), p0 = 0 on every
            // marked and RT shot holds the running mask; the flip's selector is !p1 & !dep0 & !dep1
            let p0mode = self.pool.is_empty();
            if p0mode {
                self.e8_code(b, false);
            }
            let c0 = if ttk { NO_QUBIT } else { pl.get() };
            let mf = if p0mode { vec![p0] } else if pl.free.len() >= 2 { pl.get_n(2) } else { pl.get_n(1) };
            let tq = if p0mode { NO_QUBIT } else { mf.get(1).copied().unwrap_or(NO_QUBIT) };
            let np = pl.free.len();
            let pre = pl.get_n(np);
            let t: Vec<QubitId> = (cut..cut + n).map(|l| self.v[w - 1 - l]).collect();
            let s: Vec<QubitId> = (cut..cut + n).map(|l| self.d[w - l]).collect();
            let mut srcs = vec![];
            if p2hi > lc {
                // late: the shot's boundary lane W - b - pi stays in the compare with T there (rv's MSB, always 1)
                // flipped to the 0 it stands for, so cd << 1 may use it (q = 1 CO->RT needs it when W = 258)
                let lo = (w - p2hi).saturating_sub(cut);
                srcs.push(Src { lo, hi: w - lc - cut, v: self.bq.clone(), a: w as isize - 1 - base - cut as isize,
                                d: -1, pre: pre.clone(), late: true, hk: None });
            }
            let ms = Mscr { f: mf[0], t: tq, gf: tq, chain: pre.clone(), dirty: self.dirty.clone() };
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &ms, keep_f: true };
            if ttk {
                // 111 <-> 000 under ct & !dep0, a q2 flip in the basis (q0, q1, q2) = (p0^p1, p1^p2, p2) under
                // L = !q0 & !q1 & !dep0; L is invariant under the flip, so ct = A ^ T splits: T at the top cell (inside
                // ru_w), A = D[w - cut - n + 1]'s value after ru^-1 restores it
                let dirty_t = self.dirty.clone();
                let dep1 = self.dep[1];
                let flip = |b: &mut B, extra: &[(QubitId, bool)]| {
                    if p0mode {
                        let mut l = vec![(p1, true), (dep0, true)];
                        if !mutant("s8") {
                            l.push((dep1, true));
                        }
                        l.extend(extra.iter().cloned());
                        mc_xor(b, &l, p2, &[], &dirty_t);
                        return;
                    }
                    b.cx(p1, p0);
                    b.cx(p2, p1);
                    let mut l = vec![(p0, true), (p1, true), (dep0, true)];
                    l.extend(extra.iter().cloned());
                    mc_xor(b, &l, p2, &[], &dirty_t);
                    b.cx(p2, p1);
                    b.cx(p1, p0);
                };
                let top_p3 = |b: &mut B, terms: &[Vec<(QubitId, bool)>]| {
                    for tm in terms {
                        flip(b, tm);
                    }
                };
                let ru_w = mup_t(b, &ld, Some(&top_p3));
                let ru_n = mup_t(b, &ld, None);
                b.play(&ru_w, false);
                b.play(&ru_n, true);
                if let Some(a) = top_a(&ld) {
                    flip(b, &[(a, false)]);
                }
                pl.put_n(&pre);
                if p0mode {
                    self.e8_code(b, true);
                } else {
                    pl.put_n(&mf);
                }
            } else {
            let ru = mup(b, &ld);
            b.play(&ru, false);
            let ct = top_carry(&ld); // [cd<<(pi+1) > cv] = !z
            pl.put_n(&pre);
            pl.put_n(&mf[1..]);
            // 111 <-> 000 gated by ct & !dep0: in the basis (p0^p1, p1^p2, p2) a p2 flip
            b.cx(p1, p0);
            b.cx(p2, p1);
            xand(b, &mut pl, &[(ct, false), (p0, true), (p1, true), (dep0, true)], p2);
            b.cx(p2, p1);
            b.cx(p1, p0);
            pl.take(&mf[1..]);
            pl.take(&pre);
            b.play(&ru, true);
            pl.put_n(&pre);
            pl.put_n(&mf);
            pl.put(c0);
            }
        }
        {
            let bqv = self.bq.clone();
            let h3 = [(self.pi[3], false)];
            if !mutant("c6") {
                self.bq_corr(b, &mut pl, 24, &h3);
            }
            self.add_dep5(b, &mut pl, &bqv, true);
        }
        let _ = &dep;
        self.bq_pi(b, &mut pl, None, false, true);
        // DONE un-parking
        xand(b, &mut pl, &[(p0, true), (p1, true), (dep0, false)], p2);
        b.cx(p2, dep0);

        // S9 rotation and pi update from the post phase
        self.marks.push(("S9", b.ops.len())); { let used = self.pool.len() - pl.low; let e = self.peaks.entry(self.cur_step).or_insert(0); *e = (*e).max(used); pl.low = pl.free.len(); self.cur_step = "S9"; STEP.with(|c| c.set("S9")); }
        let v0 = self.v[0];
        for j in 0..w - 1 {
            self.v[j] = self.v[j + 1];
        }
        self.v[w - 1] = v0;
        // up = AL | CO (post), or DONE with pi even (pi even <=> !pk, classical)
        // lane A4b, no pool qubit: up is held in p0 itself (p0 ^= p2 on odd slots; DONE 001 and AL | CO are disjoint)
        let p0mode = self.pool.is_empty();
        let upq = if p0mode { p0 } else { pl.get() };
        if !p0mode {
            b.cx(p0, upq); // AL | CO
        }
        if !pk {
            b.cx(p2, upq);
        }
        rot2_up(b, upq, &self.v);
        {
            // pi -> pi - 1 + 2 up. pi = 2h + 1 (pk): h += up. pi = 2h (!pk): h -= !up. Lane FHD-789: on the plain H
            // (an exception shot stays in H 12..15: h <= 3 before and after on every on-model shot)
            let h = self.pi.clone();
            let s9p = mutant("s9p");
            if !s9p {
                self.h_plain(b);
            }
            if pk {
                incp(b, &mut pl, upq, &h);
            } else {
                b.x(upq);
                decp(b, &mut pl, upq, &h);
                b.x(upq);
            }
            if !s9p {
                self.h_plain(b);
            }
        }
        if !pk {
            b.cx(p2, upq);
        }
        if !p0mode {
            b.cx(p0, upq);
            pl.put(upq);
        }
        // re-centre the offset register for the next slot: u += base(sigma) - base(sigma + 1)
        self.u_add_const(b, &mut pl, (base - next_base) as usize);
        {
            let used = self.pool.len() - pl.low;
            let e = self.peaks.entry(self.cur_step).or_insert(0);
            *e = (*e).max(used);
            self.cur_step = "S0"; STEP.with(|c| c.set("S0"));
        }
        assert_eq!(pl.free.len(), self.pool.len(), "scratch leak");
    }

    /// Play one inverse slot recording (lane G1: with the site 8 cut when the recording made one).
    pub fn play_inverse_slot(&mut self, b: &mut B, rec: &[G]) {
        if let Some(d) = self.d1.take() {
            // lane G1 site 8: undo the slot down to the probe, measure dl, apply (-1)^dl where the outcome is 1
            // (the probe scan with a CZ where it wrote dl), then undo the rest
            b.play(&rec[d.cut..], true);
            let r = b.fresh_bits(1)[0];
            b.hmr_to(d.dl, r);
            b.push_condition(r);
            let vref = d.vref.clone();
            if d.held {
                gated_scan0(b, &d.u, d.g, &d.cc, d.lo, d.hi, d.off, |b, j, c, gg| {
                    b.x(vref[j]);
                    b.ccz(c, gg, vref[j]);
                    b.x(vref[j]);
                });
            } else {
                let n = d.free.len();
                let mut pl = Pl { free: d.free.clone(), low: n, dirty: self.dirty.clone() };
                gated_scan(b, &mut pl, &d.u, d.g, &d.cc, d.lo, d.hi, d.off, |b, j, o| {
                    b.x(vref[j]);
                    b.cz(o, vref[j]);
                    b.x(vref[j]);
                });
                assert_eq!(pl.free, d.free, "site 8 scan scratch");
            }
            b.pop_condition();
            b.play(&rec[..d.cut], true);
        } else {
            b.play(&rec, true);
        }
    }

    pub fn forward(&mut self, b: &mut B, lay: &LayDouble) -> Vec<Vec<QubitId>> {
        let mut maps = Vec::with_capacity(lay.s);
        let ghost = ghost_on();
        assert!(self.rcs.is_empty(), "unconsumed forward receipts");
        for sigma in 0..lay.s {
            maps.push(self.v.clone());
            if ghost {
                self.ghost = Ghost::Fwd;
                self.rc = [None; NRC];
            }
            self.slot(b, lay, sigma);
            if ghost {
                self.rcs.push(self.rc);
            }
            self.ghost = Ghost::Plain;
        }
        maps
    }

    /// Exact inverse of `forward` (with its receipts: every forward measurement is repaired once, after the inverse
    /// slot regenerates the measured flag).
    pub fn inverse(&mut self, b: &mut B, lay: &LayDouble, maps: &[Vec<QubitId>]) {
        let ghost = !self.rcs.is_empty();
        if ghost {
            assert_eq!(self.rcs.len(), lay.s);
        }
        for sigma in (0..lay.s).rev() {
            self.v = maps[sigma].clone();
            if ghost {
                self.ghost = Ghost::Inv;
                self.rc = self.rcs[sigma];
                self.rc_used = [false; NRC];
            }
            b.begin();
            self.slot(b, lay, sigma);
            let rec = b.end();
            self.play_inverse_slot(b, &rec);
            if ghost {
                for k in 0..NRC {
                    assert_eq!(self.rc[k].is_some(), self.rc_used[k], "slot {sigma}: receipt {k} closure");
                }
            }
            self.ghost = Ghost::Plain;
            self.v = maps[sigma].clone();
        }
        self.rcs.clear();
    }
}
