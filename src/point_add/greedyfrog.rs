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

pub const R_BITS: usize = 5;
/// bits of a slot's renormalisation rotation rho <= RCAP = 7 (3-stage barrel)
pub const RHO_BITS: usize = 3;
/// lanes of the top-window compares (F2, F9): exact unless the two values agree on all of them (~2^-40)
/// lanes added on each side of the measured per-slot envelopes
/// slots per traversal: steps plus stall slots (200k walks: 8 need >= 257, 4 need 258)
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
    /// gf G6b: LA and LB hold value - base on this slot
    pub base: usize,
}

impl Win {
    /// No classical knowledge: every boundary anywhere (masks everywhere, all rows).
    pub fn full() -> Win {
        if lb_bits() >= 9 {
            Win { lb: (1, 256), lad: (0, 256), mxp: 0, mx: 0, k: krows(), act_const: false, base: 0 }
        } else {
            // the marker leaves no room for values at or above 2^(bits-1); lengths below 2^(bits-1) mean cofactors of
            // at least 2^(bits-1) - 1 bits, so the decode runs unmasked (masked decodes need u' >= -2^(bits-1))
            let top = (1usize << (lb_bits() - 1)) - 1;
            Win { lb: (1, top), lad: (0, top), mxp: nb() + 1, mx: nb() + 1, k: krows(), act_const: false, base: 0 }
        }
    }
}

/// slots between the last act-constant slot and the first slot where an envelope walk finished
const ACT_MARGIN: usize = 40;

/// walks behind the envelope: the active count at slot 0 (every walk is active there)

/// The traversal's windows, slot by slot.
pub fn windows() -> Vec<Win> {
    let (mut first_done, mut all_active_upto) = (usize::MAX, 0usize);
    check_knobs();
    let txt = env_text();
    let mut v = vec![];
    let mut env_walks = 0.0f64;
    let mut raw: Vec<(isize, isize, isize, isize)> = vec![];
    for line in txt.lines().filter(|l| !l.starts_with('#')) {
        let c: Vec<isize> = line.split_whitespace().map(|t| t.parse().unwrap()).collect();
        if c[0] == 0 {
            env_walks = c[1] as f64;
        }
        // s n lb_min lb_max lad_min lad_max cof_min r_max mxp_min mx_min kt_max rows_max slack_max
        let m = margin() as isize;
        let lb = ((c[2] - m).max(1) as usize, (c[3] + m).min(256) as usize);
        let lad = ((c[4] - m).max(0) as usize, (c[5] + m).min(256) as usize);
        let mxp = (c[8] - m).max(0) as usize;
        let mx = (c[9] - m).max(0) as usize;
        // rows: the big-quotient tail (P(rows > k) ~ 2^-k per step) is the same at every slot, so a slot holding a
        // fraction f of the shots active keeps the run's expected failures flat with k = KROWS - floor(log2(1/f));
        // slot 0's quotient is a single power of two
        let f = c[1] as f64 / env_walks;
        let k = if c[0] == 0 { 4 } else { (krows() as f64 - (1.0 / f).log2().floor()).clamp(kmin() as f64, krows() as f64) as usize };
        v.push(Win { lb, lad, mxp, mx, k, act_const: false, base: 0 });
        raw.push((c[2], c[3], c[4], c[5]));
        if c[1] as f64 == env_walks {
            all_active_upto = c[0] as usize;
        } else {
            first_done = first_done.min(c[0] as usize);
        }
    }
    while v.len() < nslots() {
        v.push(v.last().unwrap().clone());
    }
    let _ = all_active_upto;
    for (s, w) in v.iter_mut().enumerate() {
        w.act_const = s + ACT_MARGIN < first_done;
    }
    if lb_bits() < 9 {
        // gf G6b: base(s) = a multiple of GF_BASE_STEP below every LA and LB of the slot (this slot's and the next
        // slot's windows, one lane for d, GF_BASE_MARGIN lanes), 0 wherever a shot can be finished
        let lim = 1isize << (lb_bits() - 1);
        let (step, mb) = (base_step() as isize, base_margin() as isize);
        for s in 0..v.len() {
            let r0 = raw[s.min(raw.len() - 1)];
            let r1 = raw[(s + 1).min(raw.len() - 1)];
            let lo = r0.0.min(r0.2).min(r1.0).min(r1.2) - 1 - mb;
            let hi = r0.1.max(r0.3 + 1).max(r1.1).max(r1.3 + 1) + mb;
            let base = if v[s].act_const { (lo.max(0) / step) * step } else { 0 };
            assert!(hi - base < lim, "gf G6b: slot {s}: lengths [{lo}, {hi}] do not fit {} bits at base {base}", lb_bits());
            v[s].base = base as usize;
        }
    }
    v.truncate(nslots());
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
    /// live-qubit cap of the circuit: a slot takes clean ancillas and carry pools while the cap leaves room, and
    /// borrowed lanes otherwise
    pub cap: u64,
}

/// Measurement record of one forward slot.
#[derive(Clone, Debug)]
pub struct SlotBits {
    pub d: BitId,
    pub r: Vec<BitId>,
    pub sw: BitId,
    pub a1: BitId,
}


// ------------------------------------------------------------------ gf knob layer (pareto5 track gf)
// Each setting reads a GF_* environment variable once per process; unset, it is the submitted value, so an empty
// environment builds the submitted circuit. A setting meant for an official build must be written as the default.

fn knob(name: &str, default: usize) -> usize {
    std::env::var(name).ok().and_then(|v| v.trim().parse().ok()).unwrap_or(default)
}

macro_rules! knob_fn {
    ($f:ident, $name:literal, $default:expr) => {
        pub fn $f() -> usize {
            static V: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
            *V.get_or_init(|| knob($name, $default))
        }
    };
}

knob_fn!(wc, "GF_WC", 28);
knob_fn!(margin, "GF_MARGIN", 7);
knob_fn!(nslots, "GF_NSLOTS", 261);
knob_fn!(nb, "GF_NB", 31);
knob_fn!(krows, "GF_KROWS", 26);
knob_fn!(kmin, "GF_KMIN", 8);
knob_fn!(cnt_bits, "GF_CNT_BITS", 7);
// gf G6b: LA and LB as lb_bits()-bit offsets from a per-slot base (9 = the submitted registers)
knob_fn!(lb_bits, "GF_LB_BITS", 8);
knob_fn!(base_step, "GF_BASE_STEP", 16);
knob_fn!(base_margin, "GF_BASE_MARGIN", 8);
// idea8 lane knobs (0 = unchanged)
knob_fn!(lean_mask, "GF_LEAN_MASK", 1);
knob_fn!(lean_sweep, "GF_LEAN_SWEEP", 1);
knob_fn!(r_in_lb, "GF_R_IN_LB", 1);
knob_fn!(swdec_order, "GF_SWDEC_ORDER", 2);
knob_fn!(lean_norm, "GF_LEAN_NORM", 1);
knob_fn!(lean_offs, "GF_LEAN_OFFS", 1);
knob_fn!(a1_in_la, "GF_A1_IN_LA", 1);
// idea8 q80x knobs (0 = unchanged)
// GF_D1: one sweep flag S = g & !f replaces the sweep's g, f and y; the rows' zero source and the r/a1 temps move onto
// idle lanes; the r increment takes act and the temp as two controls
knob_fn!(d1, "GF_D1", 1);
// GF_M1 (needs GF_D1): masked rows run their top lane as one gate (no zero source); the masked cells' AND temp sits in
// LB's top lane in the rows (kt <= 31) and on a borrowed lane in the unrows (1), or on a borrowed lane in both (2)
knob_fn!(m1, "GF_M1", 1);
// GF_EFREE: measured flags (sw, gt) leave the live count before their phase repair; the swap flag's phase AND borrows
// lanes when the cap leaves no room; the masked window compare takes its AND temp on a borrowed lane
knob_fn!(efree, "GF_EFREE", 1);

/// gf G6b: the length registers' marker threshold (done-marked or stall-marked values are at or above it)
pub fn mark_thr() -> isize {
    if lb_bits() >= 9 { 257 } else { 1isize << (lb_bits() - 1) }
}

/// Offset of the divisor-length register while the decode's masks run (was the constant W - 1 - NB).
pub fn uoff() -> usize {
    W - 1 - nb()
}

/// The envelope text: GF_ENV names a file, else the committed greedyfrog_data/env.txt.
pub fn env_text() -> String {
    match std::env::var("GF_ENV") {
        Ok(path) => std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("GF_ENV {path}: {e}")),
        Err(_) => include_str!("greedyfrog_data/env.txt").to_string(),
    }
}

/// Validate the knob values against the circuit's fixed register widths (panics on an unsupported setting).
pub fn check_knobs() {
    let (wc, nb, k, km) = (wc(), nb(), krows(), kmin());
    assert!(wc >= 2 && wc <= 120, "GF_WC {wc} out of range");
    assert!(nb >= 8 && nb <= 62, "GF_NB {nb}: the decode masks read 6 bits of u' (NB <= 62)");
    assert!(k >= 4 && k <= 31 && k <= nb, "GF_KROWS {k}: the last-row sweep holds j in 5 bits (k <= 31, k <= NB)");
    assert!(km >= 1 && km <= k, "GF_KMIN {km} must lie in 1..=KROWS");
    assert!(nslots() >= 200, "GF_NSLOTS {} too small", nslots());
}

thread_local! {
    static SLOT: std::cell::Cell<usize> = std::cell::Cell::new(0);
    static PROFS: std::cell::RefCell<std::collections::BTreeMap<(&'static str, usize), u64>> =
        std::cell::RefCell::new(std::collections::BTreeMap::new());
    static PROF: std::cell::RefCell<(u64, &'static str, Vec<(&'static str, u64, u64, u64)>, u64)> =
        std::cell::RefCell::new((0, "", vec![], 0));
}
/// GREEDYFROG_PROF=1: accumulate Toffoli per named section, the peak reached inside it and the section's highest live
/// count (debug aid, no effect on gates).
/// q80x: the slot that the next profiled sections belong to (GREEDYFROG_PROFS=1 keeps per-slot high-water marks)
pub fn set_slot(s: usize) {
    SLOT.with(|c| c.set(s));
}
pub fn prof(b: &B, name: &'static str) {
    if std::env::var_os("GREEDYFROG_PROF").is_none() { return; }
    let sp = b.take_sect_peak();
    if std::env::var_os("GREEDYFROG_PROFS").is_some() {
        let prev = PROF.with(|p| p.borrow().1);
        if !prev.is_empty() {
            let s = SLOT.with(|c| c.get());
            PROFS.with(|m| { let mut m = m.borrow_mut(); let e = m.entry((prev, s)).or_insert(0); *e = (*e).max(sp); });
        }
    }
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
    PROFS.with(|m| {
        for ((n, s), sp) in m.borrow().iter() {
            eprintln!("GFS {n} {s} {sp}");
        }
        m.borrow_mut().clear();
    });
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
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: b.alloc_n(lb_bits() - 1), pre: b.alloc_n(lb_bits() - 1), c0: b.alloc() }
    }
    /// The 9-bit decoder without a comparator chain: its comparators borrow lanes (`ge_const_dirty`, `in_range`).
    fn alloc_lean(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: vec![], pre: b.alloc_n(lb_bits() - 1), c0: b.alloc() }
    }
    /// For the decode's masks on the 6-bit u' (prefix 5; comparators borrow lanes) with a given AND temp.
    fn alloc_small_on(b: &mut B, t: QubitId) -> Masked {
        let f = b.alloc();
        Masked { f, t, gf: f, chain: vec![], pre: b.alloc_n(5), c0: b.alloc() }
    }
    /// For the decode's masks on the 6-bit u' (prefix 5; comparators borrow lanes).
    fn alloc_small(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: b.alloc(), gf: f, chain: vec![], pre: b.alloc_n(5), c0: b.alloc() }
    }
    fn sc(&self) -> Mscr {
        Mscr { f: self.f, t: self.t, gf: self.gf, chain: self.chain.clone() }
    }
    /// q80x: the decode's masks on the 6-bit u' with the AND temp on a borrowed lane (DIRTY_T)
    fn alloc_small_dirty(b: &mut B) -> Masked {
        let f = b.alloc();
        Masked { f, t: super::mask::DIRTY_T, gf: f, chain: vec![], pre: b.alloc_n(5), c0: b.alloc() }
    }
    fn free(self, b: &mut B) {
        b.free(self.f);
        if self.t != super::mask::DIRTY_T {
            b.free(self.t);
        }
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
    let m = if lean_mask() == 1 { Masked::alloc_lean(b) } else { Masked::alloc(b) };
    let (t, s) = value_ladder(u, w);
    // carry pool over the ordinary lanes above the LB window
    let pool = pool_for(b, u, t.len() - (w.lb.1 - w.lb.0 + 1), 0);
    let srcs = [value_src(u, &m, w)];
    let sc = m.sc();
    let ld = Lad { t: &t, s: &s, c0: m.c0, srcs: &srcs, f0: false, cmpl, sc: &sc, g: &pool };
    // mid passes: the running mask stays live between the up and down passes (nothing in between touches it), so
    // neither pass spends comparators cleaning it
    let ru = super::mask::mup_mid(b, &ld);
    b.play(&ru, false);
    let tc = top_carry(&ld);
    b.ccx(a1, tc, u.x[0]);
    if let Some(d) = d {
        b.ccx(a1, tc, d);
    }
    let rd = super::mask::mdown_mid(b, &ld, Some(a1));
    b.play(&rd, false);
    b.free_n(&pool);
    m.free(b);
}

fn value_src(u: &GreedyFrog, m: &Masked, w: &Win) -> Src {
    // ladder lane l <-> physical W - hi + l; toggle where LB == hi - l
    let (lo, hi) = w.lb;
    Src { lo: 0, hi: hi - lo + 1, v: u.lb.clone(), a: hi as isize - w.base as isize, d: -1, pre: m.pre.clone(), late: false }
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
    Src { lo: 0, hi: hi - lo + 1, v: u.la.clone(), a: lo as isize - w.base as isize, d: 1, pre: m.pre.clone(), late: false }
}

/// Plain (unmasked) compare of equal-length ladders: out ^= [gate] & [s > t] (cmpl form), registers restored.
fn plain_compare(b: &mut B, t: &[QubitId], s: &[QubitId], c0: QubitId, sc: &Mscr, out: Option<QubitId>,
                 gate: Option<(QubitId, bool)>, pool: &[QubitId]) {
    // with a carry pool the up pass keeps logical-AND carries, and replaying it inverted uncomputes them by measurement
    let ld = Lad { t, s, c0, srcs: &[], f0: false, cmpl: true, sc, g: pool };
    let ru = mup(b, &ld);
    b.play(&ru, false);
    let tc = top_carry(&ld);
    match gate {
        Some((g, neg)) => {
            if neg {
                b.x(g);
            }
            match out {
                Some(o) => b.ccx(g, tc, o),
                None => b.cz(g, tc),
            }
            if neg {
                b.x(g);
            }
        }
        None => match out {
            Some(o) => b.cx(tc, o),
            None => b.z(tc),
        },
    }
    b.play(&ru, true);
}

/// Run a masked ladder pair. `cmpl`: subtract/compare form. `write`: Some(g) writes the masked sum where g = 1;
/// None only computes the top carry, XORs it into `carry_out`, and restores.
fn masked_pass(b: &mut B, t: &[QubitId], s: &[QubitId], src: Src, m: &Masked, cmpl: bool, write: Option<QubitId>,
               carry_out: Option<QubitId>, pool: &[QubitId]) {
    let srcs = [src];
    let sc = m.sc();
    let ld = Lad { t, s, c0: m.c0, srcs: &srcs, f0: false, cmpl, sc: &sc, g: pool };
    let ru = super::mask::mup_mid(b, &ld);
    b.play(&ru, false);
    if let Some(co) = carry_out {
        let tc = top_carry(&ld);
        b.cx(tc, co);
    }
    match write {
        Some(g) => {
            let rd = super::mask::mdown_mid(b, &ld, Some(g));
            b.play(&rd, false);
        }
        None => b.play(&ru, true),
    }
}

/// out ^= act & [Y[W-L..W) > X[W-L..W)] on the top WC lanes (L = LB, already done-marked by the caller). When the
/// slot's window has every active LB >= WC the compare is unmasked and `gate` (the done flag, negated) keeps
/// finished shots at 0; `gate` None leaves finished shots' bit arbitrary (callers that mask it themselves).
/// out ^= the compare (None: the phase (-1)^compare instead, for a measured erase).
fn top_compare(b: &mut B, u: &GreedyFrog, out: Option<QubitId>, w: &Win, gate: Option<(QubitId, bool)>) {
    if w.lb.0 >= wc() {
        let t: Vec<QubitId> = u.x[W - wc()..].to_vec();
        let s: Vec<QubitId> = u.y[W - wc()..].to_vec();
        let c0 = b.alloc();
        let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
        let pool = pool_for(b, u, wc(), 0);
        plain_compare(b, &t, &s, c0, &sc, out, gate, &pool);
        b.free_n(&pool);
        b.free(c0);
        return;
    }
    assert_eq!(w.base, 0, "gf G6b: the masked top compare needs base 0");
    top_compare_masked(b, u, out);
}

/// big ^= [LB > WC] & [LB < 257] (done-marked LB >= 510 excluded), comparators on a clean chain held only meanwhile.
fn big_lb_flip(b: &mut B, u: &GreedyFrog, big: QubitId) {
    let chain = b.alloc_n(lb_bits() - 1);
    let tmp = b.alloc();
    let lt = b.alloc();
    super::mask::ge_const(b, &u.lb, wc() as isize + 1, tmp, &chain);
    super::mask::ge_const(b, &u.lb, mark_thr(), lt, &chain);
    b.x(lt);
    b.ccx(tmp, lt, big);
    b.x(lt);
    super::mask::ge_const(b, &u.lb, mark_thr(), lt, &chain);
    super::mask::ge_const(b, &u.lb, wc() as isize + 1, tmp, &chain);
    b.free_n(&[lt, tmp]);
    b.free_n(&chain);
}

fn top_compare_masked(b: &mut B, u: &GreedyFrog, out: Option<QubitId>) {
    // ladder over physical lanes W-WC .. W-1; ladder l <-> physical W - WC + l; f on where LB == WC - l
    let t: Vec<QubitId> = u.x[W - wc()..].to_vec();
    let s: Vec<QubitId> = u.y[W - wc()..].to_vec();
    // shots with LB >= WC start active at lane 0 (f0 = 1 would be wrong for done shots): toggle at l = 0 for any
    // LB >= WC is not expressible as one equality, so the window starts at the lane where LB == WC (l = 0) and
    // shots with LB > WC get an extra toggle source below via the "active from the start" flag `big`, computed
    // before the mask scratch exists (its comparator chain and the ladder's scratch never coexist).
    let big = b.alloc();
    big_lb_flip(b, u, big);
    let m = Masked::alloc_lean(b);
    // f starts at `big`: emulate f0 = big by toggling f before the ladder; sources toggle where LB == WC - l (l >= 1)
    b.cx(big, m.f);
    let srcs = [Src { lo: 0, hi: wc(), v: u.lb.clone(), a: wc() as isize, d: -1, pre: m.pre.clone(), late: false }];
    let sc = m.sc();
    let ld = Lad { t: &t, s: &s, c0: m.c0, srcs: &srcs, f0: false, cmpl: true, sc: &sc, g: &[] };
    let ru = super::mask::mup_mid(b, &ld);
    b.play(&ru, false);
    let tc = top_carry(&ld);
    match out {
        Some(o) => b.cx(tc, o),
        None => b.z(tc),
    }
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
fn unrenorm_top(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, r: &[QubitId]) {
    let x = &u.x;
    for k in 0..r.len() {
        let n = 1usize << k;
        crot_down(b, r[k], x, n);
        let mut lits = act_lits(act);
        lits.extend((0..n).map(|i| (x[W - 1 - i], true)));
        erase_and(b, u, r[k], &lits);
    }
}

impl GreedyFrog {
    /// The DONE counter c lives complemented in Y lanes 0..CNT_BITS: a finished shot's Y is the constant
    /// (B = 1, marker, tA = p), whose lowest lanes hold p's top bits (all ones), so c = !Y[0..8] with c = 0 at the
    /// finish; active shots never touch it.
    pub fn with_cnt(mut self) -> GreedyFrog {
        self.cnt = self.y[..cnt_bits()].to_vec();
        self
    }
    /// c += ctrl
    fn cnt_inc(&self, b: &mut B, ctrl: QubitId) {
        let anc = b.alloc_n(cnt_bits() - 1);
        super::arith::dec(b, ctrl, &self.cnt, &anc);
        b.free_n(&anc);
    }
    /// c -= ctrl
    fn cnt_dec(&self, b: &mut B, ctrl: QubitId) {
        let anc = b.alloc_n(cnt_bits() - 1);
        super::arith::inc(b, ctrl, &self.cnt, &anc);
        b.free_n(&anc);
    }
    /// out ^= [c == 0] (all counter lanes one)
    fn cnt_zero_into(&self, b: &mut B, out: QubitId) {
        let lits: Vec<(QubitId, bool)> = self.cnt.iter().map(|&q| (q, false)).collect();
        and_into(b, &lits, out);
    }

    pub fn alloc(b: &mut B) -> GreedyFrog {
        GreedyFrog { x: b.alloc_n(W), y: b.alloc_n(W), la: b.alloc_n(lb_bits()), lb: b.alloc_n(lb_bits()),
              dirty: b.alloc_n(TEST_DIRTY),
              cap: std::env::var("GREEDYFROG_TEST_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(u64::MAX),
              cnt: vec![], par: b.alloc() }.with_cnt()
    }

    /// sw ^= act & [LA != 0] & X[W-1] & (LA < LB | LA == LB & Y top > X top)   (F9). The top compare is unmasked even
    /// when LB < WC: with LA == LB the values differ inside their top LB lanes unless A' == B, and A' == B forces
    /// B = gcd = 1, so LB == 1 is excluded instead (A' == B == 1 never swaps).
    /// sw ^= F9 (out None: the phase (-1)^F9, for a measured erase). The temporaries are erased by measurement.
    fn swap_flag(&self, b: &mut B, z0: Option<QubitId>, out: Option<QubitId>, w: &Win) {
        let lt = b.alloc();
        let eq = b.alloc();
        let cmp = b.alloc();
        let nz = b.alloc();
        lt_into(b, &self.la, &self.lb, lt);
        eq_auto(b, self, &self.la, &self.lb, eq);
        let cmp_into = |b: &mut B, u: &GreedyFrog, cmp: Option<QubitId>| {
            let t: Vec<QubitId> = u.x[W - wc()..].to_vec();
            let s: Vec<QubitId> = u.y[W - wc()..].to_vec();
            let c0 = b.alloc();
            let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
            if w.lb.0 <= 1 {
                let ne1 = b.alloc();
                and_auto(b, u, &eq_lits(&u.lb, 1), ne1);
                b.x(ne1);
                let pool = pool_for(b, u, wc(), 0);
                plain_compare(b, &t, &s, c0, &sc, cmp, Some((ne1, false)), &pool);
                b.free_n(&pool);
                b.x(ne1);
                and_auto(b, u, &eq_lits(&u.lb, 1), ne1);
                b.free(ne1);
            } else {
                let pool = pool_for(b, u, wc(), 0);
                plain_compare(b, &t, &s, c0, &sc, cmp, None, &pool);
                b.free_n(&pool);
            }
            b.free(c0);
        };
        cmp_into(b, self, Some(cmp));
        let nz_on = w.base == 0;
        if nz_on {
            zero_auto(b, self, &self.la, nz); // nz = [LA == 0]
        }
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
        let mut lits: Vec<(QubitId, bool)> = z0.map(|z| vec![(z, true)]).unwrap_or_default();
        if nz_on {
            lits.push((nz, true));
        }
        lits.extend([(self.x[W - 1], false), (or, false)]);
        match out {
            Some(sw) => and_auto(b, self, &lits, sw),
            None if efree() == 1 => phase_auto(b, self, &lits),
            None => phase_and(b, &lits),
        }
        b.x(lt);
        b.x(ec);
        b.x(or);
        b.and_u(lt, ec, or);
        b.x(ec);
        b.x(lt);
        b.free(or);
        b.and_u(eq, cmp, ec);
        b.free(ec);
        let zl: Vec<(QubitId, bool)> = self.la.iter().map(|&q| (q, true)).collect();
        if nz_on {
            erase_and(b, self, nz, &zl);
        }
        erase_mbu(b, cmp, |b| cmp_into(b, self, None));
        for i in 0..lb_bits() {
            b.cx(self.lb[i], self.la[i]);
        }
        erase_and(b, self, eq, &zl);
        for i in 0..lb_bits() {
            b.cx(self.lb[i], self.la[i]);
        }
        erase_mbu(b, lt, |b| lt_phase(b, &self.la, &self.lb));
        b.free_n(&[lt, eq, cmp, nz]);
    }

    /// One forward slot (F1..F11). Returns the measurement record.
    pub fn fwd_slot(&mut self, b: &mut B, w: &Win) -> SlotBits {
        super::mask::set_borrowed(&self.dirty);
        prof(b, "f.z0");
        // F1
        // gf G6b: on a rebased slot no shot can be finished: act = 1 classically, no done test
        let z0: Option<QubitId> = if w.base > 0 { None } else { Some(b.alloc()) };
        if let Some(z0) = z0 {
            zero_into(b, &self.la, z0);
            self.cnt_inc(b, z0);
        }
        // a1 = act & X[W-1]: the slot steps (else it is a stall that only renormalises, or finished)
        let a1 = b.alloc();
        match z0 {
            Some(z0) => {
                b.x(z0);
                b.ccx(z0, self.x[W - 1], a1);
                b.x(z0);
            }
            None => b.cx(self.x[W - 1], a1),
        }
        prof(b, "f.dcmp");
        // F2: d = a1 & [B > A >> e] (top window)
        let d = b.alloc();
        mark_msb(b, a1, &self.lb);
        top_compare(b, self, Some(d), w, Some((a1, false)));
        mark_msb(b, a1, &self.lb);
        prof(b, "f.drot");
        // F3
        crot_up(b, d, &self.x, 1);
        prof(b, "f.value");
        // F4: value chain, subtract where a1
        if let Some(z0) = z0 {
            b.x(z0); // z0 now holds act
        }
        mark_done_inv(b, z0, &self.lb);
        value_pass(b, self, w, true, a1, None);
        mark_done_inv(b, z0, &self.lb);
        prof(b, "f.cof");
        // F5: LA -= d; cofactor chain, add where a1
        {
            let anc = b.alloc_n(lb_bits() - 1);
            super::arith::dec(b, d, &self.la, &anc);
            b.free_n(&anc);
        }
        mark_done_inv(b, z0, &self.la);
        {
            let m = if lean_mask() == 1 { Masked::alloc_lean(b) } else { Masked::alloc(b) };
            let x0 = b.alloc();
            lane0_src(b, self, d, x0);
            let (t, s) = cof_ladder(self, w, x0);
            let src = cof_src(self, &m, w);
            // carry pool over the ordinary lanes below the LA - d window
            let pool = pool_for(b, self, t.len() - (w.lad.1 - w.lad.0 + 1), 0);
            masked_pass(b, &t, &s, src, &m, false, Some(a1), None, &pool);
            b.free_n(&pool);
            lane0_src(b, self, d, x0);
            b.free(x0);
            m.free(b);
        }
        mark_done_inv(b, z0, &self.la);
        prof(b, "f.renorm");
        // F6, F7, F8 (every active shot: a step's renormalisation, or a stall's)
        let r = b.alloc_n(RHO_BITS);
        renorm_top(b, &self.x, z0, &r);
        if let Some(z0) = z0 {
            b.x(z0); // back to z0
        }
        sub_small(b, &self.la, &r);
        prof(b, "f.swap");
        // F9, F10
        let sw = b.alloc();
        self.swap_flag(b, z0, Some(sw), w);
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
        // z0 = [LA == 0] & [cnt != 0] erased by measurement: the repair computes both zero tests, applies the CZ and
        // erases the tests by measurement in turn
        if let Some(z0) = z0 {
        erase_mbu(b, z0, |b| {
            let cl: Vec<(QubitId, bool)> = self.cnt.iter().map(|&q| (q, false)).collect();
            let zl: Vec<(QubitId, bool)> = self.la.iter().map(|&q| (q, true)).collect();
            let cz = b.alloc();
            and_auto(b, self, &cl, cz); // cz = [cnt == 0]
            let lz = b.alloc();
            and_auto(b, self, &zl, lz);
            phase_and(b, &[(lz, false), (cz, true)]);
            erase_and(b, self, lz, &zl);
            erase_and(b, self, cz, &cl);
            b.free(lz);
            b.free(cz);
        });
        b.free(z0);
        }
        prof(b, "end");
        bits
    }
}


// ------------------------------------------------------------------ inverse slot (decode + undo)

/// window bits of the decode (cofactor top bits kept after normalisation)
/// division rows (capacity; per-slot counts come from the envelope)
/// Offset of the divisor-length register while the decode's masks run: LA holds u' = LA + sX - UOFF, so the divisor's
/// bit length is mX = NB - u'. Mask-relevant shots have u' in [0, NB] (bits 0..5); u' < 0 (bit 8) means mX > NB.

/// The masks' 6-bit view of u': bits 0..4 and the sign bit (values below 32 match only shots with u' >= 0; active
/// shots have u' = NB - mX <= NB - 1).
fn ubits(la: &[QubitId]) -> Vec<QubitId> {
    let mut v = la[..5].to_vec();
    v.push(la[lb_bits() - 1]);
    v
}

/// Bottom-normalise a ring's cofactor window by binary search: for k = 4..0, s_k ^= [lanes 0..2^k all zero], then the
/// lanes shift down by 2^k where s_k. Funnel: stage k swaps (i, i + 2^k) for i < NB + 2^k - 1 only (the lanes the
/// window still needs), a rotation of lanes 0 .. NB + 2^(k+1) - 2. s fresh |0>; slack <= 31.
fn norm_bottom(b: &mut B, u: &GreedyFrog, ring: &[QubitId], s: &[QubitId]) {
    for k in (0..R_BITS).rev() {
        let n = 1usize << k;
        let lits: Vec<(QubitId, bool)> = (0..n).map(|i| (ring[i], true)).collect();
        and_auto(b, u, &lits, s[k]);
        for i in 0..nb() + n - 1 {
            b.cswap(s[k], ring[i], ring[i + n]);
        }
    }
}

/// Inverse of norm_bottom (erases s).
fn denorm_bottom(b: &mut B, u: &GreedyFrog, ring: &[QubitId], s: &[QubitId]) {
    for k in 0..R_BITS {
        let n = 1usize << k;
        for i in (0..nb() + n - 1).rev() {
            b.cswap(s[k], ring[i], ring[i + n]);
        }
        let lits: Vec<(QubitId, bool)> = (0..n).map(|i| (ring[i], true)).collect();
        erase_and(b, u, s[k], &lits);
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
    m: Option<Masked>,
    /// q80x layout (GF_D1): no g; f is the sweep flag S and the rows' carry-in; y is the rows' zero source
    d1: bool,
}

/// q80x: a lane id that no gate may touch (the D1 layout has no g)
const NO_Q: QubitId = QubitId(u64::MAX - 4);

impl RowTmp {
    /// q80x (GF_D1). Unmasked: s0, S (= f, the rows' carry-in), jl; the zero source is jl[0] (|0> while rows run).
    /// Masked (GF_M1): s0 and the mask scratch: flag m.f (also the zero source of the unmasked rows, |0> once the
    /// masked rows end), carry-in m.c0 (= S), prefix m.pre (= jl); the masked rows need no zero source and their AND
    /// temp is set per pass.
    fn alloc_d1(b: &mut B, masked: bool) -> RowTmp {
        let s0 = b.alloc();
        if masked {
            let f = b.alloc();
            let m = Masked { f, t: super::mask::DIRTY_T, gf: f, chain: vec![], pre: b.alloc_n(5), c0: b.alloc() };
            RowTmp { s0, g: NO_Q, f: m.c0, y: m.f, jl: m.pre[..R_BITS].to_vec(), m: Some(m), d1: true }
        } else {
            let f = b.alloc();
            let jl = b.alloc_n(R_BITS);
            RowTmp { s0, g: NO_Q, f, y: jl[0], jl, m: None, d1: true }
        }
    }
    fn alloc(b: &mut B, masked: bool) -> RowTmp {
        let (s0, g, y) = (b.alloc(), b.alloc(), b.alloc());
        if masked {
            let m = Masked::alloc_small_on(b, g);
            RowTmp { s0, g, f: m.c0, y, jl: m.pre[..R_BITS].to_vec(), m: Some(m), d1: false }
        } else {
            RowTmp { s0, g, f: b.alloc(), y, jl: b.alloc_n(R_BITS), m: None, d1: false }
        }
    }
    fn free(self, b: &mut B) {
        if self.d1 {
            b.free(self.s0);
            match self.m {
                // the AND temp is a host lane or borrowed: not owned
                Some(m) => {
                    b.free(m.f);
                    b.free_n(&m.pre);
                    b.free(m.c0);
                }
                None => {
                    b.free(self.f);
                    b.free_n(&self.jl);
                }
            }
            return;
        }
        b.free_n(&[self.s0, self.y]);
        match self.m {
            // the mask scratch's AND temp is g
            Some(m) => m.free(b),
            None => {
                b.free(self.g);
                b.free(self.f);
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

/// Junk parking for slots whose divisor cofactor can be shorter than the window: swap the normalised X window's lanes
/// l >= mX (the marker and A's low bits above the divisor cofactor) with the |0> lanes z[l - lo], lo = the window's
/// smallest mX, so that every division row runs as a plain ladder on a zero-padded divisor (whose lanes below the
/// divisor's LSB add 0 and pass the carry: the same arithmetic as the masked rows). LA holds u' (mX = NB - u').
/// Self-inverse: called again with X's window and u' unchanged, it swaps the lanes back. The flag f toggles where
/// u' == NB - l, read off the complemented 6-bit view of u' by a one-hot scan, and is cleared at the end.
fn park_junk(b: &mut B, u: &GreedyFrog, w: &Win, z: &[QubitId]) {
    let lo = w.mx;
    let v = ubits(&u.la);
    for &q in &v {
        b.x(q);
    }
    let f = b.alloc();
    let pre = b.alloc_n(v.len() - 1);
    // !v == l + 63 - NB  <=>  u'_5 == NB - l with sign 0
    super::mask::onehot_scan(b, &v, &pre, lo, nb(), 63 - nb() as isize, |b, l, o| {
        b.cx(o, f);
        b.cswap(f, u.x[l], z[l - lo]);
    });
    b.free_n(&pre);
    for &q in &v {
        b.x(q);
    }
    // f = [lo <= mX <= NB - 1] = [1 <= u' <= NB - lo] (u' >= 0)
    ge_auto(b, u, &v, 1, f);
    ge_auto(b, u, &v, (nb() - lo + 1) as isize, f);
    b.free(f);
}

/// Non-restoring division rows on the normalised windows: rem = Y[0..NB) (MSB at lane 0, sign lane s0 above it) and
/// div = X[0..NB). LA holds u = LA + sX (the divisor's bit length is mX = W - 1 - u). Row j (j < w.k), with
/// D_j = div >> j: r_{j+1} = r_j - D_j where r_j >= 0, r_j + D_j where r_j < 0, computed mod 2^(NB - j + 1) over rem
/// lanes j-1 .. NB-1. |r_{j+1}| <= D_j < 2^(NB - j), so r_{j+1}'s sign lands in lane j - 1 and the quotient bit is
/// q_j = [r_{j+1} >= 0] = !lane(j - 1); r_j's sign (lane j - 2, r_0 >= 0) picks the sign of the step and stays put.
/// Rows whose window has an active mX < NB - j + 1 are masked so they start at the divisor's LSB lane mX + j - 1
/// (rem's lower bits are untouched there, which is the exact arithmetic). No gating and no allocation: the caller
/// records this and undoes it by playing the recording inverted.
fn division_rows(b: &mut B, u: &GreedyFrog, w: &Win, rt: &RowTmp, pool: &[QubitId], parked: bool) {
    let masked_row = |j: usize| !parked && w.mx < nb() - j + 1;
    let sg = u.la[lb_bits() - 1];
    // The masked rows' flag f holds big_j = u'_sign | ![u'_5 >= j] while row j runs (the row pair hands it back
    // unchanged): big_0 = u'_sign, big_j ^ big_(j+1) = !u'_sign & [u'_5 == j], and after the last masked row it is
    // cleared with the comparator. The masked rows are the first ones (j < NB + 1 - mX).
    if masked_row(0) {
        b.cx(sg, rt.m.as_ref().expect("masked row needs mask scratch").f);
    }
    for j in 0..w.k {
        let lo = j as isize - 1;
        let t: Vec<QubitId> = (lo..nb() as isize).rev().map(|i| rt.rem(u, i)).collect();
        let s: Vec<QubitId> = (lo..nb() as isize).rev()
            .map(|i| if i >= j as isize { u.x[i as usize - j] } else { rt.zero() }).collect();
        // m = 1 subtracts: source ^= m, carry-in m. Row 0 always subtracts; row j >= 1 subtracts where lane j - 2 is 0.
        let sign = if j == 0 { None } else { Some(rt.rem(u, j as isize - 2)) };
        // q80x GF_M1: a masked row runs its top lane as one gate, so its zero source is never touched
        let top1 = masked_row(j) && rt.d1 && m1() >= 1;
        let ns = if top1 { s.len() - 1 } else { s.len() };
        let flip = |b: &mut B| {
            for &q in s[..ns].iter().chain(std::iter::once(&rt.c0())) {
                if let Some(sg) = sign {
                    b.cx(sg, q);
                }
                b.x(q);
            }
        };
        flip(b);
        if !masked_row(j) && pool.is_empty() {
            let ru = super::arith::up_m(b, &t, &s, rt.c0(), false);
            b.play(&ru, false);
            let rd = super::arith::down_m(b, &t, &s, rt.c0(), super::arith::Dm::Sum, false);
            b.play(&rd, false);
        } else if !masked_row(j) {
            // the same row with logical-AND carries on the pool's lanes (uncomputed by measurement)
            let sc = Mscr { f: rt.c0(), t: rt.c0(), gf: rt.c0(), chain: vec![] };
            let ld = Lad { t: &t, s: &s, c0: rt.c0(), srcs: &[], f0: false, cmpl: false, sc: &sc,
                           g: &pool[..pool.len().min(t.len())] };
            let ru = super::mask::mup_mid(b, &ld);
            b.play(&ru, false);
            let rd = super::mask::mdown_mid(b, &ld, Some(ALWAYS));
            b.play(&rd, false);
        } else {
            // LA holds u' (mX = NB - u'): the mask turns on at ladder lane l where mX == NB - j - l, i.e. u' == j + l,
            // and is on from the start where mX >= NB - j + 1, i.e. u' < j: f holds big_j (top of the function)
            let m = rt.m.as_ref().expect("masked row needs mask scratch");
            // big = !(!sign & [u'_5 >= j]), computed straight into the flag (the sign literal gates every comparator
            // cube), so no temporary is held across the ladder and g serves as the masked cells' AND temp
            let big = m.f;
            let srcs = [Src { lo: 0, hi: ns, v: ubits(&u.la), a: j as isize, d: 1, pre: m.pre.clone(), late: false }];
            let sc = m.sc();
            let ld = Lad { t: &t[..ns], s: &s[..ns], c0: rt.c0(), srcs: &srcs, f0: false, cmpl: false, sc: &sc, g: &[] };
            let ru = super::mask::mup_mid(b, &ld);
            b.play(&ru, false);
            if top1 {
                // The top lane's up and down cells meet: together they write t ^= f & (m ^ x), x the carry into the
                // lane and m the row's subtract flag (= !sign; row 0: 1). Its own mask toggle (u' == NB, a divisor of
                // length 0) never fires on a valid state.
                let x = top_carry(&ld);
                if let Some(sg) = sign {
                    b.cx(sg, x);
                }
                b.x(x);
                b.ccx(m.f, x, t[ns]);
                b.x(x);
                if let Some(sg) = sign {
                    b.cx(sg, x);
                }
            }
            let rd = super::mask::mdown_mid(b, &ld, Some(ALWAYS));
            b.play(&rd, false);
            // the carry pool is idle in the masked rows (every lane masked): its lanes are the flag's clean chain
            if j + 1 < w.k && masked_row(j + 1) {
                let mut lits = vec![(sg, true)];
                lits.extend(eq_lits(&u.la[..5], j));
                if pool.len() >= 4 {
                    and_into_t(b, &lits, big, &pool[..4]);
                } else {
                    and_dirty(b, &lits, big, &u.dirty);
                }
            } else if pool.len() >= 5 {
                let (chain, ge) = (&pool[..4], pool[4]);
                b.x(big);
                super::mask::ge_const(b, &u.la[..5], j as isize, ge, chain);
                b.x(sg);
                b.ccx(sg, ge, big);
                b.x(sg);
                super::mask::ge_const(b, &u.la[..5], j as isize, ge, chain);
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

impl GreedyFrog {
    /// Lanes the slot may still allocate under the cap.
    fn room(&self, b: &B) -> usize {
        self.cap.saturating_sub(b.live) as usize
    }
}

/// out ^= AND(lits): clean ancillas while the cap leaves room, borrowed lanes otherwise.
fn and_auto(b: &mut B, u: &GreedyFrog, lits: &[(QubitId, bool)], out: QubitId) {
    let need = lits.len().saturating_sub(2);
    if need == 0 || u.room(b) >= need { and_into(b, lits, out) } else { and_dirty(b, lits, out, &u.dirty) }
}

/// Phase (-1)^AND(lits): an AND chain into clean ancillas (uncomputed by measurement) and a CZ, n - 2 Toffoli.
fn phase_and(b: &mut B, lits: &[(QubitId, bool)]) {
    let n = lits.len();
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
    match n {
        0 => {}
        1 => b.z(lits[0].0),
        2 => b.cz(lits[0].0, lits[1].0),
        _ => {
            let anc = b.alloc_n(n - 2);
            b.and_c(lits[0].0, lits[1].0, anc[0]);
            for i in 2..n - 1 {
                b.and_c(anc[i - 2], lits[i].0, anc[i - 1]);
            }
            b.cz(anc[n - 3], lits[n - 1].0);
            for i in (2..n - 1).rev() {
                b.and_u(anc[i - 2], lits[i].0, anc[i - 1]);
            }
            b.and_u(lits[0].0, lits[1].0, anc[0]);
            b.free_n(&anc);
        }
    }
    for &(q, ng) in lits {
        if ng {
            b.x(q);
        }
    }
}

/// Erase t, known to hold f(state), by an X-basis measurement: the phase (-1)^(m f) it leaves is repaired by `phase`
/// in a block conditioned on the outcome m, so the repair's Toffoli count only on the shots where m = 1 (half of
/// them on average), against a full recomputation for an XOR erase.
fn erase_mbu(b: &mut B, t: QubitId, phase: impl FnOnce(&mut B)) {
    let m = b.fresh_bits(1)[0];
    b.hmr_to(t, m);
    b.push_condition(m);
    phase(b);
    b.pop_condition();
}

/// q80x: erase_mbu that frees t (|0> after the measurement) before the repair, so the repair can reuse its lane.
fn erase_mbu_free(b: &mut B, t: QubitId, phase: impl FnOnce(&mut B)) {
    let m = b.fresh_bits(1)[0];
    b.hmr_to(t, m);
    b.free(t);
    b.push_condition(m);
    phase(b);
    b.pop_condition();
}

/// q80x: the phase (-1)^AND(lits) on clean ancillas while the cap leaves room, else through one borrowed lane d:
/// twice (d ^= AND(lits[..n-1]); CZ(d, last)), with the AND on further borrowed lanes.
fn phase_auto(b: &mut B, u: &GreedyFrog, lits: &[(QubitId, bool)]) {
    let n = lits.len();
    if n <= 2 || u.room(b) >= n - 2 {
        phase_and(b, lits);
        return;
    }
    let (d, chain) = (u.dirty[0], &u.dirty[1..]);
    let (last, ng) = lits[n - 1];
    for _ in 0..2 {
        and_dirty(b, &lits[..n - 1], d, chain);
        if ng {
            b.x(last);
        }
        b.cz(d, last);
        if ng {
            b.x(last);
        }
    }
}

/// Erase t = AND(lits) by measurement while the cap leaves room for the repair's chain, by recomputation otherwise.
fn erase_and(b: &mut B, u: &GreedyFrog, t: QubitId, lits: &[(QubitId, bool)]) {
    if u.room(b) >= lits.len().saturating_sub(2) {
        erase_mbu(b, t, |b| phase_and(b, lits));
    } else {
        and_auto(b, u, lits, t);
    }
}

/// Erase t = [v >= k] by measurement (repair on a clean chain) while the cap leaves room, by recomputation otherwise.
fn ge_erase(b: &mut B, u: &GreedyFrog, v: &[QubitId], k: isize, t: QubitId) {
    let need = v.len().saturating_sub(1);
    if u.room(b) >= need {
        let chain = b.alloc_n(need);
        erase_mbu(b, t, |b| super::mask::ge_const_phase(b, v, k, &chain));
        b.free_n(&chain);
    } else {
        super::mask::ge_const_dirty(b, v, k, t, &u.dirty);
    }
}

/// Phase (-1)^[a < b] (lt_into with a phase in place of the XOR), for a measured erase.
fn lt_phase(b: &mut B, a: &[QubitId], bb: &[QubitId]) {
    let c0 = b.alloc();
    let ru = super::arith::up(b, a, bb, c0);
    b.play(&ru, false);
    b.z(bb[a.len() - 1]);
    b.play(&ru, true);
    b.free(c0);
}

/// t ^= [v >= k] on a clean chain while the cap leaves room, on borrowed lanes otherwise.
fn ge_auto(b: &mut B, u: &GreedyFrog, v: &[QubitId], k: isize, t: QubitId) {
    let need = v.len().saturating_sub(1);
    if u.room(b) >= need {
        let chain = b.alloc_n(need);
        super::mask::ge_const(b, v, k, t, &chain);
        b.free_n(&chain);
    } else {
        super::mask::ge_const_dirty(b, v, k, t, &u.dirty);
    }
}

/// bits += ctrl, clean carries while the cap leaves room.
fn inc_auto(b: &mut B, u: &GreedyFrog, ctrl: QubitId, bits: &[QubitId]) {
    let need = bits.len().saturating_sub(1);
    if u.room(b) >= need {
        let anc = b.alloc_n(need);
        super::arith::inc(b, ctrl, bits, &anc);
        b.free_n(&anc);
    } else {
        inc_dirty(b, ctrl, bits, &u.dirty);
    }
}

fn zero_auto(b: &mut B, u: &GreedyFrog, v: &[QubitId], out: QubitId) {
    let lits: Vec<(QubitId, bool)> = v.iter().map(|&q| (q, true)).collect();
    and_auto(b, u, &lits, out);
}

fn eq_auto(b: &mut B, u: &GreedyFrog, a: &[QubitId], bb: &[QubitId], out: QubitId) {
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
    zero_auto(b, u, a, out);
    for i in 0..a.len() {
        b.cx(bb[i], a[i]);
    }
}

/// v += k (or -= k): a constant register while the cap leaves room, borrowed-lane increments otherwise.
fn add_const_auto(b: &mut B, u: &GreedyFrog, v: &[QubitId], k: usize, sub: bool) {
    if u.room(b) >= v.len() + 1 { add_const(b, v, k, sub) } else { add_const_dirty(b, v, k, sub, &u.dirty) }
}

/// Clean carry pool for a ladder pass: at most `want` lanes, leaving `reserve` lanes of room.
fn pool_for(b: &mut B, u: &GreedyFrog, want: usize, reserve: usize) -> Vec<QubitId> {
    let n = want.min(u.room(b).saturating_sub(reserve));
    b.alloc_n(n)
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
/// only where row j fired) by measurement. Row 0 never changes jl (0 is the default), so it is not visited.
/// g_j = act & [kt >= j]; g = 0 on entry and exit. Emitted directly (the measured erases are not recordable); ANDs on
/// `chain` (clean when `clean`, borrowed lanes otherwise).
fn sweep_fwd(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, chain: &[QubitId], clean: bool) {
    let (jl, f, y) = (&rt.jl[..], rt.f, rt.y);
    let kt5 = &u.lb[..R_BITS];
    let k = w.k;
    ge_any(b, kt5, k as isize - 1, y, chain, clean);
    act_cx(b, act, y, rt.g);
    if clean {
        erase_mbu(b, y, |b| super::mask::ge_const_phase(b, kt5, k as isize - 1, chain));
    } else {
        ge_any(b, kt5, k as isize - 1, y, chain, clean);
    }
    for j in (1..k).rev() {
        if j + 1 < k {
            let mut lits = act_lits(act);
            lits.extend(eq_lits(kt5, j));
            and_any(b, clean, &lits, rt.g, chain);
        }
        let lane = rt.rem(u, j as isize - 1);
        and_any(b, clean, &[(lane, true), (rt.g, false), (f, true)], y, chain);
        for (i, &bit) in jl.iter().enumerate() {
            if (j >> i) & 1 == 1 {
                b.cx(y, bit);
            }
        }
        b.cx(y, f);
        let mut lits = vec![(lane, true)];
        lits.extend(eq_lits(jl, j));
        erase_and(b, u, y, &lits);
    }
    // g = act & [kt >= 1] -> act -> 0
    let mut lits = act_lits(act);
    lits.extend(eq_lits(kt5, 0));
    and_any(b, clean, &lits, rt.g, chain);
    match act {
        Some(a) => b.cx(a, rt.g),
        None => b.x(rt.g),
    }
}

/// The exact inverse of `sweep_fwd` (rows in the opposite order), with each row's y erased by measurement through
/// its forward definition !lane & g & !f.
fn sweep_bwd(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp, chain: &[QubitId], clean: bool) {
    let (jl, f, y) = (&rt.jl[..], rt.f, rt.y);
    let kt5 = &u.lb[..R_BITS];
    let k = w.k;
    match act {
        Some(a) => b.cx(a, rt.g),
        None => b.x(rt.g),
    }
    let mut lits = act_lits(act);
    lits.extend(eq_lits(kt5, 0));
    and_any(b, clean, &lits, rt.g, chain);
    for j in 1..k {
        let lane = rt.rem(u, j as isize - 1);
        let mut lits = vec![(lane, true)];
        lits.extend(eq_lits(jl, j));
        and_any(b, clean, &lits, y, chain);
        b.cx(y, f);
        for (i, &bit) in jl.iter().enumerate() {
            if (j >> i) & 1 == 1 {
                b.cx(y, bit);
            }
        }
        erase_and(b, u, y, &[(lane, true), (rt.g, false), (f, true)]);
        if j + 1 < k {
            let mut lits = act_lits(act);
            lits.extend(eq_lits(kt5, j));
            and_any(b, clean, &lits, rt.g, chain);
        }
    }
    ge_any(b, kt5, k as isize - 1, y, chain, clean);
    act_cx(b, act, y, rt.g);
    if clean {
        erase_mbu(b, y, |b| super::mask::ge_const_phase(b, kt5, k as isize - 1, chain));
    } else {
        ge_any(b, kt5, k as isize - 1, y, chain, clean);
    }
}

/// q80x (GF_D1): jl ^= the last row with q_j = 1 among the rows j <= kt of active shots, with one flag S = g & !f
/// ("still searching") on the lane rt.f: S ^= act & [kt >= k-1]; for j = k-1 .. 1: S ^= act & [kt == j] (j < k-1),
/// jl ^= j (!lane & S), S ^= [jl == j] (jl == j only where row j fired). At the end S ^= act & [kt == 0] and
/// S ^= act leave S = f = [jl != 0]. Every AND runs on borrowed lanes.
fn sweep_fwd_d1(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp) {
    let (jl, s) = (&rt.jl[..], rt.f);
    let kt5 = &u.lb[..R_BITS];
    let d = &u.dirty[..];
    let gate = act_lits(act);
    let k = w.k;
    super::mask::ge_const_dirty_gated(b, kt5, k as isize - 1, s, &gate, d);
    for j in (1..k).rev() {
        if j + 1 < k {
            let mut lits = gate.clone();
            lits.extend(eq_lits(kt5, j));
            and_dirty(b, &lits, s, d);
        }
        let lane = rt.rem(u, j as isize - 1);
        b.x(lane);
        for (i, &bit) in jl.iter().enumerate() {
            if (j >> i) & 1 == 1 {
                b.ccx(lane, s, bit);
            }
        }
        b.x(lane);
        and_dirty(b, &eq_lits(jl, j), s, d);
    }
    let mut lits = gate.clone();
    lits.extend(eq_lits(kt5, 0));
    and_dirty(b, &lits, s, d);
    match act {
        Some(a) => b.cx(a, s),
        None => b.x(s),
    }
}

/// The exact inverse of `sweep_fwd_d1`.
fn sweep_bwd_d1(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, w: &Win, rt: &RowTmp) {
    let (jl, s) = (&rt.jl[..], rt.f);
    let kt5 = &u.lb[..R_BITS];
    let d = &u.dirty[..];
    let gate = act_lits(act);
    let k = w.k;
    match act {
        Some(a) => b.cx(a, s),
        None => b.x(s),
    }
    let mut lits = gate.clone();
    lits.extend(eq_lits(kt5, 0));
    and_dirty(b, &lits, s, d);
    for j in 1..k {
        and_dirty(b, &eq_lits(jl, j), s, d);
        let lane = rt.rem(u, j as isize - 1);
        b.x(lane);
        for (i, &bit) in jl.iter().enumerate() {
            if (j >> i) & 1 == 1 {
                b.ccx(lane, s, bit);
            }
        }
        b.x(lane);
        if j + 1 < k {
            let mut lits = gate.clone();
            lits.extend(eq_lits(kt5, j));
            and_dirty(b, &lits, s, d);
        }
    }
    super::mask::ge_const_dirty_gated(b, kt5, k as isize - 1, s, &gate, d);
}

/// q80x: S ^= [jl != 0] (S = f after the sweep, so this empties it and, applied again, refills it).
fn s_flip_found(b: &mut B, u: &GreedyFrog, rt: &RowTmp) {
    b.x(rt.f);
    let lits: Vec<(QubitId, bool)> = rt.jl.iter().map(|&q| (q, true)).collect();
    and_auto(b, u, &lits, rt.f);
}

/// q80x: bits += act & c (act None: bits += c), clean chains while the cap leaves room.
fn inc2_auto(b: &mut B, u: &GreedyFrog, act: Option<QubitId>, c: QubitId, bits: &[QubitId]) {
    let Some(a) = act else {
        inc_auto(b, u, c, bits);
        return;
    };
    for i in (0..bits.len()).rev() {
        let mut lits = vec![(a, false), (c, false)];
        lits.extend(bits[..i].iter().map(|&q| (q, false)));
        and_auto(b, u, &lits, bits[i]);
    }
}

/// gt ^= [Y window > X window] over the cofactor lanes [0, mX) (LA holds u = LA + sX, mX = W - 1 - u).
fn window_gt(b: &mut B, u: &GreedyFrog, gt: Option<QubitId>, w: &Win) {
    let t: Vec<QubitId> = (0..nb()).rev().map(|i| u.x[i]).collect();
    let sv: Vec<QubitId> = (0..nb()).rev().map(|i| u.y[i]).collect();
    if w.mxp >= nb() + 1 {
        let c0 = b.alloc();
        let sc = Mscr { f: c0, t: c0, gf: c0, chain: vec![] };
        let pool = pool_for(b, u, nb(), 0);
        plain_compare(b, &t, &sv, c0, &sc, gt, None, &pool);
        b.free_n(&pool);
        b.free(c0);
        return;
    }
    // LA holds u (mX = W - 1 - u): offset it to u' = u - UOFF (mX = NB - u'). The mask turns on at ladder lane l where
    // mX == NB - l, i.e. u' == l, and is on from the start where mX >= NB + 1, i.e. u' < 0 (its sign bit).
    add_const_auto(b, u, &u.la, uoff() - w.base, true);
    let m = if efree() == 1 && u.room(b) < 8 { Masked::alloc_small_dirty(b) } else { Masked::alloc_small(b) };
    let sg = u.la[lb_bits() - 1];
    b.cx(sg, m.f);
    let srcs = [Src { lo: 0, hi: nb(), v: ubits(&u.la), a: 0, d: 1, pre: m.pre.clone(), late: false }];
    let sc = m.sc();
    let ld = Lad { t: &t, s: &sv, c0: m.c0, srcs: &srcs, f0: false, cmpl: true, sc: &sc, g: &[] };
    let ru = super::mask::mup_mid(b, &ld);
    b.play(&ru, false);
    let tc = top_carry(&ld);
    match gt {
        Some(o) => b.cx(tc, o),
        None => b.z(tc),
    }
    b.play(&ru, true);
    b.cx(sg, m.f);
    m.free(b);
    add_const_auto(b, u, &u.la, uoff() - w.base, false);
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
        let sy = b.alloc_n(R_BITS);
        norm_bottom(b, self, &self.x, &sx);
        norm_bottom(b, self, &self.y, &sy);
        prof(b, "i.swdec");
        // I2: u = LA + sX, v = LB + sY (cofactor bit lengths mX = W - 1 - u, mY = W - 1 - v):
        // sw = act & (mY < mX | mY == mX & winY <= winX)
        self.small_add(b, &self.la, &sx, false);
        self.small_add(b, &self.lb, &sy, false);
        let gt_pre = if swdec_order() == 2 {
            let g = b.alloc();
            window_gt(b, self, Some(g), w);
            Some(g)
        } else { None };
        let sw = b.alloc();
        {
            // idea8 GF_SWDEC_ORDER: the window compare first, before lt and eq hold lanes
            let (lt, eq, gt);
            if swdec_order() >= 1 {
                gt = match gt_pre {
                    Some(g) => g,
                    None => {
                        let g = b.alloc();
                        window_gt(b, self, Some(g), w);
                        g
                    }
                };
                lt = b.alloc();
                eq = b.alloc();
                lt_into(b, &self.la, &self.lb, lt);
                if swdec_order() == 2 { eq_auto(b, self, &self.la, &self.lb, eq) } else { eq_into(b, &self.la, &self.lb, eq) }
            } else {
            lt = b.alloc();
            eq = b.alloc();
            gt = b.alloc();
            lt_into(b, &self.la, &self.lb, lt);
            eq_into(b, &self.la, &self.lb, eq);
            window_gt(b, self, Some(gt), w);
            }
            let le = b.alloc();
            b.x(gt);
            b.and_c(eq, gt, le);
            b.x(gt);
            let v = b.alloc();
            b.x(lt);
            b.x(le);
            b.and_c(lt, le, v);
            b.x(v);
            act_cx(b, act, v, sw);
            b.x(v);
            b.and_u(lt, le, v);
            b.x(le);
            b.x(lt);
            b.free(v);
            b.x(gt);
            b.and_u(eq, gt, le);
            b.x(gt);
            b.free(le);
            if swdec_order() == 0 {
                erase_mbu(b, gt, |b| window_gt(b, self, None, w));
            }
            for i in 0..lb_bits() {
                b.cx(self.lb[i], self.la[i]);
            }
            let zl: Vec<(QubitId, bool)> = self.la.iter().map(|&q| (q, true)).collect();
            erase_and(b, self, eq, &zl);
            for i in 0..lb_bits() {
                b.cx(self.lb[i], self.la[i]);
            }
            erase_mbu(b, lt, |b| lt_phase(b, &self.la, &self.lb));
            if swdec_order() >= 1 && efree() == 1 {
                b.free_n(&[lt, eq]);
                erase_mbu_free(b, gt, |b| window_gt(b, self, None, w));
            } else if swdec_order() >= 1 {
                b.free_n(&[lt, eq]);
                erase_mbu(b, gt, |b| window_gt(b, self, None, w));
                b.free(gt);
            } else {
            b.free_n(&[lt, eq, gt]);
            }
        }
        self.small_add(b, &self.lb, &sy, true);
        self.small_add(b, &self.la, &sx, true);
        prof(b, "i.unswap");
        // I3, I4
        b.z_if(sw, bits.sw);
        super::arith::cswap_regs(b, sw, &self.x, &self.y);
        super::arith::cswap_regs(b, sw, &self.la, &self.lb);
        super::arith::cswap_regs(b, sw, &sx, &sy);
        b.cx(sw, self.par);
        prof(b, "i.swerase");
        // I5: erase sw with the forward's F9 logic
        let sw_rep = |b: &mut B| {
            if let Some(z0) = z0 {
                b.x(z0);
            }
            self.swap_flag(b, z0, None, w);
            if let Some(z0) = z0 {
                b.x(z0);
            }
        };
        if efree() == 1 {
            erase_mbu_free(b, sw, sw_rep);
        } else {
            erase_mbu(b, sw, sw_rep);
            b.free(sw);
        }
        prof(b, "i.rows");
        // I6: u = LA + sX in LA, kt = u - (LB + sY) = mY - mX in LB; rows; r = act & (sX - sY - j_last)
        self.small_add(b, &self.la, &sx, false);
        self.small_add(b, &self.lb, &sy, false);
        for &q in &self.lb {
            b.x(q);
        }
        add_c(b, &self.lb, &self.la, true, false);
        let masked_rows = w.mx < nb() + 1;
        if masked_rows {
            if lean_offs() == 1 { add_const_auto(b, self, &self.la, uoff() - w.base, true) } else { add_const(b, &self.la, uoff() - w.base, true) }
        }
        // Masked-row slots park the divisor window's junk when the cap leaves room for it beside the plain rows'
        // temporaries, r, a1 and the sweep's chain; every row then runs plain (and pooled where room is left).
        let zn = nb() - w.mx.min(nb());
        let park = masked_rows && self.room(b) >= zn + 9 + RHO_BITS + 1 + R_BITS - 1;
        let z = if park { b.alloc_n(zn) } else { vec![] };
        if park {
            park_junk(b, self, w, &z);
        }
        let (r, a1) = if d1() == 1 {
            self.rows_d1(b, bits, w, act, &sx, &sy, masked_rows, park)
        } else {
            let rt = RowTmp::alloc(b, masked_rows && !park);
            // The rows' carry pool is held only while a rows pass runs: the inverse pass is re-recorded on a pool taken
            // then (the same function), so r, a1 and the sweep's chain can use the lanes in between.
            let pool = pool_for(b, self, nb() + 1, 0);
            b.begin();
            division_rows(b, self, w, &rt, &pool, park);
            let rows = b.end();
            b.play(&rows, false);
            b.free_n(&pool);
            prof(b, "i.sweep");
            // The sweep runs on a clean 4-lane chain; its inverse runs later beside r and a1, on a clean chain while the
            // cap leaves room and on borrowed lanes otherwise.
            if lean_sweep() == 1 {
                sweep_fwd(b, self, act, w, &rt, &self.dirty, false);
            } else {
            let ch = b.alloc_n(R_BITS - 1);
            sweep_fwd(b, self, act, w, &rt, &ch, true);
            b.free_n(&ch);
            }
            // idea8 GF_R_IN_LB: LB holds kt <= 31 here, so its top RHO_BITS lanes are |0> on active shots
            let r = if r_in_lb() == 1 { self.lb[lb_bits() - RHO_BITS..].to_vec() } else { b.alloc_n(RHO_BITS) };
            let a1_host = a1_in_la() == 1
                && (masked_rows || W as isize - 1 - w.mx as isize - w.base as isize <= 127);
            let a1 = if !a1_host {
                b.alloc()
            } else if masked_rows {
                b.cx(self.la[lb_bits() - 1], self.la[lb_bits() - 2]);
                self.la[lb_bits() - 2]
            } else {
                self.la[lb_bits() - 1]
            };
            // jl <- sX - sY - jl in place: the rotation since the last step (rho_of in greedyfrog_model). This slot's rotation
            // rho = act & ((jl mod 8) + #{8, 15, 22, 29 <= jl}) mod 8 and a1 = act & [jl < 8] (the slot was a step).
            // Temps: y and g (|0> after the sweep) and the sweep chain.
            let jl = rt.jl.clone();
            for &q in &jl {
                b.x(q);
            }
            add_c_on(b, &jl, &sx, true, false, rt.g);
            add_c_on(b, &jl, &sy, false, true, rt.g);
            {
                for i in 0..RHO_BITS {
                    act_cx(b, act, jl[i], r[i]);
                }
                let (t, c) = (rt.y, rt.g);
                for cst in [8isize, 15, 22, 29] {
                    ge_auto(b, self, &jl, cst, t);
                    match act {
                        Some(a) => b.and_c(a, t, c),
                        None => b.cx(t, c),
                    }
                    inc_auto(b, self, c, &r);
                    match act {
                        Some(a) => b.and_u(a, t, c),
                        None => b.cx(t, c),
                    }
                    ge_erase(b, self, &jl, cst, t);
                }
                let mut lits = act_lits(act);
                lits.extend([(jl[3], true), (jl[4], true)]);
                and_auto(b, self, &lits, a1);
            }
            add_c_on(b, &jl, &sy, false, false, rt.g);
            add_c_on(b, &jl, &sx, true, true, rt.g);
            for &q in &jl {
                b.x(q);
            }
            for i in 0..RHO_BITS {
                match act {
                    Some(a) if r_in_lb() == 1 => {
                        b.push_condition(bits.r[i]);
                        b.cz(a, r[i]);
                        b.pop_condition();
                    }
                    _ => b.z_if(r[i], bits.r[i]),
                }
            }
            b.z_if(a1, bits.a1);
            if lean_sweep() == 0 && self.room(b) >= R_BITS - 1 {
                let ch2 = b.alloc_n(R_BITS - 1);
                sweep_bwd(b, self, act, w, &rt, &ch2, true);
                b.free_n(&ch2);
            } else {
                sweep_bwd(b, self, act, w, &rt, &self.dirty, false);
            }
            prof(b, "i.rows_rev");
            let pool = pool_for(b, self, nb() + 1, 0);
            b.begin();
            division_rows(b, self, w, &rt, &pool, park);
            let unrows = b.end();
            b.play(&unrows, true);
            b.free_n(&pool);
            rt.free(b);
            let r = if r_in_lb() == 1 {
                let r2 = b.alloc_n(RHO_BITS);
                for i in 0..RHO_BITS {
                    match act {
                        Some(a) => {
                            b.ccx(a, r[i], r2[i]);
                            b.cx(r2[i], r[i]);
                        }
                        None => b.swap(r[i], r2[i]),
                    }
                }
                r2
            } else { r };
            let a1 = if a1_host {
                let a = b.alloc();
                b.swap(a1, a);
                if masked_rows {
                    b.cx(self.la[lb_bits() - 1], self.la[lb_bits() - 2]);
                }
                a
            } else { a1 };
            (r, a1)
        };
        if park {
            park_junk(b, self, w, &z);
            b.free_n(&z);
        }
        if masked_rows {
            if lean_offs() == 1 { add_const_auto(b, self, &self.la, uoff() - w.base, false) } else { add_const(b, &self.la, uoff() - w.base, false) }
        }
        add_c(b, &self.lb, &self.la, true, true);
        for &q in &self.lb {
            b.x(q);
        }
        self.small_add(b, &self.lb, &sy, true);
        self.small_add(b, &self.la, &sx, true);
        prof(b, "i.denorm");
        denorm_bottom(b, self, &self.y, &sy);
        denorm_bottom(b, self, &self.x, &sx);
        b.free_n(&sx);
        b.free_n(&sy);
        prof(b, "i.unrenorm");
        // I7, I8, I9
        self.small_add(b, &self.la, &r, false);
        unrenorm_top(b, self, act, &r);
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
            let m = if lean_mask() == 1 { Masked::alloc_lean(b) } else { Masked::alloc(b) };
            let x0 = b.alloc();
            lane0_src(b, self, d, x0);
            let (t, s) = cof_ladder(self, w, x0);
            let src = cof_src(self, &m, w);
            // carry pool over the ordinary lanes below the LA - d window
            let pool = pool_for(b, self, t.len() - (w.lad.1 - w.lad.0 + 1), 0);
            masked_pass(b, &t, &s, src, &m, true, Some(a1), None, &pool);
            b.free_n(&pool);
            lane0_src(b, self, d, x0);
            b.free(x0);
            m.free(b);
        }
        mark_done_inv(b, act, &self.la);
        prof(b, "i.dundo");
        // I12, I13, I14
        {
            let anc = b.alloc_n(lb_bits() - 1);
            super::arith::inc(b, d, &self.la, &anc);
            b.free_n(&anc);
        }
        crot_down(b, d, &self.x, 1);
        mark_msb(b, a1, &self.lb);
        erase_mbu(b, d, |b| top_compare(b, self, None, w, Some((a1, false))));
        mark_msb(b, a1, &self.lb);
        b.free(d);
        prof(b, "i.end15");
        // I15: a1 = act & X[W-1] on the restored pre-state
        let mut lits = act_lits(act);
        lits.push((self.x[W - 1], false));
        erase_mbu(b, a1, |b| phase_and(b, &lits));
        b.free(a1);
        if let Some(z0) = z0 {
            b.x(z0); // z0 = done flag again
            self.cnt_dec(b, z0);
            let zl: Vec<(QubitId, bool)> = self.la.iter().map(|&q| (q, true)).collect();
            erase_and(b, self, z0, &zl);
            b.free(z0);
        }
        prof(b, "end");
    }

    /// t += s (sub: t -= s), len(s) < len(t). GF_EFREE: one carry lane; the low len(s) lanes ripple (Cuccaro) and their
    /// carry out increments the high lanes between the two passes, so the source needs no zero padding.
    fn small_add(&self, b: &mut B, t: &[QubitId], s: &[QubitId], sub: bool) {
        if efree() == 0 {
            if sub { sub_small(b, t, s) } else { add_small(b, t, s) }
            return;
        }
        let m = s.len();
        assert!(m >= 1 && m < t.len());
        let c0 = b.alloc();
        if sub {
            for &q in &t[m..] {
                b.x(q);
            }
        }
        let ru = super::arith::up_m(b, &t[..m], s, c0, sub);
        b.play(&ru, false);
        inc_auto(b, self, s[m - 1], &t[m..]);
        let rd = super::arith::down_m(b, &t[..m], s, c0, super::arith::Dm::Sum, sub);
        b.play(&rd, false);
        if sub {
            for &q in &t[m..] {
                b.x(q);
            }
        }
        b.free(c0);
    }

    /// q80x (GF_D1, GF_M1): the decode core with the D1 row layout: rows, sweep, r and a1, the sweep's inverse and the
    /// unrows. r and a1 come back on fresh lanes, as in the original path.
    #[allow(clippy::too_many_arguments)]
    fn rows_d1(&self, b: &mut B, bits: &SlotBits, w: &Win, act: Option<QubitId>, sx: &[QubitId], sy: &[QubitId],
               masked_rows: bool, park: bool) -> (Vec<QubitId>, QubitId) {
        assert!(r_in_lb() == 1, "GF_D1 needs GF_R_IN_LB");
        let lay_masked = masked_rows && !park;
        let m1_on = lay_masked && m1() >= 1;
        let mut rt = if m1_on {
            RowTmp::alloc_d1(b, true)
        } else if lay_masked {
            RowTmp::alloc(b, true)
        } else {
            RowTmp::alloc_d1(b, false)
        };
        if m1_on {
            // the masked cells' AND temp: LB's top lane (kt <= 31 leaves it |0> until rho arrives) or borrowed
            rt.m.as_mut().unwrap().t = if m1() == 1 { self.lb[lb_bits() - 1] } else { super::mask::DIRTY_T };
        }
        let pool = pool_for(b, self, nb() + 1, 0);
        b.begin();
        division_rows(b, self, w, &rt, &pool, park);
        let rows = b.end();
        b.play(&rows, false);
        b.free_n(&pool);
        prof(b, "i.sweep");
        sweep_fwd_d1(b, self, act, w, &rt);
        let r = self.lb[lb_bits() - RHO_BITS..].to_vec();
        let a1_host = a1_in_la() == 1
            && (masked_rows || W as isize - 1 - w.mx as isize - w.base as isize <= 127);
        // The r and a1 temp: the zero source y on masked layouts (|0> after the rows); on the unmasked layout y is
        // jl[0], so S is emptied (S = [jl != 0]) and serves, then refilled for the sweep's inverse.
        let s_tmp = rt.m.is_none();
        let tmp = if s_tmp { rt.f } else { rt.y };
        if s_tmp {
            s_flip_found(b, self, &rt);
        }
        // jl <- sX - sY - jl in place: rho = act & ((jl mod 8) + #{8, 15, 22, 29 <= jl}) mod 8, a1 = act & [jl < 8]
        let jl = rt.jl.clone();
        for &q in &jl {
            b.x(q);
        }
        add_c_on(b, &jl, sx, true, false, tmp);
        add_c_on(b, &jl, sy, false, true, tmp);
        for i in 0..RHO_BITS {
            act_cx(b, act, jl[i], r[i]);
        }
        for cst in [8isize, 15, 22, 29] {
            ge_auto(b, self, &jl, cst, tmp);
            inc2_auto(b, self, act, tmp, &r);
            ge_erase(b, self, &jl, cst, tmp);
        }
        let a1 = if !a1_host {
            b.alloc()
        } else if masked_rows {
            b.cx(self.la[lb_bits() - 1], self.la[lb_bits() - 2]);
            self.la[lb_bits() - 2]
        } else {
            self.la[lb_bits() - 1]
        };
        let mut lits = act_lits(act);
        lits.extend([(jl[3], true), (jl[4], true)]);
        and_auto(b, self, &lits, a1);
        add_c_on(b, &jl, sy, false, false, tmp);
        add_c_on(b, &jl, sx, true, true, tmp);
        for &q in &jl {
            b.x(q);
        }
        if s_tmp {
            s_flip_found(b, self, &rt);
        }
        for i in 0..RHO_BITS {
            match act {
                Some(a) => {
                    b.push_condition(bits.r[i]);
                    b.cz(a, r[i]);
                    b.pop_condition();
                }
                None => b.z_if(r[i], bits.r[i]),
            }
        }
        b.z_if(a1, bits.a1);
        sweep_bwd_d1(b, self, act, w, &rt);
        prof(b, "i.rows_rev");
        if m1_on {
            rt.m.as_mut().unwrap().t = super::mask::DIRTY_T;
        }
        let pool = pool_for(b, self, nb() + 1, 0);
        b.begin();
        division_rows(b, self, w, &rt, &pool, park);
        let unrows = b.end();
        b.play(&unrows, true);
        b.free_n(&pool);
        rt.free(b);
        let r2 = b.alloc_n(RHO_BITS);
        for i in 0..RHO_BITS {
            match act {
                Some(a) => {
                    b.ccx(a, r[i], r2[i]);
                    b.cx(r2[i], r[i]);
                }
                None => b.swap(r[i], r2[i]),
            }
        }
        let a1 = if a1_host {
            let a = b.alloc();
            b.swap(a1, a);
            if masked_rows {
                b.cx(self.la[lb_bits() - 1], self.la[lb_bits() - 2]);
            }
            a
        } else { a1 };
        (r2, a1)
    }

    /// gf G6b: move LA and LB from offsets on base `from` to offsets on base `to` (off' = off + from - to mod 2^n)
    pub fn rebase(&self, b: &mut B, from: usize, to: usize) {
        if from == to {
            return;
        }
        let m = 1usize << lb_bits();
        let k = (from + m - to) % m;
        add_const_auto(b, self, &self.la, k, false);
        add_const_auto(b, self, &self.lb, k, false);
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

    thread_local! {
        /// gf G6b: the base the tests load and read LA and LB against
        static TB: std::cell::Cell<usize> = std::cell::Cell::new(0);
    }
    fn set_tb(v: usize) {
        TB.with(|c| c.set(v));
    }
    fn tb() -> usize {
        TB.with(|c| c.get())
    }
    /// gf G6b: 8-bit offsets hold only values below the marker when the base is 0
    fn fits(sp: &Spec) -> bool {
        lb_bits() >= 9 || (sp.la < (1usize << (lb_bits() - 1)) && sp.lb < (1usize << (lb_bits() - 1)))
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
            let flip = j < cnt_bits() && (st.cnt >> j) & 1 == 1;
            set(u.y[j], (st.y[j] == 1) != flip);
        }
        let (la, lb) = (st.la - tb(), st.lb - tb());
        for i in 0..lb_bits() {
            set(u.la[i], (la >> i) & 1 == 1);
            set(u.lb[i], (lb >> i) & 1 == 1);
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
        let la = num(&u.la) + tb();
        let cnt = if la == 0 { (!num(&u.cnt)) & ((1 << cnt_bits()) - 1) } else { 0 };
        if la == 0 {
            for v in y.iter_mut().take(cnt_bits()) {
                *v = 1;
            }
        }
        Lanes { x: u.x.iter().map(|&q| g(q)).collect(), y, la, lb: num(&u.lb) + tb(), cnt, par: g(u.par) }
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
            set_tb(0);
            while states.len() < 64 {
                let x = rng.input();
                let mut sp = Spec::new(x);
                let slot = (rng.next() % 260) as usize;
                for _ in 0..slot {
                    sp.fwd();
                }
                if !fits(&sp) {
                    continue;
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
            set_tb(0);
            while states.len() < 64 {
                let x = rng.input();
                let mut sp = Spec::new(x);
                let slot = (rng.next() % 260) as usize;
                for _ in 0..slot {
                    sp.fwd();
                }
                if !fits(&sp) {
                    continue;
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
            .unwrap_or(vec![0, 1, 3, 12, 30, 45, 80, 140, 200, 225, 245, nslots() - 1]);
        let ws = windows();
        let rounds: usize = std::env::var("GREEDYFROG_ROUNDS").ok().and_then(|v| v.parse().ok()).unwrap_or(1);
        let mut rng = Rng(0x7777_1234_5678_9abc);
        for &slot in &list {
            let w = &ws[slot];
            set_tb(w.base);
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
        let ns_slots = nslots();
        let ws = windows();
        let mut b = B::new();
        let mut u = GreedyFrog::alloc(&mut b);
        let mut all_bits = vec![];
        let t0 = b.tof;
        for s in 0..ns_slots {
            if s > 0 {
                u.rebase(&mut b, ws[s - 1].base, ws[s].base);
            }
            all_bits.push(u.fwd_slot(&mut b, &ws[s]));
        }
        let mid_ops = b.ops.len();
        let t1 = b.tof;
        let peak_fwd = b.peak;
        for (s, bits) in all_bits.iter().enumerate().rev() {
            u.inv_slot(&mut b, bits, &ws[s]);
            if s > 0 {
                u.rebase(&mut b, ws[s].base, ws[s - 1].base);
            }
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
            for _ in 0..ns_slots {
                sp.fwd();
            }
            finals.push(Lanes::from_spec(&sp));
            xs.push(x);
        }
        // forward half
        let mut h = sha3::Shake256::default();
        h.update(b"greedyfrog-traversal");
        let mut xof = h.finalize_xof();
        let nbits = 10_000 + 12_000 * ns_slots + 64;
        let mut sim = Simulator::new(b.width() as usize, nbits, &mut xof);
        set_tb(ws[0].base);
        for (s, st) in starts.iter().enumerate() {
            load(&mut sim, &u, s, st);
        }
        sim.apply_iter(b.ops[..mid_ops].iter());
        set_tb(ws[ns_slots - 1].base);
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
        set_tb(ws[0].base);
        for s in 0..64 {
            assert_eq!(read(&sim, &u, s), starts[s], "shot {s}: start not restored");
        }
        eprintln!("greedyfrog traversal: 64 shots exact, round trip clean");
    }
}
