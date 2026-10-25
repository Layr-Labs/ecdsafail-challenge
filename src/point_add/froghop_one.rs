//! froghop-one: froghop-single's one-hop slot machine (one up-and-down excursion of V per Euclid step) on
//! froghop-double's exact-packed registers. Integer model: refmodel_one.rs.
//!
//! D = (r: dividend r_{j-1}, cd: cofactor t_{j-1}), V = (rv: divisor r_j, cv: cofactor target t_{j-2} -> t_j), each
//! W lanes with the value LSB at lane 0 (growing up) and the cofactor LSB at lane W-1 (growing down). V is rotated
//! up by pi against D (aligned lane u + pi holds V-frame lane u). The previous quotient's bits are popped on the
//! up-ramp (cofactor update cv += bit * (cd << pi), the bit erased by [cv >= cd << pi]) while the same ramp searches
//! the alignment of the next division; the division runs on the down-ramp and pushes the quotient bits.
//!
//! Quotient bits live in the register gaps (no stack register). The quotient's first bit is always 1 and is only
//! counted in the depth d. Bit i of the stack (i >= 1, i = 0 is the implicit first bit) sits at lane b + i above the
//! value: during DIV in V's gap (V frame, b the divisor's length), after the step-end swap in D's gap (b the dividend's
//! length), popped top first on the up-ramp. D is not written during OUT; V holds the divisor and its finished
//! cofactor during DIV.
//!
//! One boundary register b (6-bit offset from a per-slot base): the dividend's bit length until the step turns (OUT
//! -> RET, stack empty), the divisor's afterwards. k (5 bits) holds the alignment height (0 before it), which makes
//! the alignment event recoverable (k == pi) and is cleared at the step end against the stack depth; at the turn b
//! converts to the divisor's length, b - k + 1 - dl. Masks derive from B1 = b + [k != 0] pi: the value ladder works on
//! lanes [pi, B1] (its result is not used by aligned OUT shots), the cofactor ladder on lanes > B1 + max(d - 1, 0)
//! (above D's stack), the turn discriminator (source read one lane up) on lanes > B1 - 1 (turning shots have d = 0).
//! A DONE shot keeps its termination stamp in k and the three low depth bits.
//!
//! Slot: S0 frozen counter; S1 pop (scan of D's gap); S2 value ladder P1 (turn flag tt, division bit xd, alignment
//! flag ta); S3 alignment (k = pi, erase ta) and turn (b -> divisor length); S4 step end, push (scan of V's gap),
//! bit 0, swap; S5 cofactor ladder P2; S6 termination and phase update; S7 turn discriminator P3 (erase tt);
//! S8 rotation and pi update.

use super::arith::{and_lits, cswap_regs, dec, down_m, inc, rot2_up, up_m, Dm};
use super::builder::B;
use super::mask::{clear_onehot_dec, dirty_pre, short_pre, skip_pre, ZERO_SRC,mdown_mid, mdown_mid_probe, mup_mid, mup_mid_from, mup_mid_from_repair, mup_mid_repair, mup_mid_spare_masked_from, onehot_scan, s5_rolling_finish, s5_rolling_prefix, top_carry, Lad, Mscr, Src};
use super::modp_double::{gadd, gadd_top_zero};
use crate::circuit::{BitId, OperationType, QubitId, NO_BIT};

pub const W1: usize = 259;
pub const PIB: usize = 5;
pub const HIB: usize = 4; // stored h = pi >> 1; the low parity bit is classical per slot
pub const KB: usize = 5;
pub const DEPB: usize = 6;
/// b (1..=256) is stored as the offset u = b - 1 - base(sigma) in BB bits; base is a per-slot classical constant
/// (193 in the first-step slots, 0 where some shot may be in the last step) that keeps every value the slot decodes
/// within [0, 2^BB)
pub const BB: usize = 6;
pub const FIRST_BASE: usize = 193;
pub const CNTB: usize = 8;
/// scratch: PEAK = 2 W + 256 passenger + 25 state + POOL_1 scratch + reflection bit (POOL_1 15..=18 gives 815..=818).
/// The traversal's high water is 15; the products between a division's two traversals take the rest of the peak as
/// carry pool (POOL_1 + 16 lanes), below the signed-digit compares' 34 lanes from POOL_1 = 17 down (`modp_double::gcmp`
/// folds the lanes past the pool in place) and below c's bit 32 from POOL_1 = 16 down (`add_small_head` adds it apart).
pub const POOL_1: usize = 9;

#[derive(Clone)]
pub struct LayOne {
    pub w: usize,
    pub s: usize,
    /// per slot: lv jw p1lo lc p2hi pb0 pb1 pe0 pe1 fin 0 termon (fin: some shot may be in the last step, b == 1)
    pub rows: Vec<[usize; 12]>,
    pub smax: usize,
    /// slots < f1w: first-step logic (f1 lives in the DONE flag's qubit there)
    pub f1w: usize,
    /// per slot: base of the offset boundary register
    pub base: Vec<usize>,
    pub kmax: usize,
    pub first_termon: usize,
    pub trail_start: usize,
    /// per slot: stack windows (pop lanes of D [q0, q1), push lanes of V [u0, u1), physical)
    pub scan: Vec<[usize; 4]>,
}

/// Clip a scan window [lo, hi) to the lanes j whose offset value j - sh - base lies in [0, 2^BB): a gated scan
/// decodes (offset value, gate) with the gate as the top bit, so a lane outside would match ungated shots.
fn clip_win(lo: usize, hi: usize, base: usize, sh: usize, w: usize) -> (usize, usize) {
    let (l, h) = (lo.max(base + sh), hi.min(w).min(base + sh + (1 << BB)));
    if h > l { (l, h) } else { (0, 0) }
}

impl LayOne {
    pub fn from_text(txt: &str, smax: usize) -> LayOne {
        let mut lines = txt.lines();
        let hdr: Vec<usize> = lines.next().unwrap().split_whitespace().map(|t| t.parse().unwrap()).collect();
        let mut base = vec![];
        let mut scan = vec![];
        let w = hdr[0];
        let rows: Vec<[usize; 12]> = lines
            .filter(|l| !l.trim().is_empty())
            .map(|l| {
                let v: Vec<usize> = l.split_whitespace().map(|t| t.parse().unwrap()).collect();
                let mut r = [0usize; 12];
                r.copy_from_slice(&v[..12]);
                let bs = if v.len() > 12 { v[12] } else { 0 };
                base.push(bs);
                // V probe (lane - 1 decoded), D probe (lane decoded), pop (lane - 1), push (lane - 2)
                let (a, z) = clip_win(r[5], r[6], bs, 1, w);
                r[5] = a;
                r[6] = z;
                let (a, z) = clip_win(r[7], r[8], bs, 0, w);
                r[7] = a;
                r[8] = z;
                scan.push(if v.len() > 16 {
                    let (q0, q1) = clip_win(v[13], v[14], bs, 1, w);
                    let (u0, u1) = clip_win(v[15], v[16], bs, 2, w);
                    [q0, q1, u0, u1]
                } else { [0, 0, 0, 0] });
                r
            })
            .collect();
        assert_eq!(rows.len(), hdr[1]);
        assert_eq!(*base.last().unwrap(), 0, "the last slot must leave b - 1 unshifted");
        let first_termon = rows.iter().position(|r| r[11] != 0).unwrap();
        let trail_start = hdr[1] - 8;
        assert!(rows[trail_start..].iter().all(|r| r[0] == 0));
        LayOne { w: hdr[0], s: hdr[1], rows, smax, f1w: hdr[2], base,
                 kmax: *hdr.get(3).unwrap_or(&25), first_termon, trail_start, scan }
    }
}

/// Scratch hand-out for one slot (LIFO). Every qubit goes back |0>.
pub struct Pl {
    owner: std::collections::BTreeMap<QubitId, &'static std::panic::Location<'static>>,
    free: Vec<QubitId>,
    pub n: usize,
    pub hw: usize,
    pub cur: &'static str,
    pub hw_at: &'static str,
    pub peaks: std::collections::BTreeMap<&'static str, usize>,
}

impl Pl {
    fn new(pool: &[QubitId]) -> Pl {
        let mut free = pool.to_vec();
        free.reverse();
        Pl { owner: Default::default(), free, n: pool.len(), hw: 0, cur: "", hw_at: "", peaks: Default::default() }
    }
    #[track_caller]
    fn get(&mut self) -> QubitId {
        let q = self.free.pop().unwrap_or_else(|| panic!("froghop-one scratch pool exhausted at {}", self.cur));
        let used = self.n - self.free.len();
        if CENSUS_THR.with(|c| c.get()) != usize::MAX {
            self.owner.insert(q, std::panic::Location::caller());
            census_hit(self, used);
        }
        let e = self.peaks.entry(self.cur).or_insert(0);
        *e = (*e).max(used);
        if self.n - self.free.len() > self.hw {
            self.hw = self.n - self.free.len();
            self.hw_at = self.cur;
        }
        q
    }
    fn stage(&mut self, name: &'static str) {
        self.cur = name;
        let used = self.n - self.free.len();
        let e = self.peaks.entry(name).or_insert(0);
        *e = (*e).max(used);
    }
    #[track_caller]
    fn get_n(&mut self, n: usize) -> Vec<QubitId> {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n { v.push(self.get()); }
        v
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
}

/// Test-only negative-control switches (`A1B_MUT=<name>`); a constant `false` in the graded build.
#[cfg(test)]
pub(crate) fn a1b_mut(name: &str) -> bool {
    std::env::var("A1B_MUT").map(|v| v.split(',').any(|m| m == name)).unwrap_or(false)
}
#[cfg(not(test))]
#[inline(always)]
pub(crate) fn a1b_mut(_: &str) -> bool { false }

thread_local! {
    pub static CENSUS: std::cell::RefCell<std::collections::BTreeMap<String, usize>> = Default::default();
    pub static CENSUS_TAG: std::cell::RefCell<String> = Default::default();
    pub static CENSUS_THR: std::cell::Cell<usize> = std::cell::Cell::new(usize::MAX);
}
fn census_hit(pl: &Pl, used: usize) {
    let thr = CENSUS_THR.with(|c| c.get());
    if used < thr { return; }
    let held: std::collections::BTreeSet<QubitId> = pl.owner.keys().copied().filter(|q| !pl.free.contains(q)).collect();
    let mut lines: Vec<u32> = held.iter().map(|q| pl.owner[q].line()).collect();
    lines.sort();
    let tag = CENSUS_TAG.with(|t| t.borrow().clone());
    let key = format!("{} {} used {} held {:?}", pl.cur, tag, used, lines);
    CENSUS.with(|c| *c.borrow_mut().entry(key).or_insert(0) += 1);
}

/// As `modp_double::gadd` (t += a mod 2^n, carries as logical ANDs in `g`), but the top addend bit is zero and the
/// carry into the top lane is never stored: it is toggled straight into t[n-1] with one CCX on the lane-(n-2) carry
/// form, MAJ(t, q, c) = c ^ (t ^ c)(q ^ c). Same Toffoli count as `gadd` (the stored carry's AND was one Toffoli and
/// its measured uncompute none); `g` needs n-2 clean lanes instead of n-1. Lane A1b.
pub(crate) fn gadd_top1(b: &mut B, t: &[QubitId], a: &[Option<QubitId>], g: &[QubitId]) {
    let n = t.len();
    assert!(n >= 2 && a.len() == n && g.len() >= n - 2);
    assert!(a[n - 1].is_none());
    let mut carry: Vec<Option<QubitId>> = vec![None; n];
    let mut gi = 0;
    for i in 0..n - 2 {
        carry[i + 1] = match (a[i], carry[i]) {
            (None, None) => None,
            (Some(q), None) => {
                b.and_c(t[i], q, g[gi]); gi += 1; Some(g[gi - 1])
            }
            (None, Some(c)) => {
                b.and_c(t[i], c, g[gi]); gi += 1; Some(g[gi - 1])
            }
            (Some(q), Some(c)) => {
                b.cx(c, t[i]); b.cx(c, q);
                b.and_c(t[i], q, g[gi]);
                b.cx(c, q); b.cx(c, g[gi]);
                gi += 1; Some(g[gi - 1])
            }
        };
    }
    // t[n-1] ^= carry out of lane n-2 (a[n-1] = 0, so that is the whole top sum bit)
    let i = n - 2;
    match (a[i], carry[i]) {
        (None, None) => {}
        (Some(q), None) => b.ccx(t[i], q, t[n - 1]),
        (None, Some(c)) => b.ccx(t[i], c, t[n - 1]),
        (Some(q), Some(c)) => {
            // t[i] keeps t ^ c until its sum write below
            b.cx(c, t[i]); b.cx(c, q);
            b.ccx(t[i], q, t[n - 1]);
            b.cx(c, q);
            if !a1b_mut("top1") { b.cx(c, t[n - 1]); }
        }
    }
    for i in (0..n - 1).rev() {
        if i + 1 < n - 1 {
            if let Some(gq) = carry[i + 1] {
                match (a[i], carry[i]) {
                    (Some(q), None) => b.and_u(t[i], q, gq),
                    (None, Some(c)) => b.and_u(t[i], c, gq),
                    (Some(q), Some(c)) => {
                        b.cx(c, gq); b.cx(c, q);
                        b.and_u(t[i], q, gq);
                        b.cx(c, q);
                    }
                    (None, None) => unreachable!(),
                }
            }
        }
        match (a[i], carry[i]) {
            (None, None) => {}
            (Some(q), None) => b.cx(q, t[i]),
            (None, Some(c)) => b.cx(c, t[i]),
            (Some(q), Some(_)) => b.cx(q, t[i]),
        }
    }
}

/// An addend bit for `gadd_top1_jit`: none, a wire, or the AND of two wires.
#[derive(Clone, Copy)]
pub(crate) enum Ad {
    No,
    Q(QubitId),
    And(QubitId, QubitId),
}

/// `gadd_top1` (t += a mod 2^n, a[n-1] = 0, n-2 carry lanes) where AND addend bits are made just in time in the one
/// clean lane `tmp` and erased (measured) right after their use; a bit below lane n-2 is made twice (carry and
/// return pass). Cost: `gadd_top1`'s Toffolis + one AND per AND bit (+ one more per AND bit below n-2); scratch
/// n-1 lanes instead of n-2 + (number of AND bits). Lane A1b.
pub(crate) fn gadd_top1_jit(b: &mut B, t: &[QubitId], a: &[Ad], g: &[QubitId], tmp: QubitId) {
    let n = t.len();
    assert!(n >= 2 && a.len() == n && g.len() >= n - 2);
    assert!(matches!(a[n - 1], Ad::No));
    let mat = |b: &mut B, x: Ad| -> Option<QubitId> {
        match x {
            Ad::No => None,
            Ad::Q(q) => Some(q),
            Ad::And(p, q) => {
                b.and_c(p, q, tmp);
                Some(tmp)
            }
        }
    };
    let unmat = |b: &mut B, x: Ad| {
        if let Ad::And(p, q) = x { b.and_u(p, q, tmp); }
    };
    let mut carry: Vec<Option<QubitId>> = vec![None; n];
    let mut gi = 0;
    for i in 0..n - 2 {
        let ai = mat(b, a[i]);
        carry[i + 1] = match (ai, carry[i]) {
            (None, None) => None,
            (Some(q), None) => {
                b.and_c(t[i], q, g[gi]); gi += 1; Some(g[gi - 1])
            }
            (None, Some(c)) => {
                b.and_c(t[i], c, g[gi]); gi += 1; Some(g[gi - 1])
            }
            (Some(q), Some(c)) => {
                b.cx(c, t[i]); b.cx(c, q);
                b.and_c(t[i], q, g[gi]);
                b.cx(c, q); b.cx(c, g[gi]);
                gi += 1; Some(g[gi - 1])
            }
        };
        unmat(b, a[i]);
    }
    // lane n-2: toggle the carry out into t[n-1], then its own sum bit
    {
        let i = n - 2;
        let ai = mat(b, a[i]);
        match (ai, carry[i]) {
            (None, None) => {}
            (Some(q), None) => {
                b.ccx(t[i], q, t[n - 1]);
                b.cx(q, t[i]);
            }
            (None, Some(c)) => {
                b.ccx(t[i], c, t[n - 1]);
                b.cx(c, t[i]);
            }
            (Some(q), Some(c)) => {
                b.cx(c, t[i]); b.cx(c, q);
                b.ccx(t[i], q, t[n - 1]);
                b.cx(c, q); b.cx(c, t[n - 1]);
                if !a1b_mut("jit") { b.cx(q, t[i]); }
            }
        }
        unmat(b, a[i]);
    }
    for i in (0..n - 2).rev() {
        let ai = mat(b, a[i]);
        if let Some(gq) = carry[i + 1] {
            match (ai, carry[i]) {
                (Some(q), None) => b.and_u(t[i], q, gq),
                (None, Some(c)) => b.and_u(t[i], c, gq),
                (Some(q), Some(c)) => {
                    b.cx(c, gq); b.cx(c, q);
                    b.and_u(t[i], q, gq);
                    b.cx(c, q);
                }
                (None, None) => unreachable!(),
            }
        }
        match (ai, carry[i]) {
            (None, None) => {}
            (Some(q), None) => b.cx(q, t[i]),
            (None, Some(c)) => b.cx(c, t[i]),
            (Some(q), Some(_)) => b.cx(q, t[i]),
        }
        unmat(b, a[i]);
    }
}

/// target ^= AND of literals (n >= 3; a CCX onto the target, the chain from the pool and measured away). Lane A1b.
fn xor_lits(b: &mut B, pl: &mut Pl, lits: &[(QubitId, bool)], target: QubitId) {
    let n = lits.len();
    assert!(n >= 3);
    let m = pl.get();
    let anc = pl.get_n(n - 3);
    let r = and_lits(b, &lits[..n - 1], m, &anc);
    b.play(&r, false);
    let (q, neg) = lits[n - 1];
    if neg { b.x(q); }
    b.ccx(m, q, target);
    if neg { b.x(q); }
    b.play(&r, true);
    pl.put_n(&anc);
    pl.put(m);
}

/// Decoder prefix form (lane A1c): `pre` are the lanes handed out; `skip` drops the top level (mask::skip_pre, one
/// lane fewer), `short` the bottom one (mask::short_pre).
fn dpre(pre: &[QubitId], skip: bool, short: bool) -> Vec<QubitId> {
    let v = if skip { skip_pre(pre) } else { pre.to_vec() };
    if short { short_pre(&v) } else { v }
}

/// Controlled increment with the top carry toggled straight into the top bit (lane A1c): n - 2 carry lanes instead
/// of `arith::inc`'s n - 1, same n - 1 Toffoli.
fn inc_top1(b: &mut B, ctrl: QubitId, bits: &[QubitId], anc: &[QubitId]) {
    let n = bits.len();
    if n == 0 { return; }
    if n == 1 { b.cx(ctrl, bits[0]); return; }
    assert!(anc.len() >= n - 2);
    let mut prev = ctrl;
    for i in 1..n - 1 {
        b.and_c(prev, bits[i - 1], anc[i - 1]);
        prev = anc[i - 1];
    }
    if !a1b_mut("inctop") { b.ccx(prev, bits[n - 2], bits[n - 1]); }
    for i in (1..n - 1).rev() {
        b.cx(anc[i - 1], bits[i]);
        let p = if i == 1 { ctrl } else { anc[i - 2] };
        b.and_u(p, bits[i - 1], anc[i - 1]);
    }
    b.cx(ctrl, bits[0]);
}

/// out ^= AND of literals (qubit, negated?), transient chain from the pool (n >= 2). `undo`: measurement-uncompute
/// (out must hold exactly that AND).
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

pub struct FhOne {
    pub d: Vec<QubitId>,
    pub v: Vec<QubitId>,
    pub pi: Vec<QubitId>,
    pub k: Vec<QubitId>,
    pub fo: QubitId,
    pub fd: QubitId,
    /// RET has no qubit: fr = 1 ^ fo ^ fd ^ fnn (one-hot phase flags); in the first-step slots fnn's qubit holds f1
    pub fnn: QubitId,
    /// d6 = logical depth + 31 (dep[5] = [d != 0], dep[..5] = d - 1 for d >= 1)
    pub dep: Vec<QubitId>,
    pub al_s: QubitId, // persistent [k != 0]
    /// b - 1
    pub bq: Vec<QubitId>,
    /// swap parity (starts as the caller's reflection bit)
    pub par: QubitId,
    pub pool: Vec<QubitId>,
    pub gp: Vec<QubitId>,
    /// passenger lanes lent as dirty ancillas
    pub dirty: Vec<QubitId>,
    pub hw: usize,
    pub hw_at: &'static str,
    pub marks: Vec<(&'static str, usize)>,
    pub peaks: std::collections::BTreeMap<&'static str, usize>,
    pub(crate) d1_enabled: bool,
    pub(crate) d1phi_z0: bool,
    pub(crate) inverse_boundaries: Vec<usize>,
    d1_record: bool,
    d1_split: Option<D1Split>,
    d1_z0_split: Option<D1Z0Split>,
    pub(crate) s5_carry_bits: Vec<BitId>,
}

struct D1Split {
    cut: usize,
    dl: QubitId,
    btt: Vec<QubitId>,
    pre: Vec<QubitId>,
    vref: Vec<QubitId>,
    lo: usize,
    hi: usize,
    off: isize,
}

struct D1Z0Split {
    cut: usize,
    z0: QubitId,
    lits: Vec<(QubitId, bool)>,
    m: QubitId,
    anc: QubitId,
}

/// Plain remains the independent specification. Only the paired traversal
/// carries measurement debt; HMR must never enter a reversible recording.
#[derive(Clone, Copy)]
pub(crate) enum SlotMode {
    Plain,
    ForwardGhost { receipt: BitId, dl_receipt: Option<BitId>, extras: Option<[BitId; 16]> },
    RecordInverseWithRepair { receipt: BitId, dl_receipt: Option<BitId>, extras: Option<[BitId; 16]> },
}

/// Discharge a forward value after its final consumer. The inverse recording
/// regenerates that value and applies the phase fix before undoing its users.
fn extra_debt(b: &mut B, q: QubitId, mode: SlotMode, site: usize) -> bool {
    match mode {
        SlotMode::ForwardGhost { extras: Some(bits), .. } => {
            b.hmr_to(q, bits[site]);
            true
        }
        SlotMode::RecordInverseWithRepair { extras: Some(bits), .. } => {
            b.z_if(q, bits[site]);
            false
        }
        _ => false,
    }
}

#[must_use = "TT measurement debts must be consumed by their paired inverse"]
pub struct GhostTrace {
    pub(crate) maps: Vec<Vec<QubitId>>,
    pub(crate) receipts: Vec<BitId>,
    pub(crate) hmr_sites: Vec<usize>,
    dl_receipts: Vec<BitId>,
    dl_hmr_sites: Vec<usize>,
    extra_receipts: Vec<[BitId; 16]>,
    extra_hmr_sites: Vec<[usize; 16]>,
    s5_carry_receipts: Vec<Vec<BitId>>,
    s5_carry_hmr_sites: Vec<Vec<usize>>,
    d1_receipts: Vec<BitId>,
    owners: Vec<QubitId>,
    exit_v: Vec<QubitId>,
}

impl FhOne {
    pub fn alloc(b: &mut B, d: Vec<QubitId>, v: Vec<QubitId>, lay: &LayOne, par: QubitId, dirty: Vec<QubitId>,
                 gpool: usize) -> FhOne {
        FhOne::alloc_with_pool(b, d, v, lay, par, dirty, gpool, POOL_1)
    }

    /// `alloc` with an explicit scratch-pool size (lane A1c: tests run two pool sizes side by side).
    pub(crate) fn alloc_with_pool(b: &mut B, d: Vec<QubitId>, v: Vec<QubitId>, _lay: &LayOne, par: QubitId,
                                  dirty: Vec<QubitId>, gpool: usize, npool: usize) -> FhOne {
        let mut q = || b.alloc();
        let (fo, fd, fnn) = (q(), q(), q());
        let pi = b.alloc_n(HIB);
        let k = b.alloc_n(KB);
        let dep = b.alloc_n(DEPB);
        let bq = b.alloc_n(BB);
        let al_s = b.alloc();
        let pool = b.alloc_n(npool);
        let gp = b.alloc_n(gpool);
        FhOne { d, v, pi, k, fo, fd, fnn, dep, al_s, bq, par, pool, gp, dirty, hw: 0, hw_at: "", marks: vec![], peaks: Default::default(), d1_enabled: true, d1phi_z0: true, inverse_boundaries: vec![], d1_record: false, d1_split: None, d1_z0_split: None, s5_carry_bits: Vec::new() }
    }

    /// every qubit the traversal allocated (not D, V or par)
    pub fn all_meta(&self) -> Vec<QubitId> {
        let mut v = self.pool.clone();
        v.extend(&self.gp);
        v.extend(&self.pi);
        v.extend(&self.k);
        v.extend([self.fo, self.fd, self.fnn]);
        v.extend(&self.dep);
        v.push(self.al_s);
        v.extend(&self.bq);
        v
    }

    /// DONE stamp: k and the three low depth bits (k == 0 and d6 == 31 at the termination, and neither is read for a
    /// DONE shot afterwards). The depth bits hold the stamp's high bits complemented until `home_and_consts`.
    pub fn cnt(&self) -> Vec<QubitId> {
        let mut v = self.k.clone();
        v.extend(&self.dep[..CNTB - KB]);
        v
    }

    /// Initial state: D = (r = p, cd = 0), V = (rv = x' already in V lanes [1, 257), cv = 1 at V lane 0), b = 256,
    /// pi = 1, OUT, f1 = 1 (in fnn's qubit).
    pub fn init(&mut self, b: &mut B, lay: &LayOne) {
        let pp = super::refmodel_one::p();
        for i in 0..256 {
            if pp.bit(i) {
                b.x(self.d[i]);
            }
        }
        b.x(self.v[0]); // V-frame lane W-1 (cv bit 0) sits at aligned lane 0 when pi = 1
        let u0 = 255 - lay.base[0]; // b - 1 = 255
        assert!(u0 < 1 << BB);
        for (i, &q) in self.bq.iter().enumerate() {
            if (u0 >> i) & 1 == 1 {
                b.x(q);
            }
        }
        b.x(self.fo);
        b.x(self.fnn); // f1
        for &q in self.dep.iter().take(5) { b.x(q); } // d6 = logical depth + 31
    }

    /// Scratch-saving level of this pool (lane A1b): 0 at POOL_1 >= 15 (the 815..818 streams, byte for byte), 1 at
    /// POOL_1 = 14 (bq adder without its top carry lane, S2's tt computed after the ladder, S4's z0 erased right
    /// after its only consumer), 2 at 13 (short decoders where g / al / kq are held, S5's al addend just in time,
    /// S4's dv / pu in fd's qubit), 3 at 12 (short decoders everywhere, g and al not held: k0 carries [b == 1],
    /// just-in-time adds at S2 / S3, in-place first-step carry, dirty-ancilla kq term, one S7 bank lane in the
    /// first-step slots), 4 at 11 (tt parked S3..S6, dirty pi decoder in S2), 5 at 10 (lane A1c: po erased exactly at
    /// S1's end as fo & (dep[5] | be) and never held through S2..S5, S7's constant-0 source lane takes no qubit, S7's
    /// closing bq_pi just in time).
    pub fn lean(&self) -> usize {
        15usize.saturating_sub(self.pool.len())
    }

    /// bq += pi (sub = false) or bq -= pi (sub = true), mod 2^BB, everywhere (g = None) or where g = 1.
    /// `inverse` plays the exact inverse. Scratch is transient.
    fn bq_pi(&self, b: &mut B, pl: &mut Pl, g: Option<QubitId>, sub: bool, inverse: bool, p: bool) {
        self.bq_pi_form(b, pl, g, sub, inverse, p, false)
    }

    /// `bq_pi` with `jit`: (lean >= 1, g given) the addend bits g & pi[i] are made just in time in one lane
    /// (`gadd_top1_jit`, 5 scratch lanes instead of 8, +3 Toffoli). Same function.
    fn bq_pi_form(&self, b: &mut B, pl: &mut Pl, g: Option<QubitId>, sub: bool, inverse: bool, p: bool, jit: bool) {
        let top1 = BB == 6 && self.lean() >= 1;
        if top1 && jit && g.is_some() {
            let gq = g.unwrap();
            let tmp = pl.get();
            let carries = pl.get_n(BB - 2);
            let t = &self.bq;
            b.begin();
            if sub {
                for &q in t { b.x(q); }
            }
            let mut a: Vec<Ad> = Vec::with_capacity(BB);
            a.push(if p { Ad::Q(gq) } else { Ad::No });
            for i in 0..HIB { a.push(Ad::And(gq, self.pi[i])); }
            a.resize(BB, Ad::No);
            gadd_top1_jit(b, t, &a, &carries, tmp);
            if sub {
                for &q in t { b.x(q); }
            }
            let rec = b.end();
            b.play(&rec, inverse);
            pl.put_n(&carries);
            pl.put(tmp);
            return;
        }
        let addend = if g.is_some() { pl.get_n(HIB) } else { Vec::new() };
        let one = if p && g.is_none() { Some(pl.get()) } else { None };
        let carries = pl.get_n(if BB == 7 || top1 { BB - 2 } else { BB - 1 });
        let t = &self.bq;
        b.begin();
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        if let Some(q) = one { b.x(q); }
        let mut a: Vec<Option<QubitId>> = Vec::with_capacity(BB);
        a.push(if p { g.or(one) } else { None });
        for i in 0..HIB {
            if let Some(gq) = g {
                b.and_c(gq, self.pi[i], addend[i]);
                a.push(Some(addend[i]));
            } else {
                a.push(Some(self.pi[i]));
            }
        }
        a.resize(BB, None);
        if BB == 7 { gadd_top_zero(b, t, &a, &carries); }
        else if top1 { gadd_top1(b, t, &a, &carries); }
        else { gadd(b, t, &a, &carries); }
        if let Some(gq) = g {
            for i in (0..HIB).rev() {
                b.and_u(gq, self.pi[i], addend[i]);
            }
        }
        if let Some(q) = one { b.x(q); }
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        let rec = b.end();
        b.play(&rec, inverse);
        pl.put_n(&carries);
        if let Some(q) = one { pl.put(q); }
        pl.put_n(&addend);
    }

    fn negk(&self) -> Vec<(QubitId, bool)> {
        self.k.iter().map(|&q| (q, true)).collect()
    }

    /// bq += src (sub = false) or bq -= src, mod 2^BB, for a 5-bit register src, everywhere (g = None) or where g = 1.
    fn bq_reg(&self, b: &mut B, pl: &mut Pl, src: &[QubitId], g: Option<QubitId>, sub: bool, inverse: bool) {
        assert_eq!(src.len(), PIB);
        let c0 = pl.get();
        let tmp = pl.get();
        let anc = pl.get_n(BB - PIB - 1);
        let t = &self.bq;
        b.begin();
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        let mode = match g {
            Some(q) => Dm::Cond(q),
            None => Dm::Sum,
        };
        let u = up_m(b, &t[..PIB], src, c0, false);
        let dd = down_m(b, &t[..PIB], src, c0, mode, false);
        b.play(&u, false);
        let carry = src[PIB - 1];
        let ctl = match g {
            Some(gq) => {
                b.and_c(gq, carry, tmp);
                tmp
            }
            None => carry,
        };
        inc(b, ctl, &t[PIB..], &anc);
        if let Some(gq) = g {
            b.and_u(gq, carry, tmp);
        }
        b.play(&dd, false);
        if sub {
            for &q in t {
                b.x(q);
            }
        }
        let rec = b.end();
        b.play(&rec, inverse);
        pl.put_n(&anc);
        pl.put(tmp);
        pl.put(c0);
    }

    /// fd <-> fr in fd's qubit (fd ^= 1 ^ fo ^ fnn); self-inverse, needs one-hot phase flags.
    fn fr_swap(&self, b: &mut B, f1on: bool) {
        b.cx(self.fo, self.fd);
        if !f1on {
            b.cx(self.fnn, self.fd);
        }
        b.x(self.fd);
    }

    pub fn slot(&mut self, b: &mut B, lay: &LayOne, sigma: usize) {
        self.slot_mode(b, lay, sigma, SlotMode::Plain);
    }

    pub(crate) fn slot_mode(&mut self, b: &mut B, lay: &LayOne, sigma: usize, mode: SlotMode) {
        if sigma >= lay.trail_start {
            let row = lay.rows[sigma];
            assert_eq!((row[0], row[3], row[5], row[6], row[7], row[8], row[9], row[11]),
                (0, W1, 0, 0, 0, 0, 0, 0), "trailing row can act");
            if sigma % 2 == 0 { self.v.rotate_right(1); } else { self.v.rotate_left(1); }
            let one = self.pool[0];
            b.x(one);
            if sigma % 2 == 0 {
                inc(b, one, &self.pi, &self.pool[1..HIB]);
            } else {
                dec(b, one, &self.pi, &self.pool[1..HIB]);
            }
            b.x(one);
            match mode {
                SlotMode::ForwardGhost { receipt, dl_receipt, extras } => {
                    let q = self.pool[0];
                    b.hmr_to(q, receipt);
                    if let Some(bit) = dl_receipt { b.hmr_to(q, bit); }
                    if let Some(bits) = extras { for bit in bits { b.hmr_to(q, bit); } }
                }
                SlotMode::RecordInverseWithRepair { receipt, dl_receipt, extras } => {
                    let q = self.pool[0];
                    b.z_if(q, receipt);
                    if let Some(bit) = dl_receipt { b.z_if(q, bit); }
                    if let Some(bits) = extras { for bit in bits { b.z_if(q, bit); } }
                }
                SlotMode::Plain => {}
            }
            return;
        }
        if sigma == 0 {
            self.v.rotate_right(1);
            b.x(self.pi[0]);
            match mode {
                SlotMode::ForwardGhost { receipt, dl_receipt, extras } => {
                    let q = self.pool[0];
                    b.hmr_to(q, receipt);
                    if let Some(bit) = dl_receipt { b.hmr_to(q, bit); }
                    if let Some(bits) = extras {
                        for bit in bits { b.hmr_to(q, bit); }
                    }
                }
                SlotMode::RecordInverseWithRepair { receipt, dl_receipt, extras } => {
                    let q = self.pool[0];
                    b.z_if(q, receipt);
                    if let Some(bit) = dl_receipt { b.z_if(q, bit); }
                    if let Some(bits) = extras {
                        for bit in bits { b.z_if(q, bit); }
                    }
                }
                SlotMode::Plain => {}
            }
            return;
        }
        let w = W1;
        let row = lay.rows[sigma];
        let (lv, jw, p1lo, lc, p2hi, pb0, pb1, pe0, pe1, fin, termon) = (row[0], row[1], row[2], row[3], row[4],
            row[5], row[6].min(w), row[7], row[8].min(w), row[9] != 0, row[11] != 0);
        let first_fin = lay.rows.iter().position(|r| r[9] != 0).unwrap_or(lay.s);
        let cached_b1 = sigma < first_fin;
        let p = sigma % 2 == 0; // pi's known low bit at this slot boundary
        let f1on = sigma < lay.f1w;
        assert!(!(f1on && termon));
        // pi moves by +-1 on every shot every slot and is 1 at slot 0: pi == 0 (step ends, the swap) only on odd slots
        let odd = sigma % 2 == 1;
        let mut pl = Pl::new(&self.pool);
        if CENSUS_THR.with(|c| c.get()) != usize::MAX { CENSUS_TAG.with(|t| *t.borrow_mut() = format!("[{} odd{} cached{} fin{} term{} f1{} p2{}]", match mode { SlotMode::Plain => "P", SlotMode::ForwardGhost{..} => "F", SlotMode::RecordInverseWithRepair{..} => "R" }, odd as u8, cached_b1 as u8, fin as u8, termon as u8, f1on as u8, (lc < w) as u8)); }
        let lean = self.lean();
        // lean >= 6 (lane A1c, POOL_1 = 9): every retained / short bq decoder drops its top level (mask::skip_pre), S3's
        // increment drops its top carry lane, S1's cached bq_pi is just in time
        let skip6 = lean >= 6;
        let (fo, fd, fnn) = (self.fo, self.fd, self.fnn);
        let f1 = fnn; // meaningful only in the first-step slots
        let negpi: Vec<(QubitId, bool)> = self.pi.iter().map(|&q| (q, true)).collect();
        let cnt: Vec<QubitId> = self.cnt().to_vec();
        // stack windows (already clipped to the decodable lanes by LayOne)
        let [pop0, pop1, push0, push1] = lay.scan[sigma];
        // dep[..5] = d - 1 wherever d >= 1 (every popping or pushing shot)
        let dep5: Vec<QubitId> = self.dep[..PIB].to_vec();

        // offset register: u += base(sigma - 1) - base(sigma)
        let base = lay.base[sigma] as isize;
        let e1_fuse_lo = pb0.max(p1lo).max((base + 1) as usize);
        let e1_fuse_hi = pb1.min(lv.saturating_sub(1)).min((base + 65) as usize);
        if sigma > 0 {
            let c = (lay.base[sigma - 1] as isize - base).rem_euclid(1 << BB) as usize;
            self.bq_add_const(b, &mut pl, c);
        }
        if sigma == first_fin {
            // The final-step path uses the old b form. Convert once from B1.
            let (al, alr) = self.al_on(b, &mut pl, false);
            self.bq_pi(b, &mut pl, Some(al), true, false, p);
            self.al_off(b, &mut pl, false, al, alr);
        }
        if fin || termon {
            assert_eq!(base, 0, "slot {sigma}: [b == 1] needs base 0");
        }
        if f1on { assert_eq!(base, FIRST_BASE as isize, "first-step base"); }

        // S0 frozen counter (DONE shots)
        self.marks.push(("S0", b.mark_pos()));
        pl.stage("S0");
        // DONE stores its termination timestamp once, in S6.

        // S1 pop: po = fo & (dep != 0); the popped bit lands in be.
        self.marks.push(("S1", b.mark_pos()));
        pl.stage("S1");
        let mut po = pl.get();
        let be = pl.get();
        // lean >= 5 (lane A1c): po is not held past S1. The depth is decremented first, the final pop's implicit top 1
        // goes into be at once (was S4), the scan runs only for d >= 2 (the last pop's lane b is not touched), and
        // then po = fo & (dep[5] | be) holds on every input (be starts |0>), so po is erased exactly here.
        let po_gone = lean >= 5;
        {
            let nz = pl.get();
            b.x(nz);
            b.cx(self.dep[5], nz); // nz = [logical depth == 0]
            b.x(nz);
            b.and_c(fo, nz, po);
            b.x(nz);
            if !extra_debt(b, nz, mode, 7) {
                b.cx(self.dep[5], nz);
                b.x(nz);
            }
            pl.put(nz);
            if po_gone {
                let anc = pl.get_n(DEPB - 1);
                dec(b, po, &self.dep, &anc);
                pl.put_n(&anc);
                // the last pop (d was 1, now 0) supplies the implicit top 1
                b.x(self.dep[5]);
                if !a1b_mut("c5fix") { b.ccx(po, self.dep[5], be); }
                b.x(self.dep[5]);
                // d >= 2 (dep[5] = 1 after the decrement): the stack top at lane b + d_old - 1 = (bq + dep5) + 2 + base,
                // decoded as the 8-bit value bq ++ dep[5] ++ po; lanes below base + 2 decode to gate-0 codes
                let lo = pop0.max(base as usize + 2);
                if pop1 > lo {
                    if cached_b1 { self.bq_pi_form(b, &mut pl, Some(self.al_s), true, false, p, skip6); }
                    self.bq_reg(b, &mut pl, &dep5, None, false, false);
                    let mut bpo = self.bq.clone();
                    bpo.push(self.dep[5]);
                    bpo.push(po);
                    let pre = pl.get_n(BB + 1);
                    let dref = self.d.clone();
                    let off = 3 * (1isize << BB) - 2 - base - isize::from(a1b_mut("c5gate"));
                    onehot_scan(b, &bpo, &pre, lo, pop1, off, |b, j, o| {
                        b.cswap(o, be, dref[j]);
                    });
                    pl.put_n(&pre);
                    self.bq_reg(b, &mut pl, &dep5, None, false, true);
                    if cached_b1 { self.bq_pi_form(b, &mut pl, Some(self.al_s), true, true, p, skip6); }
                }
                // po == fo & !(!dep[5] & !be): measured away (one Toffoli for the OR term)
                let m = pl.get();
                b.x(self.dep[5]);
                b.x(be);
                b.and_c(self.dep[5], be, m);
                b.x(be);
                b.x(self.dep[5]);
                if !a1b_mut("c5erase") { b.x(m); }
                b.and_u(fo, m, po);
                if !a1b_mut("c5erase") { b.x(m); }
                b.x(self.dep[5]);
                b.x(be);
                b.and_u(self.dep[5], be, m);
                b.x(be);
                b.x(self.dep[5]);
                pl.put(m);
                // S5's po receipt channel (site 2) on the now clean lane
                let _ = extra_debt(b, po, mode, 2);
                pl.put(po);
                po = QubitId(u64::MAX);
            }
            // the stack top (bit d - 1) sits in D's gap at lane b + d - 1 (b: the dividend's length through OUT); the
            // last pop (d = 1, the implicit first bit) matches the empty lane b.  bq = b - 1 + d - 1 at the scan.
            if !po_gone && pop1 > pop0 {
                if cached_b1 { self.bq_pi(b, &mut pl, Some(self.al_s), true, false, p); }
                self.bq_reg(b, &mut pl, &dep5, None, false, false);
                let mut bpo = self.bq.clone();
                bpo.push(po);
                let pre = pl.get_n(BB);
                let dref = self.d.clone();
                onehot_scan(b, &bpo, &pre, pop0, pop1, (1isize << BB) - 1 - base, |b, j, o| {
                    b.cswap(o, be, dref[j]);
                });
                pl.put_n(&pre);
                self.bq_reg(b, &mut pl, &dep5, None, false, true);
                if cached_b1 { self.bq_pi(b, &mut pl, Some(self.al_s), true, true, p); }
            }
            if !po_gone {
                let anc = pl.get_n(DEPB - 1);
                dec(b, po, &self.dep, &anc);
                pl.put_n(&anc);
            }
        }

        // S2 value ladder P1 over lanes [0, lv), active [pi, B1]: xd = division bit, tt = OUT turn, ta = alignment
        self.marks.push(("S2", b.mark_pos()));
        pl.stage("S2");
        let xd = pl.get();
        // lean >= 1: tt is taken and written after the ladder (neither of its terms is read before S3)
        let mut tt = if lean >= 1 { QubitId(u64::MAX) } else { pl.get() };
        let ta = pl.get();
        let mut e1_hold_slot = None;
        {
            // RXD: RET at pi == k-1 always writes quotient bit 1. Compute
            // this term before S2 so the top value edge need not reach it.
            // For odd pi, compare (k >> 1)-1 with h; al_s excludes k=0,
            // whose wrapped high bits would otherwise alias pi=31.
            {
                let one = pl.get();
                b.x(one);
                if p {
                    let anc = pl.get_n(HIB - 1);
                    dec(b, one, &self.k[1..], &anc);
                    pl.put_n(&anc);
                }
                for i in 0..HIB { b.cx(self.pi[i], self.k[i + 1]); }
                self.fr_swap(b, f1on); // fd temporarily holds fr
                let mut lits = vec![(fd, false), (self.k[0], p)];
                lits.extend(self.k[1..].iter().map(|&q| (q, true)));
                if p { lits.push((self.al_s, false)); }
                and_into(b, &mut pl, &lits, xd, false);
                self.fr_swap(b, f1on);
                for i in 0..HIB { b.cx(self.pi[i], self.k[i + 1]); }
                if p {
                    let anc = pl.get_n(HIB - 1);
                    inc(b, one, &self.k[1..], &anc);
                    pl.put_n(&anc);
                }
                b.x(one);
                pl.put(one);
            }
            // Aligned OUT with an empty quotient stack turns regardless of
            // the S2 comparison. Unaligned OUT receives the ta term below.
            if lean == 0 {
                and_into(b, &mut pl, &[(fo, false), (self.dep[5], true), (self.al_s, false)], tt, false);
            }
            // g = fo & !al (OUT, not aligned, not the last step), kept through the ladder in place of al
            // (al = !g on every shot: RET / DIV shots are aligned and DONE shots have b == 1)
            // lean >= 3, non-cached slots: g = fo & !al is not held. k0 ^= [b == 1] on the non-DONE unaligned
            // shots (their k is 0), so g = fo & !al_s & !k0 can be remade around each bq_pi; the ladder's top reads
            // it through k0 directly. Restored before S3 (no S2 step reads k after RXD).
            let kfl2 = lean >= 3 && !cached_b1;
            let g = if cached_b1 || kfl2 { None } else { Some(pl.get()) };
            if kfl2 {
                self.k0_flip(b, &mut pl);
                let receipt = pl.get();
                extra_debt(b, receipt, mode, 5);
                pl.put(receipt);
            } else {
                let (al, alr) = self.al_on(b, &mut pl, fin);
                if let Some(gq) = g {
                    b.x(al);
                    b.and_c(fo, al, gq);
                    b.x(al);
                }
                if fin {
                    if extra_debt(b, al, mode, 5) {
                        pl.put(al);
                    } else {
                        self.al_off(b, &mut pl, fin, al, alr);
                    }
                } else {
                    let receipt = pl.get();
                    extra_debt(b, receipt, mode, 5);
                    pl.put(receipt);
                }
            }
            if lv > 0 && !cached_b1 {
                let gq = if kfl2 { self.g_k0(b, &mut pl, None) } else { g.unwrap() };
                b.x(gq);
                self.bq_pi_form(b, &mut pl, Some(gq), false, false, p, kfl2); // bq = B1 - 1 (offset)
                b.x(gq);
                if kfl2 { self.g_k0(b, &mut pl, Some(gq)); }
            }
            if lv > 0 {
                let c0 = pl.get();
                let mf = pl.get_n(2);
                // lean >= 3: when the pi window ends where the bq window starts, the pi toggles (transient prefix)
                // borrow the bq decoder's first prefix lane, which is still clean then (pi pairs use it the same way)
                let share_pa = lean >= 3 && jw.min(lv) <= p1lo;
                // lean >= 4, overlapping windows: the pi toggles keep only mf[1] clean and borrow be (no operand of
                // the ladder) as the dirty lane of their last Toffoli (mask::dirty_pre)
                let dirty_pa = lean >= 4 && !share_pa;
                let pa = if share_pa || dirty_pa { Vec::new() } else { pl.get_n(HIB - 3) }; // one pi prefix; borrow mf[1] for the other
                let bq_bits = if lv as isize - 3 - base < 64 { 6 } else { BB };
                // lean 2, slots holding g / lean 3, overlapping windows / lean >= 4: short retained bq decoder (one
                // prefix lane fewer, mask::short_pre)
                let s2_short = lean >= 4 || (lean == 3 && !share_pa) || (lean == 2 && !cached_b1);
                let pre = pl.get_n(bq_bits - 1 - usize::from(s2_short) - usize::from(skip6));
                let pi_pre = if dirty_pa {
                    dirty_pre(&[mf[1]], be)
                } else {
                    let mut v = if share_pa { vec![pre[0]] } else { pa.clone() };
                    v.push(mf[1]);
                    v
                };
                let src_pre = dpre(&pre, skip6, s2_short);
                let t: Vec<QubitId> = self.d[0..lv].to_vec();
                let s: Vec<QubitId> = self.v[0..lv].to_vec();
                let mut srcs =
                    vec![Src { lo: 0, hi: jw.min(lv), v: self.pi.clone(),
                               a: usize::from(p) as isize, d: 0, pre: pi_pre, late: false }];
                if p1lo < lv {
                    srcs.push(Src { lo: p1lo, hi: lv, v: self.bq[..bq_bits].to_vec(),
                                    a: -2 - base, d: 1, pre: src_pre.clone(), late: false });
                }
                let ms = Mscr { f: mf[0], t: mf[1], gf: mf[1], chain: pre.clone() };
                let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: false, cmpl: true, sc: &ms, g: &self.gp };
                let ru = mup_mid(b, &ld);
                let e1_active = false; // E1 off: free its held probe lane
                let e1_dl = if e1_active {
                    let q = pl.get();
                    pl.put(q);
                    Some(q)
                } else { None };
                let rd = if let Some(dl) = e1_dl.filter(|_| !matches!(mode, SlotMode::RecordInverseWithRepair { .. })) {
                    mdown_mid_probe(b, &ld, Some(xd), ta, dl, e1_fuse_lo, e1_fuse_hi)
                } else { mdown_mid(b, &ld, Some(xd)) };
                b.play(&ru, false);
                let ct = top_carry(&ld); // [rv<<pi > R]
                // DIV still uses S2; RET's exact term is already in xd.
                b.x(ct);
                // xd may already hold the RET term, so this is a reversible
                // XOR and cannot use AndC's fresh-zero target contract.
                b.ccx(fd, ct, xd);
                b.x(ct);
                if let Some(gq) = g {
                    b.and_c(gq, ct, ta); // alignment found, noncached B1
                } else if kfl2 {
                    // ta = (fo & !al_s) & !k0 & ct: the first AND in gf's free middle lane, the rest a dirty-ancilla
                    // Toffoli (Barenco) on po, which is no operand here and comes back unchanged
                    let h = mf[1];
                    let k0 = self.k[0];
                    b.x(self.al_s);
                    b.and_c(fo, self.al_s, h);
                    b.x(self.al_s);
                    let neg = !a1b_mut("k0top");
                    // lean >= 5: po has no lane here; be (no operand either) is the borrowed lane
                    let dq = if po_gone { be } else { po };
                    if neg { b.x(k0); }
                    b.ccx(h, k0, dq);
                    b.ccx(dq, ct, ta);
                    b.ccx(h, k0, dq);
                    b.ccx(dq, ct, ta);
                    if neg { b.x(k0); }
                    b.x(self.al_s);
                    b.and_u(fo, self.al_s, h);
                    b.x(self.al_s);
                } else {
                    // In cached slots, gf's middle scratch lane is zero.
                    // Borrow it for g = fo & !al_s, then restore it before
                    // the return ladder uses the same lane.
                    b.x(self.al_s);
                    b.and_c(fo, self.al_s, mf[1]);
                    b.x(self.al_s);
                    b.and_c(mf[1], ct, ta);
                    b.x(self.al_s);
                    b.and_u(fo, self.al_s, mf[1]);
                    b.x(self.al_s);
                }
                if lean == 0 {
                    b.x(self.dep[5]);
                    b.ccx(self.dep[5], ta, tt); // unaligned OUT turn
                    b.x(self.dep[5]);
                }
                let e1_hold = e1_dl.map(|id| {
                    let q = pl.get();
                    assert_eq!(q, id, "E1 dl lane changed during the middle");
                    q
                });
                b.play(&rd, false);
                e1_hold_slot = e1_hold;
                pl.put_n(&pre);
                pl.put_n(&pa);
                pl.put_n(&mf);
                pl.put(c0);
            }
            // The former u and nz values have no consumers after RXD. Keep
            // their receipt channels on a borrowed zero lane.
            let debt = pl.get();
            let _ = extra_debt(b, debt, mode, 8);
            let _ = extra_debt(b, debt, mode, 4);
            pl.put(debt);
            if lv > 0 && !cached_b1 {
                let gq = if kfl2 { self.g_k0(b, &mut pl, None) } else { g.unwrap() };
                b.x(gq);
                self.bq_pi_form(b, &mut pl, Some(gq), false, true, p, kfl2);
                b.x(gq);
                if kfl2 { self.g_k0(b, &mut pl, Some(gq)); }
            }
            if let Some(gq) = g {
                if !extra_debt(b, gq, mode, 0) {
                    let (al, alr) = self.al_on(b, &mut pl, fin);
                    b.x(al);
                    b.and_u(fo, al, gq);
                    b.x(al);
                    self.al_off(b, &mut pl, fin, al, alr);
                }
                pl.put(gq);
            } else {
                let debt = pl.get();
                let _ = extra_debt(b, debt, mode, 0);
                pl.put(debt);
            }
            if kfl2 { self.k0_flip(b, &mut pl); }
            if lean >= 1 {
                // fo, dep[5] and al_s are not written in S2; ta is final since the ladder's top
                tt = pl.get();
                and_into(b, &mut pl, &[(fo, false), (self.dep[5], true), (self.al_s, false)], tt, false);
                if lv > 0 && !a1b_mut("s2tt") {
                    b.x(self.dep[5]);
                    b.ccx(self.dep[5], ta, tt); // unaligned OUT turn
                    b.x(self.dep[5]);
                }
            }
        }

        // S3 alignment (ta shots): k = pi; erase ta = fo & [k == pi] (no other OUT shot has k == pi: k == 0 or k < pi).
        // In the cached slots B1 = b + pi from here; b stays the dividend's length until the turn.
        // Turn (tt shots, stack empty after the pop): b <- b - k + 1 - dl (the divisor's length) with dl = !V[b - k]
        // (V frame, phys b - k + pi), erased with D[b_new + k - 1].
        self.marks.push(("S3", b.mark_pos()));
        pl.stage("S3");
        {
            if cached_b1 { self.bq_pi_form(b, &mut pl, Some(ta), false, false, p, lean >= 3); }
            if p { b.cx(ta, self.k[0]); }
            for i in 0..HIB {
                b.ccx(ta, self.pi[i], self.k[i + 1]);
            }
            b.cx(ta, self.al_s);
            if !extra_debt(b, ta, mode, 1) {
                for i in 0..HIB {
                    b.cx(self.k[i + 1], self.pi[i]);
                }
                let e = pl.get();
                let mut eqlits = negpi.clone();
                eqlits.push((self.k[0], !p));
                and_into(b, &mut pl, &eqlits, e, false);
                b.ccx(fo, e, ta);
                and_into(b, &mut pl, &eqlits, e, true);
                pl.put(e);
                for i in 0..HIB {
                    b.cx(self.k[i + 1], self.pi[i]);
                }
            }
        }
        pl.put(ta);
        {
            let e1_fused = e1_hold_slot.is_some() && !matches!(mode, SlotMode::RecordInverseWithRepair { .. });
            let dl = if let Some(held) = e1_hold_slot.take() {
                let normal = pl.get();
                b.cx(held, normal);
                b.cx(normal, held);
                pl.put(held);
                normal
            } else { pl.get() };
            let kk = self.k.clone();
            let mut btt = self.bq.clone();
            btt.push(tt);
            let ttoff = 1isize << BB;
            self.bq_reg(b, &mut pl, &kk, Some(tt), true, false); // tt: bq = b - 1 - k (+ pi cached)
            if pb1 > pb0 {
                if !cached_b1 { self.bq_pi(b, &mut pl, None, false, false, p); }
                let pre = pl.get_n(BB - usize::from(skip6));
                let dp = dpre(&pre, skip6, false);
                let vref = self.v.clone();
                if self.d1_record {
                    assert!(matches!(mode, SlotMode::RecordInverseWithRepair { .. }));
                    assert!(self.d1_split.is_none());
                    self.d1_split = Some(D1Split { cut: b.mark_pos(), dl, btt: btt.clone(),
                        pre: dp.clone(), vref, lo: pb0, hi: pb1, off: ttoff - 1 - base });
                } else {
                    let mut scan = |lo, hi| {
                        if hi > lo {
                            onehot_scan(b, &btt, &dp, lo, hi, ttoff - 1 - base, |b, j, o| {
                                b.x(vref[j]);
                                b.ccx(o, vref[j], dl);
                                b.x(vref[j]);
                            });
                        }
                    };
                    if e1_fused {
                        scan(pb0, e1_fuse_lo);
                        scan(e1_fuse_hi, pb1);
                    } else { scan(pb0, pb1); }
                }
                pl.put_n(&pre);
                if !cached_b1 { self.bq_pi(b, &mut pl, None, false, true, p); }
            }
            {
                let h = pl.get();
                b.x(dl);
                b.and_c(tt, dl, h);
                b.x(dl);
                if skip6 {
                    let anc = pl.get_n(BB - 2);
                    inc_top1(b, h, &self.bq, &anc);
                    pl.put_n(&anc);
                } else {
                    let anc = pl.get_n(BB - 1);
                    inc(b, h, &self.bq, &anc);
                    pl.put_n(&anc);
                }
                b.x(dl);
                b.and_u(tt, dl, h);
                b.x(dl);
                pl.put(h);
            }
            // The post-update D boundary regenerates dl during the required
            // inverse traversal. The phase fix is placed before the ordinary
            // erase body in source order, so inverse playback applies it just
            // after regeneration.
            if let SlotMode::RecordInverseWithRepair { dl_receipt: Some(receipt), .. } = mode {
                b.z_if(dl, receipt);
            }
            if let SlotMode::ForwardGhost { dl_receipt: Some(receipt), .. } = mode {
                b.hmr_to(dl, receipt);
            } else if pe1 > pe0 {
                self.bq_reg(b, &mut pl, &kk, None, false, false); // tt: bq = b_new - 1 + k (+ pi cached)
                if cached_b1 { self.bq_pi(b, &mut pl, None, true, false, p); }
                let pre = pl.get_n(BB - usize::from(skip6));
                let dref = self.d.clone();
                onehot_scan(b, &btt, &dpre(&pre, skip6, false), pe0, pe1, ttoff - base, |b, j, o| {
                    b.ccx(o, dref[j], dl);
                });
                pl.put_n(&pre);
                if cached_b1 { self.bq_pi(b, &mut pl, None, true, true, p); }
                self.bq_reg(b, &mut pl, &kk, None, false, true);
            }
            pl.put(dl);
        }
        // lean >= 4: after S3, tt = fo & !dep[5] & al_s exactly (tt was fo&!d5&al_s ^ !d5&ta, ta implies fo, and S3
        // added ta into al_s). No step before S6 writes fo, and on fo shots S4 leaves dep and al_s alone (pu and se
        // are 0 there), so tt takes no lane through S4 and S5 and is remade at S6's start.
        let tt_park = lean >= 4;
        if tt_park {
            and_into(b, &mut pl, &[(fo, false), (self.dep[5], true), (self.al_s, false)], tt, true);
            pl.put(tt);
        }

        // S4 step end, push, bit 0 into be, k cleared, swap.  z0 = [pi == 0] until S8 (odd slots only)
        self.marks.push(("S4", b.mark_pos()));
        pl.stage("S4");
        // z0 lives only on odd slots: S4 (step end), then again from S6 to S8
        let mut z0 = QubitId(u64::MAX);
        if odd {
            z0 = pl.get();
            if self.d1_record && self.d1phi_z0 {
                assert!(matches!(mode, SlotMode::RecordInverseWithRepair { .. }));
                assert!(self.d1_z0_split.is_none());
                // Preserve the precise pool hand-out of and_into(4), but
                // omit its reversible body from the inverse recording.
                let m = pl.get();
                let anc = pl.get();
                self.d1_z0_split = Some(D1Z0Split {
                    cut: b.mark_pos(), z0, lits: negpi.clone(), m, anc,
                });
                pl.put(anc);
                pl.put(m);
            } else {
                and_into(b, &mut pl, &negpi, z0, false);
            }
        }
        let ww = pl.get(); // RET with c = 1
        // lean >= 3: se is 0 on every even slot (it is only written under odd); take no lane for it there
        let se_lane = lean < 3 || odd;
        let se = if se_lane { pl.get() } else { QubitId(u64::MAX) }; // step end
        {
            self.fr_swap(b, f1on);
            b.and_c(fd, xd, ww);
            self.fr_swap(b, f1on);
            // lean >= 2: dv and pu are linear in (fd, ww, se) (se implies dv) and fd is not read until they are
            // erased, so both live in fd's own qubit: fd ^= ww (dv), fd ^= se (pu = dv & !se), undone in reverse
            let inplace = lean >= 2;
            let dv = if inplace { fd } else { pl.get() };
            if inplace {
                b.cx(ww, fd);
            } else {
                b.cx(fd, dv);
                b.cx(ww, dv); // DIV after the RET->DIV transition
            }
            if odd {
                if a1b_mut("s4z0") {
                    // negative control: erase z0 before its consumer
                    and_into(b, &mut pl, &negpi, z0, true);
                    b.and_c(dv, z0, se);
                    and_into(b, &mut pl, &negpi, z0, false);
                } else {
                    b.and_c(dv, z0, se);
                }
                if lean >= 1 {
                    // z0's only S4 consumer was the AND above (pi is not written before S8): erase it now, not
                    // after the swap, so the push scan runs one lane lower
                    if !extra_debt(b, z0, mode, 12) {
                        and_into(b, &mut pl, &negpi, z0, true);
                    }
                    pl.put(z0);
                }
            }
            let pu = if inplace { fd } else { pl.get() };
            if !inplace { b.cx(dv, pu); }
            if odd {
                b.cx(se, pu); // push = dv & !se
            }
            // TOPBIT: the first bit of a quotient is always 1. Keep it in the logical depth but do not write a stack
            // lane: the sweep runs on fd & !se = pu ^ (ww & !se) (a one-bit quotient, ww & se, writes nothing either).
            let sweep_gate = |b: &mut B| {
                if odd {
                    b.x(se);
                    b.ccx(ww, se, pu);
                    b.x(se);
                } else {
                    b.cx(ww, pu);
                }
            };
            sweep_gate(b);
            // the pushed bit (bit d of the stack, d the depth before the push) goes to V's gap at V-frame lane b + d
            // (b: the divisor's length), phys b + d + pi; bq = b + pi - 1 + d - 1 at the scan
            if push1 > push0 {
                self.bq_reg(b, &mut pl, &dep5, None, false, false);
                if !cached_b1 { self.bq_pi(b, &mut pl, None, false, false, p); }
                let mut bpu = self.bq.clone();
                bpu.push(pu);
                let pre = pl.get_n(BB - usize::from(skip6));
                let vref = self.v.clone();
                onehot_scan(b, &bpu, &dpre(&pre, skip6, false), push0, push1, (1isize << BB) - 2 - base, |b, j, o| {
                    b.cswap(o, xd, vref[j]);
                });
                pl.put_n(&pre);
                if !cached_b1 { self.bq_pi(b, &mut pl, None, false, true, p); }
                self.bq_reg(b, &mut pl, &dep5, None, false, true);
            }
            let _ = jw;
            sweep_gate(b); // restore dv & !se for logical-depth increment
            if se_lane {
                b.x(se);
                b.ccx(ww, se, xd); // clear the implicit top 1 after the sweep
                b.x(se);
            } else {
                if !a1b_mut("sexd") { b.cx(ww, xd); } // even slot: !se = 1
            }
            if !po_gone {
                b.x(self.dep[5]);
                b.ccx(po, self.dep[5], be); // final pop supplies implicit top 1
                b.x(self.dep[5]);
            }
            let anc = pl.get_n(DEPB - 1);
            inc(b, pu, &self.dep, &anc);
            pl.put_n(&anc);
            if odd {
                b.cswap(se, xd, be); // bit 0 of the quotient becomes the cofactor control
                b.cx(se, pu);
            }
            if inplace {
                if !a1b_mut("s4fd") { b.cx(ww, fd); }
            } else {
                b.cx(dv, pu);
                pl.put(pu);
                b.cx(ww, dv);
                b.cx(fd, dv);
                pl.put(dv);
            }
            if odd {
                let cf = pl.get();
                if f1on {
                    // first step end: cf = se & f1; f1 cleared.  The first step divides p (256 bits), so there b + k =
                    // 257; every later dividend is shorter, b + k <= 256: erase cf with se & [b + k >= 257]
                    b.and_c(se, f1, cf);
                    b.cx(cf, f1);
                    if !extra_debt(b, cf, mode, 15) {
                        let cy = pl.get();
                        let r = if lean >= 3 { self.bq_k_carry_inplace(b, &mut pl, cy) }
                                else { self.bq_k_carry(b, &mut pl, cy) };
                        b.play(&r.0, false);
                        b.and_u(se, cy, cf);
                        b.play(&r.0, true);
                        pl.put_n(&r.1);
                        pl.put(cy);
                    }
                } else {
                    let _ = extra_debt(b, cf, mode, 15);
                }
                pl.put(cf);
                // k == dep + 1 at a step end (bit 0 is in be, bits k-1 .. 1 on the stack): clear it
                let anc = pl.get_n(DEPB - 2);
                inc(b, se, &self.dep[1..], &anc);
                for i in 0..KB {
                    b.ccx(se, self.dep[i], self.k[i]);
                }
                b.cx(se, self.al_s);
                dec(b, se, &self.dep[1..], &anc);
                pl.put_n(&anc);
                b.cx(se, self.par);
                cswap_regs(b, se, &self.d, &self.v);
                // Z0K reverted: z0 is idle through S5. Discharge it here
                // and regenerate it at S6, freeing one held lane.
                if lean == 0 {
                    if !extra_debt(b, z0, mode, 12) {
                        and_into(b, &mut pl, &negpi, z0, true);
                    }
                    pl.put(z0);
                }
            } else {
                let z = pl.get();
                let _ = extra_debt(b, z, mode, 12);
                let _ = extra_debt(b, z, mode, 15);
                pl.put(z);
            }
        }
        pl.put(xd);

        let ks7_enabled = matches!(mode, SlotMode::RecordInverseWithRepair { .. });
        // lean >= 4: S5 does not hand its decoder prefix to S7 (S6 runs without it)
        let ks7_start = if lean < 4 && p2hi > lc {
            (w - p2hi..w - lc).find_map(|l| {
                let j = w as isize - 2 - base - l as isize;
                (j >= 0 && j < (1 << BB)).then_some(j as usize)
            })
        } else { None };
        let mut ks7_pre_slot: Option<(Vec<QubitId>, usize)> = None;
        // short retained bq decoder in S5 and S7 (S7 may take over S5's prefix lanes, so both use the same form):
        // lean 2 in the slots holding al (fin) or kq (f1on), lean >= 3 on odd slots (se and z0 there)
        let s57_short = (lean >= 3 && odd) || (lean == 2 && (fin || f1on));
        // S5 cofactor ladder P2 over phys [lc, W) (ladder lane l <-> phys W-1-l), active phys > B1 + max(d - 1, 0)
        // (D's stack, lanes b + 1 .. b + d - 1, stays below it): cv += be * (cd << pi), with the mid-ladder erasure of
        // be and po.  bq holds B1 + max(d - 1, 0) - 1 (offset) from here to the end of S7.
        self.marks.push(("S5", b.mark_pos()));
        pl.stage("S5");
        // lean >= 3, fin slots: al is not held from here to S7's end. k0 carries [b == 1] (k0_flip) and al is
        // remade around the two bq_pi's; k is not read between S5 and S7b.
        let kfl5 = lean >= 3 && fin;
        let (al, alr) = if kfl5 {
            assert!(!cached_b1);
            self.k0_flip(b, &mut pl);
            let nal = self.nal_k0(b, &mut pl, None);
            b.x(nal);
            self.bq_pi_form(b, &mut pl, Some(nal), false, false, p, true); // bq = B1 - 1
            b.x(nal);
            self.nal_k0(b, &mut pl, Some(nal));
            (QubitId(u64::MAX), None)
        } else {
            let (al, alr) = self.al_on(b, &mut pl, fin);
            // lean >= 2: in the slots holding al the addend is made just in time (8 -> 5 scratch lanes)
            if !cached_b1 { self.bq_pi_form(b, &mut pl, Some(al), false, false, p, lean >= 2 && fin); } // bq = B1 - 1
            (al, alr)
        };
        self.bq_reg(b, &mut pl, &dep5, Some(self.dep[5]), false, false); // bq = B1 + max(d - 1, 0) - 1
        {
            if lc < w {
                let n = w - lc;
                let c0 = pl.get();
                let mf = pl.get_n(2);
                // S5 and inverse S7 share this retained prefix. Size it for
                // S7's one-lane-higher decoded value as well.
                let bq_bits = if p2hi as isize - 1 - base < 64 { 6 } else { BB };
                let pre = pl.get_n(bq_bits - 1 - usize::from(s57_short) - usize::from(skip6));
                let src_pre = dpre(&pre, skip6, s57_short);
                let carry_bank: Vec<QubitId> = Vec::new();
                let gp = self.gp.clone();
                let t: Vec<QubitId> = (0..n).map(|l| self.v[w - 1 - l]).collect();
                let s: Vec<QubitId> = (0..n).map(|l| self.d[w - 1 - l]).collect();
                let mut srcs = vec![];
                if p2hi > lc {
                    srcs.push(Src { lo: w - p2hi, hi: w - lc, v: self.bq[..bq_bits].to_vec(), a: w as isize - 2 - base, d: -1,
                                    pre: src_pre.clone(), late: false });
                }
                let ms = Mscr { f: mf[0], t: mf[1], gf: *mf.last().unwrap(), chain: pre.clone() };
                let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &ms, g: &gp };
                let ordinary = w - p2hi;
                let rolling = matches!(mode, SlotMode::ForwardGhost { .. }) && ordinary > 0;
                let (ru, rd) = if rolling {
                    self.s5_carry_bits = b.fresh_bits(ordinary);
                    s5_rolling_prefix(b, &ld, be, mf[1], &self.s5_carry_bits);
                    if ordinary < n {
                        let window_srcs: Vec<Src> = srcs.iter().map(|src| Src {
                            lo: src.lo - ordinary, hi: src.hi - ordinary, v: src.v.clone(),
                            a: src.a + src.d * ordinary as isize, d: src.d,
                            pre: src.pre.clone(), late: src.late,
                        }).collect();
                        let win = Lad { t: &t[ordinary..], s: &s[ordinary..],
                            c0: s[ordinary - 1], srcs: &window_srcs,
                            f0: true, cmpl: true, sc: &ms, g: &gp };
                        (mup_mid(b, &win), mdown_mid(b, &win, Some(be)))
                    } else { (Vec::new(), Vec::new()) }
                } else {
                    let repair = matches!(mode, SlotMode::RecordInverseWithRepair { .. })
                        && !self.s5_carry_bits.is_empty();
                    let ru = if ks7_enabled {
                        if let Some(start) = ks7_start {
                            if repair { mup_mid_from_repair(b, &ld, start, &self.s5_carry_bits) }
                            else { mup_mid_from(b, &ld, start) }
                        } else if repair { mup_mid_repair(b, &ld, &self.s5_carry_bits) }
                        else { mup_mid(b, &ld) }
                    } else { mup_mid(b, &ld) };
                    (ru, mdown_mid(b, &ld, Some(be)))
                };
                b.play(&rd, true);
                let ct = top_carry(&ld); // [cd<<pi > cv_post]; cmp = !ct
                // be ^= (po | se) & cmp  (po, se exclusive)
                if !extra_debt(b, be, mode, 9) {
                    b.x(ct);
                    if po_gone {
                        // lean >= 5: no po lane. The parent's po here (regenerated by the inverse) is the Boolean
                        // function fo & (dep[5] | cmp & !f1), so (po ^ se) & cmp == (fo & (dep[5] | !f1) ^ se) & cmp:
                        // be is erased (or regenerated) from fo, dep[5], f1, se and cmp alone
                        let se_term = odd && !a1b_mut("c5se");
                        if se_term { b.cx(se, fo); }
                        b.ccx(fo, ct, be); // (fo ^ se) & cmp
                        if se_term { b.cx(se, fo); }
                        if f1on && !a1b_mut("c5f1") {
                            // ^= fo & !dep[5] & f1 & cmp: h = fo & !dep[5] in mf[1] (clean at this midpoint), then a
                            // dirty-ancilla Toffoli (Barenco) on ww, held and no operand here
                            let h = mf[1];
                            b.x(self.dep[5]);
                            b.and_c(fo, self.dep[5], h);
                            b.ccx(h, f1, ww);
                            b.ccx(ww, ct, be);
                            b.ccx(h, f1, ww);
                            b.ccx(ww, ct, be);
                            b.and_u(fo, self.dep[5], h);
                            b.x(self.dep[5]);
                        }
                    } else if odd {
                        b.cx(se, po);
                        b.ccx(po, ct, be);
                        b.cx(se, po);
                    } else {
                        b.ccx(po, ct, be);
                    }
                    b.x(ct);
                }
                // po ^= fo & (ne | (cmp & !f1))  ==  fo & !(nz & !(cmp & !f1))
                // (lean >= 5: po and its receipt channel were discharged at S1)
                if !po_gone && !extra_debt(b, po, mode, 2) {
                    // nz is the literal !dep[5]. The ladder's mf[1] is
                    // clean at this midpoint and can hold h transiently.
                    b.x(self.dep[5]);
                    let h = mf[1];
                    if f1on && lean >= 3 {
                        // po ^= fo & !(nz & !kq) = fo & !nz  ^  fo & nz & cmp & !f1, the second a dirty-ancilla
                        // Toffoli (Barenco) on tt (ww from lean 4; idle here) after h = fo & nz; no kq lane
                        b.x(self.dep[5]);
                        b.ccx(fo, self.dep[5], po);
                        b.x(self.dep[5]);
                        b.and_c(fo, self.dep[5], h);
                        b.x(ct);
                        b.x(f1);
                        let dq = if tt_park { ww } else { tt }; // a held lane that is no operand here
                        b.ccx(h, ct, dq);
                        b.ccx(dq, f1, po);
                        b.ccx(h, ct, dq);
                        if !a1b_mut("f1kq") { b.ccx(dq, f1, po); }
                        b.x(f1);
                        b.x(ct);
                        b.and_u(fo, self.dep[5], h);
                    } else if f1on {
                        let kq = pl.get();
                        b.x(ct);
                        b.x(f1);
                        b.and_c(ct, f1, kq); // kq = cmp & !f1
                        b.x(f1);
                        b.x(ct);
                        b.x(kq);
                        b.and_c(self.dep[5], kq, h); // h = nz & !kq
                        b.x(kq);
                        b.x(h);
                        b.ccx(fo, h, po);
                        b.x(h);
                        b.x(kq);
                        b.and_u(self.dep[5], kq, h);
                        b.x(kq);
                        b.x(ct);
                        b.x(f1);
                        b.and_u(ct, f1, kq);
                        b.x(f1);
                        b.x(ct);
                        pl.put(kq);
                    } else {
                        b.and_c(self.dep[5], ct, h); // h = nz & !cmp
                        b.x(h);
                        b.ccx(fo, h, po);
                        b.x(h);
                        b.and_u(self.dep[5], ct, h);
                    }
                    b.x(self.dep[5]);
                }
                b.play(&ru, true);
                if rolling && ordinary < n { s5_rolling_finish(b, &ld, &self.s5_carry_bits); }
                pl.put_n(&carry_bank);
                if let Some(start) = ks7_start { ks7_pre_slot = Some((pre, start)); }
                else { pl.put_n(&pre); }
                pl.put_n(&mf);
                pl.put(c0);
            }
        }
        if lc >= w {
            if !po_gone { let _ = extra_debt(b, po, mode, 2); }
            let _ = extra_debt(b, be, mode, 9);
        }
        pl.put(be);
        if !po_gone { pl.put(po); }

        // S6 termination (OUT, b == 1, k == 0, empty stack after the pop), phase update, erasures of se and ww
        self.marks.push(("S6", b.mark_pos()));
        pl.stage("S6");
        if tt_park {
            // fo, dep[5], al_s as at S3's end (S6a's flag moves come next)
            tt = pl.get();
            and_into(b, &mut pl, &[(fo, false), (self.dep[5], true), (self.al_s, a1b_mut("ttpark"))], tt, false);
        }
        if odd {
            z0 = pl.get();
            and_into(b, &mut pl, &negpi, z0, false);
        }
        self.marks.push(("S6a", b.mark_pos()));
        pl.stage("S6a");
        // DIV -> OUT at a step end (se & !ww)
        if odd {
            let a = pl.get();
            b.x(ww);
            b.and_c(se, ww, a);
            b.cx(a, fd);
            b.cx(a, fo);
            b.and_u(se, ww, a);
            b.x(ww);
            pl.put(a);
        }
        // RET -> (z0 ? OUT : DIV) when ww (fr is implicit)
        if odd {
            let a = pl.get();
            b.and_c(ww, z0, a);
            b.cx(a, fo);
            b.cx(ww, fd);
            b.cx(a, fd);
            b.and_u(ww, z0, a);
            pl.put(a);
        } else {
            b.cx(ww, fd);
        }
        b.cx(tt, fo); // OUT -> RET
        // se: post OUT with pi == 0
        if se_lane {
            if !extra_debt(b, se, mode, 10) && odd {
                b.ccx(fo, z0, se);
            }
            pl.put(se);
        } else {
            let z = pl.get();
            let _ = extra_debt(b, z, mode, 10);
            pl.put(z);
        }
        self.marks.push(("S6b", b.mark_pos()));
        pl.stage("S6b");
        // ww: (post DIV & dep == 1) ^ (post OUT & z0 & dep == 0)
        if !extra_debt(b, ww, mode, 3) {
            let mut l1: Vec<(QubitId, bool)> = self.dep[..5].iter().map(|&q| (q, true)).collect();
            l1.push((self.dep[5], false));
            let e1 = pl.get();
            and_into(b, &mut pl, &l1, e1, false);
            b.ccx(fd, e1, ww);
            and_into(b, &mut pl, &l1, e1, true);
            pl.put(e1);
            if odd {
                let nz = pl.get();
                b.x(nz);
                b.cx(self.dep[5], nz);
                let tq = pl.get();
                b.and_c(fo, z0, tq);
                b.ccx(tq, nz, ww);
                b.and_u(fo, z0, tq);
                pl.put(tq);
                b.cx(self.dep[5], nz);
                b.x(nz);
                pl.put(nz);
            }
        }
        pl.put(ww);
        self.marks.push(("S6c", b.mark_pos()));
        pl.stage("S6c");

        // S7 turn discriminator P3: z = [cv >= cd << (pi + 1)]; erase tt = fr_post & (f1 | !z).  Ladder lane l: target
        // V lane W-1-l (cv bit l + pi), source D lane W-l (cd bit l - 1), active phys > B1 - 1: the source is read one
        // lane up, so its region starts one lane lower than P2's (target V lane B1 is V's empty lane above rv).  The
        // result is used by turning shots only, which have d = 0.
        self.marks.push(("S7", b.mark_pos()));
        pl.stage("S7");
        // In inverse playback this Z follows S7 regeneration, before inverse
        // S6 changes the witness support. It reads the original HMR outcome.
        if let SlotMode::RecordInverseWithRepair { receipt, .. } = mode {
            b.z_if(tt, receipt);
        }
        if let SlotMode::ForwardGhost { receipt, .. } = mode {
            b.hmr_to(tt, receipt);
            if let Some((pre, _)) = ks7_pre_slot.take() {
                let c0 = pl.get();
                let mf = pl.get_n(2);
                let zl = pl.get();
                pl.put(zl);
                pl.put_n(&pre);
                pl.put_n(&mf);
                pl.put(c0);
            }
        } else if lc < w {
            let n = w - lc;
            let c0 = pl.get();
            let mf = pl.get_n(2);
            let held_pre = ks7_pre_slot.take();
            let held_start = held_pre.as_ref().map(|(_, start)| *start);
            let bq_bits = if p2hi as isize - 1 - base < 64 { 6 } else { BB };
            assert!(!(skip6 && held_pre.is_some()), "skip decoders with a held S5 prefix");
            let pre = held_pre.map(|(pre, _)| pre)
                .unwrap_or_else(|| pl.get_n(bq_bits - 1 - usize::from(s57_short) - usize::from(skip6)));
            let src_pre = dpre(&pre, skip6, s57_short);
            // lean >= 5 (lane A1c): ladder lane 0's source (cd bit -1) is the constant 0; with carry-in 0 its cell is
            // the identity and its carry out is 0, so it takes no qubit (mask::ZERO_SRC: the cell is skipped, the
            // lane's toggles stay, the carry into lane 1 stays on c0)
            let zl = if lean >= 5 { ZERO_SRC } else { pl.get() };
            let t: Vec<QubitId> = (0..n).map(|l| self.v[w - 1 - l]).collect();
            // negative control c5zl: a live lane (D lane 0) as lane 0's source must break the compare
            let zsrc = if a1b_mut("c5zl") { self.d[0] } else { zl };
            let s: Vec<QubitId> = (0..n).map(|l| if l < 1 { zsrc } else { self.d[w - l] }).collect();
            let mut srcs = vec![];
            if p2hi > lc {
                srcs.push(Src { lo: w - p2hi, hi: w - lc, v: self.bq[..bq_bits].to_vec(), a: w as isize - 1 - base, d: -1,
                                pre: src_pre.clone(), late: false });
            }
            let ms = Mscr { f: mf[0], t: mf[1], gf: mf[1], chain: pre.clone() };
            // The unused gf lane becomes one more carry owner. Hold two
            // clean lanes through the complete compare,
            // its tt consumer, and inverse replay; no new physical qubits.
            let free_before = pl.free.len();
            // lean >= 3: one bank lane in the first-step slots (their kq takes the other)
            let nbank = if lean >= 4 { usize::from(!f1on) } else if lean >= 3 && f1on { 1 } else { 2 };
            assert!(free_before >= nbank + usize::from(f1on), "S7 carry bank leaves no kq room");
            let carry_bank = pl.get_n(nbank);
            let mut gp = self.gp.clone();
            gp.extend_from_slice(&carry_bank);
            for (i, &q) in gp.iter().enumerate() {
                assert!(!gp[..i].contains(&q), "duplicate S7 carry owner");
                assert!(!t.contains(&q) && !s.contains(&q) && q != c0 && q != zl);
                assert!(!mf.contains(&q) && !pre.contains(&q));
                assert!(q != tt && q != al && Some(q) != alr && (!odd || q != z0));
                assert!(srcs.iter().all(|src| !src.v.contains(&q) && !src.pre.contains(&q)));
            }
            let ld = Lad { t: &t, s: &s, c0, srcs: &srcs, f0: true, cmpl: true, sc: &ms, g: &gp };
            let ru = if ks7_enabled {
                if srcs.len() == 1 { mup_mid_spare_masked_from(b, &ld, held_start) }
                else { mup_mid(b, &ld) }
            } else { mup_mid(b, &ld) };
            b.play(&ru, false);
            let ct = top_carry(&ld); // [cd<<(pi+1) > cv] = !z
            self.fr_swap(b, f1on); // fd's qubit holds fr_post
            if f1on {
                let kq = pl.get();
                b.x(f1);
                b.x(ct);
                b.and_c(f1, ct, kq); // kq = !f1 & z
                b.x(kq);
                b.ccx(fd, kq, tt);
                b.x(kq);
                b.and_u(f1, ct, kq);
                b.x(ct);
                b.x(f1);
                pl.put(kq);
            } else {
                b.ccx(fd, ct, tt);
            }
            self.fr_swap(b, f1on);
            b.play(&ru, true);
            if ks7_enabled {
                if let Some(start) = held_start { clear_onehot_dec(b, &self.bq[..src_pre.len()+1], &src_pre, start); }
            }
            // The inverse AndC/AndU recording restores every bank lane to
            // zero. Existing traversal tests check all pool lanes per slot.
            pl.put_n(&carry_bank);
            assert_eq!(pl.free.len(), free_before, "S7 carry bank lifetime leaked");
            if zl != ZERO_SRC { pl.put(zl); }
            pl.put_n(&pre);
            pl.put_n(&mf);
            pl.put(c0);
        }
        self.bq_reg(b, &mut pl, &dep5, Some(self.dep[5]), false, true);
        if kfl5 {
            let nal = self.nal_k0(b, &mut pl, None);
            b.x(nal);
            // lean >= 5: just in time (5 scratch lanes instead of 8), as at S5's start
            self.bq_pi_form(b, &mut pl, Some(nal), false, true, p, lean >= 5);
            b.x(nal);
            self.nal_k0(b, &mut pl, Some(nal));
            let receipt = pl.get();
            extra_debt(b, receipt, mode, 6);
            pl.put(receipt);
            if !a1b_mut("s5k0") { self.k0_flip(b, &mut pl); } // bq is the pre-ladder b - 1 offset again
        } else if fin {
            if !cached_b1 { self.bq_pi(b, &mut pl, Some(al), false, true, p); }
            if extra_debt(b, al, mode, 6) {
                pl.put(al);
            } else {
                self.al_off(b, &mut pl, fin, al, alr);
            }
        } else {
            if !cached_b1 { self.bq_pi(b, &mut pl, Some(al), false, true, p); }
            let receipt = pl.get();
            extra_debt(b, receipt, mode, 6);
            pl.put(receipt);
            self.al_off(b, &mut pl, fin, al, alr);
        }
        pl.put(tt);

        // TE-LATE: S7 does not consume the DONE flag on a terminating shot.
        // Compute, stamp and discharge te here, after S5/S7 released their
        // scratch. bq is again the pre-ladder b-1 offset.
        self.marks.push(("S7b", b.mark_pos()));
        pl.stage("S7b");
        let te = pl.get();
        if termon {
            let nb = pl.get();
            let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&q| (q, true)).collect();
            and_into(b, &mut pl, &bz, nb, false);
            let mut lits: Vec<(QubitId, bool)> = vec![(nb, false)];
            lits.extend(self.k.iter().map(|&q| (q, true)));
            lits.push((self.dep[5], true));
            lits.push((fo, false));
            and_into(b, &mut pl, &lits, te, false);
            if !extra_debt(b, nb, mode, 14) {
                and_into(b, &mut pl, &bz, nb, true);
            }
            pl.put(nb);
            b.cx(te, fo);
            b.cx(te, fnn);
            let stamp = sigma - lay.first_termon;
            for (i, &q) in cnt.iter().enumerate() {
                if (stamp >> i) & 1 != 0 { b.cx(te, q); }
            }
            if !extra_debt(b, te, mode, 11) {
                // the stamp's depth bits sit on d6's ones (d6 == 31 at the termination)
                let mut lits: Vec<(QubitId, bool)> = cnt.iter().enumerate()
                    .map(|(i, &q)| (q, ((stamp >> i) & 1 == 0) ^ (i >= KB))).collect();
                lits.push((fnn, false));
                and_into(b, &mut pl, &lits, te, true);
            }
        } else {
            let z = pl.get();
            let _ = extra_debt(b, z, mode, 14);
            pl.put(z);
            let _ = extra_debt(b, te, mode, 11);
        }
        pl.put(te);

        // S8 z0 erase, rotation and pi update: up = OUT post, or DONE on even slots
        self.marks.push(("S8", b.mark_pos()));
        pl.stage("S8");
        if odd {
            if !extra_debt(b, z0, mode, 13) {
                and_into(b, &mut pl, &negpi, z0, true);
            }
            pl.put(z0);
        } else {
            let z = pl.get();
            let _ = extra_debt(b, z, mode, 13);
            pl.put(z);
        }
        let v0 = self.v[0];
        for j in 0..w - 1 {
            self.v[j] = self.v[j + 1];
        }
        self.v[w - 1] = v0;
        let upq = pl.get();
        b.cx(fo, upq);
        if sigma % 2 == 0 && !f1on {
            b.cx(fnn, upq);
        }
        rot2_up(b, upq, &self.v);
        {
            let anc = pl.get_n(HIB - 1);
            if p {
                inc(b, upq, &self.pi, &anc);
            } else {
                b.x(upq);
                dec(b, upq, &self.pi, &anc);
                b.x(upq);
            }
            pl.put_n(&anc);
        }
        if cached_b1 {
            // B1 = b + [k != 0] pi.  The slot's pi change is -1 + 2*up.
            let (al, alr) = self.al_on(b, &mut pl, false);
            let anc = pl.get_n(BB - 1);
            dec(b, al, &self.bq, &anc);
            let h = pl.get();
            b.and_c(al, upq, h);
            inc(b, h, &self.bq[1..], &anc[..BB - 2]);
            b.and_u(al, upq, h);
            pl.put(h);
            pl.put_n(&anc);
            self.al_off(b, &mut pl, false, al, alr);
        }
        if sigma % 2 == 0 && !f1on {
            b.cx(fnn, upq);
        }
        b.cx(fo, upq);
        pl.put(upq);
        assert_eq!(pl.free.len(), self.pool.len(), "scratch leak");
        if pl.hw > self.hw {
            self.hw = pl.hw;
            self.hw_at = pl.hw_at;
        }
        for (k, v) in pl.peaks.iter() {
            let e = self.peaks.entry(k).or_insert(0);
            *e = (*e).max(*v);
        }
    }

    /// Lane A1b (lean >= 3): k[0] ^= !al_s & !fnn & [bq == 0]. On model shots k == 0 wherever al_s == 0 and the shot
    /// is not DONE (fnn; fin slots only, so fnn is the DONE flag), so afterwards k[0] = [b == 1] there and
    /// al = al_s | fnn | k[0] (DONE shots have b == 1). Self-inverse while al_s, fnn and bq are unchanged.
    fn k0_flip(&self, b: &mut B, pl: &mut Pl) {
        let mut lits: Vec<(QubitId, bool)> = vec![(self.al_s, true), (self.fnn, true)];
        lits.extend(self.bq.iter().map(|&q| (q, true)));
        xor_lits(b, pl, &lits, self.k[0]);
    }

    /// Lane A1b (lean >= 3), between the two `k0_flip`s: `None` takes a lane and returns g = fo & !al_s & !k[0]
    /// (= fo & !al, the S2 form); `Some(g)` erases it again (measured) and returns the lane to the pool.
    fn g_k0(&self, b: &mut B, pl: &mut Pl, g: Option<QubitId>) -> QubitId {
        let lits = [(self.fo, false), (self.al_s, true), (self.k[0], true)];
        match g {
            None => {
                let q = pl.get();
                and_into(b, pl, &lits, q, false);
                q
            }
            Some(q) => {
                and_into(b, pl, &lits, q, true);
                pl.put(q);
                q
            }
        }
    }

    /// Lane A1b (lean >= 3), between the two `k0_flip`s: nal = !al_s & !fnn & !k[0] (= !al, the S5 / S7 form).
    fn nal_k0(&self, b: &mut B, pl: &mut Pl, nal: Option<QubitId>) -> QubitId {
        let lits = [(self.al_s, true), (self.fnn, true), (self.k[0], true)];
        match nal {
            None => {
                let q = pl.get();
                and_into(b, pl, &lits, q, false);
                q
            }
            Some(q) => {
                and_into(b, pl, &lits, q, true);
                pl.put(q);
                q
            }
        }
    }

    /// al = [k != 0] | [b == 1] (the second term only in `fin` slots, where some shot may be in the last step).
    /// Returns (al, extra qubit holding [b == 1] if computed).
    fn al_on(&self, b: &mut B, pl: &mut Pl, fin: bool) -> (QubitId, Option<QubitId>) {
        if !fin { return (self.al_s, None); }
        let nal = pl.get(); // [k == 0] & [b != 1]
        let nb1 = pl.get();
        let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&x| (x, true)).collect();
        and_into(b, pl, &bz, nb1, false);
        b.x(self.al_s);
        b.x(nb1);
        b.and_c(self.al_s, nb1, nal);
        b.x(nb1);
        b.x(self.al_s);
        and_into(b, pl, &bz, nb1, true);
        pl.put(nb1);
        b.x(nal);
        (nal, Some(QubitId(u64::MAX)))
    }
    fn al_off(&self, b: &mut B, pl: &mut Pl, fin: bool, al: QubitId, nb1: Option<QubitId>) {
        if !fin {
            assert_eq!(al, self.al_s);
            return;
        }
        assert!(nb1.is_some());
        b.x(al);
        let q = pl.get();
        let bz: Vec<(QubitId, bool)> = self.bq.iter().map(|&x| (x, true)).collect();
        and_into(b, pl, &bz, q, false);
        b.x(self.al_s);
        b.x(q);
        b.and_u(self.al_s, q, al);
        b.x(q);
        b.x(self.al_s);
        and_into(b, pl, &bz, q, true);
        pl.put(q);
        pl.put(al);
    }

    /// bq += c (mod 2^BB) for a classical c: unconditional increments of bq[i..] for the set bits of c (or decrements
    /// of the complement when that is shorter). Scratch is transient.
    fn bq_add_const(&self, b: &mut B, pl: &mut Pl, c: usize) {
        let n = BB;
        let m = 1usize << n;
        let c = c % m;
        if c == 0 {
            return;
        }
        let (cc, neg) = if (m - c).count_ones() < c.count_ones() { (m - c, true) } else { (c, false) };
        for i in 0..n {
            if (cc >> i) & 1 == 0 {
                continue;
            }
            let t = &self.bq[i..];
            if neg {
                for &q in t {
                    b.x(q);
                }
            }
            if t.len() > 1 {
                let anc = pl.get_n(t.len() - 2);
                inc(b, t[0], &t[1..], &anc);
                pl.put_n(&anc);
            }
            b.x(t[0]);
            if neg {
                for &q in t {
                    b.x(q);
                }
            }
        }
    }

    /// `bq_k_carry` with the carries kept in place on one running lane (lane A1b, lean >= 3): lane 0's carry
    /// t | k is made into it, lanes 1 .. BB-2 fold MAJ(t, k, c) = c ^ (t ^ c)(k ^ c) onto it (t, k keep t ^ c,
    /// k ^ c until the recording is played back inverted), the top lane ANDs into cy. One carry lane instead of
    /// BB - 1; one more Toffoli per folded lane on the way back.
    fn bq_k_carry_inplace(&self, b: &mut B, pl: &mut Pl, cy: QubitId) -> (Vec<super::builder::G>, Vec<QubitId>) {
        assert!(BB == KB + 1);
        let c = pl.get();
        b.begin();
        let (t, q) = (self.bq[0], self.k[0]);
        b.x(t);
        b.x(q);
        b.and_c(t, q, c);
        b.x(c);
        b.x(q);
        b.x(t);
        for i in 1..BB - 1 {
            let (t, q) = (self.bq[i], self.k[i]);
            b.cx(c, t);
            if !(a1b_mut("kcarry") && i == 2) { b.cx(c, q); }
            b.ccx(t, q, c);
        }
        b.and_c(self.bq[BB - 1], c, cy);
        (b.end(), vec![c])
    }

    /// Recording computing cy = [bq + k + 1 >= 2^BB] (carry out of the BB-bit sum bq + k with carry-in 1; with base
    /// 193, [b + k >= 257], the first step's end) with logical-AND carries from the pool; returns (recording, carry
    /// qubits to hand back). Playing it inverted uncomputes the carries.
    fn bq_k_carry(&self, b: &mut B, pl: &mut Pl, cy: QubitId) -> (Vec<super::builder::G>, Vec<QubitId>) {
        let g = pl.get_n(BB - 1);
        b.begin();
        // carries c_1 .. c_{BB-1} into g, carry out into cy; k is zero above bit KB-1
        let mut c: Option<QubitId> = None;
        for i in 0..BB {
            let tgt = if i + 1 == BB { cy } else { g[i] };
            let t = self.bq[i];
            let kq = if i < KB { Some(self.k[i]) } else { None };
            match (kq, c) {
                (Some(q), None) => {
                    // carry-in 1: c_1 = t | q
                    b.x(t);
                    b.x(q);
                    b.and_c(t, q, tgt);
                    b.x(tgt);
                    b.x(q);
                    b.x(t);
                }
                (None, Some(cq)) => b.and_c(t, cq, tgt),
                (Some(q), Some(cq)) => {
                    // MAJ(t, q, c) = c ^ (t ^ c)(q ^ c)
                    b.cx(cq, t);
                    b.cx(cq, q);
                    b.and_c(t, q, tgt);
                    b.cx(cq, q);
                    b.cx(cq, t);
                    // tgt = (t ^ c)(q ^ c); add c to make it MAJ
                    b.cx(cq, tgt);
                }
                (None, None) => {}
            }
            c = Some(tgt);
        }
        (b.end(), g)
    }
}

impl FhOne {
    /// Direct forward emission, with one fresh classical TT receipt per slot.
    /// The forward phase equals the recorded debt, not necessarily zero.
    pub fn forward_ghost(&mut self, b: &mut B, lay: &LayOne) -> GhostTrace {
        let receipts = b.fresh_bits(lay.s);
        let dl_receipts = b.fresh_bits(lay.s);
        let extra_flat = b.fresh_bits(16 * lay.s);
        let extra_receipts: Vec<[BitId; 16]> = extra_flat.chunks_exact(16)
            .map(|chunk| chunk.try_into().unwrap()).collect();
        let d1_receipts = b.fresh_bits(lay.s);
        let mut maps = Vec::with_capacity(lay.s);
        let mut hmr_sites = Vec::with_capacity(lay.s);
        let mut dl_hmr_sites = Vec::with_capacity(lay.s);
        let mut extra_hmr_sites = Vec::with_capacity(lay.s);
        let mut s5_carry_receipts = Vec::with_capacity(lay.s);
        let mut s5_carry_hmr_sites = Vec::with_capacity(lay.s);
        for (sigma, (&receipt, &dl_receipt)) in receipts.iter().zip(dl_receipts.iter()).enumerate() {
            maps.push(self.v.clone());
            let start = b.ops.len();
            self.s5_carry_bits.clear();
            let extras = extra_receipts[sigma];
            self.slot_mode(b, lay, sigma, SlotMode::ForwardGhost {
                receipt, dl_receipt: Some(dl_receipt), extras: Some(extras) });
            let sites: Vec<usize> = (start..b.ops.len()).filter(|&i| {
                b.ops[i].kind == OperationType::Hmr && b.ops[i].c_target == receipt
            }).collect();
            assert_eq!(sites.len(), 1, "one TT discharge per slot");
            hmr_sites.push(sites[0]);
            let dl_sites: Vec<usize> = (start..b.ops.len()).filter(|&i| {
                b.ops[i].kind == OperationType::Hmr && b.ops[i].c_target == dl_receipt
            }).collect();
            assert_eq!(dl_sites.len(), 1, "one dl discharge per slot");
            dl_hmr_sites.push(dl_sites[0]);
            extra_hmr_sites.push(std::array::from_fn(|j| {
                let sites: Vec<usize> = (start..b.ops.len()).filter(|&i| {
                    b.ops[i].kind == OperationType::Hmr && b.ops[i].c_target == extras[j]
                }).collect();
                assert_eq!(sites.len(), 1, "one extra discharge per slot/site");
                sites[0]
            }));
            let carry_sites: Vec<usize> = self.s5_carry_bits.iter().map(|&bit| {
                let sites: Vec<usize> = (start..b.ops.len()).filter(|&i| {
                    b.ops[i].kind == OperationType::Hmr && b.ops[i].c_target == bit
                }).collect();
                assert_eq!(sites.len(), 1, "one S5 carry discharge per ordinary lane");
                sites[0]
            }).collect();
            s5_carry_hmr_sites.push(carry_sites);
            s5_carry_receipts.push(self.s5_carry_bits.clone());
        }
        let mut owners = self.d.clone();
        owners.extend(self.all_meta());
        owners.push(self.par);
        GhostTrace { maps, receipts, hmr_sites, dl_receipts, dl_hmr_sites,
            extra_receipts, extra_hmr_sites, s5_carry_receipts, s5_carry_hmr_sites,
            d1_receipts, owners, exit_v: self.v.clone() }
    }

    /// Consumes exactly this traversal's receipt/map channel. The ordinary
    /// comparator is charged and replayed; measurements are never reversed.
    pub fn inverse_ghost(&mut self, b: &mut B, lay: &LayOne, trace: GhostTrace) {
        assert_eq!(trace.maps.len(), lay.s);
        assert_eq!(trace.receipts.len(), lay.s);
        assert_eq!(trace.hmr_sites.len(), lay.s);
        assert_eq!(trace.dl_receipts.len(), lay.s);
        assert_eq!(trace.dl_hmr_sites.len(), lay.s);
        assert_eq!(trace.extra_receipts.len(), lay.s);
        assert_eq!(trace.extra_hmr_sites.len(), lay.s);
        assert_eq!(trace.s5_carry_receipts.len(), lay.s);
        assert_eq!(trace.s5_carry_hmr_sites.len(), lay.s);
        assert_eq!(trace.d1_receipts.len(), lay.s);
        assert_eq!(self.v, trace.exit_v, "ghost lane-map channel mismatch");
        let mut owners = self.d.clone();
        owners.extend(self.all_meta());
        owners.push(self.par);
        assert_eq!(owners, trace.owners, "ghost owner channel mismatch");
        let ids: std::collections::BTreeMap<_, _> = trace.receipts.iter().enumerate()
            .map(|(i, &id)| (id, i)).collect();
        assert_eq!(ids.len(), lay.s, "duplicate ghost receipt");
        assert!(!ids.contains_key(&BitId(0)) && !ids.contains_key(&NO_BIT));
        let inverse_start = b.ops.len();
        self.inverse_boundaries.clear();
        let mut d1_covered = 0usize;
        let mut z0_covered = 0usize;
        for sigma in (0..lay.s).rev() {
            assert_eq!(trace.maps[sigma].len(), W1);
            self.v = trace.maps[sigma].clone();
            self.d1_record = self.d1_enabled;
            self.s5_carry_bits = trace.s5_carry_receipts[sigma].clone();
            self.d1_split = None;
            self.d1_z0_split = None;
            b.begin();
            self.slot_mode(b, lay, sigma, SlotMode::RecordInverseWithRepair {
                receipt: trace.receipts[sigma], dl_receipt: Some(trace.dl_receipts[sigma]),
                extras: Some(trace.extra_receipts[sigma]) });
            let rec = b.end();
            self.d1_record = false;
            let mut at = rec.len();
            if let Some(split) = self.d1_z0_split.take() {
                z0_covered += 1;
                assert!(split.cut <= at);
                b.play(&rec[split.cut..at], true);
                at = split.cut;
                assert_eq!(split.lits.len(), HIB);
                let start = b.ops.len();
                let receipt = b.fresh_bits(1)[0];
                b.hmr_to(split.z0, receipt);
                b.push_condition(receipt);
                let r = and_lits(b, &split.lits[..HIB - 1], split.m, &[split.anc]);
                b.play(&r, false);
                let (last, neg) = split.lits[HIB - 1];
                if neg { b.x(last); }
                b.cz(split.m, last);
                if neg { b.x(last); }
                b.play(&r, true);
                b.pop_condition();
                let emitted = &b.ops[start..];
                assert_eq!(emitted.iter().filter(|op| op.kind == OperationType::Hmr && op.c_target == receipt).count(), 1,
                    "one z0 receipt writer slot {sigma}");
                assert_eq!(emitted.iter().filter(|op| op.kind == OperationType::PushCondition && op.c_condition == receipt).count(), 1,
                    "one z0 receipt reader slot {sigma}");
                assert_eq!(emitted.iter().filter(|op| op.kind == OperationType::PopCondition).count(), 1,
                    "one z0 condition close slot {sigma}");
            }
            if let Some(split) = self.d1_split.take() {
                d1_covered += 1;
                assert!(split.cut <= at);
                let start = b.ops.len();
                b.play(&rec[split.cut..at], true);
                let receipt = trace.d1_receipts[sigma];
                b.hmr_to(split.dl, receipt);
                b.push_condition(receipt);
                onehot_scan(b, &split.btt, &split.pre, split.lo, split.hi, split.off, |b, j, o| {
                    b.z(o);
                    b.cz(o, split.vref[j]);
                });
                b.pop_condition();
                at = split.cut;
                let emitted = &b.ops[start..];
                assert_eq!(emitted.iter().filter(|op| op.kind == OperationType::Hmr && op.c_target == receipt).count(), 1,
                    "D1 one probe discharge slot {sigma}");
                assert_eq!(emitted.iter().filter(|op| op.kind == OperationType::PushCondition && op.c_condition == receipt).count(), 1,
                    "D1 one guarded regeneration slot {sigma}");
                assert_eq!(emitted.iter().filter(|op| op.kind == OperationType::PopCondition).count(), 1,
                    "D1 closed condition slot {sigma}");
            }
            b.play(&rec[..at], true);
            self.v = trace.maps[sigma].clone();
            self.inverse_boundaries.push(b.ops.len());
        }
        if self.d1_enabled {
            assert_eq!(d1_covered, lay.rows.iter().enumerate()
                .filter(|(sigma, r)| *sigma != 0 && *sigma < lay.trail_start && r[6].min(W1) > r[5]).count(),
                "D1 probe window coverage outside the classical/trimmed slots");
        }
        if self.d1_enabled && self.d1phi_z0 {
            assert_eq!(z0_covered, (1..lay.trail_start).filter(|sigma| sigma % 2 == 1).count(),
                "D1Phi z0 coverage outside odd active slots");
        }
        // Source-bound closure includes the interposed Div product and named
        // dy/lambda receipts: exactly one HMR writer and one inverse Z reader.
        let mut writes = vec![0; lay.s];
        let mut reads = vec![0; lay.s];
        for (pos, op) in b.ops.iter().enumerate() {
            if let Some(&i) = ids.get(&op.c_target) {
                assert_eq!(pos, trace.hmr_sites[i], "live TT receipt overwritten/declared");
                assert_eq!(op.kind, OperationType::Hmr);
                writes[i] += 1;
            }
            if let Some(&i) = ids.get(&op.c_condition) {
                assert!(pos >= inverse_start, "TT debt read before paired inverse");
                assert_eq!(op.kind, OperationType::Z);
                assert_eq!(op.q_target, b.ops[trace.hmr_sites[i]].q_target);
                reads[i] += 1;
            }
        }
        assert!(writes.iter().all(|&n| n == 1) && reads.iter().all(|&n| n == 1), "TT debt closure");
        let dl_ids: std::collections::BTreeMap<_, _> = trace.dl_receipts.iter().enumerate()
            .map(|(i, &id)| (id, i)).collect();
        assert_eq!(dl_ids.len(), lay.s, "duplicate dl receipt");
        assert!(!dl_ids.contains_key(&BitId(0)) && !dl_ids.contains_key(&NO_BIT));
        assert!(dl_ids.keys().all(|id| !ids.contains_key(id)), "dl/TT receipt overlap");
        let mut dl_writes = vec![0; lay.s];
        let mut dl_reads = vec![0; lay.s];
        for (pos, op) in b.ops.iter().enumerate() {
            if let Some(&i) = dl_ids.get(&op.c_target) {
                assert_eq!(pos, trace.dl_hmr_sites[i], "live dl receipt overwritten/declared");
                assert_eq!(op.kind, OperationType::Hmr);
                dl_writes[i] += 1;
            }
            if let Some(&i) = dl_ids.get(&op.c_condition) {
                assert!(pos >= inverse_start, "dl debt read before paired inverse");
                assert_eq!(op.kind, OperationType::Z);
                assert_eq!(op.q_target, b.ops[trace.dl_hmr_sites[i]].q_target);
                dl_reads[i] += 1;
            }
        }
        assert!(dl_writes.iter().all(|&n| n == 1) && dl_reads.iter().all(|&n| n == 1), "dl debt closure");
        let extra_ids: std::collections::BTreeMap<BitId, (usize, usize)> = trace.extra_receipts.iter()
            .enumerate().flat_map(|(i, row)| row.iter().enumerate().map(move |(j, &id)| (id, (i, j))))
            .collect();
        assert_eq!(extra_ids.len(), 16 * lay.s, "duplicate extra receipt");
        assert!(extra_ids.keys().all(|id| !ids.contains_key(id) && !dl_ids.contains_key(id)
            && *id != BitId(0) && *id != NO_BIT), "receipt channel overlap");
        let mut extra_writes = vec![[0usize; 16]; lay.s];
        let mut extra_reads = vec![[0usize; 16]; lay.s];
        for (pos, op) in b.ops.iter().enumerate() {
            if let Some(&(i, j)) = extra_ids.get(&op.c_target) {
                assert_eq!(pos, trace.extra_hmr_sites[i][j], "extra receipt overwritten/declared");
                assert_eq!(op.kind, OperationType::Hmr);
                extra_writes[i][j] += 1;
            }
            if let Some(&(i, j)) = extra_ids.get(&op.c_condition) {
                assert!(pos >= inverse_start, "extra debt read before paired inverse");
                assert_eq!(op.kind, OperationType::Z);
                assert_eq!(op.q_target, b.ops[trace.extra_hmr_sites[i][j]].q_target, "slot {i} extra {j}");
                extra_reads[i][j] += 1;
            }
        }
        assert!(extra_writes.iter().flatten().all(|&n| n == 1)
            && extra_reads.iter().flatten().all(|&n| n == 1), "extra debt closure");
        let carry_ids: std::collections::BTreeMap<BitId, (usize, usize)> = trace.s5_carry_receipts.iter()
            .enumerate().flat_map(|(i, row)| row.iter().enumerate().map(move |(j, &id)| (id, (i, j))))
            .collect();
        let carry_count: usize = trace.s5_carry_receipts.iter().map(Vec::len).sum();
        assert_eq!(carry_ids.len(), carry_count, "duplicate S5 carry receipt");
        assert!(carry_ids.keys().all(|id| !ids.contains_key(id) && !dl_ids.contains_key(id)
            && !extra_ids.contains_key(id) && *id != BitId(0) && *id != NO_BIT),
            "S5 carry receipt channel overlap");
        let mut carry_writes: Vec<Vec<usize>> = trace.s5_carry_receipts.iter().map(|row| vec![0; row.len()]).collect();
        let mut carry_reads = carry_writes.clone();
        for (pos, op) in b.ops.iter().enumerate() {
            if let Some(&(i, j)) = carry_ids.get(&op.c_target) {
                assert_eq!(pos, trace.s5_carry_hmr_sites[i][j], "S5 carry receipt overwritten");
                assert_eq!(op.kind, OperationType::Hmr);
                carry_writes[i][j] += 1;
            }
            if let Some(&(i, j)) = carry_ids.get(&op.c_condition) {
                assert!(pos >= inverse_start, "S5 carry debt read before paired inverse");
                assert_eq!(op.kind, OperationType::Z);
                carry_reads[i][j] += 1;
            }
        }
        assert!(carry_writes.iter().flatten().all(|&n| n == 1)
            && carry_reads.iter().flatten().all(|&n| n == 1), "S5 carry debt closure");
    }

    /// Forward traversal: all slots, emitting directly. Returns V's lane map at the start of every slot.
    pub fn forward(&mut self, b: &mut B, lay: &LayOne) -> Vec<Vec<QubitId>> {
        let mut maps = Vec::with_capacity(lay.s);
        for sigma in 0..lay.s {
            maps.push(self.v.clone());
            self.slot(b, lay, sigma);
        }
        maps
    }
    /// Exact inverse of `forward` (slot recordings played inverted, last slot first).
    pub fn inverse(&mut self, b: &mut B, lay: &LayOne, maps: &[Vec<QubitId>]) {
        for sigma in (0..lay.s).rev() {
            self.v = maps[sigma].clone();
            b.begin();
            self.slot(b, lay, sigma);
            let rec = b.end();
            b.play(&rec, true);
            self.v = maps[sigma].clone();
        }
    }
}

#[cfg(test)]
mod r10_c6_bqand_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};

    #[test]
    fn one_r10_c6_bqand_kernel() {
        let lay = LayOne::from_text(include_str!("sched_one.txt"), 0);
        for p in [false, true] {
            for controlled in [false, true] {
                for sub in [false, true] {
                    for inverse in [false, true] {
                        let mut b = B::new();
                        let d = b.alloc_n(W1);
                        let v = b.alloc_n(W1);
                        let par = b.alloc();
                        let dirty = b.alloc_n(256);
                        let f = FhOne::alloc(&mut b, d, v, &lay, par, dirty.clone(), 0);
                        assert_eq!(b.peak, *crate::point_add::PEAK);
                        let mut pl = Pl::new(&f.pool);
                        let ctl = controlled.then_some(f.fo);
                        f.bq_pi(&mut b, &mut pl, ctl, sub, inverse, p);
                        assert_eq!(pl.free.len(), POOL_1);
                        for batch in 0..32 {
                            let mut h = sha3::Shake256::default();
                            h.update(b"R10-C6-P0-BQAND-kernel");
                            let mut xof = h.finalize_xof();
                            let mut sim = Simulator::new(843, 1, &mut xof);
                            let mut initial = vec![0u64; 843];
                            for bit in 0..64 {
                                let input = batch * 64 + bit;
                                let bq = input & 63;
                                let hv = (input >> 6) & 15;
                                let control = (input >> 10) & 1;
                                for i in 0..BB {
                                    if (bq >> i) & 1 != 0 { initial[f.bq[i].0 as usize] |= 1u64 << bit; }
                                }
                                for i in 0..HIB {
                                    if (hv >> i) & 1 != 0 { initial[f.pi[i].0 as usize] |= 1u64 << bit; }
                                }
                                if control != 0 { initial[f.fo.0 as usize] |= 1u64 << bit; }
                            }
                            for (i, &q) in dirty.iter().enumerate() {
                                initial[q.0 as usize] = (i as u64).wrapping_mul(0x9e3779b97f4a7c15)
                                    ^ 0xa55a5aa55a5aa55a;
                            }
                            sim.qubits.copy_from_slice(&initial);
                            sim.apply_iter(b.ops.iter());
                            assert_eq!(sim.phase, 0, "phase {p}/{controlled}/{sub}/{inverse} batch {batch}");
                            for q in 0..843 {
                                if f.bq.iter().any(|x| x.0 as usize == q) { continue; }
                                assert_eq!(sim.qubits[q], initial[q],
                                    "all other wires q{q}, {p}/{controlled}/{sub}/{inverse} batch {batch}");
                            }
                            for bit in 0..64 {
                                let input = batch * 64 + bit;
                                let bq = input & 63;
                                let hv = (input >> 6) & 15;
                                let control = (input >> 10) & 1;
                                let pi = 2 * hv + usize::from(p);
                                let on = !controlled || control != 0;
                                let minus = sub ^ inverse;
                                let want = if !on { bq } else if minus {
                                    bq.wrapping_sub(pi) & 63
                                } else { (bq + pi) & 63 };
                                let got = (0..BB).fold(0usize, |v, i| {
                                    v | (((sim.qubits[f.bq[i].0 as usize] >> bit) & 1) as usize) << i
                                });
                                assert_eq!(got, want, "arithmetic input {input}, {p}/{controlled}/{sub}/{inverse}");
                            }
                        }
                        eprintln!("P0 BQAND p={p} controlled={controlled} sub={sub} inverse={inverse}: {} T, 2048 exact inputs, 843 wires", b.tof);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod a1b_bq_jit_tests {
    use super::*;
    use crate::sim::Simulator;
    use sha3::digest::{ExtendableOutput, Update};

    /// Lane A1b: the just-in-time controlled bq += pi (`bq_pi_form(.., jit = true)`, the S5 form at lean >= 2) on the
    /// build's layout, exhaustive over bq (64) x h (16) x control x p x sub x inverse, every other wire (incl. 256
    /// dirty passengers) unchanged, zero phase, scratch back to 0.
    #[test]
    fn a1b_bq_pi_jit_kernel() {
        let lay = LayOne::from_text(include_str!("sched_one.txt"), 0);
        for p in [false, true] {
            for sub in [false, true] {
                for inverse in [false, true] {
                    let mut b = B::new();
                    let d = b.alloc_n(W1);
                    let v = b.alloc_n(W1);
                    let par = b.alloc();
                    let dirty = b.alloc_n(256);
                    let f = FhOne::alloc(&mut b, d, v, &lay, par, dirty.clone(), 0);
                    let nq = b.width() as usize;
                    let mut pl = Pl::new(&f.pool);
                    let t0 = b.tof;
                    f.bq_pi_form(&mut b, &mut pl, Some(f.fo), sub, inverse, p, f.lean() >= 1);
                    assert_eq!(pl.free.len(), POOL_1);
                    for batch in 0..32 {
                        let mut h = sha3::Shake256::default();
                        h.update(b"A1B-BQ-JIT-kernel");
                        let mut xof = h.finalize_xof();
                        let mut sim = Simulator::new(nq, 1, &mut xof);
                        let mut initial = vec![0u64; nq];
                        for bit in 0..64 {
                            let input = batch * 64 + bit;
                            let bq = input & 63;
                            let hv = (input >> 6) & 15;
                            let control = (input >> 10) & 1;
                            for i in 0..BB {
                                if (bq >> i) & 1 != 0 { initial[f.bq[i].0 as usize] |= 1u64 << bit; }
                            }
                            for i in 0..HIB {
                                if (hv >> i) & 1 != 0 { initial[f.pi[i].0 as usize] |= 1u64 << bit; }
                            }
                            if control != 0 { initial[f.fo.0 as usize] |= 1u64 << bit; }
                        }
                        for (i, &q) in dirty.iter().enumerate() {
                            initial[q.0 as usize] = (i as u64).wrapping_mul(0x9e3779b97f4a7c15) ^ 0x3c3cc3c35a5aa5a5;
                        }
                        sim.qubits.copy_from_slice(&initial);
                        sim.apply_iter(b.ops.iter());
                        assert_eq!(sim.phase, 0, "phase {p}/{sub}/{inverse} batch {batch}");
                        for q in 0..nq {
                            if f.bq.iter().any(|x| x.0 as usize == q) { continue; }
                            assert_eq!(sim.qubits[q], initial[q], "other wire q{q}, {p}/{sub}/{inverse} batch {batch}");
                        }
                        for bit in 0..64 {
                            let input = batch * 64 + bit;
                            let bq = input & 63;
                            let hv = (input >> 6) & 15;
                            let control = (input >> 10) & 1;
                            let pi = 2 * hv + usize::from(p);
                            let minus = sub ^ inverse;
                            let want = if control == 0 { bq } else if minus { bq.wrapping_sub(pi) & 63 } else { (bq + pi) & 63 };
                            let got = (0..BB).fold(0usize, |acc, i| {
                                acc | (((sim.qubits[f.bq[i].0 as usize] >> bit) & 1) as usize) << i
                            });
                            assert_eq!(got, want, "input {input}, {p}/{sub}/{inverse}");
                        }
                    }
                    eprintln!("A1B BQ JIT p={p} sub={sub} inverse={inverse}: {} T, 2048 exact inputs", b.tof - t0);
                }
            }
        }
    }
}
