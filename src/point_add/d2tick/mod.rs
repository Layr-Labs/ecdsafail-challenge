//! D2 rail tick: one forward (or reverse) tick of the two-flat-array rail layout.
//!
//! Gate-for-gate port of the bitsliced construction `barrier/jl-probe/d2tick.py` (`build_tick`, `unary`,
//! `increment`, `le_const`). The construction is data independent: a tick is fully described by its public
//! window [`D2Win`] (array width `a`, tick index `t`, stack-count window `nlo..=nhi`, swap width `esw`, add width
//! `ead`), so it is planned once as an abstract gate list ([`D2Plan`]) and emitted forward or reverse.
//!
//! # Layout (tick `t`, `X = t mod 2` is the halved array, `Y = 1 - X`)
//!
//! Two arrays `P0`, `P1` of `a` wires each. Array `k` holds `[0, o_k)` typ wires (the freed LSB wires of
//! earlier ticks), `[o_k, B_k)` its rail NORMALIZED (`n = v` for `v >= 0`, `n = ~v` otherwise; the gap above
//! the rail top is 0), `[B_k, a)` its s-bit stack, filled downward from wire `a - 1`. `o_0 = ceil(t/2)`,
//! `o_1 = floor(t/2)`; `S_0 = ceil(N/2)`, `S_1 = floor(N/2)` with `N` the number of stacked s bits.
//! `sig[k]` is array `k`'s sign wire. The count register holds `N + 1` (LSB first), so its upper bits are
//! `M = ceil(N/2) = S_0`.
//!
//! # Tick
//!
//! 1. `c = n_X[0] ^ sig_X`. Masked exchange of positions `[1, Esw)` under `c AND [i < L0]`
//!    (`L0 = a - o_0 - S_0`): unmasked Fredkins below the window, a running flag fed by a `c`-controlled
//!    unary iteration over `M` inside it, the flag cleared by a controlled compare. Fredkin `(c; sig_X, sig_Y)`;
//!    `Y`'s LSB picks up `c`.
//! 2. Relabel: `o_X += 1`; the freed wire keeps `c`, then `typ_t = c ^ typ_{t-1} ^ [t > 0]`.
//! 3. Masked add `Y <- Y + ~n_X + NOT sig_X` over `[0, min(Ead, L0 - 1))` (Port: Gidney carries; operand mask,
//!    carry kill, up/down unary streams; the region's top bit tapped into `s` at the boundary, every lower
//!    bit renormalised by `CX(s)` in the down sweep, `sig_Y ^= s`).
//! 4. Push (B/C letters, `typ_t = 0`): unary iteration over `N` controlled by `NOT typ`; leaf `v` moves `s`
//!    into `P_{v & 1}[a - (v >> 1) - 1]` by a Fredkin; then `N += NOT typ`. `s` leaves the tick clean.
//!
//! The reverse tick is the exact mirror (gate list reversed, compute-AND <-> measured uncompute).
//!
//! # Promise (per shot)
//!
//! `N` in `[nlo, nhi]`; exactly one rail odd; `o_k + bl(v_k) + S_k <= a` before and after the tick; if `c`
//! then `o_0 + max bl(v) + S_0 <= a` and `max bl(v) <= esw`; `o_0 + S_0 + 1 + wad <= a` and `wad <= ead`
//! with `wad = max(bl n(H), bl n(O), bl n(r) + 1)`, `r = n(O) - n(H) - [H < 0]`; A letters (`typ_t = 1`) have
//! `s = 0`; the typ wire of tick `t - 1` satisfies `typ_t = c_t ^ typ_{t-1} ^ [t > 0]`.
//! Windows whose `nhi` exceeds what any valid shot can reach at this tick are clamped by [`D2Win::clamped`]
//! (a valid shot needs `L0 >= 2`). The window must also fit the arrays: `o_X + 1 + ead <= a`, `o_Y + ead <= a`.
//!
//! # Two constructions ([`D2Mode`])
//!
//! * `Port`: the add exactly as d2tick.py (1 Toffoli per unmasked position, Gidney carries held for the whole
//!   add). Scratch peaks at `ead - 1` plus three wires per window position: 256 at t = 0, 137 at t = 330.
//! * `LowRoom { gidney }`: same tick, in-place add (Cuccaro MAJ/UMA, 2 Toffoli per unmasked position; the
//!   window costs MAJ + MAJ^-1 + one flag-controlled sum bit per position). Scratch peak 8 at A = 288
//!   (+1 per Gidney bottom position, each of which saves 1 Toffoli).
//!
//! # API for the integration
//!
//! [`tick_forward`] / [`tick_reverse`] on [`D2Regs`] with the tick's [`D2Win`] (clamped inside) and a
//! [`D2Mode`]; [`plan`] gives the gate list, Toffoli (forward / reverse) and scratch peak without emitting.
//! Selftest: `D2_TICK_SELFTEST=1`; cost table: `D2_TICK_COST=<win file> [D2_TICK_COST_MODE=lowroom:<g>]`.

use super::builder::Builder;
use crate::circuit::QubitId;
use std::collections::BTreeMap;

pub mod selftest;

/// Public window of one tick.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct D2Win {
    /// Wires per rail array (288 in the design).
    pub a: usize,
    /// Tick index (array `t mod 2` is halved).
    pub t: usize,
    /// Stack-count window `N in [nlo, nhi]` (pre-tick).
    pub nlo: usize,
    pub nhi: usize,
    /// Exchange width (normalized bit length bound of both rails on shots with `c = 1`).
    pub esw: usize,
    /// Add width bound (`wad`, see the module doc).
    pub ead: usize,
}

impl D2Win {
    /// Origins `[o_0, o_1]` before the tick.
    pub fn origins(&self) -> [usize; 2] {
        [self.t.div_ceil(2), self.t / 2]
    }
    /// Clamp `nhi` to the largest `N` a valid shot can hold at this tick (`L0 = a - o_0 - ceil(N/2) >= 2`).
    pub fn clamped(&self) -> D2Win {
        let o0 = self.origins()[0];
        let mmax = self.a.saturating_sub(o0 + 2);
        let mut w = *self;
        w.nhi = w.nhi.min(2 * mmax);
        w.nlo = w.nlo.min(w.nhi);
        w
    }
    /// Count-register wires the tick reads (`bitlen(nhi + 2)`); a wider register is fine (its upper wires
    /// must hold 0 and are never touched).
    pub fn kbits(&self) -> usize {
        bitlen((self.nhi + 2) as u64)
    }
}

fn bitlen(x: u64) -> usize {
    (64 - x.leading_zeros()) as usize
}

/// Construction of the tick.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum D2Mode {
    /// The verified bitsliced construction of d2tick.py, gate for gate (Gidney carries on every add position,
    /// operand-mask / carry-kill wires in the window): scratch about `ead + 2 W + 7` (W = window positions).
    Port,
    /// Same tick with an in-place add: Cuccaro MAJ/UMA chain (2 Toffoli per position), the window handled by
    /// running the MAJ chain unconditionally, undoing it top-down and adding the sum bit under a region flag
    /// set by one compare plus one unary stream (3 Toffoli per window position); the lowest `gidney`
    /// positions keep Gidney carries (1 Toffoli per position, one scratch wire each). Compares use one
    /// scratch wire per bit.
    LowRoom { gidney: usize },
    /// LowRoom's tick under a scratch budget: the exchange's running flag lives on the (clean) `s` wire, and the top
    /// `fold` levels of each unary iteration / constant compare are not materialized: their literals are carried as
    /// a conjunction and folded into the first materialized AND (or into the leaf actions) as multi-controlled
    /// gates on borrowed dirty wires (the idle payload). `fold = [swap unary, swap compare, add compare, add unary]`.
    Lean { gidney: usize, fold: [u8; 4] },
}

/// The tick's quantum registers (wire ids in the caller's builder).
#[derive(Clone, Debug)]
pub struct D2Regs {
    /// The two rail arrays, `a` wires each, index 0 = bottom (LSB side).
    pub p: [Vec<QubitId>; 2],
    /// Sign wire per array.
    pub sig: [QubitId; 2],
    /// Count register holding `N + 1`, LSB first, at least `kbits()` wires.
    pub n: Vec<QubitId>,
    /// The s wire: clean (0) on entry and on exit of a forward tick.
    pub s: QubitId,
    /// Tick 0 only: the wire holding `typ_{-1}` (so `typ_0 = c_0 ^ typ_{-1}`). For `t >= 1` the previous typ
    /// wire is `p[Y][o_Y - 1]` (the previous tick's freed wire) and this field is ignored.
    pub typ0: Option<QubitId>,
    /// Lean mode: idle wires lent dirty to the multi-controlled gates (restored exactly); at least [`LEAN_DIRTY`].
    pub dirty: Vec<QubitId>,
}

// ─── Abstract gate list ─────────────────────────────────────────────────────────────────────

/// Toffoli attribution tags (same names as the Python model's tags).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Tag {
    SwapUnm,
    SwapMask,
    SwapUi,
    SwapCmp,
    SigSwap,
    AddUnm,
    AddMask,
    AddKill,
    AddOpmask,
    AddUiUp,
    AddUiDn,
    Tap,
    Push,
    PushUi,
    NInc,
    /// Low-room mode: masked sum under the region flag.
    AddCsum,
    /// Low-room mode: the region flag's initial compare.
    AddCmp,
}

impl Tag {
    pub fn name(self) -> &'static str {
        match self {
            Tag::SwapUnm => "swap_unm",
            Tag::SwapMask => "swap_mask",
            Tag::SwapUi => "swap_ui",
            Tag::SwapCmp => "swap_cmp",
            Tag::SigSwap => "sig_swap",
            Tag::AddUnm => "add_unm",
            Tag::AddMask => "add_mask",
            Tag::AddKill => "add_kill",
            Tag::AddOpmask => "add_opmask",
            Tag::AddUiUp => "add_ui_up",
            Tag::AddUiDn => "add_ui_dn",
            Tag::Tap => "tap",
            Tag::Push => "push",
            Tag::PushUi => "push_ui",
            Tag::NInc => "N_inc",
            Tag::AddCsum => "add_csum",
            Tag::AddCmp => "add_cmp",
        }
    }
}

/// One abstract gate over wire slots (`slot < n_io`: an I/O wire; otherwise a scratch slot).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum G {
    X(u32),
    Cx(u32, u32),
    /// Plain exchange (a degenerate Fredkin with a constant-one control): Clifford.
    Swap(u32, u32),
    /// `t ^= a AND b` on a non-clean target (self-inverse).
    Ccx(u32, u32, u32, Tag),
    /// Controlled exchange `(c; a, b)`: 1 Toffoli.
    Fred(u32, u32, u32, Tag),
    /// `t = a AND b` into a clean target: 1 Toffoli.
    AndC(u32, u32, u32, Tag),
    /// Measured uncompute of `t == a AND b`: HMR + classically controlled CZ, 0 Toffoli.
    AndU(u32, u32, u32, Tag),
    Alloc(u32),
    Release(u32),
    /// `t = AND(ctrls)` into a clean temporary (`Rec::mops[i]`), on borrowed dirty wires: mcx_t(n) Toffoli.
    MAndC(u32),
    /// Measured uncompute of `t == AND(ctrls)` (HMR + conditional phase on the controls).
    MAndU(u32),
    /// `t ^= AND(ctrls)` on a non-clean target (self-inverse), on borrowed dirty wires.
    Mcx(u32),
}

/// A multi-controlled operation: controls (slots, all positive: negations are explicit X gates around it), target.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MOp {
    pub ctrls: Vec<u32>,
    pub t: u32,
    pub tag: Tag,
}

/// Toffolis of `t ^= AND(n controls)` on `n - 2` dirty wires (Barenco et al., Lemma 7.2).
pub fn mcx_t(n: usize) -> usize {
    match n {
        0 | 1 => 0,
        2 => 1,
        _ => 4 * (n - 2),
    }
}

/// Toffoli-class gates of the phase `(-1)^AND(n wires)`: Z / CZ (n <= 2), one CCZ (n = 3), else a dirty wire toggled
/// by the first n - 2 around two CCZs.
pub fn phase_t(n: usize) -> usize {
    match n {
        0..=2 => 0,
        3 => 1,
        _ => 2 * mcx_t(n - 2) + 2,
    }
}

/// Control that may be the constant 1 (a unary iteration whose promise fixes every selector bit).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Ctl {
    One,
    W(u32),
}

/// Gate recorder with scratch-slot allocation.
pub struct Rec {
    pub gates: Vec<G>,
    n_io: u32,
    next: u32,
    free: Vec<u32>,
    live: u32,
    peak: u32,
    /// Multi-controlled ops referenced by `G::MAndC` / `G::MAndU` / `G::Mcx`.
    pub mops: Vec<MOp>,
    /// Lean mode: the component whose temporaries are being allocated (index into `comp_peak`).
    comp: Option<usize>,
    /// Peak live scratch while each component was active: swap unary, swap compare, add compare, add unary.
    comp_peak: [u32; 4],
}

impl Rec {
    fn new(n_io: u32) -> Self {
        Rec { gates: Vec::new(), n_io, next: n_io, free: Vec::new(), live: 0, peak: 0, mops: Vec::new(), comp: None, comp_peak: [0; 4] }
    }
    fn alloc(&mut self) -> u32 {
        let i = self.free.pop().unwrap_or_else(|| {
            let i = self.next;
            self.next += 1;
            i
        });
        self.live += 1;
        self.peak = self.peak.max(self.live);
        if let Some(c) = self.comp {
            self.comp_peak[c] = self.comp_peak[c].max(self.live);
        }
        self.gates.push(G::Alloc(i));
        i
    }
    fn release(&mut self, i: u32) {
        debug_assert!(i >= self.n_io);
        self.live -= 1;
        self.free.push(i);
        self.gates.push(G::Release(i));
    }
    fn x(&mut self, a: u32) {
        self.gates.push(G::X(a));
    }
    fn cx(&mut self, a: u32, b: u32) {
        assert_ne!(a, b);
        self.gates.push(G::Cx(a, b));
    }
    fn cxc(&mut self, c: Ctl, t: u32) {
        match c {
            Ctl::One => self.x(t),
            Ctl::W(c) => self.cx(c, t),
        }
    }
    fn ccx(&mut self, a: u32, b: u32, t: u32, tag: Tag) {
        assert!(a != b && a != t && b != t);
        self.gates.push(G::Ccx(a, b, t, tag));
    }
    fn ccxc(&mut self, c: Ctl, b: u32, t: u32, tag: Tag) {
        match c {
            Ctl::One => self.cx(b, t),
            Ctl::W(c) => self.ccx(c, b, t, tag),
        }
    }
    fn fred(&mut self, c: u32, a: u32, b: u32, tag: Tag) {
        assert!(a != b && a != c && b != c);
        self.gates.push(G::Fred(c, a, b, tag));
    }
    fn fredc(&mut self, c: Ctl, a: u32, b: u32, tag: Tag) {
        match c {
            Ctl::One => self.gates.push(G::Swap(a, b)),
            Ctl::W(c) => self.fred(c, a, b, tag),
        }
    }
    fn and_c(&mut self, a: u32, b: u32, t: u32, tag: Tag) {
        assert!(a != b && a != t && b != t);
        self.gates.push(G::AndC(a, b, t, tag));
    }
    fn and_u(&mut self, a: u32, b: u32, t: u32, tag: Tag) {
        assert!(a != b && a != t && b != t);
        self.gates.push(G::AndU(a, b, t, tag));
    }
    fn negs(&mut self, lits: &[(u32, bool)]) {
        for &(w, n) in lits {
            if n {
                self.x(w);
            }
        }
    }
    fn mop(&mut self, lits: &[(u32, bool)], t: u32, tag: Tag) -> u32 {
        let ctrls: Vec<u32> = lits.iter().map(|&(w, _)| w).collect();
        for (i, &c) in ctrls.iter().enumerate() {
            assert!(c != t && !ctrls[..i].contains(&c), "multi-controlled op: aliased wires {ctrls:?} -> {t}");
        }
        self.mops.push(MOp { ctrls, t, tag });
        self.mops.len() as u32 - 1
    }
    /// `t ^= AND(lits)` (literal = (wire, negated)); no literal = the constant 1.
    fn tog(&mut self, lits: &[(u32, bool)], t: u32, tag: Tag) {
        self.negs(lits);
        match lits.len() {
            0 => self.x(t),
            1 => self.cx(lits[0].0, t),
            2 => self.ccx(lits[0].0, lits[1].0, t, tag),
            _ => {
                let i = self.mop(lits, t, tag);
                self.gates.push(G::Mcx(i));
            }
        }
        self.negs(lits);
    }
    /// A fresh temporary holding AND(lits) (at least 2 literals).
    fn mand_c(&mut self, lits: &[(u32, bool)], tag: Tag) -> u32 {
        assert!(lits.len() >= 2);
        let t = self.alloc();
        self.negs(lits);
        if lits.len() == 2 {
            self.and_c(lits[0].0, lits[1].0, t, tag);
        } else {
            let i = self.mop(lits, t, tag);
            self.gates.push(G::MAndC(i));
        }
        self.negs(lits);
        t
    }
    /// Uncompute and release a temporary holding AND(lits).
    fn mand_u(&mut self, lits: &[(u32, bool)], t: u32, tag: Tag) {
        assert!(lits.len() >= 2);
        self.negs(lits);
        if lits.len() == 2 {
            self.and_u(lits[0].0, lits[1].0, t, tag);
        } else {
            let i = self.mop(lits, t, tag);
            self.gates.push(G::MAndU(i));
        }
        self.negs(lits);
        self.release(t);
    }
}

/// A unary-iteration / compare node in Lean mode: the constant 1, a materialized wire, or a virtual conjunction of
/// literals `(wire, negated)` not materialized (its literals are folded into later gates).
#[derive(Clone, Debug)]
pub enum Nd {
    One,
    W(u32),
    V(Vec<(u32, bool)>),
}

impl Nd {
    fn lits(&self) -> Vec<(u32, bool)> {
        match self {
            Nd::One => Vec::new(),
            Nd::W(w) => vec![(*w, false)],
            Nd::V(l) => l.clone(),
        }
    }
    fn with(&self, lit: (u32, bool)) -> Vec<(u32, bool)> {
        let mut l = self.lits();
        l.push(lit);
        l
    }
}

/// `t ^= nd AND (extra literals)`.
fn nd_tog(r: &mut Rec, nd: &Nd, extra: &[(u32, bool)], t: u32, tag: Tag) {
    let mut l = nd.lits();
    l.extend_from_slice(extra);
    r.tog(&l, t, tag);
}

/// How a materialized node is undone.
enum Undo {
    None,
    X(u32),
    And(Vec<(u32, bool)>, u32),
}

/// Materialize a conjunction: the constant 1 (no literal), the literal's own wire (one literal, X'ed while live if
/// negated), or a fresh AND temporary.
fn materialize(r: &mut Rec, lits: Vec<(u32, bool)>, tag: Tag) -> (Nd, Undo) {
    match lits.len() {
        0 => (Nd::One, Undo::None),
        1 => {
            let (w, n) = lits[0];
            if n {
                r.x(w);
                (Nd::W(w), Undo::X(w))
            } else {
                (Nd::W(w), Undo::None)
            }
        }
        _ => {
            let t = r.mand_c(&lits, tag);
            (Nd::W(t), Undo::And(lits, t))
        }
    }
}

fn undo(r: &mut Rec, u: Undo, tag: Tag) {
    match u {
        Undo::None => {}
        Undo::X(w) => r.x(w),
        Undo::And(l, t) => r.mand_u(&l, t, tag),
    }
}

type CbN<'a> = dyn FnMut(&mut Rec, i64, &Nd) + 'a;

/// Unary iteration with the top `fold` checked levels left virtual (Lean mode). Same leaves, promise and order as
/// [`Unary`]; a leaf receives its control as an [`Nd`] (virtual when every level above it was folded).
struct UnaryF<'r> {
    reg: &'r [u32],
    lo: i64,
    hi: i64,
    la: i64,
    lb: i64,
    desc: bool,
    tag: Tag,
    fold: usize,
}

impl UnaryF<'_> {
    fn node(&self, r: &mut Rec, c: Nd, prefix: i64, b: i32, depth: usize, cb: &mut CbN<'_>) {
        if b < 0 {
            cb(r, prefix, &c);
            return;
        }
        let rng = [(prefix, prefix | ((1i64 << b) - 1)), (prefix | (1i64 << b), prefix | ((1i64 << (b + 1)) - 1))];
        let inp = [inter(rng[0].0, rng[0].1, self.lo, self.hi), inter(rng[1].0, rng[1].1, self.lo, self.hi)];
        let lv = [
            inp[0] && inter(rng[0].0, rng[0].1, self.la, self.lb),
            inp[1] && inter(rng[1].0, rng[1].1, self.la, self.lb),
        ];
        if !(lv[0] || lv[1]) {
            return;
        }
        if inp[0] != inp[1] {
            let q = if inp[0] { 0 } else { 1 };
            self.node(r, c, prefix | (q << b), b - 1, depth, cb);
            return;
        }
        let rw = self.reg[b as usize];
        let pref = if self.desc { [1i64, 0] } else { [0i64, 1] };
        let order: Vec<i64> = pref.iter().copied().filter(|&q| lv[q as usize]).collect();
        if depth < self.fold {
            for &q in &order {
                let child = Nd::V(c.with((rw, q == 0)));
                self.node(r, child, prefix | (q << b), b - 1, depth + 1, cb);
            }
            return;
        }
        let first = order[0];
        let (n1, u1) = materialize(r, c.with((rw, first == 0)), self.tag);
        self.node(r, n1.clone(), prefix | (first << b), b - 1, depth + 1, cb);
        if order.len() == 1 {
            undo(r, u1, self.tag);
            return;
        }
        let second = 1 - first;
        // flip the first child into the second: AND(c, lit) ^ AND(c) = AND(c, NOT lit)
        let u2 = match u1 {
            Undo::None | Undo::X(_) => {
                // one literal, materialized in place on the register wire (c = 1)
                r.x(rw);
                if second == 0 { Undo::X(rw) } else { Undo::None }
            }
            Undo::And(_, t) => {
                let cl = c.lits();
                r.tog(&cl, t, self.tag);
                Undo::And(c.with((rw, second == 0)), t)
            }
        };
        let n2 = match &u2 {
            Undo::And(_, t) => Nd::W(*t),
            _ => Nd::W(rw),
        };
        self.node(r, n2, prefix | (second << b), b - 1, depth + 1, cb);
        undo(r, u2, self.tag);
    }
}

#[allow(clippy::too_many_arguments)]
fn unary_f(r: &mut Rec, ctrl: Nd, reg: &[u32], lo: i64, hi: i64, live: (i64, i64), desc: bool, tag: Tag, fold: usize, cb: &mut CbN<'_>) {
    let u = UnaryF { reg, lo, hi, la: live.0, lb: live.1, desc, tag, fold };
    u.node(r, ctrl, 0, reg.len() as i32 - 1, 0, cb);
}

/// `out ^= ctrl AND [reg <= kk]` with the top `fold` levels of the equality chain left virtual (Lean mode). The
/// materialized levels follow [`le_const_lean`] (one wire per level; a level's "less" and "continue" nodes share it).
fn le_const_f(r: &mut Rec, reg: &[u32], kk: i64, ctrl: Nd, out: u32, tag: Tag, fold: usize) {
    let k = reg.len();
    if kk < 0 {
        return;
    }
    if kk >= (1i64 << k) - 1 {
        nd_tog(r, &ctrl, &[], out, tag);
        return;
    }
    let mut eq = ctrl;
    let mut made: Vec<Undo> = Vec::new();
    for (depth, j) in (0..k).rev().enumerate() {
        let rw = reg[j];
        let one = (kk >> j) & 1 == 1;
        if depth < fold {
            if one {
                nd_tog(r, &eq, &[(rw, true)], out, tag); // less here
            }
            eq = Nd::V(eq.with((rw, !one)));
            continue;
        }
        // w = eq AND NOT r_j ("less" when kk_j = 1); then w ^= eq gives eq AND r_j ("continue")
        let (w, u) = materialize(r, eq.with((rw, true)), tag);
        let Nd::W(wq) = w else { unreachable!() };
        let u = if one {
            r.cx(wq, out);
            match u {
                Undo::X(x) => {
                    // in place (eq = 1): w = NOT r; NOT r ^ 1 = r
                    r.x(x);
                    Undo::None
                }
                Undo::And(_, t) => {
                    let el = eq.lits();
                    r.tog(&el, t, tag);
                    Undo::And(eq.with((rw, false)), t)
                }
                Undo::None => unreachable!("a negated literal is X'ed in place"),
            }
        } else {
            u
        };
        made.push(u);
        eq = Nd::W(wq);
    }
    nd_tog(r, &eq, &[], out, tag); // equal -> <=
    for u in made.into_iter().rev() {
        undo(r, u, tag);
    }
}

// ─── Primitives (ports of d2tick.py) ──────────────────────────────────────────────────────

type Cb<'a> = dyn FnMut(&mut Rec, i64, Ctl) + 'a;

struct Unary<'r> {
    reg: &'r [u32],
    lo: i64,
    hi: i64,
    la: i64,
    lb: i64,
    desc: bool,
    tag: Tag,
}

fn inter(x: i64, y: i64, p: i64, q: i64) -> bool {
    !(y < p || x > q)
}

impl Unary<'_> {
    /// Visit the live values `v in [la, lb]` under the promise `reg in [lo, hi]`; `cb(v, leaf)` with
    /// `leaf = ctrl AND [reg == v]`. One AND per split node; uncomputed by measurement.
    fn node(&self, r: &mut Rec, c: Ctl, prefix: i64, b: i32, cb: &mut Cb<'_>) {
        if b < 0 {
            cb(r, prefix, c);
            return;
        }
        let rng = [(prefix, prefix | ((1i64 << b) - 1)), (prefix | (1i64 << b), prefix | ((1i64 << (b + 1)) - 1))];
        let inp = [inter(rng[0].0, rng[0].1, self.lo, self.hi), inter(rng[1].0, rng[1].1, self.lo, self.hi)];
        let lv = [
            inp[0] && inter(rng[0].0, rng[0].1, self.la, self.lb),
            inp[1] && inter(rng[1].0, rng[1].1, self.la, self.lb),
        ];
        if !(lv[0] || lv[1]) {
            return;
        }
        if inp[0] != inp[1] {
            // The promise fixes this bit: no check.
            let q = if inp[0] { 0 } else { 1 };
            self.node(r, c, prefix | (q << b), b - 1, cb);
            return;
        }
        let rw = self.reg[b as usize];
        let pref = if self.desc { [1i64, 0] } else { [0i64, 1] };
        let order: Vec<i64> = pref.iter().copied().filter(|&q| lv[q as usize]).collect();
        if order.len() == 1 {
            let q = order[0];
            match c {
                Ctl::One => {
                    if q == 0 {
                        r.x(rw);
                    }
                    self.node(r, Ctl::W(rw), prefix | (q << b), b - 1, cb);
                    if q == 0 {
                        r.x(rw);
                    }
                }
                Ctl::W(cw) => {
                    let a = r.alloc();
                    if q == 0 {
                        r.x(rw);
                    }
                    r.and_c(cw, rw, a, self.tag);
                    self.node(r, Ctl::W(a), prefix | (q << b), b - 1, cb);
                    r.and_u(cw, rw, a, self.tag);
                    if q == 0 {
                        r.x(rw);
                    }
                    r.release(a);
                }
            }
            return;
        }
        let first = order[0];
        match c {
            Ctl::One => {
                if first == 0 {
                    r.x(rw);
                }
                self.node(r, Ctl::W(rw), prefix | (first << b), b - 1, cb);
                r.x(rw);
                self.node(r, Ctl::W(rw), prefix | ((1 - first) << b), b - 1, cb);
                if first == 1 {
                    r.x(rw);
                }
            }
            Ctl::W(cw) => {
                let a = r.alloc();
                if first == 0 {
                    r.x(rw);
                }
                r.and_c(cw, rw, a, self.tag);
                if first == 0 {
                    r.x(rw);
                }
                self.node(r, Ctl::W(a), prefix | (first << b), b - 1, cb);
                r.cx(cw, a); // ctrl AND the other value of bit b
                self.node(r, Ctl::W(a), prefix | ((1 - first) << b), b - 1, cb);
                if first == 1 {
                    r.x(rw);
                }
                r.and_u(cw, rw, a, self.tag);
                if first == 1 {
                    r.x(rw);
                }
                r.release(a);
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn unary(r: &mut Rec, ctrl: Ctl, reg: &[u32], lo: i64, hi: i64, live: (i64, i64), desc: bool, tag: Tag, cb: &mut Cb<'_>) {
    let u = Unary { reg, lo, hi, la: live.0, lb: live.1, desc, tag };
    u.node(r, ctrl, 0, reg.len() as i32 - 1, cb);
}

/// `reg += ctrl` (prefix ANDs computed, applied top-down, uncomputed by measurement).
fn increment(r: &mut Rec, reg: &[u32], ctrl: Option<u32>, tag: Tag) {
    let k = reg.len();
    let mut pre: Vec<Option<u32>> = vec![None; k];
    match ctrl {
        None => {
            if k >= 2 {
                pre[1] = Some(reg[0]);
            }
        }
        Some(c) => {
            pre[0] = Some(c);
            if k >= 2 {
                let p = r.alloc();
                r.and_c(c, reg[0], p, tag);
                pre[1] = Some(p);
            }
        }
    }
    for j in 2..k {
        let p = r.alloc();
        r.and_c(pre[j - 1].unwrap(), reg[j - 1], p, tag);
        pre[j] = Some(p);
    }
    for j in (1..k).rev() {
        r.cx(pre[j].unwrap(), reg[j]);
        if j >= 2 || ctrl.is_some() {
            if j >= 2 {
                r.and_u(pre[j - 1].unwrap(), reg[j - 1], pre[j].unwrap(), tag);
            } else {
                r.and_u(ctrl.unwrap(), reg[0], pre[1].unwrap(), tag);
            }
            r.release(pre[j].unwrap());
        }
    }
    match ctrl {
        None => r.x(reg[0]),
        Some(c) => r.cx(c, reg[0]),
    }
}

/// `out ^= ctrl AND [reg <= kk]` (one AND per bit, uncomputed by measurement).
fn le_const(r: &mut Rec, reg: &[u32], kk: i64, ctrl: u32, out: u32, tag: Tag) {
    let k = reg.len();
    if kk >= (1i64 << k) - 1 {
        r.cx(ctrl, out);
        return;
    }
    enum Made {
        One(u32, u32, u32, u32),
        Zero(u32, u32, u32),
    }
    let mut eq = ctrl;
    let mut made = Vec::new();
    for j in (0..k).rev() {
        let rw = reg[j];
        if (kk >> j) & 1 == 1 {
            let lt = r.alloc();
            r.x(rw);
            r.and_c(eq, rw, lt, tag);
            r.x(rw);
            r.cx(lt, out);
            let n = r.alloc();
            r.cx(eq, n);
            r.cx(lt, n);
            made.push(Made::One(eq, rw, lt, n));
            eq = n;
        } else {
            let n = r.alloc();
            r.x(rw);
            r.and_c(eq, rw, n, tag);
            r.x(rw);
            made.push(Made::Zero(eq, rw, n));
            eq = n;
        }
    }
    r.cx(eq, out);
    for m in made.into_iter().rev() {
        match m {
            Made::One(e, rw, lt, n) => {
                r.cx(lt, n);
                r.cx(e, n);
                r.release(n);
                r.x(rw);
                r.and_u(e, rw, lt, tag);
                r.x(rw);
                r.release(lt);
            }
            Made::Zero(e, rw, n) => {
                r.x(rw);
                r.and_u(e, rw, n, tag);
                r.x(rw);
                r.release(n);
            }
        }
    }
}

fn and_cc(r: &mut Rec, a: Ctl, b: u32, t: u32, tag: Tag) {
    match a {
        Ctl::One => r.cx(b, t),
        Ctl::W(a) => r.and_c(a, b, t, tag),
    }
}

fn and_uc(r: &mut Rec, a: Ctl, b: u32, t: u32, tag: Tag) {
    match a {
        Ctl::One => r.cx(b, t),
        Ctl::W(a) => r.and_u(a, b, t, tag),
    }
}

/// `out ^= ctrl AND [reg <= kk]` with one scratch wire per bit (the "continue" flag of a one-bit level is
/// made in place from its "less" flag). Same ANDs as [`le_const`]; a constant-one control costs none at the
/// top level.
fn le_const_lean(r: &mut Rec, reg: &[u32], kk: i64, ctrl: Ctl, out: u32, tag: Tag) {
    let k = reg.len();
    if kk < 0 {
        return;
    }
    if kk >= (1i64 << k) - 1 {
        r.cxc(ctrl, out);
        return;
    }
    let mut eq = ctrl;
    let mut made: Vec<(bool, Ctl, u32, u32)> = Vec::new();
    for j in (0..k).rev() {
        let rw = reg[j];
        let w = r.alloc();
        r.x(rw);
        and_cc(r, eq, rw, w, tag); // w = eq AND NOT r_j
        r.x(rw);
        let one = (kk >> j) & 1 == 1;
        if one {
            r.cx(w, out); // less here
            r.cxc(eq, w); // w = eq AND r_j: continue
        }
        made.push((one, eq, rw, w));
        eq = Ctl::W(w);
    }
    r.cxc(eq, out); // equal -> <=
    for (one, e, rw, w) in made.into_iter().rev() {
        if one {
            r.cxc(e, w);
        }
        r.x(rw);
        and_uc(r, e, rw, w, tag);
        r.x(rw);
        r.release(w);
    }
}

/// In-place masked add `b += a + cin` over `[0, min(L, top))`, `L = a_arr - o0 - 1 - M` (M on `np1`), wrapped
/// there; the region's top bit is tapped into `s` and every region bit renormalised by `CX(s)` (as the Port add).
#[allow(clippy::too_many_arguments)]
fn add_inplace(r: &mut Rec, av: &[u32], bv: &[u32], cin: u32, s: u32, top: i64, unm: i64, np1: &[u32], mlo: i64,
               mhi: i64, a_arr: i64, o0: i64, gidney: usize, lean: Option<[u8; 2]>) {
    let tu = top as usize;
    let g = gidney.min(tu - 1).min((unm - 1) as usize); // Gidney positions [0, g)
    let window = unm < top;
    let leafpos = |v: i64| a_arr - o0 - 1 - v;
    let mut gc: Vec<u32> = Vec::new(); // gc[i] = carry into position i + 1, i < g
    let cw = |i: usize, gc: &[u32]| -> u32 {
        if i == 0 {
            cin
        } else if i <= g {
            gc[i - 1]
        } else {
            av[i - 1]
        }
    };
    let tag = |i: usize| if (i as i64) < unm { Tag::AddUnm } else { Tag::AddMask };
    // up sweep: Gidney steps, then the MAJ chain (a_i <- carry out, b_i <- a ^ b, c <- a ^ c)
    for i in 0..g {
        let c = cw(i, &gc);
        r.cx(c, av[i]);
        r.cx(c, bv[i]);
        let tt = r.alloc();
        r.and_c(av[i], bv[i], tt, Tag::AddUnm);
        r.cx(c, tt);
        gc.push(tt);
    }
    for i in g..tu - 1 {
        let c = cw(i, &gc);
        r.cx(av[i], bv[i]);
        r.cx(av[i], c);
        r.ccx(c, bv[i], av[i], tag(i));
    }
    // region flag e: [L >= top] now, toggled on at each boundary (window only)
    let e = if window {
        let e = r.alloc();
        match lean {
            Some(f) => {
                r.comp = Some(2);
                le_const_f(r, np1, a_arr - o0 - 1 - top, Nd::One, e, Tag::AddCmp, f[0] as usize);
                r.comp = None;
            }
            None => le_const_lean(r, np1, a_arr - o0 - 1 - top, Ctl::One, e, Tag::AddCmp),
        }
        Some(e)
    } else {
        None
    };
    // down sweep at position i (>= g); `cond`: sum under e; `leaf`: the region's top is i
    let dn = |r: &mut Rec, gc: &[u32], i: usize, leaf: Option<&Nd>, cond: bool| {
        let c = cw(i, gc);
        let (a, b) = (av[i], bv[i]);
        if cond {
            if i < tu - 1 {
                r.ccx(c, b, a, tag(i)); // MAJ^-1
                r.cx(a, c);
                r.cx(a, b);
            }
            if let Some(l) = leaf {
                nd_tog(r, l, &[], e.unwrap(), Tag::AddUiDn);
            }
            r.cx(c, a);
            r.ccx(e.unwrap(), a, b, Tag::AddCsum);
            r.cx(c, a);
        } else if i < tu - 1 {
            r.ccx(c, b, a, tag(i)); // UMA
            r.cx(a, c);
            r.cx(c, b);
        } else {
            r.cx(a, b);
            r.cx(c, b);
        }
        if i == tu - 1 {
            match e {
                Some(e) => r.ccx(e, b, s, Tag::Tap),
                None => r.cx(b, s),
            }
        } else if let Some(l) = leaf {
            nd_tog(r, l, &[(b, false)], s, Tag::Tap);
        }
        r.cx(s, b);
    };
    let mut st = tu as i64 - 1; // next position down
    if window {
        let vs: Vec<i64> = (mlo..=mhi).filter(|&v| unm <= leafpos(v) && leafpos(v) <= top - 1).collect();
        assert!(!vs.is_empty());
        let live = (*vs.iter().min().unwrap(), *vs.iter().max().unwrap());
        let mut cbn = |r: &mut Rec, v: i64, leaf: &Nd| {
            let l = leafpos(v);
            while st >= l {
                dn(r, &gc, st as usize, None, true);
                st -= 1;
            }
            assert_eq!(st, l - 1);
            dn(r, &gc, st as usize, Some(leaf), true);
            st -= 1;
        };
        match lean {
            Some(f) => {
                r.comp = Some(3);
                unary_f(r, Nd::One, np1, mlo, mhi, live, false, Tag::AddUiDn, f[1] as usize, &mut cbn);
                r.comp = None;
            }
            None => {
                let mut cb = |r: &mut Rec, v: i64, leaf: Ctl| {
                    let nd = match leaf {
                        Ctl::One => Nd::One,
                        Ctl::W(w) => Nd::W(w),
                    };
                    cbn(r, v, &nd)
                };
                unary(r, Ctl::One, np1, mlo, mhi, live, false, Tag::AddUiDn, &mut cb);
            }
        }
    }
    while st >= g as i64 {
        dn(r, &gc, st as usize, None, false);
        st -= 1;
    }
    for i in (0..g).rev() {
        let c = cw(i, &gc);
        let tt = gc[i];
        r.cx(c, tt);
        r.and_u(av[i], bv[i], tt, Tag::AddUnm);
        r.release(tt);
        r.cx(c, av[i]);
        r.cx(av[i], bv[i]);
        r.cx(s, bv[i]);
    }
    if let Some(e) = e {
        r.x(e); // every valid shot has passed its boundary (or started inside)
        r.release(e);
    }
}

// ─── The tick ─────────────────────────────────────────────────────────────────────────────

/// Slot layout of the I/O wires inside a plan.
#[derive(Clone, Debug)]
pub struct Io {
    pub a: usize,
    pub kb: usize,
    /// Borrowed dirty wires (Lean mode's multi-controlled gates); bound to idle payload wires at emission.
    pub nd: usize,
}

/// Dirty I/O slots of a Lean plan (enough for every multi-controlled op of a tick).
pub const LEAN_DIRTY: usize = 16;

impl Io {
    pub fn p(&self, k: usize, i: usize) -> u32 {
        assert!(i < self.a, "array index {i} out of range {}", self.a);
        (k * self.a + i) as u32
    }
    pub fn sig(&self, k: usize) -> u32 {
        (2 * self.a + k) as u32
    }
    pub fn n(&self, j: usize) -> u32 {
        assert!(j < self.kb);
        (2 * self.a + 2 + j) as u32
    }
    pub fn s(&self) -> u32 {
        (2 * self.a + 2 + self.kb) as u32
    }
    pub fn typ0(&self) -> u32 {
        (2 * self.a + 3 + self.kb) as u32
    }
    pub fn dirty(&self, j: usize) -> u32 {
        assert!(j < self.nd);
        (2 * self.a + 4 + self.kb + j) as u32
    }
    pub fn n_io(&self) -> u32 {
        (2 * self.a + 4 + self.kb + self.nd) as u32
    }
}

/// State of the windowed add's sweeps.
struct AddW {
    f: u32,
    s: u32,
    top: i64,
    unm: i64,
    a: Vec<u32>,
    b: Vec<u32>,
    carry: Vec<Option<u32>>,
    raw: BTreeMap<i64, u32>,
    ap: BTreeMap<i64, u32>,
    st: i64,
    a_arr: i64,
    o0: i64,
}

impl AddW {
    fn leafpos(&self, v: i64) -> i64 {
        self.a_arr - self.o0 - 1 - v
    }
    fn opnd(&self, i: i64) -> u32 {
        if i >= self.unm {
            self.ap[&i]
        } else {
            self.a[i as usize]
        }
    }
    fn tag(&self, i: i64) -> Tag {
        if i < self.unm {
            Tag::AddUnm
        } else {
            Tag::AddMask
        }
    }
    fn up_pos(&mut self, r: &mut Rec, i: i64) {
        let iu = i as usize;
        if i >= self.unm {
            if (i == self.unm || self.raw.contains_key(&(i - 1))) && self.carry[iu].is_none() {
                // kill: carry_i = f_i AND raw_{i-1}
                let cw = r.alloc();
                r.and_c(self.f, self.raw[&(i - 1)], cw, Tag::AddKill);
                self.carry[iu] = Some(cw);
            }
            let w = r.alloc();
            r.and_c(self.f, self.a[iu], w, Tag::AddOpmask);
            self.ap.insert(i, w);
        }
        let ai = self.opnd(i);
        let ci = self.carry[iu].expect("carry into position");
        r.cx(ci, ai);
        r.cx(ci, self.b[iu]);
        if i < self.top - 1 {
            let tt = r.alloc();
            r.and_c(ai, self.b[iu], tt, self.tag(i));
            r.cx(ci, tt);
            if i + 1 >= self.unm {
                self.raw.insert(i, tt); // carry into a window position: killed later
            } else {
                self.carry[iu + 1] = Some(tt);
            }
        }
    }
    fn up_to(&mut self, r: &mut Rec, iend: i64) {
        while self.st < iend {
            let i = self.st;
            self.up_pos(r, i);
            self.st += 1;
        }
    }
    /// Down sweep at position `i`; on entry `f = f_{i+1}` (`f_top` at the top position).
    fn dn_pos(&mut self, r: &mut Rec, i: i64, leaf: Option<Ctl>) {
        let iu = i as usize;
        // (a) un-kill carry_{i+1} = f_{i+1} AND raw_i
        if i < self.top - 1 && self.raw.contains_key(&i) {
            let cw = self.carry[iu + 1].take().expect("killed carry");
            r.and_u(self.f, self.raw[&i], cw, Tag::AddKill);
            r.release(cw);
        }
        // (b) toggle to f_i if the boundary is at i + 1
        if let Some(l) = leaf {
            r.cxc(l, self.f);
        }
        // (c) undo the carry step; b_i becomes the sum bit
        let ai = self.opnd(i);
        let ci = self.carry[iu].expect("carry into position");
        if i < self.top - 1 {
            let tt = match self.raw.remove(&i) {
                Some(t) => t,
                None => self.carry[iu + 1].take().expect("carry out"),
            };
            r.cx(ci, tt);
            r.and_u(ai, self.b[iu], tt, self.tag(i));
            r.release(tt);
            self.carry[iu + 1] = None;
        }
        r.cx(ci, ai);
        r.cx(ai, self.b[iu]);
        // (d) tap the region's top bit into s
        if i == self.top - 1 {
            r.ccx(self.f, self.b[iu], self.s, Tag::Tap); // region reaches top-1 iff f_{top-1}
        } else if let Some(l) = leaf {
            r.ccxc(l, self.b[iu], self.s, Tag::Tap);
        }
        // (e) normalise
        r.cx(self.s, self.b[iu]);
        // (f) unmask the operand
        if i >= self.unm {
            let w = self.ap.remove(&i).expect("masked operand");
            r.and_u(self.f, self.a[iu], w, Tag::AddOpmask);
            r.release(w);
        }
    }
    fn dn_to(&mut self, r: &mut Rec, iend: i64) {
        while self.st >= iend {
            let i = self.st;
            self.dn_pos(r, i, None);
            self.st -= 1;
        }
    }
}

/// Emit one forward tick into `r` (I/O slots per `io`).
pub fn build_tick(r: &mut Rec, io: &Io, w: &D2Win, mode: D2Mode) {
    build_tick_opt(r, io, w, mode, true, false);
}

/// [`build_tick`] with step 4 optional: `push = false` stops after the add and the sign update, leaving the tick's
/// s bit on the `s` wire (integration: the payload cell reads it, then the d2-stack push block stores it).
///
/// `erase_typ0` (tick 0 only): after step 2 the `typ_{-1}` wire (= o_0 of the FD seed) is cleared in place, 0
/// Toffoli: `typ0 ^= typ_0` leaves `c_0`, which the FD relation `Y = 3X + (2b - 1) p` fixes from the pre-add
/// registers as `c_0 = y1 ^ y2 ^ h0 ^ h1 ^ (y1 AND h0)` (two's-complement bits of the post-swap `Y` and of the halved
/// `X`; the normalized storage cancels the signs in the linear part), so the linear part is XORed out and the AND
/// is measured out (HMR + CZ repair). The wire then holds 0 (the caller releases it); the reverse tick recomputes
/// it (1 Toffoli). Port of the carry schedule's O0 erase (`fwd_tick_c`), secp256k1 (`kp = 0`).
pub fn build_tick_opt(r: &mut Rec, io: &Io, w: &D2Win, mode: D2Mode, push: bool, erase_typ0: bool) {
    let lean = mode != D2Mode::Port;
    let a_arr = w.a as i64;
    let t = w.t;
    let (xa, ya) = (t % 2, 1 - t % 2);
    let o = w.origins();
    let (ox, oy) = (o[xa] as i64, o[ya] as i64);
    let o0 = o[0] as i64;
    let (nlo, nhi) = (w.nlo as i64, w.nhi as i64);
    let (esw, ead) = (w.esw as i64, w.ead as i64);
    let p = |k: usize, i: i64| io.p(k, usize::try_from(i).expect("negative array index"));
    let sig = [io.sig(0), io.sig(1)];
    let np: Vec<u32> = (0..io.kb).map(|j| io.n(j)).collect();
    let np1: Vec<u32> = np[1..].to_vec();
    let s = io.s();
    let (mlo, mhi) = ((nlo + 1) / 2, (nhi + 1) / 2);
    let lmin = a_arr - o0 - mhi; // smallest possible L0

    // ---- 1. LSBs and masked swap of positions [1, Esw) under c AND [i < L0]
    r.cx(sig[xa], p(xa, ox));
    r.cx(sig[ya], p(ya, oy)); // denormalized LSBs; c = P[X][oX]
    let c = p(xa, ox);
    for i in 1..esw.min(lmin) {
        r.fred(c, p(xa, ox + i), p(ya, oy + i), Tag::SwapUnm);
    }
    if esw > lmin && matches!(mode, D2Mode::Lean { .. }) {
        let D2Mode::Lean { fold, .. } = mode else { unreachable!() };
        // the running flag lives on s (clean until the add's tap); the same map as below
        let g = s;
        r.cx(c, g); // g = c AND [i < L0]
        let vcut = a_arr - o0 - esw;
        let lo_v = mlo.max(vcut + 1);
        if lo_v <= mhi {
            r.comp = Some(0);
            let mut cb = |r: &mut Rec, v: i64, leaf: &Nd| {
                let i = a_arr - o0 - v;
                nd_tog(r, leaf, &[], g, Tag::SwapUi);
                if 1 <= i && i < esw {
                    r.fred(g, p(xa, ox + i), p(ya, oy + i), Tag::SwapMask);
                }
            };
            unary_f(r, Nd::W(c), &np1, mlo, mhi, (lo_v, mhi), true, Tag::SwapUi, fold[0] as usize, &mut cb);
            r.comp = None;
        }
        if vcut >= mlo {
            r.comp = Some(1);
            le_const_f(r, &np1, vcut, Nd::W(c), g, Tag::SwapCmp, fold[1] as usize);
            r.comp = None;
        }
    } else if esw > lmin {
        let g = r.alloc();
        r.cx(c, g); // g = c AND [i < L0]
        let vcut = a_arr - o0 - esw; // i >= Esw  <->  v <= vcut
        let lo_v = mlo.max(vcut + 1);
        if lo_v <= mhi {
            let mut cb = |r: &mut Rec, v: i64, leaf: Ctl| {
                let i = a_arr - o0 - v;
                r.cxc(leaf, g);
                if 1 <= i && i < esw {
                    r.fred(g, p(xa, ox + i), p(ya, oy + i), Tag::SwapMask);
                }
            };
            unary(r, Ctl::W(c), &np1, mlo, mhi, (lo_v, mhi), true, Tag::SwapUi, &mut cb);
        }
        if vcut >= mlo {
            // leftover flag = c AND [M <= vcut]
            if lean {
                le_const_lean(r, &np1, vcut, Ctl::W(c), g, Tag::SwapCmp);
            } else {
                le_const(r, &np1, vcut, c, g, Tag::SwapCmp);
            }
        }
        r.release(g);
    }
    r.fred(c, sig[xa], sig[ya], Tag::SigSwap);
    r.cx(c, p(ya, oy)); // Y's LSB (Y was even when c = 1)
    r.cx(sig[ya], p(ya, oy)); // renormalize Y's LSB

    // ---- 2. relabel; the freed wire P[X][oX] keeps c, then typ_t = c ^ typ_{t-1} (^1 for t > 0)
    let typ = p(xa, ox);
    let typ_prev = if t >= 1 { p(ya, oy - 1) } else { io.typ0() };
    r.cx(typ_prev, typ);
    if t > 0 {
        r.x(typ);
    }
    let ox1 = ox + 1;
    if erase_typ0 {
        assert_eq!(t, 0, "erase_typ0 is a tick-0 option");
        let o = io.typ0();
        r.cx(typ, o); // o = c_0
        for q in [p(ya, 1), p(ya, 2), p(xa, 1), p(xa, 2)] {
            r.cx(q, o); // o = y1 AND h0
        }
        let (y1, h0) = (p(ya, 1), p(xa, 1));
        r.cx(sig[ya], y1);
        r.cx(sig[xa], h0);
        r.and_u(y1, h0, o, Tag::AddUnm);
        r.cx(sig[ya], y1);
        r.cx(sig[xa], h0);
    }

    // ---- 3. masked add b_i = P[Y][oY+i] += ~P[X][oX1+i] (+ NOT sig_X), wrapped at min(top, Ladd)
    let top = ead;
    let lam = lmin - 1; // smallest possible Ladd = L0 - 1
    let unm = top.min(lam);
    assert!(unm >= 1, "D2 tick {t}: no unmasked add position (window {w:?}); clamp the window");
    let av: Vec<u32> = (0..top).map(|i| p(xa, ox1 + i)).collect();
    let bv: Vec<u32> = (0..top).map(|i| p(ya, oy + i)).collect();
    for &q in &av {
        r.x(q);
    }
    r.x(sig[xa]);
    let cin = sig[xa];
    if let D2Mode::LowRoom { gidney } = mode {
        add_inplace(r, &av, &bv, cin, s, top, unm, &np1, mlo, mhi, a_arr, o0, gidney, None);
    } else if let D2Mode::Lean { gidney, fold } = mode {
        add_inplace(r, &av, &bv, cin, s, top, unm, &np1, mlo, mhi, a_arr, o0, gidney, Some([fold[2], fold[3]]));
    } else if unm == top {
        // no window: plain wrapped Gidney add, public tap
        let tu = top as usize;
        let mut carry: Vec<Option<u32>> = vec![None; tu + 1];
        carry[0] = Some(cin);
        for i in 0..tu {
            let ci = carry[i].unwrap();
            r.cx(ci, av[i]);
            r.cx(ci, bv[i]);
            if i + 1 < tu {
                let tt = r.alloc();
                r.and_c(av[i], bv[i], tt, Tag::AddUnm);
                r.cx(ci, tt);
                carry[i + 1] = Some(tt);
            }
        }
        for i in (0..tu).rev() {
            let ci = carry[i].unwrap();
            if i + 1 < tu {
                let tt = carry[i + 1].unwrap();
                r.cx(ci, tt);
                r.and_u(av[i], bv[i], tt, Tag::AddUnm);
                r.release(tt);
            }
            r.cx(ci, av[i]);
            r.cx(av[i], bv[i]);
            if i + 1 == tu {
                r.cx(bv[i], s);
            }
            r.cx(s, bv[i]);
        }
    } else {
        let f = r.alloc();
        r.x(f); // f = [i < Ladd]
        let mut st = AddW {
            f,
            s,
            top,
            unm,
            a: av.clone(),
            b: bv.clone(),
            carry: vec![None; top as usize + 1],
            raw: BTreeMap::new(),
            ap: BTreeMap::new(),
            st: 0,
            a_arr,
            o0,
        };
        st.carry[0] = Some(cin);
        let vs: Vec<i64> = (mlo..=mhi).filter(|&v| unm <= st.leafpos(v) && st.leafpos(v) <= top).collect();
        // up sweep
        if !vs.is_empty() {
            let live = (*vs.iter().min().unwrap(), *vs.iter().max().unwrap());
            let mut cb_up = |r: &mut Rec, v: i64, leaf: Ctl| {
                let lp = st.leafpos(v);
                st.up_to(r, lp); // positions < Ladd with f = 1
                r.cxc(leaf, st.f); // f = 0 from Ladd on
            };
            unary(r, Ctl::One, &np1, mlo, mhi, live, true, Tag::AddUiUp, &mut cb_up);
        }
        st.up_to(r, top);
        // down sweep: at entry of position i, f = f_{i+1} (f_top for the top position)
        st.st = top - 1;
        if !vs.is_empty() {
            let live = (*vs.iter().min().unwrap(), *vs.iter().max().unwrap());
            let mut cb_dn = |r: &mut Rec, v: i64, leaf: Ctl| {
                let pb = st.leafpos(v); // boundary: f_p = 0, f_{p-1} = 1
                st.dn_to(r, pb);
                let i = pb - 1;
                assert_eq!(st.st, i);
                if i == top - 1 {
                    r.cxc(leaf, st.f);
                    st.dn_pos(r, i, None); // top position: toggle first, tap with f
                } else {
                    st.dn_pos(r, i, Some(leaf));
                }
                st.st = i - 1;
            };
            unary(r, Ctl::One, &np1, mlo, mhi, live, false, Tag::AddUiDn, &mut cb_dn);
        }
        st.dn_to(r, 0);
        assert!(st.raw.is_empty() && st.ap.is_empty() && st.carry[1..].iter().all(|c| c.is_none()));
        r.x(f);
        r.release(f);
    }
    r.x(sig[xa]);
    for &q in &av {
        r.x(q);
    }
    r.cx(s, sig[ya]);
    if !push {
        return;
    }

    // ---- 4. push s (B/C letters) and N += NOT typ (register holds N+1: leaf value v' -> N = v' - 1)
    r.x(typ);
    {
        let mut cbp = |r: &mut Rec, vp: i64, leaf: Ctl| {
            let v = vp - 1;
            r.fredc(leaf, s, p((v & 1) as usize, a_arr - (v >> 1) - 1), Tag::Push);
        };
        unary(r, Ctl::W(typ), &np, nlo + 1, nhi + 1, (nlo + 1, nhi + 1), true, Tag::PushUi, &mut cbp);
    }
    increment(r, &np, Some(typ), Tag::NInc);
    r.x(typ);
}

// ─── Plans, costs and emission ────────────────────────────────────────────────────────────

/// A planned tick: the forward gate list over I/O slots ([`Io`]) and scratch slots, plus its costs.
pub struct D2Plan {
    pub win: D2Win,
    pub mode: D2Mode,
    pub io: Io,
    pub gates: Vec<G>,
    /// Toffoli of the forward tick (CCX + Fredkin + compute-AND).
    pub t_fwd: usize,
    /// Toffoli of the reverse tick (CCX + Fredkin + the forward's measured uncomputes, now computes).
    pub t_rev: usize,
    /// Peak number of scratch wires live at once (identical forward and reverse).
    pub scratch: usize,
    /// Forward Toffoli by tag.
    pub by_tag: BTreeMap<Tag, usize>,
    /// Lean mode: multi-controlled ops referenced by the gate list.
    pub mops: Vec<MOp>,
    /// Lean mode: peak live scratch while each folded component ran (swap unary, swap compare, add compare, add unary).
    pub comp_peak: [usize; 4],
}

/// Plan the forward tick for window `win` (use [`D2Win::clamped`] on raw per-tick windows).
pub fn plan(win: &D2Win, mode: D2Mode) -> D2Plan {
    plan_opt(win, mode, true, false)
}

/// [`plan`] of the rail op only (steps 1-3: no push, no counter increment; `s` holds the tick's s bit on exit).
pub fn plan_rail(win: &D2Win, mode: D2Mode) -> D2Plan {
    plan_opt(win, mode, false, false)
}

/// The cheapest Lean rail op (steps 1-3; tick 0 with the `typ_{-1}` erase when `erase0`) whose scratch fits `budget`:
/// over the Gidney bottom count, each folded component is folded one level more until its peak fits. Cost =
/// forward + reverse Toffoli. None when no fold fits.
pub fn plan_rail_lean_fit(win: &D2Win, budget: usize, erase0: bool) -> Option<D2Plan> {
    let mut best: Option<D2Plan> = None;
    let gmax = budget.min(win.ead);
    for g in (0..=gmax).rev() {
        let mut f = [0u8; 4];
        loop {
            let pl = plan_opt(win, D2Mode::Lean { gidney: g, fold: f }, false, erase0);
            if pl.scratch <= budget {
                if best.as_ref().is_none_or(|b| pl.t_fwd + pl.t_rev < b.t_fwd + b.t_rev) {
                    best = Some(pl);
                }
                break;
            }
            let mut changed = false;
            for c in 0..4 {
                if pl.comp_peak[c] > budget && f[c] < 10 {
                    f[c] += 1;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }
    best
}

/// [`plan_rail`] with the tick-0 `typ_{-1}` erase (see [`build_tick_opt`]).
pub fn plan_rail_erase0(win: &D2Win, mode: D2Mode) -> D2Plan {
    plan_opt(win, mode, false, true)
}

/// [`plan_opt`] for the integration (explicit mode, rail op only when `push` is false).
pub fn plan_opt_pub(win: &D2Win, mode: D2Mode, push: bool, erase_typ0: bool) -> D2Plan {
    plan_opt(win, mode, push, erase_typ0)
}

fn plan_opt(win: &D2Win, mode: D2Mode, push: bool, erase_typ0: bool) -> D2Plan {
    let nd = if matches!(mode, D2Mode::Lean { .. }) { LEAN_DIRTY } else { 0 };
    let io = Io { a: win.a, kb: win.kbits(), nd };
    let mut r = Rec::new(io.n_io());
    build_tick_opt(&mut r, &io, win, mode, push, erase_typ0);
    assert_eq!(r.live, 0, "scratch left allocated");
    let mut by_tag = BTreeMap::new();
    let (mut t_fwd, mut t_rev) = (0, 0);
    for g in &r.gates {
        match *g {
            G::Ccx(_, _, _, tag) | G::Fred(_, _, _, tag) => {
                t_fwd += 1;
                t_rev += 1;
                *by_tag.entry(tag).or_insert(0) += 1;
            }
            G::AndC(_, _, _, tag) => {
                t_fwd += 1;
                *by_tag.entry(tag).or_insert(0) += 1;
            }
            G::AndU(..) => t_rev += 1,
            G::MAndC(i) => {
                let m = &r.mops[i as usize];
                let n = m.ctrls.len();
                assert!(n <= LEAN_DIRTY + 1, "multi-controlled op with {n} controls exceeds the dirty slots");
                t_fwd += mcx_t(n);
                t_rev += phase_t(n);
                *by_tag.entry(m.tag).or_insert(0) += mcx_t(n);
            }
            G::MAndU(i) => {
                let n = r.mops[i as usize].ctrls.len();
                t_fwd += phase_t(n);
                t_rev += mcx_t(n);
            }
            G::Mcx(i) => {
                let m = &r.mops[i as usize];
                let n = m.ctrls.len();
                assert!(n <= LEAN_DIRTY + 1, "multi-controlled op with {n} controls exceeds the dirty slots");
                t_fwd += mcx_t(n);
                t_rev += mcx_t(n);
                *by_tag.entry(m.tag).or_insert(0) += mcx_t(n);
            }
            _ => {}
        }
    }
    let comp_peak = r.comp_peak.map(|x| x as usize);
    D2Plan { win: *win, mode, io, gates: r.gates, t_fwd, t_rev, scratch: r.peak as usize, by_tag, mops: r.mops, comp_peak }
}

/// Direction of an emission.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dir {
    Forward,
    Reverse,
}

fn fredkin(b: &mut Builder, c: QubitId, x: QubitId, y: QubitId) {
    b.cx(y, x);
    b.ccx(c, x, y);
    b.cx(y, x);
}

/// `t ^= AND(ctrls)` on borrowed dirty wires (Barenco et al., Lemma 7.2; every dirty wire restored).
pub fn mcx_emit(b: &mut Builder, ctrls: &[QubitId], t: QubitId, dirty: &[QubitId]) {
    let cell = std::cell::RefCell::new(&mut *b);
    super::d2_stack::gl::mcx_seq(ctrls, t, dirty, &mut |x, y, z| cell.borrow_mut().ccx(x, y, z), &mut |x, y| cell.borrow_mut().cx(x, y));
}

/// The phase `(-1)^AND(ctrls)` (inside the caller's condition block): Z / CZ / CCZ, else a dirty wire toggled by the
/// first n - 2 controls around two CCZs with the last two.
pub fn phase_emit(b: &mut Builder, ctrls: &[QubitId], dirty: &[QubitId]) {
    let n = ctrls.len();
    match n {
        0 => unreachable!("phase of an empty AND"),
        1 => b.z_if(ctrls[0], crate::circuit::NO_BIT),
        2 => b.cz(ctrls[0], ctrls[1]),
        3 => b.ccz_if(ctrls[0], ctrls[1], ctrls[2], crate::circuit::NO_BIT),
        _ => {
            let (w, rest) = (dirty[0], &dirty[1..]);
            for _ in 0..2 {
                mcx_emit(b, &ctrls[..n - 2], w, rest);
                b.ccz_if(w, ctrls[n - 2], ctrls[n - 1], crate::circuit::NO_BIT);
            }
        }
    }
}

/// Measured uncompute of a clean temporary `t == AND(ctrls)`: HMR, then the phase `(-1)^AND(ctrls)` under the outcome.
pub fn mand_measure(b: &mut Builder, ctrls: &[QubitId], t: QubitId, dirty: &[QubitId]) {
    let m = b.alloc_bit();
    b.hmr(t, m);
    b.push_condition(m);
    phase_emit(b, ctrls, dirty);
    b.pop_condition();
    b.free_bit(m);
}

fn and_measure(b: &mut Builder, x: QubitId, y: QubitId, t: QubitId) {
    let m = b.alloc_bit();
    b.hmr(t, m);
    b.cz_if(x, y, m);
    b.free_bit(m);
}

/// Emit a planned tick on the caller's registers. Scratch wires are taken from (and returned clean to) the
/// builder's pool; the peak extra width is `plan.scratch`.
pub fn emit(b: &mut Builder, pl: &D2Plan, regs: &D2Regs, dir: Dir) {
    let io = &pl.io;
    assert_eq!(regs.p[0].len(), io.a);
    assert_eq!(regs.p[1].len(), io.a);
    assert!(regs.n.len() >= io.kb, "count register narrower than kbits {}", io.kb);
    let n_io = io.n_io() as usize;
    let mut map: Vec<Option<QubitId>> = vec![None; n_io];
    for k in 0..2 {
        for i in 0..io.a {
            map[io.p(k, i) as usize] = Some(regs.p[k][i]);
        }
        map[io.sig(k) as usize] = Some(regs.sig[k]);
    }
    for j in 0..io.kb {
        map[io.n(j) as usize] = Some(regs.n[j]);
    }
    map[io.s() as usize] = Some(regs.s);
    if pl.win.t == 0 {
        map[io.typ0() as usize] = Some(regs.typ0.expect("tick 0 needs the typ_{-1} wire"));
    }
    assert!(regs.dirty.len() >= io.nd, "Lean tick needs {} dirty wires, got {}", io.nd, regs.dirty.len());
    for j in 0..io.nd {
        map[io.dirty(j) as usize] = Some(regs.dirty[j]);
    }
    let dirty: Vec<QubitId> = regs.dirty[..io.nd].to_vec();
    let q = |map: &Vec<Option<QubitId>>, i: u32| map[i as usize].expect("unbound wire slot");
    let apply = |b: &mut Builder, map: &mut Vec<Option<QubitId>>, g: G| match g {
        G::X(a) => b.x(q(map, a)),
        G::Cx(a, t) => b.cx(q(map, a), q(map, t)),
        G::Swap(x, y) => b.swap(q(map, x), q(map, y)),
        G::Ccx(x, y, t, _) => b.ccx(q(map, x), q(map, y), q(map, t)),
        G::Fred(c, x, y, _) => fredkin(b, q(map, c), q(map, x), q(map, y)),
        G::AndC(x, y, t, _) => b.ccx(q(map, x), q(map, y), q(map, t)),
        G::AndU(x, y, t, _) => and_measure(b, q(map, x), q(map, y), q(map, t)),
        G::Alloc(i) => {
            let i = i as usize;
            if map.len() <= i {
                map.resize(i + 1, None);
            }
            assert!(map[i].is_none());
            map[i] = Some(b.alloc_qubit());
        }
        G::Release(i) => {
            let w = map[i as usize].take().expect("release of an unbound slot");
            b.release_clean(w);
        }
        G::MAndC(i) | G::Mcx(i) => {
            let m = &pl.mops[i as usize];
            let ctrls: Vec<QubitId> = m.ctrls.iter().map(|&c| q(map, c)).collect();
            mcx_emit(b, &ctrls, q(map, m.t), &dirty);
        }
        G::MAndU(i) => {
            let m = &pl.mops[i as usize];
            let ctrls: Vec<QubitId> = m.ctrls.iter().map(|&c| q(map, c)).collect();
            mand_measure(b, &ctrls, q(map, m.t), &dirty);
        }
    };
    match dir {
        Dir::Forward => {
            for &g in &pl.gates {
                apply(b, &mut map, g);
            }
        }
        Dir::Reverse => {
            for &g in pl.gates.iter().rev() {
                let inv = match g {
                    G::AndC(x, y, t, tag) => G::AndU(x, y, t, tag),
                    G::AndU(x, y, t, tag) => G::AndC(x, y, t, tag),
                    G::MAndC(i) => G::MAndU(i),
                    G::MAndU(i) => G::MAndC(i),
                    G::Alloc(i) => G::Release(i),
                    G::Release(i) => G::Alloc(i),
                    other => other,
                };
                apply(b, &mut map, inv);
            }
        }
    }
}

/// Forward tick `t` on `regs` under window `win` (clamped). Returns `(toffoli, scratch peak)`.
pub fn tick_forward(b: &mut Builder, regs: &D2Regs, win: &D2Win, mode: D2Mode) -> (usize, usize) {
    let pl = plan(&win.clamped(), mode);
    emit(b, &pl, regs, Dir::Forward);
    (pl.t_fwd, pl.scratch)
}

/// Reverse tick `t` (exact inverse of [`tick_forward`] with the same window).
pub fn tick_reverse(b: &mut Builder, regs: &D2Regs, win: &D2Win, mode: D2Mode) -> (usize, usize) {
    let pl = plan(&win.clamped(), mode);
    emit(b, &pl, regs, Dir::Reverse);
    (pl.t_rev, pl.scratch)
}
