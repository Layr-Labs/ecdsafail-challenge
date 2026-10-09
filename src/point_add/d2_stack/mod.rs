//! D2 stacks and park skip (track D2, component d2-stack).
//!
//! Layout (both legs; persistent outside the payload: 2A + 2 + 8 + PB + 1 wires; 592 at A = 288, PB = 5):
//!   arrays `p[0]`, `p[1]` (A wires each).  Array k at tick t: `[0, o_k)` typ wires | `[o_k, B_k)` rail,
//!   normalized (n = v or NOT v, sign on `sig[k]`), gap = 0 | `[B_k, A)` stack, `B_k = A - S_k`,
//!   `S_0 = ceil(N/2)`, `S_1 = floor(N/2)`, `o(t) = ((t+1)/2, t/2)`.  Stack entry j (the j-th B/C letter's s
//!   bit) lives at `p[j & 1][A - 1 - (j >> 1)]`; the typ bit of tick t lives at `p[t % 2][t / 2]` (the wire
//!   freed by that tick's relabel).
//!   `nreg` (8 wires) holds N + 1, so M = ceil(N/2) is `nreg[1..]` (the tick's mask register).
//!   `preg` (PB wires, default 5) is the park register: all ones = not detected, else the index i of the
//!   checkpoint d_i that detected the park; the walk then counts as parked at p_eff = d_i - 1.
//!   `s` (1 wire) carries the tick's s bit from the tap to the push; clean outside that span.
//!
//! Per tick t, after the tick component's rail op (which writes typ_t = c XOR W(typ wire t-1) XOR 1 blindly):
//!   `fixup`     typ_t ^= [p_eff < t-1] AND NOT W(w_{t-1})   (w_{t-1} then holds a popped stack bit, not 1).
//!   -- payload cell slot: the cell reads (typ wire t, s); post-park it reads (1, 0).  Room = cap - 1,104. --
//!   `detect`    checkpoint d_i only: if the X rail after the tick is zero (the walk parked before d_i) and
//!               preg is all ones, preg := i.  Exact masked zero test; self-inverse block.
//!   `push`      B/C letters (typ_t = 0): s -> stack entry N (unary iteration over N + a Fredkin); N += 1.
//!   `tick_pop`  if p_eff < t: typ wire t (= 1, every post-park letter is A) <- stack top (entry N-1); N -= 1.
//! The walk back runs the exact inverses in reverse order (`detect` is its own inverse).
//! A walk that parks at p is detected at the first checkpoint d > p; the typ wires (p, d-1] keep their 1s.
//! With checkpoints every 3 ticks over 350..375 and every tick over 376..394 (28, so preg has 5 bits) the
//! classical model gives 0.892 overflow events per corpus at A = 288 against 0.888 for detection at every
//! tick (10M walks, tools/ckmodel.rs, out/sched_A288_d2.txt).
//!
//! Measured per traversal at A = 288 (R = 395, windows = model ranges + 3, pebbles 6):
//!   push 56,188 T; park 13,238 T (fixup 396, detect 5,834, tick_pop 7,008); the walk back costs the same.
//!   Scratch peaks: detect 14, tick_pop 9, push 8, fixup 6 (nothing is held across the cell slot).
//! Integration API: [`D2Layout`], [`sched::D2Sched`] (`from_model_table`, `default_checkpoints`),
//! [`tick_blocks`] and the four emitters [`after_tick_fwd`] / [`after_cell_fwd`] (forward) and
//! [`before_cell_rev`] / [`after_cell_rev`] (walk back); readers for batch cells: [`peek_gl`], [`typ_read_gl`].
pub mod gl;
pub mod lean;
pub mod pebble;
pub mod prim;
pub mod sched;
pub mod selftest;

use super::builder::Builder;
use crate::circuit::QubitId;
use gl::{emit, Gl, W};
use prim::*;

pub const N_BITS: usize = 8;

#[derive(Clone)]
pub struct D2Layout {
    pub a: usize,
    pub p: [Vec<QubitId>; 2],
    pub sig: [QubitId; 2],
    pub nreg: Vec<QubitId>,
    pub preg: Vec<QubitId>,
    pub s: QubitId,
    /// Idle wires the budgeted blocks may borrow dirty (restored exactly); empty = legacy constructions only.
    pub dirty: Vec<QubitId>,
}

fn qw(v: &[QubitId]) -> Vec<W> {
    v.iter().map(|&q| W::Q(q)).collect()
}

impl D2Layout {
    /// Allocate all persistent wires (all |0>).  Call [`D2Layout::init`] to set N + 1 = 1 and preg = all ones.
    pub fn alloc(c: &mut Builder, a: usize, pbits: usize) -> Self {
        let p = [c.alloc_qubits(a), c.alloc_qubits(a)];
        let sig = [c.alloc_qubit(), c.alloc_qubit()];
        let nreg = c.alloc_qubits(N_BITS);
        let preg = c.alloc_qubits(pbits);
        let s = c.alloc_qubit();
        Self { a, p, sig, nreg, preg, s, dirty: Vec::new() }
    }
    /// From existing wires (integration).
    pub fn from_wires(a: usize, p: [Vec<QubitId>; 2], sig: [QubitId; 2], nreg: Vec<QubitId>, preg: Vec<QubitId>, s: QubitId) -> Self {
        assert!(p[0].len() == a && p[1].len() == a && nreg.len() == N_BITS && !preg.is_empty());
        Self { a, p, sig, nreg, preg, s, dirty: Vec::new() }
    }
    /// N = 0 (register value 1) and preg = all ones.  Clifford only; its own inverse ([`D2Layout::fini`]).
    pub fn init(&self, c: &mut Builder) {
        c.x(self.nreg[0]);
        for &q in &self.preg {
            c.x(q);
        }
    }
    pub fn fini(&self, c: &mut Builder) {
        self.init(c);
    }
    pub fn undetected(&self) -> u64 {
        (1u64 << self.preg.len()) - 1
    }
    pub fn persistent_wires(&self) -> usize {
        2 * self.a + 2 + N_BITS + self.preg.len() + 1
    }
    pub fn typ_wire(&self, t: usize) -> QubitId {
        self.p[t % 2][t / 2]
    }
    pub fn stack_wire(&self, j: usize) -> QubitId {
        self.p[j & 1][self.a - 1 - (j >> 1)]
    }
    fn n_w(&self) -> Vec<W> {
        qw(&self.nreg)
    }
    fn p_w(&self) -> Vec<W> {
        qw(&self.preg)
    }
}

/// Classical promise window for an N-indexed unary iteration: the N values of the inputs whose control fires.
pub type NWin = (u64, u64);

// ─── blocks ───────────────────────────────────────────────────────────────────────────────────────────────

/// Push: if `typ_t` = 0, move `s` into stack entry N and N += 1.  `win` = N range of the pushing inputs.
/// T = (#N values) + (#N values - 1, unary splits) + 7 (increment), approximately 2 per N value + 6.
pub fn push_gl(l: &D2Layout, t: usize, win: NWin) -> Gl {
    let mut g = Gl::new();
    let typ = W::Q(l.typ_wire(t));
    let s = W::Q(l.s);
    let n = l.n_w();
    assert!(win.0 <= win.1 && win.1 + 1 < (1u64 << n.len()) && (win.1 as usize) < 2 * l.a);
    g.x(typ);
    let (a, p) = (l.a, l.p.clone());
    unary(&mut g, Some(typ), &n, win.0 + 1, win.1 + 1, (win.0 + 1, win.1 + 1), true, &mut |g, vp, leaf| {
        let v = (vp - 1) as usize;
        fred_o(g, leaf, s, W::Q(p[v & 1][a - 1 - (v >> 1)]));
    });
    increment(&mut g, &n, Some(typ));
    g.x(typ);
    g
}

/// Budget of clean temporaries for the budgeted blocks of one tick ([`tick_blocks_budget`]).
#[derive(Clone, Copy, Debug)]
pub struct Budget {
    pub push: usize,
    pub pop: usize,
    pub fixup: usize,
    /// The park register holds all ones at the push (before the first checkpoint's detector): lend it to the push.
    pub lend_push: bool,
}

fn dirty_w(l: &D2Layout) -> Vec<W> {
    l.dirty.iter().map(|&q| W::Q(q)).collect()
}

/// [`push_gl`] with `fold` virtual unary levels and `m` materialized increment prefixes; returns the block and the
/// peaks of its two parts.
fn push_gl_p(l: &D2Layout, t: usize, win: NWin, fold: usize, m: usize) -> (Gl, [u32; 2]) {
    let mut g = Gl::new();
    let typ = W::Q(l.typ_wire(t));
    let s = W::Q(l.s);
    let n = l.n_w();
    let dirty = dirty_w(l);
    assert!(win.0 <= win.1 && win.1 + 1 < (1u64 << n.len()) && (win.1 as usize) < 2 * l.a);
    g.x(typ);
    let (a, p) = (l.a, l.p.clone());
    lean::unary_f(&mut g, lean::Nd::W(typ), &n, win.0 + 1, win.1 + 1, (win.0 + 1, win.1 + 1), true, fold, &dirty, &mut |g, vp, leaf| {
        let v = (vp - 1) as usize;
        lean::nd_fred(g, leaf, s, W::Q(p[v & 1][a - 1 - (v >> 1)]), &dirty);
    });
    let p0 = g.peak;
    g.peak = g.live();
    lean::increment_b(&mut g, &n, Some(typ), m, &dirty);
    let p1 = g.peak;
    g.peak = p0.max(p1);
    g.x(typ);
    (g, [p0, p1])
}

/// The cheapest push whose temporaries fit `budget` (unary folds up, increment prefixes down). None: no fit.
pub fn push_gl_b(l: &D2Layout, t: usize, win: NWin, budget: usize) -> Option<Gl> {
    let k = l.nreg.len();
    let b = budget as u32;
    let fold = (0..=k).find(|&f| push_gl_p(l, t, win, f, k - 1).1[0] <= b)?;
    let m = (1..k).rev().find(|&m| push_gl_p(l, t, win, fold, m).1[1] <= b)?;
    Some(push_gl_p(l, t, win, fold, m).0)
}

/// [`tick_pop_gl`] with folds: `f` (flag compare levels), `fu` (pop unary levels), `m` (decrement prefixes).
fn tick_pop_gl_p(l: &D2Layout, t: usize, k: u64, win: NWin, f: usize, fu: usize, m: usize) -> (Gl, [u32; 3]) {
    let mut g = Gl::new();
    let pw = l.p_w();
    let dirty = dirty_w(l);
    let fl = g.alloc();
    lean::le_const_f(&mut g, &pw, k, lean::Nd::One, fl, f, &dirty);
    let p0 = g.peak;
    g.peak = g.live();
    let w = W::Q(l.typ_wire(t));
    g.cx(fl, w);
    assert!(win.0 >= 1 && win.0 <= win.1);
    let n = l.n_w();
    let (a, p) = (l.a, l.p.clone());
    lean::unary_f(&mut g, lean::Nd::W(fl), &n, win.0 + 1, win.1 + 1, (win.0 + 1, win.1 + 1), true, fu, &dirty, &mut |g, vp, leaf| {
        let top = (vp - 2) as usize;
        lean::nd_fred(g, leaf, W::Q(p[top & 1][a - 1 - (top >> 1)]), w, &dirty);
    });
    let p1 = g.peak;
    g.peak = g.live();
    lean::decrement_b(&mut g, &n, Some(fl), m, &dirty);
    let p2 = g.peak;
    lean::le_const_f(&mut g, &pw, k, lean::Nd::One, fl, f, &dirty);
    g.release(fl);
    g.peak = p0.max(p1).max(p2);
    (g, [p0, p1, p2])
}

pub fn tick_pop_gl_b(l: &D2Layout, t: usize, k: u64, win: NWin, budget: usize) -> Option<Gl> {
    let kb = l.nreg.len();
    let pb = l.preg.len();
    let b = budget as u32;
    let f = (0..=pb).find(|&f| tick_pop_gl_p(l, t, k, win, f, 0, kb - 1).1[0] <= b)?;
    let fu = (0..=kb).find(|&fu| tick_pop_gl_p(l, t, k, win, f, fu, kb - 1).1[1] <= b)?;
    let m = (1..kb).rev().find(|&m| tick_pop_gl_p(l, t, k, win, f, fu, m).1[2] <= b)?;
    Some(tick_pop_gl_p(l, t, k, win, f, fu, m).0)
}

/// [`fixup_gl`] as one controlled compare into the typ wire: `typ_t ^= NOT W(w_{t-1}) AND [preg <= k]`, the top `f`
/// levels of its chain folded (no flag wire).
fn fixup_gl_p(l: &D2Layout, t: usize, k: u64, f: usize) -> Gl {
    let mut g = Gl::new();
    let pw = l.p_w();
    let dirty = dirty_w(l);
    let prev = W::Q(l.typ_wire(t - 1));
    let cur = W::Q(l.typ_wire(t));
    lean::le_const_f(&mut g, &pw, k, lean::Nd::V(vec![(prev, true)]), cur, f, &dirty);
    g
}

pub fn fixup_gl_b(l: &D2Layout, t: usize, k: u64, budget: usize) -> Option<Gl> {
    let pb = l.preg.len();
    (0..=pb + 1).map(|f| fixup_gl_p(l, t, k, f)).find(|g| g.peak as usize <= budget)
}

/// Pop the stack top (entry N - 1) into `target` (which must be 0 when `ctrl` = 1) and N -= 1, under `ctrl`.
/// `win` = N range (N >= 1) of the inputs whose control fires.
pub fn pop_into(g: &mut Gl, l: &D2Layout, target: W, ctrl: W, win: NWin) {
    assert!(win.0 >= 1 && win.0 <= win.1);
    let n = l.n_w();
    let (a, p) = (l.a, l.p.clone());
    unary(g, Some(ctrl), &n, win.0 + 1, win.1 + 1, (win.0 + 1, win.1 + 1), true, &mut |g, vp, leaf| {
        let top = (vp - 2) as usize; // N = vp - 1, top entry N - 1
        fred_o(g, leaf, W::Q(p[top & 1][a - 1 - (top >> 1)]), target);
    });
    decrement(g, &n, Some(ctrl));
}

/// `typ_t ^= [preg <= k] AND NOT W(w_{t-1})` with k = index of the last checkpoint <= t-1: the tick read a
/// popped stack bit from w_{t-1} where the walk's letter t-1 was an A (typ 1).
pub fn fixup_gl(l: &D2Layout, t: usize, k: u64) -> Gl {
    let mut g = Gl::new();
    let pw = l.p_w();
    let f = |g: &mut Gl, o: W| le_const_into(g, &pw, k, None, o);
    let fl = flag(&mut g, &f);
    let prev = W::Q(l.typ_wire(t - 1));
    let cur = W::Q(l.typ_wire(t));
    g.ccx(fl, prev, cur);
    g.cx(fl, cur);
    flag_erase(&mut g, fl, &f);
    g
}

/// Per-tick pop: `[preg <= k]` (k = index of the last checkpoint <= t, i.e. p_eff < t) -> typ wire t (= 1)
/// cleared and loaded with the stack top, N -= 1.
pub fn tick_pop_gl(l: &D2Layout, t: usize, k: u64, win: NWin) -> Gl {
    let mut g = Gl::new();
    let pw = l.p_w();
    let f = |g: &mut Gl, o: W| le_const_into(g, &pw, k, None, o);
    let fl = flag(&mut g, &f);
    let w = W::Q(l.typ_wire(t));
    g.cx(fl, w);
    pop_into(&mut g, l, w, fl, win);
    flag_erase(&mut g, fl, &f);
    g
}

/// Read access for batch cells: `out ^= ctrl AND s(entry N - 1 - depth)` (the s bit `depth` entries below the
/// stack top).  `win` = N range of the inputs whose control fires (N > depth).  T = about 2 per N value.
pub fn peek_gl(l: &D2Layout, depth: usize, ctrl: Option<W>, out: W, win: NWin) -> Gl {
    let mut g = Gl::new();
    assert!(win.0 as usize > depth && win.0 <= win.1);
    let n = l.n_w();
    let (a, p) = (l.a, l.p.clone());
    unary(&mut g, ctrl, &n, win.0 + 1, win.1 + 1, (win.0 + 1, win.1 + 1), true, &mut |g, vp, leaf| {
        let j = (vp - 2) as usize - depth; // N = vp - 1
        let w = W::Q(p[j & 1][a - 1 - (j >> 1)]);
        match leaf {
            Some(lf) => g.ccx(lf, w, out),
            None => g.cx(w, out),
        }
    });
    g
}

/// Read access for batch cells: `out ^= typ_{t'}` for an earlier tick t' (its typ wire, or the implicit 1 of
/// an A letter whose wire took a popped stack bit: `[preg <= k]`, k = index of the last checkpoint <= t').
pub fn typ_read_gl(l: &D2Layout, tp: usize, k: Option<u64>, out: W) -> Gl {
    let mut g = Gl::new();
    let w = W::Q(l.typ_wire(tp));
    g.cx(w, out);
    if let Some(k) = k {
        let pw = l.p_w();
        let f = |g: &mut Gl, o: W| le_const_into(g, &pw, k, None, o);
        let fl = flag(&mut g, &f);
        g.ccx(fl, w, out);
        g.cx(fl, out);
        flag_erase(&mut g, fl, &f);
    }
    g
}

/// Detection parameters for one checkpoint.
#[derive(Clone, Copy, Debug)]
pub struct DetParams {
    /// Index i of this checkpoint (the value written into preg).
    pub index: u64,
    /// Zero-test top: positions [0, top) of the X rail (relative to its post-tick origin) cover every rail.
    pub top: usize,
    /// Selection leaves cover M in [m_lo, m_hi] (M outside gives z = 0: a missed detection, never a false one).
    pub m_lo: u64,
    pub m_hi: u64,
    /// Ladder pebble budget.
    pub pebbles: usize,
    /// Membership test `[preg in {ALL1, index}]` computed only at the act, controlled by z, as one AND of z and
    /// four preg literals (the index's zero bits folded onto one of them by CNOTs) on borrowed dirty wires: no flag
    /// across the zero test and no chain at the act.
    pub late_memb: bool,
    /// Selection levels below the unary iteration: the lowest `dirty_lv` bits of M are not split by AND
    /// temporaries; each leaf is one AND of (high leaf, `dirty_lv` M bits, ladder node) into z on borrowed dirty
    /// wires (4 (dirty_lv) Toffolis, its erase a phase of the same controls). Fewer temporaries, more T.
    pub dirty_lv: usize,
}

/// Ladder length of the detector at checkpoint t (0: no live selection leaf).
pub fn detect_ladder_len(l: &D2Layout, t: usize, dp: &DetParams) -> usize {
    let a = l.a as i64;
    let ox = t / 2 + 1;
    let o0 = ((t + 1) / 2) as i64;
    let top = dp.top.min(l.a - ox);
    let lo_m = dp.m_lo as i64;
    let mmax = (a - o0 - 1).min(dp.m_hi as i64);
    if lo_m <= mmax {
        (a - o0 - 1 - lo_m).min(top as i64) as usize
    } else {
        0
    }
}

/// The park detector at checkpoint t: z = [X rail after tick t == 0] (exact masked zero test over
/// positions [0, min(top, Ladd(M))), Ladd(M) = A - o_0(t) - 1 - M, M = ceil(N/2), plus NOT sig; the
/// selection leaves are exact for every register value);
/// preg ^= ALL1 ^ index under z AND [preg in {ALL1, index}].  Self-inverse; contains measurements (always
/// emitted forward).  Reads the X rail, its sign, nreg and preg only.
pub fn detect_gl(l: &D2Layout, t: usize, dp: DetParams) -> Gl {
    let mut g = Gl::new();
    let a = l.a as i64;
    let x = t % 2;
    let ox = t / 2 + 1; // X rail origin after the relabel
    let o0 = ((t + 1) / 2) as i64;
    let all1 = l.undetected();
    assert!(dp.index < all1);
    let pw = l.p_w();
    let mreg: Vec<W> = l.n_w()[1..].to_vec();
    let km = mreg.len();
    let top = dp.top.min(l.a - ox);
    let idx = dp.index;
    let ell_of = |m: i64| -> usize { (a - o0 - 1 - m).min(top as i64) as usize };
    let lo_m = dp.m_lo as i64;
    let mmax = (a - o0 - 1).min(dp.m_hi as i64); // M <= mmax -> ell >= 0
    let fm = |g: &mut Gl, o: W| memb2_into(g, &pw, all1, idx, None, o);
    let memb = if dp.late_memb { None } else { Some(flag(&mut g, &fm)) };
    // borrowed dirty wires: the other array (the detector reads only array x, its sign, nreg and preg)
    let dirty: Vec<W> = l.p[1 - x].iter().take(8).map(|&q| W::Q(q)).collect();
    let start = g.g.len();
    let z = g.alloc();
    let sig = W::Q(l.sig[x]);
    g.x(sig); // node 0 = NOT sig
    let bit = |i: usize| W::Q(l.p[x][ox + i]);
    let last_ell = if lo_m <= mmax { ell_of(lo_m) } else { 0 };
    let steps = if last_ell > 0 { pebble::plan_visits(last_ell, dp.pebbles.max(1)).0 } else { Vec::new() };
    let mut nodes: std::collections::HashMap<usize, W> = std::collections::HashMap::new();
    nodes.insert(0, sig);
    let mut pc = 0usize;
    let mut at = 0usize; // last visited node
    let mut advance = |g: &mut Gl, nodes: &mut std::collections::HashMap<usize, W>, ell: usize| {
        if ell == at {
            return;
        }
        assert!(ell > at);
        loop {
            let st = steps[pc];
            pc += 1;
            match st {
                pebble::Step::Place(j) => {
                    let prev = nodes[&(j - 1)];
                    let b = bit(j - 1);
                    g.x(b);
                    let n = g.and_c(prev, b);
                    g.x(b);
                    nodes.insert(j, n);
                }
                pebble::Step::Remove(j) => {
                    let prev = nodes[&(j - 1)];
                    let b = bit(j - 1);
                    let n = nodes.remove(&j).unwrap();
                    g.x(b);
                    g.and_u(prev, b, n);
                    g.x(b);
                }
                pebble::Step::Visit(j) => {
                    if j == ell {
                        at = ell;
                        return;
                    }
                }
            }
        }
    };
    if lo_m <= mmax && dp.dirty_lv == 0 {
        unary(&mut g, None, &mreg, 0, (1u64 << km) - 1, (lo_m as u64, mmax as u64), true, &mut |g, v, leaf| {
            let ell = ell_of(v as i64);
            advance(g, &mut nodes, ell);
            let leaf = leaf.expect("selection leaf is never constant");
            g.leaf(leaf, nodes[&ell], z);
        });
    } else if lo_m <= mmax {
        // unary over the high bits of M; the low `dl` bits become literals of a multi-controlled leaf
        let dl = dp.dirty_lv.min(km - 1);
        let (lo_u, hi_u) = (lo_m as u64, mmax as u64);
        let high = &mreg[dl..];
        let kh = high.len();
        unary(&mut g, None, high, 0, (1u64 << kh) - 1, (lo_u >> dl, hi_u >> dl), true, &mut |g, h, leaf| {
            for lv in (0..(1u64 << dl)).rev() {
                let v = (h << dl) | lv;
                if v < lo_u || v > hi_u {
                    continue;
                }
                let ell = ell_of(v as i64);
                advance(g, &mut nodes, ell);
                let mut ctrls: Vec<W> = Vec::with_capacity(dl + 2);
                if let Some(lf) = leaf {
                    ctrls.push(lf);
                }
                for i in 0..dl {
                    if (lv >> i) & 1 == 0 {
                        g.x(mreg[i]);
                    }
                    ctrls.push(mreg[i]);
                }
                ctrls.push(nodes[&ell]);
                g.mleaf(&ctrls, z, &dirty);
                for i in 0..dl {
                    if (lv >> i) & 1 == 0 {
                        g.x(mreg[i]);
                    }
                }
            }
        });
    }
    let end = g.g.len();
    // act: preg ^= ALL1 ^ index under z AND memb (memb is invariant under that swap)
    match memb {
        Some(memb) => {
            let g0 = g.and_c(z, memb);
            xor_const(&mut g, &pw, all1 ^ idx, Some(g0));
            g.and_u(z, memb, g0);
        }
        None => {
            // [preg in {ALL1, idx}] = AND over idx's one bits of preg_i, AND all of idx's zero bits equal: fold
            // the zero bits onto the first one (CNOTs), then they must read 0.
            let pb = pw.len();
            let zeros: Vec<usize> = (0..pb).filter(|&i| (idx >> i) & 1 == 0).collect();
            assert!(!zeros.is_empty());
            let d0 = zeros[0];
            let fold = |g: &mut Gl| {
                for &j in &zeros[1..] {
                    g.cx(pw[d0], pw[j]);
                }
            };
            let lits: Vec<(W, bool)> = (0..pb)
                .filter(|&i| i != d0)
                .map(|i| (pw[i], (idx >> i) & 1 == 1))
                .collect();
            let g0 = g.alloc();
            let gate = |g: &mut Gl| {
                fold(g);
                for &(w, want) in &lits {
                    if !want {
                        g.x(w);
                    }
                }
                let mut ctrls: Vec<W> = vec![z];
                ctrls.extend(lits.iter().map(|&(w, _)| w));
                g.mcx(&ctrls, g0, &dirty);
                for &(w, want) in &lits {
                    if !want {
                        g.x(w);
                    }
                }
                fold(g);
            };
            gate(&mut g);
            xor_const(&mut g, &pw, all1 ^ idx, Some(g0));
            gate(&mut g);
            g.release(g0);
        }
    }
    // phase-fixed erase of z: measure it, replay the compute range backwards with CZ at the leaves
    g.append_erase_sweep(start, end, z);
    if let Some(memb) = memb {
        flag_erase(&mut g, memb, &fm);
    }
    g
}

// ─── per-tick driver ──────────────────────────────────────────────────────────────────────────────────────

/// Gate lists of tick t's stack/park work (from a schedule).
pub struct TickBlocks {
    pub t: usize,
    pub fixup: Option<Gl>,
    pub detect: Option<Gl>,
    pub push: Option<Gl>,
    pub tick_pop: Option<Gl>,
    /// `push -> detect -> tick_pop` (else `detect -> push -> tick_pop`); see [`sched::D2Sched::detect_after_push`].
    pub detect_after_push: bool,
    /// The layout's `s` wire: clean after the push, lent to the detector as room when it runs after the push.
    pub s: QubitId,
    /// Park-register wires lent to the push as clean room (all ones there, X'ed to zero around it); empty: none.
    pub lend_push: Vec<QubitId>,
}

pub fn tick_blocks(l: &D2Layout, s: &sched::D2Sched, t: usize) -> TickBlocks {
    tick_blocks_room(l, s, t, false)
}

/// [`tick_blocks`] for a traversal with the payload half freed (`high`: the detector may use the
/// [`sched::D2Sched::det_high`] construction; every construction implements the same map).
pub fn tick_blocks_room(l: &D2Layout, s: &sched::D2Sched, t: usize, high: bool) -> TickBlocks {
    tick_blocks_budget(l, s, t, high, None)
}

/// [`tick_blocks_room`] with the push / tick pop / fixup fitted to `budget` (None: the legacy constructions).
pub fn tick_blocks_budget(l: &D2Layout, s: &sched::D2Sched, t: usize, high: bool, budget: Option<Budget>) -> TickBlocks {
    let k_t = s.last_ck_index(t);
    let k_prev = if t >= 1 { s.last_ck_index(t - 1) } else { None };
    let det = if high && !s.det_high.is_empty() { s.det_high[t] } else { s.det[t] };
    let over = |what: &str, b: usize| -> ! { panic!("D2 tick {t}: no {what} construction fits {b} temporaries") };
    let (fixup, push, tick_pop, lend_push) = match budget {
        None => (
            k_prev.map(|k| fixup_gl(l, t, k)),
            s.push_win[t].map(|w| push_gl(l, t, w)),
            k_t.map(|k| tick_pop_gl(l, t, k, s.pop_win[t].expect("pop window"))),
            Vec::new(),
        ),
        Some(bd) => {
            let pb = if bd.lend_push { bd.push + l.preg.len() } else { bd.push };
            (
                k_prev.map(|k| fixup_gl_b(l, t, k, bd.fixup).unwrap_or_else(|| over("fixup", bd.fixup))),
                s.push_win[t].map(|w| push_gl_b(l, t, w, pb).unwrap_or_else(|| over("push", pb))),
                k_t.map(|k| tick_pop_gl_b(l, t, k, s.pop_win[t].expect("pop window"), bd.pop).unwrap_or_else(|| over("tick pop", bd.pop))),
                if bd.lend_push { l.preg.clone() } else { Vec::new() },
            )
        }
    };
    let b = TickBlocks {
        t,
        fixup,
        detect: det.map(|dp| detect_gl(l, t, dp)),
        push,
        tick_pop,
        detect_after_push: s.detect_after_push,
        s: l.s,
        lend_push,
    };
    if std::env::var_os("D2_BLOCK_PEAKS").is_some() {
        let cs = b.costs();
        eprintln!("D2_BLOCK_PEAKS t={t} fixup {:?} detect {:?} push {:?} tick_pop {:?} det {:?}", cs[0], cs[1], cs[2], cs[3], s.det[t]);
    }
    b
}

/// Forward: after the tick component's rail op of tick t, before the payload cell.
pub fn after_tick_fwd(c: &mut Builder, b: &TickBlocks) {
    if let Some(g) = &b.fixup {
        emit(c, g, false);
    }
}
/// Forward: after the payload cell of tick t.
pub fn after_cell_fwd(c: &mut Builder, b: &TickBlocks) {
    if b.detect_after_push {
        if let Some(g) = &b.push {
            emit_lent(c, g, &b.lend_push, false);
        }
        if let Some(g) = &b.detect {
            emit_lent_s(c, g, b.s, false);
        }
        if let Some(g) = &b.tick_pop {
            emit_lent_s(c, g, b.s, false);
        }
        return;
    }
    for g in [&b.detect, &b.push, &b.tick_pop].into_iter().flatten() {
        emit(c, g, false);
    }
}

/// The push with the park register (all ones there) X'ed to zero and released to the builder as clean room.
fn emit_lent(c: &mut Builder, g: &Gl, preg: &[QubitId], rev: bool) {
    for &q in preg {
        c.x(q);
        c.release_clean(q);
    }
    emit(c, g, rev);
    for &q in preg {
        c.reacquire(q);
        c.x(q);
    }
}
/// A block that runs after the push (detector, tick pop) with the clean `s` wire released to the builder as room.
fn emit_lent_s(c: &mut Builder, g: &Gl, s: QubitId, rev: bool) {
    c.release_clean(s);
    emit(c, g, rev);
    c.reacquire(s);
}
/// Walk back: before the inverse payload cell of tick t.
pub fn before_cell_rev(c: &mut Builder, b: &TickBlocks) {
    if b.detect_after_push {
        if let Some(g) = &b.tick_pop {
            emit_lent_s(c, g, b.s, true);
        }
        if let Some(g) = &b.detect {
            emit_lent_s(c, g, b.s, false);
        }
        if let Some(g) = &b.push {
            emit_lent(c, g, &b.lend_push, true);
        }
    } else {
        if let Some(g) = &b.tick_pop {
            emit(c, g, true);
        }
        if let Some(g) = &b.push {
            emit(c, g, true);
        }
        if let Some(g) = &b.detect {
            emit(c, g, false);
        }
    }
}
/// Walk back: after the inverse payload cell of tick t, before the inverse rail op.
pub fn after_cell_rev(c: &mut Builder, b: &TickBlocks) {
    if let Some(g) = &b.fixup {
        emit(c, g, true);
    }
}

impl TickBlocks {
    /// (forward T, walk-back T, peak temporaries) per block, in order fixup/detect/push/tick_pop.
    pub fn costs(&self) -> [(usize, usize, u32); 4] {
        let f = |g: &Option<Gl>| {
            g.as_ref().map_or((0, 0, 0), |g| (g.t_fwd(), if g.has_meas() { g.t_fwd() } else { g.t_rev() }, g.peak))
        };
        [f(&self.fixup), f(&self.detect), f(&self.push), f(&self.tick_pop)]
    }
}
