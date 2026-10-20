//! SKY-COF rails-frame walk (research): the Skywalk rails with cofactors kept in the rails' own frame,
//! `a * R1 + b * R2 = p` (two's complement, LSB first). Same rails, letters, history and odometer as
//! [`super::walk`]; only the cofactor update, the letter decoder and the park handling differ.
//!
//! # Cofactor update (tick t)
//! The rail tick swaps the rails on `c_t = typ_t ^ typ_{t-1}` and then does `R2 -/+= H` (`H = R1 / 2`). In the
//! frame this is: swap `(a, b)` on `c_t` (Fredkins), then the UNCONDITIONAL signed add `a <- 2a + sig * b`
//! (`sig = +1` when the add agrees, i.e. `nag = 0`): no controlled add.
//!
//! # Decoder (letter `t-1`, disposed in tick t after the swap, before the add)
//! On the swapped pair `J' = (a', b')` the Kaliski cofactors of post(t-1) are `r = J'[typ_t]`, `q = J'[!typ_t]`,
//! `s = r +- |q|` (`+` iff `sign(q) == sign(R_q)`, `R_q` the swapped rail paired with q). Hence
//! `C = a'1 ^ b'1 ^ sign(R_q) ^ 1` (exact), certain-A iff `!C & sigma & |q| > r`, else (not C) ambiguous:
//! a top-window compare `ge = [r_top >= |q|_top]` (one's complement abs, conservative). The push envelope is
//! the Kaliski decoder's (measured equal tick by tick).
//!
//! # Park
//! `z = [b' == p]` (top `park_j` magnitude bits of b' all one, sign 0) is 1 from tick T0+1 on, exactly the
//! ticks whose add is `x <- 2x + p`. Entry (`E = z & [odo == 0]`, the first such tick): `a' = q` has an
//! arbitrary sign; when `q >= 0` the add sign is flipped (`2q - p`, F_e XORed into the sign wire: 0 Toffoli),
//! and F_e is recovered after the add as bit 1 of the result (`2q + p = 1`, `2q - p = 3` mod 4).
//! Every clamp tick then folds `x -= p` when `z & x >= 0` (window add of c, top-bit decrement); the fold flag
//! is the result's LSB complement. Post-park invariant `x in [-p, 2c)`; the parked output is `s = x + p`.
use super::adder;
use super::decoder::{self as dec, Hreg};
use super::tick::{self, resize_signed};
use super::walk::{self, Envelope, WalkParams};
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;
use crate::point_add::heo::Rails;
use crate::point_add::skycof_mm as mm;
use crate::point_add::N;
use alloy_primitives::U256;

/// Frame clamp: signed width of the cofactors at the Kaliski clamp (256 magnitude bits + sign).
pub const FCL: usize = N + 1;

/// Frame field width post(t): Kaliski design width + 1 sign bit, clamped.
pub fn fw(env: &Envelope, t: usize) -> usize {
    (env.cof[t] + 1).min(FCL)
}

pub struct FCof {
    pub a: Vec<Q>,
    pub b: Vec<Q>,
}

pub struct FParked {
    pub s: Vec<Q>,
    /// all history wires (every block), for reports and probes
    pub h: Hreg,
    hl: HLive,
    pub odo: Vec<Q>,
    prev: Vec<(usize, usize)>,
}

// ─── history blocks ─────────────────────────────────────────────────────────────────────────────
//
// The letters of ticks [start_b, start_{b+1}) push into block b's own stack (a controlled shift over that block's
// wires only); a block is frozen once the walk leaves it, so a push shifts only the current block. Each block's
// width envelope is designed for the same overflow rate as the single-stack envelope (`hist_blocks.tsv`).

/// History event before letter t.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum HEv {
    None,
    /// a new block (stack) starts; the previous one is frozen
    Split,
    /// the two most recent blocks merge into one stack (width `env[t]`) that takes the following letters
    Merge,
}

pub struct HPlan {
    pub ev: Vec<HEv>,
    /// width of the current stack at letter t
    pub env: Vec<usize>,
    /// the last two blocks merge into one stack of this width when the forward walk parks (`#merge W`)
    pub merge_end: Option<usize>,
    /// a block starting at letter t that is later the top operand of a merge: its counter's start value
    /// (the block's final width); it counts `W - pushes`
    pub ctr_at: Vec<Option<usize>>,
}

fn parse_hplan(txt: &str, r: usize) -> HPlan {
    let (mut env, mut ev, mut merge_end, mut mat) = (Vec::new(), Vec::new(), None, Vec::new());
    let mut last_id = 0usize;
    for l in txt.lines() {
        if let Some(w) = l.strip_prefix("#mergeat ") {
            mat.push(w.trim().parse::<usize>().unwrap());
            continue;
        }
        if let Some(w) = l.strip_prefix("#merge ") {
            merge_end = Some(w.trim().parse().unwrap());
            continue;
        }
        if l.starts_with('#') || l.trim().is_empty() {
            continue;
        }
        let f: Vec<usize> = l.split('\t').map(|x| x.trim().parse().unwrap()).collect();
        assert_eq!(f[0], env.len(), "hist_blocks: rows out of order");
        ev.push(if f[0] > 0 && f[1] != last_id { HEv::Split } else { HEv::None });
        last_id = f[1];
        env.push(f[2]);
    }
    for t in mat {
        assert_eq!(ev[t], HEv::Split, "hist_blocks: #mergeat {t} must start a new block id");
        ev[t] = HEv::Merge;
    }
    while env.len() < r {
        env.push(*env.last().unwrap());
        ev.push(HEv::None);
    }
    env.truncate(r);
    ev.truncate(r);
    // counters: simulate the block stack; a Merge's top operand (and the end merge's) must be a Split block
    let mut ctr_at = vec![None; r];
    let mut stack: Vec<Option<usize>> = vec![None]; // start letter of each live block (None = not a Split block)
    let mut merged_block = vec![false];
    for t in 0..r {
        match ev[t] {
            HEv::Split => {
                stack.push(Some(t));
                merged_block.push(false);
            }
            HEv::Merge => {
                let top = stack.pop().unwrap().expect("hist_blocks: merge top operand must be a split block");
                assert!(!merged_block.pop().unwrap());
                ctr_at[top] = Some(env[t - 1]);
                stack.pop();
                merged_block.pop();
                stack.push(None);
                merged_block.push(true);
            }
            HEv::None => {}
        }
    }
    if merge_end.is_some() {
        let top = stack.pop().unwrap().expect("hist_blocks: end merge top operand must be a split block");
        ctr_at[top] = Some(env[r - 2]);
    }
    HPlan { ev, env, merge_end, ctr_at }
}

/// Counter width: holds `0..=w`.
fn ctr_bits(w: usize) -> usize {
    (usize::BITS - w.leading_zeros()) as usize
}

/// Controlled rotation toward higher indices by `r` (new[(i + r) % n] = old[i]): `n - gcd(n, r)` Fredkins.
fn crot_up(c: &mut Builder, ctl: Q, v: &[Q], r: usize) {
    let n = v.len();
    let r = r % n;
    if r == 0 {
        return;
    }
    let g = gcd(n, r);
    for p in 0..g {
        let l = n / g;
        for j in 1..l {
            fredkin(c, ctl, v[p], v[(p + j * r) % n]);
        }
    }
}

fn crot_down(c: &mut Builder, ctl: Q, v: &[Q], r: usize) {
    let n = v.len();
    crot_up(c, ctl, v, (n - r % n) % n);
}

fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// Merge `top` (data [0, c_top), counter `s = W_top - c_top`) onto `low` (data [0, c_low)): the result holds
/// top's data then low's at [0, c_top + c_low); its wires above `w` (zero unless the total exceeds w, an envelope
/// miss) are freed.
fn merge_fwd(c: &mut Builder, top: Hreg, low: Hreg, ctr: &[Q], w: usize) -> Hreg {
    let b1 = top.wires;
    for (k, &q) in ctr.iter().enumerate() {
        crot_up(c, q, &b1, 1 << k);
    }
    let l: Vec<Q> = b1.iter().chain(&low.wires).copied().collect();
    for (k, &q) in ctr.iter().enumerate() {
        crot_down(c, q, &l, 1 << k);
    }
    assert!(w <= l.len(), "history merge: width {w} > {}", l.len());
    for &q in &l[w..] {
        c.free(q);
    }
    Hreg { wires: l[..w].to_vec() }
}

/// [`merge_fwd`] with a count-up counter `c = c_top` (lazy counters): rotate `top` down by c (= up by W - c, W = its
/// width), relabel `l` down by W, rotate `l` up by c.
fn merge_fwd_up(c: &mut Builder, top: Hreg, low: Hreg, ctr: &[Q], w: usize) -> Hreg {
    let b1 = top.wires;
    let wt = b1.len();
    for (k, &q) in ctr.iter().enumerate() {
        crot_down(c, q, &b1, 1 << k);
    }
    let mut l: Vec<Q> = b1.iter().chain(&low.wires).copied().collect();
    let n = l.len();
    l.rotate_left(wt % n);
    for (k, &q) in ctr.iter().enumerate() {
        crot_up(c, q, &l, 1 << k);
    }
    assert!(w <= l.len(), "history merge: width {w} > {}", l.len());
    for &q in &l[w..] {
        c.free(q);
    }
    Hreg { wires: l[..w].to_vec() }
}

/// Exact inverse of [`merge_fwd_up`].
fn merge_rev_up(c: &mut Builder, m: Hreg, ctr: &[Q], wt: usize, wl: usize) -> (Hreg, Hreg) {
    let mut l = m.wires;
    while l.len() < wt + wl {
        let q = c.alloc_qubit();
        l.push(q);
    }
    for (k, &q) in ctr.iter().enumerate().rev() {
        crot_down(c, q, &l, 1 << k);
    }
    let n = l.len();
    l.rotate_right(wt % n);
    let b1 = l[..wt].to_vec();
    for (k, &q) in ctr.iter().enumerate().rev() {
        crot_up(c, q, &b1, 1 << k);
    }
    (Hreg { wires: l[wt..].to_vec() }, Hreg { wires: b1 })
}

/// History counters count pushes up from 0 on wires grown as the count can grow (`SKYCOF_LAZYCTR=0` restores the
/// full-width count-down counter set at the split).
pub(crate) fn lazy_ctr() -> bool {
    super::pointadd::knob("SKYCOF_LAZYCTR").map(|v| v != "0").unwrap_or(super::pointadd::LAZY_CTR)
}

/// Exact inverse of [`merge_fwd`]: returns (low, top) at widths (`wl`, `wt`).
fn merge_rev(c: &mut Builder, m: Hreg, ctr: &[Q], wt: usize, wl: usize) -> (Hreg, Hreg) {
    let mut l = m.wires;
    while l.len() < wt + wl {
        let q = c.alloc_qubit();
        l.push(q);
    }
    for (k, &q) in ctr.iter().enumerate().rev() {
        crot_up(c, q, &l, 1 << k);
    }
    let b1 = l[..wt].to_vec();
    for (k, &q) in ctr.iter().enumerate().rev() {
        crot_down(c, q, &b1, 1 << k);
    }
    (Hreg { wires: l[wt..].to_vec() }, Hreg { wires: b1 })
}

pub fn hplan(env: &Envelope, r: usize) -> &'static HPlan {
    static H: std::sync::OnceLock<HPlan> = std::sync::OnceLock::new();
    H.get_or_init(|| {
        let on = super::pointadd::knob("SKYCOF_HBLK").map(|v| v != "0").unwrap_or(super::pointadd::HBLK);
        let hp = if !on {
            HPlan { ev: vec![HEv::None; r], env: env.h.clone(), merge_end: None, ctr_at: vec![None; r] }
        } else if let Some(path) = super::pointadd::knob("SKYCOF_HBLK_FILE") {
            parse_hplan(&std::fs::read_to_string(&path).expect("SKYCOF_HBLK_FILE"), r)
        } else {
            parse_hplan(include_str!("hist_blocks.tsv"), r)
        };
        let evs: Vec<(usize, HEv, usize)> = (0..r).filter(|&t| hp.ev[t] != HEv::None).map(|t| (t, hp.ev[t], hp.env[t - 1])).collect();
        eprintln!("SKYCOF_HPLAN events(t, ev, width before)={evs:?} end_width={} merge_end={:?}", hp.env[r - 1], hp.merge_end);
        hp
    })
}

/// Live history: the block stack (current block last), each block's counter, and the merges done (counter, top
/// width, low width) for the walk back.
pub struct HLive {
    regs: Vec<Hreg>,
    ctrs: Vec<Option<Vec<Q>>>,
    parked: Vec<(Vec<Q>, usize, usize)>,
    /// lazy counters: (block start letter, final width) of each block with a counter
    cinfo: Vec<Option<(usize, usize)>>,
    pinfo: Vec<Option<(usize, usize)>>,
}

impl HLive {
    fn new() -> Self {
        HLive { regs: vec![Hreg::new()], ctrs: vec![None], parked: Vec::new(), cinfo: vec![None], pinfo: Vec::new() }
    }
    /// Lazy counter width after letter t1 of a block (start s, final width w) is pushed.
    fn ctr_w(t1: usize, s: usize, w: usize) -> usize {
        ctr_bits((t1 + 1 - s).min(w))
    }
    /// Forward, before letter t1's push: grow the current block's lazy counter.
    fn ctr_grow(&mut self, c: &mut Builder, t1: usize) {
        if let (Some(Some(ctr)), Some(Some((s, w)))) = (self.ctrs.last_mut(), self.cinfo.last()) {
            let want = Self::ctr_w(t1, *s, *w);
            while ctr.len() < want {
                let q = c.alloc_qubit();
                ctr.push(q);
            }
        }
    }
    /// Backward, after letter t1's pop: shrink the current block's lazy counter (its top wires are 0).
    fn ctr_shrink(&mut self, c: &mut Builder, t1: usize) {
        if let (Some(Some(ctr)), Some(Some((s, w)))) = (self.ctrs.last_mut(), self.cinfo.last()) {
            let want = if t1 > *s { Self::ctr_w(t1 - 1, *s, *w) } else { 0 };
            while ctr.len() > want {
                let q = ctr.pop().unwrap();
                c.free(q);
            }
        }
    }
    fn all_wires(&self) -> Vec<Q> {
        let mut v: Vec<Q> = self.regs.iter().flat_map(|x| x.wires.iter().copied()).collect();
        v.extend(self.ctrs.iter().flatten().flatten());
        v.extend(self.parked.iter().flat_map(|x| x.0.iter().copied()));
        v
    }
    fn set_ctr(c: &mut Builder, w: usize) -> Vec<Q> {
        let ctr = c.alloc_qubits(ctr_bits(w));
        for (k, &q) in ctr.iter().enumerate() {
            if (w >> k) & 1 == 1 {
                c.x(q);
            }
        }
        ctr
    }
    fn merge(&mut self, c: &mut Builder, w: usize) {
        let top = self.regs.pop().unwrap();
        let low = self.regs.pop().unwrap();
        let ctr = self.ctrs.pop().unwrap().expect("history merge: top block has no counter");
        assert!(self.ctrs.pop().unwrap().is_none());
        let ci = self.cinfo.pop().unwrap();
        self.cinfo.pop();
        let (wt, wl) = (top.len(), low.len());
        let m = if lazy_ctr() { merge_fwd_up(c, top, low, &ctr, w) } else { merge_fwd(c, top, low, &ctr, w) };
        self.regs.push(m);
        self.ctrs.push(None);
        self.cinfo.push(None);
        self.parked.push((ctr, wt, wl));
        self.pinfo.push(ci);
    }
    fn unmerge(&mut self, c: &mut Builder, w: usize) {
        let m = self.regs.pop().unwrap();
        assert_eq!(m.len(), w, "history unmerge: merged width");
        assert!(self.ctrs.pop().unwrap().is_none());
        let (ctr, wt, wl) = self.parked.pop().unwrap();
        let ci = self.pinfo.pop().unwrap();
        let (low, top) = if lazy_ctr() { merge_rev_up(c, m, &ctr, wt, wl) } else { merge_rev(c, m, &ctr, wt, wl) };
        self.regs.push(low);
        self.ctrs.push(None);
        self.cinfo.pop();
        self.cinfo.push(None);
        self.regs.push(top);
        self.ctrs.push(Some(ctr));
        self.cinfo.push(ci);
    }
    /// Forward, top of the tick that disposes letter t1: that letter's history event.
    fn fwd_event(&mut self, c: &mut Builder, hp: &HPlan, t1: usize) {
        match hp.ev[t1] {
            HEv::None => {}
            HEv::Split => {
                self.regs.push(Hreg::new());
                if lazy_ctr() {
                    self.ctrs.push(hp.ctr_at[t1].map(|_| Vec::new()));
                    self.cinfo.push(hp.ctr_at[t1].map(|w| (t1, w)));
                } else {
                    self.ctrs.push(hp.ctr_at[t1].map(|w| Self::set_ctr(c, w)));
                    self.cinfo.push(None);
                }
            }
            HEv::Merge => self.merge(c, hp.env[t1]),
        }
    }
    /// Backward, end of the tick that restored letter t1: undo that letter's event.
    fn rev_event(&mut self, c: &mut Builder, hp: &HPlan, t1: usize) {
        match hp.ev[t1] {
            HEv::None => {}
            HEv::Split => {
                let mut top = self.regs.pop().unwrap();
                top.shrink_to(c, 0);
                let ci = self.cinfo.pop().unwrap();
                if let (Some(Some(ctr)), Some(_)) = (self.ctrs.last(), ci) {
                    assert!(ctr.is_empty(), "lazy history counter not back to 0 wires");
                }
                if ci.is_some() {
                    self.ctrs.pop();
                } else if let Some(ctr) = self.ctrs.pop().unwrap() {
                    let w = hp.ctr_at[t1].unwrap();
                    for (k, &q) in ctr.iter().enumerate() {
                        if (w >> k) & 1 == 1 {
                            c.x(q);
                        }
                    }
                    c.free_vec(&ctr);
                }
            }
            HEv::Merge => self.unmerge(c, hp.env[t1]),
        }
    }
    fn cur_fwd(&mut self, c: &mut Builder, w: usize, t1: usize) -> (&Hreg, Option<&[Q]>) {
        self.ctr_grow(c, t1);
        let h = self.regs.last_mut().unwrap();
        h.grow_to(c, w);
        (&*h, self.ctrs.last().unwrap().as_deref())
    }
    fn cur_rev(&mut self, c: &mut Builder, w: usize) -> (&Hreg, Option<&[Q]>) {
        let h = self.regs.last_mut().unwrap();
        h.shrink_to(c, w);
        (&*h, self.ctrs.last().unwrap().as_deref())
    }
}

/// Walk back: the history is narrowed as soon as the forward's width allows (before the add, right after the pop)
/// instead of at the next pop (`SKYCOF_HSYNC=0` restores).
fn hsync() -> bool {
    super::pointadd::knob("SKYCOF_HSYNC").map(|v| v != "0").unwrap_or(super::pointadd::HSYNC)
}

fn room(c: &Builder, cap: usize) -> usize {
    cap.saturating_sub(c.active_qubits() as usize)
}

fn secp_c() -> u128 {
    mm::Field::secp().c
}

fn fredkin(c: &mut Builder, ctrl: Q, a: Q, b: Q) {
    c.cx(b, a);
    c.ccx(ctrl, a, b);
    c.cx(b, a);
}

/// HMR `t` (holding `x & y`) and repair the phase.
fn meas_cz(c: &mut Builder, t: Q, x: Q, y: Q) {
    let m = c.alloc_bit();
    c.hmr(t, m);
    c.cz_if(x, y, m);
    c.free_bit(m);
    c.release_clean(t);
}

// ─── park test (AND of literal wires; the caller applies negations around compute and uncompute) ─────

/// Park test spare: b'0 (= 1 on every tick) lent as the first node of a tree with at least two nodes (never its
/// root); X'd to 0 before use and back to 1 after its measured erase (`SKYCOF_PARKB0=0` restores).
static PARK_SPARE: std::sync::Mutex<Option<Q>> = std::sync::Mutex::new(None);

fn park_b0() -> bool {
    park_shape() && super::pointadd::knob("SKYCOF_PARKB0").map(|v| v != "0").unwrap_or(super::pointadd::PARK_B0)
}

fn tree(c: &mut Builder, lits: &[Q]) -> (Q, Vec<(Q, Q, Q)>) {
    assert!(lits.len() >= 2);
    let mut nodes = Vec::new();
    let mut level: Vec<Q> = lits.to_vec();
    let mut spare = if lits.len() >= 3 { *PARK_SPARE.lock().unwrap() } else { None };
    while level.len() > 1 {
        let mut next = Vec::with_capacity(level.len() / 2 + 1);
        let mut i = 0;
        while i + 1 < level.len() {
            let n = if let Some(sp) = spare.take() {
                c.x(sp);
                sp
            } else {
                c.alloc_qubit()
            };
            c.ccx(level[i], level[i + 1], n);
            nodes.push((n, level[i], level[i + 1]));
            next.push(n);
            i += 2;
        }
        if i < level.len() {
            next.push(level[i]);
        }
        level = next;
    }
    (level[0], nodes)
}

fn erase_nodes(c: &mut Builder, nodes: &[(Q, Q, Q)]) {
    let spare = *PARK_SPARE.lock().unwrap();
    for &(n, a, b) in nodes.iter().rev() {
        if Some(n) == spare {
            let m = c.alloc_bit();
            c.hmr(n, m);
            c.cz_if(a, b, m);
            c.free_bit(m);
            c.x(n);
        } else {
            meas_cz(c, n, a, b);
        }
    }
}

fn and_frozen(c: &mut Builder, lits: &[Q]) -> Q {
    if lits.len() == 1 {
        let o = c.alloc_qubit();
        c.cx(lits[0], o);
        return o;
    }
    let (root, nodes) = tree(c, lits);
    erase_nodes(c, &nodes[..nodes.len() - 1]);
    root
}

fn mcz(c: &mut Builder, lits: &[Q]) {
    match lits.len() {
        0 => {}
        1 => c.z_if(lits[0], crate::circuit::NO_BIT),
        2 => c.cz(lits[0], lits[1]),
        n => {
            let (root, nodes) = tree(c, &lits[..n - 1]);
            c.cz(root, lits[n - 1]);
            erase_nodes(c, &nodes);
        }
    }
}

fn erase_frozen(c: &mut Builder, w: Q, lits: &[Q]) {
    if lits.len() == 1 {
        c.cx(lits[0], w);
        c.release_clean(w);
        return;
    }
    let m = c.alloc_bit();
    c.hmr(w, m);
    let early = park_shape();
    if early {
        // the HMR left w at |0>: release it before the repair's tree
        c.release_clean(w);
    }
    c.push_condition(m);
    mcz(c, lits);
    c.pop_condition();
    c.free_bit(m);
    if !early {
        c.release_clean(w);
    }
}

/// Park test: part sizes chosen for the lowest window peak (same part count, same Toffoli) and early release of
/// each measured part root (`SKYCOF_PARKSHAPE=0` restores equal parts of `PARK_PART`).
fn park_shape() -> bool {
    super::pointadd::knob("SKYCOF_PARKSHAPE").map(|v| v != "0").unwrap_or(super::pointadd::PARK_SHAPE)
}

/// Window peak (above the entry live count) of the park test's compute and uncompute for part sizes `s`.
fn park_peak(s: &[usize]) -> usize {
    let m = s.len();
    let sp = usize::from(park_b0());
    // tree over k literals: k - 1 nodes, one of them the spare when k >= 3
    let tn = |k: usize| if k >= 3 { k - 1 - sp } else { k.saturating_sub(1) };
    let nodes = |k: usize| if k >= 2 { tn(k) } else { 1 };
    let mczn = |k: usize| if k >= 3 { tn(k - 1) } else { 0 };
    let mut pk = 0;
    for (i, &k) in s.iter().enumerate() {
        pk = pk.max(i + nodes(k)); // compute part i (compute and uncompute)
        pk = pk.max(1 + i + mczn(k)); // erase part i after z exists
    }
    if m >= 2 {
        pk = pk.max(m + tn(m));
    }
    if m >= 3 {
        pk = pk.max(m + tn(m - 1));
    }
    pk
}

/// Part sizes for `n` literals in `m` parts minimising [`park_peak`] (non-increasing sizes).
fn park_sizes(n: usize, m: usize) -> Vec<usize> {
    fn rec(n: usize, m: usize, maxk: usize, cur: &mut Vec<usize>, best: &mut Option<(usize, Vec<usize>)>) {
        if m == 0 {
            if n == 0 {
                let p = park_peak(cur);
                if best.as_ref().map_or(true, |b| p < b.0) {
                    *best = Some((p, cur.clone()));
                }
            }
            return;
        }
        for k in (1..=maxk.min(n)).rev() {
            if k * m < n {
                break;
            }
            cur.push(k);
            rec(n - k, m - 1, k, cur, best);
            cur.pop();
        }
    }
    let mut best = None;
    rec(n, m, n, &mut Vec::new(), &mut best);
    best.unwrap().1
}

const PARK_PART: usize = 5;

/// `z = [b == p]` on a frame register at `FCL` wires: AND of the top `j` magnitude bits and `!sign`.
struct FPark {
    z: Q,
    parts: Vec<Vec<Q>>,
    sign: Q,
    b0: Q,
}

impl FPark {
    fn compute(c: &mut Builder, b: &[Q], j: usize) -> Self {
        assert_eq!(b.len(), FCL);
        let sign = b[N];
        let mut lits: Vec<Q> = b[N - j..N].to_vec();
        lits.push(sign);
        let parts: Vec<Vec<Q>> = if park_shape() {
            let m = lits.len().div_ceil(PARK_PART);
            let sz = park_sizes(lits.len(), m);
            let mut v = Vec::new();
            let mut at = 0;
            for k in sz {
                v.push(lits[at..at + k].to_vec());
                at += k;
            }
            v
        } else {
            lits.chunks(PARK_PART).map(|p| p.to_vec()).collect()
        };
        c.x(sign);
        if park_b0() {
            *PARK_SPARE.lock().unwrap() = Some(b[0]);
        }
        let a: Vec<Q> = parts.iter().map(|p| and_frozen(c, p)).collect();
        let z = and_frozen(c, &a);
        for (ai, p) in a.iter().zip(&parts).rev() {
            erase_frozen(c, *ai, p);
        }
        *PARK_SPARE.lock().unwrap() = None;
        c.x(sign);
        FPark { z, parts, sign, b0: b[0] }
    }
    fn uncompute(self, c: &mut Builder) {
        let m = c.alloc_bit();
        c.hmr(self.z, m);
        c.release_clean(self.z);
        c.x(self.sign);
        if park_b0() {
            *PARK_SPARE.lock().unwrap() = Some(self.b0);
        }
        c.push_condition(m);
        let a: Vec<Q> = self.parts.iter().map(|p| and_frozen(c, p)).collect();
        mcz(c, &a);
        for (ai, p) in a.iter().zip(&self.parts).rev() {
            erase_frozen(c, *ai, p);
        }
        c.pop_condition();
        *PARK_SPARE.lock().unwrap() = None;
        c.x(self.sign);
        c.free_bit(m);
    }
}

/// Live clamp-tick state between the dispose and the fold: park flag, `[odo != 0]`, entry flag.
struct ClampSt {
    zt: FPark,
    nz: Q,
    /// None (EDROP): recomputed from z, nz around each use in the add
    e: Option<Q>,
}

/// Clamp adds: no entry-flag wire across the add; `E = z & !nz` is recomputed around each of its two uses (+1 Toffoli
/// per clamp tick, one wire less at the add). Late-letter path only; off by default (`SKYCOF_EDROP=1` research).
fn edrop() -> bool {
    late2() && super::pointadd::knob("SKYCOF_EDROP").map(|v| v != "0").unwrap_or(super::pointadd::EDROP)
}

fn eflag(c: &mut Builder, z: Q, nz: Q) -> Q {
    let e = c.alloc_qubit();
    c.x(nz);
    c.ccx(z, nz, e);
    c.x(nz);
    e
}

fn eflag_erase(c: &mut Builder, e: Q, z: Q, nz: Q) {
    let m = c.alloc_bit();
    c.hmr(e, m);
    c.x(nz);
    c.cz_if(z, nz, m);
    c.x(nz);
    c.free_bit(m);
    c.release_clean(e);
}

/// `isc ^= E & ctl` with `E` the entry-flag wire or (EDROP) recomputed from `(z, nz)`.
fn e_ccx(c: &mut Builder, ent: (Option<Q>, Q, Q), ctl: Q, isc: Q) {
    match ent.0 {
        Some(e) => c.ccx(e, ctl, isc),
        None => {
            let e = eflag(c, ent.1, ent.2);
            c.ccx(e, ctl, isc);
            eflag_erase(c, e, ent.1, ent.2);
        }
    }
}

/// First clamp tick (the first tick whose previous field width is the clamp): the odometer is 0 before it.
fn first_clamp(env: &Envelope, r: usize) -> usize {
    (1..r).find(|&t| fw(env, t - 1) == FCL).expect("frame walk: no clamp tick")
}

/// Lazy odometer: allocated at the first clamp tick, released (it is 0 again) when the walk back leaves it.
/// Late odometer (with the lazy one): allocated by the first clamp letter after its park test, freed by the walk
/// back right after that letter's decrement (`SKYCOF_LATEODO=0` restores the tick-boundary allocation).
fn late_odo() -> bool {
    lazy_odo() && super::pointadd::knob("SKYCOF_LATEODO").map(|v| v != "0").unwrap_or(super::pointadd::LATE_ODO)
}

/// Clamp letters: decoder first, odometer after (`SKYCOF_ODOAFTER=0` restores the odometer-first order).
fn odo_after() -> bool {
    super::pointadd::knob("SKYCOF_ODOAFTER").map(|v| v != "0").unwrap_or(super::pointadd::ODO_AFTER)
}

fn lazy_odo() -> bool {
    super::pointadd::knob("SKYCOF_LAZYODO").map(|v| v != "0").unwrap_or(super::pointadd::LAZY_ODO)
}

fn grow_odo() -> bool {
    late_odo() && super::pointadd::knob("SKYCOF_GROWODO").map(|v| v != "0").unwrap_or(super::pointadd::GROW_ODO)
}

/// Odometer width during clamp tick `t` (after its increment); 0 before the first clamp tick.
fn odo_w(env: &Envelope, p: &WalkParams, t: usize) -> usize {
    let t0 = first_clamp(env, p.r);
    if t < t0 {
        return 0;
    }
    if !grow_odo() {
        return p.odo_bits;
    }
    let k = t - t0 + 1;
    ((usize::BITS - k.leading_zeros()) as usize).min(p.odo_bits)
}

/// Forward: grow the odometer (fresh zero top wires) to its width at tick `t`.
fn odo_grow(c: &mut Builder, env: &Envelope, p: &WalkParams, odo: &mut Vec<Q>, t: usize) {
    let w = odo_w(env, p, t);
    while odo.len() < w {
        let q = c.alloc_qubit();
        odo.push(q);
    }
}

/// Backward: shrink the odometer to its width at tick `t` (the freed top wires are 0: at most `t - t0 + 1` increments).
fn odo_shrink(c: &mut Builder, env: &Envelope, p: &WalkParams, odo: &mut Vec<Q>, t: Option<usize>) {
    let w = t.map_or(0, |t| odo_w(env, p, t));
    while odo.len() > w {
        let q = odo.pop().unwrap();
        c.free(q);
    }
}

/// Room for an odometer / counter op on `l` wires (`extra` = 1 for the nonzero test): the exact room the chunk
/// plan needs instead of a flat floor of 4 (`SKYCOF_ODOROOM=0` restores the floor).
fn odo_rm(c: &Builder, cap: usize, l: usize, extra: usize) -> usize {
    if !super::pointadd::knob("SKYCOF_ODOROOM").map(|v| v != "0").unwrap_or(super::pointadd::ODO_ROOM) {
        return odo_room(c, cap);
    }
    let mut need = 0;
    if small_odo() && l == 3 {
        need = 1;
    } else if l >= 3 || (l == 2 && !small_odo()) {
        while !mm::plan_ok(l, need, extra) {
            need += 1;
        }
    }
    room(c, cap).max(need)
}

/// Two-wire odometer / counter ops without scratch (`SKYCOF_SMALLODO=0` restores the chunked adds).
fn small_odo() -> bool {
    super::pointadd::knob("SKYCOF_SMALLODO").map(|v| v != "0").unwrap_or(super::pointadd::SMALL_ODO)
}

/// `o += ctl (mod 2^len)`.
fn odo_inc(c: &mut Builder, o: &[Q], ctl: Q, rm: usize) {
    if o.len() == 2 && small_odo() {
        c.ccx(ctl, o[0], o[1]);
        c.cx(ctl, o[0]);
    } else if o.len() == 3 && small_odo() {
        // one scratch: s = ctl & o0; o2 ^= s & o1; o1 ^= s; erase s; o0 ^= ctl
        let sq = c.alloc_qubit();
        c.ccx(ctl, o[0], sq);
        c.ccx(sq, o[1], o[2]);
        c.cx(sq, o[1]);
        meas_cz(c, sq, ctl, o[0]);
        c.cx(ctl, o[0]);
    } else {
        mm::odo_inc(c, o, ctl, rm);
    }
}

/// `o -= ctl (mod 2^len)`.
fn odo_dec(c: &mut Builder, o: &[Q], ctl: Q, rm: usize) {
    if (o.len() == 2 || o.len() == 3) && small_odo() {
        c.x_all(o);
        odo_inc(c, o, ctl, rm);
        c.x_all(o);
    } else {
        mm::odo_dec(c, o, ctl, rm);
    }
}

/// `t ^= [o != 0]`.
fn odo_nz(c: &mut Builder, o: &[Q], t: Q, rm: usize) {
    if o.len() == 2 && small_odo() {
        c.x_all(o);
        c.ccx(o[0], o[1], t);
        c.x_all(o);
        c.x(t);
    } else if o.len() == 3 && small_odo() {
        // one scratch: s = !o0 & !o1; t ^= !(s & !o2)
        c.x_all(o);
        let sq = c.alloc_qubit();
        c.ccx(o[0], o[1], sq);
        c.ccx(sq, o[2], t);
        meas_cz(c, sq, o[0], o[1]);
        c.x_all(o);
        c.x(t);
    } else {
        mm::odo_nonzero_xor(c, o, t, rm);
    }
}

fn odo_room(c: &Builder, cap: usize) -> usize {
    room(c, cap).max(4)
}

// ─── decoder ──────────────────────────────────────────────────────────────────────────────────────

/// Wires of one decode on the swapped pair `J'` (tick t, letter t-1).
struct Dctx<'a> {
    a: &'a [Q],
    b: &'a [Q],
    /// frame width of `J'` (= post(t-1))
    f: usize,
    /// typ_t
    t: Q,
    /// isC_t (rails post(t): sign(R2') = sign(R2_t) ^ isC_t)
    isc: Q,
    r1s: Q,
    r2s: Q,
    en: Option<Q>,
}

/// `w ^= sign(R_q)`, `R_q = typ_t ? R1' : R2'`. 1 CCX.
fn sigr_xor(c: &mut Builder, x: &Dctx, w: Q) {
    c.cx(x.r2s, w);
    c.cx(x.isc, w);
    c.cx(x.r2s, x.r1s);
    c.cx(x.isc, x.r1s);
    c.ccx(x.t, x.r1s, w);
    c.cx(x.isc, x.r1s);
    c.cx(x.r2s, x.r1s);
}

/// Measured erase of `w = sign(R_q)`. 0 CCX.
fn sigr_erase(c: &mut Builder, x: &Dctx, w: Q) {
    let m = c.alloc_bit();
    c.hmr(w, m);
    c.z_if(x.r2s, m);
    c.z_if(x.isc, m);
    c.cx(x.r2s, x.r1s);
    c.cx(x.isc, x.r1s);
    c.cz_if(x.t, x.r1s, m);
    c.cx(x.isc, x.r1s);
    c.cx(x.r2s, x.r1s);
    c.free_bit(m);
    c.release_clean(w);
}

/// Toggle `w` between `sigma = !(sa ^ sb ^ sR)` and `!C = a1 ^ b1 ^ sR` (self-inverse; CNOTs only).
fn toggle_sigma_nc(c: &mut Builder, x: &Dctx, w: Q) {
    let (sa, sb) = (x.a[x.f - 1], x.b[x.f - 1]);
    for q in [x.a[1], x.b[1], sa, sb] {
        c.cx(q, w);
    }
    c.x(w);
}

/// `sR <-> sigma` on `w` (self-inverse).
fn toggle_sr_sigma(c: &mut Builder, x: &Dctx, w: Q) {
    c.cx(x.a[x.f - 1], w);
    c.cx(x.b[x.f - 1], w);
    c.x(w);
}

struct Scope {
    w: Q,
    d: Q,
    d_fresh: bool,
    j: usize,
    gid: Vec<Q>,
    xa: Vec<Q>,
    yb: Vec<Q>,
    cin0: Q,
    ge: Q,
    u: Q,
    amb: Q,
    lo: usize,
    /// chunked compare (DECDEF): None = the gid / in-place chain above
    ch: Option<Chunked>,
    /// walk back: forward debts paid in the first pass (also with the gid / in-place chain)
    hk: Vec<Option<crate::circuit::BitId>>,
    /// forward with deferral: push a (possibly empty) record at close
    rec: bool,
}

/// Chunked window compare: `last` = the kept carries of the last chunk (position i holds the carry into i + 1);
/// `bds` = kept chunk boundaries (start, end, wire = carry into end); forward keeps at most one (`bds.len() <= 1`)
/// and HMRs the others with deferred debts.
struct Chunked {
    fwd: bool,
    last: Vec<(usize, Q)>,
    bds: Vec<(usize, usize, Q)>,
    debts: Vec<(usize, crate::circuit::BitId)>,
}

/// Frame decoder compare: chunked to the room, forward boundary debts deferred to the walk back's decode of the
/// same letter (`SKYCOF_DECDEF=0` restores the gid / in-place chain).
fn decdef() -> bool {
    adder::defer_enabled_pub() && super::pointadd::knob("SKYCOF_DECDEF").map(|v| v != "0").unwrap_or(super::pointadd::DEC_DEF)
}

/// `t = MAJ(x, y, ci)` on a fresh wire, x and y restored.
fn majc(c: &mut Builder, x: Q, y: Q, ci: Q) -> Q {
    c.cx(ci, x);
    c.cx(ci, y);
    let t = c.alloc_qubit();
    c.ccx(x, y, t);
    c.cx(ci, t);
    c.cx(ci, x);
    c.cx(ci, y);
    t
}

/// Phase `(-1)^MAJ(x, y, ci)` (Clifford): `MAJ = (x^ci)(y^ci) ^ ci`.
fn majc_phase(c: &mut Builder, x: Q, y: Q, ci: Q) {
    c.cx(ci, x);
    c.cx(ci, y);
    c.cz(x, y);
    c.cx(ci, x);
    c.cx(ci, y);
    c.z_if(ci, crate::circuit::NO_BIT);
}

/// Measured erase of `t = MAJ(x, y, ci)` (0 Toffoli).
fn majc_erase(c: &mut Builder, t: Q, x: Q, y: Q, ci: Q) {
    let m = c.alloc_bit();
    c.hmr(t, m);
    c.push_condition(m);
    majc_phase(c, x, y, ci);
    c.pop_condition();
    c.free_bit(m);
    c.release_clean(t);
}

fn hook_z(c: &mut Builder, hk: &[Option<crate::circuit::BitId>], e: usize, w: Q) {
    if let Some(Some(m)) = hk.get(e) {
        c.z_if(w, *m);
    }
}

impl Scope {
    fn cin(&self, i: usize) -> Q {
        if i == 0 {
            self.cin0
        } else if i <= self.j {
            self.gid[i - 1]
        } else {
            self.xa[i - 1]
        }
    }
}

/// Clamp-tick decoder: `D = en & !C` on b'0 in place instead of a fresh wire (`SKYCOF_DECB0=0` restores).
fn dec_b0() -> bool {
    super::pointadd::knob("SKYCOF_DECB0").map(|v| v != "0").unwrap_or(super::pointadd::DEC_B0)
}

/// Clamp letters (odometer after the decoder): the post-park letter is taken into `g` after the decoder (which
/// leaves a post-park letter alone), so neither `g` nor the letter wire is held across the decoder; the letter wire
/// is freed before the odometer (`SKYCOF_LATE2=0` restores).
fn late2() -> bool {
    odo_after() && super::pointadd::knob("SKYCOF_LATE2").map(|v| v != "0").unwrap_or(super::pointadd::LATE2)
}

fn dec_open(c: &mut Builder, x: &Dctx, cap: usize, w_dec: usize, reserve: usize, fwd: bool) -> Scope {
    let f = x.f;
    let lo = (f - 1).saturating_sub(w_dec).max(1);
    let n = f - 1 - lo;
    assert!(n >= 1, "frame decoder: empty window at f={f}");
    // w = sigma
    let w = c.alloc_qubit();
    sigr_xor(c, x, w);
    toggle_sr_sigma(c, x, w);
    // D = en & !C
    let (d, d_fresh) = match x.en {
        Some(en) if dec_b0() => {
            // b'0 = 1 (b' odd at every tick): b'0 <- en & !C in place, restored to 1 by the measured erase
            let b0 = x.b[0];
            c.x(b0);
            toggle_sigma_nc(c, x, w);
            c.ccx(en, w, b0);
            toggle_sigma_nc(c, x, w);
            (b0, true)
        }
        Some(en) => {
            let d = c.alloc_qubit();
            toggle_sigma_nc(c, x, w);
            c.ccx(en, w, d);
            toggle_sigma_nc(c, x, w);
            (d, true)
        }
        None => {
            // b'0 = 1 (b' odd before park): b'0 <- !C in place
            let b0 = x.b[0];
            toggle_sigma_nc(c, x, w);
            c.cx(w, b0);
            c.x(b0);
            toggle_sigma_nc(c, x, w);
            (b0, false)
        }
    };
    // windows: X = |a'| ^ typ, Y = |b'| ^ typ, complemented for the chain
    let (sa, sb) = (x.a[f - 1], x.b[f - 1]);
    let xa: Vec<Q> = x.a[lo..f - 1].to_vec();
    let yb: Vec<Q> = x.b[lo..f - 1].to_vec();
    for i in 0..n {
        c.cx(sa, xa[i]);
        c.cx(x.t, xa[i]);
        c.cx(sb, yb[i]);
        c.cx(x.t, yb[i]);
        c.x(yb[i]);
    }
    let rm = room(c, cap);
    let j = n.min(rm.saturating_sub(2 + reserve));
    let avail = rm.saturating_sub(2 + reserve);
    let dd = decdef();
    let hk: Vec<Option<crate::circuit::BitId>> = if dd && !fwd {
        let mut h = vec![None; n + 2];
        for (e, m) in adder::defer_pop(3, n) {
            h[e] = Some(m);
        }
        h
    } else {
        Vec::new()
    };
    let mut sc = Scope { w, d, d_fresh, j, gid: Vec::with_capacity(j), xa, yb, cin0: x.a[0], ge: x.a[0], u: x.a[0], amb: x.a[0], lo,
                         ch: None, hk, rec: dd && fwd };
    let chunk_fwd = dd && fwd && avail >= 2 && avail < n;
    let chunk_rev = dd && !fwd && avail >= 2 && avail < n && avail * (avail + 1) / 2 >= n;
    if chunk_fwd || chunk_rev {
        // chunk k computes at most avail - held carries (held = kept boundaries); interiors erased at once
        let mut ch = Chunked { fwd, last: Vec::new(), bds: Vec::new(), debts: Vec::new() };
        let mut start = 0;
        loop {
            let held = ch.bds.len();
            let size = (avail - held).min(n - start);
            assert!(size >= 1);
            let end = start + size;
            let cin_s = ch.bds.last().map_or(sc.cin0, |b| b.2);
            let mut ts: Vec<Q> = Vec::with_capacity(size);
            for i in start..end {
                let ci = if i == start { cin_s } else { ts[i - start - 1] };
                let t = majc(c, sc.xa[i], sc.yb[i], ci);
                hook_z(c, &sc.hk, i + 1, t);
                ts.push(t);
            }
            if end == n {
                ch.last = (start..end).zip(ts).collect();
                break;
            }
            for i in (start..end - 1).rev() {
                let ci = if i == start { cin_s } else { ts[i - start - 1] };
                majc_erase(c, ts[i - start], sc.xa[i], sc.yb[i], ci);
            }
            let bd = ts[size - 1];
            if fwd {
                if let Some((_, e0, w0)) = ch.bds.pop() {
                    let m = c.alloc_bit();
                    c.hmr(w0, m);
                    c.release_clean(w0);
                    ch.debts.push((e0, m));
                }
            }
            ch.bds.push((start, end, bd));
            start = end;
        }
        sc.ge = ch.last.last().unwrap().1;
        sc.ch = Some(ch);
    } else {
        for i in 0..j {
            let ci = sc.cin(i);
            c.cx(ci, sc.xa[i]);
            c.cx(ci, sc.yb[i]);
            let t = c.alloc_qubit();
            c.ccx(sc.xa[i], sc.yb[i], t);
            c.cx(ci, t);
            hook_z(c, &sc.hk, i + 1, t);
            sc.gid.push(t);
        }
        for i in j..n {
            let ci = sc.cin(i);
            c.cx(sc.xa[i], sc.yb[i]);
            c.cx(sc.xa[i], ci);
            c.ccx(ci, sc.yb[i], sc.xa[i]);
            hook_z(c, &sc.hk, i + 1, sc.xa[i]);
        }
        sc.ge = if j == n { sc.gid[n - 1] } else { sc.xa[n - 1] };
    }
    // u = sigma & !ge ; amb = D & !u
    sc.u = c.alloc_qubit();
    c.x(sc.ge);
    c.ccx(sc.w, sc.ge, sc.u);
    c.x(sc.ge);
    sc.amb = c.alloc_qubit();
    c.x(sc.u);
    c.ccx(sc.d, sc.u, sc.amb);
    c.x(sc.u);
    sc
}

fn dec_close(c: &mut Builder, x: &Dctx, mut sc: Scope) {
    // amb = D & !u
    let m = c.alloc_bit();
    c.hmr(sc.amb, m);
    c.x(sc.u);
    c.cz_if(sc.d, sc.u, m);
    c.x(sc.u);
    c.free_bit(m);
    c.release_clean(sc.amb);
    // u = sigma & !ge
    let m = c.alloc_bit();
    c.hmr(sc.u, m);
    c.x(sc.ge);
    c.cz_if(sc.w, sc.ge, m);
    c.x(sc.ge);
    c.free_bit(m);
    c.release_clean(sc.u);
    let n = sc.xa.len();
    if let Some(ch) = sc.ch.take() {
        // last chunk: Clifford erase (its carry-in is the kept boundary or cin0)
        let cin_l = ch.bds.last().map_or(sc.cin0, |b| b.2);
        let l0 = ch.last[0].0;
        for k in (0..ch.last.len()).rev() {
            let (i, t) = ch.last[k];
            let ci = if i == l0 { cin_l } else { ch.last[k - 1].1 };
            majc_erase(c, t, sc.xa[i], sc.yb[i], ci);
        }
        let mut debts = ch.debts;
        let mut bds = ch.bds;
        while let Some((s0, e0, w0)) = bds.pop() {
            let m = c.alloc_bit();
            c.hmr(w0, m);
            c.release_clean(w0);
            if ch.fwd {
                debts.push((e0, m));
                continue;
            }
            // walk back: replay the chunk under the outcome for the boundary's phase
            let bprev = bds.last().map_or(sc.cin0, |b| b.2);
            c.push_condition(m);
            let mut ts: Vec<Q> = Vec::new();
            for i in s0..e0 - 1 {
                let ci = if i == s0 { bprev } else { ts[i - s0 - 1] };
                ts.push(majc(c, sc.xa[i], sc.yb[i], ci));
            }
            let ci = if e0 - 1 == s0 { bprev } else { ts[e0 - 2 - s0] };
            majc_phase(c, sc.xa[e0 - 1], sc.yb[e0 - 1], ci);
            for i in (s0..e0 - 1).rev() {
                let ci = if i == s0 { bprev } else { ts[i - s0 - 1] };
                majc_erase(c, ts[i - s0], sc.xa[i], sc.yb[i], ci);
            }
            c.pop_condition();
            c.free_bit(m);
        }
        if ch.fwd {
            adder::defer_push(3, n, debts);
        }
    } else {
        for i in (sc.j..n).rev() {
            let ci = sc.cin(i);
            c.ccx(ci, sc.yb[i], sc.xa[i]);
            c.cx(sc.xa[i], ci);
            c.cx(sc.xa[i], sc.yb[i]);
        }
        for i in (0..sc.j).rev() {
            let ci = sc.cin(i);
            let t = sc.gid[i];
            c.cx(ci, t);
            meas_cz(c, t, sc.xa[i], sc.yb[i]);
            c.cx(ci, sc.xa[i]);
            c.cx(ci, sc.yb[i]);
        }
        if sc.rec {
            adder::defer_push(3, n, Vec::new());
        }
    }
    let f = x.f;
    let (sa, sb) = (x.a[f - 1], x.b[f - 1]);
    for i in 0..n {
        c.x(sc.yb[i]);
        c.cx(x.t, sc.yb[i]);
        c.cx(sb, sc.yb[i]);
        c.cx(x.t, sc.xa[i]);
        c.cx(sa, sc.xa[i]);
    }
    let _ = sc.lo;
    let w = sc.w;
    if sc.d_fresh {
        let en = x.en.unwrap();
        let m = c.alloc_bit();
        c.hmr(sc.d, m);
        toggle_sigma_nc(c, x, w);
        c.cz_if(en, w, m);
        toggle_sigma_nc(c, x, w);
        c.free_bit(m);
        if sc.d == x.b[0] {
            c.x(sc.d);
        } else {
            c.release_clean(sc.d);
        }
    } else {
        let b0 = x.b[0];
        toggle_sigma_nc(c, x, w);
        c.x(b0);
        c.cx(w, b0);
        toggle_sigma_nc(c, x, w);
    }
    toggle_sr_sigma(c, x, w);
    sigr_erase(c, x, w);
}

/// Room the decoder leaves for the history counter op.
fn ctr_reserve(ctr: Option<&[Q]>) -> usize {
    match ctr {
        None => 0,
        Some(v) if super::pointadd::knob("SKYCOF_ODOROOM").map(|x| x != "0").unwrap_or(super::pointadd::ODO_ROOM) => {
            let mut need = usize::from(small_odo() && v.len() == 3);
            if v.len() >= 4 || (v.len() == 3 && !small_odo()) || (v.len() == 2 && !small_odo()) {
                while !mm::plan_ok(v.len(), need, 0) {
                    need += 1;
                }
            }
            need
        }
        Some(_) => 4,
    }
}

fn dec_push(c: &mut Builder, x: &Dctx, typ: Q, h: &Hreg, cap: usize, w_dec: usize, ctr: Option<&[Q]>) {
    let sc = dec_open(c, x, cap, w_dec, ctr_reserve(ctr), true);
    dec::shift_in(c, sc.amb, typ, &h.wires);
    if let Some(ctr) = ctr {
        let rm = odo_rm(c, cap, ctr.len(), 0);
        if lazy_ctr() {
            odo_inc(c, ctr, sc.amb, rm);
        } else {
            odo_dec(c, ctr, sc.amb, rm);
        }
    }
    c.cx(sc.d, typ);
    c.cx(sc.amb, typ);
    dec_close(c, x, sc);
}

fn dec_pop(c: &mut Builder, x: &Dctx, typ: Q, h: &Hreg, cap: usize, w_dec: usize, ctr: Option<&[Q]>) {
    let sc = dec_open(c, x, cap, w_dec, ctr_reserve(ctr), false);
    c.cx(sc.amb, typ);
    c.cx(sc.d, typ);
    if let Some(ctr) = ctr {
        let rm = odo_rm(c, cap, ctr.len(), 0);
        if lazy_ctr() {
            odo_dec(c, ctr, sc.amb, rm);
        } else {
            odo_inc(c, ctr, sc.amb, rm);
        }
    }
    dec::shift_out(c, sc.amb, typ, &h.wires);
    dec_close(c, x, sc);
}

/// Letter 0 (A or C): `typ ^= !C`. Self-inverse, 1 CCX.
fn dec_first(c: &mut Builder, x: &Dctx, typ: Q) {
    let w = c.alloc_qubit();
    sigr_xor(c, x, w);
    c.cx(x.a[1], typ);
    c.cx(x.b[1], typ);
    c.cx(w, typ);
    sigr_erase(c, x, w);
}

// ─── letter disposal ────────────────────────────────────────────────────────────────────────────

#[allow(clippy::too_many_arguments)]
fn dispose_fwd(c: &mut Builder, p: &WalkParams, env: &Envelope, t1: usize, typ: Q, tt: Q, isc: Q, cof: &FCof,
               rails: &Rails, hl: &mut HLive, odo: &mut Vec<Q>) -> Option<ClampSt> {
    let (h, ctr) = hl.cur_fwd(c, hplan(env, p.r).env[t1], t1);
    let f = cof.a.len();
    assert_eq!(f, fw(env, t1));
    let mut x = Dctx { a: &cof.a, b: &cof.b, f, t: tt, isc, r1s: *rails.r1.last().unwrap(), r2s: *rails.r2.last().unwrap(), en: None };
    let out = if t1 == 0 {
        dec_first(c, &x, typ);
        None
    } else if f == FCL {
        let zt = FPark::compute(c, &cof.b, p.park_j);
        let z = zt.z;
        // odometer: g = z & typ; odo += g; typ ^= g; g ^= z & [odo != 0]  (nz kept live)
        captrap(c, p.cap, "parktest", t1);
        if late2() {
            c.x(z);
            x.en = Some(z);
            captrap(c, p.cap, "pre_dec", t1);
            dec_push(c, &x, typ, h, p.cap, super::pointadd::wdec_at(t1, p.w_dec), ctr);
            captrap(c, p.cap, "dec_push", t1);
            c.x(z);
            // post-park letter (the decoder left it): g = z & typ; typ ^= g -> typ = 0 for every shot
            let g = c.alloc_qubit();
            c.ccx(z, typ, g);
            c.cx(g, typ);
            c.release_clean(typ);
            if grow_odo() {
                odo_grow(c, env, p, odo, t1 + 1);
            } else if odo.is_empty() {
                assert!(late_odo() && t1 + 1 == first_clamp(env, p.r));
                *odo = c.alloc_qubits(p.odo_bits);
            }
            let rm = odo_rm(c, p.cap, odo.len(), 0);
            odo_inc(c, odo, g, rm);
            let nz = c.alloc_qubit();
            let rm = odo_rm(c, p.cap, odo.len(), 1);
            odo_nz(c, odo, nz, rm);
            c.ccx(z, nz, g);
            c.release_clean(g);
            if edrop() {
                captrap(c, p.cap, "odo", t1);
                return Some(ClampSt { zt, nz, e: None });
            }
            let e = c.alloc_qubit();
            c.x(nz);
            c.ccx(z, nz, e);
            c.x(nz);
            captrap(c, p.cap, "odo", t1);
            return Some(ClampSt { zt, nz, e: Some(e) });
        }
        if odo_after() {
            // the letter first (typ ^= g needs only g), then the odometer: its wires and scratch are not held
            // across the decoder
            let g = c.alloc_qubit();
            c.ccx(z, typ, g);
            c.cx(g, typ);
            c.x(z);
            x.en = Some(z);
            captrap(c, p.cap, "pre_dec", t1);
            dec_push(c, &x, typ, h, p.cap, super::pointadd::wdec_at(t1, p.w_dec), ctr);
            captrap(c, p.cap, "dec_push", t1);
            c.x(z);
            if grow_odo() {
                odo_grow(c, env, p, odo, t1 + 1);
            } else if odo.is_empty() {
                assert!(late_odo() && t1 + 1 == first_clamp(env, p.r));
                *odo = c.alloc_qubits(p.odo_bits);
            }
            let rm = odo_rm(c, p.cap, odo.len(), 0);
            odo_inc(c, odo, g, rm);
            let nz = c.alloc_qubit();
            let rm = odo_rm(c, p.cap, odo.len(), 1);
            odo_nz(c, odo, nz, rm);
            c.ccx(z, nz, g);
            c.release_clean(g);
            let e = c.alloc_qubit();
            c.x(nz);
            c.ccx(z, nz, e);
            c.x(nz);
            c.release_clean(typ);
            return Some(ClampSt { zt, nz, e: Some(e) });
        }
        if grow_odo() {
            odo_grow(c, env, p, odo, t1 + 1);
        } else if odo.is_empty() {
            assert!(late_odo() && t1 + 1 == first_clamp(env, p.r));
            *odo = c.alloc_qubits(p.odo_bits);
        }
        let g = c.alloc_qubit();
        c.ccx(z, typ, g);
        let rm = odo_rm(c, p.cap, odo.len(), 0);
        odo_inc(c, odo, g, rm);
        captrap(c, p.cap, "odo_inc", t1);
        c.cx(g, typ);
        let nz = c.alloc_qubit();
        let rm = odo_rm(c, p.cap, odo.len(), 1);
        odo_nz(c, odo, nz, rm);
        c.ccx(z, nz, g);
        c.release_clean(g);
        // entry flag E = z & !nz
        let e = c.alloc_qubit();
        c.x(nz);
        c.ccx(z, nz, e);
        c.x(nz);
        c.x(z);
        x.en = Some(z);
        dec_push(c, &x, typ, h, p.cap, super::pointadd::wdec_at(t1, p.w_dec), ctr);
        c.x(z);
        Some(ClampSt { zt, nz, e: Some(e) })
    } else {
        dec_push(c, &x, typ, h, p.cap, super::pointadd::wdec_at(t1, p.w_dec), ctr);
        None
    };
    c.release_clean(typ);
    out
}

#[allow(clippy::too_many_arguments)]
fn dispose_rev(c: &mut Builder, p: &WalkParams, env: &Envelope, t1: usize, tt: Q, isc: Q, cof: &FCof,
               rails: &Rails, hl: &mut HLive, odo: &mut Vec<Q>, cst: Option<ClampSt>) -> Q {
    let (h, ctr) = hl.cur_rev(c, hplan(env, p.r).env[t1]);
    if t1 > 0 && cst.is_some() && late2() {
        let ClampSt { zt, nz, e } = cst.unwrap();
        let f = cof.a.len();
        assert_eq!(f, fw(env, t1));
        let mut x = Dctx { a: &cof.a, b: &cof.b, f, t: tt, isc, r1s: *rails.r1.last().unwrap(), r2s: *rails.r2.last().unwrap(), en: None };
        let z = zt.z;
        if let Some(e) = e {
            eflag_erase(c, e, z, nz);
        }
        let g = c.alloc_qubit();
        c.ccx(z, nz, g);
        let rm = odo_rm(c, p.cap, odo.len(), 1);
        odo_nz(c, odo, nz, rm);
        c.release_clean(nz);
        let rm = odo_rm(c, p.cap, odo.len(), 0);
        odo_dec(c, odo, g, rm);
        if grow_odo() {
            odo_shrink(c, env, p, odo, if t1 + 1 > first_clamp(env, p.r) { Some(t1) } else { None });
        } else if late_odo() && t1 + 1 == first_clamp(env, p.r) {
            c.free_vec(odo);
            odo.clear();
        }
        let typ = c.alloc_qubit();
        c.cx(g, typ);
        c.ccx(z, typ, g);
        c.release_clean(g);
        c.x(z);
        x.en = Some(z);
        dec_pop(c, &x, typ, h, p.cap, super::pointadd::wdec_at(t1, p.w_dec), ctr);
        c.x(z);
        zt.uncompute(c);
        return typ;
    }
    let typ = c.alloc_qubit();
    let f = cof.a.len();
    assert_eq!(f, fw(env, t1));
    let mut x = Dctx { a: &cof.a, b: &cof.b, f, t: tt, isc, r1s: *rails.r1.last().unwrap(), r2s: *rails.r2.last().unwrap(), en: None };
    if t1 == 0 {
        assert!(cst.is_none());
        dec_first(c, &x, typ);
    } else if cst.is_some() && odo_after() {
        let ClampSt { zt, nz, e } = cst.unwrap();
        let z = zt.z;
        if let Some(e) = e {
            eflag_erase(c, e, z, nz);
        }
        let g = c.alloc_qubit();
        c.ccx(z, nz, g);
        let rm = odo_rm(c, p.cap, odo.len(), 1);
        odo_nz(c, odo, nz, rm);
        c.release_clean(nz);
        let rm = odo_rm(c, p.cap, odo.len(), 0);
        odo_dec(c, odo, g, rm);
        if grow_odo() {
            odo_shrink(c, env, p, odo, if t1 + 1 > first_clamp(env, p.r) { Some(t1) } else { None });
        } else if late_odo() && t1 + 1 == first_clamp(env, p.r) {
            c.free_vec(odo);
            odo.clear();
        }
        c.x(z);
        x.en = Some(z);
        dec_pop(c, &x, typ, h, p.cap, super::pointadd::wdec_at(t1, p.w_dec), ctr);
        c.x(z);
        c.cx(g, typ);
        c.ccx(z, typ, g);
        c.release_clean(g);
        zt.uncompute(c);
    } else if let Some(ClampSt { zt, nz, e }) = cst {
        let z = zt.z;
        c.x(z);
        x.en = Some(z);
        dec_pop(c, &x, typ, h, p.cap, super::pointadd::wdec_at(t1, p.w_dec), ctr);
        c.x(z);
        // E = z & !nz
        if let Some(e) = e {
            eflag_erase(c, e, z, nz);
        }
        // odometer reverse (nz live)
        let g = c.alloc_qubit();
        c.ccx(z, nz, g);
        let rm = odo_rm(c, p.cap, odo.len(), 1);
        odo_nz(c, odo, nz, rm);
        c.release_clean(nz);
        c.cx(g, typ);
        let rm = odo_rm(c, p.cap, odo.len(), 0);
        odo_dec(c, odo, g, rm);
        c.ccx(z, typ, g);
        c.release_clean(g);
        if grow_odo() {
            odo_shrink(c, env, p, odo, if t1 + 1 > first_clamp(env, p.r) { Some(t1) } else { None });
        } else if late_odo() && t1 + 1 == first_clamp(env, p.r) {
            c.free_vec(odo);
            odo.clear();
        }
        zt.uncompute(c);
    } else {
        assert!(f < FCL);
        dec_pop(c, &x, typ, h, p.cap, super::pointadd::wdec_at(t1, p.w_dec), ctr);
    }
    typ
}

// ─── cofactor swap / add / fold / isC ───────────────────────────────────────────────────────────

/// `swap(a, b)` on `c = tt ^ tp` (bit 0 skipped: both odd whenever c = 1). Self-inverse.
fn cswap(c: &mut Builder, cof: &FCof, tt: Q, tp: Option<Q>) {
    assert_eq!(cof.a.len(), cof.b.len());
    if let Some(tp) = tp {
        c.cx(tp, tt);
    }
    for i in 1..cof.a.len() {
        fredkin(c, tt, cof.a[i], cof.b[i]);
    }
    if let Some(tp) = tp {
        c.cx(tp, tt);
    }
}

/// `a <- 2a + (nag ? -b : b)` (mod 2^wadd), `wadd = max(wt, fprev + 1)`; `e` = entry flag (F_e = e & a' >= 0
/// is XORed into the sign wire for the add and removed after it from bit 1 of the result).
#[allow(clippy::too_many_arguments)]
fn cof_add_fwd(c: &mut Builder, cof: &mut FCof, isc: Q, rails: &Rails, fprev: usize, wt: usize, e: Option<(Option<Q>, Q, Q)>, cap: usize) {
    assert_eq!(cof.a.len(), fprev);
    assert_eq!(cof.b.len(), fprev);
    let (r1s, r2s) = (*rails.r1.last().unwrap(), *rails.r2.last().unwrap());
    if let Some(e) = e {
        let sa = cof.a[fprev - 1];
        c.x(sa);
        e_ccx(c, e, sa, isc);
        c.x(sa);
    }
    c.cx(r1s, isc);
    c.cx(r2s, isc);
    let z0 = c.alloc_qubit();
    cof.a.insert(0, z0);
    let wadd = wt.max(fprev + 1);
    resize_signed(c, &mut cof.a, wadd);
    let mut op = cof.b.clone();
    let mut ext = Vec::new();
    while op.len() + 1 < wadd {
        let q = c.alloc_qubit();
        c.cx(*op.last().unwrap(), q);
        op.push(q);
        ext.push(q);
    }
    c.cx_all(isc, &op);
    if coflsb() {
        // b odd: bit 0 of (2a) + (b ^ isc) + isc is 1 with no carry. Before the clamp a was odd too, so bit 1 is
        // 1 + op1 with carry op1: the add starts at bit 2 with carry-in op1 (no Toffoli for bits 0, 1).
        c.x(cof.a[0]);
        if e.is_none() {
            c.cx(op[1], cof.a[1]);
            adder::add_defer(c, &op[2..], &cof.a[2..], Some(op[1]), Some(cap), 2);
        } else {
            adder::add_defer(c, &op[1..], &cof.a[1..], None, Some(cap), 2);
        }
    } else {
        adder::add_defer(c, &op, &cof.a, Some(isc), Some(cap), 2);
    }
    c.cx(*op.last().unwrap(), cof.a[wadd - 1]);
    c.cx_all(isc, &op);
    for &q in ext.iter().rev() {
        let i = op.iter().position(|&w| w == q).unwrap();
        c.cx(op[i - 1], q);
        c.free(q);
    }
    c.cx(r2s, isc);
    c.cx(r1s, isc);
    if let Some(e) = e {
        e_ccx(c, e, cof.a[1], isc);
    }
}

/// Cofactor add without its two constant low bits (`SKYCOF_COFLSB=0` restores the full add byte for byte).
fn coflsb() -> bool {
    super::pointadd::knob("SKYCOF_COFLSB").map(|v| v != "0").unwrap_or(super::pointadd::COFLSB)
}

/// Exact inverse of [`cof_add_fwd`]; `a` enters at `wadd` wires, leaves at `fprev`.
#[allow(clippy::too_many_arguments)]
fn cof_add_rev(c: &mut Builder, cof: &mut FCof, isc: Q, rails: &Rails, fprev: usize, wt: usize, e: Option<(Option<Q>, Q, Q)>, cap: usize) {
    let wadd = wt.max(fprev + 1);
    assert_eq!(cof.a.len(), wadd);
    assert_eq!(cof.b.len(), fprev);
    let (r1s, r2s) = (*rails.r1.last().unwrap(), *rails.r2.last().unwrap());
    if let Some(e) = e {
        e_ccx(c, e, cof.a[1], isc);
    }
    c.cx(r1s, isc);
    c.cx(r2s, isc);
    let mut op = cof.b.clone();
    let mut ext = Vec::new();
    while op.len() + 1 < wadd {
        let q = c.alloc_qubit();
        c.cx(*op.last().unwrap(), q);
        op.push(q);
        ext.push(q);
    }
    c.cx_all(isc, &op);
    c.cx(*op.last().unwrap(), cof.a[wadd - 1]);
    if coflsb() {
        if e.is_none() {
            adder::sub_pay(c, &op[2..], &cof.a[2..], Some(op[1]), Some(cap), 2);
            c.cx(op[1], cof.a[1]);
        } else {
            adder::sub_pay(c, &op[1..], &cof.a[1..], None, Some(cap), 2);
        }
        c.x(cof.a[0]);
    } else {
        adder::sub_pay(c, &op, &cof.a, Some(isc), Some(cap), 2);
    }
    c.cx_all(isc, &op);
    for &q in ext.iter().rev() {
        let i = op.iter().position(|&w| w == q).unwrap();
        c.cx(op[i - 1], q);
        c.free(q);
    }
    c.cx(r2s, isc);
    c.cx(r1s, isc);
    resize_signed(c, &mut cof.a, fprev + 1);
    let z0 = cof.a.remove(0);
    c.free(z0);
    if let Some(e) = e {
        let sa = cof.a[fprev - 1];
        c.x(sa);
        e_ccx(c, e, sa, isc);
        c.x(sa);
    }
}

/// Clamp fold on `x` (FCL + 1 wires): `F = z & x >= 0`; `x -= F p` (low window += F c, top decrement);
/// `F = !x[0]` erased; top wire (a sign copy) trimmed.
fn fold(c: &mut Builder, x: &mut Vec<Q>, b: &[Q], z: Q, p: &WalkParams) {
    assert_eq!(x.len(), FCL + 1);
    let (t256, t257) = (x[N], x[N + 1]);
    let f = c.alloc_qubit();
    c.x(t257);
    c.ccx(z, t257, f);
    c.x(t257);
    let w = p.fold_w;
    let rm = room(c, p.cap);
    if rm >= 12 {
        mm::cadd_k(c, &x[..w], secp_c(), f, rm);
    } else {
        // b = p whenever F can be set: x -= F (p mod 2^w)
        adder::sub(c, Some(f), &b[..w], &x[..w], None, Some(p.cap));
    }
    c.cx(f, t256);
    c.ccx(f, t256, t257);
    c.cx(x[0], f);
    c.x(f);
    c.release_clean(f);
    let top = x.pop().unwrap();
    c.cx(x[N], top);
    c.free(top);
}

/// Exact inverse of [`fold`].
fn unfold(c: &mut Builder, x: &mut Vec<Q>, b: &[Q], z: Q, p: &WalkParams) {
    assert_eq!(x.len(), FCL);
    let top = c.alloc_qubit();
    c.cx(x[N], top);
    x.push(top);
    let (t256, t257) = (x[N], x[N + 1]);
    let f = c.alloc_qubit();
    c.cx(x[0], f);
    c.x(f);
    c.ccx(f, t256, t257);
    c.cx(f, t256);
    let w = p.fold_w;
    let rm = room(c, p.cap);
    if rm >= 12 {
        mm::csub_k(c, &x[..w], secp_c(), f, rm);
    } else {
        adder::add(c, Some(f), &b[..w], &x[..w], None, Some(p.cap));
    }
    // f = z & !x[257]
    let m = c.alloc_bit();
    c.hmr(f, m);
    c.x(t257);
    c.cz_if(z, t257, m);
    c.x(t257);
    c.free_bit(m);
    c.release_clean(f);
}

/// `a[1] ^= b1 ^ sign(R2) ^ 1` (self-inverse): `isC = !typ & a[1]` afterwards.
fn p_into_a1(c: &mut Builder, cof: &FCof, r2s: Q) {
    c.cx(cof.b[1], cof.a[1]);
    c.cx(r2s, cof.a[1]);
    c.x(cof.a[1]);
}

fn erase_isc(c: &mut Builder, cof: &FCof, tt: Q, isc: Q, rails: &Rails) {
    let r2s = *rails.r2.last().unwrap();
    let m = c.alloc_bit();
    c.hmr(isc, m);
    p_into_a1(c, cof, r2s);
    c.x(tt);
    c.cz_if(tt, cof.a[1], m);
    c.x(tt);
    p_into_a1(c, cof, r2s);
    c.free_bit(m);
    c.release_clean(isc);
}

fn isc_recompute(c: &mut Builder, cof: &FCof, tt: Q, rails: &Rails) -> Q {
    let r2s = *rails.r2.last().unwrap();
    let isc = c.alloc_qubit();
    p_into_a1(c, cof, r2s);
    c.x(tt);
    c.ccx(tt, cof.a[1], isc);
    c.x(tt);
    p_into_a1(c, cof, r2s);
    isc
}

static FPROF: std::sync::Mutex<[f64; 8]> = std::sync::Mutex::new([0.0; 8]);
static FPROF_LAST: std::sync::Mutex<f64> = std::sync::Mutex::new(0.0);
/// Research profile: attribute expected Toffoli since the last mark to bucket k.
pub(crate) fn fprof(c: &Builder, k: usize) {
    if let Some((_, e)) = c.report_totals() {
        let mut l = FPROF_LAST.lock().unwrap();
        if k < 8 { FPROF.lock().unwrap()[k] += e - *l; }
        *l = e;
    }
}
static WSUM: std::sync::Mutex<[usize; 6]> = std::sync::Mutex::new([0; 6]);
pub(crate) fn fprof_dump(tag: &str) {
    { let w = WSUM.lock().unwrap(); if w[0] > 0 { eprintln!("SKYCOF_WSUM rail_sw={} rail_ad={} cof_sw={} cof_ad={} hist={} decwin={}", w[0], w[1], w[2], w[3], w[4], w[5]); } }
    let mut a = FPROF.lock().unwrap();
    eprintln!("SKYCOF_FPROF {tag} rail={:.0} cswap={:.0} dispose={:.0} add={:.0} clamp={:.0} isc={:.0} other={:.0} x={:.0}", a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7]);
    *a = [0.0; 8];
}

/// Research: report the step that pushed the window peak above the cap (`SKYCOF_CAPTRAP=1`).
pub(crate) fn captrap(c: &mut Builder, cap: usize, tag: &str, t: usize) {
    if super::pointadd::knob_flag("SKYCOF_CAPTRAP") {
        let pk = c.take_win_peak() as usize;
        if pk > cap {
            eprintln!("SKYCOF_CAPTRAP t={t} step={tag} peak={pk} cap={cap} live={}", c.active_qubits());
        }
    }
}

fn trace_tick(c: &mut Builder, dir: &str, t: usize) {
    if super::pointadd::knob_flag("SKYCOF_TICK_TRACE") {
        let pk = c.take_win_peak();
        eprintln!("SKYCOF_FTICK {dir} {t} live={} peak={pk} ops={} exp={:.1}", c.active_qubits(), c.op_count(), c.report_totals().map_or(0.0, |x| x.1));
    }
}

// ─── the walk ───────────────────────────────────────────────────────────────────────────────────

/// Forward frame walk on `d` (its wires become R2). Returns the parked state with `s = -2^R / d` (lazy).
pub fn forward(c: &mut Builder, p: &WalkParams, env: &Envelope, d: &[Q]) -> FParked {
    let r = p.r;
    adder::defer_active(true);
    let mut rails = walk::seed(c, d);
    // (a, b) = (1, -1) at 2 wires
    let a = c.alloc_qubits(2);
    let b = c.alloc_qubits(2);
    c.x(a[0]);
    c.x(b[0]);
    c.x(b[1]);
    let mut cof = FCof { a, b };
    let mut hl = HLive::new();
    let lazy = lazy_odo();
    let t0 = first_clamp(env, r);
    let mut odo = if lazy { Vec::new() } else { c.alloc_qubits(p.odo_bits) };
    let mut prev = Vec::with_capacity(r);
    let mut typ: Option<Q> = None;
    for t in 0..r {
        let w = env.widths(t);
        let fprev = cof.a.len();
        prev.push((rails.r1.len(), rails.r2.len()));
        if lazy && !late_odo() && t == t0 {
            odo = c.alloc_qubits(p.odo_bits);
        }
        if t >= 1 {
            hl.fwd_event(c, hplan(env, r), t - 1);
        }
        fprof(c, 6);
        let (tt, isc, _) = tick::rail_fwd(c, &mut rails, typ, w.wsw, w.wad, Some(p.cap));
        fprof(c, 0);
        captrap(c, p.cap, "rail", t);
        cswap(c, &cof, tt, typ);
        fprof(c, 1);
        captrap(c, p.cap, "cswap", t);
        let cst = match typ {
            Some(tp) => dispose_fwd(c, p, env, t - 1, tp, tt, isc, &cof, &rails, &mut hl, &mut odo),
            None => None,
        };
        fprof(c, 2);
        captrap(c, p.cap, "dispose", t);
        let ft = fw(env, t);
        let clamp = t >= 1 && fprev == FCL;
        assert_eq!(clamp, cst.is_some());
        let wt = if clamp { ft + 1 } else { ft };
        if super::pointadd::knob_flag("SKYCOF_FPROF") {
            let mut ws = WSUM.lock().unwrap();
            ws[0] += w.wsw - 1; ws[1] += w.wad; ws[2] += fprev - 1; ws[3] += wt.max(fprev + 1); ws[4] += if t >= 1 { hplan(env, r).env[t - 1] } else { 0 };
            ws[5] += if t >= 1 { let f = fprev; (f - 1) - (f - 1).saturating_sub(p.w_dec).max(1) } else { 0 };
            eprintln!("SKYCOF_TROOM t={t} live={} room={} f={fprev} wadd={} rail={}/{} h={} clamp={clamp}", c.active_qubits(), room(c, p.cap), wt.max(fprev + 1), w.wsw, w.wad, hl.all_wires().len());
        }
        cof_add_fwd(c, &mut cof, isc, &rails, fprev, wt, cst.as_ref().map(|s| (s.e, s.zt.z, s.nz)), p.cap);
        fprof(c, 3);
        captrap(c, p.cap, "add", t);
        if let Some(ClampSt { zt, nz, e }) = cst {
            let z = zt.z;
            // E = z & !nz
            if let Some(e) = e {
                eflag_erase(c, e, z, nz);
            }
            let rm = odo_rm(c, p.cap, odo.len(), 1);
            odo_nz(c, &odo, nz, rm);
            c.release_clean(nz);
            captrap(c, p.cap, "add_tail", t);
            fold(c, &mut cof.a, &cof.b, z, p);
            captrap(c, p.cap, "fold", t);
            zt.uncompute(c);
        } else {
            resize_signed(c, &mut cof.a, ft);
        }
        resize_signed(c, &mut cof.b, ft);
        fprof(c, 4);
        captrap(c, p.cap, "clamp", t);
        erase_isc(c, &cof, tt, isc, &rails);
        fprof(c, 5);
        typ = Some(tt);
        trace_tick(c, "fwd", t);
    }
    // the last letter is a post-park A
    let tl = typ.unwrap();
    c.x(tl);
    c.release_clean(tl);
    // parked rails (0, 1), b = p: classical constants
    assert_eq!(rails.r1.len(), env.rail[r - 1]);
    assert_eq!(rails.r2.len(), env.rail[r - 1]);
    c.x(rails.r2[0]);
    c.free_vec(&rails.r1);
    c.free_vec(&rails.r2);
    assert_eq!(cof.a.len(), FCL);
    assert_eq!(cof.b.len(), FCL);
    let pv = crate::point_add::SECP256K1_P;
    for i in 0..N {
        if pv.bit(i) {
            c.x(cof.b[i]);
        }
    }
    c.free_vec(&cof.b);
    // s = x + p = (x - c) + 2^256 ; top wire 0
    let mut a = cof.a;
    let cc = U256::from(secp_c());
    c.x_all(&a);
    crate::point_add::const_arith::add_const(c, &a, cc);
    c.x_all(&a);
    c.x(a[N]);
    let top = a.pop().unwrap();
    c.free(top);
    fprof(c, 6);
    fprof_dump("fwd");
    adder::defer_active(false);
    if let Some(w) = hplan(env, r).merge_end {
        hl.merge(c, w);
    }
    let h = Hreg { wires: hl.all_wires() };
    FParked { s: a, h, hl, odo, prev }
}

/// Exact walk back from [`forward`]'s parked state; returns the wires holding `d`.
pub fn backward(c: &mut Builder, p: &WalkParams, env: &Envelope, pk: FParked) -> Vec<Q> {
    let r = p.r;
    adder::defer_active(true);
    let FParked { s, h: _, mut hl, mut odo, prev } = pk;
    let hp = hplan(env, r);
    if let Some(w) = hp.merge_end {
        hl.unmerge(c, w);
    }
    let lazy = lazy_odo();
    let t0 = first_clamp(env, r);
    let mut a = s;
    assert_eq!(a.len(), N);
    let top = c.alloc_qubit();
    a.push(top);
    // x = s - 2^256 + c
    c.x(a[N]);
    let cc = U256::from(secp_c());
    crate::point_add::const_arith::add_const(c, &a, cc);
    let b = c.alloc_qubits(FCL);
    let pv = crate::point_add::SECP256K1_P;
    for i in 0..N {
        if pv.bit(i) {
            c.x(b[i]);
        }
    }
    let mut cof = FCof { a, b };
    let wl = env.rail[r - 1];
    let mut rails = Rails { r1: c.alloc_qubits(wl), r2: c.alloc_qubits(wl) };
    c.x(rails.r2[0]);
    let tl = c.alloc_qubit();
    c.x(tl);
    let mut typ = tl;
    for t in (0..r).rev() {
        let w = env.widths(t);
        let ft = fw(env, t);
        let fprev = if t == 0 { 2 } else { fw(env, t - 1) };
        let clamp = t >= 1 && fprev == FCL;
        let wt = if clamp { ft + 1 } else { ft };
        assert_eq!(cof.a.len(), ft);
        fprof(c, 6);
        if hsync() && t >= 1 {
            // the forward add of tick t saw the current block at env[t-1] (its top wires are 0 again)
            hl.regs.last_mut().unwrap().shrink_to(c, hp.env[t - 1]);
        }
        let isc = isc_recompute(c, &cof, typ, &rails);
        resize_signed(c, &mut cof.b, fprev);
        let cst = if clamp {
            let zt = FPark::compute(c, &cof.b, p.park_j);
            let z = zt.z;
            unfold(c, &mut cof.a, &cof.b, z, p);
            let nz = c.alloc_qubit();
            let rm = odo_rm(c, p.cap, odo.len(), 1);
            odo_nz(c, &odo, nz, rm);
            if edrop() {
                Some(ClampSt { zt, nz, e: None })
            } else {
                let e = c.alloc_qubit();
                c.x(nz);
                c.ccx(z, nz, e);
                c.x(nz);
                Some(ClampSt { zt, nz, e: Some(e) })
            }
        } else {
            resize_signed(c, &mut cof.a, wt.max(fprev + 1));
            None
        };
        fprof(c, 4);
        cof_add_rev(c, &mut cof, isc, &rails, fprev, wt, cst.as_ref().map(|s| (s.e, s.zt.z, s.nz)), p.cap);
        fprof(c, 3);
        let tprev = if t >= 1 { Some(dispose_rev(c, p, env, t - 1, typ, isc, &cof, &rails, &mut hl, &mut odo, cst)) } else { None };
        if t >= 1 && lazy_ctr() {
            hl.ctr_shrink(c, t - 1);
        }
        if hsync() && t >= 2 {
            // letter t-1 popped: back to the forward's width before its push
            match hp.ev[t - 1] {
                HEv::None => hl.regs.last_mut().unwrap().shrink_to(c, hp.env[t - 2]),
                HEv::Split => hl.regs.last_mut().unwrap().shrink_to(c, 0),
                HEv::Merge => {}
            }
        }
        fprof(c, 2);
        cswap(c, &cof, typ, tprev);
        fprof(c, 1);
        tick::rail_rev(c, &mut rails, typ, isc, tprev, w.wsw, prev[t], Some(p.cap));
        fprof(c, 0);
        if t >= 1 {
            hl.rev_event(c, hp, t - 1);
        }
        trace_tick(c, "rev", t);
        if lazy && !late_odo() && t == t0 {
            c.free_vec(&odo);
            odo = Vec::new();
        }
        if let Some(tq) = tprev {
            typ = tq;
        }
    }
    // cofactors back at (1, -1), width 2; history and odometer empty
    assert_eq!(cof.a.len(), 2);
    c.x(cof.a[0]);
    c.x(cof.b[0]);
    c.x(cof.b[1]);
    c.free_vec(&cof.a);
    c.free_vec(&cof.b);
    fprof(c, 6);
    fprof_dump("rev");
    assert_eq!(hl.regs.len(), 1, "history: blocks left after the walk back");
    assert!(hl.parked.is_empty() && hl.ctrs.iter().all(|x| x.is_none()));
    hl.regs[0].shrink_to(c, 0);
    c.free_vec(&odo);
    adder::defer_active(false);
    assert_eq!(adder::defer_stack_len(), 0, "frame walk: deferred debts left over");
    walk::unseed(c, rails)
}
