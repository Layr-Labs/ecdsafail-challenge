//! Iterative one-hot engine over a small little-endian register (research code, inert by default).
//!
//! [`Engine`] walks the register's VALUE window `[lo, hi]` (inclusive) in any order and exposes a leaf
//! wire that is `|1>` exactly when `gate AND [reg == v]` for the current value `v` (`gate = None`: no
//! gate). Structure: the prefix-AND tree of a unary iteration, held as one wire per varying level.
//! * The bits above `m = bitlen(lo ^ hi)` are constant over the window: they (and the gate) are folded
//!   into ONE wire `M = gate AND [reg >> m == lo >> m]` (an AND ladder whose intermediates are cleared by
//!   measurement as soon as the top is built).
//! * Levels `j = m-1 .. 0`: `F_j = F_{j+1} AND [reg[j] == v_j]`, `F_m = M`; the leaf is `F_0`
//!   (`M` itself when `m = 0`).
//! * Moving `v -> v'`: with `t` the highest differing bit, levels `0..t` are cleared by measurement
//!   (0 Toffoli, Clifford phase repair), level `t` flips by one CX (`F_t ^= F_{t+1}`), and levels
//!   `t-1..0` are recomputed (`t` Toffoli). Consecutive values cost ~1 Toffoli per step.
//! * [`Engine::finish`] clears every level (0 Toffoli) and the fold wire (`max(0, L-2)` Toffoli
//!   under a measured condition, `L` = number of folded literals).
//! Wires: `m` levels + 1 fold wire (+ `L-2` transient wires while the fold is built / cleared).
//! The register and the gate are read only (restored after every call).
use crate::circuit::QubitId as Q;
use crate::point_add::builder::Builder;

/// A literal `[wire == pol]`.
#[derive(Clone, Copy, Debug)]
pub struct Lit {
    pub q: Q,
    pub pol: bool,
}

fn xb(c: &mut Builder, l: Lit) {
    if !l.pol {
        c.x(l.q);
    }
}

/// `t = AND(lits)` into a fresh wire (`None` for an empty AND = constant 1).
/// Toffoli `max(0, L-1)`; intermediates cleared by measurement.
pub fn and_into(c: &mut Builder, lits: &[Lit]) -> Option<Q> {
    match lits.len() {
        0 => None,
        1 => {
            let t = c.alloc_qubit();
            c.cx(lits[0].q, t);
            if !lits[0].pol {
                c.x(t);
            }
            Some(t)
        }
        _ => {
            let mut chain: Vec<Q> = Vec::new();
            for k in 1..lits.len() {
                let t = c.alloc_qubit();
                let a = if k == 1 { lits[0] } else { Lit { q: chain[k - 2], pol: true } };
                let b = lits[k];
                xb(c, a);
                xb(c, b);
                c.ccx(a.q, b.q, t);
                xb(c, b);
                xb(c, a);
                chain.push(t);
            }
            // clear intermediates top-down (each needs its predecessor alive): t_{L-3} .. t_0
            for k in (0..chain.len() - 1).rev() {
                let a = if k == 0 { lits[0] } else { Lit { q: chain[k - 1], pol: true } };
                mbu_and(c, chain[k], a, lits[k + 1]);
            }
            Some(*chain.last().unwrap())
        }
    }
}

/// Measurement uncompute of `t = a AND b` (0 Toffoli).
pub fn mbu_and(c: &mut Builder, t: Q, a: Lit, b: Lit) {
    let m = c.alloc_bit();
    c.hmr(t, m);
    xb(c, a);
    xb(c, b);
    c.cz_if(a.q, b.q, m);
    xb(c, b);
    xb(c, a);
    c.free_bit(m);
    c.release_clean(t);
}

/// Measurement uncompute of `t = AND(lits)` built by [`and_into`]. Expected Toffoli `max(0, L-2)/2`.
pub fn and_clear(c: &mut Builder, lits: &[Lit], t: Option<Q>) {
    let Some(t) = t else {
        assert!(lits.is_empty());
        return;
    };
    let m = c.alloc_bit();
    c.hmr(t, m);
    c.push_condition(m);
    match lits.len() {
        0 => unreachable!(),
        1 => {
            xb(c, lits[0]);
            c.cz(lits[0].q, lits[0].q);
            xb(c, lits[0]);
        }
        2 => {
            xb(c, lits[0]);
            xb(c, lits[1]);
            c.cz(lits[0].q, lits[1].q);
            xb(c, lits[1]);
            xb(c, lits[0]);
        }
        n => {
            let head = and_into(c, &lits[..n - 1]).unwrap();
            let last = lits[n - 1];
            xb(c, last);
            c.cz(head, last.q);
            xb(c, last);
            and_clear(c, &lits[..n - 1], Some(head));
        }
    }
    c.pop_condition();
    c.free_bit(m);
    c.release_clean(t);
}

/// Largest block (levels) an engine uses: `SKYCOF_RING_ENGINE_M` (default unlimited). Smaller blocks
/// save wires (one per level) at the cost of rebuilding the fold wire at every block crossing.
pub fn max_block_bits() -> usize {
    static M: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *M.get_or_init(|| std::env::var("SKYCOF_RING_ENGINE_M").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(64))
}

pub struct Engine {
    reg: Vec<Q>,
    gate: Option<Q>,
    m: usize,
    blk: Option<usize>,
    fold_lits: Vec<Lit>,
    fold: Option<Q>,
    lv: Vec<Option<Q>>,
    cur: Option<usize>,
    lo: usize,
    hi: usize,
}

impl Engine {
    /// Engine over values `[lo, hi]` of `reg` (little-endian), gated by `gate`. The window is covered
    /// by at most two aligned blocks of `2^m` values, `m = bitlen(hi - lo)`; the fold wire holds
    /// `gate AND [reg >> m == block]` and is rebuilt when a `goto` crosses into the other block.
    pub fn new(_c: &mut Builder, reg: &[Q], gate: Option<Q>, lo: usize, hi: usize) -> Engine {
        let k = reg.len();
        assert!(lo <= hi && hi < (1usize << k), "engine window [{lo},{hi}] for a {k}-bit register");
        let m = ((usize::BITS - (hi - lo).leading_zeros()) as usize).min(k).min(max_block_bits());
        Engine { reg: reg.to_vec(), gate, m, blk: None, fold_lits: Vec::new(), fold: None, lv: vec![None; m], cur: None, lo, hi }
    }

    /// Live wires at most (levels + fold), excluding the transient fold ladder.
    pub fn wires(&self) -> usize {
        self.m + 1
    }

    fn set_block(&mut self, c: &mut Builder, b: usize) {
        if self.blk == Some(b) {
            return;
        }
        if self.blk.is_some() {
            let lits = std::mem::take(&mut self.fold_lits);
            and_clear(c, &lits, self.fold.take());
        }
        let mut lits: Vec<Lit> = Vec::new();
        if let Some(g) = self.gate {
            lits.push(Lit { q: g, pol: true });
        }
        for j in (self.m..self.reg.len()).rev() {
            lits.push(Lit { q: self.reg[j], pol: ((b << self.m) >> j) & 1 == 1 });
        }
        self.fold = and_into(c, &lits);
        self.fold_lits = lits;
        self.blk = Some(b);
    }

    fn parent(&self, j: usize) -> Option<Q> {
        if j + 1 == self.m { self.fold } else { self.lv[j + 1] }
    }

    fn lit(&self, j: usize, v: usize) -> Lit {
        Lit { q: self.reg[j], pol: (v >> j) & 1 == 1 }
    }

    fn compute(&mut self, c: &mut Builder, j: usize, v: usize) {
        let l = self.lit(j, v);
        let t = match self.parent(j) {
            None => and_into(c, &[l]).unwrap(),
            Some(p) => {
                let t = c.alloc_qubit();
                xb(c, l);
                c.ccx(p, l.q, t);
                xb(c, l);
                t
            }
        };
        self.lv[j] = Some(t);
    }

    fn clear(&mut self, c: &mut Builder, j: usize, v: usize) {
        let t = self.lv[j].take().unwrap();
        let l = self.lit(j, v);
        match self.parent(j) {
            None => {
                // t = [reg[j] == v_j]: unitary uncompute
                c.cx(l.q, t);
                if !l.pol {
                    c.x(t);
                }
                c.release_clean(t);
            }
            Some(p) => mbu_and(c, t, Lit { q: p, pol: true }, l),
        }
    }

    /// Position the engine at value `v` (inside the window).
    pub fn goto(&mut self, c: &mut Builder, v: usize) {
        assert!(v >= self.lo && v <= self.hi, "engine goto {v} outside [{},{}]", self.lo, self.hi);
        if self.blk != Some(v >> self.m) {
            if let Some(u) = self.cur.take() {
                for j in 0..self.m {
                    self.clear(c, j, u);
                }
            }
            self.set_block(c, v >> self.m);
        }
        match self.cur {
            None => {
                for j in (0..self.m).rev() {
                    self.compute(c, j, v);
                }
            }
            Some(u) if u == v => {}
            Some(u) => {
                let t = (usize::BITS - 1 - (u ^ v).leading_zeros()) as usize;
                for j in 0..t {
                    self.clear(c, j, u);
                }
                let lt = self.lv[t].unwrap();
                match self.parent(t) {
                    Some(p) => c.cx(p, lt),
                    None => c.x(lt),
                }
                for j in (0..t).rev() {
                    self.compute(c, j, v);
                }
            }
        }
        self.cur = Some(v);
    }

    /// Leaf wire `gate AND [reg == cur]` (`None` = constant 1: ungated single-value window over a 0-bit
    /// fold, never in practice).
    pub fn leaf(&self) -> Option<Q> {
        assert!(self.cur.is_some(), "engine leaf before goto");
        if self.m == 0 { self.fold } else { self.lv[0] }
    }

    /// Clear every level and the fold wire.
    pub fn finish(mut self, c: &mut Builder) {
        if let Some(u) = self.cur {
            for j in 0..self.m {
                self.clear(c, j, u);
            }
        }
        if self.blk.is_some() {
            let lits = std::mem::take(&mut self.fold_lits);
            and_clear(c, &lits, self.fold.take());
        }
    }
}

/// AND of `lits` held on one wire with few transient wires: part ANDs of `part` literals ([`and_into`]),
/// their AND into the result, then every part AND erased by measurement ([`and_clear`]). Transient wires
/// at most `(#parts - 1) + (part - 1)` while the parts are built, `2 #parts - 1` while the result is.
pub struct FAnd {
    pub z: Q,
    parts: Vec<Vec<Lit>>,
}

pub fn frozen_and(c: &mut Builder, lits: &[Lit], part: usize) -> FAnd {
    assert!(!lits.is_empty() && part >= 2);
    if lits.len() <= part {
        let z = and_into(c, lits).unwrap();
        return FAnd { z, parts: vec![lits.to_vec()] };
    }
    let parts: Vec<Vec<Lit>> = lits.chunks(part).map(|p| p.to_vec()).collect();
    let a: Vec<Q> = parts.iter().map(|p| and_into(c, p).unwrap()).collect();
    let al: Vec<Lit> = a.iter().map(|&q| Lit { q, pol: true }).collect();
    let z = and_into(c, &al).unwrap();
    for (p, &ai) in parts.iter().zip(&a).rev() {
        and_clear(c, p, Some(ai));
    }
    FAnd { z, parts }
}

impl FAnd {
    /// Measurement uncompute of the held AND (phase recomputed from the parts under the outcome).
    pub fn clear(self, c: &mut Builder) {
        if self.parts.len() == 1 {
            and_clear(c, &self.parts[0], Some(self.z));
            return;
        }
        let m = c.alloc_bit();
        c.hmr(self.z, m);
        c.push_condition(m);
        let a: Vec<Q> = self.parts.iter().map(|p| and_into(c, p).unwrap()).collect();
        let k = a.len();
        let al: Vec<Lit> = a.iter().map(|&q| Lit { q, pol: true }).collect();
        if k == 1 {
            c.cz(a[0], a[0]);
        } else {
            let head = and_into(c, &al[..k - 1]).unwrap();
            c.cz(head, a[k - 1]);
            and_clear(c, &al[..k - 1], Some(head));
        }
        for (p, &ai) in self.parts.iter().zip(&a).rev() {
            and_clear(c, p, Some(ai));
        }
        c.pop_condition();
        c.free_bit(m);
        c.release_clean(self.z);
    }
}
