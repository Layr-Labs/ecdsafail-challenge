//! Budgeted variants of the stack primitives (track D2, narrow caps).
//!
//! The same maps as [`super::prim`], with fewer clean temporaries: the top `fold` checked levels of a unary
//! iteration or of a constant compare's equality chain are not materialized; their literals are carried as a
//! conjunction ([`Nd::V`]) and folded into the first materialized AND, or into the leaf actions, as multi-controlled
//! gates on borrowed dirty wires (Barenco et al., Lemma 7.2; every dirty wire restored). A clean multi-AND is erased by
//! measurement (HMR + the conditional phase on its controls). The increment keeps only the lowest `m` prefix ANDs and
//! toggles the bits above them by multi-controlled gates.
use super::gl::{Gl, W};

/// A node: the constant 1, a materialized wire, or a virtual conjunction of literals `(wire, negated)`.
#[derive(Clone, Debug)]
pub enum Nd {
    One,
    W(W),
    V(Vec<(W, bool)>),
}

impl Nd {
    pub fn lits(&self) -> Vec<(W, bool)> {
        match self {
            Nd::One => Vec::new(),
            Nd::W(w) => vec![(*w, false)],
            Nd::V(l) => l.clone(),
        }
    }
    pub fn with(&self, lit: (W, bool)) -> Vec<(W, bool)> {
        let mut l = self.lits();
        l.push(lit);
        l
    }
    pub fn of(c: Option<W>) -> Nd {
        c.map_or(Nd::One, Nd::W)
    }
}

fn negs(g: &mut Gl, lits: &[(W, bool)]) {
    for &(w, n) in lits {
        if n {
            g.x(w);
        }
    }
}

fn ctrls(lits: &[(W, bool)]) -> Vec<W> {
    lits.iter().map(|&(w, _)| w).collect()
}

/// `t ^= AND(lits)`; no literal = the constant 1.
pub fn tog(g: &mut Gl, lits: &[(W, bool)], t: W, dirty: &[W]) {
    negs(g, lits);
    match lits.len() {
        0 => g.x(t),
        1 => g.cx(lits[0].0, t),
        2 => g.ccx(lits[0].0, lits[1].0, t),
        _ => g.mcx(&ctrls(lits), t, dirty),
    }
    negs(g, lits);
}

/// `t ^= nd AND (extra literals)`.
pub fn nd_tog(g: &mut Gl, nd: &Nd, extra: &[(W, bool)], t: W, dirty: &[W]) {
    let mut l = nd.lits();
    l.extend_from_slice(extra);
    tog(g, &l, t, dirty);
}

/// Controlled swap of `a`, `b` under `nd` (CX, multi-controlled toggle, CX).
pub fn nd_fred(g: &mut Gl, nd: &Nd, a: W, b: W, dirty: &[W]) {
    match nd {
        Nd::One => {
            g.cx(a, b);
            g.cx(b, a);
            g.cx(a, b);
        }
        Nd::W(w) => g.fred(*w, a, b),
        Nd::V(l) => {
            g.cx(b, a);
            let mut ll = l.clone();
            ll.push((a, false));
            tog(g, &ll, b, dirty);
            g.cx(b, a);
        }
    }
}

fn mand_c(g: &mut Gl, lits: &[(W, bool)], dirty: &[W]) -> W {
    let t = g.alloc();
    negs(g, lits);
    g.mand(&ctrls(lits), t, dirty);
    negs(g, lits);
    t
}

fn mand_u(g: &mut Gl, lits: &[(W, bool)], t: W, dirty: &[W]) {
    negs(g, lits);
    g.mand_u(&ctrls(lits), t, dirty);
    negs(g, lits);
}

enum Undo {
    None,
    X(W),
    And(Vec<(W, bool)>, W),
}

fn materialize(g: &mut Gl, lits: Vec<(W, bool)>, dirty: &[W]) -> (Nd, Undo) {
    match lits.len() {
        0 => (Nd::One, Undo::None),
        1 => {
            let (w, n) = lits[0];
            if n {
                g.x(w);
                (Nd::W(w), Undo::X(w))
            } else {
                (Nd::W(w), Undo::None)
            }
        }
        _ => {
            let t = mand_c(g, &lits, dirty);
            (Nd::W(t), Undo::And(lits, t))
        }
    }
}

fn undo(g: &mut Gl, u: Undo, dirty: &[W]) {
    match u {
        Undo::None => {}
        Undo::X(w) => g.x(w),
        Undo::And(l, t) => mand_u(g, &l, t, dirty),
    }
}

fn inter(x: u64, y: u64, p: u64, q: u64) -> bool {
    !(y < p || x > q)
}

pub type CbN<'a> = dyn FnMut(&mut Gl, u64, &Nd) + 'a;

/// [`super::prim::unary`] with the top `fold` checked levels virtual. A leaf receives its control as an [`Nd`].
#[allow(clippy::too_many_arguments)]
pub fn unary_f(g: &mut Gl, ctrl: Nd, reg: &[W], lo: u64, hi: u64, live: (u64, u64), desc: bool, fold: usize, dirty: &[W], cb: &mut CbN<'_>) {
    let k = reg.len();
    assert!(k < 63 && hi < (1u64 << k) && lo <= hi);
    node(g, ctrl, 0, k as i32 - 1, 0, reg, lo, hi, live, desc, fold, dirty, cb);
}

#[allow(clippy::too_many_arguments)]
fn node(g: &mut Gl, c: Nd, prefix: u64, b: i32, depth: usize, reg: &[W], lo: u64, hi: u64, live: (u64, u64), desc: bool, fold: usize,
        dirty: &[W], cb: &mut CbN<'_>) {
    if b < 0 {
        cb(g, prefix, &c);
        return;
    }
    let bb = b as u32;
    let rng = [(prefix, prefix | ((1u64 << bb) - 1)), (prefix | (1u64 << bb), prefix | ((1u64 << (bb + 1)) - 1))];
    let inp = [inter(rng[0].0, rng[0].1, lo, hi), inter(rng[1].0, rng[1].1, lo, hi)];
    let lv = [inp[0] && inter(rng[0].0, rng[0].1, live.0, live.1), inp[1] && inter(rng[1].0, rng[1].1, live.0, live.1)];
    if !(lv[0] || lv[1]) {
        return;
    }
    if inp[0] != inp[1] {
        let qq = if inp[0] { 0 } else { 1 };
        node(g, c, prefix | (qq << bb), b - 1, depth, reg, lo, hi, live, desc, fold, dirty, cb);
        return;
    }
    let r = reg[b as usize];
    let order: Vec<u64> = (if desc { [1u64, 0] } else { [0u64, 1] }).into_iter().filter(|&qq| lv[qq as usize]).collect();
    if depth < fold {
        for &qq in &order {
            let child = Nd::V(c.with((r, qq == 0)));
            node(g, child, prefix | (qq << bb), b - 1, depth + 1, reg, lo, hi, live, desc, fold, dirty, cb);
        }
        return;
    }
    let first = order[0];
    let (n1, u1) = materialize(g, c.with((r, first == 0)), dirty);
    node(g, n1, prefix | (first << bb), b - 1, depth + 1, reg, lo, hi, live, desc, fold, dirty, cb);
    if order.len() == 1 {
        undo(g, u1, dirty);
        return;
    }
    let second = 1 - first;
    let u2 = match u1 {
        Undo::None | Undo::X(_) => {
            g.x(r);
            if second == 0 {
                Undo::X(r)
            } else {
                Undo::None
            }
        }
        Undo::And(_, t) => {
            let cl = c.lits();
            tog(g, &cl, t, dirty);
            Undo::And(c.with((r, second == 0)), t)
        }
    };
    let n2 = match &u2 {
        Undo::And(_, t) => Nd::W(*t),
        _ => Nd::W(r),
    };
    node(g, n2, prefix | (second << bb), b - 1, depth + 1, reg, lo, hi, live, desc, fold, dirty, cb);
    undo(g, u2, dirty);
}

/// `out ^= ctrl AND [reg <= k]` with the top `fold` levels of the equality chain virtual (materialized levels: one
/// wire each, a level's "less" and "continue" nodes sharing it).
pub fn le_const_f(g: &mut Gl, reg: &[W], k: u64, ctrl: Nd, out: W, fold: usize, dirty: &[W]) {
    let n = reg.len();
    if k >= (1u64 << n) - 1 {
        nd_tog(g, &ctrl, &[], out, dirty);
        return;
    }
    let mut eq = ctrl;
    let mut made: Vec<Undo> = Vec::new();
    for (depth, j) in (0..n).rev().enumerate() {
        let r = reg[j];
        let one = (k >> j) & 1 == 1;
        if depth < fold {
            if one {
                nd_tog(g, &eq, &[(r, true)], out, dirty);
            }
            eq = Nd::V(eq.with((r, !one)));
            continue;
        }
        let (w, u) = materialize(g, eq.with((r, true)), dirty);
        let Nd::W(wq) = w else { unreachable!() };
        let u = if one {
            g.cx(wq, out);
            match u {
                Undo::X(x) => {
                    g.x(x);
                    Undo::None
                }
                Undo::And(_, t) => {
                    let el = eq.lits();
                    tog(g, &el, t, dirty);
                    Undo::And(eq.with((r, false)), t)
                }
                Undo::None => unreachable!(),
            }
        } else {
            u
        };
        made.push(u);
        eq = Nd::W(wq);
    }
    nd_tog(g, &eq, &[], out, dirty);
    for u in made.into_iter().rev() {
        undo(g, u, dirty);
    }
}

/// `reg += ctrl` (mod 2^k) keeping only the lowest `m` prefix ANDs (`m >= k - 1`: the plain increment); each bit j
/// above them is toggled by AND(pre_m, reg_m .. reg_{j-1}), top bit first, on borrowed dirty wires.
pub fn increment_b(g: &mut Gl, reg: &[W], ctrl: Option<W>, m: usize, dirty: &[W]) {
    let k = reg.len();
    if k == 0 {
        return;
    }
    let m = m.clamp(1, k.max(2) - 1);
    // pre[j] = ctrl AND reg_0 .. reg_{j-1}, materialized for j = 1 ..= m (j < k)
    let mut pre: Vec<Option<W>> = vec![None; k];
    let mut owned: Vec<bool> = vec![false; k];
    if k >= 2 {
        pre[1] = Some(match ctrl {
            None => reg[0],
            Some(c) => {
                owned[1] = true;
                mand_c(g, &[(c, false), (reg[0], false)], dirty)
            }
        });
    }
    for j in 2..k.min(m + 1) {
        let p = mand_c(g, &[(pre[j - 1].unwrap(), false), (reg[j - 1], false)], dirty);
        pre[j] = Some(p);
        owned[j] = true;
    }
    let top_mat = k.min(m + 1) - 1; // highest materialized prefix index
    // bits above the materialized prefixes, top first
    for j in (top_mat + 1..k).rev() {
        let mut lits: Vec<(W, bool)> = vec![(pre[top_mat].unwrap(), false)];
        lits.extend((top_mat..j).map(|i| (reg[i], false)));
        tog(g, &lits, reg[j], dirty);
    }
    for j in (1..=top_mat).rev() {
        g.cx(pre[j].unwrap(), reg[j]);
        if owned[j] {
            let prev = if j >= 2 { pre[j - 1].unwrap() } else { ctrl.unwrap() };
            mand_u(g, &[(prev, false), (reg[j - 1], false)], pre[j].unwrap(), dirty);
        }
    }
    match ctrl {
        None => g.x(reg[0]),
        Some(c) => g.cx(c, reg[0]),
    }
}

/// `reg -= ctrl` (mod 2^k), budgeted like [`increment_b`].
pub fn decrement_b(g: &mut Gl, reg: &[W], ctrl: Option<W>, m: usize, dirty: &[W]) {
    for &w in reg {
        g.x(w);
    }
    increment_b(g, reg, ctrl, m, dirty);
    for &w in reg {
        g.x(w);
    }
}
