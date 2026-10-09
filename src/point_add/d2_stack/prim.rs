//! Reversible primitives on a [`Gl`]: unary iteration, controlled increment/decrement, constant compares.
//! `None` as a control means the constant 1.  Registers are little-endian wire lists.
use super::gl::{Gl, W};

fn inter(x: u64, y: u64, p: u64, q: u64) -> bool {
    !(y < p || x > q)
}

/// Unary iteration over the LIVE values `v` in `live = (la, lb)` of register `reg`, under the PROMISE that
/// the register value lies in `[lo, hi]`.  `cb(g, v, leaf)` runs with `leaf = ctrl AND [reg == v]`, exact for
/// every promised register value (`leaf = None` only when the leaf is the constant 1).  Leaves are visited in
/// descending (`desc`) or ascending value order.  One AND per internal split node, erased by measurement.
/// Values outside the promise can fire a wrong leaf (only when `ctrl` = 1); pass `lo = 0, hi = 2^k - 1` for an
/// iteration that is exact for every register value.
pub fn unary(
    g: &mut Gl,
    ctrl: Option<W>,
    reg: &[W],
    lo: u64,
    hi: u64,
    live: (u64, u64),
    desc: bool,
    cb: &mut dyn FnMut(&mut Gl, u64, Option<W>),
) {
    let k = reg.len();
    assert!(k < 63 && hi < (1u64 << k) && lo <= hi);
    node(g, ctrl, 0, k as i32 - 1, reg, lo, hi, live, desc, cb);
}

#[allow(clippy::too_many_arguments)]
fn node(
    g: &mut Gl,
    c: Option<W>,
    prefix: u64,
    b: i32,
    reg: &[W],
    lo: u64,
    hi: u64,
    live: (u64, u64),
    desc: bool,
    cb: &mut dyn FnMut(&mut Gl, u64, Option<W>),
) {
    if b < 0 {
        cb(g, prefix, c);
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
        node(g, c, prefix | (qq << bb), b - 1, reg, lo, hi, live, desc, cb);
        return;
    }
    let r = reg[b as usize];
    let order: Vec<u64> = (if desc { [1u64, 0] } else { [0u64, 1] }).into_iter().filter(|&qq| lv[qq as usize]).collect();
    if order.len() == 1 {
        let qq = order[0];
        match c {
            None => {
                if qq == 0 {
                    g.x(r);
                }
                node(g, Some(r), prefix | (qq << bb), b - 1, reg, lo, hi, live, desc, cb);
                if qq == 0 {
                    g.x(r);
                }
            }
            Some(cw) => {
                if qq == 0 {
                    g.x(r);
                }
                let a = g.and_c(cw, r);
                node(g, Some(a), prefix | (qq << bb), b - 1, reg, lo, hi, live, desc, cb);
                g.and_u(cw, r, a);
                if qq == 0 {
                    g.x(r);
                }
            }
        }
        return;
    }
    let first = order[0];
    match c {
        None => {
            if first == 0 {
                g.x(r);
            }
            node(g, Some(r), prefix | (first << bb), b - 1, reg, lo, hi, live, desc, cb);
            g.x(r);
            node(g, Some(r), prefix | ((1 - first) << bb), b - 1, reg, lo, hi, live, desc, cb);
            if first == 1 {
                g.x(r);
            }
        }
        Some(cw) => {
            if first == 0 {
                g.x(r);
            }
            let a = g.and_c(cw, r);
            if first == 0 {
                g.x(r);
            }
            node(g, Some(a), prefix | (first << bb), b - 1, reg, lo, hi, live, desc, cb);
            g.cx(cw, a);
            node(g, Some(a), prefix | ((1 - first) << bb), b - 1, reg, lo, hi, live, desc, cb);
            if first == 1 {
                g.x(r);
            }
            g.and_u(cw, r, a);
            if first == 1 {
                g.x(r);
            }
        }
    }
}

/// CX with a possibly-constant control.
pub fn cx_o(g: &mut Gl, c: Option<W>, t: W) {
    match c {
        None => g.x(t),
        Some(w) => g.cx(w, t),
    }
}

/// Controlled swap with a possibly-constant control (constant 1 = three CX, no T).
pub fn fred_o(g: &mut Gl, c: Option<W>, a: W, b: W) {
    match c {
        None => {
            g.cx(a, b);
            g.cx(b, a);
            g.cx(a, b);
        }
        Some(w) => g.fred(w, a, b),
    }
}

/// `reg += ctrl` (mod 2^k).  k - 1 T (controlled) / k - 2 T (uncontrolled); prefix ANDs erased by measurement.
pub fn increment(g: &mut Gl, reg: &[W], ctrl: Option<W>) {
    let k = reg.len();
    let mut pre: Vec<Option<W>> = vec![None; k];
    if k >= 2 {
        pre[1] = Some(match ctrl {
            None => reg[0],
            Some(c) => g.and_c(c, reg[0]),
        });
    }
    for j in 2..k {
        let p = g.and_c(pre[j - 1].unwrap(), reg[j - 1]);
        pre[j] = Some(p);
    }
    for j in (1..k).rev() {
        g.cx(pre[j].unwrap(), reg[j]);
        if j >= 2 {
            g.and_u(pre[j - 1].unwrap(), reg[j - 1], pre[j].unwrap());
        } else if let Some(c) = ctrl {
            g.and_u(c, reg[0], pre[1].unwrap());
        }
    }
    cx_o(g, ctrl, reg[0]);
}

/// `reg -= ctrl` (mod 2^k).
pub fn decrement(g: &mut Gl, reg: &[W], ctrl: Option<W>) {
    for &w in reg {
        g.x(w);
    }
    increment(g, reg, ctrl);
    for &w in reg {
        g.x(w);
    }
}

/// A computed AND chain over literals; `out` holds ctrl AND (all literals).  Erase with [`chain_erase`].
pub struct Chain {
    nodes: Vec<(Option<W>, W, bool, W)>, // (prev, lit wire, negated, node)
    pub out: Option<W>,
}

/// AND of `ctrl` and the literals `(wire, want)` (literal true iff wire == want).  One T per literal beyond the
/// first when uncontrolled; the intermediate nodes stay alive until [`chain_erase`] (so the chain can be
/// erased for free).  Returns out = None only when there is nothing to AND (constant 1).
pub fn chain(g: &mut Gl, ctrl: Option<W>, lits: &[(W, bool)]) -> Chain {
    let mut cur = ctrl;
    let mut nodes = Vec::new();
    for &(w, want) in lits {
        match cur {
            None => {
                // first literal with no control: use a copy so that negation does not disturb the wire.
                let t = g.alloc();
                g.cx(w, t);
                if !want {
                    g.x(t);
                }
                nodes.push((None, w, !want, t));
                cur = Some(t);
            }
            Some(p) => {
                if !want {
                    g.x(w);
                }
                let t = g.and_c(p, w);
                if !want {
                    g.x(w);
                }
                nodes.push((Some(p), w, !want, t));
                cur = Some(t);
            }
        }
    }
    Chain { nodes, out: cur }
}

pub fn chain_erase(g: &mut Gl, ch: Chain) {
    for (prev, w, neg, t) in ch.nodes.into_iter().rev() {
        match prev {
            None => {
                if neg {
                    g.x(t);
                }
                g.cx(w, t);
                g.release(t);
            }
            Some(p) => {
                if neg {
                    g.x(w);
                }
                g.and_u(p, w, t);
                if neg {
                    g.x(w);
                }
            }
        }
    }
}

/// `out ^= ctrl AND [reg == k]`.  len(reg) T (uncontrolled: len - 1).
pub fn eq_const_into(g: &mut Gl, reg: &[W], k: u64, ctrl: Option<W>, out: W) {
    let lits: Vec<(W, bool)> = reg.iter().enumerate().map(|(i, &w)| (w, (k >> i) & 1 == 1)).collect();
    let ch = chain(g, ctrl, &lits);
    cx_o(g, ch.out, out);
    chain_erase(g, ch);
}

/// `out ^= ctrl AND [reg in {a, b}]` (a != b).  T = |agree| + 2 |differ| (minus one when uncontrolled).
pub fn memb2_into(g: &mut Gl, reg: &[W], a: u64, b: u64, ctrl: Option<W>, out: W) {
    assert_ne!(a, b);
    let k = reg.len();
    let agree: Vec<(W, bool)> =
        (0..k).filter(|&i| (a >> i) & 1 == (b >> i) & 1).map(|i| (reg[i], (a >> i) & 1 == 1)).collect();
    let da: Vec<(W, bool)> = (0..k).filter(|&i| (a >> i) & 1 != (b >> i) & 1).map(|i| (reg[i], (a >> i) & 1 == 1)).collect();
    let db: Vec<(W, bool)> = da.iter().map(|&(w, v)| (w, !v)).collect();
    let e = chain(g, ctrl, &agree);
    let x1 = chain(g, e.out, &da);
    cx_o(g, x1.out, out);
    chain_erase(g, x1);
    let x2 = chain(g, e.out, &db);
    cx_o(g, x2.out, out);
    chain_erase(g, x2);
    chain_erase(g, e);
}

/// `out ^= ctrl AND [reg <= k]` (MSB-first scan; one AND per bit; the eq chain is erased by measurement).
pub fn le_const_into(g: &mut Gl, reg: &[W], k: u64, ctrl: Option<W>, out: W) {
    let n = reg.len();
    if k >= (1u64 << n) - 1 {
        cx_o(g, ctrl, out);
        return;
    }
    // eq_j = ctrl AND (reg bits above j equal k's).  For k_j = 1: less-than term = eq AND NOT r = eq XOR (eq AND r).
    let mut eq = ctrl;
    let mut made: Vec<(Option<W>, W, bool, W)> = Vec::new();
    for j in (0..n).rev() {
        let r = reg[j];
        let kj = (k >> j) & 1 == 1;
        let nxt = match eq {
            None => {
                let t = g.alloc();
                g.cx(r, t);
                if !kj {
                    g.x(t);
                }
                made.push((None, r, !kj, t));
                t
            }
            Some(p) => {
                if !kj {
                    g.x(r);
                }
                let t = g.and_c(p, r);
                if !kj {
                    g.x(r);
                }
                made.push((Some(p), r, !kj, t));
                t
            }
        };
        if kj {
            // less: eq AND NOT r = eq XOR nxt
            cx_o(g, eq, out);
            g.cx(nxt, out);
        }
        eq = Some(nxt);
    }
    cx_o(g, eq, out); // equal
    for (prev, w, neg, t) in made.into_iter().rev() {
        match prev {
            None => {
                if neg {
                    g.x(t);
                }
                g.cx(w, t);
                g.release(t);
            }
            Some(p) => {
                if neg {
                    g.x(w);
                }
                g.and_u(p, w, t);
                if neg {
                    g.x(w);
                }
            }
        }
    }
}

/// `t ^= K` under `ctrl` (CX fan-out of a constant).
pub fn xor_const(g: &mut Gl, reg: &[W], k: u64, ctrl: Option<W>) {
    for (i, &w) in reg.iter().enumerate() {
        if (k >> i) & 1 == 1 {
            cx_o(g, ctrl, w);
        }
    }
}

/// A flag wire holding f(state), computed by `f` (an `out ^=` style function), its helper chain erased.
/// Erase it later with [`flag_erase`] (re-runs `f`, same T again).
pub fn flag(g: &mut Gl, f: &dyn Fn(&mut Gl, W)) -> W {
    let t = g.alloc();
    f(g, t);
    t
}

pub fn flag_erase(g: &mut Gl, t: W, f: &dyn Fn(&mut Gl, W)) {
    f(g, t);
    g.release(t);
}
