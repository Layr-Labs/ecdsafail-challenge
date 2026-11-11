//! Low-qubit point addition around a self-inverse Euclid inverter F: |x>|0> -> |a>|par>|0>, a = +-1/x mod p.
//! F is an exact restoring-row Euclid walk with no history tape: quotient digits grow in the freed top lanes of the
//! dividend ring and are consumed by the inverse of the same row on the cofactors, so the reverse pass is the reversed
//! gate list. The N ring is its own clock: its root rises one wire per slot and acts when it reaches the top wire, so
//! the only length register is E = F - L_frame mod 32. Translated from emit/srm2.py + emit/pa2.py.
use crate::circuit::{BitId, Op, OperationType, QubitId, RegisterId};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::atomic::{AtomicBool, Ordering};

const N: usize = 256;
const W: usize = N + 1;
const NONE: u32 = u32::MAX;
const EB: usize = 2;
/// Clean lane for the AND of many controls inside F.
const ZB: usize = 1;
/// hmr-and (lane zfor-wait): the clean-lane AND of every cc_core call is uncomputed by X-basis measurement (Hmr) and
/// CZ(c0, c1) under the outcome (Gidney arXiv:1709.06648) instead of the unitary Toffoli: -1 T per call.
const HMR_AND: bool = true;
const HMR_NEGCTL: bool = false;
/// Marks both AND gates of a cc_core pair on the target wire; P::gate toggles compute / measured uncompute per lane.
const AND_FLAG: u32 = 1 << 30;
static IN_F: AtomicBool = AtomicBool::new(false);
static NO_Z: AtomicBool = AtomicBool::new(false);
const PIW: usize = 48;
const ECAP: i32 = 26;
const RW: usize = 64;
/// Clean lanes for the merged fold chain.
const ZL: usize = 4;
/// Each fold chain runs this many wires from its own start: a carry gets j wires with 2^-j.
const CHW: usize = 33;
/// ov is read back on this many top wires.
const CMPW: usize = 34;
/// LEAN_SQ (lane arxiv-research): x += lam^2 by three Karatsuba half-squares in one 258-wire register (Haener,
/// Tripier, Young et al. arXiv:2609.05625 section VII.1 squarer form, Gidney 1709.06648 halved adders whose AND
/// ancillae are the register's still-clean upper wires), folded into x with the parent's chains. Off re-emits the parent.
const LEAN_SQ: bool = true;
const LEAN_NEGCTL: bool = false;
/// LEAN_SB: 256-wire register, cross product L*H by controlled adds (no S^2); LEAN_ZL = fold lanes (3 at Q773).
const LEAN_SB: bool = true;
const LEAN_ZL: usize = 4;
/// carry window above a spill addend (the carry past it is dropped: 2^-64 per spill add)
const SPILL_W: usize = 64;
/// Multiplier bits consumed into the product.
const CAPW: usize = 0;
/// Low lanes read when a seed tests a product for zero.
const ZW: usize = 64;
const C0M1: [usize; 6] = [4, 6, 7, 8, 9, 32]; // bits of 2^32 + 976
const P0: [u64; 4] = [0xFFFFFFFEFFFFFC2F, u64::MAX, u64::MAX, u64::MAX];

fn pbit(i: usize) -> bool {
    (P0[i / 64] >> (i % 64)) & 1 == 1
}

#[derive(Clone, Copy)]
struct G(u32, u32, u32);
type Lit = (u32, bool);
type GL = Vec<G>;
#[inline]
fn gx(a: u32) -> G {
    G(a, NONE, NONE)
}
#[inline]
fn gc(a: u32, b: u32) -> G {
    G(a, b, NONE)
}
#[inline]
fn gt(a: u32, b: u32, c: u32) -> G {
    G(a, b, c)
}
fn rev(g: &[G]) -> GL {
    g.iter().rev().cloned().collect()
}

/// AND of k controls on one clean lane, 2k-3 T: conditionally clean wires, Khattar-Gidney 2024.
fn cc_core(cs: &[u32], tgt: u32, z: u32) -> GL {
    let k = cs.len();
    let m = k / 2;
    let zf = if HMR_AND { z | AND_FLAG } else { z };
    let mut up: GL = vec![gt(cs[0], cs[1], zf), gc(z, cs[0]), gc(z, cs[1])];
    let (mut guards, mut aa, mut bb) = (vec![z], vec![cs[0]], vec![cs[1]]);
    for i in 1..m {
        let (a, b) = (cs[2 * i], cs[2 * i + 1]);
        let g = aa[i - 1];
        up.extend_from_slice(&[gt(a, b, g), gc(g, a), gc(g, b)]);
        guards.push(g);
        aa.push(a);
        bb.push(b);
    }
    let mut cur = guards[m - 1];
    let mut walk: GL = vec![];
    let mut out = up.clone();
    if k % 2 == 1 {
        let x = cs[k - 1];
        if m == 1 {
            out.push(gt(z, x, tgt));
            out.extend(rev(&up));
            return out;
        }
        walk.push(gt(cur, x, bb[m - 2]));
        cur = bb[m - 2];
    }
    if m >= 2 {
        let mut i = m - 2;
        while i >= 1 {
            walk.push(gt(cur, guards[i], bb[i - 1]));
            cur = bb[i - 1];
            i -= 1;
        }
    }
    out.extend_from_slice(&walk);
    out.push(gt(cur, guards[0], tgt));
    out.extend(rev(&walk));
    out.extend(rev(&up));
    out
}

fn mcx(lits: &[Lit], tgt: u32, dirty: &[u32]) -> GL {
    let mut l: Vec<Lit> = Vec::with_capacity(lits.len());
    for &(q0, p) in lits {
        match l.iter().find(|x| x.0 == q0) {
            Some(x) => {
                if x.1 != p {
                    return vec![];
                }
            }
            None => l.push((q0, p)),
        }
    }
    let k = l.len();
    if k == 0 {
        return vec![gx(tgt)];
    }
    let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
    let mut g = pre.clone();
    if k == 1 {
        g.push(gc(l[0].0, tgt));
    } else if k == 2 {
        g.push(gt(l[0].0, l[1].0, tgt));
    } else if ZB > 0 && IN_F.load(Ordering::Relaxed) && !NO_Z.load(Ordering::Relaxed) {
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        g.extend(cc_core(&cs, tgt, 512));
    } else {
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        let mut an: Vec<u32> = Vec::with_capacity(k - 2);
        for &d in dirty {
            if d != tgt && !cs.contains(&d) {
                an.push(d);
                if an.len() == k - 2 {
                    break;
                }
            }
        }
        assert!(an.len() == k - 2);
        let mut up = vec![gt(cs[k - 1], an[k - 3], tgt)];
        let mut i = k - 2;
        while i > 1 {
            up.push(gt(cs[i], an[i - 2], an[i - 1]));
            i -= 1;
        }
        let mid = gt(cs[0], cs[1], an[0]);
        g.extend_from_slice(&up);
        g.push(mid);
        g.extend(up.iter().rev().cloned());
        g.extend_from_slice(&up[1..]);
        g.push(mid);
        g.extend(up[1..].iter().rev().cloned());
    }
    g.extend_from_slice(&pre);
    g
}

fn cswap(c: u32, a: u32, b: u32, g: &mut GL) {
    g.push(gc(b, a));
    g.push(gt(c, a, b));
    g.push(gc(b, a));
}

fn rotate_up(ctl: u32, w: &[u32], r: usize) -> GL {
    let n = w.len();
    let r = r % n;
    let mut g = vec![];
    if r == 0 {
        return g;
    }
    let mut seen = vec![false; n];
    for st in 0..n {
        if seen[st] {
            continue;
        }
        let mut i = st;
        let mut cyc = vec![];
        while !seen[i] {
            seen[i] = true;
            cyc.push(i);
            i = (i + r) % n;
        }
        for j in 1..cyc.len() {
            cswap(ctl, w[cyc[0]], w[cyc[j]], &mut g);
        }
    }
    g
}

fn inc_ctl(reg: &[u32], lits: &[Lit], dirty: &[u32]) -> GL {
    let mut g = vec![];
    for i in (0..reg.len()).rev() {
        let mut l: Vec<Lit> = lits.to_vec();
        for j in 0..i {
            l.push((reg[j], true));
        }
        g.extend(mcx(&l, reg[i], dirty));
    }
    g
}
fn dec_ctl(reg: &[u32], lits: &[Lit], dirty: &[u32]) -> GL {
    rev(&inc_ctl(reg, lits, dirty))
}

fn add_chain(t: &[u32], s: &[u32], c: u32) -> GL {
    let n = t.len();
    let mut g = Vec::with_capacity(7 * n);
    for i in 0..n {
        g.push(gc(c, s[i]));
        g.push(gc(c, t[i]));
        g.push(gt(s[i], t[i], c));
    }
    for i in (0..n).rev() {
        g.push(gt(s[i], t[i], c));
        g.push(gc(c, t[i]));
        g.push(gc(s[i], t[i]));
        g.push(gc(c, s[i]));
    }
    g
}

fn inc_long(reg: &[u32], ctl: u32, dirty: &[u32], c: u32) -> GL {
    let mut r = vec![ctl];
    r.extend_from_slice(reg);
    let mut d: Vec<u32> = Vec::with_capacity(r.len());
    for &q0 in dirty {
        if q0 != c && !r.contains(&q0) {
            d.push(q0);
            if d.len() == r.len() {
                break;
            }
        }
    }
    assert!(d.len() == r.len());
    let sub = rev(&add_chain(&r, &d, c));
    let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
    let mut g = sub.clone();
    g.extend_from_slice(&nots);
    g.extend_from_slice(&sub);
    g.extend_from_slice(&nots);
    g.push(gx(ctl));
    g
}

fn aligned_blocks(vals: &BTreeSet<i32>) -> Vec<(i32, usize)> {
    let mut out = vec![];
    let mut vals = vals.clone();
    while let Some(&v) = vals.iter().next() {
        let mut k = 0usize;
        loop {
            let k2 = k + 1;
            if v & ((1 << k2) - 1) != 0 {
                break;
            }
            if (0..(1 << k2)).all(|i| vals.contains(&(v + i))) {
                k = k2;
            } else {
                break;
            }
        }
        out.push((v, k));
        for i in 0..(1 << k) {
            vals.remove(&(v + i));
        }
    }
    out
}

const fn maskv(v: usize) -> u128 {
    let mut m = 0u128;
    let mut p = 0;
    while p < 128 {
        if (p >> v) & 1 == 0 {
            m |= 1u128 << p;
        }
        p += 1;
    }
    m
}
const MASKV: [u128; 7] = [maskv(0), maskv(1), maskv(2), maskv(3), maskv(4), maskv(5), maskv(6)];
type Cubes = Vec<Vec<(usize, u8)>>;
/// Minimum cost disjoint decision tree over the hi bits (vars 0..3) and the parity (var 4).
fn tree_rec(on: u128, off: u128, n: i32, base: i32, vs: &[usize], memo: &mut HashMap<(u128, u128, i32), (i64, Cubes)>) -> (i64, Cubes) {
    if on == 0 {
        return (0, vec![]);
    }
    if off == 0 {
        let l = n + base;
        let c = if l <= 1 { 0 } else if l == 2 { 1 } else { 4 * (l as i64 - 2) };
        return (c, vec![vec![]]);
    }
    if let Some(r) = memo.get(&(on, off, n)) {
        return r.clone();
    }
    let mut best: Option<(i64, Cubes)> = None;
    for &v in vs {
        let z = MASKV[v];
        let (on0, on1, off0, off1) = (on & z, on & !z, off & z, off & !z);
        if (on0 == 0 && off0 == 0) || (on1 == 0 && off1 == 0) {
            continue;
        }
        let (c0, l0) = tree_rec(on0, off0, n + 1, base, vs, memo);
        let (c1, l1) = tree_rec(on1, off1, n + 1, base, vs, memo);
        if best.is_none() || c0 + c1 < best.as_ref().unwrap().0 {
            let mut lst: Cubes = vec![];
            for x in &l0 {
                let mut y = vec![(v, 0u8)];
                y.extend_from_slice(x);
                lst.push(y);
            }
            for x in &l1 {
                let mut y = vec![(v, 1u8)];
                y.extend_from_slice(x);
                lst.push(y);
            }
            best = Some((c0 + c1, lst));
        }
    }
    let r = best.expect("cover");
    memo.insert((on, off, n), r.clone());
    r
}
fn dtree(on: u128, off: u128, vs: &[usize], base: i32) -> Cubes {
    let mut memo = HashMap::new();
    tree_rec(on, off, 0, base, vs, &mut memo).1
}

/// lane allocator of the stored inverter (virtual lanes)
struct B {
    free: Vec<u32>,
    next: u32,
    gates: Vec<G>,
}
impl B {
    fn alloc(&mut self) -> u32 {
        if let Some(q0) = self.free.pop() {
            q0
        } else {
            self.next += 1;
            self.next - 1
        }
    }
    fn release(&mut self, q0: u32) {
        self.free.push(q0);
        self.free.sort_by(|a, b| b.cmp(a));
    }
    fn t(&mut self, g: &[G]) {
        self.gates.extend_from_slice(g);
    }
}

struct Machine {
    b: B,
    dirty: Vec<u32>,
    pas: Vec<u32>,
    x: Vec<u32>,
    y: Vec<u32>,
    e: Vec<u32>,
    par: u32,
}

fn lf(t: i32, e: i32) -> (i32, i32) {
    if t % 2 == 1 {
        return ((t - 1) / 2, (t + 1) / 2);
    }
    let m = e >> 1;
    (t / 2 - m, t / 2 + m + (e & 1))
}
fn pairs(t: i32) -> Vec<i32> {
    let n = N as i32;
    if t % 2 == 1 {
        let (l, f) = lf(t, 1);
        return if l >= 1 && f <= n { vec![1] } else { vec![] };
    }
    (0..=ECAP)
        .filter(|&e| {
            let (l, f) = lf(t, e);
            l >= 1 && f <= n && f >= l
        })
        .collect()
}

/// Rotate a wire list up by one under c: w[i] to w[i+1], top wraps to the bottom.
fn rot1(c: u32, w: &[u32]) -> GL {
    let mut g = vec![];
    for i in (1..w.len()).rev() {
        cswap(c, w[i], w[i - 1], &mut g);
    }
    g
}

impl Machine {
    fn m(&self, l: &[Lit], t: u32) -> GL {
        mcx(l, t, &self.dirty)
    }
    fn hl(&self, v: i32) -> Vec<Lit> {
        (0..EB).map(|i| (self.e[i], (v >> i) & 1 == 1)).collect()
    }
    fn init(&mut self) {
        let mut g: GL = vec![gx(self.x[0])];
        for i in 0..N {
            if pbit(i) {
                g.push(gx(self.x[i + 1]));
            }
        }
        let xl: Vec<u32> = self.y[2..].to_vec();
        for &q0 in &xl {
            g.push(gc(self.par, q0));
        }
        let cl = self.e[0];
        for &i in &C0M1 {
            g.extend(rev(&inc_long(&xl[i..], self.par, &self.dirty, cl)));
        }
        self.b.t(&g);
    }
    #[allow(clippy::too_many_arguments)]
    fn row(&self, t: &[u32], s: &[u32], top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>) -> GL {
        let n = t.len();
        let mut g: GL = Vec::with_capacity(12 * n);
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        if top != NONE {
            conj.push(gx(top));
        }
        g.extend_from_slice(&conj);
        let wend = match inline {
            Some(il) => il.keys().next_back().map(|k| k + 1).unwrap_or(0),
            None => tog.keys().next_back().map(|k| k + 1).unwrap_or(0),
        };
        let gate3 = |g: &mut GL, a0: u32, a1: u32, tgt: u32, i: usize| {
            if let Some(il) = inline {
                for li in &il[&i] {
                    let mut l = vec![(a0, true), (a1, true)];
                    l.extend_from_slice(li);
                    g.extend(self.m(&l, tgt));
                }
            } else {
                g.extend(self.m(&[(a0, true), (a1, true), (m, true)], tgt));
            }
        };
        for i in 0..n {
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
            g.push(gc(c, s[i]));
            g.push(gc(c, t[i]));
            if i < wend {
                gate3(&mut g, s[i], t[i], c, i);
            } else {
                g.push(gt(s[i], t[i], c));
            }
        }
        for li in active {
            g.extend(self.m(li, d));
        }
        if top != NONE {
            for li in active {
                let mut l = li.clone();
                l.extend_from_slice(&[(c, true), (top, true)]);
                g.extend(self.m(&l, d));
            }
            g.push(gt(d, c, top));
        } else {
            for li in active {
                let mut l = li.clone();
                l.push((c, true));
                g.extend(self.m(&l, d));
            }
        }
        for i in (0..n).rev() {
            if i < wend {
                gate3(&mut g, s[i], t[i], c, i);
            } else {
                g.push(gt(s[i], t[i], c));
            }
            g.push(gc(c, t[i]));
            if i < wend {
                gate3(&mut g, d, s[i], t[i], i);
            } else {
                g.push(gt(d, s[i], t[i]));
            }
            g.push(gc(c, s[i]));
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
        }
        g.extend_from_slice(&conj);
        g
    }
    #[allow(clippy::too_many_arguments)]
    fn row_v(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>) -> GL {
        self.row_vz(t, s, t1, top, d, c, m, tog, active, inline, cv, false)
    }
    fn row_vz(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>, nz: bool) -> GL {
        self.row_vzx(t, s, t1, top, d, c, m, tog, active, inline, cv, nz, NONE)
    }
    fn row_vzx(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32, m: u32, tog: &BTreeMap<usize, Vec<Vec<Lit>>>, active: &[Vec<Lit>], inline: Option<&BTreeMap<usize, Vec<Vec<Lit>>>>, cv: Option<&GL>, nz: bool, xh1: u32) -> GL {
        let n = t.len();
        let mut g: GL = Vec::with_capacity(12 * n);
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        g.extend_from_slice(&conj);
        let wend = match inline {
            Some(il) => il.keys().next_back().map(|k| (k + 1).min(n)).unwrap_or(0),
            None => tog.keys().next_back().map(|k| (k + 1).min(n)).unwrap_or(0),
        };
        if let Some(cg) = cv {
            g.extend_from_slice(cg);
        }
        for i in 0..n {
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.mz(l, m, d));
                    }
                }
            }
            g.push(gc(c, s[i]));
            g.push(gc(c, t[i]));
            if i < wend && inline.is_some() {
                for li in &inline.unwrap()[&i] {
                    let mut l = vec![(s[i], true), (t[i], true)];
                    l.extend_from_slice(li);
                    g.extend(if nz { self.m(&l, c) } else { self.mz(&l, c, d) });
                }
            } else if m != NONE && i < wend {
                g.extend(self.mz(&[(s[i], true), (t[i], true), (m, true)], c, d));
            } else {
                g.push(gt(s[i], t[i], c));
            }
        }
        if let Some(cg) = cv {
            g.extend(rev(cg));
        }
        if top != NONE {
            for li in active {
                let mut a2: Vec<Lit> = li.clone();
                a2.extend_from_slice(&[(c, false), (t1, false)]);
                g.extend(self.mz(&a2, top, d));
            }
            for li in active {
                let mut a3: Vec<Lit> = li.clone();
                a3.push((top, true));
                g.extend(self.m(&a3, d));
            }
        } else {
            for li in active {
                let mut a2: Vec<Lit> = li.clone();
                a2.extend_from_slice(&[(c, false), (t1, false)]);
                g.extend(self.m(&a2, d));
            }
        }
        if xh1 != NONE {
            // the known-digit class (code 01): plain_vt's carry-out into top, gated by its code
            g.extend(self.m(&[(d, true), (xh1, false), (c, true)], top));
            g.extend(self.m(&[(d, true), (xh1, false), (c, false), (t1, true)], top));
        }
        g.extend(self.m(&[(d, true), (c, false)], t1));
        if let Some(cg) = cv {
            g.extend_from_slice(cg);
        }
        for i in (0..n).rev() {
            if i < wend && inline.is_some() {
                for li in &inline.unwrap()[&i] {
                    let mut l = vec![(s[i], true), (t[i], true)];
                    l.extend_from_slice(li);
                    g.extend(self.m(&l, c));
                }
            } else if m != NONE && i < wend {
                g.extend(self.m(&[(s[i], true), (t[i], true), (m, true)], c));
            } else {
                g.push(gt(s[i], t[i], c));
            }
            g.push(gc(c, t[i]));
            if i < wend && inline.is_some() {
                for li in &inline.unwrap()[&i] {
                    let mut l = vec![(d, true), (s[i], true)];
                    l.extend_from_slice(li);
                    g.extend(self.m(&l, t[i]));
                }
            } else if m != NONE && i < wend {
                g.extend(self.m(&[(d, true), (s[i], true), (m, true)], t[i]));
            } else {
                g.push(gt(d, s[i], t[i]));
            }
            g.push(gc(c, s[i]));
            if inline.is_none() {
                if let Some(ll) = tog.get(&i) {
                    for l in ll {
                        g.extend(self.m(l, m));
                    }
                }
            }
        }
        if let Some(cg) = cv {
            g.extend(rev(cg));
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain_vt(&self, t: &[u32], s: &[u32], t1: u32, top: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        conj.push(gx(top));
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        g.extend(self.m(&[(d, true), (c, true)], top));
        g.extend(self.m(&[(d, true), (c, false), (t1, true)], top));
        g.extend(self.m(&[(d, true), (c, false)], t1));
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain_v(&self, t: &[u32], s: &[u32], t1: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        conj.push(gx(t1));
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        g.extend(self.m(&[(d, true), (c, false)], t1));
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn plain(&self, t: &[u32], s: &[u32], top: u32, d: u32, c: u32) -> GL {
        let n = t.len();
        let mut conj: GL = t.iter().map(|&q0| gx(q0)).collect();
        if top != NONE {
            conj.push(gx(top));
        }
        let mut g = conj.clone();
        for i in 0..n {
            g.extend_from_slice(&[gc(c, s[i]), gc(c, t[i]), gt(s[i], t[i], c)]);
        }
        if top != NONE {
            g.push(gt(d, c, top));
        }
        for i in (0..n).rev() {
            g.extend_from_slice(&[gt(s[i], t[i], c), gc(c, t[i]), gt(d, s[i], t[i]), gc(c, s[i])]);
        }
        g.extend_from_slice(&conj);
        g
    }
    fn pi_gates(&self, t: i32, cc: u32, f1: u32, f2: u32, f3: u32) -> GL {
        let l = ((t - 1).div_euclid(2)) as usize;
        let x = &self.x;
        let mut y: Vec<u32> = self.y[1..].to_vec();
        y.push(self.y[0]);
        let last = |v: Vec<usize>| -> Vec<usize> {
            let k = v.len().saturating_sub(PIW);
            v[k..].to_vec()
        };
        let mut g = vec![];
        // the top lane of this frame is a known zero (it holds the act flag): only its carry-out matters
        let idx = {
            let v: Vec<usize> = ((W - l)..(W - 1)).collect();
            let k = v.len().saturating_sub(PIW - 1);
            v[k..].to_vec()
        };
        let mut fw = vec![];
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.push(gt(cc, x[W - 1], f1));
        g.extend(rev(&fw));
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.extend_from_slice(&[gc(cc, f2), gc(x[1], f2), gc(y[1], f2)]);
        g.extend(rev(&fw));
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w - 1])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, y[w]), gc(cc, x[w - 1]), gt(y[w], x[w - 1], cc)]);
        }
        g.extend_from_slice(&fw);
        g.push(gt(cc, y[1], f3));
        g.extend(rev(&fw));
        g
    }
    fn flag_e(&self, fl: u32, xt: u32, y: &[u32]) -> GL {
        let h = &self.e;
        let ctl = self.x[0];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        // act shots, hi=0: xt -> 15; not xt, y0=1 -> 13; not xt, y0=0 -> stays 0
        let mut g = self.m(&cat(&[(fl, true), (xt, true)], &self.hl(0)), ctl);
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hl(0)), ctl));
        g.extend_from_slice(&[gc(ctl, h[0]), gc(ctl, h[2]), gc(ctl, h[3])]);
        g.extend(self.m(&[(ctl, true), (xt, true)], h[1]));
        g.extend(self.m(&cat(&[(fl, true), (xt, true), (y[0], true)], &self.hl(15)), ctl));
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hl(13)), ctl));
        g
    }
    /// As m, with z a lane that is clean here: AND of k controls in 2k-3 T.
    fn mz(&self, l0: &[Lit], t: u32, z: u32) -> GL {
        let mut l: Vec<Lit> = Vec::with_capacity(l0.len());
        for &(q0, p) in l0 {
            match l.iter().find(|x| x.0 == q0) {
                Some(x) => {
                    if x.1 != p {
                        return vec![];
                    }
                }
                None => l.push((q0, p)),
            }
        }
        if l.len() < 3 || ZB > 0 {
            return self.m(l0, t);
        }
        let pre: GL = l.iter().filter(|x| !x.1).map(|x| gx(x.0)).collect();
        let cs: Vec<u32> = l.iter().map(|x| x.0).collect();
        let mut g = pre.clone();
        g.extend(cc_core(&cs, t, z));
        g.extend_from_slice(&pre);
        g
    }
    fn hc(&self, c: i32) -> Vec<Lit> {
        vec![(self.e[0], c & 1 == 1), (self.e[1], (c >> 1) & 1 == 1)]
    }
    fn slot(&mut self, t: i32) {
        if t % 2 == 1 {
            self.odd11(t);
        } else {
            self.even11(t);
        }
    }
    fn odd11(&mut self, t: i32) {
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        let yt = y[W - 1];
        let (x0, y0) = (x[0], y[0]);
        let (d, ctl) = (x0, x0);
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let al: Vec<Lit> = cat(&[(yt, true)], &self.hc(0));
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        self.b.t(&[gx(x0)]);
        // a shot at the top with e odd >= 3 waits one slot: code 11
        let g = self.m(&[(yt, true), (h1, true)], h0);
        self.b.t(&g);
        let (l, f) = ((t - 1) / 2, (t + 1) / 2);
        if l >= 1 && f <= N as i32 {
            let actv: Vec<Vec<Lit>> = vec![vec![(yt, true), (h0, false)]];
            for k in 0..2usize {
                let alo = W - l as usize - k;
                let tv: Vec<u32> = (alo..(W - k - 1)).map(|a| x[a]).collect();
                let sv: Vec<u32> = (alo..(W - k - 1)).map(|a| y[a + k]).collect();
                let t1 = x[W - 1 - k];
                let top = if k >= 1 { x[W - k] } else { NONE };
                let g = self.row_v(&tv, &sv, t1, top, d, h1, NONE, &no_tog, &actv, None, None);
                self.b.t(&g);
                let mut g: GL = vec![];
                if k >= 1 {
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(x[W - k], true)]), d));
                    }
                } else {
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(d, true)]), y0));
                    }
                    for li in &actv {
                        g.extend(self.m(&cat(li, &[(y0, true)]), d));
                    }
                }
                self.b.t(&g);
            }
            for k in [1usize, 0] {
                let ahi = W - f as usize - 1 + k;
                let wires: Vec<usize> = (k..=ahi).rev().collect();
                let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
                let sv: Vec<u32> = wires.iter().map(|&a| x[a - k]).collect();
                let nn = tv.len();
                let top = if k >= 1 { y[k - 1] } else { NONE };
                let g = self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, h1, NONE, &no_tog, &actv, None, None);
                let mut hh: GL = vec![];
                if k >= 1 {
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(x[W - k], true)]), d));
                    }
                    hh.push(gc(d, x[W - k]));
                    let xt = x[W - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(y0, true)]), xt));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(xt, true)]), y0));
                    }
                    hh.push(gc(d, top));
                } else {
                    let host = x[W - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(host, true)]), d));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(d, true)]), host));
                    }
                }
                self.b.t(&hh);
                self.b.t(&rev(&g));
            }
        }
        let g = self.m(&cat(&al, &[(y[0], false)]), ctl);
        self.b.t(&g);
        let g = rotate_up(ctl, &y, W - 1);
        self.b.t(&g);
        let g = self.m(&al, ctl);
        self.b.t(&g);
        let mut g = vec![];
        for w in 1..W {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        let xt = x[W - 1];
        self.b.t(&[gc(ctl, y[W - 1])]);
        let g = self.m(&al, ctl);
        self.b.t(&g);
        let fl = y[W - 1];
        let aa = cat(&[(fl, true)], &self.hc(0));
        let win: Vec<u32> = y[..W - 1].to_vec();
        let g = self.m(&cat(&aa, &[(xt, false), (y[W - 2], false)]), ctl);
        self.b.t(&g);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        let g = self.m(&cat(&aa, &[(xt, false), (y[0], false)]), ctl);
        self.b.t(&g);
        // acted: E'=0 and the second state take code 01 (the common rise gives 00); E'=2 stays 00 (the rise gives 10 and a marker)
        let mut g = self.m(&cat(&[(fl, true), (xt, true)], &self.hc(0)), ctl);
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hc(0)), ctl));
        g.push(gc(ctl, h0));
        g.extend(self.m(&cat(&[(fl, true), (xt, true), (y[0], true)], &self.hc(1)), ctl));
        g.extend(self.m(&cat(&[(fl, true), (xt, false), (y[0], true)], &self.hc(1)), ctl));
        self.b.t(&g);
        let mut g = self.m(&cat(&[(xt, true), (y[0], true)], &self.hc(1)), fl);
        g.extend(self.m(&cat(&[(xt, false), (y[0], false), (y[1], true)], &self.hc(0)), fl));
        g.extend(self.m(&cat(&[(y[W - 2], true), (xt, false), (y[0], true)], &self.hc(1)), fl));
        self.b.t(&g);
        self.b.t(&[gx(y[W - 1]), gc(y[W - 1], ctl), gx(y[W - 1])]);
        // one slot of rise for every shot not at the top
        let mut g = self.m(&cat(&[(ctl, true)], &self.hc(0)), y[0]);
        g.extend(self.m(&[(ctl, true), (y[0], true), (h0, false)], h1));
        g.extend(self.m(&[(ctl, true), (h1, false)], h0));
        g.extend(self.m(&[(ctl, true), (h0, true), (xt, true), (y[W - 3], true)], h1));
        g.extend(self.m(&[(ctl, true), (h0, true), (xt, false), (y[W - 4], true)], h1));
        g.extend(self.m(&cat(&[(ctl, true), (xt, true)], &self.hc(1)), y[W - 3]));
        g.extend(self.m(&cat(&[(ctl, true), (xt, false)], &self.hc(1)), y[W - 4]));
        self.b.t(&g);
        let g = rotate_up(ctl, &y, 1);
        self.b.t(&g);
        let yt2 = y[W - 1];
        let mut g = vec![gx(ctl)];
        g.extend(self.m(&cat(&[(yt2, true)], &self.hc(3)), ctl));
        g.extend(self.m(&cat(&[(yt2, true)], &self.hc(1)), ctl));
        self.b.t(&g);
        self.arrive11(t - 1, &y, ctl);
        // the second state acts at the next even slot
        let g = self.m(&[(yt2, true), (xt, false), (y[0], false), (y[1], true), (h1, false)], h0);
        self.b.t(&g);
        self.b.t(&[gx(ctl)]);
    }
    fn even11(&mut self, t: i32) {
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        let prs: Vec<i32> = pairs(t).into_iter().filter(|&e| e <= 9).collect();
        let big: Vec<i32> = prs.iter().cloned().filter(|&e| e >= 2).collect();
        let kk = 1 + big.iter().cloned().max().unwrap_or(0);
        let yt = y[W - 1];
        let (x0, y0, y1) = (x[0], y[0], y[1]);
        let (d, ctl) = (x0, x0);
        let cl: Vec<Lit> = vec![(yt, true), (h1, true)];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let no_tog: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
        self.b.t(&[gx(x0)]);
        let mut g: GL = vec![];
        for &e in &big {
            if e & 1 == 1 {
                let mut l = cl.clone();
                for j in 1..(e as usize - 1) {
                    l.push((y[j], false));
                }
                l.push((y[e as usize - 1], true));
                g.extend(self.m(&l, h0));
            }
        }
        self.b.t(&g);
        let sp0: Vec<Lit> = cat(&[(yt, true)], &self.hc(0));
        let sp1: Vec<Lit> = cat(&cat(&[(yt, true)], &self.hc(1)), &[(y1, true)]);
        let sp1c: Vec<Lit> = cat(&cat(&[(yt, true)], &self.hc(1)), &[(x[W - 1], false), (x[W - 2], false)]);
        let merge0 = prs.contains(&0) && !big.is_empty();
        let merge1 = ZB > 0 && prs.contains(&1) && !big.is_empty();
        if prs.contains(&0) && !merge0 {
            let (l, _f) = lf(t, 0);
            let lu = l as usize;
            let c1 = self.m(&sp0, d);
            self.b.t(&c1);
            let tv: Vec<u32> = ((W - lu)..(W - 1)).map(|a| x[a]).collect();
            let sv: Vec<u32> = ((W - lu)..(W - 1)).map(|a| y[a]).collect();
            let g = self.plain_v(&tv, &sv, x[W - 1], d, h0);
            self.b.t(&g);
            self.b.t(&c1);
        }
        if prs.contains(&1) && !merge1 {
            let (l, _f) = lf(t, 1);
            let lu = l as usize;
            let c1 = self.m(&sp1, d);
            self.b.t(&c1);
            let tv: Vec<u32> = ((W - lu - 1)..(W - 2)).map(|a| x[a]).collect();
            let sv: Vec<u32> = ((W - lu - 1)..(W - 2)).map(|a| y[a + 1]).collect();
            let g = self.plain_v(&tv, &sv, x[W - 2], d, h1);
            self.b.t(&g);
            self.b.t(&c1);
        }
        let lik = |k: i32| -> Vec<Lit> {
            let mut l = cl.clone();
            if k >= 3 {
                for j in 1..(k as usize - 1) {
                    l.push((y[j], false));
                }
            }
            l
        };
        for k in 0..kk {
            let act: Vec<i32> = big.iter().cloned().filter(|&e| e >= k).collect();
            if act.is_empty() {
                continue;
            }
            let starts: Vec<(i32, i32)> = act.iter().map(|&e| (e, W as i32 - lf(t, e).0 - k)).collect();
            let m0 = merge0 && k == 0;
            let m1 = merge1 && k == 1;
            let alo1 = starts.iter().map(|p| p.1).min().unwrap();
            let shi = starts.iter().map(|p| p.1).max().unwrap();
            let alo = if m0 { (W as i32) - t / 2 } else if m1 { (W as i32) - t / 2 - 1 } else { alo1 };
            assert!(!(m0 || m1) || alo < alo1);
            let (ku, alo_u) = (k as usize, alo as usize);
            let tv: Vec<u32> = (alo_u..(W - ku - 1)).map(|a| x[a]).collect();
            let sv: Vec<u32> = (alo_u..(W - ku - 1)).map(|a| y[a + ku]).collect();
            let t1 = x[W - 1 - ku];
            let top = if k >= 1 { x[W - ku] } else { NONE };
            let li = lik(k);
            let actv: Vec<Vec<Lit>> = vec![li];
            let mn = *act.iter().min().unwrap();
            let mut il: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for i in 0..(shi - alo + 1) {
                let a = alo + i;
                let nx = starts.iter().filter(|p| p.1 > a).map(|p| p.0).min();
                let e: Vec<Vec<Lit>> = if (m0 || m1) && a < alo1 {
                    vec![vec![], vec![(h1, true)]]
                } else {
                    match nx {
                        None => vec![vec![]],
                        Some(n) => {
                            let lo = (mn - 1).max(1) as usize;
                            let mut ch: Vec<Lit> = vec![];
                            if m0 || m1 {
                                ch.push((h1, true));
                            }
                            ch.extend((lo..(n as usize - 1)).map(|j| (y[j], false)));
                            vec![vec![], ch]
                        }
                    }
                };
                il.insert(i as usize, e);
            }
            let g = self.row_vz(&tv, &sv, t1, top, d, h0, NONE, &no_tog, &actv, Some(&il), None, m0 || m1);
            let c1 = if m0 { self.m(&sp0, d) } else if m1 { [self.m(&sp1, d), self.m(&[(d, true), (h1, false)], h0)].concat() } else { vec![] };
            self.b.t(&c1);
            self.b.t(&g);
            let mut g: GL = vec![];
            if k >= 1 {
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(x[W - ku], true)]), d));
                }
            } else {
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(d, true)]), y0));
                }
                for l_ in &actv {
                    g.extend(self.m(&cat(l_, &[(y0, true)]), d));
                }
            }
            self.b.t(&g);
            self.b.t(&if m1 { rev(&c1) } else { c1.clone() });
        }
        for k in (0..kk).rev() {
            let act: Vec<i32> = big.iter().cloned().filter(|&e| e >= k).collect();
            if act.is_empty() {
                continue;
            }
            let ku = k as usize;
            let li = lik(k);
            let actv: Vec<Vec<Lit>> = vec![li.clone()];
            let flag = k >= 2 && big.contains(&k);
            if flag {
                let mut g = self.m(&cat(&li, &[(y[ku - 1], true)]), h0);
                g.extend(self.m(&cat(&li, &[(h0, true)]), y[ku - 1]));
                self.b.t(&g);
            }
            let starts: Vec<(i32, i32)> = act.iter().map(|&e| (e, W as i32 - lf(t, e).1 - 1 + k)).collect();
            let m0 = merge0 && k == 0;
            let m1 = merge1 && k == 1;
            let ahi1 = starts.iter().map(|p| p.1).max().unwrap();
            let slo = starts.iter().map(|p| p.1).min().unwrap();
            let ahi = if m0 { (W as i32) - t / 2 - 1 } else { ahi1 };
            assert!(!m0 || ahi > ahi1);
            let wires: Vec<usize> = (ku..=(ahi as usize)).rev().collect();
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
            let nn = tv.len();
            let top = if k >= 1 { y[ku - 1] } else { NONE };
            let c = if k >= 2 { x[W - ku] } else { h0 };
            let mut il: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for i in 0..(ahi - slo + 1) {
                let a = ahi - i;
                let nx = starts.iter().filter(|p| p.1 < a).map(|p| p.0).min();
                let e: Vec<Vec<Lit>> = if m0 && a > ahi1 {
                    vec![vec![], vec![(h1, true)]]
                } else {
                    match nx {
                        None => vec![vec![]],
                        Some(n) => {
                            let jlo = (k + 1).max(2);
                            let mut ch: Vec<Lit> = vec![];
                            if m0 || m1 {
                                ch.push((h1, true));
                            }
                            if k >= 2 {
                                ch.push((h0, false));
                            }
                            for j in jlo..n {
                                ch.push((x[W - j as usize], false));
                            }
                            vec![vec![], ch]
                        }
                    }
                };
                il.insert(i as usize, e);
            }
            let g = self.row_vzx(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, c, NONE, &no_tog, &actv, Some(&il), None, m0 || m1, if m1 { h1 } else { NONE });
            let c1 = if m0 { self.m(&sp0, d) } else if m1 { [self.m(&sp1c, d), self.m(&[(d, true), (h1, false)], h0)].concat() } else { vec![] };
            let mut hh: GL = vec![];
            if k >= 1 {
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(x[W - ku], true)]), d));
                }
                hh.push(gc(d, x[W - ku]));
                if k == 1 {
                    let xt = x[W - 1];
                    for l_ in &actv {
                        hh.extend(self.m(&cat(l_, &[(y0, true)]), xt));
                    }
                    for l_ in &actv {
                        hh.extend(self.m(&cat(l_, &[(xt, true)]), y0));
                    }
                }
                hh.push(gc(d, top));
            } else {
                let host = x[W - 1];
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(host, true)]), d));
                }
                for l_ in &actv {
                    hh.extend(self.m(&cat(l_, &[(d, true)]), host));
                }
            }
            self.b.t(&hh);
            self.b.t(&c1);
            self.b.t(&rev(&g));
            self.b.t(&if m1 { rev(&c1) } else { c1.clone() });
            if flag {
                let mut g = self.m(&cat(&li, &[(h0, true)]), x[W - ku]);
                g.extend(self.m(&cat(&li, &[(x[W - ku], true)]), h0));
                self.b.t(&g);
            }
        }
        if prs.contains(&0) && !merge0 {
            let (_l, f) = lf(t, 0);
            let mb = W - f as usize;
            let wires: Vec<usize> = (0..mb).rev().collect();
            let c1 = self.m(&sp0, d);
            self.b.t(&c1);
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a]).collect();
            let nn = tv.len();
            let g = self.plain_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], d, x[W - 1]);
            self.b.t(&rev(&g));
            self.b.t(&c1);
        }
        if prs.contains(&1) && !merge1 {
            let (_l, f) = lf(t, 1);
            let mb = W - f as usize;
            let wires: Vec<usize> = (1..=mb).rev().collect();
            let c1 = self.m(&sp1c, d);
            self.b.t(&c1);
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - 1]).collect();
            let nn = tv.len();
            let g = self.plain_vt(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], y[0], d, x[W - 1]);
            self.b.t(&rev(&g));
            self.b.t(&c1);
        }
        // waiters step aside: a down-rotation now, the relabel below undoes it
        let hold1: Vec<Lit> = cat(&[(yt, true)], &self.hc(1));
        let mut g = self.m(&cat(&hold1, &[(x[W - 1], true)]), ctl);
        g.extend(self.m(&cat(&hold1, &[(x[W - 1], false), (x[W - 2], true)]), ctl));
        self.b.t(&g);
        let g = rotate_up(ctl, &y, W - 1);
        self.b.t(&g);
        let g = self.m(&cat(&[(y[W - 1], false), (y[W - 2], true)], &self.hc(1)), ctl);
        self.b.t(&g);
        // post
        let g = self.m(&[(yt, true), (y[0], false)], ctl);
        self.b.t(&g);
        let g = rotate_up(ctl, &y, W - 1);
        self.b.t(&g);
        self.b.t(&[gc(y[W - 1], ctl)]);
        let mut g = vec![];
        for w in 1..W {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        let xt = x[W - 1];
        self.b.t(&[gc(ctl, y[W - 1])]);
        self.b.t(&[gc(y[W - 1], ctl)]);
        let mut ny = vec![y[W - 1]];
        ny.extend_from_slice(&y[..W - 1]);
        self.y = ny.clone();
        let y = ny;
        let mut d2 = self.pas.clone();
        d2.extend_from_slice(&self.x);
        d2.extend_from_slice(&y);
        self.dirty = d2;
        let act = y[0];
        let win: Vec<u32> = y[1..].to_vec();
        // parity: rotate the new N by r. The marker sits at W-e+1, everything above it is zero.
        let mut g = self.m(&cat(&[(act, true)], &self.hc(1)), ctl);
        for &e in &big {
            if e & 1 == 1 {
                let eu = e as usize;
                let mut l = cat(&[(act, true)], &self.hc(2));
                for i in 0..(eu - 2) {
                    l.push((y[W - 1 - i], false));
                }
                l.push((y[W - eu + 1], true));
                g.extend(self.m(&l, ctl));
            }
        }
        self.b.t(&g);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        let g = self.m(&[(act, true), (y[1], false)], ctl);
        self.b.t(&g);
        // final codes; the marker of a shot that stays in 11 is already in place
        let aa: Vec<Lit> = vec![(act, true)];
        let mut g = self.m(&cat(&aa, &[(h1, false), (y[1], false)]), h0);
        g.extend(self.m(&cat(&aa, &[(h1, true), (y[W - 1], true)]), h0));
        g.extend(self.m(&cat(&aa, &self.hc(3)), y[W - 1]));
        g.extend(self.m(&cat(&aa, &[(h0, true)]), h1));
        g.extend(self.m(&cat(&aa, &[(h1, false), (xt, false)]), h0));
        g.extend(self.m(&cat(&aa, &[(h1, true), (xt, false), (y[W - 3], true)]), h0));
        g.extend(self.m(&cat(&cat(&aa, &self.hc(3)), &[(xt, false)]), y[W - 3]));
        g.extend(self.m(&cat(&aa, &[(h0, true), (xt, false)]), h1));
        g.extend(self.m(&cat(&aa, &[(h1, true)]), h0));
        self.b.t(&g);
        let g1 = self.m(&[(act, true), (xt, false)], ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        let mut g = self.m(&[(xt, true), (y[1], true)], act);
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], true), (h1, false)], act));
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], true), (h1, true), (h0, true)], act));
        g.extend(self.m(&[(xt, true), (y[1], false), (y[2], true), (h0, true)], act));
        g.extend(self.m(&[(xt, false), (y[1], false), (y[2], false), (y[3], true)], act));
        self.b.t(&g);
        if t + 1 <= 2 * N as i32 {
            let tau = ctl;
            let gl = cat(&[(xt, true), (y[1], false), (y[2], true)], &self.hc(0));
            let tg = self.m(&gl, tau);
            self.b.t(&tg);
            let p0 = self.pas[0];
            let (p12, p3) = self.pi10(t + 1, h1, h0, y[1], p0);
            self.b.t(&p12);
            let q = self.m(&[(tau, true), (h0, false), (y[1], true), (p0, true)], act);
            self.b.t(&q);
            self.b.t(&p3);
            self.b.t(&q);
            self.b.t(&rev(&p3));
            self.b.t(&rev(&p12));
            self.b.t(&tg);
        }
        if t % 8 == 0 && !self.big_pairs11(t).is_empty() {
            self.big_phase(t);
        }
        self.arrive11(t - 1, &y, ctl);
        self.b.t(&[gx(ctl)]);
    }
    fn big_pairs11(&self, t: i32) -> Vec<(i32, i32, i32, i32)> {
        let mut out = vec![];
        for w in 0..8 {
            for e in 10..=ECAP {
                if (e - w).rem_euclid(2) != 0 {
                    continue;
                }
                let (u, v) = ((e - w) / 2, (e + w) / 2);
                let (l, f) = (t / 2 - u, t / 2 + v);
                if l >= 1 && f <= N as i32 && f >= l {
                    out.push((e, w, u, v));
                }
            }
        }
        out
    }
    /// A shot that has just reached the top with e >= 10 takes code 01 and w = tn mod 8. ctl is clean.
    fn arrive11(&mut self, tn: i32, y: &[u32], ctl: u32) {
        let (h0, h1) = (self.e[0], self.e[1]);
        let w = tn.rem_euclid(8);
        let yt2 = y[W - 1];
        let mut l: Vec<Lit> = vec![(yt2, true)];
        l.extend(self.hc(2));
        for j in 1..9 {
            l.push((y[j], false));
        }
        let mut g = self.m(&l, ctl);
        g.push(gc(ctl, h0));
        g.push(gc(ctl, h1));
        for i in 0..3 {
            if (w >> i) & 1 == 1 {
                g.push(gc(ctl, y[4 + i]));
            }
        }
        let mut l: Vec<Lit> = vec![(yt2, true)];
        l.extend(self.hc(1));
        l.push((y[1], false));
        for i in 0..3 {
            l.push((y[4 + i], (w >> i) & 1 == 1));
        }
        g.extend(self.m(&l, ctl));
        self.b.t(&g);
    }
    /// Rows, marker and post of the waiting big shots (code 01) at a tier slot, after the slot's own low work.
    fn big_phase(&mut self, t: i32) {
        let (x, y, h) = (self.x.clone(), self.y.clone(), self.e.clone());
        let (h0, h1) = (h[0], h[1]);
        let prs = self.big_pairs11(t);
        let es: BTreeSet<i32> = prs.iter().map(|p| p.0).collect();
        let kk = *es.iter().next_back().unwrap() + 1;
        let yt = y[W - 1];
        let (d, ctl) = (x[0], x[0]);
        let (y0, y1) = (y[0], y[1]);
        let (w0, w1, w2) = (y[4], y[5], y[6]);
        let hb0: Vec<u32> = vec![y[2], y[3], y[7], y[8]];
        let cv9 = y[9];
        let cat = |p: &[Lit], q0: &[Lit]| -> Vec<Lit> { [p, q0].concat() };
        let g = self.m(&[(yt, true), (h0, true)], h1);
        self.b.t(&g);
        let cl: Vec<Lit> = cat(&[(yt, true)], &self.hc(3));
        let mut g: GL = vec![];
        for &e in &es {
            let mut li = cl.clone();
            for j in 9..(e as usize - 1) {
                li.push((y[j], false));
            }
            li.push((y[e as usize - 1], true));
            let m = e >> 1;
            for i in 0..4 {
                if (m >> i) & 1 == 1 {
                    g.extend(self.m(&li, hb0[i]));
                }
            }
        }
        for &e in &es {
            let mut li = cl.clone();
            for i in 0..4 {
                li.push((hb0[i], ((e >> 1) >> i) & 1 == 1));
            }
            li.push((w0, e & 1 == 1));
            g.extend(self.m(&li, y[e as usize - 1]));
        }
        self.b.t(&g);
        let lits = |cubes: &Cubes, lanes: &[u32]| -> Vec<Vec<Lit>> { cubes.iter().map(|x_| x_.iter().map(|&(v, bt)| (lanes[v], bt == 1)).collect()).collect() };
        let exact = |k: i32, lanes: &[u32]| -> Vec<Vec<Lit>> {
            let (mut on, mut off) = (0u128, 0u128);
            for &e in &es {
                let p_ = (e >> 1) | ((e & 1) << 4);
                if e >= k {
                    on |= 1u128 << p_;
                } else {
                    off |= 1u128 << p_;
                }
            }
            lits(&dtree(on, off, &[0, 1, 2, 3, 4], 1), lanes).into_iter().map(|x_| cat(&x_, &cl)).collect()
        };
        let hterm = |vals: &BTreeSet<i32>, others: &BTreeSet<i32>, lanes: &[u32]| -> Vec<Vec<Lit>> {
            let (mut on, mut off) = (0u128, 0u128);
            for &x_ in vals {
                on |= 1u128 << (x_ % 16);
            }
            for &x_ in others {
                off |= 1u128 << (x_ % 16);
            }
            lits(&dtree(on, off, &[0, 1, 2, 3], 0), lanes)
        };
        let mut cv_v = dec_ctl(&hb0, &[(w1, true)], &self.dirty);
        cv_v.extend(dec_ctl(&hb0[1..], &[(w2, true)], &self.dirty));
        for k in 0..kk {
            let act: Vec<(i32, i32, i32, i32)> = prs.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() {
                continue;
            }
            let mut starts: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
            for &(_e, _w, u, _v) in &act {
                starts.entry(W as i32 - (t / 2 - u) - k).or_default().insert(u);
            }
            let alo = *starts.keys().next().unwrap();
            assert!(alo + k >= 10);
            let (ku, alo_u) = (k as usize, alo as usize);
            let tv: Vec<u32> = (alo_u..(W - ku - 1)).map(|a| x[a]).collect();
            let sv: Vec<u32> = (alo_u..(W - ku - 1)).map(|a| y[a + ku]).collect();
            let t1 = x[W - 1 - ku];
            let top = if k >= 1 { x[W - ku] } else { NONE };
            let actv = exact(k, &[hb0[0], hb0[1], hb0[2], hb0[3], w0]);
            let allu: BTreeSet<i32> = act.iter().map(|p| p.2).collect();
            let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for (&a, us) in &starts {
                let rest: BTreeSet<i32> = allu.difference(us).cloned().collect();
                tg.insert((a - alo) as usize, hterm(us, &rest, &hb0));
            }
            let g = self.row_v(&tv, &sv, t1, top, d, cv9, y1, &tg, &actv, None, Some(&cv_v));
            self.b.t(&g);
            let mut g: GL = vec![];
            if k >= 1 {
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(x[W - ku], true)]), d));
                }
            } else {
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(d, true)]), y0));
                }
                for li in &actv {
                    g.extend(self.m(&cat(li, &[(y0, true)]), d));
                }
            }
            self.b.t(&g);
        }
        let mv = |me: &Machine, src: u32, dst: u32| -> GL {
            let mut g = me.m(&cat(&cl, &[(src, true)]), dst);
            g.extend(me.m(&cat(&cl, &[(dst, true)]), src));
            g
        };
        let mut hb = hb0.clone();
        let (mut a0, mut a1, mut a2) = (w0, w1, w2);
        for k in (0..kk).rev() {
            let act: Vec<(i32, i32, i32, i32)> = prs.iter().cloned().filter(|p| p.0 >= k).collect();
            if act.is_empty() {
                continue;
            }
            let ku = k as usize;
            if k == 9 {
                let g = mv(self, hb[3], x[W - 10]);
                self.b.t(&g);
                hb[3] = x[W - 10];
            }
            if k == 8 {
                let g = mv(self, hb[2], x[W - 9]);
                self.b.t(&g);
                hb[2] = x[W - 9];
            }
            if k == 7 {
                let g = mv(self, a2, x[W - 8]);
                self.b.t(&g);
                a2 = x[W - 8];
            }
            if k == 6 {
                let g = mv(self, a1, x[W - 7]);
                self.b.t(&g);
                a1 = x[W - 7];
            }
            if k == 5 {
                let g = mv(self, a0, x[W - 6]);
                self.b.t(&g);
                a0 = x[W - 6];
            }
            if k == 4 {
                let g = mv(self, hb[1], x[W - 5]);
                self.b.t(&g);
                hb[1] = x[W - 5];
            }
            if k == 3 {
                let g = mv(self, hb[0], x[W - 4]);
                self.b.t(&g);
                hb[0] = x[W - 4];
            }
            let mut cv_c = inc_ctl(&hb, &[(a0, true)], &self.dirty);
            cv_c.extend(inc_ctl(&hb, &[(a1, true)], &self.dirty));
            cv_c.extend(inc_ctl(&hb[1..], &[(a2, true)], &self.dirty));
            let mut starts: BTreeMap<i32, BTreeSet<i32>> = BTreeMap::new();
            for &(_e, _w, _u, v) in &act {
                starts.entry(W as i32 - (t / 2 + v) - 1 + k).or_default().insert(v);
            }
            let ahi = *starts.keys().next_back().unwrap();
            let wires: Vec<usize> = (ku..=(ahi as usize)).rev().collect();
            let tv: Vec<u32> = wires.iter().map(|&a| y[a]).collect();
            let sv: Vec<u32> = wires.iter().map(|&a| x[a - ku]).collect();
            let nn = tv.len();
            let top = if k >= 1 { y[ku - 1] } else { NONE };
            let cc = if k >= 2 {
                x[W - ku]
            } else if k == 1 {
                x[W - 2]
            } else {
                x[W - 1]
            };
            let mask = if k >= 3 { y1 } else { x[W - 3] };
            let actv = exact(k, &[hb[0], hb[1], hb[2], hb[3], a0]);
            let allv: BTreeSet<i32> = act.iter().map(|p| p.3).collect();
            let mut tg: BTreeMap<usize, Vec<Vec<Lit>>> = BTreeMap::new();
            for (&a, vs) in &starts {
                let rest: BTreeSet<i32> = allv.difference(vs).cloned().collect();
                tg.insert((ahi - a) as usize, hterm(vs, &rest, &hb));
            }
            let g = self.row_v(&tv[..nn - 1], &sv[..nn - 1], tv[nn - 1], top, d, cc, mask, &tg, &actv, None, Some(&cv_c));
            let mut hh: GL = vec![];
            if k >= 1 {
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(x[W - ku], true)]), d));
                }
                hh.push(gc(d, x[W - ku]));
                if k == 1 {
                    let xt = x[W - 1];
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(y0, true)]), xt));
                    }
                    for li in &actv {
                        hh.extend(self.m(&cat(li, &[(xt, true)]), y0));
                    }
                }
                hh.push(gc(d, top));
            } else {
                let host = x[W - 1];
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(host, true)]), d));
                }
                for li in &actv {
                    hh.extend(self.m(&cat(li, &[(d, true)]), host));
                }
            }
            self.b.t(&hh);
            self.b.t(&rev(&g));
        }
        // hi -> marker on X[W-e], largest e first
        let mut g: GL = vec![];
        for &e in es.iter().rev() {
            let m = e >> 1;
            let mk = x[W - e as usize];
            let mut li = cl.clone();
            for i in 0..4 {
                li.push((hb[i], (m >> i) & 1 == 1));
            }
            li.push((a0, e & 1 == 1));
            g.extend(self.m(&li, ctl));
            for i in 0..4 {
                if (m >> i) & 1 == 1 {
                    g.push(gc(ctl, hb[i]));
                }
            }
            g.push(gc(ctl, mk));
            let mut li = cl.clone();
            for i in 0..4 {
                if hb[i] != mk {
                    li.push((hb[i], false));
                }
            }
            li.push((mk, true));
            g.extend(self.m(&li, ctl));
        }
        self.b.t(&g);
        let g = mv(self, a0, x[W - 2]);
        self.b.t(&g);
        let g = mv(self, a1, x[W - 3]);
        self.b.t(&g);
        let g = mv(self, a2, x[W - 4]);
        self.b.t(&g);
        // its own post
        let g = self.m(&cat(&cl, &[(y[0], false)]), ctl);
        self.b.t(&g);
        let g = rotate_up(ctl, &y, W - 1);
        self.b.t(&g);
        let g = self.m(&cl, ctl);
        self.b.t(&g);
        let mut g = vec![];
        for w in 1..W {
            cswap(ctl, x[w], y[w], &mut g);
        }
        g.push(gc(ctl, self.par));
        self.b.t(&g);
        let xt = x[W - 1];
        self.b.t(&[gc(ctl, y[W - 1])]);
        let g = self.m(&cl, ctl);
        self.b.t(&g);
        let fl = y[W - 1];
        let aa: Vec<Lit> = cat(&[(fl, true)], &self.hc(3));
        for &(idx, rot) in &[(W - 4, 4usize), (W - 3, 2), (W - 2, 1)] {
            let mut g = self.m(&cat(&aa, &[(y[idx], true)]), ctl);
            g.extend(self.m(&cat(&aa, &[(ctl, true)]), y[idx]));
            self.b.t(&g);
            let g = rotate_up(ctl, &y[0..=idx], rot);
            self.b.t(&g);
            let mut g: GL = vec![];
            if rot == 4 {
                g.extend(self.m(&cat(&aa, &[(y[0], false)]), ctl));
            } else if rot == 2 {
                g.extend(self.m(&cat(&aa, &[(y[0], false), (y[2], true)]), ctl));
                g.extend(self.m(&cat(&aa, &[(y[0], false), (y[2], false), (y[4], false)]), ctl));
            } else {
                for &p_ in &[1usize, 3, 5, 7] {
                    let mut l = aa.clone();
                    for i in 0..p_ {
                        l.push((y[i], false));
                    }
                    l.push((y[p_], true));
                    g.extend(self.m(&l, ctl));
                }
            }
            self.b.t(&g);
        }
        // u=2, g=1 ends with E'=-1: no marker, code 01
        let fc1 = cat(&[(fl, true), (xt, false)], &self.hc(1));
        let mut g = self.m(&cat(&aa, &[(xt, false), (y[W - 4], true)]), ctl);
        g.push(gc(ctl, h1));
        g.extend(self.m(&fc1, ctl));
        self.b.t(&g);
        let g = self.m(&fc1, y[W - 4]);
        self.b.t(&g);
        let ab: Vec<Lit> = vec![(fl, true), (h0, true)];
        let win: Vec<u32> = y[..W - 1].to_vec();
        let g1 = self.m(&cat(&ab, &[(xt, false)]), ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        let g1 = self.m(&ab, ctl);
        self.b.t(&g1);
        let g = rot1(ctl, &win);
        self.b.t(&g);
        self.b.t(&g1);
        // erase the act flag
        let mut g: GL = vec![];
        for gg in 0..2usize {
            for w in 0..8i32 {
                let sub: Vec<&(i32, i32, i32, i32)> = prs.iter().filter(|p| p.1 == w).collect();
                if sub.is_empty() {
                    continue;
                }
                let gq = 1 + gg + w as usize;
                let mut li: Vec<Lit> = vec![(xt, gg == 0)];
                for i in 0..gq {
                    li.push((y[i], false));
                }
                li.push((y[gq], true));
                if sub.iter().any(|p| !(gg == 1 && p.2 == 2)) {
                    let mut l = cat(&li, &self.hc(3));
                    for j in (W + gq - 9)..(W - 1) {
                        l.push((y[j], false));
                    }
                    g.extend(self.m(&l, fl));
                }
                if sub.iter().any(|p| gg == 1 && p.2 == 2) {
                    g.extend(self.m(&cat(&li, &self.hc(1)), fl));
                }
            }
        }
        self.b.t(&g);
    }
    fn pi10(&self, t: i32, cc: u32, f1: u32, f2: u32, f3: u32) -> (GL, GL) {
        let l = ((t - 1).div_euclid(2)) as usize;
        let x = &self.x;
        let mut y: Vec<u32> = self.y[1..].to_vec();
        y.push(self.y[0]);
        let last = |v: Vec<usize>| -> Vec<usize> {
            let k = v.len().saturating_sub(PIW);
            v[k..].to_vec()
        };
        let mut g = vec![];
        // the top lane of this frame is a known zero (it holds the act bit): only its carry-out matters
        let idx = {
            let v: Vec<usize> = ((W - l)..(W - 1)).collect();
            let k = v.len().saturating_sub(PIW - 1);
            v[k..].to_vec()
        };
        let mut fw = vec![];
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.push(gt(cc, x[W - 1], f1));
        g.extend(rev(&fw));
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, x[w]), gc(cc, y[w]), gt(x[w], y[w], cc)]);
        }
        g.extend_from_slice(&fw);
        g.extend_from_slice(&[gc(cc, f2), gc(x[1], f2), gc(y[1], f2)]);
        g.extend(rev(&fw));
        let idx = last((2..(W - l)).rev().collect());
        let mut fw: GL = idx.iter().map(|&w| gx(x[w - 1])).collect();
        for &w in &idx {
            fw.extend_from_slice(&[gc(cc, y[w]), gc(cc, x[w - 1]), gt(y[w], x[w - 1], cc)]);
        }
        let mut h = fw.clone();
        h.push(gt(cc, y[1], f3));
        h.extend(rev(&fw));
        (g, h)
    }
}

/// F on virtual lanes: 0..255 x, 256..511 borrowed passenger, 512.. the rest.
struct FCirc {
    gates: Vec<G>,
    next: u32,
    y0: u32,
    y1: u32,
    par: u32,
    xtop: u32,
    ar: Vec<u32>,
    last: GL,
}
fn f_circuit() -> FCirc {
    IN_F.store(true, Ordering::Relaxed);
    let mut b = B { free: vec![], next: 512, gates: Vec::with_capacity(48_000_000) };
    for _ in 0..ZB {
        b.alloc();
    }
    let xl: Vec<u32> = (0..256).collect();
    let pas: Vec<u32> = (256..512).collect();
    let y0 = b.alloc();
    let par = xl[N - 1];
    let y1 = b.alloc();
    let mut y = vec![y0, y1];
    y.extend_from_slice(&xl[..N - 1]);
    let x: Vec<u32> = (0..W).map(|_| b.alloc()).collect();
    let e: Vec<u32> = (0..EB).map(|_| b.alloc()).collect();
    let mut dirty = pas.clone();
    dirty.extend_from_slice(&x);
    dirty.extend_from_slice(&y);
    let mut mc = Machine { b, dirty, pas, x, y, e, par };
    mc.init();
    for t in (3..=(2 * N as i32 - 1)).rev() {
        mc.slot(t);
    }
    IN_F.store(false, Ordering::Relaxed);
    let mut last: GL = vec![gx(mc.x[W - 1])];
    for i in 0..N {
        if pbit(i) {
            last.push(gx(mc.x[W - 2 - i]));
        }
    }
    FCirc {
        gates: mc.b.gates,
        next: mc.b.next,
        y0,
        y1,
        par,
        xtop: mc.y[W - 1],
        ar: (0..N).map(|i| mc.y[W - 2 - i]).collect(),
        last,
    }
}

/// physical emitter
struct P {
    ops: Vec<Op>,
    free: Vec<u32>,
    next: u32,
    bits: u64,
    /// hmr-and: 1 while the lane holds a cc_core AND (compute emitted, measured uncompute pending)
    hold: Vec<u8>,
}
const fn q(i: u32) -> QubitId {
    QubitId(i as u64)
}
impl P {
    fn alloc(&mut self) -> u32 {
        if let Some(a) = self.free.pop() {
            a
        } else {
            self.next += 1;
            self.next - 1
        }
    }
    fn allocn(&mut self, k: usize) -> Vec<u32> {
        (0..k).map(|_| self.alloc()).collect()
    }
    fn rel(&mut self, a: u32) {
        assert!((a as usize) >= self.hold.len() || self.hold[a as usize] == 0, "hmr-and: lane released while holding an AND");
        self.free.push(a);
        self.free.sort_by(|x, y| y.cmp(x));
    }
    #[inline]
    fn gate(&mut self, g: G) {
        let mut o = Op::empty();
        if g.2 != NONE {
            let flagged = HMR_AND && (g.2 & AND_FLAG) != 0;
            let tgt = if HMR_AND { g.2 & !AND_FLAG } else { g.2 };
            if flagged {
                let t = tgt as usize;
                if self.hold.len() <= t {
                    self.hold.resize(t + 1, 0);
                }
                if self.hold[t] == 1 {
                    // measured uncompute: Hmr on the AND lane, CZ(c0, c1) under the outcome (exact: phase ^= rng & (z ^ c0c1) = 0)
                    self.hold[t] = 0;
                    let bit = self.hmr(tgt);
                    if !HMR_NEGCTL {
                        self.czc(g.0, g.1, bit);
                    }
                    return;
                }
                self.hold[t] = 1;
            }
            o.kind = OperationType::CCX;
            o.q_control1 = q(g.0);
            o.q_control2 = q(g.1);
            o.q_target = q(tgt);
        } else if g.1 != NONE {
            o.kind = OperationType::CX;
            o.q_control1 = q(g.0);
            o.q_target = q(g.1);
        } else {
            o.kind = OperationType::X;
            o.q_target = q(g.0);
        }
        self.ops.push(o);
    }
    fn g(&mut self, l: &[G]) {
        for &x in l {
            self.gate(x);
        }
    }
    fn xc(&mut self, a: u32, b: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::X;
        o.q_target = q(a);
        o.c_condition = BitId(b);
        self.ops.push(o);
    }
    fn zc(&mut self, a: u32, b: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::Z;
        o.q_target = q(a);
        o.c_condition = BitId(b);
        self.ops.push(o);
    }
    /// LEAN_SQ: CZ(a, b) under the classical bit (Gidney's AND uncompute correction).
    fn czc(&mut self, a: u32, b: u32, bit: u64) {
        let mut o = Op::empty();
        o.kind = OperationType::CZ;
        o.q_control1 = q(a);
        o.q_target = q(b);
        o.c_condition = BitId(bit);
        self.ops.push(o);
    }
    fn hmr(&mut self, a: u32) -> u64 {
        let b = self.bits;
        self.bits += 1;
        let mut o = Op::empty();
        o.kind = OperationType::Hmr;
        o.q_target = q(a);
        o.c_target = BitId(b);
        self.ops.push(o);
        b
    }
}

fn add_gl(t: &[u32], s: &[u32], c: u32) -> GL {
    let mut g = Vec::with_capacity(3 * t.len());
    for i in 0..t.len() {
        g.push(gc(c, s[i]));
        g.push(gc(c, t[i]));
        g.push(gt(s[i], t[i], c));
    }
    g
}
fn add_back(t: &[u32], s: &[u32], c: u32) -> GL {
    let mut g = Vec::with_capacity(4 * t.len());
    for i in (0..t.len()).rev() {
        g.push(gt(s[i], t[i], c));
        g.push(gc(c, t[i]));
        g.push(gc(s[i], t[i]));
        g.push(gc(c, s[i]));
    }
    g
}

/// The shell. No spare lane for the doubling: it is a rotation, the top bit is already the LSB of its multiple of c0.
/// The carry lane doubles as the fold's clean lane. a has 255 bits, its top lane and N's top lane are free after F.
/// x is squared into in place and classical offsets load 128 bits at a time. The top CAPW multiplier bits can move into the
/// product's top lanes with a descending seed, an idea from the public frogdrop 765 note 153caee.
/// LEAN_SQ: Gidney halved adder (arXiv:1709.06648): tgt += add mod 2^w (w = tgt.len() = add.len()); the carries
/// c_1..c_(w-1) live on anc[0..w-1) (clean in, clean out) and are uncomputed by measurement (Hmr, then CZ under the
/// bit). With cout = Some(s) the carry-out c_w is computed onto s and kept. w-1 Toffoli (w with cout).
fn gid_add(p: &mut P, tgt: &[u32], add: &[u32], anc: &[u32], cout: Option<u32>) {
    let w = tgt.len();
    assert!(w >= 1 && add.len() == w);
    let kmax = if cout.is_some() { w } else { w - 1 };
    assert!(anc.len() + 1 >= kmax, "gid_add: {} ancillae for {} carries", anc.len(), kmax);
    for k in 0..kmax {
        let ck = if k == 0 { NONE } else { anc[k - 1] };
        let tc = if k == w - 1 { cout.unwrap() } else { anc[k] };
        if ck != NONE {
            p.g(&[gc(ck, add[k]), gc(ck, tgt[k])]);
        }
        p.g(&[gt(add[k], tgt[k], tc)]);
        if ck != NONE {
            p.g(&[gc(ck, tc)]);
        }
    }
    for k in (0..w).rev() {
        let ck = if k == 0 { NONE } else { anc[k - 1] };
        let processed = k < kmax;
        if processed && k < w - 1 {
            if ck != NONE {
                p.g(&[gc(ck, anc[k])]);
            }
            let m = p.hmr(anc[k]);
            p.czc(add[k], tgt[k], m);
        }
        if processed {
            if ck != NONE {
                p.g(&[gc(ck, add[k])]);
            }
            p.g(&[gc(add[k], tgt[k])]);
        } else {
            p.g(&[gc(add[k], tgt[k])]);
            if ck != NONE {
                p.g(&[gc(ck, tgt[k])]);
            }
        }
    }
}
/// LEAN_SQ: tgt -= add mod 2^w as not(not tgt + add).
fn gid_sub(p: &mut P, tgt: &[u32], add: &[u32], anc: &[u32]) {
    let x: GL = tgt.iter().map(|&q0| gx(q0)).collect();
    p.g(&x);
    gid_add(p, tgt, add, anc, None);
    p.g(&x);
}
/// LEAN_SQ: Haener's squarer, LSB first: z (2n or more wires, zero) += v^2. v^2 = -v + sum_i (2 v_i - 1) 2^(2i+1) (h_i + v_i),
/// h_i = v >> (i + 1). Step 0: z[0..n+1) -= v. Step i: sign-extend z[n+i] -> z[n+i+1]; window z[2i+1 .. n+i+2) -= u, u = h_i
/// padded to the window and inverted under v_i. Last: z[2n-1] ^= v_(n-1). AND ancillae: z above the window, then xa.
fn sq_fwd(p: &mut P, v: &[u32], z: &[u32], pad: [u32; 2], xa: [u32; 2]) {
    let n = v.len();
    let zb = z.len();
    assert!(zb >= 2 * n);
    {
        let w = n + 1;
        let mut add: Vec<u32> = v.to_vec();
        add.push(pad[0]);
        let mut anc: Vec<u32> = z[w..].to_vec();
        anc.extend_from_slice(&xa);
        gid_sub(p, &z[0..w], &add, &anc);
    }
    for i in 0..n - 1 {
        let (lo, top) = (2 * i + 1, n + i + 2);
        let w = top - lo;
        p.g(&[gc(z[n + i], z[n + i + 1])]);
        let mut add: Vec<u32> = v[i + 1..].to_vec();
        add.push(pad[0]);
        add.push(pad[1]);
        assert!(add.len() == w);
        let inv: GL = add.iter().map(|&q0| gc(v[i], q0)).collect();
        let mut anc: Vec<u32> = z[top..].to_vec();
        anc.extend_from_slice(&xa);
        p.g(&inv);
        gid_sub(p, &z[lo..top], &add, &anc);
        p.g(&inv);
    }
    p.g(&[gc(v[n - 1], z[2 * n - 1])]);
}
/// LEAN_SQ: the exact reverse of sq_fwd (z -= v^2 back to zero).
fn sq_rev(p: &mut P, v: &[u32], z: &[u32], pad: [u32; 2], xa: [u32; 2]) {
    let n = v.len();
    p.g(&[gc(v[n - 1], z[2 * n - 1])]);
    for i in (0..n - 1).rev() {
        let (lo, top) = (2 * i + 1, n + i + 2);
        let w = top - lo;
        let mut add: Vec<u32> = v[i + 1..].to_vec();
        add.push(pad[0]);
        add.push(pad[1]);
        assert!(add.len() == w);
        let inv: GL = add.iter().map(|&q0| gc(v[i], q0)).collect();
        let mut anc: Vec<u32> = z[top..].to_vec();
        anc.extend_from_slice(&xa);
        p.g(&inv);
        gid_add(p, &z[lo..top], &add, &anc, None);
        p.g(&inv);
        p.g(&[gc(z[n + i], z[n + i + 1])]);
    }
    {
        let w = n + 1;
        let mut add: Vec<u32> = v.to_vec();
        add.push(pad[0]);
        let mut anc: Vec<u32> = z[w..].to_vec();
        anc.extend_from_slice(&xa);
        gid_add(p, &z[0..w], &add, &anc, None);
    }
}
/// LEAN_SB: z[0..2n) += v * h by controlled window adds z[i..i+n+1) += v_i * h (h padded with one zero lane); 3 T per wire.
/// Partial sums stay below 2^(i+n+1), so no window overflows and the carry lane returns clean.
fn cross_fwd(p: &mut P, v: &[u32], h: &[u32], z: &[u32], pad: u32, c: u32) {
    let n = v.len();
    let mut u: Vec<u32> = h.to_vec();
    u.push(pad);
    for i in 0..n {
        let w = n + 1;
        let tgt = &z[i..i + w];
        let mut g = add_gl(tgt, &u, c);
        for j in (0..w).rev() {
            g.extend_from_slice(&[gt(u[j], tgt[j], c), gc(c, tgt[j]), gt(v[i], u[j], tgt[j]), gc(c, u[j])]);
        }
        p.g(&g);
    }
}
fn cross_rev(p: &mut P, v: &[u32], h: &[u32], z: &[u32], pad: u32, c: u32) {
    let n = v.len();
    let mut u: Vec<u32> = h.to_vec();
    u.push(pad);
    for i in (0..n).rev() {
        let w = n + 1;
        let tgt = &z[i..i + w];
        let mut g = add_gl(tgt, &u, c);
        for j in (0..w).rev() {
            g.extend_from_slice(&[gt(u[j], tgt[j], c), gc(c, tgt[j]), gt(v[i], u[j], tgt[j]), gc(c, u[j])]);
        }
        p.g(&rev(&g));
    }
}

struct S3 {
    dirty: Vec<u32>,
    zl: Vec<u32>,
}
impl S3 {
    fn m(&self, l: &[Lit], t: u32) -> GL {
        mcx(l, t, &self.dirty)
    }
    /// reg += f at its LSB, plus sign*f*2^pos for (pos,sign,z) in terms, z clean. One two-pass chain: a clean lane z in place of
    /// the borrowed bit takes f on one pass. f's wire reads f^d0 between the passes; the corrections are CNOTs.
    fn merged(&self, reg: &[u32], f: u32, terms: &[(usize, i32, u32)], c: u32) -> GL {
        let mut r = vec![f];
        r.extend_from_slice(reg);
        let mut d: Vec<u32> = Vec::with_capacity(r.len());
        let mut u = 0;
        for i in 0..r.len() {
            if let Some(t) = terms.iter().find(|t| t.0 + 1 == i) {
                d.push(t.2);
            } else {
                loop {
                    let q0 = self.dirty[u];
                    u += 1;
                    if q0 != c && !r.contains(&q0) && !terms.iter().any(|t| t.2 == q0) {
                        d.push(q0);
                        break;
                    }
                }
            }
        }
        let sub = rev(&add_chain(&r, &d, c));
        let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
        let d0 = d[0];
        let mut g: GL = vec![];
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
        }
        g.extend_from_slice(&nots);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&nots);
        g.push(gx(f));
        g
    }
    /// ZFOR-wait signed digits: `merged` whose extra terms (pos, sign, lane) add sign * (W - c) * 2^pos, W and c wires.
    /// Lane values across the two passes: positive (not W, c), negative (W, not c) (tools/chain_signed.py, exhaustive).
    fn merged_s(&self, reg: &[u32], f: u32, terms: &[(usize, i32, u32)], wt: u32, cc: u32, dterms: &[(usize, i32, u32)], c: u32) -> GL {
        let mut r = vec![f];
        r.extend_from_slice(reg);
        let mut d: Vec<u32> = Vec::with_capacity(r.len());
        let mut u = 0;
        for i in 0..r.len() {
            if let Some(t) = terms.iter().chain(dterms.iter()).find(|t| t.0 + 1 == i) {
                d.push(t.2);
            } else {
                loop {
                    let q0 = self.dirty[u];
                    u += 1;
                    if q0 != c && q0 != wt && q0 != cc && !r.contains(&q0) && !terms.iter().chain(dterms.iter()).any(|t| t.2 == q0) {
                        d.push(q0);
                        break;
                    }
                }
            }
        }
        let sub = rev(&add_chain(&r, &d, c));
        let nots: GL = d.iter().map(|&q0| gx(q0)).collect();
        let d0 = d[0];
        let mut g: GL = vec![];
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
        }
        for t in dterms.iter() {
            g.push(gc(wt, t.2));
            if t.1 > 0 {
                g.push(gx(t.2));
            }
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 < 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
        }
        for t in dterms.iter() {
            g.push(gc(wt, t.2));
            g.push(gc(cc, t.2));
        }
        g.extend_from_slice(&nots);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gc(d0, t.2));
            g.push(gx(t.2));
        }
        g.extend_from_slice(&sub);
        for t in terms.iter().filter(|t| t.1 > 0) {
            g.push(gc(f, t.2));
            g.push(gx(t.2));
        }
        for t in dterms.iter() {
            g.push(gc(cc, t.2));
            if t.1 > 0 {
                g.push(gx(t.2));
            }
        }
        g.extend_from_slice(&nots);
        g.push(gx(f));
        g
    }
    /// ZFOR-wait: acc += a with no control, carry-out on ov (zuiris's add_ctl with the control removed: 2 T per wire).
    fn add_plain(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g: GL;
        if a.len() == 256 {
            g = add_gl(acc, a, c);
            g.push(gc(c, ov));
            for j in (0..256).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gc(a[j], acc[j]), gc(c, a[j])]);
            }
        } else {
            g = add_gl(&acc[..255], a, c);
            g.push(gt(c, acc[255], ov));
            g.push(gc(c, acc[255]));
            for j in (0..255).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gc(a[j], acc[j]), gc(c, a[j])]);
            }
        }
        g
    }
    /// ZFOR-wait: zuiris's clear_ov with the control removed.
    fn clear_ov_plain(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        let mut h: GL = acc[k..].iter().map(|&q0| gx(q0)).collect();
        let mut g;
        if a.len() == 256 {
            h.extend(add_gl(&acc[k..], &a[k..], c));
            g = h.clone();
            g.push(gc(c, ov));
        } else {
            h.extend(add_gl(&acc[k..255], &a[k..], c));
            g = h.clone();
            g.push(gt(c, acc[255], ov));
        }
        g.extend(rev(&h));
        g
    }
    /// ZFOR-wait signed round: acc = acc + a (bit = 1) or acc - a (bit = 0), the subtraction as ~(~acc + a). The bit wire
    /// holds c = not bit inside the bracket; the next doubling's fold rides the ov chain as (K/2)(W255 - c).
    fn round3(&self, acc: &[u32], a: &[u32], bit: u32, c: u32, ov: u32, nxt: bool) -> GL {
        let mut g: GL = vec![gx(bit)];
        for &q0 in acc {
            g.push(gc(bit, q0));
        }
        g.extend(self.add_plain(acc, a, c, ov));
        if nxt {
            let z = &self.zl;
            g.extend(self.merged_s(&acc[0..RW], ov, &[(4, 1, z[3]), (6, -1, z[0]), (10, 1, z[1]), (32, 1, z[2])], acc[255], bit, &[(3, 1, z[4]), (5, -1, z[5]), (9, 1, z[6]), (31, 1, z[7])], c));
        } else {
            g.extend(self.lean(acc, ov, RW, c));
        }
        g.extend(self.clear_ov_plain(acc, a, c, ov));
        for &q0 in acc {
            g.push(gc(bit, q0));
        }
        g.push(gx(bit));
        g
    }
    /// ZFOR-wait: acc += a, no control (one plain round).
    fn add_round(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g = self.add_plain(acc, a, c, ov);
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov_plain(acc, a, c, ov));
        g
    }
    /// ZFOR-wait: acc -= a (fixed subtraction round, no doubling term).
    fn sub_round(&self, acc: &[u32], a: &[u32], c: u32, ov: u32) -> GL {
        let mut g: GL = acc.iter().map(|&q0| gx(q0)).collect();
        g.extend(self.add_plain(acc, a, c, ov));
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov_plain(acc, a, c, ov));
        g.extend(acc.iter().map(|&q0| gx(q0)));
        g
    }
    /// ZFOR-wait: acc := acc / 2 mod p (inverse of zuiris's doubling), returns the new labeling.
    fn halve(&self, acc: &[u32], c: u32) -> (Vec<u32>, GL) {
        let mut prev: Vec<u32> = acc[1..].to_vec();
        prev.push(acc[0]);
        let (t2, h) = self.dbl(&prev, c);
        assert!(t2 == acc);
        (prev, rev(&h))
    }
    fn lean(&self, t: &[u32], f: u32, _window: usize, c2: u32) -> GL {
        let z = &self.zl;
        if ZL >= 4 {
            return self.merged(&t[0..RW], f, &[(4, 1, z[3]), (6, -1, z[0]), (10, 1, z[1]), (32, 1, z[2])], c2);
        }
        let mut g = inc_long(&t[0..CHW], f, &self.dirty, c2);
        g.extend(self.merged(&t[4..RW], f, &[(2, -1, z[0]), (6, 1, z[1]), (28, 1, z[2])], c2));
        g
    }
    fn dbl(&self, t: &[u32], c2: u32) -> (Vec<u32>, GL) {
        let mut t2 = vec![t[255]];
        t2.extend_from_slice(&t[..255]);
        let f = t2[0];
        let z = &self.zl;
        let g = self.merged(&t2[4..RW], f, &[(2, -1, z[0]), (6, 1, z[1]), (28, 1, z[2])], c2);
        (t2, g)
    }
    fn add_ctl(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let mut g: GL;
        if a.len() == 256 {
            g = add_gl(acc, a, c);
            g.push(gt(ctl, c, ov));
            for j in (0..256).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gt(ctl, a[j], acc[j]), gc(c, a[j])]);
            }
        } else {
            g = add_gl(&acc[..255], a, c);
            g.extend(self.m(&[(ctl, true), (c, true), (acc[255], true)], ov));
            g.push(gt(ctl, c, acc[255]));
            for j in (0..255).rev() {
                g.extend_from_slice(&[gt(a[j], acc[j], c), gc(c, acc[j]), gt(ctl, a[j], acc[j]), gc(c, a[j])]);
            }
        }
        g
    }
    /// ov = ctl & (T < a), read on the top CMPW wires. An equal window reads as T >= a, so T = a (the first add) is right.
    fn clear_ov(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        let mut h: GL = acc[k..].iter().map(|&q0| gx(q0)).collect();
        let mut g;
        if a.len() == 256 {
            h.extend(add_gl(&acc[k..], &a[k..], c));
            g = h.clone();
            g.push(gt(ctl, c, ov));
        } else {
            h.extend(add_gl(&acc[k..255], &a[k..], c));
            g = h.clone();
            g.extend(self.m(&[(ctl, true), (c, true), (acc[255], true)], ov));
        }
        g.extend(rev(&h));
        g
    }
    fn round(&self, acc: &[u32], a: &[u32], ctl: u32, c: u32, ov: u32) -> GL {
        let mut g = self.add_ctl(acc, a, ctl, c, ov);
        g.extend(self.lean(acc, ov, RW, c));
        g.extend(self.clear_ov(acc, a, ctl, c, ov));
        g
    }
    /// acc = a * sum bits[i] 2^i mod p; the top w bits move into acc's top lanes. Returns acc, the fresh lanes, the gates.
    fn product(&self, p: &mut P, a: &[u32], bits: &[u32], c: u32, ov: u32, w: usize) -> (Vec<u32>, Vec<u32>, GL) {
        let nb = bits.len();
        let j_: Vec<u32> = bits[nb - w..].to_vec();
        let low = p.allocn(256 - w);
        let mut acc = low.clone();
        acc.extend_from_slice(&j_);
        let mut g: GL = vec![];
        let mut al = NONE;
        if w > 0 {
            al = p.alloc();
            let zl: Vec<Lit> = (0..ZW).map(|r| (acc[r], false)).collect();
            for k in (1..(1usize << w)).rev() {
                let mut l: Vec<Lit> = vec![(al, false)];
                for i in 0..w {
                    l.push((j_[i], (k >> i) & 1 == 1));
                }
                g.extend(self.m(&l, c));
                for i in 0..w {
                    if (k >> i) & 1 == 1 {
                        g.push(gc(c, j_[i]));
                    }
                }
                g.push(gc(c, al));
                let mut l2: Vec<Lit> = vec![(al, true)];
                l2.extend_from_slice(&zl);
                g.extend(self.m(&l2, c));
                g.extend(self.round(&acc, a, al, c, ov));
            }
            g.push(gx(al));
            g.extend(self.m(&zl, al));
        }
        // ZFOR-wait signed digits. With CAPW = w > 0, zuiris's seed loop above leaves acc = S a (S = the top w bits).
        // Then acc := 2 acc + a (one plain round), m = nb - w signed rounds on the low bits give 2ab + a; subtract a, halve.
        if w == 0 {
            for j in 0..a.len() {
                g.push(gc(a[j], acc[j]));
            }
        } else {
            let (t2, h) = self.dbl(&acc, c);
            acc = t2;
            g.extend(h);
            g.extend(self.add_round(&acc, a, c, ov));
        }
        let idx: Vec<usize> = (0..(nb - w)).rev().collect();
        for (j, &i) in idx.iter().enumerate() {
            if j == 0 && w == 0 && a.len() < 256 {
                // acc = a with a 255-bit a: top wire 0, so this doubling's fold is dead
                let mut t2 = vec![acc[255]];
                t2.extend_from_slice(&acc[..255]);
                acc = t2;
            } else {
                let (t2, h) = self.dbl(&acc, c);
                acc = t2;
                g.extend(h);
            }
            g.extend(self.round3(&acc, a, bits[i], c, ov, false));
        }
        g.extend(self.sub_round(&acc, a, c, ov));
        let (t2, h) = self.halve(&acc, c);
        acc = t2;
        g.extend(h);
        if w > 0 {
            p.rel(al);
        }
        (acc, low, g)
    }
    fn neg(&self, p: &mut P, t: &[u32], c2: u32) {
        let u = p.alloc();
        p.g(&[gx(u)]);
        let mut g: GL = t.iter().map(|&q0| gx(q0)).collect();
        for &b in &C0M1 {
            g.extend(rev(&inc_long(&t[b..], u, &self.dirty, c2)));
        }
        g.push(gx(u));
        p.g(&g);
        p.rel(u);
    }
    fn cneg_list(&self, t: &[u32], ctl: u32, neg_when: bool, c2: u32) -> GL {
        let pre: GL = if neg_when { vec![] } else { vec![gx(ctl)] };
        let mut g = pre.clone();
        for &q0 in t {
            g.push(gc(ctl, q0));
        }
        for &b in &C0M1 {
            g.extend(rev(&inc_long(&t[b..], ctl, &self.dirty, c2)));
        }
        g.extend_from_slice(&pre);
        g
    }
    /// t += classical s mod p (t -= s when sub), 128 lanes at a time.
    fn cl_add(&mut self, p: &mut P, t: &[u32], bits: u64, sub: bool) {
        const K: usize = 128;
        let l = p.allocn(K);
        let (k, c, o) = (p.alloc(), p.alloc(), p.alloc());
        self.zl = p.allocn(ZL);
        let keep = self.dirty.clone();
        self.dirty.extend_from_slice(&l);
        let (lo, hi) = (&t[..K], &t[K..]);
        let flip = |r: &[u32]| -> GL { r.iter().map(|&q0| gx(q0)).collect() };
        enum It {
            Load(u64),
            Gs(GL),
        }
        let mut seq: Vec<It> = vec![];
        let a1 = {
            let mut g = add_gl(lo, &l, c);
            g.push(gc(c, k));
            g.extend(add_back(lo, &l, c));
            g
        };
        let a2 = {
            let mut g = add_gl(hi, &l, k);
            g.push(gc(k, o));
            g.extend(add_back(hi, &l, k));
            g
        };
        let h = {
            let mut h0 = flip(lo);
            h0.extend(add_gl(lo, &l, c));
            let mut g = h0.clone();
            g.push(gc(c, k));
            g.extend(rev(&h0));
            g
        };
        let h2 = {
            let mut h0 = flip(hi);
            h0.extend(add_gl(hi, &l, k));
            let mut g = h0.clone();
            g.push(gc(k, o));
            g.extend(rev(&h0));
            g
        };
        seq.push(It::Load(0));
        seq.push(It::Gs(a1));
        seq.push(It::Load(0));
        seq.push(It::Load(K as u64));
        seq.push(It::Gs(a2));
        seq.push(It::Load(K as u64));
        seq.push(It::Load(0));
        seq.push(It::Gs(h.clone()));
        seq.push(It::Load(0));
        seq.push(It::Gs(self.lean(t, o, 256, c)));
        seq.push(It::Load(0));
        seq.push(It::Gs(h.clone()));
        seq.push(It::Load(0));
        seq.push(It::Load(K as u64));
        seq.push(It::Gs(h2));
        seq.push(It::Load(K as u64));
        seq.push(It::Load(0));
        seq.push(It::Gs(h));
        seq.push(It::Load(0));
        if sub {
            seq.reverse();
        }
        for it in &seq {
            match it {
                It::Load(off) => {
                    for i in 0..K {
                        p.xc(l[i], bits + off + i as u64);
                    }
                }
                It::Gs(g) => {
                    if sub {
                        p.g(&rev(g));
                    } else {
                        p.g(g);
                    }
                }
            }
        }
        self.dirty = keep;
        for &q0 in &l {
            p.rel(q0);
        }
        p.rel(k);
        p.rel(c);
        p.rel(o);
        for i in 0..ZL {
            p.rel(self.zl[i]);
        }
    }
    /// x += lam^2 in place: halve 256 times, then Horner on x.
    /// LEAN_SQ: ov ^= [x_top < atop] on the top CMPW wires (the parent's compare with the addend's top wires given).
    fn clear_ov_top(&self, x: &[u32], atop: &[u32], c: u32, ov: u32) -> GL {
        let k = 256 - CMPW;
        assert!(atop.len() == CMPW);
        let mut h: GL = x[k..].iter().map(|&q0| gx(q0)).collect();
        h.extend(add_gl(&x[k..], atop, c));
        let mut g = h.clone();
        g.push(gc(c, ov));
        g.extend(rev(&h));
        g
    }
    /// LEAN_SQ: x[j..256) += a (a.len() = 256 - j), carry-out on ov, fold ov c0 (the parent's chain), erase ov by the
    /// top-window compare against (a << j)'s top wires. The parent's add_plain + lean + clear_ov_plain, shifted.
    fn fold_shift(&self, x: &[u32], a: &[u32], j: usize, c: u32, ov: u32) -> GL {
        let w = 256 - j;
        assert!(a.len() == w && w >= CMPW);
        let mut g = add_gl(&x[j..], a, c);
        g.push(gc(c, ov));
        g.extend(add_back(&x[j..], a, c));
        if LEAN_ZL >= 4 {
            g.extend(self.lean(x, ov, RW, c));
        } else {
            let z = &self.zl;
            g.extend(inc_long(&x[0..CHW], ov, &self.dirty, c));
            g.extend(self.merged(&x[4..RW], ov, &[(2, -1, z[0]), (6, 1, z[1]), (28, 1, z[2])], c));
        }
        g.extend(self.clear_ov_top(x, &a[w - CMPW..], c, ov));
        g
    }
    /// LEAN_SQ: x[o..o+wv) += v, the carry-out carried on through the next SPILL_W wires by the borrowed-lane increment,
    /// then erased by the window compare (t = [x_window < v]). Exact unless the carry runs past the window (2^-64).
    fn spill_add(&self, x: &[u32], v: &[u32], o: usize, c: u32, t: u32) -> GL {
        let wv = v.len();
        let hi = o + wv;
        assert!(hi <= 256);
        let mut g = add_gl(&x[o..hi], v, c);
        g.push(gc(c, t));
        g.extend(add_back(&x[o..hi], v, c));
        let top = (hi + SPILL_W).min(256);
        if top > hi {
            g.extend(inc_long(&x[hi..top], t, &self.dirty, c));
        }
        let mut h: GL = x[o..hi].iter().map(|&q0| gx(q0)).collect();
        h.extend(add_gl(&x[o..hi], v, c));
        g.extend(h.clone());
        g.push(gc(c, t));
        g.extend(rev(&h));
        g
    }
    /// LEAN_SQ: x += (Z << sh) mod p (pos) or x -= (Z << sh) mod p, Z = z[0..zw) an integer below 2^zw. The low 256 - sh
    /// wires shift into x; the top zw - 256 + sh wires are the spill, added times c0 = 2^32 + 2^10 - 2^6 + 2^4 + 1.
    fn weighted(&self, x: &[u32], z: &[u32], zw: usize, sh: usize, pos: bool, c: u32, ov: u32) -> GL {
        let flip: GL = x.iter().map(|&q0| gx(q0)).collect();
        let mut g: GL = vec![];
        if !pos {
            g.extend(flip.clone());
        }
        let wlo = 256 - sh;
        g.extend(self.fold_shift(x, &z[..wlo], sh, c, ov));
        if zw > wlo {
            let hi = &z[wlo..zw];
            for (o, sg) in [(32usize, true), (10, true), (6, false), (4, true), (0, true)] {
                if !sg {
                    g.extend(flip.clone());
                }
                g.extend(self.spill_add(x, hi, o, c, ov));
                if !sg {
                    g.extend(flip.clone());
                }
            }
        }
        if !pos {
            g.extend(flip);
        }
        g
    }
    /// LEAN_SQ: x += lam^2 mod p. lam = L + 2^128 H, S = L + H: lam^2 = L^2 (1 - 2^128) + H^2 (c0 - 2^128) + 2^128 S^2.
    fn sq_into_lean(&mut self, p: &mut P, x: &[u32], lam: &[u32]) {
        let next0 = p.next;
        let (c, ov) = (p.alloc(), p.alloc());
        self.zl = p.allocn(LEAN_ZL);
        let (l, h) = (&lam[..128], &lam[128..]);
        let xa = [self.zl[0], self.zl[1]];
        if LEAN_SB {
            // 256-wire variant: lam^2 = L^2 + 2^129 L H + c0 H^2; pads = zl[2] and ov (ov idle during the squarers).
            let z = p.allocn(256);
            assert!(p.next == next0, "LEAN_SQ raised the peak: {} -> {}", next0, p.next);
            let pad = [self.zl[2], ov];
            sq_fwd(p, l, &z, pad, xa);
            p.g(&self.weighted(x, &z, 256, 0, true, c, ov));
            sq_rev(p, l, &z, pad, xa);
            sq_fwd(p, h, &z, pad, xa);
            for (sh, pos) in [(32usize, true), (10, true), (6, false), (4, true), (0, true)] {
                p.g(&self.weighted(x, &z, 256, sh, pos, c, ov));
            }
            if !LEAN_NEGCTL {
                sq_rev(p, h, &z, pad, xa);
            }
            cross_fwd(p, l, h, &z, self.zl[2], c);
            p.g(&self.weighted(x, &z, 256, 129, true, c, ov));
            cross_rev(p, l, h, &z, self.zl[2], c);
            for &q0 in z.iter().rev() {
                p.rel(q0);
            }
            for i in 0..LEAN_ZL {
                p.rel(self.zl[i]);
            }
            p.rel(ov);
            p.rel(c);
            assert!(p.next == next0);
            return;
        }
        let z = p.allocn(258);
        let s = p.alloc();
        assert!(p.next == next0, "LEAN_SQ raised the peak: {} -> {}", next0, p.next);
        let pad = [self.zl[2], self.zl[3]];
        sq_fwd(p, l, &z, pad, xa);
        p.g(&self.weighted(x, &z, 256, 0, true, c, ov));
        p.g(&self.weighted(x, &z, 256, 128, false, c, ov));
        sq_rev(p, l, &z, pad, xa);
        sq_fwd(p, h, &z, pad, xa);
        for (sh, pos) in [(32usize, true), (10, true), (6, false), (4, true), (0, true), (128, false)] {
            p.g(&self.weighted(x, &z, 256, sh, pos, c, ov));
        }
        sq_rev(p, h, &z, pad, xa);
        gid_add(p, l, h, &z[..128], Some(s));
        let sv: Vec<u32> = [l, &[s][..]].concat();
        sq_fwd(p, &sv, &z, pad, xa);
        p.g(&self.weighted(x, &z, 258, 128, true, c, ov));
        sq_rev(p, &sv, &z, pad, xa);
        if !LEAN_NEGCTL {
            let mut hp: Vec<u32> = h.to_vec();
            hp.push(pad[0]);
            let fl: GL = sv.iter().map(|&q0| gx(q0)).collect();
            p.g(&fl);
            gid_add(p, &sv, &hp, &z[..128], None);
            p.g(&fl);
        }
        p.rel(s);
        for &q0 in z.iter().rev() {
            p.rel(q0);
        }
        for i in 0..LEAN_ZL {
            p.rel(self.zl[i]);
        }
        p.rel(ov);
        p.rel(c);
        assert!(p.next == next0);
    }
    fn sq_into(&mut self, p: &mut P, x: &[u32], lam: &[u32]) {
        if LEAN_SQ {
            self.sq_into_lean(p, x, lam);
            return;
        }
        let (c, ov, d) = (p.alloc(), p.alloc(), p.alloc());
        self.zl = p.allocn(ZL);
        let mut cur = x.to_vec();
        for _ in 0..256 {
            let mut prev: Vec<u32> = cur[1..].to_vec();
            prev.push(cur[0]);
            let (t2, h) = self.dbl(&prev, c);
            assert!(t2 == cur);
            p.g(&rev(&h));
            cur = prev;
        }
        // ZFOR-wait signed digits: cur = x / 2^256. One plain round (2 cur + lam), 256 signed rounds on lam's bits
        // (2 cur + s_i lam), subtract lam, halve: x + lam^2.
        {
            let (t2, h) = self.dbl(&cur, c);
            cur = t2;
            p.g(&h);
            p.g(&[gx(d)]);
            p.g(&self.round3(&cur, lam, d, c, ov, false));
            p.g(&[gx(d)]);
        }
        for i in (0..256).rev() {
            let (t2, h) = self.dbl(&cur, c);
            cur = t2;
            p.g(&h);
            p.g(&[gc(lam[i], d)]);
            p.g(&self.round3(&cur, lam, d, c, ov, false));
            p.g(&[gc(lam[i], d)]);
        }
        p.g(&self.sub_round(&cur, lam, c, ov));
        let (t2, h) = self.halve(&cur, c);
        cur = t2;
        p.g(&h);
        assert!(cur == x);
        p.rel(c);
        p.rel(ov);
        p.rel(d);
        for i in 0..ZL {
            p.rel(self.zl[i]);
        }
    }
}
struct Kept {
    y0: u32,
    y1: u32,
    par: u32,
    xtop: u32,
}
fn map_lanes(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32], kept: Option<&Kept>) -> Vec<u32> {
    let mut m = vec![NONE; fc.next as usize];
    for i in 0..256 {
        m[i] = x[i];
        m[256 + i] = pas[i];
    }
    if let Some(k) = kept {
        m[fc.y0 as usize] = k.y0;
        m[fc.y1 as usize] = k.y1;
    }
    for v in 0..fc.next as usize {
        if m[v] == NONE {
            m[v] = p.alloc();
        }
    }
    m
}
fn mapg(m: &[u32], g: G) -> G {
    if g.2 != NONE {
        let t = if HMR_AND { g.2 & !AND_FLAG } else { g.2 };
        G(m[g.0 as usize], m[g.1 as usize], m[t as usize] | (g.2 & AND_FLAG & if HMR_AND { u32::MAX } else { 0 }))
    } else if g.1 != NONE {
        G(m[g.0 as usize], m[g.1 as usize], NONE)
    } else {
        G(m[g.0 as usize], NONE, NONE)
    }
}
fn emit_f(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32]) -> (Vec<u32>, Kept) {
    let m = map_lanes(p, fc, x, pas, None);
    for &g in &fc.gates {
        p.gate(mapg(&m, g));
    }
    for &g in &fc.last {
        p.gate(mapg(&m, g));
    }
    let a: Vec<u32> = fc.ar.iter().map(|&v| m[v as usize]).collect();
    let kept = Kept { y0: m[fc.y0 as usize], y1: m[fc.y1 as usize], par: m[fc.par as usize], xtop: m[fc.xtop as usize] };
    assert!(p.hold.iter().all(|&h| h == 0), "hmr-and: AND held at the end of emit_f");
    for v in 512..fc.next {
        if v != fc.y0 && v != fc.y1 {
            p.rel(m[v as usize]);
        }
    }
    (a, kept)
}
fn emit_finv(p: &mut P, fc: &FCirc, x: &[u32], pas: &[u32], k: &Kept) {
    let m = map_lanes(p, fc, x, pas, Some(k));
    for &g in fc.last.iter().rev() {
        p.gate(mapg(&m, g));
    }
    for &g in fc.gates.iter().rev() {
        p.gate(mapg(&m, g));
    }
    assert!(p.hold.iter().all(|&h| h == 0), "hmr-and: AND held at the end of emit_finv");
    for v in 512..fc.next {
        p.rel(m[v as usize]);
    }
}

fn build_unfolded() -> Vec<Op> {
    let fc = f_circuit();
    let mut p = P { ops: Vec::with_capacity(190_000_000), free: vec![], next: 0, bits: 0, hold: vec![] };
    let x = p.allocn(256);
    let y = p.allocn(256);
    let (ox, oy) = (0u64, 256u64);
    p.bits = 512;
    for r in 0..4u64 {
        let mut o = Op::empty();
        o.kind = OperationType::Register;
        o.r_target = RegisterId(r);
        p.ops.push(o);
    }
    for (r, lanes) in [(0u64, &x), (1u64, &y)] {
        for &a in lanes.iter() {
            let mut o = Op::empty();
            o.kind = OperationType::AppendToRegister;
            o.q_target = q(a);
            o.r_target = RegisterId(r);
            p.ops.push(o);
        }
    }
    for (r, base) in [(2u64, ox), (3u64, oy)] {
        for i in 0..256u64 {
            let mut o = Op::empty();
            o.kind = OperationType::AppendToRegister;
            o.c_target = BitId(base + i);
            o.r_target = RegisterId(r);
            p.ops.push(o);
        }
    }
    let w = CAPW;
    let mut a = S3 { dirty: y.clone(), zl: vec![] };
    a.cl_add(&mut p, &x, ox, true);
    a.dirty = x.clone();
    a.cl_add(&mut p, &y, oy, true);
    // division 1
    let (a1, k1) = emit_f(&mut p, &fc, &x, &y);
    a.dirty = [&a1[..255], &y[..256 - w]].concat();
    a.zl = p.allocn(ZL);
    let (lam, _low1, g) = a.product(&mut p, &a1[..255], &y, k1.xtop, a1[255], w);
    p.g(&g);
    drop(g);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    a.dirty = [&a1[..255], &y[..256 - w]].concat();
    let cg = a.cneg_list(&lam, k1.par, false, k1.xtop);
    p.g(&cg);
    let m1: Vec<u64> = y[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
    for &q0 in &y[..256 - w] {
        p.rel(q0);
    }
    emit_finv(&mut p, &fc, &x, &lam, &k1);
    // dy recompute
    let (c, ov) = (p.alloc(), p.alloc());
    a.zl = p.allocn(ZL);
    a.dirty = [&lam[..], &x[..256 - w]].concat();
    let (dy2, low2, g) = a.product(&mut p, &lam, &x, c, ov, w);
    p.g(&g);
    for i in 0..(256 - w) {
        p.zc(dy2[i], m1[i]);
    }
    p.g(&rev(&g));
    drop(g);
    for &q0 in &low2 {
        p.rel(q0);
    }
    p.rel(c);
    p.rel(ov);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    // x: dx' = lam^2 - dx - 3 ox
    let c2 = p.alloc();
    a.dirty = lam.clone();
    a.neg(&mut p, &x, c2);
    p.rel(c2);
    a.dirty = lam.clone();
    a.sq_into(&mut p, &x, &lam);
    for _ in 0..3 {
        a.dirty = lam.clone();
        a.cl_add(&mut p, &x, ox, true);
    }
    // y: ndy = -lam dx'; lam's top bits go on living inside it
    let (c, ov) = (p.alloc(), p.alloc());
    a.zl = p.allocn(ZL);
    a.dirty = [&x[..], &lam[..256 - w]].concat();
    let (ndy, _low4, g) = a.product(&mut p, &x, &lam, c, ov, w);
    p.g(&g);
    drop(g);
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    p.rel(ov);
    a.neg(&mut p, &ndy, c);
    p.rel(c);
    let m2: Vec<u64> = lam[..256 - w].iter().map(|&q0| p.hmr(q0)).collect();
    for &q0 in &lam[..256 - w] {
        p.rel(q0);
    }
    // division 2
    let (a2, k2) = emit_f(&mut p, &fc, &x, &ndy);
    a.dirty = [&a2[..255 - w], &ndy[..]].concat();
    a.zl = p.allocn(ZL);
    let (l2, low5, g) = a.product(&mut p, &ndy, &a2[..255], k2.xtop, a2[255], w);
    p.g(&g);
    let cg = a.cneg_list(&l2, k2.par, true, k2.xtop);
    p.g(&cg);
    for i in 0..(256 - w) {
        p.zc(l2[i], m2[i]);
    }
    p.g(&rev(&cg));
    p.g(&rev(&g));
    drop(g);
    for &q0 in &low5 {
        p.rel(q0);
    }
    for i in 0..ZL {
        p.rel(a.zl[i]);
    }
    emit_finv(&mut p, &fc, &x, &ndy, &k2);
    a.dirty = ndy.clone();
    a.cl_add(&mut p, &x, ox, false);
    a.dirty = x.clone();
    a.cl_add(&mut p, &ndy, oy, true);
    // move ndy onto the y register
    let mut cur = ndy.clone();
    for i in 0..256 {
        if cur[i] == y[i] {
            continue;
        }
        for j in (i + 1)..256 {
            if cur[j] == y[i] {
                cur[j] = cur[i];
                break;
            }
        }
        p.g(&[gc(cur[i], y[i]), gc(y[i], cur[i]), gc(cur[i], y[i])]);
        cur[i] = y[i];
    }
    eprintln!("point_add: ops {} peak qubits {}", p.ops.len(), p.next);
    p.ops
}

// armada-a3: nasqret's exact Toffoli-pair fold (submission 6d94a56a, gate_fold.rs, unchanged), generalized in-place
// rounds of the same identities (gate_fold2.rs), then idle-wire product holds (hold_idle.rs, value model of haotang1995's
// hold pass, dca38d60), applied to the finished stream. FOLD_NCT=0: the parent stream; HOLDS=0: folds only;
// HOLDS=1: holds on wires idle over the whole interval only (no relocation).
mod gate_fold;
mod gate_fold2;
mod hold_idle;
// shadow: three exact post-passes from the main-lane tree (files unchanged from main), run before the folds.
#[allow(dead_code)]
mod affine_simplify;
#[allow(dead_code)]
mod cond_pass;
#[allow(dead_code)]
mod quadratic_simplify;
#[allow(dead_code)]
mod truth_simplify;
pub fn build() -> Vec<Op> {
    let mut ops = build_unfolded();
    if std::env::var("FOLD_NCT").as_deref() == Ok("0") {
        return ops;
    }
    let holds = std::env::var("HOLDS").as_deref() != Ok("0");
    let holds_first = std::env::var("HOLDS_FIRST").as_deref() == Ok("1");
    if holds && holds_first {
        let (o, h) = hold_idle::apply(ops);
        eprintln!("HOLD_IDLE holds={h} (before the folds)");
        ops = o;
    }
    ops = affine_simplify::simplify(ops);
    ops = truth_simplify::simplify_products(ops);
    ops = cond_pass::final_cap_cleanup(ops);
    ops = gate_fold::apply(ops);
    let rounds = std::env::var("FOLD2").ok().and_then(|v| v.trim().parse().ok()).unwrap_or(3);
    ops = gate_fold2::apply(ops, rounds);
    if holds && !holds_first {
        let (o, h) = if std::env::var("HOLDS").as_deref() == Ok("1") { hold_idle::apply(ops) } else { hold_idle::apply_reloc(ops) };
        eprintln!("HOLD_IDLE holds={h}");
        ops = o;
    }
    ops
}
