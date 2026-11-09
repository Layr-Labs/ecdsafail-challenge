//! Conjugate a single Toffoli through a bounded affine cone. Merge it with a
//! later Toffoli when the resulting quadratic update has at most one product.
use crate::circuit::{Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
const SET: usize = 8;
const BASIS: usize = 12;
const BLOCK: usize = 16384;
const WINDOW: usize = 48;
#[derive(Clone, Copy)]
struct Group {
    wire: [QubitId; SET],
    len: usize,
}
impl Group {
    fn single(q: QubitId) -> Self {
        let mut w = Self {
            wire: [NO_QUBIT; SET],
            len: 1,
        };
        w.wire[0] = q;
        w
    }
    fn has(&self, q: QubitId) -> bool {
        self.wire[..self.len].contains(&q)
    }
    fn flip(&mut self, q: QubitId) -> bool {
        if let Some(i) = self.wire[..self.len].iter().position(|&k| k == q) {
            self.len -= 1;
            self.wire[i] = self.wire[self.len];
            true
        } else if self.len < SET {
            self.wire[self.len] = q;
            self.len += 1;
            true
        } else {
            false
        }
    }
    fn swap(&mut self, a: QubitId, b: QubitId) {
        let (u, v) = (self.has(a), self.has(b));
        if u != v {
            let (from, to) = if u { (a, b) } else { (b, a) };
            let q = self.wire[..self.len]
                .iter_mut()
                .find(|w| **w == from)
                .unwrap();
            *q = to;
        }
    }
    fn only(&self, w: QubitId) -> bool {
        self.len == 1 && self.wire[0] == w
    }
    fn mask(&self, names: &mut Names) -> Option<u16> {
        let mut m = 0;
        for &w in &self.wire[..self.len] {
            m |= 1 << names.idx(w)?;
        }
        Some(m)
    }
}
struct Names {
    wire: [QubitId; BASIS],
    len: usize,
}
impl Names {
    fn new() -> Self {
        Self {
            wire: [NO_QUBIT; BASIS],
            len: 0,
        }
    }
    fn idx(&mut self, w: QubitId) -> Option<usize> {
        if let Some(i) = self.wire[..self.len].iter().position(|&v| v == w) {
            Some(i)
        } else if self.len == BASIS {
            None
        } else {
            let i = self.len;
            self.wire[i] = w;
            self.len += 1;
            Some(i)
        }
    }
}
struct Gate {
    a: Group,
    b: Group,
    dir: Group,
    sa: bool,
    sb: bool,
    affine: usize,
    spectators: usize,
}
impl Gate {
    fn new(op: Op) -> Self {
        Self {
            a: Group::single(op.q_control1),
            b: Group::single(op.q_control2),
            dir: Group::single(op.q_target),
            sa: false,
            sb: false,
            affine: 0,
            spectators: 0,
        }
    }
    fn through(&mut self, g: Op) -> bool {
        let (t, c, d) = (g.q_target, g.q_control1, g.q_control2);
        let touches_form = |w: QubitId| self.a.has(w) || self.b.has(w);
        let enabled = g.c_condition == NO_BIT;
        match g.kind {
            K::X => {
                let a = self.a.has(t);
                let b = self.b.has(t);
                if !a && !b {
                    return true;
                }
                if !enabled {
                    return false;
                }
                self.sa ^= a;
                self.sb ^= b;
                self.affine += 1;
                true
            }
            K::CX => {
                let a = self.a.has(t);
                let b = self.b.has(t);
                let dir = self.dir.has(c);
                if !a && !b && !dir {
                    return true;
                }
                if !enabled {
                    return false;
                }
                self.affine += 1;
                (!a || self.a.flip(c)) && (!b || self.b.flip(c)) && (!dir || self.dir.flip(t))
            }
            K::Swap => {
                if !touches_form(c) && !touches_form(t) && !self.dir.has(c) && !self.dir.has(t) {
                    return true;
                }
                if !enabled {
                    return false;
                }
                self.a.swap(c, t);
                self.b.swap(c, t);
                self.dir.swap(c, t);
                self.affine += 1;
                true
            }
            K::CCX => !self.dir.has(c) && !self.dir.has(d) && !touches_form(t),
            K::Z => !self.dir.has(t),
            K::CZ => !self.dir.has(c) && !self.dir.has(t),
            K::CCZ => !self.dir.has(c) && !self.dir.has(d) && !self.dir.has(t),
            K::Hmr | K::R => {
                self.spectators += 1;
                !self.dir.has(t) && !touches_form(t)
            }
            K::Neg | K::BitStore0 | K::BitStore1 | K::BitInvert => true,
            K::PushCondition
            | K::PopCondition
            | K::AppendToRegister
            | K::Register
            | K::DebugPrint => false,
        }
    }
}
fn gate(k: K, a: QubitId, b: QubitId, t: QubitId) -> Op {
    Op {
        kind: k,
        q_control2: a,
        q_control1: b,
        q_target: t,
        ..Op::empty()
    }
}
fn cx(a: QubitId, t: QubitId) -> Op {
    gate(K::CX, NO_QUBIT, a, t)
}
fn x(t: QubitId) -> Op {
    gate(K::X, NO_QUBIT, NO_QUBIT, t)
}
fn ccx(a: QubitId, b: QubitId, t: QubitId) -> Op {
    gate(K::CCX, a, b, t)
}
fn nonlinear(a: u16, b: u16, i: usize, j: usize) -> bool {
    (((a >> i) & (b >> j)) ^ ((a >> j) & (b >> i))) & 1 != 0
}
fn correction(out: &mut Vec<Op>, d: &Group, lin: u16, sign: bool, names: &Names) {
    for &target in &d.wire[..d.len] {
        if sign {
            out.push(x(target))
        }
        let mut bits = lin;
        while bits != 0 {
            let j = bits.trailing_zeros() as usize;
            bits &= bits - 1;
            debug_assert_ne!(names.wire[j], target);
            out.push(cx(names.wire[j], target));
        }
    }
}
#[derive(Copy, Clone, Debug, Default)]
pub(super) struct Summary {
    pub savings: u64,
    pub canceled: u64,
    pub factored: u64,
    pub fanout: u64,
    pub affine_crossed: u64,
    pub measurement_crossed: u64,
    pub gates_delta: i64,
    pub limited: u64,
}
fn lower(old: &Gate, new: Op, out: &mut Vec<Op>) -> Option<(usize, bool)> {
    let (a, b, t) = (new.q_control1, new.q_control2, new.q_target);
    let common = old.dir.only(t);
    // The two shears must preserve each other's input predicates.
    if old.a.has(t) || old.b.has(t) || old.dir.has(a) || old.dir.has(b) {
        return None;
    }
    if !old.a.has(a) && !old.a.has(b) && !old.b.has(a) && !old.b.has(b) {
        return None;
    }
    let mut names = Names::new();
    let u = old.a.mask(&mut names)?;
    let v = old.b.mask(&mut names)?;
    let ai = names.idx(a)?;
    let bi = names.idx(b)?;
    let (am, bm) = (1u16 << ai, 1u16 << bi);
    // f_old = uv + sa*v + sb*u + sa*sb, including diagonal Boolean terms.
    let old_linear = (u & v) ^ (if old.sa { v } else { 0 }) ^ (if old.sb { u } else { 0 });
    let old_sign = old.sa && old.sb;
    out.clear();
    if !common {
        // For two distinct output directions, one charged gate can cover both
        // iff their nonzero homogeneous quadratic terms are identical.
        if ((u | v) & !(am | bm)) != 0 || !nonlinear(u, v, ai, bi) {
            return None;
        }
        // a and b are absent from the old difference direction; every affine
        // correction is therefore safe to apply before the product.
        correction(out, &old.dir, old_linear, old_sign, &names);
        let mut directions = old.dir;
        if !directions.flip(t) {
            return None;
        }
        let dest = directions.wire[0];
        for &other in &directions.wire[1..directions.len] {
            out.push(cx(dest, other));
        }
        out.push(ccx(a, b, dest));
        for &other in directions.wire[1..directions.len].iter().rev() {
            out.push(cx(dest, other));
        }
        return Some((1, true));
    }
    // Reconstruct a single product from the off-diagonal coefficient matrix.
    // A nonzero pivot (i,j) gives F=row(j), G=row(i). If rank exceeds two,
    // F wedge G fails the complete coefficient comparison and we keep both gates.
    let mut row = [0u16; BASIS];
    let mut pivot = None;
    for i in 0..names.len {
        for j in i + 1..names.len {
            if nonlinear(u, v, i, j) ^ nonlinear(am, bm, i, j) {
                row[i] |= 1 << j;
                row[j] |= 1 << i;
                if pivot.is_none() {
                    pivot = Some((i, j));
                }
            }
        }
    }
    let Some((i, j)) = pivot else {
        correction(out, &old.dir, old_linear, old_sign, &names);
        return Some((2, false));
    };
    let (f, g) = (row[j], row[i]);
    for k in 0..names.len {
        for l in k + 1..names.len {
            if nonlinear(f, g, k, l) != ((row[k] >> l) & 1 != 0) {
                return None;
            }
        }
    }
    debug_assert!(f & (1 << i) != 0 && f & (1 << j) == 0 && g & (1 << j) != 0 && g & (1 << i) == 0);
    correction(out, &old.dir, old_linear ^ (f & g), old_sign, &names);
    let pos = out.len();
    for (mask, p) in [(f ^ (1 << i), i), (g ^ (1 << j), j)] {
        let mut bits = mask;
        while bits != 0 {
            let w = bits.trailing_zeros() as usize;
            bits &= bits - 1;
            out.push(cx(names.wire[w], names.wire[p]));
        }
    }
    let length = out.len() - pos;
    out.push(ccx(names.wire[i], names.wire[j], t));
    for w in (pos..pos + length).rev() {
        out.push(out[w]);
    }
    Some((1, false))
}
fn scan(
    src: &[Op],
    out: &mut Vec<Op>,
    trial: &mut Vec<Op>,
    best: &mut Vec<Op>,
    mut budget: usize,
    stats: &mut Summary,
) {
    let mut i = 0;
    while i < src.len() {
        let h = src[i];
        if h.kind != K::CCX || h.c_condition != NO_BIT {
            out.push(h);
            i += 1;
            continue;
        }
        let mut state = Gate::new(h);
        let mut chosen = None;
        let mut score = (0usize, 0usize);
        for j in i + 1..src.len().min(i + WINDOW + 1) {
            let g = src[j];
            if g.kind == K::CCX && g.c_condition == NO_BIT {
                if let Some((saved, fan)) = lower(&state, g, trial) {
                    let added = trial.len().saturating_sub(2);
                    if added <= 12 * saved && added <= budget {
                        let priority = (saved, usize::MAX - trial.len());
                        if priority > score {
                            score = priority;
                            chosen = Some((j, saved, fan, state.affine, state.spectators));
                            best.clear();
                            best.extend_from_slice(trial);
                        }
                    } else {
                        stats.limited += 1;
                    }
                }
            }
            if !state.through(g) {
                break;
            }
        }
        if let Some((j, saved, fan, affine, hmr)) = chosen {
            out.extend_from_slice(&src[i + 1..j]);
            out.extend_from_slice(best);
            budget = budget + 2 - best.len();
            stats.savings += saved as u64;
            stats.canceled += u64::from(saved == 2);
            stats.factored += u64::from(saved == 1);
            stats.fanout += u64::from(fan);
            stats.affine_crossed += u64::from(affine > 0);
            stats.measurement_crossed += u64::from(hmr > 0);
            stats.gates_delta += best.len() as i64 - 2;
            i = j + 1;
        } else {
            out.push(h);
            i += 1;
        }
    }
}
pub(super) fn directional(ops: &mut Vec<Op>, reverse: bool) -> Summary {
    let n = ops.len();
    let shape = (ops.as_ptr(), ops.capacity());
    let gap = (ops.capacity() - n)
        .saturating_sub(2)
        .min(n.div_ceil(64))
        .min(1 << 24);
    let storage = n + gap;
    if gap != 0 {
        ops.resize(storage, Op::empty());
        if !reverse {
            ops.copy_within(0..n, gap);
        }
    }
    let mut orig = Vec::with_capacity(BLOCK);
    let mut out = Vec::with_capacity(2 * BLOCK);
    let (mut trial, mut best) = (Vec::with_capacity(64), Vec::with_capacity(64));
    let mut stats = Summary::default();
    let mut write = 0;
    for start in (0..n).step_by(BLOCK) {
        let end = (start + BLOCK).min(n);
        orig.clear();
        out.clear();
        if reverse {
            orig.extend(ops[n - end..n - start].iter().rev().copied());
        } else {
            orig.extend_from_slice(&ops[gap + start..gap + end]);
        }
        let available = (1024 + ((gap as u128) * (end as u128) / (n as u128)) as usize).min(gap);
        scan(
            &orig,
            &mut out,
            &mut trial,
            &mut best,
            start + available - write,
            &mut stats,
        );
        assert!(write + out.len() <= end + available);
        if reverse {
            out.reverse();
            let hi = storage - write;
            ops[hi - out.len()..hi].copy_from_slice(&out);
        } else {
            ops[write..write + out.len()].copy_from_slice(&out);
        }
        write += out.len();
    }
    if reverse && write != storage {
        ops.copy_within(storage - write..storage, 0);
    }
    ops.truncate(write);
    assert_eq!(shape, (ops.as_ptr(), ops.capacity()));
    stats
}
