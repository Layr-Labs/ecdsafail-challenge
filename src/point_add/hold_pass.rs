//! Product holds: an unconditional Toffoli that rebuilds, into a |0> target, a product an earlier unconditional
//! Toffoli built into a |0> target (same factor values, proved by an exact symbolic value hash) becomes a CX from a
//! held copy. The copy is taken by CX right after the first Toffoli and cleared by CX from the rebuilt target. A hold
//! is placed only if the live count (provably nonzero wires plus the holds already placed) stays within the qubit cap
//! over its whole interval; the held copies are then mapped onto wires that are provably |0> at the time, moved by
//! SWAP when their owner is touched. Clifford-only edits: no measurement, no approximation.
//! Width for holds is also made by dup loans: a live wire idle over [e, r) whose value (or its complement) another live
//! wire also holds at e and at r is cleared by CX from it at e and rebuilt the same way at r.
//!
//! Values are affine forms over atoms (inputs, measurement outcomes, products of affine forms), stored as a 128-bit
//! random linear hash plus a constant bit; equal forms are equal functions.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
use std::collections::HashMap;

const NONE: usize = usize::MAX;
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Val { l: u128, c: bool }
const ZV: Val = Val { l: 0, c: false };
const ONE: Val = Val { l: 0, c: true };
impl Val {
    fn x(self, o: Val) -> Val { Val { l: self.l ^ o.l, c: self.c ^ o.c } }
    fn not(self) -> Val { Val { l: self.l, c: !self.c } }
}
fn mix(mut z: u64) -> u64 {
    z = z.wrapping_add(0x9E3779B97F4A7C15);
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}
fn mix128(seed: u64, words: &[u64]) -> u128 {
    let (mut a, mut b) = (mix(seed ^ 0x1234_5678), mix(seed ^ 0x8765_4321));
    for &w in words { a = mix(a ^ w); b = mix(b.rotate_left(17) ^ w ^ a); }
    ((a as u128) << 64) | b as u128 | 1
}

/// Symbolic state of all wires and bits.
struct Sym {
    q: Vec<Val>,
    b: Vec<Val>,
    stack: Vec<Val>,
    members: HashMap<u128, Vec<u32>>,
    live: i64,
    atoms: u64,
}
impl Sym {
    fn new(nq: usize, nb: usize, regs: &[Vec<usize>; 4]) -> Self {
        let mut s = Sym { q: vec![ZV; nq], b: vec![ZV; nb], stack: vec![], members: HashMap::new(), live: 0, atoms: 0 };
        for &w in regs[0].iter().chain(regs[1].iter()) { let a = s.fresh(); s.set_q(w, a); }
        for &x in regs[2].iter().chain(regs[3].iter()) { s.b[x] = s.fresh(); }
        s
    }
    fn fresh(&mut self) -> Val { self.atoms += 1; Val { l: mix128(self.atoms, &[0xA70]), c: false } }
    fn prod(&mut self, f: &mut Vec<Val>) -> Val {
        f.retain(|&v| v != ONE);
        if f.iter().any(|&v| v == ZV) { return ZV; }
        f.sort(); f.dedup();
        for i in 1..f.len() { if f[i].l == f[i - 1].l { return ZV; } } // x and !x
        match f.len() {
            0 => ONE,
            1 => f[0],
            _ => {
                let mut words = Vec::with_capacity(3 * f.len());
                for v in f.iter() { words.push(v.l as u64); words.push((v.l >> 64) as u64); words.push(v.c as u64); }
                let p = Val { l: mix128(0xB0D, &words), c: false };
                p
            }
        }
    }
    fn set_q(&mut self, w: usize, v: Val) {
        let old = self.q[w];
        if old == v { return; }
        if old.l != 0 {
            let m = self.members.get_mut(&old.l).unwrap();
            let p = m.iter().position(|&x| x as usize == w).unwrap();
            m.swap_remove(p);
            if m.is_empty() { self.members.remove(&old.l); }
        }
        if v.l != 0 { self.members.entry(v.l).or_default().push(w as u32); }
        if (old != ZV) != (v != ZV) { self.live += if v != ZV { 1 } else { -1 }; }
        self.q[w] = v;
    }
    fn gate(&self, o: &Op) -> Vec<Val> {
        let mut g = self.stack.clone();
        if o.c_condition != NO_BIT && o.kind != K::PushCondition { g.push(self.b[o.c_condition.0 as usize]); }
        g
    }
    fn has_dup(&self, w: usize) -> bool {
        let v = self.q[w];
        v.l != 0 && self.members.get(&v.l).map_or(false, |m| m.len() >= 2)
    }
    /// a live wire other than `w` holding `v` or its complement
    fn source(&self, v: Val, w: usize) -> Option<usize> {
        self.members.get(&v.l)?.iter().map(|&x| x as usize).find(|&x| x != w)
    }
    fn upd(&mut self, w: usize, v: Val, changed: &mut Vec<u128>) {
        let old = self.q[w];
        if old != v { if old.l != 0 { changed.push(old.l); } if v.l != 0 { changed.push(v.l); } }
        self.set_q(w, v);
    }
    /// apply one op; `changed` receives the hashes whose member sets changed
    fn step(&mut self, o: &Op, changed: &mut Vec<u128>) {
        let (t, c1, c2) = (o.q_target.0 as usize, o.q_control1.0 as usize, o.q_control2.0 as usize);
        let mut g = self.gate(o);
        match o.kind {
            K::X => { let d = self.prod(&mut g); let v = self.q[t].x(d); self.upd(t, v, changed); }
            K::CX => { g.push(self.q[c1]); let d = self.prod(&mut g); let v = self.q[t].x(d); self.upd(t, v, changed); }
            K::CCX => { g.push(self.q[c1]); g.push(self.q[c2]); let d = self.prod(&mut g); let v = self.q[t].x(d); self.upd(t, v, changed); }
            K::Swap => {
                g.push(self.q[t].x(self.q[c1]));
                let d = self.prod(&mut g);
                let (vt, vc) = (self.q[t].x(d), self.q[c1].x(d));
                self.upd(t, vt, changed); self.upd(c1, vc, changed);
            }
            K::R | K::Hmr => {
                if o.kind == K::Hmr {
                    let ct = o.c_target.0 as usize;
                    let f = self.fresh();
                    let mut gb = g.clone(); gb.push(self.b[ct].x(f));
                    let d = self.prod(&mut gb);
                    self.b[ct] = self.b[ct].x(d);
                }
                g.push(self.q[t]);
                let d = self.prod(&mut g);
                let v = self.q[t].x(d);
                self.upd(t, v, changed);
            }
            K::BitInvert => { let d = self.prod(&mut g); let ct = o.c_target.0 as usize; self.b[ct] = self.b[ct].x(d); }
            K::BitStore0 => { let ct = o.c_target.0 as usize; g.push(self.b[ct]); let d = self.prod(&mut g); self.b[ct] = self.b[ct].x(d); }
            K::BitStore1 => { let ct = o.c_target.0 as usize; g.push(self.b[ct].not()); let d = self.prod(&mut g); self.b[ct] = self.b[ct].x(d); }
            K::PushCondition => { let v = self.b[o.c_condition.0 as usize]; self.stack.push(v); }
            K::PopCondition => { self.stack.pop(); }
            _ => {}
        }
    }
}

fn dims(ops: &[Op]) -> (usize, usize) {
    let (mut nq, mut nb) = (0, 0);
    for o in ops {
        for x in [o.q_target, o.q_control1, o.q_control2] { if x != NO_QUBIT { nq = nq.max(x.0 as usize + 1); } }
        for x in [o.c_target, o.c_condition] { if x != NO_BIT { nb = nb.max(x.0 as usize + 1); } }
    }
    (nq, nb)
}

/// Condition stack with "dirty" marks: a level is dirty once its bit is written after the push.
struct CondStack { v: Vec<(u64, bool)> }
impl CondStack {
    fn step(&mut self, o: &Op) {
        match o.kind {
            K::PushCondition => self.v.push((o.c_condition.0, false)),
            K::PopCondition => { self.v.pop(); }
            K::Hmr | K::BitInvert | K::BitStore0 | K::BitStore1 => {
                for e in self.v.iter_mut() { if e.0 == o.c_target.0 { e.1 = true; } }
            }
            _ => {}
        }
    }
    fn clean(&self) -> bool { self.v.iter().all(|e| !e.1) }
    fn bits(&self) -> Vec<u64> { self.v.iter().map(|e| e.0).collect() }
}

fn touched(o: &Op) -> ([usize; 3], usize) {
    let mut r = [0usize; 3];
    let mut n = 0;
    if o.kind == K::AppendToRegister { return (r, 0); }
    for x in [o.q_target, o.q_control1, o.q_control2] { if x != NO_QUBIT { r[n] = x.0 as usize; n += 1; } }
    (r, n)
}

fn registers(ops: &[Op]) -> [Vec<usize>; 4] {
    let mut rr: [Vec<usize>; 4] = Default::default();
    for o in ops {
        if o.kind == K::AppendToRegister {
            let r = o.r_target.0 as usize;
            if o.q_target != NO_QUBIT { rr[r].push(o.q_target.0 as usize); } else { rr[r].push(o.c_target.0 as usize); }
        }
    }
    rr
}

fn mk(kind: K, c1: usize, t: usize) -> Op {
    let mut o = Op::empty();
    o.kind = kind;
    if c1 != NONE { o.q_control1 = QubitId(c1 as u64); }
    if t != NONE { o.q_target = QubitId(t as u64); }
    o
}
fn pop() -> Op { mk(K::PopCondition, NONE, NONE) }
fn push(b: u64) -> Op { let mut o = mk(K::PushCondition, NONE, NONE); o.c_condition = BitId(b); o }

/// Map a logical stream whose wires >= `cap` are nomads onto physical wires 0 .. cap - 1. A nomad lives in a slot whose
/// own wire is provably 0 and is moved by SWAP (outside condition blocks, or between a pop and re-push of clean
/// levels) when that wire is touched. Returns None if some op finds no free slot.
pub fn relocate(ops: &[Op], cap: usize) -> Option<Vec<Op>> {
    let (nq, nb) = dims(ops);
    let regs = registers(ops);
    let mut sym = Sym::new(nq, nb, &regs);
    let mut touches: Vec<Vec<u32>> = vec![vec![]; cap];
    for (i, o) in ops.iter().enumerate() { let (tw, n) = touched(o); for &w in &tw[..n] { if w < cap { touches[w].push(i as u32); } } }
    let next = |w: usize, i: usize| -> usize { let v = &touches[w]; let p = v.partition_point(|&x| (x as usize) < i); if p < v.len() { v[p] as usize } else { usize::MAX } };
    let mut host: HashMap<usize, usize> = HashMap::new(); // nomad -> slot
    let mut hosted: Vec<Option<usize>> = vec![None; cap]; // slot -> nomad
    let mut cs = CondStack { v: vec![] };
    let mut out = Vec::with_capacity(ops.len() + 1024);
    let mut ch = vec![];
    let (mut moves, mut fails) = (0usize, 0usize);
    let pick = |sym: &Sym, hosted: &Vec<Option<usize>>, avoid: &[usize], at: usize| -> Option<usize> {
        let mut best: Option<(usize, usize)> = None;
        for p in 0..cap {
            if sym.q[p] != ZV || hosted[p].is_some() || avoid.contains(&p) { continue; }
            let nx = next(p, at);
            if best.map_or(true, |b| nx > b.0) { best = Some((nx, p)); }
        }
        best.map(|b| b.1)
    };
    for (i, o) in ops.iter().enumerate() {
        let (tw, n) = touched(o);
        let tws = &tw[..n];
        for &w in tws {
            if w >= cap { continue; }
            if let Some(nm) = hosted[w] {
                let Some(h2) = pick(&sym, &hosted, tws, i) else { fails += 1; continue };
                let bits = cs.bits();
                if !bits.is_empty() && !cs.clean() { fails += 1; }
                for _ in 0..bits.len() { out.push(pop()); }
                out.push(mk(K::Swap, w, h2));
                for &b in &bits { out.push(push(b)); }
                hosted[w] = None; hosted[h2] = Some(nm); host.insert(nm, h2); moves += 1;
            }
        }
        for &w in tws {
            if w >= cap && !host.contains_key(&w) {
                assert!(sym.q[w] == ZV, "relocate: nomad {w} live without a slot at {i}");
                let Some(h) = pick(&sym, &hosted, tws, i) else { fails += 1; continue };
                host.insert(w, h); hosted[h] = Some(w);
            }
        }
        let mut p = *o;
        if o.kind != K::AppendToRegister {
            let tr = |q: QubitId| if q != NO_QUBIT && q.0 as usize >= cap { QubitId(*host.get(&(q.0 as usize)).unwrap_or(&cap) as u64) } else { q };
            p.q_target = tr(p.q_target); p.q_control1 = tr(p.q_control1); p.q_control2 = tr(p.q_control2);
        }
        out.push(p);
        sym.step(o, &mut ch); ch.clear(); cs.step(o);
        for &w in tws { if w >= cap && sym.q[w] == ZV { if let Some(h) = host.remove(&w) { hosted[h] = None; } } }
    }
    eprintln!("relocate: {moves} moves, {fails} failures");
    if fails > 0 { return None; }
    Some(out)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Loan { w: usize, e: usize, r: usize }

/// Dup-loan windows: (w, e, r), e and r clean boundaries (before op e / op r), w untouched in [e, r) and duplicated by
/// another live wire at both.
fn dup_candidates(ops: &[Op], nq: usize, nb: usize, regs: &[Vec<usize>; 4]) -> Vec<Loan> {
    let mut sym = Sym::new(nq, nb, regs);
    let (mut first, mut last, mut on) = (vec![NONE; nq], vec![NONE; nq], vec![false; nq]);
    let mut pending: Vec<usize> = (0..nq).collect();
    let mut is_pending = vec![true; nq];
    let mut cs = CondStack { v: vec![] };
    let mut lb = NONE;
    let mut out = vec![];
    let mut changed = vec![];
    for (i, o) in ops.iter().enumerate() {
        if cs.clean() {
            for &w in &pending {
                is_pending[w] = false;
                let d = sym.has_dup(w);
                if d && !on[w] { on[w] = true; if first[w] == NONE { first[w] = i; } } else if !d && on[w] { on[w] = false; last[w] = lb; }
            }
            pending.clear();
            lb = i;
        }
        let (tw, n) = touched(o);
        for &w in &tw[..n] {
            if first[w] != NONE {
                let r = if on[w] { lb } else { last[w] };
                if r != NONE && r >= first[w] + 2 { out.push(Loan { w, e: first[w], r }); }
            }
            first[w] = NONE; last[w] = NONE; on[w] = false;
        }
        changed.clear();
        sym.step(o, &mut changed);
        for k in &changed {
            if let Some(m) = sym.members.get(k) {
                for &w in m { let w = w as usize; if !is_pending[w] { is_pending[w] = true; pending.push(w); } }
            }
        }
        for &w in &tw[..n] { if !is_pending[w] { is_pending[w] = true; pending.push(w); } }
        cs.step(o);
    }
    out
}

/// Insert dup loans; loans that find no source (at either end) are returned.
fn insert_loans(ops: &[Op], loans: &[Loan]) -> Result<Vec<Op>, Vec<Loan>> {
    let (nq, nb) = dims(ops);
    let regs = registers(ops);
    let mut ev: HashMap<usize, (Vec<Loan>, Vec<Loan>)> = HashMap::new();
    for l in loans { ev.entry(l.r).or_default().0.push(*l); ev.entry(l.e).or_default().1.push(*l); }
    let mut sym = Sym::new(nq, nb, &regs);
    let mut cs = CondStack { v: vec![] };
    let mut saved: HashMap<usize, Val> = HashMap::new();
    let mut out = Vec::with_capacity(ops.len() + 6 * loans.len());
    let mut ch = vec![];
    let mut failed = vec![];
    for (i, o) in ops.iter().enumerate() {
        if let Some((rs, es)) = ev.get(&i) {
            assert!(cs.clean(), "hold_pass: loan boundary {i} inside a rewritten condition");
            let bits = cs.bits();
            for _ in 0..bits.len() { let p = pop(); out.push(p); sym.step(&p, &mut ch); }
            for l in rs {
                let Some(key) = saved.remove(&l.w) else { continue };
                let Some(u) = sym.source(key, l.w) else { failed.push(*l); sym.set_q(l.w, key); continue };
                let comp = sym.q[u].c != key.c;
                let c = mk(K::CX, u, l.w); out.push(c); sym.step(&c, &mut ch);
                if comp { let x = mk(K::X, NONE, l.w); out.push(x); sym.step(&x, &mut ch); }
                assert!(sym.q[l.w] == key);
            }
            for l in es {
                let key = sym.q[l.w];
                let Some(u) = (if key == ZV { None } else { sym.source(key, l.w) }) else { failed.push(*l); continue };
                saved.insert(l.w, key);
                let comp = sym.q[u].c != key.c;
                let c = mk(K::CX, u, l.w); out.push(c); sym.step(&c, &mut ch);
                if comp { let x = mk(K::X, NONE, l.w); out.push(x); sym.step(&x, &mut ch); }
                assert!(sym.q[l.w] == ZV);
            }
            for &b in &bits { let p = push(b); out.push(p); sym.step(&p, &mut ch); }
            ch.clear();
        }
        out.push(*o); sym.step(o, &mut ch); ch.clear(); cs.step(o);
    }
    if failed.is_empty() { Ok(out) } else { Err(failed) }
}

/// Dup loans (longest first, one window per wire at a time, failing ones dropped), then holds under the stream's own
/// width.
pub fn hold_pass(ops: Vec<Op>) -> Vec<Op> {
    let (nq, nb) = dims(&ops);
    let regs = registers(&ops);
    let mut dcs = dup_candidates(&ops, nq, nb, &regs);
    dcs.sort_by_key(|l| std::cmp::Reverse(l.r - l.e));
    let mut per: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
    let mut chosen = vec![];
    for l in dcs { let v = per.entry(l.w).or_default(); if v.iter().all(|&(a, b)| l.r <= a || l.e >= b) { v.push((l.e, l.r)); chosen.push(l); } }
    let mut banned: std::collections::HashSet<Loan> = std::collections::HashSet::new();
    let mut s1 = None;
    for _ in 0..8 {
        let ls: Vec<Loan> = chosen.iter().filter(|l| !banned.contains(l)).copied().collect();
        match insert_loans(&ops, &ls) {
            Ok(s) => { eprintln!("hold_pass: {} dup loans", ls.len()); s1 = Some(s); break; }
            Err(f) => { for l in f { banned.insert(l); } }
        }
    }
    match s1 { Some(s) => holds(s, nq), None => holds(ops, nq) }
}

fn holds(ops: Vec<Op>, cap: usize) -> Vec<Op> {
    let ops_in = ops.clone();
    let (nq, nb) = dims(&ops);
    let cap = cap as i64;
    let regs = registers(&ops);
    let mut sym = Sym::new(nq, nb, &regs);
    let mut ch = vec![];
    let mut live = vec![0i32; ops.len()];
    for (i, o) in ops.iter().enumerate() { sym.step(o, &mut ch); ch.clear(); live[i] = sym.live as i32; }
    let mut sym = Sym::new(nq, nb, &regs);
    let mut lastp: HashMap<u128, (usize, usize)> = HashMap::new(); // atom -> (op, target)
    let mut cands: Vec<(usize, usize, usize, usize)> = vec![]; // (j, tj, i, ti)
    for (i, o) in ops.iter().enumerate() {
        if o.kind == K::CCX && o.c_condition == NO_BIT && sym.stack.is_empty() {
            let (t, c1, c2) = (o.q_target.0 as usize, o.q_control1.0 as usize, o.q_control2.0 as usize);
            if sym.q[t] == ZV {
                let mut f = sym.gate(o); f.push(sym.q[c1]); f.push(sym.q[c2]);
                let p = sym.prod(&mut f);
                if p.l != 0 {
                    if let Some(&(j, tj)) = lastp.get(&p.l) { cands.push((j, tj, i, t)); }
                    lastp.insert(p.l, (i, t));
                }
            }
        }
        sym.step(o, &mut ch); ch.clear();
    }
    let mut extra = vec![0i32; ops.len() + 1];
    let mut order: Vec<usize> = (0..cands.len()).collect();
    order.sort_by_key(|&k| cands[k].2 - cands[k].0);
    let mut chosen: Vec<(usize, usize, usize, usize, usize)> = vec![];
    for k in order {
        let (j, tj, i, ti) = cands[k];
        if i - j > 2_000_000 { continue; }
        if !(j..=i).all(|x| live[x] + extra[x] + 1 <= cap as i32) { continue; }
        for x in j..=i { extra[x] += 1; }
        chosen.push((j, tj, i, ti, nq + chosen.len()));
    }
    eprintln!("hold_pass: {} candidates, {} holds placed", cands.len(), chosen.len());
    let mut after: HashMap<usize, Vec<Op>> = HashMap::new();
    let mut replace: HashMap<usize, Vec<Op>> = HashMap::new();
    for &(j, tj, i, ti, h) in &chosen {
        let mut c = mk(K::CX, tj, h); c.c_condition = ops[j].c_condition;
        after.entry(j).or_default().push(c);
        let mut a = mk(K::CX, h, ti); a.c_condition = ops[i].c_condition;
        let mut b = mk(K::CX, ti, h); b.c_condition = ops[i].c_condition;
        replace.insert(i, vec![a, b]);
    }
    let mut out = Vec::with_capacity(ops.len() + 3 * chosen.len());
    for (i, o) in ops.into_iter().enumerate() {
        if let Some(r) = replace.get(&i) { out.extend(r.iter().copied()); } else { out.push(o); }
        if let Some(a) = after.get(&i) { out.extend(a.iter().copied()); }
    }
    match relocate(&out, nq) { Some(r) => r, None => { eprintln!("hold_pass: relocation failed, stream unchanged"); ops_in } }
}
