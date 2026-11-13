//! Product holds: an unconditional or cleanly-conditioned Toffoli that rebuilds, into a |0> or |1> target, a product
//! an earlier Toffoli built (or uncomputed) becomes a CX sequence from a held copy. The held copies are mapped onto
//! wires that are provably |0> at the time, moved by SWAP when their owner is touched. Clifford-only edits: no
//! measurement, no approximation.
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
use std::collections::{HashMap, HashSet};

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
                Val { l: mix128(0xB0D, &words), c: false }
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
    /// a live wire other than `w`, `c1`, `c2` holding `v` or its complement
    fn source_excluding(&self, v: Val, w: usize, c1: usize, c2: usize) -> Option<usize> {
        self.members.get(&v.l)?.iter().map(|&x| x as usize).find(|&x| x != w && x != c1 && x != c2)
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
fn mk_ccx(c1: usize, c2: usize, t: usize) -> Op {
    let mut o = Op::empty();
    o.kind = K::CCX;
    o.q_control1 = QubitId(c1 as u64);
    o.q_control2 = QubitId(c2 as u64);
    o.q_target = QubitId(t as u64);
    o
}
fn pop() -> Op { mk(K::PopCondition, NONE, NONE) }
fn push(b: u64) -> Op { let mut o = mk(K::PushCondition, NONE, NONE); o.c_condition = BitId(b); o }

/// Map a logical stream whose wires >= `cap` are nomads onto physical wires 0 .. cap - 1. A nomad lives in a slot whose
/// own wire is provably 0 and is moved by SWAP (outside condition blocks, or between a pop and re-push of clean
/// levels) when that wire is touched. Returns Err(failed_nomads) if some op finds no free slot or hits a dirty condition.
pub fn relocate_checked(ops: &[Op], cap: usize) -> Result<Vec<Op>, Vec<usize>> {
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
    let mut moves = 0usize;
    let mut failed_nomads: Vec<usize> = vec![];
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
                let Some(h2) = pick(&sym, &hosted, tws, i) else { failed_nomads.push(nm); continue };
                let bits = cs.bits();
                if !bits.is_empty() && !cs.clean() { failed_nomads.push(nm); }
                for _ in 0..bits.len() { out.push(pop()); }
                out.push(mk(K::Swap, w, h2));
                for &b in &bits { out.push(push(b)); }
                hosted[w] = None; hosted[h2] = Some(nm); host.insert(nm, h2); moves += 1;
            }
        }
        for &w in tws {
            if w >= cap && !host.contains_key(&w) {
                if sym.q[w] != ZV { failed_nomads.push(w); continue; }
                let Some(h) = pick(&sym, &hosted, tws, i) else { failed_nomads.push(w); continue };
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
    eprintln!("relocate: {moves} moves, {} failures", failed_nomads.len());
    if !failed_nomads.is_empty() {
        failed_nomads.sort_unstable();
        failed_nomads.dedup();
        return Err(failed_nomads);
    }
    Ok(out)
}

pub fn relocate(ops: &[Op], cap: usize) -> Option<Vec<Op>> {
    relocate_checked(ops, cap).ok()
}

/// Replace any cleanly-conditioned or unconditional CCX whose full effective product (including condition bits) is
/// already held on another live wire (or is constant 0/1) with an unconditional CX / X (wrapped in Pop/Push if inside
/// a clean PushCondition block). Zero extra width, zero nomads.
fn direct_copy_pass(ops: Vec<Op>) -> Vec<Op> {
    let (nq, nb) = dims(&ops);
    let regs = registers(&ops);
    let mut sym = Sym::new(nq, nb, &regs);
    let mut cs = CondStack { v: vec![] };
    let mut ch = vec![];
    let mut out = Vec::with_capacity(ops.len());
    let mut direct_hits = 0usize;
    for o in ops {
        if o.kind == K::CCX && cs.clean() {
            let (t, c1, c2) = (o.q_target.0 as usize, o.q_control1.0 as usize, o.q_control2.0 as usize);
            let mut f = sym.gate(&o);
            f.push(sym.q[c1]);
            f.push(sym.q[c2]);
            let d = sym.prod(&mut f);
            let bits = cs.bits();
            if d == ZV {
                direct_hits += 1;
                continue;
            } else if d == ONE {
                for _ in 0..bits.len() { let p = pop(); out.push(p); sym.step(&p, &mut ch); }
                let x = mk(K::X, NONE, t);
                out.push(x);
                sym.step(&x, &mut ch);
                for &b in &bits { let p = push(b); out.push(p); sym.step(&p, &mut ch); }
                ch.clear();
                direct_hits += 1;
                continue;
            } else if let Some(u) = sym.source_excluding(d, t, c1, c2) {
                let comp = sym.q[u].c != d.c;
                for _ in 0..bits.len() { let p = pop(); out.push(p); sym.step(&p, &mut ch); }
                let cx = mk(K::CX, u, t);
                out.push(cx);
                sym.step(&cx, &mut ch);
                if comp {
                    let x = mk(K::X, NONE, t);
                    out.push(x);
                    sym.step(&x, &mut ch);
                }
                for &b in &bits { let p = push(b); out.push(p); sym.step(&p, &mut ch); }
                ch.clear();
                direct_hits += 1;
                continue;
            }
        }
        out.push(o);
        sym.step(&o, &mut ch);
        ch.clear();
        cs.step(&o);
    }
    if direct_hits > 0 {
        eprintln!("hold_pass: {direct_hits} direct live-wire CCX eliminations");
    }
    out
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Loan { w: usize, e: usize, r: usize }

/// Dup-loan windows: (w, e, r), e and r clean boundaries (before op e / op r), w untouched in [e, r) and duplicated by
/// another live wire (or holding ONE) at both.
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
                let Some(u) = (if key.l == 0 { None } else { sym.source(key, l.w) }) else { failed.push(*l); continue };
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

/// Direct live-wire copy, then dup loans (longest first, one window per wire at a time, failing ones dropped), then
/// uncompute-to-compute bridges and compute-to-compute holds under the stream's own width.
pub fn hold_pass(ops: Vec<Op>) -> Vec<Op> {
    let ops = direct_copy_pass(ops);
    let (nq, nb) = dims(&ops);
    let regs = registers(&ops);
    let mut dcs = dup_candidates(&ops, nq, nb, &regs);
    dcs.sort_by_key(|l| std::cmp::Reverse(l.r - l.e));
    let mut per: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
    let mut chosen = vec![];
    for l in dcs { let v = per.entry(l.w).or_default(); if v.iter().all(|&(a, b)| l.r <= a || l.e >= b) { v.push((l.e, l.r)); chosen.push(l); } }
    let mut banned: HashSet<Loan> = HashSet::new();
    let mut s1 = None;
    for _ in 0..8 {
        let ls: Vec<Loan> = chosen.iter().filter(|l| !banned.contains(l)).copied().collect();
        match insert_loans(&ops, &ls) {
            Ok(s) => { eprintln!("hold_pass: {} dup loans", ls.len()); s1 = Some(s); break; }
            Err(f) => { for l in f { banned.insert(l); } }
        }
    }
    let out = match s1 { Some(s) => holds(s, nq), None => holds(ops, nq) };
    direct_copy_pass(out)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StartKind {
    CopyAfter,
    Uncompute,
    Dirty { c1: usize, c2: usize, d_c: bool },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EndKind {
    Clean,
    Dirty { c1: usize, c2: usize, d_c: bool },
}

#[derive(Clone, Copy, Debug)]
struct Cand {
    j: usize,
    tj: usize,
    start_kind: StartKind,
    j_c_before: bool,
    j_c_after: bool,
    i: usize,
    ti: usize,
    end_kind: EndKind,
    i_c_before: bool,
    i_c_after: bool,
    prod_l: u128,
    q_weight: u32, // quarter-Toffolis saved
}

#[derive(Clone, Copy, Debug)]
struct ChosenHold {
    cand_idx: usize,
    nomad: usize,
}

fn quarter_toffoli_weight(stack_depth: usize, has_cc: bool) -> u32 {
    let d = stack_depth + usize::from(has_cc);
    match d {
        0 => 4,
        1 => 2,
        2 => 1,
        _ => 1,
    }
}

fn wrap_cond(inner: Vec<Op>, bits: &[u64]) -> Vec<Op> {
    if bits.is_empty() {
        return inner;
    }
    let mut v = Vec::with_capacity(inner.len() + 2 * bits.len());
    for _ in 0..bits.len() { v.push(pop()); }
    v.extend(inner);
    for &b in bits { v.push(push(b)); }
    v
}

fn holds(ops: Vec<Op>, cap: usize) -> Vec<Op> {
    let ops_in = ops.clone();
    let (nq, nb) = dims(&ops);
    let regs = registers(&ops);
    let mut sym = Sym::new(nq, nb, &regs);
    let mut ch = vec![];
    let mut live = vec![0i32; ops.len()];
    for (i, o) in ops.iter().enumerate() { sym.step(o, &mut ch); ch.clear(); live[i] = sym.live as i32; }

    let mut sym = Sym::new(nq, nb, &regs);
    let mut cs = CondStack { v: vec![] };
    const K_HIST: usize = 4;
    // (op_idx, wire, c_before, c_after, q_weight)
    let mut last_unc: HashMap<u128, Vec<(usize, usize, bool, bool, u32)>> = HashMap::new();
    let mut last_comp: HashMap<u128, Vec<(usize, usize, bool, bool, u32)>> = HashMap::new();
    // (op_idx, wire, c1, c2, d_c)
    let mut last_dirty: HashMap<u128, Vec<(usize, usize, usize, usize, bool)>> = HashMap::new();
    // (op_idx, wire, d_c, q_weight)
    let mut all_ccx_by_prod: HashMap<u128, Vec<(usize, usize, bool, u32)>> = HashMap::new();
    let mut cond_bits_at: HashMap<usize, Vec<u64>> = HashMap::new();
    let mut cands: Vec<Cand> = vec![];
    let mut born_at: Vec<usize> = vec![0; nq];
    let mut last_top_idx: usize = 0;

    let piggy_weight = |sites: &[(usize, usize, bool, u32)], j: usize, i: usize| -> u32 {
        let lo = sites.partition_point(|&(idx, _, _, _)| idx <= j);
        let hi = sites.partition_point(|&(idx, _, _, _)| idx < i);
        sites[lo..hi].iter().map(|&(_, _, _, qw)| qw).sum()
    };

    for (i, o) in ops.iter().enumerate() {
        if o.kind == K::CCX && cs.clean() {
            let (t, c1, c2) = (o.q_target.0 as usize, o.q_control1.0 as usize, o.q_control2.0 as usize);
            let uncond = sym.stack.is_empty() && o.c_condition == NO_BIT;
            let mut f = sym.gate(o);
            f.push(sym.q[c1]);
            f.push(sym.q[c2]);
            let d = sym.prod(&mut f);
            if d.l != 0 && (!d.c || uncond) {
                let v_before = sym.q[t];
                let v_after = v_before.x(d);
                let qw_i = quarter_toffoli_weight(sym.stack.len(), o.c_condition != NO_BIT);
                if !cs.v.is_empty() {
                    cond_bits_at.insert(i, cs.bits());
                }
                let sites = all_ccx_by_prod.entry(d.l).or_default();
                sites.push((i, t, d.c, qw_i));
                if v_before.l == 0 {
                    // Op i is a Clean Compute into |0> or |1>
                    if let Some(uncs) = last_unc.get(&d.l) {
                        for &(j, tj, jc_bef, jc_aft, qw_j) in uncs.iter().rev() {
                            cands.push(Cand {
                                j, tj, start_kind: StartKind::Uncompute, j_c_before: jc_bef, j_c_after: jc_aft,
                                i, ti: t, end_kind: EndKind::Clean, i_c_before: v_before.c, i_c_after: v_after.c,
                                prod_l: d.l, q_weight: qw_j + qw_i,
                            });
                        }
                    }
                    if let Some(comps) = last_comp.get(&d.l) {
                        for &(j, tj, jc_bef, jc_aft, _qw_j) in comps.iter().rev() {
                            cands.push(Cand {
                                j, tj, start_kind: StartKind::CopyAfter, j_c_before: jc_bef, j_c_after: jc_aft,
                                i, ti: t, end_kind: EndKind::Clean, i_c_before: v_before.c, i_c_after: v_after.c,
                                prod_l: d.l, q_weight: qw_i,
                            });
                        }
                    }
                    if let Some(dirties) = last_dirty.get(&d.l) {
                        for &(j, tj, jc1, jc2, jd_c) in dirties.iter().rev() {
                            cands.push(Cand {
                                j, tj, start_kind: StartKind::Dirty { c1: jc1, c2: jc2, d_c: jd_c },
                                j_c_before: false, j_c_after: false,
                                i, ti: t, end_kind: EndKind::Clean, i_c_before: v_before.c, i_c_after: v_after.c,
                                prod_l: d.l, q_weight: qw_i,
                            });
                        }
                    }
                    let v = last_comp.entry(d.l).or_default();
                    if v.len() >= K_HIST { v.remove(0); }
                    v.push((i, t, v_before.c, v_after.c, qw_i));
                } else {
                    // Op i is either an Uncompute (v_before.l == d.l) or a Dirty Accumulator CCX (v_before.l != d.l)
                    if uncond {
                        if let Some(uncs) = last_unc.get(&d.l) {
                            for &(j, tj, jc_bef, jc_aft, qw_j) in uncs.iter().rev() {
                                cands.push(Cand {
                                    j, tj, start_kind: StartKind::Uncompute, j_c_before: jc_bef, j_c_after: jc_aft,
                                    i, ti: t, end_kind: EndKind::Dirty { c1, c2, d_c: d.c },
                                    i_c_before: v_before.c, i_c_after: v_after.c,
                                    prod_l: d.l, q_weight: qw_j,
                                });
                            }
                        }
                        if let Some(comps) = last_comp.get(&d.l) {
                            for &(j, tj, jc_bef, jc_aft, _qw_j) in comps.iter().rev() {
                                let pw = piggy_weight(sites, j, i);
                                if pw > 0 {
                                    cands.push(Cand {
                                        j, tj, start_kind: StartKind::CopyAfter, j_c_before: jc_bef, j_c_after: jc_aft,
                                        i, ti: t, end_kind: EndKind::Dirty { c1, c2, d_c: d.c },
                                        i_c_before: v_before.c, i_c_after: v_after.c,
                                        prod_l: d.l, q_weight: pw,
                                    });
                                }
                            }
                        }
                        if let Some(dirties) = last_dirty.get(&d.l) {
                            for &(j, tj, jc1, jc2, jd_c) in dirties.iter().rev() {
                                let pw = piggy_weight(sites, j, i);
                                if pw > 0 {
                                    cands.push(Cand {
                                        j, tj, start_kind: StartKind::Dirty { c1: jc1, c2: jc2, d_c: jd_c },
                                        j_c_before: false, j_c_after: false,
                                        i, ti: t, end_kind: EndKind::Dirty { c1, c2, d_c: d.c },
                                        i_c_before: v_before.c, i_c_after: v_after.c,
                                        prod_l: d.l, q_weight: pw,
                                    });
                                }
                            }
                        }
                    }
                    if v_before.l == d.l {
                        // Op i is an Uncompute of d.l from t (leaving t at |0> or |1>)
                        let v = last_unc.entry(d.l).or_default();
                        if v.len() >= K_HIST { v.remove(0); }
                        v.push((i, t, v_before.c, v_after.c, qw_i));
                    } else if uncond {
                        let v = last_dirty.entry(d.l).or_default();
                        if v.len() >= K_HIST { v.remove(0); }
                        v.push((i, t, c1, c2, d.c));
                    }
                }
            }
        }
        let (tw, n) = touched(o);
        let mut prev_q = [(0usize, ZV); 3];
        for idx in 0..n {
            let w = tw[idx];
            prev_q[idx] = (w, sym.q[w]);
        }
        sym.step(o, &mut ch);
        ch.clear();
        cs.step(o);
        for idx in 0..n {
            let (w, old_v) = prev_q[idx];
            if sym.q[w] != old_v {
                if old_v.l != 0 && last_top_idx > born_at[w] {
                    let v = last_comp.entry(old_v.l).or_default();
                    if let Some(last_entry) = v.last_mut() {
                        if last_entry.0 == born_at[w] && last_entry.1 == w {
                            *last_entry = (last_top_idx, w, false, old_v.c, last_entry.4);
                        } else if last_entry.0 < last_top_idx {
                            if v.len() >= K_HIST { v.remove(0); }
                            v.push((last_top_idx, w, false, old_v.c, 4));
                        }
                    } else {
                        v.push((last_top_idx, w, false, old_v.c, 4));
                    }
                }
                born_at[w] = i;
            }
        }
        if sym.stack.is_empty() {
            last_top_idx = i;
        }
    }

    // Prioritize lowest span-per-Toffoli-saved first.
    let mut order: Vec<usize> = (0..cands.len()).collect();
    order.sort_by_key(|&k| {
        let c = &cands[k];
        let eff_span = ((c.i - c.j) * 4) / (c.q_weight.max(1) as usize);
        (eff_span, std::cmp::Reverse(c.q_weight))
    });

    let mut banned_cands: HashSet<usize> = HashSet::new();
    for attempt in 0..8 {
        let mut extra = vec![0i32; ops.len() + 1];
        let mut used_replace: HashSet<usize> = HashSet::new();
        let mut chosen: Vec<(ChosenHold, Vec<(usize, usize, bool)>)> = vec![];
        let mut bridges_placed = 0usize;
        let mut holds_placed = 0usize;
        let mut dirty_placed = 0usize;
        let mut piggybacked = 0usize;

        for &k in &order {
            if banned_cands.contains(&k) { continue; }
            let c = cands[k];
            if c.i - c.j > 4_000_000 { continue; }
            if used_replace.contains(&c.i) { continue; }
            if !matches!(c.start_kind, StartKind::CopyAfter) && used_replace.contains(&c.j) { continue; }
            // Check available intermediate piggyback sites in (c.j, c.i)
            let mut m_list: Vec<(usize, usize, bool)> = Vec::new();
            if let Some(sites) = all_ccx_by_prod.get(&c.prod_l) {
                let lo = sites.partition_point(|&(idx, _, _, _)| idx <= c.j);
                let hi = sites.partition_point(|&(idx, _, _, _)| idx < c.i);
                for &(m_idx, tm, d_c, _qw) in &sites[lo..hi] {
                    if !used_replace.contains(&m_idx) {
                        m_list.push((m_idx, tm, d_c));
                    }
                }
            }
            if !matches!(c.start_kind, StartKind::Uncompute) && matches!(c.end_kind, EndKind::Dirty { .. }) && m_list.is_empty() {
                continue;
            }
            let start = if !matches!(c.start_kind, StartKind::CopyAfter) { c.j.saturating_sub(1) } else { c.j };
            if !(start..=c.i).all(|x| live[x] + extra[x] + 1 <= cap as i32) { continue; }
            for x in start..=c.i { extra[x] += 1; }
            used_replace.insert(c.i);
            if !matches!(c.start_kind, StartKind::CopyAfter) {
                used_replace.insert(c.j);
            }
            for &(m_idx, _, _) in &m_list {
                used_replace.insert(m_idx);
            }
            piggybacked += m_list.len();
            match (c.start_kind, c.end_kind) {
                (StartKind::Uncompute, EndKind::Clean) => bridges_placed += 1,
                (StartKind::CopyAfter, EndKind::Clean) => holds_placed += 1,
                _ => dirty_placed += 1,
            }
            let nomad = nq + chosen.len();
            chosen.push((ChosenHold { cand_idx: k, nomad }, m_list));
        }

        let mut after: HashMap<usize, Vec<Op>> = HashMap::new();
        let mut replace: HashMap<usize, Vec<Op>> = HashMap::new();
        let empty_bits: Vec<u64> = Vec::new();

        for (ch_hold, m_list) in &chosen {
            let c = cands[ch_hold.cand_idx];
            let h = ch_hold.nomad;
            let bits_j = cond_bits_at.get(&c.j).unwrap_or(&empty_bits);
            let bits_i = cond_bits_at.get(&c.i).unwrap_or(&empty_bits);
            match c.start_kind {
                StartKind::Uncompute => {
                    let mut rj = Vec::with_capacity(4);
                    if c.j_c_before { rj.push(mk(K::X, NONE, c.tj)); }
                    rj.push(mk(K::CX, c.tj, h));
                    rj.push(mk(K::CX, h, c.tj));
                    if c.j_c_after { rj.push(mk(K::X, NONE, c.tj)); }
                    replace.insert(c.j, wrap_cond(rj, bits_j));
                }
                StartKind::CopyAfter => {
                    let mut aj = Vec::with_capacity(2);
                    aj.push(mk(K::CX, c.tj, h));
                    if c.j_c_after { aj.push(mk(K::X, NONE, h)); }
                    after.entry(c.j).or_default().extend(wrap_cond(aj, bits_j));
                }
                StartKind::Dirty { c1, c2, d_c } => {
                    let mut rj = Vec::with_capacity(3);
                    rj.push(mk_ccx(c1, c2, h));
                    rj.push(mk(K::CX, h, c.tj));
                    if d_c { rj.push(mk(K::X, NONE, h)); }
                    replace.insert(c.j, rj);
                }
            }
            match c.end_kind {
                EndKind::Clean => {
                    let mut ri = Vec::with_capacity(4);
                    ri.push(mk(K::CX, h, c.ti));
                    if c.i_c_before { ri.push(mk(K::X, NONE, c.ti)); }
                    ri.push(mk(K::CX, c.ti, h));
                    if c.i_c_after { ri.push(mk(K::X, NONE, c.ti)); }
                    replace.insert(c.i, wrap_cond(ri, bits_i));
                }
                EndKind::Dirty { c1, c2, d_c } => {
                    let mut ri = Vec::with_capacity(3);
                    if d_c { ri.push(mk(K::X, NONE, h)); }
                    ri.push(mk(K::CX, h, c.ti));
                    ri.push(mk_ccx(c1, c2, h));
                    replace.insert(c.i, ri);
                }
            }

            for &(m_idx, tm, d_c) in m_list {
                let bits_m = cond_bits_at.get(&m_idx).unwrap_or(&empty_bits);
                let mut rm = vec![mk(K::CX, h, tm)];
                if d_c { rm.push(mk(K::X, NONE, tm)); }
                replace.insert(m_idx, wrap_cond(rm, bits_m));
            }
        }

        eprintln!(
            "hold_pass[attempt {attempt}]: {} cands -> {bridges_placed} bridges + {holds_placed} holds + {dirty_placed} dirty + {piggybacked} piggybacked",
            cands.len()
        );

        let mut out = Vec::with_capacity(ops.len() + 3 * chosen.len());
        for (i, o) in ops.iter().copied().enumerate() {
            if let Some(r) = replace.get(&i) { out.extend(r.iter().copied()); } else { out.push(o); }
            if let Some(a) = after.get(&i) { out.extend(a.iter().copied()); }
        }
        match relocate_checked(&out, nq) {
            Ok(r) => return r,
            Err(bad_nomads) => {
                for nm in bad_nomads {
                    if nm >= nq && nm - nq < chosen.len() {
                        banned_cands.insert(chosen[nm - nq].0.cand_idx);
                    }
                }
            }
        }
    }
    eprintln!("hold_pass: relocation failed after retries, stream unchanged");
    ops_in
}
