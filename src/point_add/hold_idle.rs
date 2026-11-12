//! Idle-wire product holds (armada-a3). An unconditional Toffoli that rebuilds, into a |0> target, a product that an
//! earlier unconditional Toffoli built into a |0> target (same factor values, by the exact symbolic value model of
//! haotang1995's hold pass, submission dca38d60, as used in gnuchev-band rows) becomes two CNOTs from a held copy:
//! CX(t_j -> w) right after the first Toffoli, and at the rebuild CX(w -> t_i), CX(t_i -> w). The copy lives on a
//! physical wire w that is provably |0> and untouched by every other instruction over the whole interval, so the
//! qubit count (max wire index + 1) never changes and no relocation is needed. No measurement, no approximation:
//! for every computational-basis path and every measurement record the rewritten stream performs the same map.
//! HOLDS=0 disables the pass.
#![allow(dead_code, unused_imports)]
use crate::circuit::{BitId, Op, OperationType as K, QubitId, NO_BIT, NO_QUBIT};
use std::collections::HashMap;

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

const ZB: u32 = 1 << 31;

fn mk(kind: K, c1: usize, t: usize) -> Op {
    let mut o = Op::empty();
    o.kind = kind;
    o.q_control1 = QubitId(c1 as u64);
    o.q_target = QubitId(t as u64);
    o
}

/// Returns the rewritten stream and the number of holds placed.
pub fn apply(mut ops: Vec<Op>) -> (Vec<Op>, usize) {
    let n = ops.len();
    assert!(n < ZB as usize, "hold_idle: stream too long for u32 indices");
    let (nq, nb) = dims(&ops);
    let regs = registers(&ops);
    let input: Vec<bool> = {
        let mut v = vec![false; nq];
        for &w in regs[0].iter().chain(regs[1].iter()) { v[w] = true; }
        v
    };
    // pass 1: values, per-wire touch lists (bit 31: |0> after the touch), hold candidates
    let mut touches: Vec<Vec<u32>> = vec![vec![]; nq];
    let mut cands: Vec<(u32, u32)> = vec![];
    {
        let mut sym = Sym::new(nq, nb, &regs);
        let mut lastp: HashMap<(u128, bool), u32> = HashMap::new();
        let mut ch = vec![];
        for (i, o) in ops.iter().enumerate() {
            if o.kind == K::CCX && o.c_condition == NO_BIT && sym.stack.is_empty() {
                let (t, c1, c2) = (o.q_target.0 as usize, o.q_control1.0 as usize, o.q_control2.0 as usize);
                if sym.q[t] == ZV {
                    let mut f = sym.gate(o);
                    f.push(sym.q[c1]);
                    f.push(sym.q[c2]);
                    let p = sym.prod(&mut f);
                    if p.l != 0 {
                        if let Some(&j) = lastp.get(&(p.l, p.c)) { cands.push((j, i as u32)); }
                        lastp.insert((p.l, p.c), i as u32);
                    }
                }
            }
            sym.step(o, &mut ch);
            ch.clear();
            let (tw, k) = touched(o);
            for &w in &tw[..k] {
                let z = if sym.q[w] == ZV { ZB } else { 0 };
                let v = &mut touches[w];
                match v.last_mut() {
                    Some(x) if *x & !ZB == i as u32 => *x = i as u32 | z,
                    _ => v.push(i as u32 | z),
                }
            }
        }
    }
    cands.sort_unstable();
    // pass 2: sweep; free = wires |0> after their last touch, keyed by their next touch; best fit per candidate
    let next_of = |touches: &Vec<Vec<u32>>, w: usize, c: usize| -> u32 {
        let k = if c == usize::MAX { 0 } else { c + 1 };
        touches[w].get(k).map_or(u32::MAX, |&x| x & !ZB)
    };
    let mut cursor = vec![usize::MAX; nq];
    let mut free: std::collections::BTreeSet<(u32, u32)> = std::collections::BTreeSet::new();
    for w in 0..nq {
        if !input[w] { free.insert((next_of(&touches, w, usize::MAX), w as u32)); }
    }
    let mut reserved: std::collections::BinaryHeap<std::cmp::Reverse<(u32, u32)>> = Default::default();
    let mut is_res = vec![false; nq];
    let mut chosen: Vec<(u32, u32, u32)> = vec![]; // (j, i, w)
    let mut ci = 0usize;
    for (i, o) in ops.iter().enumerate() {
        let i = i as u32;
        while let Some(&std::cmp::Reverse((e, w))) = reserved.peek() {
            if e >= i { break; }
            reserved.pop();
            let w = w as usize;
            is_res[w] = false;
            let c = cursor[w];
            let zero = if c == usize::MAX { !input[w] } else { touches[w][c] & ZB != 0 };
            if zero { free.insert((next_of(&touches, w, c), w as u32)); }
        }
        let (tw, k) = touched(o);
        for &w in &tw[..k] {
            let c = cursor[w];
            if c != usize::MAX && touches[w][c] & !ZB == i { continue; }
            assert!(!is_res[w], "hold_idle: reserved wire {w} touched at {i}");
            free.remove(&(next_of(&touches, w, c), w as u32));
            let nc = if c == usize::MAX { 0 } else { c + 1 };
            cursor[w] = nc;
            if touches[w][nc] & ZB != 0 { free.insert((next_of(&touches, w, nc), w as u32)); }
        }
        while ci < cands.len() && cands[ci].0 == i {
            let e = cands[ci].1;
            ci += 1;
            if let Some(&(nt, w)) = free.range((e + 1, 0u32)..).next() {
                free.remove(&(nt, w));
                is_res[w as usize] = true;
                reserved.push(std::cmp::Reverse((e, w)));
                chosen.push((i, e, w));
            }
        }
    }
    drop(touches);
    if let Some(m) = std::env::var("HOLDS_MAX").ok().and_then(|v| v.parse::<usize>().ok()) { chosen.truncate(m); }
    let holds = chosen.len();
    if holds == 0 { return (ops, 0); }
    // pass 3: in place. after[j]: CX(t_j -> w); at i: CX(w -> t_i), CX(t_i -> w) instead of the Toffoli.
    let mut after: Vec<(u32, u32)> = chosen.iter().map(|&(j, _, w)| (j, w)).collect();
    let mut at: Vec<(u32, u32)> = chosen.iter().map(|&(_, i, w)| (i, w)).collect();
    after.sort_unstable();
    at.sort_unstable();
    let gap = 2 * holds;
    if gap > ops.capacity() - n { ops.reserve_exact(gap); }
    ops.resize(n + gap, Op::empty());
    ops.copy_within(0..n, gap);
    let (mut a, mut b, mut wr) = (0usize, 0usize, 0usize);
    for i in 0..n {
        let o = ops[gap + i];
        if b < at.len() && at[b].0 as usize == i {
            let w = at[b].1 as usize;
            assert!(o.kind == K::CCX && o.c_condition == NO_BIT);
            let t = o.q_target.0 as usize;
            ops[wr] = mk(K::CX, w, t);
            ops[wr + 1] = mk(K::CX, t, w);
            wr += 2;
            b += 1;
        } else {
            ops[wr] = o;
            wr += 1;
        }
        while a < after.len() && after[a].0 as usize == i {
            ops[wr] = mk(K::CX, o.q_target.0 as usize, after[a].1 as usize);
            wr += 1;
            a += 1;
        }
        debug_assert!(wr <= gap + i + 1);
    }
    assert_eq!(wr, n + 2 * holds);
    ops.truncate(wr);
    (ops, holds)
}
