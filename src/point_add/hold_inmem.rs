//! Idle-wire product holds (armada-a3). An unconditional Toffoli that rebuilds, into a |0> target, a product that an
//! earlier unconditional Toffoli built into a |0> target (same factor values, by the exact symbolic value model of
//! haotang1995's hold pass, submission dca38d60, as used in gnuchev-band rows) becomes two CNOTs from a held copy:
//! CX(t_j -> w) right after the first Toffoli, and at the rebuild CX(w -> t_i), CX(t_i -> w). The copy lives on a
//! physical wire w that is provably |0> and untouched by every other instruction over the whole interval, so no
//! relocation is needed. The wires are the stream's own idle wires plus HOLD_EXTRA_WIRES extra always-zero wires above the
//! builder's highest id: the printed qubit count (max wire index + 1) is the builder's width plus the number of extra wires
//! the pass actually uses (all of them in the measured build). No measurement, no approximation:
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
    (nq + HOLD_EXTRA_WIRES, nb)
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

fn pop() -> Op { let mut o = Op::empty(); o.kind = K::PopCondition; o }
fn push(b: u64) -> Op { let mut o = Op::empty(); o.kind = K::PushCondition; o.c_condition = BitId(b); o }

fn mk(kind: K, c1: usize, t: usize) -> Op {
    let mut o = Op::empty();
    o.kind = kind;
    o.q_control1 = QubitId(c1 as u64);
    o.q_target = QubitId(t as u64);
    o
}


// ======================================================================================================================
// hold765 in-memory pass. Same decisions as hold_idle::apply_reloc (identity proven on prefixes against the in-memory
// reference), but with 2 B/op of working memory instead of ~80 B/op: live[] and extra[] become one i16 array, the per-wire
// touch lists become per-block first-touch tables plus a block-local backward scan, and the last-product hash map becomes a
// sorted record vector. No file, environment or thread dependence.

/// Source switch for the pass (HOLDS in the reference was an environment variable; this build has none).
pub const HOLD_PASS: bool = true;
/// Extra always-zero wires the pass may use for holds (room grows by this much everywhere); 0 = the 740 row. The printed
/// width is 740 + this value when all of them are used.
pub const HOLD_EXTRA_WIRES: usize = 22;
/// Spare Op slots the truth round leaves after the stream (virtual only: untouched pages are not resident). The gap of the
/// pass is about 2.65M ops on the candidate; if the spare capacity is smaller, `insert` falls back to reserve_exact.
pub const RESERVE_OPS: usize = 16_000_000;
const BLK: usize = 1 << 16;

struct Meta {
    n: usize, nq: usize, nb: usize, regs: [Vec<usize>; 4], input: Vec<bool>,
    after: Vec<u32>,     // nblk * nq: first touch of w in a block strictly after block k
    first_all: Vec<u32>, // first touch of w in the whole stream
}

fn pass0(ops: &[Op]) -> Meta {
    let n = ops.len();
    assert!(n < ZB as usize, "hold_inmem: stream too long for u32 indices");
    let (nq, nb) = dims(ops);
    let regs = registers(ops);
    let nblk = (n + BLK - 1) / BLK;
    let mut first = vec![u32::MAX; nblk * nq];
    for (i, o) in ops.iter().enumerate() {
        let (tw, k) = touched(o);
        for &w in &tw[..k] { let s = &mut first[(i / BLK) * nq + w]; if *s == u32::MAX { *s = i as u32; } }
    }
    let mut after = vec![u32::MAX; nblk * nq];
    let mut run = vec![u32::MAX; nq];
    for k in (0..nblk).rev() {
        for w in 0..nq { after[k * nq + w] = run[w]; }
        for w in 0..nq { if first[k * nq + w] != u32::MAX { run[w] = first[k * nq + w]; } }
    }
    let mut input = vec![false; nq];
    for &w in regs[0].iter().chain(regs[1].iter()) { input[w] = true; }
    Meta { n, nq, nb, regs, input, after, first_all: run }
}

/// room[i] = nq - 1 - live[i] and the candidate pairs (j, i).
fn pass1(ops: &[Op], m: &Meta) -> (Vec<i16>, Vec<(u32, u32)>) {
    let mut room: Vec<i16> = Vec::with_capacity(m.n);
    let mut recs: Vec<(u64, u64, u8, u32)> = vec![]; // (hash hi, hash lo, complement flag, op index)
    let mut sym = Sym::new(m.nq, m.nb, &m.regs);
    let mut ch = vec![];
    for (i, o) in ops.iter().enumerate() {
        if o.kind == K::CCX && o.c_condition == NO_BIT && sym.stack.is_empty() {
            let (t, c1, c2) = (o.q_target.0 as usize, o.q_control1.0 as usize, o.q_control2.0 as usize);
            if sym.q[t] == ZV {
                let mut f = sym.gate(o);
                f.push(sym.q[c1]);
                f.push(sym.q[c2]);
                let p = sym.prod(&mut f);
                if p.l != 0 { recs.push(((p.l >> 64) as u64, p.l as u64, p.c as u8, i as u32)); }
            }
        }
        sym.step(o, &mut ch);
        ch.clear();
        room.push((m.nq as i32 - 1 - (sym.live as u16 as i32)) as i16);
    }
    drop(sym);
    recs.sort_unstable();
    let mut cands: Vec<(u32, u32)> = vec![];
    for k in 1..recs.len() {
        if recs[k].0 == recs[k - 1].0 && recs[k].1 == recs[k - 1].1 && recs[k].2 == recs[k - 1].2 { cands.push((recs[k - 1].3, recs[k].3)); }
    }
    drop(recs);
    cands.sort_unstable_by_key(|c| c.1);
    (room, cands)
}

/// Acceptance under the width rule, shortest first.
fn accept(room: &mut Vec<i16>, cands: &[(u32, u32)]) -> Vec<(u32, u32)> {
    let mut order: Vec<usize> = (0..cands.len()).collect();
    order.sort_by_key(|&k| (cands[k].1 - cands[k].0, cands[k].0));
    let mut acc: Vec<(u32, u32)> = vec![];
    for k in order {
        let (j, e) = cands[k];
        let (a, b) = (j as usize, e as usize);
        if room[a..=b].iter().all(|&r| r >= 0) {
            for r in room[a..=b].iter_mut() { *r -= 1; }
            acc.push((j, e));
        }
    }
    acc.sort_unstable();
    acc
}

struct SPlan { starts: Vec<(u32, u32)>, ends: Vec<(u32, u32)>, hops: Vec<(u32, u32, u32)>, growth: usize }

/// Placement sweep (choose_reloc 2b): zero[w] / nextt[w] stand in for the touch-list cursor.
fn place(ops: &[Op], m: &Meta, acc: &[(u32, u32)]) -> SPlan {
    let nq = m.nq;
    let mut zero: Vec<bool> = m.input.iter().map(|&x| !x).collect();
    let mut nextt: Vec<u32> = m.first_all.clone();
    let mut hosted: Vec<u32> = vec![u32::MAX; nq];
    let mut host: Vec<u32> = vec![u32::MAX; acc.len()];
    let mut dead = vec![false; acc.len()];
    let mut start_w: Vec<u32> = vec![u32::MAX; acc.len()];
    let mut end_w: Vec<u32> = vec![u32::MAX; acc.len()];
    let mut hops: Vec<(u32, u32, u32, u32, u32)> = vec![]; // (i, from, to, hold, condition depth)
    let mut by_end: Vec<(u32, u32)> = acc.iter().enumerate().map(|(h, &(_, e))| (e, h as u32)).collect();
    by_end.sort_unstable();
    let (mut si, mut ei) = (0usize, 0usize);
    let mut active_end: std::collections::BinaryHeap<std::cmp::Reverse<(u32, u32)>> = Default::default();
    let mut cs = CondStack { v: vec![] };
    let mut fails = 0usize;
    let pick = |zero: &Vec<bool>, nextt: &Vec<u32>, hosted: &Vec<u32>, avoid: &[usize]| -> Option<usize> {
        let mut best: Option<(u32, usize)> = None;
        for w in 0..nq {
            if hosted[w] != u32::MAX || avoid.contains(&w) || !zero[w] { continue; }
            let nt = nextt[w];
            if best.map_or(true, |b| nt > b.0) { best = Some((nt, w)); }
        }
        best.map(|b| b.1)
    };
    let mut sym = Sym::new(m.nq, m.nb, &m.regs);
    let mut ch = vec![];
    let nblk = (m.n + BLK - 1) / BLK;
    let mut ann: Vec<[u32; 3]> = Vec::with_capacity(BLK);
    for k in 0..nblk {
        let base = k * BLK;
        let buf = &ops[base..(base + BLK).min(m.n)];
        let mut cur: Vec<u32> = m.after[k * nq..(k + 1) * nq].to_vec();
        ann.clear();
        ann.resize(buf.len(), [u32::MAX; 3]);
        for ii in (0..buf.len()).rev() {
            let (tw, kk) = touched(&buf[ii]);
            for t in 0..kk { ann[ii][t] = cur[tw[t]]; }
            for t in 0..kk { cur[tw[t]] = (base + ii) as u32; }
        }
        for (ii, o) in buf.iter().enumerate() {
            let iu = (base + ii) as u32;
            while let Some(&std::cmp::Reverse((e, h))) = active_end.peek() {
                if e >= iu { break; }
                active_end.pop();
                let h = h as usize;
                if !dead[h] { hosted[host[h] as usize] = u32::MAX; }
            }
            let (tw, kk) = touched(o);
            let tws = &tw[..kk];
            for &w in tws {
                let h = hosted[w];
                if h == u32::MAX { continue; }
                let h = h as usize;
                let ok_cs = cs.v.is_empty() || cs.clean();
                let to = if ok_cs { pick(&zero, &nextt, &hosted, tws) } else { None };
                hosted[w] = u32::MAX;
                match to {
                    Some(u) => { hosted[u] = h as u32; host[h] = u as u32; hops.push((iu, w as u32, u as u32, h as u32, cs.v.len() as u32)); }
                    None => { dead[h] = true; fails += 1; }
                }
            }
            while ei < by_end.len() && by_end[ei].0 == iu {
                let h = by_end[ei].1 as usize;
                ei += 1;
                if !dead[h] && host[h] != u32::MAX { end_w[h] = host[h]; }
            }
            sym.step(o, &mut ch);
            ch.clear();
            for (t, &w) in tws.iter().enumerate() {
                if tws[..t].contains(&w) { continue; }
                zero[w] = sym.q[w] == ZV;
                nextt[w] = ann[ii][t];
            }
            cs.step(o);
            while si < acc.len() && acc[si].0 == iu {
                let h = si;
                si += 1;
                match pick(&zero, &nextt, &hosted, &[]) {
                    Some(u) => { hosted[u] = h as u32; host[h] = u as u32; start_w[h] = u as u32; active_end.push(std::cmp::Reverse((acc[h].1, h as u32))); }
                    None => { dead[h] = true; fails += 1; }
                }
            }
        }
    }
    let mut plan = SPlan { starts: vec![], ends: vec![], hops: vec![], growth: 0 };
    for h in 0..acc.len() {
        if dead[h] { continue; }
        assert!(start_w[h] != u32::MAX && end_w[h] != u32::MAX);
        plan.starts.push((acc[h].0, start_w[h]));
        plan.ends.push((acc[h].1, end_w[h]));
    }
    let mut growth = plan.starts.len() + plan.ends.len();
    for x in hops.iter().filter(|x| !dead[x.3 as usize]) { plan.hops.push((x.0, x.1, x.2)); growth += 1 + 2 * x.4 as usize; }
    plan.growth = growth;
    plan.starts.sort_unstable();
    plan.ends.sort_unstable();
    eprintln!("HOLD_INMEM accepted={} placed={} failed={} hops={} growth_ops={}", acc.len(), plan.starts.len(), fails, plan.hops.len(), growth);
    plan
}

/// Emit the plan in place (the emission of insert_reloc). The spare capacity left by the truth round absorbs the growth.
fn insert(mut ops: Vec<Op>, plan: &SPlan) -> Vec<Op> {
    let n = ops.len();
    if plan.starts.is_empty() { return ops; }
    let gap = plan.growth;
    if gap > ops.capacity() - n { ops.reserve_exact(gap); }
    ops.resize(n + gap, Op::empty());
    ops.copy_within(0..n, gap);
    let mut cs = CondStack { v: vec![] };
    let (mut a, mut b, mut h, mut wr) = (0usize, 0usize, 0usize, 0usize);
    for i in 0..n {
        let o = ops[gap + i];
        while h < plan.hops.len() && plan.hops[h].0 as usize == i {
            let (_, f, t) = plan.hops[h];
            let bits = cs.bits();
            assert!(bits.is_empty() || cs.clean(), "hold_inmem: hop inside a dirty condition block");
            for _ in 0..bits.len() { ops[wr] = pop(); wr += 1; }
            ops[wr] = mk(K::Swap, f as usize, t as usize); wr += 1;
            for &bt in &bits { ops[wr] = push(bt); wr += 1; }
            h += 1;
        }
        if b < plan.ends.len() && plan.ends[b].0 as usize == i {
            let w = plan.ends[b].1 as usize;
            assert!(o.kind == K::CCX && o.c_condition == NO_BIT && cs.v.is_empty());
            let t = o.q_target.0 as usize;
            assert!(t != w);
            ops[wr] = mk(K::CX, w, t);
            ops[wr + 1] = mk(K::CX, t, w);
            wr += 2;
            b += 1;
        } else {
            ops[wr] = o;
            wr += 1;
        }
        while a < plan.starts.len() && plan.starts[a].0 as usize == i {
            ops[wr] = mk(K::CX, o.q_target.0 as usize, plan.starts[a].1 as usize);
            wr += 1;
            a += 1;
        }
        cs.step(&o);
    }
    assert_eq!(wr, n + gap);
    ops.truncate(wr);
    ops
}

/// The pass: returns the rewritten stream and the number of holds placed.
pub fn apply(ops: Vec<Op>) -> (Vec<Op>, usize) {
    let t0 = std::time::Instant::now();
    let m = pass0(&ops);
    let (mut room, cands) = pass1(&ops, &m);
    let ncand = cands.len();
    let acc = accept(&mut room, &cands);
    drop(room);
    drop(cands);
    let plan = place(&ops, &m, &acc);
    drop(m);
    let h = plan.starts.len();
    eprintln!("HOLD_INMEM candidates={} wall_s={:.1} (before emission)", ncand, t0.elapsed().as_secs_f64());
    let out = insert(ops, &plan);
    eprintln!("HOLD_INMEM done holds={} ops={} wall_s={:.1}", h, out.len(), t0.elapsed().as_secs_f64());
    (out, h)
}
