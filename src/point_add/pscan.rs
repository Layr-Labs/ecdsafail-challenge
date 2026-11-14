//! pscan (PRINT ONLY, the gate list is never changed): the "measured value that is
//! a parity of live wires" scan. Switch `SL_PSCAN=1` (unset: nothing runs).
//!
//! For every X measurement (Hmr) of a wire w into a fresh outcome bit b, the FIX REGION of b is every op whose context
//! (condition stack + per-op condition, as bit VALUES: a push captures the value, as the simulator does) holds b. Its
//! Toffoli weight is the sum over its CCX / CCZ of 2^-(context size), the same rule as w1. Where that weight is > 0, the
//! measured value V (w's value just before the measurement) is tested at the region's first op and at its last op:
//! is V an affine parity (XOR, plus the constant 1) of the values the other wires hold there? If so the region's phase
//! (-1)^(b V) is a layer of Z gates under b on those wires (plus a Neg), no Toffoli.
//!
//! Values: cond_pass.rs's hash-consed numbering (atoms: register inputs, AND(x, y), Cond(ctx, x), fresh unknowns; XOR =
//! canonical sorted atom sets, capped at 96 atoms, then a fresh unknown). Equal ids are equal Boolean functions of the
//! inputs and outcomes on every shot, so a span hit is an identity on every shot (sound); the converse does not hold
//! (relations among atoms are not seen), so "no" is not "absent". The span test is GF(2) elimination over the atoms of
//! the wires reached from V's atoms by a
//! breadth-first closure of at most `SL_PSCAN_LEV` levels (default 4) and `SL_PSCAN_CAP` rows (default 400); a "no" is
//! labelled with the levels used and "cap" when the next level did not fit.
//!
//! Output: `PSCAN hmr <op> wire <w> ctx_depth <d> bit <b> first <op> last <op> region_ops <n> ccx <n> weight <T>
//! v_atoms <n> v_kind <atom|set|zero|one> at_first <res> at_last <res>`; res = `span[w1,w2,..]+1` / `no@L<levels>[cap]`.
//! Then `PSCAN_SUM ...`. Op indices are those of the stream handed to the scan (after K3a, before SL_COND).

use crate::circuit::{BitId, Op, OperationType as K, QubitId, RegisterId};
use std::collections::{HashMap, HashSet};

const NQ: u32 = u32::MAX;
#[derive(Clone, Copy)]
struct L { kind: u8, c2: u32, c1: u32, t: u32, ct: u32, cc: u32 }
const K_APP: u8 = 2; const K_BINV: u8 = 3; const K_BS0: u8 = 4; const K_BS1: u8 = 5;
const K_X: u8 = 6; const K_Z: u8 = 7; const K_CX: u8 = 8; const K_SWAP: u8 = 10; const K_R: u8 = 11;
const K_HMR: u8 = 12; const K_CCX: u8 = 13; const K_CCZ: u8 = 14; const K_PUSH: u8 = 15; const K_POP: u8 = 16;
fn d(v: u64) -> u32 { if v == u64::MAX { NQ } else { assert!(v < NQ as u64); v as u32 } }
fn to_l(o: &Op) -> L { L { kind: o.kind as u8, c2: d(o.q_control2.0), c1: d(o.q_control1.0), t: d(o.q_target.0), ct: d(o.c_target.0), cc: d(o.c_condition.0) } }
fn e(v: u32) -> u64 { if v == NQ { u64::MAX } else { v as u64 } }
fn kind_of(k: u8) -> K {
    match k { 0 => K::Neg, 1 => K::Register, 2 => K::AppendToRegister, 3 => K::BitInvert, 4 => K::BitStore0, 5 => K::BitStore1,
        6 => K::X, 7 => K::Z, 8 => K::CX, 9 => K::CZ, 10 => K::Swap, 11 => K::R, 12 => K::Hmr, 13 => K::CCX, 14 => K::CCZ,
        15 => K::PushCondition, 16 => K::PopCondition, _ => K::DebugPrint }
}
fn mkop(kind: u8, t: u32, ct: u32, cc: u32) -> Op {
    let mut o = Op::empty();
    o.kind = kind_of(kind);
    o.q_target = QubitId(e(t)); o.c_target = BitId(e(ct)); o.c_condition = BitId(e(cc)); o.r_target = RegisterId(u64::MAX);
    o.validate();
    o
}
const K_NEG: u8 = 0;

const ZERO: u32 = 0; const ONE: u32 = 1;
const T_OPQ: u8 = 2; const T_AND: u8 = 3; const T_COND: u8 = 5; const T_SET: u8 = 6;
const XSET_CAP: usize = 96;
struct Vals { node: Vec<(u8, u32, u32)>, h: HashMap<(u8, u32, u32), u32>, store: Vec<Vec<u32>>, hs: HashMap<Vec<u32>, u32> }
impl Vals {
    fn new() -> Self { Vals { node: vec![(0, 0, 0), (1, 0, 0)], h: HashMap::new(), store: Vec::new(), hs: HashMap::new() } }
    fn opq(&mut self) -> u32 { let i = self.node.len() as u32; self.node.push((T_OPQ, i, 0)); i }
    fn mk(&mut self, t: u8, a: u32, b: u32) -> u32 {
        if let Some(&i) = self.h.get(&(t, a, b)) { return i; }
        let i = self.node.len() as u32; self.node.push((t, a, b)); self.h.insert((t, a, b), i); i
    }
    fn and(&mut self, a: u32, b: u32) -> u32 {
        if a == ZERO || b == ZERO { return ZERO; }
        if a == ONE { return b; } if b == ONE { return a; } if a == b { return a; }
        let (x, y) = if a < b { (a, b) } else { (b, a) }; self.mk(T_AND, x, y)
    }
    fn atoms(&self, a: u32) -> Vec<u32> {
        if a == ZERO { vec![] } else if self.node[a as usize].0 == T_SET { self.store[self.node[a as usize].1 as usize].clone() } else { vec![a] }
    }
    fn xor(&mut self, a: u32, b: u32) -> u32 {
        if a == ZERO { return b; } if b == ZERO { return a; } if a == b { return ZERO; }
        let sa = self.atoms(a); let sb = self.atoms(b);
        let r = symdiff(&sa, &sb);
        match r.len() {
            0 => ZERO,
            1 => r[0],
            l if l > XSET_CAP => self.opq(),
            _ => {
                if let Some(&id) = self.hs.get(&r) { return id; }
                let si = self.store.len() as u32; self.store.push(r.clone());
                let id = self.node.len() as u32; self.node.push((T_SET, si, 0)); self.hs.insert(r, id); id
            }
        }
    }
    fn cond(&mut self, ctx: u32, x: u32) -> u32 { if ctx == 0 || x == ZERO { x } else { self.mk(T_COND, ctx, x) } }
}
fn symdiff(sa: &[u32], sb: &[u32]) -> Vec<u32> {
    let mut r: Vec<u32> = Vec::with_capacity(sa.len() + sb.len());
    let (mut i, mut j) = (0, 0);
    while i < sa.len() && j < sb.len() {
        if sa[i] < sb[j] { r.push(sa[i]); i += 1; } else if sa[i] > sb[j] { r.push(sb[j]); j += 1; } else { i += 1; j += 1; }
    }
    r.extend_from_slice(&sa[i..]); r.extend_from_slice(&sb[j..]);
    r
}
struct Ctxs { sets: Vec<Vec<u32>>, h: HashMap<Vec<u32>, u32> }
impl Ctxs {
    fn new() -> Self { let mut c = Ctxs { sets: vec![vec![]], h: HashMap::new() }; c.h.insert(vec![], 0); c }
    fn add(&mut self, c: u32, b: u32) -> u32 {
        if b == 1 { return c; }
        if self.sets[c as usize].contains(&b) { return c; }
        let mut v = self.sets[c as usize].clone(); v.push(b); v.sort_unstable();
        if let Some(&i) = self.h.get(&v) { return i; }
        let i = self.sets.len() as u32; self.sets.push(v.clone()); self.h.insert(v, i); i
    }
}

/// One forward pass of the value numbering; `probe(k, ctx, qv, vals)` is called before op k is applied.
fn walk(ops: &[L], mut probe: impl FnMut(usize, &[u32], &[u32], &Vals, &Ctxs, u32, &[u32])) {
    let mut nq = 0u32; let mut nb = 0u32;
    for o in ops { for q in [o.c2, o.c1, o.t] { if q != NQ { nq = nq.max(q + 1); } } for b in [o.ct, o.cc] { if b != NQ { nb = nb.max(b + 1); } } }
    let mut reg_q = vec![false; nq as usize]; let mut reg_b = vec![false; nb as usize];
    for o in ops { if o.kind == K_APP { if o.t != NQ { reg_q[o.t as usize] = true; } if o.ct != NQ { reg_b[o.ct as usize] = true; } } }
    let mut v = Vals::new();
    let mut cx = Ctxs::new();
    let mut qv: Vec<u32> = (0..nq).map(|q| if reg_q[q as usize] { v.opq() } else { ZERO }).collect();
    let mut nbits: u32 = 2;
    let mut bv: Vec<u32> = vec![0; nb as usize];
    for b in 0..nb as usize { if reg_b[b] { bv[b] = nbits; nbits += 1; } }
    let mut stack: Vec<u32> = vec![0];
    for (k, o) in ops.iter().enumerate() {
        let top = *stack.last().unwrap();
        let mut ctx = top;
        if o.cc != NQ && o.kind != K_PUSH { ctx = cx.add(ctx, bv[o.cc as usize]); }
        probe(k, &cx.sets[ctx as usize].clone(), &qv, &v, &cx, ctx, &bv);
        match o.kind {
            K_CCX | K_CX | K_X => {
                let t = o.t as usize;
                let bare = match o.kind { K_CCX => v.and(qv[o.c1 as usize], qv[o.c2 as usize]), K_CX => qv[o.c1 as usize], _ => ONE };
                let term = v.cond(ctx, bare);
                qv[t] = v.xor(qv[t], term);
            }
            K_SWAP => {
                let (a, b) = (o.c1 as usize, o.t as usize);
                if ctx == 0 { qv.swap(a, b); } else { qv[a] = v.opq(); qv[b] = v.opq(); }
            }
            K_R | K_HMR => {
                let t = o.t as usize;
                if o.kind == K_HMR { bv[o.ct as usize] = nbits; nbits += 1; }
                qv[t] = if ctx == 0 { ZERO } else { v.opq() };
            }
            K_BS0 | K_BS1 | K_BINV => {
                let b = o.ct as usize; let old = bv[b];
                let cs = &cx.sets[ctx as usize];
                let nv = if ctx == 0 && o.kind == K_BS0 { 0 } else if ctx == 0 && o.kind == K_BS1 { 1 }
                    else if cs.len() == 1 && (o.kind == K_BS1 || o.kind == K_BINV) && old == 0 { cs[0] }
                    else { let id = nbits; nbits += 1; id };
                bv[b] = nv;
            }
            K_PUSH => { let c = cx.add(top, bv[o.cc as usize]); stack.push(c); }
            K_POP => { stack.pop(); }
            _ => {}
        }
    }
}

/// Is `target` (an atom set) an affine parity of the wires' values? The rows are the wires reached from the target's
/// atoms by a breadth-first closure (a wire joins when it holds an atom already reached), level by level up to `maxlev`
/// levels; a level that would take the row count past `cap` is not added (the test then runs on the levels before it
/// and its "no" is labelled with the level reached). Returns (Some((wires, constant)) or None, levels used, capped).
fn span(target: &[u32], qv: &[u32], vals: &Vals, skip: u32, cap: usize, maxlev: usize) -> (Option<(Vec<u32>, bool)>, usize, bool) {
    let tgt: Vec<u32> = target.iter().copied().filter(|&a| a != ONE).collect();
    if tgt.is_empty() { return (Some((vec![], target.contains(&ONE))), 0, false); }
    let mut idx: HashMap<u32, Vec<u32>> = HashMap::new();
    let mut wat: HashMap<u32, Vec<u32>> = HashMap::new();
    for (q, &x) in qv.iter().enumerate() {
        if x == ZERO || q as u32 == skip { continue; }
        let a = vals.atoms(x);
        for &t in &a { if t != ONE { idx.entry(t).or_default().push(q as u32); } }
        wat.insert(q as u32, a);
    }
    if tgt.iter().any(|a| !idx.contains_key(a)) { return (None, 0, false); }
    let mut seen_a: HashSet<u32> = tgt.iter().copied().collect();
    let mut seen_w: HashSet<u32> = HashSet::new();
    let mut rows: Vec<u32> = Vec::new();
    let mut frontier: Vec<u32> = tgt.clone();
    let mut lev = 0; let mut capped = false;
    while lev < maxlev && !frontier.is_empty() {
        let mut add: Vec<u32> = Vec::new();
        for &a in &frontier { if let Some(ws) = idx.get(&a) { for &w in ws { if !seen_w.contains(&w) && !add.contains(&w) { add.push(w); } } } }
        if rows.len() + add.len() > cap { capped = true; break; }
        let mut nf: Vec<u32> = Vec::new();
        for &w in &add { seen_w.insert(w); rows.push(w); for &b in &wat[&w] { if b != ONE && seen_a.insert(b) { nf.push(b); } } }
        frontier = nf; lev += 1;
    }
    let mut basis: HashMap<u32, (Vec<u32>, Vec<u32>)> = HashMap::new();
    let piv = |s: &[u32]| s.iter().rev().copied().find(|&a| a != ONE);
    for &w in &rows {
        let mut s = wat[&w].clone(); let mut comb = vec![w];
        while let Some(p) = piv(&s) {
            match basis.get(&p) { Some((bs, bc)) => { s = symdiff(&s, bs); comb = symdiff(&comb, bc); } None => break }
        }
        if let Some(p) = piv(&s) { basis.insert(p, (s, comb)); }
    }
    let mut s: Vec<u32> = target.to_vec(); let mut comb: Vec<u32> = vec![];
    while let Some(p) = piv(&s) {
        match basis.get(&p) { Some((bs, bc)) => { s = symdiff(&s, bs); comb = symdiff(&comb, bc); } None => return (None, lev, capped) }
    }
    (Some((comb, s.contains(&ONE))), lev, capped)
}

/// A span hit at a fix region's first op: (Hmr op, measured wire, region first op, region last op, region ops, CCX,
/// weight, Z wires, constant).
type Hit = (usize, u32, usize, usize, usize, usize, f64, Vec<u32>, bool);

/// `SL_PSCAN=1`: print the scan. `SL_PSCAN_FIX=1`: also rewrite every hit whose fix region is one PUSH(b) .. POP block
/// that restores its wires and whose bits are dead after it: the block becomes Z gates under b on the span wires (and a
/// Neg under b for the constant), placed where the PUSH stood. `SL_PSCAN_PAD=1` (diagnostic, never a candidate): as
/// many idle Hmr of a fresh wire before those gates as the block held Hmr + R, so the list draws the base's random
/// words in the base's order (aligned copy). `SL_PSCAN_FAULT=1` (a control): the first Z gate of every rewrite left out.
pub fn run(ops: Vec<Op>) -> Vec<Op> {
    let fix = std::env::var("SL_PSCAN_FIX").is_ok_and(|v| v == "1");
    if !fix && !std::env::var("SL_PSCAN").is_ok_and(|v| v == "1") { return ops; }
    let hits = scan_all(&ops);
    if !fix { return ops; }
    let pad = std::env::var("SL_PSCAN_PAD").is_ok_and(|v| v == "1");
    let fault = std::env::var("SL_PSCAN_FAULT").is_ok_and(|v| v == "1");
    let l: Vec<L> = ops.iter().map(to_l).collect();
    let mut nq = 0u32; let mut nb = 0u32;
    for o in &l { for q in [o.c2, o.c1, o.t] { if q != NQ { nq = nq.max(q + 1); } } for b in [o.ct, o.cc] { if b != NQ { nb = nb.max(b + 1); } } }
    // snapshots of every wire's value just before each candidate block's PUSH and just after its POP
    let mut want: HashMap<usize, Vec<(usize, bool)>> = HashMap::new();
    for (i, h) in hits.iter().enumerate() { if h.2 >= 1 { want.entry(h.2 - 1).or_default().push((i, true)); want.entry(h.3 + 1).or_default().push((i, false)); } }
    let mut snaps: HashMap<(usize, bool), Vec<u32>> = HashMap::new();
    walk(&l, |k, _c, qv, _v, _cx, _ctx, _bv| { if let Some(v) = want.get(&k) { for &(i, b) in v { snaps.insert((i, b), qv.to_vec()); } } });
    let mut repl: HashMap<usize, (usize, Vec<Op>)> = HashMap::new();
    let mut saved = 0f64;
    for (i, h) in hits.iter().enumerate() {
        let (hk, _w, first, last, nops, nccx, wt, ref zs, c1) = *h;
        let why = |r: &str| eprintln!("PSCAN_FIX skip hmr {hk}: {r}");
        if first == 0 || last + 1 >= l.len() { why("edge"); continue; }
        // the region runs from the op after the PUSH (whose own context does not hold b yet) to the POP (whose does)
        let (b0, b1) = (first - 1, last);
        let slot = l[hk].ct;
        if l[b0].kind != K_PUSH || l[b0].cc != slot || l[b1].kind != K_POP { why("region is not one PUSH(b) .. POP block"); continue; }
        if nops != last - first + 1 { why("region not contiguous"); continue; }
        let mut d = 0i64; let mut ok = true;
        for o in &l[first..last] { if o.kind == K_PUSH { d += 1; } if o.kind == K_POP { d -= 1; if d < 0 { ok = false; break; } } }
        if !ok || d != 0 { why("unbalanced block"); continue; }
        let (Some(sb), Some(sa)) = (snaps.get(&(i, true)), snaps.get(&(i, false))) else { why("no snapshot"); continue };
        let mut lastop: HashMap<u32, u8> = HashMap::new();
        for o in &l[first..last] { for q in [o.c2, o.c1, o.t] { if q != NQ { lastop.insert(q, o.kind); } } }
        let bad: Vec<u32> = lastop.iter().filter(|&(&q, &k)| !(sb[q as usize] == sa[q as usize] || (sb[q as usize] == ZERO && (k == K_HMR || k == K_R)))).map(|(&q, _)| q).collect();
        if !bad.is_empty() { why(&format!("block does not restore wires {:?}", bad)); continue; }
        // bit slots written in the block must be dead after it (next mention an unconditional overwrite at depth 0)
        let mut slots: HashSet<u32> = HashSet::new();
        for o in &l[first..last] { if matches!(o.kind, K_HMR | K_BS0 | K_BS1 | K_BINV) && o.ct != NQ { slots.insert(o.ct); } }
        let mut dead = true;
        // a read of the slot is covered when an earlier write after the block (no per-op condition) sits in a push region
        // that is still open: the read runs only where that region's captured condition holds, and so did the write.
        // An unconditional write at depth 0 ends the scan (the block's value is dead from there).
        'sl: for &s in &slots {
            let mut depth = 0i64;
            let mut cover: Option<i64> = None;
            for o in &l[b1 + 1..] {
                let reads = o.cc == s || (o.kind == K_BINV && o.ct == s);
                if reads && cover.is_none() { dead = false; break 'sl; }
                if matches!(o.kind, K_HMR | K_BS0 | K_BS1) && o.ct == s {
                    if o.cc != NQ { if cover.is_none() { dead = false; break 'sl; } }
                    else if depth == 0 { continue 'sl; }
                    else if cover.map_or(true, |c| depth < c) { cover = Some(depth); }
                }
                if o.kind == K_PUSH { depth += 1; }
                else if o.kind == K_POP { depth -= 1; if cover.is_some_and(|c| depth < c) { cover = None; } }
            }
        }
        if !dead { why("a bit written in the block is read after it"); continue; }
        let nmeas = l[first..last].iter().filter(|o| o.kind == K_HMR || o.kind == K_R).count();
        let mut v: Vec<Op> = Vec::new();
        if pad { for _ in 0..nmeas { v.push(mkop(K_HMR, nq, nb, NQ)); } }
        for (j, &q) in zs.iter().enumerate() { if fault && j == 0 { continue; } v.push(mkop(K_Z, q, NQ, slot)); }
        if c1 { v.push(mkop(K_NEG, NQ, NQ, slot)); }
        eprintln!("PSCAN_FIX hmr {hk} block {b0}..{b1} ops {} ccx {nccx} weight {wt:.3} z {:?}{} meas_removed {nmeas}{}{}", b1 - b0 + 1, zs, if c1 { " neg" } else { "" },
            if pad { " PAD" } else { "" }, if fault { " FAULT" } else { "" });
        saved += wt;
        repl.insert(b0, (b1, v));
    }
    eprintln!("PSCAN_FIX rewrites {} saved {:.3} T", repl.len(), saved);
    if repl.is_empty() { return ops; }
    let mut out: Vec<Op> = Vec::with_capacity(ops.len());
    let mut skip_to: Option<usize> = None;
    for (k, o) in ops.into_iter().enumerate() {
        if let Some(b1) = skip_to { if k <= b1 { continue; } skip_to = None; }
        if let Some((b1, v)) = repl.remove(&k) { out.extend(v); skip_to = Some(b1); continue; }
        out.push(o);
    }
    out
}

pub fn scan(ops: &[Op]) { if std::env::var("SL_PSCAN").is_ok_and(|v| v == "1") { scan_all(ops); } }

fn scan_all(ops: &[Op]) -> Vec<Hit> {
    let cap: usize = std::env::var("SL_PSCAN_CAP").ok().and_then(|v| v.parse().ok()).unwrap_or(400);
    let maxlev: usize = std::env::var("SL_PSCAN_LEV").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
    let l: Vec<L> = ops.iter().map(to_l).collect();
    // pass 1: measurements, their bit values and fix regions
    struct M { k: usize, w: u32, depth: usize, v: Vec<u32>, vkind: &'static str, first: usize, last: usize, nops: usize, nccx: usize, wt: f64 }
    let mut ms: Vec<M> = Vec::new();
    let mut by_bit: HashMap<u32, usize> = HashMap::new();
    let mut pend: Option<(usize, u32, usize, Vec<u32>, &'static str)> = None;
    walk(&l, |k, ctxset, qv, vals, _cx, _ctx, bv| {
        // the previous op was an Hmr: its new bit value is now in the slot
        if let Some((hk, w, depth, v, vk)) = pend.take() {
            let b = bv[l[hk].ct as usize];
            by_bit.insert(b, ms.len());
            ms.push(M { k: hk, w, depth, v, vkind: vk, first: NQ as usize, last: 0, nops: 0, nccx: 0, wt: 0.0 });
        }
        let o = &l[k];
        for &b in ctxset {
            if let Some(&i) = by_bit.get(&b) {
                let m = &mut ms[i];
                if m.first == NQ as usize { m.first = k; }
                m.last = k; m.nops += 1;
                if o.kind == K_CCX || o.kind == K_CCZ { m.nccx += 1; m.wt += 0.5f64.powi(ctxset.len() as i32); }
            }
        }
        if o.kind == K_HMR {
            let x = qv[o.t as usize];
            let vk = if x == ZERO { "zero" } else if x == ONE { "one" } else if vals.node[x as usize].0 == T_SET { "set" } else { "atom" };
            pend = Some((k, o.t, ctxset.len(), vals.atoms(x), vk));
        }
    });
    let cand: Vec<usize> = (0..ms.len()).filter(|&i| ms[i].wt > 0.0).collect();
    let mut at: HashMap<usize, Vec<(usize, bool)>> = HashMap::new();
    for &i in &cand { at.entry(ms[i].first).or_default().push((i, true)); at.entry(ms[i].last).or_default().push((i, false)); }
    let mut res: HashMap<(usize, bool), String> = HashMap::new();
    let mut spans: HashMap<usize, (Vec<u32>, bool)> = HashMap::new();
    walk(&l, |k, _ctxset, qv, vals, _cx, _ctx, _bv| {
        if let Some(v) = at.get(&k) {
            for &(i, first) in v {
                let m = &ms[i];
                let (r, lev, capped) = span(&m.v, qv, vals, m.w, cap, maxlev);
                let r = match r {
                    None => format!("no@L{}{}", lev, if capped { "cap" } else { "" }),
                    Some((ws, c)) => { let r = format!("span{:?}{}", ws, if c { "+1" } else { "" }); if first { spans.insert(i, (ws, c)); } r }
                };
                res.insert((i, first), r);
            }
        }
    });
    let (mut tot_w, mut hit_w, mut hits, mut caps) = (0f64, 0f64, 0usize, 0usize);
    let mut out: Vec<Hit> = Vec::new();
    for &i in &cand {
        let m = &ms[i];
        let (a, b) = (res[&(i, true)].clone(), res[&(i, false)].clone());
        if let Some((ws, c)) = spans.get(&i) { out.push((m.k, m.w, m.first, m.last, m.nops, m.nccx, m.wt, ws.clone(), *c)); }
        tot_w += m.wt;
        if a.starts_with("span") || b.starts_with("span") { hits += 1; hit_w += m.wt; }
        if a.ends_with("cap") || b.ends_with("cap") { caps += 1; }
        eprintln!("PSCAN hmr {} wire {} ctx_depth {} first {} last {} region_ops {} ccx {} weight {:.4} v_atoms {} v_kind {} at_first {} at_last {}",
            m.k, m.w, m.depth, m.first, m.last, m.nops, m.nccx, m.wt, m.v.len(), m.vkind, a, b);
    }
    eprintln!("PSCAN_SUM measurements {} with_toffoli_regions {} region_weight {:.3} span_hits {} hit_weight {:.3} capped {} cap {} levels {}",
        ms.len(), cand.len(), tot_w, hits, hit_w, caps, cap, maxlev);
    out
}

/// The X measurements whose measured value is a constant (the value numbering's ZERO or ONE: the same Boolean
/// function of the inputs and outcomes on every shot), with the Toffoli weight of their fix region (as in the scan:
/// the sum over the CCX / CCZ whose context holds the outcome of 2^-(context size)). Read by zero_force.rs.
pub(crate) fn const_measurements(ops: &[Op]) -> Vec<(usize, bool, f64)> {
    let l: Vec<L> = ops.iter().map(to_l).collect();
    let mut out: Vec<(usize, bool, f64)> = Vec::new();
    let mut by_bit: HashMap<u32, usize> = HashMap::new();
    let mut pend: Option<(usize, bool)> = None;
    walk(&l, |k, ctxset, qv, _vals, _cx, _ctx, bv| {
        if let Some((hk, one)) = pend.take() {
            by_bit.insert(bv[l[hk].ct as usize], out.len());
            out.push((hk, one, 0.0));
        }
        let o = &l[k];
        if o.kind == K_CCX || o.kind == K_CCZ {
            for &b in ctxset { if let Some(&i) = by_bit.get(&b) { out[i].2 += 0.5f64.powi(ctxset.len() as i32); } }
        }
        if o.kind == K_HMR {
            let x = qv[o.t as usize];
            if x == ZERO || x == ONE { pend = Some((k, x == ONE)); }
        }
    });
    out
}
